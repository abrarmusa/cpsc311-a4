#lang plai

;Student #1, Name: Abrar Musa
;Student #1, ugrad.cs.ubc.ca login: i1u9a
;Student #1, ID: 48915086

;Student #2, Name: Yousef Mirza
;Student #2, ugrad.cs.ubc.ca login: y9r8
;Student #2, ID: 54327127

;Student #3, Name: Kevin Tran
;Student #3, ugrad.cs.ubc.ca login: j1e9
;Student #3, ID: 31609126

; a4-step.rkt -- a4 Problems 3 and 4
; CPSC 311 2015W1 assignment 4
;
; This is ONE of TWO files.  This file is for Problems 3 and 4.
; The other file is called a4.rkt.

; a4-step.rkt
; implements a _small-step_ semantics that can, relatively easily,
; be extended with (simulated) parallelism and nondeterminism.

; BNF of the Fun language used in this file:
;
;  <E> ::= <num>
;        | {+ <E> <E>}
;        | {- <E> <E>}
;        | {with {<id> <E>} <E>}
;        | <id>
;        | {lam <id> <E>}
;        | {app <E> <E>}
;        | {rec <id> <E>}
;
;        | {if0 <E> <E> <E>}    ; "new" in a4, but already done
;        | {par <E> <E>}        ; new in a4
;        | {choose <E> <E>}     ; new in a4

; Abstract syntax of E (Fun expressions):
(define-type E
  [num (n number?)]
  [add (lhs E?) (rhs E?)]
  [sub (lhs E?) (rhs E?)]
  [with (name symbol?) (named-expr E?) (body E?)]
  [id (name symbol?)]
  
  [lam (name symbol?) (body E?)]
  [app (function E?) (argument E?)]
  [rec (u symbol?) (body E?)]
  
  [if0 (scrutinee E?) (zero-branch E?) (nonzero-branch E?)] ; "new" in a4
  [par (lhs E?) (rhs E?)]      ; new in a4
  [choose (lhs E?) (rhs E?)]   ; new in a4
  )

; Parser
(define (parse sexp)
  (cond
    
    [(number? sexp) (num sexp)]
    
    [(symbol? sexp) (id sexp)]
    
    [(list? sexp)
     (let*
         ([head      (first sexp)]
          [args      (rest sexp)]
          [arg-count (length args)])
       
       (case head
         [(+) (if (= arg-count 2)
                  (add (parse (first args)) (parse (second args)))
                  (error "parse: + needs exactly 2 arguments"))]
         
         [(-) (if (= arg-count 2)
                  (sub (parse (first args)) (parse (second args)))
                  (error "parse: - needs exactly 2 arguments"))]

         [(par) (if (= arg-count 2)
                    (par (parse (first args)) (parse (second args)))
                    (error "parse: par needs exactly 2 arguments"))]

         [(choose) (if (= arg-count 2)
                       (choose (parse (first args)) (parse (second args)))
                       (error "parse: choose needs exactly 2 arguments"))]

         [(if0) (if (= arg-count 3)
                       (if0 (parse (first args)) (parse (second args)) (parse (third args)))
                       (error "parse: if0 needs exactly 3 arguments"))]
         
         [(lam) (if (= arg-count 2)
                    (if (symbol? (first args))
                        (lam (first args) (parse (second args)))
                        (error "parse: lam must be followed by an identifier"))
                    (error "parse: malformed `lam'"))]

         [(app) (if (= arg-count 2)
                  (app (parse (first args)) (parse (second args)))
                  (error "parse: app needs 1 function and 1 argument"))]

         [(rec) (if (= arg-count 2)
                  (rec (first args) (parse (second args)))
                  (error "parse: rec needs 1 identifier and 1 body"))]

         [(with) (if (= arg-count 2)
                   (let ([inner-sexp (first args)]
                         [body-sexp  (second args)])
                     (if (and (list? inner-sexp)
                              (= (length inner-sexp) 2))
                         
                         ; extract from the inner list {<id> <WAE>}
                         (let ([name       (first inner-sexp)]
                               [named-sexp (second inner-sexp)]) 
                           (if (symbol? name)
                               (with name
                                     (parse named-sexp)
                                     (parse body-sexp))
                               
                               (error "parse: malformed `with'")))
                         
                         (error "parse: malformed `with'")))
                   (error "parse: malformed `with'"))]
         
         [else (error "parse: I only understand +, -, `with', `lam', `app'")]))]
    [else (error "parse: syntax error")]))



; subst : E symbol E -> E
;
; (subst e x v) returns e with x replaced by v.
; Precondition: v is a value, i.e. (or (E-num? v) (E-lam? v)).
;
(define (subst e x v)
  (type-case E e
    [num (n) (num n)]    
    [add (eL eR) (add (subst eL x v) (subst eR x v))]
    [sub (eL eR) (sub (subst eL x v) (subst eR x v))]
    [par (eL eR) (par (subst eL x v) (subst eR x v))]
    [choose (eL eR) (choose (subst eL x v) (subst eR x v))]
    [if0 (e eZ eNZ) (if0 (subst e x v) (subst eZ x v) (subst eNZ x v))]
    
    [with (y e eB)
          (if (symbol=? x y)
              (with x (subst e x v) eB) 
              (with y (subst e x v) (subst eB x v)))]
    [id (y)
          (if (symbol=? x y)
              v
              (id y))]
    
    [lam (y eB)
          (if (symbol=? x y)
              (lam x eB)
              (lam y (subst eB x v))
              )]
    
    [rec (y eB)
          (if (symbol=? x y)
              (rec x eB)      
              (rec y (subst eB x v)))]
    
    [app (eFun eArg) (app (subst eFun x v) (subst eArg x v))]
  )
)

; value? : E -> boolean
;
; Returns true if e is a value.  In this small version of Fun,
; the only values are numbers and lams.
;
(define (value? e)
  (type-case E e
    [num (n)     true]
    [lam (x eB)  true]
    [else        false]))

; try-step : E -> E
;
; (try-step e): If e is already a value, return it.
;               Otherwise, try to take 1 step.
(define (try-step e)
  (if (value? e)
      e
      (step e)))

; steps-aux : E -> E
;
; Calls step repeatedly, if needed, until it gets a value.
;
(define (steps-aux e)
  (if (value? e)
      (begin
        (printf "    value.\n")
        e)
      (let* ([e2 (step e)])
        (if e2
            (begin
              (printf "--> ~a\n" (unparse e2))
              (steps-aux e2))
            false))))

; steps : E -> (or false E)
;
; Calls step repeatedly, if needed, until it gets a value
(define (steps e)
  (and e
       (begin
         (printf "    ~a\n" (unparse e))
         (steps-aux e))
       ))

; reduce : E -> (or false E)
;
; Attempts to apply one of the Step-... rules, *except* for
; Step-context.  If no rules can be applied, returns false.
;
(define (reduce e)
  (type-case E e

;from piazza:
;"...There, the assignment tells you to resolve [choose's] nondeterminism using (random 2).
;For par, the assignment doesn't explicitly tell you how to resolve the
;nondeterminism...but it doesn't forbid you from resolving it in the same way."
    
    [par (e1 e2)
         ; a4 Problem 3
         ; replace with your implementation of Step-par-left/Step-par-right
         (if (= (random 2) 0)
             (try-step e1) ;if 0, step left
             (try-step e2) ;if 1, step right
             )
         ]
    
    [choose (e1 e2)
         ; a4 Problem 3
         ; replace with your implementation of Step-choose-left/Step-choose-right
         (if (= (random 2) 0)
             (try-step e1) ;if 0, step left
             (try-step e2) ;if 1, step right
             )
         ]

    [if0 (e eZ eNZ)   ; Step-if0-zero, Step-if0-nonzero
         
         (if (num? e)
             (if (= (num-n e) 0)
                 eZ
                 eNZ)
             false)
         ]
    
    [add (e1 e2)   ; Step-add
         
         (if (and (num? e1) (num? e2))
             (num (+ (num-n e1) (num-n e2)))
             false)
         ]
    
    [sub (e1 e2)   ; Step-sub
         
         (if (and (num? e1) (num? e2))
             (num (- (num-n e1) (num-n e2)))
             false)
         ]
    
    [app (e1 e2)   ; Step-app-value
         
         (if (and (lam? e1) (value? e2))
             (subst (lam-body e1) (lam-name e1) e2)
             false)
         ]
         
    [with (x e1 e2)   ; Step-with
          (if (value? e1)
              (subst e2 x e1)
              false)
         ]
         
    [rec (u e)        ; Step-rec
         (subst e u (rec u e))
         ]
        
    [id (x)
        (error "free-variable")]
    
    [else
        false]
    ))

; step : E -> (or false E)
;
; Given e, returns an e' such that  e --> e'  using the Step-... rules.
; If no such e' exists, returns false.
;
(define (step e)
  (or  ; First, try to call reduce (above) to apply one of the
       ; "reduction rules":
       ;    Step-add, Step-sub, Step-app-value, Step-with, Step-rec.
       ;    (You will implement: Step-par-left, Step-par-right,
       ;                         Step-choose-left, Step-choose-right.)
      (reduce e)
      
      ; Couldn't apply any reduction rules to the whole expression.
      ; Try to apply the context rule Step-context,
      ; using the definition of evaluation contexts C
      ; to find a subexpression that steps.
      (type-case E e
        [add (e1 e2)
             (let ([s1 (step e1)])            ; C ::= (add C e2)
               (if s1
                   (add s1 e2)
                   (if (value? e1)
                       (let ([s2 (step e2)])  ; C ::= (add v C)
                         (if s2
                             (add e1 s2)
                             false))
                       false)))]
                       
        [sub (e1 e2)
             (let ([s1 (step e1)])            ; C ::= (sub C e2)
               (if s1
                   (sub s1 e2)
                   (if (value? e1)
                       (let ([s2 (step e2)])
                         (if s2
                             (sub e1 s2)      ; C ::= (sub v C)
                             false))
                       false)))]
       
        [if0 (e eZ eNZ)
             (let ([s (step e)])              ; C ::= (if0 C eZ eNZ)
               (if s
                   (if0 s eZ eNZ)
                   false))]
       
        [app (e1 e2)
             (let ([s1 (step e1)])
               (if s1
                   (app s1 e2)              ; C ::= (app C e2)
                   (if (value? e1)
                       (let ([s2 (step e2)])
                         (if s2
                             (app e1 s2)    ; C ::= (app v C)
                             false))
                       false)))]
        
        [with (x e1 eB)
              (let ([s1 (step e1)])
                (if s1
                    (with x s1 eB)    ; C ::= (with x C eB)
                    false))]
        
        [par (e1 e2)
             ; the call to reduce, above, returned false;
             ; therefore (once you've implemented the missing code in reduce),
             ; neither e1 nor e2 is a value.
             (let ([v1 (step e1)])
               (if v1
                   (par v1 e2)               ; C ::= (par C e) 
                   (if (value? e1)
                       (let ([v2 (step e2)])
                         (if v2
                             (step e1 v2)    ; C ::= (par e C)
                             false))
                       false)))
             ; a4 Problem 3
             ]
        
        ; NOTE: no branch for choose, since it doesn't appear
        ;  in the grammar of evaluation contexts C
        
        [else
           false]
        )))

(define (unparse e)
  (if (false? e)
      `false
      (type-case E e
        [num (n) n]
        [add (e1 e2)    `(+ ,(unparse e1) ,(unparse e2))]
        [sub (e1 e2)    `(- ,(unparse e1) ,(unparse e2))]
        [if0 (e e1 e2)  `(if0 ,(unparse e) ,(unparse e1) ,(unparse e2))]
        [with (x e1 eB) `(with (,x ,(unparse e1)) ,(unparse eB))] 
        [id (x) x]
        [lam (x body)   `(lam ,x ,(unparse body))]
        [rec (u body)   `(rec ,u ,(unparse body))]
        [app (e1 e2)    `(app ,(unparse e1) ,(unparse e2))]
        [par (e1 e2)    `(par ,(unparse e1) ,(unparse e2))]
        [choose (e1 e2) `(choose ,(unparse e1) ,(unparse e2))]
        )))

(unparse (steps (parse
         '{with {repeat {lam f {lam x {app f {app f x}}}}}
                {app repeat {lam z {+ z z}}}}
         )))

(unparse (steps (parse
         '{choose {choose 1 2} {choose 3 4}})))

(unparse (steps (parse
         '{par {app {lam x 1} 0}
               {app {lam x 2} 0}})))

; try-some : E -> positive-integer -> listof E
;
; Our semantics is now very nondeterministic, so we need
; a way to evaluate the same expression repeatedly and
; collect the results into a list.
(define (try-some e n)
  (if (= n 0)
      empty
      (cons (unparse (steps e))
            (try-some e (- n 1)))))

#|
  Problem 4
  
  Replace the concrete syntax {+ 1 1}, etc. with your solution.
  Or remove the calls to parse, and write in abstract syntax.
|#
(define part4a-e1 (parse '{app {lam x 1} 0} ) )

(define part4a-e2 (parse '{rec part4a-e2 part4a-e2}) )

#| Part 4a:
   If you think no such expressions e1, e2 exist,
   explain why here:


   (Part 4a)
|#

(define part4b-e3 (parse '{+ 4 4}))

(define part4b-e4 (parse '{+ 4 4}))

#| Part 4b:
   If you think no such expressions e3, e4 exist,
   explain why here:

   No such expression exists. This is because if choose terminates to a value, it means that par will also terminate to a value;


|#


; Save before you try these...

; test 4a:
  (try-some (par part4a-e1 part4a-e2) 10)
;  (try-some (choose e1 e2) 10)

#|
; test 4b:
  (try-some (choose e3 e4) 20)
  (try-some (par e3 e4) 5)
|#


#|
(try-some (parse '{choose {choose 1 2} {choose 3 4}}) 10)

(try-some (parse '{par {app {lam x 1} 0}
                       {app {lam x 2} 0}}) 10)

(try-some (parse '{par {app {app {lam x {lam y 1}} 0} 0}
                         {app {app {lam x {lam y 2}} 0} 0}}) 10)

(try-some (parse
           '{with ; A way to take extra steps:
                  {spin {rec spin {lam k {if0 k
                                              0
                                              {app spin {- k 1}}}}}}
                  ; Starts two "threads", one that spins for time 3,
                  ; one that spins for time 4.  Occasionally, the
                  ; second thread "wins" and we return 2.
                  {par {with {s {app spin 3}}
                             {app {lam x 1} 0}}
                       {with {s {app spin 4}}
                             {app {lam x 2} 0}}}}
           )
          10)
|#
