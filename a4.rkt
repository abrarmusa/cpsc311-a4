#lang plai

; a4.rkt -- a4 Problems 1 and 2
; CPSC 311 2015W1 assignment 4
;
; This is ONE of TWO files.  This file is for Problems 1 and 2.
; The other file is called a4-step.rkt.

; BNF of the Fun++ language:
;
; <Binding> ::= {<id> <E>}            ; used in with*, below
;
;  <E> ::= <num>
;        | {+ <E> <E>}
;        | {- <E> <E>}
;        | {= <E> <E>}
;        | {< <E> <E>}
;        | {with {<id> <E>} <E>}
;        | <id>
;        | {lam <id> <Type> <E>}
;        | {app <E> <E>}
;        | {app-expr <E> <E>}
;        | {app-lazy <E> <E>}
;
;        | {rec <id> <Type> <E>}
;
;        | {with* { <Binding>... } <E>}     -----> syntactic sugar for with
;                            ^ zero or more
;        | btrue
;        | bfalse
;        | {ite <E> <E> <E>}         ; "if-then-else"
;
;        | {pair <E> <E>}
;        | {pair-case <E> {<id> <id> => <E>}}
;
;        | {empty <Type>}
;        | {cons <E> <E>}
;        | {list-case <E> {empty => <E>} {cons <id> <id> => <E>}}
;
;        | {ref <E>}
;        | {deref <E>}
;        | {setref <E> <E>}
;
;        | {downcast <Type> <E>}
;
;        | {record <Field>...}
;        | {dot <E> <Field}
;
; <Field> ::= {<id> <E>}

;  <Type> ::= Rat
;           | Bool
;           | {List <Type>}
;           | {* <Type> <Type>}
;           | {-> <Type> <Type>...}
;                              ^ one or more
;           | {Record <FieldsType>...}
;
; <FieldsType> ::= {<id> <id>... <Type>}

(define-type Type
  [t/pos]    ; positive integers
  [t/int]    ; integers
  [t/rat]    ; rationals
  [t/bool]
  [t/*       (t1 Type?)     (t2 Type?)]
  [t/->      (domain Type?) (range Type?)]
  [t/list    (elements Type?)]
  [t/ref     (contents Type?)]
  [t/record  (fields (listof FieldType?))]
  )

(define-type FieldType
  [field-type (name symbol?) (A Type?)])

(define-type Typing-context
  [tc/empty]
  [tc/cons-tp    (x symbol?) (A Type?) (rest Typing-context?)]
  )



; Abstract syntax of E (Fun expressions):

(define-type Op
  ; operators from 2 numbers to a number:
  [plusop]
  [minusop]
  ; operators from 2 numbers to a bool:
  [equalsop]
  [lessthanop]
  )


(define-type E
  ; numbers
  [num (n number?)]
  [binop (op Op?) (lhs E?) (rhs E?)]
  
  ; binding
  [with (name symbol?) (named-expr E?) (body E?)]
  [id (name symbol?)]
;  [with* (bindings (listof Binding?)) (body E?)]
  
  [lam (name symbol?) (domain Type?) (body E?)]
  
  ; recursion
  [rec (name symbol?) (body-type Type?) (body E?)]
  
  ; booleans
  [bfalse]
  [btrue]
  [ite (b E?) (then-branch E?) (else-branch E?)]
  
  ; pairs
  [pair (left E?) (right E?)]
  [pair-case (scrutinee E?) (name1 symbol?) (name2 symbol?) (body E?)]
  
  ; lists
  [list-empty (element Type?)]
  [list-cons  (head E?) (tail E?)]
  [list-case  (scrutinee E?) (empty-branch E?) (head symbol?) (tail symbol?) (cons-branch E?)]
  
  
  [clo (env Env?) (e E?)]               ; not in concrete syntax
  [clo-rec (box-env box?) (e E?)]       ; not in concrete syntax
  [thk (env Env?) (e E?)]               ; not in concrete syntax
  
  [app (function E?) (argument E?)]
  [app-expr (function E?) (argument E?)]
  [app-lazy (function E?) (argument E?)]
  [lazy-ptr (locsym (box/c E?))]        ; not in concrete syntax
  [lazy-thk (env Env?) (e E?)]          ; not in concrete syntax
  
  ; refs
  [ref       (contents-type Type?) (initial-contents E?)]
  [deref     (loc-expr E?)]
  [setref    (loc-expr E?) (new-contents E?)]
  ; [location  (locsym symbol?)]
  [location  (locsym (box/c E?))]
  
  ; downcasts
  [downcast  (target Type?) (e E?)]
  
  ; records
  [record    (fields (listof Field?))]
  
  [dot       (e E?) (field symbol?)]
  )

(define-type Field
  [fld       (name symbol?) (contents E?)])


; parse-op : symbol? -> E?
;
(define (parse-op s)
  (case s
    [(+) (plusop)]
    [(-) (minusop)]
    [(<) (lessthanop)]
    [(=) (equalsop)]
    [else (error "impossible")]))

; Parser for Fun expressions
;
(define (parse sexp)
  (cond
    
    [(number? sexp) (num sexp)]
    
    [(symbol? sexp)
     (case sexp
       [(bfalse) (bfalse)]
       [(btrue)  (btrue)]
       [else
        (id sexp)])]
    
    [(list? sexp)
     (let*
         ([head      (first sexp)]
          [args      (rest sexp)]
          [arg-count (length args)])
       
       (case head
         [(+ - = <)  (if (= arg-count 2)
                         (binop (parse-op head) (parse (first args)) (parse (second args)))
                         (error "parse: " head " needs exactly 2 arguments"))]
         
         [(with*) (if (= arg-count 2)
                      (let ([bindings   (first args)]
                            [body-sexp  (second args)])
                        (if (empty? bindings)
                            (parse body-sexp)
                            (parse (list 'with (first bindings)
                                         (list 'with* (rest bindings) body-sexp)))))
                      (error "parse: malformed `with*'"))]
         
         
         [(ite) (if (= arg-count 3)
                    (ite (parse (first args))
                         (parse (second args)) 
                         (parse (third args)))
                    (error "parse needs exactly 3 arguments"))]
         
         [(lam) (if (= arg-count 3)
                    (if (symbol? (first args))
                        (lam (first args) (parse-type (second args)) (parse (third args)))
                        (error "parse: lam must be followed by an identifier"))
                    (error "parse: malformed `lam'"))]
         
         [(app) (if (= arg-count 2)
                    (app (parse (first args)) (parse (second args)))
                    (error "parse: app needs 1 function and 1 argument"))]
         [(app-expr) (if (= arg-count 2)
                    (app-expr (parse (first args)) (parse (second args)))
                    (error "parse: app-expr needs 1 function and 1 argument"))]
         [(app-lazy) (if (= arg-count 2)
                    (app-lazy (parse (first args)) (parse (second args)))
                    (error "parse: app-lazy needs 1 function and 1 argument"))]
         
         [(rec) (if (= arg-count 3)
                    (if (symbol? (first args))
                        (rec (first args) (parse-type (second args)) (parse (third args)))
                        (error "parse: rec must be followed by an identifier"))
                    (error "parse: malformed `rec'"))]
         
         [(with) (let ([inner-sexp (first args)]
                       [body-sexp  (second args)])
                   (if (list? inner-sexp)
                       (case (length inner-sexp)
                         [(2)   (if (and (list? inner-sexp)
                                         (= (length inner-sexp) 2))
                                    ; extract from the inner list {<id> <E>}
                                    (let ([name       (first inner-sexp)]
                                          [named-sexp (second inner-sexp)]) 
                                      (if (symbol? name)
                                          (with name (parse named-sexp) (parse body-sexp))
                                          (error "parse: malformed `with'")))
                                    (error "parse: malformed `with'"))]
                         [else (error "parse: malformed `with'")])
                       (error "parse: malformed `with'")))]
                  
         [(pair) (if (= arg-count 2)
                     (pair (parse (first args))
                           (parse (second args)))
                     (error "parse: malformed `pair'"))]
         
         [(pair-case) (parse-pair-case arg-count args)]
         
         [(fst) (if (= arg-count 1)
                    (pair-case (parse (first args))
                               'x1
                               'x2
                               (id 'x1))
                    (error "parse: malformed `fst'"))]
         
         [(snd) (if (= arg-count 1)
                    (parse `{pair-case ,(first args) {x1 x2 => x2}})
                    (error "parse: malformed `snd'"))]

         
         [(cons)      (if (= arg-count 2)
                          (list-cons (parse (first args)) (parse (second args)))
                          (error "parse: malformed `cons'"))]
         
         [(empty)     (if (= arg-count 1)
                          (list-empty (parse-type (first args)))
                          (error "parse: malformed `empty'"))]
         
         [(list-case) (parse-list-case arg-count args)]
         
         [(ref) (if (= arg-count 2)
                       (ref (parse-type (first args)) (parse (second args)))
                       (error "parse: malformed `ref'"))]
         [(deref) (if (= arg-count 1)
                      (deref (parse (first args)))
                      (error "parse: malformed `deref'"))]
         [(setref) (if (= arg-count 2)
                       (setref (parse (first args))
                               (parse (second args)))
                       (error "parse: malformed `setref'"))]

         [(downcast) (if (= arg-count 2)
                         (downcast (parse-type (first args))
                                   (parse (second args)))
                         (error "parse: malformed `downcast'"))]

         [(record)   (record (append (map parse-field args)))]
         
         [(dot)   (if (and (= arg-count 2)
                           (symbol? (second args)))
                      (dot (parse (first args)) (second args))
                      (error "parse: malformed `dot'"))]
         
         [else (error "parse: syntax error")]))]
    
    [else (error "parse: syntax error")]))

(define (parse-field arg)
  (if (not (and (list? arg)
                (= (length arg) 2)
                (symbol? (first arg))))
      (error "parse-field: syntax error")
      (fld (first arg) (parse (second arg)))))

(define (parse-pair-case arg-count args)
  (if (= arg-count 2)
      
      (let ([scrutinee (parse (first args))]
            [inner-sexp (second args)])
        
        (if (and (list? inner-sexp)
                 (= (length inner-sexp) 4)
                 (symbol=? (third inner-sexp) '=>))
            
            (let ([name1 (first inner-sexp)]
                  [name2 (second inner-sexp)]
                  [body (parse (fourth inner-sexp))])
              
              (pair-case scrutinee name1 name2 body))
            
            (error "parse: malformed `pair-case'")))
      
      (error "parse: malformed `pair-case'")))

(define (parse-list-case arg-count args)
  (if (= arg-count 3)
      
      (let ([scrutinee (parse (first args))]
            [empty-branch-sexp (second args)]
            [cons-branch-sexp (third args)]
            )
        
        (if (and (list? empty-branch-sexp)
                 (= (length empty-branch-sexp) 3)
                 (symbol=? (first empty-branch-sexp) 'empty)
                 (symbol=? (second empty-branch-sexp) '=>))
            
            (let ([empty-branch (parse (third empty-branch-sexp))])
              
              (if (and (list? cons-branch-sexp)
                       (= (length cons-branch-sexp) 5)
                       (symbol=? (first cons-branch-sexp) 'cons)
                       (symbol? (second cons-branch-sexp))
                       (symbol? (third cons-branch-sexp))
                       (symbol=? (fourth cons-branch-sexp) '=>))
            
                  (let ([xh (second cons-branch-sexp)]
                        [xt (third cons-branch-sexp)]
                        [cons-branch (parse (fifth cons-branch-sexp))])
              
                    (list-case scrutinee empty-branch xh xt cons-branch))
                  (error "parse: malformed `list-case'")))
            (error "parse: malformed `list-case'")))
      (error "parse: malformed `list-case'")))


; Environments   env ::= Ã ̃
;                      | x=e, env          identifier x bound to expression e
;                      | b â‡’ u=e, env      b bound to recursive environment (u=e, env)
;                      | b                 self-reference to recursive environment b
;
; The recursion in the environment makes it harder to translate the above grammar
; to a define-type.  We *could* do it by using symbols as "environment variables" ("b"),
; but instead we'll do something less direct but hopefully more natural:
; the expression e will be stored in a Racket _box_.  We'll "tie the recursive knot"
; by mutating the contents of the box.
;
; So the grammar we'll use looks more like
;
; Environments   env ::= Ã˜
;                      | x=e, env          identifier x bound to expression e
;                      | u=[[??]], env     identifier u bound to a box, which could be anything
;
(define-type Env
  [env/empty]
  [env/cons-id   (id symbol?)  (bound-expr E?) (tail Env?)]
  )

(define-type Store
  [store/empty]
  [store/cons-loc  (loc symbol?) (bound-expr E?) (tail Store?)]
  )

; look-up-id : Env symbol -> (or false E)
;
; Returns a binding for symbol in environment.
;
(define (look-up-id env x)
  (type-case Env env

    [env/empty ()                      #false]

    [env/cons-id (y e env)             (if (symbol=? x y)
                                           e
                                           (look-up-id env x))]
    ))


(define (look-up-loc l)
  (unbox l))

  
(define (update-loc l v)
  (set-box! l v))



; build-> : listof Type -> Type
;
; Given (list A1 ... A(n-1) An), returns
;
;    (t/-> A1 (t/-> A2 ... (t/-> A(n-1) An)))
;
; Precondition: n >= 2
;
(define (build-> types)
  (if (= (length types) 2)
      (t/-> (first types) (second types))
      (t/-> (first types) (build-> (rest types)))))

; parse-field-type : sexp -> listof FieldType
;
(define (parse-field-type arg)
  (if (or (not (list? arg)) (< (length arg) 2))
      (error "parse-field: syntax error")
      (let* ([ids  (drop-right arg 1)]
             [A    (parse-type (last arg))]
             [ids  (map (lambda (x) (if (symbol? x) x (error "parse-field: syntax error"))) ids)]
             [flds (map (lambda (x) (field-type x A)) ids)])
        flds)
      ))

; parse-type : sexp -> Type
;
(define (parse-type sexp)
  (cond
    [(symbol? sexp)
       (case sexp
         [(Num)    (error "(t/num) is not in this version of Fun")]
         [(Pos)    (t/pos)]
         [(Int)    (t/int)]
         [(Rat)    (t/rat)]
         [(Bool)   (t/bool)]
         )]
    [(list? sexp)
       (if (empty? sexp)
           (error "parse-type: empty")
           (let*
               ([head      (first sexp)]
                [args      (rest sexp)]
                [arg-count (length args)])
             
             (case head
               [(*)       (t/* (parse-type (first args)) (parse-type (second args)))]
               [(->)      (build-> (map parse-type args))]
               [(List)    (t/list (parse-type (first args)))]
               [(Ref)     (t/ref (parse-type (first args)))]
               [(Record)  (t/record (append* (map parse-field-type args)))]
               [else   (error "unknown type constructor " head)])))]
     [else (error "unknown animal in type")]))


; racket-boolean-to-Fun-boolean : bool? -> E?
;
; Postcondition: result is bfalse or btrue

(define (racket-boolean-to-Fun-boolean b)
  (if b
      (btrue)
      (bfalse)))



; valid-binop : Op? E? E? -> boolean?
;
; valid-binop op v1 v2 returns true iff v1 and v2 are consistent with op:
;    If op is plusop or minusop, then v1 and v2 must be nums.
;    If op is equalsop or lessthanop, then v1 and v2 must be nums.
;
; Precondition: v1 and v2 are values (i.e., num, lam, bfalse, or btrue).

(define (valid-binop op v1 v2)
  (type-case Op op
    [plusop ()      (and (num? v1) (num? v2))]
    [minusop ()     (and (num? v1) (num? v2))]
    [equalsop ()    (and (num? v1) (num? v2))]
    [lessthanop ()  (and (num? v1) (num? v2))]
    
    ; This code is redundant, but it makes it easy to match an operator with
    ; its valid arguments, and is easier to extend if we add operators whose
    ; arguments aren't numbers.
    ))


; apply-binop : Op? E? E? -> E?
;
; apply-binop op v1 v2 applies op to v1 and v2, returning an expression.
; Used in interp, below.
;
; Precondition:
;    1.  v1 and v2 are values (i.e., num, lam, bfalse, or btrue).
;    2.  (valid-binop op v1 v2)

; Postcondition:
;    If op is plusop or minusop, result is a num.
;    If op is equalsop or lessthanop, result is bfalse or btrue.

(define (apply-binop op v1 v2)
  (type-case Op op
    [plusop ()      (num (+ (num-n v1) (num-n v2)))]
    [minusop ()     (num (- (num-n v1) (num-n v2)))]
    [equalsop ()    (racket-boolean-to-Fun-boolean (= (num-n v1) (num-n v2)))]
    [lessthanop ()  (racket-boolean-to-Fun-boolean (< (num-n v1) (num-n v2)))]))


; Interpreter for Fun expressions:
;
; env-interp : Env E -> E
;
; Given an E e, return v such that
;
;              env âŠ¢ e â‡“ v
;
(define (env-interp env e)
  (define (ret v) v)
  (printf "env-interp  ~a ; - ~n         âŠ¢  ~a~n"
          (unparse-env env)
          ; (unparse-store S)
          (unparse e))
  (type-case E e
    
    ; Values evaluate to themselves:
    [num (n)             (ret (num n))]
    
    [bfalse ()           (ret (bfalse))]
    [btrue ()            (ret (btrue))]
    
    [list-empty (A)
                (list-empty A)]

    [location (l)        (ret (location l))]
        
    ; Well...kind of.
    [lam (x A eB)        (ret (clo env (lam x A eB)))]
    
    [clo (env-clo body)            (ret (clo env-clo body))]
    [clo-rec (boxed-env-clo body)  (env-interp (unbox boxed-env-clo) body)]
    
    [thk (env-thk body)       (env-interp env-thk body)]
    [lazy-thk (env-thk body)  (error "lazy-thks should never be evaluated directly")]
    
    ; Non-values:
    [app (e1 e2)
         (type-case E (env-interp env e1)
           [clo (env-clo body)
                (type-case E body
                  [lam (x A eB)
                       (let ([v2 (env-interp env e2)])
                         (env-interp (env/cons-id x v2 env-clo) eB))]
                  [else (begin
                          (printf "~n~n~a~n" (unparse (env-interp env-clo body)))
                          (error "tried to apply non-lam" ))]
                         )]
           [else (error "tried to apply non-clo")])]
    
    [app-expr (e1 e2)
         (type-case E (env-interp env e1)
           [clo (env-clo body)
                (type-case E body
                  [lam (x A eB)
                       (env-interp (env/cons-id x (thk env e2) env-clo) eB)]
                  [else (begin
                          (printf "~n~n~a~n" (unparse (env-interp env-clo body)))
                          (error "tried to apply non-lam" ))]
                         )]
           [else (error "tried to apply non-clo")])]
    
    [app-lazy (e1 e2)
         (type-case E (env-interp env e1)
           [clo (env-clo body)
                (type-case E body
                  [lam (x A eB)
                       (let* ([loc            (box (lazy-thk env e2))]
                              [env-extended   (env/cons-id x (lazy-ptr loc) env-clo)])
                         (env-interp env-extended eB)
                         )]
                  [else (begin
                          (printf "~n~n~a~n" (unparse (env-interp env-clo body)))
                          (error "tried to apply non-lam" ))]
                         )]
           [else (error "tried to apply non-clo")])]
    
    [lazy-ptr (loc)
              (let ([contents (unbox loc)])
                (type-case E contents
                  [lazy-thk (env-arg e2)
                            ; CASE FOR RULE "Env-lazy-ptr"
                            ; not previously evaluated; evaluate it to v,
                            ;  and remember by replacing the contents of loc with v.
                            (let ([v (env-interp env-arg e2)])
                                              (set-box! loc v)
                                              v)]
                  [else   ; CASE FOR RULE "Env-lazy-ptr-done"
                          ; previously evaluated; just return it
                     contents]))
              ]
    
    [rec (u B e)
         ; A _box_ is like a pointer or reference to a mutable value.
         ; We need to create a closure that contains an environment
         ;   that binds the identifier u to a closure
         ;   that refers *to that same closure*.
         ;
         ; We'll do this by "tying a recursive knot".
         ;
         ; 1. Create a box with a "black hole" inside it.
         ;
         (let* ([b             (box 'BlackHole)]
                
                ; 2. Build a closure with a fake environment:
                ;
                ;bound-expr =  (clo-rec [['BlackHole]] e)
                ;
                [bound-expr    (clo-rec b e)]
                ;
                ; 3. Build an environment:
                ;
                ;env2 =              u=(clo-rec [['BlackHole]] e), env
                [env2   (env/cons-id u bound-expr                  env)])
           
           ; 4. "Tie the knot" by updating 'BlackHole to env2.
           
           (set-box! b env2)
           
           #| The environment env2 now includes a closure that refers to env2!

              env2 =    u=(clo-rec [[env2]] e), env
               â†‘                      |
               `â†---â€“----------------â†'
           |#
           
           (env-interp env2 e))
      ]
    
    [binop (op e1 e2)
           (let* ([v1 (env-interp env e1)]
                  [v2 (env-interp env e2)])
             (if (valid-binop op v1 v2)
                 (apply-binop op v1 v2)
                 (error "binop applied to invalid arguments")))]

    [with (x e1 e2)
          (let ([v1 (env-interp env e1)])
            (env-interp (env/cons-id x v1 env) e2))]
    
    [id (x)
        (let ([false-or-bound-expr  (look-up-id env x)])
          (if false-or-bound-expr
              (let ([v (env-interp env false-or-bound-expr)])
                v)
              (error "unknown identifier" x)))
        ]
    
    [ite (eCond eThen eElse)
         (let ([vCond (env-interp env eCond)])
           (type-case E vCond
             [btrue ()   (env-interp env eThen)]
             [bfalse ()  (env-interp env eElse)]
             [else (error "ite on a non-boolean")]))]

    [pair (e1 e2)
          (let* ([v1 (env-interp env e1)]
                 [v2 (env-interp env e2)])
            (pair v1 v2))]
    
    [pair-case (ePair x1 x2 eB)
               
               (let ([vPair  (env-interp env ePair)])
                 (type-case E vPair
                   [pair (v1 v2)  (env-interp (env/cons-id x2 v2 (env/cons-id x1 v1 env))
                                              eB)]
                   [else (error "pair-case on a non-pair")]))]
    
    [list-cons (eHead eTail)
               (let ([vHead  (env-interp env eHead)]
                     [vTail  (env-interp env eTail)])
                 (list-cons vHead vTail))]

    [list-case (scrutinee eEmpty xHead xTail eCons)
               (type-case E (env-interp env scrutinee)
                 [list-empty (A)   (env-interp env eEmpty)]
                 [list-cons (vHead vTail)
                            (let* ([env-xT    (env/cons-id xTail vTail env)]
                                   [env-xH-xT (env/cons-id xHead vHead env-xT)])
                              (env-interp env-xH-xT eCons))]
                 [else (error "list-case")])]
    
    [ref (A e)
         (let ([v (env-interp env e)])
           (let* (; [loc  (gensym 'LOC)]
                  [loc  (box v)]
                  ; [S2   (store/cons-loc loc v S1)]
                  )
             (location loc)))]
    
    [deref (e)
         (let ([v (env-interp env e)])
           (type-case E v
             [location (locsym)
                       (look-up-loc locsym)]
             [else (error "deref")])
           )]
    
    [setref (e1 e2)
         (let ([v1 (env-interp env e1)])
           (type-case E v1
             [location (b) 
                       (let ([v2 (env-interp env e2)])
                         (update-loc b v2)
                         v2)]
             [else (error "setref")])
           )]
    
    [downcast (A e)    (let* ([v  (env-interp env e)]
                              [B  (typeof (tc/empty) v)])
                         (if (and B
                                  (subtype? B A))
                             v
                             (error "downcast failed")))]
    
    [record (fields)
            (begin
              (define (interp-field field)
                (type-case Field field
                  [fld (name e)
                       (let ([v  (env-interp env e)])
                         (fld name v))]))
              (record (map interp-field fields)))]
    
    [dot (e name)      (let* ([v  (env-interp env e)])
                         (type-case E v
                           [record (fields)
                                   (get-field name fields)
                                   ]
                           [else (error ("dot: not record"))]
                         ))]
    ))

; get-field
;
(define (get-field key fields)
  (if (empty? fields)
      #false
      (type-case Field (first fields)
        [fld (name contents)  (if (symbol=? key name)
                                  contents
                                  (get-field key (rest fields)))]
        )))



; interp : E -> E
;
; Calls env-interp with an empty environment
;  and returns the resulting value.
(define (interp e)
  (env-interp (env/empty) e))

(define (unparse-op op)
  (type-case Op op
    [plusop ()      `+]
    [minusop ()     `-]
    [equalsop ()    `=]
    [lessthanop ()  `<]))

(define (unparse-type A)
  (type-case Type A
    [t/pos ()         `Pos]
    [t/int ()         `Int]
    [t/rat ()         `Rat]
    [t/bool ()        `Bool]
    [t/list (A)       `(List ,(unparse-type A))]
    [t/ref (A)        `(Ref ,(unparse-type A))]
    [t/*  (A1 A2)     `(*  ,(unparse-type A1) ,(unparse-type A2))]
    [t/-> (A1 A2)     `(-> ,(unparse-type A1) ,(unparse-type A2))]
    [t/record (fieldtypes) (cons 'Record (map unparse-fieldtype fieldtypes))]
    ))

(define (unparse-fieldtype ft)
  (type-case FieldType ft
    [field-type (name A)  `(,name ,(unparse-type A))]))

(define (unparse e)
  (type-case E e
    [num (n)                   n]
    [binop (op e1 e2)          `(,(unparse-op op) ,(unparse e1) ,(unparse e2))]
    [id (x)                    x]
    [with (x e1 eB)            `(with (,x ,(unparse e1)) ,(unparse eB))] 
    [lam (x A body)            `(lam ,x ,(unparse-type A) ,(unparse body))]
    [app (e1 e2)               `(app ,(unparse e1) ,(unparse e2))]
    [app-expr (e1 e2)          `(app-expr ,(unparse e1) ,(unparse e2))]
    [app-lazy (e1 e2)          `(app-lazy ,(unparse e1) ,(unparse e2))]
    [rec (u B body)            `(rec ,u ,(unparse-type B) ,(unparse body))]
    [bfalse ()                 `bfalse]
    [btrue ()                  `btrue]
    [ite (e e1 e2)             `(ite ,(unparse e) ,(unparse e1) ,(unparse e2))]
    [pair (e1 e2)              `(pair ,(unparse e1) ,(unparse e2))]
    [pair-case (e x1 x2 body)  `(pair-case ,(unparse e) (,x1 ,x2 => ,(unparse body)))]
    [list-empty (A)            `(list ,(unparse-type A))]
    [list-cons (e1 e2)         `(cons ,(unparse e1) ,(unparse e2))]
    [list-case (e eEmpty xh xt eCons)
               `(list-case ,(unparse e)
                           (empty      => ,(unparse eEmpty))
                           (cons ,xh ,xt => ,(unparse eCons)))]
    [ref (A e1)                `(ref ,(unparse-type A) ,(unparse e1))]
    [deref (e1)                `(deref ,(unparse e1))]
    [setref (e1 e2)            `(setref ,(unparse e1) ,(unparse e2))]
    [location (l)              `(locationã€š,(unparse (unbox l))ã€›)]
    
    [clo (env e)               `(clo ,(unparse-env env) ,(unparse e))]
    [thk (env e)               `(thk ,(unparse-env env) ,(unparse e))]
    [lazy-thk (env e)          `(lazy-thk ,(unparse-env env) ,(unparse e))]
    [lazy-ptr (l)              `(lazy-ptrã€š,(unparse (unbox l))ã€›)]
    [clo-rec (b e)
               (let ([contents (unbox b)])
                 (set-box! b 'StopSpinning)
                 (let ([result `(clo-rec ,(unparse-env contents) ,(unparse e))])
                   (set-box! b contents)
                   result))
               ]
    [downcast (A e)            `(downcast ,(unparse-type A) ,(unparse e))]
    [record (fields)           `(record ,(append* (map unparse-field fields)))]
    [dot (e name)              `(dot ,(unparse e) ,name)
         ]
    ))

(define (unparse-field field)
  (type-case Field field
    [fld (name e)    `(,name ,(unparse e))]))

(define (unparse-env env)
  (if (and (symbol? env) (symbol=? env 'StopSpinning))
      `SELF
      (type-case Env env
        [env/empty ()               `Ã˜]
        [env/cons-id (x e env)      `(,x = ,(unparse e) then ,(unparse-env env))]
        )))

; look-up-type : Typing-context symbol -> Type
;
(define (look-up-type context x)
  (type-case Typing-context context
    [tc/empty ()  (error "look-up-type: not in scope: " x)]
    [tc/cons-tp (y A context)       (if (symbol=? x y)
                                        A
                                        (look-up-type context x))]
    ))

; atomic-subtype? : Type Type -> boolean
;
; Handles subtyping for atomic types (Pos, Int, etc.).
;
(define (atomic-subtype? A B)
  (or
   (equal? A B)               ; redundant, but avoids questions about "why is (atomic-subtype? (t/int) (t/int)) false?"
   (and (t/pos? A) (t/int? B))
   (and (t/pos? A) (t/rat? B))
   (and (t/int? A) (t/rat? B))
   ))

; subtype? : Type Type -> boolean
;
(define (subtype? A B)
  (and A         ; weed out stray #false results
       B
       (or
        (equal? A B)     ; Sub-refl
        ; try atomic subtyping
        (atomic-subtype? A B)
        ; try record subtyping (Problem 2)
        (type-case Type B
          [t/record (Bflds)
                  
                     (type-case Type A
                      [t/record (Aflds)

                                

                                (let* ([Anames        (get-field-names Aflds)]
                                       [Bnames        (get-field-names Bflds)])
                                  (if (= 1 (length Bnames))
                                      (foldl (lambda (x result) (or x result)) #f
                                             (map (lambda (arg)                                          
                                                    (if (symbol=? (first Bnames) arg )
                                                        (subtype? (get-field-type arg Aflds) (get-field-type (first Bnames) Bflds))
                                                        #f))
                                                  Anames))
                                     (foldl (lambda (y result) (and y result)) #t (map (lambda (a)
                                            (subtype? A (t/record (list a))))
                                            Bflds))))]
                       [else #f])]

          
          
          [else
           ; if that doesn't work, try the other rules
           (type-case Type A
             ; [t/bool () handled by else branch]
             [t/* (A1 A2)   (type-case Type B [t/* (B1 B2)   (and (subtype? A1 B1)
                                                                  (subtype? A2 B2))]
                              [else #f])]
             
             [t/-> (A1 A2)   (type-case Type B [t/-> (B1 B2)  (and (subtype? B1 A1)  ; contravariant
                                                                   (subtype? A2 B2))]
                               [else #f])]
             
             [t/list (A0)   (type-case Type B
                              [t/list (B0)     (subtype? A0 B0)]
                              [else #f])]
             
             [t/ref (A0)    (type-case Type B
                              [t/ref (B0)      (and (subtype? A0 B0)
                                                    (subtype? B0 A0))
                                     ]
                              [else #f])]
             [else #f])]
          ))))

; get-field-names : (listof FieldType) -> (listof symbol)
;
(define (get-field-names fieldtypes)
  (map (lambda (fieldtype) (type-case FieldType fieldtype
                             [field-type (f A)  f]))
       fieldtypes))

; intersection : (listof symbol) (listof symbol) -> (listof symbol)
;
(define (intersection list1 list2)
  (if (empty? list1)
      empty
      (let ([h  (first list1)]
            [t  (rest list1)])
        (if (member h list2)
            (cons h (intersection t list2))
            (intersection t list2)))))
  
; build-upper-bound : (listof FieldType) (listof FieldType) (listof symbol)
;                  -> (or false (listof FieldType))
(define (build-upper-bound Afields Bfields common-names)
  (if (empty? common-names)
      empty
      (let* ([h         (first common-names)]
             [t         (rest common-names)]
             
             [Atype     (get-field-type h Afields)]
             [Btype     (get-field-type h Bfields)]
             ; field type (h : Atype) in Afields
             ; field type (h : Btype) in Bfields
             [AB-upper  (upper-bound Atype Btype)])
        (if (false? AB-upper)
            ; A and B have no upper bound, so leave this field out of the result
            (build-upper-bound Afields Bfields t)
            ; add this upper bound
            (cons (field-type h AB-upper) (build-upper-bound Afields Bfields t)))
        )))
    
; try-record-upper-bound : Type Type -> (or false Type)
;
; If either type is not Record, returns false.
; Otherwise, returns the Record whose fields are the intersection
; of the sets of fields of each record, and whose individual field types
; are the upper-bound of each record type.
;
(define (try-record-upper-bound A B)
  (type-case Type A
    [t/record (Afields)
      (type-case Type B
        [t/record (Bfields)
          ; A = Record Afields,   B = Record Bfields
          ;
          ; 1. Get all the field names in common.
          (let* ([Anames        (get-field-names Afields)]
                 [Bnames        (get-field-names Bfields)]
                 [common-names  (intersection Anames Bnames)])
            ; 2. Build the upper bound.
            (t/record (build-upper-bound Afields Bfields common-names)))
          ]
        [else #f])]
    [else #f])
  )

; upper-bound : Type Type -> (or false Type)
;
(define (upper-bound A B)
  (and A     ; weed out stray #false results
       B
       (if (subtype? A B)
           B              ; A <: B, so upper bound of A and B is B
           (if (subtype? B A)
               A          ; B <: A, so upper bound of A and B is A
               
               ; neither A <: B nor B <: A;
               ; however, with records there may be an upper bound
               (try-record-upper-bound A B)))))

; lower-bound : Type Type -> (or false Type)
;
(define (lower-bound A B)
  (if (false? A)
      B
      (if (false? B)
          A
          (if (subtype? A B)
              A              ; A <: B, so lower bound of A and B is A
              (if (subtype? B A)
                  B          ; B <: A, so lower bound of A and B is B
                  #false)))))


; type=? : Type Type -> boolean
;
(define (type=? A B)
  (and A         ; weed out stray #false results
       B
       (type-case Type A
         ; [t/num ()  handled by else branch]
         ; [t/bool () handled by else branch]
         [t/* (A1 A2)   (type-case Type B [t/* (B1 B2)   (and (type=? A1 B1)
                                                              (type=? A2 B2))]
                          [else #f])]
         
         [t/-> (A1 A2)  (type-case Type B [t/-> (B1 B2)  (and (type=? B1 A1)
                                                              (type=? A2 B2))]
                          [else #f])]
         [t/list (A0)   (type-case Type B
                          [t/list (B0)     (type=? A0 B0)]
                          [else #f])]
         [t/ref (A0)    (type-case Type B
                          [t/ref (B0)     (type=? A0 B0)]
                          [else #f])]
         [else    
          (equal? A B)])))


; op-signature : Op -> Type
;
(define (op-signature op)
  (let* ([rat*rat        (t/* (t/rat) (t/rat))]
         [int*int        (t/* (t/int) (t/int))]
         [pos*pos        (t/* (t/pos) (t/pos))]
         
         [rat*rat->rat   (t/-> rat*rat (t/rat))]
         [int*int->int   (t/-> int*int (t/int))]
         [pos*pos->pos   (t/-> pos*pos (t/pos))]
         
         [rat*rat->bool  (t/-> rat*rat (t/bool))])
    (type-case Op op
      [plusop ()     (list pos*pos->pos int*int->int rat*rat->rat)]
      [minusop ()    (list int*int->int rat*rat->rat)]
      [lessthanop () (list rat*rat->bool)]
      [equalsop ()   (list rat*rat->bool)]
    )))



(define (typeof-app tc eFun eArg)
  (let* ([AFun (typeof tc eFun)]
         [AArg (typeof tc eArg)])
    (and AFun
         (type-case Type AFun
           [t/-> (A1 A2)  (if (subtype? AArg A1)   ; subtype call
                              A2
                              #false)]
           [else          #false]))))

;
; typeof : Typing-context E -> (or false Type)
;
(define (typeof tc e)
  (type-case E e
    
    [num (n)               (if (not (rational? n))   ; sadly, even Racket's definition of rational is interesting
                               #false
                               (if (not (exact-integer? n))
                                   (t/rat)
                                   (if (not (>= n 0))
                                       (t/int)
                                       (t/pos)))
                               )]
    
    [binop (op e1 e2)      (let* ([A1 (typeof tc e1)]
                                  [A2 (typeof tc e2)])
                             (define (try-op-type AOp)
                               (type-case Type AOp
                                 [t/-> (domain range)
                                       (if (subtype? (t/* A1 A2) domain)
                                           range
                                           #false)]
                                 [else (error "strange op signature: " op " : " (op-signature op))]))
                             (and A1
                                  A2
                                  (let* ([ranges_or_falses  (map try-op-type (op-signature op))]
                                         [ranges            (filter (lambda (x) (not (false? x))) ranges_or_falses)])
                                    (foldl lower-bound (first ranges) (rest ranges)))
                                  ))]
    
    [bfalse ()             (t/bool)]
    [btrue ()              (t/bool)]
    
    [ite (e eThen eElse)   (and (subtype? (typeof tc e) (t/bool))    ; subtype call
                                (let ([AThen (typeof tc eThen)]
                                      [AElse (typeof tc eElse)])
                                  ; (and (type=? AThen AElse)
                                  ;     AThen)
                                  (upper-bound AThen AElse)
                                  ))]
    
    [id (x)                (let ([A (look-up-type tc x)])
                               (or A
                                   (begin
                                     (printf "unbound identifier ~v~n" x)
                                     #false)))]
    
    [with (x e eBody)      (let ([A (typeof tc e)])
                             (and A
                                  (let* ([tc-extended  (tc/cons-tp x A tc)]
                                         [B            (typeof tc-extended eBody)])
                                    B)))]
    
    [lam (x A eBody)       (let* ([tc-extended  (tc/cons-tp x A tc)]
                                  [B (typeof tc-extended eBody)])
                             (and B
                                  (t/-> A B)))]
    
    [rec (u B eBody)       (let* ([tc-extended  (tc/cons-tp u B tc)]
                                  [B2 (typeof tc-extended eBody)])
                             (and (type=? B B2)
                                  B))]
    
    [app (eFun eArg)       (typeof-app tc eFun eArg)]
    [app-expr (eFun eArg)  (typeof-app tc eFun eArg)]
    [app-lazy (eFun eArg)  (typeof-app tc eFun eArg)]
    
    [pair (e1 e2)          
                           (let* ([A1 (typeof tc e1)]
                                  [A2 (typeof tc e2)])
                             (and A1
                                  A2
                                  (t/* A1 A2)))
                           ]
    
    [pair-case (e x1 x2 eBody)
                           (let* ([Ae (typeof tc e)])
                             (and Ae
                                  (type-case Type Ae
                                    [t/* (A1 A2)  (let* ([tc-ext1 (tc/cons-tp x1 A1 tc)]
                                                         [tc-ext2 (tc/cons-tp x2 A2 tc-ext1)])
                                                    (typeof tc-ext2 eBody))]
                                    [else         #false])))
                           ]
                           
    [list-empty (A)        (t/list A)]
    [list-cons (e1 e2)     
                           (let* ([A1 (typeof tc e1)]
                                  [A2 (typeof tc e2)])
                             (and A1
                                  A2
                                  (upper-bound (t/list A1) A2)    ; had (t/list A2) before
                                  ;(if (type=? (t/list A1) A2)
                                  ;    (t/list A1)
                                  ;    #false)
                                  ))
                           ]
    
    [list-case (e eEmpty xh xt eCons)
               (let ([Ae  (typeof tc e)])
                 (and Ae
                      (type-case Type Ae
                        [t/list (A)  (let* ([AEmpty  (typeof tc eEmpty)]
                                            [tc-ext1 (tc/cons-tp xh A          tc     )]
                                            [tc-ext2 (tc/cons-tp xt (t/list A) tc-ext1)]
                                            [ACons   (typeof tc-ext2 eCons)])
                                       ; (and (type=? AEmpty ACons)
                                       ;      AEmpty)
                                       (upper-bound AEmpty ACons)
                                       )]
                        [else        #false])))
     ]
    
    [ref (A e)
         (let ([B (typeof tc e)])
           (and B
                (subtype? B A)
                (t/ref A)))
         ]
    [deref (eRef)
           (let ([ARef (typeof tc eRef)])
             (and ARef
                  (type-case Type ARef
                    [t/ref (A)   A]
                    [else        #false])))
           ]
    [setref (eRef e)
            (let ([ARef (typeof tc eRef)])
              (and ARef
                   (type-case Type ARef
                     [t/ref (A)  (let ([Ae (typeof tc e)])
                                   (and (subtype? Ae A)
                                        Ae))]
                     [else       #false])))
            ]
    
    [downcast (A e)
              (let ([B  (typeof tc e)])
                (and B   ; don't care what B is, as long as it's well-typed
                     A))]
    
    [record (fields)
            (if (empty? fields)
                (t/record empty)
                (type-case Field (first fields)
                  [fld (f1 contents)
                       (let ([A1 (typeof tc contents)]
                             [Arest (typeof tc (record (rest fields)))])
                         (and A1
                              Arest
                              (type-case Type Arest
                                [t/record (Arest)
                                          (t/record (cons (field-type f1 A1) Arest))]
                                [else (error "impossible")]))
                         )])
                )]
    
    [dot (e name)      (let ([Arecord  (typeof tc e)])
                         (and Arecord
                              (type-case Type Arecord
                                [t/record (field-types)   
                                          (get-field-type name field-types)]
                                [else #false])
                              ))]
         
                  
    [clo (env e)       (error "typeof: clo: not handled")]
    [clo-rec (env e)   (error "typeof: clo-rec: not handled")]
    [thk (env e)       (error "typeof: thk: not handled")]
    [lazy-ptr (loc)    (error "typeof: lazy-ptr: not handled")]
    [lazy-thk (env e)  (error "typeof: lazy-thk: not handled")]
    [location (loc)    (error "typeof: location: not handled")]
    ))

; get-field-type
;
(define (get-field-type key field-types)
  (if (empty? field-types)
      #false
      (type-case FieldType (first field-types)
        [field-type (name A)  (if (symbol=? key name)
                                  A
                                  (get-field-type key (rest field-types)))]
        )))

(define (typeof-program e)
  (typeof (tc/empty) e))





(typeof-program (parse '{ite bfalse {with {x btrue} x} {with {y bfalse} y}}))
(interp         (parse '{ite bfalse {with {x btrue} x} {with {y bfalse} y}}))

; (typeof-program (parse '{ite bfalse {with {x btrue} x} y}))   ; y not in scope
; (interp         (parse '{ite bfalse {with {x btrue} x} y}))

; (typeof-program (parse '{ite btrue {with {x btrue} x} y}))  ; y not in scope
(interp         (parse '{ite btrue {with {x btrue} x} y}))

(typeof-program (parse '{ite bfalse {with {x btrue} x} {with {y 3} y}}))
(interp         (parse '{ite bfalse {with {x btrue} x} {with {y 3} y}}))


(typeof-program
       (parse '{with*
         {{multiply {rec m
                         {-> Rat Rat Rat}
                         {lam x Rat {lam y Rat {ite {= y 0}
                                                    0
                                                    {ite {= y 1}
                                                         x
                                                         {+ x {app {app m x} {- y 1}}}}}}}}}
          {fact {rec u {-> Rat Rat} {lam n Rat {ite {< n 2}
                                    1
                                    {with {c {app u {- n 1}}}
                                          {app {app multiply n} c}}}}}}
         }
         {app fact 5}}))


; (typeof-program (lam 'x (t/pos) (binop (plusop) (id 'x) (id 'x))))
(typeof-program (parse '{lam x Pos {+ x x}}))

(interp (parse '{setref {ref Rat 0} -66}))

(typeof-program (parse '{ref Pos 0}))               ;

(typeof-program (parse '{setref {ref Pos 0} 3}))    ;   :-)

(typeof-program (parse '{setref {ref Int 0} -3}))   ;   :-)

(typeof-program (parse '{cons -3.5 {empty Pos}}))  ;  : List Rat
(typeof-program (parse '{cons 3.5 {empty Pos}}))   ;  : List Rat
(typeof-program (parse '{cons -3 {empty Pos}}))    ;  : List Int
(typeof-program (parse '{cons 3 {empty Pos}}))     ;  : List Pos
(typeof-program (parse '{cons -2 {cons 3 {empty Pos}}}))     ;  : List Int

(typeof-program (parse '{downcast Pos 2}))      ; : Pos
(typeof-program (parse '{downcast Rat 2}))      ; useless, but well-typed
(typeof-program (parse '{downcast Rat -2.5}))   ; : Rat
(typeof-program (parse '{downcast Pos -3}))     ; : Pos, but evaluation will fail since -3 is not Pos

(typeof-program (parse '{with {to-pos {lam x Int {ite {< -1 x}
                                                      0
                                                      {downcast Pos x}}}}
                              {pair {app to-pos 5}
                                    {app to-pos -3}}}))

(interp (parse '{with {to-pos {lam x Int {ite {< x 0}
                                              0
                                              {downcast Pos x}}}}
                      {pair {app to-pos 5}
                            {app to-pos -3}}}))

; subtype-parse : sexp sexp -> boolean
;
(define (subtype-parse A-sexp B-sexp)
  (subtype? (parse-type A-sexp) (parse-type B-sexp)))

#|
  Problem 1a

  Write your solution here:





  ...
  ---------------------------------------------------------
               (Int * Bool) <: (Bool * Rat)
|#

#|
  Problem 1b

  Define your expression e below.
  Either use (parse '{...}) on concrete syntax, or write
  abstract syntax directly.
  You can use the identifiers x1 and x2 (or, in abstract syntax, (id 'x1) and (id 'x2)),
  which are bound in ePaircase below.
|#

(define part1b-e (num 0))   ; replace num 0 with your expression e

(define ePaircase (pair-case (pair (num -3) (bfalse)) 'x1 'x2 part1b-e))




"test upper-bound"
; incompatible z fields; z field dropped:
(typeof-program (parse '{ite btrue
                             {record {x 1} {y -3} {z bfalse}}
                             {record {x 5} {y 9.5} {z 0}}}))

; compatible z fields; z field kept:
(typeof-program (parse '{ite btrue
                             {record {x 1} {y -3} {z -1.5}} 
                             {record {x 5} {y 9.5} {z 0}}}))

; no fields in common; record type with no fields:
(typeof-program (parse '{ite btrue
                             {record {x 1} {y -3} {z -1.5}}
                             {record {aa 5} {bb 9.5}}}))


"start record subtyping tests"
(subtype-parse 'Int '{Record})
(subtype-parse '{Record {x Pos} {y Int} {z Rat}}
               '{Record {x Pos} {y Int} {z Rat}})

(subtype-parse '{Record {x Pos} {y Int} {z Rat}}
               '{Record {x Pos} {z Rat} {y Int}})  ; should succeed (permutation)

(subtype-parse '{Record {x Pos} {y Int} {z Rat}}
               '{Record {x Rat} {y Rat} {z Rat}})  ; should succeed (depth)

(subtype-parse '{Record {x Pos} {y Int} {z Rat}}
               '{Record {x Rat} {y Pos} {z Rat}})  ; should fail

"width:"
(subtype-parse '{Record {x Pos} {y Pos} {z Rat}}
               '{Record {x Rat}         {z Rat}})  ; should succeed (width)

"width + depth:"
(subtype-parse '{Record {x Pos} {y Pos} {z Rat}}
               '{Record {x Int}         {z Rat}})  ; should succeed (width + depth)

"should fail:"
(subtype-parse '{Record {x Int}         {z Rat}}
               '{Record {x Pos} {y Pos} {z Rat}})  ; should fail (width reversed)


