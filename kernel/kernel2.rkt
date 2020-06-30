#lang racket
(module+ test (require rackunit))

; Immutable Kernel

(define kernel-obj?
  (or/c
   symbol?
   void?
   boolean?
   (recursive-contract kernel-list?)
   (recursive-contract kernel-env?)
   (recursive-contract kernel-op?)
   (recursive-contract kernel-ap?)))

(define kernel-list? (listof kernel-obj?))

; Environments
(define kernel-binding-set? (hash/c symbol? kernel-obj? #:immutable #f))
(struct kernel-env (local-bindings parents) #:transparent)
(provide (contract-out [struct kernel-env ([local-bindings kernel-binding-set?] [parents (listof kernel-env?)])]))

(define (kernel-env-get env var)
  (match env
    [(kernel-env local-bindings parents)
     (hash-ref local-bindings
               var
               (ormap (curryr kernel-env-get var) parents))]))

(provide (contract-out [kernel-env-get (-> kernel-env? symbol? (or/c kernel-obj? #f))]))

(module+ test
  (check-equal? (kernel-env-get (kernel-env (hash 'x 0) '()) 'x) 0)
  (check-equal? (kernel-env-get (kernel-env (hash 'x 0) (list (kernel-env (hash 'y 1) '()))) 'y) 1)
  (check-equal? (kernel-env-get (kernel-env (hash 'x 0) (list (kernel-env (hash 'y 1) '()) (kernel-env (hash 'z 2) '()))) 'z) 2)
  (check-equal? (kernel-env-get (kernel-env (hash 'x 0) (list (kernel-env (hash 'y 1) '()) (kernel-env (hash 'x 2) '()))) 'x) 0))

(define param-tree?
  (flat-rec-contract
   param-tree?
   symbol?
   '|#ignore|
   null?
   (cons/c param-tree? param-tree?)))

(define (bind-param-tree param-tree obj-tree hash)
  (match (cons param-tree obj-tree)
    [(cons (? symbol? var) _)
     (hash-set! hash var obj-tree)]
    [(cons '|#ignore| _)
     (void)]
    [(cons '() '())
     (void)]
    [(cons (cons param-car param-cdr) (cons obj-car obj-cdr))
     (bind-param-tree param-car obj-car hash)
     (bind-param-tree param-cdr obj-cdr hash)]
    [_ (raise-arguments-error 'bind-param-tree "cannot match parameter tree to object tree" "parameter tree" param-tree "object tree" obj-tree)]))

(provide (contract-out [bind-param-tree (-> param-tree? kernel-obj? kernel-env? void?)]))

; Operatives
(struct kernel-op (fn) #:transparent)
(provide (contract-out [struct kernel-op ([fn (-> kernel-obj? kernel-env? kernel-obj?)])]))

; Applicatives
(struct kernel-ap (op) #:transparent)
(provide (contract-out [struct kernel-ap ([op kernel-op?])]))

; The inert object
(define kernel-inert '|#inert|)
(define kernel-inert? (or/c kernel-inert))

; Evaluation
(define (kernel-eval exp env)
  (match exp
    [(== kernel-inert)
     (void)]
    [(? (or/c void? boolean? kernel-env? kernel-op? kernel-ap?) val)
     val]
    [(? symbol? var)
     (or (kernel-env-get env var)
         (raise-arguments-error 'kernel-eval "unbound variable" "variable" var "environment" env))]
    [(cons operator operand-tree)
     (let ([combiner (kernel-eval operator env)])
       (match combiner
         [(kernel-op combiner)
          (combiner operand-tree env)]
         [(kernel-ap combiner)
          (match operand-tree
            [(list operands ...)
             (let ([args (map (curryr kernel-eval env) operands)])
               (kernel-eval (cons combiner args) env))]
            [_ (raise-arguments-error 'kernel-eval "applicative applied to operand tree which is not a list" "operand tree" operand-tree)])]
         [_ (raise-arguments-error 'kernel-eval "head of combination is not combiner" "head" combiner)]))]
    [_ (raise-arguments-error 'kernel-eval "expression is not evaluable" "expression" exp)]))

(module+ test
  (check-equal? (kernel-eval (list 'boolean? #t) kernel-ground) #t))

(provide (contract-out [kernel-eval (-> kernel-obj? kernel-env? kernel-obj?)]))

(define (kernel-eval-ap args env)
  (match args
    [(list arg) (kernel-eval arg env)]
    [_ (raise-arguments-error 'eval "wrong number of arguments" "expected" 1 "got" (length args))]))

(provide (contract-out [kernel-eval-ap (-> (list/c kernel-obj?) kernel-env? kernel-obj?)]))

; Primitive special forms

(define (kernel-vau operands static-env)
  (match operands
    [(list param-tree dynamic-env-param body)
     (kernel-op
      (λ (operand-tree dynamic-env)
        (let ([local-env (kernel-env (make-hash) (list static-env))])
          (bind-param-tree param-tree operand-tree local-env)
          (bind-param-tree dynamic-env-param dynamic-env local-env)
          (kernel-eval body local-env))))]
    [_ (raise-arguments-error "invalid operand tree, expected list of length 3" "operand tree" operands)]))

(provide (contract-out [kernel-vau (-> (list/c param-tree? symbol? kernel-obj?) kernel-env? kernel-op?)]))

(define (kernel-define operands env)
  (match operands
    [(list param-tree obj-exp)
     (bind-param-tree
      param-tree
      (kernel-eval obj-exp env)
      (kernel-env-local-bindings env))
     kernel-inert]
    [_ (raise-arguments-error '$define! "invalid operand tree, expected list of length 2" "operand tree" operands)]))

(provide (contract-out [kernel-define (-> (list/c param-tree? kernel-obj?) kernel-env? kernel-inert?)]))
  
(define (kernel-if operands env)
  (match operands
    [(list cond-exp then-exp else-exp)
     (let ([cond-val (kernel-eval cond-exp env)])
       (match cond-val
         [#t (kernel-eval then-exp env)]
         [#f (kernel-eval else-exp env)]
         [_ (raise-arguments-error '$if "condition does not evaluate to a boolean value" "value" cond-val)]))]
    [_ (raise-arguments-error '$if "invalid operand tree, expected list of length 3" "operand tree" operands)]))

(provide (contract-out [kernel-if (-> (list/c kernel-obj? kernel-obj? kernel-obj?) kernel-env? kernel-obj?)]))

(define (kernel-op-simp fn)
  (kernel-op (λ (args env) (apply fn args))))

(provide (contract-out [kernel-op-simp (-> (-> kernel-obj? ... kernel-obj?) kernel-op?)]))

(define (kernel-ap-simp fn)
  (kernel-ap (kernel-op-simp fn)))

(provide (contract-out [kernel-ap-simp (-> (-> kernel-obj? ... kernel-obj?) kernel-ap?)]))

(define (kernel-op-arity name arity fn)
  (kernel-op
   (λ (args env)
     (let ([arg-count (length args)])
       (if (= arg-count arity)
           (apply fn args)
           (raise-arguments-error name "wrong number of arguments" "expected" arity "got" arg-count))))))

(provide (contract-out [kernel-op-arity (-> symbol? exact-nonnegative-integer? (-> kernel-obj? ... kernel-obj?)
                                            kernel-op?)]))

(define (kernel-ap-arity name arity fn)
  (kernel-ap (kernel-op-arity name arity fn)))

(provide (contract-out [kernel-ap-arity (-> symbol? exact-nonnegative-integer? (-> kernel-obj? ... kernel-obj?)
                                            kernel-ap?)]))

(define kernel-ground
  (kernel-env
   (hash
    '$vau (kernel-op kernel-vau)
    '$define! (kernel-op kernel-define)
    '$if (kernel-op kernel-if)
    'equal? (kernel-ap-arity 'equal? 2 equal?)
    'inert? (kernel-ap-arity 'inert? 1 void?)
    'boolean? (kernel-ap-arity 'boolean? 1 boolean?)
    'symbol? (kernel-ap-arity 'symbol? 1 symbol?)
    'pair? (kernel-ap-arity 'pair? 1 pair?)
    'null? (kernel-ap-arity 'null? 1 null?)
    'cons (kernel-ap-arity 'cons 2 cons)
    'environment? (kernel-ap-arity 'environment? 1 kernel-env?)
    'eval (kernel-ap (kernel-op kernel-eval-ap))
    'make-environment (kernel-ap-simp (λ envs (kernel-env (hash envs))))
    'operative? (kernel-ap-arity 'operative? 1 kernel-op?)
    'applicative? (kernel-ap-arity 'applicative? 1 kernel-ap?)
    'wrap (kernel-ap-arity 'wrap 1 kernel-ap)
    'unwrap (kernel-ap-arity 'unwrap 1 kernel-ap-op))
   '()))

(define (kernel-#%app operator . operands)
  (kernel-eval (cons operator operands) kernel-ground))

(define (kernel-#%top . exp) (kernel-eval exp kernel-ground))

; eugh, this doesn't work, i give up, i'll just write the parser myself
(provide #%module-begin
         #%top-interaction
         (rename-out [kernel-#%app #%app]
                     [kernel-#%top #%top]
                     [kernel-#%top #%datum]))