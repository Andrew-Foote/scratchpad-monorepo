#lang racket
(require racket/hash)
(module+ test
  (require rackunit))

(define kernel-list? (listof (recursive-contract kernel-exp?)))
(define kernel-env? (list/c (hash/c symbol? (recursive-contract kernel-exp?))))
(define kernel-op? (-> (recursive-contract kernel-exp?) kernel-env? (recursive-contract kernel-exp?)))

(struct kernel-ap (op) #:transparent)
(provide (contract-out [struct kernel-ap ([op kernel-op?])]))

(define kernel-exp?
  (or/c symbol?
        kernel-list?
        kernel-env?
        kernel-op?
        kernel-ap?))

(define (kernel-env-get env sym)
  (match env
    ['()
     (raise-arguments-error 'kernel-env-get "unbound symbol" "symbol" sym)]
    [(cons inner-hash outer-hashes)
     (hash-ref inner-hash sym (thunk (kernel-env-get outer-hashes sym)))]))

(provide (contract-out [kernel-env-get (-> kernel-env? symbol? kernel-exp?)]))

(module+ test
  (check-equal? (kernel-env-get (list (hash 'x '())) 'x) '())
  (check-equal? (kernel-env-get (list (hash) (hash 'x '())) 'x) '()))

(define (kernel-apply fun args env)
  (match fun
    [(kernel-ap op) (op (map (curryr kernel-eval env) args) env)]
    [_ (fun args env)]))

(provide (contract-out [kernel-apply (-> (or/c kernel-op? kernel-ap?) kernel-exp? kernel-env?)]))

(define (kernel-eval exp env)
  (match exp
    [(? symbol? sym)
     (kernel-env-get env sym)]
    [(cons fun args)
     (kernel-apply (kernel-eval fun env) args env)]))

(provide (contract-out [kernel-eval kernel-op?]))

(define (kernel-op param static-env)
  (match-let ([(list arg-param dynamic-env-param body) param])
    (λ (arg dynamic-env)
      (let ([env (hash-set* static-env arg-param arg dynamic-env-param dynamic-env)])
        (kernel-eval body env)))))

(provide (contract-out [kernel-op kernel-op?]))

(define (kernel-make-simple-op proc)
  (λ (arg env) (proc arg)))

(provide (contract-out [kernel-make-simple-op (-> (-> kernel-exp? kernel-exp?) kernel-op?)]))

(define (kernel-op-static params env)
  (match-let ([(list arg-params body) params])
    (kernel-op (list arg-params '_ body) env)))

(define (kernel-ap-dynamic params static-env)
  (kernel-ap (kernel-op params static-env)))

(define (kernel-make-simple-ap proc)
  (kernel-ap (kernel-make-simple-op proc)))
                       
(define kernel-op->ap (kernel-make-simple-ap

(define (kernel-op->ap op)
  `(ap ,op))

(define kernel-std-env
  (list
   (hash
    'op (λ (exp static-env)
          (match-let ([(list params dynamic-env-param body) exp])
            (λ (args dynamic-env)
              (kernel-eval
               body
               (cons
                (hash-set
                 (make-immutable-hash (map cons params args))
                 dynamic-env-param dynamic-env)
                static-env)))))
    'op->ap `(ap ,(λ (op env)
                    `(ap ,op)))
    'ap (λ (exp static-env)
          `(op->ap (op ,exp ,static-env))))))