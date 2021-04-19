#lang racket
(require rackunit)

(define term?
  (flat-rec-contract
   term?
   symbol?
   (list/c term? term?)
   (list/c 'λ symbol? term?)
   (list/c 'call/cc term?)))

(define (free-vars t)
  (match t
    [(? symbol? _)
     (set t)]
    [`(λ ,x ,t)
     (set-remove (free-vars t) x)]
    [`(call/cc ,t)
     (free-vars t)]
    [`(,t ,u)
     (apply set-union (map free-vars `(,t ,u)))]
    ['()
     (set)]))

(define (free? x t)
  (set-member? (free-vars t) x))

(define var-letters
  #(x y z w v u a b c d t s r p q k f g h e m n j i l o))

(define (fresh-var xs)
  (define (iter n)
    (let*-values ([(q r) (quotient/remainder n 26)]
                  [(x) (string->symbol
                        (string-append
                         (symbol->string (vector-ref var-letters r))
                         (if (zero? q)
                             ""
                             (number->string q))))])
      (if (set-member? xs x)
          (iter (+ n 1))
          x)))
  (iter 0))

(define (subst t x u)
  (match u
    [(== x)
     t]
    [(? symbol? _)
     u]
    [`(call/cc ,u)
     `(call/cc ,(subst t x u))]
    [`(λ ,y ,v)
     (cond [(not (free? x u)) u]
           [(not (free? y t)) `(λ ,y ,(subst t x v))]
           [else
            (define z (fresh-var (set-union (free-vars t) (free-vars v))))
            `(λ ,z ,(subst t x (subst z y v)))])]
    [`(,_ ,_)
     (map (curry subst t x) u)]))

(define context?
  (flat-rec-contract
   context?
   '()
   (list/c term? context?)
   (list/c context? term?)
   (list/c 'λ symbol? context?)
   (list/c 'call/cc context?)))

(define (fill c t)
  (match c
    ['()
     t]
    [`(λ ,x ,c)
     `(λ ,x ,(fill c t))]
    [`(call/cc ,c)
     `(call/cc ,(fill c t))]
    [`(,(? context? c) ,u)
     `(,(fill c t) ,u)]
    [`(,u ,(? context? c))
     `(,u ,(fill c t))]))

(define (reduce t [c '()])
  (displayln (format "(reduce ~a ~a)" t c))
  (match t
    [(? symbol? _)
     (fill c t)]
    [`(λ ,x ,t)
     (reduce t (fill c `(λ ,x ())))]
    [`((λ ,x ,t) ,u)
     (reduce (subst u x t) c)]
    [`(call/cc ,t)
     (define x (fresh-var (free-vars c)))
     (reduce `(,t (λ ,x ,(fill c x))) '())]
    [`(,(? reducible? t), u)
     (reduce t (fill c `(() ,u)))]
    [`(,t ,u)
     (reduce u (fill c `(,t ())))]))
     
(define (reducible? t)
  (match t
    [(or (? symbol? _) `(λ ,_ ,_))
     #f]
    [`(or (call/cc ,_) `((λ ,_ ,_) ,_))
     #t]
    [`(,_ ,_)
     (ormap reducible? t)]))

(module+ test
  (check-equal? (reduce 'x) 'x)
  (check-equal? (reduce '(λ x (x x))) '(λ x (x x)))
  (check-equal? (reduce '((λ x (x x)) y)) '(y y))
  (check-equal? (reduce '((λ x (λ y (x y))) y)) '(λ z (y z)))
  (check-equal? (reduce '(x (call/cc (λ k y)))) 'y)
  (check-equal? (reduce '(x (call/cc (λ k (k y))))) '(x y)))