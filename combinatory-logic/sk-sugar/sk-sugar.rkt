#lang racket
(require (for-syntax syntax/parse))
(module+ test (require rackunit))

(define term?
  (flat-rec-contract
   term?
   symbol?
   (list/c term? term?)))

(define I '((S K) K))

(define (term-reduce term)
  (match term
    [`((K ,x) ,y) x]
    [`(((S ,x) ,y) ,z) `((,x ,z) (,y ,z))]
    [`(,x ,y)
     (let ([x- (term-reduce x)])
       (if x-
           `(,x- ,y)
           (let ([y- (term-reduce y)])
             (if y-
                 `(,x ,y-)
                 #f))))]
    [_ #f]))
(provide (contract-out [term-reduce (-> term? (or/c term? #f))]))

(module+ test
  (check-equal? (term-reduce I) #f)
  (check-equal? (term-reduce `(,I x)) '((K x) (K x)))
  (check-equal? (term-reduce '((K x) (K x))) 'x))

(define (term-reduce* term)
  (let ([term- (term-reduce term)])
    (if term-
        (term-reduce* term-)
        term)))

(provide (contract-out [term-reduce* (-> term? term?)]))

(module+ test
  (check-equal? (term-reduce* `(,I x)) 'x))

(define (term-λ var term)
  (match term
    [(== var) '((S K) K)]
    [(? symbol? x) `(K ,x)]
    [`(,t ,u)
     (let ([t- (term-λ var t)]
           [u- (term-λ var u)])
       (match (cons t- u-)
         [(cons 'K u--) I]
         [(cons `(K ,t--) `(K ,u--))
          (match (cons t-- u--)
            [(cons '(S K) 'K) '(S K)]
            [_ `(K (,t-- ,u--))])]
         [(cons `(K ,t--) (== I)) t--]
         [_ `((S ,t-) ,u-)]))]))

(provide (contract-out [term-λ (-> symbol? term? term?)]))

(module+ test
  (check-equal? (term-λ 'x 'x) I)
  (check-equal? (term-λ 'x 'y) '(K y))
  (check-equal? (term-λ 'x '(x x)) `((S ,I) ,I))
  (check-equal? (term-λ 'x '(x y)) `((S ,I) (K y)))
  (check-equal? (term-λ 'x '(y x)) 'y)
  (check-equal? (term-λ 'x '(y z)) '(K (y z))))

(define B '((S (K S)) K))
(define C '((S ((S (K S)) ((S (K K)) S))) (K K)))
(define W '((S S) (S K)))

(define std-env
  (hash
   cons '(λ x y z (z x y))
   car '(λ x y x)
   cdr '(λ x y y)))

(define-syntax (term stx)
  (syntax-parse stx
    #:datum-literals (I λ let)
    [(_ I) #'I]
    [(_ x:id) #''x]
    [(_ 0) #'`(K ,I)] ; KI = λf.λx.x
    [(_ n:exact-nonnegative-integer)
     (let ([n- (syntax-e #'n)])
       #``((S ,B) ,(term #,(sub1 n-))))] ; SBn = λf.λx.f(nfx)
    [(_ (λ t)) #'(term t)]
    [(_ (λ x:id xs:id ... t)) #'(term-λ 'x (term (λ xs ... t)))]
    [(_ (let t)) #'(term t)]
    [(_ (let (x:id t) (xs:id ts) ... u)) #'`(,(term-λ 'x (term (let (xs ts) ... u))) ,(term t))]
    [(_ (x)) #'(term x)]
    [(_ (xs ... y)) #'`(,(term (xs ...)) ,(term y))]))

(module+ test
  (check-equal? (term K) 'K)
  (check-equal? (term S) 'S)
  (check-equal? (term (S K)) '(S K))
  (check-equal? (term (S K K)) I)
  (check-equal? (term I) I)
  (check-equal? (term (λ x x)) I)
  (check-equal? (term (λ x (x x))) `((S ,I) ,I))
  (check-equal? (term-reduce* (term (let [x y] (x x)))) '(y y)))

(define-syntax-rule (term-app . ts)
  (term-reduce* (term ts)))

(define-syntax-rule (term-module-begin . ts)
  (#%module-begin
   (let [cons (λ a b x (x a b))]
        [car (λ x y x)]
        [cdr (λ x y y)]
        ts)))

(provide #%module-begin
         #%top-interaction
         #%datum
         (rename-out [term-app #%app]
                     [#%datum #%top]))