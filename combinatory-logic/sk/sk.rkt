#lang racket
(module+ test (require rackunit))

(define term?
  (flat-rec-contract
   term?
   'K
   'S
   (list/c term? term?)))

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
  (check-equal? (term-reduce '((S K) K)) #f)
  (check-equal? (term-reduce '((K S) K)) 'S)
  (check-equal? (term-reduce '(((S K) K) S)) '((K S) (K S))))

(define (term-reduce* term)
  (let ([term- (term-reduce term)])
    (if term-
        (term-reduce* term-)
        term)))

(provide (contract-out [term-reduce* (-> term? term?)]))

(module+ test
  (check-equal? (term-reduce* '(((S K) K) S)) 'S))

(require (for-syntax syntax/parse))

(define-syntax (term stx)
  (syntax-parse stx
    #:datum-literals (K S)
    [(_ K) #''K]
    [(_ S) #''S]
    [(_ (x)) #'(term x)]
    [(_ (xs ... y)) #'`(,(term (xs ...)) ,(term y))]))

(module+ test
  (check-equal? (term K) 'K)
  (check-equal? (term S) 'S)
  (check-equal? (term (S K)) '(S K))
  (check-equal? (term (S K K)) '((S K) K)))

(define-syntax-rule (term-app . ts)
  (term-reduce* (term ts)))

(define-syntax (term-top stx)
  (syntax-parse stx
    #:datum-literals (K S)
    [(_ . K) #''K]
    [(_ . S) #''S]))

(provide #%module-begin #%top-interaction (rename-out [term-app #%app]
                                                      [term-top #%top]))