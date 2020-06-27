#lang racket
(require (for-syntax syntax/parse))

(module+ test (require rackunit))

(define (flip f x y) (f y x))

; Notes on *Combinatory Logic - Pure, Applied and Typed* by Katalin Bimbó




(define variable/c (make-parameter symbol?))
(define constant/c (make-parameter symbol?))

(define atomic-term? (or/c (variable/c) (constant/c)))
(struct $ (t u) #:transparent)

(define-syntax (term stx)
  (syntax-parse stx
    [(?ts ... ?u) #'($ (term (?ts ...)) ?u)]
    [(?t) #'?t]
    [x:id #'(quote x)]))

(term

(define ($* . terms)
  (foldl (curry flip $) (car terms) (cdr terms)))

(define term?
  (flat-rec-contract
   term?
   atomic-term?
   (struct/c $ term? term?)))

(define complex-term? (and/c term? (not atomic-term?)))

(define (subterms term)
  (match term
    [(? atomic-term? _)
     (set term)]
    [($ t u)
     (set-union (set term) (subterms t) (subterms u))]))

(module+ test
  ; exercise 1.1.11
  (check-equal? (subterms ($* 'x ($ 'W 'x) 'y))
                (set ($* 'x ($ 'W 'x) 'y)
                     ($ 'x ($ 'W 'x))
                     'x
                     ($ 'W 'x)
                     'W
                     'y))
  (check-equal? (subterms ($* 'y 'y ($ 'y ($ 'y 'y))))
                (set ($* 'y 'y ($ 'y ($ 'y 'y)))
                     ($ 'y 'y)
                     'y
                     ($ 'y ($ 'y 'y))))
  (check-equal? (subterms ($ ($* 'S ($ 'K 'W) 'S) ($* 'B 'W 'W)))
                (set ($ ($* 'S ($ 'K 'W) 'S) ($* 'B 'W 'W))
                     ($* 'S ($ 'K 'W) 'S)
                     ($ 'S ($ 'K 'W))
                     'S
                     ($ 'K 'W)
                     'K
                     'W
                     ($* 'B 'W 'W)
                     ($ 'B 'W)
                     'B))
  (check-equal? (subterms ($* 'z 'S ($ 'y 'S) ($* 'x 'W 'S 'K)))
                (set ($* 'z 'S ($ 'y 'S) ($* 'x 'W 'S 'K))
                     ($* 'z 'S ($ 'y 'S))
                     ($ 'z 'S)
                     'z
                     'S
                     ($ 'y 'S)
                     'y
                     ($* 'x 'W 'S 'K)
                     ($* 'x 'W 'S)
                     ($ 'x 'W)
                     'x
                     'W
                     'K)))