#lang racket

; Notes on *Combinatory Logic - Pure, Applied and Typed* by Katalin Bimbó.

(define term?
  (flat-rec-contract
   term?
   symbol?
   (list/c term? term?)))

; First, a little macro for writing combinatory terms cleanly.

(require (for-syntax syntax/parse))
(define-syntax (term stx)
  (syntax-parse stx
    [(_ ?x:id)        #''?x]
    [(_ (?t))         #'(term ?t)]
    [(_ (?ts ... ?u)) #'(list (term (?ts ...)) (term ?u))]))

(module+ test
  (require rackunit)
  (check-equal? (term (S K K)) '((S K) K)))

; I'm skipping the syntactic exercises (1.1.1--1.1.10).

; Exercise 1.1.11.
(define (subterms term)
  (match term
    [(? symbol? _)     (set term)]
    [(list left right) (set-union (set term) (subterms left) (subterms right))]))
(provide (contract-out [subterms (-> term? (set/c term?))]))

; I'm only doing one of the test cases.
(module+ test
  (check-equal? (subterms (term (x (W x) y)))
                (set (term (x (W x) y))
                     (term (x (W x)))
                     (term x)
                     (term (W x))
                     (term W)
                     (term y))))

; Exercise 1.1.12. If M is a subterm of N and N is a subterm of M, then we can prove M = N by induction on N:
; * If N is atomic, then its only subterm is N itself and we're done.
; * Otherwise, we can assume N = PQ where P and Q are terms, and the following statements are
;   true:
;   * If M is a subterm of P and P is a subterm of M, then M = P.
;   * If M is a subterm of Q and Q is a subterm of M, then M = Q.
;   Now assume M is a subterm of N = PQ and N = PQ is a subterm of M. From the latter
;   assumption, we have that P and Q are subterms of M. From the former assumption, either
;   M = N, in which case we're done, or M is a subterm of P, in which case we can conclude
;   that M = P (but that's a contradiction, since PQ can't be a subterm of P), or M is a
;   subterm of Q, in which case we can conclude that M = Q (but that's a contradiction, since
;   PQ can't be a subterm of Q).

; Exercise 1.1.13. Oh, we already did this one.

; Exercise 1.1.14. Not exactly sure what this means. Does she just want "a term t belongs to
; the set of the subterms of a term u iff t is a subterm of u"?

(struct combinator (params body) #:transparent)
(provide (contract-out [struct combinator ([params (list/c symbol?)] [body term?])]))

(define (atomic-subterms term)
  (match term
    [(? symbol? _)     (set term)]
    [(list left right) (set-union (atomic-subterms left) (atomic-subterms right))]))
(provide (contract-out [atomic-subterms (-> term? symbol?)]))

; It's not entirely clear to me whether a proper combinator is allowed to have constants in its body, but I'm guessing not.
(define (proper-combinator? obj)
  (and (combinator? obj) (subset? (atomic-subterms obj) (combinator-params obj))))