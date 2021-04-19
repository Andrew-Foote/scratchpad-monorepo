#lang racket

(struct connective (graph) #:transparent
  #:property prop:procedure
  (λ (self . args)
    (complex-prop self args)))

(define ⊥ (connective (hash '() #f)))
(define ⊤ (connective (hash '() #t)))
(define ¬ (connective (hash '(#f) #t '(#t) #f)))
(define → (connective (hash '(#f #f) #t '(#f #t) #t '(#t #f) #f '(#t #t) #t)))
(define ∨ (connective (hash '(#f #f) #f '(#f #t) #t '(#t #f) #t '(#t #t) #t)))
(define ∧ (connective (hash '(#f #f) #f '(#f #t) #f '(#t #f) #f '(#t #t) #t)))
(define ↔ (connective (hash '(#f #f) #t '(#f #t) #f '(#t #f) #f '(#t #t) #t)))
(define ? (connective (hash '(#f #f #f) #f '(#f #f #t) #t '(#f #t #f) #f '(#f #t #t) #t
                            '(#t #f #f) #f '(#t #f #t) #f '(#t #t #f) #t '(#t #t #t) #t)))

(define (connective-apply connective . args)
  (hash-ref (connective-graph connective) args))

(define (connective-arity connective)
  (length (car (hash-keys (connective-graph connective)))))

(module+ test
  (require rackunit)
  (map (λ (c) (check-equal? (connective-arity c) 0)) (list ⊥ ⊤))
  (check-equal? 1 (connective-arity ¬))
  (map (λ (c) (check-equal? (connective-arity c) 2)) (list → ∨ ∧ ↔))
  (check-equal? 3 (connective-arity ?)))

(define (connective-from-procedure arity proc)
  (connective
   (apply hash
          (append-map
           (λ (args) (list args (apply proc args)))
           (apply cartesian-product (build-list arity (λ (_) '(#f #t))))))))

(define (projection-connective arity index)
  (connective-from-procedure arity
                             (λ args
                               (list-ref args index))))

(module+ test
  (check-equal? (projection-connective 2 0) (connective (hash '(#f #f) #f '(#f #t) #f '(#t #f) #t '(#t #t) #t))))

(define (connective-compose arity head . tail)
  (connective-from-procedure arity
                             (λ args
                               (apply
                                connective-apply head
                                (map (λ (f)
                                       (apply connective-apply f args))
                                     tail)))))

(module+ test
  (check-equal? (connective-compose 1 ¬ ¬) (projection-connective 1 0))
  (check-equal? (connective-compose 2 →
                                    (connective-compose 2 ¬ (projection-connective 2 0))
                                    (projection-connective 2 1)) ∨))

(struct atomic-prop (symbol) #:transparent)

(struct complex-prop (head tail) #:transparent)

(define (prop-value prop atomic-prop-value)
  (match prop
    [(atomic-prop _)
     (atomic-prop-value prop)]
    [(complex-prop head tail)
     (hash-ref (connective-graph head) (map (curryr prop-value atomic-prop-value) tail))]))

(define (connective-from-prop params prop)
  (connective-from-procedure (length params)
                             (λ args
                               (prop-value
                                prop
                                (let ([atomic-prop-value-hash
                                       (apply hash (append-map list params args))])
                                  (λ (atomic-prop)
                                    (hash-ref
                                     atomic-prop-value-hash
                                     atomic-prop)))))))

(module+ test
  (let ([A (atomic-prop 'A)]
        [B (atomic-prop 'B)]
        [C (atomic-prop 'C)])
    (check-equal? (connective-from-prop (list A) (→ A (⊥))) ¬)
    (check-equal? (connective-from-prop '() (¬ (⊥))) ⊤)
    (check-equal? (connective-from-prop (list A B) (→ (¬ A) B)) ∨)
    (check-equal? (connective-from-prop (list A B) (→ (→ A B) B)) ∨)
    (check-equal? (connective-from-prop (list A B) (¬ (→ A (¬ B)))) ∧)
    (check-equal? (connective-from-prop (list A B C) (∨ (∧ A B) (∧ (¬ A) C))) ?)))

(define (atomic-subprops prop)
  (match prop
    [(atomic-prop _)
     (list prop)]
    [(complex-prop head tail)
     (remove-duplicates (append-map atomic-subprops tail))]))

(define (prop->connective prop)
  (connective-from-prop (atomic-subprops prop) prop))

(define (tautology? prop)
  (equal? (prop->connective prop) (connective-compose (length (atomic-subprops prop)) ⊤)))

(module+ test
  (let ([A (atomic-prop 'A)]
        [B (atomic-prop 'B)]
        [C (atomic-prop 'C)])
    (check-true (tautology? (→ A A)))
    (check-false (tautology? (→ A B)))
    (check-false (tautology? (→ (→ A B) (→ B A))))
    (check-true (tautology? (→ A (→ B A))))
    (check-true (tautology? (→ (→ A (→ B C)) (→ (→ A B) (→ A C)))))
    (check-true (tautology? (→ (⊥) A)))
    (check-true (tautology? (⊤)))))

(struct atomic-term (symbol) #:transparent)

(struct 