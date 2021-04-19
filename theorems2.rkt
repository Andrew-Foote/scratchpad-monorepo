#lang racket
(require syntax/parse/define)
(module+ test (require rackunit))

(define term-var? symbol?)

(provide (contract-out [term-var? flat-contract?]))

(define term? term-var?)

(provide (contract-out [term? flat-contract?]))

(define formula-var? symbol?)
(define rel-app? (list/c '∈ term? term?))
(define atomic-formula? (or/c formula-var? rel-app?))

(define formula?
  (flat-rec-contract
   formula?
   atomic-formula?
   (list/c '⇒ formula? formula?)
   (list/c '∀ term-var? formula?)))

(provide (contract-out [formula? flat-contract?]))

(define (format-formula φ)
  φ)

(define-for-syntax (⇒ stx)
  (syntax-parse stx
    [(_ ?φ)
     #'?φ]
    [(_ ?φ ?ψs ...)
     #'`(⇒ ,?φ ,(⇒ ?ψs ...))]
    [_
     #'(λ args
         (match-let ([(list φs (... ...) ψ) args])
           (foldr (λ (φ ψ) (⇒ φ ψ)) ψ φs)))]))

(define-match-expander ⇒ ⇒ ⇒)

(define-for-syntax (∀ stx)
  (syntax-parse stx
    [(_ ?φ)
     #'?φ]
    [(_ ?x ?ys ...)
     #'`(∀ ,?x ,(∀ ?ys ...))]
    [_
     #'(λ args
         (match-let ([(list xs (... ...) φ) args])
           (foldr (λ (x φ) (∀ x φ)) φ xs)))]))

(define-match-expander ∀ ∀ ∀)

(define (free-in-term? x t)
  (eq? x t))

(define (free? x φ)
  (match φ
    [(? formula-var? _)
     #f]
    [`(∈ ,y ,z)
     (or (free-in-term? x y) (free-in-term? x z))]
    [`(⇒ ,φ ,ψ)
     (or (free? x φ) (free? x ψ))]
    [`(∀ ,y ,φ)
     (and (not (free? x y)) (free? x φ))]))

(provide (contract-out [free? (-> term-var? formula? boolean?)]))

(define (substitutable? t x φ)
  (match φ
    [(? atomic-formula? _)
     #t]
    [`(⇒ ,φ ,ψ)
     (and (substitutable? t x φ) (substitutable? t x ψ))]
    [`(∀ ,y ,ψ)
     (or (not (free? x φ))
         (and (not (free? y t)) (substitutable? t x ψ)))]))

(provide (contract-out [substitutable? (-> term? term-var? formula? boolean?)]))

(define (subst-in-term t x u)
  (match u
    [(== x)
     t]
    [(? term-var? y)
     y]))

(define (subst t x φ)
  (match φ
    [(? formula-var? A)
     A]
    [`(∈ ,y ,z)
     `(∈ ,(subst-in-term t x y) ,(subst-in-term t x z))]
    [`(⇒ ,φ ,ψ)
     `(⇒ ,(subst t x φ) ,(subst t x ψ))]
    [`(∀ ,y ,ψ)
     (cond [(not (free? x φ)) φ]
           [(not (free? y t)) `(∀ ,x ,(subst t x ψ))]
           [else (raise-arguments-error
                  'subst "t is not substitutable for x in φ"
                  "t" t "x" x "φ" φ)])]))

(provide (contract-out [subst (-> term? term-var? formula? formula?)]))

(define-for-syntax ⊥ (λ (stx) #''(∀ x (∈ x x))))
(define-match-expander ⊥ ⊥ ⊥)


(define-for-syntax (∈ stx)
  (syntax-parse stx
    [(_ ?t ?u)
     #'`(∈ ,?t ,?u)]
    [_
     #'(λ (t u) (∈ t u))]))

(define-match-expander ∈ ∈ ∈)

(define-for-syntax (¬ stx)
  (syntax-parse stx
    [(_ ?φ)
     #'(⇒ ?φ ⊥)]
    [_
     #'(λ (φ) (¬ φ))]))

(define-match-expander ¬ ¬ ¬)

(define-for-syntax ⊤ (λ (stx) #'(¬ ⊥)))
(define-match-expander ⊤ ⊤ ⊤)

(define-for-syntax (∨ stx)
  (syntax-parse stx
    [(_)
     #'⊥]
    [(_ ?φ)
     #'?φ]
    [(_ ?φ ?ψs ...)
     #'(⇒ (¬ ?φ) (∨ ?ψs ...))]
    [_
     #'(λ φs
         (match φs
           ['()
            ⊥
            [(list φs (... ...) ψ)
             (foldr (λ (φ ψ) (∧ φ ψ) ψ φs))]]))]))

(define-match-expander ∨ ∨ ∨)

(define-for-syntax (∧ stx)
  (syntax-parse stx
    [(_)
     #'⊤]
    [(_ ?φ)
     #'?φ]
    [(_ ?φ ?ψs ...)
     #'(¬ (⇒ ?φ (¬ (∧ ?ψs ...))))]
    [_
     #'(λ φs
         (match φs
           ['()
            ⊤
            [(list φs (... ...) ψ)
             (foldr (λ (φ ψ) (∧ φ ψ) ψ φs))]]))]))

(define-match-expander ∧ ∧ ∧)

(define-for-syntax (⇔ stx)
  (syntax-parse stx
    [(_ ?φ ?ψ)
     #'(∧ (⇒ ?φ ?ψ) (⇒ ?ψ ?φ))]
    [_
     #'(λ (φ ψ) (⇔ φ ψ))]))

(define-match-expander ⇔ ⇔ ⇔)

(define-for-syntax (∃ stx)
  (syntax-parse stx
    [(_ ?φ)
     #'?φ]
    [(_ ?x ?ys ...)
     #'(¬ (∀ ?x (¬ (∃ ?ys ...))))]
    [_
     #'(λ xs
         (match-let ([(list xs (... ...) φ) xs])
           (foldr (λ (x φ) (∃ x φ)) φ xs)))]))

(define-match-expander ∃ ∃ ∃)

(define (⊆ A B)
  (let ([x (gensym)])
    (∀ x (⇒ (∈ x A) (∈ x B)))))

(define (= A B)
  (∧ (⊆ A B) (⊆ B A)))

(define (logical-axiom? obj)
  (match obj
    [`(frege ,φ ,ψ ,ξ)
     (and (formula? φ) (formula? ψ) (formula? ξ))]
    [`(simp ,φ ,ψ)
     (and (formula? φ) (formula? ψ))]
    [`(pierce ,φ ,ψ)
     (and (formula? φ) (formula? ψ))]
    [`(exp ,φ)
     (formula? φ)]
    [`(hilbert ,x ,φ ,ψ)
     (and (term-var? x) (formula? φ) (formula? ψ))]
    [`(inst ,x ,φ ,t)
     (and (term-var? x) (formula? φ) (term? t)
          (substitutable? t x φ))]
    [`(gen ,φ ,x)
     (and (formula? φ) (term-var? x)
          (not (free? x φ)))]
    [`(logical-axiom-gen ,a ,x)
     (and (logical-axiom? a) (term-var? x))]
    [_
     #f]))

(provide (contract-out [logical-axiom? flat-contract?]))

(define (frege φ ψ ξ) `(frege ,φ ,ψ ,ξ))
(define (simp φ ψ) `(simp ,φ ,ψ))
(define (pierce φ ψ) `(pierce ,φ ,ψ))
(define (exp φ) `(exp ,φ))
(define (hilbert x φ ψ) `(hilbert ,x ,φ ,ψ))
(define (inst x φ t) `(inst ,x ,φ ,t))
(define (gen φ x) `(gen ,φ ,x))
(define (logical-axiom-gen a x) `(logical-axiom-gen ,a ,x))

(define (logical-axiom-eval a)
  (match a
    [`(frege ,φ ,ψ ,ξ)
     (⇒ (⇒ φ ψ ξ) (⇒ φ ψ) φ ξ)]
    [`(simp ,φ ,ψ)
     (⇒ φ ψ φ)]
    [`(pierce ,φ ,ψ)
     (⇒ (⇒ (⇒ φ ψ) φ) φ)]
    [`(exp ,φ)
     (⇒ ⊥ φ)]
    [`(hilbert ,x ,φ ,ψ)
     (⇒ (∀ x (⇒ φ ψ)) (⇒ (∀ x φ) (∀ x ψ)))]
    [`(inst ,x ,φ ,t)
     (⇒ (∀ x φ) (subst t x φ))]
    [`(gen ,φ ,x)
     (when (free? x φ)
       (raise-arguments-error
        'logical-axiom-eval "∀ x φ is not a logical axiom, because x is free in φ"
        "φ" φ "x" x))
     (⇒ φ (∀ x φ))]
    [`(logical-axiom-gen ,a ,x)
     (∀ x (logical-axiom-eval a))]))

#;(define (axiom-eval a)
  (match a
    ['ext
     '(∀ A B (⇒ (= A B) (∀ C (⇒ (∈ A C) (∈ B C)))))]))


(define axiom? logical-axiom?)

(provide (contract-out [axiom? flat-contract?]))

(define assumption? (list/c 'assume symbol? formula?))

(provide (contract-out [assumption? flat-contract?]))

(define-for-syntax (assume stx)
  (syntax-parse stx
    [(_ ?x ?φ)
     #'`(assume ,?x ,?φ)]
    [_
     #'(λ (x φ) (assume x φ))]))

(define-match-expander assume assume assume)

(define (assume-fresh φ)
  (assume (gensym) φ))

(define (format-assumption x)
  (match-let ([`(assume ,_ ,φ) x])
    (format-formula φ)))

(define proof?
  (flat-rec-contract
   proof?
   axiom?
   assumption?
   (list/c '⇒e proof? proof?)
   (list/c ': proof? formula?)))

(provide (contract-out [proof? flat-contract?]))

(define-for-syntax (⇒e stx)
  (syntax-parse stx
    [(_ ?p)
     #'?p]
    [(_ ?ps ... ?q)
     #'`(⇒e ,(⇒e ?ps ...) ,?q)]
    [_
     #'(λ ps (foldl (λ (q p) (⇒e p q)) (car ps) (cdr ps)))]))

(define-match-expander ⇒e ⇒e ⇒e)

(define-for-syntax (: stx)
  (syntax-parse stx
    [(_ ?p ?J)
     #'`(: ,?p ,?J)]
    [_
     #'(λ (p J) (: p J))]))

(define-match-expander :
  :
  (λ (stx)
    (syntax-parse stx
      [(_ ?p ?J)
       #'(let ([J0 (proof-eval ?p)])
           (if (equal? ?J J0)
               ?p
               (raise-arguments-error
                'proof-eval "incorrect annotation"
                "annotation" (format-judgement ?J) "value" (format-judgement J0) "proof" ?p)))]
      [_
       #'(λ (p J) (: p J))])))

(define judgement? (list/c '⊢ (set/c assumption?) formula?))

(provide (contract-out [judgement? flat-contract?]))

(define-for-syntax (⊢ stx)
  (syntax-parse stx
    [(_ ?Γ ?φ)
     #'`(⊢ ,?Γ ,?φ)]
    [_
     #'(λ (Γ φ) (⊢ Γ φ))]))

(define-match-expander ⊢ ⊢ ⊢)

(define (format-judgement J)
  (match-let ([(⊢ Γ φ) J])
    (list '⊢ (map format-assumption (set->list Γ)) (format-formula φ))))

(define (proof-eval p)
  (match p
    [(? logical-axiom? _)
     (⊢ (set) (logical-axiom-eval p))]
    [(assume _ φ)
     (⊢ (set p) φ)]
    [(⇒e p q)
     (match* ((proof-eval p) (proof-eval q))
       [((⊢ Γ (⇒ φ ψ)) (⊢ Δ φ))
        (⊢ (set-union Γ Δ) ψ)]
       [((⊢ _ φ) (⊢ _ ψ))
        (raise-arguments-error
         'proof-eval "ψ is not detachable from φ"
         "φ" φ "ψ" ψ)])]
    [(: p J)
     (let ([J0 (proof-eval p)])
       (if (equal? J J0)
           J
           (raise-arguments-error
            'proof-eval "incorrect annotation"
            "annotation" (format-judgement J) "value" (format-judgement J0) "proof" p)))]))

(provide (contract-out [proof-eval (-> proof? judgement?)]))

; For every formula φ, we have ⊢ φ ⇒ φ.
(define (refl φ)
  (let* ([ψ (⇒ φ φ)]
         [p1 (: (frege φ ψ φ) (⊢ (set) (⇒ (⇒ φ ψ φ) (⇒ φ ψ) ψ)))]
         [p2 (: (simp φ ψ) (⊢ (set) (⇒ φ ψ φ)))]
         [p3 (: (simp φ φ) (⊢ (set) (⇒ φ ψ)))])
    (: (⇒e p1 p2 p3) (⊢ (set) ψ))))
  
(provide (contract-out [refl (-> formula? proof?)]))

(module+ test
  (check-equal? (proof-eval (refl 'A)) (⊢ (set) '(⇒ A A))))

; For any two formulas φ and ψ and every context Γ such that Γ ⊢ ψ, we have Γ ⊢ ψ ⇒ φ.
(define (simp-app p φ)
  (match-let ([(⊢ Γ ψ) (proof-eval p)])
    (let ([q (: (simp ψ φ) (⊢ (set) (⇒ ψ φ ψ)))])
      (: (⇒e q p) (⊢ Γ (⇒ φ ψ))))))

(module+ test
  (let ([x (assume-fresh 'A)])
    (check-equal? (proof-eval (simp-app x 'B)) (⊢ (set x) (⇒ 'B 'A)))))

; For any three formulas φ, ψ and ξ and any two contexts Γ and Δ such that Γ ⊢ φ ⇒ ψ ⇒ ξ and
; Δ ⊢ φ ⇒ ψ, we have Γ ∪ Δ ⊢ φ ⇒ ξ.
(define (frege-app p q)
  (match-let ([(⊢ Γ (⇒ φ ψ ξ)) (proof-eval p)]
              [(⊢ Δ (⇒ φ ψ)) (proof-eval q)])
    (let ([r (: (frege φ ψ ξ) (⊢ (set) (⇒ (⇒ φ ψ ξ) (⇒ φ ψ) φ ξ)))])
      (: (⇒e r p q) (⊢ (set-union Γ Δ) (⇒ φ ξ))))))

(module+ test
  (let ([x (assume-fresh (⇒ 'A 'B 'C))]
        [y (assume-fresh (⇒ 'A 'B))])
    (check-equal? (proof-eval (frege-app x y)) (⊢ (set x y) (⇒ 'A 'C)))))

; For any two formulas φ and ψ and every context Γ such that Γ ⊢ ψ, we have Γ \ {φ} ⊢ φ ⇒ ψ.
(define (⇒i1 x p)
  (match-let ([(assume _ φ) x]
              [(⊢ Γ ψ) (proof-eval p)])
    (: (match p
         [(== x)
          (: (refl φ) (⊢ (set) (⇒ φ φ)))]
         [(? (or/c axiom? assumption?) _)
          (: (simp-app p φ) (⊢ Γ (⇒ φ ψ)))]
         [(⇒e p q)
          (match* ((proof-eval p) (proof-eval q))
            [((⊢ Γ (⇒ ψ ξ)) (⊢ Δ ψ))
             (let* ([r1 (: (⇒i1 x p) (⊢ (set-remove Γ x) (⇒ φ (⇒ ψ ξ))))]
                    [r2 (: (⇒i1 x q) (⊢ (set-remove Δ x) (⇒ φ ψ)))])
               (: (frege-app r1 r2) (⊢ (set-remove (set-union Γ Δ) x) (⇒ φ ξ))))])]
         [(: p _) (⇒i1 x p)])
       (⊢ (set-remove Γ x) (⇒ φ ψ)))))

; For every nonnegative integer n, any n + 1 formulas φ_1, φ_2, ..., φ_n and ψ, and every context Γ
; such that Γ ⊢ ψ, we have Γ \ {φ_1, φ_2, ..., φ_n} ⊢ φ_1 ⇒ φ_2 ⇒ ... ⇒ φ_n ⇒ ψ.
(define (⇒i . args)
  (match-let ([(list xs ... p) args])
    (foldr ⇒i1 p xs)))

(module+ test
  (let ([x (assume-fresh 'A)]
        [y (assume-fresh 'B)]
        [z (assume-fresh 'C)])
    (check-equal? (proof-eval (⇒i x y z)) (⊢ (set z) (⇒ 'A 'B 'C)))))

; For any three formulas φ, ψ and ξ, we have ⊢ (φ ⇒ ψ) ⇒ (ψ ⇒ ξ) ⇒ φ ⇒ ξ.
(define (hyp φ ψ ξ)
  (let* ([x (assume-fresh (⇒ φ ψ))]
         [y (assume-fresh (⇒ ψ ξ))]
         [z (assume-fresh φ)]
         [p1 (: (⇒e x z) (⊢ (set x z) ψ))]
         [p2 (: (⇒e y p1) (⊢ (set x y z) ξ))])
    (: (⇒i x y z p2) (⊢ (set) (⇒ (⇒ φ ψ) (⇒ ψ ξ) φ ξ)))))

(module+ test
  (check-equal? (proof-eval (hyp 'A 'B 'C)) (⊢ (set) (⇒ (⇒ 'A 'B) (⇒ 'B 'C) 'A 'C))))

; For any two formulas φ and ψ and every context Γ such that Γ ⊢ (φ ⇒ ψ) ⇒ φ, we have Γ ⊢ φ.
(define (pierce-app p)
  (match-let ([(⊢ Γ (⇒ (⇒ φ ψ) φ)) (proof-eval p)])
    (let ([q (: (pierce φ ψ) (⊢ (set) (⇒ (⇒ (⇒ φ ψ) φ) φ)))])
      (: (⇒e q p) (⊢ Γ φ)))))

(module+ test
  (let ([x (assume-fresh (⇒ (⇒ 'A 'B) 'A))])
    (check-equal? (proof-eval (pierce-app x)) (⊢ (set x) 'A))))

; For every formula φ and every context Γ such that Γ ⊢ ⊥, we have Γ ⊢ φ.
(define (⊥e p φ)
  (match-let ([(⊢ Γ ⊥) (proof-eval p)])
    (let ([q (: (exp φ) (⊢ (set) (⇒ ⊥ φ)))])
      (: (⇒e q p) (⊢ Γ φ)))))

(module+ test
  (let ([x (assume-fresh ⊥)])
    (check-equal? (proof-eval (⊥e x 'A)) (⊢ (set x) 'A))))

; ⊥i takes x : A and y : A -> bot and returns bot

; For every formula φ and any two contexts Γ and Δ such that Γ ⊢ φ and Δ ⊢ ¬φ, we have Γ ∪ Δ ⊢ ⊥.
(define (⊥i p q)
  (match-let ([(⊢ Γ φ) (proof-eval p)]
              [(⊢ Δ (¬ φ)) (proof-eval q)])
    (: (⇒e q p) (⊢ (set-union Γ Δ) ⊥))))

(module+ test
  (let ([x (assume-fresh 'A)]
        [y (assume-fresh (¬ 'A))])
    (check-equal? (proof-eval (⊥i x y)) (⊢ (set x y) ⊥))))

; For any two formulas φ and ψ and any two contexts Γ and Δ such that Γ ⊢ φ and Δ ⊢ ¬φ, we have
; Γ ∪ Δ ⊢ ψ.
(define (exp-app p q φ)
  (match-let ([(⊢ Γ ψ) (proof-eval p)]
              [(⊢ Δ (¬ ψ)) (proof-eval q)])
    (let ([r (: (⊥i p q) (⊢ (set-union Γ Δ) ⊥))])
      (: (⊥e r φ) (⊢ (set-union Γ Δ) φ)))))

; For any two formulas φ and ψ and every context Γ such that Γ ⊢ ¬φ, we have Γ ⊢ φ ⇒ ψ.
(define (simp-app/¬ p φ)
  (match-let ([(⊢ Γ (¬ ψ)) (proof-eval p)])
    (let* ([x (assume-fresh ψ)]
           [q (: (exp-app x p φ) (⊢ (set-add Γ x) φ))])
      (: (⇒i x q) (⊢ Γ (⇒ ψ φ))))))

; For every formula φ and every context Γ such that Γ ⊢ ⊥, we have Γ \ {φ} ⊢ ¬φ.
(define (¬i x p)
  (match-let ([(assume _ φ) x]
              [(⊢ Γ ⊥) (proof-eval p)])
    (: (⇒i x p) (⊢ (set-remove Γ x) (¬ φ)))))

(module+ test
  (let ([x (assume-fresh 'A)]
        [y (assume-fresh ⊥)])
    (check-equal? (proof-eval (¬i x y)) (⊢ (set y) (¬ 'A)))))

; For any two formulas φ and ψ and any two contexts Γ and Δ such that Γ ⊢ ψ and Δ ⊢ ¬ψ, we have
; (Γ ∪ Δ) \ {φ} ⊢ ¬φ.
(define (¬i2 x p q)
  (match-let ([(assume _ φ) x]
              [(⊢ Γ ψ) (proof-eval p)]
              [(⊢ Δ (¬ ψ)) (proof-eval q)])
    (let ([r (: (⊥i p q) (⊢ (set-union Γ Δ) ⊥))])
      (: (¬i x r) (⊢ (set-remove (set-union Γ Δ) x) (¬ φ))))))

(module+ test
  (let ([x (assume-fresh 'A)]
        [y (assume-fresh 'B)]
        [z (assume-fresh (¬ 'B))])
    (check-equal? (proof-eval (¬i2 x y z)) (⊢ (set y z) (¬ 'A)))))

; For every formula φ and every context Γ such that Γ ⊢ ⊥, we have Γ \ {¬φ} ⊢ φ.
(define (¬e x p)
  (match-let ([(assume _ (¬ φ)) x]
              [(⊢ Γ ⊥) (proof-eval p)])
    (let* ([p1 (: (⊥e p φ) (⊢ Γ φ))]
           [p2 (: (⇒i x p1) (⊢ (set-remove Γ x) (⇒ (¬ φ) φ)))])
      (: (pierce-app p2) (⊢ (set-remove Γ x) φ)))))

(module+ test
  (let ([x (assume-fresh (¬ 'A))]
        [y (assume-fresh ⊥)])
    (check-equal? (proof-eval (¬e x y)) (⊢ (set y) 'A))))

; For any two formulas φ and ψ and any two contexts Γ and Δ such that Γ ⊢ ψ and Δ ⊢ ¬ψ, we have
; (Γ ∪ Δ) \ {¬φ} ⊢ φ.
(define (¬e2 x p q)
  (match-let ([(assume _ (¬ φ)) x]
              [(⊢ Γ ψ) (proof-eval p)]
              [(⊢ Δ (¬ ψ)) (proof-eval q)])
    (let ([r (: (⊥i p q) (⊢ (set-union Γ Δ) ⊥))])
      (: (¬e x r) (⊢ (set-remove (set-union Γ Δ) x) φ)))))

(module+ test
  (let ([x (assume-fresh (¬ 'A))]
        [y (assume-fresh 'B)]
        [z (assume-fresh (¬ 'B))])
    (check-equal? (proof-eval (¬e2 x y z)) (⊢ (set y z) 'A))))

(define (⇒e/¬ p q)
  (match-let ([(⊢ Γ (⇒ φ ψ)) (proof-eval p)]
              [(⊢ Δ (⇒ ψ ⊥)) (proof-eval q)])
    (let* ([x (assume 'x φ)]
           [r1 (: (⇒e p x) (⊢ (set-add Γ x) ψ))]
           [r2 (: (⇒e q r1) (⊢ (set-add (set-union Γ Δ) x) ⊥))])
      (: (¬i x r2) (⊢ (set-union Γ Δ) (¬ φ))))))

(module+ test
  (let ([x (assume-fresh (⇒ 'A 'B))]
        [y (assume-fresh (¬ 'B))])
    (check-equal? (proof-eval (⇒e/¬ x y)) (⊢ (set x y) (¬ 'A)))))

(define ⊤i (: (refl ⊥) (⊢ (set) ⊤)))

(define (lem φ)
  (: (refl (¬ φ)) (⊢ (set) (∨ φ (¬ φ)))))

(module+ test
  (check-equal? (proof-eval (lem 'A)) (⊢ (set) (∨ 'A (¬ 'A)))))

(define (∨i< p φ)
  (match-let ([(⊢ Γ ψ) (proof-eval p)])
    (: (simp-app p (¬ φ)) (⊢ Γ (∨ φ ψ)))))

(module+ test
  (let ([x (assume-fresh 'A)])
    (check-equal? (proof-eval (∨i< x 'B)) (⊢ (set x) (∨ 'B 'A)))))

(define (∨i> p φ)
  (match-let ([(⊢ Γ ψ) (proof-eval p)])
    (let* ([x (assume-fresh (¬ ψ))]
           [q (: (exp-app p x φ) (⊢ (set-add Γ x) φ))])
      (: (⇒i x q) (⊢ Γ (∨ ψ φ))))))

(module+ test
  (let ([x (assume-fresh 'A)])
    (check-equal? (proof-eval (∨i> x 'B)) (⊢ (set x) (∨ 'A 'B)))))

(define (∨s> p q)
  (match-let ([`(⊢ ,Γ ,(∨ φ ψ)) (proof-eval p)]
              [`(⊢ ,Δ ,(¬ φ)) (proof-eval q)])
    (: (⇒e p q) (⊢ (set-union Γ Δ) ψ))))

(module+ test
  (let ([x (assume-fresh (∨ 'A 'B))]
        [y (assume-fresh (¬ 'A))])
    (check-equal? (proof-eval (∨s> x y)) (⊢ (set x y) 'B))))

(define (∨s< p q)
  (match-let ([(⊢ Γ (∨ φ ψ)) (proof-eval p)]
              [(⊢ Δ (¬ ψ)) (proof-eval q)])
    (let* ([x (assume-fresh (¬ φ))]
           [r (: (∨s> p x) (⊢ (set-add Γ x) ψ))])
      (: (¬e2 x r q) (⊢ (set-union Γ Δ) φ)))))

(module+ test
  (let ([x (assume-fresh (∨ 'A 'B))]
        [y (assume-fresh (¬ 'B))])
    (check-equal? (proof-eval (∨s< x y)) (⊢ (set x y) 'A))))

; For any three formulas φ, ψ and ξ and any three contexts Γ, Δ and Θ such that Γ ⊢ φ ∨ ψ, Δ ⊢ ξ and
; Θ ⊢ ξ, we have Γ ∪ (Δ \ {φ}) ∪ (Θ \ {ψ}) ⊢ ξ.

; Proof:
;   ¬ξ   implies   ¬φ   implies   ψ   implies ξ
;       (by ⇒e/¬      (by ∨s>       (by ⇒e
;        on φ ⇒ ξ)     on φ ∨ ψ)     on ψ ⇒ ξ)
;
; so ¬ξ cannot be true. (I feel like it should be possible to make this simpler, since we are assuming
; a negation and then proving that the proposition holds after all, but I can't see any way to do it.)

(define (∨e p x q y r)
  (match-let ([(⊢ Γ (⇒ (⇒ φ ⊥) ψ)) (proof-eval p)]
              [(assume _ φ) x]
              [(⊢ Δ ξ) (proof-eval q)]
              [(assume _ ψ) y]
              [(⊢ Θ ξ) (proof-eval r)])
    (let* ([q1 (: (⇒i x q) (⊢ (set-remove Δ x) (⇒ φ ξ)))]
           [r1 (: (⇒i y r) (⊢ (set-remove Θ y) (⇒ ψ ξ)))]
           [z (assume 'z (¬ ξ))]
           [p1 (: (⇒e/¬ q1 z) (⊢ (set-add (set-remove Δ x) z) (¬ φ)))]
           [p2 (: (∨s> p p1) (⊢ (set-add (set-union Γ (set-remove Δ x)) z) ψ))]
           [p3 (: (⇒e r1 p2) (⊢ (set-add (set-union Γ (set-remove Δ x) (set-remove Θ y)) z) ξ))])
      (: (¬e2 z p3 z) (⊢ (set-union Γ (set-remove Δ x) (set-remove Θ y)) ξ)))))

(module+ test
  (let ([x (assume-fresh (∨ 'A 'B))]
        [y (assume-fresh 'A)]
        [y1 (assume-fresh 'C)]
        [z (assume-fresh 'B)]
        [z1 (assume-fresh 'C)])
    (check-equal? (proof-eval (∨e x y y1 z z1)) (⊢ (set x y1 z1) 'C))))

; For any two formulas φ and ψ and any two contexts Γ and Δ such that Γ ⊢ φ and Δ ⊢ ψ, we have
; Γ ∪ Δ ⊢ φ ∧ ψ.
(define (∧i p q)
  (match-let ([(⊢ Γ φ) (proof-eval p)]
              [(⊢ Δ ψ) (proof-eval q)])
    (let* ([x (assume-fresh (⇒ φ (¬ ψ)))]
           [r1 (: (⇒e x p) (⊢ (set-add Γ x) (¬ ψ)))])
      (: (¬i2 x q r1) (⊢ (set-union Γ Δ) (¬ (⇒ φ (¬ ψ))))))))

(module+ test
  (let ([x (assume-fresh 'A)]
        [y (assume-fresh 'B)])
    (check-equal? (proof-eval (∧i x y)) (⊢ (set x y) (∧ 'A 'B)))))

(module+ test
  (let ([x (assume-fresh (¬ 'A))])
    (check-equal? (proof-eval (simp-app/¬ x 'B)) (⊢ (set x) (⇒ 'A 'B)))))

; For any two formulas φ and ψ and every context Γ such that Γ ⊢ φ ∧ ψ, we have Γ ⊢ φ.
(define (∧e> p)
  (match-let ([(⊢ Γ (∧ φ ψ)) (proof-eval p)])
    (let* ([x (assume-fresh (¬ φ))]
           [q (: (simp-app/¬ x (¬ ψ)) (⊢ (set x) (⇒ φ (¬ ψ))))])
      (: (¬e2 x q p) (⊢ Γ φ)))))

(module+ test
  (let ([x (assume-fresh (∧ 'A 'B))])
    (check-equal? (proof-eval (∧e> x)) (⊢ (set x) 'A))))

; For any two formulas φ and ψ and every context Γ such that Γ ⊢ φ ∧ ψ, we have Γ ⊢ ψ.
(define (∧e< p)
  (match-let ([(⊢ Γ (∧ φ ψ)) (proof-eval p)])
    (let* ([x (assume-fresh (¬ ψ))]
           [q (: (simp-app x φ) (⊢ (set x) (⇒ φ (¬ ψ))))])
      (: (¬e2 x q p) (⊢ Γ ψ)))))

(module+ test
  (let ([x (assume-fresh (∧ 'A 'B))])
    (check-equal? (proof-eval (∧e< x)) (⊢ (set x) 'B))))

; For every variable x, any two formulas φ and ψ, and any two contexts Γ and Δ such that
; Γ ⊢ ∀x (φ ⇒ ψ) and Δ ⊢ ∀x φ, we have Γ ∪ Δ ⊢ ∀x ψ.
(define (hilbert-app p q)
  (match-let ([(⊢ Γ (∀ x (⇒ φ ψ))) (proof-eval p)]
              [(⊢ Δ (∀ x φ)) (proof-eval q)])
    (let ([r (: (hilbert x φ ψ) (⊢ (set) (⇒ (∀ x (⇒ φ ψ)) (∀ x φ) (∀ x ψ))))])
      (: (⇒e r p q) (⊢ (set-union Γ Δ) (∀ x ψ))))))

#;(module+ test
  (let ([a (assume-fresh '(∀ x (⇒ A B)))]
        [b (assume-fresh '(∀ x A))])
    (check-equal? (proof-eval (hilbert-app a b)) (⊢ (set a b) '(∀ x B)))))

; For every variable x, every formula φ, every context Γ such that Γ ⊢ ∀x φ and every term t
; substitutable for x in φ, we have Γ ⊢ φ[t/x].
(define (∀e p t)
  (match-let ([(⊢ Γ (∀ x φ)) (proof-eval p)])
    (let ([q (: (inst x φ t) (⊢ (set) (⇒ (∀ x φ) (subst t x φ))))])
      (: (⇒e q p) (⊢ Γ (subst t x φ))))))

#;(module+ test
  (let ([a (assume-fresh '(∀ x (∈ x x)))])
    (check-equal? (proof-eval (∀e a 'y)) (⊢ (set a) '(∈ y y)))))

; For every formula φ, every variable x not free in φ and every context Γ such that Γ ⊢ φ, we have
; Γ ⊢ ∀x φ.
(define (gen-app p x)
  (match-let ([(⊢ Γ φ) (proof-eval p)])
    (let ([q (: (gen φ x) (⊢ (set) (⇒ φ (∀ x φ))))])
      (: (⇒e q p) (⊢ Γ (∀ x φ))))))

#;(module+ test
  (let ([a (assume-fresh 'A)])
    (check-equal? (proof-eval (gen-app a 'x)) (⊢ (set a) '(∀ x A)))))

; For every variable x, every formula φ and every context Γ in which x is not free such that Γ ⊢ φ,
; we have Γ ⊢ ∀x φ.
(define (∀i1 x p)
  (match-let ([(⊢ Γ φ) (proof-eval p)])
    (: (match p
         [(? logical-axiom? a)
          (: (logical-axiom-gen a x) (⊢ (set) (∀ x φ)))]
         [(? assumption? a)
          (: (gen-app a x) (⊢ (set a) (∀ x φ)))]
         [(⇒e p q)
          (match* ((proof-eval p) (proof-eval q))
            [((⊢ Γ (⇒ φ ψ)) (⊢ Δ φ))
             (let* ([p1 (: (∀i1 x p) (⊢ Γ (∀ x (⇒ φ ψ))))]
                    [q1 (: (∀i1 x q) (⊢ Δ (∀ x φ)))])
               (: (hilbert-app p1 p1) (⊢ (set-union Γ Δ) (∀ x ψ))))])]
         [(: p φ)
          (∀i1 x p)])
       (⊢ Γ (∀ x φ)))))

; For every nonnegative integer n, any n variables x_1, x_2, ..., x_n, every formula φ and every
; context Γ in which none of x_1, x_2, ... and x_n are free such that Γ ⊢ φ, we have
; Γ ⊢ ∀x_1 ∀x_2 ... ∀x_n φ.
(define (∀i . args)
  (match-let ([(list xs ... p) args])
    (foldr ∀i1 p xs)))

#;(module+ test
  (let ([a (assume-fresh 'A)])
    (check-equal? (proof-eval (∀i 'x 'y a)) (⊢ (set a) '(∀ x y A)))))

; For every variable x, every formula φ, every every term t substitutable for x in φ and every context
; Γ such that Γ ⊢ φ[t/x], we have Γ ⊢ ∃x φ.
(define (∃i p t x φ)
  (match-let ([(⊢ Γ _) (proof-eval p)])
    (let ([x (assume-fresh (∀ x (¬ φ)))]
          [q (: (∀e x t) (⊢ (set x) (¬ (subst t x φ))))])
      (: (¬i2 x p q) (⊢ Γ (∃ x φ))))))

#;(module+ test
  (let ([a (assume-fresh '(∈ x x))])
    (check-equal? (proof-eval (∃i a 'y 'y '(∈ y y))) (⊢ (set a) (∃ 'y '(∈ y y))))))

; ∃ x φ :=: ¬∀x ¬φ
; so to introduce ∃ x φ, we assume ∀ x ¬φ, and prove a contradiction
; 