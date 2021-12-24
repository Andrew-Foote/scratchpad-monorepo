#lang racket
(require (for-syntax syntax/parse))
(require (only-in racket/control shift reset))
(define-namespace-anchor a)
(define ns (namespace-anchor->namespace a))

(define (foldr1 f xs)
  (let ([xs (reverse xs)])
    (foldr f (car xs) (cdr xs))))

(define (foldl1 f xs)
  (foldl (λ (x y) (f y x)) (car xs) (cdr xs)))

(define (raise-unless type-name pred-expr val)
  (unless ((eval pred-expr ns) val) (raise-argument-error type-name (format "~a" pred-expr) val)))

(struct sort (id) #:transparent)

(struct fun-symbol (id doms cod) #:transparent
  #:guard (λ (id doms cod type-name)
            (raise-unless type-name '(listof sort?) doms)
            (raise-unless type-name 'sort? cod)
            (values id doms cod))
  #:property prop:procedure (λ (self . args)
                              (term self args)))

(struct term (symbol args) #:transparent
  #:guard (λ (symbol args type-name)
            (raise-unless type-name 'fun-symbol? symbol)
            (raise-unless type-name '(listof term?) args)
            (match-let* ([(fun-symbol id doms _) symbol]
                         [m (length doms)]
                         [n (length args)])
              (unless (equal? (length doms) (length args))
                (raise-arguments-error type-name "f has arity m, but was given n arguments"
                                       "f" symbol "m" m "n" n))
              (let ([mismatches (filter (λ (cmp)
                                          (match-let ([(list _ dom sort) cmp])
                                            (not (equal? dom sort))))
                                        (map list (range m) doms (map term-sort args)))])
                (unless (null? mismatches)
                  (match-let ([(list k dom sort) (car mismatches)])
                    (raise-arguments-error type-name "the kth domain of f is A, but its kth argument was of type B"
                                           "f" symbol "k" k "A" dom "B" sort)))))
            (values symbol args))
  #:methods gen:custom-write
  [(define (write-proc self port mode)
    ((match mode
       [#t (curryr write port)]
       [#f (curryr display port)]
       [(or 0 1) (curryr print port mode)]) (term->sexp self)))])

(define (term-sort t)
  (raise-unless 'term-sort 'term? t)
  (match-let ([(term (fun-symbol _ _ cod) _) t])
    cod))

(define (term->sexp t)
  (raise-unless 'term->sexp 'term? t)
  (match-let ([(term (fun-symbol id doms cod) args) t])
    (cons id (map term->sexp args))))

(define (sort->pred A)
  (raise-unless 'sort->pred 'sort A)
  (λ (obj)
    (and (term? obj)
         (equal? (term-sort obj) A))))

(define (1sorted-fun-symbol id sort arity)
  (raise-unless '1sorted-fun-symbol 'natural? arity)
  (fun-symbol id (build-list arity (λ (_) sort)) sort))

(define (constant id sort)
  (1sorted-fun-symbol id sort 0))

; Connectives

(define Bool (sort 'Bool))
(define prop? (sort->pred Bool))

(define (connective id arity)
  (1sorted-fun-symbol id Bool arity))

(define condl (connective 'condl 2))

(define-match-expander →
  (λ (stx)
    (syntax-parse stx
      [(_ ?φ)
       #'?φ]
      [(_ ?φ ?ψs ...)
       #'(term (== condl) (list ?φ (→ ?ψs ...)))]))
  (λ (stx)
    (syntax-parse stx
      [(_ ?φ)
       #'?φ]
      [(_ ?φ ?ψs ...)
       #'(condl ?φ (→ ?ψs ...))]
      [_
       #'(λ φs
           (foldr1 condl φs))])))

(define bot (connective 'bot 0))

(define-for-syntax ⊥ (λ (_) #'(bot)))
(define-match-expander ⊥ ⊥ ⊥)

(define-for-syntax ¬
  (λ (stx)
    (syntax-parse stx
      [(_ ?φ) #'(→ ?φ ⊥)]
      [_ #'(λ (φ) (→ φ ⊥))])))

(define-match-expander ¬ ¬ ¬)

(define-for-syntax ∨
  (λ (stx)
    (syntax-parse stx
      [(_)
       ⊥]
      [(_
      [(_ ?φ ?ψs ...)
       #'(→ (¬ ?φ) ?ψ)]
      [_ #'(λ (φ ψ

; Relations

(define (rel-symbol id doms)
  (fun-symbol id doms Bool))

(define (1sorted-rel-symbol id sort arity)
  (raise-unless '1sorted-rel-symbol 'natural? arity)
  (rel-symbol id (build-list arity (λ (_) sort))))

; Variables

(define Var (sort 'Var))
(define var? (sort->pred Var))

(define (var id)
  ((constant id Var)))

(define Entity (sort 'Entity))
(define entity-term? (sort->pred Entity))

(define var-term (fun-symbol 'var-term (list Var) Entity))

; Quantifiers

(define Quantifier (sort 'Quantifier))
(define quantifier? (sort->pred Quantifier))

(define (quantifier id)
  (constant id Quantifier))

(define forall (quantifier '∀))

(define quantify (fun-symbol 'quantify (list Quantifier Var Bool) Bool))

(define-match-expander ∀
  (λ (stx)
    (syntax-parse stx
      [(_ ?φ)
       #'?φ]
      [(_ ?x ?ys ... ?φ)
       #'(term (== quantify) (list (== forall) ?x (∀ ?ys ... ?φ)))]))
  (λ (stx)
    (syntax-parse stx
      [(_ ?φ)
       #'?φ]
      [(_ ?x ?ys ... ?φ)
       #'(quantify (forall) ?x (∀ ?ys ... ?φ))]
      [_
       #'(λ xs/φ
           (foldr1 (λ (x φ) (quantify (forall) x φ)) xs/φ))])))

(define (free? x t)
  (raise-unless 'free? 'var? x)
  (raise-unless 'free? '(or/c entity-term? prop?) t)
  (match t
    [(term (== var-term) (list (== x)))
     #t]
    [(term (== quantify) (list _ y φ))
     (and (not (equal? x y))
          (free? x φ))]
    [(term _ args)
     (ormap (curry free? x) args)]))

(define (subst t x φ)
  (raise-unless 'subst 'entity-term? t)
  (raise-unless 'subst 'var? x)
  (raise-unless 'subst 'prop? φ)
  (match φ
    [(term (== var-term) (list (== x)))
     t]
    [(term (== quantify) (list _ y ψ))
     (cond [(not (free? x φ))
            φ]
           [(not (free? y t))
            (∀ y (subst t x φ))]
           [else
            (let ([z (var (gensym))])
              (∀ z (subst t x (subst (var-term z) y φ))))])]
    [(term f args)
     (apply f (map (curry subst t x) args))]))

; Peano arithmetic

(define zero (constant 'zero Entity))
(define succ (1sorted-fun-symbol 'succ Entity 1))
(define add (1sorted-fun-symbol 'add Entity 2))
(define mul (1sorted-fun-symbol 'mul Entity 2))
(define eq (1sorted-rel-symbol 'eq Entity 2))

(define (nat->term n)
  (raise-unless 'nat->term 'natural? n)
  (if (zero? n)
      (zero)
      (succ (nat->term (sub1 n)))))

(define (term->nat t)
  (raise-unless 'term->nat 'entity? t)
  (match t
    [(term (== zero) '())
     0]
    [(term (== succ) (list t))
     (add1 (term->nat t))]
    [(term (== add) (list t u))
     (add (term->nat t) (term->nat u))]
    [(term (== mul) (list t u))
     (mul (term->nat t) (term->nat u))]))

; Proofs

(define Proof (sort 'Proof))
(define proof? (sort->pred Proof))

(define detach2 (1sorted-fun-symbol 'detach2 Proof 2)) 

(define-match-expander detach
  (λ (stx)
    (syntax-parse stx
      [(_ ?π)
       #'?π]
      [(_ ?π ?ρs ...)
       #'(term (== detach2) (list ?π (detach ?ρs ...)))]))
  (λ (stx)
    (syntax-parse stx
      [(_ ?π)
       #'?π]
      [(_ ?πs ... ?ρ)
       #'(detach2 (detach ?πs ...) ?ρ)]
      [_
       #'(λ πs
           (foldl1 detach2 πs))])))

(define Axiom (sort 'Axiom))
(define axiom? (sort->pred Axiom))

(define axiom-proof (fun-symbol 'axiom-proof (list Axiom) Proof))

(define (axiom id)
  (constant id Axiom))

(define gen-axiom (fun-symbol 'gen-axiom (list Var Axiom) Axiom))
(define frege (fun-symbol 'frege (list Bool Bool Bool) Axiom))
(define simp (fun-symbol 'simp (list Bool Bool) Axiom))
(define ¬¬e (fun-symbol '¬¬e (list Bool) Axiom))
(define ∀→ (fun-symbol '∀→ (list Var Bool Bool) Axiom))
(define ∀e (fun-symbol '∀e (list Var Bool Entity) Axiom))
(define ∀i (fun-symbol '∀i (list Bool Var) Axiom))
(define =-0 (fun-symbol '=-0 '() Axiom))
(define =-succ (fun-symbol '=-succ (list Var Var) Axiom))
(define succ-pos (fun-symbol 'succ-pos (list Var) Axiom))
(define succ-inj (fun-symbol 'succ-inj (list Var Var) Axiom))
(define induction (fun-symbol 'induction (list Var Bool) Axiom))

(define assume (fun-symbol 'assume (list Bool) Proof))

(struct judgement (antes succ) #:transparent
  #:guard (λ (antes succ type-name)
            (raise-unless type-name '(set/c prop?) antes)
            (raise-unless type-name prop? succ)
            (values antes succ)))

(define-match-expander ⊢
  (λ (stx)
    (syntax-parse stx
      [(_ ?Γ ?ψ)
       #'(judgement ?Γ ?ψ)]))
  (λ (stx)
    (syntax-parse stx
      [(_ ?Γ ?ψ)
       #'(judgement ?Γ ?ψ)]
      [_
       #'judgement])))

(define (concl proof)
  (raise-unless 'concl 'proof? proof)
  (match proof
    [(term (== assume) (list φ))
     (⊢ (set φ) φ)]
    [(detach π ρ)
     (match* ((concl π) (concl ρ))
       [((⊢ Γ (→ φ ψ)) (⊢ Δ φ))
        (⊢ (set-union Γ Δ) ψ)]
       [(_ _)
        (shift _ #f)])]
    [(term (== axiom-proof) (list ax))
     (⊢ (set)
        (match ax
          [(term (== gen-axiom) (list x ax))
           (∀ x ax)]
          [(term (== frege) (list φ ψ ξ))
           (→ (→ φ ψ ξ) (→ φ ψ) φ ξ)]
          [(term (== simp) (list φ ψ))
           (→ φ ψ φ)]
          [(term (== ¬¬e) (list φ))
           (→ (¬ (¬ φ)) φ)]
          [(term (== ∀→) (list x φ ψ))
           (→ (∀ x (→ φ ψ)) (∀ x φ) (∀ x ψ))]
          [(term (== ∀e) (list x φ t))
           (→ (∀ x φ) (subst t x φ))]
          [(term (== ∀i) (list φ x))
           (if (free? x φ)
               (shift _ #f)
               (→ φ (∀ x φ)))]
          [(term (== =-0) '())
           (eq (nat->term 0) (nat->term 0))]
          [(term (== =-succ) (list x y))
           (→ (eq (var-term x) (var-term y))
              (eq (succ (var-term x)) (succ (var-term y))))]
          [(term (== succ-pos) (list x))
           (¬ (= (succ x) (nat->term 0)))]
          [(term (== succ-inj) (list x y))
           (→ (eq (succ (var-term x))
                  (succ (var-term y))) (eq (var-term x) (var-term y)))]
          [(term (== induction) (list x φ))
           (→ (subst (nat->term 0) x φ)
              (∀ x (→ φ (subst (succ (var-term x)) x φ)))
              (∀ x φ))]))]))

(define (: π J)
  (raise-unless ': 'proof? π)
  (raise-unless ': 'judgement? J)
  (let ([I (reset (concl π))])
    (if (and I (equal? I J))
        π
        (raise-arguments-error ': "π proves I, not J as annotated" "π" π "I" I "J" J))))

(define (refl φ)
  (raise-unless 'refl 'prop? φ)
  (: (detach
      (: (axiom-proof (frege φ (→ φ φ) φ)) (⊢ (set) (→ (→ φ (→ φ φ) φ) (→ φ φ φ) φ φ)))
      (: (axiom-proof (simp φ (→ φ φ))) (⊢ (set) (→ φ (→ φ φ) φ)))
      (: (axiom-proof (simp φ φ)) (⊢ (set) (→ φ φ φ))))
     (⊢ (set) (→ φ φ))))