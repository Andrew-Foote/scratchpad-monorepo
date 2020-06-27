#lang racket
(module+ test (require rackunit))

(define (SK-eval term)
  (match term
    [`(,fun ,arg)
     (match `(,(SK-eval fun) ,(SK-eval arg))
       [`((K ,x) ,y)
        (SK-eval x)]
       [`(((S ,x) ,y) ,z)
        (SK-eval `((,x ,z) (,y ,z)))]
       [`(,x ,y) `(,x ,y)])]
    [_ term]))

(module+ test
  (check-equal? (SK-eval '((K x) y)) 'x)
  (check-equal? (SK-eval '(((S x) y) z)) '((x z) (y z)))
  (check-equal? (SK-eval '(((K x) y) (((S x) y) z))) '(x ((x z) (y z))))
  (check-equal? (SK-eval '(((K x) y) z)) '(x z))
  (check-equal? (SK-eval '(z (((S x) y) z))) '(z ((x z) (y z))))
  (check-equal? (SK-eval '((K ((K x) y)) z)) 'x))

(define I '((S K) K))

(module+ test (check-equal? (SK-eval `(,I x)) 'x))

(define (SK-λ var term)
  (match term
    [(== var) I]
    [(? symbol? _) `(K ,term)]
    [`(,fun ,arg)
     (match `(,(SK-λ var fun) ,(SK-λ var arg))
       [`((K ,fun_) (K ,arg_))
        `(K (,fun_ ,arg_))]
       [`((K ,x) ,(== I))
        x]
       [`(,fun_ ,arg_)
        `((S ,fun_) ,arg_)])]))

(module+ test
  (check-equal? (SK-λ 'x 'x) I)
  (check-equal? (SK-λ 'x 'y) '(K y))
  (check-equal? (SK-λ 'x '(x x)) `((S ,I) ,I))
  (check-equal? (SK-λ 'x '(y z)) '(K (y z)))
  (check-equal? (SK-λ 'x '(y x)) 'y))

(define (SK-λ* . args)
  (let-values ([(vars term) (split-at args (sub1 (length args)))])
    (foldr SK-λ (car term) vars)))

(define B (SK-λ* 'x 'y 'z '(x (y z))))

(module+ test
  (check-equal? B '((S (K S)) K))
  (check-equal? (SK-eval `(((,B x) y) z)) '(x (y z))))

(define C (SK-λ* 'x 'y 'z '((x z) y)))

(module+ test
  (check-equal? (SK-eval `(((,C x) y) z)) '((x z) y)))
