#lang racket
(require (only-in racket/control shift reset))

(define iter-done (gensym))

(define (iter lst)
  (lambda ()
    (match lst
      ['()
       iter-done]
      [(cons x xs)
       (set! lst xs)
       x])))

(define (iter->list it)
  (let loop ([it it]
             [xs '()])
    (match (it)
      [(== iter-done)
       (reverse xs)]
      [x
       (loop it (cons x xs))])))

(define (iter2 lst)
  (match lst
    ['()
     (void)]
    [(cons x xs)
     (shift k `(next ,x ,k))
     (iter2 xs)]))

(define (iter2->list it)
  (let loop ([it (reset (begin (it) 'done))]
             [xs '()])
    (match it
      ['done
       (reverse xs)]
      [`(next ,x ,k)
       (loop (k 'done) (cons x xs))])))

; this is the identity function
(define (shmoop ls)
  (iter2->list (thunk (iter2 ls))))


(define (walk t)
  (match t
    [(? symbol? x)
     (shift k `(next ,x ,k))]
    [`(,t ,u)
     (walk t)
     (walk u)]
    [`(λ ,x ,t)
     (walk t)]))

(define (free-vars t)
  (let loop ([i (reset (walk t))]
             [xs '()])
    (match i
      [`(next ,x ,k)
       (loop (k 'done) (cons x xs))]
      ['done
       (reverse xs)])))

(free-vars '(λ x (x (y z))))