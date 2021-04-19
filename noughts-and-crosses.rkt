#lang racket
(module+ test (require rackunit))

; Noughts and crosses. You have a 3 x 3 board. There are two players, and turns alternate between
; the players. During each turn, the current player chooses a square on the board which is not
; already occupied and places their symbol there. The symbols for the two players are nought (O) and
; cross (X). The first player to have three of their own symbol in a row wins. It is possible to
; draw if there ends up being nowhere to go but nobody won yet.

(define game?
  (list/c (cons/c (integer-in 0 2) (integer-in 0 2))))

(define (player game)
  (cond [(even? (length game)) 'nought]
        [(odd? (length game)) 'cross]))

(define (board game)
  (match game
    ['() (build-vector 9 (λ (i) 'blank))]
    [(cons (cons x y) prev-game)
     (let* ([i (+ x (* y 3))]
            [v (vector-ref (board prev-game) i)])
       (build-vector 9 (λ (j)
                         (if (= i j)
                             (if (eq? v 'blank)
                                 (player prev-game)
                                 (raise-arguments-error 'board "illegal move" "game" game))
                             (vector-ref (board prev-game) j)))))]))

(module+ test
  (check-equal? (board '((0 . 0)))
                (vector 'nought 'blank 'blank
                        'blank 'blank 'blank
                        'blank 'blank 'blank)))

(define (board-value board coords)
  (match-let ([(cons x y) coords])
    (vector-ref board (+ x (* y 3)))))

(define lines
  '(((0 . 0) (0 . 1) (0 . 2))
    ((1 . 0) (1 . 1) (1 . 2))
    ((2 . 0) (2 . 1) (2 . 2))
    ((0 . 0) (1 . 0) (2 . 0))
    ((0 . 1) (1 . 1) (2 . 1))
    ((0 . 2) (1 . 2) (2 . 2))
    ((0 . 0) (1 . 1) (2 . 2))
    ((2 . 0) (1 . 1) (0 . 2))))

(define (winner game)
  (let* ([board (board game)]
         [winning-lines
          (filter
           (λ (line)
             (match-let ([(list first second third)
                          (map (curry board-value board) line)])
               (and
                (not (eq? first 'blank))
                (eq? first second) (eq? second third))))
           lines)])
    (if (null? winning-lines)
        #f
        (board-value board (car (car winning-lines))))))

(module+ test
  (check-equal? (winner '((0 . 2) (2 . 1) (0 . 1) (2 . 0) (0 . 0)))
                'nought))

(define (board-value->string value)
  (match value
    ['nought "O"]
    ['cross "X"]
    ['blank "-"]))

(define (board->string board)
  (string-join
   (list
    (string-join (map (λ (coord) (board-value->string (board-value board coord))) '((0 . 0) (1 . 0) (2 . 0))))
    (string-join (map (λ (coord) (board-value->string (board-value board coord))) '((0 . 1) (1 . 1) (2 . 1))))
    (string-join (map (λ (coord) (board-value->string (board-value board coord))) '((0 . 2) (1 . 2) (2 . 2)))))
   "\n"))

(module+ test
  (check-equal? (board->string (board '()))
                "- - -\n- - -\n- - -"))
   
(define (present-game)
  (define (present-game-iter game)
    (displayln (board->string (board game)))
    (displayln (format "Next move: ~a" (board-value->string (player game))))
    (match-let* ([move (read-line)]
                 [(list x y) (map string->number (string-split move))]
                 [new-game (cons (cons x y) game)]
                 [winner (winner new-game)])
      (if winner
          (begin
            (displayln (board->string (board new-game)))
            (displayln (format "Winner: ~a" (board-value->string winner))))
          (present-game-iter new-game))))
  (present-game-iter '()))

(present-game)