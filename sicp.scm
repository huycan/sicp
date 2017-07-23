#lang sicp

; Chapter 1 - Building Abstractions with Procedure


(define (square x) (* x x))
(define (sum-of-squares x y) (+ (square x) (square y)))

(define (pow x n)
  (define (pow-iter product counter)
    (if (= counter 0)
        product
        (pow-iter (* product x) (- counter 1))))
  (pow-iter 1 n))


; Ex 1.5
; The following tests if interpreter uses normal-order evaluation
; - if normal-order, the arg evaluation will be delayed until required
; - since x=0, the second clause is not needed for evaluation
; - the procedure should finish with 0
; however, applicative-order will evaluate the args eagerly
; thus ends up in infinite recursion
(define (p) (p))
(define (test-normal-order x fn) (if (= x 0) 0 fn))
; (test-normal-order 0 (p))

; Ex 1.6
; cond, if are special expression, they are evaluated with normal-order
; If we replace them with procedure, the above eager evaluation will apply
(define (new-if predicate then-clause else-clause)
  (cond (predicate then-clause)
        (else else-clause)))
(define (test-normal-order2) (new-if #t 0 (p)))
; (test-normal-order2)

; Newton's method of finding square root
; Observation:
; - root has the property: root * root = x
; - if guess != root, then root is bound by guess, and x / guess
; - and avg(x, y) produces a number bound by x, y
; - and each iteration produces tighter bound then previous one
;   bound tends towards 0
; - thus, the method converges towards true root
(define (average x y) (/ (+ x y) 2))
(define (improve guess x)
  (average guess (/ x guess)))

; Ex 1.7
; This good-enough? does not work well for:
; - very small x
;   the difference between iteration is already too small
;   (sqrt 0.00000001)
; - very large x: due to limited precision arithmetics
;   large number decimal places usually do not fall within
;   (sqrt 10000000000000) -> 3162277.6640104805
;   the decimal precision of large number root will never fall within 0.001
;   thus causes infinite iteration
(define (wacky-good-enough? guess x)
  (< (abs (- (square guess) x)) 0.001))
(define (wacky-sqrt-iter guess x)
  (if (wacky-good-enough? guess x)
      guess
      (wacky-sqrt-iter (improve guess x) x)))
(define (wacky-sqrt x) (wacky-sqrt-iter 1.0 x))
;(wacky-sqrt 0.00000001)
;(wacky-sqrt 10000000000000)

; This alternative version checks change delta between guesses
; It works correctly because it uses the converging bound property of the method
(define (better-good-enough? guess next-guess)
  (< (/ (abs (- guess next-guess)) guess) 0.001))
(define (better-sqrt-iter guess x)
  (if (better-good-enough? guess (improve guess x))
      (improve guess x)
      (better-sqrt-iter (improve guess x) x)))
(define (sqrt x) (better-sqrt-iter 1.0 x))
(sqrt 0.00000001)
(sqrt 10000000000000)

; Ex 1.8
; cube root
(define (improve-cb guess x)
  (/ (+ (/ x (square guess)) (* 2 guess)) 3))
(define (cbrt-iter guess x)
  (if (better-good-enough? guess (improve-cb guess x))
      (improve-cb guess x)
      (cbrt-iter (improve-cb guess x) x)))
(define (cbrt x) (cbrt-iter 1.0 x))
(cbrt 1000000000000)

; Observation about process state
; - recursive-factorial implicitly maintains
;   the current process state - chain of deferred operations
;   in stack, i.e. (* 6 5 4 (recursive-factorial 3))
;   if we stop and resume the program at n=3, we lose all the info
;   about current chain, i.e. the first part (* 6 5 4)
; - iterative factorial explicitly maintains results
;   as states - in formal parameters (product, counter, num)
;   thus so long as we have the states we can resume process
;   at previous stop point, by executing the procedure
(define (recursive-factorial n)
  (if (= n 1)
      1
      (* n (recursive-factorial (- n 1)))))
(define (factorial n)
  (define (iter product counter)
    (if (> counter n)
        product
        (iter (* counter product)
              (+ counter 1))))
  (iter 1 1))
(recursive-factorial 6)
(factorial 6)

; Ex 1.10
; Ackermann
(define (A x y)
  (cond ((= y 0) 0)
        ((= x 0) (* 2 y))
        ((= y 1) 2)
        (else (A (- x 1) (A x (- y 1))))))
(A 1 10)
(A 2 4)
(A 3 3)

(define (f n) (A 0 n)) ; 2*n
(define (g n) (A 1 n)) ; 2^n
(define (h n) (A 2 n)) ; 2^(2^(2^(...n) exponent n times
(define (k n) (* 5 n n)) ; 5n^2
(= (f 4) 8)
(= (g 4) (pow 2 4))
(= (h 4) (pow 2 (pow 2 (pow 2 2))))

(define (fib n)
  (define (fib-iter a b count)
    (if (= count 0)
        b
        (fib-iter (+ a b) a (- count 1))))
  (fib-iter 1 0 n))
(fib 120)


(define (count-change amount)
  (define (cc amount kinds-of-coins)
    (cond ((= amount 0) 1)
          ((or (< amount 0) (= kinds-of-coins 0)) 0)
          (else (+ (cc amount
                       (- kinds-of-coins 1))
                   (cc (- amount
                          (first-denomination
                           kinds-of-coins))
                       kinds-of-coins)))))
  (define (first-denomination kinds-of-coins)
    (cond ((= kinds-of-coins 1) 1)
          ((= kinds-of-coins 2) 5)
          ((= kinds-of-coins 3) 10)
          ((= kinds-of-coins 4) 25)
          ((= kinds-of-coins 5) 50)))
  (cc amount 5))
(count-change 100)


; Ex 1.11
(define (f111-recur n)
  (if (< n 3)
      n
      (+ (f111-recur (- n 1))
         (* 2 (f111-recur (- n 2)))
         (* 3 (f111-recur (- n 3))))))
(f111-recur 20)

(define (f111-iter n)
  (define (f acc x y counter)
    (if (= counter 0)
        acc
        (f (+ acc (* 2 x) (* 3 y)) acc x (- counter 1))))
  (if (< n 3)
      n
      (f 4 2 1 (- n 3))))
(f111-iter 20)

; Ex 1.12
(define (pascal-tri row col)
  (cond ((= row 1) 1)
        ((or (= col 1)
             (= col row))
         1)
        (else (+ (pascal-tri (- row 1) (- col 1))
                 (pascal-tri (- row 1) col)))))
(pascal-tri 6 4)

; Ex 1.13
; fib(n) = n < 2 ? n : fib(n - 1) + fib(n - 2), for n >= 0
; (x is the closest integer to y)
; => (y - (x - 1)) < abs(x - y) < ((x + 1) - y)
; induction step: prove that phi^2 = 1 + phi and psi^2 = 1 + psi
; (hint golden ratio equation)
;
; why that psi though?
; a probable rationale: fib(1) - phi = psi
; since psi indeeds tends towards 0
; and the relation should hold for fib(n)
; guess that the equality between fib, phi and psi holds
; prove this guess by induction

; Ex 1.14
; space O(n)
; the longest substree recurs at least n times for 1-coin
; its height bounds other subtrees
;
; time O(2^n) - 2 calls each step, max n height

; Ex 1.15
; O(log n) space time, problem size reduced by a factor of 3 each step
; around log3 n steps to reach base case
(define (sine angle)
  (define (cube x) (* x x x))
  (define (p x) (- (* 3 x) (* 4 (cube x))))
  (if (not (> (abs angle) 0.1))
      1
      (p (sine (/ angle 3.0)))))
(sine 15)


(define (expt b n)
  (define (expt-iter b counter product)
  (if (= counter 0)
      product
      (expt-iter b
                (- counter 1)
                (* b product)))) 
  (expt-iter b n 1))

(define (even? n)
  (= (remainder n 2) 0))
(define (fast-expt b n)
  (cond ((= n 0) 1)
        ((even? n) (square (fast-expt b (/ n 2))))
        (else (* b (fast-expt b (- n 1))))))


; Ex 1.16
(define (fast-expt-iter b n)
  (define (iter a product n)
    (cond ((= n 0) product)
          ((even? n) (iter (square a) product (/ n 2)))
          (else (iter a (* product a) (- n 1)))))
  (iter b 1 n))
(fast-expt-iter 2 0)
(= (fast-expt-iter 2 0) (fast-expt 2 0))
(fast-expt-iter 2 1)
(= (fast-expt-iter 2 1) (fast-expt 2 1))
(fast-expt-iter 3 4)
(= (fast-expt-iter 3 4) (fast-expt 3 4))
(fast-expt-iter 3 23)
(= (fast-expt-iter 3 23) (fast-expt 3 23))
(fast-expt-iter 2 10)
(= (fast-expt-iter 2 10) (fast-expt 2 10))


(define (mult a b)
  (if (= b 0)
      0
      (+ a (mult a (- b 1)))))


; Ex 1.17
(define (double a) (* 2 a))
(define (halve a) (/ a 2))
(define (fast-mult a b)
  (cond ((= b 0) 0)
        ((even? b) (double (fast-mult a (halve b))))
        (else (+ a (fast-mult a (- b 1))))))
(fast-mult 3 0)
(fast-mult 3 1)
(fast-mult 3 2)
(fast-mult 3 3)

; Ex 1.18
(define (fast-mult-iter a b)
  (define (iter x n)
    (cond ((= n 0) x)
          ((even? n) (iter (+ (double x) a) (halve n)))
          (else (iter (+ x a) (- n 1)))))
  (iter 0 b))
(fast-mult-iter 3 0)
(fast-mult-iter 3 1)
(fast-mult-iter 3 2)
(fast-mult-iter 3 3)

; Ex 1.19