(in-package "GPOLY")
(include-book "../books/polynomial/generic/pfield-instance")
(assert-event (equal (f7-normalize nil) nil))
(assert-event (equal (f7-normalize '(0 0 0)) nil))
(assert-event (equal (f7-normalize '(1 2 0)) '(1 2)))
(assert-event (equal (f7-normalize '(1 2 0 0)) '(1 2)))
(assert-event (equal (f7-poly-degree nil) -1))
(assert-event (equal (f7-poly-degree '(3)) 0))
(assert-event (equal (f7-poly-degree '(1 2 3)) 2))
(assert-event (equal (f7-poly-degree '(1 2 0 0)) 1))
(assert-event (equal (f7-poly-leading-coefficient nil) 0))
(assert-event (equal (f7-poly-leading-coefficient '(3)) 3))
(assert-event (equal (f7-poly-leading-coefficient '(1 2 3)) 3))
(assert-event (equal (f7-poly-leading-coefficient '(1 8 14 0)) 1))
(assert-event (equal (f7-poly-degree '(1 2 . bad-tail)) 1))
(assert-event (equal (f7-poly-leading-coefficient '(1 2 . bad-tail)) 2))
(assert-event (equal (f7-normalize '(1 0 2 0)) '(1 0 2)))
(assert-event (equal (f7-fix-coefficients '(-1 8 15)) '(6 1 1)))
(assert-event (equal (f7-normalize (f7-normalize '(1 2 0 0))) '(1 2)))
(assert-event (equal (f7-poly-scale 3 nil) nil))
(assert-event (equal (f7-poly-scale 3 '(0 0 0)) nil))
(assert-event (equal (f7-poly-scale 0 '(1 2 3)) nil))
(assert-event (equal (f7-poly-scale 1 '(1 2 0)) '(1 2)))
(assert-event (equal (f7-poly-scale 9 '(1 2 3)) '(2 4 6)))
(assert-event (equal (f7-poly-scale 3 'malformed-poly) nil))
(assert-event (equal (f7-poly-scale 3 '(1 2 . malformed-tail)) '(3 6)))
(assert-event (equal (f7-poly-scale 3 '(1 2 0 0)) '(3 6)))
(assert-event (equal (f7-poly-scale 3 '(2)) '(6)))
(assert-event (equal (f7-poly-scale 3 '(1 2)) '(3 6)))
(assert-event (equal (f7-poly-scale 3 '(1 2 3)) '(3 6 2)))
(assert-event (equal (f7-poly-scale -1 '(1 2 3)) '(6 5 4)))
(assert-event (equal (f7-poly-scale 9 '(1 8 14 0)) '(2 2)))
; F7 representatives exercise the divisor-scaling scalar boundary: 9
; requires FIELD-FIX and fixes to the nonzero scalar 2; the remaining cases
; cover one, negative one, another nontrivial unit, and total divisor shapes.
(assert-event (equal (gfield::f7-fix 9) 2))
(assert-event (not (equal (gfield::f7-fix 9) 0)))
(assert-event (equal (f7-poly-scale 9 '(1 1)) '(2 2)))
(assert-event (equal (f7-poly-scale 1 '(1 1)) '(1 1)))
(assert-event (equal (f7-poly-scale -1 '(1 1)) '(6 6)))
(assert-event (equal (f7-poly-scale 3 '(1 1)) '(3 3)))
(assert-event (equal (f7-poly-scale 3 'malformed-divisor) nil))
(assert-event (equal (f7-poly-scale 3 '(1 1 . malformed-tail)) '(3 3)))
(assert-event (equal (f7-poly-scale 3 '(1 1 0 0)) '(3 3)))
(assert-event (equal (f7-poly-scale 3 '(8 -1 0)) '(3 4)))
(assert-event
 (equal (f7-poly-leading-coefficient (f7-poly-scale 3 '(1 2 3))) 2))
; Monic normalization keeps constant-first order and treats normalized zero
; explicitly, including malformed and noncanonical representations.
(assert-event (equal (f7-poly-monic-normalize nil) nil))
(assert-event (equal (f7-poly-monic-normalize 'malformed-poly) nil))
(assert-event
 (equal (f7-poly-monic-normalize '(1 2 . malformed-tail)) '(4 1)))
(assert-event (equal (f7-poly-monic-normalize '(0 0 0)) nil))
(assert-event (equal (f7-poly-monic-normalize '(7)) nil))
(assert-event (equal (f7-poly-monic-normalize '(0 0 0 0 0)) nil))
(assert-event
 (equal (f7-poly-monic-normalize '(8 -1 10 0)) '(5 2 1)))
(assert-event (equal (f7-poly-monic-normalize '(1)) '(1)))
(assert-event (equal (f7-poly-monic-normalize '(3)) '(1)))
(assert-event (equal (f7-poly-monic-normalize '(-2)) '(1)))
(assert-event (equal (f7-poly-monic-normalize '(-1)) '(1)))
(assert-event (equal (f7-poly-monic-normalize '(1 2)) '(4 1)))
(assert-event (equal (f7-poly-monic-normalize '(1 2 3)) '(5 3 1)))
; Concrete F7 operands used by the generic dividend- and divisor-position
; divisibility regressions: this quadratic changes every coefficient, while
; fixed/noncanonical representations still select the same monic polynomial.
(assert-event (equal (f7-poly-monic-normalize '(2 4 6)) '(5 3 1)))
(assert-event (equal (f7-poly-monic-normalize '(9 11 13 0)) '(5 3 1)))
(assert-event
 (equal (f7-poly-monic-normalize '(2 4 6 . malformed-tail)) '(5 3 1)))
(assert-event
 (equal (f7-poly-monic-normalize '(8 9 10 0 0)) '(5 3 1)))
(assert-event
 (equal (f7-poly-monic-normalize (f7-normalize '(8 9 10 0 0)))
        (f7-poly-monic-normalize '(8 9 10 0 0))))
(assert-event
 (equal (equal (f7-poly-monic-normalize '(7 14)) nil)
        (equal (f7-normalize '(7 14)) nil)))
(assert-event
 (equal (consp (f7-poly-monic-normalize '(1 2 0)))
        (consp (f7-normalize '(1 2 0)))))
(assert-event
 (f7-canonical-polynomial-p (f7-poly-monic-normalize '(8 9 10 0))))
(assert-event
 (equal (f7-normalize (f7-poly-monic-normalize '(8 9 10 0)))
        (f7-poly-monic-normalize '(8 9 10 0))))
(assert-event
 (equal (f7-poly-leading-coefficient (f7-poly-monic-normalize '(0 0))) 0))
(assert-event
 (equal (f7-poly-leading-coefficient (f7-poly-monic-normalize '(1 2))) 1))
(assert-event
 (equal (f7-poly-leading-coefficient
         (f7-poly-monic-normalize '(1 2 3)))
        1))
(defthm normalized-output-is-canonical-regression
  (canonical-polynomial-p (normalize xs)))
(defthm pfield-generated-normalization-preserves-evaluation-regression
  (equal (pfield-eval (pfield-normalize poly) x)
         (pfield-eval poly x))
  :hints (("Goal" :by pfield-normalize-preserves-eval-from-generic)))
(assert-event (equal (f7-eval nil 3) 0))
(assert-event (equal (f7-eval '(9) 4) 2))
(assert-event (equal (f7-eval '(1 2 3) 2) 3))
(assert-event (equal (f7-eval '(6 6) 6) 0))
(assert-event (equal (f7-eval (f7-normalize '(1 2 3 0 0)) 2)
                     (f7-eval '(1 2 3 0 0) 2)))
(assert-event (equal (f7-normalize '(-1 8 15 0)) '(6 1 1)))
(assert-event (equal (f7-eval (f7-normalize '(-1 8 15 0)) 2) 5))
(defthm f7-generated-normalization-preserves-evaluation-regression
  (equal (f7-eval (f7-normalize poly) x)
         (f7-eval poly x))
  :hints (("Goal" :by f7-normalize-preserves-eval-from-generic)))
(assert-event (equal (f7-poly-add '(1 2) '(6 5)) nil))
(assert-event (equal (f7-poly-add '(1 2) '(2 5)) '(3)))
(assert-event (equal (f7-poly-neg '(1 2)) '(6 5)))
(assert-event (equal (f7-poly-sub '(1 2) '(1 2)) nil))

; Concrete total one-step division: exact term, next state, normalization,
; decrease, and reconstruction are checked rather than only list shape.
(assert-event
 (equal (f7-poly-division-step '(1 0 3) '(1 1))
        (cons '(0 3) '(1 4))))
(assert-event
 (and (equal (f7-poly-division-step-term '(1 0 3) '(1 1)) '(0 3))
      (equal (f7-poly-division-step-next '(1 0 3) '(1 1)) '(1 4))
      (f7-canonical-polynomial-p
       (f7-poly-division-step-next '(1 0 3) '(1 1)))
      (< (len (f7-poly-division-step-next '(1 0 3) '(1 1)))
         (len (f7-normalize '(1 0 3))))
      (equal (f7-poly-add
              (f7-poly-mul '(0 3) (f7-normalize '(1 1))) '(1 4))
             (f7-normalize '(1 0 3)))))
(assert-event
 (equal (f7-poly-division-step '(-6 8 10 0 0) '(8 8 0))
        (cons '(0 3) '(1 5))))
(assert-event
 (equal (f7-poly-division-step '(1 2 . malformed-tail) '(1))
        (cons '(0 2) '(1))))
(assert-event
 (equal (f7-poly-division-step '(1 2) '(1 0 1))
        (cons nil '(1 2))))
(assert-event
 (equal (f7-poly-division-step '(1 2) '(3))
        (cons '(0 3) '(1))))
(assert-event
 (equal (f7-poly-division-step '(1 2 0) '(0 0 . malformed-tail))
        (cons nil '(1 2))))
(assert-event
 (equal (f7-poly-add (f7-normalize '(1 2 0)) '(3 4))
        (f7-poly-add '(1 2 0) '(3 4))))
(assert-event
 (equal (f7-poly-add '(1 2) (f7-normalize '(3 4 0)))
        (f7-poly-add '(1 2) '(3 4 0))))
(assert-event
 (equal (f7-poly-add '(1 2) '(3 4))
        (f7-poly-add '(3 4) '(1 2))))
(assert-event
 (equal (f7-poly-add (f7-poly-add '(1 2) '(3 4)) '(5 6))
        (f7-poly-add '(1 2) (f7-poly-add '(3 4) '(5 6)))))
(assert-event
 (equal (f7-poly-add '(1 2) (f7-poly-neg '(1 2))) nil))
(assert-event
 (equal (f7-poly-add '(1 2) (f7-poly-sub '(3 4) '(1 2))) '(3 4)))
(assert-event
 (equal (f7-poly-add '(1 2) (f7-poly-sub '(1 2) '(1 2))) '(1 2)))
(assert-event
 (equal (f7-poly-add nil (f7-poly-sub '(3 4) nil)) '(3 4)))
(assert-event
 (equal (f7-poly-add '(1 2) (f7-poly-sub nil '(1 2))) nil))
(assert-event
 (equal (f7-poly-add '(2) (f7-poly-sub '(5) '(2))) '(5)))
(assert-event (equal (f7-poly-scale 3 '(1 2 3)) '(3 6 2)))
(assert-event (equal (f7-poly-scale 0 '(1 2 3)) nil))
(assert-event (equal (f7-poly-scale 1 '(1 2 0 0)) '(1 2)))
(assert-event (equal (f7-poly-scale 2 '(1 0 4)) '(2 0 1)))
(assert-event (equal (f7-poly-scale 2 '(1 . bad-tail)) '(2)))
(assert-event (f7-canonical-polynomial-p
               (f7-raw-mul '(1 2) '(3 4))))
(assert-event (equal (f7-normalize (f7-raw-mul '(1 2) '(3 4)))
                     (f7-raw-mul '(1 2) '(3 4))))
(assert-event (equal (f7-poly-mul '(1 2) '(3 4)) '(3 3 1)))
(assert-event (consp (f7-poly-mul '(1 2) '(3 4))))
(assert-event (equal (f7-poly-degree (f7-poly-mul '(1 2) '(3 4))) 2))
(assert-event
 (equal (f7-poly-leading-coefficient (f7-poly-mul '(1 2) '(3 4))) 1))
(assert-event
 (equal (f7-poly-leading-coefficient (f7-poly-mul '(1 2) '(3 4)))
        (gfield::f7-mul 2 4)))
(assert-event (f7-canonical-polynomial-p (f7-raw-mul '(2) '(4))))
(assert-event (equal (f7-normalize (f7-raw-mul '(2) '(4))) '(1)))
(assert-event (equal (f7-poly-mul '(2) '(4)) '(1)))
(assert-event (equal (f7-poly-degree (f7-poly-mul '(2) '(4))) 0))
(assert-event
 (equal (f7-poly-leading-coefficient (f7-poly-mul '(2) '(4)))
        (gfield::f7-mul 2 4)))
(assert-event (equal (f7-poly-mul nil '(1 2)) nil))
(assert-event (equal (f7-poly-mul '(1 2) nil) nil))
(assert-event (equal (f7-poly-mul '(1) '(1 2)) '(1 2)))
(assert-event (equal (f7-poly-mul '(1 2) '(1)) '(1 2)))
(assert-event (equal (f7-poly-mul '(7 14) '(3 4)) nil))
(assert-event (equal (f7-poly-mul '(1 . bad-tail) '(3 4)) '(3 4)))
(assert-event
 (equal (f7-eval (f7-poly-mul '(1 2) '(3 4)) 2)
        (gfield::f7-mul (f7-eval '(1 2) 2) (f7-eval '(3 4) 2))))
(assert-event
 (equal (f7-poly-mul '(1 2) (f7-poly-add '(3 4) '(5 6)))
        (f7-poly-add (f7-poly-mul '(1 2) '(3 4))
                     (f7-poly-mul '(1 2) '(5 6)))))
(assert-event
 (equal (f7-poly-mul (f7-poly-add '(1 2) '(3 4)) '(5 6))
        (f7-poly-add (f7-poly-mul '(1 2) '(5 6))
                     (f7-poly-mul '(3 4) '(5 6)))))
(assert-event (equal (f7-poly-mul '(1 2) '(3 4))
                     (f7-poly-mul '(3 4) '(1 2))))
(assert-event
 (equal (f7-poly-mul (f7-poly-mul '(1 2) '(3 4)) '(5 6))
        (f7-poly-mul '(1 2) (f7-poly-mul '(3 4) '(5 6)))))
(assert-event (equal (f7-const 0) nil))
(assert-event (equal (f7-const 1) '(1)))
(assert-event (equal (f7-const 8) '(1)))
(assert-event (equal (f7-eval (f7-const 5) 0) 5))
(assert-event (equal (f7-eval (f7-const 5) 6) 5))
(assert-event
 (equal (f7-poly-add (f7-const 3) (f7-const 4)) nil))
(assert-event
 (equal (f7-poly-mul (f7-const 3) (f7-const 5)) (f7-const 1)))
(assert-event
 (equal (f7-poly-mul '(1 2 3) (f7-const 4))
        (f7-poly-scale 4 '(1 2 3))))
(assert-event (equal (f7-poly-pow '(1 2) 0) '(1)))
(assert-event (equal (f7-poly-pow '(1 2 0) 1) '(1 2)))
(assert-event (equal (f7-poly-pow nil 0) '(1)))
(assert-event (equal (f7-poly-pow nil 5) nil))
; Hand check: (1+2X)^2 = 1+4X+4X^2 over F_7.
(assert-event (equal (f7-poly-pow '(1 2) 2) '(1 4 4)))
(assert-event (equal (f7-poly-pow '(1 1) 3) '(1 3 3 1)))
(assert-event
 (equal (f7-poly-pow-fast (f7-polynomial-one) (f7-normalize '(1 2 0)) 9)
        (f7-poly-pow-spec (f7-normalize '(1 2 0)) 9)))
(assert-event
 (equal (f7-normalize (f7-poly-pow '(1 2 0) 17))
        (f7-poly-pow '(1 2 0) 17)))
(assert-event
 (equal (f7-eval (f7-poly-pow '(1 1) 16) 2)
        (gfield::f7-pow (f7-eval '(1 1) 2) 16)))
(assert-event
 (equal (f7-eval (f7-poly-pow '(1 2) 11) 3)
        (gfield::f7-pow (f7-eval '(1 2) 3) 11)))
(assert-event
 (equal (f7-poly-pow '(1 2) (+ 3 4))
        (f7-poly-mul (f7-poly-pow '(1 2) 3)
                     (f7-poly-pow '(1 2) 4))))
(assert-event
 (equal (f7-poly-pow (f7-poly-pow '(1 2) 3) 4)
        (f7-poly-pow '(1 2) 12)))
; Negative exponents retain the public NFIX-to-zero semantics.
(assert-event (equal (f7-poly-pow '(1 2) -3) '(1)))
; A constant base keeps the output small while exercising 21 low-bit steps.
(assert-event (equal (f7-poly-pow '(2) 1048576) '(2)))
