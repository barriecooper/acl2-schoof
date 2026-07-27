(in-package "GFIELD")

(include-book "affine-distinct-x-output-y")
(include-book "f11-affine-distinct-x-output-x")

; Named-operation substitution of F11 operations and accessors into the generic
; transparent formula; execution evidence, not a second mathematical theory.
(defun f11-affine-distinct-x-output-y (first second)
  (let ((slope (f11-affine-distinct-x-slope first second))
        (output-x (f11-affine-distinct-x-output-x first second)))
    (f11-add
     (f11-mul
      slope
      (f11-add (f11-affine-coordinates-x first) (f11-neg output-x)))
     (f11-neg (f11-affine-coordinates-y first)))))

(assert-event
 (and (equal (f11-affine-pair-classify '(1 2) '(3 6)) :distinct-x)
      (equal (f11-affine-distinct-x-slope '(1 2) '(3 6)) 2)
      (equal (f11-affine-distinct-x-output-x '(1 2) '(3 6)) 0)
      (equal (f11-add 1 (f11-neg 0)) 1)
      (equal (f11-mul 2 1) 2)
      (equal (f11-affine-distinct-x-output-y '(1 2) '(3 6)) 0)))

(assert-event
 (and (equal (f11-affine-distinct-x-slope '(2 4) '(3 9)) 5)
      (equal (f11-affine-distinct-x-output-x '(2 4) '(3 9)) 9)
      (equal (f11-add 2 (f11-neg 9)) 4)
      (equal (f11-mul 5 4) 9)
      (equal (f11-affine-distinct-x-output-y '(2 4) '(3 9)) 5)))

(assert-event
 (and (equal (f11-affine-distinct-x-slope '(1 5) '(2 2)) 8)
      (equal (f11-affine-distinct-x-output-x '(1 5) '(2 2)) 6)
      (equal (f11-add 1 (f11-neg 6)) 6)
      (equal (f11-mul 8 6) 4)
      (equal (f11-affine-distinct-x-output-y '(1 5) '(2 2)) 10)))

(assert-event
 (and (equal (f11-affine-coordinates-fix '(12 13)) '(1 2))
      (equal (f11-affine-coordinates-fix '(14 17)) '(3 6))
      (equal (f11-affine-coordinates-x '(12 13)) 1)
      (equal (f11-affine-coordinates-y '(12 13)) 2)
      (equal (f11-affine-distinct-x-slope '(12 13) '(14 17)) 2)
      (equal (f11-affine-distinct-x-output-x '(12 13) '(14 17)) 0)
      (equal (f11-add 1 (f11-neg 0)) 1)
      (equal (f11-mul 2 1) 2)
      (equal (f11-affine-distinct-x-output-y '(12 13) '(14 17)) 0)))

(assert-event
 (and (equal (f11-affine-coordinates-fix 'bad) '(0 0))
      (equal (f11-affine-coordinates-x 'bad) 0)
      (equal (f11-affine-coordinates-y 'bad) 0)
      (equal (f11-affine-distinct-x-slope 'bad '(3 6)) 2)
      (equal (f11-affine-distinct-x-output-x 'bad '(3 6)) 1)
      (equal (f11-add 0 (f11-neg 1)) 10)
      (equal (f11-mul 2 10) 9)
      (equal (f11-affine-distinct-x-output-y 'bad '(3 6)) 9)))

; Equal x is outside the intended branch.  Seven is inherited total
; programming semantics, not a mathematical secant output-coordinate claim.
(assert-event
 (and (not (equal (f11-affine-pair-classify '(2 4) '(2 7)) :distinct-x))
      (equal (f11-affine-distinct-x-slope '(2 4) '(2 7)) 0)
      (equal (f11-affine-distinct-x-output-x '(2 4) '(2 7)) 7)
      (equal (f11-add 2 (f11-neg 7)) 6)
      (equal (f11-mul 0 6) 0)
      (equal (f11-affine-distinct-x-output-y '(2 4) '(2 7)) 7)))

(verify-guards f11-affine-distinct-x-output-y)
