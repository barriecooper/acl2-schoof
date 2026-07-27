(in-package "GFIELD")

(include-book "affine-distinct-x-output-x")
(include-book "f11-affine-distinct-x-slope")

; Named-operation substitution of F11 operations and accessors into the generic
; transparent formula; execution evidence, not a second mathematical theory.
(defun f11-affine-distinct-x-output-x (first second)
  (let ((slope (f11-affine-distinct-x-slope first second)))
    (f11-add
     (f11-add (f11-mul slope slope)
              (f11-neg (f11-affine-coordinates-x first)))
     (f11-neg (f11-affine-coordinates-x second)))))

(assert-event
 (and (equal (f11-affine-pair-classify '(1 2) '(3 6)) :distinct-x)
      (equal (f11-affine-distinct-x-slope '(1 2) '(3 6)) 2)
      (equal (f11-mul 2 2) 4)
      (equal (f11-add 4 (f11-neg (f11-affine-coordinates-x '(1 2)))) 3)
      (equal (f11-affine-distinct-x-output-x '(1 2) '(3 6)) 0)))

(assert-event
 (and (equal (f11-affine-distinct-x-slope '(2 4) '(3 9)) 5)
      (equal (f11-mul 5 5) 3)
      (equal (f11-add 3 (f11-neg 2)) 1)
      (equal (f11-affine-distinct-x-output-x '(2 4) '(3 9)) 9)))

(assert-event
 (and (equal (f11-affine-distinct-x-slope '(1 5) '(2 2)) 8)
      (equal (f11-mul 8 8) 9)
      (equal (f11-add 9 (f11-neg 1)) 8)
      (equal (f11-affine-distinct-x-output-x '(1 5) '(2 2)) 6)))

(assert-event
 (and (equal (f11-affine-coordinates-fix '(12 13)) '(1 2))
      (equal (f11-affine-coordinates-fix '(14 17)) '(3 6))
      (equal (f11-affine-distinct-x-output-x '(12 13) '(14 17)) 0)))

(assert-event
 (and (equal (f11-affine-coordinates-fix 'bad) '(0 0))
      (equal (f11-affine-distinct-x-slope 'bad '(3 6)) 2)
      (equal (f11-mul 2 2) 4)
      (equal (f11-add 4 (f11-neg (f11-affine-coordinates-x 'bad))) 4)
      (equal (f11-affine-distinct-x-output-x 'bad '(3 6)) 1)))

; Equal x is outside the intended branch.  Seven is inherited total
; programming semantics, not a mathematical secant output-coordinate claim.
(assert-event
 (and (not (equal (f11-affine-pair-classify '(2 4) '(2 7)) :distinct-x))
      (equal (f11-affine-distinct-x-slope '(2 4) '(2 7)) 0)
      (equal (f11-mul 0 0) 0)
      (equal (f11-add 0 (f11-neg 2)) 9)
      (equal (f11-affine-distinct-x-output-x '(2 4) '(2 7)) 7)))

(verify-guards f11-affine-distinct-x-output-x)
