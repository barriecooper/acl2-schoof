(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-output-y")
(include-book "f11-affine-same-point-non-opposite-output-x")

; Named-operation substitution of F11 operations and accessors into the generic
; transparent formula; execution evidence, not a geometric doubling theorem.
(defun f11-affine-same-point-non-opposite-output-y (first)
  (let ((slope (f11-affine-same-point-non-opposite-slope first))
        (output-x (f11-affine-same-point-non-opposite-output-x first)))
    (f11-add
     (f11-mul
      slope
      (f11-add (f11-affine-coordinates-x first) (f11-neg output-x)))
     (f11-neg (f11-affine-coordinates-y first)))))

; At (2,4), m=3 and x3=5 give 2-5=8, 3*8=2, and y3=2-4=9.
(assert-event
 (and (equal (f11-affine-same-point-non-opposite-slope '(2 4)) 3)
      (equal (f11-affine-same-point-non-opposite-output-x '(2 4)) 5)
      (equal (f11-add 2 (f11-neg 5)) 8)
      (equal (f11-mul 3 8) 2)
      (equal (f11-affine-same-point-non-opposite-output-y '(2 4)) 9)))

(verify-guards f11-affine-same-point-non-opposite-output-y)
