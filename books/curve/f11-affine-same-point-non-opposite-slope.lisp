(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-slope")
(include-book "f11-affine-pair-classification")

; Direct named-operation substitution into the transparent generic body.
(defun f11-affine-same-point-non-opposite-slope (first)
  (f11-div
   (f11-add
    (f11-mul
     (f11-add (f11-add (f11-one) (f11-one))
              (f11-one))
     (f11-mul (f11-affine-coordinates-x first)
              (f11-affine-coordinates-x first)))
    (f11-fix (f11-short-weierstrass-a)))
   (f11-add (f11-affine-coordinates-y first)
            (f11-affine-coordinates-y first))))

; (2,4) is on y^2=x^3+x+6.  The classifier chooses the equal,
; non-opposite branch; numerator 2 divided by denominator 8 gives slope 3.
(assert-event
 (and (f11-short-weierstrass-affine-point-p '(2 4))
      (equal (f11-affine-pair-classify '(2 4) '(2 4))
             :same-point-non-opposite)
      (equal (f11-add (f11-add (f11-one) (f11-one))
                      (f11-one))
             3)
      (equal (f11-add
              (f11-mul 3 (f11-mul 2 2))
              (f11-fix (f11-short-weierstrass-a)))
             2)
      (equal (f11-add 4 4) 8)
      (equal (f11-inv 8) 7)
      (equal (f11-affine-same-point-non-opposite-slope '(2 4)) 3)
      (equal (f11-mul 3 8) 2)))

(verify-guards f11-affine-same-point-non-opposite-slope)
