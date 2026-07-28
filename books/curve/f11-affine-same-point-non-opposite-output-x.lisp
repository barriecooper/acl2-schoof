(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-output-x")
(include-book "f11-affine-same-point-non-opposite-slope")

; Direct named-operation substitution into the transparent generic body.
(defun f11-affine-same-point-non-opposite-output-x (first)
  (let ((slope (f11-affine-same-point-non-opposite-slope first)))
    (f11-add
     (f11-mul slope slope)
     (f11-neg
      (f11-mul
       (f11-add (f11-one) (f11-one))
       (f11-affine-coordinates-x first))))))

; At (2,4), slope 3 gives x3 = 3*3 - (1+1)*2 = 9-4 = 5.
(assert-event
 (and (equal (f11-affine-same-point-non-opposite-slope '(2 4)) 3)
      (equal (f11-mul 3 3) 9)
      (equal (f11-add (f11-one) (f11-one)) 2)
      (equal (f11-mul 2 (f11-affine-coordinates-x '(2 4))) 4)
      (equal (f11-affine-same-point-non-opposite-output-x '(2 4)) 5)))

(verify-guards f11-affine-same-point-non-opposite-output-x)
