(in-package "GFIELD")

(include-book "affine-doubling-relation")
(include-book "f11-affine-same-point-non-opposite-output")
(include-book "f11-short-weierstrass")

(defun f11-affine-doubling-relation-p (input slope output)
  (and
   (f11-short-weierstrass-affine-point-p input)
   (not (equal (f11-affine-coordinates-y input)
               (f11-neg (f11-affine-coordinates-y input))))
   (equal
    (f11-mul
     (f11-fix slope)
     (f11-add (f11-affine-coordinates-y input)
              (f11-affine-coordinates-y input)))
    (f11-add
     (f11-mul
      (f11-add (f11-add (f11-one) (f11-one)) (f11-one))
      (f11-mul (f11-affine-coordinates-x input)
               (f11-affine-coordinates-x input)))
     (f11-fix (f11-short-weierstrass-a))))
   (equal
    (f11-add
     (f11-affine-coordinates-x output)
     (f11-mul (f11-add (f11-one) (f11-one))
              (f11-affine-coordinates-x input)))
    (f11-mul (f11-fix slope) (f11-fix slope)))
   (equal
    (f11-add (f11-affine-coordinates-y output)
             (f11-affine-coordinates-y input))
    (f11-mul
     (f11-fix slope)
     (f11-add (f11-affine-coordinates-x input)
              (f11-neg (f11-affine-coordinates-x output)))))
   (f11-short-weierstrass-affine-point-p output)))

(assert-event
 (let* ((input '(2 4))
        (slope (f11-affine-same-point-non-opposite-slope input))
        (output (f11-affine-same-point-non-opposite-output input)))
   (and (not (equal (f11-affine-coordinates-y input)
                    (f11-neg (f11-affine-coordinates-y input))))
        (equal slope 3)
        (equal output '(5 9))
        (f11-affine-doubling-relation-p input slope output))))

(verify-guards f11-affine-doubling-relation-p)
