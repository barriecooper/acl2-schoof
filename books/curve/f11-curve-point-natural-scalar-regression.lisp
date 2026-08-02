(in-package "GFIELD")

(include-book "curve-point-natural-scalar")
(include-book "f11-curve-point-pair-output-point")

(defun f11-curve-point-nat-mul (n point)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n)
        (f11-curve-point-infinity)
      (f11-curve-point-pair-output-point
       point (f11-curve-point-nat-mul (1- n) point)))))

(verify-guards f11-curve-point-nat-mul)

(assert-event
 (and (equal (f11-curve-point-nat-mul 0 '(:affine (2 4))) '(:infinity))
      (equal (f11-curve-point-nat-mul 1 '(:affine (2 4))) '(:affine (2 4)))
      (equal (f11-curve-point-nat-mul 2 '(:affine (2 4))) '(:affine (5 9)))
      (equal (f11-curve-point-nat-mul 3 '(:affine (2 4))) '(:affine (8 8)))
      (equal (f11-curve-point-nat-mul 11 '(:infinity)) '(:infinity))
      (equal (f11-curve-point-nat-mul 5 '(:affine (2 4)))
             (f11-curve-point-pair-output-point
              (f11-curve-point-nat-mul 2 '(:affine (2 4)))
              (f11-curve-point-nat-mul 3 '(:affine (2 4)))))))
