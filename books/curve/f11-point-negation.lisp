(in-package "GFIELD")

(include-book "point-negation")
(include-book "f11-points")

(defun f11-curve-point-neg (point)
  (let ((point (f11-curve-point-fix point)))
    (if (f11-curve-point-infinity-p point)
        (f11-curve-point-infinity)
      (f11-curve-point-affine
       (f11-affine-coordinates-x
        (f11-curve-point-affine-coordinates-get point))
       (f11-neg
        (f11-affine-coordinates-y
         (f11-curve-point-affine-coordinates-get point)))))))

(assert-event (equal (f11-curve-point-neg '(:infinity)) '(:infinity)))
(assert-event (equal (f11-curve-point-neg
                      (f11-curve-point-neg '(:infinity)))
                     '(:infinity)))
(assert-event (equal (f11-curve-point-neg '(:affine (2 4)))
                     '(:affine (2 7))))
(assert-event (f11-short-weierstrass-curve-point-p '(:affine (2 7))))
(assert-event (equal (f11-curve-point-neg
                      (f11-curve-point-neg '(:affine (2 4))))
                     '(:affine (2 4))))
(assert-event (equal (f11-curve-point-neg '(:affine (13 15)))
                     '(:affine (2 7))))
(assert-event (equal (f11-curve-point-neg '(:affine (2 5)))
                     '(:affine (2 6))))
(assert-event (f11-curve-point-representation-p
               (f11-curve-point-neg '(:affine (2 5)))))
(assert-event (not (f11-short-weierstrass-curve-point-p
                    (f11-curve-point-neg '(:affine (2 5))))))
(assert-event (equal (f11-curve-point-neg 'bad) '(:infinity)))
(assert-event (equal (f11-curve-point-neg '(:affine bad)) '(:infinity)))
(assert-event (equal (f11-curve-point-neg (f11-curve-point-neg 'bad))
                     (f11-curve-point-fix 'bad)))
(assert-event (equal (f11-curve-point-neg
                      (f11-curve-point-neg '(:unknown (2 4))))
                     (f11-curve-point-fix '(:unknown (2 4)))))

(verify-guards f11-curve-point-neg)
