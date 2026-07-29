(in-package "GFIELD")

(include-book "curve-point-pair-output-point")
(include-book "f11-affine-pair-output-point")
(include-book "f11-points")

(defun f11-curve-point-pair-output-point (first second)
  (let* ((first (f11-curve-point-fix first))
         (second (f11-curve-point-fix second)))
    (cond ((f11-curve-point-infinity-p first) second)
          ((f11-curve-point-infinity-p second) first)
          (t (f11-affine-pair-output-point
              (f11-curve-point-affine-coordinates-get first)
              (f11-curve-point-affine-coordinates-get second))))))

(assert-event
 (and
  (equal (f11-curve-point-pair-output-point '(:infinity) '(:infinity))
         '(:infinity))
  (equal (f11-curve-point-pair-output-point '(:infinity) '(:affine (2 4)))
         '(:affine (2 4)))
  (equal (f11-curve-point-pair-output-point '(:affine (2 4)) '(:infinity))
         '(:affine (2 4)))
  (equal (f11-curve-point-pair-output-point '(:affine (2 4))
                                             '(:affine (3 5)))
         '(:affine (7 2)))
  (equal (f11-curve-point-pair-output-point '(:affine (2 4))
                                             '(:affine (2 7)))
         '(:infinity))
  (equal (f11-curve-point-pair-output-point '(:affine (2 4))
                                             '(:affine (2 4)))
         '(:affine (5 9)))))

(assert-event
 (and
  (f11-curve-point-representation-p
   (f11-curve-point-pair-output-point '(:infinity) '(:infinity)))
  (f11-curve-point-representation-p
   (f11-curve-point-pair-output-point '(:infinity) '(:affine (2 4))))
  (f11-curve-point-representation-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:infinity)))
  (f11-curve-point-representation-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:affine (3 5))))
  (f11-curve-point-representation-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:affine (2 7))))
  (f11-curve-point-representation-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:affine (2 4))))
  (f11-short-weierstrass-curve-point-p
   (f11-curve-point-pair-output-point '(:infinity) '(:affine (2 4))))
  (f11-short-weierstrass-curve-point-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:infinity)))
  (f11-short-weierstrass-curve-point-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:affine (3 5))))
  (f11-short-weierstrass-curve-point-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:affine (2 7))))
  (f11-short-weierstrass-curve-point-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:affine (2 4))))
  (f11-curve-point-infinity-p
   (f11-curve-point-pair-output-point '(:affine (2 4)) '(:affine (2 7))))
  (not (f11-curve-point-infinity-p
        (f11-curve-point-pair-output-point '(:affine (2 4))
                                            '(:affine (3 5)))))
  (equal (f11-curve-point-affine-coordinates-get
          (f11-curve-point-pair-output-point '(:affine (2 4))
                                              '(:affine (2 4))))
         '(5 9))))

; Malformed full points fix to infinity, so they act like infinity here.  This
; is representation-level totality, not a geometric statement about BAD.
(assert-event
 (and
  (equal (f11-curve-point-pair-output-point 'bad 'also-bad) '(:infinity))
  (equal (f11-curve-point-pair-output-point 'bad '(:affine (2 4)))
         '(:affine (2 4)))
  (equal (f11-curve-point-pair-output-point '(:affine (2 4)) 'bad)
         '(:affine (2 4)))
  (equal (f11-curve-point-pair-output-point 'bad '(:infinity))
         '(:infinity))
  (equal (f11-curve-point-pair-output-point '(:infinity)
                                             '(:affine (13 15)))
         '(:affine (2 4)))))

(verify-guards f11-curve-point-pair-output-point)
