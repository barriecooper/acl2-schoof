(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-output-point")
(include-book "f11-affine-same-point-non-opposite-output")
(include-book "f11-points")
(include-book "f11-affine-pair-classification")

; Direct named-operation substitution into the generic tagged wrapper body.
(defun f11-affine-same-point-non-opposite-output-point (first)
  (f11-curve-point-affine-coordinates
   (f11-affine-same-point-non-opposite-output first)))

(assert-event
 (and
  (equal (f11-affine-pair-classify '(2 4) '(2 4))
         :same-point-non-opposite)
  (equal (f11-affine-same-point-non-opposite-output-point '(2 4))
         '(:affine (5 9)))
  (f11-curve-point-representation-p
   (f11-affine-same-point-non-opposite-output-point '(2 4)))
  (f11-short-weierstrass-curve-point-p
   (f11-affine-same-point-non-opposite-output-point '(2 4)))
  (not (f11-curve-point-infinity-p
        (f11-affine-same-point-non-opposite-output-point '(2 4))))
  (equal
   (f11-curve-point-affine-coordinates-get
    (f11-affine-same-point-non-opposite-output-point '(2 4)))
   (f11-affine-same-point-non-opposite-output '(2 4)))))

; Malformed inputs retain the unary scalar operation's total fixing semantics.
(assert-event
 (equal (f11-affine-same-point-non-opposite-output-point 'bad)
        '(:affine (0 0))))

(verify-guards f11-affine-same-point-non-opposite-output-point)
