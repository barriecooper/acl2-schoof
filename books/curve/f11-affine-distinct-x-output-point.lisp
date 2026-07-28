(in-package "GFIELD")

(include-book "affine-distinct-x-output-point")
(include-book "f11-affine-distinct-x-output")
(include-book "f11-points")

; Direct named-operation substitution into the generic tagged wrapper body.
(defun f11-affine-distinct-x-output-point (first second)
  (f11-curve-point-affine-coordinates
   (f11-affine-distinct-x-output first second)))

(assert-event
 (and
  (equal (f11-affine-distinct-x-output-point '(2 4) '(3 9))
         '(:affine (9 5)))
  (f11-curve-point-representation-p
   (f11-affine-distinct-x-output-point '(2 4) '(3 9)))
  (not (f11-curve-point-infinity-p
        (f11-affine-distinct-x-output-point '(2 4) '(3 9))))
  (equal
   (f11-curve-point-affine-coordinates-get
    (f11-affine-distinct-x-output-point '(2 4) '(3 9)))
   (f11-affine-distinct-x-output '(2 4) '(3 9)))))

; Malformed affine inputs retain the scalar operation's total fixing semantics.
(assert-event
 (equal (f11-affine-distinct-x-output-point 'bad '(3 6))
        '(:affine (1 9))))

; Outside :DISTINCT-X the wrapper still tags the inherited total scalar value.
(assert-event
 (equal (f11-affine-distinct-x-output-point '(2 4) '(2 7))
        '(:affine (7 7))))

(verify-guards f11-affine-distinct-x-output-point)
