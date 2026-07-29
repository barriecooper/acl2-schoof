(in-package "GFIELD")

(include-book "affine-opposite-y-output-point")
(include-book "f11-affine-pair-classification")
(include-book "f11-points")

; Direct named-operation substitution into the generic constant branch body.
(defun f11-affine-opposite-y-output-point (first second)
  (declare (ignore first second))
  (f11-curve-point-infinity))

(assert-event
 (and
  (equal (f11-affine-pair-classify '(2 4) '(2 7)) :opposite-y)
  (equal (f11-affine-opposite-y-output-point '(2 4) '(2 7))
         '(:infinity))
  (f11-curve-point-representation-p
   (f11-affine-opposite-y-output-point '(2 4) '(2 7)))
  (f11-curve-point-infinity-p
   (f11-affine-opposite-y-output-point '(2 4) '(2 7)))
  (f11-short-weierstrass-curve-point-p
   (f11-affine-opposite-y-output-point '(2 4) '(2 7)))))

; Affine fixing makes both malformed BAD and (0,0) select the self-inverse
; opposite-y case.  The branch result is still the same canonical infinity.
(assert-event
 (and (equal (f11-affine-pair-classify 'bad '(0 0)) :opposite-y)
      (equal (f11-affine-opposite-y-output-point 'bad '(0 0))
             '(:infinity))))

; The operation is deliberately total even when called outside its branch.
(assert-event
 (and (equal (f11-affine-pair-classify '(2 4) '(3 5)) :distinct-x)
      (equal (f11-affine-opposite-y-output-point '(2 4) '(3 5))
             '(:infinity))))

(verify-guards f11-affine-opposite-y-output-point)
