(in-package "GFIELD")

(include-book "f11-curve-point-addition-relation")
(include-book "f11-point-negation")

; Focused execution of the composed public operations.  The generic theorem in
; CURVE-POINT-ADDITION-INVERSE supplies the proof; these checks only protect the
; concrete F11 substitution and the infinity fixed point.
(assert-event
 (and
  (equal (f11-curve-point-pair-output-point
          '(:affine (2 4))
          (f11-curve-point-neg '(:affine (2 4))))
         '(:infinity))
  (equal (f11-curve-point-pair-output-point
          '(:infinity)
          (f11-curve-point-neg '(:infinity)))
         '(:infinity))
  (equal (f11-curve-point-pair-output-point
          (f11-curve-point-neg '(:affine (2 4)))
          '(:affine (2 4)))
         '(:infinity))))
