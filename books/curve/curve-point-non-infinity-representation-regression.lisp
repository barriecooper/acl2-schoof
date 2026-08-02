(in-package "GFIELD")

(include-book "points")

; Public-interface regression: clients can extract and reconstruct the affine
; payload of a valid non-infinity point without opening the representation.
(defthm short-weierstrass-curve-point-non-infinity-representation-client-regression
  (implies
   (and
    (short-weierstrass-curve-point-p point)
    (not (equal (curve-point-fix point)
                (curve-point-infinity))))
   (and
    (short-weierstrass-affine-point-p
     (curve-point-affine-coordinates-get
      (curve-point-fix point)))
    (equal
     (curve-point-fix point)
     (curve-point-affine-coordinates
      (curve-point-affine-coordinates-get
       (curve-point-fix point))))))
  :rule-classes nil
  :hints
  (("Goal"
    :use short-weierstrass-curve-point-non-infinity-representation
    :in-theory (theory 'minimal-theory))))
