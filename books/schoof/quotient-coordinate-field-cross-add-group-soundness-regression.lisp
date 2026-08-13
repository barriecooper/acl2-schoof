(in-package "GPOLY")

(include-book "quotient-coordinate-field-cross-add-group-soundness")

(defthm quotient-coordinate-field-cross-add-group-soundness-minimal-theory-client
  (implies
   (and (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x1 y1))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x2 y2))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point x3 y3))
        (quotient-coordinate-field-cross-add-p x1 y1 x2 y2 x3 y3)
        (not (equal (gfield::field-sub x2 x1) (gfield::field-zero))))
   (gfield::curve-point-addition-relation-p
    (quotient-coordinate-field-curve-point x1 y1)
    (quotient-coordinate-field-curve-point x2 y2)
    (quotient-coordinate-field-curve-point x3 y3)))
  :rule-classes nil
  :hints (("Goal"
           :use quotient-coordinate-field-cross-add-implies-curve-point-addition
           :in-theory (theory 'minimal-theory))))
