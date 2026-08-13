(in-package "GPOLY")

(include-book "quotient-coordinate-group-semantic-composition")

(defthm quotient-coordinate-cross-add-group-semantic-composition-minimal-theory-client
  (implies
   (and (equal (eval modulus x0) (gfield::field-zero))
        (quotient-coordinate-semantic-curve-p x0 y0 a b)
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point
          (quotient-coordinate-semantic-eval x1 x0 y0)
          (quotient-coordinate-semantic-eval y1 x0 y0)))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point
          (quotient-coordinate-semantic-eval x2 x0 y0)
          (quotient-coordinate-semantic-eval y2 x0 y0)))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point
          (quotient-coordinate-semantic-eval x3 x0 y0)
          (quotient-coordinate-semantic-eval y3 x0 y0)))
        (quotient-coordinate-cross-add-p
         x1 y1 x2 y2 x3 y3 a b modulus)
        (not
         (equal
          (gfield::field-sub
           (quotient-coordinate-semantic-eval x2 x0 y0)
           (quotient-coordinate-semantic-eval x1 x0 y0))
          (gfield::field-zero))))
   (gfield::curve-point-addition-relation-p
    (quotient-coordinate-field-curve-point
     (quotient-coordinate-semantic-eval x1 x0 y0)
     (quotient-coordinate-semantic-eval y1 x0 y0))
    (quotient-coordinate-field-curve-point
     (quotient-coordinate-semantic-eval x2 x0 y0)
     (quotient-coordinate-semantic-eval y2 x0 y0))
    (quotient-coordinate-field-curve-point
     (quotient-coordinate-semantic-eval x3 x0 y0)
     (quotient-coordinate-semantic-eval y3 x0 y0))))
  :rule-classes nil
  :hints (("Goal"
           :use quotient-coordinate-cross-add-implies-curve-point-addition
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-cross-opposite-group-semantic-composition-minimal-theory-client
  (implies
   (and (equal (eval modulus x0) (gfield::field-zero))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point
          (quotient-coordinate-semantic-eval x1 x0 y0)
          (quotient-coordinate-semantic-eval y1 x0 y0)))
        (gfield::short-weierstrass-affine-point-p
         (quotient-coordinate-field-affine-point
          (quotient-coordinate-semantic-eval x2 x0 y0)
          (quotient-coordinate-semantic-eval y2 x0 y0)))
        (quotient-coordinate-cross-opposite-p x1 y1 x2 y2 modulus))
   (gfield::curve-point-addition-relation-p
    (quotient-coordinate-field-curve-point
     (quotient-coordinate-semantic-eval x1 x0 y0)
     (quotient-coordinate-semantic-eval y1 x0 y0))
    (quotient-coordinate-field-curve-point
     (quotient-coordinate-semantic-eval x2 x0 y0)
     (quotient-coordinate-semantic-eval y2 x0 y0))
    (gfield::curve-point-infinity)))
  :rule-classes nil
  :hints (("Goal"
           :use quotient-coordinate-cross-opposite-implies-curve-point-addition
           :in-theory (theory 'minimal-theory))))
