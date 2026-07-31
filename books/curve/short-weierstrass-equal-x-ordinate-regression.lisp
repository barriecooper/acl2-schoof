(in-package "GFIELD")

(include-book "affine-pair-curve-classification")

(defthm short-weierstrass-equal-x-ordinate-client-regression
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second)
        (equal (affine-coordinates-x first)
               (affine-coordinates-x second)))
   (or (equal (affine-coordinates-y first)
              (affine-coordinates-y second))
       (equal (affine-coordinates-y second)
              (field-neg (affine-coordinates-y first)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance short-weierstrass-equal-x-implies-equal-or-neg-y
                                   (p first) (q second)))
           :in-theory (theory 'minimal-theory))))
