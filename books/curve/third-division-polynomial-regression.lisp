(in-package "GFIELD")
(include-book "third-division-polynomial")

(defthm psi3-on-curve-client-regression
 (implies (short-weierstrass-equation-p x y)
  (equal (short-weierstrass-psi3 x)
   (field-sub
    (field-mul (field-nat-mul 3 x)
               (field-mul (short-weierstrass-two-y y)
                          (short-weierstrass-two-y y)))
    (field-mul (short-weierstrass-tangent-numerator x)
               (short-weierstrass-tangent-numerator x)))))
 :rule-classes nil
 :hints (("Goal" :use short-weierstrass-psi3-on-curve
          :in-theory (theory 'minimal-theory))))

(defthm psi3-root-self-inverse-exclusion-client-regression
 (implies (and (short-weierstrass-characteristic-p)
               (short-weierstrass-affine-point-p point)
               (equal (short-weierstrass-psi3
                       (affine-coordinates-x point))
                      (field-zero)))
  (not (equal (affine-coordinates-y point)
              (field-neg (affine-coordinates-y point)))))
 :rule-classes nil
 :hints (("Goal" :use short-weierstrass-psi3-root-excludes-self-inverse-y
          :in-theory (theory 'minimal-theory))))
