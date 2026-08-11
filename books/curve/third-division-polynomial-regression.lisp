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

(defthm psi3-tangent-factorization-client-regression
 (implies (affine-doubling-relation-p input slope output)
  (equal (short-weierstrass-psi3 (affine-coordinates-x input))
   (field-mul
    (field-mul (short-weierstrass-two-y (affine-coordinates-y input))
               (short-weierstrass-two-y (affine-coordinates-y input)))
    (field-sub (affine-coordinates-x input)
               (affine-coordinates-x output)))))
 :rule-classes nil
 :hints (("Goal" :use short-weierstrass-psi3-tangent-factorization
          :in-theory (theory 'minimal-theory))))

(defthm psi3-root-iff-doubled-x-client-regression
 (implies (affine-doubling-relation-p input slope output)
  (equal
   (equal (short-weierstrass-psi3 (affine-coordinates-x input))
          (field-zero))
   (equal (affine-coordinates-x output)
          (affine-coordinates-x input))))
 :rule-classes nil
 :hints (("Goal" :use short-weierstrass-psi3-root-iff-doubled-x
          :in-theory (theory 'minimal-theory))))

(defthm psi3-root-forward-client-regression
 (implies (and (short-weierstrass-characteristic-p)
               (short-weierstrass-affine-point-p coordinates)
               (equal (short-weierstrass-psi3
                       (affine-coordinates-x coordinates))
                      (field-zero)))
  (equal (curve-point-nat-mul 3
          (curve-point-affine-coordinates coordinates))
         (curve-point-infinity)))
 :rule-classes nil
 :hints (("Goal"
          :use short-weierstrass-psi3-root-implies-nat-mul-three-is-infinity
          :in-theory (theory 'minimal-theory))))

(defthm psi3-root-reverse-client-regression
 (implies (and (short-weierstrass-characteristic-p)
               (short-weierstrass-affine-point-p coordinates)
               (equal (curve-point-nat-mul 3
                       (curve-point-affine-coordinates coordinates))
                      (curve-point-infinity)))
  (equal (short-weierstrass-psi3 (affine-coordinates-x coordinates))
         (field-zero)))
 :rule-classes nil
 :hints (("Goal"
          :use short-weierstrass-nat-mul-three-is-infinity-implies-psi3-root
          :in-theory (theory 'minimal-theory))))

(defthm psi3-root-iff-three-torsion-client-regression
 (implies (and (short-weierstrass-characteristic-p)
               (short-weierstrass-affine-point-p coordinates))
  (equal
   (equal (short-weierstrass-psi3 (affine-coordinates-x coordinates))
          (field-zero))
   (equal (curve-point-nat-mul 3
           (curve-point-affine-coordinates coordinates))
          (curve-point-infinity))))
 :rule-classes nil
 :hints (("Goal"
          :use short-weierstrass-psi3-root-iff-nat-mul-three-is-infinity
          :in-theory (theory 'minimal-theory))))
