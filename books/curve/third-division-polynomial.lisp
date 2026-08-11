(in-package "GFIELD")

(include-book "../field/natural-scalar")
(include-book "affine-doubling-relation")
(include-book "affine-inverse-secant-self-inverse")
(include-book "../field/equal-squares")

(defun short-weierstrass-tangent-numerator (x)
  (field-add (field-nat-mul 3 (field-mul x x))
             (field-fix (short-weierstrass-a))))

(defun short-weierstrass-two-y (y)
  (field-nat-mul 2 y))

; Algebraically this is 3*x^4 + 6*A*x^2 + 12*B*x - A^2.  The master
; presentation keeps the curve equation visible and avoids division.
(defun short-weierstrass-psi3 (x)
  (field-sub
   (field-nat-mul 12
                  (field-mul (field-fix x) (short-weierstrass-rhs x)))
   (field-mul (short-weierstrass-tangent-numerator x)
              (short-weierstrass-tangent-numerator x))))

(defthm short-weierstrass-tangent-numerator-of-fix
  (equal (short-weierstrass-tangent-numerator (field-fix x))
         (short-weierstrass-tangent-numerator x))
  :hints (("Goal" :in-theory
           (enable short-weierstrass-tangent-numerator
                   field-mul-of-fixes))))

(defthm short-weierstrass-two-y-of-fix
  (equal (short-weierstrass-two-y (field-fix y))
         (short-weierstrass-two-y y))
  :hints (("Goal" :in-theory
           (enable short-weierstrass-two-y field-nat-mul-of-field-fix))))

(defthm field-element-p-of-short-weierstrass-tangent-numerator
  (field-element-p (short-weierstrass-tangent-numerator x)))
(defthm field-element-p-of-short-weierstrass-two-y
  (field-element-p (short-weierstrass-two-y y)))
(defthm field-element-p-of-short-weierstrass-psi3
  (field-element-p (short-weierstrass-psi3 x))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(short-weierstrass-psi3 field-sub
               field-element-p-of-add field-element-p-of-neg
               field-element-p-of-mul field-element-p-of-field-nat-mul
               field-element-p-of-short-weierstrass-rhs
               field-element-p-of-short-weierstrass-tangent-numerator)))))
(defthm short-weierstrass-psi3-of-fix
  (equal (short-weierstrass-psi3 (field-fix x))
         (short-weierstrass-psi3 x))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(short-weierstrass-psi3 short-weierstrass-rhs
               short-weierstrass-tangent-numerator-of-fix
               field-fix-idempotent)))))

(local
 (defthm twelve-x-y2-is-three-x-two-y-squared-local
  (equal
   (field-nat-mul 12 (field-mul x (field-mul y y)))
   (field-mul (field-nat-mul 3 x)
              (field-mul (short-weierstrass-two-y y)
                         (short-weierstrass-two-y y))))
  :hints (("Goal" :in-theory
           (enable short-weierstrass-two-y field-nat-mul
                   field-mul-left-distributive field-mul-right-distributive
                   field-mul-associative field-mul-commutative)))))

(local
 (defthm substitute-curve-equation-in-scaled-product-local
  (implies (equal (field-mul (field-fix y) (field-fix y)) rhs)
   (equal (field-nat-mul 12 (field-mul (field-fix x) rhs))
          (field-nat-mul 12 (field-mul (field-fix x)
                                      (field-mul (field-fix y) (field-fix y))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)))))

(defthm short-weierstrass-psi3-on-curve
  (implies
   (short-weierstrass-equation-p x y)
   (equal
    (short-weierstrass-psi3 x)
    (field-sub
     (field-mul (field-nat-mul 3 x)
                (field-mul (short-weierstrass-two-y y)
                           (short-weierstrass-two-y y)))
     (field-mul (short-weierstrass-tangent-numerator x)
                (short-weierstrass-tangent-numerator x)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance twelve-x-y2-is-three-x-two-y-squared-local
                            (x (field-fix x)) (y (field-fix y)))
                 (:instance substitute-curve-equation-in-scaled-product-local
                            (rhs (short-weierstrass-rhs x))))
           :in-theory
           (union-theories (theory 'minimal-theory)
             '(short-weierstrass-psi3 short-weierstrass-equation-p
               field-fix-when-field-element-p
               field-element-p-of-short-weierstrass-rhs
               field-element-p-of-affine-coordinates-x
               field-fix-of-mul field-fix-idempotent
               field-nat-mul-of-field-fix short-weierstrass-two-y-of-fix))))

)

(local
 (defthm affine-curve-equation-at-zero-for-psi3-local
  (implies (and (short-weierstrass-affine-point-p point)
                (equal (affine-coordinates-y point) (field-zero)))
   (equal (short-weierstrass-rhs (affine-coordinates-x point))
          (field-zero)))
  :hints (("Goal" :in-theory
           (enable short-weierstrass-affine-point-p
                   short-weierstrass-equation-p field-mul-zero-left)))))

(local
 (defthm field-neg-equal-zero-implies-fixed-zero-local
  (implies (equal (field-neg x) (field-zero))
           (equal (field-fix x) (field-zero)))
  :hints (("Goal" :use ((:instance field-neg-of-neg (x x))
                         field-neg-of-zero)
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm psi3-root-at-curve-zero-gives-tangent-zero-local
  (implies (and (equal (short-weierstrass-rhs x) (field-zero))
                (equal (short-weierstrass-psi3 x) (field-zero)))
   (equal (short-weierstrass-tangent-numerator x) (field-zero)))
  :hints (("Goal"
           :use ((:instance field-neg-equal-zero-implies-fixed-zero-local
                            (x (field-mul (short-weierstrass-tangent-numerator x)
                                          (short-weierstrass-tangent-numerator x))))
                 (:instance field-mul-equal-zero-implies-equal-zero
                            (first (short-weierstrass-tangent-numerator x))
                            (second (short-weierstrass-tangent-numerator x))))
           :in-theory
           (union-theories (theory 'minimal-theory)
             '(short-weierstrass-psi3 field-sub field-mul-zero-left field-mul-zero-right
               field-nat-mul-of-zero field-add-zero-left field-neg-of-zero
               field-neg-of-neg field-fix-of-neg field-fix-of-mul
               field-neg-equal-zero-implies-fixed-zero-local
               field-additive-inverse-unique
               field-fix-when-field-element-p
               field-element-p-of-short-weierstrass-tangent-numerator))))))

(local
 (defthm field-nat-mul-three-as-coefficient-local
  (equal (field-nat-mul 3 x)
   (field-mul (field-add (field-add (field-one) (field-one)) (field-one)) x))
  :hints (("Goal" :in-theory
           (enable field-nat-mul field-mul-right-distributive)))))

(defthm short-weierstrass-psi3-root-excludes-self-inverse-y
 (implies
  (and (short-weierstrass-characteristic-p)
       (short-weierstrass-affine-point-p point)
       (equal (short-weierstrass-psi3 (affine-coordinates-x point))
              (field-zero)))
  (not (equal (affine-coordinates-y point)
              (field-neg (affine-coordinates-y point)))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance short-weierstrass-self-inverse-field-element-is-zero
                           (x (affine-coordinates-y point)))
                affine-curve-equation-at-zero-for-psi3-local
                (:instance psi3-root-at-curve-zero-gives-tangent-zero-local
                           (x (affine-coordinates-x point)))
                (:instance short-weierstrass-common-root-implies-discriminant-zero
                           (x (affine-coordinates-x point)))
                short-weierstrass-discriminant-expression-nonzero)
          :in-theory
          (union-theories (theory 'minimal-theory)
            '(short-weierstrass-tangent-numerator field-nat-mul
              short-weierstrass-rhs
              field-element-p-of-affine-coordinates-y
              field-element-p-of-affine-coordinates-x
              field-nat-mul-three-as-coefficient-local field-neg-of-zero
              field-fix-when-field-element-p)))))

(verify-guards short-weierstrass-tangent-numerator)
(verify-guards short-weierstrass-two-y)
(verify-guards short-weierstrass-psi3)
