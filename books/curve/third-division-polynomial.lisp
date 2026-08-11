(in-package "GFIELD")

(include-book "../field/natural-scalar")
(include-book "affine-doubling-relation")
(include-book "affine-inverse-secant-self-inverse")
(include-book "../field/equal-squares")
(include-book "curve-point-natural-scalar")
(include-book "curve-point-pair-output-point-cancellation")
(include-book "affine-pair-curve-classification")

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
 (defthm field-nat-mul-two-as-coefficient-local
  (equal (field-nat-mul 2 x)
         (field-mul (field-add (field-one) (field-one)) x))
  :hints (("Goal" :in-theory
           (enable field-nat-mul field-mul-right-distributive)))))

(local
 (defthm short-weierstrass-two-y-expanded-local
  (equal (short-weierstrass-two-y y) (field-add y y))
  :hints (("Goal" :in-theory (enable short-weierstrass-two-y field-nat-mul)))))

(local
 (defthm short-weierstrass-tangent-numerator-expanded-local
  (equal (short-weierstrass-tangent-numerator x)
   (field-add
    (field-mul (field-add (field-add (field-one) (field-one)) (field-one))
               (field-mul x x))
    (field-fix (short-weierstrass-a))))
  :hints (("Goal" :in-theory
           (enable short-weierstrass-tangent-numerator field-nat-mul
                   field-mul-right-distributive)))))

(local
 (defthm field-square-congruence-local
  (implies (equal (field-fix left) (field-fix right))
   (equal (field-mul left left) (field-mul right right)))
  :hints (("Goal" :use ((:instance field-mul-fixed-congruence
                          (x1 left) (x2 right) (y1 left) (y2 right)))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-product-square-reassociate-local
  (equal (field-mul (field-mul s d) (field-mul s d))
         (field-mul (field-mul s s) (field-mul d d)))
  :hints (("Goal" :in-theory (enable field-mul-power-interchange
                                      field-mul-associative)))))

(local
 (defthm field-multiply-fixed-equality-local
  (implies (equal (field-fix left) (field-fix right))
   (equal (field-mul left common) (field-mul right common)))
  :hints (("Goal" :use ((:instance field-mul-fixed-congruence
                          (x1 left) (x2 right) (y1 common) (y2 common)))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-mul-of-neg-right-psi3-local
  (equal (field-mul x (field-neg y)) (field-neg (field-mul x y)))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                          (x (field-mul x y))
                          (y (field-mul x (field-neg y))))
                         (:instance field-mul-left-distributive
                          (x x) (y y) (z (field-neg y))))
           :in-theory (union-theories (theory 'minimal-theory)
             '(field-add-inverse-right field-mul-zero-right field-fix-of-mul))))))

(local
 (defthm field-mul-of-neg-left-psi3-local
  (equal (field-mul (field-neg x) y) (field-neg (field-mul x y)))
  :hints (("Goal" :use ((:instance field-mul-commutative
                          (x (field-neg x)) (y y))
                         (:instance field-mul-commutative (x y) (y x)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(field-mul-of-neg-right-psi3-local))))))

(local
 (defthm field-three-minus-two-times-local
  (equal (field-add (field-mul (field-nat-mul 3 x) q)
                    (field-neg (field-mul (field-nat-mul 2 x) q)))
         (field-mul x q))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory
           (enable field-nat-mul field-mul-right-distributive
                   field-neg-of-add field-add-associative field-add-commutative)))))

(local
 (defthm field-scalar-subtraction-psi3-local
  (equal
   (field-sub (field-mul (field-nat-mul 3 x) q)
              (field-mul (field-add x3 (field-nat-mul 2 x)) q))
   (field-mul (field-sub x x3) q))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-three-minus-two-times-local field-nat-mul field-sub field-neg-of-add
              field-mul-left-distributive field-mul-right-distributive
              field-mul-of-neg-left-psi3-local field-mul-of-neg-right-psi3-local
              field-add-associative field-add-commutative field-add-swap-first-two
              field-add-inverse-left field-add-inverse-right
              field-add-zero-left field-add-zero-right
              field-mul-one-left field-mul-one-right
              field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(defthm short-weierstrass-psi3-tangent-factorization
 (implies (affine-doubling-relation-p input slope output)
  (equal
   (short-weierstrass-psi3 (affine-coordinates-x input))
   (field-mul
    (field-mul (short-weierstrass-two-y (affine-coordinates-y input))
               (short-weierstrass-two-y (affine-coordinates-y input)))
    (field-sub (affine-coordinates-x input)
               (affine-coordinates-x output)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
          :use ((:instance short-weierstrass-psi3-on-curve
                           (x (affine-coordinates-x input))
                           (y (affine-coordinates-y input)))
                (:instance field-square-congruence-local
                           (left (field-mul (field-fix slope)
                                  (short-weierstrass-two-y
                                   (affine-coordinates-y input))))
                           (right (short-weierstrass-tangent-numerator
                                   (affine-coordinates-x input))))
                (:instance field-product-square-reassociate-local
                           (s (field-fix slope))
                           (d (short-weierstrass-two-y
                               (affine-coordinates-y input))))
                (:instance field-multiply-fixed-equality-local
                           (left (field-mul (field-fix slope) (field-fix slope)))
                           (right (field-add (affine-coordinates-x output)
                                            (field-nat-mul 2
                                             (affine-coordinates-x input))))
                           (common (field-mul
                            (short-weierstrass-two-y (affine-coordinates-y input))
                            (short-weierstrass-two-y (affine-coordinates-y input)))))
                (:instance field-scalar-subtraction-psi3-local
                           (x (affine-coordinates-x input))
                           (x3 (affine-coordinates-x output))
                           (q (field-mul
                            (short-weierstrass-two-y (affine-coordinates-y input))
                            (short-weierstrass-two-y (affine-coordinates-y input)))))
                (:instance field-mul-commutative
                           (x (field-sub (affine-coordinates-x input)
                                         (affine-coordinates-x output)))
                           (y (field-mul
                            (short-weierstrass-two-y (affine-coordinates-y input))
                            (short-weierstrass-two-y (affine-coordinates-y input))))))
          :in-theory
          (union-theories (theory 'minimal-theory)
           '(field-sub field-fix-of-neg affine-doubling-relation-p short-weierstrass-affine-point-p
             short-weierstrass-two-y-expanded-local
             short-weierstrass-tangent-numerator-expanded-local
             field-nat-mul-two-as-coefficient-local
             field-nat-mul-of-field-fix field-fix-idempotent field-fix-of-add
             field-fix-of-mul field-fix-when-field-element-p
             field-element-p-of-affine-coordinates-x
             field-element-p-of-affine-coordinates-y)))))


(local
 (defthm non-self-inverse-y-implies-two-y-nonzero-local
  (implies (not (equal (field-fix y) (field-neg y)))
   (not (equal (short-weierstrass-two-y y) (field-zero))))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique (x y) (y y)))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(short-weierstrass-two-y-expanded-local field-fix-of-neg))))))

(local
 (defthm nonzero-implies-square-nonzero-local
  (implies (not (equal (field-fix d) (field-zero)))
   (not (equal (field-mul d d) (field-zero))))
  :hints (("Goal" :use ((:instance field-mul-equal-zero-implies-equal-zero
                          (first d) (second d)))
           :in-theory (theory 'minimal-theory)))))

(defthm short-weierstrass-psi3-root-iff-doubled-x
 (implies (affine-doubling-relation-p input slope output)
  (equal
   (equal (short-weierstrass-psi3 (affine-coordinates-x input)) (field-zero))
   (equal (affine-coordinates-x output) (affine-coordinates-x input))))
 :rule-classes nil
 :hints (("Goal"
          :use (short-weierstrass-psi3-tangent-factorization
                (:instance non-self-inverse-y-implies-two-y-nonzero-local
                           (y (affine-coordinates-y input)))
                (:instance nonzero-implies-square-nonzero-local
                           (d (short-weierstrass-two-y
                               (affine-coordinates-y input))))
                (:instance field-mul-left-cancel-forward
                           (x (field-mul
                               (short-weierstrass-two-y (affine-coordinates-y input))
                               (short-weierstrass-two-y (affine-coordinates-y input))))
                           (y (field-sub (affine-coordinates-x input)
                                         (affine-coordinates-x output)))
                           (z (field-zero)))
                (:instance field-sub-equal-zero-implies-fixed-equal
                           (first (affine-coordinates-x input))
                           (second (affine-coordinates-x output))))
          :in-theory
          (union-theories (theory 'minimal-theory)
           '(field-sub field-fix-of-neg affine-doubling-relation-p short-weierstrass-two-y-expanded-local
             field-fix-when-field-element-p field-fix-of-add field-fix-of-mul field-fix-of-zero
             field-element-p-of-affine-coordinates-x
             field-element-p-of-affine-coordinates-y
             field-element-p-of-short-weierstrass-two-y
             field-add-inverse-right field-mul-zero-right field-sub-self)))))


(defthm curve-point-nat-mul-two
 (implies (and (short-weierstrass-characteristic-p)
               (short-weierstrass-curve-point-p point))
  (equal (curve-point-nat-mul 2 point)
         (curve-point-pair-output-point point point)))
 :hints (("Goal" :use ((:instance curve-point-nat-mul-successor
                          (n 1) (point point))
                        (:instance curve-point-nat-mul-one (x point)))
          :in-theory (union-theories (theory 'minimal-theory)
                                     '(natp)))))

(defthm curve-point-nat-mul-three
 (equal (curve-point-nat-mul 3 point)
        (curve-point-pair-output-point point
         (curve-point-nat-mul 2 point)))
 :hints (("Goal" :use ((:instance curve-point-nat-mul-successor
                          (n 2) (point point)))
          :in-theory (union-theories (theory 'minimal-theory)
                                     '(natp)))))

(defthm curve-point-nat-mul-three-is-infinity-iff-double-is-neg
 (implies (and (short-weierstrass-characteristic-p)
               (short-weierstrass-curve-point-p point))
  (equal (equal (curve-point-nat-mul 3 point) (curve-point-infinity))
         (equal (curve-point-nat-mul 2 point) (curve-point-neg point))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance short-weierstrass-curve-point-p-of-curve-point-nat-mul
                           (n 2) (x point))
                (:instance short-weierstrass-curve-point-p-of-neg (point point))
                (:instance curve-point-pair-output-point-cancel-left
                           (a point)
                           (b (curve-point-nat-mul 2 point))
                           (c (curve-point-neg point)))
                (:instance curve-point-pair-output-point-with-negate-right
                           (point point)))
          :in-theory (union-theories (theory 'minimal-theory)
            '(curve-point-nat-mul-three natp)))))

(defthm curve-point-nat-mul-two-equal-point-implies-infinity
 (implies (and (short-weierstrass-characteristic-p)
               (short-weierstrass-curve-point-p point)
               (equal (curve-point-nat-mul 2 point) point))
  (equal point (curve-point-infinity)))
 :rule-classes nil
 :hints (("Goal"
          :use (short-weierstrass-curve-point-p-of-infinity
                (:instance curve-point-pair-output-point-cancel-left
                           (a point) (b point) (c (curve-point-infinity)))
                (:instance curve-point-pair-output-point-identity-right
                           (point point)))
          :in-theory (union-theories (theory 'minimal-theory)
                                     '(curve-point-nat-mul-two)))))


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

(local
 (defthm affine-self-classifies-tangent-local
  (implies (not (equal (affine-coordinates-y coordinates)
                       (field-neg (affine-coordinates-y coordinates))))
   (equal (affine-pair-classify coordinates coordinates)
          :same-point-non-opposite))
  :hints (("Goal" :use ((:instance
                          affine-pair-classify-same-point-non-opposite-characterization
                          (first coordinates) (second coordinates)))
           :in-theory (union-theories (theory 'minimal-theory)
            '(affine-coordinates-x-of-fix affine-coordinates-y-of-fix))))))

(local
 (defthm tangent-output-of-fix-local
  (equal (affine-same-point-non-opposite-output
          (affine-coordinates-fix coordinates))
         (affine-same-point-non-opposite-output coordinates))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(affine-same-point-non-opposite-output
              affine-same-point-non-opposite-output-x
              affine-same-point-non-opposite-output-y
              affine-same-point-non-opposite-slope
              affine-coordinates-x-of-fix affine-coordinates-y-of-fix
              field-fix-idempotent field-fix-of-add field-fix-of-mul
              field-fix-of-neg field-fix-of-inv))))))

(local
 (defthm affine-double-is-tangent-output-local
  (implies (and (short-weierstrass-characteristic-p)
                (short-weierstrass-affine-point-p coordinates)
                (not (equal (affine-coordinates-y coordinates)
                            (field-neg (affine-coordinates-y coordinates)))))
   (equal
    (curve-point-nat-mul 2 (curve-point-affine-coordinates coordinates))
    (affine-same-point-non-opposite-output-point coordinates)))
  :hints (("Goal"
           :use (affine-self-classifies-tangent-local
                 (:instance short-weierstrass-affine-point-p-of-fix
                            (coordinates coordinates))
                 (:instance short-weierstrass-curve-point-p-of-affine
                            (coordinates coordinates))
                 (:instance curve-point-nat-mul-two
                            (point (curve-point-affine-coordinates coordinates))))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(tangent-output-of-fix-local affine-pair-classify-of-fixes affine-same-point-non-opposite-output-point
              curve-point-pair-output-point-of-affines
              affine-pair-output-point-when-same-point-non-opposite))))))

(local
 (defthm tangent-output-satisfies-doubling-relation-local
  (implies (and (short-weierstrass-affine-point-p coordinates)
                (not (equal (affine-coordinates-y coordinates)
                            (field-neg (affine-coordinates-y coordinates)))))
   (affine-doubling-relation-p
    coordinates
    (affine-same-point-non-opposite-slope coordinates)
    (affine-same-point-non-opposite-output coordinates)))
  :hints (("Goal" :use ((:instance
                          affine-same-point-non-opposite-output-satisfies-doubling-relation
                          (input coordinates)))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm equal-fixed-affine-coordinates-from-components-local
  (implies (and (equal (affine-coordinates-x first)
                       (affine-coordinates-x second))
                (equal (affine-coordinates-y first)
                       (affine-coordinates-y second)))
   (equal (affine-coordinates-fix first) (affine-coordinates-fix second)))
  :hints (("Goal" :in-theory
           (enable affine-coordinates-fix affine-coordinates-make)))))



(local
 (defthm curve-point-affine-coordinates-of-fix-local
  (equal (curve-point-affine-coordinates (affine-coordinates-fix coordinates))
         (curve-point-affine-coordinates coordinates))
  :hints (("Goal" :in-theory
           (enable curve-point-affine-coordinates affine-coordinates-fix-idempotent)))))

(local
 (defthm affine-point-equal-neg-from-components-local
  (implies (and (equal (affine-coordinates-x first)
                       (affine-coordinates-x second))
                (equal (affine-coordinates-y first)
                       (field-neg (affine-coordinates-y second))))
   (equal (curve-point-affine-coordinates first)
          (curve-point-neg (curve-point-affine-coordinates second))))
  :hints (("Goal" :use ((:instance curve-point-neg-of-affine
                                   (x (affine-coordinates-x second))
                                   (y (affine-coordinates-y second))))
           :in-theory
           (enable curve-point-affine-coordinates curve-point-affine
                   affine-coordinates-fix affine-coordinates-make)))))

(local
 (defthm psi3-root-implies-double-is-point-or-neg-local
  (implies
   (and (short-weierstrass-characteristic-p)
        (short-weierstrass-affine-point-p coordinates)
        (equal (short-weierstrass-psi3 (affine-coordinates-x coordinates))
               (field-zero)))
   (or (equal (curve-point-nat-mul 2
                    (curve-point-affine-coordinates coordinates))
              (curve-point-affine-coordinates coordinates))
       (equal (curve-point-nat-mul 2
                    (curve-point-affine-coordinates coordinates))
              (curve-point-neg
               (curve-point-affine-coordinates coordinates)))))
  :hints (("Goal"
           :use ((:instance short-weierstrass-psi3-root-excludes-self-inverse-y
                            (point coordinates))
                 tangent-output-satisfies-doubling-relation-local
                 curve-point-affine-coordinates-of-fix-local
                 affine-double-is-tangent-output-local
                 (:instance short-weierstrass-psi3-root-iff-doubled-x
                            (input coordinates)
                            (slope (affine-same-point-non-opposite-slope coordinates))
                            (output (affine-same-point-non-opposite-output coordinates)))
                 (:instance short-weierstrass-equal-x-implies-equal-or-neg-y
                            (p coordinates)
                            (q (affine-same-point-non-opposite-output coordinates)))
                 (:instance equal-fixed-affine-coordinates-from-components-local
                            (first (affine-same-point-non-opposite-output coordinates))
                            (second coordinates))
                 (:instance affine-point-equal-neg-from-components-local
                            (first (affine-same-point-non-opposite-output coordinates))
                            (second coordinates)))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(affine-doubling-relation-p
              affine-same-point-non-opposite-output-point
              curve-point-affine affine-coordinates-x-of-make
              affine-coordinates-y-of-make
              affine-coordinates-fix-of-affine-same-point-non-opposite-output
              affine-coordinates-fix-idempotent
              affine-coordinates-fix-when-affine-coordinates-p
              short-weierstrass-affine-point-p
              affine-coordinates-p-of-fix field-fix-when-field-element-p
              field-element-p-of-affine-coordinates-x
              field-element-p-of-affine-coordinates-y))))))



(local
 (defthm affine-point-is-not-infinity-local
  (not (equal (curve-point-affine-coordinates coordinates)
              (curve-point-infinity)))
  :hints (("Goal" :in-theory
           (enable curve-point-affine-coordinates curve-point-infinity)))))

(defthm short-weierstrass-psi3-root-implies-nat-mul-three-is-infinity
 (implies
  (and (short-weierstrass-characteristic-p)
       (short-weierstrass-affine-point-p coordinates)
       (equal (short-weierstrass-psi3 (affine-coordinates-x coordinates))
              (field-zero)))
  (equal (curve-point-nat-mul 3
          (curve-point-affine-coordinates coordinates))
         (curve-point-infinity)))
 :rule-classes nil
 :hints (("Goal"
          :use (psi3-root-implies-double-is-point-or-neg-local
                (:instance curve-point-nat-mul-two-equal-point-implies-infinity
                           (point (curve-point-affine-coordinates coordinates)))
                (:instance curve-point-nat-mul-three-is-infinity-iff-double-is-neg
                           (point (curve-point-affine-coordinates coordinates)))
                (:instance short-weierstrass-affine-point-p-of-fix
                           (coordinates coordinates))
                (:instance short-weierstrass-curve-point-p-of-affine
                           (coordinates coordinates))
                affine-point-is-not-infinity-local)
          :in-theory (theory 'minimal-theory))))

(local
 (defthm self-inverse-y-implies-affine-neg-is-self-local
  (implies (equal (affine-coordinates-y coordinates)
                  (field-neg (affine-coordinates-y coordinates)))
   (equal (curve-point-neg (curve-point-affine-coordinates coordinates))
          (curve-point-affine-coordinates coordinates)))
  :hints (("Goal"
           :use ((:instance curve-point-neg-of-affine
                            (x (affine-coordinates-x coordinates))
                            (y (affine-coordinates-y coordinates))))
           :in-theory
           (enable curve-point-affine-coordinates curve-point-affine
                   affine-coordinates-fix affine-coordinates-make)))))

(local
 (defthm nat-mul-three-infinity-excludes-self-inverse-y-local
  (implies
   (and (short-weierstrass-characteristic-p)
        (short-weierstrass-affine-point-p coordinates)
        (equal (curve-point-nat-mul 3
                (curve-point-affine-coordinates coordinates))
               (curve-point-infinity)))
   (not (equal (affine-coordinates-y coordinates)
               (field-neg (affine-coordinates-y coordinates)))))
  :hints (("Goal"
           :use ((:instance curve-point-nat-mul-three-is-infinity-iff-double-is-neg
                            (point (curve-point-affine-coordinates coordinates)))
                 (:instance curve-point-nat-mul-two-equal-point-implies-infinity
                            (point (curve-point-affine-coordinates coordinates)))
                 (:instance short-weierstrass-affine-point-p-of-fix
                            (coordinates coordinates))
                 (:instance short-weierstrass-curve-point-p-of-affine
                            (coordinates coordinates))
                 self-inverse-y-implies-affine-neg-is-self-local
                 affine-point-is-not-infinity-local)
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm affine-neg-equality-implies-equal-x-local
  (implies
   (equal (curve-point-affine-coordinates output)
          (curve-point-neg (curve-point-affine-coordinates input)))
   (equal (affine-coordinates-x output)
          (affine-coordinates-x input)))
  :hints (("Goal"
           :use ((:instance curve-point-neg-of-affine
                            (x (affine-coordinates-x input))
                            (y (affine-coordinates-y input))))
           :in-theory
           (enable curve-point-affine-coordinates curve-point-affine
                   affine-coordinates-fix affine-coordinates-make)))))

(defthm short-weierstrass-nat-mul-three-is-infinity-implies-psi3-root
 (implies
  (and (short-weierstrass-characteristic-p)
       (short-weierstrass-affine-point-p coordinates)
       (equal (curve-point-nat-mul 3
               (curve-point-affine-coordinates coordinates))
              (curve-point-infinity)))
  (equal (short-weierstrass-psi3 (affine-coordinates-x coordinates))
         (field-zero)))
 :rule-classes nil
 :hints (("Goal"
          :use (nat-mul-three-infinity-excludes-self-inverse-y-local
                tangent-output-satisfies-doubling-relation-local
                affine-double-is-tangent-output-local
                (:instance curve-point-nat-mul-three-is-infinity-iff-double-is-neg
                           (point (curve-point-affine-coordinates coordinates)))
                (:instance affine-neg-equality-implies-equal-x-local
                           (input coordinates)
                           (output (affine-same-point-non-opposite-output coordinates)))
                (:instance short-weierstrass-psi3-root-iff-doubled-x
                           (input coordinates)
                           (slope (affine-same-point-non-opposite-slope coordinates))
                           (output (affine-same-point-non-opposite-output coordinates)))
                (:instance short-weierstrass-affine-point-p-of-fix
                           (coordinates coordinates))
                (:instance short-weierstrass-curve-point-p-of-affine
                           (coordinates coordinates)))
          :in-theory
          (union-theories (theory 'minimal-theory)
                           '(affine-same-point-non-opposite-output-point)))))

(defthm short-weierstrass-psi3-root-iff-nat-mul-three-is-infinity
 (implies
  (and (short-weierstrass-characteristic-p)
       (short-weierstrass-affine-point-p coordinates))
  (equal
   (equal (short-weierstrass-psi3 (affine-coordinates-x coordinates))
          (field-zero))
   (equal (curve-point-nat-mul 3
           (curve-point-affine-coordinates coordinates))
          (curve-point-infinity))))
 :rule-classes nil
 :hints (("Goal"
          :use (short-weierstrass-psi3-root-implies-nat-mul-three-is-infinity
                short-weierstrass-nat-mul-three-is-infinity-implies-psi3-root)
          :in-theory (theory 'minimal-theory))))

(verify-guards short-weierstrass-tangent-numerator)
(verify-guards short-weierstrass-two-y)
(verify-guards short-weierstrass-psi3)
