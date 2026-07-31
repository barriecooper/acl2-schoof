(in-package "GFIELD")

(include-book "affine-inverse-secant-a-d4")

(local
 (defthm field-mul-swap-first-two-local
   (equal (field-mul x (field-mul y z))
          (field-mul y (field-mul x z)))
   :hints (("Goal"
            :use ((:instance field-mul-associative (x x) (y y) (z z))
                  (:instance field-mul-associative (x y) (y x) (z z))
                  (:instance field-mul-commutative (x x) (y y)))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(field-fix-of-mul))))))

(local
 (defthm field-mul-of-neg-right-local
   (equal (field-mul x (field-neg y))
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-mul x y))
                      (y (field-mul x (field-neg y))))
           (:instance field-mul-left-distributive
                      (x x) (y y) (z (field-neg y))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-inverse-right field-mul-zero-right
                       field-fix-of-mul))))))

(local
 (defthm field-mul-of-neg-left-local
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-mul x y))
                      (y (field-mul (field-neg x) y)))
           (:instance field-mul-right-distributive
                      (x x) (y (field-neg x)) (z y)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-inverse-right field-mul-zero-left
                       field-fix-of-mul))))))

(local
 (defthm field-add-inverse-middle-local
   (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
   :hints (("Goal" :use ((:instance field-add-associative
                                    (x x) (y (field-neg x)) (z y)))
            :in-theory (enable field-add-inverse-right field-add-zero-left
                               field-fix-idempotent)))))

(local
 (defthm field-add-swap-first-two-local
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints (("Goal" :use ((:instance field-add-associative (x x) (y y) (z z))
                          (:instance field-add-associative (x y) (y x) (z z))
                          (:instance field-add-commutative (x x) (y y)))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-shuffle-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints (("Goal" :use ((:instance field-add-swap-first-two-local
                                    (x x) (y y)
                                    (z (field-add (field-neg x) z)))
                          (:instance field-add-inverse-middle-local (x x) (y z)))
            :in-theory (enable field-add-fix-right)))))

(local
 (defthm field-neg-of-add-local
   (equal (field-neg (field-add x y))
          (field-add (field-neg x) (field-neg y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-add x y))
                      (y (field-add (field-neg x) (field-neg y)))))
     :in-theory
     (enable field-add-associative field-add-commutative
             field-add-inverse-shuffle-local
             field-add-inverse-left field-add-inverse-right
             field-add-zero-left field-add-zero-right
             field-fix-of-add field-fix-of-neg)))))

(local
 (defthm tangent-zero-solves-coefficient-local
   (implies
    (equal (field-add
            (field-mul
             (field-add (field-add (field-one) (field-one)) (field-one))
             (field-mul x x))
            a)
           (field-zero))
    (equal (field-fix a)
           (field-neg
            (field-mul
             (field-add (field-add (field-one) (field-one)) (field-one))
             (field-mul x x)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance field-additive-inverse-unique
                                    (x (field-mul
                                        (field-add
                                         (field-add (field-one) (field-one))
                                         (field-one))
                                        (field-mul x x)))
                                    (y a)))))))

(local
 (defthm solved-linear-term-normalization-local
   (equal
    (field-neg
     (field-add
      (field-mul (field-mul x x) x)
      (field-mul
       (field-neg
        (field-mul
         (field-add (field-add (field-one) (field-one)) (field-one))
         (field-mul x x)))
       x)))
    (field-mul (field-add (field-one) (field-one))
               (field-mul (field-mul x x) x)))
   :hints
   (("Goal" :do-not '(preprocess)
     :in-theory
     (enable field-neg-of-add-local field-mul-of-neg-left-local
             field-mul-left-distributive field-mul-right-distributive
             field-mul-associative field-mul-commutative
             field-add-associative field-add-commutative
             field-add-inverse-left field-add-inverse-right
             field-add-zero-left field-add-zero-right field-neg-of-neg
             field-mul-one-left field-mul-one-right
             field-fix-of-add field-fix-of-mul field-fix-of-neg)))))

(local
 (defthm curve-zero-solves-constant-local
   (implies
    (and
     (equal (field-fix a)
            (field-neg
             (field-mul
              (field-add (field-add (field-one) (field-one)) (field-one))
              (field-mul x x))))
     (equal
      (field-add (field-mul (field-mul x x) x)
                 (field-add (field-mul a x) b))
      (field-zero)))
    (equal
     (field-fix b)
     (field-mul (field-add (field-one) (field-one))
                (field-mul (field-mul x x) x))))
   :rule-classes nil
   :hints
   (("Goal" :do-not '(preprocess)
     :use ((:instance field-additive-inverse-unique
                      (x (field-add (field-mul (field-mul x x) x)
                                    (field-mul a x)))
                      (y b))
           (:instance field-mul-fixed-congruence
                      (x1 a)
                      (x2 (field-neg
                           (field-mul
                            (field-add
                             (field-add (field-one) (field-one))
                             (field-one))
                            (field-mul x x))))
                      (y1 x) (y2 x)))
     :in-theory
     (enable field-neg-of-add-local field-mul-of-neg-left-local
             field-mul-left-distributive field-mul-right-distributive
             field-mul-associative field-mul-commutative
             field-add-associative field-add-commutative
             field-add-inverse-left field-add-inverse-right
             field-add-zero-left field-add-zero-right field-neg-of-neg
             field-mul-one-left field-mul-one-right
             field-fix-of-add field-fix-of-mul field-fix-of-neg)))))

(local
 (defthm discriminant-substitution-normalization-local
    (equal
     (let* ((two (field-add (field-one) (field-one)))
            (three (field-add two (field-one)))
            (a (field-neg (field-mul three (field-mul x x))))
            (b (field-mul two (field-mul (field-mul x x) x))))
       (field-add
        (field-mul (field-mul two two)
                   (field-mul (field-mul a a) a))
        (field-mul (field-mul (field-mul three three) three)
                   (field-mul b b))))
     (field-zero))
   :hints
   (("Goal" :do-not '(preprocess)
     :in-theory
     (union-theories (theory 'minimal-theory)
             '(field-mul-swap-first-two-local
             field-mul-of-neg-left-local field-mul-of-neg-right-local
             field-neg-of-add-local
             field-mul-associative field-mul-commutative
             field-add-associative field-add-commutative
             field-add-inverse-left field-add-inverse-right
             field-add-zero-left field-add-zero-right field-neg-of-neg
             field-mul-one-left field-mul-one-right field-mul-zero-left
             field-mul-zero-right field-fix-of-add field-fix-of-mul
             field-fix-of-neg field-add-fix-left field-add-fix-right
             field-mul-fix-left field-mul-fix-right))))))

(local
 (defthm discriminant-of-solved-coefficients-local
   (implies
    (and
     (equal (field-fix a)
            (field-neg
             (field-mul
              (field-add (field-add (field-one) (field-one)) (field-one))
              (field-mul x x))))
     (equal (field-fix b)
            (field-mul (field-add (field-one) (field-one))
                       (field-mul (field-mul x x) x))))
    (equal
     (let* ((two (field-add (field-one) (field-one)))
            (three (field-add two (field-one))))
       (field-add
        (field-mul (field-mul two two)
                   (field-mul (field-mul (field-fix a) (field-fix a)) (field-fix a)))
        (field-mul (field-mul (field-mul three three) three)
                   (field-mul (field-fix b) (field-fix b)))))
     (field-zero)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance discriminant-substitution-normalization-local))
     :in-theory (union-theories (theory 'minimal-theory)
                                '(field-fix-of-neg field-fix-of-mul))))))
(defthm short-weierstrass-common-root-implies-discriminant-zero
  (implies
   (and
    (equal
     (field-add
      (field-mul
       (field-add (field-add (field-one) (field-one)) (field-one))
       (field-mul x x))
      (field-fix (short-weierstrass-a)))
     (field-zero))
    (equal
     (field-add
      (field-mul (field-mul x x) x)
      (field-add
       (field-mul (field-fix (short-weierstrass-a)) x)
       (field-fix (short-weierstrass-b))))
     (field-zero)))
   (equal (short-weierstrass-discriminant-expression) (field-zero)))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not '(preprocess)
    :use
    ((:instance tangent-zero-solves-coefficient-local
                (a (field-fix (short-weierstrass-a))))
     (:instance curve-zero-solves-constant-local
                (a (field-fix (short-weierstrass-a)))
                (b (field-fix (short-weierstrass-b))))
     (:instance discriminant-of-solved-coefficients-local
                (a (field-fix (short-weierstrass-a)))
                (b (field-fix (short-weierstrass-b)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(short-weierstrass-discriminant-expression
       field-fix-idempotent field-fix-of-mul field-fix-of-neg)))))

(local
 (defthm affine-curve-equation-at-zero-local
   (implies
    (and (short-weierstrass-affine-point-p point)
         (equal (affine-coordinates-y point) (field-zero)))
    (equal
     (field-add
      (field-mul (field-mul (affine-coordinates-x point)
                            (affine-coordinates-x point))
                 (affine-coordinates-x point))
      (field-add
       (field-mul (field-fix (short-weierstrass-a))
                  (affine-coordinates-x point))
       (field-fix (short-weierstrass-b))))
     (field-zero)))
   :rule-classes nil
   :hints
   (("Goal"
     :in-theory
     (enable short-weierstrass-affine-point-p short-weierstrass-equation-p
             short-weierstrass-rhs field-fix-when-field-element-p
             field-element-p-of-affine-coordinates-x field-mul-zero-left
             field-fix-of-zero)))))

(local
 (defthm self-inverse-coincident-case-is-contradictory-local
   (implies
    (and
     (short-weierstrass-characteristic-p)
     (affine-opposite-y-infinity-relation-p a b infinity)
     (affine-distinct-x-secant-relation-p b c r u)
     (equal (affine-coordinates-x u) (affine-coordinates-x a))
     (equal (affine-coordinates-y a)
            (field-neg (affine-coordinates-y a))))
    nil)
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance short-weierstrass-self-inverse-field-element-is-zero
                 (x (affine-coordinates-y a)))
      (:instance affine-inverse-secant-coincident-x-implies-tangent-equation)
      (:instance affine-curve-equation-at-zero-local (point a))
      (:instance short-weierstrass-common-root-implies-discriminant-zero
                 (x (affine-coordinates-x a)))
      short-weierstrass-discriminant-expression-nonzero)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-opposite-y-infinity-relation-p
        short-weierstrass-affine-point-p short-weierstrass-equation-p
        short-weierstrass-rhs field-element-p-of-affine-coordinates-y
        field-fix-when-field-element-p field-fix-idempotent
        field-mul-zero-left field-mul-zero-right field-add-zero-left
        field-add-zero-right))))))

(defthm affine-inverse-secant-coincident-x-excludes-self-inverse
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (affine-opposite-y-infinity-relation-p a b infinity)
    (affine-distinct-x-secant-relation-p b c r u)
    (equal (affine-coordinates-x u) (affine-coordinates-x a)))
   (not
    (equal (affine-coordinates-y a)
           (field-neg (affine-coordinates-y a)))))
  :rule-classes nil
  :hints
  (("Goal" :use self-inverse-coincident-case-is-contradictory-local
    :in-theory (theory 'minimal-theory))))
