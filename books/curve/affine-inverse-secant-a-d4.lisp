(in-package "GFIELD")

(include-book "affine-inverse-secant-repeated-root")

; This book starts from the already certified repeated-root relation.  All
; auxiliary normalization below is deliberately local and division-free.
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
   :hints (("Goal" :use ((:instance field-mul-commutative
                                    (x (field-neg x)) (y y))
                          (:instance field-mul-commutative (x y) (y x)))
            :in-theory (enable field-mul-of-neg-right-local)))))

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
   :hints (("Goal" :use ((:instance field-additive-inverse-unique
                                    (x (field-add x y))
                                    (y (field-add (field-neg x)
                                                  (field-neg y)))))
            :in-theory
            (enable field-add-associative field-add-inverse-shuffle-local
                    field-add-inverse-right field-add-zero-left
                    field-fix-of-add field-fix-of-neg)))))

(local
 (defthm field-secant-line-ordinate-substitution-local
   (implies
    (equal (field-mul r (field-sub xc xa)) (field-add yc ya))
    (equal (field-sub yc ya)
           (field-sub (field-mul r (field-sub xc xa))
                      (field-add ya ya))))
   :rule-classes nil
   :hints (("Goal" :do-not '(preprocess)
            :in-theory
            (enable field-sub field-neg-of-add-local
                    field-add-associative field-add-commutative
                    field-add-inverse-left field-add-inverse-right
                    field-add-zero-left field-add-zero-right
                    field-neg-of-neg field-fix-of-add field-fix-of-neg)))))

(local
 (defthm field-secant-line-times-r-local
   (implies
    (equal (field-mul r (field-sub xc xa)) (field-add yc ya))
    (equal
     (field-mul r (field-sub yc ya))
     (field-sub
      (field-mul (field-mul r r) (field-sub xc xa))
      (field-mul r (field-add ya ya)))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-secant-line-ordinate-substitution-local))
     :in-theory
     (enable field-sub field-mul-left-distributive
             field-mul-associative field-mul-of-neg-right-local
             field-fix-of-add field-fix-of-mul field-fix-of-neg)))))

(local
 (defthm field-quadratic-product-normalization-local
   (equal
    (field-mul (field-add (field-add xc xa) xa)
               (field-sub xc xa))
    (field-sub
     (field-add (field-mul xc xc) (field-mul xc xa))
     (field-add (field-mul xa xa) (field-mul xa xa))))
   :hints
   (("Goal" :do-not '(preprocess)
     :use ((:instance field-add-inverse-shuffle-local
                      (x (field-mul xa xc))
                      (y (field-mul xc xc))
                      (z (field-add (field-neg (field-mul xa xa))
                                    (field-neg (field-mul xa xa))))))
     :in-theory
     (enable field-sub field-mul-left-distributive
             field-mul-right-distributive field-mul-associative
             field-mul-commutative field-mul-of-neg-left-local
             field-mul-of-neg-right-local field-neg-of-add-local
             field-add-associative field-add-commutative
             field-add-inverse-left field-add-inverse-right
             field-add-zero-left field-add-zero-right field-neg-of-neg
             field-fix-of-add field-fix-of-mul field-fix-of-neg)))))

(local
 (defthm field-output-x-quadratic-product-local
   (implies
    (equal (field-mul r r) (field-add (field-add xc xa) xa))
    (equal
     (field-mul (field-mul r r) (field-sub xc xa))
     (field-sub
      (field-add (field-mul xc xc) (field-mul xc xa))
      (field-add (field-mul xa xa) (field-mul xa xa)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-quadratic-product-normalization-local)
                  (:instance field-mul-fixed-congruence
                             (x1 (field-mul r r))
                             (x2 (field-add (field-add xc xa) xa))
                             (y1 (field-sub xc xa))
                             (y2 (field-sub xc xa))))
            :in-theory
            (enable field-sub field-fix-of-add field-fix-of-mul
                    field-fix-of-neg)))))

(local
 (defthm field-move-two-negative-summands-local
   (implies
    (equal (field-add x (field-add (field-neg s) (field-neg s))) z)
    (equal (field-fix x) (field-add z (field-add s s))))
   :rule-classes nil
   :hints
   (("Goal" :do-not '(preprocess)
     :use ((:instance field-add-left-cancel-forward
                      (x (field-add (field-neg s) (field-neg s)))
                      (y x)
                      (z (field-add z (field-add s s)))))
     :in-theory
     (enable field-add-associative field-add-commutative
             field-add-swap-first-two-local field-add-inverse-middle-local
             field-add-inverse-shuffle-local field-add-inverse-left
             field-add-inverse-right field-add-zero-left field-add-zero-right
             field-neg-of-neg field-fix-of-add field-fix-of-neg)))))

(local
 (defthm field-a-d4-additive-normalization-local
   (implies
    (equal
     (field-sub
      (field-sub
       (field-add (field-mul xc xc) (field-mul xc xa))
       (field-add (field-mul xa xa) (field-mul xa xa)))
      ry)
     (field-add
      (field-add
       (field-add (field-mul xc xc) (field-mul xc xa))
       (field-mul xa xa))
      curve-a))
    (equal
     (field-neg ry)
     (field-add
      (field-mul
       (field-add (field-add (field-one) (field-one)) (field-one))
       (field-mul xa xa))
      curve-a)))
   :rule-classes nil
   :hints
   (("Goal" :do-not '(preprocess)
     :use ((:instance field-move-two-negative-summands-local
                      (x (field-neg ry))
                      (s (field-mul xa xa))
                      (z (field-add curve-a (field-mul xa xa))))
           (:instance field-add-left-cancel-forward
                      (x (field-add (field-mul xc xa)
                                    (field-mul xc xc)))
                      (y (field-add
                          (field-neg ry)
                          (field-add (field-neg (field-mul xa xa))
                                     (field-neg (field-mul xa xa)))))
                      (z (field-add curve-a (field-mul xa xa)))))
     :in-theory
     (enable field-sub field-neg-of-add-local
             field-add-associative field-add-commutative
             field-add-swap-first-two-local field-add-inverse-middle-local
             field-add-inverse-shuffle-local field-add-inverse-left
             field-add-inverse-right field-add-zero-left field-add-zero-right
             field-neg-of-neg field-mul-left-distributive
             field-mul-right-distributive field-mul-one-left
             field-fix-of-add field-fix-of-mul field-fix-of-neg)))))

(defthm field-repeated-root-and-secant-output-imply-tangent-equation
  (implies
   (and
    (equal
     (field-mul r (field-sub yc ya))
     (field-add
      (field-add
       (field-add (field-mul xc xc) (field-mul xc xa))
       (field-mul xa xa))
      curve-a))
    (equal (field-mul r (field-sub xc xa)) (field-add yc ya))
    (equal (field-mul r r) (field-add (field-add xc xa) xa)))
   (equal
    (field-mul (field-neg r) (field-add ya ya))
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one)) (field-one))
      (field-mul xa xa))
     curve-a)))
  :rule-classes nil
  :hints
  (("Goal" :do-not '(preprocess)
    :use ((:instance field-secant-line-times-r-local)
          (:instance field-output-x-quadratic-product-local)
          (:instance field-a-d4-additive-normalization-local
                     (ry (field-mul r (field-add ya ya)))))
    :in-theory
    (enable field-sub field-mul-left-distributive
            field-mul-right-distributive field-mul-associative
            field-mul-commutative field-mul-of-neg-left-local
            field-mul-of-neg-right-local field-neg-of-add-local
            field-add-associative field-add-commutative
            field-add-inverse-left field-add-inverse-right
            field-add-zero-left field-add-zero-right field-neg-of-neg
            field-mul-one-left field-mul-one-right
            field-fix-of-add field-fix-of-mul field-fix-of-neg))))

(local
 (defthm field-inverse-substituted-line-local
   (implies
    (and (equal yb (field-neg ya))
         (equal (field-mul r (field-sub xc xa)) (field-sub yc yb))
         (field-element-p ya))
    (equal (field-mul r (field-sub xc xa)) (field-add yc ya)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable field-sub field-neg-of-neg
                    field-fix-when-field-element-p)))))

(local
 (defthm field-coincident-output-x-local
   (implies
    (equal (field-add (field-add xa xa) xc) (field-mul r r))
    (equal (field-mul r r) (field-add (field-add xc xa) xa)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable field-add-associative field-add-commutative
                    field-add-swap-first-two-local field-fix-of-add)))))

(defthm affine-inverse-secant-coincident-x-implies-tangent-equation
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c r u)
        (equal (affine-coordinates-x u)
               (affine-coordinates-x a)))
   (equal
    (field-mul (field-neg (field-fix r))
               (field-add (affine-coordinates-y a)
                          (affine-coordinates-y a)))
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one)) (field-one))
      (field-mul (affine-coordinates-x a)
                 (affine-coordinates-x a)))
     (field-fix (short-weierstrass-a)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-inverse-secant-coincident-x-implies-repeated-root-relation)
     (:instance field-inverse-substituted-line-local
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yc (affine-coordinates-y c))
                (xa (affine-coordinates-x a))
                (xc (affine-coordinates-x c))
                (r (field-fix r)))
     (:instance field-coincident-output-x-local
                (xa (affine-coordinates-x a))
                (xc (affine-coordinates-x c))
                (r (field-fix r)))
     (:instance field-repeated-root-and-secant-output-imply-tangent-equation
                (xa (affine-coordinates-x a))
                (ya (affine-coordinates-y a))
                (xc (affine-coordinates-x c))
                (yc (affine-coordinates-y c))
                (r (field-fix r))
                (curve-a (field-fix (short-weierstrass-a)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-distinct-x-secant-relation-p field-sub
       field-neg-of-neg field-mul-fix-left field-mul-fix-right
       field-mul-of-fixes field-fix-idempotent
       field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-fix-of-add field-fix-of-mul field-fix-of-neg)))))
