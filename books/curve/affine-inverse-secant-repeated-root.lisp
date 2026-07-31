(in-package "GFIELD")

(include-book "short-weierstrass-factored-square-difference")
(include-book "affine-distinct-x-secant-relation")
(include-book "exceptional-addition-relations")
(include-book "../field/difference-of-squares")

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
 (defthm equal-implies-field-mul-equal-local
   (implies (equal x y)
            (equal (field-mul x z) (field-mul y z)))))

(local
 (defthm field-secant-line-factor-alignment-local
   (implies
    (equal (field-mul r (field-sub xc xa)) (field-add yc ya))
    (equal (field-mul (field-sub xc xa)
                      (field-mul r (field-sub yc ya)))
           (field-mul (field-sub yc ya) (field-add yc ya))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance equal-implies-field-mul-equal-local
                             (x (field-mul r (field-sub xc xa)))
                             (y (field-add yc ya))
                             (z (field-sub yc ya)))
                  (:instance field-mul-commutative
                             (x (field-add yc ya))
                             (y (field-sub yc ya))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-mul-swap-first-two-local field-mul-associative
                              field-fix-of-mul field-fix-of-add
                              field-fix-of-neg))))))

(local
 (defthm field-secant-line-and-curve-factorization-common-factor-local
   (implies
    (and (equal (field-sub (field-mul yc yc) (field-mul ya ya))
                (field-mul (field-sub xc xa) curve-factor))
         (equal (field-mul r (field-sub xc xa))
                (field-add yc ya)))
    (equal (field-mul (field-sub xc xa)
                      (field-mul r (field-sub yc ya)))
           (field-mul (field-sub xc xa) curve-factor)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-difference-of-squares (y1 yc) (y3 ya))
           (:instance field-secant-line-factor-alignment-local))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm distinct-field-elements-imply-nonzero-difference-local
   (implies (and (field-element-p xa)
                 (field-element-p xc)
                 (not (equal xc xa)))
            (not (equal (field-sub xc xa) (field-zero))))
   :hints
   (("Goal"
     :use ((:instance field-sub-equal-zero-implies-fixed-equal
                      (first xc) (second xa)))
     :in-theory (enable field-fix-when-field-element-p)))))

(defthm field-secant-line-and-curve-factorization-imply-repeated-root-relation
  (implies
   (and (equal (field-sub (field-mul yc yc) (field-mul ya ya))
               (field-mul (field-sub xc xa) curve-factor))
        (equal (field-mul r (field-sub xc xa))
               (field-add yc ya))
        (field-element-p xa)
        (field-element-p xc)
        (field-element-p curve-factor)
        (not (equal xc xa)))
   (equal (field-mul r (field-sub yc ya)) curve-factor))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           field-secant-line-and-curve-factorization-common-factor-local)
          (:instance distinct-field-elements-imply-nonzero-difference-local)
          (:instance field-mul-left-cancel-forward
                     (x (field-sub xc xa))
                     (y (field-mul r (field-sub yc ya)))
                     (z curve-factor)))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(field-sub field-fix-of-mul field-fix-of-add
                      field-fix-of-neg field-fix-when-field-element-p)))))

(local
 (defthm inverse-y-turns-secant-difference-into-sum-local
   (implies (and (field-element-p ya)
                 (equal yb (field-neg ya)))
            (equal (field-sub yc yb) (field-add yc ya)))
   :hints (("Goal" :in-theory
            (enable field-sub field-neg-of-neg
                    field-fix-when-field-element-p)))))

(defthm affine-inverse-secant-coincident-x-implies-repeated-root-relation
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c r u)
        (equal (affine-coordinates-x u)
               (affine-coordinates-x a)))
   (equal
    (field-mul (field-fix r)
               (field-sub (affine-coordinates-y c)
                          (affine-coordinates-y a)))
    (field-add
     (field-add
      (field-add
       (field-mul (affine-coordinates-x c)
                  (affine-coordinates-x c))
       (field-mul (affine-coordinates-x c)
                  (affine-coordinates-x a)))
      (field-mul (affine-coordinates-x a)
                 (affine-coordinates-x a)))
     (field-fix (short-weierstrass-a)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance inverse-y-turns-secant-difference-into-sum-local
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yc (affine-coordinates-y c)))
     (:instance short-weierstrass-curve-equations-imply-factored-square-difference
                (ya (affine-coordinates-y a))
                (yc (affine-coordinates-y c))
                (xa (affine-coordinates-x a))
                (xc (affine-coordinates-x c))
                (curve-a (field-fix (short-weierstrass-a)))
                (curve-b (field-fix (short-weierstrass-b))))
     (:instance field-secant-line-and-curve-factorization-imply-repeated-root-relation
                (ya (affine-coordinates-y a))
                (yc (affine-coordinates-y c))
                (xa (affine-coordinates-x a))
                (xc (affine-coordinates-x c))
                (r (field-fix r))
                (curve-factor
                 (field-add
                  (field-add
                   (field-add
                    (field-mul (affine-coordinates-x c)
                               (affine-coordinates-x c))
                    (field-mul (affine-coordinates-x c)
                               (affine-coordinates-x a)))
                   (field-mul (affine-coordinates-x a)
                              (affine-coordinates-x a)))
                  (field-fix (short-weierstrass-a))))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-distinct-x-secant-relation-p
       short-weierstrass-affine-point-p short-weierstrass-equation-p
       short-weierstrass-rhs
       field-mul-of-fixes field-mul-fix-left field-mul-fix-right
       field-fix-idempotent field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-element-p-of-add field-element-p-of-mul)))))
