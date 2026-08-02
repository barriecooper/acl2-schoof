(in-package "GFIELD")

(include-book "affine-dt-opposite-y-propagation")
(include-book "affine-inverse-secant-a-d4")
(include-book "curve-point-addition-commutativity")

(local
 (defthm field-mul-right-cancel-local
   (implies (and (not (equal (field-fix d) (field-zero)))
                 (equal (field-mul x d) (field-mul y d)))
            (equal (field-fix x) (field-fix y)))
   :hints (("Goal" :use ((:instance field-mul-left-cancel-forward
                                    (x d) (y x) (z y))
                           (:instance field-mul-commutative (x x) (y d))
                           (:instance field-mul-commutative (x y) (y d)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm doubled-ordinate-nonzero-local
   (implies (and (field-element-p y)
                 (not (equal y (field-neg y))))
            (not (equal (field-add y y) (field-zero))))
   :hints (("Goal" :use ((:instance field-additive-inverse-unique
                                    (x y) (y y)))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-fix-when-field-element-p))))))

(local
 (defthm field-mul-neg-right-local
   (equal (field-mul x (field-neg y))
          (field-neg (field-mul x y)))
   :hints (("Goal" :use ((:instance field-mul-left-distributive
                                    (x x) (y y) (z (field-neg y)))
                           (:instance field-additive-inverse-unique
                                    (x (field-mul x y))
                                    (y (field-mul x (field-neg y)))))
            :in-theory (enable field-add-inverse-right
                               field-mul-zero-right field-fix-of-mul)))))

(local
 (defthm field-mul-neg-neg-local
   (equal (field-mul (field-neg x) (field-neg y))
          (field-mul x y))
   :hints (("Goal" :use ((:instance field-mul-neg-right-local
                                    (x (field-neg x)) (y y))
                           (:instance field-mul-neg-right-local (x y) (y x))
                           (:instance field-mul-commutative
                                    (x (field-neg x)) (y y))
                           (:instance field-mul-commutative (x y) (y x)))
            :in-theory (enable field-neg-of-neg field-fix-of-mul)))))

(local
 (defthm negated-tangent-equation-local
   (implies
    (and (equal xp xb)
         (equal yp (field-neg yb))
         (equal (field-mul (field-neg p) (field-add yp yp)) rhs)
         (field-element-p yb))
    (equal (field-mul p (field-add yb yb)) rhs))
   :rule-classes nil
   :hints
   (("Goal"
     :in-theory
     (enable field-mul-left-distributive field-mul-right-distributive
             field-add-inverse-left field-add-inverse-right
             field-add-zero-left field-add-zero-right field-neg-of-neg
             field-mul-neg-neg-local
             field-fix-when-field-element-p field-fix-of-add
             field-fix-of-mul field-fix-of-neg)))))

(local
 (defthm mixed-slopes-equal-local
   (implies
    (and (equal (field-mul p (field-add yb yb)) rhs)
         (equal (field-mul tangent (field-add yb yb)) rhs)
         (field-element-p yb)
         (not (equal (field-add yb yb) (field-zero))))
    (equal (field-fix p) (field-fix tangent)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance field-mul-right-cancel-local
                                    (x p) (y tangent)
                                    (d (field-add yb yb))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-element-p-of-add
                              field-fix-when-field-element-p))))))

(local
 (defthm field-add-three-rotate-local
   (equal (field-add (field-add a b) c)
          (field-add (field-add b c) a))
   :hints (("Goal" :use ((:instance field-add-associative
                                    (x a) (y b) (z c))
                           (:instance field-add-associative
                                    (x b) (y c) (z a))
                           (:instance field-add-commutative
                                    (x a) (y (field-add b c))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-fix-of-add))))))

(local
 (defthm field-two-times-local
   (equal (field-mul (field-add (field-one) (field-one)) x)
          (field-add x x))
   :hints (("Goal" :in-theory
            (enable field-mul-right-distributive field-mul-one-left
                    field-fix-of-add)))))

(local
 (defthm field-add-common-right-cancel-local
   (implies (equal (field-add x common) (field-add y common))
            (equal (field-fix x) (field-fix y)))
   :hints (("Goal" :use ((:instance field-add-left-cancel-forward
                                    (x common) (y x) (z y))
                           (:instance field-add-commutative (x x) (y common))
                           (:instance field-add-commutative (x y) (y common)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm propagated-x-local
   (implies
    (and (equal xp xb)
         (equal (field-add (field-add xp xa) xb) (field-mul p p))
         (equal (field-add xq (field-mul (field-add (field-one) (field-one)) xb))
                (field-mul tangent tangent))
         (equal (field-fix p) (field-fix tangent))
         (field-element-p xa) (field-element-p xb) (field-element-p xq))
    (equal xq xa))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-fixed-congruence
                      (x1 p) (x2 tangent) (y1 p) (y2 tangent))
            (:instance field-add-three-rotate-local
                       (a xp) (b xa) (c xb))
            (:instance field-add-common-right-cancel-local
                       (common (field-add xb xb)) (x xq) (y xa)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-two-times-local field-add-three-rotate-local
        field-add-associative field-add-commutative
        field-fix-when-field-element-p field-fix-of-add
        field-fix-of-mul))))))

(local
 (defthm propagated-y-local
   (implies
    (and (equal xq xa)
         (equal (field-fix p) (field-fix tangent))
         (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
         (equal (field-add yq yb)
                (field-mul tangent (field-sub xb xq)))
         (field-element-p ya) (field-element-p yb) (field-element-p yq))
    (equal yq (field-neg ya)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-fixed-congruence
                      (x1 p) (x2 tangent)
                      (y1 (field-sub xb xa)) (y2 (field-sub xb xq)))
            (:instance field-add-left-cancel-forward
                       (x yb) (y yq) (z (field-neg ya))))
     :in-theory
     (enable field-sub field-add-associative field-add-commutative
             field-add-inverse-left field-add-inverse-right
             field-add-zero-left field-add-zero-right
             field-fix-when-field-element-p field-fix-of-add
             field-fix-of-mul field-fix-of-neg)))))

; Maintained orientation: A+B=P, B+B=Q, and P=-B imply A=-Q.
(defthm affine-dt-left-output-opposite-y-propagates-to-right-output
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-opposite-y-infinity-relation-p p-output b infinity))
   (affine-opposite-y-infinity-relation-p a q-output infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-distinct-x-secant-relation-p-reverse
                (first a) (second b) (slope p-slope) (output p-output))
     (:instance affine-opposite-y-infinity-relation-p-symmetric
                (first p-output) (second b) (output infinity))
     (:instance affine-inverse-secant-coincident-x-implies-tangent-equation
                (a p-output) (b b) (c a) (r p-slope) (u p-output))
     (:instance negated-tangent-equation-local
                (p (field-fix p-slope))
                (xp (affine-coordinates-x p-output))
                (xb (affine-coordinates-x b))
                (yp (affine-coordinates-y p-output))
                (yb (affine-coordinates-y b))
                (rhs (field-add
                      (field-mul
                       (field-add (field-add (field-one) (field-one))
                                  (field-one))
                       (field-mul (affine-coordinates-x b)
                                  (affine-coordinates-x b)))
                      (field-fix (short-weierstrass-a)))))
     (:instance doubled-ordinate-nonzero-local
                (y (affine-coordinates-y b)))
     (:instance mixed-slopes-equal-local
                (p (field-fix p-slope)) (tangent (field-fix t-slope))
                (yb (affine-coordinates-y b))
                (rhs (field-add
                      (field-mul
                       (field-add (field-add (field-one) (field-one))
                                  (field-one))
                       (field-mul (affine-coordinates-x b)
                                  (affine-coordinates-x b)))
                      (field-fix (short-weierstrass-a)))))
     (:instance propagated-x-local
                (p (field-fix p-slope)) (tangent (field-fix t-slope))
                (xp (affine-coordinates-x p-output))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (xq (affine-coordinates-x q-output)))
     (:instance propagated-y-local
                (p (field-fix p-slope)) (tangent (field-fix t-slope))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (xq (affine-coordinates-x q-output))
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yq (affine-coordinates-y q-output))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
       affine-opposite-y-infinity-relation-p field-fix-idempotent
       field-fix-when-field-element-p field-fix-of-add field-fix-of-mul
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y)))))
