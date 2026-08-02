(in-package "GFIELD")

(include-book "affine-distinct-x-secant-relation")
(include-book "affine-doubling-relation")
(include-book "curve-point-addition-commutativity")

(local
 (defthm field-neg-mul-right-local
   (equal (field-mul x (field-neg y))
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-mul-left-distributive
                      (x x) (y y) (z (field-neg y)))
           (:instance field-additive-inverse-unique
                      (x (field-mul x y))
                      (y (field-mul x (field-neg y)))))
     :in-theory
     (enable field-add-inverse-right field-mul-zero-right
             field-fix-of-mul)))))

(local
 (defthm field-add-swap-local
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints (("Goal"
            :use ((:instance field-add-associative (x x) (y y) (z z))
                  (:instance field-add-associative (x y) (y x) (z z))
                  (:instance field-add-commutative (x x) (y y)))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-tail-local
   (equal (field-add x (field-add (field-neg x) y))
          (field-fix y))
   :hints (("Goal"
            :use ((:instance field-add-associative
                             (x x) (y (field-neg x)) (z y)))
            :in-theory (enable field-add-inverse-right field-add-zero-left
                               field-fix-idempotent)))))

(local
 (defthm field-add-inverse-shuffle-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints (("Goal"
            :use ((:instance field-add-swap-local
                             (x x) (y y)
                             (z (field-add (field-neg x) z)))
                  (:instance field-add-inverse-tail-local (x x) (y z)))
            :in-theory (enable field-add-swap-local
                               field-add-inverse-tail-local
                               field-add-fix-right)))))

(local
 (defthm field-neg-of-add-local
   (equal (field-neg (field-add x y))
          (field-add (field-neg x) (field-neg y)))
   :hints (("Goal"
            :use ((:instance field-additive-inverse-unique
                             (x (field-add x y))
                             (y (field-add (field-neg x) (field-neg y)))))
            :in-theory
            (enable field-add-associative field-add-inverse-shuffle-local
                    field-add-inverse-right field-add-zero-left
                    field-fix-of-add field-fix-of-neg)))))

(local
 (defthm field-neg-sub-local
   (equal (field-neg (field-sub x y))
          (field-sub y x))
   :hints (("Goal"
            :in-theory
            (enable field-sub field-neg-of-add-local field-neg-of-neg)))))

(local
 (defthm opposite-products-local
   (equal (field-mul tangent (field-sub xa xb))
          (field-neg (field-mul tangent (field-sub xb xa))))
   :hints (("Goal"
            :use ((:instance field-neg-mul-right-local
                             (x tangent) (y (field-sub xb xa)))
                  (:instance field-neg-sub-local (x xb) (y xa)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-add-last-two-swap-local
   (equal (field-add x (field-add y z))
          (field-add x (field-add z y)))
   :hints (("Goal"
            :use ((:instance field-add-commutative (x y) (y z))
                  (:instance field-add-fixed-congruence
                             (x1 x) (x2 x)
                             (y1 (field-add y z))
                             (y2 (field-add z y))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-fix-of-add))))))

(local
 (defthm line-sum-normalization-local
   (equal (field-add (field-add ya yp) (field-sub yb ya))
          (field-add yb yp))
   :hints (("Goal"
            :use ((:instance field-add-swap-local
                             (x ya) (y yp)
                             (z (field-add yb (field-neg ya))))
                  (:instance field-add-inverse-shuffle-local
                             (x ya) (y yb) (z yp))
                  (:instance field-add-swap-local
                             (x yp) (y yb) (z (field-neg ya)))
                  (:instance field-add-commutative
                             (x yp) (y (field-neg ya)))
                  (:instance field-add-last-two-swap-local
                             (x yb) (y yp) (z (field-neg ya)))
                  (:instance field-add-fixed-congruence
                             (x1 ya) (x2 ya)
                             (y1 (field-add yb
                                            (field-add yp (field-neg ya))))
                             (y2 (field-add yb
                                            (field-add (field-neg ya) yp)))))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(field-sub field-add-associative field-add-commutative
               field-add-swap-local field-add-last-two-swap-local
               field-add-inverse-shuffle-local
               field-add-inverse-right
               field-add-zero-left field-add-fix-right
               field-fix-of-add field-fix-of-neg))))))

(local
 (defthm equal-neg-implies-zero-sum-local
   (implies (equal x (field-neg y))
            (equal (field-add x y) (field-zero)))
   :hints (("Goal"
            :use ((:instance field-add-fixed-congruence
                             (x1 x) (x2 (field-neg y))
                             (y1 y) (y2 y)))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-add-inverse-left field-fix-of-add))))))

(local
 (defthm opposite-line-equations-imply-zero-sum-local
   (implies
    (and (equal (field-add ya yp)
                (field-mul tangent (field-sub xa xb)))
         (equal (field-sub yb ya)
                (field-mul tangent (field-sub xb xa))))
    (equal (field-add yb yp) (field-zero)))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance field-add-fixed-congruence
                      (x1 (field-add ya yp))
                      (x2 (field-mul tangent (field-sub xa xb)))
                      (y1 (field-sub yb ya))
                      (y2 (field-mul tangent (field-sub xb xa))))
           (:instance opposite-products-local (tangent tangent) (xa xa) (xb xb))
           (:instance field-additive-inverse-unique
                      (x (field-add ya yp))
                      (y (field-sub yb ya)))
           (:instance equal-neg-implies-zero-sum-local
                      (x (field-add ya yp))
                      (y (field-sub yb ya)))
           (:instance field-add-fixed-congruence
                      (x1 (field-add ya yp))
                      (x2 (field-neg (field-sub yb ya)))
                      (y1 (field-sub yb ya))
                      (y2 (field-sub yb ya))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(line-sum-normalization-local
        field-add-inverse-left field-add-inverse-right
        field-fix-of-add field-fix-of-neg
        field-fix-of-mul))))))

(local
 (defthm mixed-non-self-inverse-implies-doubled-ordinate-nonzero-local
   (implies
    (and (field-element-p y)
         (not (equal y (field-neg y))))
    (not (equal (field-add y y) (field-zero))))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique (x y) (y y)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-fix-when-field-element-p))))))

(local
 (defthm mixed-fixed-affine-equal-implies-x-equal-local
   (implies
    (equal (affine-coordinates-fix first)
           (affine-coordinates-fix second))
    (equal (affine-coordinates-x first)
           (affine-coordinates-x second)))
   :hints (("Goal" :in-theory
            (enable affine-coordinates-fix affine-coordinates-make)))))

(local
 (defthm mixed-fixed-affine-equal-implies-y-equal-local
   (implies
    (equal (affine-coordinates-fix first)
           (affine-coordinates-fix second))
    (equal (affine-coordinates-y first)
           (affine-coordinates-y second)))
   :hints (("Goal" :in-theory
            (enable affine-coordinates-fix affine-coordinates-make)))))

(defthm affine-dt-left-outer-doubling-impossible
  (implies
   (and
    (affine-distinct-x-secant-relation-p
     a b p-slope p-output)
    (affine-doubling-relation-p
     b t-slope q-output)
    (equal (affine-coordinates-fix p-output)
           (affine-coordinates-fix b)))
   nil)
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance mixed-fixed-affine-equal-implies-x-equal-local
                (first p-output) (second b))
     (:instance mixed-fixed-affine-equal-implies-y-equal-local
                (first p-output) (second b))
     (:instance field-add-commutative
                (x (affine-coordinates-y a))
                (y (affine-coordinates-y b)))
     (:instance opposite-line-equations-imply-zero-sum-local
                (tangent (field-fix p-slope))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yp (affine-coordinates-y b)))
     (:instance mixed-non-self-inverse-implies-doubled-ordinate-nonzero-local
                (y (affine-coordinates-y b))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-doubling-relation-p
       affine-coordinates-x-of-fix affine-coordinates-y-of-fix
       field-element-p-of-affine-coordinates-y)))))

(defthm affine-td-right-outer-doubling-impossible
  (implies
   (and
    (affine-doubling-relation-p
     a t-slope p-output)
    (affine-distinct-x-secant-relation-p
     a b p-slope q-output)
    (equal (affine-coordinates-fix q-output)
           (affine-coordinates-fix a)))
   nil)
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-distinct-x-secant-relation-p-reverse
                (first a) (second b) (slope p-slope) (output q-output))
     (:instance affine-dt-left-outer-doubling-impossible
                (a b) (b a)
                (p-slope p-slope) (p-output q-output)
                (t-slope t-slope) (q-output p-output)))
    :in-theory (theory 'minimal-theory))))
