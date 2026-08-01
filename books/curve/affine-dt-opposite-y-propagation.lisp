(in-package "GFIELD")

(include-book "affine-distinct-x-secant-relation")
(include-book "affine-doubling-relation")
(include-book "exceptional-addition-relations")

(local
 (defthm nonzero-difference-local
   (implies (and (field-element-p x)
                 (field-element-p y)
                 (not (equal x y)))
            (not (equal (field-sub y x) (field-zero))))
   :hints (("Goal"
            :use ((:instance field-sub-equal-zero-implies-fixed-equal
                             (first y) (second x)))
            :in-theory (enable field-fix-when-field-element-p)))))

(local
 (defthm shared-slope-local
   (implies
    (and (equal (field-mul p denominator) rhs)
         (equal (field-mul tangent denominator) rhs)
         (not (equal (field-fix denominator) (field-zero))))
    (equal (field-fix p) (field-fix tangent)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-mul-left-cancel-forward
                             (x denominator) (y p) (z tangent))
                  (:instance field-mul-commutative (x p) (y denominator))
                  (:instance field-mul-commutative (x tangent) (y denominator)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm secant-and-tangent-have-shared-slope-local
   (implies
    (and (equal (field-mul p (field-sub xb xa))
                (field-sub yb ya))
         (equal (field-add yq yb)
                (field-mul tangent (field-sub xb xq)))
         (equal xq xa)
         (equal yq (field-neg ya))
         (not (equal xa xb))
         (field-element-p xa)
         (field-element-p xb))
    (equal (field-fix p) (field-fix tangent)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance nonzero-difference-local (x xa) (y xb))
           (:instance shared-slope-local
                      (denominator (field-sub xb xa))
                      (rhs (field-sub yb ya))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-add-commutative field-add-associative
        field-add-inverse-right field-add-zero-right field-fix-of-neg
        field-element-p-of-add field-element-p-of-neg
        field-fix-when-field-element-p))))))

(local
 (defthm field-add-three-rotate-local
   (equal (field-add (field-add a b) c)
          (field-add (field-add b c) a))
   :hints (("Goal"
            :use ((:instance field-add-associative (x a) (y b) (z c))
                  (:instance field-add-associative (x b) (y c) (z a))
                  (:instance field-add-commutative
                             (x a) (y (field-add b c))))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-fix-of-add))))))

(local
 (defthm field-two-times-local
   (equal (field-mul (field-add (field-one) (field-one)) x)
          (field-add x x))
   :hints (("Goal"
            :in-theory
            (enable field-mul-right-distributive field-mul-one-left
                    field-fix-of-add)))))

(local
 (defthm propagated-x-local
   (implies
    (and (equal (field-add (field-add xp xa) xb)
                (field-mul p p))
         (equal (field-add
                 xq (field-mul (field-add (field-one) (field-one)) xb))
                (field-mul tangent tangent))
         (equal xq xa)
         (equal (field-fix p) (field-fix tangent))
         (field-element-p xp)
         (field-element-p xb))
    (equal xp xb))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-fixed-congruence
                      (x1 p) (x2 tangent) (y1 p) (y2 tangent))
           (:instance field-add-three-rotate-local
                      (a xp) (b xa) (c xb))
           (:instance field-add-left-cancel-forward
                      (x (field-add xa xb)) (y xp) (z xb)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-two-times-local field-add-three-rotate-local field-add-associative
        field-add-commutative field-fix-of-add
        field-fix-of-mul field-fix-when-field-element-p))))))

(local
 (defthm field-neg-mul-right-local
   (equal (field-mul x (field-neg y))
          (field-neg (field-mul x y)))
   :hints (("Goal"
            :use ((:instance field-mul-left-distributive
                             (x x) (y y) (z (field-neg y)))
                  (:instance field-additive-inverse-unique
                             (x (field-mul x y))
                             (y (field-mul x (field-neg y)))))
            :in-theory (enable field-add-inverse-right
                               field-mul-zero-right field-fix-of-mul)))))

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
 (defthm propagated-y-local
   (implies
    (and (equal (field-add yp ya)
                (field-mul p (field-sub xa xp)))
         (equal (field-add yq yb)
                (field-mul tangent (field-sub xb xq)))
         (equal xq xa)
         (equal xp xb)
         (equal yq (field-neg ya))
         (equal (field-fix p) (field-fix tangent))
         (field-element-p yp)
         (field-element-p yb))
    (equal yb (field-neg yp)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-fixed-congruence
                      (x1 p) (x2 tangent)
                      (y1 (field-sub xa xb))
                      (y2 (field-sub xa xb)))
           (:instance opposite-line-equations-imply-zero-sum-local
                      (ya ya) (yp yp) (yb yb)
                      (tangent tangent) (xa xa) (xb xb))
           (:instance field-additive-inverse-unique (x yp) (y yb)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-add-associative field-add-commutative
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right
        field-neg-of-neg field-fix-of-add field-fix-of-neg field-fix-of-mul
        field-fix-when-field-element-p))))))

; Reusable mixed secant/tangent O/O propagation.  It is the structural
; endpoint needed both by coincident-x exclusion and by the later outer O/O
; degeneration; its only cancellation is the first secant's own x difference.
(defthm affine-dt-opposite-y-propagates-to-left-output
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-opposite-y-infinity-relation-p a q-output infinity))
   (affine-opposite-y-infinity-relation-p p-output b infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance secant-and-tangent-have-shared-slope-local
                (p (field-fix p-slope)) (tangent (field-fix t-slope))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (xq (affine-coordinates-x q-output))
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yq (affine-coordinates-y q-output)))
     (:instance propagated-x-local
                (p (field-fix p-slope)) (tangent (field-fix t-slope))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (xq (affine-coordinates-x q-output))
                (xp (affine-coordinates-x p-output)))
     (:instance propagated-y-local
                (p (field-fix p-slope)) (tangent (field-fix t-slope))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (xq (affine-coordinates-x q-output))
                (xp (affine-coordinates-x p-output))
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yq (affine-coordinates-y q-output))
                (yp (affine-coordinates-y p-output))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
       affine-opposite-y-infinity-relation-p field-fix-idempotent
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y)))))
