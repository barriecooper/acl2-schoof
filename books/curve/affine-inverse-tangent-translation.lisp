(in-package "GFIELD")

(include-book "affine-distinct-x-secant-relation")
(include-book "affine-doubling-relation")
(include-book "exceptional-addition-relations")

; The Stage 3 inverse/tangent certificate is purely additive sign algebra.
; B is the affine inverse of A, U is a tangent output at B, and the tangent
; witness is negated for the outer line through A and U.

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
     (union-theories
      (theory 'minimal-theory)
      '(field-add-inverse-right field-mul-zero-right field-fix-of-mul))))))

(local
 (defthm field-neg-mul-left-local
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-mul-commutative (x (field-neg x)) (y y))
           (:instance field-mul-commutative (x y) (y x))
           (:instance field-neg-mul-right-local (x y) (y x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-add-swap-local
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints (("Goal"
            :use ((:instance field-add-associative (x x) (y y) (z z))
                  (:instance field-add-associative (x y) (y x) (z z))
                  (:instance field-add-commutative (x x) (y y)))
            :in-theory
            (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-tail-local
   (equal (field-add x (field-add (field-neg x) y))
          (field-fix y))
   :hints (("Goal"
            :use ((:instance field-add-associative
                             (x x) (y (field-neg x)) (z y)))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(field-add-inverse-right field-add-zero-left
               field-fix-idempotent))))))

(local
 (defthm field-add-inverse-shuffle-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints (("Goal"
            :use ((:instance field-add-swap-local
                             (x x) (y y)
                             (z (field-add (field-neg x) z)))
                  (:instance field-add-inverse-tail-local (x x) (y z)))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(field-add-swap-local field-add-inverse-tail-local
               field-add-fix-right))))))

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
     (union-theories
      (theory 'minimal-theory)
      '(field-add-associative field-add-inverse-shuffle-local
        field-add-inverse-right
        field-add-zero-left field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-neg-sub-local
   (equal (field-neg (field-sub x y))
          (field-sub y x))
   :hints (("Goal"
            :in-theory
            (enable field-sub field-neg-of-add-local field-neg-of-neg)))))

(local
 (defthm field-neg-mul-sub-local
   (equal (field-mul (field-neg t) (field-sub x y))
          (field-mul t (field-sub y x)))
   :hints (("Goal"
            :use ((:instance field-neg-mul-left-local
                             (x t) (y (field-sub x y)))
                  (:instance field-neg-mul-right-local
                             (x t) (y (field-sub x y)))
                  (:instance field-neg-sub-local (x x) (y y)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-neg-product-of-difference-local
   (implies
    (and (field-element-p x) (field-element-p y))
    (equal (field-neg (field-mul slope (field-add x (field-neg y))))
           (field-mul slope (field-add y (field-neg x)))))
   :hints (("Goal"
            :use ((:instance field-neg-mul-right-local
                             (x slope) (y (field-add x (field-neg y))))
                  (:instance field-neg-of-add-local
                             (x x) (y (field-neg y)))
                  (:instance field-neg-of-neg (x y))
                  (:instance field-add-commutative
                             (x (field-neg x)) (y y)))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(field-fix-when-field-element-p
               field-element-p-of-add field-element-p-of-neg))))))

(local
 (defthm field-two-times-local
   (equal (field-mul (field-add (field-one) (field-one)) x)
          (field-add (field-fix x) (field-fix x)))
   :hints (("Goal"
            :use ((:instance field-mul-right-distributive
                             (x (field-one)) (y (field-one)) (z x))
                  (:instance field-mul-one-left (x x)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-neg-square-local
   (equal (field-mul (field-neg x) (field-neg x))
          (field-mul (field-fix x) (field-fix x)))
   :hints
   (("Goal"
     :use ((:instance field-neg-mul-right-local
                      (x (field-neg x)) (y x))
           (:instance field-neg-mul-left-local (x x) (y x))
           (:instance field-neg-of-neg (x (field-mul x x))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-mul-fix-left field-mul-fix-right
                       field-fix-of-mul))))))

(local
 (defthm inverse-tangent-numerator-local
   (implies
    (and (equal yb (field-neg ya))
         (equal (field-mul (field-fix slope) (field-add yb yb)) rhs)
         (field-element-p ya))
    (equal (field-mul (field-neg slope) (field-add ya ya)) rhs))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-neg-mul-left-local
                      (x slope) (y (field-add ya ya)))
           (:instance field-neg-of-add-local (x ya) (y ya))
           (:instance field-neg-mul-right-local
                      (x slope) (y (field-add ya ya))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-mul-fix-left field-fix-when-field-element-p
        field-element-p-of-add field-element-p-of-neg))))))

(local
 (defthm inverse-tangent-domain-local
   (implies
    (and (equal yb (field-neg ya))
         (not (equal yb (field-neg yb)))
         (field-element-p ya)
         (field-element-p yb))
    (not (equal ya (field-neg ya))))
   :hints
   (("Goal"
     :use ((:instance field-neg-of-neg (x ya))
           (:instance field-neg-of-neg (x yb)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-fix-when-field-element-p))))))

(local
 (defthm inverse-tangent-y-coincidence-local
   (implies
    (and (equal yb (field-neg ya))
         (equal xu xa)
         (equal (field-add yu yb)
                (field-mul slope (field-sub xa xu)))
         (field-element-p ya)
         (field-element-p yb)
         (field-element-p yu)
         (field-element-p xa)
         (field-element-p xu))
    (equal yu ya))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique (x yb) (y yu))
           (:instance field-add-commutative (x yu) (y yb))
           (:instance field-neg-of-neg (x ya)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub-self field-mul-zero-right field-fix-when-field-element-p))))))

; In the distinct-x outer branch, the existing secant relation is witnessed
; by -T and its output is B itself.
(defthm affine-inverse-tangent-translation-outer-distinct-x
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-doubling-relation-p b tangent u)
        (not (equal (affine-coordinates-x u)
                    (affine-coordinates-x a))))
   (affine-distinct-x-secant-relation-p
    a u (field-neg tangent) b))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-neg-product-of-difference-local
                     (slope tangent)
                     (x (affine-coordinates-x u))
                     (y (affine-coordinates-x a)))
          (:instance field-add-commutative
                     (x (affine-coordinates-y u))
                     (y (affine-coordinates-y b))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-doubling-relation-p
       affine-distinct-x-secant-relation-p
       field-sub field-neg-mul-left-local field-neg-square-local
       field-neg-of-add-local field-neg-sub-local field-neg-mul-sub-local
       field-neg-product-of-difference-local
       field-neg-of-neg field-neg-of-zero
       field-add-associative field-add-commutative
       field-add-zero-left field-add-zero-right
       field-add-inverse-left field-add-inverse-right
       field-mul-zero-right field-mul-fix-left
       field-two-times-local
       field-fix-of-add field-fix-of-neg
       field-fix-of-mul field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y)))))

; In the coincident-x branch A and U coincide (including y), and the same
; negated witness satisfies the existing doubling relation with output B.
(defthm affine-inverse-tangent-translation-outer-doubling
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-doubling-relation-p b tangent u)
        (equal (affine-coordinates-x u)
               (affine-coordinates-x a)))
   (affine-doubling-relation-p a (field-neg tangent) b))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance inverse-tangent-domain-local
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b)))
     (:instance inverse-tangent-numerator-local
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (slope tangent)
                (rhs
                 (field-add
                  (field-mul
                   (field-add (field-add (field-one) (field-one))
                              (field-one))
                   (field-mul (affine-coordinates-x a)
                              (affine-coordinates-x a)))
                  (field-fix (short-weierstrass-a)))))
     (:instance inverse-tangent-y-coincidence-local
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yu (affine-coordinates-y u))
                (xa (affine-coordinates-x a))
                (xu (affine-coordinates-x u))
                (slope tangent)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-doubling-relation-p field-sub
       field-neg-mul-left-local field-neg-square-local
       field-neg-of-add-local field-neg-of-neg field-neg-of-zero
       field-add-associative field-add-commutative
       field-add-zero-left field-add-zero-right
       field-add-inverse-left field-add-inverse-right
       field-mul-zero-right field-mul-fix-left field-two-times-local
       field-fix-of-add field-fix-of-neg
       field-fix-of-mul field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y)))))

; Stable classifier-free Stage 3 boundary.  The disjunction is exhaustive on
; fixed x equality, so an outer opposite-y outcome is not a premise and cannot
; occur: the relation is derived as either D or T.
(defthm affine-inverse-tangent-translation
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-doubling-relation-p b tangent u))
   (or (affine-distinct-x-secant-relation-p
        a u (field-neg tangent) b)
       (affine-doubling-relation-p
        a (field-neg tangent) b)))
  :rule-classes nil
  :hints
  (("Goal"
    :use (affine-inverse-tangent-translation-outer-distinct-x
          affine-inverse-tangent-translation-outer-doubling)
    :cases ((equal (affine-coordinates-x u)
                   (affine-coordinates-x a)))
    :in-theory (theory 'minimal-theory))))
