(in-package "GFIELD")

(include-book "affine-inverse-secant-self-inverse")
(include-book "affine-doubling-relation")

; The inner secant equations, after substituting B=-A, already have the
; orientations required by the outer line.  The normalization lemmas in this
; book are intentionally local: the public interface is the four geometric
; statements at the end of the book.

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
     (union-theories (theory 'minimal-theory)
                     '(field-add-inverse-right field-mul-zero-right
                       field-fix-of-mul))))))

(local
 (defthm field-neg-mul-left-local
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-mul-commutative (x (field-neg x)) (y y))
           (:instance field-mul-commutative (x y) (y x)))
     :in-theory (enable field-neg-mul-right-local)))))

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
            (union-theories (theory 'minimal-theory)
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
            (union-theories (theory 'minimal-theory)
                            '(field-add-swap-local
                              field-add-inverse-tail-local
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
        field-add-inverse-right field-add-zero-left
        field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-neg-sub-local
   (equal (field-neg (field-sub x y))
          (field-sub y x))
   :hints (("Goal" :in-theory
            (enable field-sub field-neg-of-add-local field-neg-of-neg)))))

(local
 (defthm field-neg-mul-sub-local
   (equal (field-mul (field-neg r) (field-sub x y))
          (field-mul r (field-sub y x)))
   :hints
   (("Goal"
     :use ((:instance field-neg-mul-left-local
                      (x r) (y (field-sub x y)))
           (:instance field-neg-mul-right-local
                      (x r) (y (field-sub x y)))
           (:instance field-neg-sub-local (x x) (y y)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-neg-product-of-difference-local
   (implies
    (and (field-element-p x) (field-element-p y))
    (equal (field-neg (field-mul r (field-add x (field-neg y))))
           (field-mul r (field-add y (field-neg x)))))
   :hints
   (("Goal"
     :use ((:instance field-neg-mul-right-local
                      (x r) (y (field-add x (field-neg y))))
           (:instance field-neg-of-add-local (x x) (y (field-neg y)))
           (:instance field-neg-of-neg (x y))
           (:instance field-add-commutative (x (field-neg x)) (y y)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-fix-when-field-element-p
        field-element-p-of-add field-element-p-of-neg))))))

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
 (defthm field-two-times-local
   (equal (field-mul (field-add (field-one) (field-one)) x)
          (field-add (field-fix x) (field-fix x)))
   :hints
   (("Goal"
     :use ((:instance field-mul-right-distributive
                      (x (field-one)) (y (field-one)) (z x))
           (:instance field-mul-one-left (x x)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-three-summands-reorder-local
   (equal (field-add x (field-add y y))
          (field-add y (field-add y x)))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-local (x x) (y y) (z y))
           (:instance field-add-commutative (x x) (y y)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-associative field-fix-of-add))))))

(local
 (defthm inverse-secant-y-coincidence-local
   (implies
    (and (equal yb (field-neg ya))
         (equal xu xa)
         (equal (field-add yu yb)
                (field-mul r (field-sub xb xu)))
         (equal xb xa)
         (field-element-p ya)
         (field-element-p yb)
         (field-element-p yu)
         (field-element-p xa)
         (field-element-p xb)
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
      '(field-sub-self field-mul-zero-right
        field-fix-when-field-element-p))))))

(defthm affine-inverse-secant-coincident-x-implies-ordinate-equality
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c r u)
        (equal (affine-coordinates-x u)
               (affine-coordinates-x a)))
   (equal (affine-coordinates-y u)
          (affine-coordinates-y a)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance inverse-secant-y-coincidence-local
                     (ya (affine-coordinates-y a))
                     (yb (affine-coordinates-y b))
                     (yu (affine-coordinates-y u))
                     (xa (affine-coordinates-x a))
                     (xb (affine-coordinates-x b))
                     (xu (affine-coordinates-x u))
                     (r (field-fix r))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-distinct-x-secant-relation-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y)))))

(defthm affine-inverse-secant-translation-outer-distinct-x
  (implies
   (and (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c r u)
        (not (equal (affine-coordinates-x u)
                    (affine-coordinates-x a))))
   (affine-distinct-x-secant-relation-p
    a u (field-neg (field-fix r)) c))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-add-commutative
                     (x (affine-coordinates-y u))
                     (y (affine-coordinates-y b)))
          (:instance field-neg-product-of-difference-local
                     (r (field-fix r))
                     (x (affine-coordinates-x u))
                     (y (affine-coordinates-x a))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-distinct-x-secant-relation-p
       field-sub field-neg-mul-left-local field-neg-mul-right-local
       field-neg-of-add-local field-neg-sub-local field-neg-mul-sub-local
       field-neg-product-of-difference-local
       field-neg-square-local field-neg-of-neg
       field-add-associative field-add-commutative
       field-add-inverse-left field-add-inverse-right
       field-add-zero-left field-add-zero-right
       field-mul-fix-left field-mul-fix-right
       field-fix-of-add field-fix-of-neg field-fix-of-mul
       field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y)))))

(defthm affine-inverse-secant-translation-outer-doubling
  (implies
   (and (short-weierstrass-characteristic-p)
        (affine-opposite-y-infinity-relation-p a b infinity)
        (affine-distinct-x-secant-relation-p b c r u)
        (equal (affine-coordinates-x u)
               (affine-coordinates-x a)))
   (affine-doubling-relation-p
    a (field-neg (field-fix r)) c))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-inverse-secant-coincident-x-implies-ordinate-equality)
     (:instance affine-inverse-secant-coincident-x-excludes-self-inverse)
     (:instance affine-inverse-secant-coincident-x-implies-tangent-equation)
     (:instance field-three-summands-reorder-local
                (x (affine-coordinates-x c))
                (y (affine-coordinates-x a)))
     (:instance field-neg-product-of-difference-local
                (r (field-fix r))
                (x (affine-coordinates-x a))
                (y (affine-coordinates-x c)))
     (:instance field-add-commutative
                (x (affine-coordinates-y c))
                (y (affine-coordinates-y a))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-infinity-relation-p
       affine-distinct-x-secant-relation-p affine-doubling-relation-p
       field-sub field-neg-mul-left-local field-neg-mul-right-local
       field-neg-of-add-local field-neg-sub-local field-neg-mul-sub-local
       field-neg-product-of-difference-local
       field-neg-square-local field-neg-of-neg
       field-add-associative field-add-commutative
       field-add-inverse-left field-add-inverse-right
       field-add-zero-left field-add-zero-right
       field-mul-fix-left field-mul-fix-right field-two-times-local
       field-fix-of-add field-fix-of-neg field-fix-of-mul
       field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y)))))

(defthm affine-inverse-secant-translation
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (affine-opposite-y-infinity-relation-p a b infinity)
    (affine-distinct-x-secant-relation-p b c r u))
   (or
    (affine-distinct-x-secant-relation-p
     a u (field-neg (field-fix r)) c)
    (affine-doubling-relation-p
     a (field-neg (field-fix r)) c)))
  :rule-classes nil
  :hints
  (("Goal"
    :use (affine-inverse-secant-translation-outer-distinct-x
          affine-inverse-secant-translation-outer-doubling)
    :cases ((equal (affine-coordinates-x u)
                   (affine-coordinates-x a)))
    :in-theory (theory 'minimal-theory))))
