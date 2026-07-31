(in-package "GFIELD")

(include-book "affine-distinct-x-secant-relation")
(include-book "exceptional-addition-relations")
(include-book "curve-point-addition-commutativity")

; Proof-local additive normalization for the oriented DD-O certificate.
(local
 (defthm field-add-inverse-middle-local
   (equal (field-add x (field-add (field-neg x) y))
          (field-fix y))
   :hints (("Goal" :use ((:instance field-add-associative
                                    (x x) (y (field-neg x)) (z y)))
            :in-theory (enable field-add-inverse-right
                               field-add-zero-left)))))

(local
 (defthm field-add-swap-local
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints (("Goal" :use ((:instance field-add-associative
                                    (x x) (y y) (z z))
                          (:instance field-add-associative
                                    (x y) (y x) (z z))
                          (:instance field-add-commutative (x x) (y y)))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-shuffle-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints (("Goal"
            :use ((:instance field-add-swap-local
                             (x x) (y y)
                             (z (field-add (field-neg x) z)))
                  (:instance field-add-inverse-middle-local (x x) (y z)))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(field-add-swap-local field-add-inverse-middle-local
               field-add-fix-right))))))

(local
 (defthm field-neg-of-add-local
   (equal (field-neg (field-add x y))
          (field-add (field-neg x) (field-neg y)))
   :hints (("Goal"
            :use ((:instance field-additive-inverse-unique
                             (x (field-add x y))
                             (y (field-add (field-neg x) (field-neg y)))))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(field-add-associative field-add-inverse-shuffle-local
               field-add-inverse-right field-add-zero-left field-fix-of-add
               field-fix-of-neg))))))

(local
 (defthm field-mul-of-neg-right-local
   (equal (field-mul x (field-neg y))
          (field-neg (field-mul x y)))
   :hints (("Goal"
            :use ((:instance field-additive-inverse-unique
                             (x (field-mul x y))
                             (y (field-mul x (field-neg y))))
                  (:instance field-mul-left-distributive
                             (x x) (y y) (z (field-neg y))))
            :in-theory (enable field-add-inverse-right
                               field-mul-zero-right)))))

(local
 (defthm equal-implies-field-neg-equal-local
   (implies (equal x y)
            (equal (field-neg x) (field-neg y)))))

(local
 (defthm field-negated-difference-equality-local
   (implies
    (equal (field-add a (field-neg b))
           (field-add c (field-neg d)))
    (equal (field-add b (field-neg a))
           (field-add d (field-neg c))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance equal-implies-field-neg-equal-local
                             (x (field-add a (field-neg b)))
                             (y (field-add c (field-neg d))))
                  (:instance field-neg-of-add-local
                             (x a) (y (field-neg b)))
                  (:instance field-neg-of-add-local
                             (x c) (y (field-neg d))))
            :in-theory
            (enable field-neg-of-neg field-add-commutative
                    field-fix-when-field-element-p)))))

(local
 (defthm field-mutual-negation-local
   (implies (and (field-element-p x)
                 (field-element-p y)
                 (equal y (field-neg x)))
            (equal x (field-neg y)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance equal-implies-field-neg-equal-local
                             (x y) (y (field-neg x)))
                  (:instance field-neg-of-neg (x x)))
            :in-theory (enable field-fix-when-field-element-p)))))

(local
 (defthm dd-o1-local
   (implies
    (and (equal (field-add yp ya)
                (field-mul slope (field-sub xa xp)))
         (equal xp xc)
         (equal yp (field-neg yc)))
    (equal (field-sub yc ya)
           (field-mul slope (field-sub xc xa))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-negated-difference-equality-local
                             (a ya) (b yc)
                             (c (field-mul slope xa))
                             (d (field-mul slope xc))))
            :in-theory
            (enable field-sub field-mul-left-distributive
                    field-mul-of-neg-right-local field-neg-of-add-local
                    field-add-associative field-add-commutative
                    field-add-swap-local field-add-inverse-middle-local
                    field-add-inverse-left field-add-inverse-right
                    field-add-zero-left field-add-zero-right
                    field-neg-of-neg field-fix-of-add field-fix-of-mul
                    field-fix-of-neg)))))

(local
 (defthm field-add-differences-local
   (equal (field-add (field-sub x y) (field-sub y z))
          (field-sub x z))
   :hints
   (("Goal"
     :use ((:instance field-add-associative
                      (x (field-neg y)) (y y) (z (field-neg z))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-add-associative field-add-inverse-middle-local
        field-add-inverse-left field-add-zero-left field-add-fix-right
        field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-difference-chain-local
   (implies
    (and (equal (field-sub x y) (field-sub u v))
         (equal (field-sub v w) (field-sub y z)))
    (equal (field-sub x z) (field-sub u w)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-add-fixed-congruence
                      (x1 (field-sub x y)) (x2 (field-sub u v))
                      (y1 (field-sub y z)) (y2 (field-sub v w))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-differences-local field-fix-of-add))))))

(local
 (defthm dd-o-shared-line-local
   (implies
    (and (equal (field-sub yc ya)
                (field-mul slope (field-sub xc xa)))
         (equal (field-mul slope (field-sub xb xa))
                (field-sub yb ya)))
    (equal (field-mul slope (field-sub xc xb))
           (field-sub yc yb)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-negated-difference-equality-local
                             (a (field-mul slope xb))
                             (b (field-mul slope xa))
                             (c yb) (d ya))
                  (:instance field-difference-chain-local
                             (x yc) (y ya) (z yb)
                             (u (field-mul slope xc))
                             (v (field-mul slope xa))
                             (w (field-mul slope xb))))
            :in-theory
            (enable field-sub field-mul-left-distributive
                    field-mul-of-neg-right-local field-neg-of-add-local
                    field-add-associative field-add-commutative
                    field-add-swap-local field-add-inverse-middle-local
                    field-add-inverse-left field-add-inverse-right
                    field-add-zero-left field-add-zero-right
                    field-neg-of-neg field-fix-of-add field-fix-of-mul
                    field-fix-of-neg)))))

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
 (defthm dd-o-slope-equality-local
   (implies
    (and (equal (field-mul p denominator) rhs)
         (equal (field-mul r denominator) rhs)
         (not (equal (field-fix denominator) (field-zero))))
    (equal (field-fix p) (field-fix r)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-mul-left-cancel-forward
                             (x denominator) (y p) (z r))
                  (:instance field-mul-commutative (x p) (y denominator))
                  (:instance field-mul-commutative (x r) (y denominator)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-add-right-cancel-forward-local
   (implies (equal (field-add left common) (field-add right common))
            (equal (field-fix left) (field-fix right)))
   :hints (("Goal"
            :use ((:instance field-add-left-cancel-forward
                             (x common) (y left) (z right))
                  (:instance field-add-commutative (x left) (y common))
                  (:instance field-add-commutative (x right) (y common)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-add-two-right-cancel-local
   (implies
    (equal (field-add (field-add x b) c)
           (field-add (field-add y b) c))
    (equal (field-fix x) (field-fix y)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-add-right-cancel-forward-local
                             (left (field-add x b))
                             (right (field-add y b)) (common c))
                  (:instance field-add-right-cancel-forward-local
                             (left x) (right y) (common b)))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-fix-of-add))))))

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
 (defthm equal-via-common-values-local
   (implies (and (equal x a) (equal y b) (equal a b))
            (equal x y))
   :rule-classes nil))

(local
 (defthm dd-o-x-output-local
   (implies
    (and (equal (field-add (field-add xp xa) xb)
                (field-mul p p))
         (equal (field-add (field-add xq xb) xc)
                (field-mul r r))
         (equal xp xc)
         (equal (field-fix p) (field-fix r))
         (field-element-p xq)
         (field-element-p xa))
    (equal xq xa))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-mul-fixed-congruence
                             (x1 p) (x2 r) (y1 p) (y2 r))
                  (:instance field-add-three-rotate-local
                             (a xc) (b xa) (c xb))
                  (:instance equal-via-common-values-local
                             (x (field-add (field-add xc xa) xb))
                             (y (field-add (field-add xq xb) xc))
                             (a (field-mul p p))
                             (b (field-mul r r)))
                  (:instance field-add-two-right-cancel-local
                             (x xq) (y xa) (b xb) (c xc)))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(field-add-three-rotate-local field-fix-of-mul
               field-fix-when-field-element-p))))))

(local
 (defthm dd-o-y-output-local
   (implies
    (and (equal (field-add yq yb)
                (field-mul r (field-sub xb xq)))
         (equal (field-mul p (field-sub xb xa))
                (field-sub yb ya))
         (equal xq xa)
         (equal (field-fix p) (field-fix r))
         (field-element-p yq)
         (field-element-p ya))
    (equal yq (field-neg ya)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-mul-fixed-congruence
                      (x1 r) (x2 p)
                      (y1 (field-sub xb xa))
                      (y2 (field-sub xb xa)))
           (:instance field-add-left-cancel-forward
                      (x yb) (y yq) (z (field-neg ya))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-add-commutative field-fix-of-mul
        field-fix-of-neg field-fix-when-field-element-p))))))

; Stable classifier-free Stage 3 DD-O boundary.  The only nonzero factor used
; in the proof is the B,C secant difference already present in the relation.
(defthm affine-dd-opposite-y-propagates-to-other-tree
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p)
        (affine-distinct-x-secant-relation-p b c r-slope q)
        (affine-opposite-y-infinity-relation-p p c infinity))
   (affine-opposite-y-infinity-relation-p a q infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance dd-o1-local
                (yp (affine-coordinates-y p))
                (ya (affine-coordinates-y a))
                (yc (affine-coordinates-y c))
                (xa (affine-coordinates-x a))
                (xp (affine-coordinates-x p))
                (xc (affine-coordinates-x c))
                (slope (field-fix p-slope)))
     (:instance field-mutual-negation-local
                (x (affine-coordinates-y p))
                (y (affine-coordinates-y c)))
     (:instance dd-o-shared-line-local
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yc (affine-coordinates-y c))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (xc (affine-coordinates-x c))
                (slope (field-fix p-slope)))
     (:instance nonzero-difference-local
                (x (affine-coordinates-x b))
                (y (affine-coordinates-x c)))
     (:instance dd-o-slope-equality-local
                (p (field-fix p-slope)) (r (field-fix r-slope))
                (denominator
                 (field-sub (affine-coordinates-x c)
                            (affine-coordinates-x b)))
                (rhs (field-sub (affine-coordinates-y c)
                                (affine-coordinates-y b))))
     (:instance dd-o-x-output-local
                (xp (affine-coordinates-x p))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (xc (affine-coordinates-x c))
                (xq (affine-coordinates-x q))
                (p (field-fix p-slope)) (r (field-fix r-slope)))
     (:instance dd-o-y-output-local
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yq (affine-coordinates-y q))
                (xa (affine-coordinates-x a))
                (xb (affine-coordinates-x b))
                (xq (affine-coordinates-x q))
                (p (field-fix p-slope)) (r (field-fix r-slope))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-opposite-y-infinity-relation-p
       field-sub
       field-fix-when-field-element-p field-fix-idempotent
       field-fix-of-add field-fix-of-neg
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y)))))

; The converse tree orientation is structural: reverse both inner secants,
; reverse the opposite-y pair, and apply the oriented DD-O certificate to the
; point order C,B,A.  No coordinate algebra is replayed here.
(defthm affine-dd-opposite-y-propagates-to-left-tree
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope c)
        (affine-distinct-x-secant-relation-p b c r-slope q)
        (affine-opposite-y-infinity-relation-p a q infinity))
   (affine-opposite-y-infinity-relation-p c c infinity))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-distinct-x-secant-relation-p-reverse
                (first a) (second b) (slope p-slope) (output c))
     (:instance affine-distinct-x-secant-relation-p-reverse
                (first b) (second c) (slope r-slope) (output q))
     (:instance affine-opposite-y-infinity-relation-p-symmetric
                (first a) (second q) (output infinity))
     (:instance affine-dd-opposite-y-propagates-to-other-tree
                (a c) (b b) (c a)
                (p-slope r-slope) (p q)
                (r-slope p-slope) (q c)))
    :in-theory (theory 'minimal-theory))))
