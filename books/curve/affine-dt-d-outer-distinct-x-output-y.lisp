(in-package "GFIELD")

(include-book "affine-dt-d-outer-distinct-x-output-x")
(include-book "../field/xcert-final-y-reconstruction")

(local
 (defthm relation-input-secant-identity-local
  (implies (affine-distinct-x-secant-relation-p first second slope output)
   (equal
    (field-mul (field-fix slope)
     (field-add (affine-coordinates-y second) (affine-coordinates-y first)))
    (field-add
     (field-mul (affine-coordinates-x second) (affine-coordinates-x second))
     (field-add
      (field-mul (affine-coordinates-x second) (affine-coordinates-x first))
      (field-add
       (field-mul (affine-coordinates-x first) (affine-coordinates-x first))
       (field-fix (short-weierstrass-a)))))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance affine-pair-classify-distinct-x-characterization)
         (:instance affine-distinct-x-output-satisfies-secant-relation)
         (:instance affine-distinct-x-secant-relation-slope-unique
          (slope-a slope) (output-a output)
          (slope-b (affine-distinct-x-slope first second))
          (output-b (affine-distinct-x-output first second)))
         (:instance affine-distinct-x-input-secant-identity))
   :in-theory (union-theories (theory 'minimal-theory)
    '(affine-distinct-x-secant-relation-p affine-coordinates-x-of-fix
      field-fix-of-affine-distinct-x-slope field-fix-of-mul field-fix-of-add))))))

(local
 (defthm relation-distinct-x-difference-nonzero-local
  (implies (affine-distinct-x-secant-relation-p first second slope output)
   (not (equal (field-sub (affine-coordinates-x second)
                          (affine-coordinates-x first))
               (field-zero))))
  :hints (("Goal" :use ((:instance field-sub-equal-zero-implies-fixed-equal
                         (first (affine-coordinates-x second))
                         (second (affine-coordinates-x first))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(affine-distinct-x-secant-relation-p field-fix-when-field-element-p
      field-element-p-of-affine-coordinates-x))))))

(local
 (defthm dt-d-h-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output))
   (equal
    (field-mul (field-sub (field-fix p-slope) (field-fix t-slope))
               (field-add (field-fix p-slope) (field-fix q-slope)))
    (field-sub (affine-coordinates-x a) (affine-coordinates-x b))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance relation-distinct-x-difference-nonzero-local
          (first a) (second b) (slope p-slope) (output p-output))
         (:instance relation-distinct-x-difference-nonzero-local
          (first p-output) (second b) (slope q-slope) (output r-output))
         (:instance relation-input-secant-identity-local
          (first a) (second b) (slope p-slope) (output p-output))
         (:instance relation-input-secant-identity-local
          (first p-output) (second b) (slope q-slope) (output r-output))
         (:instance xcert-confluent-h-scalar-reconstruction
          (a (field-fix (short-weierstrass-a)))
          (p (field-fix p-slope)) (q (field-fix q-slope))
          (tangent (field-fix t-slope))
          (xa (affine-coordinates-x a)) (ya (affine-coordinates-y a))
          (xb (affine-coordinates-x b)) (yb (affine-coordinates-y b))
          (xp (affine-coordinates-x p-output))
          (yp (affine-coordinates-y p-output))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
      field-fix-idempotent field-fix-of-add field-fix-of-mul))))))

(local
 (defthm outer-distinct-x-difference-nonzero-local
  (implies (and (field-element-p xa) (field-element-p xq) (not (equal xq xa)))
   (not (equal (field-sub xq xa) (field-zero))))
  :hints (("Goal" :use ((:instance field-sub-equal-zero-implies-fixed-equal
                         (first xq) (second xa)))
   :in-theory (enable field-fix-when-field-element-p)))))

(local
 (defthm dt-d-witness-equals-canonical-slope-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (not (equal (affine-coordinates-x q-output) (affine-coordinates-x a))))
   (equal (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                     (field-fix t-slope))
          (affine-distinct-x-slope a q-output)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-dt-d-outer-distinct-x-slope-equation)
                          (:instance affine-pair-classify-distinct-x-characterization
                           (first a) (second q-output))
                          (:instance affine-distinct-x-slope-reconstructs-y-difference
                           (first a) (second q-output))
                          (:instance outer-distinct-x-difference-nonzero-local
                           (xa (affine-coordinates-x a))
                           (xq (affine-coordinates-x q-output)))
                          (:instance field-mul-left-cancel-forward
                           (x (field-sub (affine-coordinates-x q-output)
                                         (affine-coordinates-x a)))
                           (y (field-sub (field-add (field-fix p-slope)
                                                    (field-fix q-slope))
                                         (field-fix t-slope)))
                           (z (affine-distinct-x-slope a q-output))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(affine-coordinates-x-of-fix field-mul-commutative
      field-element-p-of-affine-coordinates-x field-fix-when-field-element-p
      field-fix-of-affine-distinct-x-slope field-fix-of-add field-fix-of-neg
      field-sub))))))

(local
 (defthm field-add-right-cancel-local
  (implies (equal (field-add left common) (field-add right common))
   (equal (field-fix left) (field-fix right)))
  :hints (("Goal" :use ((:instance field-add-left-cancel-forward
                          (x common) (y left) (z right))
                         (:instance field-add-commutative (x left) (y common))
                         (:instance field-add-commutative (x right) (y common)))
                  :in-theory (theory 'minimal-theory)))))

(local
 (defthm dt-d-canonical-output-x-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (not (equal (affine-coordinates-x q-output) (affine-coordinates-x a))))
   (equal (affine-distinct-x-output-x a q-output)
          (affine-coordinates-x r-output)))
  :rule-classes nil
  :hints (("Goal"
   :use (dt-d-witness-equals-canonical-slope-local
         (:instance affine-dt-d-outer-distinct-x-output-x-equation)
         (:instance affine-distinct-x-output-x-rearrangement
                    (first a) (second q-output))
         (:instance field-add-right-cancel-local
          (left (field-add (affine-distinct-x-output-x a q-output)
                           (affine-coordinates-x a)))
          (right (field-add (affine-coordinates-x r-output)
                            (affine-coordinates-x a)))
          (common (affine-coordinates-x q-output)))
         (:instance field-add-right-cancel-local
          (left (affine-distinct-x-output-x a q-output))
          (right (affine-coordinates-x r-output))
          (common (affine-coordinates-x a))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-associative field-add-commutative field-fix-of-add
      field-fix-when-field-element-p field-element-p-of-affine-coordinates-x
      field-element-p-of-affine-distinct-x-output-x field-mul-fixed-congruence
      field-fix-of-affine-distinct-x-slope))))))

(local
 (defthm field-add-swap-local
  (equal (field-add x (field-add y z)) (field-add y (field-add x z)))
  :hints (("Goal" :use ((:instance field-add-associative (x x) (y y) (z z))
                          (:instance field-add-associative (x y) (y x) (z z))
                          (:instance field-add-commutative (x x) (y y)))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-tail-local
   (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
   :hints (("Goal" :use ((:instance field-add-associative
                           (x x) (y (field-neg x)) (z y)))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(field-add-inverse-right field-add-zero-left
                           field-fix-idempotent))))))
(local
 (defthm field-add-inverse-shuffle-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints (("Goal" :use ((:instance field-add-swap-local
                           (x x) (y y) (z (field-add (field-neg x) z)))
                          (:instance field-add-inverse-tail-local (x x) (y z)))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(field-add-swap-local field-add-inverse-tail-local
                           field-add-fix-right))))))

(local
 (defthm field-neg-of-add-local
   (equal (field-neg (field-add x y))
          (field-add (field-neg x) (field-neg y)))
   :hints (("Goal" :use ((:instance field-additive-inverse-unique
                           (x (field-add x y))
                           (y (field-add (field-neg x) (field-neg y)))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(field-add-associative field-add-inverse-shuffle-local
                           field-add-inverse-right field-add-zero-left
                           field-fix-of-add field-fix-of-neg))))))

(local
 (defthm dt-d-balance-local
   (implies
    (equal (field-sub (field-add p q) r) (field-fix tt))
    (equal (field-sub (field-add p q) (field-add r tt)) (field-zero)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-add-fixed-congruence
             (x1 (field-sub (field-add p q) r)) (x2 tt)
             (y1 r) (y2 r))
           (:instance field-add-fixed-congruence
             (x1 (field-add p q)) (x2 (field-add r tt))
             (y1 (field-neg (field-add r tt)))
             (y2 (field-neg (field-add r tt)))))
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(field-sub field-add-associative field-add-commutative
        field-add-swap-local field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right field-neg-of-add-local
        field-add-inverse-shuffle-local field-add-fix-left field-add-fix-right
        field-fix-of-add field-fix-of-neg field-fix-idempotent))))))

(local
 (defthm dt-d-canonical-output-y-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (not (equal (affine-coordinates-x q-output) (affine-coordinates-x a))))
   (equal (affine-coordinates-y r-output)
          (affine-distinct-x-output-y a q-output)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (dt-d-h-local dt-d-witness-equals-canonical-slope-local
     dt-d-canonical-output-x-local
     (:instance dt-d-balance-local
      (p (field-fix p-slope)) (q (field-fix q-slope))
      (r (field-fix t-slope)) (tt (affine-distinct-x-slope a q-output)))
     (:instance affine-distinct-x-output-y-rearrangement
      (first a) (second q-output))
     (:instance xcert-field-only-final-y-equal
      (xl (affine-coordinates-x r-output))
      (yl (affine-coordinates-y r-output))
      (yr (affine-distinct-x-output-y a q-output))
      (xab (affine-coordinates-x p-output))
      (yab (affine-coordinates-y p-output))
      (xa (affine-coordinates-x a)) (ya (affine-coordinates-y a))
      (xb (affine-coordinates-x b)) (yb (affine-coordinates-y b))
      (xc (affine-coordinates-x b)) (yc (affine-coordinates-y b))
      (p (field-fix p-slope)) (q (field-fix q-slope))
      (r (field-fix t-slope))
      (tt (affine-distinct-x-slope a q-output))))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
       field-fix-idempotent field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-y
       field-fix-of-affine-distinct-x-slope
       field-fix-of-affine-distinct-x-output-y field-fix-of-add
       field-fix-of-mul field-fix-of-neg field-sub-self
       field-mul-zero-left field-mul-zero-right))))))

(defthm affine-dt-d-outer-distinct-x-output-y-equation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
    (not (equal (affine-coordinates-x q-output)
                (affine-coordinates-x a))))
   (equal
    (field-add (affine-coordinates-y r-output)
               (affine-coordinates-y a))
    (field-mul
     (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                (field-fix t-slope))
     (field-sub (affine-coordinates-x a)
                (affine-coordinates-x r-output)))))
  :rule-classes nil
  :hints (("Goal"
   :use (dt-d-witness-equals-canonical-slope-local
         dt-d-canonical-output-x-local dt-d-canonical-output-y-local
         (:instance affine-distinct-x-output-y-rearrangement
          (first a) (second q-output)))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-fixed-congruence field-mul-fixed-congruence
      field-fix-of-add field-fix-of-mul field-fix-of-neg
      field-fix-of-affine-distinct-x-slope)))))
