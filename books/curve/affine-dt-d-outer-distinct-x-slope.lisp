(in-package "GFIELD")

(include-book "affine-distinct-x-secant-identity")
(include-book "affine-distinct-x-secant-relation")
(include-book "affine-doubling-relation")
(include-book "../field/xcert-confluent-h-reconstruction")
(include-book "../field/xcert-s-reconstruction")

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
 (defthm outer-distinct-x-difference-nonzero-local
  (implies (and (field-element-p xa) (field-element-p xq) (not (equal xq xa)))
   (not (equal (field-sub xq xa) (field-zero))))
  :hints (("Goal" :use ((:instance field-sub-equal-zero-implies-fixed-equal
                         (first xq) (second xa)))
   :in-theory (enable field-fix-when-field-element-p)))))

; Checkpoint 5: the seven scalar equations are the two ordered input
; identities, the tangent numerator, both ordered secant line equations, and
; the first secant output-x and output-y equations.  The two nonzero factors
; are supplied by those same secant relations.
(local
 (defthm dt-d-confluent-h-local
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

; Checkpoints 6 and 7: specialize the factored S interface with
; xab=P, xbc=Q, xc=xb, r=t, and tt=u.
(local
 (defthm dt-d-s-factored-residual-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (not (equal (affine-coordinates-x q-output)
                    (affine-coordinates-x a))))
   (equal
    (field-mul
     (field-sub (affine-coordinates-x q-output) (affine-coordinates-x a))
     (field-sub
      (field-add (field-fix p-slope) (field-fix q-slope))
      (field-add (field-fix t-slope) (affine-distinct-x-slope a q-output))))
    (field-zero)))
  :rule-classes nil
  :hints (("Goal"
   :use (dt-d-confluent-h-local
         (:instance affine-pair-classify-distinct-x-characterization
          (first a) (second q-output))
         (:instance affine-distinct-x-slope-reconstructs-y-difference
          (first a) (second q-output))
         (:instance xcert-s-factored-reconstruction-from-h
          (p (field-fix p-slope)) (q (field-fix q-slope))
          (r (field-fix t-slope)) (tt (affine-distinct-x-slope a q-output))
          (xa (affine-coordinates-x a)) (ya (affine-coordinates-y a))
          (xb (affine-coordinates-x b)) (yb (affine-coordinates-y b))
          (xc (affine-coordinates-x b)) (yc (affine-coordinates-y b))
          (xab (affine-coordinates-x p-output))
          (yab (affine-coordinates-y p-output))
          (xbc (affine-coordinates-x q-output))
          (ybc (affine-coordinates-y q-output))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
      affine-coordinates-x-of-fix field-mul-left-distributive field-mul-right-distributive
      field-mul-one-left field-mul-one-right
      field-add-associative field-sub-self field-mul-zero-left field-mul-zero-right
      field-fix-idempotent field-fix-when-field-element-p
      field-element-p-of-affine-coordinates-x field-fix-of-add field-fix-of-mul
      field-fix-of-affine-distinct-x-slope))))))

; Checkpoint 8: this is the sole post-H cancellation.
(local
 (defthm dt-d-s-balance-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (not (equal (affine-coordinates-x q-output)
                    (affine-coordinates-x a))))
   (equal (field-sub
           (field-add (field-fix p-slope) (field-fix q-slope))
           (field-add (field-fix t-slope)
                      (affine-distinct-x-slope a q-output)))
          (field-zero)))
  :rule-classes nil
  :hints (("Goal"
   :use (dt-d-s-factored-residual-local
         (:instance outer-distinct-x-difference-nonzero-local
          (xa (affine-coordinates-x a))
          (xq (affine-coordinates-x q-output)))
         (:instance field-mul-left-cancel-forward
          (x (field-sub (affine-coordinates-x q-output)
                        (affine-coordinates-x a)))
          (y (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                         (field-add (field-fix t-slope)
                                    (affine-distinct-x-slope a q-output))))
          (z (field-zero))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-sub field-fix-of-add field-fix-of-neg field-fix-of-zero
      field-mul-zero-right field-element-p-of-affine-coordinates-x))))))

(local
 (defthm field-add-swap-local
  (equal (field-add x (field-add y z)) (field-add y (field-add x z)))
  :hints (("Goal" :use ((:instance field-add-associative (x x) (y y) (z z))
                          (:instance field-add-associative (x y) (y x) (z z))
                          (:instance field-add-commutative (x x) (y y)))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-middle-local
  (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
  :hints (("Goal" :use ((:instance field-add-associative
                          (x x) (y (field-neg x)) (z y)))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-add-inverse-right field-add-zero-left field-fix-idempotent))))))

(local
 (defthm field-add-cancel-around-local
  (equal (field-add x (field-add y (field-neg x))) (field-fix y))
  :hints (("Goal" :use ((:instance field-add-commutative
                          (x y) (y (field-neg x)))
                         (:instance field-add-inverse-middle-local (x x) (y y)))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-add-fixed-congruence field-fix-of-add))))))

; Checkpoint 9: bounded additive normalization, with no cancellation.
(local
 (defthm dt-d-witness-equals-outer-slope-local
  (implies (equal (field-sub (field-add p q) (field-add tangent u))
                  (field-zero))
   (equal (field-sub (field-add p q) tangent) (field-fix u)))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance field-sub-equal-zero-implies-fixed-equal
          (first (field-add p q)) (second (field-add tangent u)))
         (:instance field-add-fixed-congruence
          (x1 (field-add p q)) (x2 (field-add tangent u))
          (y1 (field-neg tangent)) (y2 (field-neg tangent)))
         (:instance field-add-commutative (x u) (y (field-neg tangent)))
         (:instance field-add-inverse-middle-local (x tangent) (y u))
         (:instance field-add-cancel-around-local (x tangent) (y u)))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-sub field-add-associative field-add-commutative field-add-swap-local
      field-add-inverse-left field-add-inverse-right field-add-zero-left
      field-add-zero-right field-add-inverse-middle-local field-add-cancel-around-local field-neg-of-neg field-fix-of-add field-fix-of-neg))))))

(defthm affine-dt-d-outer-distinct-x-slope-equation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
    (not (equal (affine-coordinates-x q-output) (affine-coordinates-x a))))
   (equal
    (field-mul
     (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                (field-fix t-slope))
     (field-sub (affine-coordinates-x q-output) (affine-coordinates-x a)))
    (field-sub (affine-coordinates-y q-output) (affine-coordinates-y a))))
  :rule-classes nil
  :hints (("Goal"
   :use (dt-d-s-balance-local
         (:instance dt-d-witness-equals-outer-slope-local
          (p (field-fix p-slope)) (q (field-fix q-slope))
          (tangent (field-fix t-slope))
          (u (affine-distinct-x-slope a q-output)))
         (:instance affine-pair-classify-distinct-x-characterization
          (first a) (second q-output))
         (:instance affine-distinct-x-slope-reconstructs-y-difference
          (first a) (second q-output)))
   :in-theory (union-theories (theory 'minimal-theory)
    '(affine-coordinates-x-of-fix field-fix-of-affine-distinct-x-slope
      field-mul-fixed-congruence field-fix-idempotent field-fix-of-mul
      field-fix-of-add field-fix-of-neg))))
)
