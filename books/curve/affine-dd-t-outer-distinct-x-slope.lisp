(in-package "GFIELD")

(include-book "affine-distinct-x-secant-identity")
(include-book "affine-distinct-x-secant-relation")
(include-book "affine-doubling-relation")
(include-book "../field/xcert-s-reconstruction")

; The common-curve input needed by the X-CERT H reconstruction is obtained
; from semantic secant membership, rather than exposed as a client premise.
(local
 (defthm relation-input-secant-identity-local
   (implies
    (affine-distinct-x-secant-relation-p first second slope output)
    (equal
     (field-mul
      (field-fix slope)
      (field-add (affine-coordinates-y second)
                 (affine-coordinates-y first)))
     (field-add
      (field-mul (affine-coordinates-x second)
                 (affine-coordinates-x second))
      (field-add
       (field-mul (affine-coordinates-x second)
                  (affine-coordinates-x first))
       (field-add
        (field-mul (affine-coordinates-x first)
                   (affine-coordinates-x first))
        (field-fix (short-weierstrass-a)))))))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-pair-classify-distinct-x-characterization)
      (:instance affine-distinct-x-output-satisfies-secant-relation)
      (:instance affine-distinct-x-secant-relation-slope-unique
                 (slope-a slope)
                 (output-a output)
                 (slope-b (affine-distinct-x-slope first second))
                 (output-b (affine-distinct-x-output first second)))
      (:instance affine-distinct-x-input-secant-identity))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-distinct-x-secant-relation-p
        affine-coordinates-x-of-fix
        field-fix-of-affine-distinct-x-slope
        field-fix-of-mul field-fix-of-add))))))

(local
 (defthm field-three-times-square-local
   (equal
    (field-mul (field-add (field-add (field-one) (field-one)) (field-one))
               (field-mul x x))
    (field-add (field-mul x x)
               (field-add (field-mul x x) (field-mul x x))))
   :hints (("Goal" :in-theory
            (enable field-mul-left-distributive field-fix-of-add
                    field-fix-of-mul)))))

(local
 (defthm field-add-swap-local
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints (("Goal" :use ((:instance field-add-associative (x x) (y y) (z z))
                           (:instance field-add-associative (x y) (y x) (z z))
                           (:instance field-add-commutative (x x) (y y)))
            :in-theory (union-theories (theory 'minimal-theory)
                            '(field-fix-of-add))))))

(local
 (defthm tangent-numerator-xcert-shape-local
   (implies
    (equal (field-mul t-slope (field-add yc yc))
           (field-add
            (field-mul (field-add (field-add (field-one) (field-one))
                                  (field-one))
                       (field-mul xc xc))
            curve-a))
    (equal (field-mul t-slope (field-add yc yc))
           (field-add (field-mul xc xc)
                      (field-add (field-mul xc xc)
                                 (field-add (field-mul xc xc) curve-a)))))
   :hints (("Goal" :in-theory
            (enable field-mul-left-distributive field-add-associative
                    field-add-commutative field-add-swap-local field-fix-of-add
                    field-fix-of-mul)))))

(local
 (defthm relation-distinct-x-difference-nonzero-local
   (implies
    (affine-distinct-x-secant-relation-p first second slope output)
    (not (equal (field-sub (affine-coordinates-x second)
                           (affine-coordinates-x first))
                (field-zero))))
   :hints (("Goal"
            :use ((:instance field-sub-equal-zero-implies-fixed-equal
                             (first (affine-coordinates-x second))
                             (second (affine-coordinates-x first))))
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(affine-distinct-x-secant-relation-p
               field-fix-when-field-element-p
               field-element-p-of-affine-coordinates-x))))))

(local
 (defthm outer-distinct-x-difference-nonzero-local
   (implies
    (and (field-element-p xa) (field-element-p xq)
         (not (equal xq xa)))
    (not (equal (field-sub xq xa) (field-zero))))
   :hints (("Goal"
            :use ((:instance field-sub-equal-zero-implies-fixed-equal
                             (first xq) (second xa)))
            :in-theory (enable field-fix-when-field-element-p)))))

(local
 (defthm dd-t-s-balance-local
   (implies
    (and (affine-distinct-x-secant-relation-p a b p c)
         (affine-distinct-x-secant-relation-p b c r q)
         (affine-doubling-relation-p c t-slope d)
         (not (equal (affine-coordinates-x q)
                     (affine-coordinates-x a))))
    (equal
     (field-sub
      (field-add (field-fix p) (field-fix t-slope))
      (field-add
       (field-fix r)
       (affine-distinct-x-slope a q)))
     (field-zero)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance outer-distinct-x-difference-nonzero-local
                 (xa (affine-coordinates-x a))
                 (xq (affine-coordinates-x q)))
      (:instance affine-pair-classify-distinct-x-characterization (first a) (second q))
      (:instance affine-distinct-x-slope-reconstructs-y-difference (first a) (second q))
      (:instance relation-distinct-x-difference-nonzero-local
                 (first b) (second c) (slope r) (output q))
      (:instance tangent-numerator-xcert-shape-local
                 (t-slope (field-fix t-slope))
                 (yc (affine-coordinates-y c))
                 (xc (affine-coordinates-x c))
                 (curve-a (field-fix (short-weierstrass-a))))
      (:instance relation-input-secant-identity-local
                 (first a) (second b) (slope p) (output c))
      (:instance xcert-s-scalar-reconstruction
       (curve-a (field-fix (short-weierstrass-a)))
       (p (field-fix p)) (q (field-fix t-slope)) (r (field-fix r))
       (tt (affine-distinct-x-slope a q))
       (xa (affine-coordinates-x a))
       (ya (affine-coordinates-y a))
       (xb (affine-coordinates-x b))
       (yb (affine-coordinates-y b))
       (xc (affine-coordinates-x c))
       (yc (affine-coordinates-y c))
       (xab (affine-coordinates-x c))
       (yab (affine-coordinates-y c))
       (xbc (affine-coordinates-x q))
       (ybc (affine-coordinates-y q))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
        affine-coordinates-x-of-fix
        field-three-times-square-local field-add-associative
        field-add-inverse-right field-mul-zero-right field-fix-of-zero
        field-sub field-fix-idempotent field-fix-when-field-element-p
        field-element-p-of-affine-coordinates-x
        field-element-p-of-affine-coordinates-y
        field-element-p-of-affine-distinct-x-slope
        field-fix-of-affine-distinct-x-slope
        field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm dd-t-witness-equals-outer-slope-local
   (implies
    (equal
     (field-sub (field-add p t-slope) (field-add r outer-slope))
     (field-zero))
    (equal (field-sub (field-add p t-slope) r)
           (field-fix outer-slope)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-sub-equal-zero-implies-fixed-equal
                      (first (field-add p t-slope))
                      (second (field-add r outer-slope)))
           (:instance field-add-fixed-congruence
                      (x1 (field-add p t-slope))
                      (x2 (field-add r outer-slope))
                      (y1 (field-neg r)) (y2 (field-neg r))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-add-associative field-add-commutative
        field-add-swap-local
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right field-neg-of-neg
        field-fix-of-add field-fix-of-neg))))))

; Common membership is consumed by the input-secant identity for A,B.  With
; the tangent numerator at C in the second X-CERT input-identity slot, the
; pre-cancellation H/S algebra gives
;   (xq-xa) * (p+t-r-u) = 0,
; where u is the certified secant slope of A,Q.  The outer distinct-x premise
; makes xq-xa nonzero, so X-CERT cancels that factor and gives p+t=r+u.
; Substitution into u*(xq-xa)=yq-ya is equivalently the factored residual
;   (xq-xa) * (((p+t)-r)*(xq-xa)-(yq-ya)) = 0;
; the public theorem stops after cancelling the same xq-xa factor once.
(defthm affine-dd-t-outer-distinct-x-slope-equation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p c)
    (affine-distinct-x-secant-relation-p b c r q)
    (affine-doubling-relation-p c t-slope d)
    (not (equal (affine-coordinates-x q)
                (affine-coordinates-x a))))
   (equal
    (field-mul
     (field-sub (field-add (field-fix p) (field-fix t-slope))
                (field-fix r))
     (field-sub (affine-coordinates-x q)
                (affine-coordinates-x a)))
    (field-sub (affine-coordinates-y q)
               (affine-coordinates-y a))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-pair-classify-distinct-x-characterization (first a) (second q))
     dd-t-s-balance-local
     (:instance dd-t-witness-equals-outer-slope-local
                (p (field-fix p)) (t-slope (field-fix t-slope))
                (r (field-fix r))
                (outer-slope (affine-distinct-x-slope a q)))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first a) (second q)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-coordinates-x-of-fix
       field-fix-of-affine-distinct-x-slope
       field-mul-fixed-congruence field-fix-idempotent
       field-fix-of-mul field-fix-of-add field-fix-of-neg)))))
