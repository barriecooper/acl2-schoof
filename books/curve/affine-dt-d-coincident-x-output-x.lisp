(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-tangent-equation")
(include-book "affine-same-point-non-opposite-output-x")
(include-book "affine-same-point-non-opposite-output-y")
(include-book "affine-distinct-x-secant-identity")
(include-book "affine-distinct-x-secant-relation")
(include-book "affine-doubling-relation")
(include-book "../field/xcert-confluent-h-reconstruction")
(include-book "../field/xcert-s-reconstruction")
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

(local
 (defthm non-self-inverse-implies-self-tangent-class-local
  (implies (not (equal (affine-coordinates-y a)
                       (field-neg (affine-coordinates-y a))))
   (equal (affine-pair-classify a a) :same-point-non-opposite))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance affine-pair-classify-same-point-non-opposite-characterization
                            (first a) (second a)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(affine-coordinates-x-of-fix
                          affine-coordinates-y-of-fix))))))

(local
 (defthm non-self-inverse-implies-double-y-nonzero-local
  (implies (not (equal (affine-coordinates-y a)
                       (field-neg (affine-coordinates-y a))))
   (not (equal (field-add (affine-coordinates-y a)
                          (affine-coordinates-y a))
               (field-zero))))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                                   (x (affine-coordinates-y a))
                                   (y (affine-coordinates-y a))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(field-element-p-of-affine-coordinates-y
                          field-fix-when-field-element-p))))))

(local
 (defthm field-mul-right-cancel-forward-local
  (implies (and (not (equal (field-fix denominator) (field-zero)))
                (equal (field-mul left denominator)
                       (field-mul right denominator)))
   (equal (field-fix left) (field-fix right)))
  :hints (("Goal" :use ((:instance field-mul-left-cancel-forward
                                   (x denominator) (y left) (z right))
                          (:instance field-mul-commutative (x left) (y denominator))
                          (:instance field-mul-commutative (x right) (y denominator)))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm dt-d-witness-equals-canonical-slope-local
   (implies (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
                 (affine-doubling-relation-p b t-slope q-output)
                 (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
                 (equal (affine-coordinates-x q-output)
                        (affine-coordinates-x a)))
    (equal (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                      (field-fix t-slope))
           (affine-same-point-non-opposite-slope a)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance affine-dt-d-coincident-x-excludes-self-inverse)
                  (:instance non-self-inverse-implies-self-tangent-class-local)
                  (:instance non-self-inverse-implies-double-y-nonzero-local)
                  (:instance affine-dt-d-coincident-x-tangent-equation)
                  (:instance affine-same-point-non-opposite-slope-reconstructs-tangent-numerator
                             (first a) (second a))
                  (:instance field-mul-right-cancel-forward-local
                   (left (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                                    (field-fix t-slope)))
                   (right (affine-same-point-non-opposite-slope a))
                   (denominator (field-add (affine-coordinates-y a)
                                           (affine-coordinates-y a)))))
            :in-theory (union-theories (theory 'minimal-theory)
             '(field-fix-of-affine-same-point-non-opposite-slope
               field-fix-of-add field-fix-of-neg field-sub))))))

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
 (defthm dt-d-balance-from-witness-local
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
 (defthm dt-d-h-zero-local
   (implies (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
                 (affine-doubling-relation-p b t-slope q-output)
                 (affine-distinct-x-secant-relation-p p-output b q-slope r-output))
    (equal (xcert-h (field-fix p-slope) (field-fix q-slope) (field-fix t-slope)
                    (affine-coordinates-x a) (affine-coordinates-x b))
           (field-zero)))
   :rule-classes nil
   :hints (("Goal" :use (dt-d-confluent-h-local)
            :in-theory (union-theories (theory 'minimal-theory)
                         '(xcert-h field-sub-self field-fix-of-add field-fix-of-mul
                           field-fix-of-neg))))))
(local
 (defthm dt-d-s-zero-local
   (implies (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
                 (affine-doubling-relation-p b t-slope q-output)
                 (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
                 (equal (affine-coordinates-x q-output) (affine-coordinates-x a)))
    (equal (xcert-s (field-fix p-slope) (field-fix q-slope) (field-fix t-slope)
                    (affine-same-point-non-opposite-slope a))
           (field-zero)))
   :rule-classes nil
   :hints (("Goal" :use (dt-d-witness-equals-canonical-slope-local
                           (:instance dt-d-balance-from-witness-local
                            (p (field-fix p-slope)) (q (field-fix q-slope))
                            (r (field-fix t-slope))
                            (tt (affine-same-point-non-opposite-slope a))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(xcert-s field-fix-of-affine-same-point-non-opposite-slope
                           field-fix-of-add field-fix-of-neg))))))
(local
 (defthm dt-d-telescope-zero-local
   (implies (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
                 (affine-doubling-relation-p b t-slope q-output)
                 (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
                 (equal (affine-coordinates-x q-output)
                        (affine-coordinates-x a)))
    (equal
     (xcert-telescope
      (affine-coordinates-x r-output) (affine-same-point-non-opposite-output-x a)
      (affine-coordinates-x p-output) (affine-coordinates-x q-output)
      (affine-coordinates-x a) (affine-coordinates-x b) (affine-coordinates-x b)
      (field-fix p-slope) (field-fix q-slope) (field-fix t-slope)
      (affine-same-point-non-opposite-slope a))
     (field-zero)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance affine-same-point-non-opposite-output-x-rearrangement
                           (first a)))
            :in-theory (union-theories (theory 'minimal-theory)
             '(xcert-telescope xcert-gxl xcert-gxr xcert-gxab xcert-gxbc
               affine-distinct-x-secant-relation-p affine-doubling-relation-p
               field-mul-right-distributive field-mul-one-left field-mul-one-right
               field-add-associative field-add-commutative field-add-swap-local
               field-add-inverse-shuffle-local field-neg-of-add-local
               field-add-inverse-left field-add-inverse-right
               field-sub-self field-sub-zero field-add-zero-left field-add-zero-right
               field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero
               field-fix-idempotent field-fix-when-field-element-p
               field-element-p-of-affine-coordinates-x field-fix-of-affine-same-point-non-opposite-slope))))))

(local
 (defthm dt-d-canonical-output-x-local
   (implies (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
                 (affine-doubling-relation-p b t-slope q-output)
                 (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
                 (equal (affine-coordinates-x q-output) (affine-coordinates-x a)))
    (equal (affine-same-point-non-opposite-output-x a) (affine-coordinates-x r-output)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     (dt-d-h-zero-local dt-d-s-zero-local dt-d-telescope-zero-local
      (:instance xcert-composition
       (xl (affine-coordinates-x r-output)) (xr (affine-same-point-non-opposite-output-x a))
       (xab (affine-coordinates-x p-output)) (xbc (affine-coordinates-x q-output))
       (xa (affine-coordinates-x a)) (xb (affine-coordinates-x b))
       (xc (affine-coordinates-x b))
       (p (field-fix p-slope)) (q (field-fix q-slope)) (r (field-fix t-slope))
       (tt (affine-same-point-non-opposite-slope a)))
      (:instance field-sub-equal-zero-implies-fixed-equal
       (first (affine-coordinates-x r-output))
       (second (affine-same-point-non-opposite-output-x a))))
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(xcert-dx xcert-c field-sub-self field-mul-zero-right
        field-add-zero-left field-add-zero-right field-neg-of-zero field-sub
        field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero
        field-fix-when-field-element-p field-element-p-of-affine-coordinates-x
        field-element-p-of-affine-same-point-non-opposite-output-x))))))

(local
 (defthm field-two-times-local
  (equal (field-mul (field-add (field-one) (field-one)) x)
         (field-add x x))
  :hints (("Goal" :in-theory (enable field-mul-left-distributive
                                       field-fix-of-mul)))))

(defthm affine-dt-d-coincident-x-output-x-equation
  (implies
   (and
    (affine-distinct-x-secant-relation-p
     a b p-slope p-output)
    (affine-doubling-relation-p
     b t-slope q-output)
    (affine-distinct-x-secant-relation-p
     p-output b q-slope r-output)
    (equal
     (affine-coordinates-x q-output)
     (affine-coordinates-x a)))
   (equal
    (field-add
     (field-add
      (affine-coordinates-x r-output)
      (affine-coordinates-x a))
     (affine-coordinates-x a))
    (field-mul
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix q-slope))
      (field-fix t-slope))
     (field-sub
      (field-add (field-fix p-slope)
                 (field-fix q-slope))
      (field-fix t-slope)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (dt-d-canonical-output-x-local
          dt-d-witness-equals-canonical-slope-local
          (:instance affine-same-point-non-opposite-output-x-rearrangement
                     (first a)))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(field-two-times-local field-add-associative
       field-add-fixed-congruence field-mul-fixed-congruence
       field-fix-of-add field-fix-of-mul
       field-element-p-of-affine-coordinates-x
       field-fix-when-field-element-p)))))

(local
 (defthm field-add-right-cancel-output-y-local
  (implies (equal (field-add left common) (field-add right common))
   (equal (field-fix left) (field-fix right)))
  :hints (("Goal"
           :use ((:instance field-add-left-cancel-forward
                            (x common) (y left) (z right))
                 (:instance field-add-commutative (x left) (y common))
                 (:instance field-add-commutative (x right) (y common)))
           :in-theory (theory 'minimal-theory)))))

; Recover the canonical output association from the public output-x endpoint,
; rather than replaying H, S, the telescope, or composition.
(local
 (defthm dt-d-canonical-output-x-for-output-y-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (equal (affine-coordinates-x q-output)
               (affine-coordinates-x a)))
   (equal (affine-same-point-non-opposite-output-x a)
          (affine-coordinates-x r-output)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (dt-d-witness-equals-canonical-slope-local
     (:instance affine-dt-d-coincident-x-output-x-equation)
     (:instance affine-same-point-non-opposite-output-x-rearrangement
                (first a))
     (:instance field-add-right-cancel-output-y-local
      (left (field-add (affine-same-point-non-opposite-output-x a)
                       (affine-coordinates-x a)))
      (right (field-add (affine-coordinates-x r-output)
                        (affine-coordinates-x a)))
      (common (affine-coordinates-x a)))
     (:instance field-add-right-cancel-output-y-local
      (left (affine-same-point-non-opposite-output-x a))
      (right (affine-coordinates-x r-output))
      (common (affine-coordinates-x a))))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(field-two-times-local field-add-associative field-fix-of-add field-fix-of-mul
       field-fix-when-field-element-p field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-same-point-non-opposite-output-x
       field-mul-fixed-congruence
       field-fix-of-affine-same-point-non-opposite-slope))))))

; With xab=P, xc=B, the left outer line q/R, and the right outer
; canonical tangent u/D, the final-y interface has exactly nine equations:
; two output-x equations, confluent H, balance, three input-line equations,
; and the two output-y equations.  Before H/S reduction its residual is
;
;   yR-yD = (p-t)*(xR-xB) + (t-q)*(xA-xB).
;
; Thus the coefficients are p-t and t-q respectively.  The field-only
; theorem consumes H and balance (S=0), together with the left output-x
; equation, to eliminate both terms; xD=xR associates the right output-y
; equation with the same output abscissa.  No multiplication cancellation is
; added here.
(local
 (defthm dt-d-canonical-output-y-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (equal (affine-coordinates-x q-output)
               (affine-coordinates-x a)))
   (equal (affine-coordinates-y r-output)
          (affine-same-point-non-opposite-output-y a)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (dt-d-confluent-h-local
     dt-d-witness-equals-canonical-slope-local
     dt-d-canonical-output-x-for-output-y-local
     (:instance dt-d-balance-from-witness-local
      (p (field-fix p-slope)) (q (field-fix q-slope))
      (r (field-fix t-slope))
      (tt (affine-same-point-non-opposite-slope a)))
     (:instance affine-same-point-non-opposite-output-y-rearrangement
      (first a))
     (:instance xcert-field-only-final-y-equal
      (xl (affine-coordinates-x r-output))
      (yl (affine-coordinates-y r-output))
      (yr (affine-same-point-non-opposite-output-y a))
      (xab (affine-coordinates-x p-output))
      (yab (affine-coordinates-y p-output))
      (xa (affine-coordinates-x a)) (ya (affine-coordinates-y a))
      (xb (affine-coordinates-x b)) (yb (affine-coordinates-y b))
      (xc (affine-coordinates-x b)) (yc (affine-coordinates-y b))
      (p (field-fix p-slope)) (q (field-fix q-slope))
      (r (field-fix t-slope))
      (tt (affine-same-point-non-opposite-slope a))))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
       field-fix-idempotent field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-y
       field-element-p-of-affine-same-point-non-opposite-output-y
       field-fix-of-affine-same-point-non-opposite-slope
       field-fix-of-affine-same-point-non-opposite-output-y
       field-fix-of-add field-fix-of-mul field-fix-of-neg field-sub-self
       field-mul-zero-left field-mul-zero-right))))))

(defthm affine-dt-d-coincident-x-output-y-equation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
    (equal (affine-coordinates-x q-output)
           (affine-coordinates-x a)))
   (equal
    (field-add (affine-coordinates-y r-output)
               (affine-coordinates-y a))
    (field-mul
     (field-sub (field-add (field-fix p-slope)
                           (field-fix q-slope))
                (field-fix t-slope))
     (field-sub (affine-coordinates-x a)
                (affine-coordinates-x r-output)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (dt-d-witness-equals-canonical-slope-local
          dt-d-canonical-output-x-for-output-y-local
          dt-d-canonical-output-y-local
          (:instance affine-same-point-non-opposite-output-y-rearrangement
                     (first a)))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(field-add-fixed-congruence field-mul-fixed-congruence
       field-fix-of-add field-fix-of-mul field-fix-of-neg
       field-fix-of-affine-same-point-non-opposite-slope)))))
