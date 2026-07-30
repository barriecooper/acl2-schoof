(in-package "GFIELD")

(include-book "curve-point-pair-output-point")
(include-book "affine-distinct-x-closure")
(include-book "affine-same-point-non-opposite-closure")
(include-book "curve-point-addition-commutativity")

(local
 (defthm equal-fixed-affine-coordinates-from-accessors
   (implies
    (and (equal (affine-coordinates-x (affine-coordinates-fix first))
                (affine-coordinates-x (affine-coordinates-fix second)))
         (equal (affine-coordinates-y (affine-coordinates-fix first))
                (affine-coordinates-y (affine-coordinates-fix second))))
    (equal (affine-coordinates-fix first)
           (affine-coordinates-fix second)))
   :hints (("Goal" :in-theory (enable affine-coordinates-fix
                                       affine-coordinates-make)))))

(local
 (defthm affine-doubling-output-point-of-fix
   (equal (affine-same-point-non-opposite-output-point
           (affine-coordinates-fix first))
          (affine-same-point-non-opposite-output-point first))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-same-point-non-opposite-output-point
        affine-same-point-non-opposite-output
        affine-same-point-non-opposite-output-x
        affine-same-point-non-opposite-output-y
        affine-same-point-non-opposite-slope
        affine-coordinates-x-of-fix
        affine-coordinates-y-of-fix))))))

(local
 (defthm full-affine-inner-doubling-reduction
   (implies
    (equal (affine-pair-classify first second)
           :same-point-non-opposite)
    (equal
     (curve-point-pair-output-point
      (curve-point-affine-coordinates first)
      (curve-point-affine-coordinates second))
     (affine-same-point-non-opposite-output-point first)))
   :hints
   (("Goal"
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(curve-point-pair-output-point-of-affines
        affine-pair-classify-of-fixes
        affine-pair-output-point-when-same-point-non-opposite
        affine-doubling-output-point-of-fix))))))

(local
 (defthm equal-affine-fixes-imply-equal-doubling-output-points
   (implies
    (equal (affine-coordinates-fix first)
           (affine-coordinates-fix second))
    (equal (affine-same-point-non-opposite-output-point first)
           (affine-same-point-non-opposite-output-point second)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance affine-doubling-output-point-of-fix)
      (:instance affine-doubling-output-point-of-fix
                 (first second)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm equal-affine-fixes-imply-equal-tagged-points
   (implies
    (equal (affine-coordinates-fix first)
           (affine-coordinates-fix second))
    (equal (curve-point-affine-coordinates first)
           (curve-point-affine-coordinates second)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable curve-point-affine-coordinates)))))

; Two inverse steps return to the fixed starting coordinates.  This is
; unconditional: in particular, classifier priority permits a self-inverse
; ordinate to select :opposite-y, and field negation involution covers it.
(defthm affine-pair-classify-opposite-y-chain-implies-fixed-endpoints-equal
  (implies
   (and (equal (affine-pair-classify a b) :opposite-y)
        (equal (affine-pair-classify b c) :opposite-y))
   (equal (affine-coordinates-fix a)
          (affine-coordinates-fix c)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-pair-classify-opposite-y-implies-fixed-coordinates
                (first a) (second b))
     (:instance affine-pair-classify-opposite-y-implies-fixed-coordinates
                (first b) (second c))
     (:instance field-neg-of-neg
                (x (affine-coordinates-y (affine-coordinates-fix a))))
     (:instance equal-fixed-affine-coordinates-from-accessors
                (first a) (second c)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-element-p-of-affine-coordinates-y
       field-fix-when-field-element-p)))))

(defthm affine-pair-classify-repeated-doubling-implies-fixed-triple
  (implies
   (and (equal (affine-pair-classify a b) :same-point-non-opposite)
        (equal (affine-pair-classify b c) :same-point-non-opposite))
   (and (equal (affine-coordinates-fix a)
               (affine-coordinates-fix b))
        (equal (affine-coordinates-fix b)
               (affine-coordinates-fix c))
        (equal (affine-coordinates-fix a)
               (affine-coordinates-fix c))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-pair-classify-same-point-non-opposite-implies-fixed-equal
                (first a) (second b))
     (:instance affine-pair-classify-same-point-non-opposite-implies-fixed-equal
                (first b) (second c)))
    :in-theory (theory 'minimal-theory))))

; Closure makes the generic impossibility theorem applicable to an outer
; classifier.  Symmetry supplies reversed orientations without duplication.
(defthm affine-pair-classify-distinct-x-output-not-same-x-other
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second)
        (short-weierstrass-affine-point-p third)
        (equal (affine-pair-classify first second) :distinct-x))
   (not (equal (affine-pair-classify
                (affine-distinct-x-output first second) third)
               :same-x-other)))
  :rule-classes nil
  :hints (("Goal"
           :use
           (short-weierstrass-affine-point-p-of-affine-distinct-x-output
            (:instance affine-pair-classify-not-same-x-other-for-curve-points
                       (first (affine-distinct-x-output first second))
                       (second third)))
           :in-theory (theory 'minimal-theory))))

(defthm affine-pair-classify-doubling-output-not-same-x-other
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second)
        (short-weierstrass-affine-point-p third)
        (equal (affine-pair-classify first second)
               :same-point-non-opposite))
   (not (equal (affine-pair-classify
                (affine-same-point-non-opposite-output first) third)
               :same-x-other)))
  :rule-classes nil
  :hints (("Goal"
           :use
           (short-weierstrass-affine-point-p-of-affine-same-point-non-opposite-output
            (:instance affine-pair-classify-not-same-x-other-for-curve-points
                       (first (affine-same-point-non-opposite-output first))
                       (second third)))
           :in-theory (theory 'minimal-theory))))

(defthm curve-point-pair-output-point-associative-when-infinity-input
  (implies
   (and (short-weierstrass-curve-point-p a)
        (short-weierstrass-curve-point-p b)
        (short-weierstrass-curve-point-p c)
        (or (curve-point-infinity-p a)
            (curve-point-infinity-p b)
            (curve-point-infinity-p c)))
   (equal
    (curve-point-pair-output-point
     (curve-point-pair-output-point a b) c)
    (curve-point-pair-output-point
     a (curve-point-pair-output-point b c))))
  :rule-classes nil
  :hints (("Goal"
           :use
           ((:instance short-weierstrass-curve-point-p-of-curve-point-pair-output-point
                       (first a) (second b))
            (:instance short-weierstrass-curve-point-p-of-curve-point-pair-output-point
                       (first b) (second c)))
           :cases ((curve-point-infinity-p a)
                   (curve-point-infinity-p b)
                   (curve-point-infinity-p c))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(short-weierstrass-curve-point-p curve-point-representation-p
              curve-point-infinity-p
              curve-point-fix-when-representation-p
              curve-point-pair-output-point-of-infinity-left
              curve-point-pair-output-point-of-infinity-right)))))

(defthm curve-point-pair-output-point-associative-when-both-inner-opposite-y
  (implies
   (and (short-weierstrass-affine-point-p a)
        (short-weierstrass-affine-point-p b)
        (short-weierstrass-affine-point-p c)
        (equal (affine-pair-classify a b) :opposite-y)
        (equal (affine-pair-classify b c) :opposite-y))
   (equal
    (curve-point-pair-output-point
     (curve-point-pair-output-point
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates b))
     (curve-point-affine-coordinates c))
    (curve-point-pair-output-point
     (curve-point-affine-coordinates a)
     (curve-point-pair-output-point
      (curve-point-affine-coordinates b)
      (curve-point-affine-coordinates c)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use affine-pair-classify-opposite-y-chain-implies-fixed-endpoints-equal
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-pair-output-point-of-affines
       affine-pair-classify-of-fixes
       affine-pair-output-point-when-opposite-y
       affine-opposite-y-output-point-is-infinity
       curve-point-pair-output-point-of-infinity-left
       curve-point-pair-output-point-of-infinity-right
       curve-point-fix-of-affine-coordinates
       affine-coordinates-fix-idempotent)))))

(defthm curve-point-pair-output-point-associative-when-both-inner-doubling
  (implies
   (and (short-weierstrass-affine-point-p a)
        (short-weierstrass-affine-point-p b)
        (short-weierstrass-affine-point-p c)
        (equal (affine-pair-classify a b) :same-point-non-opposite)
        (equal (affine-pair-classify b c) :same-point-non-opposite))
   (equal
    (curve-point-pair-output-point
     (curve-point-pair-output-point
      (curve-point-affine-coordinates a)
      (curve-point-affine-coordinates b))
     (curve-point-affine-coordinates c))
    (curve-point-pair-output-point
     (curve-point-affine-coordinates a)
     (curve-point-pair-output-point
      (curve-point-affine-coordinates b)
      (curve-point-affine-coordinates c)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (affine-pair-classify-repeated-doubling-implies-fixed-triple
     (:instance short-weierstrass-curve-point-p-of-affine
                (coordinates a))
     (:instance short-weierstrass-affine-point-p-of-fix
                (coordinates a))
     (:instance equal-affine-fixes-imply-equal-tagged-points
                (first a) (second c))
     (:instance equal-affine-fixes-imply-equal-doubling-output-points
                (first a) (second b))
     (:instance short-weierstrass-curve-point-p-of-affine-same-point-non-opposite-output-point
                (first a) (second b))
     (:instance curve-point-pair-output-point-commutative
                (first (affine-same-point-non-opposite-output-point a))
                (second (curve-point-affine-coordinates a))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(full-affine-inner-doubling-reduction
       curve-point-fix-of-affine-coordinates
       affine-coordinates-fix-idempotent)))))
