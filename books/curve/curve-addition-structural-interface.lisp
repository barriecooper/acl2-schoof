(in-package "GFIELD")

(include-book "curve-point-pair-output-point")
(include-book "affine-distinct-x-closure")
(include-book "affine-same-point-non-opposite-closure")

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
