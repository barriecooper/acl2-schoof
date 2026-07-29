(in-package "GFIELD")

(include-book "affine-distinct-x-output-point")
(include-book "affine-opposite-y-output-point")
(include-book "affine-same-point-non-opposite-output-point")
(include-book "affine-pair-curve-classification")

; Dispatch the four total structural classifier results.  Infinity in the
; final branch is only a programming fallback: :same-x-other is impossible
; under the two-curve-input contract proved below.
(defun affine-pair-output-point (first second)
  (let ((classification (affine-pair-classify first second)))
    (cond ((equal classification :distinct-x)
           (affine-distinct-x-output-point first second))
          ((equal classification :opposite-y)
           (affine-opposite-y-output-point first second))
          ((equal classification :same-point-non-opposite)
           (affine-same-point-non-opposite-output-point first))
          (t (curve-point-infinity)))))

(defthm affine-pair-output-point-when-distinct-x
  (implies (equal (affine-pair-classify first second) :distinct-x)
           (equal (affine-pair-output-point first second)
                  (affine-distinct-x-output-point first second)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(affine-pair-output-point)))))

(defthm affine-pair-output-point-when-opposite-y
  (implies (equal (affine-pair-classify first second) :opposite-y)
           (equal (affine-pair-output-point first second)
                  (affine-opposite-y-output-point first second)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(affine-pair-output-point)))))

(defthm affine-pair-output-point-when-same-point-non-opposite
  (implies
   (equal (affine-pair-classify first second) :same-point-non-opposite)
   (equal (affine-pair-output-point first second)
          (affine-same-point-non-opposite-output-point first)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(affine-pair-output-point)))))

(defthm affine-pair-output-point-when-same-x-other
  (implies (equal (affine-pair-classify first second) :same-x-other)
           (equal (affine-pair-output-point first second)
                  (curve-point-infinity)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(affine-pair-output-point)))))

(defthm curve-point-representation-p-of-affine-pair-output-point
  (curve-point-representation-p (affine-pair-output-point first second))
  :hints
  (("Goal"
    :use (affine-pair-classify-exhaustive)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-pair-output-point-when-distinct-x
       affine-pair-output-point-when-opposite-y
       affine-pair-output-point-when-same-point-non-opposite
       affine-pair-output-point-when-same-x-other
       curve-point-representation-p-of-affine-distinct-x-output-point
       curve-point-representation-p-of-affine-opposite-y-output-point
       curve-point-representation-p-of-affine-same-point-non-opposite-output-point
       curve-point-infinity-representation)))))

(defthm short-weierstrass-curve-point-p-of-affine-pair-output-point
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second))
   (short-weierstrass-curve-point-p
    (affine-pair-output-point first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (affine-pair-classify-exhaustive
     affine-pair-classify-not-same-x-other-for-curve-points
     short-weierstrass-curve-point-p-of-affine-distinct-x-output-point
     short-weierstrass-curve-point-p-of-affine-opposite-y-output-point
     short-weierstrass-curve-point-p-of-affine-same-point-non-opposite-output-point)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-pair-output-point-when-distinct-x
       affine-pair-output-point-when-opposite-y
       affine-pair-output-point-when-same-point-non-opposite)))))

(verify-guards affine-pair-output-point)
