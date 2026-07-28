(in-package "GFIELD")

(include-book "affine-coordinates")

(defun affine-pair-classification-result-p (result)
  (or (equal result :distinct-x)
      (equal result :opposite-y)
      (equal result :same-point-non-opposite)
      (equal result :same-x-other)))

(defun affine-pair-classify (first second)
  (let* ((first (affine-coordinates-fix first))
         (second (affine-coordinates-fix second))
         (x1 (affine-coordinates-x first))
         (y1 (affine-coordinates-y first))
         (x2 (affine-coordinates-x second))
         (y2 (affine-coordinates-y second)))
    (cond ((not (equal x1 x2)) :distinct-x)
          ((equal y2 (field-neg y1)) :opposite-y)
          ((equal y1 y2) :same-point-non-opposite)
          (t :same-x-other))))

(defthm affine-pair-classification-result-p-of-classify
  (affine-pair-classification-result-p
   (affine-pair-classify first second))
  :hints (("Goal" :in-theory (enable affine-pair-classify
                                      affine-pair-classification-result-p))))

(defthm affine-pair-classify-of-fixes
  (equal (affine-pair-classify (affine-coordinates-fix first)
                               (affine-coordinates-fix second))
         (affine-pair-classify first second)))

(defthm affine-pair-classify-distinct-x-characterization
  (equal (equal (affine-pair-classify first second) :distinct-x)
         (not (equal (affine-coordinates-x (affine-coordinates-fix first))
                     (affine-coordinates-x (affine-coordinates-fix second)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (affine-pair-classify)
                              (affine-coordinates-x-of-fix
                               affine-coordinates-y-of-fix)))))

; The orientation anticipates the conventional ordered secant quotient:
; (y_second - y_first) / (x_second - x_first).  This theorem establishes only
; its additive denominator precondition; it introduces no division or slope.
(defthm affine-pair-classify-distinct-x-implies-x-difference-nonzero
  (implies
   (equal (affine-pair-classify first second) :distinct-x)
   (not (equal (field-sub (affine-coordinates-x second)
                          (affine-coordinates-x first))
               (field-zero))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (affine-pair-classify-distinct-x-characterization
          (:instance field-sub-equal-zero-implies-fixed-equal
                     (first (affine-coordinates-x second))
                     (second (affine-coordinates-x first))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-element-p-of-affine-coordinates-x
       field-fix-when-field-element-p
       affine-coordinates-x-of-fix)))))

(defthm affine-pair-classify-opposite-y-characterization
  (equal (equal (affine-pair-classify first second) :opposite-y)
         (and (equal (affine-coordinates-x (affine-coordinates-fix first))
                     (affine-coordinates-x (affine-coordinates-fix second)))
              (equal (affine-coordinates-y (affine-coordinates-fix second))
                     (field-neg (affine-coordinates-y (affine-coordinates-fix first))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (affine-pair-classify)
                              (affine-coordinates-x-of-fix
                               affine-coordinates-y-of-fix)))))

(local
 (defthm field-neg-equal-zero-when-fix-equal-zero
   (implies (equal (field-fix x) (field-zero))
            (equal (field-neg x) (field-zero)))
   :hints (("Goal"
            :use ((:instance field-neg-of-fix (x x))
                  field-neg-of-zero)
            :in-theory (disable field-neg-of-fix field-neg-of-zero)))))

(defthm affine-pair-classify-same-point-non-opposite-characterization
  (equal (equal (affine-pair-classify first second)
                :same-point-non-opposite)
         (and (equal (affine-coordinates-x (affine-coordinates-fix first))
                     (affine-coordinates-x (affine-coordinates-fix second)))
              (equal (affine-coordinates-y (affine-coordinates-fix first))
                     (affine-coordinates-y (affine-coordinates-fix second)))
              (not (equal (affine-coordinates-y (affine-coordinates-fix second))
                          (field-neg (affine-coordinates-y (affine-coordinates-fix first)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (affine-pair-classify)
                              (affine-coordinates-x-of-fix
                               affine-coordinates-y-of-fix)))))

; This is the exact denominator anticipated by the conventional tangent
; quotient.  Classification supplies the non-self-inverse y fact; additive
; inverse uniqueness turns a zero doubled y back into the excluded equality.
(defthm affine-pair-classify-same-point-non-opposite-implies-tangent-denominator-nonzero
  (implies
   (equal (affine-pair-classify first second)
          :same-point-non-opposite)
   (not (equal (field-add (affine-coordinates-y first)
                          (affine-coordinates-y first))
               (field-zero))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (affine-pair-classify-same-point-non-opposite-characterization
     (:instance field-additive-inverse-unique
                (x (affine-coordinates-y first))
                (y (affine-coordinates-y first))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-element-p-of-affine-coordinates-y
       field-fix-when-field-element-p
       affine-coordinates-y-of-fix)))))

(defthm affine-pair-classify-same-x-other-characterization
  (equal (equal (affine-pair-classify first second) :same-x-other)
         (and (equal (affine-coordinates-x (affine-coordinates-fix first))
                     (affine-coordinates-x (affine-coordinates-fix second)))
              (not (equal (affine-coordinates-y (affine-coordinates-fix first))
                          (affine-coordinates-y (affine-coordinates-fix second))))
              (not (equal (affine-coordinates-y (affine-coordinates-fix second))
                          (field-neg (affine-coordinates-y (affine-coordinates-fix first)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (affine-pair-classify)
                              (affine-coordinates-x-of-fix
                               affine-coordinates-y-of-fix)))))

(defthm affine-pair-classify-exhaustive
  (or (equal (affine-pair-classify first second) :distinct-x)
      (equal (affine-pair-classify first second) :opposite-y)
      (equal (affine-pair-classify first second) :same-point-non-opposite)
      (equal (affine-pair-classify first second) :same-x-other))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable affine-pair-classify))))

(defthm affine-pair-classify-pairwise-disjoint
  (implies (and (affine-pair-classification-result-p left)
                (affine-pair-classification-result-p right)
                (equal (affine-pair-classify first second) left)
                (equal (affine-pair-classify first second) right))
           (equal left right))
  :rule-classes nil)

(verify-guards affine-pair-classification-result-p)
(verify-guards affine-pair-classify)
