(in-package "GFIELD")

(include-book "affine-pair-classification")

; This is the total quotient formula selected mathematically by :DISTINCT-X.
; The definition deliberately contains no classifier test or nonzero guard.
(defun affine-distinct-x-slope (first second)
  (field-div
   (field-sub (affine-coordinates-y second)
              (affine-coordinates-y first))
   (field-sub (affine-coordinates-x second)
              (affine-coordinates-x first))))

(defthm field-element-p-of-affine-distinct-x-slope
  (field-element-p (affine-distinct-x-slope first second)))

(defthm field-fix-of-affine-distinct-x-slope
  (equal (field-fix (affine-distinct-x-slope first second))
         (affine-distinct-x-slope first second)))

(defthm affine-distinct-x-slope-reconstructs-y-difference
  (implies
   (equal (affine-pair-classify first second) :distinct-x)
   (equal
    (field-mul
     (affine-distinct-x-slope first second)
     (field-sub (affine-coordinates-x second)
                (affine-coordinates-x first)))
    (field-sub (affine-coordinates-y second)
               (affine-coordinates-y first))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (affine-pair-classify-distinct-x-implies-x-difference-nonzero
     (:instance
      field-div-mul-denominator
      (numerator (field-sub (affine-coordinates-y second)
                            (affine-coordinates-y first)))
      (denominator (field-sub (affine-coordinates-x second)
                              (affine-coordinates-x first)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-slope
       field-sub
       field-element-p-of-add
       field-element-p-of-neg
       field-fix-of-add
       field-fix-when-field-element-p)))))

(verify-guards affine-distinct-x-slope)
