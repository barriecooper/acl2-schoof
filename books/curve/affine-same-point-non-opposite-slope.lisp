(in-package "GFIELD")

(include-book "affine-pair-classification")

; This is the total tangent quotient formula selected mathematically by
; :SAME-POINT-NON-OPPOSITE.  Its unary arity reflects that the formula uses
; only one point; classification of a pair belongs to the theorem below.
(defun affine-same-point-non-opposite-slope (first)
  (field-div
   (field-add
    (field-mul
     (field-add (field-add (field-one) (field-one))
                (field-one))
     (field-mul (affine-coordinates-x first)
                (affine-coordinates-x first)))
    (field-fix (short-weierstrass-a)))
   (field-add (affine-coordinates-y first)
              (affine-coordinates-y first))))

(defthm field-element-p-of-affine-same-point-non-opposite-slope
  (field-element-p (affine-same-point-non-opposite-slope first)))

(defthm field-fix-of-affine-same-point-non-opposite-slope
  (equal (field-fix (affine-same-point-non-opposite-slope first))
         (affine-same-point-non-opposite-slope first)))

(defthm affine-same-point-non-opposite-slope-reconstructs-tangent-numerator
  (implies
   (equal (affine-pair-classify first second)
          :same-point-non-opposite)
   (equal
    (field-mul
     (affine-same-point-non-opposite-slope first)
     (field-add (affine-coordinates-y first)
                (affine-coordinates-y first)))
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one))
                 (field-one))
      (field-mul (affine-coordinates-x first)
                 (affine-coordinates-x first)))
     (field-fix (short-weierstrass-a)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (affine-pair-classify-same-point-non-opposite-implies-tangent-denominator-nonzero
     (:instance
      field-div-mul-denominator
      (numerator
       (field-add
        (field-mul
         (field-add (field-add (field-one) (field-one))
                    (field-one))
         (field-mul (affine-coordinates-x first)
                    (affine-coordinates-x first)))
        (field-fix (short-weierstrass-a))))
      (denominator
       (field-add (affine-coordinates-y first)
                  (affine-coordinates-y first)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-same-point-non-opposite-slope
       field-element-p-of-add
       field-fix-when-field-element-p)))))

(verify-guards affine-same-point-non-opposite-slope)
