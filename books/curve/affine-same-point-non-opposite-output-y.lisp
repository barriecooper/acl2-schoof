(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-output-x")

; Total y-coordinate formula intended for the equal, non-opposite affine
; tangent branch.  The branch name imposes no classifier test or nonzero guard.
(defun affine-same-point-non-opposite-output-y (first)
  (let ((slope (affine-same-point-non-opposite-slope first))
        (output-x (affine-same-point-non-opposite-output-x first)))
    (field-sub
     (field-mul
      slope
      (field-sub (affine-coordinates-x first) output-x))
     (affine-coordinates-y first))))

(defthm field-element-p-of-affine-same-point-non-opposite-output-y
  (field-element-p (affine-same-point-non-opposite-output-y first))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-same-point-non-opposite-output-y
       field-element-p-of-affine-same-point-non-opposite-slope
       field-element-p-of-affine-same-point-non-opposite-output-x
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-element-p-of-mul
       field-element-p-of-add
       field-element-p-of-neg
       field-sub)))))

(defthm field-fix-of-affine-same-point-non-opposite-output-y
  (equal (field-fix (affine-same-point-non-opposite-output-y first))
         (affine-same-point-non-opposite-output-y first))
  :hints
  (("Goal"
    :use (field-element-p-of-affine-same-point-non-opposite-output-y)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-fix-when-field-element-p)))))

(defthm affine-same-point-non-opposite-output-y-rearrangement
  (equal
   (field-add
    (affine-same-point-non-opposite-output-y first)
    (affine-coordinates-y first))
   (field-mul
    (affine-same-point-non-opposite-slope first)
    (field-sub
     (affine-coordinates-x first)
     (affine-same-point-non-opposite-output-x first))))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-same-point-non-opposite-output-y
       field-sub
       field-add-associative
       field-add-inverse-left
       field-add-zero-right
       field-fix-of-mul)))))

(verify-guards affine-same-point-non-opposite-output-y)
