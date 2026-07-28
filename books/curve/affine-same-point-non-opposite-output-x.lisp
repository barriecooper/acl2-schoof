(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-slope")

; Total x-coordinate formula intended for the equal, non-opposite affine
; tangent branch.  The branch name imposes no classifier test or nonzero guard.
(defun affine-same-point-non-opposite-output-x (first)
  (let ((slope (affine-same-point-non-opposite-slope first)))
    (field-sub
     (field-mul slope slope)
     (field-mul
      (field-add (field-one) (field-one))
      (affine-coordinates-x first)))))

(defthm field-element-p-of-affine-same-point-non-opposite-output-x
  (field-element-p (affine-same-point-non-opposite-output-x first))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-same-point-non-opposite-output-x
       field-element-p-of-affine-same-point-non-opposite-slope
       field-element-p-of-affine-coordinates-x
       field-element-p-of-one
       field-element-p-of-add
       field-element-p-of-mul
       field-element-p-of-neg
       field-sub)))))

(defthm field-fix-of-affine-same-point-non-opposite-output-x
  (equal (field-fix (affine-same-point-non-opposite-output-x first))
         (affine-same-point-non-opposite-output-x first))
  :hints
  (("Goal"
    :use (field-element-p-of-affine-same-point-non-opposite-output-x)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-fix-when-field-element-p)))))

(verify-guards affine-same-point-non-opposite-output-x)
