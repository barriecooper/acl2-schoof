(in-package "GFIELD")

(include-book "affine-distinct-x-slope")

; Total x-coordinate formula intended for the distinct-x affine secant branch.
; The branch name does not impose a classifier test or a nonzero guard.
(defun affine-distinct-x-output-x (first second)
  (let ((slope (affine-distinct-x-slope first second)))
    (field-sub
     (field-sub (field-mul slope slope)
                (affine-coordinates-x first))
     (affine-coordinates-x second))))

(defthm field-element-p-of-affine-distinct-x-output-x
  (field-element-p (affine-distinct-x-output-x first second))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-output-x
       field-element-p-of-affine-distinct-x-slope
       field-element-p-of-affine-coordinates-x
       field-element-p-of-mul
       field-element-p-of-add
       field-element-p-of-neg
       field-sub)))))

(defthm field-fix-of-affine-distinct-x-output-x
  (equal (field-fix (affine-distinct-x-output-x first second))
         (affine-distinct-x-output-x first second))
  :hints
  (("Goal"
    :use (field-element-p-of-affine-distinct-x-output-x)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-fix-when-field-element-p)))))

(verify-guards affine-distinct-x-output-x)
