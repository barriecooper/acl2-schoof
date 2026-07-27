(in-package "GFIELD")

(include-book "affine-distinct-x-output-x")

; Total y-coordinate formula intended for the distinct-x affine secant branch.
; The branch name does not impose a classifier test or a nonzero guard.
(defun affine-distinct-x-output-y (first second)
  (let ((slope (affine-distinct-x-slope first second))
        (output-x (affine-distinct-x-output-x first second)))
    (field-sub
     (field-mul
      slope
      (field-sub (affine-coordinates-x first) output-x))
     (affine-coordinates-y first))))

(defthm field-element-p-of-affine-distinct-x-output-y
  (field-element-p (affine-distinct-x-output-y first second))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-output-y
       field-element-p-of-affine-distinct-x-slope
       field-element-p-of-affine-distinct-x-output-x
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-element-p-of-mul
       field-element-p-of-add
       field-element-p-of-neg
       field-sub)))))

(defthm field-fix-of-affine-distinct-x-output-y
  (equal (field-fix (affine-distinct-x-output-y first second))
         (affine-distinct-x-output-y first second))
  :hints
  (("Goal"
    :use (field-element-p-of-affine-distinct-x-output-y)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(field-fix-when-field-element-p)))))

(defthm affine-distinct-x-output-y-rearrangement
  (equal
   (field-add
    (affine-distinct-x-output-y first second)
    (affine-coordinates-y first))
   (field-mul
    (affine-distinct-x-slope first second)
    (field-sub
     (affine-coordinates-x first)
     (affine-distinct-x-output-x first second))))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-output-y
       field-sub
       field-add-associative
       field-add-inverse-left
       field-add-zero-right
       field-fix-of-mul)))))

(verify-guards affine-distinct-x-output-y)
