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

(local
 (defthm field-add-inverse-middle
   (equal (field-add x (field-add (field-neg x) y))
          (field-fix y))
   :hints
   (("Goal"
     :use ((:instance field-add-associative
                      (x x) (y (field-neg x)) (z y)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-inverse-right
        field-add-zero-left
        field-fix-idempotent))))))

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

(defthm affine-distinct-x-output-x-rearrangement
  (equal
   (field-add
    (field-add
     (affine-distinct-x-output-x first second)
     (affine-coordinates-x first))
    (affine-coordinates-x second))
   (field-mul
    (affine-distinct-x-slope first second)
    (affine-distinct-x-slope first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-output-x
       field-sub
       field-add-associative
       field-add-commutative
       field-add-inverse-middle
       field-fix-of-add
       field-fix-of-mul)))))

(verify-guards affine-distinct-x-output-x)
