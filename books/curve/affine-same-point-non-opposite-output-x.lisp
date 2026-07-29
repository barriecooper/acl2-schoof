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

(defthm affine-same-point-non-opposite-output-x-rearrangement
  (equal
   (field-add
    (affine-same-point-non-opposite-output-x first)
    (field-mul
     (field-add (field-one) (field-one))
     (affine-coordinates-x first)))
   (field-mul
    (affine-same-point-non-opposite-slope first)
    (affine-same-point-non-opposite-slope first)))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-same-point-non-opposite-output-x
       field-sub
       field-add-associative
       field-add-commutative
       field-add-inverse-middle
       field-fix-of-add
       field-fix-of-mul)))))

(verify-guards affine-same-point-non-opposite-output-x)
