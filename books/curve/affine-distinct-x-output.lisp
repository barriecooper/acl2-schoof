(in-package "GFIELD")

(include-book "affine-distinct-x-output-y")

; Canonical coordinate assembly for the two total distinct-x scalar outputs.
; This is representation construction only, not a curve-membership claim.
(defun affine-distinct-x-output (first second)
  (let ((output-x (affine-distinct-x-output-x first second))
        (output-y (affine-distinct-x-output-y first second)))
    (affine-coordinates-make output-x output-y)))

(defthm affine-coordinates-p-of-affine-distinct-x-output
  (affine-coordinates-p (affine-distinct-x-output first second))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(affine-distinct-x-output
              affine-coordinates-p
              affine-coordinates-fix
              affine-coordinates-x-of-make
              affine-coordinates-y-of-make
              field-fix-of-affine-distinct-x-output-x
              field-fix-of-affine-distinct-x-output-y)))))

(defthm affine-coordinates-x-of-affine-distinct-x-output
  (equal (affine-coordinates-x (affine-distinct-x-output first second))
         (affine-distinct-x-output-x first second))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(affine-distinct-x-output
              affine-coordinates-x-of-make
              field-fix-of-affine-distinct-x-output-x)))))

(defthm affine-coordinates-y-of-affine-distinct-x-output
  (equal (affine-coordinates-y (affine-distinct-x-output first second))
         (affine-distinct-x-output-y first second))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(affine-distinct-x-output
              affine-coordinates-y-of-make
              field-fix-of-affine-distinct-x-output-y)))))

(defthm affine-coordinates-fix-of-affine-distinct-x-output
  (equal (affine-coordinates-fix
          (affine-distinct-x-output first second))
         (affine-distinct-x-output first second))
  :hints (("Goal"
           :use (affine-coordinates-p-of-affine-distinct-x-output)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(affine-coordinates-fix-when-affine-coordinates-p)))))

(verify-guards affine-distinct-x-output)
