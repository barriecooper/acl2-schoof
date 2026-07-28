(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-output-y")

; Canonical coordinate assembly for the two total same-point-non-opposite
; scalar outputs.  This is representation construction only, not a
; curve-membership or geometric doubling claim.
(defun affine-same-point-non-opposite-output (first)
  (let ((output-x (affine-same-point-non-opposite-output-x first))
        (output-y (affine-same-point-non-opposite-output-y first)))
    (affine-coordinates-make output-x output-y)))

(defthm affine-coordinates-p-of-affine-same-point-non-opposite-output
  (affine-coordinates-p (affine-same-point-non-opposite-output first))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(affine-same-point-non-opposite-output
              affine-coordinates-p
              affine-coordinates-fix
              affine-coordinates-x-of-make
              affine-coordinates-y-of-make
              field-fix-of-affine-same-point-non-opposite-output-x
              field-fix-of-affine-same-point-non-opposite-output-y)))))

(defthm affine-coordinates-x-of-affine-same-point-non-opposite-output
  (equal
   (affine-coordinates-x (affine-same-point-non-opposite-output first))
   (affine-same-point-non-opposite-output-x first))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(affine-same-point-non-opposite-output
              affine-coordinates-x-of-make
              field-fix-of-affine-same-point-non-opposite-output-x)))))

(defthm affine-coordinates-y-of-affine-same-point-non-opposite-output
  (equal
   (affine-coordinates-y (affine-same-point-non-opposite-output first))
   (affine-same-point-non-opposite-output-y first))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(affine-same-point-non-opposite-output
              affine-coordinates-y-of-make
              field-fix-of-affine-same-point-non-opposite-output-y)))))

(defthm affine-coordinates-fix-of-affine-same-point-non-opposite-output
  (equal
   (affine-coordinates-fix (affine-same-point-non-opposite-output first))
   (affine-same-point-non-opposite-output first))
  :hints
  (("Goal"
    :use (affine-coordinates-p-of-affine-same-point-non-opposite-output)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-coordinates-fix-when-affine-coordinates-p)))))

(verify-guards affine-same-point-non-opposite-output)
