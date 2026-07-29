(in-package "GFIELD")

(include-book "affine-same-point-non-opposite-closure")
(include-book "points")

; Tag the canonical same-point-non-opposite affine output with the established
; full-point constructor.  The operation remains unary and total; its later
; binary classifier consumer appears only in the semantic theorem below.
(defun affine-same-point-non-opposite-output-point (first)
  (curve-point-affine-coordinates
   (affine-same-point-non-opposite-output first)))

(defthm curve-point-representation-p-of-affine-same-point-non-opposite-output-point
  (curve-point-representation-p
   (affine-same-point-non-opposite-output-point first))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-same-point-non-opposite-output-point
       curve-point-representation-p
       curve-point-fix-of-affine-coordinates
       affine-coordinates-fix-of-affine-same-point-non-opposite-output)))))

(defthm curve-point-affine-coordinates-get-of-affine-same-point-non-opposite-output-point
  (equal
   (curve-point-affine-coordinates-get
    (affine-same-point-non-opposite-output-point first))
   (affine-same-point-non-opposite-output first))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-same-point-non-opposite-output-point
       curve-point-affine-coordinates-get-of-constructor
       affine-coordinates-fix-of-affine-same-point-non-opposite-output)))))

(defthm short-weierstrass-curve-point-p-of-affine-same-point-non-opposite-output-point
  (implies
   (and (short-weierstrass-affine-point-p first)
        (equal (affine-pair-classify first second)
               :same-point-non-opposite))
   (short-weierstrass-curve-point-p
    (affine-same-point-non-opposite-output-point first)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (short-weierstrass-affine-point-p-of-affine-same-point-non-opposite-output
     (:instance short-weierstrass-curve-point-p-of-affine
                (coordinates
                 (affine-same-point-non-opposite-output first))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-same-point-non-opposite-output-point
       affine-coordinates-fix-of-affine-same-point-non-opposite-output)))))

(verify-guards affine-same-point-non-opposite-output-point)
