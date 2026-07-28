(in-package "GFIELD")

(include-book "affine-distinct-x-closure")
(include-book "points")

; Tag the canonical distinct-x affine output with the established full-point
; constructor.  This remains total outside the semantic distinct-x case.
(defun affine-distinct-x-output-point (first second)
  (curve-point-affine-coordinates
   (affine-distinct-x-output first second)))

(defthm curve-point-representation-p-of-affine-distinct-x-output-point
  (curve-point-representation-p
   (affine-distinct-x-output-point first second))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-output-point
       curve-point-representation-p
       curve-point-fix-of-affine-coordinates
       affine-coordinates-fix-of-affine-distinct-x-output)))))

(defthm curve-point-affine-coordinates-get-of-affine-distinct-x-output-point
  (equal
   (curve-point-affine-coordinates-get
    (affine-distinct-x-output-point first second))
   (affine-distinct-x-output first second))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-output-point
       curve-point-affine-coordinates-get-of-constructor
       affine-coordinates-fix-of-affine-distinct-x-output)))))

(defthm short-weierstrass-curve-point-p-of-affine-distinct-x-output-point
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second)
        (equal (affine-pair-classify first second) :distinct-x))
   (short-weierstrass-curve-point-p
    (affine-distinct-x-output-point first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (short-weierstrass-affine-point-p-of-affine-distinct-x-output
     (:instance short-weierstrass-curve-point-p-of-affine
                (coordinates (affine-distinct-x-output first second))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-output-point
       affine-coordinates-fix-of-affine-distinct-x-output)))))

(verify-guards affine-distinct-x-output-point)
