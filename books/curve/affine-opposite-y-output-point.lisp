(in-package "GFIELD")

(include-book "affine-pair-classification")
(include-book "points")

; The opposite-y classifier branch has the canonical point at infinity as its
; result.  Keep both inputs in this transparent, total interface because the
; future classifier dispatcher selects this relational branch from a pair.
(defun affine-opposite-y-output-point (first second)
  (declare (ignore first second))
  (curve-point-infinity))

(defthm affine-opposite-y-output-point-is-infinity
  (equal (affine-opposite-y-output-point first second)
         (curve-point-infinity)))

(defthm curve-point-representation-p-of-affine-opposite-y-output-point
  (curve-point-representation-p
   (affine-opposite-y-output-point first second)))

(defthm curve-point-infinity-p-of-affine-opposite-y-output-point
  (curve-point-infinity-p
   (affine-opposite-y-output-point first second)))

(defthm short-weierstrass-curve-point-p-of-affine-opposite-y-output-point
  (short-weierstrass-curve-point-p
   (affine-opposite-y-output-point first second))
  :rule-classes nil
  :hints
  (("Goal"
    :use short-weierstrass-curve-point-p-of-infinity
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-opposite-y-output-point)))))

(verify-guards affine-opposite-y-output-point)
