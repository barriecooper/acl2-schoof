(in-package "GFIELD")

(include-book "affine-pair-output-point")

; Fix both full points once.  Infinity branches return the retained canonical
; operand; only the affine/affine branch delegates to affine-pair dispatch.
(defun curve-point-pair-output-point (first second)
  (let* ((first (curve-point-fix first))
         (second (curve-point-fix second)))
    (cond ((curve-point-infinity-p first) second)
          ((curve-point-infinity-p second) first)
          (t (affine-pair-output-point
              (curve-point-affine-coordinates-get first)
              (curve-point-affine-coordinates-get second))))))

(defthm curve-point-pair-output-point-of-infinities
  (equal (curve-point-pair-output-point (curve-point-infinity)
                                        (curve-point-infinity))
         (curve-point-infinity)))

(defthm curve-point-pair-output-point-of-infinity-left
  (equal (curve-point-pair-output-point (curve-point-infinity) point)
         (curve-point-fix point)))

(defthm curve-point-pair-output-point-of-infinity-right
  (equal (curve-point-pair-output-point point (curve-point-infinity))
         (curve-point-fix point)))

(defthm curve-point-infinity-p-of-affine-coordinates
  (not (curve-point-infinity-p
        (curve-point-affine-coordinates coordinates))))

(defthm curve-point-pair-output-point-of-affines
  (equal
   (curve-point-pair-output-point
    (curve-point-affine-coordinates first)
   (curve-point-affine-coordinates second))
   (affine-pair-output-point (affine-coordinates-fix first)
                             (affine-coordinates-fix second)))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-pair-output-point
       curve-point-infinity-p-of-affine-coordinates
       curve-point-fix-of-affine-coordinates
       curve-point-infinity-p-of-fix
       curve-point-affine-coordinates-get-of-constructor
       affine-coordinates-fix-idempotent)))))

(defthm curve-point-pair-output-point-of-fixes
  (equal (curve-point-pair-output-point (curve-point-fix first)
                                        (curve-point-fix second))
         (curve-point-pair-output-point first second)))

(defthm curve-point-representation-p-of-curve-point-pair-output-point
  (curve-point-representation-p
   (curve-point-pair-output-point first second))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-pair-output-point
       curve-point-representation-p-of-fix
       curve-point-representation-p-of-affine-pair-output-point)))))

(defthm short-weierstrass-curve-point-p-of-curve-point-pair-output-point
  (implies
   (and (short-weierstrass-curve-point-p first)
        (short-weierstrass-curve-point-p second))
   (short-weierstrass-curve-point-p
    (curve-point-pair-output-point first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance short-weierstrass-curve-point-p-of-affine-pair-output-point
                (first (curve-point-affine-coordinates-get first))
                (second (curve-point-affine-coordinates-get second))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-pair-output-point
       short-weierstrass-curve-point-p
       curve-point-representation-p
       curve-point-fix-when-representation-p
       short-weierstrass-affine-point-p)))))

(verify-guards curve-point-pair-output-point)
