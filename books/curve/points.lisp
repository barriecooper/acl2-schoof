(in-package "GFIELD")

(include-book "affine-coordinates")

; Full points are the two explicitly tagged proper lists (:infinity) and
; (:affine coordinates).  Only an exact two-list is an affine outer shape.
(defun curve-point-infinity () (list :infinity))

(defun curve-point-affine-coordinates (coordinates)
  (list :affine (affine-coordinates-fix coordinates)))

(defun curve-point-affine (x y)
  (curve-point-affine-coordinates (affine-coordinates-make x y)))

(defun curve-point-infinity-p (point)
  (equal point (curve-point-infinity)))

; Outside a well-shaped affine branch the total accessor returns the fixed
; affine fallback (0 0).  This fallback is not asserted to lie on the curve.
(defun curve-point-affine-coordinates-get (point)
  (if (and (true-listp point)
           (equal (len point) 2)
           (equal (car point) :affine))
      (affine-coordinates-fix (cadr point))
    (affine-coordinates-fix nil)))

(defun curve-point-fix (point)
  (cond ((curve-point-infinity-p point) (curve-point-infinity))
        ((and (true-listp point)
              (equal (len point) 2)
              (equal (car point) :affine)
              (true-listp (cadr point))
              (equal (len (cadr point)) 2))
         (curve-point-affine-coordinates (cadr point)))
        (t (curve-point-infinity))))

(defun curve-point-representation-p (point)
  (equal (curve-point-fix point) point))

(defun short-weierstrass-curve-point-p (point)
  (and (curve-point-representation-p point)
       (or (curve-point-infinity-p point)
           (and (equal (car point) :affine)
                (short-weierstrass-affine-point-p
                 (curve-point-affine-coordinates-get point))))))

(defthm curve-point-infinity-representation
  (and (curve-point-representation-p (curve-point-infinity))
       (curve-point-infinity-p (curve-point-infinity))))

(defthm curve-point-affine-coordinates-get-of-constructor
  (equal (curve-point-affine-coordinates-get
          (curve-point-affine-coordinates coordinates))
         (affine-coordinates-fix coordinates)))

(defthm curve-point-representation-p-of-fix
  (curve-point-representation-p (curve-point-fix point))
  :hints (("Goal" :in-theory (enable curve-point-representation-p))))

(defthm curve-point-fix-idempotent
  (equal (curve-point-fix (curve-point-fix point))
         (curve-point-fix point)))

(defthm curve-point-fix-when-representation-p
  (implies (curve-point-representation-p point)
           (equal (curve-point-fix point) point))
  :hints (("Goal" :in-theory (enable curve-point-representation-p))))

(defthm curve-point-fix-of-infinity
  (equal (curve-point-fix (curve-point-infinity))
         (curve-point-infinity)))

(defthm curve-point-fix-of-affine-coordinates
  (equal (curve-point-fix (curve-point-affine-coordinates coordinates))
         (curve-point-affine-coordinates
          (affine-coordinates-fix coordinates))))

(defthm curve-point-infinity-p-of-fix
  (equal (curve-point-infinity-p (curve-point-fix point))
         (not (and (true-listp point)
                   (equal (len point) 2)
                   (equal (car point) :affine)
                   (true-listp (cadr point))
                   (equal (len (cadr point)) 2)))))

(defthm short-weierstrass-curve-point-p-of-fix
  (implies (curve-point-representation-p point)
           (equal (short-weierstrass-curve-point-p (curve-point-fix point))
                  (short-weierstrass-curve-point-p point)))
  :rule-classes nil)

(defthm short-weierstrass-curve-point-p-of-infinity
  (short-weierstrass-curve-point-p (curve-point-infinity))
  :rule-classes nil)

(defthm short-weierstrass-curve-point-p-of-affine
  (equal (short-weierstrass-curve-point-p
          (curve-point-affine-coordinates coordinates))
         (short-weierstrass-affine-point-p
          (affine-coordinates-fix coordinates)))
  :rule-classes nil)

(defthm short-weierstrass-curve-point-non-infinity-representation
  (implies
   (and
    (short-weierstrass-curve-point-p point)
    (not (equal (curve-point-fix point)
                (curve-point-infinity))))
   (and
    (short-weierstrass-affine-point-p
     (curve-point-affine-coordinates-get
      (curve-point-fix point)))
    (equal
     (curve-point-fix point)
     (curve-point-affine-coordinates
      (curve-point-affine-coordinates-get
       (curve-point-fix point))))))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (enable short-weierstrass-curve-point-p
            curve-point-representation-p
            curve-point-infinity-p
            curve-point-fix
            curve-point-affine-coordinates-get))))

(verify-guards curve-point-infinity)
(verify-guards curve-point-affine-coordinates)
(verify-guards curve-point-affine)
(verify-guards curve-point-infinity-p)
(verify-guards curve-point-affine-coordinates-get)
(verify-guards curve-point-fix)
(verify-guards curve-point-representation-p)
(verify-guards short-weierstrass-curve-point-p)
