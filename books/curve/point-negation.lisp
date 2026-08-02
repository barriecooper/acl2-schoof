(in-package "GFIELD")

(include-book "points")

; Negation is a total operation at the full-point fixing boundary.  Keeping the
; coordinate transformation here avoids adding a public affine-operation layer.
(defun curve-point-neg (point)
  (let ((point (curve-point-fix point)))
    (if (curve-point-infinity-p point)
        (curve-point-infinity)
      (curve-point-affine
       (affine-coordinates-x
        (curve-point-affine-coordinates-get point))
       (field-neg
        (affine-coordinates-y
         (curve-point-affine-coordinates-get point)))))))

(defthm curve-point-representation-p-of-neg
  (curve-point-representation-p (curve-point-neg point)))

(defthm curve-point-fix-of-neg
  (equal (curve-point-fix (curve-point-neg point))
         (curve-point-neg point))
  :hints (("Goal"
           :use ((:instance curve-point-fix-when-representation-p
                            (point (curve-point-neg point))))
           :in-theory (disable curve-point-fix-when-representation-p))))

(defthm curve-point-neg-of-infinity
  (equal (curve-point-neg (curve-point-infinity))
         (curve-point-infinity)))

(defthm curve-point-affine-coordinates-get-of-neg-affine
  (equal (curve-point-affine-coordinates-get
          (curve-point-neg (curve-point-affine x y)))
         (affine-coordinates-make x (field-neg y))))

(defthm curve-point-neg-of-affine
  (equal (curve-point-neg (curve-point-affine x y))
         (curve-point-affine x (field-neg y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable curve-point-neg))))

(defthm affine-coordinates-x-of-curve-point-neg-affine
  (equal (affine-coordinates-x
          (curve-point-affine-coordinates-get
           (curve-point-neg (curve-point-affine x y))))
         (field-fix x)))

(defthm affine-coordinates-y-of-curve-point-neg-affine
  (equal (affine-coordinates-y
          (curve-point-affine-coordinates-get
           (curve-point-neg (curve-point-affine x y))))
         (field-neg (field-fix y))))

(defthm curve-point-neg-of-fix
  (equal (curve-point-neg (curve-point-fix point))
         (curve-point-neg point)))

(defcong equal equal (curve-point-neg point) 1)

(defthm curve-point-neg-of-neg
  (equal (curve-point-neg (curve-point-neg point))
         (curve-point-fix point)))

(defthm curve-point-neg-involution-when-representation-p
  (implies (curve-point-representation-p point)
           (equal (curve-point-neg (curve-point-neg point)) point)))

; This field-algebra bridge is deliberately local: curve closure needs only
; the square identity, not globally enabled multiplication/negation rules.
(local
 (defthm field-mul-right-neg-local
   (equal (field-mul y (field-neg y))
          (field-neg (field-mul y y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-mul y y))
                      (y (field-mul y (field-neg y))))
           (:instance field-mul-left-distributive
                      (x y) (y y) (z (field-neg y))))))))

(local
 (defthm field-mul-of-negated-arguments
   (equal (field-mul (field-neg y) (field-neg y))
          (field-mul y y))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-mul y (field-neg y)))
                      (y (field-mul (field-neg y) (field-neg y))))
           (:instance field-mul-right-distributive
                      (x y) (y (field-neg y)) (z (field-neg y))))))))

(local
 (defthm short-weierstrass-equation-p-of-neg-y
   (implies (short-weierstrass-equation-p x y)
            (short-weierstrass-equation-p x (field-neg y)))
   :rule-classes nil
   :hints (("Goal"
            :use field-mul-of-negated-arguments
            :in-theory (enable short-weierstrass-equation-p)))))

(defthm short-weierstrass-curve-point-p-of-neg
  (implies (short-weierstrass-curve-point-p point)
           (short-weierstrass-curve-point-p (curve-point-neg point)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance short-weierstrass-equation-p-of-neg-y
                            (x (affine-coordinates-x
                                (curve-point-affine-coordinates-get point)))
                            (y (affine-coordinates-y
                                (curve-point-affine-coordinates-get point)))))
           :in-theory (enable curve-point-neg
                              short-weierstrass-curve-point-p
                              short-weierstrass-affine-point-p))))

(verify-guards curve-point-neg)
