(in-package "GFIELD")

(include-book "short-weierstrass")

; A finite affine coordinate is represented canonically by the proper two-item
; list (x y), with both entries fixed by FIELD-FIX.  Every other outer shape
; (including atoms, lists of another length, and dotted pairs) denotes (0 0).
(defun affine-coordinates-make (x y)
  (list (field-fix x) (field-fix y)))

(defun affine-coordinates-x (coordinates)
  (if (and (true-listp coordinates) (equal (len coordinates) 2))
      (field-fix (car coordinates))
    (field-zero)))

(defun affine-coordinates-y (coordinates)
  (if (and (true-listp coordinates) (equal (len coordinates) 2))
      (field-fix (cadr coordinates))
    (field-zero)))

(defun affine-coordinates-fix (coordinates)
  (affine-coordinates-make (affine-coordinates-x coordinates)
                           (affine-coordinates-y coordinates)))

(defun affine-coordinates-p (coordinates)
  (equal (affine-coordinates-fix coordinates) coordinates))

(defun short-weierstrass-affine-point-p (coordinates)
  (short-weierstrass-equation-p
   (affine-coordinates-x coordinates)
   (affine-coordinates-y coordinates)))

(defthm affine-coordinates-x-of-make
  (equal (affine-coordinates-x (affine-coordinates-make x y))
         (field-fix x)))

(defthm affine-coordinates-y-of-make
  (equal (affine-coordinates-y (affine-coordinates-make x y))
         (field-fix y)))

(defthm affine-coordinates-p-of-fix
  (affine-coordinates-p (affine-coordinates-fix coordinates))
  :hints (("Goal" :in-theory (enable affine-coordinates-p))))

(defthm affine-coordinates-fix-idempotent
  (equal (affine-coordinates-fix (affine-coordinates-fix coordinates))
         (affine-coordinates-fix coordinates)))

(defthm affine-coordinates-fix-when-affine-coordinates-p
  (implies (affine-coordinates-p coordinates)
           (equal (affine-coordinates-fix coordinates) coordinates))
  :hints (("Goal" :in-theory (enable affine-coordinates-p))))

(defthm field-element-p-of-affine-coordinates-x
  (field-element-p (affine-coordinates-x coordinates)))

(defthm field-element-p-of-affine-coordinates-y
  (field-element-p (affine-coordinates-y coordinates)))

(defthm affine-coordinates-x-of-fix
  (equal (affine-coordinates-x (affine-coordinates-fix coordinates))
         (affine-coordinates-x coordinates)))

(defthm affine-coordinates-y-of-fix
  (equal (affine-coordinates-y (affine-coordinates-fix coordinates))
         (affine-coordinates-y coordinates)))

(defthm short-weierstrass-affine-point-p-of-fix
  (equal (short-weierstrass-affine-point-p
          (affine-coordinates-fix coordinates))
         (short-weierstrass-affine-point-p coordinates))
  :rule-classes nil)

(defthm short-weierstrass-affine-point-p-definition
  (equal (short-weierstrass-affine-point-p coordinates)
         (short-weierstrass-equation-p
          (affine-coordinates-x coordinates)
          (affine-coordinates-y coordinates)))
  :rule-classes nil)

(verify-guards affine-coordinates-make)
(verify-guards affine-coordinates-x)
(verify-guards affine-coordinates-y)
(verify-guards affine-coordinates-fix)
(verify-guards affine-coordinates-p)
(verify-guards short-weierstrass-affine-point-p)
