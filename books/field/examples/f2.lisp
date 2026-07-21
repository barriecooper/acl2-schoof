(in-package "GFIELD")

; Executable Boolean field used only as an instantiation regression.
(defun f2-element-p (x) (booleanp x))
(defun f2-fix (x) (if x t nil))
(defun f2-zero () nil)
(defun f2-one () t)
(defun f2-add (x y) (if (equal (f2-fix x) (f2-fix y)) nil t))
(defun f2-mul (x y) (if (and (f2-fix x) (f2-fix y)) t nil))
(defun f2-neg (x) (f2-fix x))
(defun f2-inv (x) (f2-fix x))
(defun f2-sub (x y) (f2-add x (f2-neg y)))
(defun f2-div (x y) (f2-mul x (f2-inv y)))
(defun f2-pow (x n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (if (zp n) (f2-one) (f2-mul x (f2-pow x (1- n)))))

(defthm f2-double-negation-from-generic-kernel
  (equal (f2-neg (f2-neg x)) (f2-fix x))
  :hints (("Goal" :by (:functional-instance field-neg-of-neg
                       (field-element-p f2-element-p)
                       (field-fix f2-fix)
                       (field-zero f2-zero)
                       (field-one f2-one)
                       (field-add f2-add)
                       (field-mul f2-mul)
                       (field-neg f2-neg)
                       (field-inv f2-inv)))))
