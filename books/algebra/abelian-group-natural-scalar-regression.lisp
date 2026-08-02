(in-package "GFIELD")

(include-book "abelian-group-natural-scalar")

(defun boolean-scalar-context-p () t)
(defun boolean-scalar-element-p (x) (booleanp x))
(defun boolean-scalar-op (x y) (if x (not y) y))
(defun boolean-scalar-identity () nil)
(defun boolean-scalar-inverse (x) (if x t nil))
(defun boolean-scalar-nat-mul (n x)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n) (boolean-scalar-identity)
      (boolean-scalar-op x (boolean-scalar-nat-mul (1- n) x)))))

(defthm boolean-scalar-nat-mul-of-sum-from-generic
  (implies (and (boolean-scalar-context-p) (natp m) (natp n) (boolean-scalar-element-p x))
           (equal (boolean-scalar-nat-mul (+ m n) x)
                  (boolean-scalar-op (boolean-scalar-nat-mul m x)
                                     (boolean-scalar-nat-mul n x))))
  :hints (("Goal" :by (:functional-instance
                         abelian-group-nat-mul-of-sum
                         (abelian-group-context-p boolean-scalar-context-p)
                         (abelian-group-element-p boolean-scalar-element-p)
                         (abelian-group-op boolean-scalar-op)
                         (abelian-group-identity boolean-scalar-identity)
                         (abelian-group-inverse boolean-scalar-inverse)
                         (abelian-group-nat-mul boolean-scalar-nat-mul)))))

(defthm boolean-scalar-nat-mul-distribution-from-generic
  (implies (and (boolean-scalar-context-p) (natp n) (boolean-scalar-element-p x) (boolean-scalar-element-p y))
           (equal (boolean-scalar-nat-mul n (boolean-scalar-op x y))
                  (boolean-scalar-op (boolean-scalar-nat-mul n x)
                                     (boolean-scalar-nat-mul n y))))
  :hints (("Goal" :by (:functional-instance
                         abelian-group-nat-mul-distributes-over-op
                         (abelian-group-context-p boolean-scalar-context-p)
                         (abelian-group-element-p boolean-scalar-element-p)
                         (abelian-group-op boolean-scalar-op)
                         (abelian-group-identity boolean-scalar-identity)
                         (abelian-group-inverse boolean-scalar-inverse)
                         (abelian-group-nat-mul boolean-scalar-nat-mul)))))

(assert-event (and (equal (boolean-scalar-nat-mul 0 t) nil)
                   (equal (boolean-scalar-nat-mul 1 t) t)
                   (equal (boolean-scalar-nat-mul 6 t) nil)
                   (equal (boolean-scalar-nat-mul 7 t) t)))
