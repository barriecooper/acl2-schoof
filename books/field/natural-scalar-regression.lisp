(in-package "GFIELD")

(include-book "natural-scalar")

(defthm field-natural-scalar-boundary-regression
  (and (equal (field-nat-mul 0 x) (field-zero))
       (equal (field-nat-mul 1 x) (field-fix x))
       (equal (field-nat-mul 3 (field-add x y))
              (field-add (field-nat-mul 3 x)
                         (field-nat-mul 3 y)))
       (equal (field-nat-mul 3 (field-mul x y))
              (field-mul x (field-nat-mul 3 y))))
  :rule-classes nil)
