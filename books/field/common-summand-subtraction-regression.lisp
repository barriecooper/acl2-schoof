(in-package "GFIELD")

(include-book "common-summand-subtraction")

(defthm field-sub-eliminate-common-right-summand-client-regression
  (implies
   (and (equal x (field-add x-core tail))
        (equal y (field-add y-core tail)))
   (equal (field-sub x y)
          (field-sub x-core y-core)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-sub-eliminate-common-right-summand
                     (left x) (right y)
                     (left-core x-core) (right-core y-core)
                     (common tail)))
    :in-theory (theory 'minimal-theory))))
