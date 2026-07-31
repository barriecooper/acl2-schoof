(in-package "GFIELD")

(include-book "cubic-plus-linear-difference-factorization")

(defthm field-cubic-plus-linear-difference-factorization-client-regression
  (equal
   (field-sub
    (field-add (field-mul (field-mul x2 x2) x2) (field-mul a x2))
    (field-add (field-mul (field-mul x1 x1) x1) (field-mul a x1)))
   (field-mul
    (field-sub x2 x1)
    (field-add
     (field-add (field-add (field-mul x2 x2) (field-mul x2 x1))
                (field-mul x1 x1))
     a)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-cubic-plus-linear-difference-factorization
                     (xc x2) (xa x1) (curve-a a)))
    :in-theory (theory 'minimal-theory))))
