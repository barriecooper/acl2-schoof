(in-package "GFIELD")

(include-book "short-weierstrass-curve-equation-subtraction")
(include-book "../field/cubic-plus-linear-difference-factorization")

(defthm short-weierstrass-curve-equations-imply-factored-square-difference
  (implies
   (and
    (equal
     (field-mul ya ya)
     (field-add
      (field-mul (field-mul xa xa) xa)
      (field-add (field-mul curve-a xa) curve-b)))
    (equal
     (field-mul yc yc)
     (field-add
      (field-mul (field-mul xc xc) xc)
      (field-add (field-mul curve-a xc) curve-b))))
   (equal
    (field-sub (field-mul yc yc) (field-mul ya ya))
    (field-mul
     (field-sub xc xa)
     (field-add
      (field-add
       (field-add (field-mul xc xc) (field-mul xc xa))
       (field-mul xa xa))
      curve-a))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance short-weierstrass-curve-equations-imply-square-difference)
     (:instance field-cubic-plus-linear-difference-factorization))
    :in-theory (theory 'minimal-theory))))
