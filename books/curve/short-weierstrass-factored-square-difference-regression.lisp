(in-package "GFIELD")

(include-book "short-weierstrass-factored-square-difference")

(defthm short-weierstrass-factored-square-difference-client-regression
  (implies
   (and
    (equal
     (field-mul y1 y1)
     (field-add (field-mul (field-mul x1 x1) x1)
                (field-add (field-mul a x1) b)))
    (equal
     (field-mul y2 y2)
     (field-add (field-mul (field-mul x2 x2) x2)
                (field-add (field-mul a x2) b))))
   (equal
    (field-sub (field-mul y2 y2) (field-mul y1 y1))
    (field-mul
     (field-sub x2 x1)
     (field-add
      (field-add (field-add (field-mul x2 x2) (field-mul x2 x1))
                 (field-mul x1 x1))
      a))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      short-weierstrass-curve-equations-imply-factored-square-difference
      (xa x1) (ya y1) (xc x2) (yc y2) (curve-a a) (curve-b b)))
    :in-theory (theory 'minimal-theory))))
