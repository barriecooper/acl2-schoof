(in-package "GFIELD")

(include-book "short-weierstrass")
(include-book "../field/common-summand-subtraction")

(local
 (defthm field-add-reassociate-common-right-local
   (equal (field-add x (field-add y common))
          (field-add (field-add x y) common))
   :hints
   (("Goal"
     :use ((:instance field-add-associative
                      (x x) (y y) (z common)))
     :in-theory (theory 'minimal-theory)))))

(defthm short-weierstrass-curve-equations-imply-square-difference
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
    (field-sub
     (field-add (field-mul (field-mul xc xc) xc)
                (field-mul curve-a xc))
     (field-add (field-mul (field-mul xa xa) xa)
                (field-mul curve-a xa)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance field-add-reassociate-common-right-local
                (x (field-mul (field-mul xc xc) xc))
                (y (field-mul curve-a xc))
                (common curve-b))
     (:instance field-add-reassociate-common-right-local
                (x (field-mul (field-mul xa xa) xa))
                (y (field-mul curve-a xa))
                (common curve-b))
     (:instance field-sub-eliminate-common-right-summand
                (left (field-mul yc yc))
                (right (field-mul ya ya))
                (left-core
                 (field-add (field-mul (field-mul xc xc) xc)
                            (field-mul curve-a xc)))
                (right-core
                 (field-add (field-mul (field-mul xa xa) xa)
                            (field-mul curve-a xa)))
                (common curve-b)))
    :in-theory (theory 'minimal-theory))))
