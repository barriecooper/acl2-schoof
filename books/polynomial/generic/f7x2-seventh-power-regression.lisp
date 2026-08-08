(in-package "GPOLY")
(include-book "f7x2-seventh-power")

(defthm f7x2-seventh-power-of-embedded-constant-coefficients
  (implies
   (gfield::f7-element-p constant)
   (and (equal (f7x2-constant-coefficient
               (f7x2-seventh-power (list constant)))
              (gfield::f7-fix constant))
       (equal (f7x2-linear-coefficient
               (f7x2-seventh-power (list constant)))
              (gfield::f7-zero))))
  :hints (("Goal"
           :use ((:instance f7x2-seventh-power-is-conjugate
                            (value (list constant))))
           :in-theory (enable f7x2-conjugate))))

(defthm f7x2-seventh-power-focused-regressions
  (and
   (equal (f7x2-seventh-power '(0 1)) '(0 6))
   (equal (f7x2-seventh-power '(1 1)) '(1 6))
   (equal (f7x2-seventh-power '(3 2)) '(3 5))
   (equal (f7x2-seventh-power '(6 4)) '(6 3))
   (equal (f7x2-seventh-power '(8 1)) '(1 6))
   (equal (f7x2-seventh-power '(1 1 0)) '(1 6))
   (equal (f7x2-seventh-power '(1 1 . malformed-tail)) '(1 6))
   (equal (f7x2-seventh-power 'malformed) nil))
  :hints (("Goal"
           :use ((:instance f7x2-seventh-power-is-conjugate (value '(0 1)))
                 (:instance f7x2-seventh-power-is-conjugate (value '(1 1)))
                 (:instance f7x2-seventh-power-is-conjugate (value '(3 2)))
                 (:instance f7x2-seventh-power-is-conjugate (value '(6 4)))
                 (:instance f7x2-seventh-power-is-conjugate (value '(8 1)))
                 (:instance f7x2-seventh-power-is-conjugate (value '(1 1 0)))
                 (:instance f7x2-seventh-power-is-conjugate
                            (value '(1 1 . malformed-tail)))
                 (:instance f7x2-seventh-power-is-conjugate
                            (value 'malformed)))
           :in-theory (enable f7x2-conjugate))))
