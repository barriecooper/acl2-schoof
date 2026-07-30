(in-package "GFIELD")
(include-book "xcert-final-y-reconstruction")

(local
 (defthm xcert-output-x-h-coordinate-bridge-regression
  (implies
   (and
    (equal (field-add (field-add xl xab) xc) (field-mul q q))
    (equal (field-add (field-add xab xa) xb) (field-mul p p))
    (equal (field-mul (field-sub p r) (field-add p q))
           (field-sub xa xc)))
   (equal (field-sub xl xb)
          (field-mul (field-sub q r) (field-add p q))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance xcert-output-x-h-coordinate-bridge))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm xcert-y-difference-six-residual-reduction-regression
  (implies
   (and
    (equal (field-sub (field-add p q) (field-add r tt)) (field-zero))
    (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-add yl yab) (field-mul q (field-sub xab xl)))
    (equal (field-add yr ya) (field-mul tt (field-sub xa xl))))
   (equal
    (field-sub yl yr)
    (field-add
     (field-mul (field-sub p r) (field-sub xl xb))
     (field-mul (field-sub r q) (field-sub xa xc)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance xcert-y-difference-six-residual-reduction))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm xcert-field-only-final-y-equal-regression
  (implies
   (and
    (equal (field-add (field-add xl xab) xc) (field-mul q q))
    (equal (field-add (field-add xab xa) xb) (field-mul p p))
    (equal (field-mul (field-sub p r) (field-add p q))
           (field-sub xa xc))
    (equal (field-sub (field-add p q) (field-add r tt)) (field-zero))
    (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-add yl yab) (field-mul q (field-sub xab xl)))
    (equal (field-add yr ya) (field-mul tt (field-sub xa xl))))
   (equal (field-fix yl) (field-fix yr)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance xcert-field-only-final-y-equal))
           :in-theory (theory 'minimal-theory)))))
