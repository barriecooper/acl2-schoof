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
