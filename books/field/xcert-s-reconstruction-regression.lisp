(in-package "GFIELD")
(include-book "xcert-s-reconstruction")

(local
 (defthm xcert-s-scalar-reconstruction-regression
 (implies
  (and
   (equal (field-mul p (field-add yb ya))
    (field-add (field-mul xb xb)
     (field-add (field-mul xb xa) (field-add (field-mul xa xa) curve-a))))
   (equal (field-mul q (field-add yc yab))
    (field-add (field-mul xc xc)
     (field-add (field-mul xc xab) (field-add (field-mul xab xab) curve-a))))
   (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
   (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
   (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
   (equal (field-mul tt (field-sub xbc xa)) (field-sub ybc ya))
   (equal (field-add (field-add xab xa) xb) (field-mul p p))
   (equal (field-add yab ya) (field-mul p (field-sub xa xab)))
   (equal (field-add (field-add xbc xb) xc) (field-mul r r))
   (equal (field-add ybc yb) (field-mul r (field-sub xb xbc)))
   (not (equal (field-sub xc xb) (field-zero)))
   (not (equal (field-sub xbc xa) (field-zero))))
  (equal (field-sub (field-add p q) (field-add r tt))
         (field-zero)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance xcert-s-scalar-reconstruction))
          :in-theory (theory 'minimal-theory)))))

(local
 (defthm xcert-s-factored-from-h-client-regression
  (implies
   (and
    (equal (field-mul (field-sub p r) (field-add p q)) (field-sub xa xc))
    (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-mul tt (field-sub xbc xa)) (field-sub ybc ya))
    (equal (field-add (field-add xab xa) xb) (field-mul p p))
    (equal (field-add yab ya) (field-mul p (field-sub xa xab)))
    (equal (field-add (field-add xbc xb) xc) (field-mul r r))
    (equal (field-add ybc yb) (field-mul r (field-sub xb xbc))))
   (equal (field-mul (field-sub xbc xa)
                     (field-sub (field-add p q) (field-add r tt)))
          (field-zero)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance xcert-s-factored-reconstruction-from-h))
           :in-theory (theory 'minimal-theory)))))
