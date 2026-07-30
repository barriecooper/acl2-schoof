(in-package "GFIELD")
(include-book "xcert-h-reconstruction")

; Protect the exact seven-equation scalar interface.  In particular, the
; ordered (B,C) difference is the only nonzero premise, E2 is absent, and the
; conclusion retains the factor, sum, and coordinate orientations.
(local
 (defthm xcert-h-scalar-reconstruction-regression
  (implies
   (and
    (equal (field-mul p (field-add yb ya))
     (field-add (field-mul xb xb)
      (field-add (field-mul xb xa) (field-add (field-mul xa xa) a))))
    (equal (field-mul q (field-add yc yab))
     (field-add (field-mul xc xc)
      (field-add (field-mul xc xab) (field-add (field-mul xab xab) a))))
    (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-add (field-add xab xa) xb) (field-mul p p))
    (equal (field-add yab ya) (field-mul p (field-sub xa xab)))
    (not (equal (field-sub xc xb) (field-zero))))
   (equal
    (field-mul (field-sub p r) (field-add p q))
    (field-sub xa xc)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance xcert-h-scalar-reconstruction))
           :in-theory (theory 'minimal-theory)))))
