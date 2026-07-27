(in-package "GFIELD")

(include-book "power-correspondence")

; Minimal q-power certificate.  This constrains only a positive exponent and
; its unconditional fixed-point equation at the public comparison power.  It
; does not identify the exponent with a cardinality, characteristic, prime,
; prime power, or least such exponent.
(encapsulate
 (((field-frobenius-exponent) => *))
 (local (defun field-frobenius-exponent () 1))

 (defthm posp-of-field-frobenius-exponent
   (posp (field-frobenius-exponent))
   :rule-classes nil)

 (defthm field-pow-instance-of-field-frobenius-exponent
   (equal (field-pow-instance x (field-frobenius-exponent))
          (field-fix x))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-pow-instance-correspondence
                             (n (field-frobenius-exponent)))
                  (:instance field-pow-one))
            :in-theory (disable field-pow-instance-correspondence
                                field-pow-one)))))
