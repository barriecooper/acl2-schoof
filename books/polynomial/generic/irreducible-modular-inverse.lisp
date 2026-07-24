(in-package "GPOLY")
(include-book "irreducibility")
(include-book "modular-inverse")

; This downstream interface deliberately composes the logical irreducibility
; bridge with the existing XGCD-derived inverse laws.  It introduces no new
; computation and keeps reduced representatives at the public ring boundary.
(defthm poly-irreducible-p-nonzero-remainder-modular-inverse-left
  (implies
   (and (poly-irreducible-p modulus)
        (equal first (poly-remainder first modulus))
        (not (equal (normalize first) nil)))
   (equal
    (poly-reduced-mul (poly-modular-inverse first modulus) first modulus)
    (poly-reduced-one modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           poly-irreducible-p-nonzero-remainder-implies-monic-gcd-one)
          (:instance poly-reduced-mul-modular-inverse-left))
    :in-theory (disable poly-irreducible-p poly-remainder normalize
                        poly-monic-euclidean-gcd poly-modular-inverse
                        poly-reduced-mul poly-reduced-one))))

(defthm poly-irreducible-p-nonzero-remainder-modular-inverse-right
  (implies
   (and (poly-irreducible-p modulus)
        (equal first (poly-remainder first modulus))
        (not (equal (normalize first) nil)))
   (equal
    (poly-reduced-mul first (poly-modular-inverse first modulus) modulus)
    (poly-reduced-one modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           poly-irreducible-p-nonzero-remainder-implies-monic-gcd-one)
          (:instance poly-reduced-mul-modular-inverse-right))
    :in-theory (disable poly-irreducible-p poly-remainder normalize
                        poly-monic-euclidean-gcd poly-modular-inverse
                        poly-reduced-mul poly-reduced-one))))

; The conjunction is useful to later field promotion: one application exposes
; the complete two-sided unit contract for a canonical nonzero representative.
(defthm poly-irreducible-p-nonzero-remainder-modular-inverse
  (implies
   (and (poly-irreducible-p modulus)
        (equal first (poly-remainder first modulus))
        (not (equal (normalize first) nil)))
   (and
    (equal
     (poly-reduced-mul (poly-modular-inverse first modulus) first modulus)
     (poly-reduced-one modulus))
    (equal
     (poly-reduced-mul first (poly-modular-inverse first modulus) modulus)
     (poly-reduced-one modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           poly-irreducible-p-nonzero-remainder-modular-inverse-left)
          (:instance
           poly-irreducible-p-nonzero-remainder-modular-inverse-right)))))

(defthm poly-irreducible-p-not-divides-modular-inverse
  (implies
   (and (poly-irreducible-p modulus)
        (not (poly-divides-p modulus first)))
   (and
    (equal
     (poly-reduced-mul (poly-modular-inverse first modulus) first modulus)
     (poly-reduced-one modulus))
    (equal
     (poly-reduced-mul first (poly-modular-inverse first modulus) modulus)
     (poly-reduced-one modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance
           poly-irreducible-p-and-not-divides-implies-monic-gcd-one)
          (:instance poly-reduced-mul-modular-inverse-left)
          (:instance poly-reduced-mul-modular-inverse-right))
    :in-theory (disable poly-irreducible-p poly-divides-p
                        poly-monic-euclidean-gcd poly-modular-inverse
                        poly-reduced-mul poly-reduced-one))))
