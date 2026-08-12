(in-package "GPOLY")

(include-book "quotient-coordinate-power")
(include-book "quotient-coordinate-natural-scalar")

; Scalar multiplication commutes with multiplication in the quotient ring.
; This orientation is the one used by the fixed Pascal expansion below.
(defthm quotient-coordinate-mul-of-nat-mul-left
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-nat-mul n x modulus) z a b modulus)
   (quotient-coordinate-nat-mul
    n (quotient-coordinate-mul x z a b modulus) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-is-unit-times
                            (coordinate x))
                 (:instance quotient-coordinate-nat-mul-is-unit-times
                            (coordinate (quotient-coordinate-mul x z a b modulus)))
                 (:instance quotient-coordinate-mul-associative
                            (x (quotient-coordinate-nat-mul n (quotient-coordinate-one modulus) modulus))
                            (z x) (w z)))
           :in-theory (disable quotient-coordinate-mul
                               quotient-coordinate-mul-associative))))

