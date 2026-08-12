(in-package "GPOLY")
(include-book "quotient-coordinate-additive-frobenius")

(defthm quotient-coordinate-mul-of-natural-scalar-minimal-theory-client
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-nat-mul n x modulus) z a b modulus)
   (quotient-coordinate-nat-mul
    n (quotient-coordinate-mul x z a b modulus) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-mul-of-nat-mul-left))
           :in-theory (theory 'minimal-theory))))
