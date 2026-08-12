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


(defthm quotient-coordinate-pow-eleven-expanded-minimal-theory-client
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 11 a b modulus) (quotient-coordinate-add (quotient-coordinate-pow x 11 a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 11 (quotient-coordinate-mul (quotient-coordinate-pow x 10 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 55 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 165 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 330 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 462 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 462 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 330 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 165 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 55 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 11 (quotient-coordinate-mul x (quotient-coordinate-pow z 10 a b modulus) a b modulus) modulus) (quotient-coordinate-pow z 11 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
  :rule-classes nil
  :hints (("Goal" :use ((:instance quotient-coordinate-pow-eleven-of-add-expanded))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-eleven-multiple-cancellation-minimal-theory-client
 (implies (and (gfield::field-characteristic-p 11) (natp m))
  (equal (quotient-coordinate-nat-mul (* m 11) coordinate modulus)
         (quotient-coordinate-zero modulus)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance quotient-coordinate-nat-mul-of-eleven-multiple))
          :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-pow-eleven-add-minimal-theory-client
 (implies (gfield::field-characteristic-p 11)
  (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 11 a b modulus)
         (quotient-coordinate-add (quotient-coordinate-pow x 11 a b modulus)
                                  (quotient-coordinate-pow z 11 a b modulus) modulus)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance quotient-coordinate-pow-eleven-of-add))
          :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-frobenius-eleven-add-minimal-theory-client
 (implies (gfield::field-characteristic-p 11)
  (equal (quotient-coordinate-frobenius (quotient-coordinate-add x z modulus) 11 a b modulus)
         (quotient-coordinate-add (quotient-coordinate-frobenius x 11 a b modulus)
                                  (quotient-coordinate-frobenius z 11 a b modulus) modulus)))
 :rule-classes nil
 :hints (("Goal" :use ((:instance quotient-coordinate-frobenius-eleven-of-add))
          :in-theory (theory 'minimal-theory))))
