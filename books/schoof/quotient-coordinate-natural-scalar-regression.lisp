(in-package "GPOLY")

(include-book "quotient-coordinate-natural-scalar")

(defthm quotient-coordinate-natural-scalar-interface-minimal-theory-client
  (and
   (equal (quotient-coordinate-nat-mul 0 coordinate modulus)
          (quotient-coordinate-zero modulus))
   (equal (quotient-coordinate-nat-mul (+ 1 (nfix n)) coordinate modulus)
          (quotient-coordinate-add
           coordinate (quotient-coordinate-nat-mul n coordinate modulus)
           modulus))
   (quotient-coordinate-p
    (quotient-coordinate-nat-mul n coordinate modulus) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-zero)
                 (:instance quotient-coordinate-nat-mul-successor-total)
                 (:instance quotient-coordinate-p-of-nat-mul))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-natural-scalar-unit-times-minimal-theory-client
  (equal
   (quotient-coordinate-nat-mul n coordinate modulus)
   (quotient-coordinate-mul
    (quotient-coordinate-nat-mul
     n (quotient-coordinate-one modulus) modulus)
    coordinate a b modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-is-unit-times))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-natural-scalar-unit-embedding-minimal-theory-client
  (equal
   (quotient-coordinate-nat-mul
    n (quotient-coordinate-one modulus) modulus)
   (quotient-coordinate-embed
    (const (gfield::field-nat-mul n (gfield::field-one))) modulus))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  quotient-coordinate-nat-mul-of-one-is-embedded-field-nat-mul))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-characteristic-annihilation-minimal-theory-client
  (implies
   (gfield::field-characteristic-p p)
   (equal (quotient-coordinate-nat-mul p coordinate modulus)
          (quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-of-characteristic))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-characteristic-eleven-minimal-theory-client
  (implies
   (gfield::field-characteristic-p 11)
   (equal (quotient-coordinate-nat-mul 11 coordinate modulus)
          (quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  quotient-coordinate-nat-mul-eleven-of-characteristic))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-natural-scalar-sum-minimal-theory-client
  (implies (and (natp m) (natp n))
   (equal (quotient-coordinate-nat-mul (+ m n) x modulus)
          (quotient-coordinate-add
           (quotient-coordinate-nat-mul m x modulus)
           (quotient-coordinate-nat-mul n x modulus) modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-of-sum))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-natural-scalar-composition-minimal-theory-client
  (implies (and (natp m) (natp n))
   (equal (quotient-coordinate-nat-mul
           m (quotient-coordinate-nat-mul n x modulus) modulus)
          (quotient-coordinate-nat-mul (* m n) x modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-of-nat-mul))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-natural-scalar-distribution-minimal-theory-client
  (implies (natp n)
   (equal
    (quotient-coordinate-nat-mul
     n (quotient-coordinate-add x z modulus) modulus)
    (quotient-coordinate-add
     (quotient-coordinate-nat-mul n x modulus)
     (quotient-coordinate-nat-mul n z modulus) modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-distributes-over-add))
           :in-theory (theory 'minimal-theory))))
