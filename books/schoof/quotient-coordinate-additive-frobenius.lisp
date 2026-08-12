(in-package "GPOLY")

(include-book "quotient-coordinate-power")
(include-book "quotient-coordinate-natural-scalar")

; Natural scaling is compatible with multiplication in the left factor.
; This orientation is intended for the fixed Pascal expansion.
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


; The fixed Pascal development uses right-associated rows, ordered by
; descending X exponent.  These organizational facts remain local.
(local
 (defthm quotient-coordinate-pow-two-normal-local
   (equal (quotient-coordinate-pow x 2 a b modulus)
          (quotient-coordinate-mul x x a b modulus))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-pow-successor
                             (base x) (n 1))
                  (:instance quotient-coordinate-pow-one (base x))
                  (:instance quotient-coordinate-mul-of-fixes
                             (left x) (right x))
                  (:instance quotient-coordinate-mul-of-fixes
                             (left x)
                             (right (quotient-coordinate-fix x modulus)))
                  (:instance quotient-coordinate-fix-idempotent
                             (coordinate x)))
            :in-theory
            (union-theories (theory 'minimal-theory) '(nfix))))))

(local
 (defthm quotient-coordinate-double-closed-local
   (implies (quotient-coordinate-p term modulus)
            (equal (quotient-coordinate-add term term modulus)
                   (quotient-coordinate-nat-mul 2 term modulus)))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-nat-mul-successor
                             (n 1) (coordinate term))
                  (:instance quotient-coordinate-nat-mul-successor
                             (n 0) (coordinate term))
                  (:instance quotient-coordinate-nat-mul-zero
                             (coordinate term))
                  (:instance quotient-coordinate-add-zero-right (x term))
                  (:instance quotient-coordinate-fix-when-p
                             (coordinate term)))
            :in-theory
            (union-theories (theory 'minimal-theory) '(natp))))))

(local
 (defthm quotient-coordinate-collect-adjacent-scalars-local
   (implies (and (natp m) (natp n))
            (equal
             (quotient-coordinate-add
              (quotient-coordinate-nat-mul m term modulus)
              (quotient-coordinate-add
               (quotient-coordinate-nat-mul n term modulus)
               tail modulus) modulus)
             (quotient-coordinate-add
              (quotient-coordinate-nat-mul (+ m n) term modulus)
              tail modulus)))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-add-associative
                             (x (quotient-coordinate-nat-mul m term modulus))
                             (z (quotient-coordinate-nat-mul n term modulus))
                             (w tail))
                  (:instance quotient-coordinate-nat-mul-of-sum (x term)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-pow-two-of-add-local
   (equal
    (quotient-coordinate-pow
     (quotient-coordinate-add x z modulus) 2 a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-pow x 2 a b modulus)
     (quotient-coordinate-add
      (quotient-coordinate-nat-mul
       2 (quotient-coordinate-mul x z a b modulus) modulus)
      (quotient-coordinate-pow z 2 a b modulus) modulus) modulus))
   :hints
   (("Goal"
     :use
     ((:instance quotient-coordinate-pow-two-normal-local
                 (x (quotient-coordinate-add x z modulus)))
      (:instance quotient-coordinate-mul-right-distributive
                 (x x) (z z) (w (quotient-coordinate-add x z modulus)))
      (:instance quotient-coordinate-mul-left-distributive
                 (x x) (z x) (w z))
      (:instance quotient-coordinate-mul-left-distributive
                 (x z) (z x) (w z))
      (:instance quotient-coordinate-mul-commutative (x z) (z x))
      (:instance quotient-coordinate-add-associative
                 (x (quotient-coordinate-mul x x a b modulus))
                 (z (quotient-coordinate-mul x z a b modulus))
                 (w (quotient-coordinate-add
                     (quotient-coordinate-mul x z a b modulus)
                     (quotient-coordinate-mul z z a b modulus) modulus)))
      (:instance quotient-coordinate-add-associative
                 (x (quotient-coordinate-mul x z a b modulus))
                 (z (quotient-coordinate-mul x z a b modulus))
                 (w (quotient-coordinate-mul z z a b modulus)))
      (:instance quotient-coordinate-double-closed-local
                 (term (quotient-coordinate-mul x z a b modulus)))
      (:instance quotient-coordinate-operations-closed (x x) (z z))
      (:instance quotient-coordinate-pow-two-normal-local (x x))
      (:instance quotient-coordinate-pow-two-normal-local (x z)))
     :in-theory (theory 'minimal-theory)))))

; Bounded cubic stages distribute only the selected right-associated row.
(local
 (defthm quotient-coordinate-cubic-outer-distribution-local
   (equal
    (quotient-coordinate-mul
     (quotient-coordinate-add x z modulus)
     (quotient-coordinate-add x2
      (quotient-coordinate-add two-xz z2 modulus) modulus) a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-mul
      (quotient-coordinate-add x z modulus) x2 a b modulus)
     (quotient-coordinate-add
      (quotient-coordinate-mul
       (quotient-coordinate-add x z modulus) two-xz a b modulus)
      (quotient-coordinate-mul
       (quotient-coordinate-add x z modulus) z2 a b modulus) modulus)
     modulus))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-mul-left-distributive
                             (x (quotient-coordinate-add x z modulus))
                             (z x2)
                             (w (quotient-coordinate-add two-xz z2 modulus)))
                  (:instance quotient-coordinate-mul-left-distributive
                             (x (quotient-coordinate-add x z modulus))
                             (z two-xz) (w z2)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-cubic-endpoint-distribution-local
   (equal
    (quotient-coordinate-mul
     (quotient-coordinate-add x z modulus) term a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-mul x term a b modulus)
     (quotient-coordinate-mul z term a b modulus) modulus))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-mul-right-distributive
                             (w term)))
            :in-theory (theory 'minimal-theory)))))
