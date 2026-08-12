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

(local
 (defthm quotient-coordinate-cubic-scaled-middle-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 2 (quotient-coordinate-mul x z a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 2
     (quotient-coordinate-mul (quotient-coordinate-mul x z a b modulus) x a b modulus) modulus)
    (quotient-coordinate-nat-mul 2
     (quotient-coordinate-mul (quotient-coordinate-mul x z a b modulus) z a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-add x z modulus))
     (z (quotient-coordinate-nat-mul 2 (quotient-coordinate-mul x z a b modulus) modulus)))
    (:instance quotient-coordinate-mul-of-nat-mul-left
     (n 2) (x (quotient-coordinate-mul x z a b modulus)) (z (quotient-coordinate-add x z modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-mul x z a b modulus)) (z x) (w z))
    (:instance quotient-coordinate-nat-mul-distributes-over-add
     (n 2)
     (x (quotient-coordinate-mul (quotient-coordinate-mul x z a b modulus) x a b modulus))
     (z (quotient-coordinate-mul (quotient-coordinate-mul x z a b modulus) z a b modulus))))
   :in-theory (union-theories (theory 'minimal-theory) '(natp))))))

(local (defthm quotient-coordinate-cubic-self-local
 (equal (quotient-coordinate-mul x (quotient-coordinate-pow x 2 a b modulus) a b modulus)
        (quotient-coordinate-pow x 3 a b modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-pow-successor (base x) (n 2)))
          :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-cubic-left-end-local
 (equal (quotient-coordinate-mul z (quotient-coordinate-pow x 2 a b modulus) a b modulus)
        (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-mul-commutative
                         (x z) (z (quotient-coordinate-pow x 2 a b modulus))))
          :in-theory (theory 'minimal-theory)))))
(local (defthm quotient-coordinate-cubic-middle-left-local
 (equal (quotient-coordinate-mul (quotient-coordinate-mul x z a b modulus) x a b modulus)
        (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-mul-associative (x x) (z z) (w x))
   (:instance quotient-coordinate-mul-associative (x x) (z x) (w z))
   (:instance quotient-coordinate-mul-commutative (x z) (z x))
   (:instance quotient-coordinate-pow-two-normal-local (x x)))
  :in-theory (theory 'minimal-theory)))))
(local (defthm quotient-coordinate-cubic-middle-right-local
 (equal (quotient-coordinate-mul (quotient-coordinate-mul x z a b modulus) z a b modulus)
        (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-mul-associative (x x) (z z) (w z))
   (:instance quotient-coordinate-pow-two-normal-local (x z)))
  :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-cubic-left-endpoint-normal-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
                            (quotient-coordinate-pow x 2 a b modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-pow x 3 a b modulus)
    (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-endpoint-distribution-local
     (term (quotient-coordinate-pow x 2 a b modulus)))
    (:instance quotient-coordinate-cubic-self-local (x x))
    (:instance quotient-coordinate-cubic-left-end-local))
   :in-theory (theory 'minimal-theory)))))
(local
 (defthm quotient-coordinate-cubic-right-endpoint-normal-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
                            (quotient-coordinate-pow z 2 a b modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus)
    (quotient-coordinate-pow z 3 a b modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-endpoint-distribution-local
     (term (quotient-coordinate-pow z 2 a b modulus)))
    (:instance quotient-coordinate-cubic-self-local (x z)))
   :in-theory (theory 'minimal-theory)))))
(local
 (defthm quotient-coordinate-cubic-middle-normal-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 2 (quotient-coordinate-mul x z a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 2
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) modulus)
    (quotient-coordinate-nat-mul 2
     (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-scaled-middle-local)
    (:instance quotient-coordinate-cubic-middle-left-local)
    (:instance quotient-coordinate-cubic-middle-right-local))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-cubic-expanded-local
  (equal
   (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 3 a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-pow x 3 a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus)
     (quotient-coordinate-add
      (quotient-coordinate-nat-mul 2
       (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) modulus)
      (quotient-coordinate-add
       (quotient-coordinate-nat-mul 2
        (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
       (quotient-coordinate-add
        (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus)
        (quotient-coordinate-pow z 3 a b modulus) modulus) modulus) modulus) modulus) modulus))
  :rule-classes nil
  :hints (("Goal" :use
   ((:instance quotient-coordinate-pow-successor
     (base (quotient-coordinate-add x z modulus)) (n 2))
    (:instance quotient-coordinate-pow-two-of-add-local)
    (:instance quotient-coordinate-cubic-outer-distribution-local
     (x2 (quotient-coordinate-pow x 2 a b modulus))
     (two-xz (quotient-coordinate-nat-mul 2 (quotient-coordinate-mul x z a b modulus) modulus))
     (z2 (quotient-coordinate-pow z 2 a b modulus)))
    (:instance quotient-coordinate-cubic-left-endpoint-normal-local)
    (:instance quotient-coordinate-cubic-middle-normal-local)
    (:instance quotient-coordinate-cubic-right-endpoint-normal-local)
    (:instance quotient-coordinate-add-associative
     (x (quotient-coordinate-pow x 3 a b modulus))
     (z (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus))
     (w (quotient-coordinate-add
         (quotient-coordinate-nat-mul 2 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) modulus)
         (quotient-coordinate-add
          (quotient-coordinate-nat-mul 2 (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
          (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus)
                                   (quotient-coordinate-pow z 3 a b modulus) modulus) modulus) modulus))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(nfix quotient-coordinate-cubic-left-endpoint-normal-local
      quotient-coordinate-cubic-middle-normal-local
      quotient-coordinate-cubic-right-endpoint-normal-local
      quotient-coordinate-add-associative))))))
(local
 (defthm quotient-coordinate-one-times-closed-local
  (implies (quotient-coordinate-p term modulus)
           (equal term (quotient-coordinate-nat-mul 1 term modulus)))
  :rule-classes nil
  :hints (("Goal" :use
   ((:instance quotient-coordinate-nat-mul-successor (n 0) (coordinate term))
    (:instance quotient-coordinate-nat-mul-zero (coordinate term))
    (:instance quotient-coordinate-add-zero-right (x term))
    (:instance quotient-coordinate-fix-when-p (coordinate term)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp))))))
(local
 (defthm quotient-coordinate-collect-one-two-local
  (implies (quotient-coordinate-p term modulus)
   (equal
    (quotient-coordinate-add term
     (quotient-coordinate-add (quotient-coordinate-nat-mul 2 term modulus) tail modulus) modulus)
    (quotient-coordinate-add (quotient-coordinate-nat-mul 3 term modulus) tail modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-one-times-closed-local)
    (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 2)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local
 (defthm quotient-coordinate-collect-two-one-local
  (implies (quotient-coordinate-p term modulus)
   (equal
    (quotient-coordinate-add (quotient-coordinate-nat-mul 2 term modulus)
     (quotient-coordinate-add term tail modulus) modulus)
    (quotient-coordinate-add (quotient-coordinate-nat-mul 3 term modulus) tail modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-one-times-closed-local)
    (:instance quotient-coordinate-collect-adjacent-scalars-local (m 2) (n 1)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))

(local
 (defthm quotient-coordinate-pow-three-of-add-local
  (equal
   (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 3 a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-pow x 3 a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-nat-mul 3
      (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) modulus)
     (quotient-coordinate-add
      (quotient-coordinate-nat-mul 3
       (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
      (quotient-coordinate-pow z 3 a b modulus) modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-expanded-local)
    (:instance quotient-coordinate-collect-one-two-local
     (term (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus))
     (tail (quotient-coordinate-add
            (quotient-coordinate-nat-mul 2 (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
            (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus)
                                     (quotient-coordinate-pow z 3 a b modulus) modulus) modulus)))
    (:instance quotient-coordinate-collect-two-one-local
     (term (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus))
     (tail (quotient-coordinate-pow z 3 a b modulus)))
    (:instance quotient-coordinate-operations-closed
     (x (quotient-coordinate-pow x 2 a b modulus)) (z z))
    (:instance quotient-coordinate-operations-closed
     (x x) (z (quotient-coordinate-pow z 2 a b modulus))))
   :in-theory (theory 'minimal-theory)))))
