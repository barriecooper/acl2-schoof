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

(local
 (defthm quotient-coordinate-scaled-branch-transport-local
  (implies (natp n)
   (equal
    (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
     (quotient-coordinate-nat-mul n term modulus) a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-nat-mul n (quotient-coordinate-mul term x a b modulus) modulus)
     (quotient-coordinate-nat-mul n (quotient-coordinate-mul term z a b modulus) modulus)
     modulus)))
  :rule-classes nil
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-add x z modulus))
     (z (quotient-coordinate-nat-mul n term modulus)))
    (:instance quotient-coordinate-mul-of-nat-mul-left
     (x term) (z (quotient-coordinate-add x z modulus)))
    (:instance quotient-coordinate-mul-left-distributive (x term) (z x) (w z))
    (:instance quotient-coordinate-nat-mul-distributes-over-add
     (x (quotient-coordinate-mul term x a b modulus))
     (z (quotient-coordinate-mul term z a b modulus))))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-quartic-outer-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-add t0
     (quotient-coordinate-add t1 (quotient-coordinate-add t2 t3 modulus) modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t0 a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t1 a b modulus)
     (quotient-coordinate-add
      (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t2 a b modulus)
      (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t3 a b modulus) modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t0)
     (w (quotient-coordinate-add t1 (quotient-coordinate-add t2 t3 modulus) modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t1)
     (w (quotient-coordinate-add t2 t3 modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t2) (w t3)))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-times-cube-self-local
  (equal (quotient-coordinate-mul x (quotient-coordinate-pow x 3 a b modulus) a b modulus)
         (quotient-coordinate-pow x 4 a b modulus))
  :hints (("Goal" :use ((:instance quotient-coordinate-pow-successor (base x) (n 3)))
           :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local
 (defthm quotient-coordinate-quartic-left-endpoint-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
                            (quotient-coordinate-pow x 3 a b modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-pow x 4 a b modulus)
    (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-endpoint-distribution-local
     (term (quotient-coordinate-pow x 3 a b modulus)))
    (:instance quotient-coordinate-times-cube-self-local (x x))
    (:instance quotient-coordinate-mul-commutative
     (x z) (z (quotient-coordinate-pow x 3 a b modulus))))
   :in-theory (theory 'minimal-theory)))))
(local
 (defthm quotient-coordinate-quartic-right-endpoint-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
                            (quotient-coordinate-pow z 3 a b modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus)
    (quotient-coordinate-pow z 4 a b modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-endpoint-distribution-local
     (term (quotient-coordinate-pow z 3 a b modulus)))
    (:instance quotient-coordinate-times-cube-self-local (x z)))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-x2z-times-x-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) x a b modulus)
   (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x 2 a b modulus)) (z z) (w x))
    (:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x 2 a b modulus)) (z x) (w z))
    (:instance quotient-coordinate-mul-commutative (x z) (z x))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow x 2 a b modulus)) (z x))
    (:instance quotient-coordinate-pow-successor (base x) (n 2)))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local
 (defthm quotient-coordinate-x2z-times-z-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) z a b modulus)
   (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                            (quotient-coordinate-pow z 2 a b modulus) a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x 2 a b modulus)) (z z) (w z))
    (:instance quotient-coordinate-pow-two-normal-local (x z)))
   :in-theory (theory 'minimal-theory)))))
(local
 (defthm quotient-coordinate-xz2-times-x-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) x a b modulus)
   (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                            (quotient-coordinate-pow z 2 a b modulus) a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x x) (z (quotient-coordinate-pow z 2 a b modulus)) (w x))
    (:instance quotient-coordinate-mul-associative
     (x x) (z x) (w (quotient-coordinate-pow z 2 a b modulus)))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow z 2 a b modulus)) (z x))
    (:instance quotient-coordinate-pow-two-normal-local (x x)))
   :in-theory (theory 'minimal-theory)))))
(local
 (defthm quotient-coordinate-xz2-times-z-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) z a b modulus)
   (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x x) (z (quotient-coordinate-pow z 2 a b modulus)) (w z))
    (:instance quotient-coordinate-pow-successor (base z) (n 2))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow z 2 a b modulus)) (z z)))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))

(local
 (defthm quotient-coordinate-quartic-first-middle-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 3
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 3
     (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus) modulus)
    (quotient-coordinate-nat-mul 3
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                              (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local
     (n 3) (term (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus)))
    (:instance quotient-coordinate-x2z-times-x-local)
    (:instance quotient-coordinate-x2z-times-z-local))
   :in-theory (union-theories (theory 'minimal-theory) '(natp))))))
(local
 (defthm quotient-coordinate-quartic-second-middle-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 3
     (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 3
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                              (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
    (quotient-coordinate-nat-mul 3
     (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local
     (n 3) (term (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus)))
    (:instance quotient-coordinate-xz2-times-x-local)
    (:instance quotient-coordinate-xz2-times-z-local))
   :in-theory (union-theories (theory 'minimal-theory) '(natp))))))

(local
 (defthm quotient-coordinate-quartic-expanded-local
  (equal
   (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 4 a b modulus)
   (let ((x3z (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus))
         (x2z2 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                  (quotient-coordinate-pow z 2 a b modulus) a b modulus))
         (xz3 (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus)))
    (quotient-coordinate-add (quotient-coordinate-pow x 4 a b modulus)
     (quotient-coordinate-add x3z
      (quotient-coordinate-add (quotient-coordinate-nat-mul 3 x3z modulus)
       (quotient-coordinate-add (quotient-coordinate-nat-mul 3 x2z2 modulus)
        (quotient-coordinate-add (quotient-coordinate-nat-mul 3 x2z2 modulus)
         (quotient-coordinate-add (quotient-coordinate-nat-mul 3 xz3 modulus)
          (quotient-coordinate-add xz3 (quotient-coordinate-pow z 4 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus)))
  :rule-classes nil
  :hints (("Goal" :use
   ((:instance quotient-coordinate-pow-successor
     (base (quotient-coordinate-add x z modulus)) (n 3))
    (:instance quotient-coordinate-pow-three-of-add-local)
    (:instance quotient-coordinate-quartic-outer-local
     (t0 (quotient-coordinate-pow x 3 a b modulus))
     (t1 (quotient-coordinate-nat-mul 3 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) z a b modulus) modulus))
     (t2 (quotient-coordinate-nat-mul 3 (quotient-coordinate-mul x (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus))
     (t3 (quotient-coordinate-pow z 3 a b modulus)))
    (:instance quotient-coordinate-quartic-left-endpoint-local)
    (:instance quotient-coordinate-quartic-first-middle-local)
    (:instance quotient-coordinate-quartic-second-middle-local)
    (:instance quotient-coordinate-quartic-right-endpoint-local))
   :in-theory (union-theories (theory 'minimal-theory)
    '(nfix quotient-coordinate-quartic-left-endpoint-local
      quotient-coordinate-quartic-first-middle-local
      quotient-coordinate-quartic-second-middle-local
      quotient-coordinate-quartic-right-endpoint-local
      quotient-coordinate-add-associative))))))

(local
 (defthm quotient-coordinate-collect-one-three-local
  (implies (quotient-coordinate-p term modulus)
   (equal
    (quotient-coordinate-add term
     (quotient-coordinate-add (quotient-coordinate-nat-mul 3 term modulus) tail modulus) modulus)
    (quotient-coordinate-add (quotient-coordinate-nat-mul 4 term modulus) tail modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-one-times-closed-local)
    (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 3)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local
 (defthm quotient-coordinate-collect-three-one-local
  (implies (quotient-coordinate-p term modulus)
   (equal
    (quotient-coordinate-add (quotient-coordinate-nat-mul 3 term modulus)
     (quotient-coordinate-add term tail modulus) modulus)
    (quotient-coordinate-add (quotient-coordinate-nat-mul 4 term modulus) tail modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-one-times-closed-local)
    (:instance quotient-coordinate-collect-adjacent-scalars-local (m 3) (n 1)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local
 (defthm quotient-coordinate-collect-three-three-local
  (equal
   (quotient-coordinate-add (quotient-coordinate-nat-mul 3 term modulus)
    (quotient-coordinate-add (quotient-coordinate-nat-mul 3 term modulus) tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 6 term modulus) tail modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-collect-adjacent-scalars-local (m 3) (n 3)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))

(local
 (defthm quotient-coordinate-pow-four-of-add-local
  (equal
   (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 4 a b modulus)
   (let ((x3z (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus))
         (x2z2 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                  (quotient-coordinate-pow z 2 a b modulus) a b modulus))
         (xz3 (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus)))
    (quotient-coordinate-add (quotient-coordinate-pow x 4 a b modulus)
     (quotient-coordinate-add (quotient-coordinate-nat-mul 4 x3z modulus)
      (quotient-coordinate-add (quotient-coordinate-nat-mul 6 x2z2 modulus)
       (quotient-coordinate-add (quotient-coordinate-nat-mul 4 xz3 modulus)
                                (quotient-coordinate-pow z 4 a b modulus) modulus) modulus) modulus) modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-quartic-expanded-local)
    (:instance quotient-coordinate-collect-one-three-local
     (term (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus))
     (tail (quotient-coordinate-add
       (quotient-coordinate-nat-mul 3 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
       (quotient-coordinate-add
        (quotient-coordinate-nat-mul 3 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
        (quotient-coordinate-add
         (quotient-coordinate-nat-mul 3 (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus)
         (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus)
                                  (quotient-coordinate-pow z 4 a b modulus) modulus) modulus) modulus) modulus)))
    (:instance quotient-coordinate-collect-three-three-local
     (term (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus))
     (tail (quotient-coordinate-add
       (quotient-coordinate-nat-mul 3 (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus)
       (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus)
                                (quotient-coordinate-pow z 4 a b modulus) modulus) modulus)))
    (:instance quotient-coordinate-collect-three-one-local
     (term (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus))
     (tail (quotient-coordinate-pow z 4 a b modulus)))
    (:instance quotient-coordinate-operations-closed (x (quotient-coordinate-pow x 3 a b modulus)) (z z))
    (:instance quotient-coordinate-operations-closed (x (quotient-coordinate-pow x 2 a b modulus)) (z (quotient-coordinate-pow z 2 a b modulus)))
    (:instance quotient-coordinate-operations-closed (x x) (z (quotient-coordinate-pow z 3 a b modulus))))
   :in-theory (theory 'minimal-theory)))))
