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

; Fixed-row engineering for the remaining Pascal stages.  These two local
; monomial steps preserve the descending-X orientation without opening power
; or multiplication implementations.
(local
 (defthm quotient-coordinate-monomial-times-x-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul
     (quotient-coordinate-pow x i a b modulus)
     (quotient-coordinate-pow z j a b modulus) a b modulus)
    x a b modulus)
   (quotient-coordinate-mul
    (quotient-coordinate-pow x (+ 1 (nfix i)) a b modulus)
    (quotient-coordinate-pow z j a b modulus) a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x i a b modulus))
     (z (quotient-coordinate-pow z j a b modulus)) (w x))
    (:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x i a b modulus)) (z x)
     (w (quotient-coordinate-pow z j a b modulus)))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow z j a b modulus)) (z x))
    (:instance quotient-coordinate-pow-successor (base x) (n i))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow x i a b modulus)) (z x)))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-monomial-times-z-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul
     (quotient-coordinate-pow x i a b modulus)
     (quotient-coordinate-pow z j a b modulus) a b modulus)
    z a b modulus)
   (quotient-coordinate-mul
    (quotient-coordinate-pow x i a b modulus)
    (quotient-coordinate-pow z (+ 1 (nfix j)) a b modulus) a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x i a b modulus))
     (z (quotient-coordinate-pow z j a b modulus)) (w z))
    (:instance quotient-coordinate-pow-successor (base z) (n j))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow z j a b modulus)) (z z)))
   :in-theory (theory 'minimal-theory)))))

; The quintic repeats the bounded quartic architecture.  Coefficients remain
; opaque throughout distribution and branch normalization.
(local
 (defthm quotient-coordinate-quintic-outer-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-add t0
     (quotient-coordinate-add t1
      (quotient-coordinate-add t2
       (quotient-coordinate-add t3 t4 modulus) modulus) modulus) modulus)
    a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t0 a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t1 a b modulus)
     (quotient-coordinate-add
      (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t2 a b modulus)
      (quotient-coordinate-add
       (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t3 a b modulus)
       (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t4 a b modulus)
       modulus) modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t0)
     (w (quotient-coordinate-add t1
         (quotient-coordinate-add t2 (quotient-coordinate-add t3 t4 modulus) modulus) modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t1)
     (w (quotient-coordinate-add t2 (quotient-coordinate-add t3 t4 modulus) modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t2)
     (w (quotient-coordinate-add t3 t4 modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t3) (w t4)))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-quintic-left-endpoint-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
                            (quotient-coordinate-pow x 4 a b modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-pow x 5 a b modulus)
    (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus)
    modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-endpoint-distribution-local
     (term (quotient-coordinate-pow x 4 a b modulus)))
    (:instance quotient-coordinate-pow-successor (base x) (n 4))
    (:instance quotient-coordinate-mul-commutative
     (x z) (z (quotient-coordinate-pow x 4 a b modulus))))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))

(local
 (defthm quotient-coordinate-quintic-right-endpoint-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
                            (quotient-coordinate-pow z 4 a b modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus)
    (quotient-coordinate-pow z 5 a b modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-endpoint-distribution-local
     (term (quotient-coordinate-pow z 4 a b modulus)))
    (:instance quotient-coordinate-pow-successor (base z) (n 4)))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))

(local
 (defthm quotient-coordinate-quintic-x3z-times-x-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus)
    x a b modulus)
   (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x 3 a b modulus)) (z z) (w x))
    (:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x 3 a b modulus)) (z x) (w z))
    (:instance quotient-coordinate-mul-commutative (x z) (z x))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow x 3 a b modulus)) (z x))
    (:instance quotient-coordinate-pow-successor (base x) (n 3)))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))

(local
 (defthm quotient-coordinate-quintic-x3z-times-z-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus)
    z a b modulus)
   (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus)
                            (quotient-coordinate-pow z 2 a b modulus) a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x (quotient-coordinate-pow x 3 a b modulus)) (z z) (w z))
    (:instance quotient-coordinate-pow-two-normal-local (x z)))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-quintic-xz3-times-x-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus)
    x a b modulus)
   (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                            (quotient-coordinate-pow z 3 a b modulus) a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x x) (z (quotient-coordinate-pow z 3 a b modulus)) (w x))
    (:instance quotient-coordinate-mul-associative
     (x x) (z x) (w (quotient-coordinate-pow z 3 a b modulus)))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow z 3 a b modulus)) (z x))
    (:instance quotient-coordinate-pow-two-normal-local (x x)))
   :in-theory (theory 'minimal-theory)))))
(local
 (defthm quotient-coordinate-quintic-xz3-times-z-local
  (equal
   (quotient-coordinate-mul
    (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus)
    z a b modulus)
   (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-associative
     (x x) (z (quotient-coordinate-pow z 3 a b modulus)) (w z))
    (:instance quotient-coordinate-pow-successor (base z) (n 3))
    (:instance quotient-coordinate-mul-commutative
     (x (quotient-coordinate-pow z 3 a b modulus)) (z z)))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))

(local
 (defthm quotient-coordinate-quintic-first-middle-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 4
     (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 4
     (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus) modulus)
    (quotient-coordinate-nat-mul 4
     (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus)
                              (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local
     (n 4) (term (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus)))
    (:instance quotient-coordinate-quintic-x3z-times-x-local)
    (:instance quotient-coordinate-quintic-x3z-times-z-local))
   :in-theory (union-theories (theory 'minimal-theory) '(natp))))))

(local
 (defthm quotient-coordinate-quintic-center-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 6
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                              (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 6
     (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus)
                              (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
    (quotient-coordinate-nat-mul 6
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                              (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local
     (n 6) (term (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                                          (quotient-coordinate-pow z 2 a b modulus) a b modulus)))
    (:instance quotient-coordinate-monomial-times-x-local (i 2) (j 2))
    (:instance quotient-coordinate-monomial-times-z-local (i 2) (j 2)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))

(local
 (defthm quotient-coordinate-quintic-third-middle-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 4
     (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 4
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                              (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus)
    (quotient-coordinate-nat-mul 4
     (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local
     (n 4) (term (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus)))
    (:instance quotient-coordinate-quintic-xz3-times-x-local)
    (:instance quotient-coordinate-quintic-xz3-times-z-local))
   :in-theory (union-theories (theory 'minimal-theory) '(natp))))))

(local
 (defthm quotient-coordinate-quintic-expanded-local
  (equal
   (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 5 a b modulus)
   (let ((x4z (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus))
         (x3z2 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus))
         (x2z3 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus))
         (xz4 (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus)))
    (quotient-coordinate-add (quotient-coordinate-pow x 5 a b modulus)
     (quotient-coordinate-add x4z
      (quotient-coordinate-add (quotient-coordinate-nat-mul 4 x4z modulus)
       (quotient-coordinate-add (quotient-coordinate-nat-mul 4 x3z2 modulus)
        (quotient-coordinate-add (quotient-coordinate-nat-mul 6 x3z2 modulus)
         (quotient-coordinate-add (quotient-coordinate-nat-mul 6 x2z3 modulus)
          (quotient-coordinate-add (quotient-coordinate-nat-mul 4 x2z3 modulus)
           (quotient-coordinate-add (quotient-coordinate-nat-mul 4 xz4 modulus)
            (quotient-coordinate-add xz4 (quotient-coordinate-pow z 5 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus)))
  :rule-classes nil
  :hints (("Goal" :use
   ((:instance quotient-coordinate-pow-successor
     (base (quotient-coordinate-add x z modulus)) (n 4))
    (:instance quotient-coordinate-pow-four-of-add-local)
    (:instance quotient-coordinate-quintic-outer-local
     (t0 (quotient-coordinate-pow x 4 a b modulus))
     (t1 (quotient-coordinate-nat-mul 4 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) z a b modulus) modulus))
     (t2 (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus))
     (t3 (quotient-coordinate-nat-mul 4 (quotient-coordinate-mul x (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus))
     (t4 (quotient-coordinate-pow z 4 a b modulus)))
    (:instance quotient-coordinate-quintic-left-endpoint-local)
    (:instance quotient-coordinate-quintic-first-middle-local)
    (:instance quotient-coordinate-quintic-center-local)
    (:instance quotient-coordinate-quintic-third-middle-local)
    (:instance quotient-coordinate-quintic-right-endpoint-local))
   :in-theory (union-theories (theory 'minimal-theory)
    '(nfix quotient-coordinate-quintic-left-endpoint-local
      quotient-coordinate-quintic-first-middle-local
      quotient-coordinate-quintic-center-local
      quotient-coordinate-quintic-third-middle-local
      quotient-coordinate-quintic-right-endpoint-local
      quotient-coordinate-add-associative))))))

(local
 (defthm quotient-coordinate-collect-one-four-local
  (implies (quotient-coordinate-p term modulus)
   (equal
    (quotient-coordinate-add term
     (quotient-coordinate-add (quotient-coordinate-nat-mul 4 term modulus) tail modulus) modulus)
    (quotient-coordinate-add (quotient-coordinate-nat-mul 5 term modulus) tail modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-one-times-closed-local)
    (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 4)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local
 (defthm quotient-coordinate-collect-four-one-local
  (implies (quotient-coordinate-p term modulus)
   (equal
    (quotient-coordinate-add (quotient-coordinate-nat-mul 4 term modulus)
     (quotient-coordinate-add term tail modulus) modulus)
    (quotient-coordinate-add (quotient-coordinate-nat-mul 5 term modulus) tail modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-one-times-closed-local)
    (:instance quotient-coordinate-collect-adjacent-scalars-local (m 4) (n 1)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))

(local
 (defthm quotient-coordinate-pow-five-of-add-local
  (equal
   (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 5 a b modulus)
   (let ((x4z (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus))
         (x3z2 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus))
         (x2z3 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus))
         (xz4 (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus)))
    (quotient-coordinate-add (quotient-coordinate-pow x 5 a b modulus)
     (quotient-coordinate-add (quotient-coordinate-nat-mul 5 x4z modulus)
      (quotient-coordinate-add (quotient-coordinate-nat-mul 10 x3z2 modulus)
       (quotient-coordinate-add (quotient-coordinate-nat-mul 10 x2z3 modulus)
        (quotient-coordinate-add (quotient-coordinate-nat-mul 5 xz4 modulus)
                                 (quotient-coordinate-pow z 5 a b modulus) modulus) modulus) modulus) modulus) modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-quintic-expanded-local)
    (:instance quotient-coordinate-collect-one-four-local
     (term (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus))
     (tail (quotient-coordinate-add
       (quotient-coordinate-nat-mul 4 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
       (quotient-coordinate-add
        (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
        (quotient-coordinate-add
         (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus)
         (quotient-coordinate-add
          (quotient-coordinate-nat-mul 4 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus)
          (quotient-coordinate-add
           (quotient-coordinate-nat-mul 4 (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus)
           (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus)
                                    (quotient-coordinate-pow z 5 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus)))
    (:instance quotient-coordinate-collect-adjacent-scalars-local
     (m 4) (n 6)
     (term (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus))
     (tail (quotient-coordinate-add
       (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus)
       (quotient-coordinate-add
        (quotient-coordinate-nat-mul 4 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus)
        (quotient-coordinate-add
         (quotient-coordinate-nat-mul 4 (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus)
         (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus)
                                  (quotient-coordinate-pow z 5 a b modulus) modulus) modulus) modulus) modulus)))
    (:instance quotient-coordinate-collect-adjacent-scalars-local
     (m 6) (n 4)
     (term (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus))
     (tail (quotient-coordinate-add
       (quotient-coordinate-nat-mul 4 (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus)
       (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus)
                                (quotient-coordinate-pow z 5 a b modulus) modulus) modulus)))
    (:instance quotient-coordinate-collect-four-one-local
     (term (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus))
     (tail (quotient-coordinate-pow z 5 a b modulus)))
    (:instance quotient-coordinate-operations-closed (x (quotient-coordinate-pow x 4 a b modulus)) (z z))
    (:instance quotient-coordinate-operations-closed (x x) (z (quotient-coordinate-pow z 4 a b modulus))))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))

(local
 (defthm quotient-coordinate-scaled-monomial-branch-local
  (implies (natp n)
   (equal
    (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
     (quotient-coordinate-nat-mul n
      (quotient-coordinate-mul (quotient-coordinate-pow x i a b modulus)
                               (quotient-coordinate-pow z j a b modulus) a b modulus)
      modulus) a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-nat-mul n
      (quotient-coordinate-mul (quotient-coordinate-pow x (+ 1 (nfix i)) a b modulus)
                               (quotient-coordinate-pow z j a b modulus) a b modulus) modulus)
     (quotient-coordinate-nat-mul n
      (quotient-coordinate-mul (quotient-coordinate-pow x i a b modulus)
                               (quotient-coordinate-pow z (+ 1 (nfix j)) a b modulus) a b modulus) modulus)
     modulus)))
  :rule-classes nil
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local
     (term (quotient-coordinate-mul (quotient-coordinate-pow x i a b modulus)
                                    (quotient-coordinate-pow z j a b modulus) a b modulus)))
    (:instance quotient-coordinate-monomial-times-x-local)
    (:instance quotient-coordinate-monomial-times-z-local))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-sextic-outer-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-add t0
     (quotient-coordinate-add t1
      (quotient-coordinate-add t2
       (quotient-coordinate-add t3
        (quotient-coordinate-add t4 t5 modulus) modulus) modulus) modulus) modulus)
    a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t0 a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t1 a b modulus)
     (quotient-coordinate-add
      (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t2 a b modulus)
      (quotient-coordinate-add
       (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t3 a b modulus)
       (quotient-coordinate-add
        (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t4 a b modulus)
        (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t5 a b modulus)
        modulus) modulus) modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t0)
     (w (quotient-coordinate-add t1 (quotient-coordinate-add t2 (quotient-coordinate-add t3 (quotient-coordinate-add t4 t5 modulus) modulus) modulus) modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t1)
     (w (quotient-coordinate-add t2 (quotient-coordinate-add t3 (quotient-coordinate-add t4 t5 modulus) modulus) modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t2)
     (w (quotient-coordinate-add t3 (quotient-coordinate-add t4 t5 modulus) modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t3)
     (w (quotient-coordinate-add t4 t5 modulus)))
    (:instance quotient-coordinate-mul-left-distributive
     (x (quotient-coordinate-add x z modulus)) (z t4) (w t5)))
   :in-theory (theory 'minimal-theory)))))

(local
 (defthm quotient-coordinate-sextic-left-endpoint-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
                            (quotient-coordinate-pow x 5 a b modulus) a b modulus)
   (quotient-coordinate-add (quotient-coordinate-pow x 6 a b modulus)
    (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) z a b modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow x 5 a b modulus)))
    (:instance quotient-coordinate-pow-successor (base x) (n 5))
    (:instance quotient-coordinate-mul-commutative (x z) (z (quotient-coordinate-pow x 5 a b modulus))))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local
 (defthm quotient-coordinate-sextic-right-endpoint-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
                            (quotient-coordinate-pow z 5 a b modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-mul x (quotient-coordinate-pow z 5 a b modulus) a b modulus)
    (quotient-coordinate-pow z 6 a b modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow z 5 a b modulus)))
    (:instance quotient-coordinate-pow-successor (base z) (n 5)))
   :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))

(local
 (defthm quotient-coordinate-sextic-first-branch-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 5
     (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 5
     (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) z a b modulus) modulus)
    (quotient-coordinate-nat-mul 5
     (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus)
                              (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local
     (n 5) (term (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus)))
    (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 4 a b modulus)) (z z) (w x))
    (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 4 a b modulus)) (z x) (w z))
    (:instance quotient-coordinate-mul-commutative (x z) (z x))
    (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow x 4 a b modulus)) (z x))
    (:instance quotient-coordinate-pow-successor (base x) (n 4))
    (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 4 a b modulus)) (z z) (w z))
    (:instance quotient-coordinate-pow-two-normal-local (x z)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))

(local
 (defthm quotient-coordinate-sextic-second-branch-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 10
     (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus)
                              (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 10
     (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus)
                              (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus)
    (quotient-coordinate-nat-mul 10
     (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus)
                              (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-monomial-branch-local (n 10) (i 3) (j 2)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local
 (defthm quotient-coordinate-sextic-third-branch-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 10
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                              (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 10
     (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus)
                              (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus)
    (quotient-coordinate-nat-mul 10
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                              (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-monomial-branch-local (n 10) (i 2) (j 3)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))

(local
 (defthm quotient-coordinate-sextic-fourth-branch-local
  (equal
   (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
    (quotient-coordinate-nat-mul 5
     (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) a b modulus)
   (quotient-coordinate-add
    (quotient-coordinate-nat-mul 5
     (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus)
                              (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus)
    (quotient-coordinate-nat-mul 5
     (quotient-coordinate-mul x (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) modulus))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local
     (n 5) (term (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus)))
    (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 4 a b modulus)) (w x))
    (:instance quotient-coordinate-mul-associative (x x) (z x) (w (quotient-coordinate-pow z 4 a b modulus)))
    (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 4 a b modulus)) (z x))
    (:instance quotient-coordinate-pow-two-normal-local (x x))
    (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 4 a b modulus)) (w z))
    (:instance quotient-coordinate-pow-successor (base z) (n 4))
    (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 4 a b modulus)) (z z)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))

(local
 (defthm quotient-coordinate-sextic-expanded-local
  (equal
   (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 6 a b modulus)
   (let ((m1 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) z a b modulus))
         (m2 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus))
         (m3 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus))
         (m4 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus))
         (m5 (quotient-coordinate-mul x (quotient-coordinate-pow z 5 a b modulus) a b modulus)))
    (quotient-coordinate-add (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-add m1 (quotient-coordinate-add (quotient-coordinate-nat-mul 5 m1 modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 5 m2 modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 m2 modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 m3 modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 m3 modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 m4 modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 5 m4 modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 5 m5 modulus) (quotient-coordinate-add m5 (quotient-coordinate-pow z 6 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus)))
  :rule-classes nil
  :hints (("Goal" :use
   ((:instance quotient-coordinate-pow-successor (base (quotient-coordinate-add x z modulus)) (n 5))
    (:instance quotient-coordinate-pow-five-of-add-local)
    (:instance quotient-coordinate-sextic-outer-local
     (t0 (quotient-coordinate-pow x 5 a b modulus))
     (t1 (quotient-coordinate-nat-mul 5 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) z a b modulus) modulus))
     (t2 (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus))
     (t3 (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus))
     (t4 (quotient-coordinate-nat-mul 5 (quotient-coordinate-mul x (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus))
     (t5 (quotient-coordinate-pow z 5 a b modulus)))
    (:instance quotient-coordinate-sextic-left-endpoint-local)
    (:instance quotient-coordinate-sextic-first-branch-local)
    (:instance quotient-coordinate-sextic-second-branch-local)
    (:instance quotient-coordinate-sextic-third-branch-local)
    (:instance quotient-coordinate-sextic-fourth-branch-local)
    (:instance quotient-coordinate-sextic-right-endpoint-local))
   :in-theory (union-theories (theory 'minimal-theory)
    '(nfix quotient-coordinate-sextic-left-endpoint-local
      quotient-coordinate-sextic-first-branch-local
      quotient-coordinate-sextic-second-branch-local
      quotient-coordinate-sextic-third-branch-local
      quotient-coordinate-sextic-fourth-branch-local
      quotient-coordinate-sextic-right-endpoint-local
      quotient-coordinate-add-associative)))))
)
(local (defthm quotient-coordinate-collect-one-five-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add term (quotient-coordinate-add (quotient-coordinate-nat-mul 5 term modulus) tail modulus) modulus)
         (quotient-coordinate-add (quotient-coordinate-nat-mul 6 term modulus) tail modulus)))
 :hints (("Goal" :use ((:instance quotient-coordinate-one-times-closed-local)
                        (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 5)))
          :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local (defthm quotient-coordinate-collect-five-one-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add (quotient-coordinate-nat-mul 5 term modulus) (quotient-coordinate-add term tail modulus) modulus)
         (quotient-coordinate-add (quotient-coordinate-nat-mul 6 term modulus) tail modulus)))
 :hints (("Goal" :use ((:instance quotient-coordinate-one-times-closed-local)
                        (:instance quotient-coordinate-collect-adjacent-scalars-local (m 5) (n 1)))
          :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))

(local
 (defthm quotient-coordinate-pow-six-of-add-local
  (equal
   (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 6 a b modulus)
   (let ((m1 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) z a b modulus))
         (m2 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus))
         (m3 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus))
         (m4 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus))
         (m5 (quotient-coordinate-mul x (quotient-coordinate-pow z 5 a b modulus) a b modulus)))
    (quotient-coordinate-add (quotient-coordinate-pow x 6 a b modulus)
     (quotient-coordinate-add (quotient-coordinate-nat-mul 6 m1 modulus)
      (quotient-coordinate-add (quotient-coordinate-nat-mul 15 m2 modulus)
       (quotient-coordinate-add (quotient-coordinate-nat-mul 20 m3 modulus)
        (quotient-coordinate-add (quotient-coordinate-nat-mul 15 m4 modulus)
         (quotient-coordinate-add (quotient-coordinate-nat-mul 6 m5 modulus)
                                  (quotient-coordinate-pow z 6 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-sextic-expanded-local)
    (:instance quotient-coordinate-operations-closed (x (quotient-coordinate-pow x 5 a b modulus)) (z z))
    (:instance quotient-coordinate-operations-closed (x x) (z (quotient-coordinate-pow z 5 a b modulus))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(natp binary-+
      quotient-coordinate-collect-one-five-local
      quotient-coordinate-collect-adjacent-scalars-local
      quotient-coordinate-collect-five-one-local))))))


; Fixed septic row, decomposed into the same bounded stages as the sextic.
(local (defthm quotient-coordinate-septic-outer-local
 (equal
  (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
   (quotient-coordinate-add t0 (quotient-coordinate-add t1 (quotient-coordinate-add t2 (quotient-coordinate-add t3 (quotient-coordinate-add t4 (quotient-coordinate-add t5 t6 modulus) modulus) modulus) modulus) modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t0 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t1 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t2 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t3 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t4 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t5 a b modulus) (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t6 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(quotient-coordinate-mul-left-distributive))))))
(local (defthm quotient-coordinate-septic-left-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow x 6 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) z a b modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow x 6 a b modulus)))
   (:instance quotient-coordinate-pow-successor (base x) (n 6))
   (:instance quotient-coordinate-mul-commutative (x z) (z (quotient-coordinate-pow x 6 a b modulus))))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-septic-right-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 6 a b modulus) a b modulus) (quotient-coordinate-pow z 7 a b modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow z 6 a b modulus)))
   (:instance quotient-coordinate-pow-successor (base z) (n 6)))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-septic-branch-1-local
 (equal
  (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
   (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) z a b modulus) modulus) a b modulus)
  (quotient-coordinate-add
   (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) z a b modulus) modulus)
   (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local (n 6)
    (term (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) z a b modulus)))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 5 a b modulus)) (z z) (w x))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 5 a b modulus)) (z x) (w z))
   (:instance quotient-coordinate-mul-commutative (x z) (z x))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow x 5 a b modulus)) (z x))
   (:instance quotient-coordinate-pow-successor (base x) (n 5))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 5 a b modulus)) (z z) (w z))
   (:instance quotient-coordinate-pow-two-normal-local (x z)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-septic-branch-2-local
 (equal
  (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local
   (n 15) (i 4) (j 2)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-septic-branch-3-local
 (equal
  (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 20 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 20 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 20 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local
   (n 20) (i 3) (j 3)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-septic-branch-4-local
 (equal
  (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local
   (n 15) (i 2) (j 4)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-septic-branch-5-local
 (equal
  (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
   (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul x (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add
   (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus)
   (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul x (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use
   ((:instance quotient-coordinate-scaled-branch-transport-local (n 6)
    (term (quotient-coordinate-mul x (quotient-coordinate-pow z 5 a b modulus) a b modulus)))
   (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 5 a b modulus)) (w x))
   (:instance quotient-coordinate-mul-associative (x x) (z x) (w (quotient-coordinate-pow z 5 a b modulus)))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 5 a b modulus)) (z x))
   (:instance quotient-coordinate-pow-two-normal-local (x x))
   (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 5 a b modulus)) (w z))
   (:instance quotient-coordinate-pow-successor (base z) (n 5))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 5 a b modulus)) (z z)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-septic-expanded-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 7 a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) z a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 20 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 20 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul x (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 6 a b modulus) a b modulus) (quotient-coordinate-pow z 7 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance quotient-coordinate-pow-successor (base (quotient-coordinate-add x z modulus)) (n 6))
   (:instance quotient-coordinate-pow-six-of-add-local)
   (:instance quotient-coordinate-septic-outer-local
    (t0 (quotient-coordinate-pow x 6 a b modulus))
    (t1 (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) z a b modulus) modulus))
    (t2 (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus))
    (t3 (quotient-coordinate-nat-mul 20 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus))
    (t4 (quotient-coordinate-nat-mul 15 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus))
    (t5 (quotient-coordinate-nat-mul 6 (quotient-coordinate-mul x (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus))
    (t6 (quotient-coordinate-pow z 6 a b modulus))
   )
   (:instance quotient-coordinate-septic-left-endpoint-local)
   (:instance quotient-coordinate-septic-branch-1-local)
   (:instance quotient-coordinate-septic-branch-2-local)
   (:instance quotient-coordinate-septic-branch-3-local)
   (:instance quotient-coordinate-septic-branch-4-local)
   (:instance quotient-coordinate-septic-branch-5-local)
   (:instance quotient-coordinate-septic-right-endpoint-local))
  :in-theory (union-theories (theory 'minimal-theory)
   '(nfix quotient-coordinate-septic-left-endpoint-local
     quotient-coordinate-septic-branch-1-local quotient-coordinate-septic-branch-2-local
     quotient-coordinate-septic-branch-3-local quotient-coordinate-septic-branch-4-local
     quotient-coordinate-septic-branch-5-local quotient-coordinate-septic-right-endpoint-local
     quotient-coordinate-add-associative))))))
(local
 (defthm quotient-coordinate-collect-one-six-local
  (implies (quotient-coordinate-p term modulus)
   (equal
    (quotient-coordinate-add term
     (quotient-coordinate-add
      (quotient-coordinate-nat-mul 6 term modulus) tail modulus) modulus)
    (quotient-coordinate-add
     (quotient-coordinate-nat-mul 7 term modulus) tail modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-one-times-closed-local)
    (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 6)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))

(local
 (defthm quotient-coordinate-collect-six-one-local
  (implies (quotient-coordinate-p term modulus)
   (equal
    (quotient-coordinate-add
     (quotient-coordinate-nat-mul 6 term modulus)
     (quotient-coordinate-add term tail modulus) modulus)
    (quotient-coordinate-add
     (quotient-coordinate-nat-mul 7 term modulus) tail modulus)))
  :hints (("Goal" :use
   ((:instance quotient-coordinate-one-times-closed-local)
    (:instance quotient-coordinate-collect-adjacent-scalars-local (m 6) (n 1)))
   :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))

(local (defthm quotient-coordinate-pow-seven-of-add-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 7 a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul x (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-pow z 7 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-septic-expanded-local)
   (:instance quotient-coordinate-operations-closed
    (x (quotient-coordinate-pow x 6 a b modulus)) (z z))
   (:instance quotient-coordinate-operations-closed
    (x x) (z (quotient-coordinate-pow z 6 a b modulus))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(natp binary-+
     quotient-coordinate-collect-one-six-local
     quotient-coordinate-collect-adjacent-scalars-local
     quotient-coordinate-collect-six-one-local))))))


; Fixed octic row, decomposed into bounded distribution, branch, and collection stages.
(local (defthm quotient-coordinate-octic-outer-local
 (equal
  (quotient-coordinate-mul (quotient-coordinate-add x z modulus)
   (quotient-coordinate-add t0 (quotient-coordinate-add t1 (quotient-coordinate-add t2 (quotient-coordinate-add t3 (quotient-coordinate-add t4 (quotient-coordinate-add t5 (quotient-coordinate-add t6 t7 modulus) modulus) modulus) modulus) modulus) modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t0 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t1 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t2 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t3 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t4 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t5 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t6 a b modulus) (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t7 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(quotient-coordinate-mul-left-distributive))))))
(local (defthm quotient-coordinate-octic-left-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow x 7 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) z a b modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow x 7 a b modulus)))
   (:instance quotient-coordinate-pow-successor (base x) (n 7))
   (:instance quotient-coordinate-mul-commutative (x z) (z (quotient-coordinate-pow x 7 a b modulus))))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-octic-right-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 7 a b modulus) a b modulus) (quotient-coordinate-pow z 8 a b modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow z 7 a b modulus)))
   (:instance quotient-coordinate-pow-successor (base z) (n 7)))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-octic-branch-1-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) z a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) z a b modulus) modulus) (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-scaled-branch-transport-local (n 7) (term (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) z a b modulus)))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 6 a b modulus)) (z z) (w x))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 6 a b modulus)) (z x) (w z))
   (:instance quotient-coordinate-mul-commutative (x z) (z x))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow x 6 a b modulus)) (z x))
   (:instance quotient-coordinate-pow-successor (base x) (n 6))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 6 a b modulus)) (z z) (w z))
   (:instance quotient-coordinate-pow-two-normal-local (x z)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-octic-branch-2-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 21) (i 5) (j 2)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-octic-branch-3-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 35) (i 4) (j 3)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-octic-branch-4-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 35) (i 3) (j 4)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-octic-branch-5-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 21) (i 2) (j 5)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-octic-branch-6-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul x (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul x (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-scaled-branch-transport-local (n 7) (term (quotient-coordinate-mul x (quotient-coordinate-pow z 6 a b modulus) a b modulus)))
   (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 6 a b modulus)) (w x))
   (:instance quotient-coordinate-mul-associative (x x) (z x) (w (quotient-coordinate-pow z 6 a b modulus)))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 6 a b modulus)) (z x))
   (:instance quotient-coordinate-pow-two-normal-local (x x))
   (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 6 a b modulus)) (w z))
   (:instance quotient-coordinate-pow-successor (base z) (n 6))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 6 a b modulus)) (z z)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-octic-expanded-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 8 a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) z a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul x (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 7 a b modulus) a b modulus) (quotient-coordinate-pow z 8 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance quotient-coordinate-pow-successor (base (quotient-coordinate-add x z modulus)) (n 7))
   (:instance quotient-coordinate-pow-seven-of-add-local)
   (:instance quotient-coordinate-octic-outer-local
    (t0 (quotient-coordinate-pow x 7 a b modulus))
    (t1 (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) z a b modulus) modulus))
    (t2 (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus))
    (t3 (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus))
    (t4 (quotient-coordinate-nat-mul 35 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus))
    (t5 (quotient-coordinate-nat-mul 21 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus))
    (t6 (quotient-coordinate-nat-mul 7 (quotient-coordinate-mul x (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus))
    (t7 (quotient-coordinate-pow z 7 a b modulus))
   )
   (:instance quotient-coordinate-octic-left-endpoint-local)
   (:instance quotient-coordinate-octic-branch-1-local)
   (:instance quotient-coordinate-octic-branch-2-local)
   (:instance quotient-coordinate-octic-branch-3-local)
   (:instance quotient-coordinate-octic-branch-4-local)
   (:instance quotient-coordinate-octic-branch-5-local)
   (:instance quotient-coordinate-octic-branch-6-local)
   (:instance quotient-coordinate-octic-right-endpoint-local))
  :in-theory (union-theories (theory 'minimal-theory)
   '(nfix quotient-coordinate-octic-left-endpoint-local
     quotient-coordinate-octic-branch-1-local quotient-coordinate-octic-branch-2-local
     quotient-coordinate-octic-branch-3-local quotient-coordinate-octic-branch-4-local
     quotient-coordinate-octic-branch-5-local quotient-coordinate-octic-branch-6-local
     quotient-coordinate-octic-right-endpoint-local quotient-coordinate-add-associative))))))
(local (defthm quotient-coordinate-collect-one-seven-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add term (quotient-coordinate-add (quotient-coordinate-nat-mul 7 term modulus) tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 8 term modulus) tail modulus)))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-one-times-closed-local)
   (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 7)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local (defthm quotient-coordinate-collect-seven-one-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add (quotient-coordinate-nat-mul 7 term modulus) (quotient-coordinate-add term tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 8 term modulus) tail modulus)))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-one-times-closed-local)
   (:instance quotient-coordinate-collect-adjacent-scalars-local (m 7) (n 1)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local (defthm quotient-coordinate-pow-eight-of-add-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 8 a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 70 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul x (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-pow z 8 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-octic-expanded-local)
   (:instance quotient-coordinate-operations-closed (x (quotient-coordinate-pow x 7 a b modulus)) (z z))
   (:instance quotient-coordinate-operations-closed (x x) (z (quotient-coordinate-pow z 7 a b modulus))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(natp binary-+ quotient-coordinate-collect-one-seven-local
     quotient-coordinate-collect-adjacent-scalars-local
     quotient-coordinate-collect-seven-one-local))))))


; Fixed nonic row, decomposed into bounded distribution, branch, and collection stages.
(local (defthm quotient-coordinate-nonic-outer-local
 (equal
  (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-add t0 (quotient-coordinate-add t1 (quotient-coordinate-add t2 (quotient-coordinate-add t3 (quotient-coordinate-add t4 (quotient-coordinate-add t5 (quotient-coordinate-add t6 (quotient-coordinate-add t7 t8 modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t0 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t1 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t2 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t3 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t4 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t5 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t6 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t7 a b modulus) (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t8 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(quotient-coordinate-mul-left-distributive))))))
(local (defthm quotient-coordinate-nonic-left-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow x 8 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) z a b modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow x 8 a b modulus)))
   (:instance quotient-coordinate-pow-successor (base x) (n 8))
   (:instance quotient-coordinate-mul-commutative (x z) (z (quotient-coordinate-pow x 8 a b modulus))))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-nonic-right-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 8 a b modulus) a b modulus) (quotient-coordinate-pow z 9 a b modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow z 8 a b modulus)))
   (:instance quotient-coordinate-pow-successor (base z) (n 8)))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-nonic-branch-1-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) z a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) z a b modulus) modulus) (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-scaled-branch-transport-local (n 8) (term (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) z a b modulus)))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 7 a b modulus)) (z z) (w x))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 7 a b modulus)) (z x) (w z))
   (:instance quotient-coordinate-mul-commutative (x z) (z x))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow x 7 a b modulus)) (z x))
   (:instance quotient-coordinate-pow-successor (base x) (n 7))
   (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 7 a b modulus)) (z z) (w z))
   (:instance quotient-coordinate-pow-two-normal-local (x z)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-nonic-branch-2-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 28) (i 6) (j 2)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-nonic-branch-3-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 56) (i 5) (j 3)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-nonic-branch-4-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 70 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 70 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 70 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 70) (i 4) (j 4)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-nonic-branch-5-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 56) (i 3) (j 5)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-nonic-branch-6-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 28) (i 2) (j 6)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-nonic-branch-7-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul x (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul x (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-scaled-branch-transport-local (n 8) (term (quotient-coordinate-mul x (quotient-coordinate-pow z 7 a b modulus) a b modulus)))
   (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 7 a b modulus)) (w x))
   (:instance quotient-coordinate-mul-associative (x x) (z x) (w (quotient-coordinate-pow z 7 a b modulus)))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 7 a b modulus)) (z x))
   (:instance quotient-coordinate-pow-two-normal-local (x x))
   (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 7 a b modulus)) (w z))
   (:instance quotient-coordinate-pow-successor (base z) (n 7))
   (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 7 a b modulus)) (z z)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-nonic-expanded-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 9 a b modulus) (quotient-coordinate-add (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) z a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 70 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 70 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul x (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 8 a b modulus) a b modulus) (quotient-coordinate-pow z 9 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance quotient-coordinate-pow-successor (base (quotient-coordinate-add x z modulus)) (n 8))
   (:instance quotient-coordinate-pow-eight-of-add-local)
   (:instance quotient-coordinate-nonic-outer-local
    (t0 (quotient-coordinate-pow x 8 a b modulus))
    (t1 (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) z a b modulus) modulus))
    (t2 (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus))
    (t3 (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus))
    (t4 (quotient-coordinate-nat-mul 70 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus))
    (t5 (quotient-coordinate-nat-mul 56 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus))
    (t6 (quotient-coordinate-nat-mul 28 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus))
    (t7 (quotient-coordinate-nat-mul 8 (quotient-coordinate-mul x (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus))
    (t8 (quotient-coordinate-pow z 8 a b modulus))
   )
   (:instance quotient-coordinate-nonic-left-endpoint-local)
   (:instance quotient-coordinate-nonic-branch-1-local)
   (:instance quotient-coordinate-nonic-branch-2-local)
   (:instance quotient-coordinate-nonic-branch-3-local)
   (:instance quotient-coordinate-nonic-branch-4-local)
   (:instance quotient-coordinate-nonic-branch-5-local)
   (:instance quotient-coordinate-nonic-branch-6-local)
   (:instance quotient-coordinate-nonic-branch-7-local)
   (:instance quotient-coordinate-nonic-right-endpoint-local))
  :in-theory (union-theories (theory 'minimal-theory)
   '(nfix quotient-coordinate-nonic-left-endpoint-local
     quotient-coordinate-nonic-branch-1-local quotient-coordinate-nonic-branch-2-local
     quotient-coordinate-nonic-branch-3-local quotient-coordinate-nonic-branch-4-local
     quotient-coordinate-nonic-branch-5-local quotient-coordinate-nonic-branch-6-local
     quotient-coordinate-nonic-branch-7-local quotient-coordinate-nonic-right-endpoint-local
     quotient-coordinate-add-associative))))))
(local (defthm quotient-coordinate-collect-one-eight-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add term (quotient-coordinate-add (quotient-coordinate-nat-mul 8 term modulus) tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 9 term modulus) tail modulus)))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-one-times-closed-local)
   (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 8)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local (defthm quotient-coordinate-collect-eight-one-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add (quotient-coordinate-nat-mul 8 term modulus) (quotient-coordinate-add term tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 9 term modulus) tail modulus)))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-one-times-closed-local)
   (:instance quotient-coordinate-collect-adjacent-scalars-local (m 8) (n 1)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local (defthm quotient-coordinate-pow-nine-of-add-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 9 a b modulus) (quotient-coordinate-add (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul x (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-pow z 9 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :use
  ((:instance quotient-coordinate-nonic-expanded-local)
   (:instance quotient-coordinate-operations-closed (x (quotient-coordinate-pow x 8 a b modulus)) (z z))
   (:instance quotient-coordinate-operations-closed (x x) (z (quotient-coordinate-pow z 8 a b modulus))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(natp binary-+ quotient-coordinate-collect-one-eight-local
     quotient-coordinate-collect-adjacent-scalars-local
     quotient-coordinate-collect-eight-one-local))))))


; Fixed decic row, decomposed into bounded distribution, branch, and collection stages.
(local (defthm quotient-coordinate-decic-outer-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-add t0 (quotient-coordinate-add t1 (quotient-coordinate-add t2 (quotient-coordinate-add t3 (quotient-coordinate-add t4 (quotient-coordinate-add t5 (quotient-coordinate-add t6 (quotient-coordinate-add t7 (quotient-coordinate-add t8 t9 modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t0 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t1 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t2 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t3 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t4 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t5 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t6 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t7 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t8 a b modulus) (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t9 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(quotient-coordinate-mul-left-distributive))))))
(local (defthm quotient-coordinate-decic-left-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow x 9 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 10 a b modulus) (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) z a b modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow x 9 a b modulus)))
  (:instance quotient-coordinate-pow-successor (base x) (n 9))
  (:instance quotient-coordinate-mul-commutative (x z) (z (quotient-coordinate-pow x 9 a b modulus))))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-decic-right-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow z 9 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 9 a b modulus) a b modulus) (quotient-coordinate-pow z 10 a b modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow z 9 a b modulus)))
  (:instance quotient-coordinate-pow-successor (base z) (n 9)))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-decic-branch-1-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) z a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) z a b modulus) modulus) (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-branch-transport-local (n 9) (term (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) z a b modulus)))
  (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 8 a b modulus)) (z z) (w x))
  (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 8 a b modulus)) (z x) (w z))
  (:instance quotient-coordinate-mul-commutative (x z) (z x))
  (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow x 8 a b modulus)) (z x))
  (:instance quotient-coordinate-pow-successor (base x) (n 8))
  (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 8 a b modulus)) (z z) (w z))
  (:instance quotient-coordinate-pow-two-normal-local (x z))) :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-decic-branch-2-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 36) (i 7) (j 2)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-decic-branch-3-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 84) (i 6) (j 3)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-decic-branch-4-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 126) (i 5) (j 4)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-decic-branch-5-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 126) (i 4) (j 5)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-decic-branch-6-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 84) (i 3) (j 6)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-decic-branch-7-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 36) (i 2) (j 7)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-decic-branch-8-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul x (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul x (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-branch-transport-local (n 9) (term (quotient-coordinate-mul x (quotient-coordinate-pow z 8 a b modulus) a b modulus)))
  (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 8 a b modulus)) (w x))
  (:instance quotient-coordinate-mul-associative (x x) (z x) (w (quotient-coordinate-pow z 8 a b modulus)))
  (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 8 a b modulus)) (z x))
  (:instance quotient-coordinate-pow-two-normal-local (x x))
  (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 8 a b modulus)) (w z))
  (:instance quotient-coordinate-pow-successor (base z) (n 8))
  (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 8 a b modulus)) (z z))) :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-decic-expanded-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 10 a b modulus) (quotient-coordinate-add (quotient-coordinate-pow x 10 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) z a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul x (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 9 a b modulus) a b modulus) (quotient-coordinate-pow z 10 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :rule-classes nil
 :hints (("Goal" :use ((:instance quotient-coordinate-pow-successor (base (quotient-coordinate-add x z modulus)) (n 9))
  (:instance quotient-coordinate-pow-nine-of-add-local)
  (:instance quotient-coordinate-decic-outer-local
   (t0 (quotient-coordinate-pow x 9 a b modulus))
   (t1 (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) z a b modulus) modulus))
   (t2 (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus))
   (t3 (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus))
   (t4 (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus))
   (t5 (quotient-coordinate-nat-mul 126 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus))
   (t6 (quotient-coordinate-nat-mul 84 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus))
   (t7 (quotient-coordinate-nat-mul 36 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus))
   (t8 (quotient-coordinate-nat-mul 9 (quotient-coordinate-mul x (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus))
   (t9 (quotient-coordinate-pow z 9 a b modulus))
  )
  (:instance quotient-coordinate-decic-left-endpoint-local)
  (:instance quotient-coordinate-decic-branch-1-local)
  (:instance quotient-coordinate-decic-branch-2-local)
  (:instance quotient-coordinate-decic-branch-3-local)
  (:instance quotient-coordinate-decic-branch-4-local)
  (:instance quotient-coordinate-decic-branch-5-local)
  (:instance quotient-coordinate-decic-branch-6-local)
  (:instance quotient-coordinate-decic-branch-7-local)
  (:instance quotient-coordinate-decic-branch-8-local)
  (:instance quotient-coordinate-decic-right-endpoint-local)
) :in-theory (union-theories (theory 'minimal-theory)
 '(nfix quotient-coordinate-decic-left-endpoint-local quotient-coordinate-decic-branch-1-local quotient-coordinate-decic-branch-2-local quotient-coordinate-decic-branch-3-local quotient-coordinate-decic-branch-4-local quotient-coordinate-decic-branch-5-local quotient-coordinate-decic-branch-6-local quotient-coordinate-decic-branch-7-local quotient-coordinate-decic-branch-8-local quotient-coordinate-decic-right-endpoint-local quotient-coordinate-add-associative))))))
(local (defthm quotient-coordinate-collect-one-nine-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add term (quotient-coordinate-add (quotient-coordinate-nat-mul 9 term modulus) tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 10 term modulus) tail modulus)))
 :hints (("Goal" :use ((:instance quotient-coordinate-one-times-closed-local)
  (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 9)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local (defthm quotient-coordinate-collect-nine-one-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add (quotient-coordinate-nat-mul 9 term modulus) (quotient-coordinate-add term tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 10 term modulus) tail modulus)))
 :hints (("Goal" :use ((:instance quotient-coordinate-one-times-closed-local)
  (:instance quotient-coordinate-collect-adjacent-scalars-local (m 9) (n 1)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local (defthm quotient-coordinate-pow-ten-of-add-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 10 a b modulus) (quotient-coordinate-add (quotient-coordinate-pow x 10 a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 252 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul x (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) (quotient-coordinate-pow z 10 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-decic-expanded-local)
  (:instance quotient-coordinate-operations-closed (x (quotient-coordinate-pow x 9 a b modulus)) (z z))
  (:instance quotient-coordinate-operations-closed (x x) (z (quotient-coordinate-pow z 9 a b modulus))))
 :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+ quotient-coordinate-collect-one-nine-local quotient-coordinate-collect-adjacent-scalars-local quotient-coordinate-collect-nine-one-local))))))


; Fixed undecic row, decomposed into bounded distribution, branch, and collection stages.
(local (defthm quotient-coordinate-undecic-outer-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-add t0 (quotient-coordinate-add t1 (quotient-coordinate-add t2 (quotient-coordinate-add t3 (quotient-coordinate-add t4 (quotient-coordinate-add t5 (quotient-coordinate-add t6 (quotient-coordinate-add t7 (quotient-coordinate-add t8 (quotient-coordinate-add t9 t10 modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t0 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t1 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t2 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t3 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t4 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t5 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t6 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t7 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t8 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t9 a b modulus) (quotient-coordinate-mul (quotient-coordinate-add x z modulus) t10 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(quotient-coordinate-mul-left-distributive))))))
(local (defthm quotient-coordinate-undecic-left-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow x 10 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-pow x 11 a b modulus) (quotient-coordinate-mul (quotient-coordinate-pow x 10 a b modulus) z a b modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow x 10 a b modulus)))
  (:instance quotient-coordinate-pow-successor (base x) (n 10))
  (:instance quotient-coordinate-mul-commutative (x z) (z (quotient-coordinate-pow x 10 a b modulus))))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-undecic-right-endpoint-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-pow z 10 a b modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 10 a b modulus) a b modulus) (quotient-coordinate-pow z 11 a b modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-cubic-endpoint-distribution-local (term (quotient-coordinate-pow z 10 a b modulus)))
  (:instance quotient-coordinate-pow-successor (base z) (n 10)))
  :in-theory (union-theories (theory 'minimal-theory) '(nfix))))))
(local (defthm quotient-coordinate-undecic-branch-1-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) z a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 10 a b modulus) z a b modulus) modulus) (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-branch-transport-local (n 10) (term (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) z a b modulus)))
  (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 9 a b modulus)) (z z) (w x))
  (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 9 a b modulus)) (z x) (w z))
  (:instance quotient-coordinate-mul-commutative (x z) (z x))
  (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow x 9 a b modulus)) (z x))
  (:instance quotient-coordinate-pow-successor (base x) (n 9))
  (:instance quotient-coordinate-mul-associative (x (quotient-coordinate-pow x 9 a b modulus)) (z z) (w z))
  (:instance quotient-coordinate-pow-two-normal-local (x z))) :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-branch-2-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 45) (i 8) (j 2)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-branch-3-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 120) (i 7) (j 3)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-branch-4-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 210) (i 6) (j 4)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-branch-5-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 252 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 252 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 252 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 252) (i 5) (j 5)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-branch-6-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 210) (i 4) (j 6)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-branch-7-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 120) (i 3) (j 7)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-branch-8-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-monomial-branch-local (n 45) (i 2) (j 8)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-branch-9-local
 (equal (quotient-coordinate-mul (quotient-coordinate-add x z modulus) (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul x (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) a b modulus)
  (quotient-coordinate-add (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul x (quotient-coordinate-pow z 10 a b modulus) a b modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-scaled-branch-transport-local (n 10) (term (quotient-coordinate-mul x (quotient-coordinate-pow z 9 a b modulus) a b modulus)))
  (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 9 a b modulus)) (w x))
  (:instance quotient-coordinate-mul-associative (x x) (z x) (w (quotient-coordinate-pow z 9 a b modulus)))
  (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 9 a b modulus)) (z x))
  (:instance quotient-coordinate-pow-two-normal-local (x x))
  (:instance quotient-coordinate-mul-associative (x x) (z (quotient-coordinate-pow z 9 a b modulus)) (w z))
  (:instance quotient-coordinate-pow-successor (base z) (n 9))
  (:instance quotient-coordinate-mul-commutative (x (quotient-coordinate-pow z 9 a b modulus)) (z z))) :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))))))
(local (defthm quotient-coordinate-undecic-expanded-local
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 11 a b modulus) (quotient-coordinate-add (quotient-coordinate-pow x 11 a b modulus) (quotient-coordinate-add (quotient-coordinate-mul (quotient-coordinate-pow x 10 a b modulus) z a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 10 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 252 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 252 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul x (quotient-coordinate-pow z 10 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-mul x (quotient-coordinate-pow z 10 a b modulus) a b modulus) (quotient-coordinate-pow z 11 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :rule-classes nil
 :hints (("Goal" :use ((:instance quotient-coordinate-pow-successor (base (quotient-coordinate-add x z modulus)) (n 10))
  (:instance quotient-coordinate-pow-ten-of-add-local)
  (:instance quotient-coordinate-undecic-outer-local
   (t0 (quotient-coordinate-pow x 10 a b modulus))
   (t1 (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) z a b modulus) modulus))
   (t2 (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus))
   (t3 (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus))
   (t4 (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus))
   (t5 (quotient-coordinate-nat-mul 252 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus))
   (t6 (quotient-coordinate-nat-mul 210 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus))
   (t7 (quotient-coordinate-nat-mul 120 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus))
   (t8 (quotient-coordinate-nat-mul 45 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus))
   (t9 (quotient-coordinate-nat-mul 10 (quotient-coordinate-mul x (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus))
   (t10 (quotient-coordinate-pow z 10 a b modulus))
  )
  (:instance quotient-coordinate-undecic-left-endpoint-local)
  (:instance quotient-coordinate-undecic-branch-1-local)
  (:instance quotient-coordinate-undecic-branch-2-local)
  (:instance quotient-coordinate-undecic-branch-3-local)
  (:instance quotient-coordinate-undecic-branch-4-local)
  (:instance quotient-coordinate-undecic-branch-5-local)
  (:instance quotient-coordinate-undecic-branch-6-local)
  (:instance quotient-coordinate-undecic-branch-7-local)
  (:instance quotient-coordinate-undecic-branch-8-local)
  (:instance quotient-coordinate-undecic-branch-9-local)
  (:instance quotient-coordinate-undecic-right-endpoint-local)
) :in-theory (union-theories (theory 'minimal-theory)
 '(nfix quotient-coordinate-undecic-left-endpoint-local quotient-coordinate-undecic-branch-1-local quotient-coordinate-undecic-branch-2-local quotient-coordinate-undecic-branch-3-local quotient-coordinate-undecic-branch-4-local quotient-coordinate-undecic-branch-5-local quotient-coordinate-undecic-branch-6-local quotient-coordinate-undecic-branch-7-local quotient-coordinate-undecic-branch-8-local quotient-coordinate-undecic-branch-9-local quotient-coordinate-undecic-right-endpoint-local quotient-coordinate-add-associative))))))
(local (defthm quotient-coordinate-collect-one-ten-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add term (quotient-coordinate-add (quotient-coordinate-nat-mul 10 term modulus) tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 11 term modulus) tail modulus)))
 :hints (("Goal" :use ((:instance quotient-coordinate-one-times-closed-local)
  (:instance quotient-coordinate-collect-adjacent-scalars-local (m 1) (n 10)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(local (defthm quotient-coordinate-collect-ten-one-local
 (implies (quotient-coordinate-p term modulus)
  (equal (quotient-coordinate-add (quotient-coordinate-nat-mul 10 term modulus) (quotient-coordinate-add term tail modulus) modulus)
   (quotient-coordinate-add (quotient-coordinate-nat-mul 11 term modulus) tail modulus)))
 :hints (("Goal" :use ((:instance quotient-coordinate-one-times-closed-local)
  (:instance quotient-coordinate-collect-adjacent-scalars-local (m 10) (n 1)))
  :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+))))))
(defthm quotient-coordinate-pow-eleven-of-add-expanded
 (equal (quotient-coordinate-pow (quotient-coordinate-add x z modulus) 11 a b modulus) (quotient-coordinate-add (quotient-coordinate-pow x 11 a b modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 11 (quotient-coordinate-mul (quotient-coordinate-pow x 10 a b modulus) z a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 55 (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 165 (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 330 (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 462 (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 462 (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 330 (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 165 (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 55 (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 9 a b modulus) a b modulus) modulus) (quotient-coordinate-add (quotient-coordinate-nat-mul 11 (quotient-coordinate-mul x (quotient-coordinate-pow z 10 a b modulus) a b modulus) modulus) (quotient-coordinate-pow z 11 a b modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus) modulus))
 :hints (("Goal" :use ((:instance quotient-coordinate-undecic-expanded-local)
  (:instance quotient-coordinate-operations-closed (x (quotient-coordinate-pow x 10 a b modulus)) (z z))
  (:instance quotient-coordinate-operations-closed (x x) (z (quotient-coordinate-pow z 10 a b modulus))))
 :in-theory (union-theories (theory 'minimal-theory) '(natp binary-+ quotient-coordinate-collect-one-ten-local quotient-coordinate-collect-adjacent-scalars-local quotient-coordinate-collect-ten-one-local)))))


(defthm quotient-coordinate-nat-mul-of-eleven-multiple
  (implies (and (gfield::field-characteristic-p 11)
                (natp m))
   (equal (quotient-coordinate-nat-mul (* m 11) coordinate modulus)
          (quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-of-nat-mul
                            (n 11) (x coordinate))
                 (:instance quotient-coordinate-nat-mul-eleven-of-characteristic))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(natp quotient-coordinate-nat-mul-of-zero)))))

(defthm quotient-coordinate-pow-eleven-of-add
  (implies
   (gfield::field-characteristic-p 11)
   (equal
    (quotient-coordinate-pow (quotient-coordinate-add x z modulus)
                             11 a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-pow x 11 a b modulus)
     (quotient-coordinate-pow z 11 a b modulus) modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-eleven-of-add-expanded)
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 1)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 10 a b modulus) z a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 5)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 9 a b modulus) (quotient-coordinate-pow z 2 a b modulus) a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 15)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 8 a b modulus) (quotient-coordinate-pow z 3 a b modulus) a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 30)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 7 a b modulus) (quotient-coordinate-pow z 4 a b modulus) a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 42)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 6 a b modulus) (quotient-coordinate-pow z 5 a b modulus) a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 42)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 5 a b modulus) (quotient-coordinate-pow z 6 a b modulus) a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 30)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 4 a b modulus) (quotient-coordinate-pow z 7 a b modulus) a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 15)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 3 a b modulus) (quotient-coordinate-pow z 8 a b modulus) a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 5)
                  (coordinate (quotient-coordinate-mul (quotient-coordinate-pow x 2 a b modulus) (quotient-coordinate-pow z 9 a b modulus) a b modulus)))
                 (:instance quotient-coordinate-nat-mul-of-eleven-multiple (m 1)
                  (coordinate (quotient-coordinate-mul x (quotient-coordinate-pow z 10 a b modulus) a b modulus))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(natp binary-* quotient-coordinate-add-zero-left
                                        quotient-coordinate-fix-when-p
                                        quotient-coordinate-p-of-pow)))))

(defthm quotient-coordinate-frobenius-eleven-of-add
  (implies
   (gfield::field-characteristic-p 11)
   (equal
    (quotient-coordinate-frobenius
     (quotient-coordinate-add x z modulus) 11 a b modulus)
    (quotient-coordinate-add
     (quotient-coordinate-frobenius x 11 a b modulus)
     (quotient-coordinate-frobenius z 11 a b modulus) modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-pow-eleven-of-add))
           :expand ((quotient-coordinate-frobenius
                     (quotient-coordinate-add x z modulus) 11 a b modulus)
                    (quotient-coordinate-frobenius x 11 a b modulus)
                    (quotient-coordinate-frobenius z 11 a b modulus))
           :in-theory (theory 'minimal-theory))))
