(in-package "GPOLY")

(include-book "quotient-coordinate")
(include-book "../field/characteristic")

; Transparent repeated addition in the quotient-coordinate ring.  Both the
; count and coordinate are totalized by NFIX and the public coordinate fixer.
(defun quotient-coordinate-nat-mul (n coordinate modulus)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n))
      (quotient-coordinate-zero modulus)
    (quotient-coordinate-add
     coordinate
     (quotient-coordinate-nat-mul
      (1- (nfix n)) coordinate modulus)
     modulus)))

(defthm quotient-coordinate-nat-mul-of-nfix
  (equal (quotient-coordinate-nat-mul (nfix n) coordinate modulus)
         (quotient-coordinate-nat-mul n coordinate modulus)))

(local
 (defthm quotient-coordinate-add-left-fix-for-natural-scalar
   (equal (quotient-coordinate-add
           (quotient-coordinate-fix left modulus) right modulus)
          (quotient-coordinate-add left right modulus))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-fix-idempotent
                             (coordinate left)))
            :in-theory (e/d (quotient-coordinate-add)
                            (quotient-coordinate-fix quotient-coordinate
                             poly-remainder poly-divmod))))))

(defthm quotient-coordinate-nat-mul-of-fix
  (equal (quotient-coordinate-nat-mul
          n (quotient-coordinate-fix coordinate modulus) modulus)
         (quotient-coordinate-nat-mul n coordinate modulus))
  :hints (("Goal" :induct (quotient-coordinate-nat-mul n coordinate modulus)
           :in-theory
           (e/d (quotient-coordinate-nat-mul)
                (quotient-coordinate-add quotient-coordinate-fix
                 quotient-coordinate poly-remainder poly-divmod)))))

(defthm quotient-coordinate-nat-mul-zero
  (equal (quotient-coordinate-nat-mul 0 coordinate modulus)
         (quotient-coordinate-zero modulus)))

(defthm quotient-coordinate-nat-mul-successor
  (implies (natp n)
           (equal (quotient-coordinate-nat-mul (+ 1 n) coordinate modulus)
                  (quotient-coordinate-add
                   coordinate
                   (quotient-coordinate-nat-mul n coordinate modulus)
                   modulus)))
  :hints (("Goal"
           :expand ((quotient-coordinate-nat-mul
                     (+ 1 n) coordinate modulus))
           :in-theory (e/d (nfix zp)
                           (quotient-coordinate-add
                            quotient-coordinate-fix)))))

(defthm quotient-coordinate-nat-mul-successor-total
  (equal (quotient-coordinate-nat-mul
          (+ 1 (nfix n)) coordinate modulus)
         (quotient-coordinate-add
          coordinate
          (quotient-coordinate-nat-mul n coordinate modulus)
          modulus))
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-successor
                            (n (nfix n)))
                 (:instance quotient-coordinate-nat-mul-of-nfix))
           :in-theory (disable quotient-coordinate-nat-mul
                               quotient-coordinate-nat-mul-successor))))

(defthm quotient-coordinate-p-of-nat-mul
  (quotient-coordinate-p
   (quotient-coordinate-nat-mul n coordinate modulus) modulus)
  :hints (("Goal" :induct (quotient-coordinate-nat-mul n coordinate modulus)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-nat-mul
              quotient-coordinate-operations-closed)))))

(defthm quotient-coordinate-nat-mul-of-zero
  (equal (quotient-coordinate-nat-mul
          n (quotient-coordinate-zero modulus) modulus)
         (quotient-coordinate-zero modulus))
  :hints (("Goal" :induct (quotient-coordinate-nat-mul
                            n (quotient-coordinate-zero modulus) modulus)
           :in-theory (enable quotient-coordinate-nat-mul))))

; This bridge is deliberately proved only from the public commutative-ring
; interface.  In particular the rank-two multiplication implementation and
; polynomial reduction stay disabled throughout the induction.
(local
 (defthm quotient-coordinate-add-swap-first-two-for-natural-scalar
   (equal (quotient-coordinate-add y
            (quotient-coordinate-add x z modulus) modulus)
          (quotient-coordinate-add x
            (quotient-coordinate-add y z modulus) modulus))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-add-associative
                             (x y) (z x) (w z))
                  (:instance quotient-coordinate-add-associative
                             (x x) (z y) (w z))
                  (:instance quotient-coordinate-add-commutative
                             (x y) (z x)))
            :in-theory (disable quotient-coordinate-add
                                quotient-coordinate-add-associative
                                quotient-coordinate-add-commutative)))))

(local
 (defthm quotient-coordinate-add-zero-left-of-natural-scalar
   (equal (quotient-coordinate-add
           (quotient-coordinate-zero modulus)
           (quotient-coordinate-nat-mul n x modulus) modulus)
          (quotient-coordinate-nat-mul n x modulus))
   :hints (("Goal"
            :use ((:instance quotient-coordinate-add-zero-left
                             (x (quotient-coordinate-nat-mul n x modulus)))
                  (:instance quotient-coordinate-fix-when-p
                             (coordinate (quotient-coordinate-nat-mul n x modulus)))
                  (:instance quotient-coordinate-p-of-nat-mul (coordinate x)))
            :in-theory (theory 'minimal-theory)))))

(defthm quotient-coordinate-nat-mul-of-sum
  (implies (and (natp m) (natp n))
   (equal (quotient-coordinate-nat-mul (+ m n) x modulus)
          (quotient-coordinate-add
           (quotient-coordinate-nat-mul m x modulus)
           (quotient-coordinate-nat-mul n x modulus) modulus)))
  :hints (("Goal" :induct (quotient-coordinate-nat-mul m x modulus)
           :in-theory (e/d (quotient-coordinate-nat-mul
                              quotient-coordinate-add-swap-first-two-for-natural-scalar
                              quotient-coordinate-add-zero-left-of-natural-scalar)
                             (quotient-coordinate-add quotient-coordinate-zero quotient-coordinate-fix
                              quotient-coordinate poly-remainder poly-divmod)))))

(defthm quotient-coordinate-nat-mul-is-unit-times
  (equal
   (quotient-coordinate-nat-mul n coordinate modulus)
   (quotient-coordinate-mul
    (quotient-coordinate-nat-mul
     n (quotient-coordinate-one modulus) modulus)
    coordinate a b modulus))
  :rule-classes nil
  :hints (("Goal"
           :induct (quotient-coordinate-nat-mul n coordinate modulus)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-nat-mul
              quotient-coordinate-add-left-fix-for-natural-scalar
              quotient-coordinate-mul-zero-left
              quotient-coordinate-mul-right-distributive
              quotient-coordinate-mul-one-left)))))

(local
 (defthm quotient-coordinate-zero-is-embedded-field-zero
   (equal (quotient-coordinate-zero modulus)
          (quotient-coordinate-embed (const (gfield::field-zero)) modulus))
   :hints (("Goal" :in-theory (enable const quotient-coordinate-zero
                                       quotient-coordinate-embed)))))

(local
 (defthm quotient-coordinate-one-is-embedded-field-one
   (equal (quotient-coordinate-one modulus)
          (quotient-coordinate-embed (const (gfield::field-one)) modulus))
   :hints (("Goal"
            :use ((:instance poly-remainder-idempotent
                             (dividend (polynomial-one))))
            :in-theory (e/d (quotient-coordinate-one
                             quotient-coordinate-embed
                             poly-reduced-one-definition
                             const-of-field-one)
                            (poly-remainder poly-divmod))))))

(defthm quotient-coordinate-nat-mul-of-one-is-embedded-field-nat-mul
  (equal
   (quotient-coordinate-nat-mul
    n (quotient-coordinate-one modulus) modulus)
   (quotient-coordinate-embed
    (const (gfield::field-nat-mul n (gfield::field-one))) modulus))
  :rule-classes nil
  :hints (("Goal"
           :induct (quotient-coordinate-nat-mul
                    n (quotient-coordinate-one modulus) modulus)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-nat-mul
              gfield::field-nat-mul
              quotient-coordinate-zero-is-embedded-field-zero
              quotient-coordinate-one-is-embedded-field-one
              quotient-coordinate-embed-add
              poly-add-of-consts
              gfield::field-fix-of-one)))))

(defthm quotient-coordinate-nat-mul-of-characteristic
  (implies
   (gfield::field-characteristic-p p)
   (equal
    (quotient-coordinate-nat-mul p coordinate modulus)
    (quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-is-unit-times
                            (n p))
                 (:instance
                 quotient-coordinate-nat-mul-of-one-is-embedded-field-nat-mul
                  (n p))
                 (:instance gfield::field-nat-mul-of-characteristic
                            (gfield::p p)
                            (gfield::x (gfield::field-one)))
                 (:instance quotient-coordinate-zero-is-embedded-field-zero)
                 (:instance quotient-coordinate-mul-zero-left
                            (z coordinate)))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-nat-mul-eleven-of-characteristic
  (implies
   (gfield::field-characteristic-p 11)
   (equal
    (quotient-coordinate-nat-mul 11 coordinate modulus)
    (quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-nat-mul-of-characteristic
                            (p 11)))
           :in-theory (theory 'minimal-theory))))

(verify-guards quotient-coordinate-nat-mul)
