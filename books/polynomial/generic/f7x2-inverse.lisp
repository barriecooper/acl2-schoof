(in-package "GPOLY")
(include-book "f7x2-representation")

; This presentation-specific operation is only an executable inverse candidate.
; Its zero branch implements the total GFIELD convention explicitly; the
; nonzero branch delegates once to the existing reduced F7 modular inverse.
(defun f7x2-inv (value)
  (declare (xargs :guard t))
  (let ((fixed-value (f7x2-fix value)))
    (if (equal fixed-value (f7x2-zero))
        (f7x2-zero)
      (f7-poly-modular-inverse fixed-value '(1 0 1)))))

(verify-guards f7x2-inv)

(defthm f7x2-inv-of-f7x2-fix
  (equal (f7x2-inv (f7x2-fix value))
         (f7x2-inv value))
  :hints (("Goal"
           :use ((:instance f7x2-fix-idempotent (x value)))
           :in-theory
           (union-theories '(f7x2-inv) (theory 'minimal-theory)))))

(defthm f7x2-inv-of-f7x2-zero
  (equal (f7x2-inv (f7x2-zero))
         (f7x2-zero))
  :hints (("Goal"
           :use f7x2-fix-of-zero
           :in-theory
           (union-theories '(f7x2-inv f7x2-zero)
                           (theory 'minimal-theory)))))

; Modular inverse is defined by one final remainder.  This concrete wrapper is
; deliberately independent of irreducibility and the fixed-modulus field
; encapsulate.
(defthm f7-remainder-of-poly-modular-inverse
  (equal (f7-poly-remainder
          (f7-poly-modular-inverse value modulus)
          modulus)
         (f7-poly-modular-inverse value modulus))
  :hints (("Goal"
           :use ((:instance f7-poly-remainder-idempotent
                            (dividend
                             (mv-nth
                              1
                              (f7-poly-monic-extended-euclidean-gcd
                               value modulus))))
                 (:instance f7-poly-modular-inverse-definition
                            (first value)))
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-fix-of-f7x2-inv
  (equal (f7x2-fix (f7x2-inv value))
         (f7x2-inv value))
  :hints (("Goal"
           :cases ((equal (f7x2-fix value) (f7x2-zero)))
           :use ((:instance f7-remainder-of-poly-modular-inverse
                            (value (f7x2-fix value))
                            (modulus '(1 0 1))))
           :in-theory
           (union-theories
            '(f7x2-fix f7x2-inv f7x2-fix-of-zero
              f7-poly-remainder-zero-dividend)
            (theory 'minimal-theory)))))

(defthm f7x2-element-p-of-f7x2-inv
  (f7x2-element-p (f7x2-inv value))
  :hints (("Goal"
           :use ((:instance f7x2-fix-of-f7x2-inv))
           :in-theory
           (union-theories '(f7x2-element-p)
                           (theory 'minimal-theory)))))

; These ground evaluations are execution evidence only.  Universal closure,
; fixing, zero, and nonzero inverse laws remain separate proof obligations.
(defthm f7x2-inv-execution-regressions
  (and
   (equal (f7x2-inv (f7x2-zero)) (f7x2-zero))
   (equal (f7x2-inv nil) nil)
   (equal (f7x2-inv '(1)) '(1))
   (equal (f7x2-inv '(3)) '(5))
   (equal (f7x2-inv '(0 1)) '(0 6))
   (equal (f7x2-inv '(1 1)) '(4 3))
   (equal (f7x2-inv '(1 1 0)) '(4 3))
   (equal (f7x2-inv '(8 1)) '(4 3))
   (equal (f7x2-inv '(1 1 . malformed-tail)) '(4 3)))
  :rule-classes nil)
