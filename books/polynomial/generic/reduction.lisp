(in-package "GPOLY")
(include-book "division")

; Modular reduction is only the public remainder projection of recursive
; division.  POLY-DIVMOD owns normalization of both operands.
(defun poly-remainder (dividend modulus)
  (mv-let (quotient remainder)
    (poly-divmod dividend modulus)
    (declare (ignore quotient))
    remainder))

(defthm poly-remainder-is-divmod-remainder
  (equal (poly-remainder dividend modulus)
         (mv-nth 1 (poly-divmod dividend modulus)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-remainder))))

(defthm poly-remainder-canonical
  (canonical-polynomial-p (poly-remainder dividend modulus))
  :hints (("Goal"
           :use ((:instance poly-divmod-remainder-canonical
                            (f dividend) (g modulus)))
           :in-theory (enable poly-remainder))))

(defthm poly-remainder-of-normalize-dividend
  (equal (poly-remainder (normalize dividend) modulus)
         (poly-remainder dividend modulus))
  :hints (("Goal"
           :in-theory (e/d (poly-remainder poly-divmod)
                           (poly-divmod-core normalize)))))

(defthm poly-remainder-of-normalize-modulus
  (equal (poly-remainder dividend (normalize modulus))
         (poly-remainder dividend modulus))
  :hints (("Goal"
           :in-theory (e/d (poly-remainder poly-divmod)
                           (poly-divmod-core normalize)))))

(defthm poly-remainder-zero-modulus
  (equal (poly-remainder dividend nil) (normalize dividend))
  :hints (("Goal"
           :use ((:instance poly-divmod-zero-divisor (f dividend)))
           :in-theory (enable poly-remainder))))

(defthm poly-remainder-zero-normalized-modulus
  (implies (equal (normalize modulus) nil)
           (equal (poly-remainder dividend modulus)
                  (normalize dividend)))
  :hints (("Goal"
           :use ((:instance poly-remainder-of-normalize-modulus)
                 (:instance poly-remainder-zero-modulus))
           :in-theory (disable poly-remainder poly-divmod normalize
                               poly-remainder-of-normalize-modulus
                               poly-remainder-zero-modulus))))

(defthm poly-remainder-strict-degree-bound
  (implies (consp (normalize modulus))
           (or (equal (poly-remainder dividend modulus) nil)
               (< (poly-degree (poly-remainder dividend modulus))
                  (poly-degree (normalize modulus)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-final-remainder-degree-bound
                            (f dividend) (g modulus)))
           :in-theory (enable poly-remainder))))

(defthm poly-remainder-canonical-lower-degree
  (implies (and (canonical-polynomial-p dividend)
                (consp (normalize modulus))
                (< (poly-degree dividend)
                   (poly-degree (normalize modulus))))
           (equal (poly-remainder dividend modulus) dividend))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-larger-divisor
                            (f dividend) (g modulus))
                 (:instance normalize-when-canonical (xs dividend)))
           :in-theory (enable poly-remainder))))

(defthm poly-remainder-idempotent
  (equal (poly-remainder (poly-remainder dividend modulus) modulus)
         (poly-remainder dividend modulus))
  :hints (("Goal" :cases ((consp (normalize modulus))))
          ("Subgoal 2"
           :use ((:instance poly-remainder-zero-normalized-modulus)
                 (:instance poly-remainder-zero-normalized-modulus
                            (dividend (poly-remainder dividend modulus)))
                 (:instance normalize-when-canonical
                            (xs (poly-remainder dividend modulus)))
                 (:instance poly-remainder-canonical))
           :in-theory (disable poly-remainder normalize
                               canonical-polynomial-p))
          ("Subgoal 1"
           :use ((:instance poly-remainder-strict-degree-bound)
                 (:instance poly-remainder-canonical-lower-degree
                            (dividend (poly-remainder dividend modulus))))
           :in-theory (disable poly-remainder normalize poly-degree
                               canonical-polynomial-p))))

(verify-guards poly-remainder)

; Focused generic structural regressions use the constrained field itself. All
; expected values are structural constant-first polynomials; no evaluation
; equality or concrete reduction API is involved.
(defthm poly-remainder-regression-exact-divisibility
 (equal (poly-remainder (monomial (gfield::field-one) 2)
                        (polynomial-one))
        nil))
(defthm poly-remainder-regression-nonzero-lower-degree
 (equal (poly-remainder
         (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
         (monomial (gfield::field-one) 1))
        (polynomial-one)))
(defthm poly-remainder-regression-dividend-below-degree
 (equal (poly-remainder (polynomial-one)
                        (monomial (gfield::field-one) 1))
        (polynomial-one)))
(defthm poly-remainder-regression-zero-dividend (equal (poly-remainder nil (polynomial-one)) nil))
(defthm poly-remainder-regression-noncanonical-dividend-and-zero-modulus
 (equal (poly-remainder
         (list 'malformed-coefficient (gfield::field-one) (gfield::field-zero))
         nil)
        (list (gfield::field-fix 'malformed-coefficient)
              (gfield::field-one))))
(defthm poly-remainder-regression-noncanonical-modulus
 (equal (poly-remainder
         (polynomial-one)
         (list 'malformed-coefficient (gfield::field-one)
               (gfield::field-zero)))
        (polynomial-one)))
(defthm poly-remainder-regression-trailing-zeros
 (equal (poly-remainder
         (list (gfield::field-one) (gfield::field-zero)
               (gfield::field-zero))
         (list (gfield::field-one) (gfield::field-one)
               (gfield::field-zero)))
        (polynomial-one)))
(defthm poly-remainder-regression-malformed-dividend (equal (poly-remainder 'malformed-dividend (polynomial-one)) nil))
(defthm poly-remainder-regression-malformed-modulus
 (equal (poly-remainder (list (gfield::field-one) (gfield::field-zero))
                        'malformed-modulus)
        (polynomial-one)))
(defthm poly-remainder-regression-normalization-invariance
 (equal (poly-remainder
         (normalize (list (gfield::field-one) (gfield::field-zero)))
         (list (gfield::field-one) (gfield::field-one)
               (gfield::field-zero)))
        (poly-remainder
         (list (gfield::field-one) (gfield::field-zero))
         (normalize (list (gfield::field-one) (gfield::field-one)
                          (gfield::field-zero))))))
(defthm poly-remainder-regression-idempotence
 (equal (poly-remainder
         (poly-remainder
          (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
          (monomial (gfield::field-one) 1))
         (monomial (gfield::field-one) 1))
        (polynomial-one)))
(defthm poly-remainder-regression-strict-degree-decrease
 (< (poly-degree
     (poly-remainder
      (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
      (monomial (gfield::field-one) 1)))
    (poly-degree (monomial (gfield::field-one) 1))))
