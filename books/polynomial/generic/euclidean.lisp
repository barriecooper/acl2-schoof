(in-package "GPOLY")
(include-book "reduction")

; This is the raw Euclidean computation.  In particular, its base case does
; not scale a nonzero result to make its leading coefficient one.
(defun poly-euclidean-gcd (first second)
  (declare
   (xargs
    :measure (len (normalize second))
    :hints
    (("Goal"
      :use ((:instance normalize-poly-remainder-strict-length-bound
                       (dividend first) (modulus second)))
      :in-theory (disable normalize poly-remainder)))))
  (if (consp (normalize second))
      (poly-euclidean-gcd second (poly-remainder first second))
    (normalize first)))

(defthm poly-euclidean-gcd-zero-second
  (implies (not (consp (normalize second)))
           (equal (poly-euclidean-gcd first second)
                  (normalize first)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-euclidean-gcd))))

(defthm poly-euclidean-gcd-nonzero-second
  (implies (consp (normalize second))
           (equal (poly-euclidean-gcd first second)
                  (poly-euclidean-gcd
                   second (poly-remainder first second))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-euclidean-gcd))))

(defthm poly-euclidean-gcd-canonical
  (canonical-polynomial-p (poly-euclidean-gcd first second))
  :hints
  (("Goal"
    :induct (poly-euclidean-gcd first second)
    :in-theory (e/d (poly-euclidean-gcd)
                    (normalize poly-remainder canonical-polynomial-p)))))

(defthm normalize-of-poly-euclidean-gcd
  (equal (normalize (poly-euclidean-gcd first second))
         (poly-euclidean-gcd first second))
  :hints
  (("Goal"
    :use ((:instance normalize-when-canonical
                     (xs (poly-euclidean-gcd first second)))
          (:instance poly-euclidean-gcd-canonical))
    :in-theory (disable poly-euclidean-gcd normalize
                        canonical-polynomial-p))))

; Focused executable structural regressions.  These use constant-first dense
; polynomials and retain the raw output selected by the Euclidean chain.
(defthm poly-euclidean-gcd-regression-both-nil
  (equal (poly-euclidean-gcd nil nil) nil))

(defthm poly-euclidean-gcd-regression-first-nonzero-second-nil
  (equal (poly-euclidean-gcd (polynomial-one) nil) (polynomial-one)))

(defthm poly-euclidean-gcd-regression-first-nil-second-nonzero
  (equal (poly-euclidean-gcd nil (polynomial-one)) (polynomial-one)))

(defthm poly-euclidean-gcd-regression-nonzero-constant
  (let ((constant (list (gfield::field-neg (gfield::field-one)))))
    (equal (poly-euclidean-gcd nil constant) constant)))

(defthm poly-euclidean-gcd-regression-linear-divisor
  (equal (poly-euclidean-gcd
          (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
          (monomial (gfield::field-one) 1))
         (polynomial-one)))

(defthm poly-euclidean-gcd-regression-higher-degree-divisor
  (equal (poly-euclidean-gcd
          nil
          (list (gfield::field-zero) (gfield::field-zero)
                (gfield::field-one)))
         (list (gfield::field-zero) (gfield::field-zero)
               (gfield::field-one))))

(defthm poly-euclidean-gcd-regression-equal-inputs
  (equal (poly-euclidean-gcd
          (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
          (poly-add (monomial (gfield::field-one) 1) (polynomial-one)))
         (poly-add (monomial (gfield::field-one) 1) (polynomial-one))))

(defthm poly-euclidean-gcd-regression-trailing-zeros
  (equal (poly-euclidean-gcd
          (list (gfield::field-one) (gfield::field-zero))
          (list (gfield::field-one) (gfield::field-one)
                (gfield::field-zero)))
         (polynomial-one)))

(defthm poly-euclidean-gcd-regression-noncanonical-coefficients
  (equal (poly-euclidean-gcd
          (list 'malformed-coefficient (gfield::field-zero)) nil)
         (normalize (list 'malformed-coefficient))))

(defthm poly-euclidean-gcd-regression-malformed-atoms
  (equal (poly-euclidean-gcd 'malformed-first 'malformed-second) nil))

(defthm poly-euclidean-gcd-regression-multi-step-chain
  (equal (poly-euclidean-gcd
          (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
          (monomial (gfield::field-one) 1))
         (polynomial-one)))

(defthm poly-euclidean-gcd-regression-output-canonical
  (canonical-polynomial-p
   (poly-euclidean-gcd
    (list (gfield::field-zero) (gfield::field-zero)
          (gfield::field-zero) (gfield::field-one))
    (list (gfield::field-one) (gfield::field-zero)
          (gfield::field-one)))))

(defthm poly-euclidean-gcd-regression-output-normalized
  (equal
   (normalize
    (poly-euclidean-gcd
     (list (gfield::field-zero) (gfield::field-zero)
           (gfield::field-zero) (gfield::field-one))
     (list (gfield::field-one) (gfield::field-zero)
           (gfield::field-one))))
   (poly-euclidean-gcd
    (list (gfield::field-zero) (gfield::field-zero)
          (gfield::field-zero) (gfield::field-one))
    (list (gfield::field-one) (gfield::field-zero)
          (gfield::field-one)))))
