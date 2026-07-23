(in-package "GPOLY")
(include-book "reduction")

; DIVISOR divides DIVIDEND exactly when canonical division leaves no
; remainder.  The divisor-first order is intentional.
(defun poly-divides-p (divisor dividend)
  (declare (xargs :guard t))
  (equal (poly-remainder dividend divisor) nil))

(defthm booleanp-of-poly-divides-p
  (booleanp (poly-divides-p divisor dividend))
  :hints (("Goal" :in-theory (enable poly-divides-p))))

(defthm poly-divides-p-iff-zero-remainder
  (iff (poly-divides-p divisor dividend)
       (equal (poly-remainder dividend divisor) nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable poly-divides-p))))

(defthm poly-divides-p-iff-congruent-zero
  (iff (poly-divides-p divisor dividend)
       (poly-congruent-p dividend nil divisor))
  :hints
  (("Goal"
    :use ((:instance poly-remainder-zero-normalized-modulus
                     (dividend nil) (modulus divisor)))
    :in-theory (enable poly-divides-p poly-congruent-p))))

(defthm poly-divides-p-of-normalize-divisor
  (equal (poly-divides-p (normalize divisor) dividend)
         (poly-divides-p divisor dividend))
  :hints (("Goal" :in-theory (enable poly-divides-p))))

(defthm poly-divides-p-of-normalize-dividend
  (equal (poly-divides-p divisor (normalize dividend))
         (poly-divides-p divisor dividend))
  :hints (("Goal" :in-theory (enable poly-divides-p))))

(defthm poly-divides-p-zero
  (poly-divides-p divisor nil)
  :hints (("Goal" :in-theory (enable poly-divides-p poly-remainder))))

(defthm poly-divides-p-self
  (poly-divides-p dividend dividend)
  :hints
  (("Goal" :cases ((consp (normalize dividend))))
   ("Subgoal 1"
    :use ((:instance poly-remainder-of-poly-add-modulus-multiple
                     (dividend nil) (multiplier (polynomial-one))
                     (modulus dividend))
          (:instance poly-remainder-of-normalize-dividend
                     (dividend dividend) (modulus dividend)))
    :in-theory (e/d (poly-divides-p)
                    (poly-remainder normalize poly-add poly-mul)))
   ("Subgoal 2"
    :use ((:instance poly-remainder-zero-normalized-modulus
                     (dividend dividend) (modulus dividend)))
    :in-theory (enable poly-divides-p))))

(defthm polynomial-one-divides-p
  (poly-divides-p (polynomial-one) dividend)
  :hints
  (("Goal"
    :use ((:instance poly-divmod-divisor-one-remainder (f dividend))
          (:instance poly-remainder-is-divmod-remainder
                     (dividend dividend) (modulus (polynomial-one))))
    :in-theory (enable poly-divides-p))))

(defthm nil-poly-divides-p-iff-normalize-nil
  (iff (poly-divides-p nil dividend)
       (equal (normalize dividend) nil))
  :hints (("Goal" :in-theory (enable poly-divides-p))))

(defthm poly-divides-p-of-poly-add
  (implies (and (poly-divides-p divisor left)
                (poly-divides-p divisor right))
           (poly-divides-p divisor (poly-add left right)))
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-of-poly-add
                     (left-a left) (left-b nil)
                     (right-a right) (right-b nil)
                     (modulus divisor)))
    :in-theory (disable poly-congruent-p poly-add))))

(defthm poly-divides-p-of-poly-neg
  (implies (poly-divides-p divisor dividend)
           (poly-divides-p divisor (poly-neg dividend)))
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-of-poly-neg
                     (left dividend) (right nil) (modulus divisor)))
    :in-theory (disable poly-congruent-p poly-neg))))

(defthm poly-divides-p-of-poly-sub
  (implies (and (poly-divides-p divisor left)
                (poly-divides-p divisor right))
           (poly-divides-p divisor (poly-sub left right)))
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-of-poly-sub
                     (left-a left) (left-b nil)
                     (right-a right) (right-b nil)
                     (modulus divisor)))
    :in-theory (disable poly-congruent-p poly-sub))))

(defthm poly-divides-p-of-poly-mul
  (implies (poly-divides-p divisor left)
           (poly-divides-p divisor (poly-mul left right)))
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-of-poly-mul-same-right
                     (left-a left) (left-b nil)
                     (right right) (modulus divisor)))
    :in-theory (disable poly-congruent-p poly-mul))))


; Reconstruction and congruence compatibility show that, modulo any divisor
; of SECOND, FIRST and its Euclidean remainder have the same representative.
(defthm poly-congruent-p-with-euclidean-remainder-when-divides-second
  (implies (poly-divides-p divisor second)
           (poly-congruent-p first (poly-remainder first second) divisor))
  :hints
  (("Goal"
    :use
    ((:instance poly-divmod-reconstruction (f first) (g second))
     (:instance poly-remainder-is-divmod-remainder
                (dividend first) (modulus second))
     (:instance poly-divides-p-iff-congruent-zero
                (divisor divisor) (dividend second))
     (:instance poly-congruent-p-of-normalize-left
                (left second) (right nil) (modulus divisor))
     (:instance poly-congruent-p-of-poly-mul-same-left
                (left (mv-nth 0 (poly-divmod first second)))
                (right-a (normalize second)) (right-b nil)
                (modulus divisor))
     (:instance poly-congruent-p-of-poly-add-same-right
                (left-a
                 (poly-mul (mv-nth 0 (poly-divmod first second))
                           (normalize second)))
                (left-b nil) (right (poly-remainder first second))
                (modulus divisor))
     (:instance poly-congruent-p-of-normalize-left
                (left first) (right (poly-remainder first second))
                (modulus divisor)))
    :in-theory
    (disable poly-divmod poly-remainder poly-divides-p poly-congruent-p
             normalize poly-add poly-mul))))

(defthm poly-divides-p-euclidean-remainder-iff
  (implies (poly-divides-p divisor second)
           (iff (poly-divides-p divisor first)
                (poly-divides-p divisor (poly-remainder first second))))
  :hints
  (("Goal"
    :use
    ((:instance poly-congruent-p-with-euclidean-remainder-when-divides-second)
     (:instance poly-divides-p-iff-congruent-zero
                (dividend first))
     (:instance poly-divides-p-iff-congruent-zero
                (dividend (poly-remainder first second)))
     (:instance poly-congruent-p-symmetric
                (x first) (y (poly-remainder first second))
                (modulus divisor))
     (:instance poly-congruent-p-transitive
                (x first) (y (poly-remainder first second)) (z nil)
                (modulus divisor))
     (:instance poly-congruent-p-transitive
                (x (poly-remainder first second)) (y first) (z nil)
                (modulus divisor)))
    :in-theory (disable poly-divides-p poly-congruent-p poly-remainder))))

(defthm poly-divides-p-euclidean-step-iff
  (iff
   (and (poly-divides-p divisor first)
        (poly-divides-p divisor second))
   (and (poly-divides-p divisor second)
        (poly-divides-p divisor (poly-remainder first second))))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-euclidean-remainder-iff))
    :in-theory (disable poly-divides-p poly-remainder))))

; Focused constant-first structural regressions for the total divisibility
; semantics, including malformed and normalized-zero inputs.
(defthm poly-divides-regression-nonzero-constant-divides-zero
  (poly-divides-p (list (gfield::field-one)) nil))

(defthm poly-divides-regression-one-divides-polynomial
  (poly-divides-p (polynomial-one)
                  (poly-add (monomial (gfield::field-one) 2)
                            (polynomial-one))))

(defthm poly-divides-regression-polynomial-divides-self
  (poly-divides-p
   (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
   (poly-add (monomial (gfield::field-one) 1) (polynomial-one))))

(defthm poly-divides-regression-trailing-zeros-divides-normalization
  (poly-divides-p
   (list (gfield::field-one) (gfield::field-zero))
   (normalize (list (gfield::field-one) (gfield::field-zero)))))

(defthm poly-divides-regression-noncanonical-divisor
  (poly-divides-p
   (list (gfield::field-one) (gfield::field-zero))
   (polynomial-one)))

(defthm poly-divides-regression-noncanonical-dividend
  (poly-divides-p
   (polynomial-one)
   (list (gfield::field-one) (gfield::field-zero))))

(defthm poly-divides-regression-malformed-atoms
  (poly-divides-p 'malformed-divisor 'malformed-dividend))

(defthm poly-divides-regression-zero-divides-zero
  (poly-divides-p nil nil))

(defthm poly-divides-regression-zero-does-not-divide-one
  (not (poly-divides-p nil (polynomial-one))))

(defthm poly-divides-regression-exact-nonconstant-multiple
  (let ((factor (poly-add (monomial (gfield::field-one) 1)
                          (polynomial-one))))
    (poly-divides-p factor
                    (poly-mul factor
                              (monomial (gfield::field-one) 1)))))

(defthm poly-divides-regression-nonzero-remainder
  (not (poly-divides-p (monomial (gfield::field-one) 1)
                       (polynomial-one))))

(defthm poly-divides-regression-forward-euclidean-step
  (let ((factor (poly-add (monomial (gfield::field-one) 1)
                          (polynomial-one))))
    (implies
     (and (poly-divides-p factor (poly-mul factor factor))
          (poly-divides-p factor factor))
     (and (poly-divides-p factor factor)
          (poly-divides-p factor
                          (poly-remainder (poly-mul factor factor)
                                          factor)))))
  :hints (("Goal" :use ((:instance poly-divides-p-euclidean-step-iff)))))

(defthm poly-divides-regression-reverse-euclidean-step
  (let ((factor (poly-add (monomial (gfield::field-one) 1)
                          (polynomial-one))))
    (implies
     (and (poly-divides-p factor factor)
          (poly-divides-p factor
                          (poly-remainder (poly-mul factor factor)
                                          factor)))
     (and (poly-divides-p factor (poly-mul factor factor))
          (poly-divides-p factor factor))))
  :hints (("Goal" :use ((:instance poly-divides-p-euclidean-step-iff)))))

(defthm poly-divides-regression-multi-step-looking
  (poly-divides-p
   (polynomial-one)
   (poly-remainder
    (poly-add (monomial (gfield::field-one) 3) (polynomial-one))
    (poly-add (monomial (gfield::field-one) 2) (polynomial-one)))))

(defthm poly-divides-regression-zero-normalized-second
  (equal
   (and (poly-divides-p (polynomial-one) (polynomial-one))
        (poly-divides-p (polynomial-one)
                        (list (gfield::field-zero))))
   (and (poly-divides-p (polynomial-one)
                        (list (gfield::field-zero)))
        (poly-divides-p
         (polynomial-one)
         (poly-remainder (polynomial-one)
                         (list (gfield::field-zero))))))
  :hints (("Goal" :use ((:instance poly-divides-p-euclidean-step-iff)))))

(defthm poly-divides-regression-zero-common-divisor
  (equal
   (and (poly-divides-p nil 'malformed-first)
        (poly-divides-p nil 'malformed-second))
   (and (poly-divides-p nil 'malformed-second)
        (poly-divides-p nil
                        (poly-remainder 'malformed-first
                                        'malformed-second))))
  :hints (("Goal" :use ((:instance poly-divides-p-euclidean-step-iff)))))

(defthm poly-divides-regression-normalization-both-positions
  (and
   (equal (poly-divides-p
           (normalize (list (gfield::field-one) (gfield::field-zero)))
           (polynomial-one))
          (poly-divides-p
           (list (gfield::field-one) (gfield::field-zero))
           (polynomial-one)))
   (equal (poly-divides-p
           (polynomial-one)
           (normalize (list (gfield::field-one) (gfield::field-zero))))
          (poly-divides-p
           (polynomial-one)
           (list (gfield::field-one) (gfield::field-zero))))))

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
