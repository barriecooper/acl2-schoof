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

; The finite, executable half of the raw gcd specification.  Greatestness is
; stated separately as a theorem with an arbitrary common divisor.
(defun poly-common-divisor-p (candidate first second)
  (declare (xargs :guard t))
  (and (poly-divides-p candidate first)
       (poly-divides-p candidate second)))

(defthm booleanp-of-poly-common-divisor-p
  (booleanp (poly-common-divisor-p candidate first second))
  :hints (("Goal" :in-theory (enable poly-common-divisor-p))))

(defthm poly-common-divisor-p-implies-divides-first
  (implies (poly-common-divisor-p candidate first second)
           (poly-divides-p candidate first))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable poly-common-divisor-p))))

(defthm poly-common-divisor-p-implies-divides-second
  (implies (poly-common-divisor-p candidate first second)
           (poly-divides-p candidate second))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable poly-common-divisor-p))))

(defthm poly-common-divisor-p-of-normalize-candidate
  (equal (poly-common-divisor-p (normalize candidate) first second)
         (poly-common-divisor-p candidate first second))
  :hints (("Goal" :in-theory (enable poly-common-divisor-p))))

(defthm poly-common-divisor-p-of-normalize-first
  (equal (poly-common-divisor-p candidate (normalize first) second)
         (poly-common-divisor-p candidate first second))
  :hints (("Goal" :in-theory (enable poly-common-divisor-p))))

(defthm poly-common-divisor-p-of-normalize-second
  (equal (poly-common-divisor-p candidate first (normalize second))
         (poly-common-divisor-p candidate first second))
  :hints (("Goal" :in-theory (enable poly-common-divisor-p))))

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

(defthm normalize-divides-p-self
  (poly-divides-p (normalize dividend) dividend)
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-self)
          (:instance poly-divides-p-of-normalize-divisor
                     (divisor dividend)))
    :in-theory (disable poly-divides-p normalize))))

(defthm poly-divides-p-when-normalize-dividend-nil
  (implies (equal (normalize dividend) nil)
           (poly-divides-p divisor dividend))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-zero)
          (:instance poly-divides-p-of-normalize-dividend))
    :in-theory (disable poly-divides-p normalize))))

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

; Multiplying a known multiple by a constant proves the easy scaling
; direction.  The converse multiplies by the inverse constant and uses only
; the public constant/multiplication, nested-scaling, and normalization laws.
(local
 (defthm poly-divides-p-of-poly-scale-dividend-forward
   (implies (poly-divides-p divisor dividend)
            (poly-divides-p divisor (poly-scale scalar dividend)))
   :hints
   (("Goal"
     :use ((:instance poly-divides-p-of-poly-mul
                      (left dividend) (right (const scalar)))
           (:instance poly-mul-const-right (p dividend) (a scalar)))
     :in-theory (disable poly-divides-p poly-mul poly-scale
                         poly-divides-p-of-poly-mul
                         poly-mul-const-right)))))

(local
 (defthm poly-divides-p-of-poly-scale-dividend-backward
   (implies
    (and (not (equal (gfield::field-fix scalar)
                     (gfield::field-zero)))
         (poly-divides-p divisor (poly-scale scalar dividend)))
    (poly-divides-p divisor dividend))
   :hints
   (("Goal"
     :use ((:instance poly-divides-p-of-poly-mul
                      (left (poly-scale scalar dividend))
                      (right (const (gfield::field-inv scalar))))
           (:instance poly-mul-const-right
                      (p (poly-scale scalar dividend))
                      (a (gfield::field-inv scalar)))
           (:instance poly-scale-nested
                      (a (gfield::field-inv scalar))
                      (b scalar) (x dividend))
           (:instance gfield::field-mul-inverse-left (x scalar))
           (:instance poly-scale-by-one (x dividend))
           (:instance poly-divides-p-of-normalize-dividend
                      (divisor divisor) (dividend dividend)))
     :in-theory (disable poly-divides-p poly-mul poly-scale normalize
                         poly-divides-p-of-poly-mul poly-mul-const-right
                         poly-scale-by-one
                         poly-divides-p-of-normalize-dividend
                         gfield::field-mul-inverse-left)))))

(defthm poly-divides-p-of-poly-scale-dividend
  (implies
   (not (equal (gfield::field-fix scalar)
               (gfield::field-zero)))
   (equal (poly-divides-p divisor (poly-scale scalar dividend))
          (poly-divides-p divisor dividend)))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-of-poly-scale-dividend-forward)
          (:instance poly-divides-p-of-poly-scale-dividend-backward))
    :in-theory (disable poly-divides-p poly-scale))))

(defthm poly-divides-p-of-poly-scale-dividend-regression-boundaries
  (let ((one (polynomial-one))
        (minus-one (gfield::field-neg (gfield::field-one))))
    (and
     ; Literal and represented zero, malformed atoms, dotted tails, and
     ; trailing zero coefficients all pass through the total interfaces.
     (equal (poly-divides-p one (poly-scale (gfield::field-one) nil)) t)
     (equal (poly-divides-p one
                            (poly-scale minus-one
                                        (list (gfield::field-zero)
                                              (gfield::field-zero))))
            t)
     (equal (poly-divides-p one
                            (poly-scale minus-one 'malformed-dividend))
            t)
     (equal (poly-divides-p one
                            (poly-scale minus-one
                                        (cons (gfield::field-one)
                                              'malformed-tail)))
            t)
     (equal (poly-divides-p one
                            (poly-scale minus-one
                                        (list (gfield::field-one)
                                              (gfield::field-zero))))
            t)
     ; Coefficients are fixed before divisibility observes the dividend.
     (equal (poly-divides-p one
                            (poly-scale minus-one
                                        (list 'malformed-coefficient
                                              (gfield::field-one))))
            t)))
  :hints (("Goal" :use ((:instance polynomial-one-divides-p)))))

(defthm poly-divides-p-of-poly-scale-dividend-regression-positive-negative
  (let ((one (polynomial-one))
        (linear (list (gfield::field-one) (gfield::field-one))))
    (and
     (equal (poly-divides-p one
                            (poly-scale (gfield::field-neg
                                         (gfield::field-one))
                                        linear))
            t)
     (equal (poly-divides-p nil
                            (poly-scale (gfield::field-one) linear))
            nil)))
  :hints (("Goal" :in-theory (enable poly-divides-p))))

; This is the excluded case: zero scaling makes a nonzero dividend divisible
; by the zero polynomial, although that divisor did not divide the original.
(defthm poly-divides-p-of-poly-scale-dividend-regression-zero-counterexample
  (and (equal (poly-divides-p
               nil (poly-scale (gfield::field-zero) (polynomial-one)))
              t)
       (equal (poly-divides-p nil (polynomial-one)) nil))
  :hints (("Goal" :in-theory (enable poly-divides-p))))

(defthm poly-divides-p-of-poly-scale-dividend-regression-public-theorem
  (implies
   (not (equal (gfield::field-fix scalar) (gfield::field-zero)))
   (and
    (implies (poly-divides-p divisor dividend)
             (poly-divides-p divisor (poly-scale scalar dividend)))
    (implies (poly-divides-p divisor (poly-scale scalar dividend))
             (poly-divides-p divisor dividend))))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-of-poly-scale-dividend))
    :in-theory (disable poly-divides-p-of-poly-scale-dividend
                        poly-divides-p poly-scale))))


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

; Divisibility is transitive.  The proof stays at the public remainder
; interface: if MIDDLE divides DIVIDEND its remainder is zero, and the
; Euclidean-remainder equivalence transfers divisibility by DIVISOR.
(defthm poly-divides-p-transitive
  (implies (and (poly-divides-p divisor middle)
                (poly-divides-p middle dividend))
           (poly-divides-p divisor dividend))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-euclidean-remainder-iff
                     (divisor divisor) (first dividend) (second middle))
          (:instance poly-divides-p-iff-zero-remainder
                     (divisor middle) (dividend dividend))
          (:instance poly-divides-p-zero (divisor divisor)))
    :in-theory (disable poly-divides-p poly-remainder))))

; These two local facts expose the mutual-divisibility construction used by
; divisor scaling.  The reverse direction reuses the inverse reasoning already
; sealed inside dividend-scaling invariance.
(local
 (defthm poly-divisor-divides-p-poly-scale
   (poly-divides-p divisor (poly-scale scalar divisor))
   :hints
   (("Goal"
     :use ((:instance poly-divides-p-self (dividend divisor))
           (:instance poly-divides-p-of-poly-mul
                      (divisor divisor) (left divisor)
                      (right (const scalar)))
           (:instance poly-mul-const-right (p divisor) (a scalar)))
     :in-theory (disable poly-divides-p poly-mul poly-scale
                         poly-divides-p-self poly-divides-p-of-poly-mul
                         poly-mul-const-right)))))

(local
 (defthm poly-scale-divisor-divides-p-divisor
   (implies
    (not (equal (gfield::field-fix scalar)
                (gfield::field-zero)))
    (poly-divides-p (poly-scale scalar divisor) divisor))
   :hints
   (("Goal"
     :use ((:instance poly-divides-p-self
                      (dividend (poly-scale scalar divisor)))
           (:instance poly-divides-p-of-poly-scale-dividend
                      (scalar scalar)
                      (divisor (poly-scale scalar divisor))
                      (dividend divisor)))
     :in-theory (disable poly-divides-p poly-scale poly-divides-p-self
                         poly-divides-p-of-poly-scale-dividend)))))

(defthm poly-divides-p-of-poly-scale-divisor
  (implies
   (not (equal (gfield::field-fix scalar)
               (gfield::field-zero)))
   (equal
    (poly-divides-p (poly-scale scalar divisor) dividend)
    (poly-divides-p divisor dividend)))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-transitive
                     (divisor (poly-scale scalar divisor))
                     (middle divisor) (dividend dividend))
          (:instance poly-divides-p-transitive
                     (divisor divisor)
                     (middle (poly-scale scalar divisor))
                     (dividend dividend))
          (:instance poly-divisor-divides-p-poly-scale)
          (:instance poly-scale-divisor-divides-p-divisor))
    :in-theory (disable poly-divides-p poly-scale
                        poly-divides-p-transitive))))

; On the nonzero branch of monic normalization, its scaling scalar is a
; fixed nonzero field element.  Keep this bridge local: the public interface
; below states the divisibility consequence rather than exposing proof
; plumbing about the chosen scalar.
(local
 (defthm field-inv-of-poly-leading-coefficient-nonzero
   (implies
    (consp (normalize poly))
    (not
     (equal
      (gfield::field-fix
       (gfield::field-inv (poly-leading-coefficient poly)))
      (gfield::field-zero))))
   :hints
   (("Goal"
     :use ((:instance canonical-polynomial-p-of-normalize (xs poly))
           (:instance poly-leading-coefficient-nonzero-when-canonical-nonzero
                      (p (normalize poly)))
           (:instance poly-leading-coefficient-of-normalize (p poly))
           (:instance gfield::field-inv-nonzero
                      (x (poly-leading-coefficient poly))))
     :in-theory
     (disable normalize poly-leading-coefficient
              canonical-polynomial-p-of-normalize
              poly-leading-coefficient-nonzero-when-canonical-nonzero
              poly-leading-coefficient-of-normalize
              gfield::field-inv-nonzero)))))

(defthm poly-divides-p-of-poly-monic-normalize-dividend
  (equal
   (poly-divides-p divisor (poly-monic-normalize dividend))
   (poly-divides-p divisor dividend))
  :hints
  (("Goal"
    :cases ((consp (normalize dividend)))
    :use ((:instance field-inv-of-poly-leading-coefficient-nonzero
                     (poly dividend))
          (:instance poly-divides-p-of-poly-scale-dividend
                     (scalar
                      (gfield::field-inv
                       (poly-leading-coefficient dividend))))
          (:instance poly-divides-p-of-normalize-dividend))
    :in-theory
    (e/d (poly-monic-normalize)
         (poly-divides-p poly-scale normalize poly-leading-coefficient
          poly-divides-p-of-poly-scale-dividend
          poly-divides-p-of-normalize-dividend)))))

(defthm poly-divides-p-of-poly-monic-normalize-divisor
  (equal
   (poly-divides-p (poly-monic-normalize divisor) dividend)
   (poly-divides-p divisor dividend))
  :hints
  (("Goal"
    :cases ((consp (normalize divisor)))
    :use ((:instance field-inv-of-poly-leading-coefficient-nonzero
                     (poly divisor))
          (:instance poly-divides-p-of-poly-scale-divisor
                     (scalar
                      (gfield::field-inv
                       (poly-leading-coefficient divisor))))
          (:instance poly-divides-p-of-normalize-divisor))
    :in-theory
    (e/d (poly-monic-normalize)
         (poly-divides-p poly-scale normalize poly-leading-coefficient
          poly-divides-p-of-poly-scale-divisor
          poly-divides-p-of-normalize-divisor)))))

; Focused regressions exercise the public equivalences, rather than reopening
; remainder or scaling.  Together these cover normalized zero, malformed and
; dotted inputs, trailing zeroes, coefficient fixing, constants, and positive
; and negative divisibility outcomes in both argument positions.
(defthm poly-divides-p-of-poly-monic-normalize-regression-boundaries
  (let ((one (polynomial-one))
        (linear (list (gfield::field-one) (gfield::field-one)))
        (quadratic
         (list (gfield::field-neg (gfield::field-one))
               (gfield::field-one)
               (gfield::field-neg (gfield::field-one)))))
    (and
     (equal (poly-divides-p one (poly-monic-normalize nil))
            (poly-divides-p one nil))
     (equal (poly-divides-p (poly-monic-normalize nil) linear)
            (poly-divides-p nil linear))
     (equal (poly-divides-p one
                            (poly-monic-normalize
                             (list (gfield::field-zero))))
            (poly-divides-p one (list (gfield::field-zero))))
     (equal (poly-divides-p
             (poly-monic-normalize (list (gfield::field-zero))) linear)
            (poly-divides-p (list (gfield::field-zero)) linear))
     (equal (poly-divides-p one
                            (poly-monic-normalize 'malformed-dividend))
            (poly-divides-p one 'malformed-dividend))
     (equal (poly-divides-p
             (poly-monic-normalize 'malformed-divisor) linear)
            (poly-divides-p 'malformed-divisor linear))
     (equal (poly-divides-p
             one (poly-monic-normalize
                  (cons (gfield::field-one) 'malformed-tail)))
            (poly-divides-p
             one (cons (gfield::field-one) 'malformed-tail)))
     (equal (poly-divides-p
             (poly-monic-normalize
              (cons (gfield::field-one) 'malformed-tail)) linear)
            (poly-divides-p
             (cons (gfield::field-one) 'malformed-tail) linear))
     (equal (poly-divides-p
             linear
             (poly-monic-normalize
              (list (gfield::field-one) (gfield::field-one)
                    (gfield::field-zero))))
            (poly-divides-p
             linear
             (list (gfield::field-one) (gfield::field-one)
                   (gfield::field-zero))))
     (equal (poly-divides-p
             (poly-monic-normalize
              (list 'malformed-coefficient
                    (gfield::field-neg (gfield::field-one))))
             quadratic)
            (poly-divides-p
             (list 'malformed-coefficient
                   (gfield::field-neg (gfield::field-one)))
             quadratic))
     (equal (poly-divides-p linear (poly-monic-normalize quadratic))
            (poly-divides-p linear quadratic))
     (equal (poly-divides-p (poly-monic-normalize quadratic) linear)
            (poly-divides-p quadratic linear))))
  :hints
  (("Goal"
    :in-theory
    (disable poly-divides-p poly-monic-normalize))))

(defthm poly-divides-p-of-poly-monic-normalize-regression-public-theorems
  (and
   (implies (poly-divides-p divisor dividend)
            (poly-divides-p divisor
                            (poly-monic-normalize dividend)))
   (implies (poly-divides-p divisor (poly-monic-normalize dividend))
            (poly-divides-p divisor dividend))
   (implies (poly-divides-p divisor dividend)
            (poly-divides-p (poly-monic-normalize divisor)
                            dividend))
   (implies (poly-divides-p (poly-monic-normalize divisor) dividend)
            (poly-divides-p divisor dividend)))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-of-poly-monic-normalize-dividend)
          (:instance poly-divides-p-of-poly-monic-normalize-divisor))
    :in-theory
    (disable poly-divides-p poly-monic-normalize))))

(defthm poly-divides-p-of-poly-scale-divisor-regression-public-theorem
  (implies
   (not (equal (gfield::field-fix scalar) (gfield::field-zero)))
   (and
    (implies (poly-divides-p divisor dividend)
             (poly-divides-p (poly-scale scalar divisor) dividend))
    (implies (poly-divides-p (poly-scale scalar divisor) dividend)
             (poly-divides-p divisor dividend))))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-of-poly-scale-divisor))
    :in-theory (disable poly-divides-p-of-poly-scale-divisor
                        poly-divides-p poly-scale))))

; Exact total-semantics regressions exercise both implications through the
; public equivalence.  They cover represented zero, malformed/dotted inputs,
; trailing zeros, noncanonical coefficients, and scalars fixed by the field.
(defthm poly-divides-p-of-poly-scale-divisor-regression-boundaries
  (let ((one (polynomial-one)))
    (and
     (equal (poly-divides-p (poly-scale (gfield::field-one) nil) nil)
            (poly-divides-p nil nil))
     (equal (poly-divides-p
             (poly-scale (gfield::field-one)
                         (list (gfield::field-zero) (gfield::field-zero))) nil)
            (poly-divides-p
             (list (gfield::field-zero) (gfield::field-zero)) nil))
     (equal (poly-divides-p (poly-scale (gfield::field-one) 'malformed-divisor) nil)
            (poly-divides-p 'malformed-divisor nil))
     (equal (poly-divides-p
             (poly-scale (gfield::field-one)
                         (cons (gfield::field-one) 'malformed-tail)) one)
            (poly-divides-p
             (cons (gfield::field-one) 'malformed-tail) one))
     (equal (poly-divides-p
             (poly-scale (gfield::field-one)
                         (list (gfield::field-one) (gfield::field-zero))) one)
            (poly-divides-p
             (list (gfield::field-one) (gfield::field-zero)) one))
     (equal (poly-divides-p
             (poly-scale (gfield::field-one)
                         (list 'malformed-coefficient
                               (gfield::field-one))) one)
            (poly-divides-p
             (list 'malformed-coefficient (gfield::field-one)) one))))
  :hints
  (("Goal"
    :in-theory (e/d (poly-divides-p-of-poly-scale-divisor)
                    (poly-divides-p poly-scale)))))

(defthm poly-divides-p-of-poly-scale-divisor-regression-scalars-and-signs
  (let ((one (polynomial-one))
        (linear (list (gfield::field-one) (gfield::field-one))))
    (and
     (equal (poly-divides-p (poly-scale (gfield::field-one) one) linear)
            (poly-divides-p one linear))
     (equal (poly-divides-p
             (poly-scale (gfield::field-neg (gfield::field-one)) one) linear)
            (poly-divides-p one linear))
     (equal (poly-divides-p
             (poly-scale (gfield::field-neg (gfield::field-one)) nil) linear)
            (poly-divides-p nil linear))))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-of-poly-scale-divisor
                     (scalar (gfield::field-one))
                     (divisor (polynomial-one))
                     (dividend
                      (list (gfield::field-one) (gfield::field-one))))
          (:instance poly-divides-p-of-poly-scale-divisor
                     (scalar (gfield::field-neg (gfield::field-one)))
                     (divisor (polynomial-one))
                     (dividend
                      (list (gfield::field-one) (gfield::field-one))))
          (:instance poly-divides-p-of-poly-scale-divisor
                     (scalar (gfield::field-neg (gfield::field-one)))
                     (divisor nil)
                     (dividend
                      (list (gfield::field-one) (gfield::field-one)))))
    :in-theory (disable poly-divides-p-of-poly-scale-divisor
                        poly-divides-p poly-scale))))

; Zero scaling changes the nonzero divisor ONE into NIL.  ONE divides itself,
; while NIL does not divide ONE, so the nonzero hypothesis is necessary.
(defthm poly-divides-p-of-poly-scale-divisor-regression-zero-counterexample
  (and (equal (poly-divides-p
               (poly-scale (gfield::field-zero) (polynomial-one))
               (polynomial-one))
              nil)
       (equal (poly-divides-p (polynomial-one) (polynomial-one)) t))
  :hints (("Goal" :in-theory (enable poly-divides-p))))

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

; This public boundary is transparent post-processing of the existing raw
; Euclidean result, not a second gcd algorithm.  DEFUND keeps that composition
; available by its named equation without enabling it accidentally in later
; algebraic proofs.
(defund poly-monic-euclidean-gcd (first second)
  (poly-monic-normalize (poly-euclidean-gcd first second)))

(defthm poly-monic-euclidean-gcd-is-monic-normalize
  (equal (poly-monic-euclidean-gcd first second)
         (poly-monic-normalize (poly-euclidean-gcd first second)))
  :hints (("Goal" :in-theory (enable poly-monic-euclidean-gcd))))

(defthm normalize-of-poly-monic-euclidean-gcd
  (equal (normalize (poly-monic-euclidean-gcd first second))
         (poly-monic-euclidean-gcd first second))
  :hints
  (("Goal"
    :use ((:instance normalize-of-poly-monic-normalize
                     (poly (poly-euclidean-gcd first second))))
    :in-theory (e/d (poly-monic-euclidean-gcd)
                    (normalize poly-monic-normalize
                     normalize-of-poly-monic-normalize)))))

(defthm canonical-polynomial-p-of-poly-monic-euclidean-gcd
  (canonical-polynomial-p (poly-monic-euclidean-gcd first second))
  :hints
  (("Goal"
    :use ((:instance canonical-polynomial-p-of-poly-monic-normalize
                     (poly (poly-euclidean-gcd first second))))
    :in-theory (e/d (poly-monic-euclidean-gcd)
                    (poly-monic-normalize canonical-polynomial-p
                     canonical-polynomial-p-of-poly-monic-normalize)))))

(defthm consp-of-poly-monic-euclidean-gcd
  (equal (consp (poly-monic-euclidean-gcd first second))
         (consp (normalize (poly-euclidean-gcd first second))))
  :hints
  (("Goal"
    :use ((:instance consp-of-poly-monic-normalize
                     (poly (poly-euclidean-gcd first second))))
    :in-theory (e/d (poly-monic-euclidean-gcd)
                    (poly-monic-normalize normalize
                     consp-of-poly-monic-normalize)))))

(defthm poly-leading-coefficient-of-poly-monic-euclidean-gcd
  (equal (poly-leading-coefficient
          (poly-monic-euclidean-gcd first second))
         (if (consp (normalize (poly-euclidean-gcd first second)))
             (gfield::field-one)
           (gfield::field-zero)))
  :hints
  (("Goal"
    :use ((:instance poly-leading-coefficient-of-poly-monic-normalize
                     (poly (poly-euclidean-gcd first second))))
    :in-theory (e/d (poly-monic-euclidean-gcd)
                    (poly-monic-normalize normalize poly-leading-coefficient
                     poly-leading-coefficient-of-poly-monic-normalize)))))

; The conjunction is the natural invariant of the Euclidean recursion: the
; recursive result divides the new pair, and the public Euclidean-step theorem
; transports that fact back to the old pair.
(defthm poly-euclidean-gcd-divides-both-base
  (implies (not (consp (normalize second)))
           (and (poly-divides-p (poly-euclidean-gcd first second) first)
                (poly-divides-p (poly-euclidean-gcd first second) second)))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (e/d (poly-euclidean-gcd normalize-divides-p-self
          poly-divides-p-when-normalize-dividend-nil)
         (poly-remainder poly-divides-p normalize
          poly-divides-p-iff-congruent-zero
          poly-divides-p-of-normalize-divisor
          poly-divides-p-of-normalize-dividend
          poly-divides-p-self poly-divides-p-zero)))))

(defthm poly-euclidean-gcd-divides-both-step
  (implies
   (and (consp (normalize second))
        (poly-divides-p
         (poly-euclidean-gcd second (poly-remainder first second)) second)
        (poly-divides-p
         (poly-euclidean-gcd second (poly-remainder first second))
         (poly-remainder first second)))
   (and (poly-divides-p (poly-euclidean-gcd first second) first)
        (poly-divides-p (poly-euclidean-gcd first second) second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-euclidean-gcd-nonzero-second)
          (:instance poly-divides-p-euclidean-step-iff
                     (divisor
                      (poly-euclidean-gcd
                       second (poly-remainder first second)))))
    :in-theory
    (disable poly-euclidean-gcd poly-remainder poly-divides-p normalize
             poly-divides-p-euclidean-step-iff))))

(defthm poly-euclidean-gcd-divides-both
  (and
   (poly-divides-p (poly-euclidean-gcd first second) first)
   (poly-divides-p (poly-euclidean-gcd first second) second))
  :hints
  (("Goal"
    :induct (poly-euclidean-gcd first second)
    :in-theory (e/d (poly-euclidean-gcd)
                       (poly-remainder poly-divides-p normalize)))
   ("Subgoal *1/2"
    :use ((:instance poly-euclidean-gcd-divides-both-base))
    :in-theory (disable poly-euclidean-gcd poly-remainder poly-divides-p normalize))
   ("Subgoal *1/1"
    :use ((:instance poly-euclidean-gcd-divides-both-step))
    :in-theory (disable poly-euclidean-gcd poly-remainder poly-divides-p normalize))))

(defthm poly-euclidean-gcd-divides-first
  (poly-divides-p (poly-euclidean-gcd first second) first)
  :hints
  (("Goal"
    :use ((:instance poly-euclidean-gcd-divides-both))
    :in-theory (disable poly-euclidean-gcd-divides-both))))

(defthm poly-euclidean-gcd-divides-second
  (poly-divides-p (poly-euclidean-gcd first second) second)
  :hints
  (("Goal"
    :use ((:instance poly-euclidean-gcd-divides-both))
    :in-theory (disable poly-euclidean-gcd-divides-both))))

; Greatestness with respect to divisibility follows the computation itself.
; The arbitrary common divisor is transported to the recursive Euclidean pair
; by the public step equivalence; the base case only normalizes the dividend.
(defthm poly-common-divisor-divides-euclidean-gcd
  (implies
   (and (poly-divides-p divisor first)
        (poly-divides-p divisor second))
   (poly-divides-p divisor (poly-euclidean-gcd first second)))
  :hints
  (("Goal"
    :induct (poly-euclidean-gcd first second)
    :in-theory (e/d (poly-euclidean-gcd)
                    (poly-remainder poly-divides-p normalize)))
   ("Subgoal *1/2"
    :use ((:instance poly-euclidean-gcd-zero-second)
          (:instance poly-divides-p-of-normalize-dividend
                     (dividend first)))
    :in-theory (disable poly-euclidean-gcd poly-remainder poly-divides-p
                        normalize))
   ("Subgoal *1/1"
    :use ((:instance poly-euclidean-gcd-nonzero-second)
          (:instance poly-divides-p-euclidean-step-iff))
    :in-theory (disable poly-euclidean-gcd poly-remainder poly-divides-p
                        normalize poly-divides-p-euclidean-step-iff))))

; Public raw-gcd correctness interface.  These are packaging results only:
; each direction is an explicit instance of its independently certified
; mathematical theorem, with the recursive computation and division disabled.
(defthm poly-common-divisor-p-of-euclidean-gcd
  (poly-common-divisor-p
   (poly-euclidean-gcd first second) first second)
  :hints
  (("Goal"
    :use ((:instance poly-euclidean-gcd-divides-both))
    :in-theory (e/d (poly-common-divisor-p)
                    (poly-euclidean-gcd poly-divides-p
                     poly-euclidean-gcd-divides-both)))))

(defthm poly-common-divisor-p-greatestness
  (implies
   (poly-common-divisor-p divisor first second)
   (poly-divides-p divisor (poly-euclidean-gcd first second)))
  :hints
  (("Goal"
    :use ((:instance poly-common-divisor-divides-euclidean-gcd))
    :in-theory (e/d (poly-common-divisor-p)
                    (poly-euclidean-gcd poly-divides-p
                     poly-common-divisor-divides-euclidean-gcd)))))

(defthm poly-euclidean-gcd-raw-correct
  (and
   (poly-common-divisor-p
    (poly-euclidean-gcd first second) first second)
   (implies
    (poly-common-divisor-p divisor first second)
    (poly-divides-p divisor (poly-euclidean-gcd first second))))
  :hints
  (("Goal"
    :use ((:instance poly-common-divisor-p-of-euclidean-gcd)
          (:instance poly-common-divisor-p-greatestness))
    :in-theory (disable poly-common-divisor-p poly-euclidean-gcd
                        poly-divides-p
                        poly-common-divisor-p-of-euclidean-gcd
                        poly-common-divisor-p-greatestness))))

; Monic-gcd correctness is transported entirely through the public wrapper
; equation and the two unconditional monic-normalization divisibility laws.
; In particular, these proofs do not inspect either Euclidean recursion or
; the scaling used to implement monic normalization.
(defthm poly-monic-euclidean-gcd-divides-first
  (poly-divides-p (poly-monic-euclidean-gcd first second) first)
  :hints
  (("Goal"
    :use
    ((:instance poly-euclidean-gcd-divides-first)
     (:instance poly-divides-p-of-poly-monic-normalize-divisor
                (divisor (poly-euclidean-gcd first second))
                (dividend first)))
    :in-theory
    (enable poly-monic-euclidean-gcd-is-monic-normalize))))

(defthm poly-monic-euclidean-gcd-divides-second
  (poly-divides-p (poly-monic-euclidean-gcd first second) second)
  :hints
  (("Goal"
    :use
    ((:instance poly-euclidean-gcd-divides-second)
     (:instance poly-divides-p-of-poly-monic-normalize-divisor
                (divisor (poly-euclidean-gcd first second))
                (dividend second)))
    :in-theory
    (enable poly-monic-euclidean-gcd-is-monic-normalize))))

(defthm poly-common-divisor-p-of-poly-monic-euclidean-gcd
  (poly-common-divisor-p
   (poly-monic-euclidean-gcd first second) first second)
  :hints
  (("Goal"
    :use ((:instance poly-monic-euclidean-gcd-divides-first)
          (:instance poly-monic-euclidean-gcd-divides-second))
    :in-theory
    (e/d (poly-common-divisor-p)
         (poly-divides-p poly-monic-euclidean-gcd
          poly-monic-euclidean-gcd-divides-first
          poly-monic-euclidean-gcd-divides-second)))))

(defthm poly-divides-p-of-poly-monic-euclidean-gcd
  (implies
   (poly-common-divisor-p common first second)
   (poly-divides-p common
                   (poly-monic-euclidean-gcd first second)))
  :hints
  (("Goal"
    :use
    ((:instance poly-common-divisor-p-greatestness (divisor common))
     (:instance poly-divides-p-of-poly-monic-normalize-dividend
                (divisor common)
                (dividend (poly-euclidean-gcd first second))))
    :in-theory
    (enable poly-monic-euclidean-gcd-is-monic-normalize))))

(defthm poly-monic-euclidean-gcd-correct
  (and
   (poly-common-divisor-p
    (poly-monic-euclidean-gcd first second) first second)
   (implies
    (poly-common-divisor-p common first second)
    (poly-divides-p common
                    (poly-monic-euclidean-gcd first second))))
  :hints
  (("Goal"
    :use
    ((:instance poly-common-divisor-p-of-poly-monic-euclidean-gcd)
     (:instance poly-divides-p-of-poly-monic-euclidean-gcd))
    :in-theory
    (disable poly-common-divisor-p poly-divides-p
             poly-monic-euclidean-gcd
             poly-common-divisor-p-of-poly-monic-euclidean-gcd
             poly-divides-p-of-poly-monic-euclidean-gcd))))

; Exact structural regressions for the public specification.  They retain
; normalization boundaries and raw, possibly non-monic, Euclidean outputs.
(defthm poly-common-divisor-p-regression-boundaries
  (and
   (equal (poly-common-divisor-p nil nil nil) t)
   (equal (poly-common-divisor-p
           nil (list (gfield::field-zero))
           (list (gfield::field-zero) (gfield::field-zero)))
          t)
   (equal (poly-common-divisor-p nil nil (polynomial-one)) nil)
   (equal (poly-common-divisor-p
           (polynomial-one) 'malformed-first
           (list 'malformed-coefficient (gfield::field-zero)))
          t)
   (equal (poly-common-divisor-p
           (polynomial-one)
           (list (gfield::field-one) (gfield::field-zero))
           (list (gfield::field-one) (gfield::field-one)
                 (gfield::field-zero)))
          t))
  :hints (("Goal" :in-theory
           (disable poly-divides-p-euclidean-remainder-iff))))

(defthm poly-common-divisor-p-regression-visible-factor
  (let ((factor (poly-add (monomial (gfield::field-one) 1)
                          (polynomial-one))))
    (and
     (equal (poly-common-divisor-p
             factor factor (poly-mul factor factor))
            t)
     (equal (poly-common-divisor-p
             (list (gfield::field-neg (gfield::field-one)))
             (list (gfield::field-neg (gfield::field-one))) nil)
            t)))
  :hints (("Goal" :in-theory
           (disable poly-divides-p-euclidean-remainder-iff))))

(defthm poly-common-divisor-p-regression-normalization
  (equal
   (poly-common-divisor-p
    (normalize (list (gfield::field-one) (gfield::field-zero)))
    (normalize (list (gfield::field-one) (gfield::field-zero)))
    (normalize (list (gfield::field-one) (gfield::field-one)
                     (gfield::field-zero))))
   (poly-common-divisor-p
    (list (gfield::field-one) (gfield::field-zero))
    (list (gfield::field-one) (gfield::field-zero))
    (list (gfield::field-one) (gfield::field-one)
          (gfield::field-zero))))
  :hints
  (("Goal"
    :use
    ((:instance poly-common-divisor-p-of-normalize-candidate
                (candidate
                 (list (gfield::field-one) (gfield::field-zero)))
                (first
                 (normalize
                  (list (gfield::field-one) (gfield::field-zero))))
                (second
                 (normalize
                  (list (gfield::field-one) (gfield::field-one)
                        (gfield::field-zero)))))
     (:instance poly-common-divisor-p-of-normalize-first
                (candidate
                 (list (gfield::field-one) (gfield::field-zero)))
                (first
                 (list (gfield::field-one) (gfield::field-zero)))
                (second
                 (normalize
                  (list (gfield::field-one) (gfield::field-one)
                        (gfield::field-zero)))))
     (:instance poly-common-divisor-p-of-normalize-second
                (candidate
                 (list (gfield::field-one) (gfield::field-zero)))
                (first
                 (list (gfield::field-one) (gfield::field-zero)))
                (second
                 (list (gfield::field-one) (gfield::field-one)
                       (gfield::field-zero)))))
    :in-theory
    (disable normalize poly-common-divisor-p poly-divides-p
             poly-common-divisor-p-of-normalize-candidate
             poly-common-divisor-p-of-normalize-first
             poly-common-divisor-p-of-normalize-second))))

; Preserve and exercise the exact raw negative-unit gcd representative.  The
; divisor theorem scales it for divisibility only; it does not normalize it.
(defthm poly-divides-p-of-poly-scale-divisor-regression-raw-negative-unit-gcd
  (let* ((negative-one
          (list (gfield::field-neg (gfield::field-one))))
         (raw-gcd (poly-euclidean-gcd nil negative-one)))
    (and
     (equal raw-gcd negative-one)
     (equal (poly-divides-p
             (poly-scale (gfield::field-neg (gfield::field-one)) raw-gcd)
             negative-one)
            (poly-divides-p raw-gcd negative-one))))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-of-poly-scale-divisor
                     (scalar (gfield::field-neg (gfield::field-one)))
                     (divisor
                      (poly-euclidean-gcd
                       nil (list (gfield::field-neg
                                  (gfield::field-one)))))
                     (dividend
                      (list (gfield::field-neg (gfield::field-one))))))
    :in-theory (e/d (poly-euclidean-gcd)
                    (poly-divides-p-of-poly-scale-divisor
                     poly-divides-p poly-scale)))))

(defthm poly-common-divisor-p-regression-raw-gcd
  (let ((negative-one (list (gfield::field-neg (gfield::field-one)))))
    (and
     (equal (poly-common-divisor-p
             (poly-euclidean-gcd nil negative-one) nil negative-one)
            t)
     (equal (poly-divides-p
             (polynomial-one) (poly-euclidean-gcd nil negative-one))
            t)
     (equal
      (poly-common-divisor-p
       (poly-euclidean-gcd
        (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
        (monomial (gfield::field-one) 1))
       (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
       (monomial (gfield::field-one) 1))
      t)))
  :hints
  (("Goal"
    :use
    ((:instance poly-common-divisor-p-of-euclidean-gcd
                (first nil)
                (second
                 (list (gfield::field-neg (gfield::field-one)))))
     (:instance poly-common-divisor-p-of-euclidean-gcd
                (first
                 (poly-add (monomial (gfield::field-one) 1)
                           (polynomial-one)))
                (second (monomial (gfield::field-one) 1)))
     (:instance poly-common-divisor-p-greatestness
                (divisor (polynomial-one))
                (first nil)
                (second
                 (list (gfield::field-neg (gfield::field-one))))))
    :in-theory
    (disable poly-euclidean-gcd-raw-correct
             poly-divides-p-iff-congruent-zero
             poly-divides-p-euclidean-remainder-iff))))

; Focused greatestness regressions use exact Boolean results.  Most are
; positive common-divisor examples; the zero/nonzero case intentionally checks
; that the implication is true because its common-divisor hypotheses are false.
(defthm poly-common-divisor-greatestness-regression-boundaries
  (and
   (equal (poly-divides-p nil (poly-euclidean-gcd nil nil)) t)
   (equal (poly-divides-p
           (polynomial-one)
           (poly-euclidean-gcd (polynomial-one) nil))
          t)
   (equal (poly-divides-p
           (polynomial-one)
           (poly-euclidean-gcd nil (polynomial-one)))
          t)
   (equal (poly-divides-p
           (polynomial-one)
           (poly-euclidean-gcd (polynomial-one) 'malformed-second))
          t)
   (equal (poly-divides-p
           (polynomial-one)
           (poly-euclidean-gcd 'malformed-first (polynomial-one)))
          t)
   (equal (poly-divides-p
           nil
           (poly-euclidean-gcd
            (list (gfield::field-zero)) 'malformed-second))
          t)
   (equal
    (implies
     (and (poly-divides-p nil (polynomial-one))
          (poly-divides-p nil (polynomial-one)))
     (poly-divides-p
      nil (poly-euclidean-gcd (polynomial-one) (polynomial-one))))
    t))
  :hints
  (("Goal"
    :use ((:instance poly-common-divisor-divides-euclidean-gcd
                     (divisor nil) (first nil) (second nil))
          (:instance poly-common-divisor-divides-euclidean-gcd
                     (divisor (polynomial-one))
                     (first (polynomial-one)) (second nil))
          (:instance poly-common-divisor-divides-euclidean-gcd
                     (divisor (polynomial-one))
                     (first nil) (second (polynomial-one)))))))

(defthm poly-common-divisor-greatestness-regression-positive
  (let ((one (polynomial-one))
        (negative-one (list (gfield::field-neg (gfield::field-one))))
        (factor (poly-add (monomial (gfield::field-one) 1)
                          (polynomial-one))))
    (and
     (equal (poly-divides-p
             one (poly-euclidean-gcd
                  (poly-add (monomial (gfield::field-one) 2) one)
                  (poly-add (monomial (gfield::field-one) 1) one)))
            t)
     (equal (poly-divides-p
             negative-one
             (poly-euclidean-gcd negative-one negative-one))
            t)
     (equal (poly-divides-p
             factor (poly-euclidean-gcd factor factor))
            t)
     (equal (poly-divides-p
             factor
             (poly-euclidean-gcd (poly-mul factor factor) factor))
            t)))
  :hints
  (("Goal"
    :use ((:instance poly-common-divisor-divides-euclidean-gcd
                     (divisor (polynomial-one))
                     (first (poly-add (monomial (gfield::field-one) 2)
                                      (polynomial-one)))
                     (second (poly-add (monomial (gfield::field-one) 1)
                                       (polynomial-one))))
          (:instance poly-common-divisor-divides-euclidean-gcd
                     (divisor
                      (list (gfield::field-neg (gfield::field-one))))
                     (first
                      (list (gfield::field-neg (gfield::field-one))))
                     (second
                      (list (gfield::field-neg (gfield::field-one)))))
          (:instance poly-common-divisor-divides-euclidean-gcd
                     (divisor
                      (poly-add (monomial (gfield::field-one) 1)
                                (polynomial-one)))
                     (first
                      (poly-add (monomial (gfield::field-one) 1)
                                (polynomial-one)))
                     (second
                      (poly-add (monomial (gfield::field-one) 1)
                                (polynomial-one))))
          (:instance poly-common-divisor-divides-euclidean-gcd
                     (divisor
                      (poly-add (monomial (gfield::field-one) 1)
                                (polynomial-one)))
                     (first
                      (poly-mul
                       (poly-add (monomial (gfield::field-one) 1)
                                 (polynomial-one))
                       (poly-add (monomial (gfield::field-one) 1)
                                 (polynomial-one))))
                     (second
                      (poly-add (monomial (gfield::field-one) 1)
                                (polynomial-one))))))))

(defthm poly-common-divisor-greatestness-regression-normalization
  (and
   (equal
    (poly-divides-p
     (polynomial-one)
     (poly-euclidean-gcd
      (list (gfield::field-one) (gfield::field-zero))
      (list (gfield::field-one) (gfield::field-one)
            (gfield::field-zero))))
    t)
   (equal
    (poly-divides-p
     nil
     (poly-euclidean-gcd
      (list (gfield::field-zero) (gfield::field-zero))
      (list (gfield::field-zero))))
    t)
   (equal
    (poly-divides-p
     (polynomial-one)
     (poly-euclidean-gcd
      (list 'malformed-coefficient (gfield::field-zero))
      (polynomial-one)))
    t))
  :hints
  (("Goal"
    :use ((:instance polynomial-one-divides-p
                     (dividend
                      (poly-euclidean-gcd
                       (list (gfield::field-one) (gfield::field-zero))
                       (list (gfield::field-one) (gfield::field-one)
                             (gfield::field-zero)))))
          (:instance polynomial-one-divides-p
                     (dividend
                      (poly-euclidean-gcd
                       (list 'malformed-coefficient (gfield::field-zero))
                       (polynomial-one))))))))

(defthm poly-common-divisor-greatestness-regression-raw-associates
  (let ((negative-one (list (gfield::field-neg (gfield::field-one))))
        (one (polynomial-one)))
    (and
     (equal (poly-euclidean-gcd nil negative-one) negative-one)
     (equal (poly-divides-p
             one (poly-euclidean-gcd nil negative-one))
            t)
     (equal (poly-divides-p
             negative-one
             (poly-euclidean-gcd one negative-one))
            t))))

; Correctness regressions exercise total inputs as well as a visibly non-monic
; raw answer.  The computation regressions below record further exact chains.
(defthm poly-euclidean-gcd-divides-regression-boundaries
  (and (poly-divides-p (poly-euclidean-gcd nil nil) nil)
       (poly-divides-p (poly-euclidean-gcd (polynomial-one) nil)
                       (polynomial-one))
       (poly-divides-p (poly-euclidean-gcd nil (polynomial-one)) nil)
       (poly-divides-p
        (poly-euclidean-gcd (polynomial-one) 'malformed-second)
        'malformed-second)
       (poly-divides-p
        (poly-euclidean-gcd 'malformed-first (polynomial-one))
        'malformed-first)))

(defthm poly-euclidean-gcd-divides-regression-negative-unit
  (let ((negative-one (list (gfield::field-neg (gfield::field-one)))))
    (and (equal (poly-euclidean-gcd nil negative-one) negative-one)
         (poly-divides-p (poly-euclidean-gcd nil negative-one) nil)
         (poly-divides-p (poly-euclidean-gcd nil negative-one)
                         negative-one))))

(defthm poly-divides-p-of-poly-scale-dividend-regression-raw-negative-unit-gcd
  (let* ((negative-one
          (list (gfield::field-neg (gfield::field-one))))
         (raw-gcd (poly-euclidean-gcd nil negative-one)))
    (and
     (equal raw-gcd negative-one)
     (equal (poly-divides-p
             (polynomial-one)
             (poly-scale (gfield::field-neg (gfield::field-one)) raw-gcd))
            (poly-divides-p (polynomial-one) raw-gcd))))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-of-poly-scale-dividend
                     (scalar (gfield::field-neg (gfield::field-one)))
                     (divisor (polynomial-one))
                     (dividend
                      (poly-euclidean-gcd
                       nil
                       (list (gfield::field-neg
                              (gfield::field-one)))))))
    :in-theory (disable poly-divides-p-of-poly-scale-dividend
                        poly-divides-p poly-scale))))

(defthm poly-leading-coefficient-scale-regression-raw-negative-unit-gcd
  (let ((negative-one (list (gfield::field-neg (gfield::field-one)))))
    (equal
     (poly-leading-coefficient
      (poly-scale (gfield::field-one)
                  (poly-euclidean-gcd nil negative-one)))
     (gfield::field-neg (gfield::field-one))))
  :hints
  (("Goal"
    :use ((:instance poly-leading-coefficient-of-poly-scale
                     (scalar (gfield::field-one))
                     (poly (poly-euclidean-gcd
                            nil
                            (list (gfield::field-neg
                                   (gfield::field-one)))))))
    :in-theory (disable poly-leading-coefficient-of-poly-scale
                        poly-scale poly-leading-coefficient))))

(defthm poly-monic-normalize-regression-raw-negative-unit-gcd
  (let ((negative-one (list (gfield::field-neg (gfield::field-one)))))
    (and
     (equal (poly-monic-normalize
             (poly-euclidean-gcd nil negative-one))
            (polynomial-one))
     (equal
      (poly-leading-coefficient
       (poly-monic-normalize
        (poly-euclidean-gcd nil negative-one)))
      (gfield::field-one))))
  :hints
  (("Goal"
    :use ((:instance poly-leading-coefficient-of-poly-monic-normalize
                     (poly
                      (poly-euclidean-gcd
                       nil
                       (list (gfield::field-neg
                              (gfield::field-one))))))
          (:instance poly-mul-const-left
                     (a (gfield::field-inv
                         (gfield::field-neg (gfield::field-one))))
                     (p (const (gfield::field-neg
                                (gfield::field-one)))))
          (:instance poly-mul-of-consts
                     (a (gfield::field-inv
                         (gfield::field-neg (gfield::field-one))))
                     (b (gfield::field-neg (gfield::field-one))))
          (:instance gfield::field-mul-inverse-left
                     (x (gfield::field-neg (gfield::field-one)))))
    :in-theory (e/d (poly-monic-normalize polynomial-one const)
                    (poly-euclidean-gcd poly-scale
                     poly-leading-coefficient
                     poly-mul-const-left poly-mul-of-consts
                     gfield::field-mul-inverse-left
                     poly-leading-coefficient-of-poly-monic-normalize)))))

; The raw negative-unit result above remains exact.  Monic normalization is
; applied explicitly here, once in each divisibility argument position.
(defthm poly-monic-normalize-divisibility-regression-raw-negative-unit-gcd
  (let* ((negative-one
          (list (gfield::field-neg (gfield::field-one))))
         (raw-gcd (poly-euclidean-gcd nil negative-one)))
    (and
     (equal raw-gcd negative-one)
     (equal (poly-divides-p (polynomial-one)
                            (poly-monic-normalize raw-gcd))
            (poly-divides-p (polynomial-one) raw-gcd))
     (equal (poly-divides-p (poly-monic-normalize raw-gcd) negative-one)
            (poly-divides-p raw-gcd negative-one))))
  :hints
  (("Goal"
    :use
    ((:instance poly-divides-p-of-poly-monic-normalize-dividend
                (divisor (polynomial-one))
                (dividend
                 (poly-euclidean-gcd
                  nil (list (gfield::field-neg (gfield::field-one))))))
     (:instance poly-divides-p-of-poly-monic-normalize-divisor
                (divisor
                 (poly-euclidean-gcd
                  nil (list (gfield::field-neg (gfield::field-one)))))
                (dividend
                 (list (gfield::field-neg (gfield::field-one))))))
    :in-theory
    (e/d (poly-euclidean-gcd)
         (poly-divides-p poly-monic-normalize
          poly-divides-p-of-poly-monic-normalize-dividend
          poly-divides-p-of-poly-monic-normalize-divisor)))))

(defthm poly-euclidean-gcd-divides-regression-noncanonical
  (let ((first (list (gfield::field-one) (gfield::field-zero)))
        (second (list (gfield::field-one) (gfield::field-one)
                      (gfield::field-zero))))
    (and (poly-divides-p (poly-euclidean-gcd first second) first)
         (poly-divides-p (poly-euclidean-gcd first second) second))))

(defthm poly-euclidean-gcd-divides-regression-corollaries
  (and
   (poly-divides-p
    (poly-euclidean-gcd
     (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
     (monomial (gfield::field-one) 1))
    (poly-add (monomial (gfield::field-one) 1) (polynomial-one)))
   (poly-divides-p
    (poly-euclidean-gcd
     (poly-add (monomial (gfield::field-one) 1) (polynomial-one))
     (monomial (gfield::field-one) 1))
    (monomial (gfield::field-one) 1))))

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

; Exact structural regressions for the monic boundary.  Constant-first order
; is visible throughout; malformed atoms and dotted tails inherit NORMALIZE's
; total semantics before the raw Euclidean computation is post-processed.
(defthm poly-monic-euclidean-gcd-regression-boundaries
  (let ((one (polynomial-one)))
    (and
     (equal (poly-monic-euclidean-gcd nil nil) nil)
     (equal (poly-monic-euclidean-gcd one nil) one)
     (equal (poly-monic-euclidean-gcd nil one) one)
     (equal (poly-monic-euclidean-gcd 'malformed-first
                                      'malformed-second)
            nil)
     (equal (poly-monic-euclidean-gcd
             (cons (gfield::field-one) 'malformed-tail) nil)
            one)
     (equal (poly-monic-euclidean-gcd
             (list (gfield::field-one) (gfield::field-zero)) nil)
            one)
     (equal (poly-monic-euclidean-gcd
             (list (gfield::field-zero) (gfield::field-zero)) nil)
            nil)
     (equal (poly-monic-euclidean-gcd
             (list 'malformed-coefficient (gfield::field-zero)) nil)
            (poly-monic-normalize
             (normalize (list 'malformed-coefficient))))
     (equal (poly-monic-euclidean-gcd (list (gfield::field-zero)) nil)
            nil)))
  :hints (("Goal" :in-theory (enable poly-monic-euclidean-gcd
                                      poly-euclidean-gcd))))

(defthm poly-monic-euclidean-gcd-regression-polynomials
  (let* ((one (polynomial-one))
         (linear (poly-add (monomial (gfield::field-one) 1) one))
         (quadratic (poly-mul linear linear)))
    (and
     (equal (poly-monic-euclidean-gcd linear linear) linear)
     (equal (poly-monic-euclidean-gcd quadratic linear) linear)
     (equal (poly-monic-euclidean-gcd linear one) one)
     (equal (poly-monic-euclidean-gcd
             linear (monomial (gfield::field-one) 1))
            one)
     (equal (poly-monic-euclidean-gcd nil quadratic) quadratic))))

; Keep the associate distinction explicit at the new boundary: the raw result
; is still negative one, while only the wrapper returns field one.
(defthm poly-monic-euclidean-gcd-regression-raw-negative-unit
  (let ((negative-one (list (gfield::field-neg (gfield::field-one)))))
    (and (equal (poly-euclidean-gcd nil negative-one) negative-one)
         (equal (poly-monic-euclidean-gcd nil negative-one)
                (polynomial-one))))
  :hints
  (("Goal"
    :use ((:instance poly-monic-normalize-regression-raw-negative-unit-gcd))
    :in-theory (e/d (poly-monic-euclidean-gcd)
                    (poly-euclidean-gcd poly-monic-normalize
                     poly-monic-normalize-regression-raw-negative-unit-gcd)))))

; Exact correctness regressions stay at the generic boundary.  They cover the
; total input shapes without evaluating or reopening the Euclidean algorithm.
(defthm poly-monic-euclidean-gcd-correctness-regression-boundaries
  (let ((one (polynomial-one))
        (zero-constant (list (gfield::field-zero)))
        (linear (list (gfield::field-one) (gfield::field-one)))
        (quadratic
         (list (gfield::field-one) (gfield::field-zero)
               (gfield::field-one))))
    (and
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd nil nil) nil nil)
            t)
     (equal (poly-divides-p (poly-monic-euclidean-gcd nil one) nil) t)
     (equal (poly-divides-p (poly-monic-euclidean-gcd nil one) one) t)
     (equal (poly-divides-p (poly-monic-euclidean-gcd one nil) one) t)
     (equal (poly-divides-p (poly-monic-euclidean-gcd one nil) nil) t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd
              'malformed-first 'malformed-second)
             'malformed-first 'malformed-second)
            t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd
              (cons (gfield::field-one) 'malformed-tail) linear)
             (cons (gfield::field-one) 'malformed-tail) linear)
            t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd
              (list (gfield::field-one) (gfield::field-zero))
              (list (gfield::field-one) (gfield::field-one)
                    (gfield::field-zero)))
             (list (gfield::field-one) (gfield::field-zero))
             (list (gfield::field-one) (gfield::field-one)
                   (gfield::field-zero)))
            t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd
              (list (gfield::field-zero) (gfield::field-zero))
              zero-constant)
             (list (gfield::field-zero) (gfield::field-zero))
             zero-constant)
            t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd
              (list 'malformed-coefficient (gfield::field-zero))
              (list (gfield::field-one)
                    'noncanonical-coefficient))
             (list 'malformed-coefficient (gfield::field-zero))
             (list (gfield::field-one)
                   'noncanonical-coefficient))
            t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd linear linear) linear linear)
            t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd quadratic linear)
             quadratic linear)
            t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd linear
                                       (list (gfield::field-zero)
                                             (gfield::field-one)))
             linear
             (list (gfield::field-zero) (gfield::field-one)))
            t)
     (equal (poly-common-divisor-p
             (poly-monic-euclidean-gcd quadratic quadratic)
             quadratic quadratic)
            t)))
  :hints
  (("Goal"
    :use
    ((:instance poly-common-divisor-p-of-poly-monic-euclidean-gcd
                (first nil) (second nil)))
    :in-theory
    (disable poly-common-divisor-p poly-divides-p
             poly-monic-euclidean-gcd
             poly-monic-euclidean-gcd-is-monic-normalize
             poly-monic-euclidean-gcd-regression-boundaries
             poly-monic-euclidean-gcd-regression-polynomials
             poly-monic-euclidean-gcd-regression-raw-negative-unit))))

(defthm poly-monic-euclidean-gcd-correctness-regression-greatestness
  (let* ((factor (list (gfield::field-one) (gfield::field-one)))
         (square (poly-mul factor factor)))
    (and
     ; A visible shared linear factor divides the monic wrapper.
     (implies (poly-common-divisor-p factor factor square)
              (equal (poly-divides-p
                      factor (poly-monic-euclidean-gcd factor square))
                     t))
     ; The public raw gcd is itself a chosen common divisor, so greatestness
     ; transports it directly into the monic representative.
     (equal (poly-divides-p
             (poly-euclidean-gcd factor square)
             (poly-monic-euclidean-gcd factor square))
            t)))
  :hints
  (("Goal"
    :use
    ((:instance poly-divides-p-of-poly-monic-euclidean-gcd
                (common (list (gfield::field-one)
                              (gfield::field-one)))
                (first (list (gfield::field-one)
                             (gfield::field-one)))
                (second
                 (poly-mul
                  (list (gfield::field-one) (gfield::field-one))
                  (list (gfield::field-one) (gfield::field-one)))))
     (:instance poly-common-divisor-p-of-euclidean-gcd
                (first (list (gfield::field-one)
                             (gfield::field-one)))
                (second
                 (poly-mul
                  (list (gfield::field-one) (gfield::field-one))
                  (list (gfield::field-one) (gfield::field-one)))))
     (:instance poly-divides-p-of-poly-monic-euclidean-gcd
                (common
                 (poly-euclidean-gcd
                  (list (gfield::field-one) (gfield::field-one))
                  (poly-mul
                   (list (gfield::field-one) (gfield::field-one))
                   (list (gfield::field-one) (gfield::field-one)))))
                (first (list (gfield::field-one)
                             (gfield::field-one)))
                (second
                 (poly-mul
                  (list (gfield::field-one) (gfield::field-one))
                  (list (gfield::field-one) (gfield::field-one))))))
    :in-theory
    (disable poly-common-divisor-p poly-divides-p
             poly-monic-euclidean-gcd poly-euclidean-gcd poly-mul
             poly-monic-euclidean-gcd-is-monic-normalize
             poly-divides-p-of-poly-monic-normalize-dividend
             poly-euclidean-gcd-raw-correct
             poly-monic-euclidean-gcd-correct
             poly-monic-euclidean-gcd-divides-first
             poly-monic-euclidean-gcd-divides-second
             poly-common-divisor-p-of-poly-monic-euclidean-gcd
             poly-divides-p-of-poly-monic-euclidean-gcd))))

; NIL is not a common divisor of a nonzero input; this exact negative check
; prevents an implication-only regression from accidentally admitting it.
(defthm poly-monic-euclidean-gcd-correctness-regression-not-common
  (equal (poly-common-divisor-p nil (polynomial-one) nil) nil)
  :hints
  (("Goal"
    :in-theory
    (e/d (poly-common-divisor-p)
         (poly-divides-p poly-remainder)))))

(defthm poly-monic-euclidean-gcd-correctness-regression-negative-unit
  (let* ((negative-one
          (list (gfield::field-neg (gfield::field-one))))
         (raw-gcd (poly-euclidean-gcd nil negative-one))
         (monic-gcd (poly-monic-euclidean-gcd nil negative-one)))
    (and
     (equal raw-gcd negative-one)
     (equal monic-gcd (polynomial-one))
     (equal (poly-divides-p monic-gcd nil) t)
     (equal (poly-divides-p monic-gcd negative-one) t)
     (equal (poly-divides-p raw-gcd nil) t)
     (equal (poly-divides-p raw-gcd negative-one) t)
     (equal (poly-divides-p (polynomial-one) monic-gcd) t)))
  :hints
  (("Goal"
    :use
    ((:instance poly-monic-euclidean-gcd-regression-raw-negative-unit)
     (:instance poly-monic-euclidean-gcd-divides-first
                (first nil)
                (second
                 (list (gfield::field-neg (gfield::field-one)))))
     (:instance poly-monic-euclidean-gcd-divides-second
                (first nil)
                (second
                 (list (gfield::field-neg (gfield::field-one)))))
     (:instance poly-euclidean-gcd-divides-first
                (first nil)
                (second
                 (list (gfield::field-neg (gfield::field-one)))))
     (:instance poly-euclidean-gcd-divides-second
                (first nil)
                (second
                 (list (gfield::field-neg (gfield::field-one)))))
     (:instance poly-divides-p-of-poly-monic-euclidean-gcd
                (common (polynomial-one))
                (first nil)
                (second
                 (list (gfield::field-neg (gfield::field-one))))))
    :in-theory
    (disable poly-divides-p poly-common-divisor-p
             poly-euclidean-gcd poly-monic-euclidean-gcd))))
