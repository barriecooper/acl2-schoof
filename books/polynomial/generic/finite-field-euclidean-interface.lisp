(in-package "GPOLY")

(include-book "finite-field-reduction")

; Divisor-first divisibility over the existing generated remainder operation.
(defun finite-field-poly-divides-p (divisor dividend)
  (declare (xargs :guard t))
  (equal (finite-field-poly-remainder dividend divisor) nil))

(defun finite-field-poly-common-divisor-p (candidate first second)
  (declare (xargs :guard t))
  (and (finite-field-poly-divides-p candidate first)
       (finite-field-poly-divides-p candidate second)))

(defthm booleanp-of-finite-field-poly-divides-p
  (booleanp (finite-field-poly-divides-p divisor dividend))
  :hints (("Goal" :in-theory (enable finite-field-poly-divides-p))))

(defthm finite-field-poly-divides-p-iff-zero-remainder
  (iff (finite-field-poly-divides-p divisor dividend)
       (equal (finite-field-poly-remainder dividend divisor) nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-divides-p))))

(defthm finite-field-poly-divides-p-of-normalize-divisor
  (equal (finite-field-poly-divides-p
          (finite-field-poly-normalize divisor) dividend)
         (finite-field-poly-divides-p divisor dividend))
  :hints (("Goal" :use ((:instance finite-field-poly-remainder-of-normalize-modulus
                                   (modulus divisor)))
           :in-theory (e/d (finite-field-poly-divides-p)
                           (finite-field-poly-remainder
                            finite-field-poly-normalize)))))

(defthm finite-field-poly-divides-p-of-normalize-dividend
  (equal (finite-field-poly-divides-p
          divisor (finite-field-poly-normalize dividend))
         (finite-field-poly-divides-p divisor dividend))
  :hints (("Goal" :use ((:instance finite-field-poly-remainder-of-normalize-dividend))
           :in-theory (e/d (finite-field-poly-divides-p)
                           (finite-field-poly-remainder
                            finite-field-poly-normalize)))))

(defthm finite-field-poly-normalize-of-fix-coefficients
  (equal (finite-field-poly-normalize
          (finite-field-poly-fix-coefficients polynomial))
         (finite-field-poly-normalize polynomial))
  :hints (("Goal" :in-theory
           (enable finite-field-poly-normalize
                   finite-field-poly-fix-coefficients-idempotent))))

(defthm finite-field-poly-divides-p-of-fix-coefficients-divisor
  (equal (finite-field-poly-divides-p
          (finite-field-poly-fix-coefficients divisor) dividend)
         (finite-field-poly-divides-p divisor dividend))
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-of-normalize-divisor))
           :in-theory (enable finite-field-poly-divides-p))))

(defthm finite-field-poly-divides-p-of-fix-coefficients-dividend
  (equal (finite-field-poly-divides-p
          divisor (finite-field-poly-fix-coefficients dividend))
         (finite-field-poly-divides-p divisor dividend))
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-of-normalize-dividend))
           :in-theory (enable finite-field-poly-divides-p))))

(defthm booleanp-of-finite-field-poly-common-divisor-p
  (booleanp (finite-field-poly-common-divisor-p candidate first second))
  :hints (("Goal" :in-theory (enable finite-field-poly-common-divisor-p))))

(defthm finite-field-poly-common-divisor-p-implies-divides-first
  (implies (finite-field-poly-common-divisor-p candidate first second)
           (finite-field-poly-divides-p candidate first))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable finite-field-poly-common-divisor-p))))

(defthm finite-field-poly-common-divisor-p-implies-divides-second
  (implies (finite-field-poly-common-divisor-p candidate first second)
           (finite-field-poly-divides-p candidate second))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable finite-field-poly-common-divisor-p))))

(defthm finite-field-poly-common-divisor-p-of-normalize-candidate
  (equal (finite-field-poly-common-divisor-p
          (finite-field-poly-normalize candidate) first second)
         (finite-field-poly-common-divisor-p candidate first second))
  :hints (("Goal" :use ((:instance finite-field-poly-divides-p-of-normalize-divisor
                                   (divisor candidate) (dividend first))
                         (:instance finite-field-poly-divides-p-of-normalize-divisor
                                   (divisor candidate) (dividend second)))
           :in-theory (e/d (finite-field-poly-common-divisor-p)
                           (finite-field-poly-divides-p)))))

(defthm finite-field-poly-common-divisor-p-of-normalize-first
  (equal (finite-field-poly-common-divisor-p
          candidate (finite-field-poly-normalize first) second)
         (finite-field-poly-common-divisor-p candidate first second))
  :hints (("Goal" :use ((:instance finite-field-poly-divides-p-of-normalize-dividend
                                   (divisor candidate) (dividend first)))
           :in-theory (e/d (finite-field-poly-common-divisor-p)
                           (finite-field-poly-divides-p)))))

(defthm finite-field-poly-common-divisor-p-of-normalize-second
  (equal (finite-field-poly-common-divisor-p
          candidate first (finite-field-poly-normalize second))
         (finite-field-poly-common-divisor-p candidate first second))
  :hints (("Goal" :use ((:instance finite-field-poly-divides-p-of-normalize-dividend
                                   (divisor candidate) (dividend second)))
           :in-theory (e/d (finite-field-poly-common-divisor-p)
                           (finite-field-poly-divides-p)))))

(defthm finite-field-poly-divides-p-zero
  (finite-field-poly-divides-p divisor nil)
  :hints (("Goal" :use ((:instance finite-field-poly-remainder-zero-dividend))
           :in-theory (enable finite-field-poly-divides-p))))

(defthm finite-field-poly-divides-p-self
  (finite-field-poly-divides-p dividend dividend)
  :hints (("Goal" :use ((:instance finite-field-poly-remainder-self
                                   (modulus dividend)))
           :in-theory (enable finite-field-poly-divides-p))))

(defthm finite-field-poly-divides-p-of-multiple
  (finite-field-poly-divides-p
   divisor (finite-field-poly-mul multiplier divisor))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-remainder-of-poly-add-divisor-multiple
                     (dividend nil) (modulus divisor))
          (:instance finite-field-poly-add-of-nil-left
                     (x (finite-field-poly-mul multiplier divisor)))
          (:instance finite-field-poly-normalize-when-canonical
                     (xs (finite-field-poly-mul multiplier divisor)))
          (:instance finite-field-canonical-polynomial-p-of-poly-mul
                     (x multiplier) (y divisor))
          (:instance finite-field-poly-remainder-zero-dividend
                     (modulus divisor)))
    :in-theory (e/d (finite-field-poly-divides-p)
                    (finite-field-poly-remainder finite-field-poly-add
                     finite-field-poly-mul finite-field-poly-normalize)))))

(defthm finite-field-polynomial-one-divides-p
  (finite-field-poly-divides-p
   (list (gfield::finite-field-one)) dividend)
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-divides-p-of-multiple
                     (divisor (list (gfield::finite-field-one)))
                     (multiplier dividend))
          (:instance finite-field-poly-mul-commutative-for-reduction
                     (x dividend) (y (list (gfield::finite-field-one))))
          (:instance finite-field-poly-mul-one-left-for-remainder-self
                     (polynomial dividend))
          (:instance finite-field-poly-divides-p-of-normalize-dividend
                     (divisor (list (gfield::finite-field-one)))))
    :in-theory (disable finite-field-poly-divides-p
                        finite-field-poly-mul
                        finite-field-poly-normalize))))

(local
 (defthm finite-field-poly-remainder-equal-remainder-of-normalize
   (equal (finite-field-poly-remainder dividend modulus)
          (finite-field-poly-remainder
           (finite-field-poly-normalize dividend) modulus))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance finite-field-poly-remainder-of-normalize-dividend))
            :in-theory (disable finite-field-poly-remainder
                                finite-field-poly-normalize)))))

(local
 (defthm finite-field-poly-reconstruction-with-remainder
   (equal (finite-field-poly-add
           (finite-field-poly-mul
            (mv-nth 0 (finite-field-poly-divmod first second))
            (finite-field-poly-normalize second))
           (finite-field-poly-remainder first second))
          (finite-field-poly-normalize first))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance finite-field-poly-divmod-reconstruction
                             (f first) (g second))
                  (:instance finite-field-poly-remainder-is-divmod-remainder
                             (f first) (g second)))
            :in-theory (disable finite-field-poly-divmod
                                finite-field-poly-remainder
                                finite-field-poly-normalize
                                finite-field-poly-add
                                finite-field-poly-mul)))))

; Replacing SECOND by its remainder modulo DIVISOR in the DIVMOD
; reconstruction makes the Euclidean compatibility explicit, without opening
; either recursive divider.
(defthm finite-field-poly-remainder-with-euclidean-remainder-when-divides-second
  (implies
   (finite-field-poly-divides-p divisor second)
   (equal (finite-field-poly-remainder first divisor)
          (finite-field-poly-remainder
           (finite-field-poly-remainder first second) divisor)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-reconstruction-with-remainder)
          (:instance finite-field-poly-remainder-of-normalize-dividend
                     (dividend first) (modulus divisor))
          (:instance finite-field-poly-remainder-equal-remainder-of-normalize
                     (dividend first) (modulus divisor))
          (:instance finite-field-poly-remainder-of-poly-add-remainders
                     (left (finite-field-poly-mul
                            (finite-field-poly-normalize second)
                            (mv-nth 0 (finite-field-poly-divmod first second))))
                     (right (finite-field-poly-remainder first second))
                     (modulus divisor))
          (:instance finite-field-poly-remainder-of-poly-mul-remainder-left
                     (left (finite-field-poly-normalize second))
                     (right (mv-nth 0 (finite-field-poly-divmod first second)))
                     (modulus divisor))
          (:instance finite-field-poly-mul-commutative-for-reduction
                     (x (finite-field-poly-normalize second))
                     (y (mv-nth 0 (finite-field-poly-divmod first second))))
          (:instance finite-field-poly-remainder-of-normalize-dividend
                     (dividend second) (modulus divisor))
          (:instance finite-field-poly-remainder-idempotent
                     (dividend (finite-field-poly-remainder first second))
                     (modulus divisor))
          (:instance finite-field-poly-remainder-zero-dividend
                     (modulus divisor)))
    :in-theory
    (e/d (finite-field-poly-divides-p)
         (finite-field-poly-divmod finite-field-poly-remainder
          finite-field-poly-normalize finite-field-poly-add
          finite-field-poly-mul finite-field-poly-add-commutative
          finite-field-poly-remainder-is-divmod-remainder)))))

(defthm finite-field-poly-divides-p-euclidean-remainder-iff
  (implies
   (finite-field-poly-divides-p divisor second)
   (iff (finite-field-poly-divides-p divisor first)
        (finite-field-poly-divides-p
         divisor (finite-field-poly-remainder first second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-remainder-with-euclidean-remainder-when-divides-second))
           :in-theory (enable finite-field-poly-divides-p))))

(defthm finite-field-poly-divides-p-euclidean-step-iff
  (iff
   (and (finite-field-poly-divides-p divisor first)
        (finite-field-poly-divides-p divisor second))
   (and (finite-field-poly-divides-p divisor second)
        (finite-field-poly-divides-p
         divisor (finite-field-poly-remainder first second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-euclidean-remainder-iff))
           :in-theory (disable finite-field-poly-divides-p
                               finite-field-poly-remainder))))
