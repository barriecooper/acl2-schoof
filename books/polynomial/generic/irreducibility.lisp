(in-package "GPOLY")
(include-book "euclidean")

; A polynomial unit is exactly a nonzero constant after the repository's
; total coefficient fixing and trailing-zero normalization.
(defun poly-unit-p (poly)
  (declare (xargs :guard t))
  (equal (poly-degree poly) 0))

; Generic factor quantification is deliberately logical.  It is not a factor
; search and does not claim to be executable over an abstract coefficient
; field.
(defun-sk poly-reducible-p (poly)
  (exists (left right)
          (and (equal (poly-mul left right) (normalize poly))
               (not (poly-unit-p left))
               (not (poly-unit-p right)))))

(defun poly-irreducible-p (poly)
  (declare (xargs :guard t :verify-guards nil))
  (and (< 0 (poly-degree poly))
       (not (poly-reducible-p poly))))

(defthm poly-irreducible-p-definition
  (equal (poly-irreducible-p poly)
         (and (< 0 (poly-degree poly))
              (not (poly-reducible-p poly))))
  :rule-classes nil)

(defthm poly-reducible-p-normalize-forward
  (implies (poly-reducible-p poly)
           (poly-reducible-p (normalize poly)))
  :hints (("Goal"
           :use ((:instance poly-reducible-p-suff
                            (poly (normalize poly))
                            (left (mv-nth 0 (poly-reducible-p-witness poly)))
                            (right (mv-nth 1 (poly-reducible-p-witness poly))))))))

(defthm poly-reducible-p-normalize-reverse
  (implies (poly-reducible-p (normalize poly))
           (poly-reducible-p poly))
  :hints (("Goal"
           :use ((:instance poly-reducible-p-suff
                            (poly poly)
                            (left (mv-nth 0 (poly-reducible-p-witness
                                             (normalize poly))))
                            (right (mv-nth 1 (poly-reducible-p-witness
                                              (normalize poly)))))))))

(defthm poly-reducible-p-of-normalize
  (equal (poly-reducible-p (normalize poly))
         (poly-reducible-p poly))
  :hints (("Goal"
           :use ((:instance poly-reducible-p-normalize-forward)
                 (:instance poly-reducible-p-normalize-reverse)))))

(defthm poly-irreducible-p-of-normalize
  (equal (poly-irreducible-p (normalize poly))
         (poly-irreducible-p poly))
  :hints (("Goal"
           :use ((:instance poly-degree-of-normalize (p poly))
                 (:instance poly-reducible-p-of-normalize))
           :in-theory (e/d (poly-irreducible-p)
                           (poly-degree-of-normalize
                            poly-reducible-p-of-normalize
                            poly-reducible-p)))))

(defthm poly-irreducible-p-implies-positive-degree
  (implies (poly-irreducible-p poly)
           (< 0 (poly-degree poly)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable poly-irreducible-p))))

(defthm poly-irreducible-p-implies-normalize-nonzero
  (implies (poly-irreducible-p poly)
           (consp (normalize poly)))
  :rule-classes (:forward-chaining)
  :hints (("Goal"
           :use ((:instance poly-degree-equal-minus-one (p poly)))
           :in-theory (enable poly-irreducible-p))))

(defthm poly-irreducible-p-factor-characterization
  (implies (and (poly-irreducible-p poly)
                (equal (poly-mul left right) (normalize poly)))
           (or (poly-unit-p left)
               (poly-unit-p right)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-reducible-p-suff
                            (poly poly) (left left) (right right)))
           :in-theory (enable poly-irreducible-p))))

(defthm poly-unit-p-of-normalize
  (equal (poly-unit-p (normalize poly))
         (poly-unit-p poly)))

(defthm poly-unit-p-of-const
  (equal (poly-unit-p (const scalar))
         (not (equal (gfield::field-fix scalar)
                     (gfield::field-zero))))
  :hints (("Goal" :in-theory (enable poly-unit-p))))

; Degree zero has exactly one normalized coefficient.  This is the focused
; scalar-associate bridge needed below; no second associates relation is
; introduced.
(local
 (defthm true-listp-length-one
   (implies (and (true-listp x) (equal (len x) 1))
            (equal x (list (car x))))
   :rule-classes nil))

(defthm normalize-when-poly-unit-p
  (implies (poly-unit-p poly)
           (equal (normalize poly)
                  (const (poly-leading-coefficient poly))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance canonical-polynomial-p-of-normalize (xs poly))
                 (:instance poly-degree-when-canonical-nonzero
                            (p (normalize poly)))
                 (:instance poly-leading-coefficient-when-canonical-nonzero
                            (p (normalize poly)))
                 (:instance poly-leading-coefficient-of-normalize (p poly))
                 (:instance true-listp-length-one (x (normalize poly))))
           :in-theory (e/d (poly-unit-p const polynomial-p)
                           (normalize canonical-polynomial-p poly-degree
                            poly-leading-coefficient)))))

(defthm poly-unit-p-implies-normalize-nonzero
  (implies (poly-unit-p poly)
           (consp (normalize poly)))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :use ((:instance poly-degree-equal-minus-one (p poly)))
           :in-theory (enable poly-unit-p))))

(defthm poly-monic-normalize-when-poly-unit-p
  (implies (poly-unit-p poly)
           (equal (poly-monic-normalize poly) (polynomial-one)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance normalize-when-poly-unit-p))
           :in-theory (enable poly-monic-normalize const polynomial-one))))

; POLY-DIVIDES-P remains remainder-defined.  Its existing division quotient
; is the multiplication witness, with quotient on the left and normalized
; divisor on the right.
(defthm poly-divides-p-multiplication-witness
  (implies (poly-divides-p divisor dividend)
           (equal (normalize dividend)
                  (poly-mul (mv-nth 0 (poly-divmod dividend divisor))
                            (normalize divisor))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-divmod-exact-division
                            (f dividend) (g divisor)))
           :in-theory (enable poly-divides-p poly-remainder))))

(local
 (defthm poly-mul-when-left-unit
   (implies (poly-unit-p quotient)
            (equal (poly-mul quotient divisor)
                   (poly-scale (poly-leading-coefficient quotient) divisor)))
   :hints (("Goal"
            :use ((:instance normalize-when-poly-unit-p (poly quotient))
                  (:instance poly-mul-normalize-left
                             (x quotient) (y divisor))
                  (:instance poly-mul-const-left
                             (a (poly-leading-coefficient quotient))
                             (p divisor)))
            :in-theory (disable poly-mul poly-scale normalize
                             poly-leading-coefficient poly-unit-p
                             poly-mul-normalize-left poly-mul-const-left)))))

(local
 (defthm unit-left-factor-implies-reverse-divisibility
   (implies (and (poly-unit-p quotient)
                 (equal (normalize dividend)
                        (poly-mul quotient (normalize divisor))))
            (poly-divides-p dividend divisor))
   :hints
   (("Goal"
     :use ((:instance normalize-when-poly-unit-p (poly quotient))
           (:instance poly-unit-p-implies-normalize-nonzero (poly quotient))
           (:instance poly-mul-when-left-unit)
           (:instance poly-divides-p-of-poly-scale-divisor
                      (scalar (poly-leading-coefficient quotient))
                      (divisor divisor) (dividend divisor))
           (:instance poly-divides-p-self (dividend divisor))
           (:instance poly-divides-p-of-normalize-divisor
                      (divisor dividend) (dividend divisor)))
     :in-theory (e/d (poly-mul-const-left)
                     (poly-divides-p normalize poly-mul poly-scale
                      poly-leading-coefficient poly-unit-p))))))

(defthm poly-irreducible-p-divisor-alternative
  (implies (and (poly-irreducible-p modulus)
                (poly-divides-p divisor modulus))
           (or (poly-unit-p divisor)
               (poly-divides-p modulus divisor)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-multiplication-witness
                     (divisor divisor) (dividend modulus))
          (:instance poly-irreducible-p-factor-characterization
                     (poly modulus)
                     (left (mv-nth 0 (poly-divmod modulus divisor)))
                     (right (normalize divisor))))
    :in-theory (disable poly-divides-p poly-divmod poly-mul normalize
                        poly-unit-p))
   ("Goal'"
    :use ((:instance unit-left-factor-implies-reverse-divisibility
                     (quotient (mv-nth 0 (poly-divmod modulus divisor)))
                     (dividend modulus) (divisor divisor)))
    :in-theory (disable poly-divides-p poly-divmod poly-mul normalize
                        poly-unit-p))))

(defthm poly-monic-euclidean-gcd-unit-is-one
  (implies (poly-unit-p (poly-monic-euclidean-gcd first second))
           (equal (poly-monic-euclidean-gcd first second)
                  (polynomial-one)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance normalize-when-poly-unit-p
                     (poly (poly-monic-euclidean-gcd first second)))
          (:instance normalize-of-poly-monic-euclidean-gcd)
          (:instance poly-leading-coefficient-of-poly-monic-euclidean-gcd))
    :in-theory (e/d (const polynomial-one)
                    (poly-unit-p poly-monic-euclidean-gcd normalize
                     poly-leading-coefficient)))))

(defthm poly-irreducible-p-monic-gcd-one-or-divides-first
  (implies (poly-irreducible-p modulus)
           (or (equal (poly-monic-euclidean-gcd first modulus)
                      (polynomial-one))
               (poly-divides-p modulus first)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-irreducible-p-divisor-alternative
                     (divisor (poly-monic-euclidean-gcd first modulus)))
          (:instance poly-monic-euclidean-gcd-divides-first
                     (first first) (second modulus))
          (:instance poly-monic-euclidean-gcd-divides-second
                     (first first) (second modulus))
          (:instance poly-divides-p-transitive
                     (divisor modulus)
                     (middle (poly-monic-euclidean-gcd first modulus))
                     (dividend first))
          (:instance poly-monic-euclidean-gcd-unit-is-one
                     (first first) (second modulus)))
    :in-theory (disable poly-irreducible-p poly-divides-p
                        poly-monic-euclidean-gcd poly-unit-p))))

(defthm poly-irreducible-p-and-not-divides-implies-monic-gcd-one
  (implies (and (poly-irreducible-p modulus)
                (not (poly-divides-p modulus first)))
           (equal (poly-monic-euclidean-gcd first modulus)
                  (polynomial-one)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-irreducible-p-monic-gcd-one-or-divides-first))
    :in-theory (disable poly-irreducible-p poly-divides-p
                        poly-monic-euclidean-gcd))))

(defthm nonzero-poly-remainder-not-divisible-by-positive-degree-modulus
  (implies (and (< 0 (poly-degree modulus))
                (not (equal (poly-remainder first modulus) nil)))
           (not (poly-divides-p modulus
                                (poly-remainder first modulus))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-remainder-idempotent
                     (dividend first) (modulus modulus))
          (:instance poly-divides-p-iff-zero-remainder
                     (divisor modulus)
                     (dividend (poly-remainder first modulus))))
    :in-theory (disable poly-divides-p poly-remainder))))

(defthm poly-irreducible-p-nonzero-remainder-implies-monic-gcd-one
  (implies (and (poly-irreducible-p modulus)
                (equal first (poly-remainder first modulus))
                (not (equal (normalize first) nil)))
           (equal (poly-monic-euclidean-gcd first modulus)
                  (polynomial-one)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-irreducible-p-implies-positive-degree
                     (poly modulus))
          (:instance nonzero-poly-remainder-not-divisible-by-positive-degree-modulus)
          (:instance poly-irreducible-p-and-not-divides-implies-monic-gcd-one))
    :in-theory (disable poly-irreducible-p poly-divides-p poly-remainder
                        poly-monic-euclidean-gcd normalize poly-degree))))

(defthm poly-irreducible-p-of-nil
  (not (poly-irreducible-p nil))
  :hints (("Goal" :in-theory (enable poly-irreducible-p))))

(defthm poly-irreducible-p-of-polynomial-one
  (not (poly-irreducible-p (polynomial-one)))
  :hints (("Goal" :in-theory (enable poly-irreducible-p))))

(defthm poly-irreducible-p-of-const
  (not (poly-irreducible-p (const scalar)))
  :hints (("Goal" :in-theory (enable poly-irreducible-p))))
