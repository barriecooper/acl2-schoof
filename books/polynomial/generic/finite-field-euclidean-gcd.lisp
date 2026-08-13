(in-package "GPOLY")

(include-book "finite-field-euclidean-interface")

; The reduction book proves the strict bound on the canonical remainder itself.
; Its normalization theorem turns that public bound into this recursion measure.
(defun finite-field-poly-euclidean-gcd (first second)
  (declare
   (xargs
    :measure (len (finite-field-poly-normalize second))
    :hints
    (("Goal"
      :use ((:instance finite-field-poly-remainder-strict-length-bound
                       (dividend first) (modulus second))
            (:instance finite-field-poly-normalize-of-remainder
                       (dividend first) (modulus second)))
      :in-theory (disable finite-field-poly-normalize
                          finite-field-poly-remainder)))))
  (if (consp (finite-field-poly-normalize second))
      (finite-field-poly-euclidean-gcd
       second (finite-field-poly-remainder first second))
    (finite-field-poly-normalize first)))

(verify-guards finite-field-poly-euclidean-gcd)

(defthm finite-field-poly-euclidean-gcd-zero-second
  (implies (not (consp (finite-field-poly-normalize second)))
           (equal (finite-field-poly-euclidean-gcd first second)
                  (finite-field-poly-normalize first)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-euclidean-gcd))))

(defthm finite-field-poly-euclidean-gcd-nonzero-second
  (implies (consp (finite-field-poly-normalize second))
           (equal (finite-field-poly-euclidean-gcd first second)
                  (finite-field-poly-euclidean-gcd
                   second (finite-field-poly-remainder first second))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-euclidean-gcd))))

(defthm finite-field-poly-euclidean-gcd-canonical
  (finite-field-canonical-polynomial-p
   (finite-field-poly-euclidean-gcd first second))
  :hints
  (("Goal"
    :induct (finite-field-poly-euclidean-gcd first second)
    :in-theory
    (e/d (finite-field-poly-euclidean-gcd)
         (finite-field-poly-normalize finite-field-poly-remainder
          finite-field-canonical-polynomial-p)))))

(defthm finite-field-poly-euclidean-gcd-of-normalize-first
  (equal (finite-field-poly-euclidean-gcd
          (finite-field-poly-normalize first) second)
         (finite-field-poly-euclidean-gcd first second))
  :hints
  (("Goal"
    :induct (finite-field-poly-euclidean-gcd first second)
    :in-theory
    (e/d (finite-field-poly-euclidean-gcd)
         (finite-field-poly-normalize finite-field-poly-remainder)))
   ("Subgoal *1/1"
    :use ((:instance finite-field-poly-remainder-of-normalize-dividend
                     (dividend first) (modulus second)))
    :in-theory (disable finite-field-poly-normalize
                        finite-field-poly-remainder))))

(defthm finite-field-poly-euclidean-gcd-of-normalize-second
  (equal (finite-field-poly-euclidean-gcd
          first (finite-field-poly-normalize second))
         (finite-field-poly-euclidean-gcd first second))
  :hints
  (("Goal"
    :induct (finite-field-poly-euclidean-gcd first second)
    :in-theory
    (e/d (finite-field-poly-euclidean-gcd)
         (finite-field-poly-normalize finite-field-poly-remainder)))
   ("Subgoal *1/1"
    :use ((:instance finite-field-poly-remainder-of-normalize-modulus
                     (dividend first) (modulus second))
          (:instance finite-field-poly-euclidean-gcd-of-normalize-first
                     (first second)
                     (second (finite-field-poly-remainder first second))))
    :in-theory (disable finite-field-poly-normalize
                        finite-field-poly-remainder))))

(defthm finite-field-poly-normalize-of-euclidean-gcd
  (equal (finite-field-poly-normalize
          (finite-field-poly-euclidean-gcd first second))
         (finite-field-poly-euclidean-gcd first second))
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-normalize-when-canonical
                     (xs (finite-field-poly-euclidean-gcd first second)))
          (:instance finite-field-poly-euclidean-gcd-canonical))
    :in-theory (disable finite-field-poly-euclidean-gcd
                        finite-field-poly-normalize
                        finite-field-canonical-polynomial-p))))

; Two deliberately small base-case consequences, expressed only through the
; already-public normalization invariance and zero laws for divisibility.
(defthm finite-field-poly-normalize-divides-p-self
  (finite-field-poly-divides-p
   (finite-field-poly-normalize dividend) dividend)
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-divides-p-self
                     (dividend (finite-field-poly-normalize dividend)))
          (:instance finite-field-poly-divides-p-of-normalize-divisor))
    :in-theory (disable finite-field-poly-divides-p
                        finite-field-poly-normalize))))

(defthm finite-field-poly-divides-p-when-normalize-dividend-nil
  (implies (equal (finite-field-poly-normalize dividend) nil)
           (finite-field-poly-divides-p divisor dividend))
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-divides-p-zero)
          (:instance finite-field-poly-divides-p-of-normalize-dividend
                     (dividend dividend)))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-euclidean-gcd-divides-both-base
  (implies
   (not (consp (finite-field-poly-normalize second)))
   (and
    (finite-field-poly-divides-p
     (finite-field-poly-euclidean-gcd first second) first)
    (finite-field-poly-divides-p
     (finite-field-poly-euclidean-gcd first second) second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-normalize-equal-nil-when-not-consp
                     (xs second)))
    :in-theory
    (e/d (finite-field-poly-euclidean-gcd
          finite-field-poly-normalize-divides-p-self
          finite-field-poly-divides-p-when-normalize-dividend-nil)
         (finite-field-poly-remainder finite-field-poly-divides-p
          finite-field-poly-normalize)))))

(defthm finite-field-poly-euclidean-gcd-divides-both-step
  (implies
   (and
    (consp (finite-field-poly-normalize second))
    (finite-field-poly-divides-p
     (finite-field-poly-euclidean-gcd
      second (finite-field-poly-remainder first second))
     second)
    (finite-field-poly-divides-p
     (finite-field-poly-euclidean-gcd
      second (finite-field-poly-remainder first second))
     (finite-field-poly-remainder first second)))
   (and
    (finite-field-poly-divides-p
     (finite-field-poly-euclidean-gcd first second) first)
    (finite-field-poly-divides-p
     (finite-field-poly-euclidean-gcd first second) second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-euclidean-gcd-nonzero-second)
          (:instance finite-field-poly-divides-p-euclidean-step-iff
                     (divisor
                      (finite-field-poly-euclidean-gcd
                       second (finite-field-poly-remainder first second)))))
    :in-theory
    (disable finite-field-poly-euclidean-gcd
             finite-field-poly-remainder finite-field-poly-divides-p
             finite-field-poly-normalize))))

(defthm finite-field-poly-euclidean-gcd-divides-both
  (and
   (finite-field-poly-divides-p
    (finite-field-poly-euclidean-gcd first second) first)
   (finite-field-poly-divides-p
    (finite-field-poly-euclidean-gcd first second) second))
  :hints
  (("Goal"
    :induct (finite-field-poly-euclidean-gcd first second)
    :in-theory
    (e/d (finite-field-poly-euclidean-gcd)
         (finite-field-poly-remainder finite-field-poly-divides-p
          finite-field-poly-normalize)))
   ("Subgoal *1/2"
    :use ((:instance finite-field-poly-euclidean-gcd-divides-both-base))
    :in-theory (disable finite-field-poly-euclidean-gcd
                        finite-field-poly-remainder
                        finite-field-poly-divides-p
                        finite-field-poly-normalize))
   ("Subgoal *1/1"
    :use ((:instance finite-field-poly-euclidean-gcd-divides-both-step))
    :in-theory (disable finite-field-poly-euclidean-gcd
                        finite-field-poly-remainder
                        finite-field-poly-divides-p
                        finite-field-poly-normalize))))

(defthm finite-field-poly-euclidean-gcd-divides-first
  (finite-field-poly-divides-p
   (finite-field-poly-euclidean-gcd first second) first)
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-divides-both))
           :in-theory
           (disable finite-field-poly-euclidean-gcd-divides-both))))

(defthm finite-field-poly-euclidean-gcd-divides-second
  (finite-field-poly-divides-p
   (finite-field-poly-euclidean-gcd first second) second)
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-divides-both))
           :in-theory
           (disable finite-field-poly-euclidean-gcd-divides-both))))

(defthm finite-field-poly-common-divisor-divides-euclidean-gcd
  (implies
   (and (finite-field-poly-divides-p divisor first)
        (finite-field-poly-divides-p divisor second))
   (finite-field-poly-divides-p
    divisor (finite-field-poly-euclidean-gcd first second)))
  :hints
  (("Goal"
    :induct (finite-field-poly-euclidean-gcd first second)
    :in-theory
    (e/d (finite-field-poly-euclidean-gcd)
         (finite-field-poly-remainder finite-field-poly-divides-p
          finite-field-poly-normalize)))
   ("Subgoal *1/2"
    :use ((:instance finite-field-poly-euclidean-gcd-zero-second)
          (:instance finite-field-poly-divides-p-of-normalize-dividend
                     (dividend first)))
    :in-theory (disable finite-field-poly-euclidean-gcd
                        finite-field-poly-remainder
                        finite-field-poly-divides-p
                        finite-field-poly-normalize))
   ("Subgoal *1/1"
    :use ((:instance finite-field-poly-euclidean-gcd-nonzero-second)
          (:instance finite-field-poly-divides-p-euclidean-step-iff))
    :in-theory (disable finite-field-poly-euclidean-gcd
                        finite-field-poly-remainder
                        finite-field-poly-divides-p
                        finite-field-poly-normalize))))

(defthm finite-field-poly-common-divisor-p-of-euclidean-gcd
  (finite-field-poly-common-divisor-p
   (finite-field-poly-euclidean-gcd first second) first second)
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-euclidean-gcd-divides-both))
    :in-theory
    (e/d (finite-field-poly-common-divisor-p)
         (finite-field-poly-euclidean-gcd finite-field-poly-divides-p
          finite-field-poly-euclidean-gcd-divides-both)))))

(defthm finite-field-poly-common-divisor-p-greatestness
  (implies
   (finite-field-poly-common-divisor-p divisor first second)
   (finite-field-poly-divides-p
    divisor (finite-field-poly-euclidean-gcd first second)))
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-common-divisor-divides-euclidean-gcd))
    :in-theory
    (e/d (finite-field-poly-common-divisor-p)
         (finite-field-poly-euclidean-gcd finite-field-poly-divides-p
          finite-field-poly-common-divisor-divides-euclidean-gcd)))))

(defthm finite-field-poly-euclidean-gcd-raw-correct
  (and
   (finite-field-poly-common-divisor-p
    (finite-field-poly-euclidean-gcd first second) first second)
   (implies
    (finite-field-poly-common-divisor-p divisor first second)
    (finite-field-poly-divides-p
     divisor (finite-field-poly-euclidean-gcd first second))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-common-divisor-p-of-euclidean-gcd)
          (:instance finite-field-poly-common-divisor-p-greatestness))
    :in-theory
    (disable finite-field-poly-common-divisor-p
             finite-field-poly-euclidean-gcd
             finite-field-poly-divides-p
             finite-field-poly-common-divisor-p-of-euclidean-gcd
             finite-field-poly-common-divisor-p-greatestness))))
