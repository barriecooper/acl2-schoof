(in-package "GPOLY")

(include-book "finite-field-euclidean-gcd")
(include-book "euclidean")

; The finite-field target deliberately retains the same transparent total
; operation as the generic development: normalize first, then multiply every
; coefficient by the inverse of the canonical leading coefficient.
(def-monic-normalize-instance
  finite-field-poly-monic-normalize
  finite-field-poly-normalize
  finite-field-poly-scale
  finite-field-poly-leading-coefficient
  gfield::finite-field-inv)

(verify-guards finite-field-poly-monic-normalize)

(local
 (defun finite-field-poly-const-for-monic (a)
   (if (equal (gfield::finite-field-fix a)
              (gfield::finite-field-zero))
       nil
     (list (gfield::finite-field-fix a)))))

(local
 (defun finite-field-polynomial-one-for-monic ()
   (list (gfield::finite-field-one))))


(local
 (defthm finite-field-poly-scale-of-normalize-for-monic
   (equal (finite-field-poly-scale
           a (finite-field-poly-normalize x))
          (finite-field-poly-scale a x))
   :hints (("Goal" :in-theory
            (enable finite-field-poly-scale
                    finite-field-poly-normalize)))))

(defthm finite-field-poly-monic-normalize-of-normalize
  (equal (finite-field-poly-monic-normalize
          (finite-field-poly-normalize polynomial))
         (finite-field-poly-monic-normalize polynomial))
  :hints
  (("Goal"
    :use ((:instance finite-field-poly-scale-of-normalize-for-monic
                     (a (gfield::finite-field-inv
                         (finite-field-poly-leading-coefficient polynomial)))
                     (x polynomial))
          (:instance finite-field-poly-leading-coefficient-of-poly-normalize
                     (p polynomial)))
    :in-theory
    (e/d (finite-field-poly-monic-normalize)
         (finite-field-poly-scale finite-field-poly-normalize
          finite-field-poly-leading-coefficient
          finite-field-poly-leading-coefficient-when-canonical-nonzero)))))

(defthm finite-field-canonical-polynomial-p-of-poly-monic-normalize
  (finite-field-canonical-polynomial-p
   (finite-field-poly-monic-normalize polynomial))
  :hints (("Goal"
           :use ((:instance finite-field-canonical-polynomial-p-of-poly-scale
                            (a (gfield::finite-field-inv
                                (finite-field-poly-leading-coefficient
                                 polynomial)))
                            (x polynomial)))
           :in-theory (enable finite-field-poly-monic-normalize))))

(defthm finite-field-poly-normalize-of-poly-monic-normalize
  (equal (finite-field-poly-normalize
          (finite-field-poly-monic-normalize polynomial))
         (finite-field-poly-monic-normalize polynomial))
  :hints (("Goal"
           :use ((:instance finite-field-poly-normalize-when-canonical
                            (xs (finite-field-poly-monic-normalize polynomial)))
                 (:instance
                  finite-field-canonical-polynomial-p-of-poly-monic-normalize))
           :in-theory (disable finite-field-poly-normalize
                               finite-field-poly-monic-normalize))))

(set-default-hints
 '((and stable-under-simplificationp
        (list :use (theory 'gfield::finite-field-context-instance-theory)
              :in-theory
              (list 'quote
                    (union-theories
                     '(finite-field-div
                       finite-field-poly-monic-normalize
                       finite-field-poly-divides-p
                       finite-field-poly-common-divisor-p
                       finite-field-poly-remainder
                       finite-field-poly-divmod
                       finite-field-poly-divmod-core
                       finite-field-poly-division-step-core
                       finite-field-poly-division-step
                       finite-field-poly-division-step-term
                       finite-field-poly-division-step-next
                       finite-field-poly-monomial
                       finite-field-poly-shift
                       finite-field-poly-zero-prefix
                       finite-field-poly-const-for-monic
                       finite-field-polynomial-one-for-monic)
                     (union-theories
                      (theory 'finite-field-poly-definition-theory)
                      (theory 'minimal-theory))))))))

(defthm finite-field-consp-of-poly-monic-normalize
  (equal (consp (finite-field-poly-monic-normalize polynomial))
         (consp (finite-field-poly-normalize polynomial)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance
    consp-of-poly-monic-normalize
    (gfield::field-element-p gfield::finite-field-element-p)
    (gfield::field-fix gfield::finite-field-fix)
    (gfield::field-zero gfield::finite-field-zero)
    (gfield::field-one gfield::finite-field-one)
    (gfield::field-add gfield::finite-field-add)
    (gfield::field-mul gfield::finite-field-mul)
    (gfield::field-neg gfield::finite-field-neg)
    (gfield::field-inv gfield::finite-field-inv)
    (gfield::field-div finite-field-div)
    (fix-coefficients finite-field-poly-fix-coefficients)
    (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
    (normalize finite-field-poly-normalize)
    (coefficient-list-p finite-field-coefficient-list-p)
    (polynomial-p finite-field-polynomial-p)
    (canonical-polynomial-p finite-field-canonical-polynomial-p)
    (raw-add finite-field-poly-raw-add)
    (poly-add finite-field-poly-add)
    (raw-neg finite-field-poly-raw-neg)
    (poly-neg finite-field-poly-neg)
    (poly-sub finite-field-poly-sub)
    (raw-scale finite-field-poly-raw-scale)
    (poly-scale finite-field-poly-scale)
    (raw-mul finite-field-poly-raw-mul)
    (poly-mul finite-field-poly-mul)
    (zero-prefix finite-field-poly-zero-prefix)
    (poly-shift finite-field-poly-shift)
    (monomial finite-field-poly-monomial)
    (poly-degree finite-field-poly-degree)
    (poly-leading-coefficient finite-field-poly-leading-coefficient)
    (poly-monic-normalize finite-field-poly-monic-normalize)))))

(defthm finite-field-poly-degree-of-poly-monic-normalize-when-nonzero
  (implies (consp (finite-field-poly-normalize polynomial))
           (equal (finite-field-poly-degree
                   (finite-field-poly-monic-normalize polynomial))
                  (finite-field-poly-degree polynomial)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance
    poly-degree-of-poly-monic-normalize-when-nonzero
    (gfield::field-element-p gfield::finite-field-element-p)
    (gfield::field-fix gfield::finite-field-fix)
    (gfield::field-zero gfield::finite-field-zero)
    (gfield::field-one gfield::finite-field-one)
    (gfield::field-add gfield::finite-field-add)
    (gfield::field-mul gfield::finite-field-mul)
    (gfield::field-neg gfield::finite-field-neg)
    (gfield::field-inv gfield::finite-field-inv)
    (gfield::field-div finite-field-div)
    (fix-coefficients finite-field-poly-fix-coefficients)
    (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
    (normalize finite-field-poly-normalize)
    (coefficient-list-p finite-field-coefficient-list-p)
    (polynomial-p finite-field-polynomial-p)
    (canonical-polynomial-p finite-field-canonical-polynomial-p)
    (raw-add finite-field-poly-raw-add)
    (poly-add finite-field-poly-add)
    (raw-neg finite-field-poly-raw-neg)
    (poly-neg finite-field-poly-neg)
    (poly-sub finite-field-poly-sub)
    (raw-scale finite-field-poly-raw-scale)
    (poly-scale finite-field-poly-scale)
    (raw-mul finite-field-poly-raw-mul)
    (poly-mul finite-field-poly-mul)
    (zero-prefix finite-field-poly-zero-prefix)
    (poly-shift finite-field-poly-shift)
    (monomial finite-field-poly-monomial)
    (poly-degree finite-field-poly-degree)
    (poly-leading-coefficient finite-field-poly-leading-coefficient)
    (poly-monic-normalize finite-field-poly-monic-normalize)))))

(defthm finite-field-poly-leading-coefficient-of-poly-monic-normalize
  (equal (finite-field-poly-leading-coefficient
          (finite-field-poly-monic-normalize polynomial))
         (if (consp (finite-field-poly-normalize polynomial))
             (gfield::finite-field-one)
           (gfield::finite-field-zero)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance
    poly-leading-coefficient-of-poly-monic-normalize
    (gfield::field-element-p gfield::finite-field-element-p)
    (gfield::field-fix gfield::finite-field-fix)
    (gfield::field-zero gfield::finite-field-zero)
    (gfield::field-one gfield::finite-field-one)
    (gfield::field-add gfield::finite-field-add)
    (gfield::field-mul gfield::finite-field-mul)
    (gfield::field-neg gfield::finite-field-neg)
    (gfield::field-inv gfield::finite-field-inv)
    (gfield::field-div finite-field-div)
    (fix-coefficients finite-field-poly-fix-coefficients)
    (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
    (normalize finite-field-poly-normalize)
    (coefficient-list-p finite-field-coefficient-list-p)
    (polynomial-p finite-field-polynomial-p)
    (canonical-polynomial-p finite-field-canonical-polynomial-p)
    (raw-add finite-field-poly-raw-add)
    (poly-add finite-field-poly-add)
    (raw-neg finite-field-poly-raw-neg)
    (poly-neg finite-field-poly-neg)
    (poly-sub finite-field-poly-sub)
    (raw-scale finite-field-poly-raw-scale)
    (poly-scale finite-field-poly-scale)
    (raw-mul finite-field-poly-raw-mul)
    (poly-mul finite-field-poly-mul)
    (zero-prefix finite-field-poly-zero-prefix)
    (poly-shift finite-field-poly-shift)
    (monomial finite-field-poly-monomial)
    (poly-degree finite-field-poly-degree)
    (poly-leading-coefficient finite-field-poly-leading-coefficient)
    (poly-monic-normalize finite-field-poly-monic-normalize)))))

; This is the explicitly discharged nonzero fact used by both associate laws.
; It follows from canonical normalization, its nonzero leading coefficient,
; and the finite-field inverse law; no branch assumption is hidden.
(local
 (defthm finite-field-inverse-leading-coefficient-nonzero
   (implies
    (consp (finite-field-poly-normalize polynomial))
    (not (equal
          (gfield::finite-field-fix
           (gfield::finite-field-inv
            (finite-field-poly-leading-coefficient polynomial)))
          (gfield::finite-field-zero))))
   :hints
   (("Goal"
     :use ((:instance finite-field-canonical-polynomial-p-of-poly-normalize
                      (xs polynomial))
           (:instance
            finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
            (p (finite-field-poly-normalize polynomial)))
           (:instance finite-field-poly-leading-coefficient-of-poly-normalize
                      (p polynomial))
           (:instance finite-field-inv-nonzero
                      (y (finite-field-poly-leading-coefficient polynomial))))
     :in-theory
     (disable finite-field-poly-normalize
              finite-field-poly-leading-coefficient
              finite-field-canonical-polynomial-p-of-poly-normalize
              finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
              finite-field-poly-leading-coefficient-of-poly-normalize)))))

; Instantiate only the two associate laws needed downstream.  The generic
; proof supplies the multiplication witnesses, inverse scaling, transitivity,
; and mutual divisibility; those plumbing facts are intentionally not public
; at this finite-field boundary.
(defthm finite-field-poly-divides-p-of-poly-monic-normalize-dividend
  (equal
   (finite-field-poly-divides-p
    divisor (finite-field-poly-monic-normalize dividend))
   (finite-field-poly-divides-p divisor dividend))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :by (:functional-instance
                poly-divides-p-of-poly-monic-normalize-dividend
                (gfield::field-element-p gfield::finite-field-element-p)
                (gfield::field-fix gfield::finite-field-fix)
                (gfield::field-zero gfield::finite-field-zero)
                (gfield::field-one gfield::finite-field-one)
                (gfield::field-add gfield::finite-field-add)
                (gfield::field-mul gfield::finite-field-mul)
                (gfield::field-neg gfield::finite-field-neg)
                (gfield::field-inv gfield::finite-field-inv)
                (gfield::field-div finite-field-div)
                (fix-coefficients finite-field-poly-fix-coefficients)
                (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                (normalize finite-field-poly-normalize)
                (coefficient-list-p finite-field-coefficient-list-p)
                (polynomial-p finite-field-polynomial-p)
                (canonical-polynomial-p finite-field-canonical-polynomial-p)
                (raw-add finite-field-poly-raw-add)
                (poly-add finite-field-poly-add)
                (raw-neg finite-field-poly-raw-neg)
                (poly-neg finite-field-poly-neg)
                (poly-sub finite-field-poly-sub)
                (raw-scale finite-field-poly-raw-scale)
                (poly-scale finite-field-poly-scale)
                (raw-mul finite-field-poly-raw-mul)
                (poly-mul finite-field-poly-mul)
                (const finite-field-poly-const-for-monic)
                (polynomial-one finite-field-polynomial-one-for-monic)
                (zero-prefix finite-field-poly-zero-prefix)
                (poly-shift finite-field-poly-shift)
                (monomial finite-field-poly-monomial)
                (poly-degree finite-field-poly-degree)
                (poly-leading-coefficient finite-field-poly-leading-coefficient)
                (poly-monic-normalize finite-field-poly-monic-normalize)
                (poly-division-step-core finite-field-poly-division-step-core)
                (poly-division-step finite-field-poly-division-step)
                (poly-division-step-term finite-field-poly-division-step-term)
                (poly-division-step-next finite-field-poly-division-step-next)
                (poly-divmod-core finite-field-poly-divmod-core)
                (poly-divmod finite-field-poly-divmod)
                (poly-remainder finite-field-poly-remainder)
                (poly-divides-p finite-field-poly-divides-p)
                (poly-common-divisor-p finite-field-poly-common-divisor-p)))))

(defthm finite-field-poly-divides-p-of-poly-monic-normalize-divisor
  (equal
   (finite-field-poly-divides-p
    (finite-field-poly-monic-normalize divisor) dividend)
   (finite-field-poly-divides-p divisor dividend))
  :hints (("Goal"
           :in-theory (theory 'minimal-theory)
           :by (:functional-instance
                poly-divides-p-of-poly-monic-normalize-divisor
                (gfield::field-element-p gfield::finite-field-element-p)
                (gfield::field-fix gfield::finite-field-fix)
                (gfield::field-zero gfield::finite-field-zero)
                (gfield::field-one gfield::finite-field-one)
                (gfield::field-add gfield::finite-field-add)
                (gfield::field-mul gfield::finite-field-mul)
                (gfield::field-neg gfield::finite-field-neg)
                (gfield::field-inv gfield::finite-field-inv)
                (gfield::field-div finite-field-div)
                (fix-coefficients finite-field-poly-fix-coefficients)
                (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                (normalize finite-field-poly-normalize)
                (coefficient-list-p finite-field-coefficient-list-p)
                (polynomial-p finite-field-polynomial-p)
                (canonical-polynomial-p finite-field-canonical-polynomial-p)
                (raw-add finite-field-poly-raw-add)
                (poly-add finite-field-poly-add)
                (raw-neg finite-field-poly-raw-neg)
                (poly-neg finite-field-poly-neg)
                (poly-sub finite-field-poly-sub)
                (raw-scale finite-field-poly-raw-scale)
                (poly-scale finite-field-poly-scale)
                (raw-mul finite-field-poly-raw-mul)
                (poly-mul finite-field-poly-mul)
                (const finite-field-poly-const-for-monic)
                (polynomial-one finite-field-polynomial-one-for-monic)
                (zero-prefix finite-field-poly-zero-prefix)
                (poly-shift finite-field-poly-shift)
                (monomial finite-field-poly-monomial)
                (poly-degree finite-field-poly-degree)
                (poly-leading-coefficient finite-field-poly-leading-coefficient)
                (poly-monic-normalize finite-field-poly-monic-normalize)
                (poly-division-step-core finite-field-poly-division-step-core)
                (poly-division-step finite-field-poly-division-step)
                (poly-division-step-term finite-field-poly-division-step-term)
                (poly-division-step-next finite-field-poly-division-step-next)
                (poly-divmod-core finite-field-poly-divmod-core)
                (poly-divmod finite-field-poly-divmod)
                (poly-remainder finite-field-poly-remainder)
                (poly-divides-p finite-field-poly-divides-p)
                (poly-common-divisor-p finite-field-poly-common-divisor-p)))))

; The broad defaults above are confined to the functional-instantiation
; obligations.  Direct wrapper and correctness proofs below use only their
; explicit hints and the ordinary inherited theory.
(set-default-hints nil)

(defun finite-field-poly-monic-euclidean-gcd (first second)
  (declare (xargs :guard t))
  (finite-field-poly-monic-normalize
   (finite-field-poly-euclidean-gcd first second)))

(verify-guards finite-field-poly-monic-euclidean-gcd)

(defthm finite-field-poly-monic-euclidean-gcd-is-monic-normalize
  (equal (finite-field-poly-monic-euclidean-gcd first second)
         (finite-field-poly-monic-normalize
          (finite-field-poly-euclidean-gcd first second)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-monic-euclidean-gcd-of-normalize-first
  (equal (finite-field-poly-monic-euclidean-gcd
          (finite-field-poly-normalize first) second)
         (finite-field-poly-monic-euclidean-gcd first second))
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-of-normalize-first))
           :in-theory (enable finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-monic-euclidean-gcd-of-normalize-second
  (equal (finite-field-poly-monic-euclidean-gcd
          first (finite-field-poly-normalize second))
         (finite-field-poly-monic-euclidean-gcd first second))
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-of-normalize-second))
           :in-theory (enable finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-canonical-polynomial-p-of-poly-monic-euclidean-gcd
  (finite-field-canonical-polynomial-p
   (finite-field-poly-monic-euclidean-gcd first second))
  :hints (("Goal"
           :use ((:instance
                  finite-field-canonical-polynomial-p-of-poly-monic-normalize
                  (polynomial (finite-field-poly-euclidean-gcd first second))))
           :in-theory (enable finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-normalize-of-poly-monic-euclidean-gcd
  (equal (finite-field-poly-normalize
          (finite-field-poly-monic-euclidean-gcd first second))
         (finite-field-poly-monic-euclidean-gcd first second))
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-normalize-of-poly-monic-normalize
                  (polynomial (finite-field-poly-euclidean-gcd first second))))
           :in-theory (enable finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-consp-of-poly-monic-euclidean-gcd
  (equal (consp (finite-field-poly-monic-euclidean-gcd first second))
         (consp (finite-field-poly-euclidean-gcd first second)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-consp-of-poly-monic-normalize
                            (polynomial
                             (finite-field-poly-euclidean-gcd first second)))
                 (:instance finite-field-poly-normalize-of-euclidean-gcd))
           :in-theory (enable finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-leading-coefficient-of-poly-monic-euclidean-gcd
  (equal
   (finite-field-poly-leading-coefficient
    (finite-field-poly-monic-euclidean-gcd first second))
   (if (consp (finite-field-poly-euclidean-gcd first second))
       (gfield::finite-field-one)
     (gfield::finite-field-zero)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-leading-coefficient-of-poly-monic-normalize
                  (polynomial (finite-field-poly-euclidean-gcd first second)))
                 (:instance finite-field-poly-normalize-of-euclidean-gcd))
           :in-theory (enable finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-monic-euclidean-gcd-divides-first
  (finite-field-poly-divides-p
   (finite-field-poly-monic-euclidean-gcd first second) first)
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-divides-first)
                 (:instance
                  finite-field-poly-divides-p-of-poly-monic-normalize-divisor
                  (divisor (finite-field-poly-euclidean-gcd first second))
                  (dividend first)))
           :in-theory (enable
                       finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-monic-euclidean-gcd-divides-second
  (finite-field-poly-divides-p
   (finite-field-poly-monic-euclidean-gcd first second) second)
  :hints (("Goal"
           :use ((:instance finite-field-poly-euclidean-gcd-divides-second)
                 (:instance
                  finite-field-poly-divides-p-of-poly-monic-normalize-divisor
                  (divisor (finite-field-poly-euclidean-gcd first second))
                  (dividend second)))
           :in-theory (enable
                       finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-common-divisor-p-of-poly-monic-euclidean-gcd
  (finite-field-poly-common-divisor-p
   (finite-field-poly-monic-euclidean-gcd first second) first second)
  :hints (("Goal"
           :use ((:instance finite-field-poly-monic-euclidean-gcd-divides-first)
                 (:instance finite-field-poly-monic-euclidean-gcd-divides-second))
           :in-theory (enable finite-field-poly-common-divisor-p))))

(defthm finite-field-poly-common-divisor-divides-monic-euclidean-gcd
  (implies
   (finite-field-poly-common-divisor-p divisor first second)
   (finite-field-poly-divides-p
    divisor (finite-field-poly-monic-euclidean-gcd first second)))
  :hints (("Goal"
           :use ((:instance finite-field-poly-common-divisor-divides-euclidean-gcd)
                 (:instance
                  finite-field-poly-divides-p-of-poly-monic-normalize-dividend
                  (dividend (finite-field-poly-euclidean-gcd first second))))
           :in-theory (enable
                       finite-field-poly-monic-euclidean-gcd))))

(defthm finite-field-poly-monic-euclidean-gcd-correct
  (and
   (finite-field-poly-common-divisor-p
    (finite-field-poly-monic-euclidean-gcd first second) first second)
   (implies
    (finite-field-poly-common-divisor-p divisor first second)
    (finite-field-poly-divides-p
     divisor (finite-field-poly-monic-euclidean-gcd first second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-common-divisor-p-of-poly-monic-euclidean-gcd)
                 (:instance
                  finite-field-poly-common-divisor-divides-monic-euclidean-gcd))
           :in-theory
           (disable finite-field-poly-common-divisor-p
                    finite-field-poly-divides-p
                    finite-field-poly-monic-euclidean-gcd))))
