(in-package "GPOLY")

(include-book "finite-field-modular-inverse")
(include-book "f11-production-reduced-ring")

; This concrete layer deliberately reuses the production F11 normalization,
; arithmetic, divmod, quotient, remainder, and reduced-ring operations.
(def-monic-normalize-instance
  f11-poly-monic-normalize f11-normalize f11-poly-scale
  f11-poly-leading-coefficient gfield::f11-inv)

(def-divisibility-instance
  f11-poly-divides-p f11-poly-common-divisor-p f11-poly-remainder)

(defthm f11-poly-normalized-remainder-strict-length-bound
  (implies (consp (f11-normalize modulus))
           (< (len (f11-normalize (f11-poly-remainder dividend modulus)))
              (len (f11-normalize modulus))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-remainder-strict-length-bound)
                         (:instance f11-poly-normalize-of-remainder))
           :in-theory (disable f11-normalize f11-poly-remainder))))

(def-euclidean-gcd-instance
  f11-poly-euclidean-gcd f11-poly-monic-euclidean-gcd f11-normalize
  f11-poly-remainder f11-poly-monic-normalize
  f11-poly-normalized-remainder-strict-length-bound)

; Exactly one DIVMOD call is shared by the quotient and remainder at each step.
(defthm f11-poly-remainder-is-divmod-remainder
  (equal (f11-poly-remainder f g)
         (mv-nth 1 (f11-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable f11-poly-remainder))))

(defun f11-poly-extended-euclidean-gcd (first second)
  (declare
   (xargs :measure (len (f11-normalize second))
          :hints (("Goal"
                   :use ((:instance f11-poly-remainder-strict-length-bound
                                    (dividend first) (modulus second))
                         (:instance f11-poly-normalize-of-remainder
                                    (dividend first) (modulus second))
                         (:instance f11-poly-remainder-is-divmod-remainder
                                    (f first) (g second)))
                   :in-theory (disable f11-normalize f11-poly-remainder
                                       f11-poly-divmod)))))
  (if (consp (f11-normalize second))
      (mv-let (quotient remainder) (f11-poly-divmod first second)
        (mv-let (gcd s-next t-next)
          (f11-poly-extended-euclidean-gcd second remainder)
          (mv gcd t-next
              (f11-poly-sub s-next (f11-poly-mul t-next quotient)))))
    (mv (f11-normalize first) (list (gfield::f11-one)) nil)))

(verify-guards f11-poly-extended-euclidean-gcd)

; One common scalar normalizes all three raw-XGCD projections.
(defun f11-poly-monic-extended-euclidean-gcd (first second)
  (declare (xargs :guard t))
  (mv-let (gcd s coefficient-t)
    (f11-poly-extended-euclidean-gcd first second)
    (let ((scale (gfield::f11-inv (f11-poly-leading-coefficient gcd))))
      (mv (f11-poly-monic-normalize gcd)
          (f11-poly-scale scale s)
          (f11-poly-scale scale coefficient-t)))))

; One monic-XGCD call and one reduction of projection 1.
(defund f11-poly-modular-inverse (first modulus)
  (declare (xargs :guard t))
  (mv-let (gcd s coefficient-t)
    (f11-poly-monic-extended-euclidean-gcd first modulus)
    (declare (ignore gcd coefficient-t))
    (f11-poly-remainder s modulus)))

(verify-guards f11-poly-monic-normalize)
(verify-guards f11-poly-divides-p)
(verify-guards f11-poly-common-divisor-p)
(verify-guards f11-poly-euclidean-gcd)
(verify-guards f11-poly-monic-euclidean-gcd)
(verify-guards f11-poly-monic-extended-euclidean-gcd)
(verify-guards f11-poly-modular-inverse)

(local
 (defthm f11-stack-canonical-implies-coefficient-list
   (implies (f11-canonical-polynomial-p xs)
            (f11-coefficient-list-p xs))
   :hints (("Goal" :in-theory (enable f11-canonical-polynomial-p
                                       f11-normalize f11-fix-coefficients
                                       f11-trim-trailing-zeros
                                       f11-coefficient-list-p)))))
(local
 (defthm f11-stack-normalize-canonical-list
   (implies (and (f11-coefficient-list-p xs)
                 (or (not (consp xs))
                     (not (equal (car (last xs)) 0))))
            (equal (f11-normalize xs) xs))
   :hints (("Goal" :induct (f11-trim-trailing-zeros xs)
            :in-theory (enable f11-normalize f11-fix-coefficients
                               f11-trim-trailing-zeros
                               f11-coefficient-list-p gfield::f11-fix
                               gfield::f11-element-p)))))
(local
 (defthm f11-stack-last-zero-not-normalized
   (implies (and (f11-coefficient-list-p xs) (consp xs)
                 (equal (car (last xs)) 0))
            (not (equal (f11-normalize xs) xs)))
   :hints (("Goal" :induct (f11-trim-trailing-zeros xs)
            :in-theory (enable f11-normalize f11-fix-coefficients
                               f11-trim-trailing-zeros
                               f11-coefficient-list-p gfield::f11-fix
                               gfield::f11-element-p)))))

; Keep the functional substitution visible and centralized: every concrete
; theorem below is a staged transport from the certified finite-field stack.
(defmacro def-f11-stack-law (name source formula &key (rule-classes ':rewrite))
  `(defthm ,name
     ,formula
     :rule-classes ,rule-classes
     :hints
     (("Goal"
       :in-theory (union-theories
                    '(f11-poly-monic-normalize f11-poly-divides-p
                      f11-poly-common-divisor-p f11-poly-euclidean-gcd
                      f11-poly-monic-euclidean-gcd
                      f11-poly-extended-euclidean-gcd
                      f11-poly-monic-extended-euclidean-gcd
                      f11-poly-modular-inverse
                      f11-poly-reduced-mul f11-poly-reduced-one
                      f11-polynomial-one
                      f11-normalize f11-fix-coefficients
                      f11-trim-trailing-zeros
                      f11-poly-add f11-poly-raw-add
                      f11-poly-neg f11-poly-raw-neg f11-poly-sub
                      f11-poly-scale f11-poly-raw-scale
                      f11-poly-mul f11-poly-raw-mul
                      f11-poly-degree f11-poly-leading-coefficient
                      f11-poly-divmod f11-poly-divmod-core
                      f11-poly-quotient f11-poly-remainder
                      f11-poly-division-step-core f11-monomial
                      f11-zero-prefix f11-poly-shift
                      f11-canonical-polynomial-p f11-coefficient-list-p
                      gfield::f11-zero gfield::f11-one
                      gfield::f11-div
                      gfield::f11-element-p pfield::fep)
                    (theory 'minimal-theory))
       :by (:functional-instance ,source
            (gfield::finite-field-element-p gfield::f11-element-p)
            (gfield::finite-field-fix gfield::f11-fix)
            (gfield::finite-field-zero gfield::f11-zero)
            (gfield::finite-field-one gfield::f11-one)
            (gfield::finite-field-add gfield::f11-add)
            (gfield::finite-field-mul gfield::f11-mul)
            (gfield::finite-field-neg gfield::f11-neg)
            (gfield::finite-field-inv gfield::f11-inv)
            (gfield::finite-field-rank gfield::f11-fix)
            (gfield::finite-field-unrank gfield::f11-fix)
            (gfield::finite-field-bound (lambda () 11))
            (finite-field-div gfield::f11-div)
            (finite-field-poly-fix-coefficients f11-fix-coefficients)
            (finite-field-poly-trim-trailing-zeros f11-trim-trailing-zeros)
            (finite-field-poly-normalize f11-normalize)
            (finite-field-coefficient-list-p f11-coefficient-list-p)
            (finite-field-polynomial-p f11-coefficient-list-p)
            (finite-field-canonical-polynomial-p f11-canonical-polynomial-p)
            (finite-field-poly-raw-add f11-poly-raw-add)
            (finite-field-poly-add f11-poly-add)
            (finite-field-poly-raw-neg f11-poly-raw-neg)
            (finite-field-poly-neg f11-poly-neg)
            (finite-field-poly-sub f11-poly-sub)
            (finite-field-poly-raw-scale f11-poly-raw-scale)
            (finite-field-poly-scale f11-poly-scale)
            (finite-field-poly-raw-mul f11-poly-raw-mul)
            (finite-field-poly-mul f11-poly-mul)
            (finite-field-poly-degree f11-poly-degree)
            (finite-field-poly-leading-coefficient f11-poly-leading-coefficient)
            (finite-field-poly-zero-prefix f11-zero-prefix)
            (finite-field-poly-shift f11-poly-shift)
            (finite-field-poly-monomial f11-monomial)
            (finite-field-poly-division-step-core f11-poly-division-step-core)
            (finite-field-poly-divmod-core f11-poly-divmod-core)
            (finite-field-poly-divmod f11-poly-divmod)
            (finite-field-poly-quotient f11-poly-quotient)
            (finite-field-poly-remainder f11-poly-remainder)
            (finite-field-poly-divides-p f11-poly-divides-p)
            (finite-field-poly-common-divisor-p f11-poly-common-divisor-p)
            (finite-field-poly-euclidean-gcd f11-poly-euclidean-gcd)
            (finite-field-poly-monic-normalize f11-poly-monic-normalize)
            (finite-field-poly-monic-euclidean-gcd f11-poly-monic-euclidean-gcd)
            (finite-field-poly-extended-euclidean-gcd
             f11-poly-extended-euclidean-gcd)
            (finite-field-poly-monic-extended-euclidean-gcd
             f11-poly-monic-extended-euclidean-gcd)
            (finite-field-polynomial-one f11-polynomial-one)
            (finite-field-poly-reduced-mul f11-poly-reduced-mul)
            (finite-field-poly-reduced-one f11-poly-reduced-one)
            (finite-field-poly-modular-inverse f11-poly-modular-inverse)))
      (and stable-under-simplificationp
           (list :use (append
                       '((:instance f11-poly-remainder-is-divmod-remainder)
                         f11-stack-canonical-implies-coefficient-list
                         f11-stack-normalize-canonical-list
                         f11-stack-last-zero-not-normalized)
                       (theory 'gfield::f11-finite-field-context-instance-theory)))))))

; Missing public remainder prerequisites needed by Euclidean clients.
(defthm f11-poly-remainder-canonical
  (f11-canonical-polynomial-p (f11-poly-remainder dividend modulus))
  :hints (("Goal" :use ((:instance f11-poly-divmod-remainder-canonical
                                   (f dividend) (g modulus))
                         (:instance f11-poly-remainder-is-divmod-remainder
                                   (f dividend) (g modulus))))))

(def-f11-stack-law f11-poly-reduced-mul-commutative
  finite-field-poly-reduced-mul-commutative
  (equal (f11-poly-reduced-mul a b modulus)
         (f11-poly-reduced-mul b a modulus)) :rule-classes nil)

; Raw and monic GCD aggregate boundaries.
(def-f11-stack-law f11-poly-euclidean-gcd-raw-correct
  finite-field-poly-euclidean-gcd-raw-correct
  (and (f11-poly-common-divisor-p
        (f11-poly-euclidean-gcd first second) first second)
       (implies (f11-poly-common-divisor-p divisor first second)
                (f11-poly-divides-p divisor
                                    (f11-poly-euclidean-gcd first second))))
  :rule-classes nil)
(def-f11-stack-law f11-poly-euclidean-gcd-canonical
  finite-field-poly-euclidean-gcd-canonical
  (f11-canonical-polynomial-p (f11-poly-euclidean-gcd first second)))
(def-f11-stack-law f11-poly-normalize-of-euclidean-gcd
  finite-field-poly-normalize-of-euclidean-gcd
  (equal (f11-normalize (f11-poly-euclidean-gcd first second))
         (f11-poly-euclidean-gcd first second)))

(def-f11-stack-law f11-poly-monic-euclidean-gcd-is-monic-normalize
  finite-field-poly-monic-euclidean-gcd-is-monic-normalize
  (equal (f11-poly-monic-euclidean-gcd first second)
         (f11-poly-monic-normalize
          (f11-poly-euclidean-gcd first second))) :rule-classes nil)

(def-f11-stack-law f11-poly-monic-euclidean-gcd-correct
  finite-field-poly-monic-euclidean-gcd-correct
  (and (f11-poly-common-divisor-p
        (f11-poly-monic-euclidean-gcd first second) first second)
       (implies (f11-poly-common-divisor-p divisor first second)
                (f11-poly-divides-p divisor
                                    (f11-poly-monic-euclidean-gcd first second))))
  :rule-classes nil)
(def-f11-stack-law f11-canonical-polynomial-p-of-poly-monic-euclidean-gcd
  finite-field-canonical-polynomial-p-of-poly-monic-euclidean-gcd
  (f11-canonical-polynomial-p
   (f11-poly-monic-euclidean-gcd first second)))
(def-f11-stack-law f11-consp-of-poly-monic-euclidean-gcd
  finite-field-consp-of-poly-monic-euclidean-gcd
  (equal (consp (f11-poly-monic-euclidean-gcd first second))
         (consp (f11-poly-euclidean-gcd first second))) :rule-classes nil)
(def-f11-stack-law f11-poly-leading-coefficient-of-poly-monic-euclidean-gcd
  finite-field-poly-leading-coefficient-of-poly-monic-euclidean-gcd
  (equal (f11-poly-leading-coefficient
          (f11-poly-monic-euclidean-gcd first second))
         (if (consp (f11-poly-euclidean-gcd first second))
             (gfield::f11-one) (gfield::f11-zero)))
  :rule-classes nil)

; Raw XGCD operations and stable correctness boundary.
(def-f11-stack-law f11-poly-extended-euclidean-gcd-zero-second
  finite-field-poly-extended-euclidean-gcd-zero-second
  (implies (not (consp (f11-normalize second)))
           (equal (f11-poly-extended-euclidean-gcd first second)
                  (mv (f11-normalize first)
                      (list (gfield::f11-one)) nil))) :rule-classes nil)
(def-f11-stack-law f11-poly-extended-euclidean-gcd-raw-specification
  finite-field-poly-extended-euclidean-gcd-raw-specification
  (and (equal (mv-nth 0 (f11-poly-extended-euclidean-gcd first second))
              (f11-poly-euclidean-gcd first second))
       (equal (f11-poly-add
               (f11-poly-mul
                (mv-nth 1 (f11-poly-extended-euclidean-gcd first second)) first)
               (f11-poly-mul
                (mv-nth 2 (f11-poly-extended-euclidean-gcd first second)) second))
              (f11-poly-euclidean-gcd first second))
       (f11-canonical-polynomial-p
        (mv-nth 0 (f11-poly-extended-euclidean-gcd first second)))
       (f11-canonical-polynomial-p
        (mv-nth 1 (f11-poly-extended-euclidean-gcd first second)))
       (f11-canonical-polynomial-p
        (mv-nth 2 (f11-poly-extended-euclidean-gcd first second))))
  :rule-classes nil)

; Monic XGCD and its unconditional scaled Bezout boundary.
(def-f11-stack-law f11-poly-monic-extended-euclidean-gcd-is-scaled-xgcd
  finite-field-poly-monic-extended-euclidean-gcd-is-scaled-xgcd
  (equal (f11-poly-monic-extended-euclidean-gcd first second)
         (mv-let (gcd s coefficient-t)
           (f11-poly-extended-euclidean-gcd first second)
           (let ((scale (gfield::f11-inv
                         (f11-poly-leading-coefficient gcd))))
             (mv (f11-poly-monic-normalize gcd)
                 (f11-poly-scale scale s)
                 (f11-poly-scale scale coefficient-t))))) :rule-classes nil)
(def-f11-stack-law f11-poly-monic-extended-euclidean-gcd-bezout
  finite-field-poly-monic-extended-euclidean-gcd-bezout
  (equal (f11-poly-add
          (f11-poly-mul
           (mv-nth 1 (f11-poly-monic-extended-euclidean-gcd first second)) first)
          (f11-poly-mul
           (mv-nth 2 (f11-poly-monic-extended-euclidean-gcd first second)) second))
         (f11-poly-monic-euclidean-gcd first second)) :rule-classes nil)
(def-f11-stack-law f11-poly-monic-extended-euclidean-gcd-specification
  finite-field-poly-monic-extended-euclidean-gcd-specification
  (and (equal (mv-nth 0 (f11-poly-monic-extended-euclidean-gcd first second))
              (f11-poly-monic-euclidean-gcd first second))
       (equal (f11-poly-add
               (f11-poly-mul
                (mv-nth 1 (f11-poly-monic-extended-euclidean-gcd first second)) first)
               (f11-poly-mul
                (mv-nth 2 (f11-poly-monic-extended-euclidean-gcd first second)) second))
              (f11-poly-monic-euclidean-gcd first second))
       (f11-canonical-polynomial-p
        (mv-nth 0 (f11-poly-monic-extended-euclidean-gcd first second)))
       (f11-canonical-polynomial-p
        (mv-nth 1 (f11-poly-monic-extended-euclidean-gcd first second)))
       (f11-canonical-polynomial-p
        (mv-nth 2 (f11-poly-monic-extended-euclidean-gcd first second)))
       (equal (f11-poly-leading-coefficient
               (mv-nth 0 (f11-poly-monic-extended-euclidean-gcd first second)))
              (if (consp (f11-poly-euclidean-gcd first second))
             (gfield::f11-one) (gfield::f11-zero))))
  :rule-classes nil)

(def-f11-stack-law f11-poly-monic-extended-euclidean-gcd-bezout-when-one
  finite-field-poly-monic-extended-euclidean-gcd-bezout-when-one
  (implies (equal (f11-poly-monic-euclidean-gcd first second)
                  (list (gfield::f11-one)))
           (equal (f11-poly-add
                   (f11-poly-mul
                    (mv-nth 1 (f11-poly-monic-extended-euclidean-gcd first second)) first)
                   (f11-poly-mul
                    (mv-nth 2 (f11-poly-monic-extended-euclidean-gcd first second)) second))
                  (list (gfield::f11-one)))) :rule-classes nil)

; Modular inverse projection, shape, bridge, and conditional correctness.
(def-f11-stack-law f11-poly-modular-inverse-definition
  finite-field-poly-modular-inverse-definition
  (equal (f11-poly-modular-inverse first modulus)
         (f11-poly-remainder
          (mv-nth 1 (f11-poly-monic-extended-euclidean-gcd first modulus))
          modulus)) :rule-classes nil)
(def-f11-stack-law f11-poly-modular-inverse-canonical
  finite-field-poly-modular-inverse-canonical
  (f11-canonical-polynomial-p (f11-poly-modular-inverse first modulus)))
(def-f11-stack-law f11-poly-normalize-of-poly-modular-inverse
  finite-field-poly-normalize-of-poly-modular-inverse
  (equal (f11-normalize (f11-poly-modular-inverse first modulus))
         (f11-poly-modular-inverse first modulus)))
(def-f11-stack-law f11-poly-remainder-of-poly-mul-poly-modular-inverse
  finite-field-poly-remainder-of-poly-mul-poly-modular-inverse
  (equal (f11-poly-remainder
          (f11-poly-mul (f11-poly-modular-inverse first modulus) first) modulus)
         (f11-poly-remainder
          (f11-poly-mul
           (mv-nth 1 (f11-poly-monic-extended-euclidean-gcd first modulus)) first)
          modulus)) :rule-classes nil)
(def-f11-stack-law f11-poly-modular-inverse-correct
  finite-field-poly-modular-inverse-correct
  (implies (equal (f11-poly-monic-euclidean-gcd first modulus)
                  (f11-polynomial-one))
           (equal (f11-poly-remainder
                   (f11-poly-mul (f11-poly-modular-inverse first modulus) first)
                   modulus)
                  (f11-poly-remainder (f11-polynomial-one) modulus)))
  :rule-classes nil)
(def-f11-stack-law f11-poly-reduced-mul-modular-inverse-left
  finite-field-poly-reduced-mul-modular-inverse-left
  (implies (equal (f11-poly-monic-euclidean-gcd first modulus)
                  (f11-polynomial-one))
           (equal (f11-poly-reduced-mul
                   (f11-poly-modular-inverse first modulus) first modulus)
                  (f11-poly-reduced-one modulus))) :rule-classes nil)
(def-f11-stack-law f11-poly-reduced-mul-modular-inverse-right
  finite-field-poly-reduced-mul-modular-inverse-right
  (implies (equal (f11-poly-monic-euclidean-gcd first modulus)
                  (f11-polynomial-one))
           (equal (f11-poly-reduced-mul
                   first (f11-poly-modular-inverse first modulus) modulus)
                  (f11-poly-reduced-one modulus))) :rule-classes nil)
(def-f11-stack-law f11-poly-modular-inverse-remainder-one
  finite-field-poly-modular-inverse-remainder-one
  (implies (and (equal (f11-poly-monic-euclidean-gcd first modulus)
                       (f11-polynomial-one))
                (consp (f11-normalize modulus))
                (< 0 (f11-poly-degree (f11-normalize modulus))))
           (equal (f11-poly-remainder
                   (f11-poly-mul (f11-poly-modular-inverse first modulus) first)
                   modulus)
                  (f11-polynomial-one))) :rule-classes nil)
(def-f11-stack-law f11-poly-modular-inverse-specification
  finite-field-poly-modular-inverse-specification
  (and (f11-canonical-polynomial-p (f11-poly-modular-inverse first modulus))
       (equal (f11-normalize (f11-poly-modular-inverse first modulus))
              (f11-poly-modular-inverse first modulus))
       (implies (equal (f11-poly-monic-euclidean-gcd first modulus)
                       (f11-polynomial-one))
                (and (equal (f11-poly-reduced-mul
                             (f11-poly-modular-inverse first modulus)
                             first modulus)
                            (f11-poly-reduced-one modulus))
                     (equal (f11-poly-reduced-mul
                             first (f11-poly-modular-inverse first modulus)
                             modulus)
                            (f11-poly-reduced-one modulus)))))
  :rule-classes nil)
