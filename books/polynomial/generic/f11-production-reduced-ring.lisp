(in-package "GPOLY")

(include-book "finite-field-reduced-ring")
(include-book "../../schoof/f11-division-polynomial-functional-instance")

; The concrete instance uses the same generated definitions as the production
; finite-field-prefixed algorithms; only the coefficient operations change.
(def-monomial-instance f11-zero-prefix f11-poly-shift f11-monomial f11-normalize
  gfield::f11-fix gfield::f11-zero)

(def-division-step-instance
  f11-poly-division-step-core f11-poly-division-step
  f11-poly-division-step-term f11-poly-division-step-next
  f11-poly-degree f11-poly-leading-coefficient f11-monomial
  f11-poly-sub f11-poly-mul f11-normalize gfield::f11-div)

(local
 (defthm f11-canonical-implies-coefficient-list-for-instance
   (implies (f11-canonical-polynomial-p xs)
            (f11-coefficient-list-p xs))
   :hints (("Goal" :in-theory (enable f11-canonical-polynomial-p
                                       f11-normalize
                                       f11-fix-coefficients
                                       f11-trim-trailing-zeros
                                       f11-coefficient-list-p)))))

(local
 (defthm f11-normalize-canonical-list-for-instance
   (implies (and (f11-coefficient-list-p xs)
                 (or (not (consp xs))
                     (not (equal (car (last xs)) 0))))
            (equal (f11-normalize xs) xs))
   :hints (("Goal" :induct (f11-trim-trailing-zeros xs)
            :in-theory (enable f11-normalize f11-fix-coefficients
                               f11-trim-trailing-zeros
                               f11-coefficient-list-p
                               gfield::f11-fix
                               gfield::f11-element-p)))))

(local
 (defthm f11-last-zero-not-normalized-for-instance
   (implies (and (f11-coefficient-list-p xs) (consp xs)
                 (equal (car (last xs)) 0))
            (not (equal (f11-normalize xs) xs)))
   :hints (("Goal" :induct (f11-trim-trailing-zeros xs)
            :in-theory (enable f11-normalize f11-fix-coefficients
                               f11-trim-trailing-zeros
                               f11-coefficient-list-p
                               gfield::f11-fix
                               gfield::f11-element-p)))))

; The generated divmod recursion is totalized by dividend normalization and
; uses the normalized remainder length as its measure.  This concrete decrease
; lemma is the F11 instance of the production finite-field theorem.
(defthm f11-poly-division-step-core-length-decreases
  (implies (and (f11-canonical-polynomial-p remainder)
                (f11-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (f11-poly-degree divisor)
                    (f11-poly-degree remainder)))
           (< (len (cdr (f11-poly-division-step-core remainder divisor)))
              (len remainder)))
  :hints (("Goal" :in-theory
           (theory 'minimal-theory)
           :by (:functional-instance
                finite-field-poly-division-step-core-length-decreases
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
                (finite-field-poly-leading-coefficient
                 f11-poly-leading-coefficient)
                (finite-field-poly-zero-prefix f11-zero-prefix)
                (finite-field-poly-shift f11-poly-shift)
                (finite-field-poly-monomial f11-monomial)
                (finite-field-poly-division-step-core
                 f11-poly-division-step-core)))
          (and stable-under-simplificationp
               (list :use (append '(f11-canonical-implies-coefficient-list-for-instance
                                    f11-normalize-canonical-list-for-instance
                                    f11-last-zero-not-normalized-for-instance)
                                  (theory 'gfield::f11-finite-field-context-instance-theory))
                     :in-theory
                     (list 'quote
                           (union-theories
                            (theory 'gfield::f11-finite-field-context-instance-theory)
                            (union-theories
                             '((:definition f11-poly-division-step-core)
                               (:definition f11-monomial)
                               (:definition f11-zero-prefix)
                               (:definition f11-poly-sub)
                               (:definition f11-poly-add)
                               (:definition f11-poly-neg)
                               (:definition f11-poly-mul)
                               (:definition f11-poly-raw-add)
                               (:definition f11-poly-raw-neg)
                               (:definition f11-poly-raw-scale)
                               (:definition f11-poly-raw-mul)
                               (:definition f11-normalize)
                               (:definition f11-fix-coefficients)
                               (:definition f11-trim-trailing-zeros)
                               (:definition f11-coefficient-list-p)
                               (:definition f11-canonical-polynomial-p)
                               (:definition f11-poly-degree)
                               (:definition f11-poly-leading-coefficient)
                               (:definition gfield::f11-div)
                               (:definition gfield::f11-zero)
                               (:definition gfield::f11-one))
                             (theory 'minimal-theory))))))))

(def-divmod-instance
  f11-poly-divmod-core f11-poly-divmod f11-canonical-polynomial-p
  f11-poly-degree f11-poly-division-step-core f11-poly-add f11-normalize
  f11-poly-division-step-core-length-decreases)
(def-divmod-projections-instance
  f11-poly-quotient f11-poly-remainder f11-poly-divmod)

(defun f11-polynomial-one () '(1))
(defun f11-poly-reduced-add (left right modulus)
  (f11-poly-remainder (f11-poly-add left right) modulus))
(defun f11-poly-reduced-neg (polynomial modulus)
  (f11-poly-remainder (f11-poly-neg polynomial) modulus))
(defun f11-poly-reduced-sub (left right modulus)
  (f11-poly-remainder (f11-poly-sub left right) modulus))
(defun f11-poly-reduced-mul (left right modulus)
  (f11-poly-remainder (f11-poly-mul left right) modulus))
(defun f11-poly-reduced-one (modulus)
  (f11-poly-remainder (f11-polynomial-one) modulus))

(verify-guards f11-zero-prefix)
(verify-guards f11-coefficient-list-p)
(verify-guards f11-canonical-polynomial-p)
(verify-guards f11-poly-shift)
(verify-guards f11-monomial)
(verify-guards f11-poly-division-step-core)
(verify-guards f11-poly-division-step)
(verify-guards f11-poly-division-step-term)
(verify-guards f11-poly-division-step-next)
(verify-guards f11-poly-divmod-core)
(verify-guards f11-poly-divmod)
(verify-guards f11-poly-quotient)
(verify-guards f11-poly-remainder)
(verify-guards f11-polynomial-one)
(verify-guards f11-poly-reduced-add)
(verify-guards f11-poly-reduced-neg)
(verify-guards f11-poly-reduced-sub)
(verify-guards f11-poly-reduced-mul)
(verify-guards f11-poly-reduced-one)

(defthm f11-poly-reduced-operation-definitions
  (and (equal (f11-poly-reduced-add left right modulus)
              (f11-poly-remainder (f11-poly-add left right) modulus))
       (equal (f11-poly-reduced-neg left modulus)
              (f11-poly-remainder (f11-poly-neg left) modulus))
       (equal (f11-poly-reduced-sub left right modulus)
              (f11-poly-remainder (f11-poly-sub left right) modulus))
       (equal (f11-poly-reduced-mul left right modulus)
              (f11-poly-remainder (f11-poly-mul left right) modulus))
       (equal (f11-poly-reduced-one modulus)
              (f11-poly-remainder '(1) modulus))))

; Narrow semantic transport for the production remainder interface.  These are
; the laws needed by quotient-coordinate clients; the generated F11 divider
; remains the only concrete reduction implementation.
(defmacro def-f11-production-remainder-law (name source formula)
  `(defthm ,name
     ,formula
     :rule-classes nil
     :hints
     (("Goal"
       :in-theory (union-theories
                   (theory 'gfield::f11-finite-field-context-instance-theory)
                   (union-theories
                    '((:definition f11-poly-divmod-core)
                      (:definition f11-poly-divmod)
                      (:definition f11-poly-remainder)
                      (:definition f11-poly-division-step-core)
                      (:definition f11-normalize)
                      (:definition f11-fix-coefficients)
                      (:definition f11-trim-trailing-zeros)
                      (:definition f11-canonical-polynomial-p)
                      (:definition f11-poly-degree)
                      (:definition gfield::f11-div)
                      (:definition gfield::f11-zero)
                      (:definition gfield::f11-one))
                    (theory 'minimal-theory)))
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
            (finite-field-poly-remainder f11-poly-remainder)))
      (and stable-under-simplificationp
           (list
            :use (append
                  '(f11-canonical-implies-coefficient-list-for-instance
                    f11-normalize-canonical-list-for-instance
                    f11-last-zero-not-normalized-for-instance
                    f11-poly-division-step-core-length-decreases)
                  (theory 'gfield::f11-finite-field-context-instance-theory))
            :in-theory
            (list 'quote
                  (union-theories
                   '((:definition f11-poly-divmod-core)
                     (:definition f11-poly-divmod)
                     (:definition f11-poly-quotient)
                     (:definition f11-poly-remainder)
                     (:definition f11-poly-division-step-core)
                     (:definition f11-monomial)
                     (:definition f11-zero-prefix)
                     (:definition f11-poly-add)
                     (:definition f11-poly-neg)
                     (:definition f11-poly-sub)
                     (:definition f11-poly-scale)
                     (:definition f11-poly-mul)
                     (:definition f11-poly-raw-add)
                     (:definition f11-poly-raw-neg)
                     (:definition f11-poly-raw-scale)
                     (:definition f11-poly-raw-mul)
                     (:definition f11-normalize)
                     (:definition f11-fix-coefficients)
                     (:definition f11-trim-trailing-zeros)
                     (:definition f11-coefficient-list-p)
                     (:definition f11-canonical-polynomial-p)
                     (:definition f11-poly-degree)
                     (:definition f11-poly-leading-coefficient)
                     (:definition gfield::f11-div)
                     (:definition gfield::f11-zero)
                     (:definition gfield::f11-one))
                   (theory 'minimal-theory))))))))

(def-f11-production-remainder-law
  f11-poly-remainder-of-normalize-dividend
  finite-field-poly-remainder-of-normalize-dividend
  (equal (f11-poly-remainder (f11-normalize dividend) modulus)
         (f11-poly-remainder dividend modulus)))

(def-f11-production-remainder-law
  f11-poly-remainder-idempotent
  finite-field-poly-remainder-idempotent
  (equal (f11-poly-remainder (f11-poly-remainder dividend modulus) modulus)
         (f11-poly-remainder dividend modulus)))

(def-f11-production-remainder-law
  f11-poly-remainder-of-poly-add-remainders
  finite-field-poly-remainder-of-poly-add-remainders
  (equal (f11-poly-remainder (f11-poly-add left right) modulus)
         (f11-poly-remainder
          (f11-poly-add (f11-poly-remainder left modulus)
                        (f11-poly-remainder right modulus))
          modulus)))

(def-f11-production-remainder-law
  f11-poly-remainder-of-poly-mul-remainders
  finite-field-poly-remainder-of-poly-mul-remainders
  (equal (f11-poly-remainder (f11-poly-mul left right) modulus)
         (f11-poly-remainder
          (f11-poly-mul (f11-poly-remainder left modulus)
                        (f11-poly-remainder right modulus))
          modulus)))

(def-f11-production-remainder-law
  f11-poly-remainder-zero-dividend
  finite-field-poly-remainder-zero-dividend
  (equal (f11-poly-remainder nil modulus) nil))

(def-f11-production-remainder-law
  f11-poly-remainder-self
  finite-field-poly-remainder-self
  (equal (f11-poly-remainder modulus modulus) nil))
