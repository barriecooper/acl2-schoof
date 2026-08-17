(in-package "GPOLY")

(include-book "runtime-p-monic-divmod")

; The PFIELD polynomial layer predates recursive division.  These definitions
; expose the established generic long-division template at that layer; they do
; not introduce a new recursion or a runtime-p implementation.
(def-monomial-instance
  pfield-zero-prefix pfield-poly-shift pfield-monomial pfield-normalize
  gfield::pfield-fix gfield::pfield-zero)

(def-division-step-instance
  pfield-poly-division-step-core pfield-poly-division-step
  pfield-poly-division-step-term pfield-poly-division-step-next
  pfield-poly-degree pfield-poly-leading-coefficient pfield-monomial
  pfield-poly-sub pfield-poly-mul pfield-normalize gfield::pfield-div)

; This is the generic structural recognizer at the PFIELD operations.  The
; older PFIELD fixed-point recognizer remains unchanged; the generated
; long-division recursion uses this transparent functional-instance target.
(defun pfield-division-canonical-polynomial-p (xs)
  (and (pfield-coefficient-list-p xs)
       (or (not (consp xs))
           (not (equal (car (last xs)) (gfield::pfield-zero))))))

(local (defthm pfield-coefficient-list-p-of-nil-for-division-instance
  (equal (pfield-coefficient-list-p nil) t)
  :hints (("Goal" :in-theory (enable pfield-coefficient-list-p)))))

(local (defthm runtime-p-canonical-pfield-division-correspondence
  (equal (runtime-p-canonical-polynomial-p
          xs (gfield::pfield-modulus))
         (pfield-division-canonical-polynomial-p xs))
  :hints (("Goal"
           :induct (runtime-p-coefficient-list-p
                    xs (gfield::pfield-modulus))
           :in-theory (enable runtime-p-canonical-polynomial-p
                              pfield-division-canonical-polynomial-p
                              runtime-p-coefficient-list-p
                              pfield-coefficient-list-p
                              runtime-p-coefficient-p
                              runtime-p-effective-modulus-of-pfield-modulus
                              gfield::pfield-element-p)))))

(local (defthm pfield-division-monic-implies-consp
  (implies (and (pfield-division-canonical-polynomial-p divisor)
                (equal (pfield-poly-leading-coefficient divisor)
                       (gfield::pfield-one)))
           (consp divisor))
  :hints (("Goal"
           :use gfield::pfield-zero-not-equal-pfield-one
           :in-theory (enable pfield-poly-leading-coefficient
                              pfield-division-canonical-polynomial-p)))))

(local (defthm pfield-division-canonical-is-existing-canonical
  (equal (pfield-division-canonical-polynomial-p xs)
         (pfield-canonical-polynomial-p xs))
  :hints (("Goal"
           :use ((:instance runtime-p-canonical-pfield-division-correspondence)
                 (:instance runtime-p-canonical-polynomial-p-of-normalize
                            (xs xs) (p (gfield::pfield-modulus)))
                 (:instance runtime-p-normalize-when-canonical
                            (xs xs) (p (gfield::pfield-modulus)))
                 (:instance runtime-p-normalize-pfield-correspondence
                            (x xs)))
           :in-theory (enable pfield-canonical-polynomial-p)))))

(local (defthm runtime-p-degree-pfield-correspondence
  (equal (runtime-p-poly-degree poly (gfield::pfield-modulus))
         (pfield-poly-degree poly))
  :hints (("Goal" :use ((:instance runtime-p-normalize-pfield-correspondence (x poly)))
           :in-theory (e/d (runtime-p-poly-degree pfield-poly-degree)
                           (runtime-p-normalize pfield-normalize))))))

(local (defthm runtime-p-leading-pfield-correspondence
  (equal (runtime-p-poly-leading-coefficient
          poly (gfield::pfield-modulus))
         (pfield-poly-leading-coefficient poly))
  :hints (("Goal" :use ((:instance runtime-p-normalize-pfield-correspondence (x poly)))
           :in-theory (e/d (runtime-p-poly-leading-coefficient
                             pfield-poly-leading-coefficient)
                           (runtime-p-normalize pfield-normalize))))))

(local (defthm runtime-p-normalize-pfield-rewrite
  (equal (runtime-p-normalize x (gfield::pfield-modulus))
         (pfield-normalize x))
  :hints (("Goal" :use runtime-p-normalize-pfield-correspondence))))
(local (defthm runtime-p-poly-add-pfield-rewrite
  (equal (runtime-p-poly-add x y (gfield::pfield-modulus))
         (pfield-poly-add x y))
  :hints (("Goal" :use runtime-p-poly-add-pfield-correspondence))))
(local (defthm runtime-p-poly-sub-pfield-rewrite
  (equal (runtime-p-poly-sub x y (gfield::pfield-modulus))
         (pfield-poly-sub x y))
  :hints (("Goal" :use runtime-p-poly-sub-pfield-correspondence))))
(local (defthm runtime-p-poly-mul-pfield-rewrite
  (equal (runtime-p-poly-mul x y (gfield::pfield-modulus))
         (pfield-poly-mul x y))
  :hints (("Goal" :use runtime-p-poly-mul-pfield-correspondence))))

(local (defthm runtime-p-monomial-is-pfield-zero-prefix-when-fixed
  (implies (and (equal (runtime-p-coefficient-fix
                        a (gfield::pfield-modulus)) a)
                (not (equal a (runtime-p-zero (gfield::pfield-modulus)))))
           (equal (runtime-p-poly-monomial a n (gfield::pfield-modulus))
                  (pfield-zero-prefix
                   (nfix n) (list a))))
  :hints (("Goal" :induct (runtime-p-poly-monomial
                            a n (gfield::pfield-modulus))
           :in-theory (enable runtime-p-poly-monomial pfield-zero-prefix)))))

(local (defthm runtime-p-monomial-pfield-correspondence
  (equal (runtime-p-poly-monomial a n (gfield::pfield-modulus))
         (pfield-monomial a n))
  :hints (("Goal"
           :use ((:instance runtime-p-monomial-is-pfield-zero-prefix-when-fixed
                            (a (runtime-p-coefficient-fix
                                a (gfield::pfield-modulus)))))
           :in-theory (enable pfield-monomial pfield-zero-prefix
                                      runtime-p-poly-monomial
                                      runtime-p-coefficient-fix-pfield-correspondence
                                      runtime-p-zero-pfield-correspondence)))))

(local (defthm pfield-inv-one-for-monic-correspondence
  (equal (gfield::pfield-inv (gfield::pfield-one))
         (gfield::pfield-one))
  :hints (("Goal"
           :use ((:instance gfield::pfield-mul-inverse-left
                            (x (gfield::pfield-one)))
                 (:instance gfield::pfield-mul-one-right-for-power
                            (x (gfield::pfield-inv
                                (gfield::pfield-one)))))))))

(local (defthm pfield-div-by-one-for-monic-correspondence
  (equal (gfield::pfield-div x (gfield::pfield-one))
         (gfield::pfield-fix x))
  :hints (("Goal" :in-theory (enable gfield::pfield-div)
           :use (pfield-inv-one-for-monic-correspondence
                 (:instance gfield::pfield-mul-one-left
                            (x x)))))))

(local (defthm runtime-p-step-core-pfield-correspondence
  (implies (equal (pfield-poly-leading-coefficient divisor)
                  (gfield::pfield-one))
           (equal (runtime-p-monic-division-step-core
                   remainder divisor (gfield::pfield-modulus))
                  (pfield-poly-division-step-core remainder divisor)))
  :hints (("Goal" :in-theory (e/d (runtime-p-monic-division-step-core
                             pfield-poly-division-step-core
                             runtime-p-one-pfield-correspondence)
                            (gfield::pfield-div pfield-poly-sub
                             pfield-poly-mul runtime-p-poly-sub
                             runtime-p-poly-mul))
           :use ((:instance pfield-div-by-one-for-monic-correspondence
                            (x (pfield-poly-leading-coefficient remainder))))))))

(local (defthm runtime-p-step-pfield-core-correspondence
  (implies (and (runtime-p-canonical-polynomial-p
                 remainder (gfield::pfield-modulus))
                (runtime-p-canonical-polynomial-p
                 divisor (gfield::pfield-modulus))
                (equal (pfield-poly-leading-coefficient divisor)
                       (gfield::pfield-one)))
           (equal (runtime-p-monic-division-step
                   remainder divisor (gfield::pfield-modulus))
                  (pfield-poly-division-step-core remainder divisor)))
  :hints (("Goal"
           :use ((:instance runtime-p-step-core-pfield-correspondence)
                 (:instance runtime-p-normalize-when-canonical
                            (xs remainder)
                            (p (gfield::pfield-modulus)))
                 (:instance runtime-p-normalize-when-canonical
                            (xs divisor)
                            (p (gfield::pfield-modulus))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(runtime-p-monic-division-step
              runtime-p-normalize-pfield-rewrite))))))

(local (defthm pfield-step-core-length-decreases
  (implies (and (pfield-division-canonical-polynomial-p remainder)
                (pfield-division-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (pfield-poly-degree divisor)
                    (pfield-poly-degree remainder)))
           (< (len (cdr (pfield-poly-division-step-core remainder divisor)))
              (len remainder)))
  :rule-classes nil
  :hints
  (("Goal"
    :by (:functional-instance
         poly-division-step-core-length-decreases
         (gfield::field-element-p gfield::pfield-element-p)
         (gfield::field-fix gfield::pfield-fix)
         (gfield::field-zero gfield::pfield-zero)
         (gfield::field-one gfield::pfield-one)
         (gfield::field-add gfield::pfield-add)
         (gfield::field-mul gfield::pfield-mul)
         (gfield::field-neg gfield::pfield-neg)
         (gfield::field-inv gfield::pfield-inv)
         (gfield::field-div gfield::pfield-div)
         (fix-coefficients pfield-fix-coefficients)
         (trim-trailing-zeros pfield-trim-trailing-zeros)
         (normalize pfield-normalize)
         (coefficient-list-p pfield-coefficient-list-p)
         (canonical-polynomial-p pfield-division-canonical-polynomial-p)
         (raw-add pfield-raw-add)
         (poly-add pfield-poly-add)
         (raw-neg pfield-raw-neg)
         (poly-neg pfield-poly-neg)
         (poly-sub pfield-poly-sub)
         (raw-scale pfield-raw-scale)
         (raw-mul pfield-raw-mul)
         (poly-mul pfield-poly-mul)
         (zero-prefix pfield-zero-prefix)
         (monomial pfield-monomial)
         (poly-degree pfield-poly-degree)
         (poly-leading-coefficient pfield-poly-leading-coefficient)
         (poly-division-step-core pfield-poly-division-step-core)
         (poly-division-step-next pfield-poly-division-step-next))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 28.2"
    :use ((:instance gfield::pfield-mul-inverse-left
                     (x gfield::x))
          (:instance gfield::pfield-mul-commutative
                     (x gfield::x)
                     (y (gfield::pfield-inv gfield::x))))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 56.4"
    :use ((:instance pfield-poly-division-step-core))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 56.3"
    :use ((:instance pfield-poly-division-step-core))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 56.2"
    :use ((:instance pfield-poly-division-step-core))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 56.1"
    :use ((:instance pfield-poly-division-step-core))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 55.2"
    :use ((:instance pfield-poly-leading-coefficient-semantics))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 55.1"
    :use ((:instance pfield-poly-leading-coefficient-semantics))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 54"
    :use ((:instance pfield-normalize))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 53.2"
    :use ((:instance pfield-fix-coefficients))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 53.1"
    :use ((:instance pfield-fix-coefficients))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 52"
    :use ((:instance gfield::pfield-mul-inverse-left
                     (x gfield::x)))
    :in-theory (theory 'minimal-theory))
   (and stable-under-simplificationp
        '(:use (gfield::pfield-inv-of-zero
                gfield::pfield-mul-left-distributive
                gfield::pfield-mul-one-left
                gfield::pfield-mul-commutative
                gfield::pfield-mul-associative
                gfield::pfield-add-inverse-left
                gfield::pfield-add-zero-left
                gfield::pfield-add-commutative
                gfield::pfield-add-associative
                gfield::pfield-neg-of-fix
                gfield::pfield-inv-of-fix
                gfield::pfield-mul-of-fixes
                gfield::pfield-mul-fix-left
                gfield::pfield-mul-fix-right
                gfield::pfield-add-of-fixes
                gfield::pfield-add-fix-left
                gfield::pfield-add-fix-right
                gfield::pfield-element-p-of-pfield-zero
                gfield::pfield-element-p-of-pfield-one
                gfield::pfield-zero-not-equal-pfield-one
                gfield::pfield-fix-of-zero
                gfield::pfield-fix-of-one
                gfield::pfield-element-p-of-pfield-add
                gfield::pfield-element-p-of-pfield-mul
                gfield::pfield-element-p-of-pfield-neg
                gfield::pfield-element-p-of-pfield-inv
                gfield::pfield-element-p-of-pfield-fix
                gfield::booleanp-of-pfield-element-p
                gfield::pfield-fix-when-pfield-element-p
                gfield::pfield-fix-idempotent
                gfield::pfield-fix-of-pfield-add
                gfield::pfield-fix-of-pfield-mul
                gfield::pfield-fix-of-pfield-neg
                gfield::pfield-fix-of-pfield-inv
                gfield::pfield-mul-fixed-congruence
                gfield::pfield-add-fixed-congruence
                gfield::pfield-zero
                gfield::pfield-div
                pfield-trim-trailing-zeros
                pfield-monomial
                pfield-zero-prefix
                pfield-raw-add pfield-poly-add
                pfield-raw-neg pfield-poly-neg pfield-poly-sub
                pfield-raw-scale pfield-raw-mul pfield-poly-mul
                pfield-division-canonical-polynomial-p
                pfield-coefficient-list-p
                pfield-coefficient-list-p-of-nil-for-division-instance
                pfield-poly-degree-semantics)
          :in-theory (theory 'minimal-theory))))))

(local (defthm pfield-step-core-length-decreases-for-existing-canonical
  (implies (and (pfield-canonical-polynomial-p remainder)
                (pfield-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (pfield-poly-degree divisor)
                    (pfield-poly-degree remainder)))
           (< (len (cdr (pfield-poly-division-step-core remainder divisor)))
              (len remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pfield-step-core-length-decreases))
           :in-theory (enable
                       pfield-division-canonical-is-existing-canonical)))))

; The generic PFIELD divmod supports this monic correspondence boundary.  Its
; recursion is generated by DEF-DIVMOD-INSTANCE, the repository's established
; division implementation template.
(def-divmod-instance
  pfield-poly-divmod-core pfield-poly-divmod pfield-canonical-polynomial-p
  pfield-poly-degree pfield-poly-division-step-core pfield-poly-add
  pfield-normalize
  pfield-step-core-length-decreases-for-existing-canonical)
(def-divmod-projections-instance
  pfield-poly-quotient pfield-poly-remainder pfield-poly-divmod)

(local (defthm runtime-p-core-pfield-correspondence
  (implies (and (equal (pfield-poly-leading-coefficient divisor)
                       (gfield::pfield-one))
                (runtime-p-canonical-polynomial-p quotient
                                                  (gfield::pfield-modulus))
                (runtime-p-canonical-polynomial-p remainder
                                                  (gfield::pfield-modulus))
                (runtime-p-canonical-polynomial-p divisor
                                                  (gfield::pfield-modulus)))
           (equal (runtime-p-monic-divmod-core
                   quotient remainder divisor (gfield::pfield-modulus))
                  (pfield-poly-divmod-core quotient remainder divisor)))
  :hints (("Goal" :induct (pfield-poly-divmod-core
                            quotient remainder divisor)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(pfield-poly-divmod-core
              runtime-p-coefficient-fix-pfield-correspondence
              runtime-p-zero-pfield-correspondence
              runtime-p-one-pfield-correspondence
              runtime-p-degree-pfield-correspondence
              runtime-p-leading-pfield-correspondence
              runtime-p-step-pfield-core-correspondence
              runtime-p-poly-add-pfield-rewrite
              runtime-p-canonical-pfield-division-correspondence
              pfield-division-canonical-is-existing-canonical
              car-cons cdr-cons)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-monic-divmod-core-equation
                                   (p (gfield::pfield-modulus)))
                        (:instance
                         pfield-poly-divmod-core-functional-instance-equation)
                        (:instance
                         runtime-p-monic-division-step-output-canonical
                         (p (gfield::pfield-modulus)))
                        (:instance
                         runtime-p-monic-division-step-projection-equations
                         (p (gfield::pfield-modulus)))
                        (:instance
                         runtime-p-canonical-polynomial-p-of-poly-add
                         (x quotient)
                         (y (car (runtime-p-monic-division-step
                                  remainder divisor
                                  (gfield::pfield-modulus))))
                         (p (gfield::pfield-modulus)))
                        (:instance pfield-division-monic-implies-consp))
                 :in-theory
                 (union-theories
                  (theory 'minimal-theory)
                  '(runtime-p-one-pfield-correspondence
                    runtime-p-degree-pfield-correspondence
                    runtime-p-leading-pfield-correspondence
                    runtime-p-step-pfield-core-correspondence
                    runtime-p-poly-add-pfield-rewrite
                    runtime-p-canonical-pfield-division-correspondence
                    pfield-division-canonical-is-existing-canonical
                    car-cons cdr-cons)))))))

(defthm runtime-p-monic-divmod-pfield-correspondence
  (implies (equal (pfield-poly-leading-coefficient (pfield-normalize g))
                  (gfield::pfield-one))
           (equal (runtime-p-monic-divmod f g (gfield::pfield-modulus))
                  (pfield-poly-divmod f g)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-monic-divmod
                                      pfield-poly-divmod)
           :use (runtime-p-normalize-pfield-correspondence
                 (:instance runtime-p-core-pfield-correspondence
                            (quotient nil)
                            (remainder (pfield-normalize f))
                            (divisor (pfield-normalize g)))))))

(defthm runtime-p-monic-quotient-pfield-correspondence
  (implies (equal (pfield-poly-leading-coefficient (pfield-normalize g))
                  (gfield::pfield-one))
           (equal (runtime-p-monic-quotient f g (gfield::pfield-modulus))
                  (pfield-poly-quotient f g)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-monic-divmod-pfield-correspondence))
           :in-theory (enable runtime-p-monic-quotient pfield-poly-quotient))))

(defthm runtime-p-monic-remainder-pfield-correspondence
  (implies (equal (pfield-poly-leading-coefficient (pfield-normalize g))
                  (gfield::pfield-one))
           (equal (runtime-p-monic-remainder f g (gfield::pfield-modulus))
                  (pfield-poly-remainder f g)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-monic-divmod-pfield-correspondence))
           :in-theory (enable runtime-p-monic-remainder pfield-poly-remainder))))
