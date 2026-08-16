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

(local (defthm pfield-step-core-length-decreases
  (implies (and (pfield-canonical-polynomial-p remainder)
                (pfield-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (equal (pfield-poly-leading-coefficient divisor)
                       (gfield::pfield-one))
                (<= (pfield-poly-degree divisor)
                    (pfield-poly-degree remainder)))
           (< (len (cdr (pfield-poly-division-step-core remainder divisor)))
              (len remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use (runtime-p-normalize-pfield-correspondence
                 (:instance runtime-p-monic-division-step-active-length-decreases
                            (p (gfield::pfield-modulus))))
           :in-theory (enable runtime-p-monic-division-step-next
                              runtime-p-monic-division-step
                              runtime-p-normalize-when-canonical
                              runtime-p-step-core-pfield-correspondence
                              runtime-p-degree-pfield-correspondence
                              runtime-p-leading-pfield-correspondence)))))

; The generic PFIELD divmod supports this monic correspondence boundary.  Its
; recursion is generated by DEF-DIVMOD-INSTANCE, the repository's established
; division implementation template.
(def-divmod-instance
  pfield-poly-divmod-core pfield-poly-divmod pfield-canonical-polynomial-p
  pfield-poly-degree pfield-poly-division-step-core pfield-poly-add
  pfield-normalize pfield-step-core-length-decreases)
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
  :hints (("Goal" :induct (runtime-p-monic-divmod-core
                            quotient remainder divisor
                            (gfield::pfield-modulus))
           :in-theory (enable runtime-p-monic-divmod-core
                              pfield-poly-divmod-core
                              runtime-p-canonical-polynomial-p
                              pfield-canonical-polynomial-p
                              runtime-p-coefficient-list-p
                              pfield-coefficient-list-p
                              runtime-p-coefficient-fix-pfield-correspondence
                              runtime-p-zero-pfield-correspondence
                              runtime-p-one-pfield-correspondence
                              runtime-p-degree-pfield-correspondence
                              runtime-p-leading-pfield-correspondence
                              runtime-p-step-core-pfield-correspondence
                              runtime-p-poly-add-pfield-correspondence)))))

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
