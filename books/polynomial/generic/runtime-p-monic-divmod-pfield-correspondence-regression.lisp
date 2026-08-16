(in-package "GPOLY")

(include-book "runtime-p-monic-divmod-pfield-correspondence")
(include-book "f7-division")

; F7 is a concrete client of the fixed-PFIELD theorem.  The operation mapping
; identifies the transparent PFIELD adapter with the already-certified F7
; long-division instance generated from the same generic template.
(defthm runtime-p-monic-divmod-f7-correspondence
  (implies (equal (f7-poly-leading-coefficient (f7-normalize g))
                  (gfield::f7-one))
           (equal (runtime-p-monic-divmod f g 7)
                  (f7-poly-divmod f g)))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                runtime-p-monic-divmod-pfield-correspondence
                (gfield::pfield-modulus (lambda () 7))
                (gfield::pfield-element-p gfield::f7-element-p)
                (gfield::pfield-fix gfield::f7-fix)
                (gfield::pfield-zero gfield::f7-zero)
                (gfield::pfield-one gfield::f7-one)
                (gfield::pfield-add gfield::f7-add)
                (gfield::pfield-mul gfield::f7-mul)
                (gfield::pfield-neg gfield::f7-neg)
                (gfield::pfield-inv gfield::f7-inv)
                (gfield::pfield-div gfield::f7-div)
                (pfield-fix-coefficients f7-fix-coefficients)
                (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                (pfield-normalize f7-normalize)
                (pfield-poly-degree f7-poly-degree)
                (pfield-poly-leading-coefficient f7-poly-leading-coefficient)
                (pfield-canonical-polynomial-p f7-canonical-polynomial-p)
                (pfield-zero-prefix f7-zero-prefix)
                (pfield-poly-shift f7-poly-shift)
                (pfield-monomial f7-monomial)
                (pfield-poly-add f7-poly-add)
                (pfield-poly-sub f7-poly-sub)
                (pfield-poly-mul f7-poly-mul)
                (pfield-poly-division-step-core f7-poly-division-step-core)
                (pfield-poly-division-step f7-poly-division-step)
                (pfield-poly-division-step-term f7-poly-division-step-term)
                (pfield-poly-division-step-next f7-poly-division-step-next)
                (pfield-poly-divmod-core f7-poly-divmod-core)
                (pfield-poly-divmod f7-poly-divmod))
           :in-theory (enable dm::primep))))

(defthm runtime-p-monic-divmod-pfield-minimal-theory-client
  (implies (equal (pfield-poly-leading-coefficient (pfield-normalize g))
                  (gfield::pfield-one))
           (equal (runtime-p-monic-divmod f g (gfield::pfield-modulus))
                  (pfield-poly-divmod f g)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance runtime-p-monic-divmod-pfield-correspondence)))))

; Multi-step division, including exact quotient and remainder equality.
(assert-event
 (and (equal (runtime-p-monic-divmod '(5 5 3) '(1 1) 7)
             (f7-poly-divmod '(5 5 3) '(1 1)))
      (equal (runtime-p-monic-quotient '(5 5 3) '(1 1) 7)
             (f7-poly-quotient '(5 5 3) '(1 1)))
      (equal (runtime-p-monic-remainder '(5 5 3) '(1 1) 7)
             (f7-poly-remainder '(5 5 3) '(1 1)))))
; Exact divisibility.
(assert-event
 (equal (runtime-p-monic-divmod '(2 5 3) '(1 1) 7)
        (f7-poly-divmod '(2 5 3) '(1 1))))
; Dividend below divisor degree and zero dividend.
(assert-event
 (equal (runtime-p-monic-divmod '(1) '(1 0 1) 7)
        (f7-poly-divmod '(1) '(1 0 1))))
(assert-event
 (equal (runtime-p-monic-divmod nil '(1 1) 7)
        (f7-poly-divmod nil '(1 1))))
; Dotted tails and trailing zeroes are normalized by both public operations.
(assert-event
 (equal (runtime-p-monic-divmod '(5 5 3 0 . bad) '(1 1 0 . bad) 7)
        (f7-poly-divmod '(5 5 3 0 . bad) '(1 1 0 . bad))))
