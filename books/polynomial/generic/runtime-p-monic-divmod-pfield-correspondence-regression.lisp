(in-package "GPOLY")

(include-book "runtime-p-monic-divmod-pfield-correspondence")
(include-book "f7-division")

(defun f7-division-canonical-polynomial-p (xs)
  (and (f7-coefficient-list-p xs)
       (or (not (consp xs))
           (not (equal (car (last xs)) (gfield::f7-zero))))))

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
                (pfield-coefficient-list-p f7-coefficient-list-p)
                (pfield-division-canonical-polynomial-p
                 f7-division-canonical-polynomial-p)
                (pfield-poly-degree f7-poly-degree)
                (pfield-poly-leading-coefficient f7-poly-leading-coefficient)
                (pfield-canonical-polynomial-p f7-canonical-polynomial-p)
                (pfield-zero-prefix f7-zero-prefix)
                (pfield-poly-shift f7-poly-shift)
                (pfield-monomial f7-monomial)
                (pfield-poly-add f7-poly-add)
                (pfield-raw-add f7-raw-add)
                (pfield-raw-neg f7-raw-neg)
                (pfield-poly-neg f7-poly-neg)
                (pfield-poly-sub f7-poly-sub)
                (pfield-raw-scale f7-raw-scale)
                (pfield-raw-mul f7-raw-mul)
                (pfield-poly-mul f7-poly-mul)
                (pfield-poly-division-step-core f7-poly-division-step-core)
                (pfield-poly-division-step f7-poly-division-step)
                (pfield-poly-division-step-term f7-poly-division-step-term)
                (pfield-poly-division-step-next f7-poly-division-step-next)
                (pfield-poly-divmod-core f7-poly-divmod-core)
                (pfield-poly-divmod f7-poly-divmod))
           :in-theory (enable dm::primep))
          (and stable-under-simplificationp
               '(:use ((:instance
                         f7-poly-divmod-core-functional-instance-equation)
                        (:instance f7-leading-coefficient-ordered-quotient-package))
                 :in-theory (enable f7-poly-divmod-core
                                    f7-canonical-polynomial-p
                                    f7-normalize)))))

(defthm runtime-p-monic-divmod-pfield-minimal-theory-client
  (implies (equal (pfield-poly-leading-coefficient (pfield-normalize g))
                  (gfield::pfield-one))
           (equal (runtime-p-monic-divmod f g (gfield::pfield-modulus))
                  (pfield-poly-divmod f g)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance runtime-p-monic-divmod-pfield-correspondence)))))

(defun runtime-p-f7-divmod-equal (f g)
  (mv-let (runtime-q runtime-r) (runtime-p-monic-divmod f g 7)
    (mv-let (f7-q f7-r) (f7-poly-divmod f g)
      (equal (list runtime-q runtime-r) (list f7-q f7-r)))))

; Multi-step division, including exact quotient and remainder equality.
(assert-event
 (and (runtime-p-f7-divmod-equal '(5 5 3) '(1 1))
      (equal (runtime-p-monic-quotient '(5 5 3) '(1 1) 7)
             (f7-poly-quotient '(5 5 3) '(1 1)))
      (equal (runtime-p-monic-remainder '(5 5 3) '(1 1) 7)
             (f7-poly-remainder '(5 5 3) '(1 1)))))
; Exact divisibility.
(assert-event
 (runtime-p-f7-divmod-equal '(2 5 3) '(1 1)))
; Dividend below divisor degree and zero dividend.
(assert-event
 (runtime-p-f7-divmod-equal '(1) '(1 0 1)))
(assert-event
 (runtime-p-f7-divmod-equal nil '(1 1)))
; Dotted tails and trailing zeroes are normalized by both public operations.
(assert-event
 (runtime-p-f7-divmod-equal
  '(5 5 3 0 . bad) '(1 1 0 . bad)))
