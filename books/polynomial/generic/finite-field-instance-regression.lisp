(in-package "GPOLY")

(include-book "finite-field-instance")
(include-book "pfield-instance")
(include-book "../../field/pfield-finite-field-context-regression")

(defthm pfield-poly-normalize-idempotent-from-finite-field-instance
  (equal (pfield-normalize (pfield-normalize xs)) (pfield-normalize xs))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable pfield-normalize
                                      pfield-trim-trailing-zeros
                                      pfield-fix-coefficients))))

(defthm pfield-polynomial-core-correspondence-regression
  (and (pfield-canonical-polynomial-p (pfield-normalize x))
       (pfield-canonical-polynomial-p (pfield-poly-mul x y)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance pfield-canonical-polynomial-p-of-normalize
                            (xs x))
                 (:instance pfield-canonical-polynomial-p-of-poly-mul))
           :in-theory (theory 'minimal-theory))))

; F7 reuses its existing executable polynomial family.  These checks cover the
; complete core operation surface without defining any second F7 family.
(defthm f7-finite-field-polynomial-core-execution-regressions
  (and (equal (f7-normalize '(1 2 0 0)) '(1 2))
       (equal (f7-normalize (cons 'malformed '(2 0))) '(0 2))
       (equal (f7-normalize '(1 2 . malformed)) '(1 2))
       (equal (gfield::f7-fix (car (f7-normalize '(8 2)))) 1)
       (equal (if (< 5 (len (f7-normalize '(1 2))))
                  (gfield::f7-fix (nth 5 (f7-normalize '(1 2))))
                (gfield::f7-zero))
              0)
       (equal (f7-poly-add '(1 2) '(3 4)) '(4 6))
       (equal (f7-poly-neg '(1 2)) '(6 5))
       (equal (f7-poly-sub '(1 2) '(3 4)) '(5 5))
       (equal (f7-poly-mul '(1 2) '(3 4)) '(3 3 1))
       (equal (f7-poly-degree nil) -1)
       (equal (f7-poly-degree (f7-normalize '(1 2 0))) 1)
       (equal (f7-poly-leading-coefficient nil) 0)
       (equal (f7-poly-leading-coefficient (f7-normalize '(1 2 0))) 2))
  :rule-classes nil)

(defthm f7-polynomial-core-theorem-correspondence-regression
  (and (f7-canonical-polynomial-p (f7-normalize x))
       (f7-canonical-polynomial-p (f7-poly-add x y))
       (f7-canonical-polynomial-p (f7-poly-neg x))
       (f7-canonical-polynomial-p (f7-poly-sub x y))
       (f7-canonical-polynomial-p (f7-poly-mul x y)))
  :rule-classes nil
  :hints (("Goal" :use (f7-canonical-polynomial-p-of-normalize
                         f7-canonical-polynomial-p-of-poly-add
                         f7-canonical-polynomial-p-of-poly-neg
                         f7-canonical-polynomial-p-of-poly-sub
                         f7-canonical-polynomial-p-of-poly-mul))))
