(in-package "GPOLY")
(include-book "pfield-instance")
(include-book "division")


; Ordinary generated recursive division over the named concrete field.
(verify-guards gfield::f7-element-p)
(verify-guards f7-coefficient-list-p)
(verify-guards f7-canonical-polynomial-p)
(def-divmod-instance
  f7-poly-divmod-core f7-poly-divmod f7-canonical-polynomial-p
  f7-poly-degree f7-poly-division-step-core f7-poly-add f7-normalize
  f7-poly-division-step-core-length-decreases)
(def-divmod-projections-instance
  f7-poly-quotient f7-poly-remainder f7-poly-divmod)

(defthm f7-add-fixed-congruence-for-divmod-instantiation
  (implies (and (equal (gfield::f7-fix x1) (gfield::f7-fix x2))
                (equal (gfield::f7-fix y1) (gfield::f7-fix y2)))
           (equal (gfield::f7-add x1 y1) (gfield::f7-add x2 y2)))
  :hints (("Goal" :in-theory (e/d (gfield::f7-add)
                                    (gfield::f7-fix)))))
(defthm f7-mul-fixed-congruence-for-divmod-instantiation
  (implies (and (equal (gfield::f7-fix x1) (gfield::f7-fix x2))
                (equal (gfield::f7-fix y1) (gfield::f7-fix y2)))
           (equal (gfield::f7-mul x1 y1) (gfield::f7-mul x2 y2)))
  :hints (("Goal" :in-theory (e/d (gfield::f7-mul)
                                    (gfield::f7-fix)))))
(defthm f7-trim-change-implies-last-zero-for-divmod-instantiation
  (implies (and (f7-coefficient-list-p xs)
                (not (equal (f7-trim-trailing-zeros xs) xs)))
           (equal (car (last xs)) (gfield::f7-zero)))
  :hints (("Goal"
           :use ((:instance
                  f7-trim-trailing-zeros-when-coefficient-list-p-and-last-nonzero
                  (p xs)))
           :in-theory (enable f7-coefficient-list-p))))

(defthm f7-poly-divmod-public-interface-from-generic
  (and (f7-canonical-polynomial-p (mv-nth 0 (f7-poly-divmod f g)))
       (f7-canonical-polynomial-p (mv-nth 1 (f7-poly-divmod f g)))
       (equal (f7-poly-add
               (f7-poly-mul (mv-nth 0 (f7-poly-divmod f g))
                            (f7-normalize g))
               (mv-nth 1 (f7-poly-divmod f g)))
              (f7-normalize f))
       (implies (consp (f7-normalize g))
                (or (equal (mv-nth 1 (f7-poly-divmod f g)) nil)
                    (< (f7-poly-degree (mv-nth 1 (f7-poly-divmod f g)))
                       (f7-poly-degree (f7-normalize g))))))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        poly-divmod-public-interface
                        (gfield::field-element-p gfield::f7-element-p)
                        (gfield::field-fix gfield::f7-fix)
                        (gfield::field-zero gfield::f7-zero)
                        (gfield::field-one gfield::f7-one)
                        (gfield::field-add gfield::f7-add)
                        (gfield::field-mul gfield::f7-mul)
                        (gfield::field-neg gfield::f7-neg)
                        (gfield::field-inv gfield::f7-inv)
                        (gfield::field-div gfield::f7-div)
                        (fix-coefficients f7-fix-coefficients)
                        (trim-trailing-zeros f7-trim-trailing-zeros)
                        (normalize f7-normalize)
                        (coefficient-list-p f7-coefficient-list-p)
                        (polynomial-p f7-polynomial-p)
                        (canonical-polynomial-p f7-canonical-polynomial-p)
                        (raw-add f7-raw-add) (poly-add f7-poly-add)
                        (raw-neg f7-raw-neg) (poly-neg f7-poly-neg)
                        (poly-sub f7-poly-sub)
                        (raw-scale f7-raw-scale) (poly-scale f7-poly-scale)
                        (raw-mul f7-raw-mul) (poly-mul f7-poly-mul)
                        (zero-prefix f7-zero-prefix)
                        (poly-shift f7-poly-shift) (monomial f7-monomial)
                        (poly-degree f7-poly-degree)
                        (poly-leading-coefficient f7-poly-leading-coefficient)
                        (poly-division-step-core f7-poly-division-step-core)
                        (poly-division-step f7-poly-division-step)
                        (poly-division-step-term f7-poly-division-step-term)
                        (poly-division-step-next f7-poly-division-step-next)
                        (poly-divmod-core f7-poly-divmod-core)
                        (poly-divmod f7-poly-divmod)))
          ("Subgoal 29.2" :use gfield::f7-mul-inverse-right)
          ("Subgoal 26.9"
           :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                            (x1 gfield::x1) (x2 gfield::x2)
                            (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 26.4"
           :use ((:instance f7-mul-fixed-congruence-for-divmod-instantiation
                            (x1 gfield::x1) (x2 gfield::x2)
                            (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 25.11"
           :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation
                            (x1 gfield::x1) (x2 gfield::x2)
                            (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 25.6"
           :use ((:instance f7-add-fixed-congruence-for-divmod-instantiation
                            (x1 gfield::x1) (x2 gfield::x2)
                            (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 22.2.1"
           :use gfield::f7-element-p-of-f7-fix
           :in-theory (enable gfield::f7-fix gfield::f7-element-p))
          ("Subgoal 22.2.1'''" :in-theory (enable mod))
          ("Subgoal 22.2.1'" :in-theory (enable mod))
          ("Subgoal 21.2.1'" :in-theory (enable mod))
          ("Subgoal 9.9.1'" :use ((:instance f7-poly-divmod-core)))
          ("Subgoal 6.9.1'" :use ((:instance f7-poly-divmod-core)))
          ("Subgoal 2.3'"
           :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
          ("Subgoal 2.1"
           :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero
                            (p xs))))
          ("Subgoal 8.2.1'" :in-theory (enable mod))))

(defthm f7-poly-divmod-quotient-canonical
  (f7-canonical-polynomial-p (mv-nth 0 (f7-poly-divmod f g)))
  :hints (("Goal" :use f7-poly-divmod-public-interface-from-generic)))
(defthm f7-poly-divmod-remainder-canonical
  (f7-canonical-polynomial-p (mv-nth 1 (f7-poly-divmod f g)))
  :hints (("Goal" :use f7-poly-divmod-public-interface-from-generic)))
(defthm f7-poly-divmod-reconstruction
  (equal (f7-poly-add
          (f7-poly-mul (mv-nth 0 (f7-poly-divmod f g)) (f7-normalize g))
          (mv-nth 1 (f7-poly-divmod f g)))
         (f7-normalize f))
  :rule-classes nil
  :hints (("Goal" :use f7-poly-divmod-public-interface-from-generic)))
(defthm f7-poly-divmod-final-remainder-degree-bound
  (implies (consp (f7-normalize g))
           (or (equal (mv-nth 1 (f7-poly-divmod f g)) nil)
               (< (f7-poly-degree (mv-nth 1 (f7-poly-divmod f g)))
                  (f7-poly-degree (f7-normalize g)))))
  :rule-classes nil
  :hints (("Goal" :use f7-poly-divmod-public-interface-from-generic)))
(defthm f7-poly-quotient-is-divmod-quotient
  (equal (f7-poly-quotient f g) (mv-nth 0 (f7-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable f7-poly-quotient))))
(defthm f7-poly-remainder-is-divmod-remainder
  (equal (f7-poly-remainder f g) (mv-nth 1 (f7-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable f7-poly-remainder))))
(defthm f7-poly-remainder-canonical
  (f7-canonical-polynomial-p (f7-poly-remainder f g))
  :hints (("Goal" :use f7-poly-divmod-remainder-canonical)))
(defthm f7-poly-divmod-zero-normalized-divisor
  (implies (equal (f7-normalize g) nil)
           (equal (f7-poly-divmod f g) (mv nil (f7-normalize f))))
  :hints (("Goal" :in-theory (enable f7-poly-divmod f7-poly-divmod-core))))
(defthm f7-poly-divmod-nonzero-constant-regression
  (equal (f7-poly-divmod '(1 2 3) '(2)) (mv '(4 1 5) nil)))
(defthm f7-poly-divmod-zero-normalized-regression
  (equal (f7-poly-divmod '(1 9 0) '(7 14 . bad)) (mv nil '(1 2))))

; Focused exact ordinary-execution regressions, including total malformed input.
(assert-event (mv-let (q r) (f7-poly-divmod '(6 1 1) '(1 1))
                (and (equal q '(0 1)) (equal r '(6)))))
(assert-event (mv-let (q r) (f7-poly-divmod '(1 0 0 1) '(1 1))
                (and (equal q '(1 6 1)) (equal r nil))))
(assert-event (mv-let (q r) (f7-poly-divmod '(1) '(0 1))
                (and (equal q nil) (equal r '(1)))))
(assert-event (mv-let (q r) (f7-poly-divmod '(8 9 0 0) '(1 1 0))
                (and (equal q '(2)) (equal r '(6)))))
(assert-event (mv-let (q r) (f7-poly-divmod 'malformed '(1 1))
                (and (equal q nil) (equal r nil))))
(assert-event (mv-let (q r) (f7-poly-divmod '(1 2 . bad) '(1 . bad))
                (and (equal q '(1 2)) (equal r nil))))
(assert-event
 (mv-let (q r) (f7-poly-divmod '(1 0 0 1) '(1 1))
   (and (equal q (f7-poly-quotient '(1 0 0 1) '(1 1)))
        (equal r (f7-poly-remainder '(1 0 0 1) '(1 1)))
        (f7-canonical-polynomial-p r)
        (equal (f7-normalize r) r)
        (equal (f7-poly-add (f7-poly-mul q '(1 1)) r) '(1 0 0 1)))))

(verify-guards f7-poly-divmod-core)
(verify-guards f7-poly-divmod)
(verify-guards f7-poly-quotient)
(verify-guards f7-poly-remainder)
