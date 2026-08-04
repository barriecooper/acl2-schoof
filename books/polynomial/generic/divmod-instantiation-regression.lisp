(in-package "GPOLY")
(include-book "f7-division")

; A second client exercises the generated recursive equation seam while the
; recursive implementation remains disabled.
(local (in-theory (disable f7-poly-divmod-core)))

(def-divmod-public-interface-instance
 f7-divmod-instantiation-regression
 f7-canonical-polynomial-p f7-normalize f7-poly-add f7-poly-mul
 f7-poly-degree f7-poly-divmod
 ((gfield::field-element-p gfield::f7-element-p)
  (gfield::field-fix gfield::f7-fix)
  (gfield::field-zero gfield::f7-zero)
  (gfield::field-one gfield::f7-one)
  (gfield::field-add gfield::f7-add)
  (gfield::field-mul gfield::f7-mul)
  (gfield::field-neg gfield::f7-neg)
  (gfield::field-inv gfield::f7-inv)
  (gfield::field-div gfield::f7-div))
 ((fix-coefficients f7-fix-coefficients)
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
  (poly-leading-coefficient f7-poly-leading-coefficient))
 ((poly-division-step-core f7-poly-division-step-core)
  (poly-division-step f7-poly-division-step)
  (poly-division-step-term f7-poly-division-step-term)
  (poly-division-step-next f7-poly-division-step-next)
  (poly-divmod-core f7-poly-divmod-core)
  (poly-divmod f7-poly-divmod))
 f7-poly-divmod-core-functional-instance-equation
 (("Subgoal 29.2" :use gfield::f7-mul-inverse-right)
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
  ("Subgoal 2.3'"
   :use f7-trim-change-implies-last-zero-for-divmod-instantiation)
  ("Subgoal 2.1"
   :use ((:instance f7-canonical-polynomial-p-implies-last-nonzero
                    (p xs))))
  ("Subgoal 8.2.1'" :in-theory (enable mod))))

(defthm f7-divmod-instantiation-regression-minimal-theory-client
  (f7-canonical-polynomial-p (mv-nth 1 (f7-poly-divmod f g)))
  :rule-classes nil
  :hints (("Goal"
           :use f7-divmod-instantiation-regression-remainder-canonical
           :in-theory (theory 'minimal-theory))))
