(in-package "GPOLY")

(include-book "f11-division-polynomial-functional-instance-regression")

; Concrete fixing plumbing required because the public F11 table wrapper fixes
; coefficients eagerly, while the generic wrapper relies on the step's fixing
; invariance.
(defthm f11-division-polynomial-base-of-coefficient-fixes
  (equal (f11-division-polynomial-base
          n (gfield::f11-fix a) (gfield::f11-fix b))
         (f11-division-polynomial-base n a b))
  :hints
  (("Goal"
    :use f11-division-polynomial-base-of-coefficient-fixes-from-finite-field-instance
    :in-theory (theory 'minimal-theory))))

(defthm f11-division-polynomial-c-of-coefficient-fixes
  (equal (f11-division-polynomial-c (gfield::f11-fix a)
                                    (gfield::f11-fix b))
         (f11-division-polynomial-c a b))
  :hints (("Goal" :in-theory (enable f11-division-polynomial-c))))

(defthm f11-division-polynomial-recurrence-step-of-coefficient-fixes
  (equal (f11-division-polynomial-recurrence-step
          n table (gfield::f11-fix a) (gfield::f11-fix b))
         (f11-division-polynomial-recurrence-step n table a b))
  :hints
  (("Goal"
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(f11-division-polynomial-recurrence-step
       f11-division-polynomial-base-of-coefficient-fixes
       f11-division-polynomial-c-of-coefficient-fixes)))))

(defthm f11-division-polynomial-table-nat-of-coefficient-fixes
  (equal (f11-division-polynomial-table-nat
          n (gfield::f11-fix a) (gfield::f11-fix b))
         (f11-division-polynomial-table-nat n a b))
  :hints
  (("Goal"
    :induct (f11-division-polynomial-table-nat n a b)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(f11-division-polynomial-table-nat
       f11-division-polynomial-base-of-coefficient-fixes
       f11-division-polynomial-recurrence-step-of-coefficient-fixes)))))

(defthm f11-division-polynomial-table-of-coefficient-fixes
  (equal (f11-division-polynomial-table
          n (gfield::f11-fix a) (gfield::f11-fix b))
         (f11-division-polynomial-table n a b))
  :hints (("Goal" :in-theory (enable f11-division-polynomial-table))))
