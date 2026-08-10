(in-package "GPOLY")

(include-book "f11-division-polynomial-functional-instance")

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

; Named logical equations for the recursive target operations in the complete
; generic-to-F11 substitution.  They are deliberately non-rewriting: their
; purpose is auditable functional-instance constraint discharge.
(defthm f11-natural-coefficient-definition-correspondence
  (equal (f11-natural-coefficient n)
         (if (zp (nfix n))
             (gfield::f11-zero)
           (gfield::f11-add
            (gfield::f11-one)
            (f11-natural-coefficient (1- (nfix n))))))
  :rule-classes nil
  :hints (("Goal" :expand ((f11-natural-coefficient n)))))

(defthm f11-division-polynomial-table-extend-definition-correspondence
  (equal (f11-division-polynomial-table-extend table value)
         (if (endp table)
             (list value)
           (cons (car table)
                 (f11-division-polynomial-table-extend (cdr table) value))))
  :rule-classes nil
  :hints (("Goal" :expand ((f11-division-polynomial-table-extend table value)))))

(defthm f11-division-polynomial-table-nat-definition-correspondence
  (equal (f11-division-polynomial-table-nat n a b)
         (if (zp n)
             (list (f11-division-polynomial-base 0 a b))
           (let ((old (f11-division-polynomial-table-nat (1- n) a b)))
             (f11-division-polynomial-table-extend
              old (f11-division-polynomial-recurrence-step n old a b)))))
  :rule-classes nil
  :hints (("Goal"
           :expand ((f11-division-polynomial-table-nat n a b))
           :in-theory (theory 'minimal-theory))))

(defthm f11-division-polynomial-table-definition-correspondence
  (equal (f11-division-polynomial-table n a b)
         (f11-division-polynomial-table-nat
          (nfix n) (gfield::f11-fix a) (gfield::f11-fix b)))
  :rule-classes nil)

(defthm f11-division-polynomial-sequence-entries-p-definition-correspondence
  (equal (f11-division-polynomial-sequence-entries-p k table a b)
         (and (equal (nth k table)
                     (f11-division-polynomial-recurrence-step k table a b))
              (if (zp k)
                  t
                (f11-division-polynomial-sequence-entries-p
                 (1- k) table a b))))
  :rule-classes nil
  :hints (("Goal"
           :expand ((f11-division-polynomial-sequence-entries-p
                     k table a b))
           :in-theory (theory 'minimal-theory))))

(defthm f11-division-polynomial-sequence-p-definition-correspondence
  (equal (f11-division-polynomial-sequence-p n table a b)
         (and (true-listp table)
              (equal (len table) (+ 1 (nfix n)))
              (f11-division-polynomial-sequence-entries-p
               (nfix n) table a b)))
  :rule-classes nil)

(defthm f11-division-polynomial-definition-correspondence
  (equal (f11-division-polynomial n a b)
         (nth (nfix n) (f11-division-polynomial-table n a b)))
  :rule-classes nil)


(defthm true-listp-of-f11-division-polynomial-table-extend
  (true-listp (f11-division-polynomial-table-extend table value)))

(defthm len-of-f11-division-polynomial-table-extend
  (equal (len (f11-division-polynomial-table-extend table value))
         (+ 1 (len table))))

(defthm nth-below-of-f11-division-polynomial-table-extend
  (implies (and (natp k) (< k (len table)))
           (equal (nth k (f11-division-polynomial-table-extend table value))
                  (nth k table)))
  :hints (("Goal" :induct (nth k table)
           :in-theory (enable f11-division-polynomial-table-extend))))

(defthm nth-at-end-of-f11-division-polynomial-table-extend
  (implies (true-listp table)
           (equal (nth (len table)
                       (f11-division-polynomial-table-extend table value))
                  value)))

(defthm f11-division-polynomial-table-nat-base
  (equal (f11-division-polynomial-table-nat 0 a b)
         (list (f11-division-polynomial-base 0 a b)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(f11-division-polynomial-table-nat zp)))))

(defthm f11-division-polynomial-table-base
  (equal (f11-division-polynomial-table 0 a b)
         (list (f11-division-polynomial-base 0 a b)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(f11-division-polynomial-table
                             f11-division-polynomial-table-nat-base
                             f11-division-polynomial-base-of-coefficient-fixes nfix)))))

(defthm len-of-singleton-for-f11-division-polynomial-table
  (equal (len (list x)) 1))

(defthm len-of-f11-division-polynomial-table-nat
  (implies (natp n)
           (equal (len (f11-division-polynomial-table-nat n a b))
                  (+ 1 n)))
  :hints (("Goal" :induct (f11-division-polynomial-table-nat n a b)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-division-polynomial-table-nat
              len-of-f11-division-polynomial-table-extend
              len-of-singleton-for-f11-division-polynomial-table natp zp)))))

(defthm len-of-f11-division-polynomial-table
  (equal (len (f11-division-polynomial-table n a b))
         (+ 1 (nfix n)))
  :hints (("Goal" :use ((:instance len-of-f11-division-polynomial-table-nat
                                    (n (nfix n))
                                    (a (gfield::f11-fix a))
                                    (b (gfield::f11-fix b))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(f11-division-polynomial-table nfix natp)))))

(defthm true-listp-of-f11-division-polynomial-table-nat
  (true-listp (f11-division-polynomial-table-nat n a b))
  :hints (("Goal" :induct (f11-division-polynomial-table-nat n a b)
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(f11-division-polynomial-table-nat
                             true-listp-of-f11-division-polynomial-table-extend
                             zp)))))

(defthm true-listp-of-f11-division-polynomial-table
  (true-listp (f11-division-polynomial-table n a b))
  :hints (("Goal" :use ((:instance true-listp-of-f11-division-polynomial-table-nat
                                    (n (nfix n))
                                    (a (gfield::f11-fix a))
                                    (b (gfield::f11-fix b))))
           :in-theory (enable f11-division-polynomial-table))))
