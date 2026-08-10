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
       f11-division-polynomial-recurrence-step-of-coefficient-fixes
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

(local
 (defthm len-of-singleton-for-f11-division-polynomial-table
   (equal (len (list x)) 1)))

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

(defthm f11-division-polynomial-table-nat-newest-at-prefix-length
  (implies (posp n)
           (equal
            (nth (len (f11-division-polynomial-table-nat (1- n) a b))
                 (f11-division-polynomial-table-nat n a b))
            (f11-division-polynomial-recurrence-step
             n (f11-division-polynomial-table-nat (1- n) a b) a b)))
  :hints (("Goal"
           :expand ((f11-division-polynomial-table-nat n a b))
           :use ((:instance nth-at-end-of-f11-division-polynomial-table-extend
                            (table (f11-division-polynomial-table-nat (1- n) a b))
                            (value (f11-division-polynomial-recurrence-step
                                    n (f11-division-polynomial-table-nat (1- n) a b)
                                    a b))))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(posp zp natp
                         true-listp-of-f11-division-polynomial-table-nat)))))

(local
 (defthm one-plus-one-less-when-posp-for-f11-table
   (implies (posp n) (equal (+ 1 (1- n)) n))))

(local
 (defthm natp-of-one-less-when-posp-for-f11-table
   (implies (posp n) (natp (1- n)))))

(defthm f11-division-polynomial-table-nat-newest-entry
  (implies (posp n)
           (equal
            (nth n (f11-division-polynomial-table-nat n a b))
            (f11-division-polynomial-recurrence-step
             n (f11-division-polynomial-table-nat (1- n) a b) a b)))
  :hints (("Goal"
           :use (f11-division-polynomial-table-nat-newest-at-prefix-length
                 (:instance len-of-f11-division-polynomial-table-nat (n (1- n)))
                 one-plus-one-less-when-posp-for-f11-table
                 natp-of-one-less-when-posp-for-f11-table)
           :in-theory (theory 'minimal-theory))))

(local
 (defthm nfix-of-one-less-when-posp-for-f11-table
   (implies (posp n)
            (equal (nfix (1- n)) (1- n)))
   :hints (("Goal" :in-theory (enable nfix posp)))))

(defthm f11-division-polynomial-table-newest-entry
  (implies (posp (nfix n))
           (equal
            (nth (nfix n) (f11-division-polynomial-table n a b))
            (f11-division-polynomial-recurrence-step
             (nfix n)
             (f11-division-polynomial-table (1- (nfix n)) a b)
             a b)))
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-table-nat-newest-entry
                            (n (nfix n))
                            (a (gfield::f11-fix a))
                            (b (gfield::f11-fix b))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-division-polynomial-table
              f11-division-polynomial-table-nat-of-coefficient-fixes
              f11-division-polynomial-recurrence-step-of-coefficient-fixes
              nfix-of-one-less-when-posp-for-f11-table)))))
(local
 (defun f11-division-polynomial-table-lookup-induct (k n)
   (if (or (zp n) (equal k n))
       nil
     (f11-division-polynomial-table-lookup-induct k (1- n)))))

(defthm f11-division-polynomial-table-nat-lookup-stable
  (implies (and (natp k) (natp n) (<= k n))
           (equal (nth k (f11-division-polynomial-table-nat n a b))
                  (nth k (f11-division-polynomial-table-nat k a b))))
  :hints (("Goal" :induct (f11-division-polynomial-table-lookup-induct k n)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(f11-division-polynomial-table-nat
                         f11-division-polynomial-table-lookup-induct
                         nth-below-of-f11-division-polynomial-table-extend
                         len-of-f11-division-polynomial-table-nat
                         one-plus-one-less-when-posp-for-f11-table
                         natp-of-one-less-when-posp-for-f11-table
                         natp posp zp nfix nth)))))

(defthm integerp-when-natp-for-f11-table
  (implies (natp x) (integerp x)))

(defthm nfix-when-natp-for-f11-table
  (implies (natp x) (equal (nfix x) x)))

(defthm f11-division-polynomial-table-lookup-stable
  (implies (and (natp k) (<= k (nfix n)))
           (equal (nth k (f11-division-polynomial-table n a b))
                  (nth k (f11-division-polynomial-table k a b))))
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-table-nat-lookup-stable
                            (n (nfix n))))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(f11-division-polynomial-table nfix
                         natp
                         (:executable-counterpart natp)
                         integerp-when-natp-for-f11-table
                         nfix-when-natp-for-f11-table
                         f11-division-polynomial-table-nat-of-coefficient-fixes)))))

(defthm f11-division-polynomial-table-index-in-range
  (implies (and (natp k) (<= k (nfix n)))
           (< k (len (f11-division-polynomial-table n a b)))))


(defthm f11-division-polynomial-newest-step
  (implies (posp (nfix n))
           (equal (f11-division-polynomial n a b)
                  (f11-division-polynomial-recurrence-step
                   (nfix n)
                   (f11-division-polynomial-table (1- (nfix n)) a b)
                   a b)))
  :hints (("Goal"
           :use f11-division-polynomial-table-newest-entry
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(f11-division-polynomial)))))

(defthm f11-division-polynomial-table-lookup-is-evaluator
  (implies (and (natp k) (<= k (nfix n)))
           (equal (nth k (f11-division-polynomial-table n a b))
                  (f11-division-polynomial k a b)))
  :hints (("Goal"
           :use f11-division-polynomial-table-lookup-stable
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-division-polynomial nfix-when-natp-for-f11-table)))))

(defthm f11-division-polynomial-index-zero
  (equal (f11-division-polynomial 0 a b)
         (f11-division-polynomial-base 0 a b))
  :hints (("Goal" :in-theory
           (enable f11-division-polynomial f11-division-polynomial-table
                   f11-division-polynomial-table-nat))))

(defthm f11-division-polynomial-evaluator-base-equations
  (and (equal (f11-division-polynomial 0 a b)
              (f11-division-polynomial-base 0 a b))
       (equal (f11-division-polynomial 1 a b)
              (f11-division-polynomial-base 1 a b))
       (equal (f11-division-polynomial 2 a b)
              (f11-division-polynomial-base 2 a b))
       (equal (f11-division-polynomial 3 a b)
              (f11-division-polynomial-base 3 a b))
       (equal (f11-division-polynomial 4 a b)
              (f11-division-polynomial-base 4 a b)))
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-newest-step (n 1))
                 (:instance f11-division-polynomial-newest-step (n 2))
                 (:instance f11-division-polynomial-newest-step (n 3))
                 (:instance f11-division-polynomial-newest-step (n 4))
                 f11-division-polynomial-index-zero)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-division-polynomial-recurrence-step
              posp nfix nth car-cons)))))
(defthm f11-division-polynomial-recurrence-step-base
  (implies (< (nfix n) 5)
           (equal (f11-division-polynomial-recurrence-step n table a b)
                  (f11-division-polynomial-base n a b)))
  :hints (("Goal"
           :use f11-division-polynomial-base-of-nfix-from-finite-field-instance
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(f11-division-polynomial-recurrence-step)))))

(defthm f11-division-polynomial-recurrence-step-odd-even-half
  (implies (and (natp m) (<= 2 m) (evenp m))
           (equal
            (f11-division-polynomial-recurrence-step (+ 1 (* 2 m)) table a b)
            (f11-poly-sub
             (f11-poly-mul
              (f11-poly-square (f11-division-polynomial-c a b))
              (f11-poly-mul (nth (+ m 2) table)
                                     (f11-poly-cube (nth m table))))
             (f11-poly-mul (nth (- m 1) table)
                                    (f11-poly-cube
                                     (nth (+ m 1) table))))))
  :hints (("Goal" :use division-polynomial-odd-index-arithmetic
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(f11-division-polynomial-recurrence-step oddp evenp)))))

(defthm f11-division-polynomial-recurrence-step-odd-odd-half
  (implies (and (natp m) (<= 2 m) (oddp m))
           (equal
            (f11-division-polynomial-recurrence-step (+ 1 (* 2 m)) table a b)
            (f11-poly-sub
             (f11-poly-mul (nth (+ m 2) table)
                                    (f11-poly-cube (nth m table)))
             (f11-poly-mul
              (f11-poly-square (f11-division-polynomial-c a b))
              (f11-poly-mul (nth (- m 1) table)
                                     (f11-poly-cube
                                      (nth (+ m 1) table)))))))
  :hints (("Goal" :use division-polynomial-odd-index-arithmetic
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(f11-division-polynomial-recurrence-step oddp evenp)))))

(defthm f11-division-polynomial-recurrence-step-even
  (implies (and (natp m) (<= 3 m))
           (equal
            (f11-division-polynomial-recurrence-step (* 2 m) table a b)
            (f11-poly-mul
             (nth m table)
             (f11-poly-sub
              (f11-poly-mul (nth (+ m 2) table)
                                     (f11-poly-square
                                      (nth (- m 1) table)))
              (f11-poly-mul (nth (- m 2) table)
                                     (f11-poly-square
                                      (nth (+ m 1) table)))))))
  :hints (("Goal" :use division-polynomial-even-index-arithmetic
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(f11-division-polynomial-recurrence-step oddp evenp)))))

(local
 (defthm f11-division-polynomial-odd-index-positive
   (implies (natp m) (posp (nfix (+ 1 (* 2 m)))))))

(local
 (defthm f11-division-polynomial-even-index-positive
   (implies (and (natp m) (<= 3 m))
            (posp (nfix (* 2 m))))))

(local
 (defthm one-less-f11-division-polynomial-odd-index
   (implies (natp m)
            (equal (1- (+ 1 (* 2 m))) (* 2 m)))))

(defthm f11-division-polynomial-odd-even-half
  (implies (and (natp m) (<= 2 m) (evenp m))
           (equal
            (f11-division-polynomial (+ 1 (* 2 m)) a b)
            (f11-poly-sub
             (f11-poly-mul
              (f11-poly-square (f11-division-polynomial-c a b))
              (f11-poly-mul
               (f11-division-polynomial (+ m 2) a b)
               (f11-poly-cube
                (f11-division-polynomial m a b))))
             (f11-poly-mul
              (f11-division-polynomial (- m 1) a b)
              (f11-poly-cube
               (f11-division-polynomial (+ m 1) a b))))))
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-newest-step
                            (n (+ 1 (* 2 m))))
                 f11-division-polynomial-odd-index-positive
                 one-less-f11-division-polynomial-odd-index
                 (:instance f11-division-polynomial-recurrence-step-odd-even-half
                            (table (f11-division-polynomial-table (* 2 m) a b)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (- m 1)) (n (* 2 m)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k m) (n (* 2 m)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 1)) (n (* 2 m)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 2)) (n (* 2 m))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(nfix posp natp
                                        f11-division-polynomial-odd-index-positive)))))

(defthm f11-division-polynomial-odd-odd-half
  (implies (and (natp m) (<= 2 m) (oddp m))
           (equal
            (f11-division-polynomial (+ 1 (* 2 m)) a b)
            (f11-poly-sub
             (f11-poly-mul
              (f11-division-polynomial (+ m 2) a b)
              (f11-poly-cube (f11-division-polynomial m a b)))
             (f11-poly-mul
              (f11-poly-square (f11-division-polynomial-c a b))
              (f11-poly-mul
               (f11-division-polynomial (- m 1) a b)
               (f11-poly-cube
                (f11-division-polynomial (+ m 1) a b)))))))
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-newest-step
                            (n (+ 1 (* 2 m))))
                 f11-division-polynomial-odd-index-positive
                 one-less-f11-division-polynomial-odd-index
                 (:instance f11-division-polynomial-recurrence-step-odd-odd-half
                            (table (f11-division-polynomial-table (* 2 m) a b)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k (- m 1)) (n (* 2 m)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k m) (n (* 2 m)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k (+ m 1)) (n (* 2 m)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k (+ m 2)) (n (* 2 m))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(nfix posp natp
                                        f11-division-polynomial-odd-index-positive)))))

(defthm f11-division-polynomial-even
  (implies (and (natp m) (<= 3 m))
           (equal
            (f11-division-polynomial (* 2 m) a b)
            (f11-poly-mul
             (f11-division-polynomial m a b)
             (f11-poly-sub
              (f11-poly-mul
               (f11-division-polynomial (+ m 2) a b)
               (f11-poly-square
                (f11-division-polynomial (- m 1) a b)))
              (f11-poly-mul
               (f11-division-polynomial (- m 2) a b)
               (f11-poly-square
                (f11-division-polynomial (+ m 1) a b)))))))
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-newest-step (n (* 2 m)))
                 f11-division-polynomial-even-index-positive
                 (:instance f11-division-polynomial-recurrence-step-even
                            (table (f11-division-polynomial-table (1- (* 2 m)) a b)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k (- m 2)) (n (1- (* 2 m))))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k (- m 1)) (n (1- (* 2 m))))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k m) (n (1- (* 2 m))))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k (+ m 1)) (n (1- (* 2 m))))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator (k (+ m 2)) (n (1- (* 2 m)))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(nfix posp natp
                                        f11-division-polynomial-even-index-positive)))))

(local
 (defthm f11-division-polynomial-odd-lower-index-bounds
   (implies (and (natp m) (<= 2 m))
            (and (natp (+ 1 (* 2 m)))
                 (natp (- m 1))
                 (natp m)
                 (natp (+ m 1))
                 (natp (+ m 2))
                 (<= (- m 1) (+ 1 (* 2 m)))
                 (<= m (+ 1 (* 2 m)))
                 (<= (+ m 1) (+ 1 (* 2 m)))
                 (<= (+ m 2) (+ 1 (* 2 m)))))))

(local
 (defthm f11-division-polynomial-even-lower-index-bounds
   (implies (and (natp m) (<= 3 m))
            (and (natp (* 2 m))
                 (natp (- m 2))
                 (natp (- m 1))
                 (natp m)
                 (natp (+ m 1))
                 (natp (+ m 2))
                 (<= (- m 2) (* 2 m))
                 (<= (- m 1) (* 2 m))
                 (<= m (* 2 m))
                 (<= (+ m 1) (* 2 m))
                 (<= (+ m 2) (* 2 m))))))

(defthm f11-division-polynomial-table-entry-recurrence-odd-even-half
  (implies (and (natp m) (<= 2 m) (evenp m)
                (<= (+ 1 (* 2 m)) (nfix n)))
           (equal
            (nth (+ 1 (* 2 m))
                 (f11-division-polynomial-table n a b))
            (f11-division-polynomial-recurrence-step
             (+ 1 (* 2 m))
             (f11-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :use (f11-division-polynomial-odd-lower-index-bounds
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ 1 (* 2 m))))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (- m 1)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k m))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 1)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 2)))
                 f11-division-polynomial-odd-even-half
                 (:instance f11-division-polynomial-recurrence-step-odd-even-half
                            (table (f11-division-polynomial-table n a b))))
           :in-theory (theory 'minimal-theory))))

(defthm f11-division-polynomial-table-entry-recurrence-odd-odd-half
  (implies (and (natp m) (<= 2 m) (oddp m)
                (<= (+ 1 (* 2 m)) (nfix n)))
           (equal
            (nth (+ 1 (* 2 m))
                 (f11-division-polynomial-table n a b))
            (f11-division-polynomial-recurrence-step
             (+ 1 (* 2 m))
             (f11-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :use (f11-division-polynomial-odd-lower-index-bounds
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ 1 (* 2 m))))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (- m 1)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k m))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 1)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 2)))
                 f11-division-polynomial-odd-odd-half
                 (:instance f11-division-polynomial-recurrence-step-odd-odd-half
                            (table (f11-division-polynomial-table n a b))))
           :in-theory (theory 'minimal-theory))))

(defthm f11-division-polynomial-table-entry-recurrence-even-index
  (implies (and (natp m) (<= 3 m)
                (<= (* 2 m) (nfix n)))
           (equal
            (nth (* 2 m) (f11-division-polynomial-table n a b))
            (f11-division-polynomial-recurrence-step
             (* 2 m) (f11-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :use (f11-division-polynomial-even-lower-index-bounds
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (* 2 m)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (- m 2)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (- m 1)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k m))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 1)))
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 2)))
                 f11-division-polynomial-even
                 (:instance f11-division-polynomial-recurrence-step-even
                            (table (f11-division-polynomial-table n a b))))
           :in-theory (theory 'minimal-theory))))

(local
 (defthm f11-natural-below-five-cases-for-f11
   (implies (and (natp k) (< k 5))
            (or (equal k 0) (equal k 1) (equal k 2)
                (equal k 3) (equal k 4)))))

(defthm f11-division-polynomial-table-entry-recurrence-base
  (implies (and (natp k) (< k 5) (<= k (nfix n)))
           (equal
            (nth k (f11-division-polynomial-table n a b))
            (f11-division-polynomial-recurrence-step
             k (f11-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :cases ((equal k 0) (equal k 1) (equal k 2)
                   (equal k 3) (equal k 4))
           :use (f11-natural-below-five-cases-for-f11
                 (:instance f11-division-polynomial-table-lookup-is-evaluator)
                 (:instance f11-division-polynomial-recurrence-step-base
                            (table (f11-division-polynomial-table n a b)))
                 f11-division-polynomial-evaluator-base-equations)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(f11-division-polynomial-recurrence-step-base
                         nfix)))))

(local
 (defthm f11-division-polynomial-index-floor-classification
   (implies (natp k)
            (let ((m (floor k 2)))
              (and (natp m)
                   (or (evenp k) (oddp k))
                   (or (evenp m) (oddp m))
                   (implies (oddp k) (equal k (+ 1 (* 2 m))))
                   (implies (evenp k) (equal k (* 2 m)))
                   (implies (and (<= 5 k) (oddp k)) (<= 2 m))
                   (implies (and (<= 5 k) (evenp k)) (<= 3 m)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable oddp evenp)))))

(defthm f11-division-polynomial-table-entry-recurrence
  (implies (and (natp k) (<= k (nfix n)))
           (equal
            (nth k (f11-division-polynomial-table n a b))
            (f11-division-polynomial-recurrence-step
             k (f11-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :cases ((< k 5))
           :use (f11-division-polynomial-index-floor-classification
                 f11-division-polynomial-table-entry-recurrence-base
                 (:instance f11-division-polynomial-table-entry-recurrence-odd-even-half
                            (m (floor k 2)))
                 (:instance f11-division-polynomial-table-entry-recurrence-odd-odd-half
                            (m (floor k 2)))
                 (:instance f11-division-polynomial-table-entry-recurrence-even-index
                            (m (floor k 2))))
           :in-theory (theory 'minimal-theory))))

(local
 (defun division-polynomial-sequence-index-induct (n)
   (if (zp n) nil
     (division-polynomial-sequence-index-induct (1- n)))))

(local
 (defthm natp-of-nfix-for-f11-division-polynomial
   (natp (nfix n))
   :hints (("Goal" :in-theory (enable nfix natp)))))

(local
 (defthm less-equal-reflexive-for-f11-division-polynomial
   (<= x x)))

(defthm f11-division-polynomial-table-entries-satisfy-sequence
  (implies (and (natp k) (<= k (nfix n)))
           (f11-division-polynomial-sequence-entries-p
            k (f11-division-polynomial-table n a b) a b))
  :hints (("Goal"
           :induct (division-polynomial-sequence-index-induct k)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(division-polynomial-sequence-index-induct
              f11-division-polynomial-sequence-entries-p
              f11-division-polynomial-table-entry-recurrence
              natp zp)))))

(defthm f11-division-polynomial-table-satisfies-sequence-p
  (f11-division-polynomial-sequence-p
   n (f11-division-polynomial-table n a b) a b)
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-table-entries-satisfy-sequence
                            (k (nfix n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-division-polynomial-sequence-p
              len-of-f11-division-polynomial-table
              true-listp-of-f11-division-polynomial-table
              natp-of-nfix-for-f11-division-polynomial
              less-equal-reflexive-for-f11-division-polynomial)))))


(defthm f11-division-polynomial-sequence-entries-p-at-index
  (implies (and (f11-division-polynomial-sequence-entries-p
                 n table a b)
                (natp k) (natp n) (<= k n))
           (equal (nth k table)
                  (f11-division-polynomial-recurrence-step
                   k table a b)))
  :hints (("Goal"
           :induct (division-polynomial-sequence-index-induct n)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(division-polynomial-sequence-index-induct
              f11-division-polynomial-sequence-entries-p
              natp zp)))))

(defthm f11-division-polynomial-sequence-p-recurrence
  (implies (and (f11-division-polynomial-sequence-p n table a b)
                (natp k) (<= k (nfix n)))
           (equal (nth k table)
                  (f11-division-polynomial-recurrence-step
                   k table a b)))
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-sequence-entries-p-at-index
                            (n (nfix n))))
           :in-theory (enable f11-division-polynomial-sequence-p))))


(defthm f11-division-polynomial-recurrence-step-lower-congruence
  (implies (and (natp n) (<= 5 n)
                (equal (nth (floor n 2) left) (nth (floor n 2) right))
                (equal (nth (- (floor n 2) 2) left) (nth (- (floor n 2) 2) right))
                (equal (nth (- (floor n 2) 1) left) (nth (- (floor n 2) 1) right))
                (equal (nth (+ (floor n 2) 1) left) (nth (+ (floor n 2) 1) right))
                (equal (nth (+ (floor n 2) 2) left) (nth (+ (floor n 2) 2) right)))
           (equal (f11-division-polynomial-recurrence-step n left a b)
                  (f11-division-polynomial-recurrence-step n right a b)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(f11-division-polynomial-recurrence-step
                             nfix-when-natp-for-f11-table)))))
(local
 (defun division-polynomial-sequence-agrees-through-p (k table a b)
   (and (equal (nth k table)
               (f11-division-polynomial k a b))
        (if (zp k) t
          (division-polynomial-sequence-agrees-through-p
           (1- k) table a b)))))

(local
 (defthm division-polynomial-sequence-agrees-through-p-at-index
   (implies (and (division-polynomial-sequence-agrees-through-p
                  k table a b)
                 (natp j) (natp k) (<= j k))
            (equal (nth j table)
                   (f11-division-polynomial j a b)))
   :hints (("Goal"
            :induct (division-polynomial-sequence-index-induct k)
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(division-polynomial-sequence-index-induct
               division-polynomial-sequence-agrees-through-p
               natp zp))))))

(local
 (defthm division-polynomial-later-lower-index-bounds
   (implies (and (natp k) (<= 5 k))
            (let ((m (floor k 2)))
              (and (natp m)
                   (equal (nfix k) k)
                   (natp (1- k))
                   (natp (- m 2))
                   (natp (- m 1))
                   (natp (+ m 1))
                   (natp (+ m 2))
                   (< (- m 2) k)
                   (< (- m 1) k)
                   (< m k)
                   (< (+ m 1) k)
                   (< (+ m 2) k)
                   (<= (- m 2) (1- k))
                   (<= (- m 1) (1- k))
                   (<= m (1- k))
                   (<= (+ m 1) (1- k))
                   (<= (+ m 2) (1- k))
                   (<= (- m 2) (nfix k))
                   (<= (- m 1) (nfix k))
                   (<= m (nfix k))
                   (<= (+ m 1) (nfix k))
                   (<= (+ m 2) (nfix k)))))))

(local
 (defthm f11-division-polynomial-specified-table-base-agreement
   (implies (and (f11-division-polynomial-sequence-p n table a b)
                 (natp k) (< k 5) (<= k (nfix n)))
            (equal (nth k table)
                   (f11-division-polynomial k a b)))
   :hints (("Goal"
            :cases ((equal k 0) (equal k 1) (equal k 2)
                    (equal k 3) (equal k 4))
            :use (f11-natural-below-five-cases-for-f11
                  (:instance f11-division-polynomial-sequence-p-recurrence)
                  (:instance f11-division-polynomial-recurrence-step-base)
                  f11-division-polynomial-evaluator-base-equations)
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(f11-division-polynomial-recurrence-step-base
               nfix))))))

(local
 (defthm f11-division-polynomial-specified-table-later-agreement
   (implies (and (f11-division-polynomial-sequence-p n table a b)
                 (natp k) (<= 5 k) (<= k (nfix n))
                 (division-polynomial-sequence-agrees-through-p
                  (1- k) table a b))
            (equal (nth k table)
                   (f11-division-polynomial k a b)))
   :hints (("Goal"
            :use (division-polynomial-later-lower-index-bounds
                  (:instance f11-division-polynomial-sequence-p-recurrence)
                  (:instance f11-division-polynomial-table-entry-recurrence
                             (n k))
                  (:instance f11-division-polynomial-table-lookup-is-evaluator
                             (n k) (k k))
                  (:instance f11-division-polynomial-recurrence-step-lower-congruence
                             (n k) (left table)
                             (right (f11-division-polynomial-table k a b)))
                  (:instance division-polynomial-sequence-agrees-through-p-at-index
                             (k (1- k)) (j (floor k 2)))
                  (:instance division-polynomial-sequence-agrees-through-p-at-index
                             (k (1- k)) (j (- (floor k 2) 2)))
                  (:instance division-polynomial-sequence-agrees-through-p-at-index
                             (k (1- k)) (j (- (floor k 2) 1)))
                  (:instance division-polynomial-sequence-agrees-through-p-at-index
                             (k (1- k)) (j (+ (floor k 2) 1)))
                  (:instance division-polynomial-sequence-agrees-through-p-at-index
                             (k (1- k)) (j (+ (floor k 2) 2)))
                  (:instance f11-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (floor k 2)))
                  (:instance f11-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (- (floor k 2) 2)))
                  (:instance f11-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (- (floor k 2) 1)))
                  (:instance f11-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (+ (floor k 2) 1)))
                  (:instance f11-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (+ (floor k 2) 2))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm f11-division-polynomial-specified-table-current-agreement
   (implies (and (f11-division-polynomial-sequence-p n table a b)
                 (natp k) (<= k (nfix n))
                 (implies (posp k)
                          (division-polynomial-sequence-agrees-through-p
                           (1- k) table a b)))
            (equal (nth k table)
                   (f11-division-polynomial k a b)))
   :hints (("Goal"
            :cases ((< k 5))
            :use (f11-division-polynomial-specified-table-base-agreement
                  f11-division-polynomial-specified-table-later-agreement)
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(posp integerp-when-natp-for-f11-table))))))

(local
 (defthm f11-division-polynomial-specified-table-agrees-through
   (implies (and (f11-division-polynomial-sequence-p n table a b)
                 (natp k) (<= k (nfix n)))
            (division-polynomial-sequence-agrees-through-p k table a b))
   :hints (("Goal"
            :induct (division-polynomial-sequence-index-induct k)
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(division-polynomial-sequence-index-induct
               division-polynomial-sequence-agrees-through-p
               f11-division-polynomial-specified-table-current-agreement
               natp posp zp))))))

(defthm f11-division-polynomial-specified-table-entry-agreement
  (implies (and (f11-division-polynomial-sequence-p n table a b)
                (natp k) (<= k (nfix n)))
           (equal (nth k table)
                  (f11-division-polynomial k a b)))
  :hints (("Goal"
           :use f11-division-polynomial-specified-table-agrees-through
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(division-polynomial-sequence-agrees-through-p)))))

(defthm f11-division-polynomial-generated-table-correspondence
  (and (f11-division-polynomial-sequence-p
        n (f11-division-polynomial-table n a b) a b)
       (equal
        (nth (nfix n) (f11-division-polynomial-table n a b))
        (f11-division-polynomial n a b)))
  :hints (("Goal"
           :use (f11-division-polynomial-table-satisfies-sequence-p
                 (:instance f11-division-polynomial-table-lookup-is-evaluator
                            (k (nfix n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-division-polynomial-of-nfix
              natp-of-nfix-for-f11-division-polynomial
              less-equal-reflexive-for-f11-division-polynomial)))))

(defthm f11-division-polynomial-sequence-p-entry-correspondence
  (implies (and (f11-division-polynomial-sequence-p n table a b)
                (natp k) (<= k (nfix n)))
           (equal (nth k table)
                  (f11-division-polynomial k a b)))
  :hints (("Goal"
           :use f11-division-polynomial-specified-table-entry-agreement
           :in-theory (theory 'minimal-theory))))

(defthm f11-division-polynomial-sequence-p-final-entry-correspondence
  (implies (f11-division-polynomial-sequence-p n table a b)
           (equal (nth (nfix n) table)
                  (f11-division-polynomial n a b)))
  :hints (("Goal"
           :use ((:instance f11-division-polynomial-sequence-p-entry-correspondence
                            (k (nfix n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-division-polynomial-of-nfix
              natp-of-nfix-for-f11-division-polynomial
              less-equal-reflexive-for-f11-division-polynomial)))))

(defthm f11-division-polynomial-all-index-semantic-correspondence
  (and
   (f11-division-polynomial-sequence-p
    n (f11-division-polynomial-table n a b) a b)
   (implies (and (f11-division-polynomial-sequence-p n table a b)
                 (natp k) (<= k (nfix n)))
            (equal (nth k table)
                   (f11-division-polynomial k a b)))
   (implies (f11-division-polynomial-sequence-p n table a b)
            (equal (nth (nfix n) table)
                   (f11-division-polynomial n a b)))
   (equal (f11-division-polynomial (nfix n) a b)
          (f11-division-polynomial n a b))
   (equal (f11-division-polynomial
           n (gfield::f11-fix a) (gfield::f11-fix b))
          (f11-division-polynomial n a b)))
  :rule-classes nil
  :hints (("Goal"
           :use (f11-division-polynomial-table-satisfies-sequence-p
                 f11-division-polynomial-sequence-p-entry-correspondence
                 f11-division-polynomial-sequence-p-final-entry-correspondence
                 f11-division-polynomial-of-nfix
                 f11-division-polynomial-of-coefficient-fixes)
           :in-theory (theory 'minimal-theory))))
