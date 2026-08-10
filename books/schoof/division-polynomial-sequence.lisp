(in-package "GPOLY")

(include-book "division-polynomial-table")
(include-book "arithmetic-5/top" :dir :system)

; Relational, bounded recurrence specification.  In particular, this does not
; mention the executable table builder.
(defun finite-field-division-polynomial-sequence-entries-p (k table a b)
  (declare (xargs :guard (and (natp k) (true-listp table))))
  (and (equal (nth k table)
              (finite-field-division-polynomial-recurrence-step k table a b))
       (if (zp k)
           t
         (finite-field-division-polynomial-sequence-entries-p
          (1- k) table a b))))

(defun finite-field-division-polynomial-sequence-p (n table a b)
  (declare (xargs :guard t))
  (and (true-listp table)
       (equal (len table) (+ 1 (nfix n)))
       (finite-field-division-polynomial-sequence-entries-p
        (nfix n) table a b)))

(defthm finite-field-division-polynomial-sequence-p-exact-length
  (implies (finite-field-division-polynomial-sequence-p n table a b)
           (and (true-listp table)
                (equal (len table) (+ 1 (nfix n)))))
  :rule-classes nil)

(local
 (defun division-polynomial-sequence-index-induct (n)
   (if (zp n) nil
     (division-polynomial-sequence-index-induct (1- n)))))

(defthm finite-field-division-polynomial-sequence-entries-p-at-index
  (implies (and (finite-field-division-polynomial-sequence-entries-p
                 n table a b)
                (natp k) (natp n) (<= k n))
           (equal (nth k table)
                  (finite-field-division-polynomial-recurrence-step
                   k table a b)))
  :hints (("Goal"
           :induct (division-polynomial-sequence-index-induct n)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(division-polynomial-sequence-index-induct
              finite-field-division-polynomial-sequence-entries-p
              natp zp)))))

(defthm finite-field-division-polynomial-sequence-p-recurrence
  (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                (natp k) (<= k (nfix n)))
           (equal (nth k table)
                  (finite-field-division-polynomial-recurrence-step
                   k table a b)))
  :hints (("Goal"
           :use ((:instance finite-field-division-polynomial-sequence-entries-p-at-index
                            (n (nfix n))))
           :in-theory (enable finite-field-division-polynomial-sequence-p))))

; The step reads no index at or above N.  This narrow congruence theorem is the
; induction seam between the relational specification and the builder.
(defthm finite-field-division-polynomial-recurrence-step-lower-congruence
  (implies (and (natp n)
                (<= 5 n)
                (equal (nth (floor n 2) left) (nth (floor n 2) right))
                (equal (nth (- (floor n 2) 2) left)
                       (nth (- (floor n 2) 2) right))
                (equal (nth (- (floor n 2) 1) left)
                       (nth (- (floor n 2) 1) right))
                (equal (nth (+ (floor n 2) 1) left)
                       (nth (+ (floor n 2) 1) right))
                (equal (nth (+ (floor n 2) 2) left)
                       (nth (+ (floor n 2) 2) right)))
           (equal (finite-field-division-polynomial-recurrence-step n left a b)
                  (finite-field-division-polynomial-recurrence-step n right a b)))
  :hints (("Goal"
           :in-theory (enable finite-field-division-polynomial-recurrence-step))))

(defun finite-field-division-polynomial (n a b)
  (declare (xargs :guard t))
  (nth (nfix n) (finite-field-division-polynomial-table n a b)))

(local
 (defthm nfix-idempotent-for-division-polynomial
   (equal (nfix (nfix n)) (nfix n))
   :hints (("Goal" :in-theory (enable nfix)))))

(local
 (defthm natp-of-nfix-for-division-polynomial
   (natp (nfix n))
   :hints (("Goal" :in-theory (enable nfix natp)))))

(local
 (defthm less-equal-reflexive-for-division-polynomial
   (<= x x)))

(defthm finite-field-division-polynomial-of-nfix
  (equal (finite-field-division-polynomial (nfix n) a b)
         (finite-field-division-polynomial n a b))
  :hints (("Goal"
           :use finite-field-division-polynomial-table-of-nfix
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(finite-field-division-polynomial
                             nfix-idempotent-for-division-polynomial)))))

(defthm finite-field-division-polynomial-of-coefficient-fixes
  (equal (finite-field-division-polynomial
          n (gfield::finite-field-fix a) (gfield::finite-field-fix b))
         (finite-field-division-polynomial n a b))
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(finite-field-division-polynomial
              finite-field-division-polynomial-table-of-coefficient-fixes)))))

(defthm finite-field-canonical-polynomial-p-of-division-polynomial
  (finite-field-canonical-polynomial-p
   (finite-field-division-polynomial n a b))
  :hints (("Goal"
           :use ((:instance finite-field-canonical-polynomial-p-of-table-entry
                            (k (nfix n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(finite-field-division-polynomial
              natp-of-nfix-for-division-polynomial
              less-equal-reflexive-for-division-polynomial)))))

(defthm finite-field-polynomial-p-of-division-polynomial
  (finite-field-polynomial-p (finite-field-division-polynomial n a b))
  :hints (("Goal"
           :use finite-field-canonical-polynomial-p-of-division-polynomial
           :in-theory (enable finite-field-canonical-polynomial-p
                              finite-field-polynomial-p))))

(defthm finite-field-division-polynomial-newest-step
  (implies (posp (nfix n))
           (equal (finite-field-division-polynomial n a b)
                  (finite-field-division-polynomial-recurrence-step
                   (nfix n)
                   (finite-field-division-polynomial-table
                    (1- (nfix n)) a b)
                   a b)))
  :hints (("Goal"
           :use finite-field-division-polynomial-table-newest-entry
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(finite-field-division-polynomial)))))

(defthm finite-field-division-polynomial-table-lookup-is-evaluator
  (implies (and (natp k) (<= k (nfix n)))
           (equal (nth k (finite-field-division-polynomial-table n a b))
                  (finite-field-division-polynomial k a b)))
  :hints (("Goal"
           :use finite-field-division-polynomial-table-lookup-stable
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(finite-field-division-polynomial
                                        nfix-when-natp-for-division-polynomial-table)))))

(defthm finite-field-division-polynomial-index-zero
  (equal (finite-field-division-polynomial 0 a b)
         (finite-field-division-polynomial-base 0 a b))
  :hints (("Goal" :in-theory (enable finite-field-division-polynomial
                                      finite-field-division-polynomial-table
                                      finite-field-division-polynomial-table-nat))))

(defthm finite-field-division-polynomial-evaluator-base-equations
  (and (equal (finite-field-division-polynomial 0 a b)
              (finite-field-division-polynomial-base 0 a b))
       (equal (finite-field-division-polynomial 1 a b)
              (finite-field-division-polynomial-base 1 a b))
       (equal (finite-field-division-polynomial 2 a b)
              (finite-field-division-polynomial-base 2 a b))
       (equal (finite-field-division-polynomial 3 a b)
              (finite-field-division-polynomial-base 3 a b))
       (equal (finite-field-division-polynomial 4 a b)
              (finite-field-division-polynomial-base 4 a b)))
  :hints (("Goal"
           :use ((:instance finite-field-division-polynomial-newest-step (n 1))
                 (:instance finite-field-division-polynomial-newest-step (n 2))
                 (:instance finite-field-division-polynomial-newest-step (n 3))
                 (:instance finite-field-division-polynomial-newest-step (n 4))
                 finite-field-division-polynomial-index-zero)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(finite-field-division-polynomial
                         finite-field-division-polynomial-recurrence-step-base
                         finite-field-division-polynomial-base-of-nfix
                         posp nfix nth car-cons)))))

(local
 (defthm division-polynomial-odd-index-positive
   (implies (natp m) (posp (nfix (+ 1 (* 2 m)))))))

(local
 (defthm division-polynomial-even-index-positive
   (implies (and (natp m) (<= 3 m))
            (posp (nfix (* 2 m))))))

(local
 (defthm one-less-division-polynomial-odd-index
   (implies (natp m)
            (equal (1- (+ 1 (* 2 m))) (* 2 m)))))

(defthm finite-field-division-polynomial-odd-even-half
  (implies (and (natp m) (<= 2 m) (evenp m))
           (equal
            (finite-field-division-polynomial (+ 1 (* 2 m)) a b)
            (finite-field-poly-sub
             (finite-field-poly-mul
              (finite-field-poly-square (finite-field-division-polynomial-c a b))
              (finite-field-poly-mul
               (finite-field-division-polynomial (+ m 2) a b)
               (finite-field-poly-cube
                (finite-field-division-polynomial m a b))))
             (finite-field-poly-mul
              (finite-field-division-polynomial (- m 1) a b)
              (finite-field-poly-cube
               (finite-field-division-polynomial (+ m 1) a b))))))
  :hints (("Goal"
           :use ((:instance finite-field-division-polynomial-newest-step
                            (n (+ 1 (* 2 m))))
                 division-polynomial-odd-index-positive
                 one-less-division-polynomial-odd-index
                 (:instance finite-field-division-polynomial-recurrence-step-odd-even-half
                            (table (finite-field-division-polynomial-table (* 2 m) a b)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (- m 1)) (n (* 2 m)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k m) (n (* 2 m)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 1)) (n (* 2 m)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 2)) (n (* 2 m))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(nfix posp natp
                                        division-polynomial-odd-index-positive)))))

(defthm finite-field-division-polynomial-odd-odd-half
  (implies (and (natp m) (<= 2 m) (oddp m))
           (equal
            (finite-field-division-polynomial (+ 1 (* 2 m)) a b)
            (finite-field-poly-sub
             (finite-field-poly-mul
              (finite-field-division-polynomial (+ m 2) a b)
              (finite-field-poly-cube (finite-field-division-polynomial m a b)))
             (finite-field-poly-mul
              (finite-field-poly-square (finite-field-division-polynomial-c a b))
              (finite-field-poly-mul
               (finite-field-division-polynomial (- m 1) a b)
               (finite-field-poly-cube
                (finite-field-division-polynomial (+ m 1) a b)))))))
  :hints (("Goal"
           :use ((:instance finite-field-division-polynomial-newest-step
                            (n (+ 1 (* 2 m))))
                 division-polynomial-odd-index-positive
                 one-less-division-polynomial-odd-index
                 (:instance finite-field-division-polynomial-recurrence-step-odd-odd-half
                            (table (finite-field-division-polynomial-table (* 2 m) a b)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k (- m 1)) (n (* 2 m)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k m) (n (* 2 m)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k (+ m 1)) (n (* 2 m)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k (+ m 2)) (n (* 2 m))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(nfix posp natp
                                        division-polynomial-odd-index-positive)))))

(defthm finite-field-division-polynomial-even
  (implies (and (natp m) (<= 3 m))
           (equal
            (finite-field-division-polynomial (* 2 m) a b)
            (finite-field-poly-mul
             (finite-field-division-polynomial m a b)
             (finite-field-poly-sub
              (finite-field-poly-mul
               (finite-field-division-polynomial (+ m 2) a b)
               (finite-field-poly-square
                (finite-field-division-polynomial (- m 1) a b)))
              (finite-field-poly-mul
               (finite-field-division-polynomial (- m 2) a b)
               (finite-field-poly-square
                (finite-field-division-polynomial (+ m 1) a b)))))))
  :hints (("Goal"
           :use ((:instance finite-field-division-polynomial-newest-step (n (* 2 m)))
                 division-polynomial-even-index-positive
                 (:instance finite-field-division-polynomial-recurrence-step-even
                            (table (finite-field-division-polynomial-table (1- (* 2 m)) a b)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k (- m 2)) (n (1- (* 2 m))))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k (- m 1)) (n (1- (* 2 m))))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k m) (n (1- (* 2 m))))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k (+ m 1)) (n (1- (* 2 m))))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator (k (+ m 2)) (n (1- (* 2 m)))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(nfix posp natp
                                        division-polynomial-even-index-positive)))))


(verify-guards finite-field-division-polynomial-sequence-entries-p)
(verify-guards finite-field-division-polynomial-sequence-p)
(verify-guards finite-field-division-polynomial)
