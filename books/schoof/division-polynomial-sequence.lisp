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

(local
 (defthm division-polynomial-odd-lower-index-bounds
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
 (defthm division-polynomial-even-lower-index-bounds
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

(defthm finite-field-division-polynomial-table-entry-recurrence-odd-even-half
  (implies (and (natp m) (<= 2 m) (evenp m)
                (<= (+ 1 (* 2 m)) (nfix n)))
           (equal
            (nth (+ 1 (* 2 m))
                 (finite-field-division-polynomial-table n a b))
            (finite-field-division-polynomial-recurrence-step
             (+ 1 (* 2 m))
             (finite-field-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :use (division-polynomial-odd-lower-index-bounds
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ 1 (* 2 m))))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (- m 1)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k m))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 1)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 2)))
                 finite-field-division-polynomial-odd-even-half
                 (:instance finite-field-division-polynomial-recurrence-step-odd-even-half
                            (table (finite-field-division-polynomial-table n a b))))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-division-polynomial-table-entry-recurrence-odd-odd-half
  (implies (and (natp m) (<= 2 m) (oddp m)
                (<= (+ 1 (* 2 m)) (nfix n)))
           (equal
            (nth (+ 1 (* 2 m))
                 (finite-field-division-polynomial-table n a b))
            (finite-field-division-polynomial-recurrence-step
             (+ 1 (* 2 m))
             (finite-field-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :use (division-polynomial-odd-lower-index-bounds
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ 1 (* 2 m))))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (- m 1)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k m))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 1)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 2)))
                 finite-field-division-polynomial-odd-odd-half
                 (:instance finite-field-division-polynomial-recurrence-step-odd-odd-half
                            (table (finite-field-division-polynomial-table n a b))))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-division-polynomial-table-entry-recurrence-even-index
  (implies (and (natp m) (<= 3 m)
                (<= (* 2 m) (nfix n)))
           (equal
            (nth (* 2 m) (finite-field-division-polynomial-table n a b))
            (finite-field-division-polynomial-recurrence-step
             (* 2 m) (finite-field-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :use (division-polynomial-even-lower-index-bounds
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (* 2 m)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (- m 2)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (- m 1)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k m))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 1)))
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (+ m 2)))
                 finite-field-division-polynomial-even
                 (:instance finite-field-division-polynomial-recurrence-step-even
                            (table (finite-field-division-polynomial-table n a b))))
           :in-theory (theory 'minimal-theory))))

(local
 (defthm natural-below-five-cases
   (implies (and (natp k) (< k 5))
            (or (equal k 0) (equal k 1) (equal k 2)
                (equal k 3) (equal k 4)))))

(defthm finite-field-division-polynomial-table-entry-recurrence-base
  (implies (and (natp k) (< k 5) (<= k (nfix n)))
           (equal
            (nth k (finite-field-division-polynomial-table n a b))
            (finite-field-division-polynomial-recurrence-step
             k (finite-field-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :cases ((equal k 0) (equal k 1) (equal k 2)
                   (equal k 3) (equal k 4))
           :use (natural-below-five-cases
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator)
                 (:instance finite-field-division-polynomial-recurrence-step-base
                            (table (finite-field-division-polynomial-table n a b)))
                 finite-field-division-polynomial-evaluator-base-equations)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(finite-field-division-polynomial-recurrence-step-base
                         nfix)))))

(local
 (defthm division-polynomial-index-floor-classification
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

(defthm finite-field-division-polynomial-table-entry-recurrence
  (implies (and (natp k) (<= k (nfix n)))
           (equal
            (nth k (finite-field-division-polynomial-table n a b))
            (finite-field-division-polynomial-recurrence-step
             k (finite-field-division-polynomial-table n a b) a b)))
  :hints (("Goal"
           :cases ((< k 5))
           :use (division-polynomial-index-floor-classification
                 finite-field-division-polynomial-table-entry-recurrence-base
                 (:instance finite-field-division-polynomial-table-entry-recurrence-odd-even-half
                            (m (floor k 2)))
                 (:instance finite-field-division-polynomial-table-entry-recurrence-odd-odd-half
                            (m (floor k 2)))
                 (:instance finite-field-division-polynomial-table-entry-recurrence-even-index
                            (m (floor k 2))))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-division-polynomial-table-entries-satisfy-sequence
  (implies (and (natp k) (<= k (nfix n)))
           (finite-field-division-polynomial-sequence-entries-p
            k (finite-field-division-polynomial-table n a b) a b))
  :hints (("Goal"
           :induct (division-polynomial-sequence-index-induct k)
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(division-polynomial-sequence-index-induct
              finite-field-division-polynomial-sequence-entries-p
              finite-field-division-polynomial-table-entry-recurrence
              natp zp)))))

(defthm finite-field-division-polynomial-table-satisfies-sequence-p
  (finite-field-division-polynomial-sequence-p
   n (finite-field-division-polynomial-table n a b) a b)
  :hints (("Goal"
           :use ((:instance finite-field-division-polynomial-table-entries-satisfy-sequence
                            (k (nfix n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(finite-field-division-polynomial-sequence-p
              len-of-finite-field-division-polynomial-table
              true-listp-of-finite-field-division-polynomial-table
              natp-of-nfix-for-division-polynomial
              less-equal-reflexive-for-division-polynomial)))))

(local
 (defun division-polynomial-sequence-agrees-through-p (k table a b)
   (and (equal (nth k table)
               (finite-field-division-polynomial k a b))
        (if (zp k) t
          (division-polynomial-sequence-agrees-through-p
           (1- k) table a b)))))

(local
 (defthm division-polynomial-sequence-agrees-through-p-at-index
   (implies (and (division-polynomial-sequence-agrees-through-p
                  k table a b)
                 (natp j) (natp k) (<= j k))
            (equal (nth j table)
                   (finite-field-division-polynomial j a b)))
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
 (defthm finite-field-division-polynomial-specified-table-base-agreement
   (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                 (natp k) (< k 5) (<= k (nfix n)))
            (equal (nth k table)
                   (finite-field-division-polynomial k a b)))
   :hints (("Goal"
            :cases ((equal k 0) (equal k 1) (equal k 2)
                    (equal k 3) (equal k 4))
            :use (natural-below-five-cases
                  (:instance finite-field-division-polynomial-sequence-p-recurrence)
                  (:instance finite-field-division-polynomial-recurrence-step-base)
                  finite-field-division-polynomial-evaluator-base-equations)
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(finite-field-division-polynomial-recurrence-step-base
               nfix))))))

(local
 (defthm finite-field-division-polynomial-specified-table-later-agreement
   (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                 (natp k) (<= 5 k) (<= k (nfix n))
                 (division-polynomial-sequence-agrees-through-p
                  (1- k) table a b))
            (equal (nth k table)
                   (finite-field-division-polynomial k a b)))
   :hints (("Goal"
            :use (division-polynomial-later-lower-index-bounds
                  (:instance finite-field-division-polynomial-sequence-p-recurrence)
                  (:instance finite-field-division-polynomial-table-entry-recurrence
                             (n k))
                  (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                             (n k) (k k))
                  (:instance finite-field-division-polynomial-recurrence-step-lower-congruence
                             (n k) (left table)
                             (right (finite-field-division-polynomial-table k a b)))
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
                  (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (floor k 2)))
                  (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (- (floor k 2) 2)))
                  (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (- (floor k 2) 1)))
                  (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (+ (floor k 2) 1)))
                  (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                             (n k) (k (+ (floor k 2) 2))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm finite-field-division-polynomial-specified-table-current-agreement
   (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                 (natp k) (<= k (nfix n))
                 (implies (posp k)
                          (division-polynomial-sequence-agrees-through-p
                           (1- k) table a b)))
            (equal (nth k table)
                   (finite-field-division-polynomial k a b)))
   :hints (("Goal"
            :cases ((< k 5))
            :use (finite-field-division-polynomial-specified-table-base-agreement
                  finite-field-division-polynomial-specified-table-later-agreement)
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(posp integerp-when-natp-for-division-polynomial-table))))))

(local
 (defthm finite-field-division-polynomial-specified-table-agrees-through
   (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                 (natp k) (<= k (nfix n)))
            (division-polynomial-sequence-agrees-through-p k table a b))
   :hints (("Goal"
            :induct (division-polynomial-sequence-index-induct k)
            :in-theory
            (union-theories
             (theory 'minimal-theory)
             '(division-polynomial-sequence-index-induct
               division-polynomial-sequence-agrees-through-p
               finite-field-division-polynomial-specified-table-current-agreement
               natp posp zp))))))

(defthm finite-field-division-polynomial-specified-table-entry-agreement
  (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                (natp k) (<= k (nfix n)))
           (equal (nth k table)
                  (finite-field-division-polynomial k a b)))
  :hints (("Goal"
           :use finite-field-division-polynomial-specified-table-agrees-through
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(division-polynomial-sequence-agrees-through-p)))))

(defthm finite-field-division-polynomial-generated-table-correspondence
  (and (finite-field-division-polynomial-sequence-p
        n (finite-field-division-polynomial-table n a b) a b)
       (equal
        (nth (nfix n) (finite-field-division-polynomial-table n a b))
        (finite-field-division-polynomial n a b)))
  :hints (("Goal"
           :use (finite-field-division-polynomial-table-satisfies-sequence-p
                 (:instance finite-field-division-polynomial-table-lookup-is-evaluator
                            (k (nfix n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(finite-field-division-polynomial-of-nfix
              natp-of-nfix-for-division-polynomial
              less-equal-reflexive-for-division-polynomial)))))

(defthm finite-field-division-polynomial-sequence-p-entry-correspondence
  (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                (natp k) (<= k (nfix n)))
           (equal (nth k table)
                  (finite-field-division-polynomial k a b)))
  :hints (("Goal"
           :use finite-field-division-polynomial-specified-table-entry-agreement
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-division-polynomial-sequence-p-final-entry-correspondence
  (implies (finite-field-division-polynomial-sequence-p n table a b)
           (equal (nth (nfix n) table)
                  (finite-field-division-polynomial n a b)))
  :hints (("Goal"
           :use ((:instance finite-field-division-polynomial-sequence-p-entry-correspondence
                            (k (nfix n))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(finite-field-division-polynomial-of-nfix
              natp-of-nfix-for-division-polynomial
              less-equal-reflexive-for-division-polynomial)))))


(verify-guards finite-field-division-polynomial-sequence-entries-p)
(verify-guards finite-field-division-polynomial-sequence-p)
(verify-guards finite-field-division-polynomial)
