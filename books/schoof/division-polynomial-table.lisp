(in-package "GPOLY")

(include-book "division-polynomial-recurrence-step")
(include-book "arithmetic-5/top" :dir :system)

; A deliberately narrow one-element extension interface.  Keeping this local
; avoids making later table proofs depend on a broad append theory.
(defun finite-field-division-polynomial-table-extend (table value)
  (declare (xargs :guard (true-listp table)))
  (if (endp table)
      (list value)
    (cons (car table)
          (finite-field-division-polynomial-table-extend (cdr table) value))))

(defthm true-listp-of-finite-field-division-polynomial-table-extend
  (true-listp (finite-field-division-polynomial-table-extend table value)))

(defthm len-of-finite-field-division-polynomial-table-extend
  (equal (len (finite-field-division-polynomial-table-extend table value))
         (+ 1 (len table))))

(defthm nth-below-of-finite-field-division-polynomial-table-extend
  (implies (and (natp k)
                (< k (len table)))
           (equal (nth k (finite-field-division-polynomial-table-extend
                          table value))
                  (nth k table)))
  :hints (("Goal" :induct (nth k table)
           :in-theory (enable finite-field-division-polynomial-table-extend))))

(defthm nth-at-end-of-finite-field-division-polynomial-table-extend
  (implies (true-listp table)
           (equal (nth (len table)
                       (finite-field-division-polynomial-table-extend table value))
                  value)))

; N is natural internally.  The single recursive result is evaluated once and
; bound as PREFIX; consequently each recurrence-step polynomial is constructed
; once, although each list extension still traverses its prefix.
(defun finite-field-division-polynomial-table-nat (n a b)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (list (finite-field-division-polynomial-base 0 a b))
    (let ((prefix (finite-field-division-polynomial-table-nat (1- n) a b)))
      (finite-field-division-polynomial-table-extend
       prefix
       (finite-field-division-polynomial-recurrence-step n prefix a b)))))

(defun finite-field-division-polynomial-table (n a b)
  (declare (xargs :guard t))
  (finite-field-division-polynomial-table-nat (nfix n) a b))

(defthm finite-field-division-polynomial-table-nat-base
  (equal (finite-field-division-polynomial-table-nat 0 a b)
         (list (finite-field-division-polynomial-base 0 a b))))

(defthm finite-field-division-polynomial-table-base
  (equal (finite-field-division-polynomial-table 0 a b)
         (list (finite-field-division-polynomial-base 0 a b))))

(defthm len-of-finite-field-division-polynomial-table-nat
  (implies (natp n)
           (equal (len (finite-field-division-polynomial-table-nat n a b))
                  (+ 1 n)))
  :hints (("Goal" :induct (finite-field-division-polynomial-table-nat n a b)
           :in-theory (enable finite-field-division-polynomial-table-nat))))

(defthm len-of-finite-field-division-polynomial-table
  (equal (len (finite-field-division-polynomial-table n a b))
         (+ 1 (nfix n)))
  :hints (("Goal" :in-theory (enable finite-field-division-polynomial-table))))

(defthm true-listp-of-finite-field-division-polynomial-table-nat
  (true-listp (finite-field-division-polynomial-table-nat n a b)))

(defthm true-listp-of-finite-field-division-polynomial-table
  (true-listp (finite-field-division-polynomial-table n a b)))

(defthm finite-field-division-polynomial-table-nat-newest-at-prefix-length
  (implies (posp n)
           (equal
            (nth (len (finite-field-division-polynomial-table-nat (1- n) a b))
                 (finite-field-division-polynomial-table-nat n a b))
            (finite-field-division-polynomial-recurrence-step
             n (finite-field-division-polynomial-table-nat (1- n) a b) a b)))
  :hints (("Goal"
           :expand ((finite-field-division-polynomial-table-nat n a b))
           :use ((:instance nth-at-end-of-finite-field-division-polynomial-table-extend
                            (table (finite-field-division-polynomial-table-nat (1- n) a b))
                            (value (finite-field-division-polynomial-recurrence-step
                                    n (finite-field-division-polynomial-table-nat (1- n) a b)
                                    a b))))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(posp zp natp
                         true-listp-of-finite-field-division-polynomial-table-nat)))))

(defthm one-plus-one-less-when-posp
  (implies (posp n)
           (equal (+ 1 (1- n)) n)))

(defthm natp-of-one-less-when-posp
  (implies (posp n) (natp (1- n))))

(defthm finite-field-division-polynomial-table-nat-newest-entry
  (implies (posp n)
           (equal
            (nth n (finite-field-division-polynomial-table-nat n a b))
            (finite-field-division-polynomial-recurrence-step
             n (finite-field-division-polynomial-table-nat (1- n) a b) a b)))
  :hints (("Goal"
           :use (finite-field-division-polynomial-table-nat-newest-at-prefix-length
                 (:instance len-of-finite-field-division-polynomial-table-nat
                            (n (1- n)))
                 one-plus-one-less-when-posp
                 natp-of-one-less-when-posp)
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-division-polynomial-table-newest-entry
  (implies (posp (nfix n))
           (equal
            (nth (nfix n) (finite-field-division-polynomial-table n a b))
            (finite-field-division-polynomial-recurrence-step
             (nfix n)
             (finite-field-division-polynomial-table (1- (nfix n)) a b)
             a b)))
  :hints (("Goal" :in-theory (enable finite-field-division-polynomial-table))))

(local
 (defun finite-field-division-polynomial-table-lookup-induct (k n)
   (if (or (zp n) (equal k n))
       nil
     (finite-field-division-polynomial-table-lookup-induct k (1- n)))))

(defthm finite-field-division-polynomial-table-nat-lookup-stable
  (implies (and (natp k) (natp n) (<= k n))
           (equal (nth k (finite-field-division-polynomial-table-nat n a b))
                  (nth k (finite-field-division-polynomial-table-nat k a b))))
  :hints (("Goal" :induct (finite-field-division-polynomial-table-lookup-induct k n)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(finite-field-division-polynomial-table-nat
                         finite-field-division-polynomial-table-lookup-induct
                         nth-below-of-finite-field-division-polynomial-table-extend
                         len-of-finite-field-division-polynomial-table-nat
                         one-plus-one-less-when-posp
                         natp-of-one-less-when-posp
                         natp posp zp nfix nth)))))

(defthm integerp-when-natp-for-division-polynomial-table
  (implies (natp x) (integerp x)))

(defthm nfix-when-natp-for-division-polynomial-table
  (implies (natp x) (equal (nfix x) x)))

(defthm finite-field-division-polynomial-table-lookup-stable
  (implies (and (natp k) (<= k (nfix n)))
           (equal (nth k (finite-field-division-polynomial-table n a b))
                  (nth k (finite-field-division-polynomial-table k a b))))
  :hints (("Goal"
           :use ((:instance finite-field-division-polynomial-table-nat-lookup-stable
                            (n (nfix n))))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(finite-field-division-polynomial-table nfix
                         natp
                         (:executable-counterpart natp)
                         integerp-when-natp-for-division-polynomial-table
                         nfix-when-natp-for-division-polynomial-table)))))

(defthm finite-field-division-polynomial-table-index-in-range
  (implies (and (natp k) (<= k (nfix n)))
           (< k (len (finite-field-division-polynomial-table n a b)))))

(defthm finite-field-canonical-polynomial-p-of-table-zero-entry
  (finite-field-canonical-polynomial-p
   (nth 0 (finite-field-division-polynomial-table 0 a b)))
  :hints (("Goal"
           :use ((:instance finite-field-canonical-polynomial-p-of-division-polynomial-base
                            (n 0)))
           :in-theory (enable finite-field-division-polynomial-table-base))))

(defthm finite-field-canonical-polynomial-p-of-table-entry
  (implies (and (natp k) (<= k (nfix n)))
           (finite-field-canonical-polynomial-p
            (nth k (finite-field-division-polynomial-table n a b))))
  :hints (("Goal"
           :cases ((zp k))
           :use (finite-field-division-polynomial-table-lookup-stable
                 (:instance finite-field-division-polynomial-table-newest-entry
                            (n k))
                 (:instance finite-field-canonical-polynomial-p-of-division-polynomial-recurrence-step
                            (n k)
                            (table (finite-field-division-polynomial-table (1- k) a b)))
                 finite-field-canonical-polynomial-p-of-table-zero-entry)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(posp zp natp nfix
                         nfix-when-natp-for-division-polynomial-table
                         integerp-when-natp-for-division-polynomial-table
                         natp-of-one-less-when-posp)))))

(defthm finite-field-polynomial-p-of-table-entry
  (implies (and (natp k) (<= k (nfix n)))
           (finite-field-polynomial-p
            (nth k (finite-field-division-polynomial-table n a b))))
  :hints (("Goal"
           :use finite-field-canonical-polynomial-p-of-table-entry
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(finite-field-canonical-polynomial-p
                         finite-field-polynomial-p)))))

(defthm finite-field-division-polynomial-table-of-nfix
  (equal (finite-field-division-polynomial-table (nfix n) a b)
         (finite-field-division-polynomial-table n a b)))

(defthm finite-field-division-polynomial-table-nat-of-coefficient-fixes
  (equal (finite-field-division-polynomial-table-nat
          n (gfield::finite-field-fix a) (gfield::finite-field-fix b))
         (finite-field-division-polynomial-table-nat n a b))
  :hints (("Goal" :induct (finite-field-division-polynomial-table-nat n a b)
           :in-theory (enable finite-field-division-polynomial-table-nat))))

(defthm finite-field-division-polynomial-table-of-coefficient-fixes
  (equal (finite-field-division-polynomial-table
          n (gfield::finite-field-fix a) (gfield::finite-field-fix b))
         (finite-field-division-polynomial-table n a b))
  :hints (("Goal" :in-theory (enable finite-field-division-polynomial-table))))

