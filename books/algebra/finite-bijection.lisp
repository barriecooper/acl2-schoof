(in-package "GFIELD")

; A field-independent constructive presentation of a finite carrier.  The
; constrained functions are logical; the range and carrier below are ordinary
; transparent executable definitions.
(encapsulate
 (((finite-fix *) => *)
  ((finite-rank *) => *)
  ((finite-unrank *) => *)
  ((finite-bound) => *))

 (local (defun finite-fix (x) (if x t nil)))
 (local (defun finite-rank (x) (if x 1 0)))
 (local (defun finite-unrank (k) (equal k 1)))
 (local (defun finite-bound () 2))

 (defthm posp-of-finite-bound
   (posp (finite-bound)))

 (defthm natp-of-finite-rank
   (natp (finite-rank x))
   :rule-classes :type-prescription)

 (defthm finite-rank-upper-bound
   (< (finite-rank x) (finite-bound))
   :rule-classes (:rewrite :linear))

 (defthm finite-fix-idempotent
   (equal (finite-fix (finite-fix x))
          (finite-fix x)))

 (defthm finite-fix-of-finite-unrank
   (equal (finite-fix (finite-unrank k))
          (finite-unrank k)))

 (defthm finite-unrank-of-finite-rank
   (equal (finite-unrank (finite-rank x))
          (finite-fix x)))

 (defthm finite-rank-of-finite-unrank-when-bounded
   (implies (and (natp k)
                 (< k (finite-bound)))
            (equal (finite-rank (finite-unrank k)) k))))

(defthm finite-rank-of-finite-fix
  (equal (finite-rank (finite-fix x))
         (finite-rank x))
  :hints (("Goal"
           :use ((:instance finite-unrank-of-finite-rank)
                 (:instance finite-rank-of-finite-unrank-when-bounded
                            (k (finite-rank x))))
           :in-theory (disable finite-unrank-of-finite-rank
                               finite-rank-of-finite-unrank-when-bounded))))

(defthm equal-of-finite-unrank-when-bounded
  (implies (and (natp i) (< i (finite-bound))
                (natp j) (< j (finite-bound)))
           (equal (equal (finite-unrank i) (finite-unrank j))
                  (equal i j)))
  :hints (("Goal"
           :use ((:instance finite-rank-of-finite-unrank-when-bounded (k i))
                 (:instance finite-rank-of-finite-unrank-when-bounded (k j))
                 (:instance
                  (:theorem
                   (implies (equal a b)
                            (equal (finite-rank a) (finite-rank b))))
                  (a (finite-unrank i))
                  (b (finite-unrank j)))))))

(defun finite-natural-range-from-count (start count)
  (declare (xargs :guard (and (natp start) (natp count))
                  :measure (nfix count)))
  (if (zp (nfix count))
      nil
    (cons (nfix start)
          (finite-natural-range-from-count (+ 1 (nfix start))
                                           (1- (nfix count))))))

(defthm true-listp-of-finite-natural-range-from-count
  (true-listp (finite-natural-range-from-count start count))
  :rule-classes :type-prescription)

(defthm member-equal-of-finite-natural-range-from-count
  (iff (member-equal x (finite-natural-range-from-count start count))
       (and (natp x)
            (<= (nfix start) x)
            (< x (+ (nfix start) (nfix count)))))
  :hints (("Goal" :induct (finite-natural-range-from-count start count)
           :in-theory (enable finite-natural-range-from-count))))

(defthm no-duplicatesp-equal-of-finite-natural-range-from-count
  (no-duplicatesp-equal (finite-natural-range-from-count start count))
  :hints (("Goal" :induct (finite-natural-range-from-count start count)
           :in-theory (enable finite-natural-range-from-count))))

(defthm len-of-finite-natural-range-from-count
  (equal (len (finite-natural-range-from-count start count))
         (nfix count))
  :hints (("Goal" :induct (finite-natural-range-from-count start count)
           :in-theory (enable finite-natural-range-from-count))))

(verify-guards finite-natural-range-from-count)

(defun finite-unrank-list (indices)
  (declare (xargs :guard (true-listp indices)))
  (if (endp indices)
      nil
    (cons (finite-unrank (car indices))
          (finite-unrank-list (cdr indices)))))

(defthm true-listp-of-finite-unrank-list
  (true-listp (finite-unrank-list indices))
  :rule-classes :type-prescription)

(defthm len-of-finite-unrank-list
  (equal (len (finite-unrank-list indices)) (len indices)))

(defthm member-equal-of-finite-unrank-list
  (implies (member-equal index indices)
           (member-equal (finite-unrank index)
                         (finite-unrank-list indices))))

(defthm finite-fix-when-member-equal-of-finite-unrank-list
  (implies (member-equal value (finite-unrank-list indices))
           (equal (finite-fix value) value))
  :hints (("Goal" :induct (finite-unrank-list indices)
           :in-theory (enable finite-unrank-list))))

(local
 (defun finite-bounded-index-list-p (indices)
   (if (endp indices)
       t
     (and (natp (car indices))
          (< (car indices) (finite-bound))
          (finite-bounded-index-list-p (cdr indices))))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm finite-bounded-index-list-p-of-range-lemma
   (implies (and (natp start)
                 (natp count)
                 (<= (+ start count) (finite-bound)))
            (finite-bounded-index-list-p
             (finite-natural-range-from-count start count)))
   :hints (("Goal" :induct (finite-natural-range-from-count start count)
            :in-theory (enable finite-bounded-index-list-p
                               finite-natural-range-from-count)))))

(local
 (defthm finite-bounded-index-list-p-of-range
   (finite-bounded-index-list-p
    (finite-natural-range-from-count 0 (finite-bound)))
   :hints (("Goal"
            :use ((:instance finite-bounded-index-list-p-of-range-lemma
                             (start 0) (count (finite-bound))))
            :in-theory (disable finite-bounded-index-list-p)))))

(local
 (defthm member-index-when-member-finite-unrank-list
   (implies (and (natp index) (< index (finite-bound))
                 (finite-bounded-index-list-p indices)
                 (member-equal (finite-unrank index)
                               (finite-unrank-list indices)))
            (member-equal index indices))
   :hints (("Goal" :induct (finite-unrank-list indices)
            :in-theory (enable finite-unrank-list
                               finite-bounded-index-list-p)))))

(local
 (defthm no-duplicatesp-equal-of-finite-unrank-list
   (implies (and (no-duplicatesp-equal indices)
                 (finite-bounded-index-list-p indices))
            (no-duplicatesp-equal (finite-unrank-list indices)))
   :hints (("Goal" :induct (finite-unrank-list indices)
            :in-theory (enable finite-unrank-list
                               finite-bounded-index-list-p)))))

(defun finite-elements ()
  (declare (xargs :guard t))
  (finite-unrank-list
   (finite-natural-range-from-count 0 (finite-bound))))

(defun finite-cardinality ()
  (declare (xargs :guard t))
  (len (finite-elements)))

(defthm true-listp-of-finite-elements
  (true-listp (finite-elements))
  :rule-classes :type-prescription)

(defthm finite-fix-when-member-equal-of-finite-elements
  (implies (member-equal x (finite-elements))
           (equal (finite-fix x) x))
  :hints (("Goal" :in-theory (enable finite-elements))))

(defthm member-equal-of-finite-fix-and-finite-elements
  (member-equal (finite-fix x) (finite-elements))
  :hints (("Goal"
           :use ((:instance member-equal-of-finite-natural-range-from-count
                            (x (finite-rank x)) (start 0)
                            (count (finite-bound)))
                 (:instance member-equal-of-finite-unrank-list
                            (index (finite-rank x))
                            (indices (finite-natural-range-from-count
                                      0 (finite-bound)))))
           :in-theory (enable finite-elements))))

(defthm no-duplicatesp-equal-of-finite-elements
  (no-duplicatesp-equal (finite-elements))
  :hints (("Goal" :in-theory (enable finite-elements))))

(defthm len-of-finite-elements
  (equal (len (finite-elements)) (finite-bound))
  :hints (("Goal" :in-theory (enable finite-elements))))

(defthm finite-cardinality-equals-len-of-finite-elements
  (equal (finite-cardinality) (len (finite-elements)))
  :hints (("Goal" :in-theory (enable finite-cardinality))))

(defthm finite-cardinality-equals-bound
  (equal (finite-cardinality) (finite-bound))
  :hints (("Goal" :use len-of-finite-elements
           :in-theory (enable finite-cardinality))))

(defthm posp-of-finite-cardinality
  (posp (finite-cardinality))
  :hints (("Goal" :use (finite-cardinality-equals-bound
                         posp-of-finite-bound))))

(verify-guards finite-unrank-list)
(verify-guards finite-elements)
(verify-guards finite-cardinality)
