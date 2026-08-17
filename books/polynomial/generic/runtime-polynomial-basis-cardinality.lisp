(in-package "GPOLY")

(include-book "runtime-polynomial-basis")
(include-book "../../algebra/finite-bijection")

; Descriptor threading prevents a literal functional instance of the nullary-
; bound finite-bijection context.  These transparent wrappers reuse its neutral
; natural range and follow its unrank-map construction exactly.
(defun runtime-polynomial-basis-unrank-list (indices descriptor)
  (declare (xargs :guard (true-listp indices)))
  (if (endp indices) nil
    (cons (runtime-polynomial-basis-unrank (car indices) descriptor)
          (runtime-polynomial-basis-unrank-list (cdr indices) descriptor))))

(defun runtime-polynomial-basis-elements (descriptor)
  (declare (xargs :guard t))
  (runtime-polynomial-basis-unrank-list
   (gfield::finite-natural-range-from-count
    0 (runtime-polynomial-basis-bound descriptor))
   descriptor))

(defun runtime-polynomial-basis-cardinality (descriptor)
  (declare (xargs :guard t))
  (len (runtime-polynomial-basis-elements descriptor)))

(defthm true-listp-of-runtime-polynomial-basis-unrank-list
  (true-listp (runtime-polynomial-basis-unrank-list indices descriptor))
  :rule-classes :type-prescription)

(defthm len-of-runtime-polynomial-basis-unrank-list
  (equal (len (runtime-polynomial-basis-unrank-list indices descriptor))
         (len indices)))

(defthm member-equal-of-runtime-polynomial-basis-unrank-list
  (implies (member-equal index indices)
           (member-equal
            (runtime-polynomial-basis-unrank index descriptor)
            (runtime-polynomial-basis-unrank-list indices descriptor))))

(local
 (defthm member-equal-of-cons-for-runtime-polynomial-basis
   (iff (member-equal x (cons a rest))
        (or (equal x a) (member-equal x rest)))
   :hints (("Goal" :in-theory (enable member-equal)))))

(local
 (defthm no-duplicatesp-equal-of-cons-for-runtime-polynomial-basis
   (equal (no-duplicatesp-equal (cons a rest))
          (and (not (member-equal a rest))
               (no-duplicatesp-equal rest)))
   :hints (("Goal" :in-theory (enable no-duplicatesp-equal)))))

(defthm runtime-polynomial-basis-fix-when-member-equal-of-unrank-list
  (implies
   (member-equal value
                 (runtime-polynomial-basis-unrank-list indices descriptor))
   (equal (runtime-polynomial-basis-fix value descriptor) value))
  :hints (("Goal"
           :induct (runtime-polynomial-basis-unrank-list indices descriptor)
           :in-theory
           (union-theories '(runtime-polynomial-basis-unrank-list member-equal
                             runtime-polynomial-basis-fix-of-unrank
                             member-equal-of-cons-for-runtime-polynomial-basis)
                           (theory 'minimal-theory)))
          (and stable-under-simplificationp
               '(:cases ((equal value
                                (runtime-polynomial-basis-unrank
                                 (car indices) descriptor)))
                 :use ((:instance runtime-polynomial-basis-fix-of-unrank
                                  (k (car indices))))
                 :in-theory
                 (union-theories
                  '(runtime-polynomial-basis-unrank-list member-equal
                    member-equal-of-cons-for-runtime-polynomial-basis)
                  (theory 'minimal-theory))))))

(local
 (defun runtime-polynomial-basis-bounded-index-list-p (indices descriptor)
   (if (endp indices) t
     (and (natp (car indices))
          (< (car indices) (runtime-polynomial-basis-bound descriptor))
          (runtime-polynomial-basis-bounded-index-list-p
           (cdr indices) descriptor)))))

(local
 (defthm runtime-polynomial-basis-bounded-index-list-p-of-range-lemma
   (implies
    (and (natp start) (natp count)
         (<= (+ start count) (runtime-polynomial-basis-bound descriptor)))
    (runtime-polynomial-basis-bounded-index-list-p
     (gfield::finite-natural-range-from-count start count) descriptor))
   :hints (("Goal"
            :induct (gfield::finite-natural-range-from-count start count)
            :in-theory (enable
                        runtime-polynomial-basis-bounded-index-list-p
                        gfield::finite-natural-range-from-count)))))

(local
 (defthm runtime-polynomial-basis-bounded-index-list-p-of-range
   (runtime-polynomial-basis-bounded-index-list-p
    (gfield::finite-natural-range-from-count
     0 (runtime-polynomial-basis-bound descriptor)) descriptor)
   :hints (("Goal"
            :use ((:instance
                   runtime-polynomial-basis-bounded-index-list-p-of-range-lemma
                   (start 0)
                   (count (runtime-polynomial-basis-bound descriptor)))
                  (:instance posp-of-runtime-polynomial-basis-bound))
            :in-theory
            (union-theories '(posp natp)
                            (theory 'minimal-theory))))))

(local
 (defthm runtime-polynomial-basis-unrank-injective-when-bounded
   (implies
    (and (natp i) (< i (runtime-polynomial-basis-bound descriptor))
         (natp j) (< j (runtime-polynomial-basis-bound descriptor)))
    (equal (equal (runtime-polynomial-basis-unrank i descriptor)
                  (runtime-polynomial-basis-unrank j descriptor))
           (equal i j)))
   :hints (("Goal"
            :use ((:instance
                   runtime-polynomial-basis-rank-of-unrank-when-bounded (k i))
                  (:instance
                   runtime-polynomial-basis-rank-of-unrank-when-bounded (k j))
                  (:instance
                   (:theorem
                    (implies (equal a b)
                             (equal (runtime-polynomial-basis-rank a descriptor)
                                    (runtime-polynomial-basis-rank b descriptor))))
                   (a (runtime-polynomial-basis-unrank i descriptor))
                   (b (runtime-polynomial-basis-unrank j descriptor))))
            :in-theory (union-theories '(natp) (theory 'minimal-theory))))))

(local
 (defthm member-index-when-member-runtime-polynomial-basis-unrank-list
   (implies
    (and (natp index)
         (< index (runtime-polynomial-basis-bound descriptor))
         (runtime-polynomial-basis-bounded-index-list-p indices descriptor)
         (member-equal
          (runtime-polynomial-basis-unrank index descriptor)
          (runtime-polynomial-basis-unrank-list indices descriptor)))
    (member-equal index indices))
   :hints (("Goal"
            :induct (runtime-polynomial-basis-unrank-list indices descriptor)
            :in-theory
            (union-theories
             '(runtime-polynomial-basis-unrank-list
               runtime-polynomial-basis-bounded-index-list-p
               runtime-polynomial-basis-unrank-injective-when-bounded
               member-equal member-equal-of-cons-for-runtime-polynomial-basis
               natp)
             (theory 'minimal-theory))))))

(local
 (defthm no-duplicatesp-equal-of-runtime-polynomial-basis-unrank-list
   (implies
    (and (no-duplicatesp-equal indices)
         (runtime-polynomial-basis-bounded-index-list-p indices descriptor))
    (no-duplicatesp-equal
     (runtime-polynomial-basis-unrank-list indices descriptor)))
   :hints (("Goal"
            :induct (runtime-polynomial-basis-unrank-list indices descriptor)
            :in-theory
            (union-theories
             '(runtime-polynomial-basis-unrank-list
               runtime-polynomial-basis-bounded-index-list-p
               member-index-when-member-runtime-polynomial-basis-unrank-list
               no-duplicatesp-equal-of-cons-for-runtime-polynomial-basis
               no-duplicatesp-equal member-equal natp)
             (theory 'minimal-theory)))
           (and stable-under-simplificationp
                '(:use
                  ((:instance
                    member-index-when-member-runtime-polynomial-basis-unrank-list
                    (index (car indices))
                    (indices (cdr indices))))
                  :in-theory
                  (union-theories '(natp no-duplicatesp-equal)
                                  (theory 'minimal-theory)))))))

(defthm true-listp-of-runtime-polynomial-basis-elements
  (true-listp (runtime-polynomial-basis-elements descriptor))
  :rule-classes :type-prescription)

(defthm runtime-polynomial-basis-fix-when-member-equal-of-elements
  (implies (member-equal x (runtime-polynomial-basis-elements descriptor))
           (equal (runtime-polynomial-basis-fix x descriptor) x))
  :hints (("Goal" :in-theory (enable runtime-polynomial-basis-elements))))

(defthm member-equal-of-runtime-polynomial-basis-fix-and-elements
  (member-equal (runtime-polynomial-basis-fix x descriptor)
                (runtime-polynomial-basis-elements descriptor))
  :hints
  (("Goal"
    :use ((:instance gfield::member-equal-of-finite-natural-range-from-count
                     (x (runtime-polynomial-basis-rank x descriptor))
                     (start 0)
                     (count (runtime-polynomial-basis-bound descriptor)))
          (:instance member-equal-of-runtime-polynomial-basis-unrank-list
                     (index (runtime-polynomial-basis-rank x descriptor))
                     (indices
                      (gfield::finite-natural-range-from-count
                       0 (runtime-polynomial-basis-bound descriptor))))
          (:instance runtime-polynomial-basis-unrank-of-rank)
          (:instance runtime-polynomial-basis-rank-bound)
          (:instance posp-of-runtime-polynomial-basis-bound)
          (:instance natp-of-runtime-p-rank
                     (coefficients
                      (runtime-polynomial-basis-vector x descriptor))
                     (p (runtime-polynomial-basis-p descriptor))))
    :in-theory
    (union-theories
     '(runtime-polynomial-basis-elements runtime-polynomial-basis-rank
       natp posp nfix)
     (theory 'minimal-theory)))))

(defthm no-duplicatesp-equal-of-runtime-polynomial-basis-elements
  (no-duplicatesp-equal (runtime-polynomial-basis-elements descriptor))
  :hints (("Goal"
           :use ((:instance
                  runtime-polynomial-basis-bounded-index-list-p-of-range)
                 (:instance
                  gfield::no-duplicatesp-equal-of-finite-natural-range-from-count
                  (start 0)
                  (count (runtime-polynomial-basis-bound descriptor)))
                 (:instance
                  no-duplicatesp-equal-of-runtime-polynomial-basis-unrank-list
                  (indices
                   (gfield::finite-natural-range-from-count
                    0 (runtime-polynomial-basis-bound descriptor)))))
           :in-theory (enable runtime-polynomial-basis-elements))))

(defthm len-of-runtime-polynomial-basis-elements
  (equal (len (runtime-polynomial-basis-elements descriptor))
         (runtime-polynomial-basis-bound descriptor))
  :hints (("Goal"
           :use ((:instance
                  gfield::len-of-finite-natural-range-from-count
                  (start 0)
                  (count (runtime-polynomial-basis-bound descriptor)))
                 (:instance posp-of-runtime-polynomial-basis-bound))
           :in-theory
           (union-theories
            '(runtime-polynomial-basis-elements
              len-of-runtime-polynomial-basis-unrank-list posp natp nfix)
            (theory 'minimal-theory)))))

(defthm runtime-polynomial-basis-cardinality-equals-bound
  (equal (runtime-polynomial-basis-cardinality descriptor)
         (runtime-polynomial-basis-bound descriptor))
  :hints (("Goal" :in-theory (enable runtime-polynomial-basis-cardinality))))

(defthm runtime-polynomial-basis-cardinality-is-p-to-the-m
  (equal (runtime-polynomial-basis-cardinality descriptor)
         (expt (runtime-polynomial-basis-p descriptor)
               (runtime-polynomial-basis-degree descriptor)))
  :hints (("Goal"
           :use (runtime-polynomial-basis-cardinality-equals-bound
                 runtime-polynomial-basis-bound-is-p-to-the-m))))

(verify-guards runtime-polynomial-basis-unrank-list)
(verify-guards runtime-polynomial-basis-elements)
(verify-guards runtime-polynomial-basis-cardinality)
