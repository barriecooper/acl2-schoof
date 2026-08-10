(in-package "GFIELD")

(include-book "pfield-finite-field-context")

(defun pfield-finite-unrank-list (indices)
  (declare (xargs :guard (true-listp indices)))
  (if (endp indices)
      nil
    (cons (pfield-fix (car indices))
          (pfield-finite-unrank-list (cdr indices)))))

(defun pfield-finite-elements ()
  (declare (xargs :guard t))
  (pfield-finite-unrank-list
   (finite-natural-range-from-count 0 (pfield-modulus))))

(defun pfield-finite-cardinality ()
  (declare (xargs :guard t))
  (len (pfield-finite-elements)))

(deftheory pfield-finite-bijection-instance-theory
  '(posp-of-pfield-modulus-for-finite-bijection
    natp-of-pfield-fix-for-finite-bijection
    pfield-fix-upper-bound-for-finite-bijection
    pfield-fix-of-fix-for-finite-bijection
    pfield-fix-of-unrank-for-finite-bijection
    pfield-fix-inverse-when-bounded pfield-fix-when-natural-and-bounded
    (:definition pfield-finite-unrank-list)
    (:definition pfield-finite-elements)
    (:definition pfield-finite-cardinality)))

(defthm pfield-finite-coverage-from-generic-theory
  (member-equal (pfield-fix x) (pfield-finite-elements))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                member-equal-of-finite-fix-and-finite-elements
                (finite-fix pfield-fix)
                (finite-rank pfield-fix)
                (finite-unrank pfield-fix)
                (finite-bound pfield-modulus)
                (finite-unrank-list pfield-finite-unrank-list)
                (finite-elements pfield-finite-elements))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           (theory 'pfield-finite-bijection-instance-theory)))))

(defthm pfield-finite-no-duplicates-from-generic-theory
  (no-duplicatesp-equal (pfield-finite-elements))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                no-duplicatesp-equal-of-finite-elements
                (finite-fix pfield-fix)
                (finite-rank pfield-fix)
                (finite-unrank pfield-fix)
                (finite-bound pfield-modulus)
                (finite-unrank-list pfield-finite-unrank-list)
                (finite-elements pfield-finite-elements))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           (theory 'pfield-finite-bijection-instance-theory)))))

(defthm pfield-finite-cardinality-from-generic-theory
  (equal (pfield-finite-cardinality) (pfield-modulus))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                finite-cardinality-equals-bound
                (finite-fix pfield-fix)
                (finite-rank pfield-fix)
                (finite-unrank pfield-fix)
                (finite-bound pfield-modulus)
                (finite-unrank-list pfield-finite-unrank-list)
                (finite-elements pfield-finite-elements)
                (finite-cardinality pfield-finite-cardinality))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           (theory 'pfield-finite-bijection-instance-theory)))))

(local
 (defthm pfield-finite-unrank-list-of-bounded-range
   (implies (and (natp start) (natp count)
                 (<= (+ start count) (pfield-modulus)))
            (equal (pfield-finite-unrank-list
                    (finite-natural-range-from-count start count))
                   (finite-natural-range-from-count start count)))
   :hints (("Goal" :induct (finite-natural-range-from-count start count)
            :in-theory (enable pfield-finite-unrank-list
                               finite-natural-range-from-count
                               pfield-fix pfield-element-p
                               pfield::fep pfield::fep-fix)))))

(local
 (defthm finite-natural-range-equals-pfield-natural-range
   (equal (finite-natural-range-from-count start count)
          (pfield-natural-range-from-count start count))
   :hints (("Goal" :induct (finite-natural-range-from-count start count)
            :in-theory (enable finite-natural-range-from-count
                               pfield-natural-range-from-count)))))

(defthm pfield-finite-elements-equals-pfield-elements
  (equal (pfield-finite-elements) (pfield-elements))
  :hints (("Goal"
           :use ((:instance pfield-finite-unrank-list-of-bounded-range
                            (start 0) (count (pfield-modulus))))
           :in-theory (enable pfield-finite-elements pfield-elements))))

(defthm pfield-finite-cardinality-equals-pfield-cardinality
  (equal (pfield-finite-cardinality) (pfield-cardinality))
  :hints (("Goal" :in-theory (enable pfield-finite-cardinality))))

(defthm pfield-finite-coverage-minimal-theory-client
  (member-equal (pfield-fix x) (pfield-finite-elements))
  :rule-classes nil
  :hints (("Goal" :use pfield-finite-coverage-from-generic-theory
           :in-theory (theory 'minimal-theory))))

(defthm pfield-finite-cardinality-minimal-theory-client
  (equal (pfield-finite-cardinality) (pfield-modulus))
  :rule-classes nil
  :hints (("Goal" :use pfield-finite-cardinality-from-generic-theory
           :in-theory (theory 'minimal-theory))))

(verify-guards pfield-finite-unrank-list)
(verify-guards pfield-finite-elements)
(verify-guards pfield-finite-cardinality)
