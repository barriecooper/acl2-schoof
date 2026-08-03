(in-package "GPOLY")

(include-book "f7x2-cardinality")
(include-book "../../algebra/finite-bijection")

(defun f7x2-finite-elements ()
  (declare (xargs :guard t))
  (f7x2-unrank-list
   (gfield::finite-natural-range-from-count 0 49)))

(defun f7x2-finite-cardinality ()
  (declare (xargs :guard t))
  (len (f7x2-finite-elements)))

(defthm posp-of-49-for-finite-bijection (posp 49))

(defthm natp-of-f7x2-rank-for-finite-bijection
  (natp (f7x2-rank x))
  :hints (("Goal" :use natp-of-f7x2-rank)))

(deftheory f7x2-finite-bijection-instance-theory
  '(posp-of-49-for-finite-bijection
    natp-of-f7x2-rank-for-finite-bijection
    f7x2-rank-upper-bound f7x2-fix-idempotent
    f7x2-fix-of-f7x2-unrank f7x2-unrank-of-f7x2-rank
    f7x2-rank-of-f7x2-unrank-when-below-49
    (:definition f7x2-unrank-list)
    (:definition f7x2-finite-elements)
    (:definition f7x2-finite-cardinality)))

(defthm f7x2-finite-coverage-from-generic-theory
  (member-equal (f7x2-fix x) (f7x2-finite-elements))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                gfield::member-equal-of-finite-fix-and-finite-elements
                (gfield::finite-fix f7x2-fix)
                (gfield::finite-rank f7x2-rank)
                (gfield::finite-unrank f7x2-unrank)
                (gfield::finite-bound (lambda () 49))
                (gfield::finite-unrank-list f7x2-unrank-list)
                (gfield::finite-elements f7x2-finite-elements))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           (theory 'f7x2-finite-bijection-instance-theory)))))

(defthm f7x2-finite-no-duplicates-from-generic-theory
  (no-duplicatesp-equal (f7x2-finite-elements))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                gfield::no-duplicatesp-equal-of-finite-elements
                (gfield::finite-fix f7x2-fix)
                (gfield::finite-rank f7x2-rank)
                (gfield::finite-unrank f7x2-unrank)
                (gfield::finite-bound (lambda () 49))
                (gfield::finite-unrank-list f7x2-unrank-list)
                (gfield::finite-elements f7x2-finite-elements))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           (theory 'f7x2-finite-bijection-instance-theory)))))

(defthm f7x2-finite-cardinality-from-generic-theory
  (equal (f7x2-finite-cardinality) 49)
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance gfield::finite-cardinality-equals-bound
                (gfield::finite-fix f7x2-fix)
                (gfield::finite-rank f7x2-rank)
                (gfield::finite-unrank f7x2-unrank)
                (gfield::finite-bound (lambda () 49))
                (gfield::finite-unrank-list f7x2-unrank-list)
                (gfield::finite-elements f7x2-finite-elements)
                (gfield::finite-cardinality f7x2-finite-cardinality))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           (theory 'f7x2-finite-bijection-instance-theory)))))

(local
 (defthm finite-natural-range-equals-pfield-natural-range-for-f7x2
   (equal (gfield::finite-natural-range-from-count start count)
          (gfield::pfield-natural-range-from-count start count))
   :hints (("Goal"
            :induct (gfield::finite-natural-range-from-count start count)
            :in-theory
            (enable gfield::finite-natural-range-from-count
                    gfield::pfield-natural-range-from-count)))))

(defthm f7x2-finite-elements-equals-f7x2-elements
  (equal (f7x2-finite-elements) (f7x2-elements))
  :hints (("Goal" :in-theory (enable f7x2-finite-elements f7x2-elements))))

(defthm f7x2-finite-cardinality-equals-f7x2-cardinality
  (equal (f7x2-finite-cardinality) (f7x2-cardinality))
  :hints (("Goal" :in-theory (enable f7x2-finite-cardinality))))

(defthm f7x2-finite-coverage-minimal-theory-client
  (member-equal (f7x2-fix x) (f7x2-finite-elements))
  :rule-classes nil
  :hints (("Goal" :use f7x2-finite-coverage-from-generic-theory
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-finite-cardinality-minimal-theory-client
  (equal (f7x2-finite-cardinality) 49)
  :rule-classes nil
  :hints (("Goal" :use f7x2-finite-cardinality-from-generic-theory
           :in-theory (theory 'minimal-theory))))

(verify-guards f7x2-finite-elements)
(verify-guards f7x2-finite-cardinality)
