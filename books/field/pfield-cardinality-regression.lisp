(in-package "GFIELD")

(include-book "pfield-cardinality")
(include-book "examples/f11")

(defun f7-elements ()
  (declare (xargs :guard t))
  (pfield-natural-range-from-count 0 7))

(defun f7-cardinality ()
  (declare (xargs :guard t))
  (len (f7-elements)))

(defthm f7-elements-execution-regression
  (equal (f7-elements) '(0 1 2 3 4 5 6))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f7-elements
                                      pfield-natural-range-from-count))))

(defthm no-duplicatesp-equal-of-f7-elements
  (no-duplicatesp-equal (f7-elements))
  :hints (("Goal" :in-theory (enable f7-elements))))

(defthm f7-element-p-of-member-equal-of-f7-elements
  (implies (member-equal x (f7-elements))
           (f7-element-p x))
  :hints (("Goal"
           :by (:functional-instance
                pfield-element-p-of-member-equal-of-pfield-elements
                (pfield-modulus (lambda () 7))
                (pfield-element-p f7-element-p)
                (pfield-elements f7-elements))
           :in-theory (enable dm::primep))))

(defthm member-equal-of-f7-fix-and-f7-elements
  (member-equal (f7-fix x) (f7-elements))
  :hints (("Goal"
           :by (:functional-instance
                member-equal-of-pfield-fix-and-pfield-elements
                (pfield-modulus (lambda () 7))
                (pfield-element-p f7-element-p)
                (pfield-fix f7-fix)
                (pfield-elements f7-elements))
           :in-theory (enable dm::primep))))

(defthm len-of-f7-elements
  (equal (len (f7-elements)) 7)
  :hints (("Goal" :in-theory (enable f7-elements))))

(defthm f7-cardinality-equals-seven
  (equal (f7-cardinality) 7)
  :hints (("Goal" :in-theory (enable f7-cardinality))))

(defun f11-elements ()
  (declare (xargs :guard t))
  (pfield-natural-range-from-count 0 11))

(defun f11-cardinality ()
  (declare (xargs :guard t))
  (len (f11-elements)))

(defthm f11-elements-execution-regression
  (equal (f11-elements) '(0 1 2 3 4 5 6 7 8 9 10))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable f11-elements
                                      pfield-natural-range-from-count))))

(defthm no-duplicatesp-equal-of-f11-elements
  (no-duplicatesp-equal (f11-elements))
  :hints (("Goal" :in-theory (enable f11-elements))))

(defthm f11-element-p-of-member-equal-of-f11-elements
  (implies (member-equal x (f11-elements))
           (f11-element-p x))
  :hints (("Goal"
           :by (:functional-instance
                pfield-element-p-of-member-equal-of-pfield-elements
                (pfield-modulus (lambda () 11))
                (pfield-element-p f11-element-p)
                (pfield-elements f11-elements))
           :in-theory (enable dm::primep))))

(defthm member-equal-of-f11-fix-and-f11-elements
  (member-equal (f11-fix x) (f11-elements))
  :hints (("Goal"
           :by (:functional-instance
                member-equal-of-pfield-fix-and-pfield-elements
                (pfield-modulus (lambda () 11))
                (pfield-element-p f11-element-p)
                (pfield-fix f11-fix)
                (pfield-elements f11-elements))
           :in-theory (enable dm::primep))))

(defthm len-of-f11-elements
  (equal (len (f11-elements)) 11)
  :hints (("Goal" :in-theory (enable f11-elements))))

(defthm f11-cardinality-equals-eleven
  (equal (f11-cardinality) 11)
  :hints (("Goal" :in-theory (enable f11-cardinality))))

(defthm pfield-cardinality-coverage-minimal-theory-client
  (member-equal (pfield-fix x) (pfield-elements))
  :rule-classes nil
  :hints (("Goal"
           :use member-equal-of-pfield-fix-and-pfield-elements
           :in-theory (theory 'minimal-theory))))

(defthm pfield-cardinality-modulus-minimal-theory-client
  (equal (pfield-cardinality) (pfield-modulus))
  :rule-classes nil
  :hints (("Goal"
           :use pfield-cardinality-equals-modulus
           :in-theory (theory 'minimal-theory))))

(defthm fixer-aware-cardinality-execution-regressions
  (and (member-equal (f7-fix 'malformed) (f7-elements))
       (member-equal (f7-fix -1) (f7-elements))
       (member-equal (f7-fix 7) (f7-elements))
       (member-equal (f7-fix 15) (f7-elements))
       (member-equal (f11-fix 'malformed) (f11-elements))
       (member-equal (f11-fix -1) (f11-elements))
       (member-equal (f11-fix 11) (f11-elements))
       (member-equal (f11-fix 23) (f11-elements)))
  :rule-classes nil)

(verify-guards f7-elements)
(verify-guards f7-cardinality)
(verify-guards f11-elements)
(verify-guards f11-cardinality)
