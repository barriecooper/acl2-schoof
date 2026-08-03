(in-package "GFIELD")

(include-book "finite-bijection")

(defun boolean-finite-fix (x) (if x t nil))
(defun boolean-finite-rank (x) (if x 1 0))
(defun boolean-finite-unrank (k) (equal k 1))
(defun boolean-finite-bound () 2)

(verify-guards boolean-finite-unrank)
(verify-guards boolean-finite-bound)

(defun boolean-finite-unrank-list (indices)
  (declare (xargs :guard (true-listp indices)))
  (if (endp indices)
      nil
    (cons (boolean-finite-unrank (car indices))
          (boolean-finite-unrank-list (cdr indices)))))

(verify-guards boolean-finite-unrank-list)

(defun boolean-finite-elements ()
  (declare (xargs :guard t))
  (boolean-finite-unrank-list
   (finite-natural-range-from-count 0 (boolean-finite-bound))))

(defun boolean-finite-cardinality ()
  (declare (xargs :guard t))
  (len (boolean-finite-elements)))

(defthm boolean-finite-bound-positive (posp (boolean-finite-bound)))
(defthm natp-of-boolean-finite-rank
  (natp (boolean-finite-rank x))
  :rule-classes (:rewrite :type-prescription))
(defthm boolean-finite-rank-upper-bound
  (< (boolean-finite-rank x) (boolean-finite-bound)))
(defthm boolean-finite-fix-idempotent
  (equal (boolean-finite-fix (boolean-finite-fix x))
         (boolean-finite-fix x)))
(defthm boolean-finite-fix-of-unrank
  (equal (boolean-finite-fix (boolean-finite-unrank k))
         (boolean-finite-unrank k)))
(defthm boolean-finite-unrank-of-rank
  (equal (boolean-finite-unrank (boolean-finite-rank x))
         (boolean-finite-fix x)))
(defthm boolean-finite-rank-of-unrank-when-bounded
  (implies (and (natp k) (< k (boolean-finite-bound)))
           (equal (boolean-finite-rank (boolean-finite-unrank k)) k)))

(defthm boolean-finite-unrank-list-definition
  (equal (boolean-finite-unrank-list indices)
         (if (endp indices) nil
           (cons (boolean-finite-unrank (car indices))
                 (boolean-finite-unrank-list (cdr indices))))))
(defthm boolean-finite-elements-definition
  (equal (boolean-finite-elements)
         (boolean-finite-unrank-list
          (finite-natural-range-from-count 0 (boolean-finite-bound)))))
(defthm boolean-finite-cardinality-definition
  (equal (boolean-finite-cardinality) (len (boolean-finite-elements))))

(deftheory boolean-finite-instance-theory
  '(boolean-finite-bound-positive
    natp-of-boolean-finite-rank
    boolean-finite-rank-upper-bound boolean-finite-fix-idempotent
    boolean-finite-fix-of-unrank boolean-finite-unrank-of-rank
    boolean-finite-rank-of-unrank-when-bounded
    (:definition boolean-finite-unrank-list)
    (:definition boolean-finite-elements)
    (:definition boolean-finite-cardinality)))

(defthm boolean-finite-rank-of-fix-minimal-theory-client
  (equal (boolean-finite-rank (boolean-finite-fix x))
         (boolean-finite-rank x))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance finite-rank-of-finite-fix
                              (finite-fix boolean-finite-fix)
                              (finite-rank boolean-finite-rank)
                              (finite-unrank boolean-finite-unrank)
                              (finite-bound boolean-finite-bound))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (theory 'boolean-finite-instance-theory)))))

(defthm boolean-finite-injectivity-minimal-theory-client
  (implies (and (natp i) (< i (boolean-finite-bound))
                (natp j) (< j (boolean-finite-bound)))
           (equal (equal (boolean-finite-unrank i)
                         (boolean-finite-unrank j))
                  (equal i j)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        equal-of-finite-unrank-when-bounded
                        (finite-fix boolean-finite-fix)
                        (finite-rank boolean-finite-rank)
                        (finite-unrank boolean-finite-unrank)
                        (finite-bound boolean-finite-bound))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (theory 'boolean-finite-instance-theory)))))

(defthm boolean-finite-coverage-minimal-theory-client
  (member-equal (boolean-finite-fix x) (boolean-finite-elements))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        member-equal-of-finite-fix-and-finite-elements
                        (finite-fix boolean-finite-fix)
                        (finite-rank boolean-finite-rank)
                        (finite-unrank boolean-finite-unrank)
                        (finite-bound boolean-finite-bound)
                        (finite-unrank-list boolean-finite-unrank-list)
                        (finite-elements boolean-finite-elements))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (theory 'boolean-finite-instance-theory)))))

(defthm boolean-finite-no-duplicates-minimal-theory-client
  (no-duplicatesp-equal (boolean-finite-elements))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        no-duplicatesp-equal-of-finite-elements
                        (finite-fix boolean-finite-fix)
                        (finite-rank boolean-finite-rank)
                        (finite-unrank boolean-finite-unrank)
                        (finite-bound boolean-finite-bound)
                        (finite-unrank-list boolean-finite-unrank-list)
                        (finite-elements boolean-finite-elements))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (theory 'boolean-finite-instance-theory)))))

(defthm boolean-finite-cardinality-minimal-theory-client
  (equal (boolean-finite-cardinality) (boolean-finite-bound))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance finite-cardinality-equals-bound
                              (finite-fix boolean-finite-fix)
                              (finite-rank boolean-finite-rank)
                              (finite-unrank boolean-finite-unrank)
                              (finite-bound boolean-finite-bound)
                              (finite-unrank-list boolean-finite-unrank-list)
                              (finite-elements boolean-finite-elements)
                              (finite-cardinality boolean-finite-cardinality))
           :in-theory (union-theories (theory 'minimal-theory)
                                      (theory 'boolean-finite-instance-theory)))))

(defthm boolean-finite-execution-regressions
  (and (equal (boolean-finite-elements) '(nil t))
       (equal (boolean-finite-cardinality) 2)
       (equal (boolean-finite-fix 'malformed) t)
       (equal (boolean-finite-rank nil) 0)
       (equal (boolean-finite-rank t) 1))
  :rule-classes nil)

(verify-guards boolean-finite-elements)
(verify-guards boolean-finite-cardinality)
