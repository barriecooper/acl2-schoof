(in-package "GPOLY")

(include-book "f7x2-cardinality")

(defthm f7x2-bijection-minimal-theory-client
  (equal (f7x2-unrank (f7x2-rank x))
         (f7x2-fix x))
  :rule-classes nil
  :hints (("Goal" :use f7x2-unrank-of-f7x2-rank
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-cardinality-minimal-theory-client
  (equal (f7x2-cardinality) 49)
  :rule-classes nil
  :hints (("Goal" :use f7x2-cardinality-equals-49
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-coverage-minimal-theory-client
  (member-equal (f7x2-fix x) (f7x2-elements))
  :rule-classes nil
  :hints (("Goal" :use member-equal-of-f7x2-fix-and-f7x2-elements
           :in-theory (theory 'minimal-theory))))

(defthm f7x2-rank-execution-regressions
  (and (equal (f7x2-rank (f7x2-zero)) 0)
       (equal (f7x2-rank (f7x2-one)) 1)
       (equal (f7x2-rank '(0 1)) 7)
       (equal (f7x2-rank '(3 4)) 31))
  :rule-classes nil)

(defthm f7x2-unrank-execution-regressions
  (and (equal (f7x2-unrank 0) nil)
       (equal (f7x2-unrank 1) '(1))
       (equal (f7x2-unrank 7) '(0 1))
       (equal (f7x2-unrank 48) '(6 6))
       (equal (f7x2-unrank 'malformed) nil)
       (equal (f7x2-unrank -1) nil)
       (equal (f7x2-unrank 49) nil)
       (equal (f7x2-unrank 1000)
              (f7x2-unrank (mod 1000 49))))
  :rule-classes nil)

(defthm f7x2-carrier-execution-regressions
  (and (equal (len (f7x2-elements)) 49)
       (equal (f7x2-cardinality) 49)
       (member-equal (f7x2-fix 'malformed) (f7x2-elements))
       (member-equal (f7x2-fix '(1 2 . bad)) (f7x2-elements))
       (member-equal (f7x2-fix '(8 -1)) (f7x2-elements))
       (member-equal (f7x2-fix '(0 0 0 1)) (f7x2-elements)))
  :rule-classes nil)
