(in-package "GPOLY")

(include-book "division-polynomial-sequence")

(defthm division-polynomial-sequence-shape-minimal-theory-client
  (implies (finite-field-division-polynomial-sequence-p n table a b)
           (and (true-listp table)
                (equal (len table) (+ 1 (nfix n)))
                (implies (and (natp k) (<= k (nfix n)))
                         (equal
                          (nth k table)
                          (finite-field-division-polynomial-recurrence-step
                           k table a b)))))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-division-polynomial-sequence-p-exact-length
                 finite-field-division-polynomial-sequence-p-recurrence)
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-evaluator-boundary-minimal-theory-client
  (and (equal (finite-field-division-polynomial (nfix n) a b)
              (finite-field-division-polynomial n a b))
       (equal (finite-field-division-polynomial
               n (gfield::finite-field-fix a) (gfield::finite-field-fix b))
              (finite-field-division-polynomial n a b))
       (finite-field-canonical-polynomial-p
        (finite-field-division-polynomial n a b))
       (finite-field-polynomial-p
        (finite-field-division-polynomial n a b)))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-division-polynomial-of-nfix
                 finite-field-division-polynomial-of-coefficient-fixes
                 finite-field-canonical-polynomial-p-of-division-polynomial
                 finite-field-polynomial-p-of-division-polynomial)
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-evaluator-base-minimal-theory-client
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
  :rule-classes nil
  :hints (("Goal"
           :use finite-field-division-polynomial-evaluator-base-equations
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-evaluator-recurrences-minimal-theory-client
  (and (implies (and (natp m) (<= 2 m) (evenp m))
                (equal (finite-field-division-polynomial (+ 1 (* 2 m)) a b)
                       (finite-field-poly-sub
                        (finite-field-poly-mul
                         (finite-field-poly-square (finite-field-division-polynomial-c a b))
                         (finite-field-poly-mul
                          (finite-field-division-polynomial (+ m 2) a b)
                          (finite-field-poly-cube (finite-field-division-polynomial m a b))))
                        (finite-field-poly-mul
                         (finite-field-division-polynomial (- m 1) a b)
                         (finite-field-poly-cube
                          (finite-field-division-polynomial (+ m 1) a b))))))
       (implies (and (natp m) (<= 2 m) (oddp m))
                (equal (finite-field-division-polynomial (+ 1 (* 2 m)) a b)
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
       (implies (and (natp m) (<= 3 m))
                (equal (finite-field-division-polynomial (* 2 m) a b)
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
                           (finite-field-division-polynomial (+ m 1) a b))))))))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-division-polynomial-odd-even-half
                 finite-field-division-polynomial-odd-odd-half
                 finite-field-division-polynomial-even)
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-generated-entry-recurrence-minimal-theory-client
  (implies (and (natp k) (<= k (nfix n)))
           (equal
            (nth k (finite-field-division-polynomial-table n a b))
            (finite-field-division-polynomial-recurrence-step
             k (finite-field-division-polynomial-table n a b) a b)))
  :rule-classes nil
  :hints (("Goal"
           :use finite-field-division-polynomial-table-entry-recurrence
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-generated-sequence-minimal-theory-client
  (finite-field-division-polynomial-sequence-p
   n (finite-field-division-polynomial-table n a b) a b)
  :rule-classes nil
  :hints (("Goal"
           :use finite-field-division-polynomial-table-satisfies-sequence-p
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-specified-entry-agreement-minimal-theory-client
  (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                (natp k) (<= k (nfix n)))
           (equal (nth k table)
                  (finite-field-division-polynomial k a b)))
  :rule-classes nil
  :hints (("Goal"
           :use finite-field-division-polynomial-specified-table-entry-agreement
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-sequence-correspondence-minimal-theory-client
  (and
   (implies (and (finite-field-division-polynomial-sequence-p n table a b)
                 (natp k) (<= k (nfix n)))
            (equal (nth k table)
                   (finite-field-division-polynomial k a b)))
   (implies (finite-field-division-polynomial-sequence-p n table a b)
            (equal (nth (nfix n) table)
                   (finite-field-division-polynomial n a b))))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-division-polynomial-sequence-p-entry-correspondence
                 finite-field-division-polynomial-sequence-p-final-entry-correspondence)
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-generated-correspondence-minimal-theory-client
  (and (finite-field-division-polynomial-sequence-p
        n (finite-field-division-polynomial-table n a b) a b)
       (equal
        (nth (nfix n) (finite-field-division-polynomial-table n a b))
        (finite-field-division-polynomial n a b)))
  :rule-classes nil
  :hints (("Goal"
           :use finite-field-division-polynomial-generated-table-correspondence
           :in-theory (theory 'minimal-theory))))
