(in-package "GPOLY")

(include-book "division-polynomial-table")

(defthm division-polynomial-table-extension-minimal-theory-client
  (implies (and (true-listp table) (natp k) (< k (len table)))
           (and (true-listp
                 (finite-field-division-polynomial-table-extend table value))
                (equal (len (finite-field-division-polynomial-table-extend
                             table value))
                       (+ 1 (len table)))
                (equal (nth k (finite-field-division-polynomial-table-extend
                               table value))
                       (nth k table))
                (equal (nth (len table)
                            (finite-field-division-polynomial-table-extend
                             table value))
                       value)))
  :rule-classes nil
  :hints (("Goal"
           :use (true-listp-of-finite-field-division-polynomial-table-extend
                 len-of-finite-field-division-polynomial-table-extend
                 nth-below-of-finite-field-division-polynomial-table-extend
                 nth-at-end-of-finite-field-division-polynomial-table-extend)
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-table-builder-minimal-theory-client
  (and (equal (len (finite-field-division-polynomial-table n a b))
              (+ 1 (nfix n)))
       (true-listp (finite-field-division-polynomial-table n a b))
       (implies (posp (nfix n))
                (equal
                 (nth (nfix n) (finite-field-division-polynomial-table n a b))
                 (finite-field-division-polynomial-recurrence-step
                  (nfix n)
                  (finite-field-division-polynomial-table (1- (nfix n)) a b)
                  a b)))
       (implies (and (natp k) (<= k (nfix n)))
                (and (equal
                      (nth k (finite-field-division-polynomial-table n a b))
                      (nth k (finite-field-division-polynomial-table k a b)))
                     (finite-field-canonical-polynomial-p
                      (nth k (finite-field-division-polynomial-table n a b)))
                     (finite-field-polynomial-p
                      (nth k (finite-field-division-polynomial-table n a b)))))
       (equal (finite-field-division-polynomial-table (nfix n) a b)
              (finite-field-division-polynomial-table n a b))
       (equal (finite-field-division-polynomial-table
               n (gfield::finite-field-fix a) (gfield::finite-field-fix b))
              (finite-field-division-polynomial-table n a b)))
  :rule-classes nil
  :hints (("Goal"
           :use (len-of-finite-field-division-polynomial-table
                 true-listp-of-finite-field-division-polynomial-table
                 finite-field-division-polynomial-table-newest-entry
                 finite-field-division-polynomial-table-lookup-stable
                 finite-field-canonical-polynomial-p-of-table-entry
                 finite-field-polynomial-p-of-table-entry
                 finite-field-division-polynomial-table-of-nfix
                 finite-field-division-polynomial-table-of-coefficient-fixes)
           :in-theory (theory 'minimal-theory))))
