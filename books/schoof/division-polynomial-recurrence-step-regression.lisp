(in-package "GPOLY")

(include-book "division-polynomial-recurrence-step")

(defthm division-polynomial-c-minimal-theory-client
  (and (equal (finite-field-division-polynomial-c a b)
              (let ((four (finite-field-natural-coefficient 4))
                    (a (gfield::finite-field-fix a))
                    (b (gfield::finite-field-fix b)))
                (finite-field-poly-normalize
                 (list (gfield::finite-field-mul four b)
                       (gfield::finite-field-mul four a)
                       (gfield::finite-field-zero) four))))
       (finite-field-canonical-polynomial-p
        (finite-field-division-polynomial-c a b))
       (finite-field-polynomial-p
        (finite-field-division-polynomial-c a b)))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-division-polynomial-c-equation
                 finite-field-canonical-polynomial-p-of-division-polynomial-c
                 finite-field-polynomial-p-of-division-polynomial-c)
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-step-closure-and-fixing-minimal-theory-client
  (and (finite-field-canonical-polynomial-p
        (finite-field-division-polynomial-recurrence-step n table a b))
       (finite-field-polynomial-p
        (finite-field-division-polynomial-recurrence-step n table a b))
       (equal (finite-field-division-polynomial-recurrence-step
               (nfix n) table a b)
              (finite-field-division-polynomial-recurrence-step n table a b))
       (equal (finite-field-division-polynomial-recurrence-step
               n table (gfield::finite-field-fix a)
               (gfield::finite-field-fix b))
              (finite-field-division-polynomial-recurrence-step n table a b)))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-canonical-polynomial-p-of-division-polynomial-recurrence-step
                 finite-field-polynomial-p-of-division-polynomial-recurrence-step
                 finite-field-division-polynomial-recurrence-step-of-nfix
                 finite-field-division-polynomial-recurrence-step-of-coefficient-fixes)
           :in-theory (theory 'minimal-theory))))

(defthm division-polynomial-step-orientations-minimal-theory-client
  (and
   (implies (and (natp m) (<= 2 m) (evenp m))
            (equal
             (finite-field-division-polynomial-recurrence-step
              (+ 1 (* 2 m)) table a b)
             (finite-field-poly-sub
              (finite-field-poly-mul
               (finite-field-poly-square
                (finite-field-division-polynomial-c a b))
               (finite-field-poly-mul (nth (+ m 2) table)
                                      (finite-field-poly-cube (nth m table))))
              (finite-field-poly-mul
               (nth (- m 1) table)
               (finite-field-poly-cube (nth (+ m 1) table))))))
   (implies (and (natp m) (<= 2 m) (oddp m))
            (equal
             (finite-field-division-polynomial-recurrence-step
              (+ 1 (* 2 m)) table a b)
             (finite-field-poly-sub
              (finite-field-poly-mul (nth (+ m 2) table)
                                     (finite-field-poly-cube (nth m table)))
              (finite-field-poly-mul
               (finite-field-poly-square
                (finite-field-division-polynomial-c a b))
               (finite-field-poly-mul
                (nth (- m 1) table)
                (finite-field-poly-cube (nth (+ m 1) table)))))))
   (implies (and (natp m) (<= 3 m))
            (equal
             (finite-field-division-polynomial-recurrence-step (* 2 m) table a b)
             (finite-field-poly-mul
              (nth m table)
              (finite-field-poly-sub
               (finite-field-poly-mul
                (nth (+ m 2) table)
                (finite-field-poly-square (nth (- m 1) table)))
               (finite-field-poly-mul
                (nth (- m 2) table)
                (finite-field-poly-square (nth (+ m 1) table))))))))
  :rule-classes nil
  :hints (("Goal"
           :use (finite-field-division-polynomial-recurrence-step-odd-even-half
                 finite-field-division-polynomial-recurrence-step-odd-odd-half
                 finite-field-division-polynomial-recurrence-step-even)
           :in-theory (theory 'minimal-theory))))
