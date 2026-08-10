(in-package "GPOLY")

(include-book "division-polynomial-base")
(include-book "division-polynomial-recurrence-step")
(include-book "f11-division-polynomial")
(include-book "../polynomial/generic/f11-finite-field-instance-regression")

; A semantic transport of the generic index-3 base equation to the existing
; transparent F11 implementation.  This is not a concrete curve evaluation.
(defthm f11-division-polynomial-base-index-3-from-finite-field-instance
  (equal
   (f11-division-polynomial-base 3 a b)
   (let* ((a (gfield::f11-fix a))
          (b (gfield::f11-fix b))
          (a2 (gfield::f11-mul a a)))
     (f11-normalize
      (list (gfield::f11-neg a2)
            (gfield::f11-mul (f11-natural-coefficient 12) b)
            (gfield::f11-mul (f11-natural-coefficient 6) a)
            (gfield::f11-zero)
            (f11-natural-coefficient 3)))))
  :rule-classes nil
  :hints
  (("Goal"
    :by (:functional-instance
         finite-field-division-polynomial-base-index-3
         (gfield::finite-field-element-p gfield::f11-element-p)
         (gfield::finite-field-fix gfield::f11-fix)
         (gfield::finite-field-zero gfield::f11-zero)
         (gfield::finite-field-one gfield::f11-one)
         (gfield::finite-field-add gfield::f11-add)
         (gfield::finite-field-mul gfield::f11-mul)
         (gfield::finite-field-neg gfield::f11-neg)
         (gfield::finite-field-inv gfield::f11-inv)
         (gfield::finite-field-rank gfield::f11-fix)
         (gfield::finite-field-unrank gfield::f11-fix)
         (gfield::finite-field-bound (lambda () 11))
         (finite-field-poly-fix-coefficients f11-fix-coefficients)
         (finite-field-poly-trim-trailing-zeros f11-trim-trailing-zeros)
         (finite-field-poly-normalize f11-normalize)
         (finite-field-natural-coefficient f11-natural-coefficient)
         (finite-field-division-polynomial-base-spec
          f11-division-polynomial-base)
         (finite-field-division-polynomial-base
          f11-division-polynomial-base))
    :in-theory (theory 'minimal-theory))
   (and stable-under-simplificationp
        (list
         :use (theory 'gfield::f11-finite-field-context-instance-theory)
         :in-theory
         (list 'quote
               (union-theories
                (theory 'gfield::f11-finite-field-context-instance-theory)
                (union-theories
                 '((:definition nfix)
                  (:definition zp)
                  (:definition gfield::f11-zero)
                  (:definition gfield::f11-one)
                  (:definition f11-fix-coefficients)
                  (:definition f11-trim-trailing-zeros)
                  (:definition f11-normalize)
                  (:definition f11-natural-coefficient)
                   (:definition f11-division-polynomial-base))
                 (theory 'minimal-theory))))))))

; The remaining base cases use the same joint-context instance.  Together with
; the index-3 theorem above these events cover the complete, totalized base
; operation rather than only the nontrivial sample that established the seam.
(defthm f11-division-polynomial-base-equations-from-finite-field-instance
  (and (equal (f11-division-polynomial-base 0 a b) nil)
       (equal (f11-division-polynomial-base 1 a b)
              (list (gfield::f11-one)))
       (equal (f11-division-polynomial-base 2 a b)
              (list (gfield::f11-one))))
  :rule-classes nil)

(defthm f11-division-polynomial-base-index-4-from-finite-field-instance
  (equal
   (f11-division-polynomial-base 4 a b)
   (let* ((a (gfield::f11-fix a))
          (b (gfield::f11-fix b))
          (a2 (gfield::f11-mul a a))
          (a3 (gfield::f11-mul a2 a))
          (b2 (gfield::f11-mul b b))
          (ab (gfield::f11-mul a b)))
     (f11-normalize
      (list
       (gfield::f11-neg
        (gfield::f11-add
         (gfield::f11-mul (f11-natural-coefficient 2) a3)
         (gfield::f11-mul (f11-natural-coefficient 16) b2)))
       (gfield::f11-neg
        (gfield::f11-mul (f11-natural-coefficient 8) ab))
       (gfield::f11-neg
        (gfield::f11-mul (f11-natural-coefficient 10) a2))
       (gfield::f11-mul (f11-natural-coefficient 40) b)
       (gfield::f11-mul (f11-natural-coefficient 10) a)
       (gfield::f11-zero)
       (f11-natural-coefficient 2)))))
  :rule-classes nil)

(defthm f11-division-polynomial-base-when-unsupported-index-from-finite-field-instance
  (implies (not (member-equal (nfix n) '(0 1 2 3 4)))
           (equal (f11-division-polynomial-base n a b) nil))
  :rule-classes nil)

(defthm f11-division-polynomial-base-of-fixes-from-finite-field-instance
  (and (equal (f11-division-polynomial-base (nfix n) a b)
              (f11-division-polynomial-base n a b))
       (equal (f11-division-polynomial-base
               n (gfield::f11-fix a) (gfield::f11-fix b))
              (f11-division-polynomial-base n a b)))
  :rule-classes nil)

; A compact reusable polynomial-operation interface.  Each equality identifies
; the generated transparent operation used by the F11 recurrence instance.
(defthm f11-division-polynomial-operation-interface
  (and (equal (f11-poly-square x) (f11-poly-mul x x))
       (equal (f11-poly-cube x) (f11-poly-mul x (f11-poly-square x)))
       (equal (f11-division-polynomial-c a b)
              (let ((four (f11-natural-coefficient 4))
                    (a (gfield::f11-fix a))
                    (b (gfield::f11-fix b)))
                (f11-normalize
                 (list (gfield::f11-mul four b)
                       (gfield::f11-mul four a)
                       (gfield::f11-zero) four)))))
  :rule-classes nil)

; This all-case theorem is the functional-instance endpoint: it transports the
; generic recurrence definition, including its base and three recurrence
; branches, to the generated F11 polynomial operations.
(defthm f11-division-polynomial-recurrence-step-from-finite-field-instance
  (equal
   (f11-division-polynomial-recurrence-step n table a b)
   (let ((n (nfix n)))
     (if (< n 5)
         (f11-division-polynomial-base n a b)
       (let* ((m (floor n 2))
              (fm-2 (nth (- m 2) table))
              (fm-1 (nth (- m 1) table))
              (fm (nth m table))
              (fm+1 (nth (+ m 1) table))
              (fm+2 (nth (+ m 2) table))
              (c2 (f11-poly-square (f11-division-polynomial-c a b))))
         (if (oddp n)
             (if (evenp m)
                 (f11-poly-sub
                  (f11-poly-mul c2
                                (f11-poly-mul fm+2 (f11-poly-cube fm)))
                  (f11-poly-mul fm-1 (f11-poly-cube fm+1)))
               (f11-poly-sub
                (f11-poly-mul fm+2 (f11-poly-cube fm))
                (f11-poly-mul c2
                              (f11-poly-mul fm-1 (f11-poly-cube fm+1)))))
           (f11-poly-mul
            fm
            (f11-poly-sub
             (f11-poly-mul fm+2 (f11-poly-square fm-1))
             (f11-poly-mul fm-2 (f11-poly-square fm+1)))))))))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                finite-field-division-polynomial-recurrence-step
                (gfield::finite-field-element-p gfield::f11-element-p)
                (gfield::finite-field-fix gfield::f11-fix)
                (gfield::finite-field-zero gfield::f11-zero)
                (gfield::finite-field-one gfield::f11-one)
                (gfield::finite-field-add gfield::f11-add)
                (gfield::finite-field-mul gfield::f11-mul)
                (gfield::finite-field-neg gfield::f11-neg)
                (gfield::finite-field-inv gfield::f11-inv)
                (gfield::finite-field-rank gfield::f11-fix)
                (gfield::finite-field-unrank gfield::f11-fix)
                (gfield::finite-field-bound (lambda () 11))
                (finite-field-poly-fix-coefficients f11-fix-coefficients)
                (finite-field-poly-trim-trailing-zeros f11-trim-trailing-zeros)
                (finite-field-poly-normalize f11-normalize)
                (finite-field-poly-raw-add f11-poly-raw-add)
                (finite-field-poly-add f11-poly-add)
                (finite-field-poly-raw-neg f11-poly-raw-neg)
                (finite-field-poly-neg f11-poly-neg)
                (finite-field-poly-sub f11-poly-sub)
                (finite-field-poly-raw-scale f11-poly-raw-scale)
                (finite-field-poly-scale f11-poly-scale)
                (finite-field-poly-raw-mul f11-poly-raw-mul)
                (finite-field-poly-mul f11-poly-mul)
                (finite-field-natural-coefficient f11-natural-coefficient)
                (finite-field-division-polynomial-base-spec f11-division-polynomial-base)
                (finite-field-division-polynomial-base f11-division-polynomial-base)
                (finite-field-division-polynomial-c f11-division-polynomial-c)
                (finite-field-poly-square f11-poly-square)
                (finite-field-poly-cube f11-poly-cube)
                (finite-field-division-polynomial-odd-even-step
                 (lambda (c2 fm-1 fm fm+1 fm+2)
                   (f11-poly-sub
                    (f11-poly-mul
                     c2 (f11-poly-mul fm+2 (f11-poly-cube fm)))
                    (f11-poly-mul fm-1 (f11-poly-cube fm+1)))))
                (finite-field-division-polynomial-odd-odd-step
                 (lambda (c2 fm-1 fm fm+1 fm+2)
                   (f11-poly-sub
                    (f11-poly-mul fm+2 (f11-poly-cube fm))
                    (f11-poly-mul
                     c2 (f11-poly-mul fm-1 (f11-poly-cube fm+1))))))
                (finite-field-division-polynomial-even-step
                 (lambda (fm-2 fm-1 fm fm+1 fm+2)
                   (f11-poly-mul
                    fm
                    (f11-poly-sub
                     (f11-poly-mul fm+2 (f11-poly-square fm-1))
                     (f11-poly-mul fm-2 (f11-poly-square fm+1))))))
                (finite-field-division-polynomial-recurrence-step
                 f11-division-polynomial-recurrence-step))
           :in-theory (theory 'minimal-theory))
          (and stable-under-simplificationp
               (list
                :use (theory 'gfield::f11-finite-field-context-instance-theory)
                :in-theory
                (list 'quote
                      (union-theories
                       (theory 'gfield::f11-finite-field-context-instance-theory)
                       (union-theories
                        '((:definition nfix)
                          (:definition zp)
                          (:definition gfield::f11-zero)
                          (:definition gfield::f11-one)
                          (:definition f11-fix-coefficients)
                          (:definition f11-trim-trailing-zeros)
                          (:definition f11-normalize)
                          (:definition f11-poly-raw-add)
                          (:definition f11-poly-add)
                          (:definition f11-poly-raw-neg)
                          (:definition f11-poly-neg)
                          (:definition f11-poly-sub)
                          (:definition f11-poly-raw-scale)
                          (:definition f11-poly-scale)
                          (:definition f11-poly-raw-mul)
                          (:definition f11-poly-mul)
                          (:definition f11-natural-coefficient)
                          (:definition f11-division-polynomial-base)
                          (:definition f11-division-polynomial-c)
                          (:definition f11-poly-square)
                          (:definition f11-poly-cube)
                          (:definition f11-division-polynomial-recurrence-step))
                        (theory 'minimal-theory))))))))
