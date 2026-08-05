(in-package "GPOLY")

(include-book "finite-field-division-step")

(set-default-hints nil)

(local (in-theory (disable finite-field-canonical-polynomial-p
                           finite-field-poly-degree
                           finite-field-poly-division-step-core)))

(def-divmod-instance
  finite-field-poly-divmod-core
  finite-field-poly-divmod
  finite-field-canonical-polynomial-p
  finite-field-poly-degree
  finite-field-poly-division-step-core
  finite-field-poly-add
  finite-field-poly-normalize
  finite-field-poly-division-step-core-length-decreases)

(def-divmod-projections-instance
  finite-field-poly-quotient
  finite-field-poly-remainder
  finite-field-poly-divmod)

(verify-guards finite-field-poly-divmod-core)
(verify-guards finite-field-poly-divmod)
(verify-guards finite-field-poly-quotient)
(verify-guards finite-field-poly-remainder)

(deftheory finite-field-divmod-definition-theory
  '(finite-field-poly-divmod-core
    finite-field-poly-divmod
    finite-field-poly-quotient
    finite-field-poly-remainder))

(defthm finite-field-poly-quotient-is-divmod-quotient
  (equal (finite-field-poly-quotient f g)
         (mv-nth 0 (finite-field-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable finite-field-poly-quotient))))

(defthm finite-field-poly-remainder-is-divmod-remainder
  (equal (finite-field-poly-remainder f g)
         (mv-nth 1 (finite-field-poly-divmod f g)))
  :hints (("Goal" :in-theory (enable finite-field-poly-remainder))))

(defthm finite-field-poly-normalize-definition-for-divmod
  (equal (finite-field-poly-normalize poly)
         (finite-field-poly-trim-trailing-zeros
          (finite-field-poly-fix-coefficients poly)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-normalize))))

(defthm finite-field-poly-divmod-definition-for-reduction-instantiation
  (equal (finite-field-poly-divmod f g)
         (let ((result
                (finite-field-poly-divmod-core nil
                                               (finite-field-poly-normalize f)
                                               (finite-field-poly-normalize g))))
           (list (car result) (cdr result))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-divmod))))


(defthm finite-field-poly-degree-when-normalize-not-consp
  (implies (not (consp (finite-field-poly-normalize poly)))
           (equal (finite-field-poly-degree poly) -1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-of-poly-normalize
                            (p poly))
                 (:instance finite-field-poly-degree-of-nil))
           :in-theory (enable finite-field-poly-degree))))

(defthm finite-field-poly-degree-when-normalize-consp
  (implies (consp (finite-field-poly-normalize poly))
           (equal (finite-field-poly-degree poly)
                  (+ -1 (len (finite-field-poly-normalize poly)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-normalize poly)))
                 (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs poly))
                 (:instance finite-field-poly-degree-of-poly-normalize
                            (p poly)))
           :in-theory (disable finite-field-poly-degree
                               finite-field-poly-normalize))))

(defthm finite-field-poly-degree-when-normalize-consp-expanded
  (implies (consp (finite-field-poly-normalize poly))
           (equal (finite-field-poly-degree poly)
                  (+ -1
                     (len (finite-field-poly-trim-trailing-zeros
                           (finite-field-poly-fix-coefficients poly))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-when-normalize-consp)
                 (:instance finite-field-poly-normalize-definition-for-divmod))
           :in-theory (disable finite-field-poly-degree
                               finite-field-poly-normalize))))


(defthm finite-field-poly-degree-definition-for-divmod
  (equal (finite-field-poly-degree poly)
         (if (consp (finite-field-poly-normalize poly))
             (+ -1 (len (finite-field-poly-normalize poly)))
           -1))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-degree))))

; Aggregate public divmod interface remains the next boundary.

(defthm finite-field-poly-divmod-core-accumulator-step-canonical
  (implies (and (finite-field-canonical-polynomial-p quotient)
                (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (finite-field-canonical-polynomial-p
            (finite-field-poly-add
             quotient
             (car (finite-field-poly-division-step-core remainder divisor)))))
  :hints (("Goal"
           :use ((:instance finite-field-poly-division-step-core-term-properties))
           :in-theory (disable finite-field-poly-division-step-core
                               finite-field-poly-add
                               finite-field-poly-mul
                               finite-field-poly-raw-mul
                               finite-field-poly-normalize))))


; Direct core output canonicality remains the next checkpoint.

(defthm finite-field-poly-divmod-core-quotient-canonical
  (implies (and (finite-field-canonical-polynomial-p quotient)
                (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor))
           (finite-field-canonical-polynomial-p
            (car (finite-field-poly-divmod-core quotient remainder divisor))))
  :hints (("Goal" :induct (finite-field-poly-divmod-core quotient remainder divisor)
           :in-theory (e/d (finite-field-poly-divmod-core)
                           (finite-field-poly-division-step-core
                            finite-field-poly-add finite-field-poly-sub
                            finite-field-poly-mul finite-field-poly-monomial
                            finite-field-poly-normalize
                            finite-field-poly-raw-add
                            finite-field-poly-raw-mul
                            finite-field-canonical-polynomial-p
                            finite-field-poly-degree)))))

(defthm finite-field-poly-divmod-core-remainder-canonical
  (implies (and (finite-field-canonical-polynomial-p quotient)
                (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor))
           (finite-field-canonical-polynomial-p
            (cdr (finite-field-poly-divmod-core quotient remainder divisor))))
  :hints (("Goal" :induct (finite-field-poly-divmod-core quotient remainder divisor)
           :in-theory (e/d (finite-field-poly-divmod-core)
                           (finite-field-poly-division-step-core
                            finite-field-poly-add finite-field-poly-sub
                            finite-field-poly-mul finite-field-poly-monomial
                            finite-field-poly-normalize
                            finite-field-poly-raw-add
                            finite-field-poly-raw-mul
                            finite-field-canonical-polynomial-p
                            finite-field-poly-degree)))))
(defthm finite-field-canonical-polynomial-atom-is-nil
  (implies (and (finite-field-canonical-polynomial-p p)
                (not (consp p)))
           (equal p nil))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable finite-field-canonical-polynomial-p
                              finite-field-coefficient-list-p))))

(defthm finite-field-poly-divmod-core-final-remainder-degree-bound
  (implies (and (finite-field-canonical-polynomial-p quotient)
                (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp divisor))
           (let ((final-remainder
                  (cdr (finite-field-poly-divmod-core quotient remainder divisor))))
             (or (equal final-remainder nil)
                 (< (finite-field-poly-degree final-remainder)
                    (finite-field-poly-degree divisor)))))
  :rule-classes nil
  :hints (("Goal"
           :induct (finite-field-poly-divmod-core quotient remainder divisor)
           :in-theory (e/d (finite-field-poly-divmod-core)
                           (finite-field-poly-division-step-core
                            finite-field-poly-add finite-field-poly-sub
                            finite-field-poly-mul
                            finite-field-poly-monomial
                            finite-field-poly-normalize
                            finite-field-poly-raw-add
                            finite-field-poly-raw-mul
                            finite-field-canonical-polynomial-p
                            finite-field-poly-degree)))
          (and stable-under-simplificationp
               (list :use
                     (list (list :instance
                                 'finite-field-canonical-polynomial-atom-is-nil
                                 (list 'p 'remainder)))
                     :in-theory
                     (list 'disable
                           'finite-field-poly-divmod-core
                           'finite-field-poly-division-step-core
                           'finite-field-poly-add
                           'finite-field-poly-sub
                           'finite-field-poly-mul
                           'finite-field-poly-monomial
                           'finite-field-poly-normalize
                           'finite-field-poly-raw-add
                           'finite-field-poly-raw-mul
                           'finite-field-canonical-polynomial-p
                           'finite-field-poly-degree)))))

(defthm finite-field-canonical-polynomial-p-of-nil
  (finite-field-canonical-polynomial-p nil)
  :hints (("Goal" :in-theory (enable finite-field-canonical-polynomial-p
                                     finite-field-coefficient-list-p))))

(defthm finite-field-poly-divmod-quotient-canonical
  (finite-field-canonical-polynomial-p
   (mv-nth 0 (finite-field-poly-divmod f g)))
  :hints (("Goal"
           :use ((:instance finite-field-poly-divmod-core-quotient-canonical
                            (quotient nil)
                            (remainder (finite-field-poly-normalize f))
                            (divisor (finite-field-poly-normalize g))))
           :in-theory (e/d (finite-field-poly-divmod)
                           (finite-field-poly-divmod-core
                            finite-field-poly-normalize
                            finite-field-canonical-polynomial-p)))))

(defthm finite-field-poly-divmod-remainder-canonical
  (finite-field-canonical-polynomial-p
   (mv-nth 1 (finite-field-poly-divmod f g)))
  :hints (("Goal"
           :use ((:instance finite-field-poly-divmod-core-remainder-canonical
                            (quotient nil)
                            (remainder (finite-field-poly-normalize f))
                            (divisor (finite-field-poly-normalize g))))
           :in-theory (e/d (finite-field-poly-divmod)
                           (finite-field-poly-divmod-core
                            finite-field-poly-normalize
                            finite-field-canonical-polynomial-p)))))

(defthm finite-field-poly-divmod-final-remainder-degree-bound
  (implies (consp (finite-field-poly-normalize g))
           (or (equal (mv-nth 1 (finite-field-poly-divmod f g)) nil)
               (< (finite-field-poly-degree
                   (mv-nth 1 (finite-field-poly-divmod f g)))
                  (finite-field-poly-degree
                   (finite-field-poly-normalize g)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divmod-core-final-remainder-degree-bound
                            (quotient nil)
                            (remainder (finite-field-poly-normalize f))
                            (divisor (finite-field-poly-normalize g)))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-normalize g))))
           :in-theory (e/d (finite-field-poly-divmod)
                           (finite-field-poly-divmod-core
                            finite-field-poly-normalize
                            finite-field-poly-degree)))))
(defthm finite-field-poly-divmod-accumulator-algebra
  (implies (and (finite-field-polynomial-p quotient)
                (finite-field-polynomial-p term)
                (finite-field-polynomial-p divisor)
                (finite-field-polynomial-p next)
                (finite-field-polynomial-p remainder)
                (equal (finite-field-poly-add
                        (finite-field-poly-mul term divisor)
                        next)
                       remainder))
           (equal (finite-field-poly-add
                   (finite-field-poly-mul
                    (finite-field-poly-add quotient term)
                    divisor)
                   next)
                  (finite-field-poly-add
                   (finite-field-poly-mul quotient divisor)
                   remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-mul-right-distributive
                            (x quotient) (y term) (z divisor))
                 (:instance finite-field-poly-add-associative
                            (x (finite-field-poly-mul quotient divisor))
                            (y (finite-field-poly-mul term divisor))
                            (z next)))
           :in-theory (disable finite-field-poly-add
                               finite-field-poly-mul
                               finite-field-poly-raw-mul
                               finite-field-poly-normalize))))

(defthm finite-field-poly-divmod-core-reconstruction-invariant
  (implies (and (finite-field-canonical-polynomial-p quotient)
                (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor))
           (equal (finite-field-poly-add
                   (finite-field-poly-mul
                    (car (finite-field-poly-divmod-core quotient remainder divisor))
                    divisor)
                   (cdr (finite-field-poly-divmod-core quotient remainder divisor)))
                  (finite-field-poly-add
                   (finite-field-poly-mul quotient divisor)
                   remainder)))
  :rule-classes nil
  :hints (("Goal"
           :induct (finite-field-poly-divmod-core quotient remainder divisor)
           :in-theory (e/d (finite-field-poly-divmod-core)
                           (finite-field-poly-division-step-core
                            finite-field-poly-add finite-field-poly-mul
                            finite-field-poly-sub finite-field-poly-monomial
                            finite-field-poly-normalize
                            finite-field-poly-raw-add
                            finite-field-poly-raw-mul
                            finite-field-canonical-polynomial-p
                            finite-field-poly-degree)))
          (and stable-under-simplificationp
               (list :use
                     (list (list :instance
                                 'finite-field-poly-division-step-core-reconstruction)
                           (list :instance
                                 'finite-field-poly-division-step-core-term-properties)
                           (list :instance
                                 'finite-field-poly-division-step-core-next-polynomial)
                           (list :instance
                                 'finite-field-poly-divmod-accumulator-algebra
                                 (list 'term
                                       '(car (finite-field-poly-division-step-core
                                              remainder divisor)))
                                 (list 'next
                                       '(cdr (finite-field-poly-division-step-core
                                              remainder divisor)))))
                     :in-theory
                     (list 'disable
                           'finite-field-poly-divmod-core
                           'finite-field-poly-division-step-core
                           'finite-field-poly-add
                           'finite-field-poly-mul
                           'finite-field-poly-sub
                           'finite-field-poly-monomial
                           'finite-field-poly-normalize
                           'finite-field-poly-raw-add
                           'finite-field-poly-raw-mul
                           'finite-field-canonical-polynomial-p
                           'finite-field-poly-degree)))))

(defthm finite-field-poly-divmod-reconstruction
  (equal (finite-field-poly-add
          (finite-field-poly-mul
           (mv-nth 0 (finite-field-poly-divmod f g))
           (finite-field-poly-normalize g))
          (mv-nth 1 (finite-field-poly-divmod f g)))
         (finite-field-poly-normalize f))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divmod-core-reconstruction-invariant
                            (quotient nil)
                            (remainder (finite-field-poly-normalize f))
                            (divisor (finite-field-poly-normalize g))))
           :in-theory (e/d (finite-field-poly-divmod)
                           (finite-field-poly-divmod-core
                            finite-field-poly-add
                            finite-field-poly-mul
                            finite-field-poly-normalize)))))

(defthm finite-field-canonical-polynomial-p-of-poly-quotient
  (finite-field-canonical-polynomial-p
   (finite-field-poly-quotient f g))
  :hints (("Goal"
           :use ((:instance finite-field-poly-divmod-quotient-canonical)))))

(defthm finite-field-canonical-polynomial-p-of-poly-remainder
  (finite-field-canonical-polynomial-p
   (finite-field-poly-remainder f g))
  :hints (("Goal"
           :use ((:instance finite-field-poly-divmod-remainder-canonical)))))

(defthm finite-field-poly-remainder-degree-bound
  (implies (consp (finite-field-poly-normalize g))
           (or (equal (finite-field-poly-remainder f g) nil)
               (< (finite-field-poly-degree
                   (finite-field-poly-remainder f g))
                  (finite-field-poly-degree
                   (finite-field-poly-normalize g)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divmod-final-remainder-degree-bound)))))
