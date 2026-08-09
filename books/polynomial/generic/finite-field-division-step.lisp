(in-package "GPOLY")

(include-book "finite-field-monomial-division-support")
(include-book "division-step")

(set-default-hints nil)

(def-division-step-instance
  finite-field-poly-division-step-core
  finite-field-poly-division-step
  finite-field-poly-division-step-term
  finite-field-poly-division-step-next
  finite-field-poly-degree
  finite-field-poly-leading-coefficient
  finite-field-poly-monomial
  finite-field-poly-sub
  finite-field-poly-mul
  finite-field-poly-normalize
  finite-field-div)

(verify-guards finite-field-poly-division-step-core)
(verify-guards finite-field-poly-division-step)
(verify-guards finite-field-poly-division-step-term)
(verify-guards finite-field-poly-division-step-next)

(deftheory finite-field-division-step-definition-theory
  '(finite-field-poly-division-step-core
    finite-field-poly-division-step
    finite-field-poly-division-step-term
    finite-field-poly-division-step-next))

(defthm finite-field-poly-division-step-core-inactive
  (implies (or (not (consp remainder))
               (not (consp divisor))
               (< (finite-field-poly-degree remainder)
                  (finite-field-poly-degree divisor)))
           (equal (finite-field-poly-division-step-core remainder divisor)
                  (cons nil remainder)))
  :hints (("Goal" :in-theory (enable finite-field-poly-division-step-core))))

(defthm finite-field-divisor-leading-coefficient-nonzero-for-division-step
  (implies (and (finite-field-canonical-polynomial-p divisor) (consp divisor))
           (not (equal (finite-field-poly-leading-coefficient divisor)
                       (gfield::finite-field-zero))))
  :hints (("Goal"
           :use ((:instance finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p divisor))))))

(defthm finite-field-divisor-leading-coefficient-inverse-nonzero-for-division-step
  (implies (and (finite-field-canonical-polynomial-p divisor) (consp divisor))
           (not (equal (gfield::finite-field-inv
                        (finite-field-poly-leading-coefficient divisor))
                       (gfield::finite-field-zero))))
  :hints (("Goal"
           :use ((:instance finite-field-inv-nonzero
                            (y (finite-field-poly-leading-coefficient divisor)))
                 (:instance finite-field-element-p-of-poly-leading-coefficient
                            (p divisor))
                 (:instance finite-field-divisor-leading-coefficient-nonzero-for-division-step)))))

(defthm finite-field-poly-division-step-core-term-properties
  (implies (and (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (let ((term (car (finite-field-poly-division-step-core remainder divisor))))
             (and (finite-field-canonical-polynomial-p term)
                  (consp term)
                  (equal (finite-field-poly-degree term)
                         (- (finite-field-poly-degree remainder)
                            (finite-field-poly-degree divisor)))
                  (equal (finite-field-poly-leading-coefficient term)
                         (finite-field-div
                          (finite-field-poly-leading-coefficient remainder)
                          (finite-field-poly-leading-coefficient divisor))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-of-monomial
                            (a (finite-field-div
                                (finite-field-poly-leading-coefficient remainder)
                                (finite-field-poly-leading-coefficient divisor)))
                            (n (- (finite-field-poly-degree remainder)
                                  (finite-field-poly-degree divisor))))
                 (:instance finite-field-poly-leading-coefficient-of-monomial
                            (a (finite-field-div
                                (finite-field-poly-leading-coefficient remainder)
                                (finite-field-poly-leading-coefficient divisor)))
                            (n (- (finite-field-poly-degree remainder)
                                  (finite-field-poly-degree divisor))))
                 (:instance finite-field-div-nonzero
                            (x (finite-field-poly-leading-coefficient remainder))
                            (y (finite-field-poly-leading-coefficient divisor)))
                 (:instance finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p remainder))
                 (:instance finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p divisor))
                 (:instance finite-field-element-p-of-poly-leading-coefficient
                            (p remainder))
                 (:instance finite-field-element-p-of-poly-leading-coefficient
                            (p divisor))
                 (:instance finite-field-poly-normalize-when-canonical (xs remainder))
                 (:instance finite-field-poly-normalize-when-canonical (xs divisor)))
           :in-theory (enable finite-field-poly-division-step-core))))

(local
 (deftheory finite-field-mul-degree-instance-theory
   (union-theories
    (theory 'finite-field-poly-definition-theory)
    (theory 'minimal-theory))))

(set-default-hints
 '((and stable-under-simplificationp
        (list :use (theory 'gfield::finite-field-context-instance-theory)
              :in-theory
              (list 'quote
                    (theory 'finite-field-mul-degree-instance-theory))))))

(defthm finite-field-poly-leading-coefficient-of-poly-mul
  (implies (and (finite-field-canonical-polynomial-p f)
                (finite-field-canonical-polynomial-p g)
                (consp f)
                (consp g))
           (equal (finite-field-poly-leading-coefficient
                   (finite-field-poly-mul f g))
                  (gfield::finite-field-mul
                   (finite-field-poly-leading-coefficient f)
                   (finite-field-poly-leading-coefficient g))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance poly-leading-coefficient-of-poly-mul
                 (gfield::field-element-p gfield::finite-field-element-p)
                 (gfield::field-fix gfield::finite-field-fix)
                 (gfield::field-zero gfield::finite-field-zero)
                 (gfield::field-one gfield::finite-field-one)
                 (gfield::field-add gfield::finite-field-add)
                 (gfield::field-mul gfield::finite-field-mul)
                 (gfield::field-neg gfield::finite-field-neg)
                 (gfield::field-inv gfield::finite-field-inv)
                 (coefficient-list-p finite-field-coefficient-list-p)
                 (polynomial-p finite-field-polynomial-p)
                 (canonical-polynomial-p finite-field-canonical-polynomial-p)
                 (fix-coefficients finite-field-poly-fix-coefficients)
                 (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                 (normalize finite-field-poly-normalize)
                 (raw-add finite-field-poly-raw-add)
                 (poly-add finite-field-poly-add)
                 (raw-scale finite-field-poly-raw-scale)
                 (poly-scale finite-field-poly-scale)
                 (raw-mul finite-field-poly-raw-mul)
                 (poly-mul finite-field-poly-mul)
                 (poly-degree finite-field-poly-degree)
                 (poly-leading-coefficient finite-field-poly-leading-coefficient)))))


(defthm finite-field-poly-degree-of-poly-mul
  (implies (and (finite-field-canonical-polynomial-p f)
                (finite-field-canonical-polynomial-p g)
                (consp f)
                (consp g))
           (equal (finite-field-poly-degree (finite-field-poly-mul f g))
                  (+ (finite-field-poly-degree f)
                     (finite-field-poly-degree g))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance poly-degree-of-poly-mul
                 (gfield::field-element-p gfield::finite-field-element-p)
                 (gfield::field-fix gfield::finite-field-fix)
                 (gfield::field-zero gfield::finite-field-zero)
                 (gfield::field-one gfield::finite-field-one)
                 (gfield::field-add gfield::finite-field-add)
                 (gfield::field-mul gfield::finite-field-mul)
                 (gfield::field-neg gfield::finite-field-neg)
                 (gfield::field-inv gfield::finite-field-inv)
                 (coefficient-list-p finite-field-coefficient-list-p)
                 (polynomial-p finite-field-polynomial-p)
                 (canonical-polynomial-p finite-field-canonical-polynomial-p)
                 (fix-coefficients finite-field-poly-fix-coefficients)
                 (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                 (normalize finite-field-poly-normalize)
                 (raw-add finite-field-poly-raw-add)
                 (poly-add finite-field-poly-add)
                 (raw-scale finite-field-poly-raw-scale)
                 (poly-scale finite-field-poly-scale)
                 (raw-mul finite-field-poly-raw-mul)
                 (poly-mul finite-field-poly-mul)
                 (poly-degree finite-field-poly-degree)
                 (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-consp-of-poly-mul-when-canonical-nonzero
  (implies (and (finite-field-canonical-polynomial-p f)
                (finite-field-canonical-polynomial-p g)
                (consp f)
                (consp g))
           (consp (finite-field-poly-mul f g)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance consp-of-poly-mul-when-canonical-nonzero
                 (gfield::field-element-p gfield::finite-field-element-p)
                 (gfield::field-fix gfield::finite-field-fix)
                 (gfield::field-zero gfield::finite-field-zero)
                 (gfield::field-one gfield::finite-field-one)
                 (gfield::field-add gfield::finite-field-add)
                 (gfield::field-mul gfield::finite-field-mul)
                 (gfield::field-neg gfield::finite-field-neg)
                 (gfield::field-inv gfield::finite-field-inv)
                 (coefficient-list-p finite-field-coefficient-list-p)
                 (polynomial-p finite-field-polynomial-p)
                 (canonical-polynomial-p finite-field-canonical-polynomial-p)
                 (fix-coefficients finite-field-poly-fix-coefficients)
                 (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                 (normalize finite-field-poly-normalize)
                 (raw-add finite-field-poly-raw-add)
                 (poly-add finite-field-poly-add)
                 (raw-scale finite-field-poly-raw-scale)
                 (poly-scale finite-field-poly-scale)
                 (raw-mul finite-field-poly-raw-mul)
                 (poly-mul finite-field-poly-mul)
                 (poly-degree finite-field-poly-degree)
                 (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(set-default-hints nil)

(defthm finite-field-poly-division-step-core-product-properties
  (implies (and (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (let* ((term (car (finite-field-poly-division-step-core remainder divisor)))
                  (product (finite-field-poly-mul term divisor)))
             (and (finite-field-canonical-polynomial-p product)
                  (consp product)
                  (equal (finite-field-poly-degree product)
                         (finite-field-poly-degree remainder))
                  (equal (finite-field-poly-leading-coefficient product)
                         (finite-field-poly-leading-coefficient remainder)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-division-step-core-term-properties)
                 (:instance finite-field-poly-degree-of-poly-mul
                            (f (car (finite-field-poly-division-step-core remainder divisor)))
                            (g divisor))
                 (:instance finite-field-consp-of-poly-mul-when-canonical-nonzero
                            (f (car (finite-field-poly-division-step-core remainder divisor)))
                            (g divisor))
                 (:instance finite-field-poly-leading-coefficient-of-poly-mul
                            (f (car (finite-field-poly-division-step-core remainder divisor)))
                            (g divisor))
                 (:instance finite-field-div-mul-denominator
                            (x (finite-field-poly-leading-coefficient remainder))
                            (y (finite-field-poly-leading-coefficient divisor)))
                 (:instance finite-field-element-p-of-poly-leading-coefficient
                            (p divisor))
                 (:instance finite-field-element-p-of-poly-leading-coefficient
                            (p remainder))
                 (:instance finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p divisor)))
           :in-theory
           (disable finite-field-poly-mul finite-field-poly-monomial
                    finite-field-poly-normalize finite-field-poly-raw-mul
                    finite-field-poly-raw-add gfield::finite-field-mul-commutative))))

(defthm finite-field-poly-division-step-core-next-canonical
  (implies (finite-field-canonical-polynomial-p remainder)
           (finite-field-canonical-polynomial-p
            (cdr (finite-field-poly-division-step-core remainder divisor))))
  :hints (("Goal"
           :cases ((and (finite-field-canonical-polynomial-p divisor)
                        (consp remainder) (consp divisor)
                        (<= (finite-field-poly-degree divisor)
                            (finite-field-poly-degree remainder))))
           :use ((:instance finite-field-poly-division-step-core-product-properties))
           :in-theory (e/d (finite-field-poly-division-step-core)
                           (finite-field-poly-mul
                            finite-field-poly-sub
                            finite-field-poly-monomial
                            finite-field-poly-normalize
                            finite-field-poly-raw-mul
                            finite-field-poly-raw-add)))))


(defthm finite-field-canonical-polynomial-p-of-raw-neg-when-canonical
  (implies (finite-field-canonical-polynomial-p x)
           (finite-field-canonical-polynomial-p
            (finite-field-poly-raw-neg x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance
                canonical-polynomial-p-of-raw-neg-when-canonical
                (gfield::field-element-p gfield::finite-field-element-p)
                (gfield::field-fix gfield::finite-field-fix)
                (gfield::field-zero gfield::finite-field-zero)
                (gfield::field-one gfield::finite-field-one)
                (gfield::field-add gfield::finite-field-add)
                (gfield::field-mul gfield::finite-field-mul)
                (gfield::field-neg gfield::finite-field-neg)
                (gfield::field-inv gfield::finite-field-inv)
                (coefficient-list-p finite-field-coefficient-list-p)
                (canonical-polynomial-p finite-field-canonical-polynomial-p)
                (raw-neg finite-field-poly-raw-neg)))
          (and stable-under-simplificationp
               (list :use (theory 'gfield::finite-field-context-instance-theory)
                     :in-theory
                     (list 'quote
                           '(finite-field-coefficient-list-p
                             finite-field-canonical-polynomial-p
                             finite-field-poly-raw-neg))))))

(defthm finite-field-poly-neg-when-canonical
  (implies (finite-field-canonical-polynomial-p x)
           (equal (finite-field-poly-neg x)
                  (finite-field-poly-raw-neg x)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-canonical-polynomial-p-of-raw-neg-when-canonical)
                 (:instance finite-field-poly-normalize-when-canonical
                            (xs (finite-field-poly-raw-neg x))))
           :in-theory (e/d (finite-field-poly-neg)
                           (finite-field-poly-normalize
                            finite-field-poly-fix-coefficients
                            finite-field-poly-trim-trailing-zeros)))))

(defthm finite-field-poly-sub-definition
  (equal (finite-field-poly-sub x y)
         (finite-field-poly-add x (finite-field-poly-neg y)))
  :hints (("Goal" :in-theory (enable finite-field-poly-sub))))

(defthm finite-field-poly-sub-of-canonical-operands
  (implies (and (finite-field-canonical-polynomial-p x)
                (finite-field-canonical-polynomial-p y))
           (equal (finite-field-poly-sub x y)
                  (finite-field-poly-normalize
                   (finite-field-poly-raw-add
                    x (finite-field-poly-raw-neg y)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-sub-definition)
                 (:instance finite-field-poly-neg-when-canonical (x y))
                 (:instance finite-field-poly-normalize-when-canonical (xs x))
                 (:instance finite-field-poly-normalize-when-canonical
                            (xs (finite-field-poly-raw-neg y)))
                 (:instance
                  finite-field-canonical-polynomial-p-of-raw-neg-when-canonical
                  (x y)))
           :in-theory (e/d (finite-field-poly-add)
                           (finite-field-poly-sub
                            finite-field-poly-neg
                            finite-field-poly-normalize
                            finite-field-poly-raw-add)))))

(defthm finite-field-poly-add-left-to-poly-sub
  (implies (and (finite-field-polynomial-p x)
                (finite-field-canonical-polynomial-p y))
           (equal (finite-field-poly-add x (finite-field-poly-sub y x)) y))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-sub-definition)
           :use ((:functional-instance poly-add-left-to-poly-sub
                 (gfield::field-element-p gfield::finite-field-element-p)
                 (gfield::field-fix gfield::finite-field-fix)
                 (gfield::field-zero gfield::finite-field-zero)
                 (gfield::field-one gfield::finite-field-one)
                 (gfield::field-add gfield::finite-field-add)
                 (gfield::field-mul gfield::finite-field-mul)
                 (gfield::field-neg gfield::finite-field-neg)
                 (gfield::field-inv gfield::finite-field-inv)
                 (coefficient-list-p finite-field-coefficient-list-p)
                 (polynomial-p finite-field-polynomial-p)
                 (canonical-polynomial-p finite-field-canonical-polynomial-p)
                 (fix-coefficients finite-field-poly-fix-coefficients)
                 (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                 (normalize finite-field-poly-normalize)
                 (raw-add finite-field-poly-raw-add)
                 (poly-add finite-field-poly-add)
                 (raw-neg finite-field-poly-raw-neg)
                 (poly-neg finite-field-poly-neg)
                 (poly-sub finite-field-poly-sub))))))

(defthm finite-field-poly-division-step-core-active
  (implies (and (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (equal (finite-field-poly-division-step-core remainder divisor)
                  (let* ((k (- (finite-field-poly-degree remainder)
                               (finite-field-poly-degree divisor)))
                         (c (finite-field-div
                             (finite-field-poly-leading-coefficient remainder)
                             (finite-field-poly-leading-coefficient divisor)))
                         (term (finite-field-poly-monomial c k)))
                    (cons term
                          (finite-field-poly-sub
                           remainder
                           (finite-field-poly-mul term divisor))))))
  :hints (("Goal" :in-theory (enable finite-field-poly-division-step-core))))

(defthm finite-field-poly-division-step-core-term-active
  (implies (and (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (equal (car (finite-field-poly-division-step-core remainder divisor))
                  (let* ((k (- (finite-field-poly-degree remainder)
                               (finite-field-poly-degree divisor)))
                         (c (finite-field-div
                             (finite-field-poly-leading-coefficient remainder)
                             (finite-field-poly-leading-coefficient divisor))))
                    (finite-field-poly-monomial c k))))
  :hints (("Goal" :use ((:instance finite-field-poly-division-step-core-active))
           :in-theory (disable finite-field-poly-division-step-core))))

(defthm finite-field-poly-division-step-core-next-active
  (implies (and (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (equal (cdr (finite-field-poly-division-step-core remainder divisor))
                  (finite-field-poly-sub
                   remainder
                   (finite-field-poly-mul
                    (car (finite-field-poly-division-step-core remainder divisor))
                    divisor))))
  :hints (("Goal" :use ((:instance finite-field-poly-division-step-core-active))
           :in-theory (disable finite-field-poly-division-step-core))))

(defthm finite-field-poly-division-step-core-next-polynomial
  (implies (finite-field-canonical-polynomial-p remainder)
           (finite-field-polynomial-p
            (cdr (finite-field-poly-division-step-core remainder divisor))))
  :hints (("Goal"
           :cases ((and (consp remainder) (consp divisor)
                        (<= (finite-field-poly-degree divisor)
                            (finite-field-poly-degree remainder))))
           :use ((:instance finite-field-poly-division-step-core-next-active)
                 (:instance finite-field-canonical-polynomial-p-of-poly-sub
                            (x remainder)
                            (y (finite-field-poly-mul
                                (car (finite-field-poly-division-step-core remainder divisor))
                                divisor)))
                 (:instance finite-field-poly-normalize-when-canonical
                            (xs remainder)))
           :in-theory (disable finite-field-poly-division-step-core
                               finite-field-poly-sub-definition))))



(defthm finite-field-polynomial-p-of-poly-mul
  (finite-field-polynomial-p (finite-field-poly-mul x y))
  :hints (("Goal"
           :use ((:instance finite-field-canonical-polynomial-p-of-poly-mul
                            (x x) (y y))))))


(defthm finite-field-poly-mul-of-nil-left
  (equal (finite-field-poly-mul nil x) nil)
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance poly-mul-of-nil-left
                 (gfield::field-element-p gfield::finite-field-element-p)
                 (gfield::field-fix gfield::finite-field-fix)
                 (gfield::field-zero gfield::finite-field-zero)
                 (gfield::field-one gfield::finite-field-one)
                 (gfield::field-add gfield::finite-field-add)
                 (gfield::field-mul gfield::finite-field-mul)
                 (gfield::field-neg gfield::finite-field-neg)
                 (gfield::field-inv gfield::finite-field-inv)
                 (fix-coefficients finite-field-poly-fix-coefficients)
                 (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                 (normalize finite-field-poly-normalize)
                 (raw-add finite-field-poly-raw-add)
                 (raw-scale finite-field-poly-raw-scale)
                 (raw-mul finite-field-poly-raw-mul)
                 (poly-mul finite-field-poly-mul)))))


(defthm finite-field-poly-division-step-core-reconstruction
  (implies (finite-field-canonical-polynomial-p remainder)
           (equal (finite-field-poly-add
                   (finite-field-poly-mul
                    (car (finite-field-poly-division-step-core remainder divisor))
                    divisor)
                   (cdr (finite-field-poly-division-step-core remainder divisor)))
                  remainder))
  :rule-classes nil
  :hints (("Goal"
           :cases ((and (consp remainder) (consp divisor)
                        (<= (finite-field-poly-degree divisor)
                            (finite-field-poly-degree remainder))))
           :use ((:instance finite-field-poly-division-step-core-next-active)
                 (:instance finite-field-poly-add-left-to-poly-sub
                            (x (finite-field-poly-mul
                                (car (finite-field-poly-division-step-core remainder divisor))
                                divisor))
                            (y remainder)))
           :in-theory
           (e/d (finite-field-poly-division-step-core)
                (finite-field-poly-mul finite-field-poly-sub
                 finite-field-poly-add finite-field-poly-monomial
                 finite-field-poly-normalize finite-field-poly-raw-mul
                 finite-field-poly-raw-add finite-field-poly-sub-definition)))))

(defthm finite-field-len-of-poly-sub-strict-when-equal-len-and-leading-equal
  (implies (and (finite-field-canonical-polynomial-p x)
                (finite-field-canonical-polynomial-p y)
                (consp x) (consp y)
                (equal (len x) (len y))
                (equal (finite-field-poly-leading-coefficient x)
                       (finite-field-poly-leading-coefficient y)))
           (< (len (finite-field-poly-sub x y)) (len x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance len-of-poly-sub-strict-when-equal-len-and-leading-equal
                 (gfield::field-element-p gfield::finite-field-element-p)
                 (gfield::field-fix gfield::finite-field-fix)
                 (gfield::field-zero gfield::finite-field-zero)
                 (gfield::field-one gfield::finite-field-one)
                 (gfield::field-add gfield::finite-field-add)
                 (gfield::field-mul gfield::finite-field-mul)
                 (gfield::field-neg gfield::finite-field-neg)
                 (gfield::field-inv gfield::finite-field-inv)
                 (coefficient-list-p finite-field-coefficient-list-p)
                 (canonical-polynomial-p finite-field-canonical-polynomial-p)
                 (fix-coefficients finite-field-poly-fix-coefficients)
                 (trim-trailing-zeros finite-field-poly-trim-trailing-zeros)
                 (normalize finite-field-poly-normalize)
                 (raw-add finite-field-poly-raw-add)
                 (raw-neg finite-field-poly-raw-neg)
                 (poly-neg finite-field-poly-neg)
                 (poly-add finite-field-poly-add)
                 (poly-sub finite-field-poly-sub)
                 (poly-degree finite-field-poly-degree)
                 (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-equal-len-when-canonical-nonzero-and-equal-degree
  (implies (and (finite-field-canonical-polynomial-p first)
                (finite-field-canonical-polynomial-p second)
                (consp first) (consp second)
                (equal (finite-field-poly-degree first)
                       (finite-field-poly-degree second)))
           (equal (len first) (len second)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-when-canonical-nonzero
                            (p first))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p second)))
           :in-theory (disable finite-field-canonical-polynomial-p
                               finite-field-poly-degree))))

(defthm finite-field-poly-division-step-core-product-length-equal
  (implies (and (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (equal (len (finite-field-poly-mul
                        (car (finite-field-poly-division-step-core remainder divisor))
                        divisor))
                  (len remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-division-step-core-product-properties)
                 (:instance finite-field-equal-len-when-canonical-nonzero-and-equal-degree
                            (first (finite-field-poly-mul
                                    (car (finite-field-poly-division-step-core remainder divisor))
                                    divisor))
                            (second remainder)))
           :in-theory (disable finite-field-poly-mul
                               finite-field-poly-division-step-core))))

(defthm finite-field-poly-division-step-core-product-leading-equal
  (implies (and (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (equal (finite-field-poly-leading-coefficient
                   (finite-field-poly-mul
                    (car (finite-field-poly-division-step-core remainder divisor))
                    divisor))
                  (finite-field-poly-leading-coefficient remainder)))
  :hints (("Goal"
           :use ((:instance finite-field-poly-division-step-core-product-properties))
           :in-theory (disable finite-field-poly-mul
                               finite-field-poly-division-step-core))))

(defthm finite-field-poly-division-step-core-active-length-decreases
  (implies (and (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (< (len (cdr (finite-field-poly-division-step-core remainder divisor)))
              (len remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-division-step-core-next-active)
                 (:instance finite-field-poly-division-step-core-product-properties)
                 (:instance finite-field-poly-division-step-core-product-length-equal)
                 (:instance finite-field-poly-division-step-core-product-leading-equal)
                 (:instance finite-field-len-of-poly-sub-strict-when-equal-len-and-leading-equal
                            (x remainder)
                            (y (finite-field-poly-mul
                                (car (finite-field-poly-division-step-core remainder divisor))
                                divisor))))
           :in-theory (disable finite-field-poly-division-step-core
                               finite-field-poly-mul
                               finite-field-poly-sub-definition))))


(defthm finite-field-degree-less-when-canonical-nonzero-and-len-less
  (implies (and (finite-field-canonical-polynomial-p x)
                (finite-field-canonical-polynomial-p y)
                (consp x) (consp y)
                (< (len y) (len x)))
           (< (finite-field-poly-degree y)
              (finite-field-poly-degree x)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-when-canonical-nonzero
                            (p x))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p y)))
           :in-theory (disable finite-field-canonical-polynomial-p
                               finite-field-poly-degree))))


(defthm finite-field-poly-division-step-core-degree-decreases
  (implies (and (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (let ((next (cdr (finite-field-poly-division-step-core remainder divisor))))
             (or (not (consp next))
                 (< (finite-field-poly-degree next)
                    (finite-field-poly-degree remainder)))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((consp (cdr (finite-field-poly-division-step-core remainder divisor))))
           :use ((:instance finite-field-poly-division-step-core-active-length-decreases)
                 (:instance finite-field-poly-division-step-core-next-canonical)
                 (:instance finite-field-poly-normalize-when-canonical
                            (xs remainder))
                 (:instance finite-field-poly-normalize-when-canonical
                            (xs divisor))
                 (:instance finite-field-degree-less-when-canonical-nonzero-and-len-less
                            (x remainder)
                            (y (cdr (finite-field-poly-division-step-core remainder divisor))))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p remainder))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (cdr (finite-field-poly-division-step-core remainder divisor)))))
           :in-theory (disable finite-field-poly-division-step-core
                               finite-field-poly-division-step-core-active
                               finite-field-poly-division-step-core-inactive
                               finite-field-poly-degree))))

(defthm finite-field-poly-division-step-core-length-decreases
  (implies (and (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (finite-field-poly-degree divisor)
                    (finite-field-poly-degree remainder)))
           (< (len (cdr (finite-field-poly-division-step-core remainder divisor)))
              (len remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-division-step-core-active-length-decreases))
           :in-theory (disable finite-field-poly-division-step-core))))
