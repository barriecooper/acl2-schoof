(in-package "GPOLY")
(include-book "monomial")

(verify-guards gfield::field-div)
(verify-guards raw-add)
(verify-guards poly-add)
(verify-guards raw-neg)
(verify-guards poly-neg)
(verify-guards poly-sub)
(verify-guards raw-scale)
(verify-guards raw-mul)
(verify-guards poly-mul)

; A result is the transparent pair (quotient-term . next-remainder).
(defun poly-division-step-core (remainder divisor)
  (if (and (consp remainder)
           (consp divisor)
           (<= (poly-degree divisor) (poly-degree remainder)))
      (let* ((k (- (poly-degree remainder) (poly-degree divisor)))
             (c (gfield::field-div (poly-leading-coefficient remainder)
                                   (poly-leading-coefficient divisor)))
             (term (monomial c k)))
        (cons term (poly-sub remainder (poly-mul term divisor))))
    (cons nil remainder)))

(defun poly-division-step (remainder divisor)
  (let ((remainder (normalize remainder))
        (divisor (normalize divisor)))
    (poly-division-step-core remainder divisor)))

(defun poly-division-step-term (remainder divisor)
  (car (poly-division-step remainder divisor)))

(defun poly-division-step-next (remainder divisor)
  (cdr (poly-division-step remainder divisor)))

(defthm field-div-nonzero
  (implies (and (not (equal (gfield::field-fix x) (gfield::field-zero)))
                (not (equal (gfield::field-fix y) (gfield::field-zero))))
           (not (equal (gfield::field-div x y) (gfield::field-zero))))
  :hints (("Goal" :in-theory (enable gfield::field-div))))

(defthm field-div-mul-denominator
  (implies (not (equal (gfield::field-fix y) (gfield::field-zero)))
           (equal (gfield::field-mul (gfield::field-div x y) y)
                  (gfield::field-fix x)))
  :hints (("Goal"
           :use ((:instance gfield::field-mul-inverse-left (x y)))
           :in-theory (enable gfield::field-div
                              gfield::field-mul-associative))))

(defthm last-of-raw-neg
  (implies (consp x)
           (equal (car (last (raw-neg x)))
                  (gfield::field-neg (car (last x)))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-neg x) :in-theory (enable raw-neg))))

(defthm consp-of-raw-neg
  (equal (consp (raw-neg x)) (consp x))
  :hints (("Goal" :in-theory (enable raw-neg))))

(defthm last-of-raw-add-when-equal-len
  (implies (and (consp x) (consp y) (equal (len x) (len y)))
           (equal (car (last (raw-add x y)))
                  (gfield::field-add (car (last x)) (car (last y)))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-add x y) :in-theory (enable raw-add))))

(defthm consp-of-raw-add-left
  (implies (consp x) (consp (raw-add x y)))
  :hints (("Goal" :in-theory (enable raw-add))))

(defthm canonical-polynomial-p-of-raw-neg-when-canonical
  (implies (canonical-polynomial-p x)
           (canonical-polynomial-p (raw-neg x)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance last-of-raw-neg))
           :in-theory (enable canonical-polynomial-p equal-field-neg-zero))))

(defthm poly-neg-when-canonical
  (implies (canonical-polynomial-p x)
           (equal (poly-neg x) (raw-neg x)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance canonical-polynomial-p-of-raw-neg-when-canonical)
                 (:instance normalize-when-canonical (xs (raw-neg x))))
           :in-theory (enable poly-neg))))

(defthm len-of-trim-strict-when-last-zero
  (implies (and (coefficient-list-p x)
                (consp x)
                (equal (car (last x)) (gfield::field-zero)))
           (< (len (trim-trailing-zeros x)) (len x)))
  :rule-classes :linear
  :hints (("Goal" :induct (trim-trailing-zeros x)
           :in-theory (enable trim-trailing-zeros))))

(defthm len-of-normalize-strict-when-last-zero
  (implies (and (coefficient-list-p x)
                (consp x)
                (equal (car (last x)) (gfield::field-zero)))
           (< (len (normalize x)) (len x)))
  :rule-classes :linear
  :hints (("Goal"
           :use ((:instance len-of-trim-strict-when-last-zero))
           :in-theory (enable normalize))))

(defthm poly-sub-of-canonical-operands
  (implies (and (canonical-polynomial-p x)
                (canonical-polynomial-p y))
           (equal (poly-sub x y)
                  (normalize (raw-add x (raw-neg y)))))
  :hints (("Goal"
           :use ((:instance poly-neg-when-canonical (x y)))
           :in-theory (enable poly-sub poly-add))))

(defthm last-of-raw-sub-zero-when-equal-len-and-leading-equal
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (consp x) (consp y)
                (equal (len x) (len y))
                (equal (car (last x)) (car (last y))))
           (equal (car (last (raw-add x (raw-neg y))))
                  (gfield::field-zero)))
  :hints (("Goal"
           :use ((:instance last-of-raw-neg (x y))
                 (:instance last-of-raw-add-when-equal-len
                            (x x) (y (raw-neg y))))
           :in-theory (disable raw-neg raw-add))))

(defthm len-of-poly-sub-strict-when-equal-len-and-last-equal
  (implies (and (canonical-polynomial-p x)
                (canonical-polynomial-p y)
                (consp x)
                (consp y)
                (equal (len x) (len y))
                (equal (car (last x)) (car (last y))))
           (< (len (poly-sub x y)) (len x)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (e/d (poly-sub-of-canonical-operands)
                (poly-sub-definition (:definition poly-sub) poly-add poly-neg
                 (:definition normalize) (:definition trim-trailing-zeros)
                 raw-add raw-add-commutative)))))

(defthm len-of-poly-sub-strict-when-equal-len-and-leading-equal
  (implies (and (canonical-polynomial-p x)
                (canonical-polynomial-p y)
                (consp x) (consp y)
                (equal (len x) (len y))
                (equal (poly-leading-coefficient x)
                       (poly-leading-coefficient y)))
           (< (len (poly-sub x y)) (len x)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance len-of-poly-sub-strict-when-equal-len-and-last-equal)
                 (:instance poly-leading-coefficient-when-canonical-nonzero
                            (p x))
                 (:instance poly-leading-coefficient-when-canonical-nonzero
                            (p y))))))

(defthm poly-division-step-core-inactive
  (implies (or (not (consp remainder))
               (not (consp divisor))
               (< (poly-degree remainder) (poly-degree divisor)))
           (equal (poly-division-step-core remainder divisor)
                  (cons nil remainder)))
  :hints (("Goal" :in-theory (enable poly-division-step-core))))

(defthm divisor-leading-coefficient-nonzero-for-division-step
  (implies (and (canonical-polynomial-p divisor) (consp divisor))
           (not (equal (poly-leading-coefficient divisor)
                       (gfield::field-zero)))))

(defthm divisor-leading-coefficient-inverse-nonzero-for-division-step
  (implies (and (canonical-polynomial-p divisor) (consp divisor))
           (not (equal (gfield::field-inv
                        (poly-leading-coefficient divisor))
                       (gfield::field-zero))))
  :hints (("Goal"
           :use ((:instance gfield::field-inv-nonzero
                            (x (poly-leading-coefficient divisor)))
                 (:instance field-element-p-of-poly-leading-coefficient
                            (p divisor))
                 (:instance divisor-leading-coefficient-nonzero-for-division-step)))))

(defthm poly-division-step-core-term-properties
  (implies (and (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (poly-degree divisor) (poly-degree remainder)))
           (let ((term (car (poly-division-step-core remainder divisor))))
             (and (canonical-polynomial-p term)
                  (consp term)
                  (equal (poly-degree term)
                         (- (poly-degree remainder) (poly-degree divisor)))
                  (equal (poly-leading-coefficient term)
                         (gfield::field-div
                          (poly-leading-coefficient remainder)
                          (poly-leading-coefficient divisor))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-degree-of-monomial
                            (a (gfield::field-div
                                (poly-leading-coefficient remainder)
                                (poly-leading-coefficient divisor)))
                            (n (- (poly-degree remainder)
                                  (poly-degree divisor))))
                 (:instance poly-leading-coefficient-of-monomial
                            (a (gfield::field-div
                                (poly-leading-coefficient remainder)
                                (poly-leading-coefficient divisor)))
                            (n (- (poly-degree remainder)
                                  (poly-degree divisor))))
                 (:instance field-div-nonzero
                            (x (poly-leading-coefficient remainder))
                            (y (poly-leading-coefficient divisor)))
                 (:instance poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p remainder))
                 (:instance poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p divisor))
                 (:instance field-element-p-of-poly-leading-coefficient
                            (p remainder))
                 (:instance field-element-p-of-poly-leading-coefficient
                            (p divisor)))
           :in-theory (enable poly-division-step-core))))

(defthm poly-division-step-core-product-properties
  (implies (and (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (poly-degree divisor) (poly-degree remainder)))
           (let* ((term (car (poly-division-step-core remainder divisor)))
                  (product (poly-mul term divisor)))
             (and (canonical-polynomial-p product)
                  (consp product)
                  (equal (poly-degree product) (poly-degree remainder))
                  (equal (poly-leading-coefficient product)
                         (poly-leading-coefficient remainder)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-division-step-core-term-properties)
                 (:instance poly-degree-of-poly-mul
                            (f (car (poly-division-step-core remainder divisor)))
                            (g divisor))
                 (:instance consp-of-poly-mul-when-canonical-nonzero
                            (f (car (poly-division-step-core remainder divisor)))
                            (g divisor))
                 (:instance poly-leading-coefficient-of-poly-mul
                            (f (car (poly-division-step-core remainder divisor)))
                            (g divisor))
                 (:instance field-div-mul-denominator
                            (x (poly-leading-coefficient remainder))
                            (y (poly-leading-coefficient divisor)))
                 (:instance field-element-p-of-poly-leading-coefficient
                            (p divisor))
                 (:instance field-element-p-of-poly-leading-coefficient
                            (p remainder))
                 (:instance poly-leading-coefficient-nonzero-when-canonical-nonzero
                            (p divisor)))
           :in-theory
           (disable poly-mul monomial normalize raw-mul raw-add
                    raw-add-commutative gfield::field-mul-commutative))))

(defthm poly-division-step-core-next-canonical
  (implies (canonical-polynomial-p remainder)
           (canonical-polynomial-p
            (cdr (poly-division-step-core remainder divisor))))
  :hints (("Goal" :in-theory (enable poly-division-step-core))))

(defthm poly-division-step-core-next-polynomial
  (implies (canonical-polynomial-p remainder)
           (polynomial-p (cdr (poly-division-step-core remainder divisor)))))

(defthm poly-division-step-core-next-true-listp
  (implies (canonical-polynomial-p remainder)
           (true-listp (cdr (poly-division-step-core remainder divisor)))))

(defthm poly-division-step-core-degree-decreases
  (implies (and (canonical-polynomial-p remainder)
                (canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (poly-degree divisor) (poly-degree remainder)))
           (let ((next (cdr (poly-division-step-core remainder divisor))))
             (or (not (consp next))
                 (< (poly-degree next) (poly-degree remainder)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-division-step-core-product-properties)
                 (:instance len-of-poly-sub-strict-when-equal-len-and-leading-equal
                            (x remainder)
                            (y (poly-mul
                                (car (poly-division-step-core remainder divisor))
                                divisor)))
                 (:instance poly-degree-when-canonical-nonzero (p remainder))
                 (:instance poly-degree-when-canonical-nonzero
                            (p (cdr (poly-division-step-core remainder divisor)))))
           :in-theory (enable poly-division-step-core))))

(defthm poly-add-left-to-poly-sub
  (implies (and (polynomial-p x) (canonical-polynomial-p y))
           (equal (poly-add x (poly-sub y x)) y))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-add-associative (x x) (y y) (z (poly-neg x)))
                 (:instance poly-add-associative (x y) (y x) (z (poly-neg x)))
                 (:instance poly-add-commutative (x x) (y y))
                 (:instance poly-add-inverse-right (x x)))
           :in-theory (disable poly-add-associative poly-add-commutative))))

(defthm poly-division-step-core-reconstruction
  (implies (canonical-polynomial-p remainder)
           (equal (poly-add
                   (poly-mul (car (poly-division-step-core remainder divisor))
                             divisor)
                   (cdr (poly-division-step-core remainder divisor)))
                  remainder))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-add-left-to-poly-sub
                            (x (poly-mul
                                (car (poly-division-step-core remainder divisor))
                                divisor))
                            (y remainder)))
           :in-theory
           (e/d (poly-division-step-core)
                (poly-mul poly-sub poly-add monomial normalize raw-mul
                 raw-add raw-add-commutative poly-sub-definition)))))

(defthm poly-division-step-inactive-zero-remainder
  (equal (poly-division-step nil divisor) (cons nil nil))
  :hints (("Goal" :in-theory (enable poly-division-step))))

(defthm poly-division-step-inactive-zero-divisor
  (equal (poly-division-step remainder nil)
         (cons nil (normalize remainder)))
  :hints (("Goal" :in-theory (enable poly-division-step))))

(defthm poly-division-step-inactive-larger-divisor
  (implies (< (poly-degree remainder) (poly-degree divisor))
           (equal (poly-division-step remainder divisor)
                  (cons nil (normalize remainder))))
  :hints (("Goal" :in-theory (enable poly-division-step))))

(defthm poly-division-step-reconstruction
  (equal (poly-add (poly-mul (poly-division-step-term remainder divisor)
                             (normalize divisor))
                   (poly-division-step-next remainder divisor))
         (normalize remainder))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-division-step-core-reconstruction
                            (remainder (normalize remainder))
                            (divisor (normalize divisor))))
           :in-theory
           (e/d (poly-division-step-term poly-division-step-next
                                         poly-division-step)
                (poly-division-step-core poly-mul poly-sub poly-add monomial
                 normalize raw-mul raw-add raw-add-commutative
                 poly-sub-definition)))))

(defthm poly-division-step-degree-decreases
  (implies (and (consp (normalize remainder))
                (consp (normalize divisor))
                (<= (poly-degree divisor) (poly-degree remainder)))
           (let ((next (poly-division-step-next remainder divisor)))
             (or (not (consp next))
                 (< (poly-degree next) (poly-degree remainder)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-division-step-core-degree-decreases
                            (remainder (normalize remainder))
                            (divisor (normalize divisor))))
           :in-theory
           (e/d (poly-division-step-next poly-division-step)
                (poly-division-step-core poly-mul poly-sub poly-add monomial
                 normalize raw-mul raw-add raw-add-commutative
                 poly-sub-definition)))))

; Focused symbolic totality regressions (the constrained field has no evaluator).
(defthm poly-division-step-regression-malformed-atom
  (equal (poly-division-step 'malformed divisor) (cons nil nil))
  :hints (("Goal" :in-theory (enable poly-division-step))))

(verify-guards poly-division-step-core)
(verify-guards poly-division-step)
(verify-guards poly-division-step-term)
(verify-guards poly-division-step-next)
