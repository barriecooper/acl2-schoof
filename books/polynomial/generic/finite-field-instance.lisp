(in-package "GPOLY")

(include-book "degree")
(include-book "../../field/finite-field-context")

; This is a logical GPOLY target over the jointly constrained finite-field
; operations.  The coding operations are intentionally not used here.
(defun finite-field-coefficient-list-p (xs)
  (if (atom xs)
      (null xs)
    (and (gfield::finite-field-element-p (car xs))
         (finite-field-coefficient-list-p (cdr xs)))))

(defun finite-field-polynomial-p (xs)
  (finite-field-coefficient-list-p xs))

(defun finite-field-canonical-polynomial-p (xs)
  (and (finite-field-coefficient-list-p xs)
       (or (not (consp xs))
           (not (equal (car (last xs))
                       (gfield::finite-field-zero))))))

(def-normalize-eval-instance
  finite-field-poly-fix-coefficients
  finite-field-poly-trim-trailing-zeros
  finite-field-poly-normalize
  finite-field-poly-eval
  gfield::finite-field-fix
  gfield::finite-field-zero
  gfield::finite-field-add
  gfield::finite-field-mul)

(defun finite-field-poly-coefficient (n polynomial)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n))
      (if (consp polynomial)
          (gfield::finite-field-fix (car polynomial))
        (gfield::finite-field-zero))
    (finite-field-poly-coefficient (1- (nfix n))
                                   (if (consp polynomial)
                                       (cdr polynomial)
                                     nil))))

(def-degree-instance
  finite-field-poly-degree finite-field-poly-leading-coefficient
  finite-field-poly-normalize gfield::finite-field-zero)

(def-add-instance
  finite-field-poly-raw-add finite-field-poly-add
  finite-field-poly-fix-coefficients finite-field-poly-normalize
  gfield::finite-field-add)

(def-neg-sub-instance
  finite-field-poly-raw-neg finite-field-poly-neg finite-field-poly-sub
  finite-field-poly-add finite-field-poly-normalize
  gfield::finite-field-neg)

(def-scale-instance
  finite-field-poly-raw-scale finite-field-poly-scale
  finite-field-poly-normalize gfield::finite-field-fix
  gfield::finite-field-mul)

(def-mul-instance
  finite-field-poly-raw-mul finite-field-poly-mul
  finite-field-poly-raw-add finite-field-poly-raw-scale
  finite-field-poly-normalize gfield::finite-field-zero)

(deftheory finite-field-poly-definition-theory
  '(finite-field-coefficient-list-p finite-field-polynomial-p
    finite-field-canonical-polynomial-p
    finite-field-poly-fix-coefficients
    finite-field-poly-trim-trailing-zeros finite-field-poly-normalize
    finite-field-poly-eval finite-field-poly-coefficient
    finite-field-poly-degree finite-field-poly-leading-coefficient
    finite-field-poly-raw-add finite-field-poly-add
    finite-field-poly-raw-neg finite-field-poly-neg finite-field-poly-sub
    finite-field-poly-raw-scale finite-field-poly-scale
    finite-field-poly-raw-mul finite-field-poly-mul))

(set-default-hints
 '((and stable-under-simplificationp
        (list :use (theory 'gfield::finite-field-context-instance-theory)
              :in-theory
              (list 'quote
                    (union-theories
                     (theory 'finite-field-poly-definition-theory)
                     (theory 'minimal-theory)))))))

; Every theorem below is transported from the authoritative GPOLY source.  The
; substitutions name both constrained field operations and transparent target
; definitions; no equality between the two constrained contexts is asserted.

(defthm finite-field-coefficient-list-p-of-poly-fix-coefficients
  (finite-field-coefficient-list-p
   (finite-field-poly-fix-coefficients xs))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        coefficient-list-p-of-fix-coefficients
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (coefficient-list-p finite-field-coefficient-list-p)
                        (fix-coefficients finite-field-poly-fix-coefficients)))
          (and stable-under-simplificationp
               (list :use (theory 'gfield::finite-field-context-instance-theory)
                     :in-theory
                     (list 'quote
                           (union-theories
                            (theory 'finite-field-poly-definition-theory)
                            (theory 'minimal-theory)))))))

(defthm finite-field-poly-fix-coefficients-when-coefficient-list-p
  (implies (finite-field-coefficient-list-p xs)
           (equal (finite-field-poly-fix-coefficients xs) xs))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        fix-coefficients-when-coefficient-list-p
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (coefficient-list-p finite-field-coefficient-list-p)
                        (fix-coefficients finite-field-poly-fix-coefficients)))))

(defthm finite-field-poly-fix-coefficients-idempotent
  (equal (finite-field-poly-fix-coefficients
          (finite-field-poly-fix-coefficients xs))
         (finite-field-poly-fix-coefficients xs))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        fix-coefficients-idempotent
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (fix-coefficients finite-field-poly-fix-coefficients)))))

(defthm finite-field-canonical-polynomial-p-of-poly-normalize
  (finite-field-canonical-polynomial-p
   (finite-field-poly-normalize xs))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        canonical-polynomial-p-of-normalize
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
                        (normalize finite-field-poly-normalize)))))

(defthm finite-field-poly-normalize-when-canonical
  (implies (finite-field-canonical-polynomial-p xs)
           (equal (finite-field-poly-normalize xs) xs))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        normalize-when-canonical
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
                        (normalize finite-field-poly-normalize)))))

(defthm finite-field-poly-normalize-idempotent
  (equal (finite-field-poly-normalize (finite-field-poly-normalize xs))
         (finite-field-poly-normalize xs))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        normalize-idempotent
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
                        (normalize finite-field-poly-normalize)))))

(defthm finite-field-len-of-poly-normalize
  (<= (len (finite-field-poly-normalize xs)) (len xs))
  :rule-classes :linear
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        len-of-normalize
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
                        (normalize finite-field-poly-normalize)))))

(defthm finite-field-element-p-of-poly-coefficient
  (gfield::finite-field-element-p
   (finite-field-poly-coefficient n polynomial))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        field-element-p-of-poly-coefficient
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (poly-coefficient finite-field-poly-coefficient)))))

(defthm finite-field-poly-coefficient-of-nfix
  (equal (finite-field-poly-coefficient (nfix n) polynomial)
         (finite-field-poly-coefficient n polynomial))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-coefficient-of-nfix
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (poly-coefficient finite-field-poly-coefficient)))))

(defthm finite-field-poly-coefficient-when-atom
  (implies (not (consp polynomial))
           (equal (finite-field-poly-coefficient n polynomial)
                  (gfield::finite-field-zero)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-coefficient-when-atom
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (poly-coefficient finite-field-poly-coefficient)))))

(defthm finite-field-poly-coefficient-of-cons-zero
  (equal (finite-field-poly-coefficient 0 (cons coefficient rest))
         (gfield::finite-field-fix coefficient))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-coefficient-of-cons-zero
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (poly-coefficient finite-field-poly-coefficient)))))

(defthm finite-field-poly-coefficient-of-cons-successor
  (equal (finite-field-poly-coefficient (+ 1 (nfix n))
                                        (cons coefficient rest))
         (finite-field-poly-coefficient n rest))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-coefficient-of-cons-successor
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (poly-coefficient finite-field-poly-coefficient)))))

(defthm finite-field-poly-coefficient-when-index-at-least-len
  (implies (<= (len polynomial) (nfix n))
           (equal (finite-field-poly-coefficient n polynomial)
                  (gfield::finite-field-zero)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        poly-coefficient-when-index-at-least-len
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (poly-coefficient finite-field-poly-coefficient)))))

(defthm finite-field-poly-coefficient-of-poly-fix-coefficients
  (equal (finite-field-poly-coefficient
          n (finite-field-poly-fix-coefficients polynomial))
         (finite-field-poly-coefficient n polynomial))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        poly-coefficient-of-fix-coefficients
                        (gfield::field-element-p gfield::finite-field-element-p)
                        (gfield::field-fix gfield::finite-field-fix)
                        (gfield::field-zero gfield::finite-field-zero)
                        (gfield::field-one gfield::finite-field-one)
                        (gfield::field-add gfield::finite-field-add)
                        (gfield::field-mul gfield::finite-field-mul)
                        (gfield::field-neg gfield::finite-field-neg)
                        (gfield::field-inv gfield::finite-field-inv)
                        (fix-coefficients finite-field-poly-fix-coefficients)
                        (poly-coefficient finite-field-poly-coefficient)))))

(defthm finite-field-poly-coefficient-of-poly-normalize
  (equal (finite-field-poly-coefficient
          n (finite-field-poly-normalize polynomial))
         (finite-field-poly-coefficient n polynomial))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        poly-coefficient-of-normalize
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
                        (poly-coefficient finite-field-poly-coefficient)))))

; Degree and leading-coefficient interface.
(defthm finite-field-poly-degree-of-poly-normalize
  (equal (finite-field-poly-degree (finite-field-poly-normalize p))
         (finite-field-poly-degree p))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-degree-of-normalize
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
                        (poly-degree finite-field-poly-degree)
                        (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-poly-leading-coefficient-of-poly-normalize
  (equal (finite-field-poly-leading-coefficient
          (finite-field-poly-normalize p))
         (finite-field-poly-leading-coefficient p))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        poly-leading-coefficient-of-normalize
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
                        (poly-degree finite-field-poly-degree)
                        (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-poly-degree-of-nil
  (equal (finite-field-poly-degree nil) -1)
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-degree-of-nil
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
                        (poly-degree finite-field-poly-degree)
                        (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-poly-leading-coefficient-of-nil
  (equal (finite-field-poly-leading-coefficient nil)
         (gfield::finite-field-zero))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-leading-coefficient-of-nil
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
                        (poly-degree finite-field-poly-degree)
                        (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-poly-degree-when-canonical-nonzero
  (implies (and (finite-field-canonical-polynomial-p p) (consp p))
           (equal (finite-field-poly-degree p) (1- (len p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        poly-degree-when-canonical-nonzero
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
                        (poly-degree finite-field-poly-degree)
                        (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-poly-leading-coefficient-when-canonical-nonzero
  (implies (and (finite-field-canonical-polynomial-p p) (consp p))
           (equal (finite-field-poly-leading-coefficient p)
                  (car (last p))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        poly-leading-coefficient-when-canonical-nonzero
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
                        (poly-degree finite-field-poly-degree)
                        (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-element-p-of-poly-leading-coefficient
  (gfield::finite-field-element-p
   (finite-field-poly-leading-coefficient p))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        field-element-p-of-poly-leading-coefficient
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
                        (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-poly-leading-coefficient-nonzero-when-canonical-nonzero
  (implies (and (finite-field-canonical-polynomial-p p) (consp p))
           (not (equal (finite-field-poly-leading-coefficient p)
                       (gfield::finite-field-zero))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance
                        poly-leading-coefficient-nonzero-when-canonical-nonzero
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
                        (poly-leading-coefficient finite-field-poly-leading-coefficient)))))

(defthm finite-field-integerp-of-poly-degree
  (integerp (finite-field-poly-degree p))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance integerp-of-poly-degree
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
                        (poly-degree finite-field-poly-degree)))))

; Canonical closure and a narrow coefficient interface for arithmetic.
(defthm finite-field-canonical-polynomial-p-of-poly-add
  (finite-field-canonical-polynomial-p (finite-field-poly-add x y))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance canonical-polynomial-p-of-poly-add
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
                        (poly-add finite-field-poly-add)))))

(defthm finite-field-canonical-polynomial-p-of-poly-neg
  (finite-field-canonical-polynomial-p (finite-field-poly-neg x))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance canonical-polynomial-p-of-poly-neg
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
                        (raw-neg finite-field-poly-raw-neg)
                        (poly-neg finite-field-poly-neg)))))

(defthm finite-field-canonical-polynomial-p-of-poly-sub
  (finite-field-canonical-polynomial-p (finite-field-poly-sub x y))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance canonical-polynomial-p-of-poly-sub
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
                        (poly-add finite-field-poly-add)
                        (raw-neg finite-field-poly-raw-neg)
                        (poly-neg finite-field-poly-neg)
                        (poly-sub finite-field-poly-sub)))))

(defthm finite-field-canonical-polynomial-p-of-poly-scale
  (finite-field-canonical-polynomial-p
   (finite-field-poly-scale a x))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance canonical-polynomial-p-of-poly-scale
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
                        (raw-scale finite-field-poly-raw-scale)
                        (poly-scale finite-field-poly-scale)))))

(defthm finite-field-canonical-polynomial-p-of-poly-mul
  (finite-field-canonical-polynomial-p (finite-field-poly-mul x y))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance canonical-polynomial-p-of-poly-mul
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
                        (raw-scale finite-field-poly-raw-scale)
                        (raw-mul finite-field-poly-raw-mul)
                        (poly-mul finite-field-poly-mul)))))

(defthm finite-field-poly-coefficient-of-poly-add
  (equal (finite-field-poly-coefficient
          n (finite-field-poly-add first second))
         (gfield::finite-field-add
          (finite-field-poly-coefficient n first)
          (finite-field-poly-coefficient n second)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-coefficient-of-poly-add
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
                        (poly-coefficient finite-field-poly-coefficient)
                        (raw-add finite-field-poly-raw-add)
                        (poly-add finite-field-poly-add)))))

(defthm finite-field-poly-coefficient-of-poly-scale
  (equal (finite-field-poly-coefficient
          n (finite-field-poly-scale scalar polynomial))
         (gfield::finite-field-mul
          scalar (finite-field-poly-coefficient n polynomial)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-coefficient-of-poly-scale
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
                        (poly-coefficient finite-field-poly-coefficient)
                        (raw-scale finite-field-poly-raw-scale)
                        (poly-scale finite-field-poly-scale)))))

(local
 (defun finite-field-poly-convolution-sum-aux
     (count total first second)
   (declare (xargs :measure (nfix count)))
   (if (zp (nfix count))
       (gfield::finite-field-mul
        (finite-field-poly-coefficient 0 first)
        (finite-field-poly-coefficient (nfix total) second))
     (gfield::finite-field-add
      (finite-field-poly-convolution-sum-aux
       (1- (nfix count)) total first second)
      (gfield::finite-field-mul
       (finite-field-poly-coefficient (nfix count) first)
       (finite-field-poly-coefficient
        (- (nfix total) (nfix count)) second))))))

(local
 (defun finite-field-poly-convolution-sum (n first second)
   (finite-field-poly-convolution-sum-aux
    (nfix n) (nfix n) first second)))

(set-default-hints nil)

(local
 (deftheory finite-field-poly-with-convolution-definition-theory
   (union-theories
    (theory 'finite-field-poly-definition-theory)
    '(finite-field-poly-convolution-sum-aux
      finite-field-poly-convolution-sum))))

(set-default-hints
 '((and stable-under-simplificationp
        (list :use (theory 'gfield::finite-field-context-instance-theory)
              :in-theory
              (list 'quote
                    (union-theories
                     (theory
                      'finite-field-poly-with-convolution-definition-theory)
                     (theory 'minimal-theory)))))))

(local
 (defthm finite-field-poly-coefficient-of-poly-mul-via-convolution
   (equal (finite-field-poly-coefficient
           n (finite-field-poly-mul first second))
          (finite-field-poly-convolution-sum n first second))
   :hints
   (("Goal"
     :in-theory (theory 'minimal-theory)
     :by (:functional-instance
          poly-coefficient-of-poly-mul
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
          (poly-coefficient finite-field-poly-coefficient)
          (raw-add finite-field-poly-raw-add)
          (raw-scale finite-field-poly-raw-scale)
          (raw-mul finite-field-poly-raw-mul)
          (poly-mul finite-field-poly-mul)
          (poly-convolution-sum-aux
           finite-field-poly-convolution-sum-aux)
          (poly-convolution-sum finite-field-poly-convolution-sum))))))

(set-default-hints nil)

(set-default-hints
 '((and stable-under-simplificationp
        (list :use (theory 'gfield::finite-field-context-instance-theory)
              :in-theory
              (list 'quote
                    (union-theories
                     (theory 'finite-field-poly-definition-theory)
                     (theory 'minimal-theory)))))))

; A bounded multiplication coefficient endpoint keeps the proof-only
; convolution target local instead of adding it to the public core API.
(defthm finite-field-poly-coefficient-zero-of-poly-mul
  (equal (finite-field-poly-coefficient
          0 (finite-field-poly-mul first second))
         (gfield::finite-field-mul
          (finite-field-poly-coefficient 0 first)
          (finite-field-poly-coefficient 0 second)))
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-coefficient-of-poly-mul-via-convolution
                  (n 0)))
           :in-theory (enable finite-field-poly-convolution-sum
                              finite-field-poly-convolution-sum-aux))))

(defthm finite-field-poly-add-of-nil-left
  (equal (finite-field-poly-add nil x)
         (finite-field-poly-normalize x))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-add-of-nil-left
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
                        (poly-add finite-field-poly-add)))))

(defthm finite-field-poly-add-commutative
  (equal (finite-field-poly-add x y) (finite-field-poly-add y x))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-add-commutative
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
                        (poly-add finite-field-poly-add)))))

(defthm finite-field-poly-add-associative
  (equal (finite-field-poly-add (finite-field-poly-add x y) z)
         (finite-field-poly-add x (finite-field-poly-add y z)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-add-associative-total
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
                        (poly-add finite-field-poly-add)))))

(defthm finite-field-poly-add-inverse-right
  (equal (finite-field-poly-add x (finite-field-poly-neg x)) nil)
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                    :by (:functional-instance poly-add-inverse-right-total
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
                        (poly-neg finite-field-poly-neg)))))

(set-default-hints nil)

; Opaque public-interface regressions: downstream books need only these named
; results, not the generated recursive implementations.
(defthm finite-field-poly-normalize-canonical-minimal-theory-client
  (finite-field-canonical-polynomial-p
   (finite-field-poly-normalize x))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          finite-field-canonical-polynomial-p-of-poly-normalize
                          (xs x)))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-coefficient-normalize-minimal-theory-client
  (equal (finite-field-poly-coefficient
          n (finite-field-poly-normalize x))
         (finite-field-poly-coefficient n x))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          finite-field-poly-coefficient-of-poly-normalize
                          (polynomial x)))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-add-canonical-minimal-theory-client
  (finite-field-canonical-polynomial-p (finite-field-poly-add x y))
  :rule-classes nil
  :hints (("Goal" :use finite-field-canonical-polynomial-p-of-poly-add
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-degree-leading-minimal-theory-client
  (and (equal (finite-field-poly-degree nil) -1)
       (equal (finite-field-poly-leading-coefficient nil)
              (gfield::finite-field-zero)))
  :rule-classes nil
  :hints (("Goal" :use (finite-field-poly-degree-of-nil
                         finite-field-poly-leading-coefficient-of-nil)
           :in-theory (theory 'minimal-theory))))



(defthm finite-field-poly-mul-of-nil-left
  (equal (finite-field-poly-mul nil x) nil)
  :hints (("Goal"
           :in-theory (enable finite-field-poly-mul
                              finite-field-poly-raw-mul
                              finite-field-poly-normalize
                              finite-field-poly-trim-trailing-zeros
                              finite-field-poly-fix-coefficients))))

(defthm finite-field-canonical-polynomial-p-implies-polynomial-p
  (implies (finite-field-canonical-polynomial-p xs)
           (finite-field-polynomial-p xs))
  :hints (("Goal"
           :in-theory (enable finite-field-canonical-polynomial-p
                              finite-field-polynomial-p))))

(local
 (deftheory finite-field-poly-distributivity-instance-theory
   (union-theories
    (theory 'finite-field-poly-definition-theory)
    (theory 'minimal-theory))))

(defthm finite-field-poly-mul-right-distributive
  (equal (finite-field-poly-mul (finite-field-poly-add x y) z)
         (finite-field-poly-add (finite-field-poly-mul x z)
                                (finite-field-poly-mul y z)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :by (:functional-instance poly-mul-right-distributive
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
                 (poly-mul finite-field-poly-mul)))
          (and stable-under-simplificationp
               (list :use (theory 'gfield::finite-field-context-instance-theory)
                     :in-theory
                     (list 'quote
                           (theory 'finite-field-poly-distributivity-instance-theory))))))

(defthm finite-field-len-of-poly-fix-coefficients
  (equal (len (finite-field-poly-fix-coefficients xs)) (len xs))
  :hints (("Goal" :induct (finite-field-poly-fix-coefficients xs)
           :in-theory (enable finite-field-poly-fix-coefficients))))

(defthm finite-field-len-of-poly-raw-add
  (equal (len (finite-field-poly-raw-add x y))
         (max (len x) (len y)))
  :hints (("Goal" :induct (finite-field-poly-raw-add x y)
           :in-theory (enable finite-field-poly-raw-add
                              finite-field-poly-fix-coefficients))))

(defthm finite-field-len-of-poly-raw-neg
  (equal (len (finite-field-poly-raw-neg x)) (len x))
  :rule-classes nil
  :hints (("Goal" :induct (finite-field-poly-raw-neg x)
           :in-theory (enable finite-field-poly-raw-neg))))

(verify-guards finite-field-coefficient-list-p)
(verify-guards finite-field-polynomial-p)
(verify-guards finite-field-canonical-polynomial-p)
(verify-guards finite-field-poly-fix-coefficients)
(verify-guards finite-field-poly-trim-trailing-zeros)
(verify-guards finite-field-poly-normalize)
(verify-guards finite-field-poly-eval)
(verify-guards finite-field-poly-coefficient)
(verify-guards finite-field-poly-degree)
(verify-guards finite-field-poly-leading-coefficient)
(verify-guards finite-field-poly-raw-add)
(verify-guards finite-field-poly-add)
(verify-guards finite-field-poly-raw-neg)
(verify-guards finite-field-poly-neg)
(verify-guards finite-field-poly-sub)
(verify-guards finite-field-poly-raw-scale)
(verify-guards finite-field-poly-scale)
(verify-guards finite-field-poly-raw-mul)
(verify-guards finite-field-poly-mul)

(set-default-hints nil)
