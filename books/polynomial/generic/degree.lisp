(in-package "GPOLY")
(include-book "const")

; Formal degree and leading coefficient are structural properties of the
; normalized dense representation, not properties recovered from evaluation.
(verify-guards fix-coefficients)
(verify-guards trim-trailing-zeros)
(verify-guards normalize)
(def-degree-instance poly-degree poly-leading-coefficient normalize
                     gfield::field-zero)

(defthm poly-degree-of-normalize
  (equal (poly-degree (normalize p)) (poly-degree p)))

(defthm poly-leading-coefficient-of-normalize
  (equal (poly-leading-coefficient (normalize p))
         (poly-leading-coefficient p)))

(defthm poly-degree-of-nil
  (equal (poly-degree nil) -1))

(defthm poly-leading-coefficient-of-nil
  (equal (poly-leading-coefficient nil) (gfield::field-zero)))

(defthm poly-degree-when-canonical-nonzero
  (implies (and (canonical-polynomial-p p) (consp p))
           (equal (poly-degree p) (1- (len p)))))

(defthm poly-leading-coefficient-when-canonical-nonzero
  (implies (and (canonical-polynomial-p p) (consp p))
           (equal (poly-leading-coefficient p) (car (last p)))))

(defthm poly-leading-coefficient-nonzero-when-canonical-nonzero
  (implies (and (canonical-polynomial-p p) (consp p))
           (not (equal (poly-leading-coefficient p)
                       (gfield::field-zero)))))

(defthm integerp-of-poly-degree
  (integerp (poly-degree p))
  :rule-classes :type-prescription)

(defthm poly-degree-lower-bound
  (<= -1 (poly-degree p))
  :rule-classes :linear)

(defthm poly-degree-equal-minus-one
  (equal (equal (poly-degree p) -1)
         (equal (normalize p) nil)))

(defthm natp-of-poly-degree-when-normalize-nonzero
  (implies (consp (normalize p))
           (natp (poly-degree p)))
  :rule-classes :type-prescription)

(defthm field-element-p-of-poly-leading-coefficient
  (gfield::field-element-p (poly-leading-coefficient p)))

(defthm poly-leading-coefficient-equal-zero
  (equal (equal (poly-leading-coefficient p) (gfield::field-zero))
         (equal (normalize p) nil)))

(defthm poly-degree-less-than-input-length
  (implies (consp (normalize p))
           (< (poly-degree p) (len p)))
  :rule-classes :linear)

(defthm poly-degree-of-const
  (equal (poly-degree (const a))
         (if (equal (gfield::field-fix a) (gfield::field-zero)) -1 0))
  :hints (("Goal" :in-theory (enable const))))

(defthm poly-leading-coefficient-of-const
  (equal (poly-leading-coefficient (const a))
         (gfield::field-fix a))
  :hints (("Goal" :in-theory (enable const))))

(defthm poly-degree-of-polynomial-one
  (equal (poly-degree (polynomial-one)) 0))

(defthm poly-leading-coefficient-of-polynomial-one
  (equal (poly-leading-coefficient (polynomial-one))
         (gfield::field-one)))

(defthm poly-degree-of-normalized-singleton
  (equal (poly-degree (normalize (list a)))
         (if (equal (gfield::field-fix a) (gfield::field-zero)) -1 0)))

(defthm poly-leading-coefficient-of-normalized-singleton
  (equal (poly-leading-coefficient (normalize (list a)))
         (gfield::field-fix a)))

(verify-guards poly-degree)
(verify-guards poly-leading-coefficient)
