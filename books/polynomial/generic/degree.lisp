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

(defthm field-element-p-of-poly-leading-coefficient
  (gfield::field-element-p (poly-leading-coefficient p)))

(defthm poly-leading-coefficient-nonzero-when-canonical-nonzero
  (implies (and (canonical-polynomial-p p) (consp p))
           (not (equal (poly-leading-coefficient p)
                       (gfield::field-zero)))))

; The top convolution coefficient is the ordered product of the two input
; leading coefficients.  The field no-zero-divisor law therefore makes the
; complete raw convolution canonical, so normalization removes nothing.
(defthm field-element-p-of-last-when-coefficient-list-p
  (implies (and (coefficient-list-p p)
                (consp p))
           (gfield::field-element-p (car (last p))))
  :rule-classes nil
  :hints (("Goal" :induct (coefficient-list-p p))))

(defthm canonical-polynomial-p-of-raw-mul-when-nonzero
  (implies (and (canonical-polynomial-p f)
                (canonical-polynomial-p g)
                (consp f)
                (consp g))
           (canonical-polynomial-p (raw-mul f g)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-leading-coefficient-of-raw-mul)
                 (:instance field-element-p-of-last-when-coefficient-list-p
                            (p f))
                 (:instance field-element-p-of-last-when-coefficient-list-p
                            (p g)))
           :in-theory (e/d (canonical-polynomial-p)
                           (raw-mul raw-add raw-scale)))))

(defthm normalize-of-raw-mul-when-canonical-nonzero
  (implies (and (canonical-polynomial-p f)
                (canonical-polynomial-p g)
                (consp f)
                (consp g))
           (equal (normalize (raw-mul f g))
                  (raw-mul f g)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance canonical-polynomial-p-of-raw-mul-when-nonzero)
                 (:instance normalize-when-canonical
                            (xs (raw-mul f g)))))))

(defthm poly-leading-coefficient-of-poly-mul
  (implies (and (canonical-polynomial-p f)
                (canonical-polynomial-p g)
                (consp f)
                (consp g))
           (equal (poly-leading-coefficient (poly-mul f g))
                  (gfield::field-mul (poly-leading-coefficient f)
                                     (poly-leading-coefficient g))))
  :hints (("Goal"
           :use ((:instance raw-leading-coefficient-of-raw-mul)
                 (:instance normalize-of-raw-mul-when-canonical-nonzero))
           :in-theory (enable poly-mul))))

(defthm poly-degree-of-poly-mul
  (implies (and (canonical-polynomial-p f)
                (canonical-polynomial-p g)
                (consp f)
                (consp g))
           (equal (poly-degree (poly-mul f g))
                  (+ (poly-degree f) (poly-degree g))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance len-of-raw-mul (x f) (y g))
                 (:instance normalize-of-raw-mul-when-canonical-nonzero))
           :in-theory (e/d (poly-mul)
                           (len-of-raw-mul)))))

(defthm consp-of-poly-mul-when-canonical-nonzero
  (implies (and (canonical-polynomial-p f)
                (canonical-polynomial-p g)
                (consp f)
                (consp g))
           (consp (poly-mul f g)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance normalize-of-raw-mul-when-canonical-nonzero))
           :in-theory (enable poly-mul))))

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

(defthm poly-leading-coefficient-equal-zero
  (equal (equal (poly-leading-coefficient p) (gfield::field-zero))
         (equal (normalize p) nil)))

(defthm poly-leading-coefficient-of-poly-scale-when-nonzero
  (implies (and (not (equal (gfield::field-fix scalar)
                            (gfield::field-zero)))
                (consp (normalize poly)))
           (equal (poly-leading-coefficient (poly-scale scalar poly))
                  (gfield::field-mul scalar
                                     (poly-leading-coefficient poly))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance raw-leading-coefficient-of-raw-scale
                     (a scalar) (x (normalize poly)))
          (:instance normalize-of-raw-scale-when-canonical-nonzero
                     (a scalar) (x (normalize poly)))
          (:instance poly-leading-coefficient-when-canonical-nonzero
                     (p (normalize poly)))
          (:instance poly-leading-coefficient-when-canonical-nonzero
                     (p (raw-scale scalar (normalize poly)))))
    :in-theory (e/d (poly-scale canonical-polynomial-p)
                    (poly-leading-coefficient-when-canonical-nonzero
                     normalize poly-leading-coefficient)))))

(defthm poly-leading-coefficient-of-poly-scale-when-scalar-zero
  (implies (equal (gfield::field-fix scalar) (gfield::field-zero))
           (equal (poly-leading-coefficient (poly-scale scalar poly))
                  (gfield::field-mul scalar
                                     (poly-leading-coefficient poly))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-scale-when-field-fix-zero
                     (a scalar) (x poly))
          (:instance equal-field-mul-zero
                     (a scalar) (x (poly-leading-coefficient poly))))
    :in-theory (enable poly-leading-coefficient))))

(defthm poly-leading-coefficient-of-poly-scale-when-poly-zero
  (implies (not (consp (normalize poly)))
           (equal (poly-leading-coefficient (poly-scale scalar poly))
                  (gfield::field-mul scalar
                                     (poly-leading-coefficient poly))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-scale-when-normalize-nil
                     (a scalar) (x poly))
          (:instance poly-leading-coefficient-equal-zero (p poly)))
    :in-theory (enable poly-leading-coefficient))))

(defthm poly-leading-coefficient-of-poly-scale
  (equal (poly-leading-coefficient (poly-scale scalar poly))
         (gfield::field-mul scalar (poly-leading-coefficient poly)))
  :hints
  (("Goal"
    :cases ((equal (gfield::field-fix scalar) (gfield::field-zero))
            (consp (normalize poly)))
    :use ((:instance poly-leading-coefficient-of-poly-scale-when-scalar-zero)
          (:instance poly-leading-coefficient-of-poly-scale-when-poly-zero)
          (:instance poly-leading-coefficient-of-poly-scale-when-nonzero))
    :in-theory (disable poly-scale poly-leading-coefficient normalize))))

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
