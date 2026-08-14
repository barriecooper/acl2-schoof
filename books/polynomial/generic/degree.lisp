(in-package "GPOLY")
(include-book "const")

; Formal degree and leading coefficient are structural properties of the
; normalized dense representation, not properties recovered from evaluation.
(def-degree-instance poly-degree poly-leading-coefficient normalize
                     gfield::field-zero)
(verify-guards poly-degree)
(verify-guards poly-leading-coefficient)
(def-monic-normalize-instance poly-monic-normalize normalize poly-scale
                              poly-leading-coefficient gfield::field-inv)

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

(defthm poly-monic-normalize-of-normalize
  (equal (poly-monic-normalize (normalize poly))
         (poly-monic-normalize poly))
  :hints
  (("Goal"
    :use ((:instance poly-scale-of-normalize
                     (a (gfield::field-inv
                         (poly-leading-coefficient poly)))
                     (x poly))
          (:instance poly-leading-coefficient-of-normalize (p poly)))
    :in-theory (e/d (poly-monic-normalize)
                    (poly-scale normalize poly-leading-coefficient
                     poly-leading-coefficient-when-canonical-nonzero)))))

(defthm canonical-polynomial-p-of-poly-monic-normalize
  (canonical-polynomial-p (poly-monic-normalize poly))
  :hints (("Goal" :in-theory (enable poly-monic-normalize))))

(defthm normalize-of-poly-monic-normalize
  (equal (normalize (poly-monic-normalize poly))
         (poly-monic-normalize poly))
  :hints
  (("Goal"
    :use ((:instance canonical-polynomial-p-of-poly-monic-normalize)
          (:instance normalize-when-canonical
                     (xs (poly-monic-normalize poly))))
    :in-theory (disable poly-monic-normalize normalize))))

(local
 (defthm consp-of-inverse-leading-coefficient-scale
   (implies (consp (normalize poly))
            (consp
             (poly-scale
              (gfield::field-inv (poly-leading-coefficient poly))
              poly)))
   :hints
   (("Goal"
     :cases ((consp
              (poly-scale
               (gfield::field-inv (poly-leading-coefficient poly))
               poly)))
     :use ((:instance poly-leading-coefficient-of-poly-scale
                      (scalar (gfield::field-inv
                               (poly-leading-coefficient poly))))
           (:instance poly-leading-coefficient-equal-zero
                      (p (poly-scale
                          (gfield::field-inv
                           (poly-leading-coefficient poly))
                          poly)))
           (:instance poly-leading-coefficient-equal-zero (p poly))
           (:instance gfield::field-mul-inverse-left
                      (x (poly-leading-coefficient poly))))
     :in-theory (disable poly-scale normalize poly-leading-coefficient
                         poly-leading-coefficient-of-poly-scale
                         gfield::field-mul-inverse-left)))))

(defthm poly-leading-coefficient-of-poly-monic-normalize
  (equal (poly-leading-coefficient (poly-monic-normalize poly))
         (if (consp (normalize poly))
             (gfield::field-one)
           (gfield::field-zero)))
  :hints
  (("Goal"
    :cases ((consp (normalize poly)))
    :use ((:instance poly-leading-coefficient-of-poly-scale
                     (scalar (gfield::field-inv
                              (poly-leading-coefficient poly))))
          (:instance poly-leading-coefficient-nonzero-when-canonical-nonzero
                     (p (normalize poly)))
          (:instance poly-leading-coefficient-of-normalize (p poly))
          (:instance gfield::field-mul-inverse-left
                     (x (poly-leading-coefficient poly))))
    :in-theory (e/d (poly-monic-normalize)
                    (poly-scale poly-leading-coefficient normalize
                     poly-leading-coefficient-of-poly-scale
                     poly-leading-coefficient-nonzero-when-canonical-nonzero
                     gfield::field-mul-inverse-left)))))

(defthm consp-of-poly-monic-normalize
  (equal (consp (poly-monic-normalize poly))
         (consp (normalize poly)))
  :hints
  (("Goal"
    :cases ((consp (normalize poly)))
    :use ((:instance consp-of-inverse-leading-coefficient-scale))
    :in-theory (e/d (poly-monic-normalize)
                    (poly-leading-coefficient normalize
                     poly-scale
                     poly-leading-coefficient-of-poly-monic-normalize)))))

(defthm poly-degree-of-poly-monic-normalize-when-nonzero
  (implies (consp (normalize poly))
           (equal (poly-degree (poly-monic-normalize poly))
                  (poly-degree poly)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-leading-coefficient-nonzero-when-canonical-nonzero
                     (p (normalize poly)))
          (:instance poly-leading-coefficient-of-normalize (p poly))
          (:instance gfield::field-inv-nonzero
                     (gfield::x (poly-leading-coefficient poly)))
          (:instance normalize-of-raw-scale-when-canonical-nonzero
                     (a (gfield::field-inv
                         (poly-leading-coefficient poly)))
                     (x (normalize poly)))
          (:instance len-of-raw-scale
                     (a (gfield::field-inv
                         (poly-leading-coefficient poly)))
                     (x (normalize poly)))
          (:instance canonical-polynomial-p-of-poly-monic-normalize)
          (:instance consp-of-poly-monic-normalize)
          (:instance poly-degree-when-canonical-nonzero
                     (p (poly-monic-normalize poly)))
          (:instance poly-degree-when-canonical-nonzero
                     (p (normalize poly))))
    :in-theory
    (e/d (poly-monic-normalize poly-scale poly-degree)
         (normalize poly-leading-coefficient
          normalize-of-poly-monic-normalize
          poly-leading-coefficient-nonzero-when-canonical-nonzero
          gfield::field-inv-nonzero)))))

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
