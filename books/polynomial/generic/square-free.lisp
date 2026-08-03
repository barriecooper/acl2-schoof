(in-package "GPOLY")

(include-book "derivative")
(include-book "euclidean")

(defun poly-square-free-p (polynomial)
  (declare (xargs :guard t))
  (equal
   (poly-monic-euclidean-gcd polynomial (poly-derivative polynomial))
   (polynomial-one)))

(defthm poly-square-free-p-definition
  (equal
   (poly-square-free-p polynomial)
   (equal
    (poly-monic-euclidean-gcd polynomial (poly-derivative polynomial))
    (polynomial-one)))
  :rule-classes nil)

(defthm booleanp-of-poly-square-free-p
  (booleanp (poly-square-free-p polynomial)))

(defthm poly-square-free-p-of-normalize
  (equal (poly-square-free-p (normalize polynomial))
         (poly-square-free-p polynomial))
  :hints
  (("Goal"
    :use ((:instance poly-monic-euclidean-gcd-of-normalize-first
                     (first polynomial)
                     (second (poly-derivative polynomial)))
          (:instance poly-derivative-of-normalize (poly polynomial)))
    :in-theory (enable poly-square-free-p))))

(defthm poly-square-free-p-of-fix-coefficients
  (equal (poly-square-free-p (fix-coefficients polynomial))
         (poly-square-free-p polynomial))
  :hints
  (("Goal"
    :use ((:instance poly-square-free-p-of-normalize
                     (polynomial (fix-coefficients polynomial)))
          (:instance poly-square-free-p-of-normalize))
    :in-theory (disable poly-square-free-p normalize fix-coefficients))))

(defthm not-poly-square-free-p-of-nil
  (not (poly-square-free-p nil))
  :hints (("Goal" :in-theory (enable poly-square-free-p
                                      poly-monic-euclidean-gcd
                                      poly-euclidean-gcd))))

(defthm poly-square-free-p-of-polynomial-one
  (poly-square-free-p (polynomial-one))
  :hints (("Goal" :in-theory (enable poly-square-free-p
                                      poly-monic-euclidean-gcd
                                      poly-euclidean-gcd
                                      poly-monic-normalize))))

(defthm poly-square-free-p-of-const
  (equal
   (poly-square-free-p (const coefficient))
   (not (equal (gfield::field-fix coefficient)
               (gfield::field-zero))))
  :hints
  (("Goal"
    :cases ((equal (gfield::field-fix coefficient)
                   (gfield::field-zero)))
    :in-theory (enable poly-square-free-p poly-monic-euclidean-gcd
                       poly-euclidean-gcd poly-monic-normalize const))))

(defun poly-has-square-divisor-p (polynomial divisor)
  (declare (xargs :guard t))
  (and (< 0 (poly-degree divisor))
       (poly-divides-p (poly-mul divisor divisor) polynomial)))

(defthm booleanp-of-poly-has-square-divisor-p
  (booleanp (poly-has-square-divisor-p polynomial divisor)))

(defthm poly-has-square-divisor-p-of-normalize-polynomial
  (equal (poly-has-square-divisor-p (normalize polynomial) divisor)
         (poly-has-square-divisor-p polynomial divisor))
  :hints (("Goal" :in-theory (enable poly-has-square-divisor-p))))

(defthm poly-has-square-divisor-p-of-normalize-divisor
  (equal (poly-has-square-divisor-p polynomial (normalize divisor))
         (poly-has-square-divisor-p polynomial divisor))
  :hints (("Goal" :in-theory (enable poly-has-square-divisor-p))))

(defthm poly-derivative-of-poly-square
  (equal
   (poly-derivative (poly-mul divisor divisor))
   (poly-add
    (poly-mul (poly-derivative divisor) divisor)
    (poly-mul divisor (poly-derivative divisor))))
  :hints (("Goal" :use ((:instance poly-derivative-of-poly-mul
                                   (f divisor) (g divisor))))))

(defthm poly-has-square-divisor-p-implies-divides
  (implies
   (poly-has-square-divisor-p polynomial divisor)
   (poly-divides-p divisor polynomial))
  :hints
  (("Goal"
    :use ((:instance poly-divides-p-self (dividend divisor))
          (:instance poly-divides-p-of-poly-mul
                     (left divisor) (right divisor))
          (:instance poly-divides-p-transitive
                     (middle (poly-mul divisor divisor))
                     (dividend polynomial)))
    :in-theory (enable poly-has-square-divisor-p))))

(defthm poly-has-square-divisor-p-implies-positive-degree
  (implies (poly-has-square-divisor-p polynomial divisor)
           (< 0 (poly-degree divisor)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable poly-has-square-divisor-p))))

(local
 (defthm divisor-divides-square-local
   (poly-divides-p divisor (poly-mul divisor divisor))
   :hints
   (("Goal"
     :use ((:instance poly-divides-p-self (dividend divisor))
           (:instance poly-divides-p-of-poly-mul
                      (left divisor) (right divisor)))
     :in-theory (disable poly-divides-p poly-mul)))))

(local
 (defthm divisor-divides-derivative-square-local
   (poly-divides-p divisor
                   (poly-derivative (poly-mul divisor divisor)))
   :hints
   (("Goal"
     :use
     ((:instance poly-divides-p-self (dividend divisor))
      (:instance poly-divides-p-of-poly-mul
                 (left divisor) (right (poly-derivative divisor)))
      (:instance poly-mul-commutative
                 (x (poly-derivative divisor)) (y divisor))
      (:instance poly-divides-p-of-poly-add
                 (left (poly-mul (poly-derivative divisor) divisor))
                 (right (poly-mul divisor (poly-derivative divisor))))
      (:instance poly-derivative-of-poly-square))
     :in-theory (disable poly-divides-p poly-mul poly-add
                         poly-derivative)))))

(local
 (defthm divisor-divides-derivative-first-product-local
   (poly-divides-p
    divisor
    (poly-mul (poly-derivative quotient)
              (poly-mul divisor divisor)))
   :hints
   (("Goal"
     :use
     ((:instance divisor-divides-square-local)
      (:instance poly-divides-p-of-poly-mul
                 (left (poly-mul divisor divisor))
                 (right (poly-derivative quotient)))
      (:instance poly-mul-commutative
                 (x (poly-derivative quotient))
                 (y (poly-mul divisor divisor))))
     :in-theory (disable poly-divides-p poly-mul)))))

(local
 (defthm divisor-divides-derivative-second-product-local
   (poly-divides-p
    divisor
    (poly-mul quotient
              (poly-derivative (poly-mul divisor divisor))))
   :hints
   (("Goal"
     :use
     ((:instance divisor-divides-derivative-square-local)
      (:instance poly-divides-p-of-poly-mul
                 (left (poly-derivative (poly-mul divisor divisor)))
                 (right quotient))
      (:instance poly-mul-commutative
                 (x quotient)
                 (y (poly-derivative (poly-mul divisor divisor)))))
     :in-theory (disable poly-divides-p poly-mul poly-derivative)))))

(local
 (defthm divisor-divides-derivative-of-square-times-quotient
   (poly-divides-p
    divisor
    (poly-derivative
     (poly-mul quotient (poly-mul divisor divisor))))
   :hints
   (("Goal"
     :use
     ((:instance divisor-divides-derivative-first-product-local)
      (:instance divisor-divides-derivative-second-product-local)
      (:instance poly-divides-p-of-poly-add
                 (left (poly-mul (poly-derivative quotient)
                                 (poly-mul divisor divisor)))
                 (right (poly-mul quotient
                                  (poly-derivative
                                   (poly-mul divisor divisor)))))
      (:instance poly-derivative-of-poly-mul
                 (f quotient) (g (poly-mul divisor divisor))))
     :in-theory (disable poly-divides-p poly-mul poly-add
                         poly-derivative)))))

(defthm poly-has-square-divisor-p-implies-divides-poly-derivative
  (implies
   (poly-has-square-divisor-p polynomial divisor)
   (poly-divides-p divisor (poly-derivative polynomial)))
  :hints
  (("Goal"
    :use
    ((:instance poly-divides-p-multiplication-witness
                (divisor (poly-mul divisor divisor))
                (dividend polynomial))
     (:instance divisor-divides-derivative-of-square-times-quotient
                (quotient
                 (mv-nth 0
                         (poly-divmod polynomial
                                      (poly-mul divisor divisor)))))
     (:instance poly-derivative-of-normalize (poly polynomial))
     (:instance poly-mul-normalize-right
                (x (mv-nth 0
                           (poly-divmod polynomial
                                        (poly-mul divisor divisor))))
                (y (poly-mul divisor divisor))))
    :in-theory (enable poly-has-square-divisor-p))))

(defthm
 poly-has-square-divisor-p-implies-common-derivative-divisor
  (implies
   (poly-has-square-divisor-p polynomial divisor)
   (poly-common-divisor-p divisor polynomial
                          (poly-derivative polynomial)))
  :hints
  (("Goal"
    :use ((:instance poly-has-square-divisor-p-implies-divides)
          (:instance
           poly-has-square-divisor-p-implies-divides-poly-derivative))
    :in-theory (enable poly-common-divisor-p))))

(local
 (defthm consp-of-normalize-when-positive-degree
   (implies (< 0 (poly-degree polynomial))
            (consp (normalize polynomial)))
   :hints
   (("Goal"
     :use ((:instance poly-degree-equal-minus-one (p polynomial))
           (:instance poly-degree-lower-bound (p polynomial)))
     :in-theory (disable poly-degree normalize)))))

(defthm positive-degree-poly-does-not-divide-polynomial-one
  (implies
   (< 0 (poly-degree polynomial))
   (not (poly-divides-p polynomial (polynomial-one))))
  :hints
  (("Goal"
    :use
    ((:instance poly-remainder-of-polynomial-one-when-positive-degree
                (modulus polynomial))
     (:instance consp-of-normalize-when-positive-degree)
     (:instance poly-degree-of-normalize (p polynomial)))
    :in-theory (e/d (poly-divides-p polynomial-one)
                    (poly-remainder normalize poly-degree)))))

(defthm poly-square-free-p-implies-not-poly-has-square-divisor-p
  (implies
   (poly-square-free-p polynomial)
   (not (poly-has-square-divisor-p polynomial divisor)))
  :hints
  (("Goal"
    :use
    ((:instance
      poly-has-square-divisor-p-implies-common-derivative-divisor)
     (:instance poly-divides-p-of-poly-monic-euclidean-gcd
                (common divisor)
                (first polynomial)
                (second (poly-derivative polynomial)))
     (:instance positive-degree-poly-does-not-divide-polynomial-one
                (polynomial divisor))
     (:instance poly-square-free-p-definition)
     (:instance poly-has-square-divisor-p-implies-positive-degree))
    :in-theory (theory 'minimal-theory))))

(verify-guards poly-square-free-p)
(verify-guards poly-has-square-divisor-p)
