(in-package "GPOLY")
(include-book "irreducibility")
(local (include-book "arithmetic-5/top" :dir :system))

; A logical factor-existence specification, not an executable factor search.
(defun-sk poly-has-bounded-monic-factor-p (poly bound)
  (exists (factor)
          (and (canonical-polynomial-p factor)
               (consp factor)
               (equal (poly-leading-coefficient factor)
                      (gfield::field-one))
               (< 0 (poly-degree factor))
               (<= (poly-degree factor) (nfix bound))
               (poly-divides-p factor poly))))

(defthm poly-has-bounded-monic-factor-p-of-nfix
  (equal (poly-has-bounded-monic-factor-p poly (nfix bound))
         (poly-has-bounded-monic-factor-p poly bound))
  :hints (("Goal"
           :use ((:instance poly-has-bounded-monic-factor-p-suff
                            (poly poly) (bound (nfix bound))
                            (factor (poly-has-bounded-monic-factor-p-witness
                                     poly bound)))
                 (:instance poly-has-bounded-monic-factor-p-suff
                            (poly poly) (bound bound)
                            (factor (poly-has-bounded-monic-factor-p-witness
                                     poly (nfix bound)))))
           :in-theory (disable poly-has-bounded-monic-factor-p-suff))))

(defthm poly-has-bounded-monic-factor-p-of-normalize
  (equal (poly-has-bounded-monic-factor-p (normalize poly) bound)
         (poly-has-bounded-monic-factor-p poly bound))
  :hints (("Goal"
           :use ((:instance poly-has-bounded-monic-factor-p-suff
                            (poly (normalize poly)) (bound bound)
                            (factor (poly-has-bounded-monic-factor-p-witness
                                     poly bound)))
                 (:instance poly-has-bounded-monic-factor-p-suff
                            (poly poly) (bound bound)
                            (factor (poly-has-bounded-monic-factor-p-witness
                                     (normalize poly) bound)))
                 (:instance poly-divides-p-of-normalize-dividend
                            (divisor (poly-has-bounded-monic-factor-p-witness
                                      poly bound))
                            (dividend poly))
                 (:instance poly-divides-p-of-normalize-dividend
                            (divisor (poly-has-bounded-monic-factor-p-witness
                                      (normalize poly) bound))
                            (dividend poly)))
           :in-theory (disable poly-has-bounded-monic-factor-p-suff
                               poly-divides-p normalize))))

(local
 (defthm positive-summands-have-half-bounded-summand
   (implies (and (integerp a) (integerp b) (< 0 a) (< 0 b)
                 (equal (+ a b) n))
            (or (<= a (floor n 2))
                (<= b (floor n 2))))
   :rule-classes nil
   :hints (("Goal" :cases ((<= a b))))))

(local
 (defthm positive-degree-implies-normalize-nonzero-for-bound
   (implies (< 0 (poly-degree poly))
            (consp (normalize poly)))
   :rule-classes nil
   :hints (("Goal" :cases ((consp (normalize poly)))
            :use ((:instance poly-degree-equal-minus-one (p poly)))
            :in-theory (disable poly-degree normalize)))))

(local
 (defthm normalized-factor-nonzero-when-product-positive-degree-left
   (implies (and (< 0 (poly-degree poly))
                 (equal (poly-mul left right) (normalize poly)))
            (consp (normalize left)))
   :rule-classes nil
   :hints (("Goal" :cases ((consp (normalize left)))
            :use ((:instance poly-mul-normalize-left (x left) (y right))
                  (:instance positive-degree-implies-normalize-nonzero-for-bound))
            :in-theory (disable poly-mul-normalize-left poly-mul normalize
                                poly-degree)))))

(local
 (defthm normalized-factor-nonzero-when-product-positive-degree-right
   (implies (and (< 0 (poly-degree poly))
                 (equal (poly-mul left right) (normalize poly)))
            (consp (normalize right)))
   :rule-classes nil
   :hints (("Goal" :cases ((consp (normalize right)))
            :use ((:instance poly-mul-normalize-right (x left) (y right))
                  (:instance positive-degree-implies-normalize-nonzero-for-bound))
            :in-theory (disable poly-mul-normalize-right poly-mul normalize
                                poly-degree)))))

(local
 (defthm normalized-nonunit-factor-positive-degree-for-bound
   (implies (and (consp (normalize factor))
                 (not (poly-unit-p factor)))
            (< 0 (poly-degree (normalize factor))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance poly-degree-of-normalize (p factor))
                  (:instance natp-of-poly-degree-when-normalize-nonzero
                             (p factor)))
            :in-theory (e/d (poly-unit-p)
                            (poly-degree normalize
                             poly-degree-of-normalize))))))

(local
 (defthm left-normalized-factor-divides-product
   (poly-divides-p (normalize left) (poly-mul left right))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance poly-divides-p-self (dividend (normalize left)))
                  (:instance poly-divides-p-of-poly-mul
                             (divisor (normalize left))
                             (left (normalize left)) (right right))
                  (:instance poly-mul-normalize-left (x left) (y right)))
            :in-theory (disable poly-divides-p poly-mul normalize)))))

(local
 (defthm right-normalized-factor-divides-product
   (poly-divides-p (normalize right) (poly-mul left right))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance poly-divides-p-self (dividend (normalize right)))
                  (:instance poly-divides-p-of-poly-mul
                             (divisor (normalize right))
                             (left (normalize right)) (right left))
                  (:instance poly-mul-normalize-left (x right) (y left))
                  (:instance poly-mul-commutative (x left) (y right)))
            :in-theory (disable poly-divides-p poly-mul normalize)))))

(local
 (defthm reducible-positive-degree-factor-data
   (implies (and (equal (normalize poly) poly)
                 (< 0 (poly-degree poly))
                 (poly-reducible-p poly))
            (let* ((left (normalize
                          (mv-nth 0 (poly-reducible-p-witness poly))))
                   (right (normalize
                           (mv-nth 1 (poly-reducible-p-witness poly)))))
              (and (canonical-polynomial-p left)
                   (canonical-polynomial-p right)
                   (consp left) (consp right)
                   (< 0 (poly-degree left))
                   (< 0 (poly-degree right))
                   (equal (+ (poly-degree left) (poly-degree right))
                          (poly-degree poly))
                   (poly-divides-p left poly)
                   (poly-divides-p right poly))))
   :rule-classes nil
   :hints
   (("Goal" :use ((:instance poly-reducible-p (poly poly))
                    (:instance normalized-factor-nonzero-when-product-positive-degree-left
                              (left (mv-nth 0 (poly-reducible-p-witness poly)))
                              (right (mv-nth 1 (poly-reducible-p-witness poly))))
                    (:instance normalized-factor-nonzero-when-product-positive-degree-right
                              (left (mv-nth 0 (poly-reducible-p-witness poly)))
                              (right (mv-nth 1 (poly-reducible-p-witness poly)))))
     :in-theory (disable poly-reducible-p poly-unit-p poly-mul normalize
                         poly-degree))
    ("Goal'" :use ((:instance poly-mul-normalize-left
                              (x (mv-nth 0 (poly-reducible-p-witness poly)))
                              (y (normalize
                                  (mv-nth 1 (poly-reducible-p-witness poly)))))
                    (:instance poly-mul-normalize-right
                              (x (mv-nth 0 (poly-reducible-p-witness poly)))
                              (y (mv-nth 1 (poly-reducible-p-witness poly)))))
     :in-theory (disable poly-mul normalize))
    ("Goal''" :use ((:instance normalized-nonunit-factor-positive-degree-for-bound
                               (factor (mv-nth 0 (poly-reducible-p-witness poly))))
                     (:instance normalized-nonunit-factor-positive-degree-for-bound
                               (factor (mv-nth 1 (poly-reducible-p-witness poly))))
                     (:instance poly-degree-of-poly-mul
                               (f (normalize
                                   (mv-nth 0 (poly-reducible-p-witness poly))))
                               (g (normalize
                                   (mv-nth 1 (poly-reducible-p-witness poly)))))
                     (:instance canonical-polynomial-p-of-normalize
                               (xs (mv-nth 0 (poly-reducible-p-witness poly))))
                     (:instance canonical-polynomial-p-of-normalize
                               (xs (mv-nth 1 (poly-reducible-p-witness poly))))
                     (:instance left-normalized-factor-divides-product
                               (left (mv-nth 0 (poly-reducible-p-witness poly)))
                               (right (mv-nth 1 (poly-reducible-p-witness poly))))
                     (:instance right-normalized-factor-divides-product
                               (left (mv-nth 0 (poly-reducible-p-witness poly)))
                               (right (mv-nth 1 (poly-reducible-p-witness poly))))
                     (:instance poly-divides-p-of-normalize-dividend
                               (divisor (normalize
                                         (mv-nth 0 (poly-reducible-p-witness poly))))
                               (dividend poly))
                     (:instance poly-divides-p-of-normalize-dividend
                               (divisor (normalize
                                         (mv-nth 1 (poly-reducible-p-witness poly))))
                               (dividend poly)))
     :in-theory (theory 'minimal-theory)))))

(defthm poly-has-bounded-monic-factor-p-from-normalized-factor
  (implies (and (canonical-polynomial-p factor)
                (consp factor)
                (< 0 (poly-degree factor))
                (<= (poly-degree factor) (nfix bound))
                (poly-divides-p factor poly))
           (poly-has-bounded-monic-factor-p poly bound))
  :rule-classes nil
  :hints (("Goal"
           :cases ((poly-has-bounded-monic-factor-p poly bound))
           :use ((:instance poly-has-bounded-monic-factor-p-suff
                            (factor (poly-monic-normalize factor)))
                 (:instance poly-degree-of-poly-monic-normalize-when-nonzero
                            (poly factor))
                 (:instance normalize-when-canonical (xs factor))
                 (:instance canonical-polynomial-p-of-poly-monic-normalize
                            (poly factor))
                 (:instance consp-of-poly-monic-normalize (poly factor))
                 (:instance poly-leading-coefficient-of-poly-monic-normalize
                            (poly factor))
                 (:instance poly-divides-p-of-poly-monic-normalize-divisor
                            (divisor factor) (dividend poly)))
           :in-theory (theory 'minimal-theory))))

(defthm poly-reducible-normalized-positive-degree-implies-bounded-monic-factor
  (implies (and (equal (normalize poly) poly)
                (< 0 (poly-degree poly))
                (poly-reducible-p poly))
           (poly-has-bounded-monic-factor-p
            poly (floor (poly-degree poly) 2)))
  :rule-classes nil
  :hints (("Goal"
           :use (reducible-positive-degree-factor-data
                 (:instance positive-summands-have-half-bounded-summand
                            (a (poly-degree
                                (normalize
                                 (mv-nth 0 (poly-reducible-p-witness poly)))))
                            (b (poly-degree
                                (normalize
                                 (mv-nth 1 (poly-reducible-p-witness poly)))))
                            (n (poly-degree poly)))
                 (:instance poly-has-bounded-monic-factor-p-from-normalized-factor
                            (factor (normalize
                                     (mv-nth 0 (poly-reducible-p-witness poly))))
                            (bound (floor (poly-degree poly) 2)))
                 (:instance poly-has-bounded-monic-factor-p-from-normalized-factor
                            (factor (normalize
                                     (mv-nth 1 (poly-reducible-p-witness poly))))
                            (bound (floor (poly-degree poly) 2))))
           :in-theory (disable poly-reducible-p
                               poly-has-bounded-monic-factor-p
                               poly-degree normalize))))

(defthm poly-normalized-positive-degree-without-bounded-monic-factor-is-irreducible
  (implies (and (equal (normalize poly) poly)
                (< 0 (poly-degree poly))
                (not (poly-has-bounded-monic-factor-p
                      poly (floor (poly-degree poly) 2))))
           (poly-irreducible-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-irreducible-p-definition)
                 (:instance
                  poly-reducible-normalized-positive-degree-implies-bounded-monic-factor))
           :in-theory (theory 'minimal-theory))))
