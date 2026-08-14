(in-package "GPOLY")
(include-book "factor-degree-bound")
(include-book "finite-field-monic-euclidean-gcd")

; Logical finite-field-prefixed interface; no executable factor search.
(defun finite-field-poly-unit-p (poly)
  (declare (xargs :guard t))
  (equal (finite-field-poly-degree poly) 0))

(defun-sk finite-field-poly-reducible-p (poly)
  (exists (left right)
          (and (equal (finite-field-poly-mul left right)
                      (finite-field-poly-normalize poly))
               (not (finite-field-poly-unit-p left))
               (not (finite-field-poly-unit-p right)))))

(defun finite-field-poly-irreducible-p (poly)
  (declare (xargs :guard t :verify-guards nil))
  (and (< 0 (finite-field-poly-degree poly))
       (not (finite-field-poly-reducible-p poly))))

(defun-sk finite-field-poly-has-bounded-monic-factor-p (poly bound)
  (exists (factor)
          (and (finite-field-canonical-polynomial-p factor)
               (consp factor)
               (equal (finite-field-poly-leading-coefficient factor)
                      (gfield::finite-field-one))
               (< 0 (finite-field-poly-degree factor))
               (<= (finite-field-poly-degree factor) (nfix bound))
               (finite-field-poly-divides-p factor poly))))

(defthm finite-field-poly-irreducible-p-definition
  (equal (finite-field-poly-irreducible-p poly)
         (and (< 0 (finite-field-poly-degree poly))
              (not (finite-field-poly-reducible-p poly))))
  :rule-classes nil)

(defthm finite-field-poly-reducible-p-of-normalize
  (equal (finite-field-poly-reducible-p
          (finite-field-poly-normalize poly))
         (finite-field-poly-reducible-p poly))
  :hints (("Goal"
           :use ((:instance finite-field-poly-reducible-p-suff
                            (poly (finite-field-poly-normalize poly))
                            (left (mv-nth 0
                             (finite-field-poly-reducible-p-witness poly)))
                            (right (mv-nth 1
                             (finite-field-poly-reducible-p-witness poly))))
                 (:instance finite-field-poly-reducible-p-suff
                            (poly poly)
                            (left (mv-nth 0
                             (finite-field-poly-reducible-p-witness
                              (finite-field-poly-normalize poly))))
                            (right (mv-nth 1
                             (finite-field-poly-reducible-p-witness
                              (finite-field-poly-normalize poly))))))
           :in-theory (disable finite-field-poly-reducible-p-suff
                               finite-field-poly-mul
                               finite-field-poly-normalize))))

(defthm finite-field-poly-irreducible-p-of-normalize
  (equal (finite-field-poly-irreducible-p
          (finite-field-poly-normalize poly))
         (finite-field-poly-irreducible-p poly))
  :hints (("Goal"
           :use ((:instance finite-field-poly-reducible-p-of-normalize)
                 (:instance finite-field-poly-degree-of-poly-normalize
                            (p poly)))
           :in-theory (e/d (finite-field-poly-irreducible-p)
                           (finite-field-poly-reducible-p
                            finite-field-poly-degree
                            finite-field-poly-normalize)))))

(defthm finite-field-poly-has-bounded-monic-factor-p-of-normalize
  (equal (finite-field-poly-has-bounded-monic-factor-p
          (finite-field-poly-normalize poly) bound)
         (finite-field-poly-has-bounded-monic-factor-p poly bound))
  :hints (("Goal"
           :use ((:instance finite-field-poly-has-bounded-monic-factor-p-suff
                            (poly (finite-field-poly-normalize poly))
                            (bound bound)
                            (factor
                             (finite-field-poly-has-bounded-monic-factor-p-witness
                              poly bound)))
                 (:instance finite-field-poly-has-bounded-monic-factor-p-suff
                            (poly poly) (bound bound)
                            (factor
                             (finite-field-poly-has-bounded-monic-factor-p-witness
                              (finite-field-poly-normalize poly) bound)))
                 (:instance finite-field-poly-divides-p-of-normalize-dividend
                            (divisor
                             (finite-field-poly-has-bounded-monic-factor-p-witness
                              poly bound)) (dividend poly))
                 (:instance finite-field-poly-divides-p-of-normalize-dividend
                            (divisor
                             (finite-field-poly-has-bounded-monic-factor-p-witness
                              (finite-field-poly-normalize poly) bound))
                            (dividend poly)))
           :in-theory (disable
                       finite-field-poly-has-bounded-monic-factor-p-suff
                       finite-field-poly-divides-p
                       finite-field-poly-normalize))))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm finite-field-positive-summands-have-half-bounded-summand
  (implies (and (integerp a) (integerp b) (< 0 a) (< 0 b)
                (equal (+ a b) n))
           (or (<= a (floor n 2)) (<= b (floor n 2))))
  :rule-classes nil
  :hints (("Goal" :cases ((<= a b))))))

(local
 (defthm finite-field-positive-degree-implies-normalize-nonzero
  (implies (< 0 (finite-field-poly-degree poly))
           (consp (finite-field-poly-normalize poly)))
  :rule-classes nil
  :hints (("Goal" :cases ((consp (finite-field-poly-normalize poly)))
           :use ((:instance finite-field-poly-degree-when-normalize-not-consp
                            (poly poly)))
           :in-theory (disable finite-field-poly-degree
                               finite-field-poly-normalize)))))

(local
 (defthm finite-field-normalized-factor-nonzero-left
  (implies (and (< 0 (finite-field-poly-degree poly))
                (equal (finite-field-poly-mul left right)
                       (finite-field-poly-normalize poly)))
           (consp (finite-field-poly-normalize left)))
  :rule-classes nil
  :hints (("Goal" :cases ((consp (finite-field-poly-normalize left)))
           :use ((:instance finite-field-poly-mul-normalize-left
                            (x left) (y right))
                 (:instance finite-field-positive-degree-implies-normalize-nonzero))
           :in-theory (disable
                               finite-field-poly-mul
                               finite-field-poly-normalize
                               finite-field-poly-degree)))))

(local
 (defthm finite-field-normalized-factor-nonzero-right
  (implies (and (< 0 (finite-field-poly-degree poly))
                (equal (finite-field-poly-mul left right)
                       (finite-field-poly-normalize poly)))
           (consp (finite-field-poly-normalize right)))
  :rule-classes nil
  :hints (("Goal" :cases ((consp (finite-field-poly-normalize right)))
           :use ((:instance finite-field-poly-mul-normalize-right
                            (x left) (y right))
                 (:instance finite-field-positive-degree-implies-normalize-nonzero))
           :in-theory (disable
                               finite-field-poly-mul
                               finite-field-poly-normalize
                               finite-field-poly-degree)))))

(local
 (defthm len-positive-when-consp-for-factor-bound
  (implies (consp x) (< 0 (len x)))))
(local
 (defthm len-zero-implies-not-consp-for-factor-bound
  (implies (equal (len x) 0) (not (consp x)))))

(local
 (defthm finite-field-normalized-nonunit-factor-positive-degree
  (implies (and (consp (finite-field-poly-normalize factor))
                (not (finite-field-poly-unit-p factor)))
           (< 0 (finite-field-poly-degree
                 (finite-field-poly-normalize factor))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-degree-of-poly-normalize
                            (p factor))
                 (:instance finite-field-poly-degree-when-normalize-consp
                            (poly factor))
                 (:instance len-positive-when-consp-for-factor-bound
                            (x (finite-field-poly-normalize factor)))
                 (:instance len-zero-implies-not-consp-for-factor-bound
                            (x (finite-field-poly-normalize factor))))
           :in-theory (e/d (finite-field-poly-unit-p)
                           (finite-field-poly-degree
                            finite-field-poly-normalize))))))

(local
 (defthm finite-field-left-factor-divides-exact-product
  (finite-field-poly-divides-p
   left (finite-field-poly-mul left right))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-divides-p-of-multiple
                            (divisor left) (multiplier right))
                 (:instance finite-field-poly-mul-commutative-for-reduction
                            (x left) (y right)))
           :in-theory (disable finite-field-poly-divides-p
                               finite-field-poly-mul)))))

(local
 (defthm finite-field-reducible-positive-degree-factor-data
  (implies
   (and (equal (finite-field-poly-normalize poly) poly)
        (< 0 (finite-field-poly-degree poly))
        (finite-field-poly-reducible-p poly))
   (let* ((left (finite-field-poly-normalize
                 (mv-nth 0 (finite-field-poly-reducible-p-witness poly))))
          (right (finite-field-poly-normalize
                  (mv-nth 1 (finite-field-poly-reducible-p-witness poly)))))
    (and (finite-field-canonical-polynomial-p left)
         (finite-field-canonical-polynomial-p right)
         (consp left) (consp right)
         (< 0 (finite-field-poly-degree left))
         (< 0 (finite-field-poly-degree right))
         (equal (+ (finite-field-poly-degree left)
                   (finite-field-poly-degree right))
                (finite-field-poly-degree poly))
         (finite-field-poly-divides-p left poly)
         (finite-field-poly-divides-p right poly))))
  :rule-classes nil
  :hints
  (("Goal" :use ((:instance finite-field-poly-reducible-p (poly poly))
                   (:instance finite-field-normalized-factor-nonzero-left
                             (left (mv-nth 0 (finite-field-poly-reducible-p-witness poly)))
                             (right (mv-nth 1 (finite-field-poly-reducible-p-witness poly))))
                   (:instance finite-field-normalized-factor-nonzero-right
                             (left (mv-nth 0 (finite-field-poly-reducible-p-witness poly)))
                             (right (mv-nth 1 (finite-field-poly-reducible-p-witness poly)))))
    :in-theory (disable finite-field-poly-reducible-p
                        finite-field-poly-unit-p finite-field-poly-mul
                        finite-field-poly-normalize finite-field-poly-degree))
   ("Goal'" :use ((:instance finite-field-poly-mul-normalize-left
                             (x (mv-nth 0 (finite-field-poly-reducible-p-witness poly)))
                             (y (finite-field-poly-normalize
                                 (mv-nth 1 (finite-field-poly-reducible-p-witness poly)))))
                   (:instance finite-field-poly-mul-normalize-right
                             (x (mv-nth 0 (finite-field-poly-reducible-p-witness poly)))
                             (y (mv-nth 1 (finite-field-poly-reducible-p-witness poly)))))
    :in-theory (disable finite-field-poly-mul
                        finite-field-poly-normalize))
   ("Goal''" :use
    ((:instance finite-field-normalized-nonunit-factor-positive-degree
                (factor (mv-nth 0 (finite-field-poly-reducible-p-witness poly))))
     (:instance finite-field-normalized-nonunit-factor-positive-degree
                (factor (mv-nth 1 (finite-field-poly-reducible-p-witness poly))))
     (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                (xs (mv-nth 0 (finite-field-poly-reducible-p-witness poly))))
     (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                (xs (mv-nth 1 (finite-field-poly-reducible-p-witness poly))))
     (:instance finite-field-poly-degree-of-poly-mul
                (f (finite-field-poly-normalize
                    (mv-nth 0 (finite-field-poly-reducible-p-witness poly))))
                (g (finite-field-poly-normalize
                    (mv-nth 1 (finite-field-poly-reducible-p-witness poly)))))
     (:instance finite-field-left-factor-divides-exact-product
                (left (finite-field-poly-normalize
                       (mv-nth 0 (finite-field-poly-reducible-p-witness poly))))
                (right (finite-field-poly-normalize
                        (mv-nth 1 (finite-field-poly-reducible-p-witness poly)))))
     (:instance finite-field-left-factor-divides-exact-product
                (left (finite-field-poly-normalize
                       (mv-nth 1 (finite-field-poly-reducible-p-witness poly))))
                (right (finite-field-poly-normalize
                        (mv-nth 0 (finite-field-poly-reducible-p-witness poly)))))
     (:instance finite-field-poly-mul-commutative-for-reduction
                (x (mv-nth 0 (finite-field-poly-reducible-p-witness poly)))
                (y (mv-nth 1 (finite-field-poly-reducible-p-witness poly))))
     (:instance finite-field-poly-mul-commutative-for-reduction
                (x (finite-field-poly-normalize
                    (mv-nth 0 (finite-field-poly-reducible-p-witness poly))))
                (y (finite-field-poly-normalize
                    (mv-nth 1 (finite-field-poly-reducible-p-witness poly)))))
     (:instance finite-field-poly-divides-p-of-normalize-dividend
                (divisor (finite-field-poly-normalize
                          (mv-nth 0 (finite-field-poly-reducible-p-witness poly))))
                (dividend poly))
     (:instance finite-field-poly-divides-p-of-normalize-dividend
                (divisor (finite-field-poly-normalize
                          (mv-nth 1 (finite-field-poly-reducible-p-witness poly))))
                (dividend poly)))
    :in-theory (theory 'minimal-theory)))))

(defthm finite-field-poly-has-bounded-monic-factor-p-from-normalized-factor
 (implies
  (and (finite-field-canonical-polynomial-p factor)
       (consp factor)
       (< 0 (finite-field-poly-degree factor))
       (<= (finite-field-poly-degree factor) (nfix bound))
       (finite-field-poly-divides-p factor poly))
  (finite-field-poly-has-bounded-monic-factor-p poly bound))
 :rule-classes nil
 :hints
 (("Goal" :cases ((finite-field-poly-has-bounded-monic-factor-p poly bound))
   :use ((:instance finite-field-poly-has-bounded-monic-factor-p-suff
                    (factor (finite-field-poly-monic-normalize factor)))
         (:instance finite-field-poly-normalize-when-canonical (xs factor))
         (:instance finite-field-poly-degree-of-poly-monic-normalize-when-nonzero
                    (polynomial factor))
         (:instance finite-field-consp-of-poly-monic-normalize
                    (polynomial factor))
         (:instance finite-field-canonical-polynomial-p-of-poly-monic-normalize
                    (polynomial factor))
         (:instance finite-field-poly-leading-coefficient-of-poly-monic-normalize
                    (polynomial factor))
         (:instance finite-field-poly-divides-p-of-poly-monic-normalize-divisor
                    (divisor factor) (dividend poly)))
   :in-theory (theory 'minimal-theory))))

(defthm finite-field-poly-reducible-normalized-positive-degree-implies-bounded-monic-factor
 (implies
  (and (equal (finite-field-poly-normalize poly) poly)
       (< 0 (finite-field-poly-degree poly))
       (finite-field-poly-reducible-p poly))
  (finite-field-poly-has-bounded-monic-factor-p
   poly (floor (finite-field-poly-degree poly) 2)))
 :rule-classes nil
 :hints
 (("Goal"
   :use
   (finite-field-reducible-positive-degree-factor-data
    (:instance finite-field-positive-summands-have-half-bounded-summand
               (a (finite-field-poly-degree
                   (finite-field-poly-normalize
                    (mv-nth 0 (finite-field-poly-reducible-p-witness poly)))))
               (b (finite-field-poly-degree
                   (finite-field-poly-normalize
                    (mv-nth 1 (finite-field-poly-reducible-p-witness poly)))))
               (n (finite-field-poly-degree poly)))
    (:instance finite-field-poly-has-bounded-monic-factor-p-from-normalized-factor
               (factor (finite-field-poly-normalize
                        (mv-nth 0 (finite-field-poly-reducible-p-witness poly))))
               (bound (floor (finite-field-poly-degree poly) 2)))
    (:instance finite-field-poly-has-bounded-monic-factor-p-from-normalized-factor
               (factor (finite-field-poly-normalize
                        (mv-nth 1 (finite-field-poly-reducible-p-witness poly))))
               (bound (floor (finite-field-poly-degree poly) 2))))
   :in-theory (disable finite-field-poly-reducible-p
                       finite-field-poly-has-bounded-monic-factor-p
                       finite-field-poly-degree finite-field-poly-normalize))))

(defthm finite-field-poly-normalized-positive-degree-without-bounded-monic-factor-is-irreducible
 (implies
  (and (equal (finite-field-poly-normalize poly) poly)
       (< 0 (finite-field-poly-degree poly))
       (not (finite-field-poly-has-bounded-monic-factor-p
             poly (floor (finite-field-poly-degree poly) 2))))
  (finite-field-poly-irreducible-p poly))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance finite-field-poly-irreducible-p-definition)
                (:instance finite-field-poly-reducible-normalized-positive-degree-implies-bounded-monic-factor))
          :in-theory (theory 'minimal-theory))))
