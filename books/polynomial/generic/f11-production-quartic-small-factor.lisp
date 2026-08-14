(in-package "GPOLY")

(include-book "f11-production-euclidean-stack")

; Logical specifications only: neither predicate performs factor search.
(defun f11-poly-unit-p (poly)
  (declare (xargs :guard t))
  (equal (f11-poly-degree poly) 0))

(defun-sk f11-poly-reducible-p (poly)
  (exists (left right)
          (and (equal (f11-poly-mul left right) (f11-normalize poly))
               (not (f11-poly-unit-p left))
               (not (f11-poly-unit-p right)))))

(defun f11-poly-irreducible-p (poly)
  (declare (xargs :guard t :verify-guards nil))
  (and (< 0 (f11-poly-degree poly))
       (not (f11-poly-reducible-p poly))))

(defun-sk f11-poly-has-small-monic-factor-p (poly)
  (exists (factor)
          (and (f11-canonical-polynomial-p factor)
               (consp factor)
               (equal (f11-poly-leading-coefficient factor)
                      (gfield::f11-one))
               (or (equal (f11-poly-degree factor) 1)
                   (equal (f11-poly-degree factor) 2))
               (f11-poly-divides-p factor poly))))

(defthm f11-poly-irreducible-p-definition
  (equal (f11-poly-irreducible-p poly)
         (and (< 0 (f11-poly-degree poly))
              (not (f11-poly-reducible-p poly))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                               '(f11-poly-irreducible-p)))))

; Local discharge facts required by the production stack's transport macro.
(local
 (defthm f11-stack-canonical-implies-coefficient-list
   (implies (f11-canonical-polynomial-p xs) (f11-coefficient-list-p xs))
   :hints (("Goal" :in-theory (enable f11-canonical-polynomial-p
                                       f11-normalize f11-fix-coefficients
                                       f11-trim-trailing-zeros
                                       f11-coefficient-list-p)))))
(local
 (defthm f11-stack-normalize-canonical-list
   (implies (and (f11-coefficient-list-p xs)
                 (or (not (consp xs))
                     (not (equal (car (last xs)) 0))))
            (equal (f11-normalize xs) xs))
   :hints (("Goal" :induct (f11-trim-trailing-zeros xs)
            :in-theory (enable f11-normalize f11-fix-coefficients
                               f11-trim-trailing-zeros
                               f11-coefficient-list-p gfield::f11-fix
                               gfield::f11-element-p)))))
(local
 (defthm f11-stack-last-zero-not-normalized
   (implies (and (f11-coefficient-list-p xs) (consp xs)
                 (equal (car (last xs)) 0))
            (not (equal (f11-normalize xs) xs)))
   :hints (("Goal" :induct (f11-trim-trailing-zeros xs)
            :in-theory (enable f11-normalize f11-fix-coefficients
                               f11-trim-trailing-zeros
                               f11-coefficient-list-p gfield::f11-fix
                               gfield::f11-element-p)))))

; Narrow transports from the already certified finite-field/F11 stack.
(def-f11-stack-law f11-poly-normalize-idempotent-for-irreducibility
  finite-field-poly-normalize-idempotent
  (equal (f11-normalize (f11-normalize polynomial))
         (f11-normalize polynomial)))
(def-f11-stack-law f11-poly-degree-of-normalize-for-irreducibility
  finite-field-poly-degree-of-poly-normalize
  (equal (f11-poly-degree (f11-normalize polynomial))
         (f11-poly-degree polynomial)))
(def-f11-stack-law f11-canonical-polynomial-p-of-normalize-for-irreducibility
  finite-field-canonical-polynomial-p-of-poly-normalize
  (f11-canonical-polynomial-p (f11-normalize polynomial)))
(def-f11-stack-law f11-poly-mul-normalize-left-for-irreducibility
  finite-field-poly-mul-normalize-left-for-reduction-public
  (equal (f11-poly-mul (f11-normalize left) right)
         (f11-poly-mul left right)))
(def-f11-stack-law f11-poly-mul-normalize-right-for-irreducibility
  finite-field-poly-mul-normalize-right-for-reduction-public
  (equal (f11-poly-mul left (f11-normalize right))
         (f11-poly-mul left right)))
(def-f11-stack-law f11-poly-degree-of-poly-mul-for-irreducibility
  finite-field-poly-degree-of-poly-mul
  (implies (and (f11-canonical-polynomial-p left)
                (f11-canonical-polynomial-p right)
                (consp left) (consp right))
           (equal (f11-poly-degree (f11-poly-mul left right))
                  (+ (f11-poly-degree left) (f11-poly-degree right))))
  :rule-classes nil)
(def-f11-stack-law f11-poly-mul-commutative-for-irreducibility
  finite-field-poly-mul-commutative-for-reduction
  (equal (f11-poly-mul left right) (f11-poly-mul right left))
  :rule-classes nil)
(def-f11-stack-law f11-poly-divides-p-of-multiple-for-irreducibility
  finite-field-poly-divides-p-of-multiple
  (f11-poly-divides-p divisor (f11-poly-mul multiplier divisor))
  :rule-classes nil)
(def-f11-stack-law f11-poly-divides-p-of-normalize-dividend-for-irreducibility
  finite-field-poly-divides-p-of-normalize-dividend
  (equal (f11-poly-divides-p divisor (f11-normalize dividend))
         (f11-poly-divides-p divisor dividend)))
(def-f11-stack-law f11-poly-degree-of-poly-monic-normalize-when-nonzero
  finite-field-poly-degree-of-poly-monic-normalize-when-nonzero
  (implies (consp (f11-normalize factor))
           (equal (f11-poly-degree (f11-poly-monic-normalize factor))
                  (f11-poly-degree factor)))
  :rule-classes nil)
(def-f11-stack-law f11-consp-of-poly-monic-normalize-for-irreducibility
  finite-field-consp-of-poly-monic-normalize
  (equal (consp (f11-poly-monic-normalize factor))
         (consp (f11-normalize factor)))
  :rule-classes nil)
(def-f11-stack-law f11-canonical-polynomial-p-of-poly-monic-normalize-for-irreducibility
  finite-field-canonical-polynomial-p-of-poly-monic-normalize
  (f11-canonical-polynomial-p (f11-poly-monic-normalize factor)))
(def-f11-stack-law f11-poly-leading-coefficient-of-poly-monic-normalize-for-irreducibility
  finite-field-poly-leading-coefficient-of-poly-monic-normalize
  (equal (f11-poly-leading-coefficient (f11-poly-monic-normalize factor))
         (if (consp (f11-normalize factor)) (gfield::f11-one)
           (gfield::f11-zero)))
  :rule-classes nil)
(def-f11-stack-law f11-poly-divides-p-of-poly-monic-normalize-divisor-for-irreducibility
  finite-field-poly-divides-p-of-poly-monic-normalize-divisor
  (equal (f11-poly-divides-p (f11-poly-monic-normalize divisor) dividend)
         (f11-poly-divides-p divisor dividend)))

(defthm f11-poly-reducible-p-of-normalize
  (equal (f11-poly-reducible-p (f11-normalize poly))
         (f11-poly-reducible-p poly))
  :hints (("Goal"
           :use ((:instance f11-poly-reducible-p-suff
                            (poly (f11-normalize poly))
                            (left (mv-nth 0 (f11-poly-reducible-p-witness poly)))
                            (right (mv-nth 1 (f11-poly-reducible-p-witness poly))))
                 (:instance f11-poly-reducible-p-suff
                            (poly poly)
                            (left (mv-nth 0 (f11-poly-reducible-p-witness
                                             (f11-normalize poly))))
                            (right (mv-nth 1 (f11-poly-reducible-p-witness
                                              (f11-normalize poly))))))
           :in-theory (disable f11-poly-reducible-p-suff
                               f11-poly-mul f11-normalize))))

(defthm f11-poly-irreducible-p-of-normalize
  (equal (f11-poly-irreducible-p (f11-normalize poly))
         (f11-poly-irreducible-p poly))
  :hints (("Goal" :use ((:instance f11-poly-reducible-p-of-normalize)
                         (:instance f11-poly-degree-of-normalize-for-irreducibility
                                    (polynomial poly)))
           :in-theory (e/d (f11-poly-irreducible-p)
                           (f11-poly-reducible-p f11-poly-degree f11-normalize)))))

(defthm f11-poly-irreducible-p-implies-positive-degree
  (implies (f11-poly-irreducible-p poly) (< 0 (f11-poly-degree poly)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :use ((:instance f11-poly-irreducible-p-definition))
           :in-theory (theory 'minimal-theory))))

(defthm f11-poly-irreducible-p-factor-characterization
  (implies (and (f11-poly-irreducible-p poly)
                (equal (f11-poly-mul left right) (f11-normalize poly)))
           (or (f11-poly-unit-p left) (f11-poly-unit-p right)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-irreducible-p-definition)
                         (:instance f11-poly-reducible-p-suff
                                    (poly poly) (left left) (right right)))
           :in-theory (theory 'minimal-theory))))

(local
 (defthm positive-integer-summands-of-four-have-small-summand
   (implies (and (integerp a) (integerp b) (< 0 a) (< 0 b)
                 (equal (+ a b) 4))
            (or (or (equal a 1) (equal a 2))
                (or (equal b 1) (equal b 2))))
   :rule-classes nil
   :hints (("Goal" :cases ((<= 3 a) (<= 3 b))))))

(local
 (defthm f11-normalized-nonunit-factor-positive-degree
   (implies (and (consp (f11-normalize factor))
                 (not (f11-poly-unit-p factor)))
            (< 0 (f11-poly-degree (f11-normalize factor))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance f11-poly-degree-of-normalize-for-irreducibility
                                    (polynomial factor)))
            :in-theory (enable f11-poly-unit-p f11-poly-degree)))))

(local
 (defthm f11-left-factor-divides-exact-product
   (f11-poly-divides-p left (f11-poly-mul left right))
   :rule-classes nil
   :hints (("Goal" :use ((:instance f11-poly-divides-p-of-multiple-for-irreducibility
                                    (divisor left) (multiplier right))
                          (:instance f11-poly-mul-commutative-for-irreducibility))
            :in-theory (disable f11-poly-divides-p f11-poly-mul)))))

(local
 (defthm f11-poly-mul-zero-normalized-left
   (implies (not (consp (f11-normalize left)))
            (equal (f11-poly-mul left right) nil))
   :hints (("Goal" :use ((:instance f11-poly-mul-normalize-left-for-irreducibility))
            :in-theory (enable f11-poly-mul f11-poly-raw-mul)))))
(local
 (defthm f11-poly-mul-zero-normalized-right
   (implies (not (consp (f11-normalize right)))
            (equal (f11-poly-mul left right) nil))
   :hints (("Goal" :use ((:instance f11-poly-mul-normalize-right-for-irreducibility))
            :in-theory (enable f11-poly-mul f11-poly-raw-mul)))))

(local
 (defthm f11-reducible-quartic-factor-data
   (implies (and (equal (f11-normalize poly) poly)
                 (equal (f11-poly-degree poly) 4)
                 (f11-poly-reducible-p poly))
            (let* ((left (f11-normalize
                          (mv-nth 0 (f11-poly-reducible-p-witness poly))))
                   (right (f11-normalize
                           (mv-nth 1 (f11-poly-reducible-p-witness poly)))))
              (and (consp left) (consp right)
                   (< 0 (f11-poly-degree left))
                   (< 0 (f11-poly-degree right))
                   (equal (+ (f11-poly-degree left)
                             (f11-poly-degree right)) 4)
                   (f11-poly-divides-p left poly)
                   (f11-poly-divides-p right poly))))
   :rule-classes nil
   :hints
   (("Goal" :use ((:instance f11-poly-reducible-p (poly poly))
                    (:instance f11-poly-mul-zero-normalized-left
                              (left (mv-nth 0 (f11-poly-reducible-p-witness poly)))
                              (right (mv-nth 1 (f11-poly-reducible-p-witness poly))))
                    (:instance f11-poly-mul-zero-normalized-right
                              (left (mv-nth 0 (f11-poly-reducible-p-witness poly)))
                              (right (mv-nth 1 (f11-poly-reducible-p-witness poly)))))
     :in-theory (disable f11-poly-reducible-p f11-poly-unit-p
                         f11-poly-mul f11-normalize))
    ("Goal'" :use ((:instance f11-poly-mul-normalize-left-for-irreducibility
                              (left (mv-nth 0 (f11-poly-reducible-p-witness poly)))
                              (right (f11-normalize
                                      (mv-nth 1 (f11-poly-reducible-p-witness poly)))))
                    (:instance f11-poly-mul-normalize-right-for-irreducibility
                              (left (mv-nth 0 (f11-poly-reducible-p-witness poly)))
                              (right (mv-nth 1 (f11-poly-reducible-p-witness poly)))))
     :in-theory (disable f11-poly-mul f11-normalize))
    ("Goal''" :use ((:instance f11-normalized-nonunit-factor-positive-degree
                               (factor (mv-nth 0 (f11-poly-reducible-p-witness poly))))
                     (:instance f11-normalized-nonunit-factor-positive-degree
                               (factor (mv-nth 1 (f11-poly-reducible-p-witness poly))))
                     (:instance f11-poly-degree-of-poly-mul-for-irreducibility
                               (left (f11-normalize
                                      (mv-nth 0 (f11-poly-reducible-p-witness poly))))
                               (right (f11-normalize
                                       (mv-nth 1 (f11-poly-reducible-p-witness poly)))))
                     (:instance f11-left-factor-divides-exact-product
                               (left (f11-normalize
                                      (mv-nth 0 (f11-poly-reducible-p-witness poly))))
                               (right (f11-normalize
                                       (mv-nth 1 (f11-poly-reducible-p-witness poly)))))
                     (:instance f11-left-factor-divides-exact-product
                               (left (f11-normalize
                                      (mv-nth 1 (f11-poly-reducible-p-witness poly))))
                               (right (f11-normalize
                                       (mv-nth 0 (f11-poly-reducible-p-witness poly)))))
                     (:instance f11-poly-mul-commutative-for-irreducibility
                               (left (mv-nth 0 (f11-poly-reducible-p-witness poly)))
                               (right (mv-nth 1 (f11-poly-reducible-p-witness poly))))
                     (:instance f11-poly-divides-p-of-normalize-dividend-for-irreducibility
                               (divisor (f11-normalize
                                         (mv-nth 0 (f11-poly-reducible-p-witness poly))))
                               (dividend poly))
                     (:instance f11-poly-divides-p-of-normalize-dividend-for-irreducibility
                               (divisor (f11-normalize
                                         (mv-nth 1 (f11-poly-reducible-p-witness poly))))
                               (dividend poly)))
     :in-theory (disable f11-poly-degree f11-poly-divides-p f11-poly-mul
                         f11-normalize f11-poly-unit-p)))))

(local
 (defthm f11-small-factor-witness-from-normalized-factor
   (implies (and (f11-canonical-polynomial-p factor) (consp factor)
                 (or (equal (f11-poly-degree factor) 1)
                     (equal (f11-poly-degree factor) 2))
                 (f11-poly-divides-p factor poly))
            (f11-poly-has-small-monic-factor-p poly))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance f11-poly-has-small-monic-factor-p-suff
                             (factor (f11-poly-monic-normalize factor)))
                  (:instance f11-poly-degree-of-poly-monic-normalize-when-nonzero)
                  (:instance f11-consp-of-poly-monic-normalize-for-irreducibility)
                  (:instance f11-poly-leading-coefficient-of-poly-monic-normalize-for-irreducibility)
                  (:instance f11-poly-divides-p-of-poly-monic-normalize-divisor-for-irreducibility
                             (divisor factor) (dividend poly)))
            :in-theory (disable f11-poly-has-small-monic-factor-p-suff
                                f11-poly-monic-normalize f11-poly-degree
                                f11-poly-leading-coefficient f11-poly-divides-p
                                f11-normalize)))))

(defthm f11-poly-reducible-normalized-quartic-implies-small-monic-factor
  (implies (and (equal (f11-normalize poly) poly)
                (equal (f11-poly-degree poly) 4)
                (f11-poly-reducible-p poly))
           (f11-poly-has-small-monic-factor-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use (f11-reducible-quartic-factor-data
                 (:instance positive-integer-summands-of-four-have-small-summand
                            (a (f11-poly-degree
                                (f11-normalize
                                 (mv-nth 0 (f11-poly-reducible-p-witness poly)))))
                            (b (f11-poly-degree
                                (f11-normalize
                                 (mv-nth 1 (f11-poly-reducible-p-witness poly))))))
                 (:instance f11-small-factor-witness-from-normalized-factor
                            (factor (f11-normalize
                                     (mv-nth 0 (f11-poly-reducible-p-witness poly)))))
                 (:instance f11-small-factor-witness-from-normalized-factor
                            (factor (f11-normalize
                                     (mv-nth 1 (f11-poly-reducible-p-witness poly))))))
           :in-theory (disable f11-poly-reducible-p
                               f11-poly-has-small-monic-factor-p
                               f11-poly-degree f11-normalize))))

(defthm f11-poly-degree-four-without-small-monic-factor-is-irreducible
  (implies (and (equal (f11-normalize poly) poly)
                (equal (f11-poly-degree poly) 4)
                (not (f11-poly-has-small-monic-factor-p poly)))
           (f11-poly-irreducible-p poly))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-irreducible-p-definition)
                         (:instance f11-poly-reducible-normalized-quartic-implies-small-monic-factor))
           :in-theory (theory 'minimal-theory))))
