(in-package "GPOLY")
(include-book "euclidean")

; The raw extended Euclidean computation follows the same remainder chain as
; POLY-EUCLIDEAN-GCD.  The single POLY-DIVMOD call supplies both values needed
; by the coefficient update and recursive descent.
(defun poly-extended-euclidean-gcd (first second)
  (declare
   (xargs
    :measure (len (normalize second))
    :hints
    (("Goal"
      :use ((:instance normalize-poly-remainder-strict-length-bound
                       (dividend first) (modulus second))
            (:instance poly-remainder-is-divmod-remainder
                       (dividend first) (modulus second)))
      :in-theory (disable normalize poly-remainder poly-divmod)))))
  (if (consp (normalize second))
      (mv-let (quotient remainder)
        (poly-divmod first second)
        (mv-let (gcd s-next t-next)
          (poly-extended-euclidean-gcd second remainder)
          (mv gcd
              t-next
              (poly-sub s-next (poly-mul t-next quotient)))))
    (mv (normalize first) (polynomial-one) nil)))

(defthm poly-extended-euclidean-gcd-zero-second
  (implies (not (consp (normalize second)))
           (equal (poly-extended-euclidean-gcd first second)
                  (mv (normalize first) (polynomial-one) nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (poly-extended-euclidean-gcd)
                                      (normalize polynomial-one)))))

(defthm poly-extended-euclidean-gcd-nonzero-second
  (implies
   (consp (normalize second))
   (equal
    (poly-extended-euclidean-gcd first second)
    (mv-let (quotient remainder)
      (poly-divmod first second)
      (mv-let (gcd s-next t-next)
        (poly-extended-euclidean-gcd second remainder)
        (mv gcd t-next
            (poly-sub s-next (poly-mul t-next quotient)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (poly-extended-euclidean-gcd)
                                      (poly-divmod normalize poly-sub poly-mul)))))

(local
 (defthm poly-extended-euclidean-gcd-projections-canonical
   (and (canonical-polynomial-p
         (mv-nth 0 (poly-extended-euclidean-gcd first second)))
        (canonical-polynomial-p
         (mv-nth 1 (poly-extended-euclidean-gcd first second)))
        (canonical-polynomial-p
         (mv-nth 2 (poly-extended-euclidean-gcd first second))))
   :hints (("Goal"
            :induct (poly-extended-euclidean-gcd first second)
            :in-theory (e/d (poly-extended-euclidean-gcd)
                            (normalize poly-divmod))))))

(defthm poly-extended-euclidean-gcd-gcd-canonical
  (canonical-polynomial-p
   (mv-nth 0 (poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use poly-extended-euclidean-gcd-projections-canonical)))

(defthm poly-extended-euclidean-gcd-first-coefficient-canonical
  (canonical-polynomial-p
   (mv-nth 1 (poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use poly-extended-euclidean-gcd-projections-canonical)))

(defthm poly-extended-euclidean-gcd-second-coefficient-canonical
  (canonical-polynomial-p
   (mv-nth 2 (poly-extended-euclidean-gcd first second)))
  :hints (("Goal" :use poly-extended-euclidean-gcd-projections-canonical)))

(defthm normalize-of-poly-extended-euclidean-gcd-gcd
  (equal (normalize
          (mv-nth 0 (poly-extended-euclidean-gcd first second)))
         (mv-nth 0 (poly-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :use ((:instance normalize-when-canonical
                            (xs (mv-nth 0
                                  (poly-extended-euclidean-gcd first second))))
                 (:instance poly-extended-euclidean-gcd-gcd-canonical)))))

(defthm normalize-of-poly-extended-euclidean-gcd-first-coefficient
  (equal (normalize
          (mv-nth 1 (poly-extended-euclidean-gcd first second)))
         (mv-nth 1 (poly-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :use ((:instance normalize-when-canonical
                            (xs (mv-nth 1
                                  (poly-extended-euclidean-gcd first second))))
                 (:instance
                  poly-extended-euclidean-gcd-first-coefficient-canonical)))))

(defthm normalize-of-poly-extended-euclidean-gcd-second-coefficient
  (equal (normalize
          (mv-nth 2 (poly-extended-euclidean-gcd first second)))
         (mv-nth 2 (poly-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :use ((:instance normalize-when-canonical
                            (xs (mv-nth 2
                                  (poly-extended-euclidean-gcd first second))))
                 (:instance
                  poly-extended-euclidean-gcd-second-coefficient-canonical)))))

(defthm poly-extended-euclidean-gcd-gcd-is-poly-euclidean-gcd
  (equal (mv-nth 0 (poly-extended-euclidean-gcd first second))
         (poly-euclidean-gcd first second))
  :hints (("Goal"
           :induct (poly-extended-euclidean-gcd first second)
           :in-theory (e/d (poly-extended-euclidean-gcd
                            poly-euclidean-gcd poly-remainder)
                           (poly-divmod normalize)))))

(local
 (defthm poly-extended-euclidean-gcd-bezout-step
   (implies
    (and (equal (poly-add (poly-mul quotient second) remainder)
                (normalize first))
         (equal (poly-add (poly-mul s-next second)
                          (poly-mul t-next remainder))
                gcd))
    (equal
     (poly-add
      (poly-mul t-next first)
      (poly-mul (poly-sub s-next (poly-mul t-next quotient)) second))
     gcd))
   :hints
   (("Goal"
     :use ((:instance poly-mul-right-distributive
                      (x s-next) (y (poly-neg (poly-mul t-next quotient)))
                      (z second))
           (:instance poly-mul-associative
                      (x t-next) (y quotient) (z second))
           (:instance poly-mul-of-poly-neg-left
                      (x (poly-mul t-next quotient)) (y second))
           (:instance poly-add-associative
                      (x (poly-mul t-next first))
                      (y (poly-mul s-next second))
                      (z (poly-neg (poly-mul (poly-mul t-next quotient)
                                             second))))
           (:instance poly-add-commutative
                      (x (poly-mul t-next first))
                      (y (poly-mul s-next second)))
           (:instance poly-mul-left-distributive
                      (x t-next) (y (poly-mul quotient second))
                      (z remainder))
           (:instance poly-mul-normalize-right
                      (x t-next) (y first))
           (:instance poly-add-inverse-right
                      (x (poly-mul t-next (poly-mul quotient second))))
           (:instance poly-add-zero-right
                      (x (poly-mul t-next remainder)))
           (:instance poly-add-associative
                      (x (poly-mul t-next (poly-mul quotient second)))
                      (y (poly-mul t-next remainder))
                      (z (poly-neg
                          (poly-mul t-next (poly-mul quotient second)))))
           (:instance poly-add-associative
                      (x (poly-mul t-next remainder))
                      (y (poly-mul t-next (poly-mul quotient second)))
                      (z (poly-neg
                          (poly-mul t-next (poly-mul quotient second)))))
           (:instance poly-add-commutative
                      (x (poly-mul t-next (poly-mul quotient second)))
                      (y (poly-mul t-next remainder)))
           (:instance poly-add-associative
                      (x (poly-mul s-next second))
                      (y (poly-mul t-next first))
                      (z (poly-mul (poly-neg (poly-mul t-next quotient))
                                   second))))
     :in-theory (e/d (poly-sub-definition)
                     (poly-divmod poly-add poly-mul poly-neg normalize
                      poly-add-associative poly-add-commutative))))))

(defthm poly-extended-euclidean-gcd-bezout
  (equal
   (poly-add
    (poly-mul
     (mv-nth 1 (poly-extended-euclidean-gcd first second)) first)
    (poly-mul
     (mv-nth 2 (poly-extended-euclidean-gcd first second)) second))
   (mv-nth 0 (poly-extended-euclidean-gcd first second)))
  :hints (("Goal"
           :induct (poly-extended-euclidean-gcd first second)
           :in-theory (e/d (poly-extended-euclidean-gcd)
                           (poly-divmod normalize poly-add poly-mul poly-sub
                            poly-sub-definition
                            poly-extended-euclidean-gcd-gcd-is-poly-euclidean-gcd)))
          ("Subgoal *1/1"
           :use ((:instance poly-divmod-reconstruction
                            (f first) (g second))
                 (:instance poly-extended-euclidean-gcd-bezout-step
                            (quotient (mv-nth 0 (poly-divmod first second)))
                            (remainder (mv-nth 1 (poly-divmod first second)))
                            (gcd (mv-nth 0
                                  (poly-extended-euclidean-gcd
                                   second
                                   (mv-nth 1 (poly-divmod first second)))))
                            (s-next (mv-nth 1
                                     (poly-extended-euclidean-gcd
                                      second
                                      (mv-nth 1 (poly-divmod first second)))))
                            (t-next (mv-nth 2
                                     (poly-extended-euclidean-gcd
                                      second
                                      (mv-nth 1 (poly-divmod first second))))))))))

(defthm poly-extended-euclidean-gcd-bezout-with-euclidean-gcd
  (equal
   (poly-add
    (poly-mul
     (mv-nth 1 (poly-extended-euclidean-gcd first second)) first)
    (poly-mul
     (mv-nth 2 (poly-extended-euclidean-gcd first second)) second))
   (poly-euclidean-gcd first second))
  :hints (("Goal"
           :use ((:instance poly-extended-euclidean-gcd-bezout)
                 (:instance
                  poly-extended-euclidean-gcd-gcd-is-poly-euclidean-gcd)))))

; Focused executable-shape regressions over the constrained field.  They use
; only zero, one, and constructed polynomial operations, so their exact triples
; do not depend on a concrete field representation.
(defthm poly-extended-euclidean-gcd-regression-zero-zero
  (equal (poly-extended-euclidean-gcd nil nil)
         (mv nil (polynomial-one) nil)))

(defthm poly-extended-euclidean-gcd-regression-first-zero
  (equal (poly-extended-euclidean-gcd first nil)
         (mv (normalize first) (polynomial-one) nil)))

(defthm poly-extended-euclidean-gcd-regression-zero-nonzero
  (implies (consp (normalize second))
           (equal (poly-extended-euclidean-gcd nil second)
                  (mv (normalize second) nil (polynomial-one))))
  :hints (("Goal"
           :use ((:instance poly-divmod-zero-dividend (g second)))
           :in-theory (e/d (poly-extended-euclidean-gcd)
                           (poly-divmod normalize poly-sub poly-mul)))))

(defthm poly-extended-euclidean-gcd-regression-malformed-atoms
  (equal (poly-extended-euclidean-gcd 'malformed-first 'malformed-second)
         (mv nil (polynomial-one) nil)))

(defthm poly-extended-euclidean-gcd-regression-dotted-list
  (equal (poly-extended-euclidean-gcd
          (cons (gfield::field-one) 'malformed-first-tail)
          (cons (gfield::field-one) 'malformed-second-tail))
         (mv (polynomial-one) nil (polynomial-one))))

(defthm poly-extended-euclidean-gcd-regression-trailing-zero
  (equal (poly-extended-euclidean-gcd
          (list (gfield::field-one) (gfield::field-zero)) nil)
         (mv (polynomial-one) (polynomial-one) nil)))

(defthm poly-extended-euclidean-gcd-regression-field-fix
  (equal (poly-extended-euclidean-gcd
          (list 'malformed-coefficient (gfield::field-one)) nil)
         (mv (normalize
              (list 'malformed-coefficient (gfield::field-one)))
             (polynomial-one) nil)))

(defthm poly-extended-euclidean-gcd-regression-equal-nonzero
  (equal (poly-extended-euclidean-gcd (polynomial-one) (polynomial-one))
         (mv (polynomial-one) nil (polynomial-one))))

(defthm poly-extended-euclidean-gcd-regression-exact-divisibility
  (equal (poly-extended-euclidean-gcd
          (monomial (gfield::field-one) 2)
          (monomial (gfield::field-one) 1))
         (mv (monomial (gfield::field-one) 1)
             nil (polynomial-one))))

(defthm poly-extended-euclidean-gcd-regression-multi-step
  (let ((x (monomial (gfield::field-one) 1)))
    (equal (poly-extended-euclidean-gcd
            (poly-add (poly-mul x x) (polynomial-one)) x)
           (mv (polynomial-one) (polynomial-one) (poly-neg x)))))

(defthm poly-extended-euclidean-gcd-regression-bezout-exact-divisibility
  (let* ((first (monomial (gfield::field-one) 2))
         (second (monomial (gfield::field-one) 1))
         (result (poly-extended-euclidean-gcd first second)))
    (equal (poly-add (poly-mul (mv-nth 1 result) first)
                     (poly-mul (mv-nth 2 result) second))
           (mv-nth 0 result))))

(defthm poly-extended-euclidean-gcd-regression-bezout-multi-step
  (let* ((x (monomial (gfield::field-one) 1))
         (first (poly-add (poly-mul x x) (polynomial-one)))
         (result (poly-extended-euclidean-gcd first x)))
    (equal (poly-add (poly-mul (mv-nth 1 result) first)
                     (poly-mul (mv-nth 2 result) x))
           (mv-nth 0 result))))
