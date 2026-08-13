(in-package "GPOLY")

(include-book "finite-field-xgcd")

(defthm finite-field-xgcd-minimal-theory-client
  (and
   (equal
    (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second))
    (finite-field-poly-euclidean-gcd first second))
   (equal
    (finite-field-poly-add
     (finite-field-poly-mul
      (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)) first)
     (finite-field-poly-mul
      (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second)) second))
    (finite-field-poly-euclidean-gcd first second))
   (finite-field-canonical-polynomial-p
    (mv-nth 0 (finite-field-poly-extended-euclidean-gcd first second)))
   (finite-field-canonical-polynomial-p
    (mv-nth 1 (finite-field-poly-extended-euclidean-gcd first second)))
   (finite-field-canonical-polynomial-p
    (mv-nth 2 (finite-field-poly-extended-euclidean-gcd first second))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-extended-euclidean-gcd-raw-specification))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-xgcd-zero-zero-regression
  (equal (finite-field-poly-extended-euclidean-gcd nil nil)
         (mv nil (finite-field-polynomial-one-for-xgcd) nil))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-extended-euclidean-gcd-zero-second
                  (first nil) (second nil)))
           :in-theory (enable finite-field-poly-normalize))))

(defthm finite-field-xgcd-nonzero-zero-regression
  (equal
   (finite-field-poly-extended-euclidean-gcd
    (finite-field-polynomial-one-for-xgcd) nil)
   (mv (finite-field-polynomial-one-for-xgcd)
       (finite-field-polynomial-one-for-xgcd) nil))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-extended-euclidean-gcd-zero-second
                  (first (finite-field-polynomial-one-for-xgcd))
                  (second nil)))
           :in-theory
           (enable finite-field-polynomial-one-for-xgcd
                   finite-field-poly-normalize))))

; These instances exercise the total client boundary at representations
; that historically expose fixing and normalization mistakes.
(defmacro def-finite-field-xgcd-client-case (name first second)
  `(defthm ,name
     (and
      (equal (mv-nth 0 (finite-field-poly-extended-euclidean-gcd
                         ,first ,second))
             (finite-field-poly-euclidean-gcd ,first ,second))
      (equal
       (finite-field-poly-add
        (finite-field-poly-mul
         (mv-nth 1 (finite-field-poly-extended-euclidean-gcd
                    ,first ,second)) ,first)
        (finite-field-poly-mul
         (mv-nth 2 (finite-field-poly-extended-euclidean-gcd
                    ,first ,second)) ,second))
       (finite-field-poly-euclidean-gcd ,first ,second))
      (finite-field-canonical-polynomial-p
       (mv-nth 0 (finite-field-poly-extended-euclidean-gcd ,first ,second)))
      (finite-field-canonical-polynomial-p
       (mv-nth 1 (finite-field-poly-extended-euclidean-gcd ,first ,second)))
      (finite-field-canonical-polynomial-p
       (mv-nth 2 (finite-field-poly-extended-euclidean-gcd ,first ,second))))
     :rule-classes nil
     :hints (("Goal"
              :use ((:instance
                     finite-field-poly-extended-euclidean-gcd-raw-specification
                     (first ,first) (second ,second)))
              :in-theory (theory 'minimal-theory)))))

(def-finite-field-xgcd-client-case
  finite-field-xgcd-malformed-atoms-regression
  'bad-first 'bad-second)

(def-finite-field-xgcd-client-case
  finite-field-xgcd-dotted-tails-regression
  (cons (gfield::finite-field-one) 'bad-tail)
  (cons (gfield::finite-field-zero) 'other-tail))

(def-finite-field-xgcd-client-case
  finite-field-xgcd-trailing-zero-regression
  (list (gfield::finite-field-one) (gfield::finite-field-zero))
  (list (gfield::finite-field-one)))

(def-finite-field-xgcd-client-case
  finite-field-xgcd-fixed-coefficient-regression
  (list 'bad-coefficient (gfield::finite-field-one))
  (list (gfield::finite-field-one)))

(def-finite-field-xgcd-client-case
  finite-field-xgcd-equal-inputs-regression
  (finite-field-polynomial-one-for-xgcd)
  (finite-field-polynomial-one-for-xgcd))

(def-finite-field-xgcd-client-case
  finite-field-xgcd-exact-divisibility-regression
  (finite-field-poly-mul
   (finite-field-poly-add
    (finite-field-poly-monomial (gfield::finite-field-one) 1)
    (finite-field-polynomial-one-for-xgcd))
   (finite-field-polynomial-one-for-xgcd))
  (finite-field-polynomial-one-for-xgcd))

(def-finite-field-xgcd-client-case
  finite-field-xgcd-multistep-chain-regression
  (finite-field-poly-add
   (finite-field-poly-monomial (gfield::finite-field-one) 3)
   (finite-field-polynomial-one-for-xgcd))
  (finite-field-poly-add
   (finite-field-poly-monomial (gfield::finite-field-one) 2)
   (finite-field-polynomial-one-for-xgcd)))
