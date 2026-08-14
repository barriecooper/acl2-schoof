(in-package "GPOLY")

(include-book "finite-field-monic-xgcd")

(defthm finite-field-monic-xgcd-minimal-theory-client
  (and
   (equal
    (mv-nth 0
            (finite-field-poly-monic-extended-euclidean-gcd first second))
    (finite-field-poly-monic-euclidean-gcd first second))
   (equal
    (finite-field-poly-add
     (finite-field-poly-mul
      (mv-nth 1
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      first)
     (finite-field-poly-mul
      (mv-nth 2
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      second))
    (finite-field-poly-monic-euclidean-gcd first second))
   (finite-field-canonical-polynomial-p
    (mv-nth 0
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (finite-field-canonical-polynomial-p
    (mv-nth 1
            (finite-field-poly-monic-extended-euclidean-gcd first second)))
   (finite-field-canonical-polynomial-p
    (mv-nth 2
            (finite-field-poly-monic-extended-euclidean-gcd first second))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-monic-extended-euclidean-gcd-specification))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-xgcd-total-boundary-regressions
  (let ((one (list (gfield::finite-field-one))))
    (and
     (equal (finite-field-poly-extended-euclidean-gcd nil nil)
            (mv nil one nil))
     (equal (finite-field-poly-monic-extended-euclidean-gcd nil nil)
            (mv nil nil nil))
     (equal (finite-field-poly-monic-extended-euclidean-gcd one nil)
            (mv one one nil))
     (equal (finite-field-poly-monic-extended-euclidean-gcd nil one)
            (mv one nil one))
     (equal (finite-field-poly-monic-extended-euclidean-gcd
             'malformed-first 'malformed-second)
            (mv nil nil nil))
     (equal (finite-field-poly-monic-extended-euclidean-gcd
             (cons (gfield::finite-field-one) 'malformed-tail) nil)
            (mv one one nil))
     (equal (finite-field-poly-monic-extended-euclidean-gcd
             (list (gfield::finite-field-one)
                   (gfield::finite-field-zero)) nil)
            (mv one one nil))
     (equal (finite-field-poly-monic-extended-euclidean-gcd
             (list 'malformed-coefficient
                   (gfield::finite-field-zero)) nil)
            (mv (finite-field-poly-monic-normalize
                 (list 'malformed-coefficient))
                (finite-field-poly-scale
                 (gfield::finite-field-inv
                  (finite-field-poly-leading-coefficient
                   (list 'malformed-coefficient)))
                 one)
                nil))))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (enable finite-field-poly-monic-extended-euclidean-gcd
            finite-field-poly-extended-euclidean-gcd
            finite-field-poly-monic-normalize))))

; This wrapper-shape client records common-scalar plumbing only; it does not
; claim that this particular already-monic input makes rescaling nontrivial.
(defthm finite-field-monic-xgcd-multistep-common-scaling-regression
  (let* ((one (list (gfield::finite-field-one)))
         (x (finite-field-poly-monomial
             (gfield::finite-field-one) 1))
         (first (finite-field-poly-add
                 (finite-field-poly-mul x x) one))
         (second x)
         (raw (finite-field-poly-extended-euclidean-gcd first second))
         (scale
          (gfield::finite-field-inv
           (finite-field-poly-leading-coefficient (mv-nth 0 raw))))
         (monic
          (finite-field-poly-monic-extended-euclidean-gcd first second)))
    (and
     (equal (mv-nth 0 monic)
            (finite-field-poly-monic-normalize (mv-nth 0 raw)))
     (equal (mv-nth 1 monic)
            (finite-field-poly-scale scale (mv-nth 1 raw)))
     (equal (mv-nth 2 monic)
            (finite-field-poly-scale scale (mv-nth 2 raw)))))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory
    (enable finite-field-poly-monic-extended-euclidean-gcd))))

; This general client covers nonmonic constants and linear gcds without adding
; an unjustified concrete finite-field characteristic assumption.
(defthm finite-field-monic-xgcd-nonzero-result-is-monic-regression
  (implies
   (consp (finite-field-poly-euclidean-gcd first second))
   (equal
    (finite-field-poly-leading-coefficient
     (mv-nth 0
             (finite-field-poly-monic-extended-euclidean-gcd first second)))
    (gfield::finite-field-one)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-leading-coefficient-of-poly-monic-extended-euclidean-gcd))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-xgcd-reconstruction-regression
  (let* ((result
          (finite-field-poly-monic-extended-euclidean-gcd first second)))
    (and
     (equal (mv-nth 0 result)
            (finite-field-poly-monic-euclidean-gcd first second))
     (equal
      (finite-field-poly-add
       (finite-field-poly-mul (mv-nth 1 result) first)
       (finite-field-poly-mul (mv-nth 2 result) second))
      (mv-nth 0 result))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-gcd-is-monic-euclidean-gcd)
     (:instance finite-field-poly-monic-extended-euclidean-gcd-bezout))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-xgcd-polynomial-one-bezout-regression
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first second)
          (list (gfield::finite-field-one)))
   (equal
    (finite-field-poly-add
     (finite-field-poly-mul
      (mv-nth 1
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      first)
     (finite-field-poly-mul
      (mv-nth 2
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      second))
    (list (gfield::finite-field-one))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-bezout-when-one))
    :in-theory (theory 'minimal-theory))))
