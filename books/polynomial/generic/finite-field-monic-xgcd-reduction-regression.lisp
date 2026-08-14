(in-package "GPOLY")

(include-book "finite-field-monic-xgcd-reduction")

(defthm finite-field-monic-xgcd-coefficient-reduction-minimal-theory-client
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first second)
          (list (gfield::finite-field-one)))
   (equal
    (finite-field-poly-remainder
     (finite-field-poly-mul
      (mv-nth 1
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      first)
     second)
    (finite-field-poly-remainder
     (list (gfield::finite-field-one)) second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-reduction))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-xgcd-remainder-one-minimal-theory-client
  (implies
   (and
    (equal (finite-field-poly-monic-euclidean-gcd first second)
           (list (gfield::finite-field-one)))
    (consp (finite-field-poly-normalize second))
    (< 0 (finite-field-poly-degree
          (finite-field-poly-normalize second))))
   (equal
    (finite-field-poly-remainder
     (finite-field-poly-mul
      (mv-nth 1
              (finite-field-poly-monic-extended-euclidean-gcd first second))
      first)
     second)
    (list (gfield::finite-field-one))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-remainder-one))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-xgcd-reduction-positive-degree-regression
  (let ((first (list (gfield::finite-field-one)
                     (gfield::finite-field-zero)
                     (gfield::finite-field-one)))
        (second (list (gfield::finite-field-zero)
                      (gfield::finite-field-one))))
    (implies
     (and (equal (finite-field-poly-monic-euclidean-gcd first second)
                 (list (gfield::finite-field-one)))
          (consp (finite-field-poly-normalize second))
          (< 0 (finite-field-poly-degree
                (finite-field-poly-normalize second))))
     (equal
      (finite-field-poly-remainder
       (finite-field-poly-mul
        (mv-nth 1
                (finite-field-poly-monic-extended-euclidean-gcd first second))
        first)
       second)
      (list (gfield::finite-field-one)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-remainder-one
      (first (list (gfield::finite-field-one)
                   (gfield::finite-field-zero)
                   (gfield::finite-field-one)))
      (second (list (gfield::finite-field-zero)
                    (gfield::finite-field-one)))))
    :in-theory (theory 'minimal-theory))))

(defthm finite-field-monic-xgcd-multistep-reduction-regression
  (implies
   (equal (finite-field-poly-monic-euclidean-gcd first second)
          (list (gfield::finite-field-one)))
   (let ((result
          (finite-field-poly-monic-extended-euclidean-gcd first second)))
     (and
      (equal
       (finite-field-poly-add
        (finite-field-poly-mul (mv-nth 1 result) first)
        (finite-field-poly-mul (mv-nth 2 result) second))
       (list (gfield::finite-field-one)))
      (equal
       (finite-field-poly-remainder
        (finite-field-poly-mul (mv-nth 1 result) first) second)
       (finite-field-poly-remainder
        (list (gfield::finite-field-one)) second)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance
      finite-field-poly-monic-extended-euclidean-gcd-bezout-when-one)
     (:instance
      finite-field-poly-monic-extended-euclidean-gcd-first-coefficient-reduction))
    :in-theory (theory 'minimal-theory))))

(local
 (defthm finite-field-singleton-one-canonical-reduction-regression
   (finite-field-canonical-polynomial-p
    (list (gfield::finite-field-one)))
   :hints
   (("Goal"
     :in-theory
     (enable finite-field-canonical-polynomial-p
             finite-field-poly-leading-coefficient)))))

(local
 (defthm finite-field-modulus-normalization-reduction-regressions
   (and
    (equal (finite-field-poly-normalize 'malformed-modulus) nil)
    (equal (finite-field-poly-normalize
            (list (gfield::finite-field-zero)
                  (gfield::finite-field-zero)))
           nil)
    (equal (finite-field-poly-normalize
            (list (gfield::finite-field-zero)
                  (gfield::finite-field-one)
                  (gfield::finite-field-zero)))
           (list (gfield::finite-field-zero)
                 (gfield::finite-field-one))))
   :hints
   (("Goal"
     :in-theory
     (enable finite-field-poly-normalize
             finite-field-poly-trim-trailing-zeros)))))

(local
 (defthm finite-field-trailing-zero-modulus-positive-degree-regression
   (and
    (consp
     (finite-field-poly-normalize
      (list (gfield::finite-field-zero)
            (gfield::finite-field-one)
            (gfield::finite-field-zero))))
    (< 0
       (finite-field-poly-degree
        (finite-field-poly-normalize
         (list (gfield::finite-field-zero)
               (gfield::finite-field-one)
               (gfield::finite-field-zero))))))
   :hints
   (("Goal"
     :use ((:instance finite-field-modulus-normalization-reduction-regressions))
     :in-theory (enable finite-field-poly-degree)))))

(defthm finite-field-polynomial-one-total-remainder-regressions
  (let ((one (list (gfield::finite-field-one)))
        (x-with-trailing-zero
         (list (gfield::finite-field-zero)
               (gfield::finite-field-one)
               (gfield::finite-field-zero))))
    (and
     (equal (finite-field-poly-remainder one one) nil)
     (equal (finite-field-poly-remainder one nil) one)
     (equal (finite-field-poly-remainder one 'malformed-modulus) one)
     (equal (finite-field-poly-remainder
             one (list (gfield::finite-field-zero)
                       (gfield::finite-field-zero)))
            one)
     (equal (finite-field-poly-remainder one x-with-trailing-zero) one)))
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-remainder-self
                (modulus (list (gfield::finite-field-one))))
     (:instance finite-field-poly-normalize-when-canonical
                (xs (list (gfield::finite-field-one))))
     (:instance finite-field-singleton-one-canonical-reduction-regression)
     (:instance finite-field-modulus-normalization-reduction-regressions)
     (:instance finite-field-trailing-zero-modulus-positive-degree-regression)
     (:instance finite-field-poly-remainder-zero-normalized-modulus
                (dividend (list (gfield::finite-field-one)))
                (modulus nil))
     (:instance finite-field-poly-remainder-zero-normalized-modulus
                (dividend (list (gfield::finite-field-one)))
                (modulus 'malformed-modulus))
     (:instance finite-field-poly-remainder-zero-normalized-modulus
                (dividend (list (gfield::finite-field-one)))
                (modulus (list (gfield::finite-field-zero)
                               (gfield::finite-field-zero))))
     (:instance
      finite-field-poly-remainder-of-polynomial-one-when-positive-degree
      (modulus (list (gfield::finite-field-zero)
                     (gfield::finite-field-one)
                     (gfield::finite-field-zero)))))
    :in-theory
    (union-theories
     (theory 'finite-field-poly-definition-theory)
     (union-theories
      (theory 'gfield::finite-field-context-instance-theory)
      (theory 'minimal-theory))))))

(local
 (defthm finite-field-negative-one-nonzero-reduction-regression
   (not (equal (gfield::finite-field-neg (gfield::finite-field-one))
               (gfield::finite-field-zero)))
   :hints
   (("Goal"
     :use
     ((:instance gfield::finite-field-add-inverse-left
                 (x (gfield::finite-field-one)))
      (:instance gfield::finite-field-add-zero-left
                 (x (gfield::finite-field-one)))
      (:instance gfield::finite-field-zero-not-equal-finite-field-one))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(gfield::finite-field-fix-of-one
        gfield::finite-field-add-zero-left))))))

(defthm finite-field-polynomial-one-modulo-negative-one-regression
  (equal
   (finite-field-poly-remainder
    (list (gfield::finite-field-one))
    (list (gfield::finite-field-neg (gfield::finite-field-one))))
   nil)
  :hints
  (("Goal"
    :use
    ((:instance finite-field-poly-remainder-of-poly-add-divisor-multiple
                (dividend nil)
                (multiplier
                 (list (gfield::finite-field-neg
                        (gfield::finite-field-one))))
                (modulus
                 (list (gfield::finite-field-neg
                        (gfield::finite-field-one)))))
     (:instance finite-field-poly-remainder-zero-dividend
                (modulus
                 (list (gfield::finite-field-neg
                        (gfield::finite-field-one)))))
     (:instance finite-field-poly-mul-of-poly-neg-left-total
                (x (list (gfield::finite-field-one)))
                (y (list (gfield::finite-field-neg
                          (gfield::finite-field-one)))))
     (:instance gfield::finite-field-neg-of-neg
                (x (gfield::finite-field-one)))
     (:instance gfield::finite-field-add-inverse-left
                (x (gfield::finite-field-one)))
     (:instance gfield::finite-field-add-zero-left
                (x (gfield::finite-field-one)))
     (:instance finite-field-negative-one-nonzero-reduction-regression))
    :in-theory
    (enable finite-field-poly-neg finite-field-poly-raw-neg
            finite-field-poly-add finite-field-poly-raw-add
            finite-field-poly-mul-one-left-for-remainder-self))))

(defthm finite-field-monic-xgcd-reduction-nontrivial-gcd-regression
  (let ((one (list (gfield::finite-field-one)))
        (linear (list (gfield::finite-field-one)
                      (gfield::finite-field-one))))
    (not (equal (finite-field-poly-monic-euclidean-gcd linear nil)
                one)))
  :hints
  (("Goal"
    :in-theory
    (enable finite-field-poly-monic-euclidean-gcd
            finite-field-poly-euclidean-gcd
            finite-field-poly-monic-normalize))))
