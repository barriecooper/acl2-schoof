(in-package "GPOLY")

(include-book "finite-field-divmod")
(local (include-book "division"))

(local (in-theory (disable finite-field-poly-divmod-core
                           finite-field-poly-divmod
                           finite-field-poly-division-step-core
                           finite-field-poly-add
                           finite-field-poly-mul
                           finite-field-poly-normalize
                           finite-field-poly-raw-add
                           finite-field-poly-raw-mul)))

(defthm finite-field-poly-remainder-canonical
  (finite-field-canonical-polynomial-p
   (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :use ((:instance finite-field-canonical-polynomial-p-of-poly-remainder
                                  (f dividend) (g modulus))))))

(defthm finite-field-poly-normalize-of-remainder
  (equal (finite-field-poly-normalize
          (finite-field-poly-remainder dividend modulus))
         (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :use ((:instance finite-field-poly-remainder-canonical)
                         (:instance finite-field-poly-normalize-when-canonical
                                  (xs (finite-field-poly-remainder dividend modulus))))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-remainder-of-normalize-dividend
  (equal (finite-field-poly-remainder
          (finite-field-poly-normalize dividend) modulus)
         (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :in-theory (e/d (finite-field-poly-remainder
                                    finite-field-poly-divmod)
                                   (finite-field-poly-divmod-core
                                    finite-field-poly-normalize)))))

(defthm finite-field-poly-remainder-of-normalize-modulus
  (equal (finite-field-poly-remainder
          dividend (finite-field-poly-normalize modulus))
         (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :in-theory (e/d (finite-field-poly-remainder
                                    finite-field-poly-divmod)
                                   (finite-field-poly-divmod-core
                                    finite-field-poly-normalize)))))

(defthm finite-field-poly-divmod-zero-divisor
  (equal (finite-field-poly-divmod f nil)
         (mv nil (finite-field-poly-normalize f)))
  :hints (("Goal" :in-theory (enable finite-field-poly-divmod
                                      finite-field-poly-divmod-core))))

(defthm finite-field-poly-divmod-zero-dividend
  (equal (finite-field-poly-divmod nil g) (mv nil nil))
  :hints (("Goal" :in-theory (enable finite-field-poly-divmod
                                      finite-field-poly-divmod-core
                                      finite-field-poly-normalize))))

(defthm finite-field-poly-remainder-zero-modulus
  (equal (finite-field-poly-remainder dividend nil)
         (finite-field-poly-normalize dividend))
  :hints (("Goal" :use ((:instance finite-field-poly-divmod-zero-divisor
                                  (f dividend)))
           :in-theory (enable finite-field-poly-remainder))))

(defthm finite-field-poly-normalize-equal-nil-when-not-consp
  (implies (not (consp (finite-field-poly-normalize xs)))
           (equal (finite-field-poly-normalize xs) nil))
  :hints (("Goal" :use ((:instance finite-field-canonical-polynomial-atom-is-nil
                                  (p (finite-field-poly-normalize xs)))
                         (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                                  (xs xs)))
           :in-theory (disable finite-field-poly-normalize
                               finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-divmod-zero-normalized-divisor
  (implies (equal (finite-field-poly-normalize g) nil)
           (equal (finite-field-poly-divmod f g)
                  (mv nil (finite-field-poly-normalize f))))
  :hints (("Goal" :in-theory (enable finite-field-poly-divmod
                                      finite-field-poly-divmod-core))))

(defthm finite-field-poly-remainder-zero-normalized-modulus
  (implies (equal (finite-field-poly-normalize modulus) nil)
           (equal (finite-field-poly-remainder dividend modulus)
                  (finite-field-poly-normalize dividend)))
  :hints (("Goal" :use ((:instance finite-field-poly-divmod-zero-normalized-divisor
                                  (f dividend) (g modulus)))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize))))

(defthm finite-field-poly-remainder-zero-dividend
  (equal (finite-field-poly-remainder nil modulus) nil)
  :hints (("Goal" :use ((:instance finite-field-poly-divmod-zero-dividend
                                  (g modulus)))
           :in-theory (enable finite-field-poly-remainder))))


(local
 (defthm len-positive-when-consp
   (implies (consp x)
            (< 0 (len x)))))

(defthm finite-field-poly-remainder-strict-length-bound
  (implies (consp (finite-field-poly-normalize modulus))
           (< (len (finite-field-poly-remainder dividend modulus))
              (len (finite-field-poly-normalize modulus))))
  :rule-classes nil
  :hints (("Goal" :cases ((consp (finite-field-poly-remainder dividend modulus)))
           :use ((:instance finite-field-poly-remainder-canonical)
                 (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs modulus))
                 (:instance finite-field-poly-remainder-degree-bound
                            (f dividend) (g modulus))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-remainder dividend modulus)))
                 (:instance finite-field-poly-degree-when-canonical-nonzero
                            (p (finite-field-poly-normalize modulus))))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-poly-degree
                               finite-field-canonical-polynomial-p))))

(defthm finite-field-poly-remainder-canonical-lower-degree
  (implies (and (finite-field-canonical-polynomial-p dividend)
                (consp (finite-field-poly-normalize modulus))
                (< (finite-field-poly-degree dividend)
                   (finite-field-poly-degree
                    (finite-field-poly-normalize modulus))))
           (equal (finite-field-poly-remainder dividend modulus)
                  dividend))
  :rule-classes nil
  :hints (("Goal" :cases ((<= (finite-field-poly-degree (finite-field-poly-normalize modulus))
                                (finite-field-poly-degree dividend)))
           :use ((:instance finite-field-poly-normalize-when-canonical
                            (xs dividend))
                 (:instance finite-field-canonical-polynomial-p-of-poly-normalize
                            (xs modulus))
                 (:instance finite-field-canonical-polynomial-p-of-nil)
                 (:instance finite-field-poly-degree-when-normalize-consp
                            (poly modulus)))
           :expand ((finite-field-poly-divmod-core nil dividend (finite-field-poly-normalize modulus)))
           :in-theory (e/d (finite-field-poly-remainder
                            finite-field-poly-divmod
                            finite-field-poly-divmod-core)
                           (finite-field-poly-normalize
                            finite-field-canonical-polynomial-p
                            finite-field-poly-degree)))))

(defthm finite-field-poly-remainder-idempotent
  (equal (finite-field-poly-remainder
          (finite-field-poly-remainder dividend modulus)
          modulus)
         (finite-field-poly-remainder dividend modulus))
  :hints (("Goal" :cases ((consp (finite-field-poly-normalize modulus))))
          ("Subgoal 2"
           :use ((:instance finite-field-poly-remainder-zero-normalized-modulus)
                 (:instance finite-field-poly-remainder-zero-normalized-modulus
                            (dividend (finite-field-poly-remainder dividend modulus)))
                 (:instance finite-field-poly-normalize-when-canonical
                            (xs (finite-field-poly-remainder dividend modulus)))
                 (:instance finite-field-poly-remainder-canonical))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-canonical-polynomial-p))
          ("Subgoal 1"
           :use ((:instance finite-field-poly-remainder-degree-bound
                            (f dividend) (g modulus))
                 (:instance finite-field-poly-remainder-canonical-lower-degree
                            (dividend (finite-field-poly-remainder dividend modulus))))
           :in-theory (disable finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-poly-degree
                               finite-field-canonical-polynomial-p))))

(defund finite-field-poly-reduced-p (polynomial modulus)
  (declare (xargs :guard t))
  (equal (finite-field-poly-remainder polynomial modulus)
         polynomial))

(defthm finite-field-poly-reduced-p-definition
  (equal (finite-field-poly-reduced-p polynomial modulus)
         (equal (finite-field-poly-remainder polynomial modulus)
                polynomial))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable finite-field-poly-reduced-p))))

(defthm finite-field-poly-reduced-p-of-remainder
  (finite-field-poly-reduced-p
   (finite-field-poly-remainder polynomial modulus) modulus)
  :hints (("Goal" :use ((:instance finite-field-poly-reduced-p-definition
                                  (polynomial (finite-field-poly-remainder
                                               polynomial modulus)))
                         (:instance finite-field-poly-remainder-idempotent
                                  (dividend polynomial)))
           :in-theory (disable finite-field-poly-reduced-p
                               finite-field-poly-remainder))))

(defthm finite-field-poly-remainder-when-reduced-p
  (implies (finite-field-poly-reduced-p polynomial modulus)
           (equal (finite-field-poly-remainder polynomial modulus)
                  polynomial))
  :hints (("Goal" :use ((:instance finite-field-poly-reduced-p-definition))
           :in-theory (disable finite-field-poly-reduced-p))))

(defthm finite-field-poly-reduced-p-iff-canonical-and-degree-bounded
  (implies
   (consp (finite-field-poly-normalize modulus))
   (equal
    (finite-field-poly-reduced-p polynomial modulus)
    (and (finite-field-canonical-polynomial-p polynomial)
         (or (equal polynomial nil)
             (< (finite-field-poly-degree polynomial)
                (finite-field-poly-degree
                 (finite-field-poly-normalize modulus)))))))
  :rule-classes nil
  :hints (("Goal" :cases ((<= (finite-field-poly-degree (finite-field-poly-normalize modulus))
                                (finite-field-poly-degree polynomial)))
           :use ((:instance finite-field-poly-reduced-p-definition)
                 (:instance finite-field-poly-remainder-canonical
                            (dividend polynomial))
                 (:instance finite-field-poly-remainder-degree-bound
                            (f polynomial) (g modulus))
                 (:instance finite-field-poly-remainder-canonical-lower-degree
                            (dividend polynomial)))
           :in-theory (disable finite-field-poly-reduced-p
                               finite-field-poly-remainder
                               finite-field-poly-normalize
                               finite-field-canonical-polynomial-p
                               finite-field-poly-degree))))

(verify-guards finite-field-poly-reduced-p)
