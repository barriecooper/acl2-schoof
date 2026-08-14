(in-package "GPOLY")
(include-book "f11-production-quartic-small-factor")

(defthm f11-reducible-quartic-small-factor-minimal-client
  (implies (and (equal (f11-normalize poly) poly)
                (equal (f11-poly-degree poly) 4)
                (f11-poly-reducible-p poly))
           (f11-poly-has-small-monic-factor-p poly))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          f11-poly-reducible-normalized-quartic-implies-small-monic-factor))
           :in-theory (theory 'minimal-theory))))

(defthm f11-quartic-irreducibility-criterion-minimal-client
  (implies (and (equal (f11-normalize poly) poly)
                (equal (f11-poly-degree poly) 4)
                (not (f11-poly-has-small-monic-factor-p poly)))
           (f11-poly-irreducible-p poly))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          f11-poly-degree-four-without-small-monic-factor-is-irreducible))
           :in-theory (theory 'minimal-theory))))

(defthm f11-linear-times-cubic-is-reducible
  (f11-poly-reducible-p '(1 1 0 1 1))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-reducible-p-suff
                                   (poly '(1 1 0 1 1))
                                   (left '(1 1)) (right '(1 0 0 1))))
           :in-theory (enable f11-poly-mul f11-poly-raw-mul
                              f11-poly-unit-p f11-poly-degree
                              f11-normalize f11-fix-coefficients
                              f11-trim-trailing-zeros gfield::f11-fix
                              gfield::f11-add gfield::f11-mul
                              pfield::fep pfield::fep-fix
                              f11-poly-raw-add f11-poly-raw-scale))))

(defthm f11-linear-times-cubic-has-linear-witness
  (f11-poly-has-small-monic-factor-p '(1 1 0 1 1))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-has-small-monic-factor-p-suff
                                   (poly '(1 1 0 1 1)) (factor '(1 1))))
           :in-theory (enable f11-poly-divides-p f11-poly-remainder
                              f11-poly-degree f11-poly-leading-coefficient
                              f11-canonical-polynomial-p f11-normalize
                              f11-fix-coefficients f11-trim-trailing-zeros
                              gfield::f11-one gfield::f11-fix))))

(defthm f11-two-quadratics-is-reducible
  (f11-poly-reducible-p '(1 0 2 0 1))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-reducible-p-suff
                                   (poly '(1 0 2 0 1))
                                   (left '(1 0 1)) (right '(1 0 1))))
           :in-theory (enable f11-poly-mul f11-poly-raw-mul
                              f11-poly-unit-p f11-poly-degree
                              f11-normalize f11-fix-coefficients
                              f11-trim-trailing-zeros gfield::f11-fix
                              gfield::f11-add gfield::f11-mul
                              pfield::fep pfield::fep-fix
                              f11-poly-raw-add f11-poly-raw-scale))))

(defthm f11-two-quadratics-has-quadratic-witness
  (f11-poly-has-small-monic-factor-p '(1 0 2 0 1))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-has-small-monic-factor-p-suff
                                   (poly '(1 0 2 0 1)) (factor '(1 0 1))))
           :in-theory (enable f11-poly-divides-p f11-poly-remainder
                              f11-poly-degree f11-poly-leading-coefficient
                              f11-canonical-polynomial-p f11-normalize
                              f11-fix-coefficients f11-trim-trailing-zeros
                              gfield::f11-one gfield::f11-fix))))

(defthm f11-monic-degree-preservation-concrete-regressions
  (and (equal (f11-poly-degree (f11-poly-monic-normalize '(2 4 3))) 2)
       (equal (f11-poly-degree (f11-poly-monic-normalize '(13 4 3))) 2)
       (equal (f11-poly-degree (f11-poly-monic-normalize '(2 4 3 0))) 2)
       (equal (f11-poly-degree (f11-poly-monic-normalize '(2 4 3 . tail))) 2))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-degree-of-poly-monic-normalize-when-nonzero
                                   (factor '(2 4 3)))
                         (:instance f11-poly-degree-of-poly-monic-normalize-when-nonzero
                                   (factor '(13 4 3)))
                         (:instance f11-poly-degree-of-poly-monic-normalize-when-nonzero
                                   (factor '(2 4 3 0)))
                         (:instance f11-poly-degree-of-poly-monic-normalize-when-nonzero
                                   (factor '(2 4 3 . tail))))
           :in-theory (enable f11-normalize f11-fix-coefficients
                              f11-trim-trailing-zeros f11-poly-degree
                              gfield::f11-fix))))

(defthm f11-logical-normalization-regressions
  (and (equal (f11-poly-reducible-p '(1 1 0 1 1 0))
              (f11-poly-reducible-p '(1 1 0 1 1)))
       (equal (f11-poly-irreducible-p '(12 1 0 1 1 . tail))
              (f11-poly-irreducible-p '(1 1 0 1 1))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-reducible-p-of-normalize
                                   (poly '(1 1 0 1 1 0)))
                         (:instance f11-poly-irreducible-p-of-normalize
                                   (poly '(12 1 0 1 1 . tail))))
           :in-theory (enable f11-normalize f11-fix-coefficients
                              f11-trim-trailing-zeros gfield::f11-fix))))

(defthm f11-small-factor-total-semantics-regressions
  (and (not (f11-poly-irreducible-p nil))
       (not (f11-poly-irreducible-p '(3)))
       (not (f11-poly-irreducible-p 'malformed))
       (equal (f11-normalize '(1 0 . tail)) '(1)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f11-poly-irreducible-p-definition (poly nil))
                         (:instance f11-poly-irreducible-p-definition (poly '(3)))
                         (:instance f11-poly-irreducible-p-definition (poly 'malformed)))
           :in-theory (enable f11-poly-degree f11-normalize
                              f11-fix-coefficients f11-trim-trailing-zeros
                              gfield::f11-fix))))
