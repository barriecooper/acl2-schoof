(in-package "GPOLY")
(include-book "finite-field-factor-degree-bound")

(defthm finite-field-factor-degree-bound-minimal-client
  (implies (and (equal (finite-field-poly-normalize poly) poly)
                (< 0 (finite-field-poly-degree poly))
                (finite-field-poly-reducible-p poly))
           (finite-field-poly-has-bounded-monic-factor-p
            poly (floor (finite-field-poly-degree poly) 2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-reducible-normalized-positive-degree-implies-bounded-monic-factor))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-no-bounded-factor-irreducibility-minimal-client
  (implies
   (and (equal (finite-field-poly-normalize poly) poly)
        (< 0 (finite-field-poly-degree poly))
        (not (finite-field-poly-has-bounded-monic-factor-p
              poly (floor (finite-field-poly-degree poly) 2))))
   (finite-field-poly-irreducible-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-normalized-positive-degree-without-bounded-monic-factor-is-irreducible))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-reducibility-normalization-minimal-client
  (equal (finite-field-poly-reducible-p
          (finite-field-poly-normalize poly))
         (finite-field-poly-reducible-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance finite-field-poly-reducible-p-of-normalize))
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-bounded-factor-normalization-minimal-client
  (equal (finite-field-poly-has-bounded-monic-factor-p
          (finite-field-poly-normalize poly) bound)
         (finite-field-poly-has-bounded-monic-factor-p poly bound))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  finite-field-poly-has-bounded-monic-factor-p-of-normalize))
           :in-theory (theory 'minimal-theory))))
