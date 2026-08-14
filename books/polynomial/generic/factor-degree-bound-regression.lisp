(in-package "GPOLY")
(include-book "factor-degree-bound")

(defthm generic-factor-degree-bound-minimal-client
  (implies (and (equal (normalize poly) poly)
                (< 0 (poly-degree poly))
                (poly-reducible-p poly))
           (poly-has-bounded-monic-factor-p
            poly (floor (poly-degree poly) 2)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  poly-reducible-normalized-positive-degree-implies-bounded-monic-factor))
           :in-theory (theory 'minimal-theory))))

(defthm generic-no-bounded-factor-irreducibility-minimal-client
  (implies (and (equal (normalize poly) poly)
                (< 0 (poly-degree poly))
                (not (poly-has-bounded-monic-factor-p
                      poly (floor (poly-degree poly) 2))))
           (poly-irreducible-p poly))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  poly-normalized-positive-degree-without-bounded-monic-factor-is-irreducible))
           :in-theory (theory 'minimal-theory))))

(defthm generic-half-degree-bound-arithmetic-regression
  (and (equal (floor 2 2) 1)
       (equal (floor 3 2) 1)
       (equal (floor 4 2) 2)
       (equal (floor 5 2) 2)
       (equal (floor 7 2) 3))
  :rule-classes nil)

(defthm generic-bounded-factor-normalization-minimal-client
  (equal (poly-has-bounded-monic-factor-p (normalize poly) bound)
         (poly-has-bounded-monic-factor-p poly bound))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-has-bounded-monic-factor-p-of-normalize))
           :in-theory (theory 'minimal-theory))))
