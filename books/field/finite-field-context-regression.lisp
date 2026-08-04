(in-package "GFIELD")

(include-book "finite-field-context")

(defthm finite-field-neg-of-neg-minimal-theory-client
  (equal (finite-field-neg (finite-field-neg x)) (finite-field-fix x))
  :rule-classes nil
  :hints (("Goal" :use finite-field-neg-of-neg
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-rank-of-fix-minimal-theory-client
  (equal (finite-field-rank (finite-field-fix x)) (finite-field-rank x))
  :rule-classes nil
  :hints (("Goal" :use finite-field-rank-of-finite-field-fix
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-unrank-injective-minimal-theory-client
  (implies (and (natp i) (< i (finite-field-bound))
                (natp j) (< j (finite-field-bound)))
           (equal (equal (finite-field-unrank i) (finite-field-unrank j))
                  (equal i j)))
  :rule-classes nil
  :hints (("Goal" :use equal-of-finite-field-unrank-when-bounded
           :in-theory (theory 'minimal-theory))))

(defthm finite-field-bound-lower-bound-minimal-theory-client
  (< 1 (finite-field-bound))
  :rule-classes nil
  :hints (("Goal" :use finite-field-bound-greater-than-one
           :in-theory (theory 'minimal-theory))))
