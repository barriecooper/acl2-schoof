(in-package "GPOLY")

(include-book "finite-field-fixed-modulus-carrier")
(include-book "f7-division")

(defthm finite-field-fixed-modulus-carrier-coverage-minimal-theory-client
  (member-equal (finite-field-fixed-modulus-reconstruct
                 (finite-field-fixed-modulus-coefficient-vector x modulus))
                (finite-field-fixed-modulus-elements modulus))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use member-equal-of-finite-field-fixed-modulus-fix-and-elements)))

(defthm finite-field-fixed-modulus-cardinality-minimal-theory-client
  (equal (finite-field-fixed-modulus-cardinality modulus)
         (finite-field-fixed-modulus-coefficient-vector-coding-bound modulus))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-fixed-modulus-cardinality-equals-bound)))

(defthm finite-field-fixed-modulus-no-duplicates-minimal-theory-client
  (no-duplicatesp-equal (finite-field-fixed-modulus-elements modulus))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use no-duplicatesp-equal-of-finite-field-fixed-modulus-elements)))

