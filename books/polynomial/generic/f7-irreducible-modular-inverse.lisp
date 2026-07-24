(in-package "GPOLY")
(include-book "f7-quadratic-irreducibility")
(include-book "f7-reduced-arithmetic")
(include-book "irreducible-modular-inverse")

; These are focused concrete regressions for the generic interface.  They are
; not a quotient type or a finite-field table.  Each theorem records the
; certificate premise, canonical nonzero residue, GCD bridge result, existing
; XGCD-derived inverse, and both reduced unit laws.
(defthm f7-one-irreducible-modular-inverse-regression
  (let ((first '(1)) (modulus '(1 0 1)))
    (and (f7-poly-irreducible-p modulus)
         (equal (f7-poly-remainder first modulus) (f7-normalize first))
         (not (equal (f7-normalize first) nil))
         (equal (f7-poly-monic-euclidean-gcd first modulus) '(1))
         (equal (f7-poly-modular-inverse first modulus) '(1))
         (equal (f7-poly-reduced-mul
                 (f7-poly-modular-inverse first modulus) first modulus)
                (f7-poly-reduced-one modulus))
         (equal (f7-poly-reduced-mul
                 first (f7-poly-modular-inverse first modulus) modulus)
                (f7-poly-reduced-one modulus))))
  :rule-classes nil
  :hints (("Goal" :use f7-x-squared-plus-one-is-irreducible)))

(defthm f7-three-irreducible-modular-inverse-regression
  (let ((first '(3)) (modulus '(1 0 1)))
    (and (f7-poly-irreducible-p modulus)
         (equal (f7-poly-remainder first modulus) (f7-normalize first))
         (not (equal (f7-normalize first) nil))
         (equal (f7-poly-monic-euclidean-gcd first modulus) '(1))
         (equal (f7-poly-modular-inverse first modulus) '(5))
         (equal (f7-poly-reduced-mul
                 (f7-poly-modular-inverse first modulus) first modulus)
                (f7-poly-reduced-one modulus))
         (equal (f7-poly-reduced-mul
                 first (f7-poly-modular-inverse first modulus) modulus)
                (f7-poly-reduced-one modulus))))
  :rule-classes nil
  :hints (("Goal" :use f7-x-squared-plus-one-is-irreducible)))

(defthm f7-x-irreducible-modular-inverse-regression
  (let ((first '(0 1)) (modulus '(1 0 1)))
    (and (f7-poly-irreducible-p modulus)
         (equal (f7-poly-remainder first modulus) (f7-normalize first))
         (not (equal (f7-normalize first) nil))
         (equal (f7-poly-monic-euclidean-gcd first modulus) '(1))
         (equal (f7-poly-modular-inverse first modulus) '(0 6))
         (equal (f7-poly-reduced-mul
                 (f7-poly-modular-inverse first modulus) first modulus)
                (f7-poly-reduced-one modulus))
         (equal (f7-poly-reduced-mul
                 first (f7-poly-modular-inverse first modulus) modulus)
                (f7-poly-reduced-one modulus))))
  :rule-classes nil
  :hints (("Goal" :use f7-x-squared-plus-one-is-irreducible)))

(defthm f7-one-plus-x-irreducible-modular-inverse-regression
  (let ((first '(1 1)) (modulus '(1 0 1)))
    (and (f7-poly-irreducible-p modulus)
         (equal (f7-poly-remainder first modulus) (f7-normalize first))
         (not (equal (f7-normalize first) nil))
         (equal (f7-poly-monic-euclidean-gcd first modulus) '(1))
         (equal (f7-poly-modular-inverse first modulus) '(4 3))
         (equal (f7-poly-reduced-mul
                 (f7-poly-modular-inverse first modulus) first modulus)
                (f7-poly-reduced-one modulus))
         (equal (f7-poly-reduced-mul
                 first (f7-poly-modular-inverse first modulus) modulus)
                (f7-poly-reduced-one modulus))))
  :rule-classes nil
  :hints (("Goal" :use f7-x-squared-plus-one-is-irreducible)))

(defthm f7-irreducible-modular-inverse-boundary-regressions
  (and
   ; Zero and the modulus normalize/reduce to zero and hence do not satisfy
   ; the explicit nonzero canonical-representative boundary.
   (equal (f7-normalize nil) nil)
   (equal (f7-poly-remainder '(1 0 1) '(1 0 1)) nil)
   ; Existing total normalization gives alternate representations the same
   ; semantics without requiring syntactic canonicality.
   (equal (f7-poly-remainder '(1 1 0) '(1 0 1)) '(1 1))
   (equal (f7-poly-modular-inverse '(1 1 0) '(1 0 1)) '(4 3))
   (equal (f7-poly-remainder '(8 1) '(1 0 1)) '(1 1))
   (equal (f7-poly-modular-inverse '(8 1) '(1 0 1)) '(4 3))
   (equal (f7-poly-remainder '(1 1 . malformed-tail) '(1 0 1)) '(1 1))
   (equal (f7-poly-modular-inverse
           '(1 1 . malformed-tail) '(1 0 1)) '(4 3)))
  :rule-classes nil)
