(in-package "GFIELD")

(include-book "pfield-finite-field-context")

(defthm pfield-neg-of-neg-from-finite-field-context
  (equal (pfield-neg (pfield-neg x)) (pfield-fix x))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance finite-field-neg-of-neg
             (finite-field-element-p pfield-element-p)
       (finite-field-fix pfield-fix)
       (finite-field-zero pfield-zero) (finite-field-one pfield-one)
       (finite-field-add pfield-add) (finite-field-mul pfield-mul)
       (finite-field-neg pfield-neg) (finite-field-inv pfield-inv)
       (finite-field-rank pfield-fix) (finite-field-unrank pfield-fix)
       (finite-field-bound pfield-modulus))
           :in-theory (theory 'minimal-theory))
          (and stable-under-simplificationp
               '(:use (booleanp-of-pfield-element-p pfield-element-p-of-pfield-fix
 pfield-fix-when-pfield-element-p pfield-fix-idempotent
 pfield-element-p-of-pfield-zero pfield-element-p-of-pfield-one
 pfield-zero-not-equal-pfield-one pfield-fix-of-zero pfield-fix-of-one
 pfield-element-p-of-pfield-add pfield-element-p-of-pfield-mul
 pfield-element-p-of-pfield-neg pfield-element-p-of-pfield-inv
 pfield-fix-of-pfield-add pfield-fix-of-pfield-mul pfield-fix-of-pfield-neg
 pfield-fix-of-pfield-inv pfield-add-of-fixes pfield-add-fix-left
 pfield-add-fix-right pfield-mul-of-fixes pfield-mul-fix-left pfield-mul-fix-right
 pfield-neg-of-fix pfield-inv-of-fix pfield-add-associative pfield-add-commutative
 pfield-add-zero-left pfield-add-inverse-left pfield-add-fixed-congruence
 pfield-mul-fixed-congruence pfield-mul-associative pfield-mul-commutative
 pfield-mul-one-left pfield-mul-left-distributive pfield-inv-of-zero
 pfield-mul-inverse-left posp-of-pfield-modulus-for-finite-bijection
 natp-of-pfield-fix-for-finite-bijection pfield-fix-upper-bound-for-finite-bijection
 pfield-fix-of-unrank-for-finite-bijection pfield-fix-inverse-when-bounded)
                 :in-theory (theory 'minimal-theory)))))

(defthm pfield-rank-of-fix-from-finite-field-context
  (equal (pfield-fix (pfield-fix x)) (pfield-fix x))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance finite-field-rank-of-finite-field-fix
             (finite-field-element-p pfield-element-p)
       (finite-field-fix pfield-fix)
       (finite-field-zero pfield-zero) (finite-field-one pfield-one)
       (finite-field-add pfield-add) (finite-field-mul pfield-mul)
       (finite-field-neg pfield-neg) (finite-field-inv pfield-inv)
       (finite-field-rank pfield-fix) (finite-field-unrank pfield-fix)
       (finite-field-bound pfield-modulus))
           :in-theory (theory 'minimal-theory))
          (and stable-under-simplificationp
               '(:use (booleanp-of-pfield-element-p pfield-element-p-of-pfield-fix
 pfield-fix-when-pfield-element-p pfield-fix-idempotent
 pfield-element-p-of-pfield-zero pfield-element-p-of-pfield-one
 pfield-zero-not-equal-pfield-one pfield-fix-of-zero pfield-fix-of-one
 pfield-element-p-of-pfield-add pfield-element-p-of-pfield-mul
 pfield-element-p-of-pfield-neg pfield-element-p-of-pfield-inv
 pfield-fix-of-pfield-add pfield-fix-of-pfield-mul pfield-fix-of-pfield-neg
 pfield-fix-of-pfield-inv pfield-add-of-fixes pfield-add-fix-left
 pfield-add-fix-right pfield-mul-of-fixes pfield-mul-fix-left pfield-mul-fix-right
 pfield-neg-of-fix pfield-inv-of-fix pfield-add-associative pfield-add-commutative
 pfield-add-zero-left pfield-add-inverse-left pfield-add-fixed-congruence
 pfield-mul-fixed-congruence pfield-mul-associative pfield-mul-commutative
 pfield-mul-one-left pfield-mul-left-distributive pfield-inv-of-zero
 pfield-mul-inverse-left posp-of-pfield-modulus-for-finite-bijection
 natp-of-pfield-fix-for-finite-bijection pfield-fix-upper-bound-for-finite-bijection
 pfield-fix-of-unrank-for-finite-bijection pfield-fix-inverse-when-bounded)
                 :in-theory (theory 'minimal-theory)))))

(defthm pfield-unrank-of-rank-from-finite-field-context
  (equal (pfield-fix (pfield-fix x)) (pfield-fix x))
  :rule-classes nil
  :hints (("Goal" :use pfield-rank-of-fix-from-finite-field-context
           :in-theory (theory 'minimal-theory))))

(defthm pfield-rank-of-unrank-when-bounded-from-finite-field-context
  (implies (and (natp k) (< k (pfield-modulus)))
           (equal (pfield-fix (pfield-fix k)) k))
  :rule-classes nil
  :hints (("Goal" :use pfield-fix-inverse-when-bounded
           :in-theory (theory 'minimal-theory))))

; The complete field-operation substitution is inherited through the PFIELD
; finite-field proving theorem.
(defthm f7-neg-of-neg-from-finite-field-context
  (equal (f7-neg (f7-neg x)) (f7-fix x))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                       pfield-neg-of-neg-from-finite-field-context
                       (pfield-modulus (lambda () 7))
                       (pfield-element-p f7-element-p)
                       (pfield-fix f7-fix)
                       (pfield-zero f7-zero) (pfield-one f7-one)
                       (pfield-add f7-add) (pfield-mul f7-mul)
                       (pfield-neg f7-neg) (pfield-inv f7-inv))
           :in-theory (enable dm::primep))))

; F7 inherits the PFIELD proving instance without new rank/unrank wrappers.
(defthm f7-unrank-of-rank-for-finite-field-context
  (equal (f7-fix (f7-fix x)) (f7-fix x))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                       pfield-rank-of-fix-from-finite-field-context
                       (pfield-modulus (lambda () 7))
                       (pfield-fix f7-fix))
            :in-theory (enable dm::primep))))

(defthm f7-bound-for-finite-field-context
  (< (f7-fix x) 7)
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                       pfield-fix-upper-bound-for-finite-bijection
                       (pfield-modulus (lambda () 7))
                       (pfield-fix f7-fix))
           :in-theory (enable dm::primep))))

(defthm f7-finite-field-context-execution-regressions
  (and (equal (f7-fix 0) 0)
       (equal (f7-fix 1) 1)
       (equal (f7-fix 6) 6)
       (equal (f7-fix 7) 0)
       (equal (f7-fix -1) 6)
       (equal (f7-fix 'malformed) 0))
  :rule-classes nil)
