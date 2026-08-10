(in-package "GFIELD")

(include-book "pfield-finite-field-context")
(include-book "examples/f11")

; Complete substitution:
; PFIELD-MODULUS -> 11; PFIELD-ELEMENT-P -> F11-ELEMENT-P;
; PFIELD-FIX -> F11-FIX; zero/one/add/mul/neg/inv -> their F11 names.
; Consequently both rank and unrank are F11-FIX and the bound is 11.
(defthm f11-finite-field-context-constraint-seam
  (and
   (booleanp (f11-element-p x))
   (f11-element-p (f11-fix x))
   (implies (f11-element-p x) (equal (f11-fix x) x))
   (equal (f11-fix (f11-fix x)) (f11-fix x))
   (f11-element-p (f11-zero)) (f11-element-p (f11-one))
   (not (equal (f11-zero) (f11-one)))
   (equal (f11-fix (f11-zero)) (f11-zero))
   (equal (f11-fix (f11-one)) (f11-one))
   (f11-element-p (f11-add x y)) (f11-element-p (f11-mul x y))
   (f11-element-p (f11-neg x)) (f11-element-p (f11-inv x))
   (equal (f11-fix (f11-add x y)) (f11-add x y))
   (equal (f11-fix (f11-mul x y)) (f11-mul x y))
   (equal (f11-fix (f11-neg x)) (f11-neg x))
   (equal (f11-fix (f11-inv x)) (f11-inv x))
   (equal (f11-add (f11-fix x) (f11-fix y)) (f11-add x y))
   (equal (f11-add (f11-fix x) y) (f11-add x y))
   (equal (f11-add x (f11-fix y)) (f11-add x y))
   (equal (f11-mul (f11-fix x) y) (f11-mul x y))
   (equal (f11-mul x (f11-fix y)) (f11-mul x y))
   (equal (f11-mul (f11-fix x) (f11-fix y)) (f11-mul x y))
   (equal (f11-neg (f11-fix x)) (f11-neg x))
   (equal (f11-inv (f11-fix x)) (f11-inv x))
   (equal (f11-add (f11-add x y) z) (f11-add x (f11-add y z)))
   (equal (f11-add x y) (f11-add y x))
   (equal (f11-add (f11-zero) x) (f11-fix x))
   (equal (f11-add (f11-neg x) x) (f11-zero))
   (implies (and (equal (f11-fix x1) (f11-fix x2))
                 (equal (f11-fix y1) (f11-fix y2)))
            (equal (f11-add x1 y1) (f11-add x2 y2)))
   (implies (and (equal (f11-fix x1) (f11-fix x2))
                 (equal (f11-fix y1) (f11-fix y2)))
            (equal (f11-mul x1 y1) (f11-mul x2 y2)))
   (equal (f11-mul (f11-mul x y) z) (f11-mul x (f11-mul y z)))
   (equal (f11-mul x y) (f11-mul y x))
   (equal (f11-mul (f11-one) x) (f11-fix x))
   (equal (f11-mul x (f11-add y z))
          (f11-add (f11-mul x y) (f11-mul x z)))
   (equal (f11-inv (f11-zero)) (f11-zero))
   (implies (not (equal (f11-fix x) (f11-zero)))
            (equal (f11-mul (f11-inv x) x) (f11-one)))
   (posp 11) (natp (f11-fix x)) (< (f11-fix x) 11)
   (equal (f11-fix (f11-fix k)) (f11-fix k))
   (equal (f11-fix (f11-fix x)) (f11-fix x))
   (implies (and (natp k) (< k 11))
            (equal (f11-fix (f11-fix k)) k)))
  :rule-classes nil
  :hints (("Goal"
           :by (:functional-instance
                pfield-finite-field-context-constraint-seam
                (pfield-modulus (lambda () 11))
                (pfield-element-p f11-element-p) (pfield-fix f11-fix)
                (pfield-zero f11-zero) (pfield-one f11-one)
                (pfield-add f11-add) (pfield-mul f11-mul)
                (pfield-neg f11-neg) (pfield-inv f11-inv))
           :in-theory (enable dm::primep))))

; Functional instantiation consumes individual constraint rules, not a disabled
; conjunction.  These projections deliberately mirror the FINITE-FIELD-*
; constraint schemas and are kept together in the focused theory below.
(defmacro def-f11-context-projection (name term)
  `(defthm ,name ,term
     :hints (("Goal"
              :use f11-finite-field-context-constraint-seam
              :in-theory (theory 'minimal-theory)))))

(def-f11-context-projection booleanp-of-f11-element-p-for-context
  (booleanp (f11-element-p x)))
(def-f11-context-projection f11-element-p-of-f11-fix-for-context
  (f11-element-p (f11-fix x)))
(def-f11-context-projection f11-fix-when-f11-element-p-for-context
  (implies (f11-element-p x) (equal (f11-fix x) x)))
(def-f11-context-projection f11-fix-idempotent-for-context
  (equal (f11-fix (f11-fix x)) (f11-fix x)))
(def-f11-context-projection f11-element-p-of-zero-for-context
  (f11-element-p (f11-zero)))
(def-f11-context-projection f11-element-p-of-one-for-context
  (f11-element-p (f11-one)))
(def-f11-context-projection f11-zero-not-equal-one-for-context
  (not (equal (f11-zero) (f11-one))))
(def-f11-context-projection f11-fix-of-zero-for-context
  (equal (f11-fix (f11-zero)) (f11-zero)))
(def-f11-context-projection f11-fix-of-one-for-context
  (equal (f11-fix (f11-one)) (f11-one)))
(def-f11-context-projection f11-element-p-of-add-for-context
  (f11-element-p (f11-add x y)))
(def-f11-context-projection f11-element-p-of-mul-for-context
  (f11-element-p (f11-mul x y)))
(def-f11-context-projection f11-element-p-of-neg-for-context
  (f11-element-p (f11-neg x)))
(def-f11-context-projection f11-element-p-of-inv-for-context
  (f11-element-p (f11-inv x)))
(def-f11-context-projection f11-fix-of-add-for-context
  (equal (f11-fix (f11-add x y)) (f11-add x y)))
(def-f11-context-projection f11-fix-of-mul-for-context
  (equal (f11-fix (f11-mul x y)) (f11-mul x y)))
(def-f11-context-projection f11-fix-of-neg-for-context
  (equal (f11-fix (f11-neg x)) (f11-neg x)))
(def-f11-context-projection f11-fix-of-inv-for-context
  (equal (f11-fix (f11-inv x)) (f11-inv x)))
(def-f11-context-projection f11-add-of-fixes-for-context
  (equal (f11-add (f11-fix x) (f11-fix y)) (f11-add x y)))
(def-f11-context-projection f11-add-fix-left-for-context
  (equal (f11-add (f11-fix x) y) (f11-add x y)))
(def-f11-context-projection f11-add-fix-right-for-context
  (equal (f11-add x (f11-fix y)) (f11-add x y)))
(def-f11-context-projection f11-mul-fix-left-for-context
  (equal (f11-mul (f11-fix x) y) (f11-mul x y)))
(def-f11-context-projection f11-mul-fix-right-for-context
  (equal (f11-mul x (f11-fix y)) (f11-mul x y)))
(def-f11-context-projection f11-mul-of-fixes-for-context
  (equal (f11-mul (f11-fix x) (f11-fix y)) (f11-mul x y)))
(def-f11-context-projection f11-neg-of-fix-for-context
  (equal (f11-neg (f11-fix x)) (f11-neg x)))
(def-f11-context-projection f11-inv-of-fix-for-context
  (equal (f11-inv (f11-fix x)) (f11-inv x)))
(def-f11-context-projection f11-add-associative-for-context
  (equal (f11-add (f11-add x y) z) (f11-add x (f11-add y z))))
(def-f11-context-projection f11-add-commutative-for-context
  (equal (f11-add x y) (f11-add y x)))
(def-f11-context-projection f11-add-zero-left-for-context
  (equal (f11-add (f11-zero) x) (f11-fix x)))
(def-f11-context-projection f11-add-inverse-left-for-context
  (equal (f11-add (f11-neg x) x) (f11-zero)))
(def-f11-context-projection f11-add-fixed-congruence-for-context
  (implies (and (equal (f11-fix x1) (f11-fix x2))
                (equal (f11-fix y1) (f11-fix y2)))
           (equal (f11-add x1 y1) (f11-add x2 y2))))
(def-f11-context-projection f11-mul-fixed-congruence-for-context
  (implies (and (equal (f11-fix x1) (f11-fix x2))
                (equal (f11-fix y1) (f11-fix y2)))
           (equal (f11-mul x1 y1) (f11-mul x2 y2))))
(def-f11-context-projection f11-mul-associative-for-context
  (equal (f11-mul (f11-mul x y) z) (f11-mul x (f11-mul y z))))
(def-f11-context-projection f11-mul-commutative-for-context
  (equal (f11-mul x y) (f11-mul y x)))
(def-f11-context-projection f11-mul-one-left-for-context
  (equal (f11-mul (f11-one) x) (f11-fix x)))
(def-f11-context-projection f11-mul-left-distributive-for-context
  (equal (f11-mul x (f11-add y z))
         (f11-add (f11-mul x y) (f11-mul x z))))
(def-f11-context-projection f11-inv-of-zero-for-context
  (equal (f11-inv (f11-zero)) (f11-zero)))
(def-f11-context-projection f11-mul-inverse-left-for-context
  (implies (not (equal (f11-fix x) (f11-zero)))
           (equal (f11-mul (f11-inv x) x) (f11-one))))
(def-f11-context-projection posp-of-11-for-finite-field-context
  (posp 11))
(def-f11-context-projection natp-of-f11-rank-for-context
  (natp (f11-fix x)))
(def-f11-context-projection f11-rank-upper-bound-for-context
  (< (f11-fix x) 11))
(def-f11-context-projection f11-fix-of-unrank-for-context
  (equal (f11-fix (f11-fix k)) (f11-fix k)))
(def-f11-context-projection f11-unrank-of-rank-for-context
  (equal (f11-fix (f11-fix x)) (f11-fix x)))
(def-f11-context-projection f11-rank-of-unrank-when-bounded-for-context
  (implies (and (natp k) (< k 11))
           (equal (f11-fix (f11-fix k)) k)))

(deftheory f11-finite-field-context-instance-theory
  '(booleanp-of-f11-element-p-for-context
    f11-element-p-of-f11-fix-for-context
    f11-fix-when-f11-element-p-for-context f11-fix-idempotent-for-context
    f11-element-p-of-zero-for-context f11-element-p-of-one-for-context
    f11-zero-not-equal-one-for-context f11-fix-of-zero-for-context
    f11-fix-of-one-for-context f11-element-p-of-add-for-context
    f11-element-p-of-mul-for-context f11-element-p-of-neg-for-context
    f11-element-p-of-inv-for-context f11-fix-of-add-for-context
    f11-fix-of-mul-for-context f11-fix-of-neg-for-context
    f11-fix-of-inv-for-context f11-add-of-fixes-for-context
    f11-add-fix-left-for-context f11-add-fix-right-for-context
    f11-mul-fix-left-for-context f11-mul-fix-right-for-context
    f11-mul-of-fixes-for-context f11-neg-of-fix-for-context
    f11-inv-of-fix-for-context f11-add-associative-for-context
    f11-add-commutative-for-context f11-add-zero-left-for-context
    f11-add-inverse-left-for-context f11-add-fixed-congruence-for-context
    f11-mul-fixed-congruence-for-context f11-mul-associative-for-context
    f11-mul-commutative-for-context f11-mul-one-left-for-context
    f11-mul-left-distributive-for-context f11-inv-of-zero-for-context
    f11-mul-inverse-left-for-context posp-of-11-for-finite-field-context
    natp-of-f11-rank-for-context f11-rank-upper-bound-for-context
    f11-fix-of-unrank-for-context f11-unrank-of-rank-for-context
    f11-rank-of-unrank-when-bounded-for-context))
