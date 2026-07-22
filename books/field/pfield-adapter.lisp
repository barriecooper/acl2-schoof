(in-package "GFIELD")

(include-book "kernel")
(include-book "kestrel/prime-fields/prime-fields-rules" :dir :system)

; A fixed, but otherwise arbitrary, prime.  The local definition is only a
; consistency witness.  Concrete books replace this nullary function and the
; wrappers below by functional instantiation.
(encapsulate
 (((pfield-modulus) => *))
 (local (defun pfield-modulus () 3))
 (defthm primep-of-pfield-modulus
   (dm::primep (pfield-modulus))
   :hints (("Goal" :in-theory (enable dm::primep)))))

(defthm integerp-of-pfield-modulus
  (integerp (pfield-modulus))
  :rule-classes :type-prescription
  :hints (("Goal" :use primep-of-pfield-modulus
           :in-theory (enable dm::primep))))

(defthm pfield-modulus-lower-bound
  (<= 2 (pfield-modulus))
  :rule-classes :linear
  :hints (("Goal" :use primep-of-pfield-modulus
           :in-theory (enable dm::primep))))

; Exact-arity, total wrappers.  Fixing the arguments makes their equations
; hold for every ACL2 object, as required by the GFIELD kernel.
(defun pfield-element-p (x)
  (pfield::fep x (pfield-modulus)))

(defun pfield-fix (x)
  (pfield::fep-fix x (pfield-modulus)))

(defun pfield-zero () 0)
(defun pfield-one () 1)

(defun pfield-add (x y)
  (pfield::add (pfield-fix x) (pfield-fix y) (pfield-modulus)))

(defun pfield-mul (x y)
  (pfield::mul (pfield-fix x) (pfield-fix y) (pfield-modulus)))

(defun pfield-neg (x)
  (pfield::neg (pfield-fix x) (pfield-modulus)))

(defun pfield-inv (x)
  (pfield::inv (pfield-fix x) (pfield-modulus)))

(defun pfield-sub (x y) (pfield-add x (pfield-neg y)))
(defun pfield-div (x y) (pfield-mul x (pfield-inv y)))
(def-pow-instance pfield-pow-spec pfield-pow-fast pfield-pow
  pfield-one pfield-mul pfield-fix)

; Canonical representatives and closure.
(defthm booleanp-of-pfield-element-p
  (booleanp (pfield-element-p x)) :rule-classes :type-prescription)

(defthm pfield-element-p-of-pfield-fix
  (pfield-element-p (pfield-fix x)))

(defthm pfield-fep-of-pfield-fix
  (pfield::fep (pfield-fix x) (pfield-modulus))
  :hints (("Goal" :in-theory (enable pfield-element-p))))

(defthm integerp-of-pfield-fix
  (integerp (pfield-fix x))
  :rule-classes :type-prescription
  :hints (("Goal" :use (pfield-fep-of-pfield-fix
                         (:instance pfield::integerp-when-fep
                          (x (pfield-fix x))
                          (p (pfield-modulus)))))))

(defthm pfield-fix-when-pfield-element-p
  (implies (pfield-element-p x) (equal (pfield-fix x) x)))

(defthm pfield-fix-idempotent
  (equal (pfield-fix (pfield-fix x)) (pfield-fix x))
  :hints (("Goal" :use ((:instance pfield-fix-when-pfield-element-p
                          (x (pfield-fix x))))
           :in-theory (disable pfield-fix-when-pfield-element-p))))

(defthm mod-of-pfield-fix
  (equal (mod (pfield-fix x) (pfield-modulus)) (pfield-fix x))
  :hints (("Goal" :use pfield-fep-of-pfield-fix
           :in-theory (disable pfield-fix))))

(defthm pfield-element-p-of-pfield-zero
  (pfield-element-p (pfield-zero)))

(defthm pfield-element-p-of-pfield-one
  (pfield-element-p (pfield-one)))

(defthm pfield-zero-not-equal-pfield-one
  (not (equal (pfield-zero) (pfield-one))))

(defthm pfield-fix-of-zero
  (equal (pfield-fix (pfield-zero)) (pfield-zero)))
(defthm pfield-fix-of-one
  (equal (pfield-fix (pfield-one)) (pfield-one)))

(defthm pfield-element-p-of-pfield-add
  (pfield-element-p (pfield-add x y)))

(defthm pfield-element-p-of-pfield-mul
  (pfield-element-p (pfield-mul x y)))

(defthm pfield-element-p-of-pfield-neg
  (pfield-element-p (pfield-neg x)))

(defthm pfield-element-p-of-pfield-inv
  (pfield-element-p (pfield-inv x)))

(defthm pfield-fix-of-pfield-add
  (equal (pfield-fix (pfield-add x y)) (pfield-add x y)))
(defthm pfield-fix-of-pfield-mul
  (equal (pfield-fix (pfield-mul x y)) (pfield-mul x y)))
(defthm pfield-fix-of-pfield-neg
  (equal (pfield-fix (pfield-neg x)) (pfield-neg x)))
(defthm pfield-fix-of-pfield-inv
  (equal (pfield-fix (pfield-inv x)) (pfield-inv x)))

; Fixing compatibility and field laws.
(defthm pfield-add-of-fixes
  (equal (pfield-add (pfield-fix x) (pfield-fix y))
         (pfield-add x y)))
(defthm pfield-add-fix-left
  (equal (pfield-add (pfield-fix x) y) (pfield-add x y)))
(defthm pfield-add-fix-right
  (equal (pfield-add x (pfield-fix y)) (pfield-add x y)))
(defthm pfield-mul-of-fixes
  (equal (pfield-mul (pfield-fix x) (pfield-fix y))
         (pfield-mul x y)))
(defthm pfield-mul-fix-left
  (equal (pfield-mul (pfield-fix x) y) (pfield-mul x y)))
(defthm pfield-mul-fix-right
  (equal (pfield-mul x (pfield-fix y)) (pfield-mul x y)))
(defthm pfield-neg-of-fix
  (equal (pfield-neg (pfield-fix x)) (pfield-neg x))
  :hints (("Goal" :in-theory (e/d (pfield-neg) (pfield-fix)))))
(defthm pfield-inv-of-fix
  (equal (pfield-inv (pfield-fix x)) (pfield-inv x))
  :hints (("Goal" :in-theory (e/d (pfield-inv) (pfield-fix)))))

(defthm pfield-add-associative
  (equal (pfield-add (pfield-add x y) z)
         (pfield-add x (pfield-add y z))))

(defthm pfield-add-commutative
  (equal (pfield-add x y) (pfield-add y x))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable pfield-add pfield::add))))
(in-theory (disable pfield-add-commutative))

(defthm pfield-add-zero-left
  (equal (pfield-add (pfield-zero) x) (pfield-fix x)))

(defthm pfield-add-inverse-left
  (equal (pfield-add (pfield-neg x) x) (pfield-zero)))

(defthm pfield-add-fixed-congruence
  (implies (and (equal (pfield-fix x1) (pfield-fix x2))
                (equal (pfield-fix y1) (pfield-fix y2)))
           (equal (pfield-add x1 y1) (pfield-add x2 y2)))
  :hints (("Goal" :in-theory (e/d (pfield-add)
                                    (pfield-fix pfield::add)))))

(defthm pfield-mul-fixed-congruence
  (implies (and (equal (pfield-fix x1) (pfield-fix x2))
                (equal (pfield-fix y1) (pfield-fix y2)))
           (equal (pfield-mul x1 y1) (pfield-mul x2 y2)))
  :hints (("Goal" :in-theory (e/d (pfield-mul)
                                    (pfield-fix pfield::mul)))))

(defthm pfield-mul-associative
  (equal (pfield-mul (pfield-mul x y) z)
         (pfield-mul x (pfield-mul y z))))

(defthm pfield-mul-commutative
  (equal (pfield-mul x y) (pfield-mul y x))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable pfield-mul pfield::mul))))
(in-theory (disable pfield-mul-commutative))

(defthm pfield-mul-one-left
  (equal (pfield-mul (pfield-one) x) (pfield-fix x)))

(defthm pfield-mul-left-distributive
  (equal (pfield-mul x (pfield-add y z))
         (pfield-add (pfield-mul x y) (pfield-mul x z))))

(defthm pfield-inv-of-zero
  (equal (pfield-inv (pfield-zero)) (pfield-zero)))

(defthm pfield-mul-inverse-left
  (implies (not (equal (pfield-fix x) (pfield-zero)))
           (equal (pfield-mul (pfield-inv x) x) (pfield-one)))
  :hints (("Goal" :use ((:instance pfield::mul-of-inv-arg1
                          (x (pfield-fix x))
                          (p (pfield-modulus)))
                         (:instance pfield-element-p-of-pfield-fix))
           :in-theory (e/d (pfield-mul pfield-inv pfield-zero pfield-one
                                      pfield-element-p
                                      pfield::mod-of-ifix-when-fep)
                           (pfield::mul-of-inv-arg1 pfield-fix)))))

; Ordinary EQUAL of fixed values is the entire adapter equality boundary.
(defthm equal-of-pfield-fixed-values
  (equal (equal (pfield-fix x) (pfield-fix y))
         (and (pfield-element-p (pfield-fix x))
              (pfield-element-p (pfield-fix y))
              (equal (pfield-fix x) (pfield-fix y)))))

; A nontrivial theorem transported from the generic kernel through the
; fixed-arity wrappers.
(defthm pfield-double-negation-from-generic-kernel
  (equal (pfield-neg (pfield-neg x)) (pfield-fix x))
  :hints (("Goal" :by (:functional-instance field-neg-of-neg
                       (field-element-p pfield-element-p)
                       (field-fix pfield-fix)
                       (field-zero pfield-zero)
                       (field-one pfield-one)
                       (field-add pfield-add)
                       (field-mul pfield-mul)
                       (field-neg pfield-neg)
                       (field-inv pfield-inv))
            :do-not '(preprocess)
            :in-theory '(pfield-element-p-of-pfield-fix
                         pfield-fix-idempotent
                         pfield-element-p-of-pfield-zero
                         pfield-element-p-of-pfield-one
                         pfield-zero-not-equal-pfield-one
                         pfield-fix-of-zero pfield-fix-of-one
                         pfield-element-p-of-pfield-add
                         pfield-element-p-of-pfield-mul
                         pfield-element-p-of-pfield-neg
                         pfield-element-p-of-pfield-inv
                         pfield-fix-of-pfield-add pfield-fix-of-pfield-mul
                         pfield-fix-of-pfield-neg pfield-fix-of-pfield-inv
                         pfield-add-of-fixes pfield-mul-of-fixes
                         pfield-neg-of-fix pfield-inv-of-fix
                         pfield-add-zero-left pfield-add-inverse-left
                         pfield-mul-one-left
                         pfield-inv-of-zero))
          ("Subgoal 14" :by pfield-mul-fix-right)
          ("Subgoal 13" :by pfield-mul-commutative)
          ("Subgoal 12" :by pfield-add-fix-right)
          ("Subgoal 11" :by pfield-add-commutative)
          ("Subgoal 10" :by pfield-mul-left-distributive)
          ("Subgoal 9" :by pfield-mul-fix-left)
          ("Subgoal 8" :by booleanp-of-pfield-element-p)
          ("Subgoal 7" :by pfield-mul-associative)
          ("Subgoal 6" :by pfield-add-fix-left)
          ("Subgoal 5" :by pfield-add-associative)
          ("Subgoal 4" :by pfield-mul-inverse-left)
          ("Subgoal 3" :by pfield-fix-when-pfield-element-p)
          ("Subgoal 2" :by pfield-mul-fixed-congruence)
          ("Subgoal 1" :by pfield-add-fixed-congruence)))

; PFIELD power assurance.  A direct specialization is intentionally used here:
; functional replacement of the two recursive DEFUNs generates separate
; definitional-equation constraints, and unconstrained rewriting of those
; constraints unfolds only one recursive side.  The resulting obligations are
; recursive equivalence proofs rather than transport of the algebraic result.
(defthm pfield-mul-one-right-for-power
  (equal (pfield-mul x (pfield-one)) (pfield-fix x))
  :hints (("Goal" :in-theory (enable pfield-mul pfield-one))))

(defthm pfield-pow-spec-successor
  (equal (pfield-pow-spec base (+ 1 (nfix n)))
         (pfield-mul (pfield-fix base) (pfield-pow-spec base n)))
  :hints (("Goal" :in-theory (enable pfield-pow-spec))))

(defthm pfield-pow-spec-plus-two
  (implies (and (pfield-element-p base)
                (natp n))
           (equal (pfield-pow-spec base (+ 2 n))
                  (pfield-mul
                   base (pfield-mul base (pfield-pow-spec base n)))))
  :hints (("Goal" :use
           ((:instance pfield-pow-spec-successor (n (+ 1 n)))
            (:instance pfield-pow-spec-successor (n n)))
           :in-theory (disable pfield-mul-commutative))))

(defthm pfield-pow-spec-of-square
  (implies (and (pfield-element-p base)
                (natp n))
           (equal (pfield-pow-spec (pfield-mul base base) n)
                  (pfield-pow-spec base (* 2 n))))
  :hints (("Goal" :induct (pfield-pow-spec base n)
           :in-theory (e/d (pfield-pow-spec pfield-pow-spec-plus-two
                                            pfield-mul-associative)
                           (pfield-mul-commutative pfield-mul)))
          ("Subgoal *1/2" :use
           ((:instance pfield-pow-spec-plus-two
             (base base) (n (+ -2 (* 2 n)))))
           :in-theory (disable pfield-mul-commutative pfield-mul))))

(defthm pfield-pow-spec-odd-form
  (implies (and (pfield-element-p base)
                (natp n))
           (equal (pfield-pow-spec base (+ 1 (* 2 n)))
                  (pfield-mul base (pfield-pow-spec base (* 2 n)))))
  :hints (("Goal" :use
           ((:instance pfield-pow-spec-successor
             (base base) (n (* 2 n))))
           :in-theory (disable pfield-mul-commutative))))

(defthm pfield-pow-fast-accumulator-invariant
  (implies (and (pfield-element-p acc)
                (pfield-element-p base)
                (natp n))
           (equal (pfield-pow-fast acc base n)
                  (pfield-mul acc (pfield-pow-spec base n))))
  :hints (("Goal" :induct (pfield-pow-fast acc base n)
           :in-theory (e/d (pfield-pow-fast pfield-pow-spec
                                             pfield-pow-spec-of-square
                                             pfield-pow-spec-odd-form
                                             pfield-mul-associative)
                           (pfield-mul-commutative pfield-mul)))
          ("Subgoal *1/2" :use
           ((:instance natural-split-at-low-bit (n n))
            (:instance pfield-pow-spec-odd-form
             (base base) (n (floor n 2))))
           :in-theory (disable pfield-mul-commutative pfield-mul))
          ("Subgoal *1/3" :use
           ((:instance natural-split-at-low-bit (n n)))
           :in-theory (disable pfield-mul-commutative pfield-mul))
          ("Subgoal *1/1" :use
           ((:instance natural-split-at-low-bit (n n))
            (:instance pfield-mul-one-right-for-power (x acc)))
           :in-theory (disable pfield-mul-commutative pfield-mul))))

(defthm pfield-element-p-of-pow-spec
  (pfield-element-p (pfield-pow-spec x n))
  :hints (("Goal" :induct (pfield-pow-spec x n)
           :in-theory (enable pfield-pow-spec))))

(defthm pfield-pow-fast-correct
  (equal (pfield-pow-fast (pfield-one) (pfield-fix x) (nfix n))
         (pfield-pow-spec (pfield-fix x) (nfix n)))
  :hints (("Goal" :use
           ((:instance pfield-pow-fast-accumulator-invariant
             (acc (pfield-one)) (base (pfield-fix x)) (n (nfix n)))
            (:instance pfield-mul-one-left
             (x (pfield-pow-spec (pfield-fix x) (nfix n))))
            (:instance pfield-fix-when-pfield-element-p
             (x (pfield-pow-spec (pfield-fix x) (nfix n)))))
           :in-theory (disable pfield-mul-commutative pfield-mul
                               pfield-pow-spec))))

(verify-guards pfield-fix)
(verify-guards pfield-one)
(verify-guards pfield-mul)
(verify-guards pfield-pow-fast)
(verify-guards pfield-pow
  :hints (("Goal" :use pfield-pow-fast-correct)))

; Executable F_7 regression instance.
(defun f7-element-p (x) (pfield::fep x 7))
(defun f7-fix (x) (pfield::fep-fix x 7))
(defun f7-zero () 0)
(defun f7-one () 1)
(defun f7-add (x y) (pfield::add (f7-fix x) (f7-fix y) 7))
(defun f7-mul (x y) (pfield::mul (f7-fix x) (f7-fix y) 7))
(defun f7-neg (x) (pfield::neg (f7-fix x) 7))
(defun f7-inv (x) (pfield::inv (f7-fix x) 7))
(defun f7-sub (x y) (f7-add x (f7-neg y)))
(defun f7-div (x y) (f7-mul x (f7-inv y)))
(def-pow-instance f7-pow-spec f7-pow-fast f7-pow
  f7-one f7-mul f7-fix)

(defthm f7-double-negation-from-generic-kernel
  (equal (f7-neg (f7-neg x)) (f7-fix x))
  :hints (("Goal" :by (:functional-instance
                       pfield-double-negation-from-generic-kernel
                       (pfield-modulus (lambda () 7))
                       (pfield-element-p f7-element-p)
                       (pfield-fix f7-fix)
                       (pfield-zero f7-zero)
                       (pfield-one f7-one)
                       (pfield-add f7-add)
                       (pfield-mul f7-mul)
                       (pfield-neg f7-neg)
                       (pfield-inv f7-inv))
            :in-theory (enable dm::primep))))
