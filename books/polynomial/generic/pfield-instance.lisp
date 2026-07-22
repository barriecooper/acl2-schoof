(in-package "GPOLY")
(include-book "power")
(include-book "../../field/pfield-adapter")

; Generate the exact-arity PFIELD adapter boundary from the same templates as
; the generic theory and concrete instances.  The constrained modulus keeps
; these definitions logical adapters rather than directly executable code.
(def-normalize-eval-instance
  pfield-fix-coefficients pfield-trim-trailing-zeros
  pfield-normalize pfield-eval
  gfield::pfield-fix gfield::pfield-zero
  gfield::pfield-add gfield::pfield-mul)

(defun pfield-coefficient-list-p (xs)
  (if (atom xs) (null xs)
    (and (gfield::pfield-element-p (car xs))
         (pfield-coefficient-list-p (cdr xs)))))
(defun pfield-polynomial-p (xs) (pfield-coefficient-list-p xs))

(defthm pfield-normalize-preserves-eval-from-generic
  (equal (pfield-eval (pfield-normalize poly) x)
         (pfield-eval poly x))
  :hints (("Goal" :by (:functional-instance
                        eval-of-normalize
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                         (eval pfield-eval)))))

(def-add-instance pfield-raw-add pfield-poly-add pfield-fix-coefficients
                  pfield-normalize gfield::pfield-add)
(def-scale-instance pfield-raw-scale pfield-poly-scale pfield-normalize
                    gfield::pfield-fix gfield::pfield-mul)
(def-mul-instance pfield-raw-mul pfield-poly-mul pfield-raw-add
                  pfield-raw-scale pfield-normalize gfield::pfield-zero)
(def-neg-sub-instance pfield-raw-neg pfield-poly-neg pfield-poly-sub
                      pfield-poly-add pfield-normalize gfield::pfield-neg)
(def-const-instance pfield-const gfield::pfield-fix gfield::pfield-zero)
(defun pfield-polynomial-one () (list (gfield::pfield-one)))
(gfield::def-pow-instance pfield-poly-pow-spec pfield-poly-pow-fast
  pfield-poly-pow pfield-polynomial-one pfield-poly-mul pfield-normalize)

(defthm pfield-eval-of-const
  (equal (pfield-eval (pfield-const a) x) (gfield::pfield-fix a))
  :hints (("Goal" :in-theory (enable pfield-const))))

(defthm pfield-poly-mul-const-left
  (equal (pfield-poly-mul (pfield-const a) p)
         (pfield-poly-scale a p))
  :hints (("Goal" :by (:functional-instance
                        poly-mul-const-left
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (raw-add pfield-raw-add) (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul) (poly-mul pfield-poly-mul)
                        (const pfield-const)))
          ("Subgoal 31.2" :use gfield::pfield-mul-inverse-left)
          ("Subgoal 26.9" :use gfield::pfield-mul-fixed-congruence)
          ("Subgoal 25.11" :use gfield::pfield-add-fixed-congruence)
          ("Subgoal 22.2.1"
           :use gfield::pfield-element-p-of-pfield-fix
           :in-theory (enable gfield::pfield-fix
                              gfield::pfield-element-p))
          ("Subgoal 22.2.1'''" :in-theory (enable mod))
          ("Subgoal 21.2.1'" :in-theory (enable mod))
          ("Subgoal 8.2.1'" :in-theory (enable mod))))

(defthm pfield-poly-mul-of-consts
  (equal (pfield-poly-mul (pfield-const a) (pfield-const b))
         (pfield-const (gfield::pfield-mul a b)))
  :hints (("Goal"
           :in-theory (enable pfield-const pfield-poly-mul pfield-raw-mul
                              pfield-poly-scale pfield-raw-scale
                              pfield-normalize pfield-trim-trailing-zeros
                              pfield-fix-coefficients))))

(defthm pfield-eval-of-poly-scale-from-generic
  (equal (pfield-eval (pfield-poly-scale a poly) x)
         (gfield::pfield-mul a (pfield-eval poly x)))
  :hints (("Goal" :by (:functional-instance
                        eval-of-poly-scale
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (eval pfield-eval)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)))))

(defthm pfield-eval-of-raw-scale-from-generic
  (equal (pfield-eval (pfield-raw-scale a poly) x)
         (gfield::pfield-mul a (pfield-eval poly x)))
  :hints (("Goal" :by (:functional-instance
                        eval-of-raw-scale
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (eval pfield-eval)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)))))

(defthm pfield-eval-of-raw-add-from-generic
  (equal (pfield-eval (pfield-raw-add x y) a)
         (gfield::pfield-add (pfield-eval x a) (pfield-eval y a)))
  :hints (("Goal" :induct (pfield-raw-add x y)
           :in-theory (enable gfield::pfield-mul-left-distributive
                              gfield::pfield-add-associative))))

(defthm pfield-eval-of-add-from-generic
  (equal (pfield-eval (pfield-poly-add x y) a)
         (gfield::pfield-add (pfield-eval x a) (pfield-eval y a)))
  :hints (("Goal"
           :use ((:instance pfield-normalize-preserves-eval-from-generic
                            (poly (pfield-raw-add (pfield-normalize x)
                                                  (pfield-normalize y)))
                            (x a))
                 (:instance pfield-normalize-preserves-eval-from-generic
                            (poly x) (x a))
                 (:instance pfield-normalize-preserves-eval-from-generic
                            (poly y) (x a))
                 (:instance pfield-eval-of-raw-add-from-generic
                            (x (pfield-normalize x))
                            (y (pfield-normalize y))))
           :in-theory (disable pfield-normalize-preserves-eval-from-generic
                               pfield-eval-of-raw-add-from-generic))))


(defthm pfield-eval-of-raw-mul-from-generic
  (equal (pfield-eval (pfield-raw-mul f g) x)
         (gfield::pfield-mul (pfield-eval f x) (pfield-eval g x)))
  :hints (("Goal" :by (:functional-instance
                        eval-of-raw-mul
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (eval pfield-eval)
                        (raw-add pfield-raw-add)
                        (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul)
                        (poly-mul pfield-poly-mul)))))

(defthm pfield-eval-of-poly-mul-from-generic
  (equal (pfield-eval (pfield-poly-mul f g) x)
         (gfield::pfield-mul (pfield-eval f x) (pfield-eval g x)))
  :hints (("Goal"
           :use ((:instance pfield-normalize-preserves-eval-from-generic
                            (poly (pfield-raw-mul (pfield-normalize f)
                                                  (pfield-normalize g)))
                            (x x))
                 (:instance pfield-normalize-preserves-eval-from-generic
                            (poly f) (x x))
                 (:instance pfield-normalize-preserves-eval-from-generic
                            (poly g) (x x))
                 (:instance pfield-eval-of-raw-mul-from-generic
                            (f (pfield-normalize f))
                            (g (pfield-normalize g))))
           :in-theory (disable pfield-normalize-preserves-eval-from-generic
                               pfield-eval-of-raw-mul-from-generic))))

(defthm pfield-raw-add-commutative-from-generic
  (equal (pfield-raw-add x y) (pfield-raw-add y x))
  :hints (("Goal" :by (:functional-instance
                        raw-add-commutative
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (raw-add pfield-raw-add)))))

(defthm pfield-zero-is-0
  (equal (gfield::pfield-zero) 0))

(defthm pfield-fix-of-literal-zero
  (equal (gfield::pfield-fix 0) 0))

(defthm pfield-one-is-1
  (equal (gfield::pfield-one) 1))

(defthm pfield-fix-of-literal-one
  (equal (gfield::pfield-fix 1) 1))

(defthm pfield-element-p-of-literal-one
  (gfield::pfield-element-p 1))

(defthm pfield-element-p-of-literal-zero
  (gfield::pfield-element-p 0))

(defthm pfield-mul-literal-one-left
  (equal (gfield::pfield-mul 1 x) (gfield::pfield-fix x)))

(defthm pfield-inv-of-literal-zero
  (equal (gfield::pfield-inv 0) 0))

(defthm pfield-add-literal-zero-left
  (equal (gfield::pfield-add 0 x) (gfield::pfield-fix x)))

(defthm pfield-poly-mul-commutative-from-generic
  (equal (pfield-poly-mul x y) (pfield-poly-mul y x))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        poly-mul-commutative
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (raw-add pfield-raw-add)
                        (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul)
                        (poly-mul pfield-poly-mul))
           :do-not '(preprocess)
           :in-theory '(pfield-zero-is-0 pfield-fix-of-literal-zero
                        pfield-one-is-1
                        pfield-fix-of-literal-one
                        pfield-element-p-of-literal-one
                        pfield-element-p-of-literal-zero
                        pfield-mul-literal-one-left
                        pfield-inv-of-literal-zero
                        pfield-add-literal-zero-left
                        pfield-fix-coefficients
                        pfield-trim-trailing-zeros pfield-normalize
                        pfield-raw-add pfield-poly-add
                        pfield-raw-scale pfield-poly-scale
                        pfield-raw-mul pfield-poly-mul
                        gfield::booleanp-of-pfield-element-p
                        gfield::pfield-element-p-of-pfield-fix
                        gfield::pfield-fix-idempotent
                        gfield::pfield-element-p-of-pfield-zero
                        gfield::pfield-element-p-of-pfield-one
                        gfield::pfield-zero-not-equal-pfield-one
                        gfield::pfield-fix-of-zero
                        gfield::pfield-fix-of-one
                        gfield::pfield-element-p-of-pfield-add
                        gfield::pfield-element-p-of-pfield-mul
                        gfield::pfield-element-p-of-pfield-neg
                        gfield::pfield-element-p-of-pfield-inv
                        gfield::pfield-fix-of-pfield-add
                        gfield::pfield-fix-of-pfield-mul
                        gfield::pfield-fix-of-pfield-neg
                        gfield::pfield-fix-of-pfield-inv
                        gfield::pfield-add-of-fixes
                        gfield::pfield-mul-of-fixes
                        gfield::pfield-neg-of-fix
                        gfield::pfield-inv-of-fix
                        gfield::pfield-add-zero-left
                        gfield::pfield-add-inverse-left
                        gfield::pfield-mul-one-left
                        gfield::pfield-inv-of-zero
                        gfield::pfield-add-fix-right
                        gfield::pfield-add-fix-left
                        gfield::pfield-mul-fix-left))
          ("Subgoal 13" :by gfield::pfield-mul-fix-right)
          ("Subgoal 12" :by gfield::pfield-mul-left-distributive)
          ("Subgoal 11" :by gfield::pfield-mul-commutative)
          ("Subgoal 10" :by gfield::pfield-mul-associative)
          ("Subgoal 9" :by gfield::pfield-add-commutative)
          ("Subgoal 8" :by gfield::pfield-add-associative)
          ("Subgoal 7" :by gfield::booleanp-of-pfield-element-p)
          ("Subgoal 6" :by gfield::pfield-fix-when-pfield-element-p)
          ("Subgoal 5" :use gfield::pfield-mul-inverse-left)
          ("Subgoal 3" :by gfield::pfield-mul-fixed-congruence)
          ("Subgoal 2" :by gfield::pfield-add-fixed-congruence)))

(defthm pfield-poly-mul-left-distributive-from-generic
  (equal (pfield-poly-mul x (pfield-poly-add y z))
         (pfield-poly-add (pfield-poly-mul x y)
                          (pfield-poly-mul x z)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        poly-mul-left-distributive
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (raw-add pfield-raw-add)
                        (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul)
                        (poly-mul pfield-poly-mul)))))

(defthm pfield-poly-mul-right-distributive-from-generic
  (equal (pfield-poly-mul (pfield-poly-add x y) z)
         (pfield-poly-add (pfield-poly-mul x z)
                          (pfield-poly-mul y z)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        poly-mul-right-distributive
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (raw-add pfield-raw-add)
                        (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul)
                        (poly-mul pfield-poly-mul)))))

(defthm pfield-poly-mul-associative-from-generic
  (equal (pfield-poly-mul (pfield-poly-mul x y) z)
         (pfield-poly-mul x (pfield-poly-mul y z)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        poly-mul-associative
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (raw-add pfield-raw-add)
                        (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul)
                        (poly-mul pfield-poly-mul)))))

; Canonicality for this generated adapter is exactly fixed-point status under
; its existing normalization operation; no parallel representation is added.
(defun pfield-canonical-polynomial-p (xs)
  (equal (pfield-normalize xs) xs))

(defthm pfield-canonical-polynomial-p-of-normalize
  (pfield-canonical-polynomial-p (pfield-normalize xs))
  :hints (("Goal" :in-theory (enable pfield-canonical-polynomial-p
                                      pfield-normalize
                                      pfield-fix-coefficients
                                      pfield-trim-trailing-zeros))))

(defthm pfield-normalize-when-canonical
  (implies (pfield-canonical-polynomial-p xs)
           (equal (pfield-normalize xs) xs))
  :hints (("Goal" :in-theory (enable pfield-canonical-polynomial-p))))

(defthm pfield-canonical-polynomial-p-of-polynomial-one
  (pfield-canonical-polynomial-p (pfield-polynomial-one))
  :hints (("Goal" :in-theory (enable pfield-canonical-polynomial-p
                                      pfield-polynomial-one
                                      pfield-normalize
                                      pfield-fix-coefficients
                                      pfield-trim-trailing-zeros))))

(defthm pfield-canonical-polynomial-p-of-literal-one
  (pfield-canonical-polynomial-p '(1))
  :hints (("Goal" :use pfield-canonical-polynomial-p-of-polynomial-one
           :in-theory (enable pfield-polynomial-one))))

(defthm pfield-canonical-polynomial-p-of-poly-mul
  (pfield-canonical-polynomial-p (pfield-poly-mul x y))
  :hints (("Goal" :in-theory (e/d (pfield-canonical-polynomial-p
                                           pfield-poly-mul)
                                          (pfield-normalize)))))

(defthm pfield-poly-mul-of-one-left-for-power
  (equal (pfield-poly-mul (pfield-polynomial-one) x)
         (pfield-normalize x))
  :hints (("Goal" :use ((:functional-instance
                        poly-mul-of-one-left
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (raw-add pfield-raw-add) (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul) (poly-mul pfield-poly-mul)
                        (polynomial-one pfield-polynomial-one)))
           :in-theory (enable pfield-polynomial-one))))

(defthm pfield-poly-mul-of-one-right-for-power
  (equal (pfield-poly-mul x (pfield-polynomial-one))
         (pfield-normalize x))
  :hints (("Goal" :use ((:functional-instance
                        poly-mul-of-one-right
                        (gfield::field-element-p gfield::pfield-element-p)
                        (gfield::field-fix gfield::pfield-fix)
                        (gfield::field-zero gfield::pfield-zero)
                        (gfield::field-one gfield::pfield-one)
                        (gfield::field-add gfield::pfield-add)
                        (gfield::field-mul gfield::pfield-mul)
                        (gfield::field-neg gfield::pfield-neg)
                        (gfield::field-inv gfield::pfield-inv)
                        (fix-coefficients pfield-fix-coefficients)
                        (trim-trailing-zeros pfield-trim-trailing-zeros)
                        (normalize pfield-normalize)
                        (raw-add pfield-raw-add) (poly-add pfield-poly-add)
                        (raw-scale pfield-raw-scale)
                        (poly-scale pfield-poly-scale)
                        (raw-mul pfield-raw-mul) (poly-mul pfield-poly-mul)
                        (polynomial-one pfield-polynomial-one)))
           :in-theory (enable pfield-polynomial-one))))

(defthm pfield-poly-mul-one-left-when-canonical
  (implies (pfield-canonical-polynomial-p x)
           (equal (pfield-poly-mul (pfield-polynomial-one) x) x))
  :hints (("Goal" :use pfield-poly-mul-of-one-left-for-power
           :in-theory (enable pfield-canonical-polynomial-p))))

(defthm pfield-poly-mul-one-right-when-canonical
  (implies (pfield-canonical-polynomial-p x)
           (equal (pfield-poly-mul x (pfield-polynomial-one)) x))
  :hints (("Goal" :use pfield-poly-mul-of-one-right-for-power
           :in-theory (enable pfield-canonical-polynomial-p))))

(defthm pfield-poly-mul-associate-right-for-power
  (equal (pfield-poly-mul (pfield-poly-mul a b) c)
         (pfield-poly-mul a (pfield-poly-mul b c)))
  :hints (("Goal" :use ((:instance pfield-poly-mul-associative-from-generic
                                    (x a) (y b) (z c)))
           :in-theory (disable))))

(defthm pfield-poly-pow-spec-successor
  (equal (pfield-poly-pow-spec base (+ 1 (nfix n)))
         (pfield-poly-mul (pfield-normalize base)
                       (pfield-poly-pow-spec base n)))
  :hints (("Goal" :in-theory (enable pfield-poly-pow-spec))))

(defthm pfield-poly-pow-spec-plus-two
  (implies (and (pfield-canonical-polynomial-p base) (natp n))
           (equal (pfield-poly-pow-spec base (+ 2 n))
                  (pfield-poly-mul base
                    (pfield-poly-mul base (pfield-poly-pow-spec base n)))))
  :hints (("Goal" :use ((:instance pfield-poly-pow-spec-successor
                                    (base base) (n (+ 1 n)))
                          (:instance pfield-poly-pow-spec-successor
                                    (base base) (n n)))
           :in-theory (disable))))

(defthm pfield-poly-pow-spec-of-square
  (implies (and (pfield-canonical-polynomial-p base) (natp n))
           (equal (pfield-poly-pow-spec (pfield-poly-mul base base) n)
                  (pfield-poly-pow-spec base (* 2 n))))
  :hints (("Goal" :induct (pfield-poly-pow-spec base n)
           :in-theory (e/d (pfield-poly-pow-spec
                            pfield-poly-pow-spec-plus-two
                            pfield-poly-mul-associate-right-for-power)
                           (pfield-poly-mul)))
          ("Subgoal *1/2" :use ((:instance pfield-poly-pow-spec-plus-two
                                            (base base)
                                            (n (+ -2 (* 2 n)))))
           :in-theory (disable pfield-poly-mul))))

(defthm pfield-poly-pow-spec-odd-form
  (implies (and (pfield-canonical-polynomial-p base) (natp n))
           (equal (pfield-poly-pow-spec base (+ 1 (* 2 n)))
                  (pfield-poly-mul base (pfield-poly-pow-spec base (* 2 n)))))
  :hints (("Goal" :use ((:instance pfield-poly-pow-spec-successor
                                    (base base) (n (* 2 n))))
           :in-theory (disable))))

(defthm pfield-poly-pow-fast-accumulator-invariant
  (implies (and (pfield-canonical-polynomial-p acc)
                (pfield-canonical-polynomial-p base)
                (natp n))
           (equal (pfield-poly-pow-fast acc base n)
                  (pfield-poly-mul acc (pfield-poly-pow-spec base n))))
  :hints (("Goal" :induct (pfield-poly-pow-fast acc base n)
           :in-theory (e/d (pfield-poly-pow-fast pfield-poly-pow-spec
                            pfield-poly-pow-spec-of-square
                            pfield-poly-pow-spec-odd-form
                            pfield-poly-mul-associate-right-for-power)
                           (pfield-poly-mul pfield-normalize
                            pfield-canonical-polynomial-p
                            pfield-polynomial-one)))
          ("Subgoal *1/2" :use ((:instance gfield::natural-split-at-low-bit (n n))
                                  (:instance pfield-poly-pow-spec-odd-form
                                             (base base) (n (floor n 2))))
           :in-theory (disable pfield-poly-mul pfield-normalize
                               pfield-canonical-polynomial-p pfield-polynomial-one))
          ("Subgoal *1/3" :use ((:instance gfield::natural-split-at-low-bit (n n)))
           :in-theory (disable pfield-poly-mul pfield-normalize
                               pfield-canonical-polynomial-p pfield-polynomial-one))
          ("Subgoal *1/1" :use ((:instance gfield::natural-split-at-low-bit (n n))
                                  (:instance pfield-poly-mul-one-right-when-canonical
                                             (x acc)))
           :in-theory (disable pfield-poly-mul pfield-normalize
                               pfield-canonical-polynomial-p pfield-polynomial-one))))

(defthm pfield-canonical-polynomial-p-of-poly-pow-spec
  (pfield-canonical-polynomial-p (pfield-poly-pow-spec base n))
  :hints (("Goal" :induct (pfield-poly-pow-spec base n)
           :in-theory (e/d (pfield-poly-pow-spec)
                           (pfield-poly-mul pfield-normalize
                            pfield-canonical-polynomial-p
                            pfield-polynomial-one)))
          ("Subgoal *1/1" :use pfield-canonical-polynomial-p-of-literal-one)))

(defthm pfield-poly-pow-fast-correct
  (equal (pfield-poly-pow-fast (pfield-polynomial-one)
                            (pfield-normalize f) (nfix n))
         (pfield-poly-pow-spec (pfield-normalize f) (nfix n)))
  :hints (("Goal"
           :use ((:instance pfield-poly-pow-fast-accumulator-invariant
                            (acc (pfield-polynomial-one))
                            (base (pfield-normalize f))
                            (n (nfix n)))
                 (:instance pfield-poly-mul-one-left-when-canonical
                            (x (pfield-poly-pow-spec
                                (pfield-normalize f) (nfix n))))
                 (:instance pfield-canonical-polynomial-p-of-poly-pow-spec
                            (base (pfield-normalize f)) (n (nfix n))))
           :in-theory (disable pfield-poly-pow-fast pfield-poly-pow-spec
                               pfield-poly-mul pfield-normalize
                               pfield-canonical-polynomial-p
                               pfield-polynomial-one))))


(verify-guards gfield::pfield-zero)
(verify-guards gfield::pfield-add)
(verify-guards pfield-fix-coefficients)
(verify-guards pfield-trim-trailing-zeros)
(verify-guards pfield-normalize)
(verify-guards pfield-raw-add)
(verify-guards pfield-poly-add)
(verify-guards pfield-raw-scale)
(verify-guards pfield-poly-scale)
(verify-guards pfield-raw-mul)
(verify-guards pfield-poly-mul)
(verify-guards pfield-polynomial-one)
(verify-guards pfield-poly-pow-fast)
(verify-guards pfield-poly-pow
  :hints (("Goal" :use ((:instance pfield-poly-pow-fast-correct
                                    (f gfield::x) (n gfield::n))))))

; Ordinary executable F_7 DEFUNs generated from the same templates as the
; abstract algorithms.  Use :TRANS1 on this event to inspect the expansion.
(def-normalize-eval-instance
  f7-fix-coefficients f7-trim-trailing-zeros f7-normalize f7-eval
  gfield::f7-fix gfield::f7-zero gfield::f7-add gfield::f7-mul)

(defthm f7-normalize-preserves-eval-from-generic
  (equal (f7-eval (f7-normalize poly) x)
         (f7-eval poly x))
  :hints (("Goal" :by (:functional-instance
                        pfield-normalize-preserves-eval-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-eval f7-eval))
           :in-theory (enable dm::primep))))
(def-add-instance f7-raw-add f7-poly-add f7-fix-coefficients f7-normalize
                  gfield::f7-add)
(def-neg-sub-instance f7-raw-neg f7-poly-neg f7-poly-sub f7-poly-add
                      f7-normalize gfield::f7-neg)
(def-scale-instance f7-raw-scale f7-poly-scale f7-normalize
                    gfield::f7-fix gfield::f7-mul)
(def-mul-instance f7-raw-mul f7-poly-mul f7-raw-add f7-raw-scale
                  f7-normalize gfield::f7-zero)
(def-const-instance f7-const gfield::f7-fix gfield::f7-zero)
(defun f7-polynomial-one () (list (gfield::f7-one)))
(gfield::def-pow-instance f7-poly-pow-spec f7-poly-pow-fast f7-poly-pow
  f7-polynomial-one f7-poly-mul f7-normalize)

(defthm f7-eval-of-const-from-pfield
  (equal (f7-eval (f7-const a) x) (gfield::f7-fix a))
  :hints (("Goal" :in-theory (enable f7-const))))

(defthm f7-poly-mul-const-left-from-pfield
  (equal (f7-poly-mul (f7-const a) p) (f7-poly-scale a p))
  :hints (("Goal" :by (:functional-instance
                        pfield-poly-mul-const-left
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul)
                        (pfield-const f7-const))
           :in-theory (enable dm::primep))))

(defthm f7-poly-mul-of-consts-from-pfield
  (equal (f7-poly-mul (f7-const a) (f7-const b))
         (f7-const (gfield::f7-mul a b)))
  :hints (("Goal" :in-theory (enable f7-const f7-poly-mul f7-raw-mul
                                      f7-poly-scale f7-raw-scale
                                      f7-normalize f7-trim-trailing-zeros
                                      f7-fix-coefficients))))

(defthm f7-eval-of-poly-add-from-generic
  (equal (f7-eval (f7-poly-add x y) a)
         (gfield::f7-add (f7-eval x a) (f7-eval y a)))
  :hints (("Goal" :by (:functional-instance
                        pfield-eval-of-add-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-eval f7-eval)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add))
           :in-theory (enable dm::primep))))

(defthm f7-eval-of-poly-scale-from-generic
  (equal (f7-eval (f7-poly-scale a poly) x)
         (gfield::f7-mul a (f7-eval poly x)))
  :hints (("Goal" :by (:functional-instance
                        pfield-eval-of-poly-scale-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-eval f7-eval)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale))
           :in-theory (enable dm::primep))))

(defthm f7-eval-of-poly-mul-from-generic
  (equal (f7-eval (f7-poly-mul f g) x)
         (gfield::f7-mul (f7-eval f x) (f7-eval g x)))
  :hints (("Goal" :by (:functional-instance
                        pfield-eval-of-poly-mul-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-element-p gfield::f7-element-p)
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (gfield::pfield-neg gfield::f7-neg)
                        (gfield::pfield-inv gfield::f7-inv)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-eval f7-eval)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul))
           :in-theory (enable dm::primep))))

(defthm f7-poly-mul-commutative-from-generic
  (equal (f7-poly-mul x y) (f7-poly-mul y x))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        pfield-poly-mul-commutative-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul))
           :in-theory (enable dm::primep))))

(defthm f7-poly-mul-left-distributive-from-generic
  (equal (f7-poly-mul x (f7-poly-add y z))
         (f7-poly-add (f7-poly-mul x y) (f7-poly-mul x z)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        pfield-poly-mul-left-distributive-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul))
           :in-theory (enable dm::primep))))

(defthm f7-poly-mul-right-distributive-from-generic
  (equal (f7-poly-mul (f7-poly-add x y) z)
         (f7-poly-add (f7-poly-mul x z) (f7-poly-mul y z)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        pfield-poly-mul-right-distributive-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul))
           :in-theory (enable dm::primep))))

(defthm f7-poly-mul-associative-from-generic
  (equal (f7-poly-mul (f7-poly-mul x y) z)
         (f7-poly-mul x (f7-poly-mul y z)))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        pfield-poly-mul-associative-from-generic
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul))
           :in-theory (enable dm::primep))))



; Canonicality for this generated adapter is exactly fixed-point status under
; its existing normalization operation; no parallel representation is added.
(defun f7-canonical-polynomial-p (xs)
  (equal (f7-normalize xs) xs))

(defthm f7-canonical-polynomial-p-of-normalize
  (f7-canonical-polynomial-p (f7-normalize xs))
  :hints (("Goal" :in-theory (enable f7-canonical-polynomial-p
                                      f7-normalize
                                      f7-fix-coefficients
                                      f7-trim-trailing-zeros))))

(defthm f7-normalize-when-canonical
  (implies (f7-canonical-polynomial-p xs)
           (equal (f7-normalize xs) xs))
  :hints (("Goal" :in-theory (enable f7-canonical-polynomial-p))))

(defthm f7-canonical-polynomial-p-of-polynomial-one
  (f7-canonical-polynomial-p (f7-polynomial-one))
  :hints (("Goal" :in-theory (enable f7-canonical-polynomial-p
                                      f7-polynomial-one
                                      f7-normalize
                                      f7-fix-coefficients
                                      f7-trim-trailing-zeros))))

(defthm f7-normalize-idempotent-for-power
  (equal (f7-normalize (f7-normalize xs)) (f7-normalize xs))
  :hints (("Goal" :use ((:instance f7-normalize-when-canonical
                                    (xs (f7-normalize xs))))
           :in-theory (disable f7-normalize
                               f7-canonical-polynomial-p))))

(defthm f7-canonical-polynomial-p-of-literal-one
  (f7-canonical-polynomial-p '(1))
  :hints (("Goal" :use f7-canonical-polynomial-p-of-polynomial-one
           :in-theory (enable f7-polynomial-one))))

(defthm f7-canonical-polynomial-p-of-poly-mul
  (f7-canonical-polynomial-p (f7-poly-mul x y))
  :hints (("Goal" :in-theory (e/d (f7-canonical-polynomial-p
                                           f7-poly-mul)
                                          (f7-normalize)))))

(defthm f7-poly-mul-of-one-left-for-power
  (equal (f7-poly-mul (f7-polynomial-one) x)
         (f7-normalize x))
  :hints (("Goal" :by (:functional-instance
                        pfield-poly-mul-of-one-left-for-power
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul)
                        (pfield-polynomial-one f7-polynomial-one))
           :in-theory (enable dm::primep))))

(defthm f7-poly-mul-of-one-right-for-power
  (equal (f7-poly-mul x (f7-polynomial-one))
         (f7-normalize x))
  :hints (("Goal" :by (:functional-instance
                        pfield-poly-mul-of-one-right-for-power
                        (gfield::pfield-modulus (lambda () 7))
                        (gfield::pfield-fix gfield::f7-fix)
                        (gfield::pfield-zero gfield::f7-zero)
                        (gfield::pfield-one gfield::f7-one)
                        (gfield::pfield-add gfield::f7-add)
                        (gfield::pfield-mul gfield::f7-mul)
                        (pfield-fix-coefficients f7-fix-coefficients)
                        (pfield-trim-trailing-zeros f7-trim-trailing-zeros)
                        (pfield-normalize f7-normalize)
                        (pfield-raw-add f7-raw-add)
                        (pfield-poly-add f7-poly-add)
                        (pfield-raw-scale f7-raw-scale)
                        (pfield-poly-scale f7-poly-scale)
                        (pfield-raw-mul f7-raw-mul)
                        (pfield-poly-mul f7-poly-mul)
                        (pfield-polynomial-one f7-polynomial-one))
           :in-theory (enable dm::primep))))

(defthm f7-poly-mul-one-left-when-canonical
  (implies (f7-canonical-polynomial-p x)
           (equal (f7-poly-mul (f7-polynomial-one) x) x))
  :hints (("Goal" :use f7-poly-mul-of-one-left-for-power
           :in-theory (enable f7-canonical-polynomial-p))))

(defthm f7-poly-mul-one-right-when-canonical
  (implies (f7-canonical-polynomial-p x)
           (equal (f7-poly-mul x (f7-polynomial-one)) x))
  :hints (("Goal" :use f7-poly-mul-of-one-right-for-power
           :in-theory (enable f7-canonical-polynomial-p))))

(defthm f7-poly-mul-associate-right-for-power
  (equal (f7-poly-mul (f7-poly-mul a b) c)
         (f7-poly-mul a (f7-poly-mul b c)))
  :hints (("Goal" :use ((:instance f7-poly-mul-associative-from-generic
                                    (x a) (y b) (z c)))
           :in-theory (disable))))

(defthm f7-poly-pow-spec-successor
  (equal (f7-poly-pow-spec base (+ 1 (nfix n)))
         (f7-poly-mul (f7-normalize base)
                       (f7-poly-pow-spec base n)))
  :hints (("Goal" :in-theory (enable f7-poly-pow-spec))))

(defthm f7-poly-pow-spec-plus-two
  (implies (and (f7-canonical-polynomial-p base) (natp n))
           (equal (f7-poly-pow-spec base (+ 2 n))
                  (f7-poly-mul base
                    (f7-poly-mul base (f7-poly-pow-spec base n)))))
  :hints (("Goal" :use ((:instance f7-poly-pow-spec-successor
                                    (base base) (n (+ 1 n)))
                          (:instance f7-poly-pow-spec-successor
                                    (base base) (n n)))
           :in-theory (disable))))

(defthm f7-poly-pow-spec-of-square
  (implies (and (f7-canonical-polynomial-p base) (natp n))
           (equal (f7-poly-pow-spec (f7-poly-mul base base) n)
                  (f7-poly-pow-spec base (* 2 n))))
  :hints (("Goal" :induct (f7-poly-pow-spec base n)
           :in-theory (e/d (f7-poly-pow-spec
                            f7-poly-pow-spec-plus-two
                            f7-poly-mul-associate-right-for-power)
                           (f7-poly-mul)))
          ("Subgoal *1/2" :use ((:instance f7-poly-pow-spec-plus-two
                                            (base base)
                                            (n (+ -2 (* 2 n)))))
           :in-theory (disable f7-poly-mul))))

(defthm f7-poly-pow-spec-odd-form
  (implies (and (f7-canonical-polynomial-p base) (natp n))
           (equal (f7-poly-pow-spec base (+ 1 (* 2 n)))
                  (f7-poly-mul base (f7-poly-pow-spec base (* 2 n)))))
  :hints (("Goal" :use ((:instance f7-poly-pow-spec-successor
                                    (base base) (n (* 2 n))))
           :in-theory (disable))))

(defthm f7-poly-pow-fast-accumulator-invariant
  (implies (and (f7-canonical-polynomial-p acc)
                (f7-canonical-polynomial-p base)
                (natp n))
           (equal (f7-poly-pow-fast acc base n)
                  (f7-poly-mul acc (f7-poly-pow-spec base n))))
  :hints (("Goal" :induct (f7-poly-pow-fast acc base n)
           :in-theory (e/d (f7-poly-pow-fast f7-poly-pow-spec
                            f7-poly-pow-spec-of-square
                            f7-poly-pow-spec-odd-form
                            f7-poly-mul-associate-right-for-power)
                           (f7-poly-mul f7-normalize
                            f7-canonical-polynomial-p
                            f7-polynomial-one)))
          ("Subgoal *1/2" :use ((:instance gfield::natural-split-at-low-bit (n n))
                                  (:instance f7-poly-pow-spec-odd-form
                                             (base base) (n (floor n 2))))
           :in-theory (disable f7-poly-mul f7-normalize
                               f7-canonical-polynomial-p f7-polynomial-one))
          ("Subgoal *1/3" :use ((:instance gfield::natural-split-at-low-bit (n n)))
           :in-theory (disable f7-poly-mul f7-normalize
                               f7-canonical-polynomial-p f7-polynomial-one))
          ("Subgoal *1/1" :use ((:instance gfield::natural-split-at-low-bit (n n))
                                  (:instance f7-poly-mul-one-right-when-canonical
                                             (x acc)))
           :in-theory (disable f7-poly-mul f7-normalize
                               f7-canonical-polynomial-p f7-polynomial-one))))

(defthm f7-canonical-polynomial-p-of-poly-pow-spec
  (f7-canonical-polynomial-p (f7-poly-pow-spec base n))
  :hints (("Goal" :induct (f7-poly-pow-spec base n)
           :in-theory (e/d (f7-poly-pow-spec)
                           (f7-poly-mul f7-normalize
                            f7-canonical-polynomial-p
                            f7-polynomial-one)))
          ("Subgoal *1/1" :use f7-canonical-polynomial-p-of-literal-one)))

(defthm f7-poly-pow-fast-correct
  (equal (f7-poly-pow-fast (f7-polynomial-one)
                            (f7-normalize f) (nfix n))
         (f7-poly-pow-spec (f7-normalize f) (nfix n)))
  :hints (("Goal"
           :use ((:instance f7-poly-pow-fast-accumulator-invariant
                            (acc (f7-polynomial-one))
                            (base (f7-normalize f))
                            (n (nfix n)))
                 (:instance f7-poly-mul-one-left-when-canonical
                            (x (f7-poly-pow-spec
                                (f7-normalize f) (nfix n))))
                 (:instance f7-canonical-polynomial-p-of-poly-pow-spec
                            (base (f7-normalize f)) (n (nfix n))))
           :in-theory (disable f7-poly-pow-fast f7-poly-pow-spec
                               f7-poly-mul f7-normalize
                               f7-canonical-polynomial-p
                               f7-polynomial-one))))

(verify-guards gfield::f7-zero)
(verify-guards gfield::f7-add)
(verify-guards f7-fix-coefficients)
(verify-guards f7-trim-trailing-zeros)
(verify-guards f7-normalize)
(verify-guards f7-raw-add)
(verify-guards f7-poly-add)
(verify-guards f7-raw-scale)
(verify-guards f7-poly-scale)
(verify-guards f7-raw-mul)
(verify-guards f7-poly-mul)
(verify-guards f7-polynomial-one)
(verify-guards f7-poly-pow-fast)
(verify-guards f7-poly-pow
  :hints (("Goal" :use ((:instance f7-poly-pow-fast-correct
                                    (f gfield::x) (n gfield::n))))))

(assert-event (equal (f7-normalize '(1 2 0 0)) '(1 2)))
(assert-event (equal (f7-normalize '(0 0 0)) nil))
(assert-event (equal (f7-eval '(1 2 3) 2) 3))
(assert-event (equal (f7-eval '(6 6) 6) 0))
(assert-event (equal (f7-eval (f7-normalize '(1 2 3 0 0)) 2)
                     (f7-eval '(1 2 3 0 0) 2)))
(assert-event (equal (f7-poly-add '(1 2) '(2 3)) '(3 5)))
(assert-event (equal (f7-poly-add '(6 6) '(2 3)) '(1 2)))
(assert-event (equal (f7-poly-add '(1) '(2 3)) '(3 3)))
(assert-event (equal (f7-poly-add '(1 2) '(2 5)) '(3)))
(assert-event (equal (f7-poly-add '(1 2) '(6 5)) nil))
(assert-event (equal (f7-poly-neg '(1 2)) '(6 5)))
(assert-event (equal (f7-poly-sub '(1 2) '(2 3)) '(6 6)))
(assert-event (equal (f7-poly-sub '(1 2) '(1 2)) nil))
(assert-event (equal (f7-eval (f7-poly-add '(1 2) '(2 3)) 2) 6))
(assert-event (equal (f7-eval (f7-poly-neg '(1 2)) 2) 2))
(assert-event (equal (f7-eval (f7-poly-sub '(1 2) '(2 3)) 2) 4))
(assert-event
 (equal (f7-poly-add (f7-poly-add '(1 2) '(2 3)) '(4 5))
        (f7-poly-add '(1 2) (f7-poly-add '(2 3) '(4 5)))))
(assert-event (equal (f7-poly-scale 3 '(1 2 3)) '(3 6 2)))
(assert-event (equal (f7-poly-scale 0 '(1 2 3)) nil))
(assert-event (equal (f7-poly-scale 1 '(1 2 0 0)) '(1 2)))
(assert-event (equal (f7-poly-scale 2 '(1 0 4)) '(2 0 1)))
(assert-event (equal (f7-poly-scale 7 '(1 0 4)) nil))
(assert-event (equal (f7-poly-scale 2 '(1 . 4)) '(2)))
(assert-event (equal (f7-eval (f7-poly-scale 3 '(1 2 3)) 2)
                     (gfield::f7-mul 3 (f7-eval '(1 2 3) 2))))
(assert-event
 (equal (f7-poly-scale 2 (f7-poly-scale 3 '(1 2 3)))
        (f7-poly-scale (gfield::f7-mul 2 3) '(1 2 3))))
(assert-event
 (equal (f7-poly-scale 3 (f7-poly-add '(1 2) '(3 4)))
        (f7-poly-add (f7-poly-scale 3 '(1 2))
                     (f7-poly-scale 3 '(3 4)))))
(assert-event (equal (f7-poly-mul nil '(1 2)) nil))
(assert-event (equal (f7-poly-mul '(1 2) nil) nil))
(assert-event (equal (f7-poly-mul '(1) '(1 2)) '(1 2)))
(assert-event (equal (f7-poly-mul '(1 2) '(1)) '(1 2)))
(assert-event (equal (f7-poly-mul '(3) '(1 2)) '(3 6)))
; (1+2X)(3+4X) = 3+3X+X^2 over F_7.
(assert-event (equal (f7-poly-mul '(1 2) '(3 4)) '(3 3 1)))
(assert-event (equal (f7-poly-mul '(1 0 4) '(2 0 2)) '(2 0 3 0 1)))
(assert-event (equal (f7-poly-mul '(7 14) '(1 2)) nil))
(assert-event (equal (f7-poly-mul '(1 2 0 0) '(3 4 0)) '(3 3 1)))
(assert-event (equal (f7-poly-mul '(1 . bad-tail) '(3 4)) '(3 4)))
(assert-event
 (equal (f7-eval (f7-poly-mul '(1 2) '(3 4)) 2)
        (gfield::f7-mul (f7-eval '(1 2) 2) (f7-eval '(3 4) 2))))
(assert-event (equal (f7-const 0) nil))
(assert-event (equal (f7-const 1) '(1)))
(assert-event (equal (f7-const 8) '(1)))
(assert-event (equal (f7-const 'malformed) nil))
(assert-event (equal (f7-eval (f7-const 5) 0) 5))
(assert-event (equal (f7-eval (f7-const 5) 6) 5))
(assert-event
 (equal (f7-poly-add (f7-const 3) (f7-const 4)) (f7-const 0)))
(assert-event
 (equal (f7-poly-mul (f7-const 3) (f7-const 5)) (f7-const 1)))
(assert-event
 (equal (f7-poly-mul (f7-const 0) (f7-const 5)) nil))
(assert-event
 (equal (f7-poly-mul '(1 2 3) (f7-const 4))
        (f7-poly-scale 4 '(1 2 3))))
