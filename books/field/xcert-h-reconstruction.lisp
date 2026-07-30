(in-package "GFIELD")
(include-book "xcert-algebra")
(include-book "sorting/perm" :dir :system)

(local (defun field-sum-list (xs)
 (if (consp xs) (field-add (car xs) (field-sum-list (cdr xs))) (field-zero))))

(local (defthm field-sum-list-nil
 (equal (field-sum-list nil) (field-zero))
 :hints (("Goal" :expand ((field-sum-list nil))))))
(local (defthm field-add-swap-local
 (equal (field-add x (field-add y z)) (field-add y (field-add x z)))
 :hints (("Goal" :use ((:instance field-add-associative (x x)(y y)(z z)) (:instance field-add-associative (x y)(y x)(z z)) (:instance field-add-commutative (x x)(y y))) :in-theory (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))
(local (defthm field-sum-list-of-rm
 (implies (acl2::memb a xs)
  (equal (field-sum-list xs) (field-add a (field-sum-list (acl2::rm a xs)))))
 :hints (("Goal" :induct (acl2::rm a xs) :in-theory (enable field-add-swap-local)))))
(local (defthm field-sum-list-perm
 (implies (acl2::perm xs ys) (equal (field-sum-list xs) (field-sum-list ys)))
 :rule-classes nil
 :hints (("Goal" :induct (acl2::perm xs ys))
         ("Subgoal *1/1" :use ((:instance field-sum-list-of-rm (a (car xs)) (xs ys)))
          :in-theory (disable field-sum-list-of-rm)))))
(local (defthm field-add-inverse-tail
 (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
 :hints (("Goal" :use ((:instance field-add-associative (x x) (y (field-neg x)) (z y)))
          :in-theory (union-theories (theory 'minimal-theory) '(field-add-inverse-right field-add-zero-left field-fix-idempotent))))))

(local (defthm raw-sum-is-normal-sum
 (equal (field-sum-list (list
  (field-mul p yb)
  (field-mul p ya)
  (field-neg (field-mul xb xb))
  (field-neg (field-mul xb xa))
  (field-neg (field-mul xa xa))
  (field-neg a)
  (field-neg (field-mul q yc))
  (field-neg (field-mul q yab))
  (field-mul xc xc)
  (field-mul xc xab)
  (field-mul xab xab)
  a
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul q (field-mul p xa))
  (field-mul q yb)
  (field-neg (field-mul q ya))
  (field-neg (field-mul p (field-mul r xc)))
  (field-mul p (field-mul r xb))
  (field-mul p yc)
  (field-neg (field-mul p yb))
  (field-neg (field-mul q (field-mul r xc)))
  (field-mul q (field-mul r xb))
  (field-mul q yc)
  (field-neg (field-mul q yb))
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul q xab)))
  (field-neg (field-mul p yc))
  (field-mul p yab)
  (field-mul p (field-mul p xab))
  (field-neg (field-mul xab xb))
  (field-neg (field-mul xa xab))
  (field-neg (field-mul xab xab))
  (field-mul p (field-mul p xc))
  (field-neg (field-mul xb xc))
  (field-neg (field-mul xa xc))
  (field-neg (field-mul xab xc))
  (field-neg (field-mul p (field-mul p xa)))
  (field-mul xa xb)
  (field-mul xa xa)
  (field-mul xa xab)
  (field-neg (field-mul p (field-mul p xb)))
  (field-mul xb xb)
  (field-mul xa xb)
  (field-mul xab xb)
  (field-mul q yab)
  (field-mul q ya)
  (field-neg (field-mul q (field-mul p xa)))
  (field-mul q (field-mul p xab))
  (field-neg (field-mul p yab))
  (field-neg (field-mul p ya))
  (field-mul p (field-mul p xa))
  (field-neg (field-mul p (field-mul p xab)))))
        (field-sum-list (list
  (field-mul p yb)
  (field-neg (field-mul p yb))
  (field-mul p ya)
  (field-neg (field-mul p ya))
  (field-mul xb xb)
  (field-neg (field-mul xb xb))
  (field-mul xb xa)
  (field-neg (field-mul xb xa))
  (field-mul xa xa)
  (field-neg (field-mul xa xa))
  a
  (field-neg a)
  (field-mul q yc)
  (field-neg (field-mul q yc))
  (field-mul q yab)
  (field-neg (field-mul q yab))
  (field-mul xc xab)
  (field-neg (field-mul xc xab))
  (field-mul xab xab)
  (field-neg (field-mul xab xab))
  (field-mul q (field-mul p xa))
  (field-neg (field-mul q (field-mul p xa)))
  (field-mul q yb)
  (field-neg (field-mul q yb))
  (field-mul q ya)
  (field-neg (field-mul q ya))
  (field-mul p yc)
  (field-neg (field-mul p yc))
  (field-mul q (field-mul p xab))
  (field-neg (field-mul q (field-mul p xab)))
  (field-mul p yab)
  (field-neg (field-mul p yab))
  (field-mul xa xab)
  (field-neg (field-mul xa xab))
  (field-mul p (field-mul p xa))
  (field-neg (field-mul p (field-mul p xa)))
  (field-mul xb xab)
  (field-neg (field-mul xb xab))
  (field-mul xab (field-mul p p))
  (field-neg (field-mul xab (field-mul p p)))
  (field-mul xc (field-mul p p))
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul r xc)))
  (field-neg (field-mul q (field-mul r xc)))
  (field-neg (field-mul xb (field-mul p p)))
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul p (field-mul r xb))
  (field-mul q (field-mul r xb))
  (field-neg (field-mul xc xa))
  (field-mul xc xc)
  (field-mul xa xb)
  (field-neg (field-mul xc xb)))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable field-sum-list field-add-associative field-add-commutative)))))

(local (defthm normal-sum-is-target-sum
 (equal (field-sum-list (list
  (field-mul p yb)
  (field-neg (field-mul p yb))
  (field-mul p ya)
  (field-neg (field-mul p ya))
  (field-mul xb xb)
  (field-neg (field-mul xb xb))
  (field-mul xb xa)
  (field-neg (field-mul xb xa))
  (field-mul xa xa)
  (field-neg (field-mul xa xa))
  a
  (field-neg a)
  (field-mul q yc)
  (field-neg (field-mul q yc))
  (field-mul q yab)
  (field-neg (field-mul q yab))
  (field-mul xc xab)
  (field-neg (field-mul xc xab))
  (field-mul xab xab)
  (field-neg (field-mul xab xab))
  (field-mul q (field-mul p xa))
  (field-neg (field-mul q (field-mul p xa)))
  (field-mul q yb)
  (field-neg (field-mul q yb))
  (field-mul q ya)
  (field-neg (field-mul q ya))
  (field-mul p yc)
  (field-neg (field-mul p yc))
  (field-mul q (field-mul p xab))
  (field-neg (field-mul q (field-mul p xab)))
  (field-mul p yab)
  (field-neg (field-mul p yab))
  (field-mul xa xab)
  (field-neg (field-mul xa xab))
  (field-mul p (field-mul p xa))
  (field-neg (field-mul p (field-mul p xa)))
  (field-mul xb xab)
  (field-neg (field-mul xb xab))
  (field-mul xab (field-mul p p))
  (field-neg (field-mul xab (field-mul p p)))
  (field-mul xc (field-mul p p))
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul r xc)))
  (field-neg (field-mul q (field-mul r xc)))
  (field-neg (field-mul xb (field-mul p p)))
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul p (field-mul r xb))
  (field-mul q (field-mul r xb))
  (field-neg (field-mul xc xa))
  (field-mul xc xc)
  (field-mul xa xb)
  (field-neg (field-mul xc xb))))
        (field-sum-list (list
  (field-mul xc (field-mul p p))
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul r xc)))
  (field-neg (field-mul q (field-mul r xc)))
  (field-neg (field-mul xb (field-mul p p)))
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul p (field-mul r xb))
  (field-mul q (field-mul r xb))
  (field-neg (field-mul xc xa))
  (field-mul xc xc)
  (field-mul xa xb)
  (field-neg (field-mul xc xb)))))
 :rule-classes nil :hints (("Goal" :in-theory (e/d (field-sum-list field-sum-list-nil field-add-inverse-tail field-fix-idempotent field-fix-of-zero) (field-add-commutative field-add-associative field-add-swap-local)))))
)

(local
 (defthm field-mul-of-neg-right-local
  (equal (field-mul x (field-neg y)) (field-neg (field-mul x y)))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                         (x (field-mul x y)) (y (field-mul x (field-neg y))))
                        (:instance field-mul-left-distributive
                         (x x) (y y) (z (field-neg y))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(field-add-inverse-right field-mul-zero-right field-fix-of-mul))))))
(local
 (defthm field-mul-of-neg-left-local
  (equal (field-mul (field-neg x) y) (field-neg (field-mul x y)))
  :hints (("Goal" :use ((:instance field-mul-commutative (x (field-neg x)) (y y))
                        (:instance field-mul-commutative (x y) (y x))
                        (:instance field-mul-of-neg-right-local (x y) (y x)))
           :in-theory (theory 'minimal-theory)))))
(local
 (defthm field-add-inverse-shuffle-local
  (equal (field-add x (field-add y (field-add (field-neg x) z)))
         (field-add y (field-fix z)))
  :hints (("Goal" :use ((:instance field-add-swap-local
                         (x x) (y y) (z (field-add (field-neg x) z)))
                        (:instance field-add-inverse-tail (x x) (y z)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(field-add-swap-local field-add-inverse-tail field-add-fix-right))))))
(local
 (defthm field-neg-of-add-local
  (equal (field-neg (field-add x y))
         (field-add (field-neg x) (field-neg y)))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                         (x (field-add x y))
                         (y (field-add (field-neg x) (field-neg y)))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(field-add-associative field-add-inverse-shuffle-local
                          field-add-inverse-right field-add-zero-left
                          field-fix-of-add field-fix-of-neg))))))

(local (defthm field-fix-of-field-sum-list-local
 (equal (field-fix (field-sum-list xs)) (field-sum-list xs))
 :hints (("Goal" :induct (field-sum-list xs) :in-theory (enable field-sum-list field-fix-of-add field-fix-of-zero)))))
(local (defthm field-sum-list-append-local
 (equal (field-sum-list (append xs ys)) (field-add (field-sum-list xs) (field-sum-list ys)))
 :hints (("Goal" :induct (append xs ys) :in-theory (enable field-sum-list field-add-associative field-fix-of-add field-fix-of-zero field-fix-of-field-sum-list-local)))))
(local (defthm residual-segment-1-local
 (equal (field-sub (field-mul p (field-add yb ya)) (field-add (field-mul xb xb) (field-add (field-mul xb xa) (field-add (field-mul xa xa) a)))) (field-sum-list (list
  (field-mul p yb)
  (field-mul p ya)
  (field-neg (field-mul xb xb))
  (field-neg (field-mul xb xa))
  (field-neg (field-mul xa xa))
  (field-neg a)))) :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (enable field-sum-list field-sum-list-nil field-sub field-neg-of-add-local field-neg-of-neg field-mul-left-distributive field-mul-right-distributive field-mul-of-neg-left-local field-mul-of-neg-right-local field-mul-associative field-mul-commutative field-add-associative field-add-commutative field-add-zero-left field-add-zero-right field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero field-add-fix-left field-add-fix-right field-mul-fix-left field-mul-fix-right)))))
(local (defthm residual-segment-2-local
 (equal (field-neg (field-sub (field-mul q (field-add yc yab)) (field-add (field-mul xc xc) (field-add (field-mul xc xab) (field-add (field-mul xab xab) a))))) (field-sum-list (list
  (field-neg (field-mul q yc))
  (field-neg (field-mul q yab))
  (field-mul xc xc)
  (field-mul xc xab)
  (field-mul xab xab)
  a))) :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (enable field-sum-list field-sum-list-nil field-sub field-neg-of-add-local field-neg-of-neg field-mul-left-distributive field-mul-right-distributive field-mul-of-neg-left-local field-mul-of-neg-right-local field-mul-associative field-mul-commutative field-add-associative field-add-commutative field-add-zero-left field-add-zero-right field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero field-add-fix-left field-add-fix-right field-mul-fix-left field-mul-fix-right)))))
(local (defthm residual-segment-3-local
 (equal (field-neg (field-mul q (field-sub (field-mul p (field-sub xb xa)) (field-sub yb ya)))) (field-sum-list (list
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul q (field-mul p xa))
  (field-mul q yb)
  (field-neg (field-mul q ya))))) :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (enable field-sum-list field-sum-list-nil field-sub field-neg-of-add-local field-neg-of-neg field-mul-left-distributive field-mul-right-distributive field-mul-of-neg-left-local field-mul-of-neg-right-local field-mul-associative field-mul-commutative field-add-associative field-add-commutative field-add-zero-left field-add-zero-right field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero field-add-fix-left field-add-fix-right field-mul-fix-left field-mul-fix-right)))))
(local (defthm residual-segment-4-local
 (equal (field-neg (field-mul (field-add p q) (field-sub (field-mul r (field-sub xc xb)) (field-sub yc yb)))) (field-sum-list (list
  (field-neg (field-mul p (field-mul r xc)))
  (field-mul p (field-mul r xb))
  (field-mul p yc)
  (field-neg (field-mul p yb))
  (field-neg (field-mul q (field-mul r xc)))
  (field-mul q (field-mul r xb))
  (field-mul q yc)
  (field-neg (field-mul q yb))))) :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (enable field-sum-list field-sum-list-nil field-sub field-neg-of-add-local field-neg-of-neg field-mul-left-distributive field-mul-right-distributive field-mul-of-neg-left-local field-mul-of-neg-right-local field-mul-associative field-mul-commutative field-add-associative field-add-commutative field-add-zero-left field-add-zero-right field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero field-add-fix-left field-add-fix-right field-mul-fix-left field-mul-fix-right)))))
(local (defthm residual-segment-5-local
 (equal (field-mul p (field-sub (field-mul q (field-sub xc xab)) (field-sub yc yab))) (field-sum-list (list
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul q xab)))
  (field-neg (field-mul p yc))
  (field-mul p yab)))) :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (enable field-sum-list field-sum-list-nil field-sub field-neg-of-add-local field-neg-of-neg field-mul-left-distributive field-mul-right-distributive field-mul-of-neg-left-local field-mul-of-neg-right-local field-mul-associative field-mul-commutative field-add-associative field-add-commutative field-add-zero-left field-add-zero-right field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero field-add-fix-left field-add-fix-right field-mul-fix-left field-mul-fix-right)))))
(local (defthm residual-segment-6-local
 (equal (field-mul (field-sub (field-sub (field-add xa xb) xc) xab) (field-sub (field-add (field-add xab xa) xb) (field-mul p p))) (field-sum-list (list
  (field-mul p (field-mul p xab))
  (field-neg (field-mul xab xb))
  (field-neg (field-mul xa xab))
  (field-neg (field-mul xab xab))
  (field-mul p (field-mul p xc))
  (field-neg (field-mul xb xc))
  (field-neg (field-mul xa xc))
  (field-neg (field-mul xab xc))
  (field-neg (field-mul p (field-mul p xa)))
  (field-mul xa xb)
  (field-mul xa xa)
  (field-mul xa xab)
  (field-neg (field-mul p (field-mul p xb)))
  (field-mul xb xb)
  (field-mul xa xb)
  (field-mul xab xb)))) :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (e/d (field-sum-list field-sum-list-nil field-sub field-neg-of-add-local field-neg-of-neg field-mul-left-distributive field-mul-right-distributive field-mul-of-neg-left-local field-mul-of-neg-right-local field-mul-associative field-mul-commutative field-add-associative field-add-commutative field-add-zero-left field-add-zero-right field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero field-add-fix-left field-add-fix-right field-mul-fix-left field-mul-fix-right) (field-add-inverse-left field-add-inverse-right field-add-inverse-tail field-add-inverse-shuffle-local field-add-swap-local))))))
(local (defthm residual-segment-7-local
 (equal (field-mul (field-sub q p) (field-sub (field-add yab ya) (field-mul p (field-sub xa xab)))) (field-sum-list (list
  (field-mul q yab)
  (field-mul q ya)
  (field-neg (field-mul q (field-mul p xa)))
  (field-mul q (field-mul p xab))
  (field-neg (field-mul p yab))
  (field-neg (field-mul p ya))
  (field-mul p (field-mul p xa))
  (field-neg (field-mul p (field-mul p xab)))))) :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (enable field-sum-list field-sum-list-nil field-sub field-neg-of-add-local field-neg-of-neg field-mul-left-distributive field-mul-right-distributive field-mul-of-neg-left-local field-mul-of-neg-right-local field-mul-associative field-mul-commutative field-add-associative field-add-commutative field-add-zero-left field-add-zero-right field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero field-add-fix-left field-add-fix-right field-mul-fix-left field-mul-fix-right)))))
(local (defthm raw-sum-partition-local
 (equal (field-sum-list (list
  (field-mul p yb)
  (field-mul p ya)
  (field-neg (field-mul xb xb))
  (field-neg (field-mul xb xa))
  (field-neg (field-mul xa xa))
  (field-neg a)
  (field-neg (field-mul q yc))
  (field-neg (field-mul q yab))
  (field-mul xc xc)
  (field-mul xc xab)
  (field-mul xab xab)
  a
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul q (field-mul p xa))
  (field-mul q yb)
  (field-neg (field-mul q ya))
  (field-neg (field-mul p (field-mul r xc)))
  (field-mul p (field-mul r xb))
  (field-mul p yc)
  (field-neg (field-mul p yb))
  (field-neg (field-mul q (field-mul r xc)))
  (field-mul q (field-mul r xb))
  (field-mul q yc)
  (field-neg (field-mul q yb))
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul q xab)))
  (field-neg (field-mul p yc))
  (field-mul p yab)
  (field-mul p (field-mul p xab))
  (field-neg (field-mul xab xb))
  (field-neg (field-mul xa xab))
  (field-neg (field-mul xab xab))
  (field-mul p (field-mul p xc))
  (field-neg (field-mul xb xc))
  (field-neg (field-mul xa xc))
  (field-neg (field-mul xab xc))
  (field-neg (field-mul p (field-mul p xa)))
  (field-mul xa xb)
  (field-mul xa xa)
  (field-mul xa xab)
  (field-neg (field-mul p (field-mul p xb)))
  (field-mul xb xb)
  (field-mul xa xb)
  (field-mul xab xb)
  (field-mul q yab)
  (field-mul q ya)
  (field-neg (field-mul q (field-mul p xa)))
  (field-mul q (field-mul p xab))
  (field-neg (field-mul p yab))
  (field-neg (field-mul p ya))
  (field-mul p (field-mul p xa))
  (field-neg (field-mul p (field-mul p xab))))) (field-add (field-sum-list (list
  (field-mul p yb)
  (field-mul p ya)
  (field-neg (field-mul xb xb))
  (field-neg (field-mul xb xa))
  (field-neg (field-mul xa xa))
  (field-neg a))) (field-add (field-sum-list (list
  (field-neg (field-mul q yc))
  (field-neg (field-mul q yab))
  (field-mul xc xc)
  (field-mul xc xab)
  (field-mul xab xab)
  a)) (field-add (field-sum-list (list
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul q (field-mul p xa))
  (field-mul q yb)
  (field-neg (field-mul q ya)))) (field-add (field-sum-list (list
  (field-neg (field-mul p (field-mul r xc)))
  (field-mul p (field-mul r xb))
  (field-mul p yc)
  (field-neg (field-mul p yb))
  (field-neg (field-mul q (field-mul r xc)))
  (field-mul q (field-mul r xb))
  (field-mul q yc)
  (field-neg (field-mul q yb)))) (field-add (field-sum-list (list
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul q xab)))
  (field-neg (field-mul p yc))
  (field-mul p yab))) (field-add (field-sum-list (list
  (field-mul p (field-mul p xab))
  (field-neg (field-mul xab xb))
  (field-neg (field-mul xa xab))
  (field-neg (field-mul xab xab))
  (field-mul p (field-mul p xc))
  (field-neg (field-mul xb xc))
  (field-neg (field-mul xa xc))
  (field-neg (field-mul xab xc))
  (field-neg (field-mul p (field-mul p xa)))
  (field-mul xa xb)
  (field-mul xa xa)
  (field-mul xa xab)
  (field-neg (field-mul p (field-mul p xb)))
  (field-mul xb xb)
  (field-mul xa xb)
  (field-mul xab xb))) (field-sum-list (list
  (field-mul q yab)
  (field-mul q ya)
  (field-neg (field-mul q (field-mul p xa)))
  (field-mul q (field-mul p xab))
  (field-neg (field-mul p yab))
  (field-neg (field-mul p ya))
  (field-mul p (field-mul p xa))
  (field-neg (field-mul p (field-mul p xab)))))))))))) :rule-classes nil
 :hints (("Goal" :in-theory (e/d (field-add-associative field-sum-list field-sum-list-nil field-add-zero-left field-add-zero-right field-fix-of-field-sum-list-local field-add-fix-left field-add-fix-right) (field-add-commutative field-add-swap-local field-add-inverse-left field-add-inverse-right field-add-inverse-tail field-add-inverse-shuffle-local))))))
(local (defthm seven-residual-expression-to-raw-sum-local
 (equal (field-add
 (field-sub
  (field-sub
   (field-sub
    (field-mul p (field-add yb ya))
    (field-add (field-mul xb xb)
     (field-add (field-mul xb xa) (field-add (field-mul xa xa) a))))
   (field-sub
    (field-mul q (field-add yc yab))
    (field-add (field-mul xc xc)
     (field-add (field-mul xc xab) (field-add (field-mul xab xab) a)))))
  (field-mul q
   (field-sub (field-mul p (field-sub xb xa)) (field-sub yb ya))))
 (field-add
  (field-neg
   (field-mul (field-add p q)
    (field-sub (field-mul r (field-sub xc xb)) (field-sub yc yb))))
  (field-add
   (field-mul p
    (field-sub (field-mul q (field-sub xc xab)) (field-sub yc yab)))
   (field-add
    (field-mul
     (field-sub (field-sub (field-add xa xb) xc) xab)
     (field-sub (field-add (field-add xab xa) xb) (field-mul p p)))
    (field-mul (field-sub q p)
     (field-sub (field-add yab ya) (field-mul p (field-sub xa xab)))))))) (field-sum-list (list
  (field-mul p yb)
  (field-mul p ya)
  (field-neg (field-mul xb xb))
  (field-neg (field-mul xb xa))
  (field-neg (field-mul xa xa))
  (field-neg a)
  (field-neg (field-mul q yc))
  (field-neg (field-mul q yab))
  (field-mul xc xc)
  (field-mul xc xab)
  (field-mul xab xab)
  a
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul q (field-mul p xa))
  (field-mul q yb)
  (field-neg (field-mul q ya))
  (field-neg (field-mul p (field-mul r xc)))
  (field-mul p (field-mul r xb))
  (field-mul p yc)
  (field-neg (field-mul p yb))
  (field-neg (field-mul q (field-mul r xc)))
  (field-mul q (field-mul r xb))
  (field-mul q yc)
  (field-neg (field-mul q yb))
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul q xab)))
  (field-neg (field-mul p yc))
  (field-mul p yab)
  (field-mul p (field-mul p xab))
  (field-neg (field-mul xab xb))
  (field-neg (field-mul xa xab))
  (field-neg (field-mul xab xab))
  (field-mul p (field-mul p xc))
  (field-neg (field-mul xb xc))
  (field-neg (field-mul xa xc))
  (field-neg (field-mul xab xc))
  (field-neg (field-mul p (field-mul p xa)))
  (field-mul xa xb)
  (field-mul xa xa)
  (field-mul xa xab)
  (field-neg (field-mul p (field-mul p xb)))
  (field-mul xb xb)
  (field-mul xa xb)
  (field-mul xab xb)
  (field-mul q yab)
  (field-mul q ya)
  (field-neg (field-mul q (field-mul p xa)))
  (field-mul q (field-mul p xab))
  (field-neg (field-mul p yab))
  (field-neg (field-mul p ya))
  (field-mul p (field-mul p xa))
  (field-neg (field-mul p (field-mul p xab))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance raw-sum-partition-local) (:instance residual-segment-1-local) (:instance residual-segment-2-local) (:instance residual-segment-3-local) (:instance residual-segment-4-local) (:instance residual-segment-5-local) (:instance residual-segment-6-local) (:instance residual-segment-7-local)) :in-theory (e/d (field-add-associative field-fix-of-field-sum-list-local) (field-add-commutative field-add-swap-local field-add-inverse-left field-add-inverse-right field-add-inverse-tail field-add-inverse-shuffle-local))))))

(local (defthm target-sum-to-factorized-expression-local
 (equal (field-sum-list (list
  (field-mul xc (field-mul p p))
  (field-mul p (field-mul q xc))
  (field-neg (field-mul p (field-mul r xc)))
  (field-neg (field-mul q (field-mul r xc)))
  (field-neg (field-mul xb (field-mul p p)))
  (field-neg (field-mul q (field-mul p xb)))
  (field-mul p (field-mul r xb))
  (field-mul q (field-mul r xb))
  (field-neg (field-mul xc xa))
  (field-mul xc xc)
  (field-mul xa xb)
  (field-neg (field-mul xc xb))))
  (field-mul (field-sub xc xb)
   (field-sub (field-mul (field-sub p r) (field-add p q))
              (field-sub xa xc))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (enable field-sub field-neg-of-add-local field-neg-of-neg
 field-mul-left-distributive field-mul-right-distributive
 field-mul-of-neg-left-local field-mul-of-neg-right-local
 field-mul-associative field-mul-commutative
 field-add-associative field-add-commutative field-add-swap-local
 field-add-inverse-left field-add-inverse-right field-add-zero-left field-add-zero-right
 field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero
 field-add-fix-left field-add-fix-right field-mul-fix-left field-mul-fix-right
 field-sum-list field-sum-list-nil)))))

(local
 (defthm xcert-h-residual-identity-local
  (equal
   (field-mul
    (field-sub xc xb)
    (field-sub
     (field-mul (field-sub p r) (field-add p q))
     (field-sub xa xc)))
   (field-add
    (field-sub
     (field-sub
      (field-sub
       (field-mul p (field-add yb ya))
       (field-add (field-mul xb xb)
        (field-add (field-mul xb xa) (field-add (field-mul xa xa) a))))
      (field-sub
       (field-mul q (field-add yc yab))
       (field-add (field-mul xc xc)
        (field-add (field-mul xc xab) (field-add (field-mul xab xab) a)))))
     (field-mul q
      (field-sub (field-mul p (field-sub xb xa)) (field-sub yb ya))))
    (field-add
     (field-neg
      (field-mul (field-add p q)
       (field-sub (field-mul r (field-sub xc xb)) (field-sub yc yb))))
     (field-add
      (field-mul p
       (field-sub (field-mul q (field-sub xc xab)) (field-sub yc yab)))
      (field-add
       (field-mul
        (field-sub (field-sub (field-add xa xb) xc) xab)
        (field-sub (field-add (field-add xab xa) xb) (field-mul p p)))
       (field-mul (field-sub q p)
        (field-sub (field-add yab ya)
                   (field-mul p (field-sub xa xab)))))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance seven-residual-expression-to-raw-sum-local)
                         (:instance raw-sum-is-normal-sum)
                         (:instance normal-sum-is-target-sum)
                         (:instance target-sum-to-factorized-expression-local))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm xcert-h-zero-product-local
  (implies
   (and
    (equal (field-mul p (field-add yb ya))
     (field-add (field-mul xb xb)
      (field-add (field-mul xb xa) (field-add (field-mul xa xa) a))))
    (equal (field-mul q (field-add yc yab))
     (field-add (field-mul xc xc)
      (field-add (field-mul xc xab) (field-add (field-mul xab xab) a))))
    (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-add (field-add xab xa) xb) (field-mul p p))
    (equal (field-add yab ya) (field-mul p (field-sub xa xab))))
   (equal
    (field-mul
     (field-sub xc xb)
     (field-sub
      (field-mul (field-sub p r) (field-add p q))
      (field-sub xa xc)))
    (field-zero)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance xcert-h-residual-identity-local))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-sub-self field-mul-zero-left field-mul-zero-right
              field-neg-of-zero field-add-zero-left field-add-zero-right
              field-fix-of-zero))))))

(local
 (defthm xcert-h-cancel-local
  (implies
   (and
    (not (equal (field-sub xc xb) (field-zero)))
    (equal
     (field-mul (field-sub xc xb)
      (field-sub
       (field-mul (field-sub p r) (field-add p q))
       (field-sub xa xc)))
     (field-zero)))
   (equal
    (field-sub
     (field-mul (field-sub p r) (field-add p q))
     (field-sub xa xc))
    (field-zero)))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance field-mul-left-cancel-forward
          (x (field-sub xc xb))
          (y (field-sub
              (field-mul (field-sub p r) (field-add p q))
              (field-sub xa xc)))
          (z (field-zero))))
   :in-theory
   (union-theories (theory 'minimal-theory)
    '(field-sub field-fix-of-add field-fix-of-neg field-fix-of-zero
      field-mul-zero-right))))))

(defthm xcert-h-scalar-reconstruction
 (implies
  (and
   (equal (field-mul p (field-add yb ya))
    (field-add (field-mul xb xb)
     (field-add (field-mul xb xa) (field-add (field-mul xa xa) a))))
   (equal (field-mul q (field-add yc yab))
    (field-add (field-mul xc xc)
     (field-add (field-mul xc xab) (field-add (field-mul xab xab) a))))
   (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
   (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
   (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
   (equal (field-add (field-add xab xa) xb) (field-mul p p))
   (equal (field-add yab ya) (field-mul p (field-sub xa xab)))
   (not (equal (field-sub xc xb) (field-zero))))
  (equal
   (field-mul (field-sub p r) (field-add p q))
   (field-sub xa xc)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance xcert-h-zero-product-local)
        (:instance xcert-h-cancel-local)
        (:instance field-sub-equal-zero-implies-fixed-equal
         (first (field-mul (field-sub p r) (field-add p q)))
         (second (field-sub xa xc))))
  :in-theory
  (union-theories (theory 'minimal-theory)
   '(field-sub field-fix-of-add field-fix-of-mul field-fix-of-neg)))))
