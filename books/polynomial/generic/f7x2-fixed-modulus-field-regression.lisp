(in-package "GPOLY")
(include-book "f7x2-field")

; These are consequences proved after the GFIELD encapsulate, not field axioms.
; Their functional instances validate the complete public F7X2 constraint set.
(defthm f7x2-field-add-left-cancel-regression
  (equal (equal (f7x2-add x y) (f7x2-add x z))
         (equal (f7x2-fix y) (f7x2-fix z)))
  :rule-classes nil
  :hints
  (("Goal"
    :by (:functional-instance
       gfield::field-add-left-cancel
       (gfield::field-element-p f7x2-element-p)
       (gfield::field-fix f7x2-fix)
       (gfield::field-zero f7x2-zero)
       (gfield::field-one f7x2-one)
       (gfield::field-add f7x2-add)
       (gfield::field-mul f7x2-mul)
       (gfield::field-neg f7x2-neg)
       (gfield::field-inv f7x2-inv))
    :do-not '(preprocess)
    :in-theory (union-theories '(f7x2-mul-of-fix-left f7x2-mul-of-fix-right
                      f7x2-add-of-fix-left f7x2-add-of-fix-right
                      f7x2-field-add-of-fixes f7x2-field-mul-of-fixes
                      f7x2-neg-of-fix f7x2-inv-of-f7x2-fix
                      f7x2-field-booleanp-of-element-p
                      f7x2-element-p-of-f7x2-fix f7x2-fix-idempotent
                      f7x2-element-p-of-zero f7x2-element-p-of-one
                      f7x2-zero-not-equal-f7x2-one f7x2-fix-of-zero f7x2-fix-of-one
                      f7x2-element-p-of-f7x2-add f7x2-element-p-of-f7x2-mul
                      f7x2-element-p-of-f7x2-neg f7x2-element-p-of-f7x2-inv
                      f7x2-fix-of-f7x2-add f7x2-fix-of-f7x2-mul
                      f7x2-fix-of-f7x2-neg f7x2-fix-of-f7x2-inv
                      f7x2-add-inverse-left f7x2-add-zero-left
                      f7x2-mul-left-distributive f7x2-mul-one-left f7x2-mul-associative
                      f7x2-inv-of-f7x2-zero f7x2-field-mul-inverse-left) (theory 'minimal-theory)))
   ("Subgoal 7"
    :use ((:instance f7x2-add-commutative
                     (first gfield::x) (second gfield::y)))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 6"
    :use ((:instance f7x2-mul-commutative
                     (first gfield::x) (second gfield::y)))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 5"
    :use ((:instance f7x2-add-associative
                     (first gfield::x) (second gfield::y) (third gfield::z)))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 3"
    :use ((:instance f7x2-fix-when-f7x2-element-p (x gfield::x)))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 2"
    :use ((:instance f7x2-mul-fixed-congruence
                     (x1 gfield::x1) (x2 gfield::x2)
                     (y1 gfield::y1) (y2 gfield::y2)))
    :in-theory (theory 'minimal-theory))
   ("Subgoal 1"
    :use ((:instance f7x2-add-fixed-congruence
                     (x1 gfield::x1) (x2 gfield::x2)
                     (y1 gfield::y1) (y2 gfield::y2)))
    :in-theory (theory 'minimal-theory))))

(defthm f7x2-field-div-mul-denominator-regression
  (implies (not (equal (f7x2-fix denominator) (f7x2-zero)))
           (equal (f7x2-mul (f7x2-div numerator denominator)
                            denominator)
                  (f7x2-fix numerator)))
  :rule-classes nil
  :hints
  (("Goal"
    :by (:functional-instance
       gfield::field-div-mul-denominator
       (gfield::field-element-p f7x2-element-p)
       (gfield::field-fix f7x2-fix)
       (gfield::field-zero f7x2-zero)
       (gfield::field-one f7x2-one)
       (gfield::field-add f7x2-add)
       (gfield::field-mul f7x2-mul)
       (gfield::field-neg f7x2-neg)
       (gfield::field-inv f7x2-inv)
       (gfield::field-div f7x2-div))
    :do-not '(preprocess)
    :in-theory (union-theories '(f7x2-div f7x2-mul-of-fix-left f7x2-mul-of-fix-right
                      f7x2-add-of-fix-left f7x2-add-of-fix-right
                      f7x2-field-add-of-fixes f7x2-field-mul-of-fixes
                      f7x2-neg-of-fix f7x2-inv-of-f7x2-fix
                      booleanp-of-f7x2-element-p
                      f7x2-element-p-of-f7x2-fix f7x2-fix-idempotent
                      f7x2-element-p-of-zero f7x2-element-p-of-one
                      f7x2-zero-not-equal-f7x2-one f7x2-fix-of-zero f7x2-fix-of-one
                      f7x2-element-p-of-f7x2-add f7x2-element-p-of-f7x2-mul
                      f7x2-element-p-of-f7x2-neg f7x2-element-p-of-f7x2-inv
                      f7x2-fix-of-f7x2-add f7x2-fix-of-f7x2-mul
                      f7x2-fix-of-f7x2-neg f7x2-fix-of-f7x2-inv
                      f7x2-add-inverse-left f7x2-add-zero-left
                      f7x2-mul-left-distributive f7x2-mul-one-left f7x2-mul-associative
                      f7x2-inv-of-f7x2-zero f7x2-field-mul-inverse-left) (theory 'minimal-theory)))))
