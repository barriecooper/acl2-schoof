(in-package "GPOLY")
(include-book "pfield-instance")
(include-book "quadratic-irreducibility")

; These predicates are the concrete logical boundary needed to state an F7
; irreducibility certificate.  They are quantifiers, not executable searches.
(defun f7-poly-unit-p (poly)
  (equal (f7-poly-degree poly) 0))

(defun-sk f7-poly-reducible-p (poly)
  (exists (left right)
          (and (equal (f7-poly-mul left right) (f7-normalize poly))
               (not (f7-poly-unit-p left))
               (not (f7-poly-unit-p right)))))

(defun f7-poly-irreducible-p (poly)
  (and (< 0 (f7-poly-degree poly))
       (not (f7-poly-reducible-p poly))))

(defun-sk f7-poly-has-root-p (poly)
  (exists (root)
          (and (gfield::f7-element-p root)
               (equal (f7-eval poly root) (gfield::f7-zero)))))

(local
 (defthm f7-add-fixed-congruence-for-quadratic-instantiation
   (implies (and (equal (gfield::f7-fix x1) (gfield::f7-fix x2))
                 (equal (gfield::f7-fix y1) (gfield::f7-fix y2)))
            (equal (gfield::f7-add x1 y1) (gfield::f7-add x2 y2)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (gfield::f7-add)
                                     (gfield::f7-fix))))))
(local
 (defthm f7-mul-fixed-congruence-for-quadratic-instantiation
   (implies (and (equal (gfield::f7-fix x1) (gfield::f7-fix x2))
                 (equal (gfield::f7-fix y1) (gfield::f7-fix y2)))
            (equal (gfield::f7-mul x1 y1) (gfield::f7-mul x2 y2)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (gfield::f7-mul)
                                     (gfield::f7-fix))))))

; Restate only the generated two-witness constraint that the generic
; quadratic theorem's functional instance needs.
(defthm f7-poly-reducible-p-full-witness-constraint-for-instantiation
  (implies (and (equal (f7-poly-mul left right) (f7-normalize poly))
                (not (f7-poly-unit-p left))
                (not (f7-poly-unit-p right)))
           (and (equal
                 (f7-poly-mul
                  (mv-nth 0 (f7-poly-reducible-p-witness poly))
                  (mv-nth 1 (f7-poly-reducible-p-witness poly)))
                 (f7-normalize poly))
                (not (f7-poly-unit-p
                      (mv-nth 0 (f7-poly-reducible-p-witness poly))))
                (not (f7-poly-unit-p
                      (mv-nth 1 (f7-poly-reducible-p-witness poly))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-poly-reducible-p-suff
                            (poly poly) (left left) (right right))
                 (:instance f7-poly-reducible-p (poly poly)))
           :in-theory (disable f7-poly-reducible-p
                               f7-poly-reducible-p-suff))))

(defthm f7-poly-has-root-p-full-witness-constraint-for-instantiation
  (implies (and (gfield::f7-element-p root)
                (equal (f7-eval poly root) (gfield::f7-zero)))
           (and (gfield::f7-element-p
                 (f7-poly-has-root-p-witness poly))
                (equal (f7-eval poly (f7-poly-has-root-p-witness poly))
                       (gfield::f7-zero))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-poly-has-root-p-suff
                            (poly poly) (root root))
                 (:instance f7-poly-has-root-p (poly poly)))
           :in-theory (disable f7-poly-has-root-p
                               f7-poly-has-root-p-suff))))

(defthm f7-element-exhaustion
  (implies (gfield::f7-element-p x)
           (or (equal x 0) (equal x 1) (equal x 2) (equal x 3)
               (equal x 4) (equal x 5) (equal x 6)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable gfield::f7-element-p pfield::fep))))

(defthm f7-x-squared-plus-one-at-0
  (equal (f7-eval '(1 0 1) 0) 1))
(defthm f7-x-squared-plus-one-at-1
  (equal (f7-eval '(1 0 1) 1) 2))
(defthm f7-x-squared-plus-one-at-2
  (equal (f7-eval '(1 0 1) 2) 5))
(defthm f7-x-squared-plus-one-at-3
  (equal (f7-eval '(1 0 1) 3) 3))
(defthm f7-x-squared-plus-one-at-4
  (equal (f7-eval '(1 0 1) 4) 3))
(defthm f7-x-squared-plus-one-at-5
  (equal (f7-eval '(1 0 1) 5) 5))
(defthm f7-x-squared-plus-one-at-6
  (equal (f7-eval '(1 0 1) 6) 2))

(defthm f7-x-squared-plus-one-is-root-free
  (not (f7-poly-has-root-p '(1 0 1)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-poly-has-root-p (poly '(1 0 1)))
                 (:instance f7-element-exhaustion
                            (x (f7-poly-has-root-p-witness '(1 0 1)))))
           :in-theory (disable f7-poly-has-root-p))))

(defthm f7-x-squared-plus-one-has-degree-two
  (equal (f7-poly-degree '(1 0 1)) 2))

(defthm f7-root-free-quadratic-is-irreducible
  (implies (and (equal (f7-poly-degree poly) 2)
                (not (f7-poly-has-root-p poly)))
           (f7-poly-irreducible-p poly))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance
                        root-free-quadratic-is-irreducible
                        (gfield::field-element-p gfield::f7-element-p)
                        (gfield::field-fix gfield::f7-fix)
                        (gfield::field-zero gfield::f7-zero)
                        (gfield::field-one gfield::f7-one)
                        (gfield::field-add gfield::f7-add)
                        (gfield::field-mul gfield::f7-mul)
                        (gfield::field-neg gfield::f7-neg)
                        (gfield::field-inv gfield::f7-inv)
                        (fix-coefficients f7-fix-coefficients)
                        (trim-trailing-zeros f7-trim-trailing-zeros)
                        (normalize f7-normalize)
                        (eval f7-eval)
                        (poly-degree f7-poly-degree)
                        (raw-add f7-raw-add)
                        (poly-add f7-poly-add)
                        (raw-scale f7-raw-scale)
                        (poly-scale f7-poly-scale)
                        (raw-mul f7-raw-mul)
                        (poly-mul f7-poly-mul)
                        (poly-unit-p f7-poly-unit-p)
                        (poly-reducible-p f7-poly-reducible-p)
                        (poly-reducible-p-witness
                         f7-poly-reducible-p-witness)
                        (poly-irreducible-p f7-poly-irreducible-p)
                        (poly-has-root-p f7-poly-has-root-p)
                        (poly-has-root-p-witness
                         f7-poly-has-root-p-witness)))
          ("Subgoal 29"
           :use f7-poly-reducible-p-full-witness-constraint-for-instantiation)
          ("Subgoal 26.2" :use gfield::f7-mul-inverse-right)
          ("Subgoal 23.4"
           :use ((:instance
                  f7-mul-fixed-congruence-for-quadratic-instantiation
                  (x1 gfield::x1) (x2 gfield::x2)
                  (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 22.11"
           :use ((:instance
                  f7-add-fixed-congruence-for-quadratic-instantiation
                  (x1 gfield::x1) (x2 gfield::x2)
                  (y1 gfield::y1) (y2 gfield::y2))))
          ("Subgoal 19.2.1'" :in-theory (enable mod))
          ("Subgoal 18.2.1''" :in-theory (enable mod))
          ("Subgoal 3"
           :use f7-poly-has-root-p-full-witness-constraint-for-instantiation)))

(defthm f7-x-squared-plus-one-is-irreducible
  (f7-poly-irreducible-p '(1 0 1))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-root-free-quadratic-is-irreducible
                            (poly '(1 0 1)))
                 f7-x-squared-plus-one-is-root-free
                 f7-x-squared-plus-one-has-degree-two)
           :in-theory (disable f7-poly-irreducible-p
                               f7-poly-has-root-p
                               f7-poly-reducible-p))))

(defthm f7-x-squared-plus-one-trailing-zero-normalizes
  (equal (f7-normalize '(1 0 1 0)) '(1 0 1)))

(defthm f7-x-squared-plus-one-fixed-coefficient-normalizes
  (equal (f7-normalize '(8 0 1)) '(1 0 1)))

(defthm f7-x-squared-plus-one-dotted-tail-normalizes
  (equal (f7-normalize '(1 0 1 . malformed-tail)) '(1 0 1)))

(defthm f7-poly-reducible-p-of-normalize
  (equal (f7-poly-reducible-p (f7-normalize poly))
         (f7-poly-reducible-p poly))
  :hints (("Goal"
           :use ((:instance f7-poly-reducible-p-suff
                            (poly (f7-normalize poly))
                            (left (mv-nth 0 (f7-poly-reducible-p-witness poly)))
                            (right (mv-nth 1 (f7-poly-reducible-p-witness poly))))
                 (:instance f7-poly-reducible-p-suff
                            (poly poly)
                            (left (mv-nth 0 (f7-poly-reducible-p-witness
                                             (f7-normalize poly))))
                            (right (mv-nth 1 (f7-poly-reducible-p-witness
                                              (f7-normalize poly))))))
           :in-theory (disable f7-poly-reducible-p-suff))))

(defthm f7-poly-irreducible-p-of-normalize
  (equal (f7-poly-irreducible-p (f7-normalize poly))
         (f7-poly-irreducible-p poly))
  :hints (("Goal"
           :use ((:instance f7-poly-reducible-p-of-normalize))
           :in-theory (e/d (f7-poly-irreducible-p)
                           (f7-poly-reducible-p
                            f7-poly-reducible-p-of-normalize)))))

(defthm f7-x-squared-plus-one-trailing-zero-is-irreducible
  (f7-poly-irreducible-p '(1 0 1 0))
  :rule-classes nil
  :hints (("Goal"
           :use (f7-x-squared-plus-one-is-irreducible
                 (:instance f7-poly-irreducible-p-of-normalize
                            (poly '(1 0 1 0))))
           :in-theory (disable f7-poly-irreducible-p
                               f7-poly-reducible-p))))

(defthm f7-x-squared-plus-one-fixed-coefficient-is-irreducible
  (f7-poly-irreducible-p '(8 0 1))
  :rule-classes nil
  :hints (("Goal"
           :use (f7-x-squared-plus-one-is-irreducible
                 (:instance f7-poly-irreducible-p-of-normalize
                            (poly '(8 0 1))))
           :in-theory (disable f7-poly-irreducible-p
                               f7-poly-reducible-p))))

(defthm f7-x-squared-plus-one-dotted-tail-is-irreducible
  (f7-poly-irreducible-p '(1 0 1 . malformed-tail))
  :rule-classes nil
  :hints (("Goal"
           :use (f7-x-squared-plus-one-is-irreducible
                 (:instance f7-poly-irreducible-p-of-normalize
                            (poly '(1 0 1 . malformed-tail))))
           :in-theory (disable f7-poly-irreducible-p
                               f7-poly-reducible-p))))

(defthm f7-nil-is-not-irreducible
  (not (f7-poly-irreducible-p nil)))

(defthm f7-one-is-not-irreducible
  (not (f7-poly-irreducible-p '(1))))

(defthm f7-three-is-not-irreducible
  (not (f7-poly-irreducible-p '(3))))

(defthm f7-x-squared-minus-one-has-root-one
  (f7-poly-has-root-p '(6 0 1))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-poly-has-root-p-suff
                                    (poly '(6 0 1)) (root 1))))))

(defthm f7-x-squared-minus-one-has-root-six
  (f7-poly-has-root-p '(6 0 1))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-poly-has-root-p-suff
                                    (poly '(6 0 1)) (root 6))))))
