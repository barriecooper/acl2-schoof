(in-package "GPOLY")
(include-book "scale")

; Recursive shifted scaling, rather than a second coefficient-convolution
; implementation, reuses the already certified raw addition and scaling.
(def-mul-instance raw-mul poly-mul raw-add raw-scale normalize
                  gfield::field-zero)

(defthm raw-mul-when-atom-left
  (implies (atom x) (equal (raw-mul x y) nil)))

(defthm raw-mul-when-atom-right
  (implies (atom y) (equal (raw-mul x y) nil)))

(defthm raw-mul-of-cons
  (equal (raw-mul (cons a x) y)
         (if (consp y)
             (raw-add (raw-scale a y)
                      (cons (gfield::field-zero) (raw-mul x y)))
           nil)))

(defthm true-listp-of-raw-mul
  (true-listp (raw-mul x y)))

(defthm coefficient-list-p-of-raw-mul
  (coefficient-list-p (raw-mul x y)))

(defthm canonical-polynomial-p-of-poly-mul
  (canonical-polynomial-p (poly-mul x y)))

(defthm polynomial-p-of-poly-mul
  (polynomial-p (poly-mul x y)))

(defthm poly-mul-of-nil-left
  (equal (poly-mul nil x) nil))

(defthm poly-mul-of-nil-right
  (equal (poly-mul x nil) nil))

(defthm eval-of-zero-cons
  (equal (eval (cons (gfield::field-zero) poly) x)
         (gfield::field-mul x (eval poly x))))

(defthm eval-of-raw-mul
  (equal (eval (raw-mul f g) x)
         (gfield::field-mul (eval f x) (eval g x)))
  :hints (("Goal" :induct (raw-mul f g)
           :in-theory (enable gfield::field-mul-right-distributive
                              gfield::field-mul-associative
                              gfield::field-mul-commutative))))

(defthm eval-of-poly-mul
  (equal (eval (poly-mul f g) x)
         (gfield::field-mul (eval f x) (eval g x))))

(defthm poly-mul-normalize-left
  (equal (poly-mul (normalize x) y) (poly-mul x y)))

(defthm poly-mul-normalize-right
  (equal (poly-mul x (normalize y)) (poly-mul x y)))

(defthm poly-mul-fix-coefficients-left
  (equal (poly-mul (fix-coefficients x) y) (poly-mul x y)))

(defthm poly-mul-fix-coefficients-right
  (equal (poly-mul x (fix-coefficients y)) (poly-mul x y)))

(defcong equal equal (poly-mul x y) 1)
(defcong equal equal (poly-mul x y) 2)

(defthm raw-mul-of-one-left
  (equal (raw-mul (list (gfield::field-one)) x)
         (fix-coefficients x)))

(defthm raw-mul-by-singleton-right
  (equal (raw-mul x (list a)) (raw-scale a x))
  :hints (("Goal" :induct (raw-scale a x)
           :in-theory (enable gfield::field-mul-commutative))))

(defthm poly-mul-of-one-left
  (equal (poly-mul (list (gfield::field-one)) x) (normalize x)))

(defthm poly-mul-one-left-when-canonical
  (implies (canonical-polynomial-p x)
           (equal (poly-mul (list (gfield::field-one)) x) x)))

(defthm poly-mul-of-one-right
  (equal (poly-mul x (list (gfield::field-one))) (normalize x))
  :hints (("Goal" :in-theory (enable poly-mul poly-scale))))

(defthm poly-mul-one-right-when-canonical
  (implies (canonical-polynomial-p x)
           (equal (poly-mul x (list (gfield::field-one))) x)))

; The multiplication laws below are coefficient identities.  In particular,
; none of them is obtained from the evaluation theorem above (evaluation is
; not extensional for formal polynomials over a finite field).

(defthm raw-add-interchange
  (implies (and (coefficient-list-p a)
                (coefficient-list-p b)
                (coefficient-list-p c)
                (coefficient-list-p d))
           (equal (raw-add (raw-add a b) (raw-add c d))
                  (raw-add (raw-add a c) (raw-add b d))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-add-associative
                            (x (raw-add a b)) (y c) (z d))
                 (:instance raw-add-associative (x a) (y b) (z c))
                 (:instance raw-add-associative (x a) (y c) (z b))
                 (:instance raw-add-associative
                            (x (raw-add a c)) (y b) (z d))
                 (:instance raw-add-commutative (x b) (y c)))
           :in-theory (disable raw-add-associative
                               raw-add-commutative))))

(defthm raw-add-of-zero-prefixes
  (equal (raw-add (cons (gfield::field-zero) x)
                  (cons (gfield::field-zero) y))
         (cons (gfield::field-zero) (raw-add x y))))

(defthm raw-scale-of-zero-prefix
  (equal (raw-scale a (cons (gfield::field-zero) x))
         (cons (gfield::field-zero) (raw-scale a x))))

(defthm consp-of-raw-scale
  (equal (consp (raw-scale a x)) (consp x)))

(defthm fix-coefficients-of-raw-scale
  (equal (fix-coefficients (raw-scale a x)) (raw-scale a x)))

(defthm raw-scale-reconstruct
  (implies (consp x)
           (equal (cons (gfield::field-fix (car (raw-scale a x)))
                        (fix-coefficients (cdr (raw-scale a x))))
                  (raw-scale a x))))

(defthm raw-add-nested-interchange
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (coefficient-list-p z))
           (equal (raw-add x (raw-add y z))
                  (raw-add y (raw-add x z))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-add-associative (x x) (y y) (z z))
                 (:instance raw-add-associative (x y) (y x) (z z))
                 (:instance raw-add-commutative (x x) (y y)))
           :in-theory (disable raw-add-associative
                               raw-add-commutative))))

(defthm raw-mul-right-recursion
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (gfield::field-element-p a))
           (equal (raw-mul x (cons a y))
                  (if (consp x)
                      (raw-add (raw-scale a x)
                               (cons (gfield::field-zero) (raw-mul x y)))
                    nil)))
  :rule-classes nil
  :hints (("Goal" :induct (raw-mul x y)
           :in-theory (enable gfield::field-mul-commutative))
          ("Subgoal *1/2.1"
           :use ((:instance raw-add-nested-interchange
                            (x (raw-scale (car x) y))
                            (y (raw-scale a (cdr x)))
                            (z (cons (gfield::field-zero)
                                     (raw-mul (cdr x) y))))))))

(defthm raw-mul-commutative
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y))
           (equal (raw-mul x y) (raw-mul y x)))
  :rule-classes nil
  :hints (("Goal" :induct (raw-mul x y))
          ("Subgoal *1/2"
           :use ((:instance raw-mul-right-recursion
                            (x y) (a (car x)) (y (cdr x)))))))

(defthm raw-mul-right-distributive
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (coefficient-list-p z))
           (equal (raw-mul x (raw-add y z))
                  (raw-add (raw-mul x y) (raw-mul x z))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-mul x y)
           :in-theory (enable raw-scale-of-raw-add))
          ("Subgoal *1/2"
           :use ((:instance raw-add-interchange
                            (a (raw-scale (car x) y))
                            (b (cons (gfield::field-zero)
                                     (raw-mul (cdr x) y)))
                            (c (raw-scale (car x) z))
                            (d (cons (gfield::field-zero)
                                     (raw-mul (cdr x) z))))))))

(defthm raw-mul-left-distributive
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (coefficient-list-p z))
           (equal (raw-mul (raw-add x y) z)
                  (raw-add (raw-mul x z) (raw-mul y z))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-mul-commutative
                            (x (raw-add x y)) (y z))
                 (:instance raw-mul-commutative (x x) (y z))
                 (:instance raw-mul-commutative (x y) (y z))
                 (:instance raw-mul-right-distributive
                            (x z) (y x) (z y))))))

(defthm raw-mul-of-raw-scale-left
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y))
           (equal (raw-mul (raw-scale a x) y)
                  (raw-scale a (raw-mul x y))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-mul x y)
           :in-theory (enable raw-scale-nested
                              raw-scale-of-raw-add))))

(defthm len-of-raw-scale
  (equal (len (raw-scale a x)) (len x)))

(defthm consp-of-raw-mul
  (equal (consp (raw-mul x y))
         (and (consp x) (consp y))))

(defthm len-of-raw-mul
  (implies (and (true-listp x) (true-listp y))
           (equal (len (raw-mul x y))
                  (if (or (endp x) (endp y))
                      0
                    (+ -1 (len x) (len y))))))

; The following three list facts isolate the structural content needed at the
; top of a convolution.  They are kept out of the default rewrite theory: in
; particular, LAST of RAW-ADD should only be selected when the length
; comparison that makes one operand decisive is already known.
(defthm last-of-raw-scale
  (implies (consp x)
           (equal (car (last (raw-scale a x)))
                  (gfield::field-mul a (car (last x)))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-scale a x))))

(defthm last-of-raw-add-when-right-longer
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (< (len x) (len y)))
           (equal (car (last (raw-add x y)))
                  (car (last y))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-add x y))))

(defthm last-of-zero-prefix
  (implies (consp x)
           (equal (car (last (cons (gfield::field-zero) x)))
                  (car (last x))))
  :rule-classes nil)

(defthm raw-add-zero-singleton-right
  (implies (and (coefficient-list-p x)
                (consp x))
           (equal (raw-add x (list (gfield::field-zero))) x))
  :rule-classes nil
  :hints (("Goal" :induct (coefficient-list-p x)
           :in-theory (enable raw-add))))

(defthm raw-mul-singleton-left
  (implies (and (gfield::field-element-p a)
                (coefficient-list-p g)
                (consp g))
           (equal (raw-mul (list a) g)
                  (raw-scale a g)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-add-zero-singleton-right
                            (x (raw-scale a g))))
           :in-theory (e/d (raw-mul)
                           (raw-add-commutative)))))

(defthm len-raw-scale-less-than-zero-prefix-raw-mul
  (implies (and (true-listp f)
                (true-listp g)
                (consp f)
                (consp g))
           (< (len (raw-scale a g))
              (len (cons (gfield::field-zero) (raw-mul f g)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance len-of-raw-scale (x g))
                 (:instance len-of-raw-mul (x f) (y g)))
           :in-theory (disable raw-scale raw-mul))))

(defthm raw-leading-coefficient-of-raw-mul
  (implies (and (coefficient-list-p f)
                (coefficient-list-p g)
                (consp f)
                (consp g))
           (equal (car (last (raw-mul f g)))
                  (gfield::field-mul (car (last f))
                                     (car (last g)))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-mul f g)
           :in-theory (disable gfield::field-mul-commutative
                               raw-add-commutative))
          ("Subgoal *1/2"
           :use ((:instance raw-mul-singleton-left
                            (a (car f)) (g g))
                 (:instance last-of-raw-scale
                            (a (car f)) (x g)))
           :in-theory (disable gfield::field-mul-commutative
                               raw-add-commutative
                               raw-mul))
          ("Subgoal *1/3"
           :use ((:instance last-of-raw-add-when-right-longer
                            (x (raw-scale (car f) g))
                            (y (cons (gfield::field-zero)
                                     (raw-mul (cdr f) g))))
                 (:instance last-of-zero-prefix
                            (x (raw-mul (cdr f) g)))
                 (:instance len-of-raw-scale
                            (a (car f)) (x g))
                 (:instance len-of-raw-mul (x (cdr f)) (y g))
                 (:instance coefficient-list-p-of-raw-mul
                            (x (cdr f)) (y g))
                 (:instance len-raw-scale-less-than-zero-prefix-raw-mul
                            (a (car f)) (f (cdr f)) (g g)))
           :in-theory (disable gfield::field-mul-commutative
                               raw-add-commutative
                               raw-add raw-scale raw-mul))))

(defthm len-raw-add-lower-bound-left
  (<= (len x) (len (raw-add x y)))
  :rule-classes :linear)

(defthm len-raw-mul-lower-bound-right
  (implies (and (true-listp x) (true-listp y)
                (consp x) (consp y))
           (<= (len y) (len (raw-mul x y))))
  :rule-classes :linear)

(defthm raw-add-of-zero-scale-left
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (<= (len x) (len y)))
           (equal (raw-add (raw-scale (gfield::field-zero) x) y)
                  y))
  :hints (("Goal" :induct (raw-add x y)
           :in-theory (disable raw-add-commutative
                               raw-add-of-zero-prefixes
                               raw-scale-of-zero-prefix
                               raw-scale-by-zero
                               len-raw-add-lower-bound-left
                               len-raw-mul-lower-bound-right))))

(defthm raw-add-zero-scale-before-product
  (implies (and (coefficient-list-p y)
                (coefficient-list-p z)
                (coefficient-list-p rest)
                (consp y) (consp z))
           (equal (raw-add
                   (raw-scale (gfield::field-zero) z)
                   (raw-add (raw-scale a (raw-mul y z)) rest))
                  (raw-add (raw-scale a (raw-mul y z)) rest)))
  :hints (("Goal"
           :use ((:instance raw-add-of-zero-scale-left
                            (x z)
                            (y (raw-add (raw-scale a (raw-mul y z))
                                        rest)))
                 (:instance len-raw-mul-lower-bound-right (x y) (y z))
                 (:instance len-raw-add-lower-bound-left
                            (x (raw-scale a (raw-mul y z))) (y rest)))
           :in-theory (disable raw-add raw-scale raw-mul
                               raw-add-commutative
                               raw-scale-by-zero
                               raw-scale-of-zero-prefix
                               raw-add-of-zero-prefixes))))

(defthm raw-mul-associative
  (implies (and (coefficient-list-p x)
                (coefficient-list-p y)
                (coefficient-list-p z))
           (equal (raw-mul (raw-mul x y) z)
                  (raw-mul x (raw-mul y z))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-mul x y)
           :in-theory (disable raw-add-commutative
                               raw-scale-by-zero
                               raw-scale-of-zero-prefix
                               raw-add-of-zero-prefixes))
          ("Subgoal *1/2"
           :use ((:instance raw-mul-left-distributive
                            (x (raw-scale (car x) y))
                            (y (cons (gfield::field-zero)
                                     (raw-mul (cdr x) y)))
                            (z z))
                 (:instance raw-mul-of-raw-scale-left
                            (a (car x)) (x y) (y z))
                 (:instance raw-add-interchange
                            (a (raw-scale (car x) (raw-mul y z)))
                            (b (raw-scale (gfield::field-zero) z))
                            (c nil)
                            (d (cons (gfield::field-zero)
                                     (raw-mul (raw-mul (cdr x) y) z))))
                 (:instance raw-add-nested-interchange
                            (x (raw-mul (raw-scale (car x) y) z))
                            (y (raw-scale (gfield::field-zero) z))
                            (z (cons (gfield::field-zero)
                                     (raw-mul (raw-mul (cdr x) y) z))))
                 (:instance raw-add-zero-scale-before-product
                            (a (car x)) (y y) (z z)
                            (rest (cons (gfield::field-zero)
                                        (raw-mul (raw-mul (cdr x) y) z))))))))

; These rearranging shift facts are proof infrastructure, not default
; simplifiers.  In particular, they must not interact with distributive
; expansion or the raw recursion outside an explicitly selected proof.
(in-theory (disable raw-add-of-zero-prefixes raw-scale-of-zero-prefix))

(defthm poly-mul-of-constant-left
  (equal (poly-mul (list (gfield::field-fix a)) x)
         (poly-scale a x))
  :hints (("Goal" :in-theory (enable poly-mul poly-scale))))

(defthm normalize-of-zero-prefix
  (equal (normalize (cons (gfield::field-zero) x))
         (if (consp (normalize x))
             (cons (gfield::field-zero) (normalize x))
           nil))
  :hints (("Goal" :in-theory (enable normalize trim-trailing-zeros
                                     fix-coefficients))))

(defthm normalize-raw-add-congruence
  (implies (and (polynomial-p a) (polynomial-p b)
                (polynomial-p c) (polynomial-p d)
                (equal (normalize a) (normalize c))
                (equal (normalize b) (normalize d)))
           (equal (normalize (raw-add a b))
                  (normalize (raw-add c d))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance normalize-raw-add-normalize-left (x a) (y b))
                 (:instance normalize-raw-add-normalize-right
                            (x (normalize a)) (y b))
                 (:instance normalize-raw-add-normalize-left (x c) (y d))
                 (:instance normalize-raw-add-normalize-right
                            (x (normalize c)) (y d))))))

(defthm normalize-raw-mul-normalize-right
  (implies (and (coefficient-list-p x) (coefficient-list-p y))
           (equal (normalize (raw-mul x (normalize y)))
                  (normalize (raw-mul x y))))
  :rule-classes nil
  :hints (("Goal" :induct (raw-mul x y))
          ("Subgoal *1/2"
           :use ((:instance normalize-raw-add-congruence
                            (a (raw-scale (car x) (normalize y)))
                            (b (cons (gfield::field-zero)
                                     (raw-mul (cdr x) (normalize y))))
                            (c (raw-scale (car x) y))
                            (d (cons (gfield::field-zero)
                                     (raw-mul (cdr x) y))))
                 (:instance normalize-raw-scale-of-normalize
                            (a (car x)) (x y))))))

(defthm normalize-raw-mul-normalize-left
  (implies (and (coefficient-list-p x) (coefficient-list-p y))
           (equal (normalize (raw-mul (normalize x) y))
                  (normalize (raw-mul x y))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-mul-commutative
                            (x (normalize x)) (y y))
                 (:instance raw-mul-commutative (x x) (y y))
                 (:instance normalize-raw-mul-normalize-right
                            (x y) (y x))))))

(defthm poly-mul-commutative
  (equal (poly-mul x y) (poly-mul y x))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-mul-commutative
                            (x (normalize x)) (y (normalize y))))
           :in-theory (enable poly-mul))))

(defthm poly-mul-left-distributive
  (equal (poly-mul x (poly-add y z))
         (poly-add (poly-mul x y) (poly-mul x z)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-mul-right-distributive
                            (x (normalize x))
                            (y (normalize y))
                            (z (normalize z)))
                 (:instance poly-mul-normalize-right
                            (x (normalize x))
                            (y (raw-add (normalize y) (normalize z))))
                 (:instance normalize-raw-mul-normalize-right
                            (x (normalize x))
                            (y (raw-add (normalize y) (normalize z))))
                 (:instance normalize-raw-add-normalize-left
                            (x (raw-mul (normalize x) (normalize y)))
                            (y (normalize
                                (raw-mul (normalize x) (normalize z)))))
                 (:instance normalize-raw-add-normalize-right
                            (x (raw-mul (normalize x) (normalize y)))
                            (y (raw-mul (normalize x) (normalize z)))))
           :in-theory (enable poly-mul poly-add))))

(defthm poly-mul-right-distributive
  (equal (poly-mul (poly-add x y) z)
         (poly-add (poly-mul x z) (poly-mul y z)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance poly-mul-commutative
                            (x (poly-add x y)) (y z))
                 (:instance poly-mul-commutative (x x) (y z))
                 (:instance poly-mul-commutative (x y) (y z))
                 (:instance poly-mul-left-distributive
                            (x z) (y x) (z y))))))

(defthm poly-mul-associative
  (equal (poly-mul (poly-mul x y) z)
         (poly-mul x (poly-mul y z)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance raw-mul-associative
                            (x (normalize x))
                            (y (normalize y))
                            (z (normalize z)))
                 (:instance normalize-raw-mul-normalize-left
                            (x (raw-mul (normalize x) (normalize y)))
                            (y (normalize z)))
                 (:instance normalize-raw-mul-normalize-right
                            (x (normalize x))
                            (y (raw-mul (normalize y) (normalize z)))))
           :in-theory (enable poly-mul))))
