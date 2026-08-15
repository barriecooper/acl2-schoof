(in-package "GPOLY")

(include-book "runtime-p-algebra")

; Proof-local rewrite orientations of the public coefficient ring laws.
(local (defthm rp-add-associative
  (equal (runtime-p-add (runtime-p-add x y p) z p)
         (runtime-p-add x (runtime-p-add y z p) p))
  :hints (("Goal" :use ((:instance runtime-p-add-associative))))))
(local (defthm rp-add-commutative
  (equal (runtime-p-add x y p) (runtime-p-add y x p))
  :hints (("Goal" :use ((:instance runtime-p-add-commutative))))))
(local (defthm rp-mul-associative
  (equal (runtime-p-mul (runtime-p-mul x y p) z p)
         (runtime-p-mul x (runtime-p-mul y z p) p))
  :hints (("Goal" :use ((:instance runtime-p-mul-associative))))))
(local (defthm rp-mul-commutative
  (equal (runtime-p-mul x y p) (runtime-p-mul y x p))
  :hints (("Goal" :use ((:instance runtime-p-mul-commutative))))))
(local (defthm rp-mul-left-distributive
  (equal (runtime-p-mul x (runtime-p-add y z p) p)
         (runtime-p-add (runtime-p-mul x y p)
                        (runtime-p-mul x z p) p))
  :hints (("Goal" :use ((:instance runtime-p-mul-left-distributive))))))
(local (defthm rp-mul-right-distributive
  (equal (runtime-p-mul (runtime-p-add x y p) z p)
         (runtime-p-add (runtime-p-mul x z p)
                        (runtime-p-mul y z p) p))
  :hints (("Goal" :use ((:instance runtime-p-mul-right-distributive))))))

(local (defthm rp-coefficient-list-p-of-raw-add
  (runtime-p-coefficient-list-p (runtime-p-raw-add x y p) p)
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (enable runtime-p-coefficient-list-p)))))
(local (defthm rp-coefficient-list-p-of-raw-scale
  (runtime-p-coefficient-list-p (runtime-p-raw-scale a x p) p)
  :hints (("Goal" :induct (runtime-p-raw-scale a x p)
           :in-theory (enable runtime-p-coefficient-list-p)))))
(local (defthm rp-coefficient-list-p-of-raw-mul
  (runtime-p-coefficient-list-p (runtime-p-raw-mul x y p) p)
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable runtime-p-raw-mul)))))

(local (defthm rp-raw-add-commutative
  (equal (runtime-p-raw-add x y p)
         (runtime-p-raw-add y x p))
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (enable runtime-p-raw-add rp-add-commutative)))))

(local (defun rp-raw-add-induct3 (x y z)
  (declare (xargs :measure (+ (len x) (len y) (len z))))
  (if (or (consp x) (consp y) (consp z))
      (rp-raw-add-induct3 (if (consp x) (cdr x) nil)
                       (if (consp y) (cdr y) nil)
                       (if (consp z) (cdr z) nil))
    nil)))
(local (defthm rp-raw-add-associative
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p)
                (runtime-p-coefficient-list-p z p))
           (equal (runtime-p-raw-add (runtime-p-raw-add x y p) z p)
                  (runtime-p-raw-add x (runtime-p-raw-add y z p) p)))
  :hints (("Goal" :induct (rp-raw-add-induct3 x y z)
           :in-theory (enable runtime-p-raw-add
                              runtime-p-coefficient-list-p
                              rp-add-associative)))))

(local (defthm rp-raw-add-interchange
  (implies (and (runtime-p-coefficient-list-p a p)
                (runtime-p-coefficient-list-p b p)
                (runtime-p-coefficient-list-p c p)
                (runtime-p-coefficient-list-p d p))
           (equal (runtime-p-raw-add
                   (runtime-p-raw-add a b p)
                   (runtime-p-raw-add c d p) p)
                  (runtime-p-raw-add
                   (runtime-p-raw-add a c p)
                   (runtime-p-raw-add b d p) p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance rp-raw-add-associative
                                   (x (runtime-p-raw-add a b p)) (y c) (z d))
                         (:instance rp-raw-add-associative (x a) (y b) (z c))
                         (:instance rp-raw-add-associative (x a) (y c) (z b))
                         (:instance rp-raw-add-associative
                                   (x (runtime-p-raw-add a c p)) (y b) (z d))
                         (:instance rp-raw-add-commutative (x b) (y c)))
           :in-theory (disable rp-raw-add-associative rp-raw-add-commutative)))))

(local (defthm rp-raw-add-nested-interchange
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p)
                (runtime-p-coefficient-list-p z p))
           (equal (runtime-p-raw-add x (runtime-p-raw-add y z p) p)
                  (runtime-p-raw-add y (runtime-p-raw-add x z p) p)))
  :hints (("Goal" :use ((:instance rp-raw-add-associative)
                         (:instance rp-raw-add-associative (x y) (y x))
                         (:instance rp-raw-add-commutative (y y)))
           :in-theory (disable rp-raw-add-associative rp-raw-add-commutative)))))

(local (defthm rp-raw-scale-nested
  (equal (runtime-p-raw-scale a (runtime-p-raw-scale b x p) p)
         (runtime-p-raw-scale (runtime-p-mul a b p) x p))
  :hints (("Goal" :induct (runtime-p-raw-scale b x p)
           :in-theory (enable runtime-p-raw-scale rp-mul-associative)))))
(local (defthm rp-raw-scale-of-raw-add
  (equal (runtime-p-raw-scale a (runtime-p-raw-add x y p) p)
         (runtime-p-raw-add (runtime-p-raw-scale a x p)
                            (runtime-p-raw-scale a y p) p))
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (enable runtime-p-raw-add runtime-p-raw-scale
                              rp-mul-left-distributive)))))
(local (defthm rp-raw-scale-of-zero-prefix
  (equal (runtime-p-raw-scale a (cons 0 x) p)
         (cons 0 (runtime-p-raw-scale a x p)))
  :hints (("Goal" :in-theory (enable runtime-p-raw-scale)))))
(local (defthm rp-raw-add-of-zero-prefixes
  (equal (runtime-p-raw-add (cons 0 x) (cons 0 y) p)
         (cons 0 (runtime-p-raw-add x y p)))
  :hints (("Goal" :in-theory (enable runtime-p-raw-add)))))

(local (defthm rp-consp-of-raw-scale
  (equal (consp (runtime-p-raw-scale a x p)) (consp x))
  :hints (("Goal" :in-theory (enable runtime-p-raw-scale)))))
(local (defthm rp-fix-coefficients-of-raw-scale
  (equal (runtime-p-fix-coefficients (runtime-p-raw-scale a x p) p)
         (runtime-p-raw-scale a x p))
  :hints (("Goal" :induct (runtime-p-raw-scale a x p)
           :in-theory (enable runtime-p-raw-scale)))))
(local (defthm rp-coefficient-p-of-car
  (implies (and (runtime-p-coefficient-list-p x p) (consp x))
           (runtime-p-coefficient-p (car x) p))
  :hints (("Goal" :in-theory (enable runtime-p-coefficient-list-p)))))
(local (defthm rp-coefficient-list-p-of-cdr
  (implies (runtime-p-coefficient-list-p x p)
           (runtime-p-coefficient-list-p (cdr x) p))
  :hints (("Goal" :in-theory (enable runtime-p-coefficient-list-p)))))

(local (defthm rp-raw-scale-fixed-car
  (implies (consp x)
           (equal (runtime-p-coefficient-fix
                   (car (runtime-p-raw-scale a x p)) p)
                  (car (runtime-p-raw-scale a x p))))
  :hints (("Goal"
           :use ((:instance rp-coefficient-list-p-of-raw-scale)
                 (:instance rp-coefficient-p-of-car
                            (x (runtime-p-raw-scale a x p)))
                 (:instance runtime-p-coefficient-fix-when-recognized
                            (x (car (runtime-p-raw-scale a x p)))))
           :in-theory (disable runtime-p-raw-scale
                               runtime-p-coefficient-fix)))))
(local (defthm rp-raw-scale-fixed-cdr
  (equal (runtime-p-fix-coefficients
          (cdr (runtime-p-raw-scale a x p)) p)
         (cdr (runtime-p-raw-scale a x p)))
  :hints (("Goal"
           :use ((:instance rp-coefficient-list-p-of-raw-scale)
                 (:instance rp-coefficient-list-p-of-cdr
                            (x (runtime-p-raw-scale a x p)))
                 (:instance runtime-p-fix-coefficients-when-recognized
                            (xs (cdr (runtime-p-raw-scale a x p)))))
           :in-theory (disable runtime-p-raw-scale
                               runtime-p-fix-coefficients)))))

(local (defthm rp-raw-scale-reconstruct
  (implies (consp x)
           (equal (cons (runtime-p-coefficient-fix
                         (car (runtime-p-raw-scale a x p)) p)
                        (runtime-p-fix-coefficients
                         (cdr (runtime-p-raw-scale a x p)) p))
                  (runtime-p-raw-scale a x p)))
  :hints (("Goal" :use ((:instance rp-fix-coefficients-of-raw-scale))
           :in-theory (enable runtime-p-raw-scale)))))

(local (defthm rp-raw-add-zero-singleton-left
  (implies (and (runtime-p-coefficient-list-p x p) (consp x))
           (equal (runtime-p-raw-add (list 0) x p) x))
  :hints (("Goal" :induct (runtime-p-coefficient-list-p x p)
           :in-theory (enable runtime-p-raw-add
                              runtime-p-coefficient-list-p)))))
(local (defthm rp-raw-add-zero-singleton-right
  (implies (and (runtime-p-coefficient-list-p x p) (consp x))
           (equal (runtime-p-raw-add x (list 0) p) x))
  :hints (("Goal" :use ((:instance rp-raw-add-commutative
                                   (y (list 0)))
                         (:instance rp-raw-add-zero-singleton-left))))))
(local (defthm rp-raw-scale-of-cons
  (equal (runtime-p-raw-scale a (cons b x) p)
         (cons (runtime-p-mul a b p)
               (runtime-p-raw-scale a x p)))
  :hints (("Goal" :in-theory (enable runtime-p-raw-scale)))))

(local (defthm rp-raw-scale-of-add
  (equal (runtime-p-raw-scale (runtime-p-add a b p) x p)
         (runtime-p-raw-add (runtime-p-raw-scale a x p)
                            (runtime-p-raw-scale b x p) p))
  :hints (("Goal" :induct (runtime-p-raw-scale a x p)
           :in-theory (enable runtime-p-raw-scale runtime-p-raw-add
                              rp-mul-right-distributive)))))

(local (defun rp-raw-add-mul-induct (x y z)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (consp x) (consp y))
      (rp-raw-add-mul-induct (cdr x) (cdr y) z)
    (list x y z))))

(local (defthm rp-raw-mul-left-distributive
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p)
                (runtime-p-coefficient-list-p z p))
           (equal (runtime-p-raw-mul (runtime-p-raw-add x y p) z p)
                  (runtime-p-raw-add (runtime-p-raw-mul x z p)
                                     (runtime-p-raw-mul y z p) p)))
  :rule-classes nil
  :hints (("Goal" :induct (rp-raw-add-mul-induct x y z)
           :in-theory (e/d (runtime-p-raw-mul runtime-p-raw-add
                                rp-raw-scale-of-add)
                           (runtime-p-add runtime-p-mul
                            runtime-p-coefficient-fix
                            runtime-p-fix-coefficients
                            runtime-p-effective-modulus)))
          ("Subgoal *1/1"
           :use ((:instance rp-raw-add-interchange
                            (a (runtime-p-raw-scale (car x) z p))
                            (b (runtime-p-raw-scale (car y) z p))
                            (c (cons 0 (runtime-p-raw-mul (cdr x) z p)))
                            (d (cons 0 (runtime-p-raw-mul (cdr y) z p)))))))))
(local (defthm rp-raw-mul-of-raw-scale-left
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p))
           (equal (runtime-p-raw-mul (runtime-p-raw-scale a x p) y p)
                  (runtime-p-raw-scale a (runtime-p-raw-mul x y p) p)))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable runtime-p-raw-mul rp-raw-scale-nested
                              rp-raw-scale-of-raw-add)))))

(local (defthm rp-len-of-raw-scale
  (equal (len (runtime-p-raw-scale a x p)) (len x))
  :hints (("Goal" :induct (runtime-p-raw-scale a x p)
           :in-theory (enable runtime-p-raw-scale)))))
(local (defthm rp-true-listp-of-raw-mul
  (true-listp (runtime-p-raw-mul x y p))
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable runtime-p-raw-mul)))))
(local (defthm rp-len-of-raw-add
  (equal (len (runtime-p-raw-add x y p)) (max (len x) (len y)))
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (enable runtime-p-raw-add)))))
(local (defthm rp-consp-of-raw-mul
  (equal (consp (runtime-p-raw-mul x y p))
         (and (consp x) (consp y)))
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable runtime-p-raw-mul)))))

(local (defthm rp-len-of-raw-mul
  (implies (and (true-listp x) (true-listp y))
           (equal (len (runtime-p-raw-mul x y p))
                  (if (or (endp x) (endp y)) 0
                    (+ -1 (len x) (len y)))))
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable runtime-p-raw-mul)))))
(local (defthm rp-raw-scale-by-zero
  (equal (runtime-p-raw-scale 0 x p)
         (if (consp x) (cons 0 (runtime-p-raw-scale 0 (cdr x) p)) nil))
  :hints (("Goal" :in-theory (enable runtime-p-raw-scale)))))
(local (defthm rp-len-raw-add-lower-bound-left
  (<= (len x) (len (runtime-p-raw-add x y p)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance rp-len-of-raw-add))))))
(local (defthm rp-len-raw-mul-lower-bound-right
  (implies (and (true-listp x) (true-listp y) (consp x) (consp y))
           (<= (len y) (len (runtime-p-raw-mul x y p))))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance rp-len-of-raw-mul))))))
(local (defthm rp-raw-add-of-zero-scale-left
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p)
                (<= (len x) (len y)))
           (equal (runtime-p-raw-add (runtime-p-raw-scale 0 x p) y p) y))
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (e/d (runtime-p-raw-add runtime-p-raw-scale)
                           (rp-raw-add-commutative
                            rp-raw-scale-by-zero
                            rp-raw-scale-of-zero-prefix
                            rp-raw-add-of-zero-prefixes
                            rp-len-raw-add-lower-bound-left
                            rp-len-raw-mul-lower-bound-right))))))
(local (defthm rp-true-listp-when-coefficient-list-p
  (implies (runtime-p-coefficient-list-p x p) (true-listp x))
  :hints (("Goal" :induct (runtime-p-coefficient-list-p x p)
           :in-theory (enable runtime-p-coefficient-list-p)))))

(local (defthm rp-len-product-summand-lower-bound
  (implies (and (true-listp y) (true-listp z)
                (consp y) (consp z))
           (<= (len z)
               (len (runtime-p-raw-add
                     (runtime-p-raw-scale
                      a (runtime-p-raw-mul y z p) p)
                     rest p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance rp-len-raw-mul-lower-bound-right (x y) (y z))
                 (:instance rp-len-of-raw-scale
                            (x (runtime-p-raw-mul y z p)))
                 (:instance rp-len-raw-add-lower-bound-left
                            (x (runtime-p-raw-scale
                                a (runtime-p-raw-mul y z p) p))
                            (y rest)))
           :in-theory (disable runtime-p-raw-add runtime-p-raw-scale
                               runtime-p-raw-mul rp-len-of-raw-add
                               rp-len-of-raw-scale)))))

(local (defthm rp-raw-add-zero-scale-before-product
  (implies (and (runtime-p-coefficient-list-p y p)
                (runtime-p-coefficient-list-p z p)
                (runtime-p-coefficient-list-p rest p)
                (consp y) (consp z))
           (equal (runtime-p-raw-add
                   (runtime-p-raw-scale 0 z p)
                   (runtime-p-raw-add
                    (runtime-p-raw-scale a (runtime-p-raw-mul y z p) p)
                    rest p) p)
                  (runtime-p-raw-add
                   (runtime-p-raw-scale a (runtime-p-raw-mul y z p) p)
                   rest p)))
  :hints (("Goal"
           :use ((:instance rp-raw-add-of-zero-scale-left
                            (x z)
                            (y (runtime-p-raw-add
                                (runtime-p-raw-scale
                                 a (runtime-p-raw-mul y z p) p)
                                rest p)))
                 (:instance rp-len-product-summand-lower-bound))
           :do-not-induct t
           :in-theory (disable runtime-p-raw-add runtime-p-raw-scale
                               runtime-p-raw-mul rp-raw-add-commutative
                               rp-raw-scale-by-zero
                               rp-raw-scale-of-zero-prefix
                               rp-raw-add-of-zero-prefixes
                               rp-len-of-raw-add rp-len-of-raw-scale
                               rp-len-raw-add-lower-bound-left
                               rp-len-raw-mul-lower-bound-right)))))

(local (defthm rp-raw-mul-associative
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p)
                (runtime-p-coefficient-list-p z p))
           (equal (runtime-p-raw-mul (runtime-p-raw-mul x y p) z p)
                  (runtime-p-raw-mul x (runtime-p-raw-mul y z p) p)))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (disable rp-raw-add-commutative
                               rp-raw-scale-by-zero
                               rp-raw-scale-of-zero-prefix
                               rp-raw-add-of-zero-prefixes))
          ("Subgoal *1/2"
           :use ((:instance rp-raw-mul-left-distributive
                            (x (runtime-p-raw-scale (car x) y p))
                            (y (cons 0 (runtime-p-raw-mul (cdr x) y p)))
                            (z z))
                 (:instance rp-raw-mul-of-raw-scale-left
                            (a (car x)) (x y) (y z))
                 (:instance rp-raw-add-interchange
                            (a (runtime-p-raw-scale
                                (car x) (runtime-p-raw-mul y z p) p))
                            (b (runtime-p-raw-scale 0 z p))
                            (c nil)
                            (d (cons 0
                                     (runtime-p-raw-mul
                                      (runtime-p-raw-mul (cdr x) y p) z p))))
                 (:instance rp-raw-add-nested-interchange
                            (x (runtime-p-raw-mul
                                (runtime-p-raw-scale (car x) y p) z p))
                            (y (runtime-p-raw-scale 0 z p))
                            (z (cons 0
                                     (runtime-p-raw-mul
                                      (runtime-p-raw-mul (cdr x) y p) z p))))
                 (:instance rp-raw-add-zero-scale-before-product
                            (a (car x)) (y y) (z z)
                            (rest (cons 0
                                        (runtime-p-raw-mul
                                         (runtime-p-raw-mul (cdr x) y p)
                                         z p)))))))))

(local (defthm rp-coefficient-list-p-of-normalize
  (runtime-p-coefficient-list-p (runtime-p-normalize x p) p)
  :hints (("Goal" :use ((:instance
                          runtime-p-canonical-polynomial-p-of-normalize
                          (xs x)))
           :in-theory (enable runtime-p-canonical-polynomial-p)))))
(local (defthm rp-normalize-raw-add-normalize-left
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p))
           (equal (runtime-p-normalize
                   (runtime-p-raw-add (runtime-p-normalize x p) y p) p)
                  (runtime-p-normalize (runtime-p-raw-add x y p) p)))
  :hints (("Goal" :induct (runtime-p-raw-add x y p)))))
(local (defthm rp-normalize-raw-add-normalize-right
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p))
           (equal (runtime-p-normalize
                   (runtime-p-raw-add x (runtime-p-normalize y p) p) p)
                  (runtime-p-normalize (runtime-p-raw-add x y p) p)))
  :hints (("Goal"
           :use ((:instance rp-normalize-raw-add-normalize-left
                            (x y) (y x))
                 (:instance rp-raw-add-commutative
                            (x (runtime-p-normalize y p)) (y x))
                 (:instance rp-raw-add-commutative))
           :in-theory (disable rp-normalize-raw-add-normalize-left)))))
(local (defthm rp-normalize-raw-scale-of-normalize
  (equal (runtime-p-normalize
          (runtime-p-raw-scale a (runtime-p-normalize x p) p) p)
         (runtime-p-normalize (runtime-p-raw-scale a x p) p))
  :hints (("Goal" :induct (runtime-p-raw-scale a x p)))))
(local (defthm rp-normalize-raw-add-congruence
  (implies (and (runtime-p-coefficient-list-p a p)
                (runtime-p-coefficient-list-p b p)
                (runtime-p-coefficient-list-p c p)
                (runtime-p-coefficient-list-p d p)
                (equal (runtime-p-normalize a p)
                       (runtime-p-normalize c p))
                (equal (runtime-p-normalize b p)
                       (runtime-p-normalize d p)))
           (equal (runtime-p-normalize (runtime-p-raw-add a b p) p)
                  (runtime-p-normalize (runtime-p-raw-add c d p) p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance rp-normalize-raw-add-normalize-left (x a) (y b))
                 (:instance rp-normalize-raw-add-normalize-right
                            (x (runtime-p-normalize a p)) (y b))
                 (:instance rp-normalize-raw-add-normalize-left (x c) (y d))
                 (:instance rp-normalize-raw-add-normalize-right
                            (x (runtime-p-normalize c p)) (y d)))))))
(local (defthm rp-normalize-raw-mul-normalize-right
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p))
           (equal (runtime-p-normalize
                   (runtime-p-raw-mul x (runtime-p-normalize y p) p) p)
                  (runtime-p-normalize (runtime-p-raw-mul x y p) p)))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-raw-mul x y p))
          ("Subgoal *1/2"
           :use ((:instance rp-normalize-raw-add-congruence
                            (a (runtime-p-raw-scale
                                (car x) (runtime-p-normalize y p) p))
                            (b (cons 0
                                     (runtime-p-raw-mul
                                      (cdr x) (runtime-p-normalize y p) p)))
                            (c (runtime-p-raw-scale (car x) y p))
                            (d (cons 0 (runtime-p-raw-mul (cdr x) y p))))
                 (:instance rp-normalize-raw-scale-of-normalize
                            (a (car x)) (x y)))))))

(local (defthm rp-raw-mul-right-recursion
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p)
                (runtime-p-coefficient-p a p))
           (equal (runtime-p-raw-mul x (cons a y) p)
                  (if (consp x)
                      (runtime-p-raw-add
                       (runtime-p-raw-scale a x p)
                       (cons 0 (runtime-p-raw-mul x y p)) p)
                    nil)))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable rp-mul-commutative))
          ("Subgoal *1/2.1"
           :use ((:instance rp-raw-add-nested-interchange
                            (x (runtime-p-raw-scale (car x) y p))
                            (y (runtime-p-raw-scale a (cdr x) p))
                            (z (cons 0 (runtime-p-raw-mul (cdr x) y p)))))))))
(local (defthm rp-raw-mul-commutative
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p))
           (equal (runtime-p-raw-mul x y p)
                  (runtime-p-raw-mul y x p)))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-raw-mul x y p))
          ("Subgoal *1/2"
           :use ((:instance rp-raw-mul-right-recursion
                            (x y) (a (car x)) (y (cdr x))))))))
(local (defthm rp-normalize-raw-mul-normalize-left
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p))
           (equal (runtime-p-normalize
                   (runtime-p-raw-mul (runtime-p-normalize x p) y p) p)
                  (runtime-p-normalize (runtime-p-raw-mul x y p) p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance rp-raw-mul-commutative
                            (x (runtime-p-normalize x p)) (y y))
                 (:instance rp-raw-mul-commutative (x x) (y y))
                 (:instance rp-normalize-raw-mul-normalize-right
                            (x y) (y x)))))))

(defthm runtime-p-poly-mul-associative
  (equal
   (runtime-p-poly-mul
    (runtime-p-poly-mul x y p) z p)
   (runtime-p-poly-mul
    x (runtime-p-poly-mul y z p) p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance rp-raw-mul-associative
                            (x (runtime-p-normalize x p))
                            (y (runtime-p-normalize y p))
                            (z (runtime-p-normalize z p)))
                 (:instance rp-normalize-raw-mul-normalize-left
                            (x (runtime-p-raw-mul
                                (runtime-p-normalize x p)
                                (runtime-p-normalize y p) p))
                            (y (runtime-p-normalize z p)))
                 (:instance rp-normalize-raw-mul-normalize-right
                            (x (runtime-p-normalize x p))
                            (y (runtime-p-raw-mul
                                (runtime-p-normalize y p)
                                (runtime-p-normalize z p) p))))
           :in-theory (enable runtime-p-poly-mul))))
