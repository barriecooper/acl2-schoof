(in-package "GPOLY")

(include-book "runtime-p-monic-product-leading-term")
(local (include-book "arithmetic-5/top" :dir :system))

; These raw-list facts are deliberately local.  The public seam below speaks
; only about normalized polynomials and runtime polynomial subtraction.
(local (defthm runtime-p-len-of-raw-neg
  (equal (len (runtime-p-raw-neg x p)) (len x))
  :hints (("Goal" :induct (runtime-p-raw-neg x p)
           :in-theory (enable runtime-p-raw-neg)))))

(local (defthm runtime-p-consp-of-raw-neg
  (equal (consp (runtime-p-raw-neg x p)) (consp x))
  :hints (("Goal" :in-theory (enable runtime-p-raw-neg)))))

(local (defthm runtime-p-last-of-raw-neg
  (implies (consp x)
           (equal (car (last (runtime-p-raw-neg x p)))
                  (runtime-p-neg (car (last x)) p)))
  :hints (("Goal" :induct (runtime-p-raw-neg x p)
           :in-theory (enable runtime-p-raw-neg)))))

(local (defthm runtime-p-last-of-raw-add-when-equal-len
  (implies (and (consp x) (consp y) (equal (len x) (len y)))
           (equal (car (last (runtime-p-raw-add x y p)))
                  (runtime-p-add (car (last x)) (car (last y)) p)))
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (enable runtime-p-raw-add)))))

(local (defthm runtime-p-len-of-raw-add
  (equal (len (runtime-p-raw-add x y p)) (max (len x) (len y)))
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (enable runtime-p-raw-add)))))

(local (defthm runtime-p-coefficient-list-p-of-raw-neg
  (runtime-p-coefficient-list-p (runtime-p-raw-neg x p) p)
  :hints (("Goal" :induct (runtime-p-raw-neg x p)
           :in-theory (enable runtime-p-raw-neg
                              runtime-p-coefficient-list-p)))))

(local (defthm runtime-p-neg-equal-zero
  (implies (runtime-p-coefficient-p x p)
           (equal (equal (runtime-p-neg x p) (runtime-p-zero p))
                  (equal x (runtime-p-zero p))))
  :hints (("Goal"
           :use ((:instance runtime-p-neg-double (x x))
                 (:instance runtime-p-coefficient-fix-when-recognized))
           :in-theory (disable runtime-p-neg-double)))))

(local (defthm runtime-p-raw-neg-canonical-when-canonical
  (implies (runtime-p-canonical-polynomial-p x p)
           (runtime-p-canonical-polynomial-p (runtime-p-raw-neg x p) p))
  :hints (("Goal"
           :use ((:instance runtime-p-last-of-raw-neg))
           :in-theory (enable runtime-p-canonical-polynomial-p)))))

(local (defthm runtime-p-normalize-of-raw-neg-when-canonical
  (implies (runtime-p-canonical-polynomial-p x p)
           (equal (runtime-p-normalize (runtime-p-raw-neg x p) p)
                  (runtime-p-raw-neg x p)))
  :hints (("Goal"
           :use ((:instance runtime-p-raw-neg-canonical-when-canonical)
                 (:instance runtime-p-normalize-when-canonical
                            (xs (runtime-p-raw-neg x p))))))))

(local (defthm runtime-p-coefficient-list-p-of-raw-add
  (runtime-p-coefficient-list-p (runtime-p-raw-add x y p) p)
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (enable runtime-p-raw-add
                              runtime-p-coefficient-list-p)))))

(local (defthm runtime-p-len-of-trim-strict-when-last-zero
  (implies (and (runtime-p-coefficient-list-p x p)
                (consp x)
                (equal (car (last x)) (runtime-p-zero p)))
           (< (len (runtime-p-trim-trailing-zeros x p)) (len x)))
  :rule-classes :linear
  :hints (("Goal" :induct (runtime-p-trim-trailing-zeros x p)
           :in-theory (enable runtime-p-trim-trailing-zeros
                              runtime-p-coefficient-list-p
                              runtime-p-zero)))))

(local (defthm runtime-p-last-of-raw-sub-zero
  (implies (and (runtime-p-coefficient-list-p x p)
                (runtime-p-coefficient-list-p y p)
                (consp x) (consp y)
                (equal (len x) (len y))
                (equal (car (last x)) (car (last y))))
           (equal (car (last (runtime-p-raw-add
                              x (runtime-p-raw-neg y p) p)))
                  (runtime-p-zero p)))
  :hints (("Goal"
           :use ((:instance runtime-p-last-of-raw-neg (x y))
                 (:instance runtime-p-len-of-raw-neg (x y))
                 (:instance runtime-p-consp-of-raw-neg (x y))
                 (:instance runtime-p-last-of-raw-add-when-equal-len
                            (y (runtime-p-raw-neg y p)))
                 (:instance runtime-p-add-inverse-right
                            (x (car (last y)))))
           :do-not-induct t
           :in-theory (disable runtime-p-raw-neg runtime-p-raw-add)))))

(defthm runtime-p-len-of-poly-sub-strict-when-equal-normalized-len-and-leading-equal
  (implies
   (and (consp (runtime-p-normalize x p))
        (consp (runtime-p-normalize y p))
        (equal (len (runtime-p-normalize x p))
               (len (runtime-p-normalize y p)))
        (equal (runtime-p-poly-leading-coefficient x p)
               (runtime-p-poly-leading-coefficient y p)))
   (and (runtime-p-canonical-polynomial-p (runtime-p-poly-sub x y p) p)
        (< (len (runtime-p-poly-sub x y p))
           (len (runtime-p-normalize x p)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-last-of-raw-sub-zero
                            (x (runtime-p-normalize x p))
                            (y (runtime-p-normalize y p)))
                 (:instance runtime-p-len-of-trim-strict-when-last-zero
                            (x (runtime-p-raw-add
                                (runtime-p-normalize x p)
                                (runtime-p-raw-neg
                                 (runtime-p-normalize y p) p) p)))
                 (:instance runtime-p-len-of-raw-add
                            (x (runtime-p-normalize x p))
                            (y (runtime-p-raw-neg
                                (runtime-p-normalize y p) p)))
                 (:instance runtime-p-len-of-raw-neg
                            (x (runtime-p-normalize y p))))
           :in-theory (enable runtime-p-poly-sub runtime-p-poly-add
                              runtime-p-poly-neg
                              runtime-p-normalize
                              runtime-p-poly-leading-coefficient))))

(defthm runtime-p-degree-less-when-canonical-nonzero-and-len-less
  (implies (and (runtime-p-canonical-polynomial-p x p)
                (runtime-p-canonical-polynomial-p y p)
                (consp x) (consp y)
                (< (len y) (len x)))
           (< (runtime-p-poly-degree y p)
              (runtime-p-poly-degree x p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-degree-when-canonical-nonzero
                            (poly x))
                 (:instance runtime-p-poly-degree-when-canonical-nonzero
                            (poly y)))
           :in-theory (disable runtime-p-poly-degree
                               runtime-p-canonical-polynomial-p))))

(defthm runtime-p-active-monic-subtraction-properties
  (implies
   (and (consp (runtime-p-normalize remainder p))
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p))
        (<= (runtime-p-poly-degree divisor p)
            (runtime-p-poly-degree remainder p)))
   (let* ((term
           (runtime-p-poly-monomial
            (runtime-p-poly-leading-coefficient remainder p)
            (- (runtime-p-poly-degree remainder p)
               (runtime-p-poly-degree divisor p))
            p))
          (product (runtime-p-poly-mul term divisor p))
          (next (runtime-p-poly-sub remainder product p)))
     (and (runtime-p-canonical-polynomial-p next p)
          (equal (runtime-p-poly-add product next p)
                 (runtime-p-normalize remainder p))
          (< (len next) (len (runtime-p-normalize remainder p)))
          (or (not (consp next))
              (< (runtime-p-poly-degree next p)
                 (runtime-p-poly-degree remainder p))))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((consp
                    (runtime-p-poly-sub
                     remainder
                     (runtime-p-poly-mul
                      (runtime-p-poly-monomial
                       (runtime-p-poly-leading-coefficient remainder p)
                       (- (runtime-p-poly-degree remainder p)
                          (runtime-p-poly-degree divisor p)) p)
                      divisor p) p)))
           :use ((:instance runtime-p-monic-product-leading-term-properties)
                 (:instance
                  runtime-p-len-of-poly-sub-strict-when-equal-normalized-len-and-leading-equal
                  (x remainder)
                  (y (runtime-p-poly-mul
                      (runtime-p-poly-monomial
                       (runtime-p-poly-leading-coefficient remainder p)
                       (- (runtime-p-poly-degree remainder p)
                          (runtime-p-poly-degree divisor p)) p)
                      divisor p)))
                 (:instance runtime-p-poly-sub-reconstruction
                            (x remainder)
                            (y (runtime-p-poly-mul
                                (runtime-p-poly-monomial
                                 (runtime-p-poly-leading-coefficient remainder p)
                                 (- (runtime-p-poly-degree remainder p)
                                    (runtime-p-poly-degree divisor p)) p)
                                divisor p)))
                 (:instance runtime-p-poly-add-commutative
                            (x (runtime-p-poly-sub
                                remainder
                                (runtime-p-poly-mul
                                 (runtime-p-poly-monomial
                                  (runtime-p-poly-leading-coefficient remainder p)
                                  (- (runtime-p-poly-degree remainder p)
                                     (runtime-p-poly-degree divisor p)) p)
                                 divisor p) p))
                            (y (runtime-p-poly-mul
                                (runtime-p-poly-monomial
                                 (runtime-p-poly-leading-coefficient remainder p)
                                 (- (runtime-p-poly-degree remainder p)
                                    (runtime-p-poly-degree divisor p)) p)
                                divisor p)))
                 (:instance runtime-p-canonical-polynomial-p-of-poly-sub
                            (x remainder)
                            (y (runtime-p-poly-mul
                                (runtime-p-poly-monomial
                                 (runtime-p-poly-leading-coefficient remainder p)
                                 (- (runtime-p-poly-degree remainder p)
                                    (runtime-p-poly-degree divisor p)) p)
                                divisor p)))
                 (:instance runtime-p-canonical-polynomial-p-of-normalize
                            (xs remainder))
                 (:instance runtime-p-normalize-when-canonical
                            (xs (runtime-p-poly-mul
                                 (runtime-p-poly-monomial
                                  (runtime-p-poly-leading-coefficient remainder p)
                                  (- (runtime-p-poly-degree remainder p)
                                     (runtime-p-poly-degree divisor p)) p)
                                 divisor p)))
                 (:instance runtime-p-poly-degree-of-normalize
                            (poly remainder))
                 (:instance runtime-p-degree-less-when-canonical-nonzero-and-len-less
                            (x (runtime-p-normalize remainder p))
                            (y (runtime-p-poly-sub
                                remainder
                                (runtime-p-poly-mul
                                 (runtime-p-poly-monomial
                                  (runtime-p-poly-leading-coefficient remainder p)
                                  (- (runtime-p-poly-degree remainder p)
                                     (runtime-p-poly-degree divisor p)) p)
                                 divisor p) p))))
           :in-theory (theory 'minimal-theory))))
