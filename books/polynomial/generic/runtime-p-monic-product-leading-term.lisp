(in-package "GPOLY")

(include-book "runtime-p-polynomial-monomial-degree")
(local (include-book "arithmetic-5/top" :dir :system))

; Proof-only structural model of multiplying an ascending polynomial by a
; monomial.  It is deliberately local: clients should reason through the
; normalization-aware public theorems below, not raw multiplication.
(local (defun runtime-p-zero-prefix (n xs)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n)) xs
    (cons 0 (runtime-p-zero-prefix (1- (nfix n)) xs)))))

(local (defun runtime-p-zero-list (n)
  (if (zp n) nil (cons 0 (runtime-p-zero-list (1- n))))))

(local (defun runtime-p-zero-list-xs-induct (n xs)
  (if (or (zp n) (atom xs)) nil
    (runtime-p-zero-list-xs-induct (1- n) (cdr xs)))))

(local (defthm runtime-p-raw-scale-zero
  (equal (runtime-p-raw-scale 0 xs p)
         (runtime-p-zero-list (len xs)))
  :hints (("Goal" :induct (runtime-p-raw-scale 0 xs p)
           :in-theory (enable runtime-p-raw-scale)))))

(local (defthm runtime-p-raw-add-zero-list-left
  (implies (and (runtime-p-coefficient-list-p xs p)
                (<= (nfix n) (len xs)))
           (equal (runtime-p-raw-add (runtime-p-zero-list n) xs p) xs))
  :hints (("Goal" :induct (runtime-p-zero-list-xs-induct n xs)
           :in-theory (enable runtime-p-raw-add
                              runtime-p-coefficient-list-p)))))

(local (defthm runtime-p-raw-add-zero-list-right
  (implies (and (runtime-p-coefficient-list-p xs p)
                (<= (nfix n) (len xs)))
           (equal (runtime-p-raw-add xs (runtime-p-zero-list n) p) xs))
  :hints (("Goal" :induct (runtime-p-zero-list-xs-induct n xs)
           :in-theory (enable runtime-p-raw-add
                              runtime-p-coefficient-list-p)))))

(local (defthm runtime-p-raw-add-single-zero-right
  (implies (and (runtime-p-coefficient-list-p xs p) (consp xs))
           (equal (runtime-p-raw-add xs '(0) p) xs))
  :hints (("Goal"
           :use ((:instance runtime-p-raw-add-zero-list-right (n 1)))
           :in-theory (enable runtime-p-zero-list)))))

(local (defthm runtime-p-raw-scale-of-fix
  (equal (runtime-p-raw-scale (runtime-p-coefficient-fix a p) xs p)
         (runtime-p-raw-scale a xs p))
  :hints (("Goal" :induct (runtime-p-raw-scale a xs p)
           :in-theory (enable runtime-p-raw-scale)))))

(local (defthm runtime-p-raw-scale-congruence
  (implies (equal (runtime-p-coefficient-fix a p)
                  (runtime-p-coefficient-fix b p))
           (equal (runtime-p-raw-scale a xs p)
                  (runtime-p-raw-scale b xs p)))
  :hints (("Goal" :induct (runtime-p-raw-scale a xs p)
           :in-theory (enable runtime-p-raw-scale)))))

(local (defthm runtime-p-coefficient-list-p-of-raw-scale
  (runtime-p-coefficient-list-p (runtime-p-raw-scale a xs p) p)
  :hints (("Goal" :induct (runtime-p-raw-scale a xs p)
           :in-theory (enable runtime-p-raw-scale
                              runtime-p-coefficient-list-p)))))

(local (defthm len-of-runtime-p-raw-scale
  (equal (len (runtime-p-raw-scale a xs p)) (len xs))
  :hints (("Goal" :induct (runtime-p-raw-scale a xs p)
           :in-theory (enable runtime-p-raw-scale)))))

(local (defthm consp-of-runtime-p-raw-scale
  (equal (consp (runtime-p-raw-scale a xs p)) (consp xs))
  :hints (("Goal" :in-theory (enable runtime-p-raw-scale)))))

(local (defthm runtime-p-coefficient-list-p-of-zero-prefix
  (implies (runtime-p-coefficient-list-p xs p)
           (runtime-p-coefficient-list-p (runtime-p-zero-prefix n xs) p))
  :hints (("Goal" :induct (runtime-p-zero-prefix n xs)
           :in-theory (enable runtime-p-zero-prefix
                              runtime-p-coefficient-list-p)))))

(local (defthm len-of-runtime-p-zero-prefix
  (equal (len (runtime-p-zero-prefix n xs))
         (+ (nfix n) (len xs)))
  :hints (("Goal" :induct (runtime-p-zero-prefix n xs)
           :in-theory (enable runtime-p-zero-prefix)))))

(local (defthm consp-of-runtime-p-zero-prefix
  (equal (consp (runtime-p-zero-prefix n xs))
         (or (not (zp (nfix n))) (consp xs)))
  :hints (("Goal" :in-theory (enable runtime-p-zero-prefix)))))

(local (defthm runtime-p-raw-mul-monomial-left
  (implies (and (runtime-p-coefficient-list-p xs p)
                (runtime-p-coefficient-p a p)
                (consp xs))
           (equal (runtime-p-raw-mul (runtime-p-poly-monomial a n p) xs p)
                  (if (equal a 0)
                      nil
                    (runtime-p-zero-prefix
                     n (runtime-p-raw-scale a xs p)))))
  :hints (("Goal" :induct (runtime-p-poly-monomial a n p)
           :in-theory (enable runtime-p-poly-monomial
                              runtime-p-zero-prefix
                              runtime-p-raw-mul))
          ("Subgoal *1/3"
           :use ((:instance runtime-p-raw-add-zero-list-left
                            (n (len xs))
                            (xs (cons 0
                                      (runtime-p-zero-prefix
                                       (1- (nfix n))
                                       (runtime-p-raw-scale
                                        (runtime-p-coefficient-fix a p)
                                        xs p)))))
                 (:instance runtime-p-raw-scale-of-fix))))))

(local (defthm last-of-runtime-p-zero-prefix
  (implies (consp xs)
           (equal (car (last (runtime-p-zero-prefix n xs)))
                  (car (last xs))))
  :hints (("Goal" :induct (runtime-p-zero-prefix n xs)
           :in-theory (enable runtime-p-zero-prefix)))))

(local (defthm last-of-runtime-p-raw-scale
  (implies (consp xs)
           (equal (car (last (runtime-p-raw-scale a xs p)))
                  (runtime-p-mul a (car (last xs)) p)))
  :hints (("Goal" :induct (runtime-p-raw-scale a xs p)
           :in-theory (enable runtime-p-raw-scale)))))

(local (defthm runtime-p-mul-by-one-right
  (equal (runtime-p-mul x (runtime-p-one p) p)
         (runtime-p-coefficient-fix x p))))

(local (defthm runtime-p-raw-monomial-product-canonical
  (implies (and (runtime-p-canonical-polynomial-p xs p)
                (consp xs)
                (not (equal (runtime-p-coefficient-fix a p) 0))
                (equal (car (last xs)) (runtime-p-one p)))
           (runtime-p-canonical-polynomial-p
            (runtime-p-raw-mul (runtime-p-poly-monomial a n p) xs p) p))
  :hints (("Goal"
           :use ((:instance runtime-p-raw-mul-monomial-left))
           :in-theory (enable runtime-p-canonical-polynomial-p)))))

(local (defthm runtime-p-raw-monomial-product-canonical-when-top-nonzero
  (implies (and (runtime-p-canonical-polynomial-p xs p)
                (consp xs)
                (not (equal (runtime-p-mul
                             (runtime-p-coefficient-fix a p)
                             (car (last xs)) p)
                            (runtime-p-zero p))))
           (runtime-p-canonical-polynomial-p
            (runtime-p-raw-mul (runtime-p-poly-monomial a n p) xs p) p))
  :hints (("Goal"
           :use ((:instance runtime-p-raw-mul-monomial-left
                            (a (runtime-p-coefficient-fix a p)))
                 (:instance last-of-runtime-p-zero-prefix
                            (xs (runtime-p-raw-scale
                                 (runtime-p-coefficient-fix a p) xs p)))
                 (:instance last-of-runtime-p-raw-scale
                            (a (runtime-p-coefficient-fix a p))))
           :in-theory (enable runtime-p-canonical-polynomial-p)))))

(local (defthm runtime-p-raw-monomial-product-properties
  (implies (and (runtime-p-canonical-polynomial-p xs p)
                (consp xs)
                (not (equal (runtime-p-mul
                             (runtime-p-coefficient-fix a p)
                             (car (last xs)) p)
                            (runtime-p-zero p))))
           (let ((raw (runtime-p-raw-mul
                       (runtime-p-poly-monomial
                        (runtime-p-coefficient-fix a p) n p) xs p)))
             (and (runtime-p-canonical-polynomial-p raw p)
                  (consp raw)
                  (equal (len raw) (+ (nfix n) (len xs)))
                  (equal (car (last raw))
                         (runtime-p-mul
                          (runtime-p-coefficient-fix a p)
                          (car (last xs)) p)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                 runtime-p-raw-monomial-product-canonical-when-top-nonzero
                  (a (runtime-p-coefficient-fix a p)))
                 (:instance runtime-p-coefficient-p-of-fix (x a))
                 (:instance runtime-p-mul-zero-left
                            (x (car (last xs))))
                 (:instance runtime-p-raw-mul-monomial-left
                            (a (runtime-p-coefficient-fix a p)))
                 (:instance len-of-runtime-p-zero-prefix
                            (xs (runtime-p-raw-scale
                                 (runtime-p-coefficient-fix a p) xs p)))
                 (:instance consp-of-runtime-p-zero-prefix
                            (xs (runtime-p-raw-scale
                                 (runtime-p-coefficient-fix a p) xs p)))
                 (:instance len-of-runtime-p-raw-scale
                            (a (runtime-p-coefficient-fix a p)))
                 (:instance consp-of-runtime-p-raw-scale
                            (a (runtime-p-coefficient-fix a p)))
                 (:instance last-of-runtime-p-zero-prefix
                            (xs (runtime-p-raw-scale
                                 (runtime-p-coefficient-fix a p) xs p)))
                 (:instance last-of-runtime-p-raw-scale
                            (a (runtime-p-coefficient-fix a p))))
           :do-not-induct t
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(runtime-p-canonical-polynomial-p
                         runtime-p-coefficient-fix-idempotent
                         runtime-p-mul-zero-left
                         runtime-p-zero
                         runtime-p-poly-monomial-of-nfix))))))

(defthm runtime-p-poly-mul-nonzero-monomial-properties
  (let* ((fixed-coefficient (runtime-p-coefficient-fix coefficient p))
         (shift (nfix exponent))
         (normalized-divisor (runtime-p-normalize divisor p))
         (term (runtime-p-poly-monomial fixed-coefficient shift p))
         (top (runtime-p-mul
               fixed-coefficient
               (runtime-p-poly-leading-coefficient normalized-divisor p) p))
         (product (runtime-p-poly-mul term normalized-divisor p)))
    (implies
     (and (consp normalized-divisor)
          (not (equal top (runtime-p-zero p))))
     (and (runtime-p-canonical-polynomial-p product p)
          (consp product)
          (equal (runtime-p-poly-degree product p)
                 (+ shift (runtime-p-poly-degree normalized-divisor p)))
          (equal (runtime-p-poly-leading-coefficient product p) top)
          (equal (len product) (+ shift (len normalized-divisor))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-raw-monomial-product-properties
                  (a (runtime-p-coefficient-fix coefficient p))
                  (n (nfix exponent))
                  (xs (runtime-p-normalize divisor p)))
                 (:instance runtime-p-canonical-polynomial-p-of-normalize
                            (xs divisor))
                 (:instance runtime-p-normalize-of-poly-monomial
                            (a (runtime-p-coefficient-fix coefficient p))
                            (n (nfix exponent)))
                 (:instance runtime-p-normalize-when-canonical
                            (xs (runtime-p-raw-mul
                                 (runtime-p-poly-monomial
                                  (runtime-p-coefficient-fix coefficient p)
                                  (nfix exponent) p)
                                 (runtime-p-normalize divisor p) p)))
                 (:instance runtime-p-poly-degree-when-canonical-nonzero
                            (poly (runtime-p-raw-mul
                                   (runtime-p-poly-monomial
                                    (runtime-p-coefficient-fix coefficient p)
                                    (nfix exponent) p)
                                   (runtime-p-normalize divisor p) p)))
                 (:instance
                  runtime-p-poly-leading-coefficient-when-canonical-nonzero
                  (poly (runtime-p-raw-mul
                         (runtime-p-poly-monomial
                          (runtime-p-coefficient-fix coefficient p)
                          (nfix exponent) p)
                         (runtime-p-normalize divisor p) p)))
                 (:instance runtime-p-poly-degree-when-canonical-nonzero
                            (poly (runtime-p-normalize divisor p)))
                 (:instance
                  runtime-p-poly-leading-coefficient-when-canonical-nonzero
                  (poly (runtime-p-normalize divisor p))))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(runtime-p-poly-mul
                         nfix
                         runtime-p-coefficient-fix-idempotent
                         runtime-p-normalize-of-poly-monomial
                         runtime-p-normalize-idempotent)))))

(defthm runtime-p-poly-mul-nonzero-monomial-by-monic-properties
  (implies
   (and (not (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p)))
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p)))
   (let ((product
          (runtime-p-poly-mul (runtime-p-poly-monomial a n p) divisor p)))
     (and (runtime-p-canonical-polynomial-p product p)
          (consp product)
          (equal (runtime-p-poly-degree product p)
                 (+ (nfix n) (runtime-p-poly-degree divisor p)))
          (equal (runtime-p-poly-leading-coefficient product p)
                 (runtime-p-coefficient-fix a p))
          (equal (len product)
                 (+ (nfix n) (len (runtime-p-normalize divisor p)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-raw-mul-monomial-left
                            (a (runtime-p-coefficient-fix a p))
                            (xs (runtime-p-normalize divisor p)))
                 (:instance runtime-p-raw-monomial-product-canonical
                            (xs (runtime-p-normalize divisor p))))
           :in-theory (enable runtime-p-poly-mul
                              runtime-p-poly-degree
                              runtime-p-poly-leading-coefficient))))

(local (defthm runtime-p-normalized-len-order-from-degree-order
  (implies (and (consp (runtime-p-normalize x p))
                (consp (runtime-p-normalize y p))
                (<= (runtime-p-poly-degree x p)
                    (runtime-p-poly-degree y p)))
           (<= (len (runtime-p-normalize x p))
               (len (runtime-p-normalize y p))))
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree)))))

(defthm runtime-p-equal-normalized-length-when-equal-degree
  (implies (and (consp (runtime-p-normalize first p))
                (consp (runtime-p-normalize second p))
                (equal (runtime-p-poly-degree first p)
                       (runtime-p-poly-degree second p)))
           (equal (len (runtime-p-normalize first p))
                  (len (runtime-p-normalize second p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree))))

(defthm runtime-p-monic-product-leading-term-properties
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
          (product (runtime-p-poly-mul term divisor p)))
     (and (runtime-p-canonical-polynomial-p product p)
          (consp product)
          (equal (runtime-p-poly-degree product p)
                 (runtime-p-poly-degree remainder p))
          (equal (runtime-p-poly-leading-coefficient product p)
                 (runtime-p-poly-leading-coefficient remainder p))
          (equal (len product)
                 (len (runtime-p-normalize remainder p))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  runtime-p-poly-mul-nonzero-monomial-by-monic-properties
                  (a (runtime-p-poly-leading-coefficient remainder p))
                  (n (- (runtime-p-poly-degree remainder p)
                        (runtime-p-poly-degree divisor p))))
                 (:instance runtime-p-normalized-len-order-from-degree-order
                            (x divisor) (y remainder))
                 (:instance runtime-p-poly-leading-coefficient-equal-zero
                            (poly divisor))
                 (:instance runtime-p-poly-leading-coefficient-equal-zero
                            (poly remainder))
                 (:instance runtime-p-coefficient-p-of-poly-leading-coefficient
                            (poly remainder))
                 (:instance runtime-p-coefficient-fix-when-recognized
                            (x (runtime-p-poly-leading-coefficient remainder p)))
                 (:instance runtime-p-equal-normalized-length-when-equal-degree
                            (first
                             (runtime-p-poly-mul
                              (runtime-p-poly-monomial
                               (runtime-p-poly-leading-coefficient remainder p)
                               (- (runtime-p-poly-degree remainder p)
                                  (runtime-p-poly-degree divisor p))
                               p)
                              divisor p))
                            (second remainder)))
           :in-theory (enable runtime-p-zero runtime-p-one))))
