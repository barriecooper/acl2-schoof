(in-package "GPOLY")

(include-book "runtime-p-coefficient-inverse")
(include-book "runtime-p-active-monic-subtraction")
(local (include-book "arithmetic-5/top" :dir :system))

(defun runtime-p-division-step-core (remainder divisor p)
  (declare (xargs :guard t))
  (if (and (consp remainder) (consp divisor)
           (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                 (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                  (runtime-p-one p))
           (<= (runtime-p-poly-degree divisor p)
               (runtime-p-poly-degree remainder p)))
      (let* ((coefficient (runtime-p-mul
                           (runtime-p-poly-leading-coefficient remainder p)
                           (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p))
             (term (runtime-p-poly-monomial coefficient
                    (- (runtime-p-poly-degree remainder p)
                       (runtime-p-poly-degree divisor p)) p))
             (product (runtime-p-poly-mul term divisor p)))
        (cons term (runtime-p-poly-sub remainder product p)))
    (cons nil remainder)))

(defun runtime-p-division-step (remainder divisor p)
  (declare (xargs :guard t))
  (runtime-p-division-step-core (runtime-p-normalize remainder p)
                                (runtime-p-normalize divisor p) p))
(defun runtime-p-division-step-term (remainder divisor p)
  (declare (xargs :guard t)) (car (runtime-p-division-step remainder divisor p)))
(defun runtime-p-division-step-next (remainder divisor p)
  (declare (xargs :guard t)) (cdr (runtime-p-division-step remainder divisor p)))
(verify-guards runtime-p-division-step-core)
(verify-guards runtime-p-division-step)
(verify-guards runtime-p-division-step-term)
(verify-guards runtime-p-division-step-next)

(defthm runtime-p-division-step-of-normalize
  (equal (runtime-p-division-step (runtime-p-normalize remainder p)
                                  (runtime-p-normalize divisor p) p)
         (runtime-p-division-step remainder divisor p)))

(defthm runtime-p-division-step-active
  (implies (and (consp (runtime-p-normalize remainder p))
                (consp (runtime-p-normalize divisor p))
                (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (runtime-p-one p))
                (<= (runtime-p-poly-degree divisor p) (runtime-p-poly-degree remainder p)))
           (equal (runtime-p-division-step remainder divisor p)
                  (let* ((coefficient (runtime-p-mul
                         (runtime-p-poly-leading-coefficient remainder p)
                         (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p))
                         (term (runtime-p-poly-monomial coefficient
                         (- (runtime-p-poly-degree remainder p)
                            (runtime-p-poly-degree divisor p)) p)))
                    (cons term (runtime-p-poly-sub remainder
                                (runtime-p-poly-mul term divisor p) p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-division-step runtime-p-division-step-core))))

(defthm runtime-p-division-step-inactive
  (implies (or (not (consp (runtime-p-normalize remainder p)))
               (not (consp (runtime-p-normalize divisor p)))
               (not (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                           (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                           (runtime-p-one p)))
               (< (runtime-p-poly-degree remainder p) (runtime-p-poly-degree divisor p)))
           (equal (runtime-p-division-step remainder divisor p)
                  (cons nil (runtime-p-normalize remainder p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-division-step runtime-p-division-step-core))))

(defthm runtime-p-division-step-projection-equations
  (and (equal (runtime-p-division-step-term remainder divisor p)
              (car (runtime-p-division-step remainder divisor p)))
       (equal (runtime-p-division-step-next remainder divisor p)
              (cdr (runtime-p-division-step remainder divisor p))))
  :rule-classes nil)

(defthm runtime-p-division-step-term-equation
  (equal (runtime-p-division-step-term remainder divisor p)
         (car (runtime-p-division-step remainder divisor p)))
  :hints (("Goal" :in-theory (enable runtime-p-division-step-term))))

(defthm runtime-p-division-step-next-equation
  (equal (runtime-p-division-step-next remainder divisor p)
         (cdr (runtime-p-division-step remainder divisor p)))
  :hints (("Goal" :in-theory (enable runtime-p-division-step-next))))

(local (defthm runtime-p-division-step-top-equality
  (implies (and (runtime-p-coefficient-p r p)
                (equal (runtime-p-mul d (runtime-p-inv d p) p) (runtime-p-one p)))
           (equal (runtime-p-mul (runtime-p-mul r (runtime-p-inv d p) p) d p) r))
  :hints (("Goal" :use ((:instance runtime-p-mul-associative
                          (x r) (y (runtime-p-inv d p)) (z d))
                         (:instance runtime-p-mul-commutative
                          (x (runtime-p-inv d p)) (y d))
                         (:instance runtime-p-mul-one-right (x r))
                         (:instance runtime-p-coefficient-fix-when-recognized (x r)))
           :in-theory (theory 'minimal-theory)))))

(local (defthm runtime-p-division-step-degree-arithmetic
  (implies (and (natp rdegree) (natp ddegree) (<= ddegree rdegree))
           (and (equal (nfix (- rdegree ddegree)) (- rdegree ddegree))
                (equal (+ (- rdegree ddegree) ddegree) rdegree)))
  :rule-classes nil))

(local (defthm runtime-p-division-step-length-arithmetic
  (implies (and (natp rdegree) (natp ddegree)
                (<= ddegree rdegree)
                (equal rlen (+ 1 rdegree))
                (equal dlen (+ 1 ddegree)))
           (equal (+ (- rdegree ddegree) dlen) rlen))
  :rule-classes nil))

(defthm runtime-p-division-step-active-product-properties
  (implies (and (consp (runtime-p-normalize remainder p))
                (consp (runtime-p-normalize divisor p))
                (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (runtime-p-one p))
                (<= (runtime-p-poly-degree divisor p) (runtime-p-poly-degree remainder p)))
    (let* ((coefficient (runtime-p-mul
             (runtime-p-poly-leading-coefficient remainder p)
             (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p))
           (shift (- (runtime-p-poly-degree remainder p)
                     (runtime-p-poly-degree divisor p)))
           (product (runtime-p-poly-mul
                     (runtime-p-poly-monomial coefficient shift p) divisor p)))
      (and (runtime-p-canonical-polynomial-p product p)
           (consp product)
           (equal (runtime-p-poly-degree product p)
                  (runtime-p-poly-degree remainder p))
           (equal (runtime-p-poly-leading-coefficient product p)
                  (runtime-p-poly-leading-coefficient remainder p))
           (equal (len product) (len (runtime-p-normalize remainder p))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-division-step-top-equality
                  (r (runtime-p-poly-leading-coefficient remainder p))
                 (d (runtime-p-poly-leading-coefficient divisor p)))
                 (:instance runtime-p-coefficient-p-of-poly-leading-coefficient
                  (poly remainder))
                 (:instance runtime-p-coefficient-p-of-inv
                  (x (runtime-p-poly-leading-coefficient divisor p)))
                 (:instance runtime-p-coefficient-p-of-mul
                  (x (runtime-p-poly-leading-coefficient remainder p))
                  (y (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p)))
                 (:instance runtime-p-coefficient-fix-when-recognized
                  (x (runtime-p-mul
                      (runtime-p-poly-leading-coefficient remainder p)
                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)))
                 (:instance runtime-p-poly-leading-coefficient-equal-zero
                  (poly remainder))
                 (:instance runtime-p-canonical-polynomial-p-of-normalize (xs remainder))
                 (:instance runtime-p-poly-mul-nonzero-monomial-properties
                  (coefficient (runtime-p-mul
                    (runtime-p-poly-leading-coefficient remainder p)
                    (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p))
                  (exponent (- (runtime-p-poly-degree remainder p)
                               (runtime-p-poly-degree divisor p)))
                  (divisor divisor))
                 (:instance runtime-p-poly-degree-when-canonical-nonzero
                  (poly (runtime-p-normalize remainder p)))
                 (:instance runtime-p-poly-degree-when-canonical-nonzero
                  (poly (runtime-p-normalize divisor p)))
                 (:instance runtime-p-poly-degree-of-normalize (poly remainder))
                 (:instance runtime-p-poly-degree-of-normalize (poly divisor))
                 (:instance runtime-p-poly-mul-of-normalizes
                  (x (runtime-p-poly-monomial
                      (runtime-p-mul
                       (runtime-p-poly-leading-coefficient remainder p)
                       (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                      (- (runtime-p-poly-degree remainder p)
                         (runtime-p-poly-degree divisor p)) p))
                  (y divisor))
                 (:instance runtime-p-normalize-of-poly-monomial
                  (a (runtime-p-mul
                      (runtime-p-poly-leading-coefficient remainder p)
                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p))
                  (n (- (runtime-p-poly-degree remainder p)
                        (runtime-p-poly-degree divisor p))))
                 (:instance natp-of-runtime-p-poly-degree-when-normalize-nonzero
                  (poly remainder))
                 (:instance natp-of-runtime-p-poly-degree-when-normalize-nonzero
                  (poly divisor))
                 (:instance runtime-p-division-step-degree-arithmetic
                  (rdegree (runtime-p-poly-degree remainder p))
                  (ddegree (runtime-p-poly-degree divisor p)))
                 (:instance runtime-p-division-step-length-arithmetic
                  (rdegree (runtime-p-poly-degree remainder p))
                  (ddegree (runtime-p-poly-degree divisor p))
                  (rlen (len (runtime-p-normalize remainder p)))
                  (dlen (len (runtime-p-normalize divisor p)))))
           :do-not-induct t
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(runtime-p-coefficient-fix-when-recognized
                         runtime-p-canonical-polynomial-p-of-normalize
                         runtime-p-poly-leading-coefficient-of-normalize))))
)


(defthm runtime-p-division-step-term-active-properties
  (implies (and (consp (runtime-p-normalize remainder p))
                (consp (runtime-p-normalize divisor p))
                (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (runtime-p-one p))
                (<= (runtime-p-poly-degree divisor p) (runtime-p-poly-degree remainder p)))
           (let ((term (runtime-p-division-step-term remainder divisor p)))
             (and (runtime-p-canonical-polynomial-p term p)
                  (consp term)
                  (equal (runtime-p-poly-degree term p)
                         (- (runtime-p-poly-degree remainder p)
                            (runtime-p-poly-degree divisor p)))
                  (equal (runtime-p-poly-leading-coefficient term p)
                         (runtime-p-mul
                          (runtime-p-poly-leading-coefficient remainder p)
                          (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-division-step-active)
                          (:instance runtime-p-division-step-top-equality
                           (r (runtime-p-poly-leading-coefficient remainder p))
                           (d (runtime-p-poly-leading-coefficient divisor p)))
                          (:instance runtime-p-coefficient-p-of-poly-leading-coefficient (poly remainder))
                          (:instance runtime-p-coefficient-p-of-inv
                           (x (runtime-p-poly-leading-coefficient divisor p)))
                          (:instance runtime-p-coefficient-p-of-mul
                           (x (runtime-p-poly-leading-coefficient remainder p))
                           (y (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p)))
                          (:instance runtime-p-poly-leading-coefficient-equal-zero (poly remainder))
                          (:instance runtime-p-poly-degree-of-poly-monomial
                           (a (runtime-p-mul (runtime-p-poly-leading-coefficient remainder p)
                                             (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p))
                           (n (- (runtime-p-poly-degree remainder p)
                                 (runtime-p-poly-degree divisor p))))
                          (:instance runtime-p-poly-leading-coefficient-of-poly-monomial
                           (a (runtime-p-mul (runtime-p-poly-leading-coefficient remainder p)
                                             (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p))
                           (n (- (runtime-p-poly-degree remainder p)
                                 (runtime-p-poly-degree divisor p)))))
           :in-theory (enable runtime-p-division-step-term))))

(local (defthm runtime-p-canonical-polynomial-p-of-nil-for-division-step
  (runtime-p-canonical-polynomial-p nil p)
  :hints (("Goal" :in-theory (enable runtime-p-canonical-polynomial-p
                                     runtime-p-coefficient-list-p)))))

(defthm runtime-p-division-step-output-canonical
  (and (runtime-p-canonical-polynomial-p
        (runtime-p-division-step-term remainder divisor p) p)
       (runtime-p-canonical-polynomial-p
        (runtime-p-division-step-next remainder divisor p) p))
  :rule-classes nil
  :hints (("Goal"
           :cases ((and (consp (runtime-p-normalize remainder p))
                        (consp (runtime-p-normalize divisor p))
                        (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                              (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                               (runtime-p-one p))
                        (<= (runtime-p-poly-degree divisor p)
                            (runtime-p-poly-degree remainder p))))
           :use ((:instance runtime-p-division-step-active)
                 (:instance runtime-p-division-step-inactive)
                 (:instance runtime-p-division-step-term-active-properties)
                 (:instance runtime-p-canonical-polynomial-p-of-poly-sub
                  (x remainder)
                  (y (runtime-p-poly-mul
                      (runtime-p-division-step-term remainder divisor p)
                      divisor p)))
                 (:instance runtime-p-canonical-polynomial-p-of-normalize (xs remainder))
                 (:instance runtime-p-canonical-polynomial-p-of-nil-for-division-step))
           :in-theory (union-theories (theory 'minimal-theory)
             '(runtime-p-division-step-term runtime-p-division-step-next car-cons cdr-cons)))))

(defthm runtime-p-division-step-term-active-equation
  (implies (and (consp (runtime-p-normalize remainder p))
                (consp (runtime-p-normalize divisor p))
                (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (runtime-p-one p))
                (<= (runtime-p-poly-degree divisor p) (runtime-p-poly-degree remainder p)))
           (equal (runtime-p-division-step-term remainder divisor p) (runtime-p-poly-monomial
            (runtime-p-mul (runtime-p-poly-leading-coefficient remainder p)
                           (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
            (- (runtime-p-poly-degree remainder p)
               (runtime-p-poly-degree divisor p)) p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-division-step-active))
           :in-theory (enable runtime-p-division-step-term))))

(defthm runtime-p-division-step-next-active-equation
  (implies (and (consp (runtime-p-normalize remainder p))
                (consp (runtime-p-normalize divisor p))
                (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (runtime-p-one p))
                (<= (runtime-p-poly-degree divisor p) (runtime-p-poly-degree remainder p)))
           (equal (runtime-p-division-step-next remainder divisor p)
                  (runtime-p-poly-sub remainder
                    (runtime-p-poly-mul (runtime-p-poly-monomial
            (runtime-p-mul (runtime-p-poly-leading-coefficient remainder p)
                           (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
            (- (runtime-p-poly-degree remainder p)
               (runtime-p-poly-degree divisor p)) p) divisor p) p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-division-step-active))
           :in-theory (enable runtime-p-division-step-next))))

(defthm runtime-p-division-step-active-reconstruction
  (implies (and (consp (runtime-p-normalize remainder p))
                (consp (runtime-p-normalize divisor p))
                (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (runtime-p-one p))
                (<= (runtime-p-poly-degree divisor p) (runtime-p-poly-degree remainder p)))
   (equal (runtime-p-poly-add
           (runtime-p-poly-mul (runtime-p-division-step-term remainder divisor p)
                               (runtime-p-normalize divisor p) p)
           (runtime-p-division-step-next remainder divisor p) p)
          (runtime-p-normalize remainder p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-division-step-term-active-equation)
                 (:instance runtime-p-division-step-next-active-equation)
                 (:instance runtime-p-division-step-active)
                 (:instance runtime-p-division-step-active
                  (remainder (runtime-p-normalize remainder p))
                  (divisor (runtime-p-normalize divisor p)))
                 (:instance runtime-p-division-step-of-normalize)
                 (:instance runtime-p-division-step-projection-equations)
                 (:instance runtime-p-division-step-term-equation)
                 (:instance runtime-p-division-step-next-equation)
                 (:instance runtime-p-poly-add-commutative
                  (x (runtime-p-poly-mul
                      (runtime-p-division-step-term remainder divisor p) divisor p))
                  (y (runtime-p-division-step-next remainder divisor p)))
                 (:instance runtime-p-poly-sub-reconstruction
                  (x remainder)
                  (y (runtime-p-poly-mul
                      (runtime-p-poly-monomial
                       (runtime-p-mul
                        (runtime-p-poly-leading-coefficient remainder p)
                        (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (- (runtime-p-poly-degree remainder p)
                          (runtime-p-poly-degree divisor p)) p)
                      divisor p)))
                 (:instance runtime-p-poly-sub-of-normalizes
                  (x remainder)
                  (y (runtime-p-poly-mul
                      (runtime-p-poly-monomial
                       (runtime-p-mul
                        (runtime-p-poly-leading-coefficient remainder p)
                        (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (- (runtime-p-poly-degree remainder p)
                          (runtime-p-poly-degree divisor p)) p)
                      divisor p)))
                 (:instance runtime-p-poly-mul-of-normalizes
                  (x (runtime-p-poly-monomial
                      (runtime-p-mul
                       (runtime-p-poly-leading-coefficient remainder p)
                       (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                      (- (runtime-p-poly-degree remainder p)
                         (runtime-p-poly-degree divisor p)) p))
                  (y divisor))
                 (:instance runtime-p-normalize-of-poly-monomial
                  (a (runtime-p-mul
                      (runtime-p-poly-leading-coefficient remainder p)
                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p))
                  (n (- (runtime-p-poly-degree remainder p)
                        (runtime-p-poly-degree divisor p)))))
           :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
             '(runtime-p-division-step-term runtime-p-division-step-next car-cons cdr-cons)))))

(defthm runtime-p-division-step-inactive-reconstruction
  (implies (or (not (consp (runtime-p-normalize remainder p)))
               (not (consp (runtime-p-normalize divisor p)))
               (not (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                           (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                           (runtime-p-one p)))
               (< (runtime-p-poly-degree remainder p) (runtime-p-poly-degree divisor p)))
   (equal (runtime-p-poly-add
           (runtime-p-poly-mul (runtime-p-division-step-term remainder divisor p)
                               (runtime-p-normalize divisor p) p)
           (runtime-p-division-step-next remainder divisor p) p)
          (runtime-p-normalize remainder p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-division-step-inactive)
                          (:instance runtime-p-poly-mul-zero-left
                           (x (runtime-p-normalize divisor p)))
                          (:instance runtime-p-poly-add-zero-left
                           (x (runtime-p-normalize remainder p)))
                          (:instance runtime-p-normalize-idempotent (xs remainder)))
           :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
             '(runtime-p-division-step-term runtime-p-division-step-next car-cons cdr-cons)))))

(defthm runtime-p-division-step-reconstruction
  (equal (runtime-p-poly-add
          (runtime-p-poly-mul (runtime-p-division-step-term remainder divisor p)
                              (runtime-p-normalize divisor p) p)
          (runtime-p-division-step-next remainder divisor p) p)
         (runtime-p-normalize remainder p))
  :rule-classes nil
  :hints (("Goal" :cases ((and (consp (runtime-p-normalize remainder p))
                                (consp (runtime-p-normalize divisor p))
                                (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                                                      (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
                                       (runtime-p-one p))
                                (<= (runtime-p-poly-degree divisor p)
                                    (runtime-p-poly-degree remainder p))))
           :use ((:instance runtime-p-division-step-active-reconstruction)
                 (:instance runtime-p-division-step-inactive-reconstruction))
           :do-not-induct t :in-theory (theory 'minimal-theory))))

