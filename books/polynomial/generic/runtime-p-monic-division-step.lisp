(in-package "GPOLY")

(include-book "runtime-p-active-monic-subtraction")

; The core receives canonical inputs from the public wrapper.  Keeping the
; normalization outside makes that wrapper's raw-input contract explicit while
; retaining a single calculation for the pair and both projections.
(defun runtime-p-monic-division-step-core (remainder divisor p)
  (declare (xargs :guard t))
  (if (and (consp remainder)
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
        (cons term (runtime-p-poly-sub remainder product p)))
    (cons nil remainder)))

(defun runtime-p-monic-division-step (remainder divisor p)
  (declare (xargs :guard t))
  (runtime-p-monic-division-step-core
   (runtime-p-normalize remainder p)
   (runtime-p-normalize divisor p)
   p))

(defun runtime-p-monic-division-step-term (remainder divisor p)
  (declare (xargs :guard t))
  (car (runtime-p-monic-division-step remainder divisor p)))

(defun runtime-p-monic-division-step-next (remainder divisor p)
  (declare (xargs :guard t))
  (cdr (runtime-p-monic-division-step remainder divisor p)))

(verify-guards runtime-p-monic-division-step-core)
(verify-guards runtime-p-monic-division-step)
(verify-guards runtime-p-monic-division-step-term)
(verify-guards runtime-p-monic-division-step-next)

(defthm runtime-p-monic-division-step-of-normalize
  (equal (runtime-p-monic-division-step
          (runtime-p-normalize remainder p)
          (runtime-p-normalize divisor p) p)
         (runtime-p-monic-division-step remainder divisor p)))


(defthm runtime-p-monic-division-step-active
  (implies
   (and (consp (runtime-p-normalize remainder p))
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p))
        (<= (runtime-p-poly-degree divisor p)
            (runtime-p-poly-degree remainder p)))
   (equal
    (runtime-p-monic-division-step remainder divisor p)
    (let* ((term
            (runtime-p-poly-monomial
             (runtime-p-poly-leading-coefficient remainder p)
             (- (runtime-p-poly-degree remainder p)
                (runtime-p-poly-degree divisor p)) p))
           (product (runtime-p-poly-mul term divisor p)))
      (cons term (runtime-p-poly-sub remainder product p)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-monic-division-step
                                      runtime-p-monic-division-step-core))))

(defthm runtime-p-monic-division-step-inactive
  (implies
   (or (not (consp (runtime-p-normalize remainder p)))
       (not (equal (runtime-p-poly-leading-coefficient divisor p)
                   (runtime-p-one p)))
       (< (runtime-p-poly-degree remainder p)
          (runtime-p-poly-degree divisor p)))
   (equal (runtime-p-monic-division-step remainder divisor p)
          (cons nil (runtime-p-normalize remainder p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-monic-division-step
                                      runtime-p-monic-division-step-core))))

(defthm runtime-p-monic-division-step-projection-equations
  (and (equal (runtime-p-monic-division-step-term remainder divisor p)
              (car (runtime-p-monic-division-step remainder divisor p)))
       (equal (runtime-p-monic-division-step-next remainder divisor p)
              (cdr (runtime-p-monic-division-step remainder divisor p))))
  :rule-classes nil)

(defthm runtime-p-monic-division-step-term-active-properties
  (implies
   (and (consp (runtime-p-normalize remainder p))
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p))
        (<= (runtime-p-poly-degree divisor p)
            (runtime-p-poly-degree remainder p)))
   (let ((term (runtime-p-monic-division-step-term remainder divisor p)))
     (and (runtime-p-canonical-polynomial-p term p)
          (consp term)
          (equal (runtime-p-poly-degree term p)
                 (- (runtime-p-poly-degree remainder p)
                    (runtime-p-poly-degree divisor p)))
          (equal (runtime-p-poly-leading-coefficient term p)
                 (runtime-p-poly-leading-coefficient remainder p)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-division-step-active)
                 (:instance runtime-p-poly-leading-coefficient-equal-zero
                            (poly remainder))
                 (:instance runtime-p-coefficient-p-of-poly-leading-coefficient
                            (poly remainder))
                 (:instance runtime-p-coefficient-fix-when-recognized
                            (x (runtime-p-poly-leading-coefficient remainder p)))
                 (:instance runtime-p-poly-degree-of-poly-monomial
                            (a (runtime-p-poly-leading-coefficient remainder p))
                            (n (- (runtime-p-poly-degree remainder p)
                                  (runtime-p-poly-degree divisor p))))
                 (:instance runtime-p-poly-leading-coefficient-of-poly-monomial
                            (a (runtime-p-poly-leading-coefficient remainder p))
                            (n (- (runtime-p-poly-degree remainder p)
                                  (runtime-p-poly-degree divisor p)))))
           :in-theory (enable runtime-p-monic-division-step-term))))

(defthm runtime-p-monic-division-step-term-inactive
  (implies
   (or (not (consp (runtime-p-normalize remainder p)))
       (not (equal (runtime-p-poly-leading-coefficient divisor p)
                   (runtime-p-one p)))
       (< (runtime-p-poly-degree remainder p)
          (runtime-p-poly-degree divisor p)))
   (equal (runtime-p-monic-division-step-term remainder divisor p) nil))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-monic-division-step-inactive))
           :in-theory (enable runtime-p-monic-division-step-term))))


(local (defthm runtime-p-canonical-polynomial-p-of-nil-for-step
  (runtime-p-canonical-polynomial-p nil p)
  :hints (("Goal" :in-theory (enable runtime-p-canonical-polynomial-p
                                     runtime-p-coefficient-list-p)))))

(defthm runtime-p-monic-division-step-output-canonical
  (and (runtime-p-canonical-polynomial-p
        (runtime-p-monic-division-step-term remainder divisor p) p)
       (runtime-p-canonical-polynomial-p
        (runtime-p-monic-division-step-next remainder divisor p) p))
  :rule-classes nil
  :hints (("Goal"
           :cases ((and (consp (runtime-p-normalize remainder p))
                        (equal (runtime-p-poly-leading-coefficient divisor p)
                               (runtime-p-one p))
                        (<= (runtime-p-poly-degree divisor p)
                            (runtime-p-poly-degree remainder p))))
           :use ((:instance runtime-p-active-monic-subtraction-properties)
                 (:instance runtime-p-monic-division-step-active)
                 (:instance runtime-p-monic-division-step-inactive)
                 (:instance runtime-p-canonical-polynomial-p-of-poly-monomial
                            (a (runtime-p-poly-leading-coefficient remainder p))
                            (n (- (runtime-p-poly-degree remainder p)
                                  (runtime-p-poly-degree divisor p))))
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
                 (:instance runtime-p-canonical-polynomial-p-of-nil-for-step))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(runtime-p-monic-division-step-term
                         runtime-p-monic-division-step-next
                         car-cons cdr-cons)))))

(local (defthm runtime-p-monic-division-step-inactive-reconstruction
  (implies
   (or (not (consp (runtime-p-normalize remainder p)))
       (not (equal (runtime-p-poly-leading-coefficient divisor p)
                   (runtime-p-one p)))
       (< (runtime-p-poly-degree remainder p)
          (runtime-p-poly-degree divisor p)))
   (equal
    (runtime-p-poly-add
     (runtime-p-poly-mul
      (runtime-p-monic-division-step-term remainder divisor p)
      (runtime-p-normalize divisor p) p)
     (runtime-p-monic-division-step-next remainder divisor p) p)
    (runtime-p-normalize remainder p)))
  :hints (("Goal"
           :use ((:instance runtime-p-monic-division-step-inactive)
                 (:instance runtime-p-poly-mul-zero-left
                            (x (runtime-p-normalize divisor p)))
                 (:instance runtime-p-poly-add-zero-left
                            (x (runtime-p-normalize remainder p)))
                 (:instance runtime-p-normalize-idempotent
                            (xs remainder)))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(runtime-p-monic-division-step-term
                         runtime-p-monic-division-step-next
                         car-cons cdr-cons))))))

(defthm runtime-p-monic-division-step-reconstruction
  (equal
   (runtime-p-poly-add
    (runtime-p-poly-mul
     (runtime-p-monic-division-step-term remainder divisor p)
     (runtime-p-normalize divisor p) p)
    (runtime-p-monic-division-step-next remainder divisor p) p)
   (runtime-p-normalize remainder p))
  :rule-classes nil
  :hints (("Goal"
           :cases ((and (consp (runtime-p-normalize remainder p))
                        (equal (runtime-p-poly-leading-coefficient divisor p)
                               (runtime-p-one p))
                        (<= (runtime-p-poly-degree divisor p)
                            (runtime-p-poly-degree remainder p))))
           :use ((:instance runtime-p-active-monic-subtraction-properties)
                 (:instance runtime-p-monic-division-step-active)
                 (:instance runtime-p-poly-mul-of-normalizes
                            (x (runtime-p-poly-monomial
                                (runtime-p-poly-leading-coefficient remainder p)
                                (- (runtime-p-poly-degree remainder p)
                                   (runtime-p-poly-degree divisor p)) p))
                            (y divisor))
                 (:instance runtime-p-normalize-of-poly-monomial
                            (a (runtime-p-poly-leading-coefficient remainder p))
                            (n (- (runtime-p-poly-degree remainder p)
                                  (runtime-p-poly-degree divisor p))))
                 (:instance runtime-p-monic-division-step-inactive-reconstruction))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(runtime-p-monic-division-step-term
                         runtime-p-monic-division-step-next
                         car-cons cdr-cons)))))

(defthm runtime-p-monic-division-step-active-length-decreases
  (implies
   (and (consp (runtime-p-normalize remainder p))
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p))
        (<= (runtime-p-poly-degree divisor p)
            (runtime-p-poly-degree remainder p)))
   (< (len (runtime-p-monic-division-step-next remainder divisor p))
      (len (runtime-p-normalize remainder p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-active-monic-subtraction-properties)
                 (:instance runtime-p-monic-division-step-active))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(runtime-p-monic-division-step-next cdr-cons)))))

(defthm runtime-p-monic-division-step-active-degree-decreases
  (implies
   (and (consp (runtime-p-normalize remainder p))
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p))
        (<= (runtime-p-poly-degree divisor p)
            (runtime-p-poly-degree remainder p)))
   (let ((next (runtime-p-monic-division-step-next remainder divisor p)))
     (or (not (consp next))
         (< (runtime-p-poly-degree next p)
            (runtime-p-poly-degree remainder p)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-active-monic-subtraction-properties)
                 (:instance runtime-p-monic-division-step-active))
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(runtime-p-monic-division-step-next cdr-cons)))))
