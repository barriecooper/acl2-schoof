(in-package "GPOLY")

(include-book "runtime-p-division-step")


(local
 (defthm runtime-p-divmod-active-length-decreases
   (implies
    (and (runtime-p-canonical-polynomial-p remainder p)
         (runtime-p-canonical-polynomial-p divisor p)
         (consp remainder)
         (consp divisor)
         (equal (runtime-p-mul
                 (runtime-p-poly-leading-coefficient divisor p)
                 (runtime-p-inv
                  (runtime-p-poly-leading-coefficient divisor p) p) p)
                (runtime-p-one p))
         (<= (runtime-p-poly-degree divisor p)
             (runtime-p-poly-degree remainder p)))
    (< (len (cdr (runtime-p-division-step remainder divisor p)))
       (len remainder)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance runtime-p-division-step-active-length-decreases)
                  (:instance runtime-p-division-step-next-equation)
                  (:instance runtime-p-normalize-when-canonical (xs remainder))
                  (:instance runtime-p-normalize-when-canonical (xs divisor)))
            :in-theory (theory 'minimal-theory)))))

; The state is canonical.  Each active branch binds the public step once and
; reuses both of its coordinates.
(defun runtime-p-divmod-core (quotient remainder divisor p)
  (declare
   (xargs :guard t
          :measure (len remainder)
          :hints (("Goal"
                   :use ((:instance runtime-p-divmod-active-length-decreases))
                   :in-theory (disable runtime-p-division-step)))))
  (if (and (runtime-p-canonical-polynomial-p quotient p)
           (runtime-p-canonical-polynomial-p remainder p)
           (runtime-p-canonical-polynomial-p divisor p)
           (consp remainder)
           (consp divisor)
           (equal (runtime-p-mul
                   (runtime-p-poly-leading-coefficient divisor p)
                   (runtime-p-inv
                    (runtime-p-poly-leading-coefficient divisor p) p) p)
                  (runtime-p-one p))
           (<= (runtime-p-poly-degree divisor p)
               (runtime-p-poly-degree remainder p)))
      (let* ((step (runtime-p-division-step remainder divisor p))
             (term (car step))
             (next (cdr step)))
        (runtime-p-divmod-core
         (runtime-p-poly-add quotient term p) next divisor p))
    (cons quotient remainder)))

(defthm runtime-p-divmod-core-equation
  (equal
   (runtime-p-divmod-core quotient remainder divisor p)
   (if (and (runtime-p-canonical-polynomial-p quotient p)
            (runtime-p-canonical-polynomial-p remainder p)
            (runtime-p-canonical-polynomial-p divisor p)
            (consp remainder)
            (consp divisor)
            (equal (runtime-p-mul
                    (runtime-p-poly-leading-coefficient divisor p)
                    (runtime-p-inv
                     (runtime-p-poly-leading-coefficient divisor p) p) p)
                   (runtime-p-one p))
            (<= (runtime-p-poly-degree divisor p)
                (runtime-p-poly-degree remainder p)))
       (let* ((step (runtime-p-division-step remainder divisor p))
              (term (car step))
              (next (cdr step)))
         (runtime-p-divmod-core
          (runtime-p-poly-add quotient term p) next divisor p))
     (cons quotient remainder)))
  :rule-classes nil
  :hints (("Goal" :by (:instance runtime-p-divmod-core))))

(defun runtime-p-divmod (f g p)
  (declare (xargs :guard t))
  (let* ((f (runtime-p-normalize f p))
         (g (runtime-p-normalize g p))
         (result (runtime-p-divmod-core nil f g p)))
    (mv (car result) (cdr result))))

(defun runtime-p-quotient (f g p)
  (declare (xargs :guard t))
  (mv-let (q r) (runtime-p-divmod f g p)
    (declare (ignore r)) q))

(defun runtime-p-remainder (f g p)
  (declare (xargs :guard t))
  (mv-let (q r) (runtime-p-divmod f g p)
    (declare (ignore q)) r))

(verify-guards runtime-p-divmod-core)
(verify-guards runtime-p-divmod)
(verify-guards runtime-p-quotient)
(verify-guards runtime-p-remainder)

(defthm runtime-p-quotient-is-divmod-quotient
  (equal (runtime-p-quotient f g p)
         (mv-nth 0 (runtime-p-divmod f g p))))

(defthm runtime-p-remainder-is-divmod-remainder
  (equal (runtime-p-remainder f g p)
         (mv-nth 1 (runtime-p-divmod f g p))))

(defthm runtime-p-divmod-of-normalize
  (equal (runtime-p-divmod (runtime-p-normalize f p)
                                 (runtime-p-normalize g p) p)
         (runtime-p-divmod f g p)))

(defthm runtime-p-divmod-inactive
  (implies
   (or (not (consp (runtime-p-normalize f p)))
       (not (consp (runtime-p-normalize g p)))
       (not (equal
             (runtime-p-mul
              (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p)
              (runtime-p-inv
               (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p) p)
              p)
             (runtime-p-one p)))
       (< (runtime-p-poly-degree (runtime-p-normalize f p) p)
          (runtime-p-poly-degree (runtime-p-normalize g p) p)))
  (equal (runtime-p-divmod f g p)
          (mv nil (runtime-p-normalize f p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-divmod-core-equation
                            (quotient nil)
                            (remainder (runtime-p-normalize f p))
                            (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-divmod)
                           (runtime-p-divmod-core
                            runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-canonical-polynomial-p-of-nil-for-general-divmod
  (runtime-p-canonical-polynomial-p nil p)
  :hints (("Goal" :in-theory (enable runtime-p-canonical-polynomial-p
                                     runtime-p-coefficient-list-p))))

(defthm runtime-p-divmod-core-quotient-canonical
  (implies (and (runtime-p-canonical-polynomial-p quotient p)
                (runtime-p-canonical-polynomial-p remainder p)
                (runtime-p-canonical-polynomial-p divisor p))
           (runtime-p-canonical-polynomial-p
            (car (runtime-p-divmod-core quotient remainder divisor p)) p))
  :hints (("Goal" :induct (runtime-p-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-divmod-core)
                           (runtime-p-division-step
                            runtime-p-poly-add runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-division-step-output-canonical))
                 :in-theory (disable runtime-p-divmod-core
                                     runtime-p-division-step
                                     runtime-p-poly-add runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-divmod-core-remainder-canonical
  (implies (and (runtime-p-canonical-polynomial-p quotient p)
                (runtime-p-canonical-polynomial-p remainder p)
                (runtime-p-canonical-polynomial-p divisor p))
           (runtime-p-canonical-polynomial-p
            (cdr (runtime-p-divmod-core quotient remainder divisor p)) p))
  :hints (("Goal" :induct (runtime-p-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-divmod-core)
                           (runtime-p-division-step
                            runtime-p-poly-add runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-division-step-output-canonical))
                 :in-theory (disable runtime-p-divmod-core
                                     runtime-p-division-step
                                     runtime-p-poly-add runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-divmod-core-final-remainder-bound
  (implies (and (runtime-p-canonical-polynomial-p quotient p)
                (runtime-p-canonical-polynomial-p remainder p)
                (runtime-p-canonical-polynomial-p divisor p)
                (consp divisor)
                (equal (runtime-p-mul
                        (runtime-p-poly-leading-coefficient divisor p)
                        (runtime-p-inv
                         (runtime-p-poly-leading-coefficient divisor p) p) p)
                       (runtime-p-one p)))
           (let ((final (cdr (runtime-p-divmod-core
                              quotient remainder divisor p))))
             (or (equal final nil)
                 (< (runtime-p-poly-degree final p)
                    (runtime-p-poly-degree divisor p)))))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-divmod-core)
                           (runtime-p-division-step runtime-p-poly-add
                            runtime-p-normalize runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-division-step-output-canonical))
                 :in-theory (disable runtime-p-divmod-core
                                     runtime-p-division-step
                                     runtime-p-poly-add runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-divmod-accumulator-algebra
  (implies
   (equal (runtime-p-poly-add (runtime-p-poly-mul term divisor p) next p)
          remainder)
   (equal (runtime-p-poly-add
           (runtime-p-poly-mul (runtime-p-poly-add quotient term p) divisor p)
           next p)
          (runtime-p-poly-add
           (runtime-p-poly-mul quotient divisor p) remainder p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-mul-right-distributive
                            (x quotient) (y term) (z divisor))
                 (:instance runtime-p-poly-add-associative
                            (x (runtime-p-poly-mul quotient divisor p))
                            (y (runtime-p-poly-mul term divisor p)) (z next)))
           :in-theory (disable runtime-p-poly-add runtime-p-poly-mul))))

(defthm runtime-p-divmod-core-reconstruction-invariant
  (implies (and (runtime-p-canonical-polynomial-p quotient p)
                (runtime-p-canonical-polynomial-p remainder p)
                (runtime-p-canonical-polynomial-p divisor p))
           (equal
            (runtime-p-poly-add
             (runtime-p-poly-mul
              (car (runtime-p-divmod-core quotient remainder divisor p))
              divisor p)
             (cdr (runtime-p-divmod-core quotient remainder divisor p)) p)
            (runtime-p-poly-add
             (runtime-p-poly-mul quotient divisor p) remainder p)))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-divmod-core)
                           (runtime-p-division-step runtime-p-poly-add
                            runtime-p-poly-mul runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-division-step-reconstruction)
                        (:instance runtime-p-division-step-output-canonical)
                        (:instance runtime-p-divmod-accumulator-algebra
                         (term (car (runtime-p-division-step remainder divisor p)))
                         (next (cdr (runtime-p-division-step remainder divisor p)))))
                 :in-theory (disable runtime-p-divmod-core
                                     runtime-p-division-step
                                     runtime-p-poly-add runtime-p-poly-mul
                                     runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-divmod-quotient-canonical
  (runtime-p-canonical-polynomial-p
   (mv-nth 0 (runtime-p-divmod f g p)) p)
  :hints (("Goal" :use ((:instance runtime-p-divmod-core-quotient-canonical
                                   (quotient nil)
                                   (remainder (runtime-p-normalize f p))
                                   (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-divmod)
                           (runtime-p-divmod-core runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-divmod-remainder-canonical
  (runtime-p-canonical-polynomial-p
   (mv-nth 1 (runtime-p-divmod f g p)) p)
  :hints (("Goal" :use ((:instance runtime-p-divmod-core-remainder-canonical
                                   (quotient nil)
                                   (remainder (runtime-p-normalize f p))
                                   (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-divmod)
                           (runtime-p-divmod-core runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-divmod-reconstruction
  (equal (runtime-p-poly-add
          (runtime-p-poly-mul (mv-nth 0 (runtime-p-divmod f g p))
                              (runtime-p-normalize g p) p)
          (mv-nth 1 (runtime-p-divmod f g p)) p)
         (runtime-p-normalize f p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-divmod-core-reconstruction-invariant
                            (quotient nil)
                            (remainder (runtime-p-normalize f p))
                            (divisor (runtime-p-normalize g p)))
                 (:instance runtime-p-poly-mul-zero-left
                            (x (runtime-p-normalize g p)))
                 (:instance runtime-p-poly-add-zero-left
                            (x (runtime-p-normalize f p))))
           :in-theory (e/d (runtime-p-divmod)
                           (runtime-p-divmod-core runtime-p-poly-add
                            runtime-p-poly-mul runtime-p-normalize)))))

(defthm runtime-p-divmod-final-remainder-bound
  (implies (and (consp (runtime-p-normalize g p))
                (equal
                 (runtime-p-mul
                  (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p)
                  (runtime-p-inv
                   (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p) p)
                  p)
                 (runtime-p-one p)))
           (or (equal (mv-nth 1 (runtime-p-divmod f g p)) nil)
               (< (runtime-p-poly-degree
                   (mv-nth 1 (runtime-p-divmod f g p)) p)
                  (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-divmod-core-final-remainder-bound
                                   (quotient nil)
                                   (remainder (runtime-p-normalize f p))
                                   (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-divmod)
                           (runtime-p-divmod-core runtime-p-normalize)))))

(defthm runtime-p-canonical-polynomial-p-of-quotient
  (runtime-p-canonical-polynomial-p (runtime-p-quotient f g p) p))

(defthm runtime-p-canonical-polynomial-p-of-remainder
  (runtime-p-canonical-polynomial-p (runtime-p-remainder f g p) p))

(defthm runtime-p-projection-reconstruction
  (equal (runtime-p-poly-add
          (runtime-p-poly-mul (runtime-p-quotient f g p)
                              (runtime-p-normalize g p) p)
          (runtime-p-remainder f g p) p)
         (runtime-p-normalize f p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-divmod-reconstruction)))))

(defthm runtime-p-remainder-bound
  (implies (and (consp (runtime-p-normalize g p))
                (equal
                 (runtime-p-mul
                  (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p)
                  (runtime-p-inv
                   (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p) p)
                  p)
                 (runtime-p-one p)))
           (or (equal (runtime-p-remainder f g p) nil)
               (< (runtime-p-poly-degree (runtime-p-remainder f g p) p)
                  (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-divmod-final-remainder-bound)))))

(defthm runtime-p-divmod-correctness
  (and (runtime-p-canonical-polynomial-p
        (mv-nth 0 (runtime-p-divmod f g p)) p)
       (runtime-p-canonical-polynomial-p
        (mv-nth 1 (runtime-p-divmod f g p)) p)
       (equal (runtime-p-poly-add
               (runtime-p-poly-mul
                (mv-nth 0 (runtime-p-divmod f g p))
                (runtime-p-normalize g p) p)
               (mv-nth 1 (runtime-p-divmod f g p)) p)
              (runtime-p-normalize f p))
       (implies (and (consp (runtime-p-normalize g p))
                (equal
                 (runtime-p-mul
                  (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p)
                  (runtime-p-inv
                   (runtime-p-poly-leading-coefficient (runtime-p-normalize g p) p) p)
                  p)
                 (runtime-p-one p)))
                (or (equal (mv-nth 1 (runtime-p-divmod f g p)) nil)
                    (< (runtime-p-poly-degree
                        (mv-nth 1 (runtime-p-divmod f g p)) p)
                       (runtime-p-poly-degree (runtime-p-normalize g p) p)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-divmod-quotient-canonical)
                         (:instance runtime-p-divmod-remainder-canonical)
                         (:instance runtime-p-divmod-reconstruction)
                         (:instance runtime-p-divmod-final-remainder-bound)))))

(defthm runtime-p-divmod-prime-final-remainder-bound
  (implies (and (dm::primep (runtime-p-effective-modulus p))
                (consp (runtime-p-normalize g p)))
           (or (equal (mv-nth 1 (runtime-p-divmod f g p)) nil)
               (< (runtime-p-poly-degree
                   (mv-nth 1 (runtime-p-divmod f g p)) p)
                  (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-divmod-final-remainder-bound)
                 (:instance runtime-p-division-step-prime-divisor-inverse-check
                            (divisor (runtime-p-normalize g p)))
                 (:instance runtime-p-normalize-idempotent (xs g)))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-remainder-prime-bound
  (implies (and (dm::primep (runtime-p-effective-modulus p))
                (consp (runtime-p-normalize g p)))
           (or (equal (runtime-p-remainder f g p) nil)
               (< (runtime-p-poly-degree (runtime-p-remainder f g p) p)
                  (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-divmod-prime-final-remainder-bound)))))

(defthm runtime-p-divmod-prime-correctness
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (and (runtime-p-canonical-polynomial-p
         (mv-nth 0 (runtime-p-divmod f g p)) p)
        (runtime-p-canonical-polynomial-p
         (mv-nth 1 (runtime-p-divmod f g p)) p)
        (equal (runtime-p-poly-add
                (runtime-p-poly-mul
                 (mv-nth 0 (runtime-p-divmod f g p))
                 (runtime-p-normalize g p) p)
                (mv-nth 1 (runtime-p-divmod f g p)) p)
               (runtime-p-normalize f p))
        (or (equal (mv-nth 1 (runtime-p-divmod f g p)) nil)
            (< (runtime-p-poly-degree
                (mv-nth 1 (runtime-p-divmod f g p)) p)
               (runtime-p-poly-degree (runtime-p-normalize g p) p)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-divmod-quotient-canonical)
                          (:instance runtime-p-divmod-remainder-canonical)
                          (:instance runtime-p-divmod-reconstruction)
                          (:instance runtime-p-divmod-prime-final-remainder-bound)))))

(include-book "runtime-p-monic-divmod")

(local
 (defthm runtime-p-divmod-monic-divisor-eligible
   (implies (equal (runtime-p-poly-leading-coefficient divisor p)
                   (runtime-p-one p))
            (and (consp divisor)
                 (equal (runtime-p-mul
                         (runtime-p-poly-leading-coefficient divisor p)
                         (runtime-p-inv
                          (runtime-p-poly-leading-coefficient divisor p) p) p)
                        (runtime-p-one p))))
   :hints (("Goal"
            :use ((:instance runtime-p-poly-leading-coefficient-equal-zero
                             (poly divisor))
                  (:instance runtime-p-inv-of-one)
                  (:instance runtime-p-mul-one-left
                             (x (runtime-p-one p))))))))

(defthm runtime-p-divmod-core-when-monic
  (implies
   (and (runtime-p-canonical-polynomial-p quotient p)
        (runtime-p-canonical-polynomial-p remainder p)
        (runtime-p-canonical-polynomial-p divisor p)
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p)))
   (equal (runtime-p-divmod-core quotient remainder divisor p)
          (runtime-p-monic-divmod-core quotient remainder divisor p)))
  :rule-classes nil
  :hints (("Goal"
           :induct (runtime-p-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-divmod-core)
                           (runtime-p-monic-divmod-core
                               runtime-p-division-step
                               runtime-p-monic-division-step
                               runtime-p-poly-add runtime-p-normalize
                               runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-divmod-core-equation)
                        (:instance runtime-p-monic-divmod-core-equation)
                        (:instance runtime-p-divmod-monic-divisor-eligible)
                        (:instance runtime-p-division-step-when-monic)
                        (:instance runtime-p-division-step-output-canonical))
                 :in-theory (disable runtime-p-divmod-core
                                     runtime-p-monic-divmod-core
                                     runtime-p-division-step
                                     runtime-p-monic-division-step
                                     runtime-p-poly-add runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-divmod-when-monic
  (implies (equal (runtime-p-poly-leading-coefficient
                   (runtime-p-normalize g p) p)
                  (runtime-p-one p))
           (equal (runtime-p-divmod f g p)
                  (runtime-p-monic-divmod f g p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-divmod-core-when-monic
                            (quotient nil)
                            (remainder (runtime-p-normalize f p))
                            (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-divmod runtime-p-monic-divmod)
                           (runtime-p-divmod-core runtime-p-monic-divmod-core
                            runtime-p-normalize runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-quotient-when-monic
  (implies (equal (runtime-p-poly-leading-coefficient
                   (runtime-p-normalize g p) p)
                  (runtime-p-one p))
           (equal (runtime-p-quotient f g p)
                  (runtime-p-monic-quotient f g p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-divmod-when-monic)))))

(defthm runtime-p-remainder-when-monic
  (implies (equal (runtime-p-poly-leading-coefficient
                   (runtime-p-normalize g p) p)
                  (runtime-p-one p))
           (equal (runtime-p-remainder f g p)
                  (runtime-p-monic-remainder f g p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-divmod-when-monic)))))
