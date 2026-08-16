(in-package "GPOLY")

(include-book "runtime-p-monic-division-step")

; The state is canonical.  Each active branch binds the public step once and
; reuses both of its coordinates.
(defun runtime-p-monic-divmod-core (quotient remainder divisor p)
  (declare
   (xargs :guard t
          :measure (len remainder)
          :hints (("Goal"
                   :use ((:instance
                          runtime-p-monic-division-step-active-length-decreases)
                         (:instance runtime-p-normalize-when-canonical
                                    (xs remainder)))
                   :in-theory (e/d (runtime-p-monic-division-step-next)
                                   (runtime-p-monic-division-step
                                    runtime-p-monic-division-step-core
                                    runtime-p-normalize
                                    runtime-p-canonical-polynomial-p
                                    runtime-p-poly-leading-coefficient
                                    runtime-p-poly-degree))))))
  (if (and (runtime-p-canonical-polynomial-p quotient p)
           (runtime-p-canonical-polynomial-p remainder p)
           (runtime-p-canonical-polynomial-p divisor p)
           (consp remainder)
           (equal (runtime-p-poly-leading-coefficient divisor p)
                  (runtime-p-one p))
           (<= (runtime-p-poly-degree divisor p)
               (runtime-p-poly-degree remainder p)))
      (let* ((step (runtime-p-monic-division-step remainder divisor p))
             (term (car step))
             (next (cdr step)))
        (runtime-p-monic-divmod-core
         (runtime-p-poly-add quotient term p) next divisor p))
    (cons quotient remainder)))

(defthm runtime-p-monic-divmod-core-equation
  (equal
   (runtime-p-monic-divmod-core quotient remainder divisor p)
   (if (and (runtime-p-canonical-polynomial-p quotient p)
            (runtime-p-canonical-polynomial-p remainder p)
            (runtime-p-canonical-polynomial-p divisor p)
            (consp remainder)
            (equal (runtime-p-poly-leading-coefficient divisor p)
                   (runtime-p-one p))
            (<= (runtime-p-poly-degree divisor p)
                (runtime-p-poly-degree remainder p)))
       (let* ((step (runtime-p-monic-division-step remainder divisor p))
              (term (car step))
              (next (cdr step)))
         (runtime-p-monic-divmod-core
          (runtime-p-poly-add quotient term p) next divisor p))
     (cons quotient remainder)))
  :rule-classes nil
  :hints (("Goal" :by (:instance runtime-p-monic-divmod-core))))

(defun runtime-p-monic-divmod (f g p)
  (declare (xargs :guard t))
  (let* ((f (runtime-p-normalize f p))
         (g (runtime-p-normalize g p))
         (result (runtime-p-monic-divmod-core nil f g p)))
    (mv (car result) (cdr result))))

(defun runtime-p-monic-quotient (f g p)
  (declare (xargs :guard t))
  (mv-let (q r) (runtime-p-monic-divmod f g p)
    (declare (ignore r)) q))

(defun runtime-p-monic-remainder (f g p)
  (declare (xargs :guard t))
  (mv-let (q r) (runtime-p-monic-divmod f g p)
    (declare (ignore q)) r))

(verify-guards runtime-p-monic-divmod-core)
(verify-guards runtime-p-monic-divmod)
(verify-guards runtime-p-monic-quotient)
(verify-guards runtime-p-monic-remainder)

(defthm runtime-p-monic-quotient-is-divmod-quotient
  (equal (runtime-p-monic-quotient f g p)
         (mv-nth 0 (runtime-p-monic-divmod f g p))))

(defthm runtime-p-monic-remainder-is-divmod-remainder
  (equal (runtime-p-monic-remainder f g p)
         (mv-nth 1 (runtime-p-monic-divmod f g p))))

(defthm runtime-p-monic-divmod-of-normalize
  (equal (runtime-p-monic-divmod (runtime-p-normalize f p)
                                 (runtime-p-normalize g p) p)
         (runtime-p-monic-divmod f g p)))

(defthm runtime-p-monic-divmod-inactive
  (implies
   (or (not (consp (runtime-p-normalize f p)))
       (not (equal (runtime-p-poly-leading-coefficient
                    (runtime-p-normalize g p) p)
                   (runtime-p-one p)))
       (< (runtime-p-poly-degree (runtime-p-normalize f p) p)
          (runtime-p-poly-degree (runtime-p-normalize g p) p)))
  (equal (runtime-p-monic-divmod f g p)
          (mv nil (runtime-p-normalize f p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-divmod-core-equation
                            (quotient nil)
                            (remainder (runtime-p-normalize f p))
                            (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-monic-divmod)
                           (runtime-p-monic-divmod-core
                            runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-canonical-polynomial-p-of-nil-for-divmod
  (runtime-p-canonical-polynomial-p nil p)
  :hints (("Goal" :in-theory (enable runtime-p-canonical-polynomial-p
                                     runtime-p-coefficient-list-p))))

(defthm runtime-p-monic-divmod-core-quotient-canonical
  (implies (and (runtime-p-canonical-polynomial-p quotient p)
                (runtime-p-canonical-polynomial-p remainder p)
                (runtime-p-canonical-polynomial-p divisor p))
           (runtime-p-canonical-polynomial-p
            (car (runtime-p-monic-divmod-core quotient remainder divisor p)) p))
  :hints (("Goal" :induct (runtime-p-monic-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-monic-divmod-core)
                           (runtime-p-monic-division-step
                            runtime-p-poly-add runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-monic-division-step-output-canonical))
                 :in-theory (disable runtime-p-monic-divmod-core
                                     runtime-p-monic-division-step
                                     runtime-p-poly-add runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-monic-divmod-core-remainder-canonical
  (implies (and (runtime-p-canonical-polynomial-p quotient p)
                (runtime-p-canonical-polynomial-p remainder p)
                (runtime-p-canonical-polynomial-p divisor p))
           (runtime-p-canonical-polynomial-p
            (cdr (runtime-p-monic-divmod-core quotient remainder divisor p)) p))
  :hints (("Goal" :induct (runtime-p-monic-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-monic-divmod-core)
                           (runtime-p-monic-division-step
                            runtime-p-poly-add runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-monic-division-step-output-canonical))
                 :in-theory (disable runtime-p-monic-divmod-core
                                     runtime-p-monic-division-step
                                     runtime-p-poly-add runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-monic-divmod-core-final-remainder-bound
  (implies (and (runtime-p-canonical-polynomial-p quotient p)
                (runtime-p-canonical-polynomial-p remainder p)
                (runtime-p-canonical-polynomial-p divisor p)
                (equal (runtime-p-poly-leading-coefficient divisor p)
                       (runtime-p-one p)))
           (let ((final (cdr (runtime-p-monic-divmod-core
                              quotient remainder divisor p))))
             (or (equal final nil)
                 (< (runtime-p-poly-degree final p)
                    (runtime-p-poly-degree divisor p)))))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-monic-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-monic-divmod-core)
                           (runtime-p-monic-division-step runtime-p-poly-add
                            runtime-p-normalize runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-monic-division-step-output-canonical))
                 :in-theory (disable runtime-p-monic-divmod-core
                                     runtime-p-monic-division-step
                                     runtime-p-poly-add runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-monic-divmod-accumulator-algebra
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

(defthm runtime-p-monic-divmod-core-reconstruction-invariant
  (implies (and (runtime-p-canonical-polynomial-p quotient p)
                (runtime-p-canonical-polynomial-p remainder p)
                (runtime-p-canonical-polynomial-p divisor p))
           (equal
            (runtime-p-poly-add
             (runtime-p-poly-mul
              (car (runtime-p-monic-divmod-core quotient remainder divisor p))
              divisor p)
             (cdr (runtime-p-monic-divmod-core quotient remainder divisor p)) p)
            (runtime-p-poly-add
             (runtime-p-poly-mul quotient divisor p) remainder p)))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-monic-divmod-core quotient remainder divisor p)
           :in-theory (e/d (runtime-p-monic-divmod-core)
                           (runtime-p-monic-division-step runtime-p-poly-add
                            runtime-p-poly-mul runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))
          (and stable-under-simplificationp
               '(:use ((:instance runtime-p-monic-division-step-reconstruction)
                        (:instance runtime-p-monic-division-step-output-canonical)
                        (:instance runtime-p-monic-divmod-accumulator-algebra
                         (term (car (runtime-p-monic-division-step remainder divisor p)))
                         (next (cdr (runtime-p-monic-division-step remainder divisor p)))))
                 :in-theory (disable runtime-p-monic-divmod-core
                                     runtime-p-monic-division-step
                                     runtime-p-poly-add runtime-p-poly-mul
                                     runtime-p-normalize
                                     runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-monic-divmod-quotient-canonical
  (runtime-p-canonical-polynomial-p
   (mv-nth 0 (runtime-p-monic-divmod f g p)) p)
  :hints (("Goal" :use ((:instance runtime-p-monic-divmod-core-quotient-canonical
                                   (quotient nil)
                                   (remainder (runtime-p-normalize f p))
                                   (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-monic-divmod)
                           (runtime-p-monic-divmod-core runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-monic-divmod-remainder-canonical
  (runtime-p-canonical-polynomial-p
   (mv-nth 1 (runtime-p-monic-divmod f g p)) p)
  :hints (("Goal" :use ((:instance runtime-p-monic-divmod-core-remainder-canonical
                                   (quotient nil)
                                   (remainder (runtime-p-normalize f p))
                                   (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-monic-divmod)
                           (runtime-p-monic-divmod-core runtime-p-normalize
                            runtime-p-canonical-polynomial-p)))))

(defthm runtime-p-monic-divmod-reconstruction
  (equal (runtime-p-poly-add
          (runtime-p-poly-mul (mv-nth 0 (runtime-p-monic-divmod f g p))
                              (runtime-p-normalize g p) p)
          (mv-nth 1 (runtime-p-monic-divmod f g p)) p)
         (runtime-p-normalize f p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-divmod-core-reconstruction-invariant
                            (quotient nil)
                            (remainder (runtime-p-normalize f p))
                            (divisor (runtime-p-normalize g p)))
                 (:instance runtime-p-poly-mul-zero-left
                            (x (runtime-p-normalize g p)))
                 (:instance runtime-p-poly-add-zero-left
                            (x (runtime-p-normalize f p))))
           :in-theory (e/d (runtime-p-monic-divmod)
                           (runtime-p-monic-divmod-core runtime-p-poly-add
                            runtime-p-poly-mul runtime-p-normalize)))))

(defthm runtime-p-monic-divmod-final-remainder-bound
  (implies (equal (runtime-p-poly-leading-coefficient
                   (runtime-p-normalize g p) p)
                  (runtime-p-one p))
           (or (equal (mv-nth 1 (runtime-p-monic-divmod f g p)) nil)
               (< (runtime-p-poly-degree
                   (mv-nth 1 (runtime-p-monic-divmod f g p)) p)
                  (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-monic-divmod-core-final-remainder-bound
                                   (quotient nil)
                                   (remainder (runtime-p-normalize f p))
                                   (divisor (runtime-p-normalize g p))))
           :in-theory (e/d (runtime-p-monic-divmod)
                           (runtime-p-monic-divmod-core runtime-p-normalize)))))

(defthm runtime-p-canonical-polynomial-p-of-monic-quotient
  (runtime-p-canonical-polynomial-p (runtime-p-monic-quotient f g p) p))

(defthm runtime-p-canonical-polynomial-p-of-monic-remainder
  (runtime-p-canonical-polynomial-p (runtime-p-monic-remainder f g p) p))

(defthm runtime-p-monic-projection-reconstruction
  (equal (runtime-p-poly-add
          (runtime-p-poly-mul (runtime-p-monic-quotient f g p)
                              (runtime-p-normalize g p) p)
          (runtime-p-monic-remainder f g p) p)
         (runtime-p-normalize f p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-monic-divmod-reconstruction)))))

(defthm runtime-p-monic-remainder-bound
  (implies (equal (runtime-p-poly-leading-coefficient
                   (runtime-p-normalize g p) p) (runtime-p-one p))
           (or (equal (runtime-p-monic-remainder f g p) nil)
               (< (runtime-p-poly-degree (runtime-p-monic-remainder f g p) p)
                  (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-monic-divmod-final-remainder-bound)))))

(defthm runtime-p-monic-divmod-correctness
  (and (runtime-p-canonical-polynomial-p
        (mv-nth 0 (runtime-p-monic-divmod f g p)) p)
       (runtime-p-canonical-polynomial-p
        (mv-nth 1 (runtime-p-monic-divmod f g p)) p)
       (equal (runtime-p-poly-add
               (runtime-p-poly-mul
                (mv-nth 0 (runtime-p-monic-divmod f g p))
                (runtime-p-normalize g p) p)
               (mv-nth 1 (runtime-p-monic-divmod f g p)) p)
              (runtime-p-normalize f p))
       (implies (equal (runtime-p-poly-leading-coefficient
                        (runtime-p-normalize g p) p) (runtime-p-one p))
                (or (equal (mv-nth 1 (runtime-p-monic-divmod f g p)) nil)
                    (< (runtime-p-poly-degree
                        (mv-nth 1 (runtime-p-monic-divmod f g p)) p)
                       (runtime-p-poly-degree (runtime-p-normalize g p) p)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-monic-divmod-quotient-canonical)
                         (:instance runtime-p-monic-divmod-remainder-canonical)
                         (:instance runtime-p-monic-divmod-reconstruction)
                         (:instance runtime-p-monic-divmod-final-remainder-bound)))))
