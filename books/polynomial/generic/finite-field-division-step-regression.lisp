(in-package "GPOLY")

(include-book "finite-field-division-step")
(include-book "f7-division")

(local
 (defthm finite-field-division-step-next-canonical-minimal-theory-client
   (implies (finite-field-canonical-polynomial-p remainder)
            (finite-field-canonical-polynomial-p
             (cdr (finite-field-poly-division-step-core remainder divisor))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance finite-field-poly-division-step-core-next-canonical))))))

(local
 (defthm finite-field-division-step-reconstruction-minimal-theory-client
   (implies (finite-field-canonical-polynomial-p remainder)
            (equal (finite-field-poly-add
                    (finite-field-poly-mul
                     (car (finite-field-poly-division-step-core remainder divisor))
                     divisor)
                    (cdr (finite-field-poly-division-step-core remainder divisor)))
                   remainder))
   :rule-classes nil
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance finite-field-poly-division-step-core-reconstruction))))))

(local
 (defthm finite-field-division-step-degree-decrease-minimal-theory-client
   (implies (and (finite-field-canonical-polynomial-p remainder)
                 (finite-field-canonical-polynomial-p divisor)
                 (consp remainder) (consp divisor)
                 (<= (finite-field-poly-degree divisor)
                     (finite-field-poly-degree remainder)))
            (let ((next (cdr (finite-field-poly-division-step-core remainder divisor))))
              (or (not (consp next))
                  (< (finite-field-poly-degree next)
                     (finite-field-poly-degree remainder)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance finite-field-poly-division-step-core-degree-decreases))))))

(local
 (defthm finite-field-division-step-length-decrease-minimal-theory-client
   (implies (and (finite-field-canonical-polynomial-p remainder)
                 (finite-field-canonical-polynomial-p divisor)
                 (consp remainder) (consp divisor)
                 (<= (finite-field-poly-degree divisor)
                     (finite-field-poly-degree remainder)))
            (< (len (cdr (finite-field-poly-division-step-core remainder divisor)))
               (len remainder)))
   :rule-classes nil
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance finite-field-poly-division-step-core-length-decreases))))))

(defthm f7-division-step-active-execution-regression
  (equal (f7-poly-division-step-core '(1 2 3) '(1 1))
         (cons '(0 3) '(1 6))))

(defthm f7-division-step-inactive-execution-regression
  (equal (f7-poly-division-step-core '(1) '(1 1))
         (cons nil '(1))))

(defthm f7-division-step-term-execution-regression
  (equal (f7-poly-division-step-term '(1 2 3) '(1 1))
         '(0 3)))

(defthm f7-division-step-next-execution-regression
  (equal (f7-poly-division-step-next '(1 2 3) '(1 1))
         '(1 6)))

(defthm f7-division-step-reconstruction-client
  (implies (f7-canonical-polynomial-p remainder)
           (equal (f7-poly-add
                   (f7-poly-mul
                    (car (f7-poly-division-step-core remainder divisor))
                    divisor)
                   (cdr (f7-poly-division-step-core remainder divisor)))
                  remainder))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-poly-division-step-core-reconstruction)))))

(defthm f7-division-step-degree-decrease-client
  (implies (and (f7-canonical-polynomial-p remainder)
                (f7-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (f7-poly-degree divisor)
                    (f7-poly-degree remainder)))
           (let ((next (cdr (f7-poly-division-step-core remainder divisor))))
             (or (not (consp next))
                 (< (f7-poly-degree next)
                    (f7-poly-degree remainder)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-poly-division-step-core-degree-decreases)))))

(defthm f7-division-step-length-decrease-client
  (implies (and (f7-canonical-polynomial-p remainder)
                (f7-canonical-polynomial-p divisor)
                (consp remainder) (consp divisor)
                (<= (f7-poly-degree divisor)
                    (f7-poly-degree remainder)))
           (< (len (cdr (f7-poly-division-step-core remainder divisor)))
              (len remainder)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f7-poly-division-step-core-length-decreases)))))
