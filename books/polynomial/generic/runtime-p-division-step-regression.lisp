(in-package "GPOLY")
(include-book "runtime-p-division-step")
(defthm runtime-p-division-step-reconstruction-minimal-theory-client
  (equal (runtime-p-poly-add
          (runtime-p-poly-mul (runtime-p-division-step-term remainder divisor p)
                              (runtime-p-normalize divisor p) p)
          (runtime-p-division-step-next remainder divisor p) p)
         (runtime-p-normalize remainder p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-division-step-reconstruction))
           :in-theory (theory 'minimal-theory))))
(assert-event (equal (runtime-p-division-step '(1 4 3) '(2 3) 7) '((0 1) 1 2)))
(assert-event (equal (runtime-p-division-step '(1 4 3) '(1 2) 6) '(nil 1 4 3)))
(assert-event (equal (runtime-p-division-step '(1 4 3 0 . bad) '(2 3 0 . bad) 7) '((0 1) 1 2)))
(assert-event (equal (runtime-p-division-step '(1 1) '(1 1) 'bad) '((1))))

(defthm runtime-p-division-step-active-length-decrease-minimal-theory-client
  (implies
   (and (consp (runtime-p-normalize remainder p))
        (consp (runtime-p-normalize divisor p))
        (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                              (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
               (runtime-p-one p))
        (<= (runtime-p-poly-degree divisor p) (runtime-p-poly-degree remainder p)))
   (< (len (runtime-p-division-step-next remainder divisor p))
      (len (runtime-p-normalize remainder p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-division-step-active-length-decreases))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-division-step-active-degree-decrease-minimal-theory-client
  (implies
   (and (consp (runtime-p-normalize remainder p))
        (consp (runtime-p-normalize divisor p))
        (equal (runtime-p-mul (runtime-p-poly-leading-coefficient divisor p)
                              (runtime-p-inv (runtime-p-poly-leading-coefficient divisor p) p) p)
               (runtime-p-one p))
        (<= (runtime-p-poly-degree divisor p) (runtime-p-poly-degree remainder p)))
   (or (not (consp (runtime-p-division-step-next remainder divisor p)))
       (< (runtime-p-poly-degree (runtime-p-division-step-next remainder divisor p) p)
          (runtime-p-poly-degree remainder p))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-division-step-active-degree-decreases))
           :in-theory (theory 'minimal-theory))))

(assert-event (equal (runtime-p-division-step '(1 4 3) '(2 3) 7) '((0 1) 1 2)))
(assert-event
 (and (equal (runtime-p-mul 8 (runtime-p-inv 8 9) 9) 1)
      (< (len (runtime-p-division-step-next '(1 4 3) '(1 8) 9)) 3)))
(assert-event (equal (runtime-p-division-step '(1 4 3) '(1 2) 6) '(nil 1 4 3)))
(assert-event (equal (runtime-p-division-step '(1 1) '(1 1) 'bad)
                     (runtime-p-monic-division-step '(1 1) '(1 1) 'bad)))
(assert-event (and (equal (runtime-p-division-step '(1 2) '(1) 7)
                          (runtime-p-monic-division-step '(1 2) '(1) 7))
                   (equal (runtime-p-division-step-term '(1 2) '(1) 7)
                          (runtime-p-monic-division-step-term '(1 2) '(1) 7))
                   (equal (runtime-p-division-step-next '(1 2) '(1) 7)
                          (runtime-p-monic-division-step-next '(1 2) '(1) 7))))
(assert-event (and (equal (runtime-p-mul 2 (runtime-p-inv 2 7) 7) 1)
                   (equal (runtime-p-mul 3 (runtime-p-inv 3 7) 7) 1)
                   (equal (runtime-p-mul 6 (runtime-p-inv 6 7) 7) 1)))
