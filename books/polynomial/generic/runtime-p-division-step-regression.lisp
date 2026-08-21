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
