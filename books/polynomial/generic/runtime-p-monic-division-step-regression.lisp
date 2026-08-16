(in-package "GPOLY")

(include-book "runtime-p-monic-division-step")

(defthm runtime-p-monic-division-step-reconstruction-minimal-theory-client
  (equal
   (runtime-p-poly-add
    (runtime-p-poly-mul
     (runtime-p-monic-division-step-term remainder divisor p)
     (runtime-p-normalize divisor p) p)
    (runtime-p-monic-division-step-next remainder divisor p) p)
   (runtime-p-normalize remainder p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-division-step-reconstruction))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-monic-division-step-decrease-minimal-theory-client
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
           :use ((:instance
                  runtime-p-monic-division-step-active-length-decreases))
           :in-theory (theory 'minimal-theory))))

; Composite-modulus active calculation: the lower product coefficient 3*2
; vanishes modulo 6, while the monic leading product survives.
(assert-event
 (and (equal (runtime-p-monic-division-step '(5 0 4 3) '(2 1) 6)
             '((0 0 3) 5 0 4))
      (equal (runtime-p-monic-division-step-term '(5 0 4 3) '(2 1) 6)
             '(0 0 3))
      (equal (runtime-p-monic-division-step-next '(5 0 4 3) '(2 1) 6)
             '(5 0 4))))

(assert-event (equal (runtime-p-monic-division-step nil '(1) 6)
                     '(nil)))
(assert-event (equal (runtime-p-monic-division-step '(1 2) nil 6)
                     '(nil 1 2)))
(assert-event (equal (runtime-p-monic-division-step '(1 2) '(3) 6)
                     '(nil 1 2)))
(assert-event (equal (runtime-p-monic-division-step '(1 2) '(1 0 1) 6)
                     '(nil 1 2)))

; Dotted tails and trailing zeros are discarded before activity is decided.
(assert-event
 (equal (runtime-p-monic-division-step
         '(7 0 3 0 . malformed-tail) '(7 1 0 . malformed-tail) 6)
        '((0 3) 1 3)))

; A malformed modulus follows the effective-modulus-2 convention.
(assert-event
 (equal (runtime-p-monic-division-step '(3 0 3) '(1 1) 'malformed)
        '((0 1) 1 1)))

; Exact divisibility makes the next remainder exactly NIL.
(assert-event
 (and (equal (runtime-p-monic-division-step '(2 1) '(2 1) 6)
             '((1)))
      (equal (runtime-p-monic-division-step-next '(2 1) '(2 1) 6)
             nil)))
