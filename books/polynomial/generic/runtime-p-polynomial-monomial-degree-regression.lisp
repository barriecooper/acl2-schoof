(in-package "GPOLY")
(include-book "runtime-p-polynomial-monomial-degree")

(assert-event
 (and (equal (runtime-p-poly-monomial 14 3 6) '(0 0 0 2))
      (equal (len (runtime-p-poly-monomial 14 3 6)) 4)
      (equal (runtime-p-poly-degree (runtime-p-poly-monomial 14 3 6) 6) 3)
      (equal (runtime-p-poly-leading-coefficient
              (runtime-p-poly-monomial 14 3 6) 6) 2)))
(assert-event (equal (runtime-p-poly-monomial 12 7 6) nil))
(assert-event (equal (runtime-p-poly-monomial 5 2 'malformed)
                     (runtime-p-poly-monomial 5 2 2)))
(assert-event
 (and (equal (runtime-p-poly-monomial 5 -3 6) '(5))
      (equal (runtime-p-poly-monomial 5 'malformed 6) '(5))))
(assert-event
 (and (equal (runtime-p-poly-degree '(7 8 0 . 9) 6) 1)
      (equal (runtime-p-poly-leading-coefficient '(7 8 0 . 9) 6) 2)
      (equal (runtime-p-poly-degree '(1 2 12) 6) 1)
      (equal (runtime-p-poly-leading-coefficient '(1 2 12) 6) 2)))
(assert-event
 (equal (runtime-p-poly-monomial (runtime-p-one 6) 0 6)
        (runtime-p-polynomial-one 6)))

(defthm runtime-p-poly-degree-of-poly-monomial-minimal-theory-client
  (implies (not (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p)))
           (equal (runtime-p-poly-degree (runtime-p-poly-monomial a n p) p)
                  (nfix n)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-poly-degree-of-poly-monomial))
           :in-theory (theory 'minimal-theory))))
(defthm runtime-p-poly-leading-coefficient-of-poly-monomial-minimal-theory-client
  (implies (not (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p)))
           (equal (runtime-p-poly-leading-coefficient
                   (runtime-p-poly-monomial a n p) p)
                  (runtime-p-coefficient-fix a p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-leading-coefficient-of-poly-monomial))
           :in-theory (theory 'minimal-theory))))
(defthm runtime-p-poly-monomial-when-fixed-zero-minimal-theory-client
  (implies (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p))
           (equal (runtime-p-poly-monomial a n p) nil))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-poly-monomial-when-fixed-zero))
           :in-theory (theory 'minimal-theory))))
