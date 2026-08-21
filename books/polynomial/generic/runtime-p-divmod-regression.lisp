(in-package "GPOLY")

(include-book "runtime-p-divmod")

(defthm runtime-p-divmod-reconstruction-minimal-theory-client
  (equal (runtime-p-poly-add
          (runtime-p-poly-mul (mv-nth 0 (runtime-p-divmod f g p))
                              (runtime-p-normalize g p) p)
          (mv-nth 1 (runtime-p-divmod f g p)) p)
         (runtime-p-normalize f p))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance runtime-p-divmod-reconstruction)))))

(defthm runtime-p-divmod-bound-minimal-theory-client
  (implies (and (consp (runtime-p-normalize g p))
                (equal (runtime-p-mul
                        (runtime-p-poly-leading-coefficient
                         (runtime-p-normalize g p) p)
                        (runtime-p-inv
                         (runtime-p-poly-leading-coefficient
                          (runtime-p-normalize g p) p) p) p)
                       (runtime-p-one p)))
           (or (equal (mv-nth 1 (runtime-p-divmod f g p)) nil)
               (< (runtime-p-poly-degree
                   (mv-nth 1 (runtime-p-divmod f g p)) p)
                  (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance runtime-p-divmod-final-remainder-bound)))))

; Three-term quotient and two active reductions over F7.
(assert-event
 (mv-let (q r) (runtime-p-divmod '(1 2 3 4) '(2 3) 7)
   (equal (list q r) '((5 4 6) (5)))))
; Exact divisibility by the same nonmonic divisor.
(assert-event
 (mv-let (q r) (runtime-p-divmod '(2 5 3) '(2 3) 7)
   (equal (list q r) '((1 1) nil))))
(assert-event (mv-let (q r) (runtime-p-divmod '(1) '(2 3) 7)
                (equal (list q r) '(nil (1)))))
(assert-event (mv-let (q r) (runtime-p-divmod nil '(2 3) 7)
                (equal (list q r) '(nil nil))))
(assert-event (mv-let (q r) (runtime-p-divmod '(1 2) nil 7)
                (equal (list q r) '(nil (1 2)))))
(assert-event
 (mv-let (q1 r1) (runtime-p-divmod '(1 2 3 4 0 . bad) '(2 3 0 . bad) 7)
   (mv-let (q2 r2) (runtime-p-divmod '(1 2 3 4) '(2 3) 7)
     (equal (list q1 r1) (list q2 r2)))))
(assert-event
 (mv-let (q1 r1) (runtime-p-divmod '(3 4 1) '(1 1) 'malformed)
   (mv-let (q2 r2) (runtime-p-divmod '(3 4 1) '(1 1) 2)
     (equal (list q1 r1) (list q2 r2)))))
; Eight is recognized by the explicit inverse check modulo composite 9.
(assert-event
 (mv-let (q r) (runtime-p-divmod '(1 2 3) '(2 8) 9)
   (and (consp q) (or (equal r nil) (< (runtime-p-poly-degree r 9) 1)))))
; Two is a unit modulo 9, but is deliberately not recognized by this check.
(assert-event
 (mv-let (q r) (runtime-p-divmod '(1 2 3) '(1 2) 9)
   (equal (list q r) '(nil (1 2 3)))))
; Pair and both projections agree exactly with recursive monic divmod.
(assert-event
 (and (mv-let (q1 r1) (runtime-p-divmod '(5 5 3) '(1 1) 6)
             (mv-let (q2 r2) (runtime-p-monic-divmod '(5 5 3) '(1 1) 6)
               (equal (list q1 r1) (list q2 r2))))
      (equal (runtime-p-quotient '(5 5 3) '(1 1) 6)
             (runtime-p-monic-quotient '(5 5 3) '(1 1) 6))
      (equal (runtime-p-remainder '(5 5 3) '(1 1) 6)
             (runtime-p-monic-remainder '(5 5 3) '(1 1) 6))))
