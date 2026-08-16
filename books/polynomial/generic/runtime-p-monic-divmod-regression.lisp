(in-package "GPOLY")

(include-book "runtime-p-monic-divmod")

(defthm runtime-p-monic-divmod-reconstruction-minimal-theory-client
  (equal (runtime-p-poly-add
          (runtime-p-poly-mul (mv-nth 0 (runtime-p-monic-divmod f g p))
                              (runtime-p-normalize g p) p)
          (mv-nth 1 (runtime-p-monic-divmod f g p)) p)
         (runtime-p-normalize f p))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance runtime-p-monic-divmod-reconstruction)))))

(defthm runtime-p-monic-divmod-bound-minimal-theory-client
  (implies (equal (runtime-p-poly-leading-coefficient
                   (runtime-p-normalize g p) p) (runtime-p-one p))
           (or (equal (mv-nth 1 (runtime-p-monic-divmod f g p)) nil)
               (< (runtime-p-poly-degree
                   (mv-nth 1 (runtime-p-monic-divmod f g p)) p)
                  (runtime-p-poly-degree (runtime-p-normalize g p) p))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance runtime-p-monic-divmod-final-remainder-bound)))))

; Two active iterations over the composite ring Z/6Z.
(assert-event
 (mv-let (q r) (runtime-p-monic-divmod '(5 5 3) '(1 1) 6)
   (and (equal q '(2 3))
        (equal r '(3))
        (equal (runtime-p-poly-add
                (runtime-p-poly-mul q (runtime-p-normalize '(1 1) 6) 6) r 6)
               (runtime-p-normalize '(5 5 3) 6)))))

(assert-event
 (mv-let (q r) (runtime-p-monic-divmod '(2 5 3) '(1 1) 6)
   (equal (list q r) '((2 3) nil))))
(assert-event (mv-let (q r) (runtime-p-monic-divmod nil '(1 1) 6)
                (equal (list q r) '(nil nil))))
(assert-event (mv-let (q r) (runtime-p-monic-divmod '(1 2) nil 6)
                (equal (list q r) '(nil (1 2)))))
(assert-event (mv-let (q r) (runtime-p-monic-divmod '(1 2) '(1 2) 6)
                (equal (list q r) '(nil (1 2)))))
(assert-event (mv-let (q r) (runtime-p-monic-divmod '(1) '(1 0 1) 6)
                (equal (list q r) '(nil (1)))))
(assert-event
 (mv-let (q r) (runtime-p-monic-divmod '(5 5 3 0 . bad) '(1 1 0 . bad) 6)
   (equal (list q r) '((2 3) (3)))))
(assert-event
 (mv-let (q1 r1) (runtime-p-monic-divmod '(3 4 1) '(1 1) 'malformed)
   (mv-let (q2 r2) (runtime-p-monic-divmod '(3 4 1) '(1 1) 2)
     (equal (list q1 r1) (list q2 r2)))))
(assert-event
 (mv-let (q r) (runtime-p-monic-divmod '(5 5 3) '(1 1) 6)
   (and (equal (runtime-p-monic-quotient '(5 5 3) '(1 1) 6) q)
        (equal (runtime-p-monic-remainder '(5 5 3) '(1 1) 6) r))))
