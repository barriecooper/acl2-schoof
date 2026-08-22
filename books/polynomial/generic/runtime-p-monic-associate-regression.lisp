(in-package "GPOLY")

(include-book "runtime-p-monic-associate")

; Inverse-leading-coefficient scaling of 2+3x over F7.
(assert-event
 (equal (runtime-p-poly-monic-normalize '(2 3) 7) '(3 1)))

; A genuinely multi-step nonmonic division has the same exact remainder.
(assert-event
 (and (equal (runtime-p-remainder '(1 2 3 4) '(2 3) 7) '(5))
      (equal (runtime-p-remainder
              '(1 2 3 4)
              (runtime-p-poly-monic-normalize '(2 3) 7) 7)
             '(5))))

(assert-event
 (and (equal (runtime-p-remainder '(2 5 3) '(2 3) 7) nil)
      (equal (runtime-p-remainder
              '(2 5 3) (runtime-p-poly-monic-normalize '(2 3) 7) 7)
             nil)))

(assert-event
 (equal (runtime-p-remainder '(1) '(2 3) 7)
        (runtime-p-remainder
         '(1) (runtime-p-poly-monic-normalize '(2 3) 7) 7)))

(assert-event
 (equal (runtime-p-remainder nil '(2 3) 7)
        (runtime-p-remainder
         nil (runtime-p-poly-monic-normalize '(2 3) 7) 7)))

; Raw dotted tails and trailing zeros normalize before both operations.
(assert-event
 (and (equal (runtime-p-poly-monic-normalize '(2 3 0 . bad) 7) '(3 1))
      (equal (runtime-p-remainder '(1 2 3 4 0 . bad) '(2 3 0 . bad) 7)
             (runtime-p-remainder
              '(1 2 3 4 0 . bad)
              (runtime-p-poly-monic-normalize '(2 3 0 . bad) 7) 7))))

; Malformed p is exactly the effective-modulus-2 fallback.
(assert-event
 (and (equal (runtime-p-poly-monic-normalize '(2 3) 'bad)
             (runtime-p-poly-monic-normalize '(2 3) 2))
      (equal (runtime-p-remainder '(3 4 1) '(1 1) 'bad)
             (runtime-p-remainder
              '(3 4 1)
              (runtime-p-poly-monic-normalize '(1 1) 'bad) 'bad))))

; Composite execution is total; no field or remainder-invariance theorem is
; asserted for this value.
(assert-event
 (equal (runtime-p-poly-monic-normalize '(1 2) 9) '(2 4)))

(defthm runtime-p-remainder-of-monic-associate-minimal-theory-client
  (implies
   (and (dm::primep (runtime-p-effective-modulus p))
        (consp (runtime-p-normalize g p)))
   (equal (runtime-p-remainder f g p)
          (runtime-p-remainder
           f (runtime-p-poly-monic-normalize g p) p)))
  :rule-classes nil
  :hints
  (("Goal"
    :in-theory (theory 'minimal-theory)
    :use ((:instance runtime-p-remainder-of-poly-monic-normalize)))))
