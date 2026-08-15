(in-package "GPOLY")

(include-book "runtime-p-representation")

; Concrete execution covers prime, composite, and malformed moduli.  The
; composite/malformed cases are representation tests, not field claims.
(assert-event (equal (runtime-p-effective-modulus 7) 7))
(assert-event (equal (runtime-p-effective-modulus 11) 11))
(assert-event (equal (runtime-p-effective-modulus 6) 6))
(assert-event (equal (runtime-p-effective-modulus 1) 2))
(assert-event (equal (runtime-p-effective-modulus 'bad) 2))
(assert-event (equal (runtime-p-coefficient-fix -1 7) 6))
(assert-event (equal (runtime-p-coefficient-fix 25 11) 3))
(assert-event (equal (runtime-p-normalize 'bad 7) nil))
(assert-event (equal (runtime-p-normalize '(1 2 . bad) 7) '(1 2)))
(assert-event (equal (runtime-p-normalize '(1 2 0 0) 7) '(1 2)))
(assert-event (equal (runtime-p-poly-add '(1 2) '(6 3) 7) '(0 5)))
(assert-event (equal (runtime-p-poly-neg '(1 2) 7) '(6 5)))
(assert-event (equal (runtime-p-poly-mul '(1 2) '(3 4) 7) '(3 3 1)))
(assert-event (equal (runtime-p-poly-mul '(1 2) '(3 4) 6) '(3 4 2)))
(assert-event (equal (runtime-p-unrank 0 99 7) nil))
(assert-event (equal (runtime-p-rank (runtime-p-unrank 3 0 7) 7) 0))
(assert-event (equal (runtime-p-rank (runtime-p-unrank 3 342 7) 7) 342))
; UNRANK totalizes out-of-range K by NFIX and truncation to WIDTH digits.
(assert-event (equal (runtime-p-unrank 2 50 7) '(1 0)))

(defthm runtime-p-normalize-pfield-correspondence-client
  (equal (runtime-p-normalize '(8 -1 0) (gfield::pfield-modulus))
         (pfield-normalize '(8 -1 0)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-normalize-pfield-correspondence
                          (x '(8 -1 0)))))))

(defthm runtime-p-multiplication-pfield-correspondence-client
  (equal (runtime-p-poly-mul '(1 2) '(3 4) (gfield::pfield-modulus))
         (pfield-poly-mul '(1 2) '(3 4)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-poly-mul-pfield-correspondence
                          (x '(1 2)) (y '(3 4)))))))

(defthm runtime-p-coding-round-trip-client
  (equal (runtime-p-rank (runtime-p-unrank 3 342 7) 7) 342)
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-rank-of-unrank
                          (width 3) (k 342) (p 7))))))
