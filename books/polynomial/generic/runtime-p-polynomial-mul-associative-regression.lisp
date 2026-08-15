(in-package "GPOLY")

(include-book "runtime-p-polynomial-mul-associative")

; Composite-modulus execution evidence for both association orders.
(assert-event
 (equal (runtime-p-poly-mul
         (runtime-p-poly-mul '(1 2) '(3 4) 6) '(5 1) 6)
        '(3 5 2 2)))
(assert-event
 (equal (runtime-p-poly-mul
         '(1 2) (runtime-p-poly-mul '(3 4) '(5 1) 6) 6)
        '(3 5 2 2)))

; The public theorem is usable without any recursive runtime definition.
(defthm runtime-p-poly-mul-associative-minimal-theory-client
  (equal
   (runtime-p-poly-mul
    (runtime-p-poly-mul x y p) z p)
   (runtime-p-poly-mul
    x (runtime-p-poly-mul y z p) p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-mul-associative))
           :in-theory (theory 'minimal-theory))))
