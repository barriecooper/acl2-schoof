(in-package "GPOLY")

(include-book "runtime-p-polynomial-mul-laws")

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

; Nontrivial composite-modulus execution evidence for both distributive orders.
(assert-event
 (equal (runtime-p-poly-mul
         '(1 2 3) (runtime-p-poly-add '(4 5) '(2 1 1) 6) 6)
        (runtime-p-poly-add
         (runtime-p-poly-mul '(1 2 3) '(4 5) 6)
         (runtime-p-poly-mul '(1 2 3) '(2 1 1) 6) 6)))
(assert-event
 (equal (runtime-p-poly-mul
         (runtime-p-poly-add '(1 2 3) '(4 5) 6) '(2 1 1) 6)
        (runtime-p-poly-add
         (runtime-p-poly-mul '(1 2 3) '(2 1 1) 6)
         (runtime-p-poly-mul '(4 5) '(2 1 1) 6) 6)))

; A malformed modulus continues to select the established modulus-2 fallback.
(assert-event
 (equal (runtime-p-poly-mul '(3 2 5) '(4 3) 'malformed)
        (runtime-p-poly-mul '(3 2 5) '(4 3) 2)))

(defthm runtime-p-poly-mul-commutative-minimal-theory-client
  (equal (runtime-p-poly-mul x y p)
         (runtime-p-poly-mul y x p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-mul-commutative))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-poly-mul-left-distributive-minimal-theory-client
  (equal
   (runtime-p-poly-mul x (runtime-p-poly-add y z p) p)
   (runtime-p-poly-add (runtime-p-poly-mul x y p)
                       (runtime-p-poly-mul x z p) p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-mul-left-distributive))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-poly-mul-right-distributive-minimal-theory-client
  (equal
   (runtime-p-poly-mul (runtime-p-poly-add x y p) z p)
   (runtime-p-poly-add (runtime-p-poly-mul x z p)
                       (runtime-p-poly-mul y z p) p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-mul-right-distributive))
           :in-theory (theory 'minimal-theory))))
