(in-package "GPOLY")

(include-book "runtime-p-polynomial-algebra")

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

; The aggregate additive laws are usable without recursive runtime definitions.
(defthm runtime-p-poly-add-associative-minimal-theory-client
  (equal
   (runtime-p-poly-add (runtime-p-poly-add x y p) z p)
   (runtime-p-poly-add x (runtime-p-poly-add y z p) p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-add-associative))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-poly-add-commutative-minimal-theory-client
  (equal (runtime-p-poly-add x y p)
         (runtime-p-poly-add y x p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-add-commutative))
           :in-theory (theory 'minimal-theory))))

(defthm runtime-p-poly-sub-reconstruction-minimal-theory-client
  (equal (runtime-p-poly-add (runtime-p-poly-sub x y p) y p)
         (runtime-p-normalize x p))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-poly-sub-reconstruction))
           :in-theory (theory 'minimal-theory))))

; Nontrivial composite-modulus execution evidence for inverse, involution, and
; exact subtraction reconstruction.
(assert-event
 (equal (runtime-p-poly-add
         (runtime-p-poly-neg '(1 5 3) 6) '(1 5 3) 6)
        nil))
(assert-event
 (equal (runtime-p-poly-neg (runtime-p-poly-neg '(1 5 3) 6) 6)
        '(1 5 3)))
(assert-event
 (equal (runtime-p-poly-add
         (runtime-p-poly-sub '(1 5 0) '(4 2 3) 6) '(4 2 3) 6)
        '(1 5)))

; A malformed modulus continues to select the established modulus-2 fallback.
(assert-event
 (equal (runtime-p-poly-sub '(7 4 3) '(2 9) 'malformed)
        (runtime-p-poly-sub '(7 4 3) '(2 9) 2)))

; A dotted input is totalized and normalized: its atomic tail is ignored, so
; additive identity returns the canonical polynomial rather than the raw input.
(assert-event
 (and (equal (runtime-p-poly-add nil '(1 8 0 . 9) 6)
             (runtime-p-normalize '(1 8 0 . 9) 6))
      (equal (runtime-p-normalize '(1 8 0 . 9) 6) '(1 2))
      (not (equal (runtime-p-normalize '(1 8 0 . 9) 6)
                  '(1 8 0 . 9)))))
