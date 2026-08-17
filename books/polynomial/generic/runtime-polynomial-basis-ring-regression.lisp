(in-package "GPOLY")

(include-book "runtime-polynomial-basis-ring")

(defconst *runtime-ring-f7x2* '(:polynomial-basis 7 (1 0 1)))
(defconst *runtime-ring-z6* '(:polynomial-basis 6 (1 0 1)))
(defconst *runtime-ring-reducible* '(:polynomial-basis 7 (6 0 1)))

; An opt-in client can obtain the complete interface without enabling any
; implementation definitions or ambient rewrite theory.
(defthm runtime-polynomial-basis-ring-minimal-client
  (and (equal (runtime-polynomial-basis-add x y descriptor)
              (runtime-polynomial-basis-add y x descriptor))
       (equal (runtime-polynomial-basis-mul
               (runtime-polynomial-basis-mul x y descriptor) z descriptor)
              (runtime-polynomial-basis-mul
               x (runtime-polynomial-basis-mul y z descriptor) descriptor))
       (equal (runtime-polynomial-basis-mul
               x (runtime-polynomial-basis-add y z descriptor) descriptor)
              (runtime-polynomial-basis-add
               (runtime-polynomial-basis-mul x y descriptor)
               (runtime-polynomial-basis-mul x z descriptor) descriptor)))
  :rule-classes nil
  :hints (("Goal"
           :use runtime-polynomial-basis-commutative-ring-laws
           :in-theory (theory 'minimal-theory))))

(assert-event
 (and
  ; Raw dotted and trailing-zero inputs; the products before reduction have
  ; degree greater than the quadratic modulus.
  (let ((x '(3 2 0 . raw)) (y '(5 1 4 0)) (z '(6 3 2)))
    (and (equal (runtime-polynomial-basis-mul
                 (runtime-polynomial-basis-mul x y *runtime-ring-f7x2*)
                 z *runtime-ring-f7x2*)
                (runtime-polynomial-basis-mul
                 x (runtime-polynomial-basis-mul y z *runtime-ring-f7x2*)
                 *runtime-ring-f7x2*))
         (equal (runtime-polynomial-basis-mul
                 x (runtime-polynomial-basis-add y z *runtime-ring-f7x2*)
                 *runtime-ring-f7x2*)
                (runtime-polynomial-basis-add
                 (runtime-polynomial-basis-mul x y *runtime-ring-f7x2*)
                 (runtime-polynomial-basis-mul x z *runtime-ring-f7x2*)
                 *runtime-ring-f7x2*))))
  ; No primality is used: Z/6Z coefficients still give a commutative ring.
  (equal (runtime-polynomial-basis-mul
          (runtime-polynomial-basis-mul '(5 4 3) '(4 5 2) *runtime-ring-z6*)
          '(3 1) *runtime-ring-z6*)
         (runtime-polynomial-basis-mul
          '(5 4 3)
          (runtime-polynomial-basis-mul '(4 5 2) '(3 1) *runtime-ring-z6*)
          *runtime-ring-z6*))
  ; X^2-1 is reducible, which is irrelevant to distributivity.
  (equal (runtime-polynomial-basis-mul
          '(2 4) (runtime-polynomial-basis-add
                   '(6 3) '(5 2) *runtime-ring-reducible*)
          *runtime-ring-reducible*)
         (runtime-polynomial-basis-add
          (runtime-polynomial-basis-mul '(2 4) '(6 3)
                                        *runtime-ring-reducible*)
          (runtime-polynomial-basis-mul '(2 4) '(5 2)
                                        *runtime-ring-reducible*)
          *runtime-ring-reducible*))
  ; Identities, inverse, and malformed-descriptor totalization.
  (let ((x '(9 3 0 . raw)) (d 'malformed))
    (and (equal (runtime-polynomial-basis-add
                 x (runtime-polynomial-basis-zero d) d)
                (runtime-polynomial-basis-fix x d))
         (equal (runtime-polynomial-basis-mul
                 x (runtime-polynomial-basis-one d) d)
                (runtime-polynomial-basis-fix x d))
         (equal (runtime-polynomial-basis-add
                 x (runtime-polynomial-basis-neg x d) d)
                (runtime-polynomial-basis-zero d))))))
