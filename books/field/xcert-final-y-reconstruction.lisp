(in-package "GFIELD")
(include-book "xcert-s-reconstruction")

; Field-only staging lemmas for the final-y calculation.  In particular, this
; book contains no curve objects, classifier assumptions, or cancellation by a
; nonzero field element.

(local (defthm field-mul-of-neg-right-local
 (equal (field-mul x (field-neg y)) (field-neg (field-mul x y)))
 :hints (("Goal" :use ((:instance field-additive-inverse-unique
                         (x (field-mul x y)) (y (field-mul x (field-neg y))))
                        (:instance field-mul-left-distributive
                         (x x) (y y) (z (field-neg y))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-inverse-right field-mul-zero-right
                         field-fix-of-mul))))))
(local (defthm field-mul-of-neg-left-local
 (equal (field-mul (field-neg x) y) (field-neg (field-mul x y)))
 :hints (("Goal" :use ((:instance field-mul-commutative
                         (x (field-neg x)) (y y))
                        (:instance field-mul-commutative (x y) (y x))
                        (:instance field-mul-of-neg-right-local (x y) (y x)))
          :in-theory (theory 'minimal-theory)))))
(local (defthm field-add-swap-local
 (equal (field-add x (field-add y z)) (field-add y (field-add x z)))
 :hints (("Goal" :use ((:instance field-add-associative (x x)(y y)(z z))
                        (:instance field-add-associative (x y)(y x)(z z))
                        (:instance field-add-commutative (x x)(y y)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-fix-of-add))))))
(local (defthm field-add-inverse-tail-local
 (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
 :hints (("Goal" :use ((:instance field-add-associative
                         (x x) (y (field-neg x)) (z y)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-inverse-right field-add-zero-left
                         field-fix-idempotent))))))
(local (defthm field-add-inverse-shuffle-local
 (equal (field-add x (field-add y (field-add (field-neg x) z)))
        (field-add y (field-fix z)))
 :hints (("Goal" :use ((:instance field-add-swap-local
                         (x x) (y y) (z (field-add (field-neg x) z)))
                        (:instance field-add-inverse-tail-local (x x) (y z)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-swap-local field-add-inverse-tail-local
                         field-add-fix-right))))))
(local (defthm field-add-cancel-around-local
 (equal (field-add x (field-add y (field-add z (field-neg x))))
        (field-add y (field-fix z)))
 :hints (("Goal" :use ((:instance field-add-swap-local
                         (x x) (y y) (z (field-add z (field-neg x))))
                        (:instance field-add-swap-local
                         (x x) (y z) (z (field-neg x))))
          :in-theory (union-theories (theory 'minimal-theory)
           '(field-add-associative field-add-inverse-right
             field-add-zero-right field-add-fix-right))))))
(local (defthm field-add-inverse-around-short-local
 (equal (field-add x (field-add y (field-neg x))) (field-fix y))
 :hints (("Goal" :use ((:instance field-add-cancel-around-local
                         (x x) (y y) (z (field-zero))))
          :in-theory (enable field-add-zero-left field-add-zero-right
                             field-add-fix-right)))))
(local (defthm field-neg-of-add-local
 (equal (field-neg (field-add x y))
        (field-add (field-neg x) (field-neg y)))
 :hints (("Goal" :use ((:instance field-additive-inverse-unique
                         (x (field-add x y))
                         (y (field-add (field-neg x) (field-neg y)))))
          :in-theory (union-theories (theory 'minimal-theory)
           '(field-add-associative field-add-inverse-shuffle-local
             field-add-inverse-right field-add-zero-left field-fix-of-add
             field-fix-of-neg))))))

(local (defthm field-two-differences-combine-local
 (equal (field-add (field-mul (field-sub q p) sum)
                   (field-mul (field-sub p r) sum))
        (field-mul (field-sub q r) sum))
 :hints (("Goal" :in-theory (enable field-sub field-mul-right-distributive
  field-mul-of-neg-left-local field-add-associative field-add-commutative
  field-add-cancel-around-local field-fix-of-add field-fix-of-mul field-fix-of-neg)))))
(local (defthm field-square-step-local
 (equal (field-add (field-mul p p)
                   (field-mul (field-sub q p) (field-add p q)))
        (field-mul q q))
 :hints (("Goal" :in-theory (enable field-sub field-mul-left-distributive
  field-mul-right-distributive field-mul-associative field-mul-commutative
  field-mul-of-neg-left-local field-neg-of-add-local field-add-associative
  field-add-commutative field-add-inverse-tail-local
  field-add-inverse-around-short-local field-add-cancel-around-local field-fix-of-add
  field-fix-of-mul field-fix-of-neg)))))
(local (defthm xcert-coordinate-bridge-stage1-local
 (equal (field-add common (field-mul (field-sub q r) sum))
        (field-add common
         (field-add (field-mul (field-sub q p) sum)
                    (field-mul (field-sub p r) sum))))
 :hints (("Goal" :use ((:instance field-two-differences-combine-local))
          :in-theory (enable field-fix-of-add field-fix-of-mul field-fix-of-neg)))))
(local (defthm xcert-coordinate-bridge-stage2-local
 (implies (equal (field-mul (field-sub p r) sum) delta)
  (equal (field-add common
          (field-add (field-mul (field-sub q p) sum)
                     (field-mul (field-sub p r) sum)))
         (field-add common
          (field-add (field-mul (field-sub q p) sum) delta))))
 :hints (("Goal" :in-theory (enable field-fix-of-add field-fix-of-mul
                                    field-fix-of-neg)))))
(local (defthm xcert-coordinate-bridge-stage3-local
 (equal (field-add (field-add xb (field-add xab xc))
          (field-add u (field-sub xa xc)))
        (field-add (field-add (field-add xab xa) xb) u))
 :hints (("Goal" :in-theory (enable field-sub field-add-associative
  field-add-commutative field-add-swap-local field-add-inverse-shuffle-local
  field-add-cancel-around-local field-fix-of-add field-fix-of-neg)))))
(local (defthm xcert-coordinate-bridge-stage4-local
 (implies (equal (field-add (field-add xab xa) xb) square)
  (equal (field-add (field-add (field-add xab xa) xb) u)
         (field-add square u)))
 :hints (("Goal" :in-theory (enable field-fix-of-add)))))
(local (defthm xcert-coordinate-bridge-right-side-local
 (implies
  (and (equal (field-add (field-add xab xa) xb) (field-mul p p))
       (equal (field-mul (field-sub p r) (field-add p q))
              (field-sub xa xc)))
  (equal (field-add (field-add xb (field-add xab xc))
                    (field-mul (field-sub q r) (field-add p q)))
         (field-mul q q)))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance xcert-coordinate-bridge-stage1-local
    (common (field-add xb (field-add xab xc))) (sum (field-add p q)))
   (:instance xcert-coordinate-bridge-stage2-local
    (common (field-add xb (field-add xab xc))) (sum (field-add p q))
    (delta (field-sub xa xc)))
   (:instance xcert-coordinate-bridge-stage3-local
    (u (field-mul (field-sub q p) (field-add p q))))
   (:instance xcert-coordinate-bridge-stage4-local
    (square (field-mul p p))
    (u (field-mul (field-sub q p) (field-add p q))))
   (:instance field-square-step-local))
  :in-theory (theory 'minimal-theory)))))

(local (defthm xcert-coordinate-bridge-left-side-local
 (implies (equal (field-add (field-add xl xab) xc) square)
  (equal (field-add (field-add xb (field-add xab xc)) (field-sub xl xb))
         square))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable field-sub field-add-associative
  field-add-commutative field-add-swap-local field-add-inverse-shuffle-local
  field-add-cancel-around-local field-fix-of-add field-fix-of-neg)))))
(local (defthm xcert-coordinate-bridge-after-common-local
 (implies
  (and
   (equal (field-add (field-add xl xab) xc) (field-mul q q))
   (equal (field-add (field-add xab xa) xb) (field-mul p p))
   (equal (field-mul (field-sub p r) (field-add p q))
          (field-sub xa xc)))
  (equal
   (field-add (field-add xb (field-add xab xc)) (field-sub xl xb))
   (field-add (field-add xb (field-add xab xc))
              (field-mul (field-sub q r) (field-add p q)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance xcert-coordinate-bridge-left-side-local
                            (square (field-mul q q)))
                           (:instance xcert-coordinate-bridge-right-side-local))
          :in-theory (theory 'minimal-theory)))))

(defthm xcert-output-x-h-coordinate-bridge
 (implies
  (and
   (equal (field-add (field-add xl xab) xc) (field-mul q q))
   (equal (field-add (field-add xab xa) xb) (field-mul p p))
   (equal (field-mul (field-sub p r) (field-add p q))
          (field-sub xa xc)))
  (equal (field-sub xl xb)
         (field-mul (field-sub q r) (field-add p q))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance xcert-coordinate-bridge-after-common-local)
                (:instance field-add-left-cancel-forward
                 (x (field-add xb (field-add xab xc)))
                 (y (field-sub xl xb))
                 (z (field-mul (field-sub q r) (field-add p q)))))
          :in-theory (union-theories (theory 'minimal-theory)
           '(field-sub field-fix-of-add field-fix-of-mul
             field-fix-of-neg)))))


; The algebra is split into a y-only telescope and a product-only identity so
; that ACL2 never normalizes the full residual expression at once.
(local
 (defthm xcert-y-telescope-stage1-local
  (equal
   (field-add (field-neg (field-sub yb ya))
              (field-neg (field-sub yc yb)))
   (field-sub ya yc))
  :hints (("Goal" :use ((:instance field-add-inverse-shuffle-local
                           (x (field-neg yb)) (y ya) (z (field-neg yc))))
   :in-theory (union-theories (theory 'minimal-theory)
   '(field-sub field-neg-of-add-local field-neg-of-neg field-add-associative
     field-add-commutative field-add-inverse-tail-local
     field-add-inverse-around-short-local field-add-inverse-left
     field-add-inverse-right field-add-zero-left field-add-zero-right
     field-add-fix-left field-add-fix-right field-fix-of-add field-fix-of-neg))))))
(local
 (defthm xcert-y-telescope-stage2-local
  (equal (field-add (field-sub ya yc) (field-sub yc yab))
         (field-sub ya yab))
  :hints (("Goal" :use ((:instance field-add-inverse-shuffle-local (x (field-neg yc)) (y ya) (z (field-neg yab)))
                          (:instance field-add-swap-local (x ya) (y (field-neg yc))
                           (z (field-add yc (field-neg yab)))))
   :in-theory (union-theories (theory 'minimal-theory)
   '(field-sub field-neg-of-neg field-add-associative field-add-commutative
     field-add-inverse-around-short-local field-add-inverse-tail-local
     field-add-inverse-left field-add-inverse-right field-add-zero-left
     field-add-zero-right field-add-fix-left field-add-fix-right field-fix-of-add field-fix-of-neg))))))
(local
 (defthm xcert-y-telescope-stage3-local
  (equal (field-add (field-sub ya yab) (field-add yl yab))
         (field-add ya yl))
  :hints (("Goal" :use ((:instance field-add-cancel-around-local (x (field-neg yab)) (y ya) (z yl))
                          (:instance field-add-swap-local (x ya) (y (field-neg yab))
                           (z (field-add yab yl))))
   :in-theory (union-theories (theory 'minimal-theory)
   '(field-sub field-neg-of-neg field-add-associative field-add-commutative
     field-add-inverse-around-short-local field-add-inverse-tail-local
     field-add-inverse-left field-add-inverse-right field-add-zero-left
     field-add-zero-right field-add-fix-left field-add-fix-right field-fix-of-add field-fix-of-neg))))))
(local
 (defthm xcert-y-telescope-stage4-local
  (equal (field-add (field-add ya yl) (field-neg (field-add yr ya)))
         (field-sub yl yr))
  :hints (("Goal" :use ((:instance field-add-cancel-around-local (x ya) (y yl) (z (field-neg yr))))
   :in-theory (union-theories (theory 'minimal-theory)
   '(field-sub field-neg-of-add-local field-add-associative
     field-add-commutative field-add-inverse-around-short-local
     field-add-inverse-tail-local field-add-inverse-left
     field-add-inverse-right field-add-zero-left field-add-zero-right
     field-add-fix-left field-add-fix-right field-fix-of-add field-fix-of-neg))))))
(local
 (defthm xcert-y-ordinate-telescope-local
  (equal
   (field-add
    (field-add
     (field-add
      (field-add (field-neg (field-sub yb ya))
                 (field-neg (field-sub yc yb)))
      (field-sub yc yab))
     (field-add yl yab))
    (field-neg (field-add yr ya)))
   (field-sub yl yr))
  :hints (("Goal" :use ((:instance xcert-y-telescope-stage1-local)
                          (:instance xcert-y-telescope-stage2-local)
                          (:instance xcert-y-telescope-stage3-local)
                          (:instance xcert-y-telescope-stage4-local))
   :in-theory (union-theories (theory 'minimal-theory)
    '(xcert-y-telescope-stage1-local xcert-y-telescope-stage2-local
      xcert-y-telescope-stage3-local xcert-y-telescope-stage4-local
      field-add-associative field-add-fix-left field-add-fix-right field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-add-cancel-after-7-local
  (equal (field-add x (field-add a (field-add b (field-add c (field-add d (field-add e (field-add f (field-add g (field-add (field-neg x) z)))))))))
         (field-add a (field-add b (field-add c (field-add d (field-add e (field-add f (field-add g (field-fix z)))))))))
  :hints (("Goal" :use ((:instance field-add-inverse-shuffle-local
                           (y (field-add a (field-add b (field-add c (field-add d (field-add e (field-add f g)))))))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-associative field-add-fix-left field-add-fix-right
      field-fix-of-add field-fix-of-neg))))))
(local
 (defthm field-add-cancel-after-6-local
  (equal (field-add x (field-add a (field-add b (field-add c (field-add d (field-add e (field-add f (field-add (field-neg x) z))))))))
         (field-add a (field-add b (field-add c (field-add d (field-add e (field-add f (field-fix z))))))))
  :hints (("Goal" :use ((:instance field-add-inverse-shuffle-local
                           (y (field-add a (field-add b (field-add c (field-add d (field-add e f))))))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-associative field-add-fix-left field-add-fix-right
      field-fix-of-add field-fix-of-neg))))))
(local
 (defthm field-add-cancel-after-3-local
  (equal (field-add x (field-add a (field-add b (field-add c (field-add (field-neg x) z)))))
         (field-add a (field-add b (field-add c (field-fix z)))))
  :hints (("Goal" :use ((:instance field-add-inverse-shuffle-local
                           (y (field-add a (field-add b c)))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-associative field-add-fix-left field-add-fix-right
      field-fix-of-add field-fix-of-neg))))))
(local
 (defthm field-add-cancel-after-2-local
  (equal (field-add x (field-add a (field-add b (field-add (field-neg x) z))))
         (field-add a (field-add b (field-fix z))))
  :hints (("Goal" :use ((:instance field-add-inverse-shuffle-local
                           (y (field-add a b))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-associative field-add-fix-left field-add-fix-right
      field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-add-cancel-after-4-local
  (equal (field-add x (field-add a (field-add b (field-add c (field-add d (field-add (field-neg x) z)))))) (field-add a (field-add b (field-add c (field-add d (field-fix z))))))
  :hints (("Goal" :use ((:instance field-add-inverse-shuffle-local (y (field-add a (field-add b (field-add c d))))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-associative field-add-fix-left field-add-fix-right
      field-fix-of-add field-fix-of-neg))))))

(local
 (defthm field-add-cancel-after-4-end-local
  (equal
   (field-add x (field-add a (field-add b (field-add c
    (field-add d (field-neg x))))))
   (field-add a (field-add b (field-add c (field-fix d)))))
  :hints (("Goal" :use ((:instance field-add-cancel-after-4-local
                           (z (field-zero))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-zero-right field-add-fix-right field-fix-of-add
      field-fix-of-neg))))))

(local
 (defthm field-add-cancel-after-1-local
  (equal (field-add x (field-add a (field-add (field-neg x) z)))
         (field-add a (field-fix z)))
  :hints (("Goal" :use ((:instance field-add-inverse-shuffle-local
                           (y a)))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-add-fix-right field-fix-of-add field-fix-of-neg))))))

(local
 (defthm xcert-y-product-balance-local
  (equal
   (field-add
    (field-mul (field-sub xa xl)
               (field-sub (field-add p q) (field-add r tt)))
    (field-add
     (field-mul p (field-sub xb xa))
     (field-add
      (field-mul r (field-sub xc xb))
      (field-add
       (field-neg (field-mul q (field-sub xc xab)))
       (field-add
        (field-neg (field-mul q (field-sub xab xl)))
        (field-mul tt (field-sub xa xl)))))))
   (field-neg
    (field-add
     (field-mul (field-sub p r) (field-sub xl xb))
     (field-mul (field-sub r q) (field-sub xa xc)))))
  :hints (("Goal" :do-not '(preprocess)
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-sub field-mul-left-distributive field-mul-right-distributive
      field-mul-associative field-mul-commutative field-mul-of-neg-right-local
      field-mul-of-neg-left-local field-neg-of-add-local field-neg-of-neg
      field-add-associative field-add-commutative field-add-swap-local
      field-add-inverse-tail-local field-add-inverse-shuffle-local
      field-add-cancel-around-local field-add-inverse-around-short-local
      field-add-inverse-left field-add-inverse-right field-add-zero-left
      field-add-zero-right field-add-cancel-after-7-local
      field-add-cancel-after-6-local field-add-cancel-after-3-local
      field-add-cancel-after-2-local field-add-cancel-after-4-local field-add-cancel-after-4-end-local field-add-fix-left field-add-fix-right field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm xcert-y-six-residual-decomposition-local
  (equal
   (field-sub
    (field-sub yl yr)
    (field-add
     (field-mul (field-sub p r) (field-sub xl xb))
     (field-mul (field-sub r q) (field-sub xa xc))))
   (field-add
    (field-mul (field-sub xa xl)
               (field-sub (field-add p q) (field-add r tt)))
    (field-add
     (field-sub (field-mul p (field-sub xb xa)) (field-sub yb ya))
     (field-add
      (field-sub (field-mul r (field-sub xc xb)) (field-sub yc yb))
      (field-add
       (field-neg (field-sub (field-mul q (field-sub xc xab))
                             (field-sub yc yab)))
       (field-add
        (field-sub (field-add yl yab)
                   (field-mul q (field-sub xab xl)))
        (field-neg (field-sub (field-add yr ya)
                              (field-mul tt (field-sub xa xl))))))))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
   :use ((:instance xcert-y-ordinate-telescope-local)
         (:instance xcert-y-product-balance-local))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-sub field-neg-of-add-local field-neg-of-neg
      field-add-associative field-add-commutative field-add-swap-local
      field-add-inverse-tail-local field-add-inverse-shuffle-local
      field-add-cancel-around-local field-add-inverse-around-short-local
      field-add-inverse-left field-add-inverse-right field-add-zero-left
      field-add-zero-right field-add-cancel-after-3-local
      field-add-cancel-after-2-local field-add-cancel-after-1-local field-add-fix-left field-add-fix-right field-fix-of-add field-fix-of-neg))))))

(local
 (defthm xcert-y-residuals-vanish-local
  (implies
   (and
    (equal (field-sub (field-add p q) (field-add r tt)) (field-zero))
    (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
    (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
    (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
    (equal (field-add yl yab) (field-mul q (field-sub xab xl)))
    (equal (field-add yr ya) (field-mul tt (field-sub xa xl))))
   (equal
    (field-sub (field-sub yl yr)
     (field-add (field-mul (field-sub p r) (field-sub xl xb))
                (field-mul (field-sub r q) (field-sub xa xc))))
    (field-zero)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance xcert-y-six-residual-decomposition-local))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-sub-self field-fix-idempotent field-fix-of-zero field-neg-of-zero field-mul-zero-right field-add-zero-left
      field-add-zero-right field-fix-of-add
      field-fix-of-mul field-fix-of-neg))))))

(defthm xcert-y-difference-six-residual-reduction
 (implies
  (and
   (equal (field-sub (field-add p q) (field-add r tt)) (field-zero))
   (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
   (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
   (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
   (equal (field-add yl yab) (field-mul q (field-sub xab xl)))
   (equal (field-add yr ya) (field-mul tt (field-sub xa xl))))
  (equal (field-sub yl yr)
   (field-add (field-mul (field-sub p r) (field-sub xl xb))
              (field-mul (field-sub r q) (field-sub xa xc)))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance xcert-y-residuals-vanish-local)
                        (:instance field-sub-equal-zero-implies-fixed-equal
                         (first (field-sub yl yr))
                         (second (field-add
                             (field-mul (field-sub p r) (field-sub xl xb))
                             (field-mul (field-sub r q) (field-sub xa xc))))))
          :in-theory (union-theories (theory 'minimal-theory)
           '(field-sub field-fix-of-add field-fix-of-mul field-fix-of-neg)))))

; Once the two public reconstruction results above have supplied the two
; coordinate differences, only this bounded three-factor cancellation remains.
(local
 (defthm field-reverse-subtraction-local
  (equal (field-sub x y) (field-neg (field-sub y x)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-sub field-neg-of-add-local field-neg-of-neg
              field-add-commutative field-add-fix-left field-fix-of-add
              field-fix-of-neg))))))

(local
 (defthm field-three-factor-swap-local
  (equal (field-mul b (field-mul a c))
         (field-mul a (field-mul b c)))
  :hints (("Goal"
           :use ((:instance field-mul-associative (x b) (y a) (z c))
                 (:instance field-mul-associative (x a) (y b) (z c))
                 (:instance field-mul-commutative (x b) (y a)))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-fix-of-mul))))))

(local
 (defthm field-opposite-three-factor-sum-local
  (equal
   (field-add (field-mul a (field-mul b c))
              (field-mul (field-neg b) (field-mul a c)))
   (field-zero))
  :hints (("Goal"
           :use ((:instance field-mul-of-neg-left-local
                            (x b) (y (field-mul a c)))
                 (:instance field-three-factor-swap-local))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-add-inverse-right field-fix-of-add field-fix-of-mul
              field-fix-of-neg))))))

(defthm xcert-field-only-final-y-equal
 (implies
  (and
   (equal (field-add (field-add xl xab) xc) (field-mul q q))
   (equal (field-add (field-add xab xa) xb) (field-mul p p))
   (equal (field-mul (field-sub p r) (field-add p q))
          (field-sub xa xc))
   (equal (field-sub (field-add p q) (field-add r tt)) (field-zero))
   (equal (field-mul p (field-sub xb xa)) (field-sub yb ya))
   (equal (field-mul r (field-sub xc xb)) (field-sub yc yb))
   (equal (field-mul q (field-sub xc xab)) (field-sub yc yab))
   (equal (field-add yl yab) (field-mul q (field-sub xab xl)))
   (equal (field-add yr ya) (field-mul tt (field-sub xa xl))))
  (equal (field-fix yl) (field-fix yr)))
 :rule-classes nil
 :hints
 (("Goal"
   :do-not '(preprocess)
   :use ((:instance xcert-y-difference-six-residual-reduction)
         (:instance xcert-output-x-h-coordinate-bridge)
         (:instance field-reverse-subtraction-local (x r) (y q))
         (:instance field-opposite-three-factor-sum-local
                    (a (field-sub p r))
                    (b (field-sub q r))
                    (c (field-add p q)))
         (:instance field-sub-equal-zero-implies-fixed-equal
                    (first yl) (second yr)))
   :in-theory (union-theories (theory 'minimal-theory)
    '(field-fix-of-add field-fix-of-mul field-fix-of-neg)))))
