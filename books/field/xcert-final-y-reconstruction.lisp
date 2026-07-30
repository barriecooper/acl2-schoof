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
