(in-package "GFIELD")
(include-book "kernel")

; Field-only algebra for the X-CERT coordinate calculation.  The residual
; generators below are explicit expressions, not hypotheses that vanish.
; Curve-semantic interpretation is deliberately outside this book.

(defund xcert-gxl (xl xab xc q) (field-sub (field-add (field-add xl xab) xc) (field-mul q q)))
(defund xcert-gxr (xr xa xbc tt) (field-sub (field-add (field-add xr xa) xbc) (field-mul tt tt)))
(defund xcert-gxab (xab xa xb p) (field-sub (field-add (field-add xab xa) xb) (field-mul p p)))
(defund xcert-gxbc (xbc xb xc r) (field-sub (field-add (field-add xbc xb) xc) (field-mul r r)))
(defund xcert-dx (xl xr) (field-sub xl xr))
(defund xcert-telescope (xl xr xab xbc xa xb xc p q r tt)
 (field-add (field-sub (field-sub (xcert-gxl xl xab xc q) (xcert-gxr xr xa xbc tt))
                       (xcert-gxab xab xa xb p))
            (xcert-gxbc xbc xb xc r)))
(defund xcert-remainder (p q r tt xa xc)
 (field-add (field-add (field-sub (field-mul q q) (field-mul p p))
                       (field-sub (field-mul r r) (field-mul tt tt)))
            (field-add (field-sub xa xc) (field-sub xa xc))))
(defund xcert-h (p q r xa xc)
 (field-sub (field-mul (field-sub p r) (field-add p q)) (field-sub xa xc)))
(defund xcert-s (p q r tt) (field-sub (field-add p q) (field-add r tt)))
(defund xcert-c (p q r tt) (field-add (field-sub (field-add p q) r) tt))

(local (defthm field-mul-of-neg-right-local
 (equal (field-mul x (field-neg y)) (field-neg (field-mul x y)))
 :hints (("Goal" :use ((:instance field-additive-inverse-unique (x (field-mul x y)) (y (field-mul x (field-neg y))))
                        (:instance field-mul-left-distributive (x x) (y y) (z (field-neg y))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-mul-left-distributive field-add-inverse-right field-mul-zero-right field-fix-of-mul))))))
(local (defthm field-add-inverse-middle-local
 (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
 :hints (("Goal" :use ((:instance field-add-associative (x x) (y (field-neg x)) (z y)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-inverse-right field-add-zero-left field-fix-idempotent))))))
(local (defthm field-add-swap-first-two-local
 (equal (field-add x (field-add y z)) (field-add y (field-add x z)))
 :hints (("Goal" :use ((:instance field-add-associative (x x) (y y) (z z))
                        (:instance field-add-associative (x y) (y x) (z z))
                        (:instance field-add-commutative (x x) (y y)))
          :in-theory (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))
(local (defthm field-add-inverse-shuffle-local
 (equal (field-add x (field-add y (field-add (field-neg x) z))) (field-add y (field-fix z)))
 :hints (("Goal" :use ((:instance field-add-swap-first-two-local (x x) (y y) (z (field-add (field-neg x) z)))
                        (:instance field-add-inverse-middle-local (x x) (y z)))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-swap-first-two-local field-add-inverse-middle-local field-add-fix-right))))))
(local (defthm field-neg-of-add-local
 (equal (field-neg (field-add x y)) (field-add (field-neg x) (field-neg y)))
 :hints (("Goal" :use ((:instance field-additive-inverse-unique
                         (x (field-add x y)) (y (field-add (field-neg x) (field-neg y)))))
          :in-theory (union-theories (theory 'minimal-theory)
                       '(field-add-associative field-add-inverse-shuffle-local field-add-inverse-right
                         field-add-zero-left field-fix-of-add field-fix-of-neg))))))
(local (defthm field-mul-of-neg-left-local
 (equal (field-mul (field-neg x) y) (field-neg (field-mul x y)))
 :hints (("Goal" :use ((:instance field-mul-commutative (x (field-neg x)) (y y))
                        (:instance field-mul-commutative (x y) (y x))
                        (:instance field-mul-of-neg-right-local (x y) (y x)))
          :in-theory (theory 'minimal-theory)))))

(local (defthm field-xcert-s-alignment-local
 (equal (field-sub (field-add p q) (field-add r tt))
        (field-sub (field-sub (field-add p q) r) tt))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (union-theories (theory 'minimal-theory)
           '(field-sub field-neg-of-add-local field-add-associative field-fix-of-add field-fix-of-neg))))))
(local (defthm field-difference-of-squares-local
 (equal (field-mul (field-add a b) (field-sub a b))
        (field-sub (field-mul a a) (field-mul b b)))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (union-theories (theory 'minimal-theory)
           '(field-sub field-mul-left-distributive field-mul-right-distributive
             field-mul-associative field-mul-commutative field-mul-of-neg-right-local
             field-mul-of-neg-left-local field-neg-of-add-local field-add-associative
             field-add-commutative field-add-swap-first-two-local field-add-inverse-middle-local
             field-add-inverse-shuffle-local field-add-inverse-left field-add-inverse-right
             field-add-zero-left field-add-zero-right field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local (defthm field-add-cancel-separated-local
 (equal (field-add b (field-add c (field-add d (field-add (field-neg b) e))))
        (field-add c (field-add d (field-fix e))))
 :hints (("Goal" :use ((:instance field-add-swap-first-two-local
                         (x b) (y c) (z (field-add d (field-add (field-neg b) e))))
                        (:instance field-add-inverse-shuffle-local (x b) (y d) (z e)))
          :in-theory (union-theories (theory 'minimal-theory) '(field-add-fix-right))))))

(local (defthm field-square-minus-double-sum-local
 (equal
  (field-sub (field-mul (field-add x y) (field-add x y))
             (field-add (field-mul x (field-add z y))
                        (field-mul x (field-add z y))))
  (field-add (field-mul y y)
             (field-sub (field-mul x x)
                        (field-add (field-mul x z) (field-mul x z)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :in-theory (union-theories (theory 'minimal-theory)
           '(field-sub field-mul-left-distributive field-mul-right-distributive
             field-mul-associative field-mul-commutative field-mul-of-neg-right-local
             field-mul-of-neg-left-local field-neg-of-add-local field-neg-of-neg
             field-add-associative field-add-commutative field-add-swap-first-two-local
             field-add-inverse-middle-local field-add-inverse-shuffle-local field-add-cancel-separated-local
             field-add-inverse-left field-add-inverse-right field-add-zero-left field-add-zero-right
             field-fix-of-add field-fix-of-mul field-fix-of-neg field-add-fix-left field-add-fix-right))))))

(local (defthm field-sub-square-minus-double-product-local
 (equal
  (field-sub (field-mul (field-sub p r) (field-sub p r))
             (field-add (field-mul (field-sub p r) p)
                        (field-mul (field-sub p r) p)))
  (field-sub (field-mul r r) (field-mul p p)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess) :use ((:instance field-add-swap-first-two-local
                   (x (field-neg (field-mul p p)))
                   (y (field-neg (field-mul p r)))
                   (z (field-zero)))
        (:instance field-add-inverse-shuffle-local
                   (x (field-mul p r))
                   (y (field-mul r r))
                   (z (field-neg (field-mul p p)))))
 :in-theory (union-theories (theory 'minimal-theory)
           '(field-sub field-mul-left-distributive field-mul-right-distributive
             field-mul-associative field-mul-commutative field-mul-of-neg-right-local
             field-mul-of-neg-left-local field-neg-of-add-local field-neg-of-neg
             field-add-associative field-add-commutative field-add-swap-first-two-local
             field-add-inverse-middle-local field-add-inverse-shuffle-local field-add-cancel-separated-local
             field-add-inverse-left field-add-inverse-right field-add-zero-left field-add-zero-right
             field-fix-of-add field-fix-of-mul field-fix-of-neg field-add-fix-left field-add-fix-right))))))

(local (defthm field-xcert-core-quadratic-local
 (equal
  (field-sub
   (field-mul (field-sub (field-add p q) r) (field-sub (field-add p q) r))
   (field-add (field-mul (field-sub p r) (field-add p q))
              (field-mul (field-sub p r) (field-add p q))))
  (field-add (field-sub (field-mul q q) (field-mul p p)) (field-mul r r)))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance field-square-minus-double-sum-local
                           (x (field-sub p r)) (y q) (z p))
                (:instance field-sub-square-minus-double-product-local))
          :in-theory
          (union-theories (theory 'minimal-theory)
           '(field-sub field-add-associative field-add-commutative
             field-neg-of-add-local field-neg-of-neg field-fix-of-add field-fix-of-mul
             field-fix-of-neg field-add-fix-left field-add-fix-right))))))

(local (defthm field-xcert-remainder-literal-local
 (equal
  (field-add
   (field-neg
    (field-add
     (field-sub (field-mul (field-sub p r) (field-add p q)) (field-sub xa xc))
     (field-sub (field-mul (field-sub p r) (field-add p q)) (field-sub xa xc))))
   (field-mul
    (field-add (field-sub (field-add p q) r) tt)
    (field-sub (field-add p q) (field-add r tt))))
  (field-add
   (field-add (field-sub (field-mul q q) (field-mul p p))
              (field-sub (field-mul r r) (field-mul tt tt)))
   (field-add (field-sub xa xc) (field-sub xa xc))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
          :use ((:instance field-xcert-s-alignment-local)
                (:instance field-difference-of-squares-local
                 (a (field-sub (field-add p q) r)) (b tt))
                (:instance field-xcert-core-quadratic-local))
          :in-theory
          (union-theories (theory 'minimal-theory)
           '(field-sub field-neg-of-add-local field-neg-of-neg
             field-add-associative field-add-commutative field-add-swap-first-two-local
             field-add-inverse-middle-local field-add-inverse-shuffle-local
             field-add-inverse-left field-add-inverse-right field-add-zero-left field-add-zero-right
             field-fix-of-add field-fix-of-mul field-fix-of-neg field-add-fix-left field-add-fix-right))))
))

(local (defthm field-sub-of-subs-local
 (equal (field-sub (field-sub a u) (field-sub b v))
        (field-add (field-sub a b) (field-sub v u)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(field-sub field-neg-of-add-local field-neg-of-neg field-add-associative field-add-commutative
    field-add-swap-first-two-local field-fix-of-add field-fix-of-neg field-add-fix-left field-add-fix-right))))))
(local (defthm field-sub-triples-common-local
 (equal (field-sub (field-add (field-add a common) b) (field-add (field-add common c) d))
        (field-add (field-sub a c) (field-sub b d)))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(field-sub field-neg-of-add-local field-add-associative field-add-commutative
    field-add-swap-first-two-local field-add-inverse-shuffle-local field-neg-of-neg
    field-fix-of-add field-fix-of-neg field-add-fix-right))))))
(local (defthm xcert-left-half-local
 (equal (field-sub (xcert-gxl xl xab xc q) (xcert-gxab xab xa xb p))
  (field-add (field-add (field-sub xl xa) (field-sub xc xb))
             (field-sub (field-mul p p) (field-mul q q))))
 :hints (("Goal" :use ((:instance field-sub-of-subs-local
  (a (field-add (field-add xl xab) xc)) (u (field-mul q q))
  (b (field-add (field-add xab xa) xb)) (v (field-mul p p)))
  (:instance field-sub-triples-common-local (a xl) (common xab) (b xc) (c xa) (d xb)))
  :in-theory (union-theories (theory 'minimal-theory) '(xcert-gxl xcert-gxab field-fix-of-add field-add-fix-left))))))
(local (defthm xcert-right-half-local
 (equal (field-add (field-neg (xcert-gxr xr xa xbc tt)) (xcert-gxbc xbc xb xc r))
  (field-add (field-add (field-sub xb xr) (field-sub xc xa))
             (field-sub (field-mul tt tt) (field-mul r r))))
 :hints (("Goal" :use ((:instance field-sub-of-subs-local
  (a (field-add (field-add xbc xb) xc)) (u (field-mul r r))
  (b (field-add (field-add xr xa) xbc)) (v (field-mul tt tt))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(xcert-gxr xcert-gxbc field-sub-triples-common-local field-sub field-neg-of-add-local field-neg-of-neg
     field-add-associative field-add-commutative field-add-swap-first-two-local field-add-inverse-shuffle-local field-add-cancel-separated-local
     field-fix-of-add field-fix-of-neg field-add-fix-left field-add-fix-right))))))
(local (defthm xcert-telescope-order-local
 (equal (xcert-telescope xl xr xab xbc xa xb xc p q r tt)
  (field-add (field-sub (xcert-gxl xl xab xc q) (xcert-gxab xab xa xb p))
             (field-add (field-neg (xcert-gxr xr xa xbc tt)) (xcert-gxbc xbc xb xc r))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(xcert-telescope field-sub field-neg-of-add-local field-neg-of-neg field-add-associative
    field-add-commutative field-add-swap-first-two-local field-fix-of-add field-fix-of-neg))))))
(local (defthm xcert-xb-coordinate-bridge-local
 (equal
  (field-add (field-add (field-sub xl xa) (field-sub xc xb))
             (field-add (field-sub xb xr) (field-sub xc xa)))
  (field-add (field-sub xl xr)
             (field-add (field-sub xc xa) (field-sub xc xa))))
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(field-sub field-add-associative field-add-commutative field-add-swap-first-two-local
    field-add-inverse-shuffle-local field-add-cancel-separated-local field-neg-of-neg
    field-fix-of-add field-fix-of-neg field-add-fix-left field-add-fix-right)))))
)
(local (defthm xcert-coordinate-complement-local
 (equal
  (field-add
   (field-add (field-add (field-sub xl xa) (field-sub xc xb))
              (field-add (field-sub xb xr) (field-sub xc xa)))
   (field-add (field-sub xa xc) (field-sub xa xc)))
  (field-sub xl xr))
 :hints (("Goal" :use ((:instance xcert-xb-coordinate-bridge-local))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-sub field-neg-of-add-local field-neg-of-neg field-add-associative field-add-commutative
     field-add-swap-first-two-local field-add-inverse-shuffle-local field-add-cancel-separated-local
     field-add-inverse-left field-add-inverse-right field-add-zero-left field-add-zero-right
     field-fix-of-add field-fix-of-neg field-add-fix-left field-add-fix-right)))))
)
(local (defthm xcert-halves-plus-remainder-local
 (equal
  (field-add
   (field-add
    (field-add (field-add (field-sub xl xa) (field-sub xc xb))
               (field-sub (field-mul p p) (field-mul q q)))
    (field-add (field-add (field-sub xb xr) (field-sub xc xa))
               (field-sub (field-mul tt tt) (field-mul r r))))
   (field-add
    (field-add (field-sub (field-mul q q) (field-mul p p))
               (field-sub (field-mul r r) (field-mul tt tt)))
    (field-add (field-sub xa xc) (field-sub xa xc))))
  (field-sub xl xr))
 :hints (("Goal" :use ((:instance xcert-coordinate-complement-local))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-sub field-neg-of-add-local field-neg-of-neg field-add-associative field-add-commutative
     field-add-swap-first-two-local field-add-inverse-shuffle-local field-add-cancel-separated-local
     field-add-inverse-left field-add-inverse-right field-add-zero-left field-add-zero-right
     field-fix-of-add field-fix-of-neg field-fix-of-mul field-add-fix-left field-add-fix-right)))))
)
(defthm xcert-output-telescope
 (equal (xcert-dx xl xr)
  (field-add (xcert-telescope xl xr xab xbc xa xb xc p q r tt)
             (xcert-remainder p q r tt xa xc)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(xcert-dx xcert-remainder xcert-telescope-order-local
    xcert-left-half-local xcert-right-half-local xcert-halves-plus-remainder-local)))))
(defthm xcert-remainder-identity
 (equal (xcert-remainder p q r tt xa xc)
  (field-add (field-neg (field-add (xcert-h p q r xa xc) (xcert-h p q r xa xc)))
             (field-mul (xcert-c p q r tt) (xcert-s p q r tt))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance field-xcert-remainder-literal-local))
  :in-theory (union-theories (theory 'minimal-theory)
   '(xcert-remainder xcert-h xcert-c xcert-s field-fix-of-add field-fix-of-mul field-fix-of-neg)))))
(local (defthm field-add-sub-reassociate-local
 (equal (field-add tpart (field-add (field-neg hpart) cspart))
        (field-add (field-sub tpart hpart) cspart))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
  '(field-sub field-add-associative field-fix-of-add field-fix-of-neg))))))
(defthm xcert-composition
 (equal (xcert-dx xl xr)
  (field-add
   (field-sub (xcert-telescope xl xr xab xbc xa xb xc p q r tt)
              (field-add (xcert-h p q r xa xc) (xcert-h p q r xa xc)))
   (field-mul (xcert-c p q r tt) (xcert-s p q r tt))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance xcert-output-telescope)
        (:instance xcert-remainder-identity)
        (:instance field-add-sub-reassociate-local
         (tpart (xcert-telescope xl xr xab xbc xa xb xc p q r tt))
         (hpart (field-add (xcert-h p q r xa xc) (xcert-h p q r xa xc)))
         (cspart (field-mul (xcert-c p q r tt) (xcert-s p q r tt)))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-fix-of-add field-add-fix-left field-add-fix-right)))))
