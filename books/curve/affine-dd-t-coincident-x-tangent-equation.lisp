(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-ordinate")
(include-book "affine-distinct-x-secant-identity")
(include-book "../field/two-line-telescope")
(include-book "../field/xcert-h-reconstruction")
(include-book "../field/common-summand-subtraction")

; Checkpoint 1: preserve the public ordinate theorem as a separately audited
; local consequence of precisely the eventual public premises.
(local
 (defthm dd-t-ordinate-equality-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p c)
        (affine-distinct-x-secant-relation-p b c r q)
        (affine-doubling-relation-p c tangent-slope d)
        (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal (affine-coordinates-y q) (affine-coordinates-y a)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-dd-t-coincident-x-implies-ordinate-equality
                          (p-slope p) (r-slope r) (t-slope tangent-slope)))
           :in-theory (theory 'minimal-theory)))))

; Checkpoint 2a: exact first-line orientation required by the telescope.
(local
 (defthm dd-t-first-line-local
  (implies (affine-distinct-x-secant-relation-p a b p c)
   (equal (field-sub (affine-coordinates-y b) (affine-coordinates-y a))
          (field-mul (field-fix p)
                     (field-sub (affine-coordinates-x b)
                                (affine-coordinates-x a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable affine-distinct-x-secant-relation-p)))))

; Checkpoint 2b: xq=xa and yq=ya specialize the second output-y equation.
(local
 (defthm dd-t-second-line-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p c)
        (affine-distinct-x-secant-relation-p b c r q)
        (affine-doubling-relation-p c tangent-slope d)
        (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal (field-add (affine-coordinates-y a) (affine-coordinates-y b))
          (field-mul (field-fix r)
                     (field-sub (affine-coordinates-x b)
                                (affine-coordinates-x a)))))
  :rule-classes nil
  :hints (("Goal" :use (dd-t-ordinate-equality-local)
           :in-theory (union-theories (theory 'minimal-theory)
                         '(affine-distinct-x-secant-relation-p
                           field-add-commutative))))))

; Checkpoint 3: invoke, rather than replay, the certified generic telescope.
(local
 (defthm dd-t-doubled-ordinate-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p c)
        (affine-distinct-x-secant-relation-p b c r q)
        (affine-doubling-relation-p c tangent-slope d)
        (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal (field-add (affine-coordinates-y a) (affine-coordinates-y a))
          (field-mul (field-sub (field-fix r) (field-fix p))
                     (field-sub (affine-coordinates-x b)
                                (affine-coordinates-x a)))))
  :rule-classes nil
  :hints (("Goal"
           :use (dd-t-first-line-local dd-t-second-line-local
                 (:instance field-two-line-equations-imply-doubled-first-ordinate
                  (ya (affine-coordinates-y a))
                  (yb (affine-coordinates-y b))
                  (p (field-fix p)) (r (field-fix r))
                  (delta (field-sub (affine-coordinates-x b)
                                    (affine-coordinates-x a)))))
           :in-theory (theory 'minimal-theory)))))
(include-book "../field/xcert-final-y-reconstruction")

(local
 (defthm relation-input-secant-identity-local
   (implies (affine-distinct-x-secant-relation-p first second slope output)
    (equal (field-mul (field-fix slope)
                      (field-add (affine-coordinates-y second)
                                 (affine-coordinates-y first)))
     (field-add (field-mul (affine-coordinates-x second)
                           (affine-coordinates-x second))
      (field-add (field-mul (affine-coordinates-x second)
                            (affine-coordinates-x first))
       (field-add (field-mul (affine-coordinates-x first)
                             (affine-coordinates-x first))
                  (field-fix (short-weierstrass-a)))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance affine-pair-classify-distinct-x-characterization)
                           (:instance affine-distinct-x-output-satisfies-secant-relation)
                           (:instance affine-distinct-x-secant-relation-slope-unique
                            (slope-a slope) (output-a output)
                            (slope-b (affine-distinct-x-slope first second))
                            (output-b (affine-distinct-x-output first second)))
                           (:instance affine-distinct-x-input-secant-identity))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(affine-distinct-x-secant-relation-p
                           affine-coordinates-x-of-fix
                           field-fix-of-affine-distinct-x-slope
                           field-fix-of-mul field-fix-of-add))))))

(local
 (defthm field-three-times-square-local
   (equal (field-mul (field-add (field-add (field-one) (field-one)) (field-one))
                     (field-mul x x))
          (field-add (field-mul x x)
                     (field-add (field-mul x x) (field-mul x x))))
   :hints (("Goal" :in-theory (enable field-mul-left-distributive
                                       field-fix-of-add field-fix-of-mul)))))

(local
 (defthm field-add-swap-local
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints (("Goal" :use ((:instance field-add-associative (x x) (y y) (z z))
                           (:instance field-add-associative (x y) (y x) (z z))
                           (:instance field-add-commutative (x x) (y y)))
            :in-theory (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))
(local
 (defthm tangent-numerator-xcert-shape-local
   (implies
    (equal (field-mul slope (field-add yc yc))
           (field-add
            (field-mul (field-add (field-add (field-one) (field-one)) (field-one))
                       (field-mul xc xc)) curve-a))
    (equal (field-mul slope (field-add yc yc))
           (field-add (field-mul xc xc)
                      (field-add (field-mul xc xc)
                                 (field-add (field-mul xc xc) curve-a)))))
   :hints (("Goal" :in-theory
            (enable field-mul-left-distributive field-add-associative
                    field-add-commutative field-add-swap-local field-fix-of-add
                    field-fix-of-mul)))))
(local
 (defthm tangent-input-identity-local
   (implies (affine-doubling-relation-p c slope d)
    (equal (field-mul (field-fix slope)
                      (field-add (affine-coordinates-y c) (affine-coordinates-y c)))
     (field-add (field-mul (affine-coordinates-x c) (affine-coordinates-x c))
      (field-add (field-mul (affine-coordinates-x c) (affine-coordinates-x c))
       (field-add (field-mul (affine-coordinates-x c) (affine-coordinates-x c))
                  (field-fix (short-weierstrass-a)))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance tangent-numerator-xcert-shape-local
                           (slope (field-fix slope))
                           (yc (affine-coordinates-y c))
                           (xc (affine-coordinates-x c))
                           (curve-a (field-fix (short-weierstrass-a)))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(affine-doubling-relation-p))))))

(local
 (defthm relation-x-difference-nonzero-local
   (implies (affine-distinct-x-secant-relation-p first second slope output)
    (not (equal (field-sub (affine-coordinates-x second)
                           (affine-coordinates-x first))
                (field-zero))))
   :hints (("Goal" :use ((:instance field-sub-equal-zero-implies-fixed-equal
                          (first (affine-coordinates-x second))
                          (second (affine-coordinates-x first))))
            :in-theory (union-theories (theory 'minimal-theory)
             '(affine-distinct-x-secant-relation-p field-fix-when-field-element-p
               field-element-p-of-affine-coordinates-x))))))

(local
 (defthm outer-x-difference-nonzero-local
   (implies (and (field-element-p xa) (field-element-p xq)
                 (not (equal xq xa)))
    (not (equal (field-sub xq xa) (field-zero))))
   :hints (("Goal" :use ((:instance field-sub-equal-zero-implies-fixed-equal
                          (first xq) (second xa)))
            :in-theory (enable field-fix-when-field-element-p)))))

(local
 (defthm dd-t-h-local
   (implies (and (affine-distinct-x-secant-relation-p a b p c)
                 (affine-distinct-x-secant-relation-p b c r q)
                 (affine-doubling-relation-p c t-slope d))
    (equal (field-mul (field-sub (field-fix p) (field-fix r))
                      (field-add (field-fix p) (field-fix t-slope)))
           (field-sub (affine-coordinates-x a)
                      (affine-coordinates-x c))))
   :rule-classes nil
   :hints (("Goal" :use
            ((:instance relation-input-secant-identity-local
              (first a) (second b) (slope p) (output c))
             (:instance tangent-input-identity-local (slope t-slope))
             (:instance relation-x-difference-nonzero-local
              (first b) (second c) (slope r) (output q))
             (:instance xcert-h-scalar-reconstruction
              (a (field-fix (short-weierstrass-a)))
              (p (field-fix p)) (q (field-fix t-slope)) (r (field-fix r))
              (xa (affine-coordinates-x a)) (ya (affine-coordinates-y a))
              (xb (affine-coordinates-x b)) (yb (affine-coordinates-y b))
              (xc (affine-coordinates-x c)) (yc (affine-coordinates-y c))
              (xab (affine-coordinates-x c)) (yab (affine-coordinates-y c))))
            :in-theory (union-theories (theory 'minimal-theory)
             '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
               field-fix-idempotent field-fix-when-field-element-p
               field-element-p-of-affine-coordinates-x
               field-element-p-of-affine-coordinates-y field-fix-of-add
               field-fix-of-mul field-fix-of-neg field-sub-self
               field-mul-zero-right))))))

(local
 (defthm field-add-inverse-tail-balance-local
  (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
  :hints (("Goal" :use ((:instance field-add-associative
                          (x x) (y (field-neg x)) (z y)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(field-add-inverse-right field-add-zero-left
                          field-fix-idempotent))))))

; Checkpoint 5: exact definitional balance; there is no nonzero hypothesis.
(local
 (defthm dd-t-witness-balance-local
  (equal
   (field-add (field-fix p) (field-fix tangent-slope))
   (field-add
    (field-fix r)
    (field-sub (field-add (field-fix p) (field-fix tangent-slope)) (field-fix r))))
  :hints (("Goal"
           :use ((:instance field-add-swap-local
                            (x (field-fix r)) (y (field-fix tangent-slope))
                            (z (field-neg (field-fix r))))
                 (:instance field-add-inverse-tail-balance-local
                            (x (field-fix r)) (y (field-fix tangent-slope))))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-sub field-add-associative field-add-commutative
              field-add-swap-local field-add-inverse-left
              field-add-inverse-right field-add-zero-left
              field-add-zero-right field-fix-idempotent
              field-fix-of-add field-fix-of-neg))))))

; This book starts from the already certified repeated-root relation.  All
; auxiliary normalization below is deliberately local and division-free.
(local
 (defthm field-mul-of-neg-right-local
   (equal (field-mul x (field-neg y))
          (field-neg (field-mul x y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-mul x y))
                      (y (field-mul x (field-neg y))))
           (:instance field-mul-left-distributive
                      (x x) (y y) (z (field-neg y))))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(field-add-inverse-right field-mul-zero-right
                       field-fix-of-mul))))))

(local
 (defthm field-mul-of-neg-left-local
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints (("Goal" :use ((:instance field-mul-commutative
                                    (x (field-neg x)) (y y))
                          (:instance field-mul-commutative (x y) (y x)))
            :in-theory (enable field-mul-of-neg-right-local)))))

(local
 (defthm field-add-inverse-middle-local
   (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
   :hints (("Goal" :use ((:instance field-add-associative
                                    (x x) (y (field-neg x)) (z y)))
            :in-theory (enable field-add-inverse-right field-add-zero-left
                               field-fix-idempotent)))))

(local
 (defthm field-add-swap-first-two-local
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints (("Goal" :use ((:instance field-add-associative (x x) (y y) (z z))
                          (:instance field-add-associative (x y) (y x) (z z))
                          (:instance field-add-commutative (x x) (y y)))
            :in-theory (union-theories (theory 'minimal-theory)
                                       '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-shuffle-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints (("Goal" :use ((:instance field-add-swap-first-two-local
                                    (x x) (y y)
                                    (z (field-add (field-neg x) z)))
                          (:instance field-add-inverse-middle-local (x x) (y z)))
            :in-theory (enable field-add-fix-right)))))

(local
 (defthm field-neg-of-add-local
   (equal (field-neg (field-add x y))
          (field-add (field-neg x) (field-neg y)))
   :hints (("Goal" :use ((:instance field-additive-inverse-unique
                                    (x (field-add x y))
                                    (y (field-add (field-neg x)
                                                  (field-neg y)))))
            :in-theory
            (enable field-add-associative field-add-inverse-shuffle-local
                    field-add-inverse-right field-add-zero-left
                    field-fix-of-add field-fix-of-neg)))))

; Checkpoint 6a: the first remaining field transformation, before using H.
(local
 (defthm dd-t-witness-times-telescope-factor-local
  (equal
   (field-mul (field-sub (field-add p tangent-slope) r) (field-sub r p))
   (field-add
    (field-neg (field-mul (field-sub p r) (field-add p tangent-slope)))
    (field-mul (field-sub p r) r)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive
              field-mul-right-distributive field-mul-associative
              field-mul-commutative field-mul-of-neg-left-local
              field-mul-of-neg-right-local field-neg-of-add-local
              field-neg-of-neg field-add-associative field-add-commutative
              field-add-swap-first-two-local field-add-inverse-middle-local
              field-add-inverse-shuffle-local field-add-inverse-left
              field-add-inverse-right field-add-zero-left field-add-zero-right
              field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm dd-t-multiply-telescope-local
  (implies (equal doubled (field-mul (field-sub r p) delta))
   (equal (field-mul s doubled)
          (field-mul (field-mul s (field-sub r p)) delta)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(field-mul-associative field-fix-of-mul))))))


(local
 (defthm field-neg-of-sub-reverse-local
  (equal (field-neg (field-sub x y)) (field-sub y x))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-sub field-neg-of-add-local field-neg-of-neg
              field-add-commutative field-add-fix-left field-add-fix-right field-fix-of-add field-fix-of-neg))))))

(local
 (defthm dd-t-use-h-local
  (implies
   (equal (field-mul (field-sub p r) (field-add p tangent-slope))
          (field-sub xa xc))
   (equal
    (field-mul
     (field-add
      (field-neg (field-mul (field-sub p r) (field-add p tangent-slope)))
      (field-mul (field-sub p r) r)) delta)
    (field-mul
     (field-add (field-sub xc xa) (field-mul (field-sub p r) r)) delta)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance field-neg-of-sub-reverse-local
                          (x xa) (y xc)))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm dd-t-first-input-after-second-line-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p c)
        (affine-distinct-x-secant-relation-p b c r q)
        (affine-doubling-relation-p c tangent-slope d)
        (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal
    (field-mul
     (field-fix p)
     (field-mul (field-fix r)
                (field-sub (affine-coordinates-x b)
                           (affine-coordinates-x a))))
    (field-add
     (field-mul (affine-coordinates-x b) (affine-coordinates-x b))
     (field-add
      (field-mul (affine-coordinates-x b) (affine-coordinates-x a))
      (field-add
       (field-mul (affine-coordinates-x a) (affine-coordinates-x a))
       (field-fix (short-weierstrass-a)))))))
  :rule-classes nil
  :hints (("Goal"
           :use (dd-t-second-line-local
                 (:instance relation-input-secant-identity-local
                  (first a) (second b) (slope p) (output c)))
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-mul-associative field-add-commutative
              field-fix-of-add field-fix-of-mul))))))

(local
 (defthm dd-t-secant-substitution-shape-local
  (equal
   (field-mul
    (field-add (field-sub xc xa) (field-mul (field-sub p r) r)) delta)
   (field-add
    (field-mul delta (field-mul p r))
    (field-mul (field-sub (field-sub xc xa) (field-mul r r)) delta)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive
              field-mul-right-distributive field-mul-associative
              field-mul-commutative field-mul-of-neg-left-local
              field-mul-of-neg-right-local field-neg-of-add-local
              field-neg-of-neg field-add-associative field-add-commutative
              field-add-swap-first-two-local field-add-inverse-middle-local
              field-add-inverse-shuffle-local field-add-inverse-left
              field-add-inverse-right field-add-zero-left field-add-zero-right
              field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm field-add-cancel-separated-numerator-local
  (equal (field-add b (field-add c (field-add d (field-add (field-neg b) e))))
         (field-add c (field-add d (field-fix e))))
  :hints (("Goal"
           :use ((:instance field-add-swap-first-two-local
                            (x b) (y c)
                            (z (field-add d (field-add (field-neg b) e))))
                 (:instance field-add-inverse-shuffle-local
                            (x b) (y d) (z e)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(field-add-fix-right))))))

(local
 (defthm dd-t-final-quadratic-residual-local
  (equal
   (field-add
    (field-add (field-mul xb xb)
     (field-add (field-mul xb xa)
      (field-add (field-mul xa xa) curve-a)))
    (field-mul
     (field-sub (field-sub xc xa) (field-add (field-add xa xb) xc))
     (field-sub xb xa)))
   (field-add (field-mul xa xa)
    (field-add (field-mul xa xa)
     (field-add (field-mul xa xa) curve-a))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(field-sub field-mul-left-distributive
              field-mul-right-distributive field-mul-associative
              field-mul-commutative field-mul-of-neg-left-local
              field-mul-of-neg-right-local field-neg-of-add-local
              field-neg-of-neg field-add-associative field-add-commutative
              field-add-swap-first-two-local field-add-inverse-middle-local
              field-add-inverse-shuffle-local field-add-cancel-separated-numerator-local
              field-add-inverse-left
              field-add-inverse-right field-add-zero-left field-add-zero-right
              field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

(local
 (defthm dd-t-final-product-composition-local
  (implies
   (and (equal doubled (field-mul delta factor))
        (equal (field-mul delta (field-mul factor slope)) target))
   (equal (field-mul slope doubled) target))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance field-mul-associative
                            (x slope) (y delta) (z factor))
                 (:instance field-mul-associative
                            (x delta) (y factor) (z slope))
                 (:instance field-mul-commutative
                            (x slope) (y (field-mul delta factor))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(field-fix-of-mul))))))

(local
 (defthm field-three-square-plus-a-shape-local
  (equal
   (field-add (field-mul x x)
    (field-add (field-mul x x) (field-add (field-mul x x) a)))
   (field-add
    (field-mul (field-add (field-add (field-one) (field-one)) (field-one))
               (field-mul x x)) a))
  :hints (("Goal" :use ((:instance field-three-times-square-local (x x)))
           :in-theory (union-theories (theory 'minimal-theory)
            '(field-add-associative field-fix-of-add field-fix-of-mul))))))

(local
 (defthm dd-t-public-numerator-shape-local
  (implies
   (equal (field-mul doubled slope)
          (field-add (field-mul x x)
           (field-add (field-mul x x)
            (field-add (field-mul x x) curve-a))))
   (equal
    (field-mul slope doubled)
    (field-add
     (field-mul (field-add (field-add (field-one) (field-one)) (field-one))
                (field-mul x x))
     curve-a)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance field-three-square-plus-a-shape-local
                            (x x) (a curve-a))
                 (:instance field-mul-commutative (x slope) (y doubled)))
           :in-theory (theory 'minimal-theory)))))

(defthm affine-dd-t-coincident-x-tangent-equation
 (implies
  (and
   (affine-distinct-x-secant-relation-p a b p-slope c)
   (affine-distinct-x-secant-relation-p b c r-slope q)
   (affine-doubling-relation-p c t-slope d)
   (equal (affine-coordinates-x q) (affine-coordinates-x a)))
  (equal
   (field-mul
    (field-sub
     (field-add (field-fix p-slope) (field-fix t-slope))
     (field-fix r-slope))
    (field-add (affine-coordinates-y a) (affine-coordinates-y a)))
   (field-add
    (field-mul
     (field-add (field-add (field-one) (field-one)) (field-one))
     (field-mul (affine-coordinates-x a) (affine-coordinates-x a)))
    (field-fix (short-weierstrass-a)))))
 :rule-classes nil
 :hints
 (("Goal"
   :use
   ((:instance dd-t-public-numerator-shape-local
     (doubled (field-add (affine-coordinates-y a)
                         (affine-coordinates-y a)))
     (slope (field-sub (field-add (field-fix p-slope) (field-fix t-slope))
                       (field-fix r-slope)))
     (x (affine-coordinates-x a))
     (curve-a (field-fix (short-weierstrass-a))))
    (:instance dd-t-doubled-ordinate-local
     (p p-slope) (r r-slope) (tangent-slope t-slope))
    (:instance dd-t-h-local (p p-slope) (r r-slope))
    (:instance dd-t-multiply-telescope-local
     (s (field-sub (field-add (field-fix p-slope) (field-fix t-slope))
                   (field-fix r-slope)))
     (doubled (field-add (affine-coordinates-y a)
                         (affine-coordinates-y a)))
     (p (field-fix p-slope)) (r (field-fix r-slope))
     (delta (field-sub (affine-coordinates-x b)
                       (affine-coordinates-x a))))
    (:instance dd-t-witness-times-telescope-factor-local
     (p (field-fix p-slope)) (r (field-fix r-slope))
     (tangent-slope (field-fix t-slope)))
    (:instance dd-t-use-h-local
     (p (field-fix p-slope)) (r (field-fix r-slope))
     (tangent-slope (field-fix t-slope))
     (xa (affine-coordinates-x a)) (xc (affine-coordinates-x c))
     (delta (field-sub (affine-coordinates-x b)
                       (affine-coordinates-x a))))
    (:instance dd-t-first-input-after-second-line-local
     (p p-slope) (r r-slope) (tangent-slope t-slope))
    (:instance dd-t-secant-substitution-shape-local
     (p (field-fix p-slope)) (r (field-fix r-slope))
     (xa (affine-coordinates-x a))
     (xc (affine-coordinates-x c))
     (delta (field-sub (affine-coordinates-x b)
                       (affine-coordinates-x a))))
    (:instance dd-t-final-product-composition-local
     (doubled (field-add (affine-coordinates-y a)
                         (affine-coordinates-y a)))
     (delta (field-sub (affine-coordinates-x b)
                       (affine-coordinates-x a)))
     (factor (field-sub (field-fix r-slope) (field-fix p-slope)))
     (slope (field-sub (field-add (field-fix p-slope) (field-fix t-slope))
                       (field-fix r-slope)))
     (target (field-add
              (field-mul (affine-coordinates-x a) (affine-coordinates-x a))
              (field-add
               (field-mul (affine-coordinates-x a) (affine-coordinates-x a))
               (field-add
                (field-mul (affine-coordinates-x a) (affine-coordinates-x a))
                (field-fix (short-weierstrass-a)))))))
    (:instance dd-t-final-quadratic-residual-local
     (xa (affine-coordinates-x a)) (xb (affine-coordinates-x b))
     (xc (affine-coordinates-x c))
     (curve-a (field-fix (short-weierstrass-a)))))
   :in-theory
   (union-theories
    (theory 'minimal-theory)
    '(affine-distinct-x-secant-relation-p field-three-times-square-local
      field-mul-associative field-mul-commutative
      field-fix-idempotent field-fix-of-add field-fix-of-mul
      field-fix-of-neg)))))
