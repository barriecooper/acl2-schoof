(in-package "GFIELD")

(include-book "curve-point-addition-relation")

; Algebra used only to bridge the ordered secant presentation.  Keeping these
; facts local avoids turning operand reversal into a global rewrite policy.
(local
 (defthm field-add-inverse-middle-local
   (equal (field-add x (field-add (field-neg x) y))
          (field-fix y))
   :hints (("Goal" :use ((:instance field-add-associative
                                     (x x) (y (field-neg x)) (z y)))
            :in-theory (enable field-add-inverse-right
                               field-add-zero-left)))))

(local
 (defthm field-add-swap-first-two-local
   (equal (field-add x (field-add y z))
          (field-add y (field-add x z)))
   :hints (("Goal" :use ((:instance field-add-associative
                                     (x x) (y y) (z z))
                           (:instance field-add-associative
                                      (x y) (y x) (z z))
                           (:instance field-add-commutative (x x) (y y)))
            :in-theory
            (union-theories (theory 'minimal-theory)
                            '(field-fix-of-add))))))

(local
 (defthm field-add-inverse-shuffle-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints
   (("Goal"
     :use ((:instance field-add-swap-first-two-local
                      (x x) (y y) (z (field-add (field-neg x) z)))
           (:instance field-add-inverse-middle-local (x x) (y z)))
     :in-theory (enable field-add-fix-right)))))

(local
 (defthm field-add-cancel-around-local
   (equal (field-add x (field-add y (field-neg x)))
          (field-fix y))
   :hints (("Goal" :use ((:instance field-add-swap-first-two-local
                                     (x x) (y y) (z (field-neg x))))
            :in-theory (enable field-add-inverse-right
                               field-add-zero-right)))))

(local
 (defthm field-neg-of-add-local
   (equal (field-neg (field-add x y))
          (field-add (field-neg x) (field-neg y)))
   :hints
   (("Goal"
     :use ((:instance field-additive-inverse-unique
                      (x (field-add x y))
                      (y (field-add (field-neg x) (field-neg y)))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-add-associative field-add-inverse-shuffle-local
        field-add-inverse-right field-add-zero-left field-fix-of-add
        field-fix-of-neg))))))

(local
 (defthm field-sub-reverse-local
   (equal (field-sub x y)
          (field-neg (field-sub y x)))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable field-sub field-neg-of-add-local
                    field-add-commutative)))))

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
     :in-theory (enable field-add-inverse-right field-mul-zero-right)))))

(local
 (defthm field-mul-of-neg-left-local
   (equal (field-mul (field-neg x) y)
          (field-neg (field-mul x y)))
   :hints (("Goal" :use ((:instance field-mul-commutative
                                     (x (field-neg x)) (y y))
                           (:instance field-mul-commutative (x y) (y x)))
            :in-theory (enable field-mul-of-neg-right-local)))))

(local
 (defthm field-mul-neg-neg-local
   (equal (field-mul (field-neg x) (field-neg y))
          (field-mul x y))
   :hints (("Goal" :in-theory
            (enable field-mul-of-neg-left-local
                    field-neg-of-neg)))))

(local
 (defthm field-neg-zero-when-fixed-zero-local
   (implies (equal (field-fix x) (field-zero))
            (equal (field-neg x) (field-zero)))
   :hints (("Goal" :use ((:instance field-neg-of-fix (x x))
                           (:instance field-neg-of-zero))
            :in-theory (disable field-neg-of-fix field-neg-of-zero)))))

(local
 (defthm field-inv-zero-when-fixed-zero-local
   (implies (equal (field-fix x) (field-zero))
            (equal (field-inv x) (field-zero)))
   :hints (("Goal" :use ((:instance field-inv-of-fix (x x))
                           (:instance field-inv-of-zero))
            :in-theory (disable field-inv-of-fix field-inv-of-zero)))))

(local
 (defthm field-neg-nonzero-local
   (implies (not (equal (field-fix x) (field-zero)))
            (not (equal (field-neg x) (field-zero))))
   :hints (("Goal" :use ((:instance field-neg-of-neg (x x))
                           (:instance field-neg-of-zero))
            :in-theory (disable field-neg-of-neg field-neg-of-zero)))))

(local
 (defthm field-mutual-negation-local
   (implies (and (field-element-p x)
                 (equal y (field-neg x)))
            (equal x (field-neg y)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance field-neg-of-neg (x x)))
            :in-theory (enable field-fix-when-field-element-p)))))

(local
 (defthm field-inv-of-neg-local
   (equal (field-inv (field-neg x))
          (field-neg (field-inv x)))
   :hints
   (("Goal" :cases ((equal (field-fix x) (field-zero))))
    ("Subgoal 2"
     :use ((:instance field-multiplicative-inverse-unique
                      (x (field-neg x)) (y (field-neg (field-inv x)))))
     :in-theory (enable field-mul-neg-neg-local field-neg-of-zero))
    ("Subgoal 1" :in-theory
     (enable field-neg-zero-when-fixed-zero-local
             field-inv-zero-when-fixed-zero-local
             field-inv-of-zero field-neg-of-zero)))))

(local
 (defthm field-div-neg-neg-local
   (equal (field-div (field-neg numerator) (field-neg denominator))
          (field-div numerator denominator))
   :hints (("Goal" :in-theory
            (enable field-div field-inv-of-neg-local
                    field-mul-neg-neg-local)))))

(local
 (defthm field-div-of-reversed-subtractions-local
   (equal (field-div (field-sub first-y second-y)
                     (field-sub first-x second-x))
          (field-div (field-sub second-y first-y)
                     (field-sub second-x first-x)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance field-sub-reverse-local
                             (x first-y) (y second-y))
                  (:instance field-sub-reverse-local
                             (x first-x) (y second-x))
                  (:instance field-div-neg-neg-local
                             (numerator (field-sub second-y first-y))
                             (denominator (field-sub second-x first-x))))
            :in-theory (theory 'minimal-theory)))))

; The relation's secant equations are ordered.  The line equation and the
; symmetric x equation imply the reversed y equation for the same slope.
(local
 (defthm field-secants-share-output-y-local
   (implies
    (and (field-element-p x1) (field-element-p x2)
         (field-element-p y1) (field-element-p y2)
         (field-element-p xo) (field-element-p yo)
         (field-element-p slope)
         (equal (field-mul slope (field-sub x2 x1))
                (field-sub y2 y1))
         (equal (field-add yo y1)
                (field-mul slope (field-sub x1 xo))))
    (equal (field-add yo y2)
           (field-mul slope (field-sub x2 xo))))
   :hints
   (("Goal"
     :use ((:instance field-add-fixed-congruence
                      (x1 (field-mul slope (field-sub x2 x1)))
                      (x2 (field-sub y2 y1))
                      (y1 y1) (y2 y1))
           (:instance field-add-fixed-congruence
                      (x1 (field-add yo y1))
                      (x2 (field-mul slope (field-sub x1 xo)))
                      (y1 (field-sub y2 y1))
                      (y2 (field-sub y2 y1))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-sub field-mul-left-distributive
        field-mul-right-distributive field-add-associative
        field-add-commutative field-add-swap-first-two-local
        field-add-inverse-middle-local field-add-inverse-shuffle-local
        field-add-cancel-around-local
        field-add-left-cancel
        field-fix-when-field-element-p
        field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right field-fix-of-add
        field-fix-of-mul field-fix-of-neg
        field-mul-of-neg-right-local field-mul-of-neg-left-local
        field-neg-of-add-local field-neg-of-neg))))))

(defthm affine-distinct-x-secant-relation-p-reverse
   (implies
    (affine-distinct-x-secant-relation-p first second slope output)
    (affine-distinct-x-secant-relation-p second first slope output))
   :hints
   (("Goal"
     :use ((:instance field-secants-share-output-y-local
                      (slope (field-fix slope))
                      (x1 (affine-coordinates-x first))
                      (x2 (affine-coordinates-x second))
                      (y1 (affine-coordinates-y first))
                      (y2 (affine-coordinates-y second))
                      (xo (affine-coordinates-x output))
                      (yo (affine-coordinates-y output)))
           (:instance field-sub-reverse-local
                      (x (affine-coordinates-x first))
                      (y (affine-coordinates-x second)))
           (:instance field-sub-reverse-local
                      (x (affine-coordinates-y first))
                      (y (affine-coordinates-y second)))
           (:instance field-add-swap-first-two-local
                      (x (affine-coordinates-x output))
                      (y (affine-coordinates-x first))
                      (z (affine-coordinates-x second))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-distinct-x-secant-relation-p
        field-element-p-of-affine-coordinates-x
        field-element-p-of-affine-coordinates-y
        field-element-p-of-field-fix
        field-mul-of-neg-right-local field-neg-of-neg
        field-add-associative field-add-commutative field-fix-of-add
        field-fix-of-mul field-fix-of-neg)))))

(local
 (defun commutativity-doubling-slope-local (input)
   (field-div
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one)) (field-one))
      (field-mul (affine-coordinates-x input)
                 (affine-coordinates-x input)))
     (field-fix (short-weierstrass-a)))
    (field-add (affine-coordinates-y input)
               (affine-coordinates-y input)))))

(local
 (defthm equal-affine-fixes-imply-equal-accessors-local
   (implies (equal (affine-coordinates-fix first)
                   (affine-coordinates-fix second))
            (and (equal (affine-coordinates-x first)
                        (affine-coordinates-x second))
                 (equal (affine-coordinates-y first)
                        (affine-coordinates-y second))))
   :hints (("Goal" :use ((:instance affine-coordinates-x-of-fix
                                     (coordinates first))
                           (:instance affine-coordinates-x-of-fix
                                     (coordinates second))
                           (:instance affine-coordinates-y-of-fix
                                     (coordinates first))
                           (:instance affine-coordinates-y-of-fix
                                     (coordinates second)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm doubling-relation-of-equal-affine-fixes-local
   (implies
    (and (equal (affine-coordinates-fix first)
                (affine-coordinates-fix second))
     (affine-doubling-relation-p
      first (commutativity-doubling-slope-local first) output))
     (affine-doubling-relation-p
      second (commutativity-doubling-slope-local second) output))
   :hints
   (("Goal"
     :use ((:instance short-weierstrass-affine-point-p-of-fix
                      (coordinates first))
           (:instance short-weierstrass-affine-point-p-of-fix
                      (coordinates second))
           equal-affine-fixes-imply-equal-accessors-local)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(commutativity-doubling-slope-local
        affine-doubling-relation-p short-weierstrass-affine-point-p
        affine-coordinates-fix-idempotent
        affine-coordinates-x-of-fix affine-coordinates-y-of-fix
        field-add-of-fixes field-mul-of-fixes field-div
        field-inv-of-fix field-fix-idempotent))))))

; Swapping operands preserves the independent five-case specification.  No
; separate domain hypotheses are needed: membership and total fixing are
; already conjuncts of CURVE-POINT-ADDITION-RELATION-P.
(defthm curve-point-addition-relation-p-commutative
  (implies
   (curve-point-addition-relation-p first second output)
   (curve-point-addition-relation-p second first output))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-div-of-reversed-subtractions-local
                     (first-x (affine-coordinates-x
                               (curve-point-affine-coordinates-get
                                (curve-point-fix first))))
                     (second-x (affine-coordinates-x
                                (curve-point-affine-coordinates-get
                                 (curve-point-fix second))))
                     (first-y (affine-coordinates-y
                               (curve-point-affine-coordinates-get
                                (curve-point-fix first))))
                     (second-y (affine-coordinates-y
                                (curve-point-affine-coordinates-get
                                 (curve-point-fix second)))))
          (:instance field-mutual-negation-local
                     (x (affine-coordinates-y
                         (curve-point-affine-coordinates-get
                          (curve-point-fix first))))
                     (y (affine-coordinates-y
                         (curve-point-affine-coordinates-get
                          (curve-point-fix second)))))
          (:instance doubling-relation-of-equal-affine-fixes-local
                     (first (curve-point-affine-coordinates-get
                             (curve-point-fix first)))
                     (second (curve-point-affine-coordinates-get
                              (curve-point-fix second)))
                     (output (curve-point-affine-coordinates-get
                              (curve-point-fix output))))
          (:instance affine-distinct-x-secant-relation-p-reverse
                     (first (curve-point-affine-coordinates-get
                             (curve-point-fix first)))
                     (second (curve-point-affine-coordinates-get
                              (curve-point-fix second)))
                     (slope
                      (field-div
                       (field-sub
                        (affine-coordinates-y
                         (curve-point-affine-coordinates-get
                          (curve-point-fix second)))
                        (affine-coordinates-y
                         (curve-point-affine-coordinates-get
                          (curve-point-fix first))))
                       (field-sub
                        (affine-coordinates-x
                         (curve-point-affine-coordinates-get
                          (curve-point-fix second)))
                        (affine-coordinates-x
                         (curve-point-affine-coordinates-get
                          (curve-point-fix first))))))
                     (output (curve-point-affine-coordinates-get
                              (curve-point-fix output)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-addition-relation-p
       commutativity-doubling-slope-local
       curve-point-left-infinity-identity-relation-p
       curve-point-right-infinity-identity-relation-p
       affine-opposite-y-infinity-relation-p
       curve-point-fix-idempotent
       affine-coordinates-x-of-fix affine-coordinates-y-of-fix
       field-element-p-of-affine-coordinates-y
       affine-doubling-relation-p-of-fixes
       affine-opposite-y-infinity-relation-p-of-fixes
       field-neg-of-neg)))))

(defthm curve-point-pair-output-point-commutative
  (implies
   (and (short-weierstrass-curve-point-p first)
        (short-weierstrass-curve-point-p second))
   (equal (curve-point-pair-output-point first second)
          (curve-point-pair-output-point second first)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance curve-point-addition-relation-output-determinate
                (output-a (curve-point-pair-output-point first second))
                (output-b (curve-point-pair-output-point second first)))
     (:instance curve-point-pair-output-point-satisfies-addition-relation)
     (:instance curve-point-pair-output-point-satisfies-addition-relation
                (first second) (second first))
     (:instance curve-point-addition-relation-p-commutative
                (output (curve-point-pair-output-point first second)))
     (:instance curve-point-addition-relation-p-commutative
                (first second) (second first)
                (output (curve-point-pair-output-point second first)))
     (:instance curve-point-representation-p-of-curve-point-pair-output-point)
     (:instance curve-point-representation-p-of-curve-point-pair-output-point
                (first second) (second first)))
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(curve-point-fix-when-representation-p)))))
