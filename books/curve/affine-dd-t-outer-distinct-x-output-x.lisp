(in-package "GFIELD")

(include-book "affine-dd-t-outer-distinct-x-slope")
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
 (defthm dd-t-witness-equals-canonical-slope-local
   (implies (and (affine-distinct-x-secant-relation-p a b p c)
                 (affine-distinct-x-secant-relation-p b c r q)
                 (affine-doubling-relation-p c t-slope d)
                 (not (equal (affine-coordinates-x q)
                             (affine-coordinates-x a))))
    (equal (field-sub (field-add (field-fix p) (field-fix t-slope))
                      (field-fix r))
           (affine-distinct-x-slope a q)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance affine-dd-t-outer-distinct-x-slope-equation)
                  (:instance affine-pair-classify-distinct-x-characterization
                   (first a) (second q))
                  (:instance affine-distinct-x-slope-reconstructs-y-difference
                   (first a) (second q))
                  (:instance outer-x-difference-nonzero-local
                   (xa (affine-coordinates-x a))
                   (xq (affine-coordinates-x q)))
                  (:instance field-mul-left-cancel-forward
                   (x (field-sub (affine-coordinates-x q)
                                 (affine-coordinates-x a)))
                   (y (field-sub (field-add (field-fix p) (field-fix t-slope))
                                 (field-fix r)))
                   (z (affine-distinct-x-slope a q))))
            :in-theory (union-theories (theory 'minimal-theory)
             '(field-mul-commutative affine-coordinates-x-of-fix
               field-element-p-of-affine-coordinates-x field-fix-when-field-element-p
               field-fix-of-affine-distinct-x-slope
               field-fix-of-add field-fix-of-neg field-sub))))))

(local
 (defthm field-add-inverse-tail-local
   (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
   :hints (("Goal" :use ((:instance field-add-associative
                           (x x) (y (field-neg x)) (z y)))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(field-add-inverse-right field-add-zero-left
                           field-fix-idempotent))))))
(local
 (defthm field-add-inverse-shuffle-local
   (equal (field-add x (field-add y (field-add (field-neg x) z)))
          (field-add y (field-fix z)))
   :hints (("Goal" :use ((:instance field-add-swap-local
                           (x x) (y y) (z (field-add (field-neg x) z)))
                          (:instance field-add-inverse-tail-local (x x) (y z)))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(field-add-swap-local field-add-inverse-tail-local
                           field-add-fix-right))))))

(local
 (defthm field-neg-of-add-local
   (equal (field-neg (field-add x y))
          (field-add (field-neg x) (field-neg y)))
   :hints (("Goal" :use ((:instance field-additive-inverse-unique
                           (x (field-add x y))
                           (y (field-add (field-neg x) (field-neg y)))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(field-add-associative field-add-inverse-shuffle-local
                           field-add-inverse-right field-add-zero-left
                           field-fix-of-add field-fix-of-neg))))))

(local
 (defthm dd-t-balance-from-witness-local
   (implies
    (equal (field-sub (field-add p q) r) (field-fix tt))
    (equal (field-sub (field-add p q) (field-add r tt)) (field-zero)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance field-add-fixed-congruence
             (x1 (field-sub (field-add p q) r)) (x2 tt)
             (y1 r) (y2 r))
           (:instance field-add-fixed-congruence
             (x1 (field-add p q)) (x2 (field-add r tt))
             (y1 (field-neg (field-add r tt)))
             (y2 (field-neg (field-add r tt)))))
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(field-sub field-add-associative field-add-commutative
        field-add-swap-local field-add-inverse-left field-add-inverse-right
        field-add-zero-left field-add-zero-right field-neg-of-add-local
        field-add-inverse-shuffle-local field-add-fix-left field-add-fix-right
        field-fix-of-add field-fix-of-neg field-fix-idempotent))))))

(local
 (defthm dd-t-h-zero-local
   (implies (and (affine-distinct-x-secant-relation-p a b p c)
                 (affine-distinct-x-secant-relation-p b c r q)
                 (affine-doubling-relation-p c t-slope d))
    (equal (xcert-h (field-fix p) (field-fix t-slope) (field-fix r)
                    (affine-coordinates-x a) (affine-coordinates-x c))
           (field-zero)))
   :rule-classes nil
   :hints (("Goal" :use (dd-t-h-local)
            :in-theory (union-theories (theory 'minimal-theory)
                         '(xcert-h field-sub-self field-fix-of-add field-fix-of-mul
                           field-fix-of-neg))))))
(local
 (defthm dd-t-s-zero-local
   (implies (and (affine-distinct-x-secant-relation-p a b p c)
                 (affine-distinct-x-secant-relation-p b c r q)
                 (affine-doubling-relation-p c t-slope d)
                 (not (equal (affine-coordinates-x q) (affine-coordinates-x a))))
    (equal (xcert-s (field-fix p) (field-fix t-slope) (field-fix r)
                    (affine-distinct-x-slope a q))
           (field-zero)))
   :rule-classes nil
   :hints (("Goal" :use (dd-t-witness-equals-canonical-slope-local
                           (:instance dd-t-balance-from-witness-local
                            (p (field-fix p)) (q (field-fix t-slope))
                            (r (field-fix r))
                            (tt (affine-distinct-x-slope a q))))
            :in-theory (union-theories (theory 'minimal-theory)
                         '(xcert-s field-fix-of-affine-distinct-x-slope
                           field-fix-of-add field-fix-of-neg))))))
(local
 (defthm dd-t-telescope-zero-local
   (implies (and (affine-distinct-x-secant-relation-p a b p c)
                 (affine-distinct-x-secant-relation-p b c r q)
                 (affine-doubling-relation-p c t-slope d))
    (equal
     (xcert-telescope
      (affine-coordinates-x d) (affine-distinct-x-output-x a q)
      (affine-coordinates-x c) (affine-coordinates-x q)
      (affine-coordinates-x a) (affine-coordinates-x b) (affine-coordinates-x c)
      (field-fix p) (field-fix t-slope) (field-fix r)
      (affine-distinct-x-slope a q))
     (field-zero)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance affine-distinct-x-output-x-rearrangement
                           (first a) (second q)))
            :in-theory (union-theories (theory 'minimal-theory)
             '(xcert-telescope xcert-gxl xcert-gxr xcert-gxab xcert-gxbc
               affine-distinct-x-secant-relation-p affine-doubling-relation-p
               field-mul-right-distributive field-mul-one-left field-mul-one-right
               field-add-associative field-add-commutative field-add-swap-local
               field-add-inverse-shuffle-local field-neg-of-add-local
               field-add-inverse-left field-add-inverse-right
               field-sub-self field-sub-zero field-add-zero-left field-add-zero-right
               field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero
               field-fix-idempotent field-fix-when-field-element-p
               field-element-p-of-affine-coordinates-x field-fix-of-affine-distinct-x-slope))))))

(local
 (defthm dd-t-canonical-output-x-local
   (implies (and (affine-distinct-x-secant-relation-p a b p c)
                 (affine-distinct-x-secant-relation-p b c r q)
                 (affine-doubling-relation-p c t-slope d)
                 (not (equal (affine-coordinates-x q) (affine-coordinates-x a))))
    (equal (affine-distinct-x-output-x a q) (affine-coordinates-x d)))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     (dd-t-h-zero-local dd-t-s-zero-local dd-t-telescope-zero-local
      (:instance xcert-composition
       (xl (affine-coordinates-x d)) (xr (affine-distinct-x-output-x a q))
       (xab (affine-coordinates-x c)) (xbc (affine-coordinates-x q))
       (xa (affine-coordinates-x a)) (xb (affine-coordinates-x b))
       (xc (affine-coordinates-x c))
       (p (field-fix p)) (q (field-fix t-slope)) (r (field-fix r))
       (tt (affine-distinct-x-slope a q)))
      (:instance field-sub-equal-zero-implies-fixed-equal
       (first (affine-coordinates-x d))
       (second (affine-distinct-x-output-x a q))))
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(xcert-dx xcert-c field-sub-self field-mul-zero-right
        field-add-zero-left field-add-zero-right field-neg-of-zero field-sub
        field-fix-of-add field-fix-of-mul field-fix-of-neg field-fix-of-zero
        field-fix-when-field-element-p field-element-p-of-affine-coordinates-x
        field-element-p-of-affine-distinct-x-output-x))))))

(defthm affine-dd-t-outer-distinct-x-output-x-equation
  (implies
   (and (affine-distinct-x-secant-relation-p a b p c)
        (affine-distinct-x-secant-relation-p b c r q)
        (affine-doubling-relation-p c t-slope d)
        (not (equal (affine-coordinates-x q)
                    (affine-coordinates-x a))))
   (equal
    (field-add (field-add (affine-coordinates-x d)
                          (affine-coordinates-x a))
               (affine-coordinates-x q))
    (field-mul
     (field-sub (field-add (field-fix p) (field-fix t-slope))
                (field-fix r))
     (field-sub (field-add (field-fix p) (field-fix t-slope))
                (field-fix r)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (dd-t-canonical-output-x-local dd-t-h-zero-local dd-t-s-zero-local dd-t-telescope-zero-local
          dd-t-witness-equals-canonical-slope-local
          (:instance dd-t-balance-from-witness-local
           (p (field-fix p)) (q (field-fix t-slope)) (r (field-fix r))
           (tt (affine-distinct-x-slope a q)))
          (:instance xcert-composition
           (xl (affine-coordinates-x d))
           (xr (affine-distinct-x-output-x a q))
           (xab (affine-coordinates-x c)) (xbc (affine-coordinates-x q))
           (xa (affine-coordinates-x a)) (xb (affine-coordinates-x b))
           (xc (affine-coordinates-x c))
           (p (field-fix p)) (q (field-fix t-slope)) (r (field-fix r))
           (tt (affine-distinct-x-slope a q)))
          (:instance affine-distinct-x-output-x-rearrangement
           (first a) (second q))
          (:instance field-sub-equal-zero-implies-fixed-equal
           (first (affine-coordinates-x d))
           (second (affine-distinct-x-output-x a q))))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(field-add-associative field-add-commutative field-add-swap-local
       field-add-inverse-left field-add-inverse-right field-add-zero-left field-add-zero-right
       field-mul-left-distributive field-mul-right-distributive
       field-mul-one-left field-mul-one-right
       xcert-dx xcert-telescope xcert-gxl xcert-gxr xcert-gxab xcert-gxbc
       xcert-h xcert-s xcert-c field-sub-self
       affine-distinct-x-secant-relation-p affine-doubling-relation-p
       field-fix-idempotent field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x field-element-p-of-affine-coordinates-y
       field-fix-of-affine-distinct-x-slope field-fix-of-add field-fix-of-mul
       field-fix-of-neg field-fix-of-zero field-add-zero-left field-add-zero-right
       field-mul-zero-left field-mul-zero-right field-sub)))))
