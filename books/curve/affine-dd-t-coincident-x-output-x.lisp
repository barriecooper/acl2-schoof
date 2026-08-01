(in-package "GFIELD")

(include-book "affine-dd-t-coincident-x-tangent-domain")
(include-book "affine-dd-t-coincident-x-tangent-equation")
(include-book "affine-same-point-non-opposite-output-x")
(include-book "../field/xcert-algebra")

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
 (defthm non-self-inverse-implies-self-tangent-class-local
  (implies (not (equal (affine-coordinates-y a)
                       (field-neg (affine-coordinates-y a))))
   (equal (affine-pair-classify a a) :same-point-non-opposite))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance affine-pair-classify-same-point-non-opposite-characterization
                            (first a) (second a)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(affine-coordinates-x-of-fix
                          affine-coordinates-y-of-fix))))))

(local
 (defthm non-self-inverse-implies-double-y-nonzero-local
  (implies (not (equal (affine-coordinates-y a)
                       (field-neg (affine-coordinates-y a))))
   (not (equal (field-add (affine-coordinates-y a)
                          (affine-coordinates-y a))
               (field-zero))))
  :hints (("Goal" :use ((:instance field-additive-inverse-unique
                                   (x (affine-coordinates-y a))
                                   (y (affine-coordinates-y a))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(field-element-p-of-affine-coordinates-y
                          field-fix-when-field-element-p))))))

(local
 (defthm field-mul-right-cancel-forward-local
  (implies (and (not (equal (field-fix denominator) (field-zero)))
                (equal (field-mul left denominator)
                       (field-mul right denominator)))
   (equal (field-fix left) (field-fix right)))
  :hints (("Goal" :use ((:instance field-mul-left-cancel-forward
                                   (x denominator) (y left) (z right))
                          (:instance field-mul-commutative (x left) (y denominator))
                          (:instance field-mul-commutative (x right) (y denominator)))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm dd-t-witness-equals-canonical-slope-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope c)
        (affine-distinct-x-secant-relation-p b c r-slope q)
        (affine-doubling-relation-p c t-slope d)
        (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal
    (field-sub (field-add (field-fix p-slope) (field-fix t-slope))
               (field-fix r-slope))
    (affine-same-point-non-opposite-slope a)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance affine-dd-t-coincident-x-excludes-self-inverse)
                 (:instance non-self-inverse-implies-self-tangent-class-local)
                 (:instance non-self-inverse-implies-double-y-nonzero-local)
                 (:instance affine-dd-t-coincident-x-tangent-equation)
                 (:instance affine-same-point-non-opposite-slope-reconstructs-tangent-numerator
                            (first a) (second a))
                 (:instance field-mul-right-cancel-forward-local
                            (left (field-sub
                                   (field-add (field-fix p-slope) (field-fix t-slope))
                                   (field-fix r-slope)))
                            (right (affine-same-point-non-opposite-slope a))
                            (denominator (field-add (affine-coordinates-y a)
                                                    (affine-coordinates-y a)))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(field-fix-of-affine-same-point-non-opposite-slope
                          field-fix-of-add field-fix-of-neg field-sub))))))

(local
 (defthm field-two-times-local
  (equal (field-mul (field-add (field-one) (field-one)) x)
         (field-add x x))
  :hints (("Goal" :in-theory (enable field-mul-left-distributive
                                       field-fix-of-mul)))))

(local
 (defthm dd-t-xcert-h-zero-local
  (implies (and (affine-distinct-x-secant-relation-p a b p c)
                (affine-distinct-x-secant-relation-p b c r q)
                (affine-doubling-relation-p c ts d))
   (equal (xcert-h (field-fix p) (field-fix ts) (field-fix r)
                     (affine-coordinates-x a) (affine-coordinates-x c))
          (field-zero)))
  :hints (("Goal" :use ((:instance dd-t-h-local (t-slope ts)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(xcert-h field-sub-self field-fix-of-add field-fix-of-mul field-fix-of-neg))))))

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

(local
 (defthm dd-t-xcert-s-zero-local
  (implies (equal (field-sub (field-add (field-fix p) (field-fix ts))
                             (field-fix r)) u)
   (equal (xcert-s (field-fix p) (field-fix ts) (field-fix r) u)
          (field-zero)))
  :hints (("Goal" :use ((:instance dd-t-witness-balance-local
                                   (tangent-slope ts)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(xcert-s field-sub-self field-fix-of-add))))))

(local
 (defthm dd-t-xcert-telescope-zero-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p c)
        (affine-distinct-x-secant-relation-p b c r q)
        (affine-doubling-relation-p c ts d)
        (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal
    (xcert-telescope
     (affine-coordinates-x d) (affine-same-point-non-opposite-output-x a)
     (affine-coordinates-x c) (affine-coordinates-x a)
     (affine-coordinates-x a) (affine-coordinates-x b) (affine-coordinates-x c)
     (field-fix p) (field-fix ts) (field-fix r)
     (affine-same-point-non-opposite-slope a))
    (field-zero)))
  :hints (("Goal" :use ((:instance affine-same-point-non-opposite-output-x-rearrangement
                                   (first a)))
           :in-theory (union-theories (theory 'minimal-theory)
                         '(affine-distinct-x-secant-relation-p
                              affine-doubling-relation-p field-two-times-local
                              xcert-telescope xcert-gxl xcert-gxr xcert-gxab xcert-gxbc
                              field-sub field-sub-self field-add-inverse-left
                              field-add-inverse-right field-neg-of-neg field-add-zero-left field-add-zero-right
                              field-add-associative field-add-commutative field-add-swap-local
                              field-add-inverse-tail-balance-local
                              field-fix-of-add field-fix-of-mul field-fix-of-zero))))))

; The X-CERT specialization uses xab=C, xbc=A, left slope/output t/D,
; and right slope/output s/E, where E is the canonical tangent output at A.
(local
 (defthm dd-t-canonical-output-x-equals-d-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope c)
        (affine-distinct-x-secant-relation-p b c r-slope q)
        (affine-doubling-relation-p c t-slope d)
        (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal (affine-same-point-non-opposite-output-x a)
          (affine-coordinates-x d)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance dd-t-h-local (p p-slope) (r r-slope))
     (:instance dd-t-xcert-h-zero-local (p p-slope) (r r-slope) (ts t-slope))
     (:instance dd-t-xcert-s-zero-local
                (p p-slope) (r r-slope) (ts t-slope)
                (u (affine-same-point-non-opposite-slope a)))
     (:instance dd-t-xcert-telescope-zero-local
                (p p-slope) (r r-slope) (ts t-slope))
     (:instance dd-t-witness-equals-canonical-slope-local)
     (:instance affine-same-point-non-opposite-output-x-rearrangement
                (first a))
     (:instance xcert-composition
      (p (field-fix p-slope)) (q (field-fix t-slope))
      (r (field-fix r-slope))
      (tt (affine-same-point-non-opposite-slope a))
      (xa (affine-coordinates-x a)) (xb (affine-coordinates-x b))
      (xc (affine-coordinates-x c))
      (xab (affine-coordinates-x c))
      (xbc (affine-coordinates-x a))
      (xl (affine-coordinates-x d))
      (xr (affine-same-point-non-opposite-output-x a)))
     (:instance field-sub-equal-zero-implies-fixed-equal
      (first (affine-coordinates-x d))
      (second (affine-same-point-non-opposite-output-x a))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(xcert-dx field-sub
       field-add-zero-left field-add-zero-right field-mul-zero-left
       field-fix-of-zero field-neg-of-zero field-mul-zero-right field-fix-of-mul
       field-fix-when-field-element-p field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-same-point-non-opposite-output-x
       field-fix-of-add field-fix-of-neg))))))

(defthm affine-dd-t-coincident-x-output-x-equation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope c)
    (affine-distinct-x-secant-relation-p b c r-slope q)
    (affine-doubling-relation-p c t-slope d)
    (equal (affine-coordinates-x q) (affine-coordinates-x a)))
   (equal
    (field-add (field-add (affine-coordinates-x d)
                          (affine-coordinates-x a))
               (affine-coordinates-x a))
    (field-mul
     (field-sub (field-add (field-fix p-slope) (field-fix t-slope))
                (field-fix r-slope))
     (field-sub (field-add (field-fix p-slope) (field-fix t-slope))
                (field-fix r-slope)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use (dd-t-witness-equals-canonical-slope-local
          dd-t-canonical-output-x-equals-d-local
          (:instance affine-same-point-non-opposite-output-x-rearrangement
                     (first a)))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(field-mul-left-distributive field-two-times-local field-add-associative
       field-fix-of-add field-fix-of-mul)))))
