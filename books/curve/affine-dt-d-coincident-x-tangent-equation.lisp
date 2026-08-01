(in-package "GFIELD")

(include-book "affine-dt-d-coincident-x-tangent-domain")
(include-book "affine-distinct-x-secant-identity")
(include-book "../field/two-line-telescope")
(include-book "../field/xcert-confluent-h-reconstruction")

; The ordinate and tangent-domain endpoints remain separate public facts.  Only
; the ordinate equality is algebraically needed below; the domain theorem is
; included so later clients obtain the already certified tangent domain too.
(local
 (defthm dt-d-ordinate-equality-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (equal (affine-coordinates-x q-output) (affine-coordinates-x a)))
   (equal (affine-coordinates-y q-output) (affine-coordinates-y a)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          affine-dt-d-coincident-x-implies-ordinate-equality))
           :in-theory (theory 'minimal-theory)))))

; Checkpoint 2: the two exact line equations have the common right factor
; xB-xA.  The second one is the doubling output-y equation after xQ=xA and
; yQ=yA have been substituted.
(local
 (defthm dt-d-first-line-local
  (implies (affine-distinct-x-secant-relation-p a b p-slope p-output)
   (equal
    (field-sub (affine-coordinates-y b) (affine-coordinates-y a))
    (field-mul (field-fix p-slope)
               (field-sub (affine-coordinates-x b)
                          (affine-coordinates-x a)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable affine-distinct-x-secant-relation-p)))))

(local
 (defthm dt-d-second-line-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (equal (affine-coordinates-x q-output) (affine-coordinates-x a)))
   (equal
    (field-add (affine-coordinates-y a) (affine-coordinates-y b))
    (field-mul (field-fix t-slope)
               (field-sub (affine-coordinates-x b)
                          (affine-coordinates-x a)))))
  :rule-classes nil
  :hints (("Goal" :use (dt-d-ordinate-equality-local)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(affine-doubling-relation-p))))))

(local
 (defthm dt-d-doubled-ordinate-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
        (equal (affine-coordinates-x q-output) (affine-coordinates-x a)))
   (equal
    (field-add (affine-coordinates-y a) (affine-coordinates-y a))
    (field-mul
     (field-sub (field-fix t-slope) (field-fix p-slope))
     (field-sub (affine-coordinates-x b) (affine-coordinates-x a)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (dt-d-first-line-local dt-d-second-line-local
     (:instance field-two-line-equations-imply-doubled-first-ordinate
      (ya (affine-coordinates-y a)) (yb (affine-coordinates-y b))
      (p (field-fix p-slope)) (r (field-fix t-slope))
      (delta (field-sub (affine-coordinates-x b)
                        (affine-coordinates-x a)))))
    :in-theory (union-theories (theory 'minimal-theory)
                               '(field-fix-of-add field-fix-of-mul
                                 field-fix-of-neg))))))

; The semantic wrapper for confluent H has exactly the scalar interface of the
; checked-in reconstruction.  In particular, both cancellations stay inside
; xcert-confluent-h-scalar-reconstruction.
(local
 (defthm relation-input-secant-identity-local
  (implies (affine-distinct-x-secant-relation-p first second slope output)
   (equal
    (field-mul (field-fix slope)
     (field-add (affine-coordinates-y second) (affine-coordinates-y first)))
    (field-add
     (field-mul (affine-coordinates-x second) (affine-coordinates-x second))
     (field-add
      (field-mul (affine-coordinates-x second) (affine-coordinates-x first))
      (field-add
       (field-mul (affine-coordinates-x first) (affine-coordinates-x first))
       (field-fix (short-weierstrass-a)))))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance affine-pair-classify-distinct-x-characterization)
         (:instance affine-distinct-x-output-satisfies-secant-relation)
         (:instance affine-distinct-x-secant-relation-slope-unique
          (slope-a slope) (output-a output)
          (slope-b (affine-distinct-x-slope first second))
          (output-b (affine-distinct-x-output first second)))
         (:instance affine-distinct-x-input-secant-identity))
   :in-theory (union-theories (theory 'minimal-theory)
    '(affine-distinct-x-secant-relation-p affine-coordinates-x-of-fix
      field-fix-of-affine-distinct-x-slope field-fix-of-mul
      field-fix-of-add))))))

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
 (defthm dt-d-confluent-h-local
  (implies
   (and (affine-distinct-x-secant-relation-p a b p-slope p-output)
        (affine-doubling-relation-p b t-slope q-output)
        (affine-distinct-x-secant-relation-p p-output b q-slope r-output))
   (equal
    (field-mul (field-sub (field-fix p-slope) (field-fix t-slope))
               (field-add (field-fix p-slope) (field-fix q-slope)))
    (field-sub (affine-coordinates-x a) (affine-coordinates-x b))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance relation-x-difference-nonzero-local
          (first a) (second b) (slope p-slope) (output p-output))
         (:instance relation-x-difference-nonzero-local
          (first p-output) (second b) (slope q-slope) (output r-output))
         (:instance relation-input-secant-identity-local
          (first a) (second b) (slope p-slope) (output p-output))
         (:instance relation-input-secant-identity-local
          (first p-output) (second b) (slope q-slope) (output r-output))
         (:instance xcert-confluent-h-scalar-reconstruction
          (a (field-fix (short-weierstrass-a)))
          (p (field-fix p-slope)) (q (field-fix q-slope))
          (tangent (field-fix t-slope))
          (xa (affine-coordinates-x a)) (ya (affine-coordinates-y a))
          (xb (affine-coordinates-x b)) (yb (affine-coordinates-y b))
          (xp (affine-coordinates-x p-output))
          (yp (affine-coordinates-y p-output))))
   :in-theory (union-theories (theory 'minimal-theory)
    '(affine-distinct-x-secant-relation-p affine-doubling-relation-p
      field-fix-idempotent field-fix-of-add field-fix-of-mul))))))

; Small normalization vocabulary used by the bounded residual stages.
(local (defthm field-mul-of-neg-right-local
 (equal (field-mul x (field-neg y)) (field-neg (field-mul x y)))
 :hints (("Goal" :use ((:instance field-additive-inverse-unique
  (x (field-mul x y)) (y (field-mul x (field-neg y))))
  (:instance field-mul-left-distributive (x x) (y y) (z (field-neg y))))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-add-inverse-right field-mul-zero-right field-fix-of-mul))))))
(local (defthm field-mul-of-neg-left-local
 (equal (field-mul (field-neg x) y) (field-neg (field-mul x y)))
 :hints (("Goal" :use ((:instance field-mul-commutative
  (x (field-neg x)) (y y)) (:instance field-mul-commutative (x y) (y x)))
  :in-theory (enable field-mul-of-neg-right-local)))))
(local (defthm field-add-inverse-middle-local
 (equal (field-add x (field-add (field-neg x) y)) (field-fix y))
 :hints (("Goal" :use ((:instance field-add-associative
  (x x) (y (field-neg x)) (z y)))
  :in-theory (union-theories (theory 'minimal-theory)
   '(field-add-inverse-right field-add-zero-left field-fix-idempotent))))))
(local (defthm field-add-swap-first-two-local
 (equal (field-add x (field-add y z)) (field-add y (field-add x z)))
 :hints (("Goal" :use ((:instance field-add-associative (x x) (y y) (z z))
                        (:instance field-add-associative (x y) (y x) (z z))
                        (:instance field-add-commutative (x x) (y y)))
  :in-theory (union-theories (theory 'minimal-theory) '(field-fix-of-add))))))
(local (defthm field-add-inverse-shuffle-local
 (equal (field-add x (field-add y (field-add (field-neg x) z)))
        (field-add y (field-fix z)))
 :hints (("Goal" :use ((:instance field-add-swap-first-two-local
  (x x) (y y) (z (field-add (field-neg x) z)))
  (:instance field-add-inverse-middle-local (x x) (y z)))
  :in-theory (enable field-add-fix-right)))))
(local (defthm field-neg-of-add-residual-local
 (equal (field-neg (field-add x y))
        (field-add (field-neg x) (field-neg y)))
 :hints (("Goal" :use ((:instance field-additive-inverse-unique
  (x (field-add x y)) (y (field-add (field-neg x) (field-neg y)))))
  :in-theory (enable field-add-associative field-add-inverse-shuffle-local
                     field-add-inverse-right field-add-zero-left
                     field-fix-of-add field-fix-of-neg)))))
(local (defconst *dt-d-residual-theory*
 '(field-sub field-mul-left-distributive field-mul-right-distributive
   field-mul-associative field-mul-commutative field-mul-of-neg-left-local
   field-mul-of-neg-right-local field-neg-of-add-residual-local field-neg-of-neg
   field-add-associative field-add-commutative field-add-inverse-left
   field-add-swap-first-two-local field-add-inverse-middle-local
   field-add-inverse-shuffle-local
   field-add-inverse-right field-add-zero-left field-add-zero-right
   field-mul-one-left field-mul-one-right field-add-fix-left
   field-add-fix-right field-mul-fix-left field-mul-fix-right
   field-fix-idempotent field-fix-of-add field-fix-of-mul field-fix-of-neg)))

(local
 (defthm field-neg-fixed-congruence-residual-local
  (implies (equal (field-fix x) (field-fix y))
           (equal (field-neg x) (field-neg y)))
  :hints (("Goal" :use ((:instance field-neg-of-fix (x x))
                         (:instance field-neg-of-fix (x y)))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm dt-d-confluent-h-oriented-local
  (implies
   (equal (field-mul (field-sub p tangent) l) (field-sub xa xb))
   (equal (field-mul (field-sub tangent p) l) (field-sub xb xa)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance field-neg-fixed-congruence-residual-local
                  (x (field-mul (field-sub p tangent) l))
                  (y (field-sub xa xb))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      *dt-d-residual-theory*)))))

; Checkpoint 4: L=t+s for s=L-t.  This is additive normalization only.
(local
 (defthm dt-d-witness-balance-local
  (equal (field-add p q)
         (field-add tangent (field-sub (field-add p q) tangent)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           *dt-d-residual-theory*)))))

; Residual stage 1: exact product obtained by multiplying the doubled-ordinate
; telescope by the witness.
(local
 (defthm dt-d-multiply-telescope-local
  (implies (equal doubled (field-mul factor delta))
   (equal (field-mul s doubled)
          (field-mul (field-mul s factor) delta)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
                           '(field-mul-associative field-fix-of-mul))))))

; Residual stage 2: balance expands s, and the oriented H equation replaces
; (t-p)*L by d.  No factor is cancelled.
(local
 (defthm dt-d-product-rotate-local
  (equal (field-mul tangent (field-mul delta factor))
         (field-mul delta (field-mul factor tangent)))
  :hints (("Goal" :use ((:instance field-mul-associative
                          (x delta) (y factor) (z tangent))
                         (:instance field-mul-commutative
                          (x tangent) (y (field-mul delta factor))))
           :in-theory (theory 'minimal-theory)))))

(local
 (defthm dt-d-use-balance-shape-local
  (implies
   (equal l (field-add tangent s))
   (equal
    (field-mul (field-mul s factor) delta)
    (field-sub (field-mul (field-mul factor l) delta)
               (field-mul tangent (field-mul factor delta)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance dt-d-product-rotate-local))
           :in-theory (union-theories (theory 'minimal-theory)
                                      *dt-d-residual-theory*)))))

(local
 (defthm dt-d-use-balance-and-h-local
  (implies
   (and (equal l (field-add tangent s))
        (equal (field-mul factor l) delta))
   (equal
    (field-mul (field-mul s factor) delta)
    (field-sub (field-mul delta delta)
               (field-mul tangent (field-mul factor delta)))))
  :rule-classes nil
  :hints (("Goal" :use (dt-d-use-balance-shape-local)
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(field-sub field-mul-fixed-congruence
                                        field-fix-of-mul field-fix-of-neg))))))

; Residual stage 3: the second line and tangent numerator at B turn the last
; product into 2*t^2*d-(3*xB^2+a).  This is the complete ordinate input.
(local
 (defthm dt-d-tangent-ordinate-residual-local
  (implies
   (and (equal doubled (field-add ya ya))
        (equal (field-mul tangent delta) (field-add ya yb))
        (equal (field-mul tangent (field-add yb yb)) tangent-numerator))
   (equal
    (field-mul tangent doubled)
    (field-sub
     (field-mul (field-add (field-one) (field-one))
                (field-mul (field-mul tangent tangent) delta))
     tangent-numerator)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance field-mul-associative
                  (x tangent) (y tangent) (z delta)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      *dt-d-residual-theory*)))))

; Residual stage 4: after output-x substitutes t^2=xA+2*xB, the remaining
; bounded polynomial is d^2-2*t^2*d+3*xB^2+a=3*xA^2+a for d=xB-xA.
(local
 (defthm dt-d-final-quadratic-residual-local
  (implies
   (and (equal delta (field-sub xb xa))
        (equal tangent-square
               (field-add xa
                (field-mul (field-add (field-one) (field-one)) xb))))
   (equal
    (field-add
     (field-sub
      (field-mul delta delta)
      (field-mul (field-add (field-one) (field-one))
                 (field-mul tangent-square delta)))
     (field-add
      (field-mul (field-add (field-add (field-one) (field-one))
                            (field-one))
                 (field-mul xb xb))
      curve-a))
    (field-add
     (field-mul (field-add (field-add (field-one) (field-one))
                           (field-one))
                (field-mul xa xa))
     curve-a)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                                      *dt-d-residual-theory*)))))

; Compose only the staged residual equalities.  The scalar inputs beyond the
; telescope/H/balance are the tangent numerator at B and doubling output-x;
; neither secant output-x equation is needed by the final residual.
(local
 (defthm dt-d-compose-residual-local
  (implies
   (and (equal left (field-sub delta-square tangent-times-doubled))
        (equal tangent-times-doubled
               (field-sub twice-tangent-square-delta tangent-numerator))
        (equal
         (field-add
          (field-sub delta-square twice-tangent-square-delta)
          tangent-numerator)
         target))
   (equal left target))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories (theory 'minimal-theory)
                                      *dt-d-residual-theory*)))))

(local
 (defthm dt-d-numerator-reconstruction-local
  (implies
   (and (equal (field-add ya ya) (field-mul factor delta))
        (equal l (field-add tangent s))
        (equal (field-mul factor l) delta)
        (equal (field-mul tangent delta) (field-add ya yb))
        (equal (field-mul tangent (field-add yb yb))
               (field-add
                (field-mul
                 (field-add (field-add (field-one) (field-one)) (field-one))
                 (field-mul xb xb)) curve-a))
        (equal (field-mul tangent tangent)
               (field-add xa
                (field-mul (field-add (field-one) (field-one)) xb)))
        (equal delta (field-sub xb xa)))
   (equal
    (field-mul s (field-add ya ya))
    (field-add
     (field-mul
      (field-add (field-add (field-one) (field-one)) (field-one))
      (field-mul xa xa)) curve-a)))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance dt-d-multiply-telescope-local
          (doubled (field-add ya ya)))
         (:instance dt-d-use-balance-and-h-local)
         (:instance dt-d-tangent-ordinate-residual-local
          (doubled (field-add ya ya))
          (tangent-numerator
           (field-add
            (field-mul
             (field-add (field-add (field-one) (field-one)) (field-one))
             (field-mul xb xb)) curve-a)))
         (:instance dt-d-final-quadratic-residual-local
          (tangent-square (field-mul tangent tangent)))
         (:instance dt-d-compose-residual-local
          (left (field-mul s (field-add ya ya)))
          (delta-square (field-mul delta delta))
          (tangent-times-doubled (field-mul tangent (field-add ya ya)))
          (twice-tangent-square-delta
           (field-mul (field-add (field-one) (field-one))
                      (field-mul (field-mul tangent tangent) delta)))
          (tangent-numerator
           (field-add
            (field-mul
             (field-add (field-add (field-one) (field-one)) (field-one))
             (field-mul xb xb)) curve-a))
          (target
           (field-add
            (field-mul
             (field-add (field-add (field-one) (field-one)) (field-one))
             (field-mul xa xa)) curve-a))))
   :in-theory (union-theories (theory 'minimal-theory)
                              '(field-add-fixed-congruence field-sub
                                field-fix-of-add field-fix-of-mul
                                field-fix-of-neg))))))

(defthm affine-dt-d-coincident-x-tangent-equation
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope p-output)
    (affine-doubling-relation-p b t-slope q-output)
    (affine-distinct-x-secant-relation-p p-output b q-slope r-output)
    (equal (affine-coordinates-x q-output) (affine-coordinates-x a)))
   (equal
    (field-mul
     (field-sub
      (field-add (field-fix p-slope) (field-fix q-slope))
      (field-fix t-slope))
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
    (dt-d-doubled-ordinate-local dt-d-second-line-local
     dt-d-confluent-h-local
     (:instance dt-d-confluent-h-oriented-local
      (p (field-fix p-slope)) (tangent (field-fix t-slope))
      (l (field-add (field-fix p-slope) (field-fix q-slope)))
      (xa (affine-coordinates-x a)) (xb (affine-coordinates-x b)))
     (:instance dt-d-witness-balance-local
      (p (field-fix p-slope)) (q (field-fix q-slope))
      (tangent (field-fix t-slope)))
     (:instance dt-d-numerator-reconstruction-local
      (s (field-sub (field-add (field-fix p-slope) (field-fix q-slope))
                    (field-fix t-slope)))
      (l (field-add (field-fix p-slope) (field-fix q-slope)))
      (factor (field-sub (field-fix t-slope) (field-fix p-slope)))
      (tangent (field-fix t-slope))
      (delta (field-sub (affine-coordinates-x b)
                        (affine-coordinates-x a)))
      (xa (affine-coordinates-x a)) (ya (affine-coordinates-y a))
      (xb (affine-coordinates-x b)) (yb (affine-coordinates-y b))
      (curve-a (field-fix (short-weierstrass-a)))))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(affine-doubling-relation-p field-sub field-neg-of-add-residual-local
       field-neg-of-neg field-mul-of-neg-left-local
       field-mul-of-neg-right-local field-add-associative
       field-add-commutative field-mul-associative field-mul-commutative
       field-fix-idempotent field-fix-of-add field-fix-of-mul
       field-fix-of-neg)))))
