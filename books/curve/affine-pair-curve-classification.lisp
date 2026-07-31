(in-package "GFIELD")

(include-book "affine-pair-classification")
(include-book "../field/equal-squares")

; This equation bridge is proof-local: equal fixed x coordinates make the two
; instances of the common constrained curve right-hand side literally equal.
(local
 (defthm equal-affine-x-on-curve-implies-equal-y-squares
   (implies
    (and (short-weierstrass-affine-point-p first)
         (short-weierstrass-affine-point-p second)
         (equal (affine-coordinates-x first)
                (affine-coordinates-x second)))
    (equal (field-mul
            (affine-coordinates-y first)
            (affine-coordinates-y first))
           (field-mul
            (affine-coordinates-y second)
            (affine-coordinates-y second))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance short-weierstrass-affine-point-p-definition
                             (coordinates first))
                  (:instance short-weierstrass-affine-point-p-definition
                             (coordinates second)))
            :in-theory (e/d (short-weierstrass-equation-p)
                            (short-weierstrass-rhs
                             affine-coordinates-x
                             affine-coordinates-y))))))

(defthm short-weierstrass-equal-x-implies-equal-or-neg-y
   (implies
    (and (short-weierstrass-affine-point-p p)
         (short-weierstrass-affine-point-p q)
         (equal (affine-coordinates-x p)
                (affine-coordinates-x q)))
    (or (equal (affine-coordinates-y p)
               (affine-coordinates-y q))
        (equal (affine-coordinates-y q)
               (field-neg (affine-coordinates-y p)))))
   :rule-classes nil
   :hints
   (("Goal"
     :do-not '(preprocess)
     :use ((:instance equal-affine-x-on-curve-implies-equal-y-squares
                      (first p) (second q))
           (:instance field-equal-squares-implies-equal-or-neg
                      (first (affine-coordinates-y p))
                      (second (affine-coordinates-y q))))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(field-element-p-of-affine-coordinates-y
        field-fix-when-field-element-p)))))

(defthm affine-pair-classify-not-same-x-other-for-curve-points
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second))
   (not (equal (affine-pair-classify first second) :same-x-other)))
  :rule-classes nil
  :hints
  (("Goal"
    :do-not '(preprocess)
    :use (affine-pair-classify-same-x-other-characterization
          (:instance short-weierstrass-equal-x-implies-equal-or-neg-y
                     (p first) (q second)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-coordinates-x-of-fix
       affine-coordinates-y-of-fix)))))
