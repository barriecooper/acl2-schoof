(in-package "GPOLY")
(include-book "reduced-arithmetic")

; POLY-CONGRUENT-P is the quotient-equality boundary: it compares the unique
; canonical representatives computed by POLY-REMAINDER.  This book packages
; the representative-level consequences needed by reduced arithmetic; it does
; not introduce quotient objects or quotient-ring laws.

(local
 (in-theory (disable poly-congruent-p poly-remainder normalize
                     poly-reduced-add poly-reduced-neg
                     poly-reduced-sub poly-reduced-mul)))

(defthm equal-implies-poly-congruent-p
  (implies (equal left right)
           (poly-congruent-p left right modulus)))

(defthm remainder-fixed-poly-congruent-p-iff-equal
  (implies (and (equal (poly-remainder left modulus) left)
                (equal (poly-remainder right modulus) right))
           (equal (poly-congruent-p left right modulus)
                  (equal left right)))
  :hints (("Goal" :use ((:instance poly-congruent-p-iff-equal-remainders)))))

(defthm poly-congruent-p-polynomial-one-modulus
  (poly-congruent-p left right (polynomial-one))
  :hints (("Goal"
           :use ((:instance poly-remainder-polynomial-one-modulus
                            (dividend left))
                 (:instance poly-remainder-polynomial-one-modulus
                            (dividend right)))
           :in-theory (enable poly-congruent-p))))

(defthm poly-congruent-p-nonzero-constant-modulus
  (implies (and (consp (normalize modulus))
                (equal (poly-degree (normalize modulus)) 0))
           (poly-congruent-p left right modulus))
  :hints (("Goal"
           :use ((:instance poly-remainder-nonzero-constant-modulus
                            (dividend left))
                 (:instance poly-remainder-nonzero-constant-modulus
                            (dividend right)))
           :in-theory (enable poly-congruent-p))))

; Literal representative equality is stronger and more useful here than a
; congruence conclusion.  Each proof factors through the already-certified
; unconditional invariance of the corresponding reduced operation.
(defthm poly-reduced-add-respects-poly-congruent-p
  (implies (and (poly-congruent-p left-a left-b modulus)
                (poly-congruent-p right-a right-b modulus))
           (equal (poly-reduced-add left-a right-a modulus)
                  (poly-reduced-add left-b right-b modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-iff-equal-remainders
                     (left left-a) (right left-b))
          (:instance poly-congruent-p-iff-equal-remainders
                     (left right-a) (right right-b))
          (:instance poly-reduced-add-of-remainders
                     (left left-a) (right right-a))
          (:instance poly-reduced-add-of-remainders
                     (left left-b) (right right-b))))))

(defthm poly-reduced-neg-respects-poly-congruent-p
  (implies (poly-congruent-p left right modulus)
           (equal (poly-reduced-neg left modulus)
                  (poly-reduced-neg right modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-iff-equal-remainders)
          (:instance poly-reduced-neg-of-remainder (polynomial left))
          (:instance poly-reduced-neg-of-remainder (polynomial right))))))

(defthm poly-reduced-sub-respects-poly-congruent-p
  (implies (and (poly-congruent-p left-a left-b modulus)
                (poly-congruent-p right-a right-b modulus))
           (equal (poly-reduced-sub left-a right-a modulus)
                  (poly-reduced-sub left-b right-b modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-iff-equal-remainders
                     (left left-a) (right left-b))
          (:instance poly-congruent-p-iff-equal-remainders
                     (left right-a) (right right-b))
          (:instance poly-reduced-sub-of-remainders
                     (left left-a) (right right-a))
          (:instance poly-reduced-sub-of-remainders
                     (left left-b) (right right-b))))))

(defthm poly-reduced-mul-respects-poly-congruent-p
  (implies (and (poly-congruent-p left-a left-b modulus)
                (poly-congruent-p right-a right-b modulus))
           (equal (poly-reduced-mul left-a right-a modulus)
                  (poly-reduced-mul left-b right-b modulus)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance poly-congruent-p-iff-equal-remainders
                     (left left-a) (right left-b))
          (:instance poly-congruent-p-iff-equal-remainders
                     (left right-a) (right right-b))
          (:instance poly-reduced-mul-of-remainders
                     (left left-a) (right right-a))
          (:instance poly-reduced-mul-of-remainders
                     (left left-b) (right right-b))))))
