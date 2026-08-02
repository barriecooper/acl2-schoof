(in-package "GFIELD")

(include-book "curve-point-pair-output-point-associativity")
(include-book "curve-point-addition-inverse")

; Equality is preserved by a common executable left translation.  Keeping this
; substitution step explicit lets the cancellation proof expose only equality
; congruence, rather than any implementation detail of point addition.
(local
 (defthm left-translate-equality-by-neg-local
   (implies
    (equal (curve-point-pair-output-point a b)
           (curve-point-pair-output-point a c))
    (equal
     (curve-point-pair-output-point
      (curve-point-neg a) (curve-point-pair-output-point a b))
     (curve-point-pair-output-point
      (curve-point-neg a) (curve-point-pair-output-point a c))))
   :rule-classes nil
   :hints (("Goal" :in-theory (theory 'minimal-theory)))))

; Associativity, the left inverse, and left identity normalize a translation
; by -a.  Closure supplies precisely the domain needed by associativity.
(local
 (defthm left-associated-cancellation-normal-form-local
   (implies
    (and
     (short-weierstrass-characteristic-p)
     (short-weierstrass-curve-point-p a)
     (short-weierstrass-curve-point-p b))
    (equal
     (curve-point-pair-output-point
      (curve-point-neg a) (curve-point-pair-output-point a b))
     b))
   :rule-classes nil
   :hints
   (("Goal"
     :use
     ((:instance short-weierstrass-curve-point-p-of-neg (point a))
      (:instance curve-point-pair-output-point-associative
                 (a (curve-point-neg a)) (b a) (c b))
      (:instance curve-point-pair-output-point-with-negate-left (point a))
      (:instance curve-point-pair-output-point-identity-left (point b)))
     :in-theory (theory 'minimal-theory)))))

(defthm curve-point-pair-output-point-cancel-left
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c)
    (equal
     (curve-point-pair-output-point a b)
     (curve-point-pair-output-point a c)))
   (equal b c))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (left-translate-equality-by-neg-local
     (:instance left-associated-cancellation-normal-form-local (b b))
     (:instance left-associated-cancellation-normal-form-local (b c)))
    :in-theory (theory 'minimal-theory))))

; Commutativity converts a common right operand to the left-cancellation
; orientation, avoiding a duplicate inverse/associativity argument.
(defthm curve-point-pair-output-point-cancel-right
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c)
    (equal
     (curve-point-pair-output-point b a)
     (curve-point-pair-output-point c a)))
   (equal b c))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance curve-point-pair-output-point-commutative
                (first b) (second a))
     (:instance curve-point-pair-output-point-commutative
                (first c) (second a))
     (:instance curve-point-pair-output-point-cancel-left))
    :in-theory (theory 'minimal-theory))))
