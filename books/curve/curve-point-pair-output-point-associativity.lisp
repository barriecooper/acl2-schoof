(in-package "GFIELD")

(include-book "curve-point-addition-relation-associativity")

; The dispatcher produces canonical tagged points on every ACL2 input.  Keep
; this bridge separate so clients of executable laws never need its definition.
(defthm curve-point-fix-of-curve-point-pair-output-point
  (equal
   (curve-point-fix (curve-point-pair-output-point first second))
   (curve-point-pair-output-point first second))
  :hints
  (("Goal"
    :use curve-point-representation-p-of-curve-point-pair-output-point
    :in-theory
    (union-theories (theory 'minimal-theory)
                    '(curve-point-fix-when-representation-p)))))

; Semantic associativity applied to the four dispatcher witnesses.  Closure of
; the two inner calls supplies the domains for the two outer soundness facts.
(defthm curve-point-pair-output-point-associative-fixed
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c))
   (equal
    (curve-point-fix
     (curve-point-pair-output-point
      (curve-point-pair-output-point a b) c))
    (curve-point-fix
     (curve-point-pair-output-point
      a (curve-point-pair-output-point b c)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance short-weierstrass-curve-point-p-of-curve-point-pair-output-point
                (first a) (second b))
     (:instance short-weierstrass-curve-point-p-of-curve-point-pair-output-point
                (first b) (second c))
     (:instance curve-point-pair-output-point-satisfies-addition-relation
                (first a) (second b))
     (:instance curve-point-pair-output-point-satisfies-addition-relation
                (first b) (second c))
     (:instance curve-point-pair-output-point-satisfies-addition-relation
                (first (curve-point-pair-output-point a b)) (second c))
     (:instance curve-point-pair-output-point-satisfies-addition-relation
                (first a) (second (curve-point-pair-output-point b c)))
     (:instance curve-point-addition-relation-associative
                (ab (curve-point-pair-output-point a b))
                (bc (curve-point-pair-output-point b c))
                (left
                 (curve-point-pair-output-point
                  (curve-point-pair-output-point a b) c))
                (right
                 (curve-point-pair-output-point
                  a (curve-point-pair-output-point b c)))))
    :in-theory (theory 'minimal-theory))))

; Public executable endpoint.  No dispatcher unfolding or branch algebra is
; involved: canonical output removes the two fixers from the semantic result.
(defthm curve-point-pair-output-point-associative
  (implies
   (and
    (short-weierstrass-characteristic-p)
    (short-weierstrass-curve-point-p a)
    (short-weierstrass-curve-point-p b)
    (short-weierstrass-curve-point-p c))
   (equal
    (curve-point-pair-output-point
     (curve-point-pair-output-point a b) c)
    (curve-point-pair-output-point
     a (curve-point-pair-output-point b c))))
  :rule-classes nil
  :hints
  (("Goal"
    :use curve-point-pair-output-point-associative-fixed
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-fix-of-curve-point-pair-output-point)))))
