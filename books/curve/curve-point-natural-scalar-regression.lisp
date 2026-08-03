(in-package "GFIELD")

(include-book "curve-point-natural-scalar")

; Client-side generation exercises the public scalar instantiation endpoint.
(def-curve-point-natural-scalar-theorem
  curve-point-natural-scalar-client-sum
  abelian-group-nat-mul-of-sum)

(def-curve-point-natural-scalar-theorem
  curve-point-natural-scalar-client-composition
  abelian-group-nat-mul-of-nat-mul)

(defthm curve-point-natural-scalar-composition-zero-left-client
  (implies (and (short-weierstrass-characteristic-p)
                (natp n)
                (short-weierstrass-curve-point-p point))
           (equal (curve-point-nat-mul 0 (curve-point-nat-mul n point))
                  (curve-point-nat-mul (* 0 n) point)))
  :hints (("Goal" :use ((:instance curve-point-nat-mul-of-nat-mul
                                   (m 0) (x point)))
           :in-theory (union-theories (theory 'minimal-theory) '(natp)))))

(defthm curve-point-natural-scalar-composition-zero-right-client
  (implies (and (short-weierstrass-characteristic-p)
                (natp m)
                (short-weierstrass-curve-point-p point))
           (equal (curve-point-nat-mul m (curve-point-nat-mul 0 point))
                  (curve-point-nat-mul (* m 0) point)))
  :hints (("Goal" :use ((:instance curve-point-nat-mul-of-nat-mul
                                   (n 0) (x point)))
           :in-theory (union-theories (theory 'minimal-theory) '(natp)))))

(defthm curve-point-natural-scalar-composition-one-left-client
  (implies (and (short-weierstrass-characteristic-p)
                (natp n)
                (short-weierstrass-curve-point-p point))
           (equal (curve-point-nat-mul 1 (curve-point-nat-mul n point))
                  (curve-point-nat-mul (* 1 n) point)))
  :hints (("Goal" :use ((:instance curve-point-nat-mul-of-nat-mul
                                   (m 1) (x point)))
           :in-theory (union-theories (theory 'minimal-theory) '(natp)))))

(defthm curve-point-natural-scalar-composition-one-right-client
  (implies (and (short-weierstrass-characteristic-p)
                (natp m)
                (short-weierstrass-curve-point-p point))
           (equal (curve-point-nat-mul m (curve-point-nat-mul 1 point))
                  (curve-point-nat-mul (* m 1) point)))
  :hints (("Goal" :use ((:instance curve-point-nat-mul-of-nat-mul
                                   (n 1) (x point)))
           :in-theory (union-theories (theory 'minimal-theory) '(natp)))))
