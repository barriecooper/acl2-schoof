(in-package "GPOLY")

(include-book "f11-quotient-coordinate-evaluation")

(defthm f11-eval-at-universal-x-minimal-theory-client
  (equal (f11-quotient-coordinate-eval
          polynomial (f11-quotient-coordinate-x modulus) a b modulus)
         (f11-quotient-coordinate-embed
          (f11-poly-remainder polynomial modulus) modulus))
  :rule-classes nil
  :hints (("Goal" :use f11-quotient-coordinate-eval-at-universal-x
           :in-theory (theory 'minimal-theory))))

(defthm f11-modulus-at-universal-x-minimal-theory-client
  (equal (f11-quotient-coordinate-eval
          modulus (f11-quotient-coordinate-x modulus) a b modulus)
         (f11-quotient-coordinate-zero modulus))
  :rule-classes nil
  :hints (("Goal" :use f11-quotient-coordinate-modulus-eval-at-universal-x
           :in-theory (theory 'minimal-theory))))

(defthm f11-golden-psi3-at-universal-x-minimal-theory-client
  (let ((modulus (f11-division-polynomial 3 1 6)))
    (equal (f11-quotient-coordinate-eval
            modulus (f11-quotient-coordinate-x modulus) 1 6 modulus)
           (f11-quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal" :use f11-golden-psi3-eval-at-universal-x
           :in-theory (theory 'minimal-theory))))

(defthm f11-golden-literal-psi3-at-universal-x-minimal-theory-client
  (equal (f11-quotient-coordinate-eval
          '(10 6 6 0 3)
          (f11-quotient-coordinate-x '(10 6 6 0 3))
          1 6 '(10 6 6 0 3))
         (f11-quotient-coordinate-zero '(10 6 6 0 3)))
  :rule-classes nil
  :hints (("Goal" :use f11-golden-literal-psi3-eval-at-universal-x
           :in-theory (theory 'minimal-theory))))
