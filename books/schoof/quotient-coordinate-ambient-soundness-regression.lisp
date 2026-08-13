(in-package "GPOLY")

(include-book "quotient-coordinate-ambient-soundness")

(defthm quotient-coordinate-frobenius-ambient-soundness-minimal-theory-client
  (implies (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
                (quotient-coordinate-ambient-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-frobenius coordinate q a b modulus) x0 y0)
            (gfield::ambient-pow
             (quotient-coordinate-ambient-eval coordinate x0 y0) q)))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-ambient-eval-of-frobenius
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-frobenius-iterate-ambient-soundness-minimal-theory-client
  (implies (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
                (quotient-coordinate-ambient-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-frobenius-iterate
              coordinate q iterations a b modulus) x0 y0)
            (gfield::ambient-pow
             (quotient-coordinate-ambient-eval coordinate x0 y0)
             (expt (nfix q) (nfix iterations)))))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-ambient-eval-of-frobenius-iterate
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-cross-add-ambient-soundness-minimal-theory-client
  (implies
   (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
        (quotient-coordinate-ambient-curve-p x0 y0 a b)
        (quotient-coordinate-cross-add-p
         x1 y1 x2 y2 x3 y3 a b modulus))
   (quotient-coordinate-ambient-cross-add-p
    (quotient-coordinate-ambient-eval x1 x0 y0)
    (quotient-coordinate-ambient-eval y1 x0 y0)
    (quotient-coordinate-ambient-eval x2 x0 y0)
    (quotient-coordinate-ambient-eval y2 x0 y0)
    (quotient-coordinate-ambient-eval x3 x0 y0)
    (quotient-coordinate-ambient-eval y3 x0 y0)))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-cross-add-p-ambient-soundness
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-cross-opposite-ambient-soundness-minimal-theory-client
  (implies
   (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
        (quotient-coordinate-cross-opposite-p x1 y1 x2 y2 modulus))
   (quotient-coordinate-ambient-cross-opposite-p
    (quotient-coordinate-ambient-eval x1 x0 y0)
    (quotient-coordinate-ambient-eval y1 x0 y0)
    (quotient-coordinate-ambient-eval x2 x0 y0)
    (quotient-coordinate-ambient-eval y2 x0 y0)))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-cross-opposite-p-ambient-soundness
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-trace-candidate-ambient-soundness-minimal-theory-client
  (implies
   (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
        (quotient-coordinate-ambient-curve-p x0 y0 a b)
        (quotient-coordinate-trace-candidate-p x y q trace a b modulus))
   (quotient-coordinate-ambient-trace-candidate-p
    (quotient-coordinate-ambient-eval x x0 y0)
    (quotient-coordinate-ambient-eval y x0 y0)
    q trace))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-trace-candidate-p-ambient-soundness
           :in-theory (theory 'minimal-theory))))

(defthm ambient-remainder-evaluation-minimal-theory-client
  (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
           (equal (ambient-eval (poly-remainder polynomial modulus) x0)
                  (ambient-eval polynomial x0)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance ambient-eval-of-poly-remainder-at-root (x x0)))
           :in-theory (theory 'minimal-theory))))

(defthm quotient-coordinate-mul-ambient-soundness-minimal-theory-client
  (implies (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
                (quotient-coordinate-ambient-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-mul left right a b modulus) x0 y0)
            (gfield::ambient-mul
             (quotient-coordinate-ambient-eval left x0 y0)
             (quotient-coordinate-ambient-eval right x0 y0))))
  :rule-classes nil
  :hints (("Goal" :use quotient-coordinate-ambient-eval-of-mul
           :in-theory (theory 'minimal-theory))))
