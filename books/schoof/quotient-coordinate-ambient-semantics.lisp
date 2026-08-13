(in-package "GPOLY")

(include-book "quotient-coordinate-power")
(include-book "../polynomial/generic/ambient-evaluation")

; The ambient value denoted by u(x)+y*v(x).  Selectors deliberately give this a
; total meaning on malformed coordinate objects.
(defun quotient-coordinate-ambient-eval (coordinate x0 y0)
  (gfield::ambient-add
   (ambient-eval (quotient-coordinate-u coordinate) x0)
   (gfield::ambient-mul y0 (ambient-eval (quotient-coordinate-v coordinate) x0))))

(defun quotient-coordinate-ambient-curve-p (x0 y0 a b)
  (equal
   (gfield::ambient-mul y0 y0)
   (gfield::ambient-add
    (gfield::ambient-mul (gfield::ambient-mul x0 x0) x0)
    (gfield::ambient-add
     (gfield::ambient-mul (gfield::base-to-ambient a) x0)
     (gfield::base-to-ambient b)))))

(local
 (defthm eval-remainder-at-root-rewrite
   (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
            (equal (ambient-eval (poly-remainder polynomial modulus) x0)
                   (ambient-eval polynomial x0)))
   :hints (("Goal" :use ((:instance ambient-eval-of-poly-remainder-at-root
                                    (x x0)))))))

(local (in-theory (disable poly-remainder poly-divmod poly-reduced-add
                           poly-reduced-neg poly-reduced-sub poly-reduced-mul
                           poly-reduced-one)))

(defthm quotient-coordinate-ambient-eval-of-fix
  (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
           (equal (quotient-coordinate-ambient-eval
                   (quotient-coordinate-fix coordinate modulus) x0 y0)
                  (quotient-coordinate-ambient-eval coordinate x0 y0)))
  :hints (("Goal"
           :use ((:instance eval-remainder-at-root-rewrite
                            (polynomial (quotient-coordinate-u coordinate)))
                 (:instance eval-remainder-at-root-rewrite
                            (polynomial (quotient-coordinate-v coordinate))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-ambient-eval quotient-coordinate-fix
              quotient-coordinate quotient-coordinate-u
              quotient-coordinate-v car-cons cdr-cons)))))

(defthm quotient-coordinate-ambient-eval-of-zero
  (equal (quotient-coordinate-ambient-eval
          (quotient-coordinate-zero modulus) x0 y0)
         (gfield::ambient-zero)))

(defthm quotient-coordinate-ambient-eval-of-one
  (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
           (equal (quotient-coordinate-ambient-eval
                   (quotient-coordinate-one modulus) x0 y0)
                  (gfield::ambient-one))))

(defthm quotient-coordinate-ambient-eval-of-x
  (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
           (equal (quotient-coordinate-ambient-eval
                   (quotient-coordinate-x modulus) x0 y0)
                  (gfield::ambient-fix x0))))

(defthm quotient-coordinate-ambient-eval-of-y
  (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
           (equal (quotient-coordinate-ambient-eval
                   (quotient-coordinate-y modulus) x0 y0)
                  (gfield::ambient-fix y0))))

(defthm quotient-coordinate-ambient-eval-of-add
  (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-add left right modulus) x0 y0)
            (gfield::ambient-add
             (quotient-coordinate-ambient-eval left x0 y0)
             (quotient-coordinate-ambient-eval right x0 y0)))))

(defthm quotient-coordinate-ambient-eval-of-neg
  (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-neg coordinate modulus) x0 y0)
            (gfield::ambient-neg
             (quotient-coordinate-ambient-eval coordinate x0 y0)))))

(defthm quotient-coordinate-ambient-eval-of-sub
  (implies (equal (ambient-eval modulus x0) (gfield::ambient-zero))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-sub left right modulus) x0 y0)
            (gfield::ambient-sub
             (quotient-coordinate-ambient-eval left x0 y0)
             (quotient-coordinate-ambient-eval right x0 y0)))))

(defthm quotient-coordinate-ambient-eval-of-mul
  (implies (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
                (quotient-coordinate-ambient-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-mul left right a b modulus) x0 y0)
            (gfield::ambient-mul
             (quotient-coordinate-ambient-eval left x0 y0)
             (quotient-coordinate-ambient-eval right x0 y0))))
  :rule-classes nil)

(local (defun ambient-power-induct (n)
         (if (zp n) nil (ambient-power-induct (1- n)))))
(local (defthm ambient-power-positive-predecessor
         (implies (and (natp n) (not (zp n)))
                  (and (natp (1- n))
                       (equal (+ 1 (1- n)) n)))
         :rule-classes nil))

(local
 (defthm quotient-coordinate-ambient-eval-of-pow-when-natp
  (implies (and (natp n)
                (equal (ambient-eval modulus x0) (gfield::ambient-zero))
                (quotient-coordinate-ambient-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-pow coordinate n a b modulus) x0 y0)
            (gfield::ambient-pow
             (quotient-coordinate-ambient-eval coordinate x0 y0) n)))
  :hints (("Goal" :induct (ambient-power-induct n)
           :in-theory (enable ambient-power-induct))
          ("Subgoal *1/2"
           :use ((:instance quotient-coordinate-pow-successor
                            (base coordinate) (n (1- n)))
                 ambient-power-positive-predecessor
                 (:instance gfield::ambient-pow-successor-total
                            (x (quotient-coordinate-ambient-eval coordinate x0 y0))
                            (n (1- n)))
                 (:instance quotient-coordinate-ambient-eval-of-mul
                            (left coordinate)
                            (right (quotient-coordinate-pow coordinate (1- n)
                                                            a b modulus))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(nfix natp zp)))
          ("Subgoal *1/1"
           :use ((:instance quotient-coordinate-pow-zero (base coordinate))
                 (:instance quotient-coordinate-ambient-eval-of-one)
                 (:instance gfield::ambient-pow-zero
                            (x (quotient-coordinate-ambient-eval coordinate x0 y0))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(natp zp))))))

(defthm quotient-coordinate-ambient-eval-of-pow
  (implies (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
                (quotient-coordinate-ambient-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-pow coordinate n a b modulus) x0 y0)
            (gfield::ambient-pow
             (quotient-coordinate-ambient-eval coordinate x0 y0) n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-ambient-eval-of-pow-when-natp
                            (n (nfix n))))
           :in-theory (enable quotient-coordinate-pow-of-nfix
                              gfield::ambient-pow-of-nfix))))
