(in-package "GPOLY")

(include-book "quotient-coordinate-power")
(include-book "../polynomial/generic/remainder-evaluation")

; The field value denoted by u(x)+y*v(x).  Selectors deliberately give this a
; total meaning on malformed coordinate objects.
(defun quotient-coordinate-semantic-eval (coordinate x0 y0)
  (gfield::field-add
   (eval (quotient-coordinate-u coordinate) x0)
   (gfield::field-mul y0 (eval (quotient-coordinate-v coordinate) x0))))

(defun quotient-coordinate-semantic-curve-p (x0 y0 a b)
  (equal
   (gfield::field-mul y0 y0)
   (gfield::field-add
    (gfield::field-mul (gfield::field-mul x0 x0) x0)
    (gfield::field-add (gfield::field-mul a x0) b))))

(local
 (defthm eval-remainder-at-root-rewrite
   (implies (equal (eval modulus x0) (gfield::field-zero))
            (equal (eval (poly-remainder polynomial modulus) x0)
                   (eval polynomial x0)))
   :hints (("Goal" :use ((:instance eval-of-poly-remainder-at-root
                                    (x x0)))))))

(local (in-theory (disable poly-remainder poly-divmod poly-reduced-add
                           poly-reduced-neg poly-reduced-sub poly-reduced-mul
                           poly-reduced-one)))

(defthm quotient-coordinate-semantic-eval-of-fix
  (implies (equal (eval modulus x0) (gfield::field-zero))
           (equal (quotient-coordinate-semantic-eval
                   (quotient-coordinate-fix coordinate modulus) x0 y0)
                  (quotient-coordinate-semantic-eval coordinate x0 y0)))
  :hints (("Goal"
           :use ((:instance eval-remainder-at-root-rewrite
                            (polynomial (quotient-coordinate-u coordinate)))
                 (:instance eval-remainder-at-root-rewrite
                            (polynomial (quotient-coordinate-v coordinate))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-semantic-eval quotient-coordinate-fix
              quotient-coordinate quotient-coordinate-u
              quotient-coordinate-v car-cons cdr-cons)))))

(defthm quotient-coordinate-semantic-eval-of-zero
  (equal (quotient-coordinate-semantic-eval
          (quotient-coordinate-zero modulus) x0 y0)
         (gfield::field-zero)))

(defthm quotient-coordinate-semantic-eval-of-one
  (implies (equal (eval modulus x0) (gfield::field-zero))
           (equal (quotient-coordinate-semantic-eval
                   (quotient-coordinate-one modulus) x0 y0)
                  (gfield::field-one))))

(defthm quotient-coordinate-semantic-eval-of-x
  (implies (equal (eval modulus x0) (gfield::field-zero))
           (equal (quotient-coordinate-semantic-eval
                   (quotient-coordinate-x modulus) x0 y0)
                  (gfield::field-fix x0))))

(defthm quotient-coordinate-semantic-eval-of-y
  (implies (equal (eval modulus x0) (gfield::field-zero))
           (equal (quotient-coordinate-semantic-eval
                   (quotient-coordinate-y modulus) x0 y0)
                  (gfield::field-fix y0))))

(defthm quotient-coordinate-semantic-eval-of-add
  (implies (equal (eval modulus x0) (gfield::field-zero))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-add left right modulus) x0 y0)
            (gfield::field-add
             (quotient-coordinate-semantic-eval left x0 y0)
             (quotient-coordinate-semantic-eval right x0 y0)))))

(defthm quotient-coordinate-semantic-eval-of-neg
  (implies (equal (eval modulus x0) (gfield::field-zero))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-neg coordinate modulus) x0 y0)
            (gfield::field-neg
             (quotient-coordinate-semantic-eval coordinate x0 y0)))))

(defthm quotient-coordinate-semantic-eval-of-sub
  (implies (equal (eval modulus x0) (gfield::field-zero))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-sub left right modulus) x0 y0)
            (gfield::field-sub
             (quotient-coordinate-semantic-eval left x0 y0)
             (quotient-coordinate-semantic-eval right x0 y0)))))

(defthm quotient-coordinate-semantic-eval-of-mul
  (implies (and (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-mul left right a b modulus) x0 y0)
            (gfield::field-mul
             (quotient-coordinate-semantic-eval left x0 y0)
             (quotient-coordinate-semantic-eval right x0 y0))))
  :rule-classes nil)

(local (defun semantic-power-induct (n)
         (if (zp n) nil (semantic-power-induct (1- n)))))
(local (defthm semantic-power-positive-predecessor
         (implies (and (natp n) (not (zp n)))
                  (and (natp (1- n))
                       (equal (+ 1 (1- n)) n)))
         :rule-classes nil))

(local
 (defthm quotient-coordinate-semantic-eval-of-pow-when-natp
  (implies (and (natp n)
                (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-pow coordinate n a b modulus) x0 y0)
            (gfield::field-pow
             (quotient-coordinate-semantic-eval coordinate x0 y0) n)))
  :hints (("Goal" :induct (semantic-power-induct n)
           :in-theory (enable semantic-power-induct))
          ("Subgoal *1/2"
           :use ((:instance quotient-coordinate-pow-successor
                            (base coordinate) (n (1- n)))
                 semantic-power-positive-predecessor
                 (:instance gfield::field-pow-successor-total
                            (x (quotient-coordinate-semantic-eval coordinate x0 y0))
                            (n (1- n)))
                 (:instance quotient-coordinate-semantic-eval-of-mul
                            (left coordinate)
                            (right (quotient-coordinate-pow coordinate (1- n)
                                                            a b modulus))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(nfix natp zp)))
          ("Subgoal *1/1"
           :use ((:instance quotient-coordinate-pow-zero (base coordinate))
                 (:instance quotient-coordinate-semantic-eval-of-one)
                 (:instance gfield::field-pow-zero
                            (x (quotient-coordinate-semantic-eval coordinate x0 y0))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(natp zp))))))

(defthm quotient-coordinate-semantic-eval-of-pow
  (implies (and (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-pow coordinate n a b modulus) x0 y0)
            (gfield::field-pow
             (quotient-coordinate-semantic-eval coordinate x0 y0) n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-semantic-eval-of-pow-when-natp
                            (n (nfix n))))
           :in-theory (enable quotient-coordinate-pow-of-nfix
                              gfield::field-pow-of-nfix))))
