(in-package "GPOLY")

(include-book "quotient-coordinate-ambient-semantics")
(include-book "quotient-coordinate-trace-predicate")

; The cardinality-indexed names retain exactly the totalized exponent
; semantics of quotient-coordinate-pow; in particular, q and iterations are
; both read through nfix by the underlying definitions.
(defthm quotient-coordinate-ambient-eval-of-frobenius
  (implies (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
                (quotient-coordinate-ambient-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-ambient-eval
             (quotient-coordinate-frobenius coordinate q a b modulus) x0 y0)
            (gfield::ambient-pow
             (quotient-coordinate-ambient-eval coordinate x0 y0) q)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance quotient-coordinate-ambient-eval-of-pow
                                    (n q)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(quotient-coordinate-frobenius)))))

(defthm quotient-coordinate-ambient-eval-of-frobenius-iterate
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
  :hints (("Goal" :use ((:instance quotient-coordinate-ambient-eval-of-pow
                                    (n (expt (nfix q) (nfix iterations)))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(quotient-coordinate-frobenius-iterate)))))

; These field predicates deliberately retain the cross-products.  No
; denominator is cancelled and no affine group-law interpretation is implied.
(defun quotient-coordinate-ambient-cross-add-p (x1 y1 x2 y2 x3 y3)
  (let ((d (gfield::ambient-sub x2 x1))
        (n (gfield::ambient-sub y2 y1)))
    (and
     (equal
      (gfield::ambient-mul
       (gfield::ambient-mul d d)
       (gfield::ambient-add x1 (gfield::ambient-add x2 x3)))
      (gfield::ambient-mul n n))
     (equal
      (gfield::ambient-mul d (gfield::ambient-add y1 y3))
      (gfield::ambient-mul n (gfield::ambient-sub x1 x3))))))

(defun quotient-coordinate-ambient-cross-opposite-p (x1 y1 x2 y2)
  (and (equal (gfield::ambient-fix x1) (gfield::ambient-fix x2))
       (equal (gfield::ambient-add y1 y2) (gfield::ambient-zero))))

(defthm quotient-coordinate-cross-add-p-ambient-soundness
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
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-cross-add-p
              quotient-coordinate-ambient-cross-add-p
              quotient-coordinate-ambient-eval-of-add
              quotient-coordinate-ambient-eval-of-sub))
           :use
           ((:instance quotient-coordinate-ambient-eval-of-mul
                       (left (quotient-coordinate-sub x2 x1 modulus))
                       (right (quotient-coordinate-sub x2 x1 modulus)))
            (:instance quotient-coordinate-ambient-eval-of-mul
                       (left (quotient-coordinate-sub y2 y1 modulus))
                       (right (quotient-coordinate-sub y2 y1 modulus)))
            (:instance quotient-coordinate-ambient-eval-of-mul
                       (left (quotient-coordinate-mul
                              (quotient-coordinate-sub x2 x1 modulus)
                              (quotient-coordinate-sub x2 x1 modulus)
                              a b modulus))
                       (right (quotient-coordinate-add
                               x1 (quotient-coordinate-add x2 x3 modulus)
                               modulus)))
            (:instance quotient-coordinate-ambient-eval-of-mul
                       (left (quotient-coordinate-sub x2 x1 modulus))
                       (right (quotient-coordinate-add y1 y3 modulus)))
            (:instance quotient-coordinate-ambient-eval-of-mul
                       (left (quotient-coordinate-sub y2 y1 modulus))
                       (right (quotient-coordinate-sub x1 x3 modulus)))))))

(defthm quotient-coordinate-cross-opposite-p-ambient-soundness
  (implies
   (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
        (quotient-coordinate-cross-opposite-p x1 y1 x2 y2 modulus))
   (quotient-coordinate-ambient-cross-opposite-p
    (quotient-coordinate-ambient-eval x1 x0 y0)
    (quotient-coordinate-ambient-eval y1 x0 y0)
    (quotient-coordinate-ambient-eval x2 x0 y0)
    (quotient-coordinate-ambient-eval y2 x0 y0)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-cross-opposite-p
              quotient-coordinate-ambient-cross-opposite-p))
           :use ((:instance quotient-coordinate-ambient-eval-of-fix
                            (coordinate x1))
                 (:instance quotient-coordinate-ambient-eval-of-fix
                            (coordinate x2))
                 (:instance quotient-coordinate-ambient-eval-of-add
                            (left y1) (right y2))
                 (:instance quotient-coordinate-ambient-eval-of-zero)))))

(defun quotient-coordinate-ambient-trace-candidate-p (x y q trace)
  (let* ((pi-x (gfield::ambient-pow x q))
         (pi-y (gfield::ambient-pow y q))
         (pi2-x (gfield::ambient-pow x (expt (nfix q) 2)))
         (pi2-y (gfield::ambient-pow y (expt (nfix q) 2)))
         (minus-y (gfield::ambient-neg y))
         (residue (mod (nfix trace) 3)))
    (if (equal residue 0)
        (quotient-coordinate-ambient-cross-opposite-p
         pi2-x pi2-y x minus-y)
      (quotient-coordinate-ambient-cross-add-p
       pi2-x pi2-y x minus-y pi-x
       (if (equal residue 1) pi-y (gfield::ambient-neg pi-y))))))

(local (defthm nfix-of-two-for-ambient-trace
         (equal (nfix 2) 2)))

(defthm quotient-coordinate-trace-candidate-p-ambient-soundness
  (implies
   (and (equal (ambient-eval modulus x0) (gfield::ambient-zero))
        (quotient-coordinate-ambient-curve-p x0 y0 a b)
        (quotient-coordinate-trace-candidate-p x y q trace a b modulus))
   (quotient-coordinate-ambient-trace-candidate-p
    (quotient-coordinate-ambient-eval x x0 y0)
    (quotient-coordinate-ambient-eval y x0 y0)
    q trace))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-cross-add-p-ambient-soundness
                            (x1 (quotient-coordinate-frobenius-iterate x q 2 a b modulus))
                            (y1 (quotient-coordinate-frobenius-iterate y q 2 a b modulus))
                            (x2 x) (y2 (quotient-coordinate-neg y modulus))
                            (x3 (quotient-coordinate-frobenius x q a b modulus))
                            (y3 (if (equal (mod (nfix trace) 3) 1)
                                    (quotient-coordinate-frobenius y q a b modulus)
                                  (quotient-coordinate-neg
                                   (quotient-coordinate-frobenius y q a b modulus)
                                   modulus))))
                 (:instance quotient-coordinate-cross-opposite-p-ambient-soundness
                            (x1 (quotient-coordinate-frobenius-iterate x q 2 a b modulus))
                            (y1 (quotient-coordinate-frobenius-iterate y q 2 a b modulus))
                            (x2 x) (y2 (quotient-coordinate-neg y modulus)))
                 (:instance quotient-coordinate-ambient-eval-of-frobenius
                            (coordinate x))
                 (:instance quotient-coordinate-ambient-eval-of-frobenius
                            (coordinate y))
                 (:instance quotient-coordinate-ambient-eval-of-frobenius-iterate
                            (coordinate x) (iterations 2))
                 (:instance quotient-coordinate-ambient-eval-of-frobenius-iterate
                            (coordinate y) (iterations 2))
                 (:instance quotient-coordinate-ambient-eval-of-neg
                            (coordinate y))
                 (:instance quotient-coordinate-ambient-eval-of-neg
                            (coordinate (quotient-coordinate-frobenius
                                         y q a b modulus))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-trace-candidate-p
              quotient-coordinate-ambient-trace-candidate-p
              nfix-of-two-for-ambient-trace)))))
