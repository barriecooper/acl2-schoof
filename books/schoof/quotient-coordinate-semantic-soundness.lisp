(in-package "GPOLY")

(include-book "quotient-coordinate-semantics")
(include-book "quotient-coordinate-trace-predicate")

; The cardinality-indexed names retain exactly the totalized exponent
; semantics of quotient-coordinate-pow; in particular, q and iterations are
; both read through nfix by the underlying definitions.
(defthm quotient-coordinate-semantic-eval-of-frobenius
  (implies (and (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-frobenius coordinate q a b modulus) x0 y0)
            (gfield::field-pow
             (quotient-coordinate-semantic-eval coordinate x0 y0) q)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance quotient-coordinate-semantic-eval-of-pow
                                    (n q)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(quotient-coordinate-frobenius)))))

(defthm quotient-coordinate-semantic-eval-of-frobenius-iterate
  (implies (and (equal (eval modulus x0) (gfield::field-zero))
                (quotient-coordinate-semantic-curve-p x0 y0 a b))
           (equal
            (quotient-coordinate-semantic-eval
             (quotient-coordinate-frobenius-iterate
              coordinate q iterations a b modulus) x0 y0)
            (gfield::field-pow
             (quotient-coordinate-semantic-eval coordinate x0 y0)
             (expt (nfix q) (nfix iterations)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance quotient-coordinate-semantic-eval-of-pow
                                    (n (expt (nfix q) (nfix iterations)))))
           :in-theory
           (union-theories (theory 'minimal-theory)
                           '(quotient-coordinate-frobenius-iterate)))))

; These field predicates deliberately retain the cross-products.  No
; denominator is cancelled and no affine group-law interpretation is implied.
(defun quotient-coordinate-field-cross-add-p (x1 y1 x2 y2 x3 y3)
  (let ((d (gfield::field-sub x2 x1))
        (n (gfield::field-sub y2 y1)))
    (and
     (equal
      (gfield::field-mul
       (gfield::field-mul d d)
       (gfield::field-add x1 (gfield::field-add x2 x3)))
      (gfield::field-mul n n))
     (equal
      (gfield::field-mul d (gfield::field-add y1 y3))
      (gfield::field-mul n (gfield::field-sub x1 x3))))))

(defun quotient-coordinate-field-cross-opposite-p (x1 y1 x2 y2)
  (and (equal (gfield::field-fix x1) (gfield::field-fix x2))
       (equal (gfield::field-add y1 y2) (gfield::field-zero))))

(defthm quotient-coordinate-cross-add-p-semantic-soundness
  (implies
   (and (equal (eval modulus x0) (gfield::field-zero))
        (quotient-coordinate-semantic-curve-p x0 y0 a b)
        (quotient-coordinate-cross-add-p
         x1 y1 x2 y2 x3 y3 a b modulus))
   (quotient-coordinate-field-cross-add-p
    (quotient-coordinate-semantic-eval x1 x0 y0)
    (quotient-coordinate-semantic-eval y1 x0 y0)
    (quotient-coordinate-semantic-eval x2 x0 y0)
    (quotient-coordinate-semantic-eval y2 x0 y0)
    (quotient-coordinate-semantic-eval x3 x0 y0)
    (quotient-coordinate-semantic-eval y3 x0 y0)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-cross-add-p
              quotient-coordinate-field-cross-add-p
              quotient-coordinate-semantic-eval-of-add
              quotient-coordinate-semantic-eval-of-sub))
           :use
           ((:instance quotient-coordinate-semantic-eval-of-mul
                       (left (quotient-coordinate-sub x2 x1 modulus))
                       (right (quotient-coordinate-sub x2 x1 modulus)))
            (:instance quotient-coordinate-semantic-eval-of-mul
                       (left (quotient-coordinate-sub y2 y1 modulus))
                       (right (quotient-coordinate-sub y2 y1 modulus)))
            (:instance quotient-coordinate-semantic-eval-of-mul
                       (left (quotient-coordinate-mul
                              (quotient-coordinate-sub x2 x1 modulus)
                              (quotient-coordinate-sub x2 x1 modulus)
                              a b modulus))
                       (right (quotient-coordinate-add
                               x1 (quotient-coordinate-add x2 x3 modulus)
                               modulus)))
            (:instance quotient-coordinate-semantic-eval-of-mul
                       (left (quotient-coordinate-sub x2 x1 modulus))
                       (right (quotient-coordinate-add y1 y3 modulus)))
            (:instance quotient-coordinate-semantic-eval-of-mul
                       (left (quotient-coordinate-sub y2 y1 modulus))
                       (right (quotient-coordinate-sub x1 x3 modulus)))))))

(defthm quotient-coordinate-cross-opposite-p-semantic-soundness
  (implies
   (and (equal (eval modulus x0) (gfield::field-zero))
        (quotient-coordinate-cross-opposite-p x1 y1 x2 y2 modulus))
   (quotient-coordinate-field-cross-opposite-p
    (quotient-coordinate-semantic-eval x1 x0 y0)
    (quotient-coordinate-semantic-eval y1 x0 y0)
    (quotient-coordinate-semantic-eval x2 x0 y0)
    (quotient-coordinate-semantic-eval y2 x0 y0)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-cross-opposite-p
              quotient-coordinate-field-cross-opposite-p))
           :use ((:instance quotient-coordinate-semantic-eval-of-fix
                            (coordinate x1))
                 (:instance quotient-coordinate-semantic-eval-of-fix
                            (coordinate x2))
                 (:instance quotient-coordinate-semantic-eval-of-add
                            (left y1) (right y2))
                 (:instance quotient-coordinate-semantic-eval-of-zero)))))

(defun quotient-coordinate-field-trace-candidate-p (x y q trace)
  (let* ((pi-x (gfield::field-pow x q))
         (pi-y (gfield::field-pow y q))
         (pi2-x (gfield::field-pow x (expt (nfix q) 2)))
         (pi2-y (gfield::field-pow y (expt (nfix q) 2)))
         (minus-y (gfield::field-neg y))
         (residue (mod (nfix trace) 3)))
    (if (equal residue 0)
        (quotient-coordinate-field-cross-opposite-p
         pi2-x pi2-y x minus-y)
      (quotient-coordinate-field-cross-add-p
       pi2-x pi2-y x minus-y pi-x
       (if (equal residue 1) pi-y (gfield::field-neg pi-y))))))

(local (defthm nfix-of-two-for-semantic-trace
         (equal (nfix 2) 2)))

(defthm quotient-coordinate-trace-candidate-p-semantic-soundness
  (implies
   (and (equal (eval modulus x0) (gfield::field-zero))
        (quotient-coordinate-semantic-curve-p x0 y0 a b)
        (quotient-coordinate-trace-candidate-p x y q trace a b modulus))
   (quotient-coordinate-field-trace-candidate-p
    (quotient-coordinate-semantic-eval x x0 y0)
    (quotient-coordinate-semantic-eval y x0 y0)
    q trace))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance quotient-coordinate-cross-add-p-semantic-soundness
                            (x1 (quotient-coordinate-frobenius-iterate x q 2 a b modulus))
                            (y1 (quotient-coordinate-frobenius-iterate y q 2 a b modulus))
                            (x2 x) (y2 (quotient-coordinate-neg y modulus))
                            (x3 (quotient-coordinate-frobenius x q a b modulus))
                            (y3 (if (equal (mod (nfix trace) 3) 1)
                                    (quotient-coordinate-frobenius y q a b modulus)
                                  (quotient-coordinate-neg
                                   (quotient-coordinate-frobenius y q a b modulus)
                                   modulus))))
                 (:instance quotient-coordinate-cross-opposite-p-semantic-soundness
                            (x1 (quotient-coordinate-frobenius-iterate x q 2 a b modulus))
                            (y1 (quotient-coordinate-frobenius-iterate y q 2 a b modulus))
                            (x2 x) (y2 (quotient-coordinate-neg y modulus)))
                 (:instance quotient-coordinate-semantic-eval-of-frobenius
                            (coordinate x))
                 (:instance quotient-coordinate-semantic-eval-of-frobenius
                            (coordinate y))
                 (:instance quotient-coordinate-semantic-eval-of-frobenius-iterate
                            (coordinate x) (iterations 2))
                 (:instance quotient-coordinate-semantic-eval-of-frobenius-iterate
                            (coordinate y) (iterations 2))
                 (:instance quotient-coordinate-semantic-eval-of-neg
                            (coordinate y))
                 (:instance quotient-coordinate-semantic-eval-of-neg
                            (coordinate (quotient-coordinate-frobenius
                                         y q a b modulus))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(quotient-coordinate-trace-candidate-p
              quotient-coordinate-field-trace-candidate-p
              nfix-of-two-for-semantic-trace)))))
