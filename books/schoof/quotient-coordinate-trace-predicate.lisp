(in-package "GPOLY")

(include-book "quotient-coordinate-power")

; Division-free affine secant relation.  D=x2-x1 and N=y2-y1.  The two
; equations are D^2(x1+x2+x3)=N^2 and D(y1+y3)=N(x1-x3).  Over a field, and
; only when D is invertible, these are the usual affine addition formulas.
; Here they are deliberately just quotient-ring equalities: D may be a zero
; divisor, so no converse affine/group-law claim is made.
(defun quotient-coordinate-cross-add-p
  (x1 y1 x2 y2 x3 y3 a b modulus)
  (let ((d (quotient-coordinate-sub x2 x1 modulus))
        (n (quotient-coordinate-sub y2 y1 modulus)))
    (and
     (equal
      (quotient-coordinate-mul
       (quotient-coordinate-mul d d a b modulus)
       (quotient-coordinate-add
        x1 (quotient-coordinate-add x2 x3 modulus) modulus)
       a b modulus)
      (quotient-coordinate-mul n n a b modulus))
     (equal
      (quotient-coordinate-mul
       d (quotient-coordinate-add y1 y3 modulus) a b modulus)
      (quotient-coordinate-mul
       n (quotient-coordinate-sub x1 x3 modulus) a b modulus)))))

; A narrow algebraic spelling of P1+P2=infinity: equal fixed x coordinates
; and opposite y coordinates.  This is not a complete projective point layer.
(defun quotient-coordinate-cross-opposite-p (x1 y1 x2 y2 modulus)
  (and (equal (quotient-coordinate-fix x1 modulus)
              (quotient-coordinate-fix x2 modulus))
       (equal (quotient-coordinate-add y1 y2 modulus)
              (quotient-coordinate-zero modulus))))

; Algebraic trace candidate for pi^2(P)-P=[t]pi(P), with t reduced modulo 3.
; Residue 0 uses the narrow infinity relation; residues 1 and 2 use the two
; cross-multiplied secant equations with target pi(P) and -pi(P).
(defun quotient-coordinate-trace-candidate-p
  (x y q trace a b modulus)
  (let* ((pi-x (quotient-coordinate-frobenius x q a b modulus))
         (pi-y (quotient-coordinate-frobenius y q a b modulus))
         (pi2-x (quotient-coordinate-frobenius-iterate x q 2 a b modulus))
         (pi2-y (quotient-coordinate-frobenius-iterate y q 2 a b modulus))
         (minus-y (quotient-coordinate-neg y modulus))
         (residue (mod (nfix trace) 3)))
    (if (equal residue 0)
        (quotient-coordinate-cross-opposite-p
         pi2-x pi2-y x minus-y modulus)
      (quotient-coordinate-cross-add-p
       pi2-x pi2-y x minus-y
       pi-x (if (equal residue 1)
                pi-y
              (quotient-coordinate-neg pi-y modulus))
       a b modulus))))

(defthm booleanp-of-quotient-coordinate-cross-add-p
  (booleanp (quotient-coordinate-cross-add-p
             x1 y1 x2 y2 x3 y3 a b modulus)))

(defthm booleanp-of-quotient-coordinate-cross-opposite-p
  (booleanp (quotient-coordinate-cross-opposite-p x1 y1 x2 y2 modulus)))

(defthm booleanp-of-quotient-coordinate-trace-candidate-p
  (booleanp (quotient-coordinate-trace-candidate-p
             x y q trace a b modulus)))

(defthm quotient-coordinate-trace-candidate-of-nfix
  (equal (quotient-coordinate-trace-candidate-p
          x y q (nfix trace) a b modulus)
         (quotient-coordinate-trace-candidate-p
          x y q trace a b modulus)))

(defthm quotient-coordinate-trace-candidate-malformed-trace
  (implies (not (natp trace))
           (equal (quotient-coordinate-trace-candidate-p
                   x y q trace a b modulus)
                  (quotient-coordinate-trace-candidate-p
                   x y q 0 a b modulus))))

; Public semantic contract: exactly the two displayed cross-products (or the
; narrow opposite relation for residue zero), with no hidden division.
(defthm quotient-coordinate-trace-candidate-definition
  (equal
   (quotient-coordinate-trace-candidate-p x y q trace a b modulus)
   (let* ((pi-x (quotient-coordinate-frobenius x q a b modulus))
          (pi-y (quotient-coordinate-frobenius y q a b modulus))
          (pi2-x (quotient-coordinate-frobenius-iterate x q 2 a b modulus))
          (pi2-y (quotient-coordinate-frobenius-iterate y q 2 a b modulus))
          (minus-y (quotient-coordinate-neg y modulus))
          (residue (mod (nfix trace) 3)))
     (if (equal residue 0)
         (quotient-coordinate-cross-opposite-p
          pi2-x pi2-y x minus-y modulus)
       (quotient-coordinate-cross-add-p
        pi2-x pi2-y x minus-y pi-x
        (if (equal residue 1) pi-y
          (quotient-coordinate-neg pi-y modulus))
        a b modulus))))
  :rule-classes nil)

(verify-guards quotient-coordinate-cross-add-p)
(verify-guards quotient-coordinate-cross-opposite-p)
(verify-guards quotient-coordinate-trace-candidate-p)
