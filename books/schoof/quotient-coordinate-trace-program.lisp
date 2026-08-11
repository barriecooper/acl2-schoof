(in-package "GPOLY")

; Operation-parametric statement of the production cross-multiplied trace
; program.  The constrained operations carry no algebraic axioms: this seam
; certifies program structure only.
(encapsulate
 (((trace-program-fix * *) => *)
  ((trace-program-zero *) => *)
  ((trace-program-add * * *) => *)
  ((trace-program-neg * *) => *)
  ((trace-program-sub * * *) => *)
  ((trace-program-mul * * * * *) => *)
  ((trace-program-power * * * * *) => *)
  ((trace-program-power-iterate * * * * * *) => *))
 (local (defun trace-program-fix (x modulus) (declare (ignore modulus)) x))
 (local (defun trace-program-zero (modulus) (declare (ignore modulus)) nil))
 (local (defun trace-program-add (x y modulus)
          (declare (ignore y modulus)) x))
 (local (defun trace-program-neg (x modulus) (declare (ignore modulus)) x))
 (local (defun trace-program-sub (x y modulus)
          (declare (ignore y modulus)) x))
 (local (defun trace-program-mul (x y a b modulus)
          (declare (ignore y a b modulus)) x))
 (local (defun trace-program-power (x q a b modulus)
          (declare (ignore q a b modulus)) x))
 (local (defun trace-program-power-iterate (x q n a b modulus)
          (declare (ignore q n a b modulus)) x)))

(defun trace-program-cross-add-p (x1 y1 x2 y2 x3 y3 a b modulus)
  (let ((d (trace-program-sub x2 x1 modulus))
        (n (trace-program-sub y2 y1 modulus)))
    (and
     (equal (trace-program-mul
             (trace-program-mul d d a b modulus)
             (trace-program-add x1 (trace-program-add x2 x3 modulus) modulus)
             a b modulus)
            (trace-program-mul n n a b modulus))
     (equal (trace-program-mul
             d (trace-program-add y1 y3 modulus) a b modulus)
            (trace-program-mul
             n (trace-program-sub x1 x3 modulus) a b modulus)))))

(defun trace-program-cross-opposite-p (x1 y1 x2 y2 modulus)
  (and (equal (trace-program-fix x1 modulus)
              (trace-program-fix x2 modulus))
       (equal (trace-program-add y1 y2 modulus)
              (trace-program-zero modulus))))

(defun trace-program-candidate-p (x y q trace a b modulus)
  (let* ((pi-x (trace-program-power x q a b modulus))
         (pi-y (trace-program-power y q a b modulus))
         (pi2-x (trace-program-power-iterate x q 2 a b modulus))
         (pi2-y (trace-program-power-iterate y q 2 a b modulus))
         (minus-y (trace-program-neg y modulus))
         (residue (mod (nfix trace) 3)))
    (if (equal residue 0)
        (trace-program-cross-opposite-p pi2-x pi2-y x minus-y modulus)
      (trace-program-cross-add-p
       pi2-x pi2-y x minus-y pi-x
       (if (equal residue 1) pi-y (trace-program-neg pi-y modulus))
       a b modulus))))

(defthm quotient-coordinate-trace-program-definition
  (equal
   (trace-program-candidate-p x y q trace a b modulus)
   (let* ((pi-x (trace-program-power x q a b modulus))
          (pi-y (trace-program-power y q a b modulus))
          (pi2-x (trace-program-power-iterate x q 2 a b modulus))
          (pi2-y (trace-program-power-iterate y q 2 a b modulus))
          (minus-y (trace-program-neg y modulus))
          (residue (mod (nfix trace) 3)))
     (if (equal residue 0)
         (trace-program-cross-opposite-p pi2-x pi2-y x minus-y modulus)
       (trace-program-cross-add-p
        pi2-x pi2-y x minus-y pi-x
        (if (equal residue 1) pi-y (trace-program-neg pi-y modulus))
        a b modulus))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable trace-program-candidate-p))))
