(in-package "GPOLY")

(include-book "quotient-coordinate-trace-predicate")
(include-book "../polynomial/generic/f11-production-reduced-ring")

; Concrete specialization of the transparent production representation.  A
; coordinate is still the pair (u . v), denoting u+y*v; only polynomial
; reduction and coefficient arithmetic have been specialized to F11.
(defun f11-quotient-coordinate (u v modulus)
  (cons (f11-poly-remainder u modulus)
        (f11-poly-remainder v modulus)))

(defun f11-quotient-coordinate-u (coordinate)
  (if (consp coordinate) (car coordinate) nil))
(defun f11-quotient-coordinate-v (coordinate)
  (if (consp coordinate) (cdr coordinate) nil))

(defun f11-quotient-coordinate-fix (coordinate modulus)
  (f11-quotient-coordinate (f11-quotient-coordinate-u coordinate)
                           (f11-quotient-coordinate-v coordinate) modulus))
(defun f11-quotient-coordinate-zero (modulus)
  (f11-quotient-coordinate nil nil modulus))
(defun f11-quotient-coordinate-one (modulus)
  (f11-quotient-coordinate (f11-poly-reduced-one modulus) nil modulus))
(defun f11-quotient-coordinate-x (modulus)
  (f11-quotient-coordinate '(0 1) nil modulus))
(defun f11-quotient-coordinate-y (modulus)
  (f11-quotient-coordinate nil (f11-poly-reduced-one modulus) modulus))

(defun f11-quotient-coordinate-add (left right modulus)
  (let ((left (f11-quotient-coordinate-fix left modulus))
        (right (f11-quotient-coordinate-fix right modulus)))
    (f11-quotient-coordinate
     (f11-poly-reduced-add (f11-quotient-coordinate-u left)
                           (f11-quotient-coordinate-u right) modulus)
     (f11-poly-reduced-add (f11-quotient-coordinate-v left)
                           (f11-quotient-coordinate-v right) modulus)
     modulus)))
(defun f11-quotient-coordinate-neg (coordinate modulus)
  (let ((coordinate (f11-quotient-coordinate-fix coordinate modulus)))
    (f11-quotient-coordinate
     (f11-poly-reduced-neg (f11-quotient-coordinate-u coordinate) modulus)
     (f11-poly-reduced-neg (f11-quotient-coordinate-v coordinate) modulus)
     modulus)))
(defun f11-quotient-coordinate-sub (left right modulus)
  (f11-quotient-coordinate-add
   left (f11-quotient-coordinate-neg right modulus) modulus))
(defun f11-quotient-coordinate-curve-cubic (a b modulus)
  (f11-poly-remainder
   (list (gfield::f11-fix b) (gfield::f11-fix a) 0 1) modulus))
(defun f11-quotient-coordinate-mul (left right a b modulus)
  (let* ((left (f11-quotient-coordinate-fix left modulus))
         (right (f11-quotient-coordinate-fix right modulus))
         (u1 (f11-quotient-coordinate-u left))
         (v1 (f11-quotient-coordinate-v left))
         (u2 (f11-quotient-coordinate-u right))
         (v2 (f11-quotient-coordinate-v right))
         (cubic (f11-quotient-coordinate-curve-cubic a b modulus)))
    (f11-quotient-coordinate
     (f11-poly-reduced-add
      (f11-poly-reduced-mul u1 u2 modulus)
      (f11-poly-reduced-mul
       cubic (f11-poly-reduced-mul v1 v2 modulus) modulus)
      modulus)
     (f11-poly-reduced-add (f11-poly-reduced-mul u1 v2 modulus)
                           (f11-poly-reduced-mul v1 u2 modulus) modulus)
     modulus)))

(verify-guards f11-quotient-coordinate)
(verify-guards f11-quotient-coordinate-u)
(verify-guards f11-quotient-coordinate-v)
(verify-guards f11-quotient-coordinate-fix)
(verify-guards f11-quotient-coordinate-zero)
(verify-guards f11-quotient-coordinate-one)
(verify-guards f11-quotient-coordinate-x)
(verify-guards f11-quotient-coordinate-y)
(verify-guards f11-quotient-coordinate-add)
(verify-guards f11-quotient-coordinate-neg)
(verify-guards f11-quotient-coordinate-sub)
(verify-guards f11-quotient-coordinate-curve-cubic)
(verify-guards f11-quotient-coordinate-mul)

(defun f11-quotient-coordinate-pow-spec (base n a b modulus)
  (declare (xargs :guard (natp n)))
  (if (zp n) (f11-quotient-coordinate-one modulus)
    (f11-quotient-coordinate-mul
     base (f11-quotient-coordinate-pow-spec base (1- n) a b modulus)
     a b modulus)))
(defun f11-quotient-coordinate-pow (base n a b modulus)
  (f11-quotient-coordinate-pow-spec
   (f11-quotient-coordinate-fix base modulus) (nfix n) a b modulus))
(defun f11-quotient-coordinate-cardinality-power (coordinate q a b modulus)
  (f11-quotient-coordinate-pow coordinate q a b modulus))
(defun f11-quotient-coordinate-cardinality-power-iterate
  (coordinate q iterations a b modulus)
  (f11-quotient-coordinate-pow
   coordinate (expt (nfix q) (nfix iterations)) a b modulus))

(defun f11-quotient-coordinate-cross-add-p
  (x1 y1 x2 y2 x3 y3 a b modulus)
  (let ((d (f11-quotient-coordinate-sub x2 x1 modulus))
        (n (f11-quotient-coordinate-sub y2 y1 modulus)))
    (and
     (equal (f11-quotient-coordinate-mul
             (f11-quotient-coordinate-mul d d a b modulus)
             (f11-quotient-coordinate-add
              x1 (f11-quotient-coordinate-add x2 x3 modulus) modulus)
             a b modulus)
            (f11-quotient-coordinate-mul n n a b modulus))
     (equal (f11-quotient-coordinate-mul
             d (f11-quotient-coordinate-add y1 y3 modulus) a b modulus)
            (f11-quotient-coordinate-mul
             n (f11-quotient-coordinate-sub x1 x3 modulus) a b modulus)))))
(defun f11-quotient-coordinate-cross-opposite-p (x1 y1 x2 y2 modulus)
  (and (equal (f11-quotient-coordinate-fix x1 modulus)
              (f11-quotient-coordinate-fix x2 modulus))
       (equal (f11-quotient-coordinate-add y1 y2 modulus)
              (f11-quotient-coordinate-zero modulus))))
(defun f11-quotient-coordinate-trace-candidate-p
  (x y q trace a b modulus)
  (let* ((pi-x (f11-quotient-coordinate-cardinality-power x q a b modulus))
         (pi-y (f11-quotient-coordinate-cardinality-power y q a b modulus))
         (pi2-x (f11-quotient-coordinate-cardinality-power-iterate
                 x q 2 a b modulus))
         (pi2-y (f11-quotient-coordinate-cardinality-power-iterate
                 y q 2 a b modulus))
         (minus-y (f11-quotient-coordinate-neg y modulus))
         (residue (mod (nfix trace) 3)))
    (if (equal residue 0)
        (f11-quotient-coordinate-cross-opposite-p
         pi2-x pi2-y x minus-y modulus)
      (f11-quotient-coordinate-cross-add-p
       pi2-x pi2-y x minus-y pi-x
       (if (equal residue 1) pi-y
         (f11-quotient-coordinate-neg pi-y modulus)) a b modulus))))

; This single transparent expansion theorem is the structural correspondence
; boundary.  It applies to arbitrary (including malformed) ACL2 inputs and
; moduli; no canonicality, nonzero-modulus, field, or domain hypothesis is
; hidden in the specialization.
(defthm f11-quotient-coordinate-trace-candidate-production-specialization
  (equal (f11-quotient-coordinate-trace-candidate-p x y q trace a b modulus)
         (let* ((pi-x (f11-quotient-coordinate-pow x q a b modulus))
                (pi-y (f11-quotient-coordinate-pow y q a b modulus))
                (pi2-x (f11-quotient-coordinate-pow
                        x (expt (nfix q) 2) a b modulus))
                (pi2-y (f11-quotient-coordinate-pow
                        y (expt (nfix q) 2) a b modulus))
                (minus-y (f11-quotient-coordinate-neg y modulus))
                (residue (mod (nfix trace) 3)))
           (if (equal residue 0)
               (f11-quotient-coordinate-cross-opposite-p
                pi2-x pi2-y x minus-y modulus)
             (f11-quotient-coordinate-cross-add-p
              pi2-x pi2-y x minus-y pi-x
              (if (equal residue 1) pi-y
                (f11-quotient-coordinate-neg pi-y modulus))
              a b modulus))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (f11-quotient-coordinate-trace-candidate-p
                 f11-quotient-coordinate-cardinality-power
                 f11-quotient-coordinate-cardinality-power-iterate)
                (f11-quotient-coordinate-pow expt)))))

(verify-guards f11-quotient-coordinate-pow-spec)
(verify-guards f11-quotient-coordinate-pow)
(verify-guards f11-quotient-coordinate-cardinality-power)
(verify-guards f11-quotient-coordinate-cardinality-power-iterate)
(verify-guards f11-quotient-coordinate-cross-add-p)
(verify-guards f11-quotient-coordinate-cross-opposite-p)
(verify-guards f11-quotient-coordinate-trace-candidate-p)

(in-theory (disable f11-quotient-coordinate-pow-spec))
