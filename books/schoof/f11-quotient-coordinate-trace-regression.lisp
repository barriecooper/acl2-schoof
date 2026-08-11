(in-package "GPOLY")

(include-book "f11-quotient-coordinate")

(defun f11-psi3-modulus ()
  (f11-division-polynomial 3 1 6))
(defun f11-psi3-x ()
  (f11-quotient-coordinate-x (f11-psi3-modulus)))
(defun f11-psi3-y ()
  (f11-quotient-coordinate-y (f11-psi3-modulus)))
(defun f11-psi3-pi-x ()
  (f11-quotient-coordinate-cardinality-power
   (f11-psi3-x) 11 1 6 (f11-psi3-modulus)))
(defun f11-psi3-pi-y ()
  (f11-quotient-coordinate-cardinality-power
   (f11-psi3-y) 11 1 6 (f11-psi3-modulus)))
(defun f11-psi3-pi2-x ()
  (f11-quotient-coordinate-cardinality-power-iterate
   (f11-psi3-x) 11 2 1 6 (f11-psi3-modulus)))
(defun f11-psi3-pi2-y ()
  (f11-quotient-coordinate-cardinality-power-iterate
   (f11-psi3-y) 11 2 1 6 (f11-psi3-modulus)))
(defun f11-psi3-trace-candidate-p (trace)
  (f11-quotient-coordinate-trace-candidate-p
   (f11-psi3-x) (f11-psi3-y) 11 trace 1 6 (f11-psi3-modulus)))

(verify-guards f11-psi3-modulus)
(verify-guards f11-psi3-x)
(verify-guards f11-psi3-y)
(verify-guards f11-psi3-pi-x)
(verify-guards f11-psi3-pi-y)
(verify-guards f11-psi3-pi2-x)
(verify-guards f11-psi3-pi2-y)
(verify-guards f11-psi3-trace-candidate-p)

(defthm f11-psi3-production-values
  (and (equal (f11-psi3-modulus) '(10 6 6 0 3))
       (equal (list (f11-psi3-x) (f11-psi3-y))
              '(((0 1)) (nil 1)))
       (equal (list (f11-psi3-pi-x) (f11-psi3-pi-y))
              '(((5 0 9 1)) (nil 1 6 7 3)))
       (equal (list (f11-psi3-pi2-x) (f11-psi3-pi2-y))
              '(((3 7 7 1)) (nil 4 4 4 10)))))

(defthm f11-psi3-trace-residue-zero-rejected
  (not (f11-psi3-trace-candidate-p 0)))
(defthm f11-psi3-trace-residue-one-rejected
  (not (f11-psi3-trace-candidate-p 1)))
(defthm f11-psi3-trace-residue-two-accepted
  (f11-psi3-trace-candidate-p 2))

; Exact nondegeneracy evidence for the accepted branch.  D and N are both
; nonzero.  Its x cross-products equal the first displayed nonzero value and
; its y cross-products equal the second, so acceptance is not 0=0 vacuity.
(defthm f11-psi3-trace-cross-product-values
  (let* ((m (f11-psi3-modulus))
         (x (f11-psi3-x)) (y (f11-psi3-y))
         (px (f11-psi3-pi-x)) (py (f11-psi3-pi-y))
         (p2x (f11-psi3-pi2-x)) (p2y (f11-psi3-pi2-y))
         (minus-y (f11-quotient-coordinate-neg y m))
         (d (f11-quotient-coordinate-sub x p2x m))
         (n (f11-quotient-coordinate-sub minus-y p2y m))
         (d2 (f11-quotient-coordinate-mul d d 1 6 m))
         (x-sum (f11-quotient-coordinate-add
                 p2x (f11-quotient-coordinate-add x px m) m)))
    (and (equal d '((8 5 4 10)))
         (equal n '(nil 6 7 7 1))
         (equal (f11-quotient-coordinate-mul d2 x-sum 1 6 m)
                '((2 9 3 8)))
         (equal (f11-quotient-coordinate-mul n n 1 6 m)
                '((2 9 3 8)))
         (equal (f11-quotient-coordinate-mul
                 d (f11-quotient-coordinate-add
                    p2y (f11-quotient-coordinate-neg py m) m) 1 6 m)
                '(nil 4 1 8 4))
         (equal (f11-quotient-coordinate-mul
                 n (f11-quotient-coordinate-sub p2x px m) 1 6 m)
                '(nil 4 1 8 4)))))
