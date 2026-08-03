(in-package "GPOLY")

(include-book "derivative")
(include-book "pfield-instance")

; Concrete F7 execution spelling of the generic transparent definitions.  It
; is regression evidence only; the generic theorems are certified above.
(defun f7-field-nat-mul (n x)
   (declare (xargs :measure (nfix n)))
   (let ((n (nfix n)))
     (if (zp n)
         (gfield::f7-zero)
       (gfield::f7-add (gfield::f7-fix x)
                       (f7-field-nat-mul (1- n) x)))))

(defun f7-raw-derivative-aux (poly index)
   (declare (xargs :measure (acl2-count poly)))
   (if (atom poly)
       nil
     (cons (f7-field-nat-mul (nfix index) (car poly))
           (f7-raw-derivative-aux (cdr poly) (+ 1 (nfix index))))))

(defun f7-poly-derivative (poly)
   (f7-normalize
    (if (atom (f7-fix-coefficients poly))
        nil
      (f7-raw-derivative-aux (cdr (f7-fix-coefficients poly)) 1))))

(defthm derivative-product-rule-minimal-theory-client
  (equal
   (poly-derivative (poly-mul f g))
   (poly-add (poly-mul (poly-derivative f) g)
             (poly-mul f (poly-derivative g))))
  :hints (("Goal" :use poly-derivative-of-poly-mul
           :in-theory (theory 'minimal-theory))))

(defthm f7-poly-derivative-execution-regressions
  (and (equal (f7-poly-derivative nil) nil)
       (equal (f7-poly-derivative '(4)) nil)
       (equal (f7-poly-derivative '(4 3)) '(3))
       (equal (f7-poly-derivative '(1 2 3 4)) '(2 6 5))
       (equal (f7-poly-derivative
               (f7-poly-add '(1 2 3) '(4 5 6)))
              (f7-poly-add (f7-poly-derivative '(1 2 3))
                           (f7-poly-derivative '(4 5 6))))
       (equal (f7-poly-derivative (f7-poly-neg '(1 2 3)))
              (f7-poly-neg (f7-poly-derivative '(1 2 3))))
       ; Two nonconstant factors.
       (equal (f7-poly-derivative (f7-poly-mul '(1 2) '(3 4)))
              '(3 2))
       ; Zero and constant factors.
       (equal (f7-poly-derivative (f7-poly-mul '(1 2) nil)) nil)
       (equal (f7-poly-derivative (f7-poly-mul '(3) '(1 2 3)))
              '(6 4))
       ; A noncanonical input's trailing zero is discarded during the product.
       (equal (f7-poly-derivative (f7-poly-mul '(1 2 0) '(3 4)))
              '(3 2))
       ; The middle coefficient cancels in characteristic seven.
       (equal (f7-poly-derivative (f7-poly-mul '(1 1) '(1 6)))
              '(0 5))
       ; Direct execution of both sides of the product rule.
       (equal
        (f7-poly-derivative (f7-poly-mul '(1 2 3) '(4 5)))
        (f7-poly-add
         (f7-poly-mul (f7-poly-derivative '(1 2 3)) '(4 5))
         (f7-poly-mul '(1 2 3) (f7-poly-derivative '(4 5)))))
       ; x^7 has derivative 7*x^6 = 0 in characteristic seven.
       (equal (f7-poly-derivative '(0 0 0 0 0 0 0 1)) nil))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable f7-poly-derivative
                              f7-raw-derivative-aux
                              f7-field-nat-mul
                              f7-poly-add f7-raw-add
                              f7-poly-mul f7-raw-mul
                              f7-poly-scale f7-raw-scale
                              f7-poly-neg f7-raw-neg
                              f7-normalize f7-fix-coefficients
                              f7-trim-trailing-zeros
                              gfield::f7-add gfield::f7-neg
                              gfield::f7-fix gfield::f7-zero))))

(verify-guards f7-field-nat-mul)
(verify-guards f7-raw-derivative-aux)
(verify-guards f7-poly-derivative)
