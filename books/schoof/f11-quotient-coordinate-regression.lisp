(in-package "GPOLY")

(include-book "f11-quotient-coordinate")

; Compatibility names for the older execution witness are now transparent
; wrappers around the certified production specialization, not duplicated
; rank-two formulas.
(defun f11-quotient-fix (coordinate modulus)
  (f11-quotient-coordinate-fix coordinate modulus))

(defun f11-quotient-add (left right modulus)
  (f11-quotient-coordinate-add left right modulus))

(defun f11-quotient-mul (left right a b modulus)
  (f11-quotient-coordinate-mul left right a b modulus))

(defun f11-quotient-regression-modulus ()
  (f11-division-polynomial 3 1 6))

(defun f11-quotient-regression-y ()
  (f11-quotient-fix (cons nil '(1)) (f11-quotient-regression-modulus)))

(assert-event
 (equal (f11-quotient-regression-modulus)
        (f11-division-polynomial-base 3 1 6)))

(assert-event
 (let* ((modulus (f11-quotient-regression-modulus))
        (fixed (f11-quotient-fix (cons '(1 2 3 4 5) '(6 7 8 9 10)) modulus)))
   (and (< (f11-poly-degree (car fixed)) (f11-poly-degree modulus))
        (< (f11-poly-degree (cdr fixed)) (f11-poly-degree modulus)))))

(assert-event
 (let* ((modulus (f11-quotient-regression-modulus))
        (left (cons '(1 0 2 0 3) '(4 1)))
        (right (cons '(2 1) '(3 0 1)))
        (sum (f11-quotient-add left right modulus))
        (product (f11-quotient-mul left right 1 6 modulus)))
   (and (consp (car sum)) (consp (cdr sum))
        (< (f11-poly-degree (car product)) (f11-poly-degree modulus))
        (< (f11-poly-degree (cdr product)) (f11-poly-degree modulus)))))

(assert-event
 (let* ((modulus (f11-quotient-regression-modulus))
        (square (f11-quotient-mul (f11-quotient-regression-y)
                                  (f11-quotient-regression-y)
                                  1 6 modulus)))
   (equal square (f11-quotient-fix (cons '(6 1 0 1) nil) modulus))))

(assert-event
 (equal (f11-quotient-fix 'malformed (f11-quotient-regression-modulus))
        (cons nil nil)))

(verify-guards f11-quotient-fix)
(verify-guards f11-quotient-add)
(verify-guards f11-quotient-mul)
(verify-guards f11-quotient-regression-modulus)
(verify-guards f11-quotient-regression-y)

(defthm f11-quotient-coordinate-eval-malformed-client
  (and (equal (f11-quotient-coordinate-eval
               'malformed coordinate a b modulus)
              (f11-quotient-coordinate-zero modulus))
       (equal (f11-quotient-coordinate-embed 'malformed modulus)
              (f11-quotient-coordinate-zero modulus)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance f11-quotient-coordinate-embed-of-normalize
                            (polynomial 'malformed)))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(f11-quotient-coordinate-eval f11-normalize
              f11-fix-coefficients f11-trim-trailing-zeros
              f11-quotient-coordinate-embed-zero)))))
