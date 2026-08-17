(in-package "GPOLY")

(include-book "runtime-p-coefficient-inverse")
(include-book "runtime-p-active-monic-subtraction")

; Retained, unregistered experimental implementation.  The executable boundary
; is complete, but registration awaits the nonmonic product-leading-term proof.
(defun runtime-p-division-step-core (remainder divisor p)
  (declare (xargs :guard t))
  (if (and (consp remainder)
           (consp divisor)
           (equal (runtime-p-mul
                   (runtime-p-poly-leading-coefficient divisor p)
                   (runtime-p-inv
                    (runtime-p-poly-leading-coefficient divisor p) p) p)
                  (runtime-p-one p))
           (<= (runtime-p-poly-degree divisor p)
               (runtime-p-poly-degree remainder p)))
      (let* ((coefficient
              (runtime-p-mul
               (runtime-p-poly-leading-coefficient remainder p)
               (runtime-p-inv
                (runtime-p-poly-leading-coefficient divisor p) p) p))
             (term (runtime-p-poly-monomial
                    coefficient
                    (- (runtime-p-poly-degree remainder p)
                       (runtime-p-poly-degree divisor p)) p))
             (product (runtime-p-poly-mul term divisor p)))
        (cons term (runtime-p-poly-sub remainder product p)))
    (cons nil remainder)))

(defun runtime-p-division-step (remainder divisor p)
  (declare (xargs :guard t))
  (runtime-p-division-step-core (runtime-p-normalize remainder p)
                                (runtime-p-normalize divisor p) p))

(defun runtime-p-division-step-term (remainder divisor p)
  (declare (xargs :guard t))
  (car (runtime-p-division-step remainder divisor p)))

(defun runtime-p-division-step-next (remainder divisor p)
  (declare (xargs :guard t))
  (cdr (runtime-p-division-step remainder divisor p)))

(verify-guards runtime-p-division-step-core)
(verify-guards runtime-p-division-step)
(verify-guards runtime-p-division-step-term)
(verify-guards runtime-p-division-step-next)

(defthm runtime-p-division-step-of-normalize
  (equal (runtime-p-division-step (runtime-p-normalize remainder p)
                                  (runtime-p-normalize divisor p) p)
         (runtime-p-division-step remainder divisor p)))

(defthm runtime-p-division-step-projection-equations
  (and (equal (runtime-p-division-step-term remainder divisor p)
              (car (runtime-p-division-step remainder divisor p)))
       (equal (runtime-p-division-step-next remainder divisor p)
              (cdr (runtime-p-division-step remainder divisor p))))
  :rule-classes nil)

; Nonmonic unit-leading execution and safe composite nonunit inactivity.
(assert-event
 (equal (runtime-p-division-step '(1 4 3) '(2 3) 7)
        '((0 1) 1 2)))
(assert-event
 (equal (runtime-p-division-step '(1 4 3) '(1 2) 6)
        '(nil 1 4 3)))
(assert-event
 (equal (runtime-p-division-step '(1 4 3 0 . bad) '(2 3 0 . bad) 7)
        '((0 1) 1 2)))
(assert-event
 (equal (runtime-p-division-step '(1 1) '(1 1) 'bad)
        '((1))))
