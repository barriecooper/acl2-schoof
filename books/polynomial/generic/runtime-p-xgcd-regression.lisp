(in-package "GPOLY")
(include-book "runtime-p-xgcd")
(defun runtime-p-xgcd-regression-result (first second p)
  (declare (xargs :guard t))
  (mv-let (g s coefficient-t)
    (runtime-p-extended-euclidean-gcd first second p)
    (list g s coefficient-t)))

(assert-event
 (equal (runtime-p-xgcd-regression-result '(1 0 1) '(0 1) 7)
        '((1) (1) (0 6))))
(assert-event
 (let* ((first '(1 0 1))
        (second '(0 1))
        (result (runtime-p-xgcd-regression-result first second 7)))
   (equal (runtime-p-poly-add
           (runtime-p-poly-mul (cadr result) first 7)
           (runtime-p-poly-mul (caddr result) second 7) 7)
          (car result))))
(assert-event
 (equal (runtime-p-xgcd-regression-result nil '(0 1) 7)
        '((0 1) nil (1))))
(assert-event
 (equal (runtime-p-xgcd-regression-result '(1 0) nil 7)
        '((1) (1) nil)))
(assert-event
 (equal (runtime-p-xgcd-regression-result
         (cons 1 'bad-tail) (cons 1 'bad-tail) 7)
        '((1) nil (1))))
(assert-event
 (equal (runtime-p-xgcd-regression-result '(1 0 1) '(0 1) 'bad)
        (runtime-p-xgcd-regression-result '(1 0 1) '(0 1) 2)))
; Modulo 8, 1 passes the explicit check and allows an active step.
(assert-event
 (runtime-p-poly-divisor-admissible-p '(0 1) 8))
; Modulo 8, 2 fails the exponentiation-based explicit inverse check, so the
; total chain returns its inactive triple without claiming ring-theoretic GCD.
(assert-event
 (and (not (runtime-p-poly-divisor-admissible-p '(0 2) 8))
      (equal (runtime-p-xgcd-regression-result '(1 0 1) '(0 2) 8)
             '((1 0 1) (1) nil))))

(defthm runtime-p-xgcd-minimal-bezout-client
  (equal
   (runtime-p-poly-add
    (runtime-p-poly-mul
     (mv-nth 1 (runtime-p-extended-euclidean-gcd first second p)) first p)
    (runtime-p-poly-mul
     (mv-nth 2 (runtime-p-extended-euclidean-gcd first second p)) second p) p)
   (runtime-p-euclidean-gcd first second p))
  :hints (("Goal"
           :use ((:instance runtime-p-extended-euclidean-gcd-bezout))
           :in-theory (theory 'minimal-theory))))
