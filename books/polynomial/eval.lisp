(in-package "ACL2")
(include-book "base")
(include-book "kestrel/arithmetic-light/mod" :dir :system)

(defun poly-eval (poly x p)
  (if (endp poly) 0
    (pfield::add (car poly)
                 (pfield::mul x (poly-eval (cdr poly) x p) p) p)))

(defthm normalize-preserves-eval
  (equal (poly-eval (poly-normalize poly) x p)
         (poly-eval poly x p)))
