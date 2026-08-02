(in-package "GFIELD")

(include-book "abelian-group")

(defun boolean-group-context-p () t)
(defun boolean-group-element-p (x) (booleanp x))
(defun boolean-group-op (x y) (if x (not y) y))
(defun boolean-group-identity () nil)
(defun boolean-group-inverse (x) (if x t nil))

(defthm boolean-group-inverse-of-identity-from-generic
  (implies (boolean-group-context-p)
           (equal (boolean-group-inverse (boolean-group-identity))
                  (boolean-group-identity)))
  :hints
  (("Goal"
    :by
    (:functional-instance
     abelian-group-inverse-of-identity
     (abelian-group-context-p boolean-group-context-p)
     (abelian-group-element-p boolean-group-element-p)
     (abelian-group-op boolean-group-op)
     (abelian-group-identity boolean-group-identity)
     (abelian-group-inverse boolean-group-inverse)))))
