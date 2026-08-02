(in-package "GFIELD")

; A carrier-based abelian group in an explicit ambient context.  The context
; is nullary so that a concrete functional instance may retain a global
; parameter hypothesis (for example, a field-characteristic restriction)
; instead of turning a conditional group law into an unconditional axiom.
(encapsulate
 (((abelian-group-context-p) => *)
  ((abelian-group-element-p *) => *)
  ((abelian-group-op * *) => *)
  ((abelian-group-identity) => *)
  ((abelian-group-inverse *) => *))

 (local (defun abelian-group-context-p () t))
 (local (defun abelian-group-element-p (x) (booleanp x)))
 (local (defun abelian-group-op (x y) (if x (not y) y)))
 (local (defun abelian-group-identity () nil))
 (local (defun abelian-group-inverse (x) (if x t nil)))

 (defthm abelian-group-identity-in-carrier
   (implies (abelian-group-context-p)
            (abelian-group-element-p (abelian-group-identity))))

 (defthm abelian-group-operation-closure
   (implies (and (abelian-group-context-p)
                 (abelian-group-element-p x)
                 (abelian-group-element-p y))
            (abelian-group-element-p (abelian-group-op x y))))

 (defthm abelian-group-inverse-closure
   (implies (and (abelian-group-context-p)
                 (abelian-group-element-p x))
            (abelian-group-element-p (abelian-group-inverse x))))

 (defthm abelian-group-associativity
   (implies (and (abelian-group-context-p)
                 (abelian-group-element-p x)
                 (abelian-group-element-p y)
                 (abelian-group-element-p z))
            (equal (abelian-group-op (abelian-group-op x y) z)
                   (abelian-group-op x (abelian-group-op y z)))))

 (defthm abelian-group-left-identity
   (implies (and (abelian-group-context-p)
                 (abelian-group-element-p x))
            (equal (abelian-group-op (abelian-group-identity) x) x)))

 (defthm abelian-group-left-inverse
   (implies (and (abelian-group-context-p)
                 (abelian-group-element-p x))
            (equal (abelian-group-op (abelian-group-inverse x) x)
                   (abelian-group-identity))))

 (defthm abelian-group-commutativity
   (implies (and (abelian-group-context-p)
                 (abelian-group-element-p x)
                 (abelian-group-element-p y))
            (equal (abelian-group-op x y)
                   (abelian-group-op y x)))))

; A deliberately small foundational consequence.  Its curve specialization
; is the focused check that clients can consume the abstraction rather than a
; curve-specific group-law theorem.
(defthm abelian-group-inverse-of-identity
  (implies (abelian-group-context-p)
           (equal (abelian-group-inverse (abelian-group-identity))
                  (abelian-group-identity)))
  :hints
  (("Goal"
    :use
    ((:instance abelian-group-left-inverse
                (x (abelian-group-identity)))
     (:instance abelian-group-left-identity
                (x (abelian-group-inverse (abelian-group-identity))))
     (:instance abelian-group-commutativity
                (x (abelian-group-inverse (abelian-group-identity)))
                (y (abelian-group-identity)))
     abelian-group-identity-in-carrier
     (:instance abelian-group-inverse-closure
                (x (abelian-group-identity)))))))
