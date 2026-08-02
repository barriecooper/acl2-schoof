(in-package "GFIELD")

(include-book "curve-point-pair-output-point-associativity")
(include-book "curve-point-addition-inverse")
(include-book "../algebra/abelian-group")
(include-book "tools/def-functional-instance" :dir :system)

; Public functional-instance endpoint.  The nullary abstract context maps to
; the maintained characteristic predicate, so every generated consequence
; retains that premise.  The seven functional-instantiation obligations are
; discharged only by the public executable group laws and infinity closure.
(defmacro def-curve-point-abelian-group-theorem (name generic-theorem)
  `(acl2::def-functional-instance
     ,name ,generic-theorem
     ((abelian-group-context-p short-weierstrass-characteristic-p)
      (abelian-group-element-p short-weierstrass-curve-point-p)
      (abelian-group-op curve-point-pair-output-point)
      (abelian-group-identity curve-point-infinity)
      (abelian-group-inverse curve-point-neg))
     :rule-classes nil
     :hints
     (("Goal"
       :in-theory (theory 'minimal-theory))
      (and stable-under-simplificationp
           '(:use
             (short-weierstrass-curve-point-p-of-infinity
              (:instance
               short-weierstrass-curve-point-p-of-curve-point-pair-output-point
               (first x) (second y))
              (:instance short-weierstrass-curve-point-p-of-neg (point x))
              (:instance curve-point-pair-output-point-identity-left
                         (point x))
              (:instance curve-point-pair-output-point-associative
                         (a x) (b y) (c z))
              (:instance curve-point-pair-output-point-commutative
                         (first x) (second y))
              (:instance curve-point-pair-output-point-with-negate-left
                         (point x)))
             :in-theory (theory 'minimal-theory))))
     :by-hint-p t))

(def-curve-point-abelian-group-theorem
  curve-point-abelian-group-inverse-of-identity
  abelian-group-inverse-of-identity)
