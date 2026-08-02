(in-package "GFIELD")

(include-book "curve-point-abelian-group")
(include-book "../algebra/abelian-group-natural-scalar")
(include-book "tools/def-functional-instance" :dir :system)

; Transparent linear reference implementation, with the same NFIX semantics
; and left-addition orientation as ABELIAN-GROUP-NAT-MUL.
(defun curve-point-nat-mul (n point)
  (declare (xargs :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n)
        (curve-point-infinity)
      (curve-point-pair-output-point
       point (curve-point-nat-mul (1- n) point)))))

(defthm curve-point-nat-mul-of-nfix
  (equal (curve-point-nat-mul (nfix n) point)
         (curve-point-nat-mul n point))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(curve-point-nat-mul nfix)))))

(defthm curve-point-nat-mul-zero
  (equal (curve-point-nat-mul 0 point) (curve-point-infinity))
  :hints (("Goal" :in-theory (enable curve-point-nat-mul))))

(defthm curve-point-nat-mul-successor
  (implies (natp n)
           (equal (curve-point-nat-mul (+ 1 n) point)
                  (curve-point-pair-output-point
                   point (curve-point-nat-mul n point))))
  :hints (("Goal" :in-theory
           (set-difference-theories
            (union-theories (theory 'minimal-theory)
                            '(nfix natp zp acl2::fold-consts-in-+ unicity-of-0 fix))
            '(curve-point-nat-mul-of-nfix))
           :expand ((curve-point-nat-mul (+ 1 n) point))
           :do-not-induct t)))

(defthm curve-point-fix-of-nat-mul
  (equal (curve-point-fix (curve-point-nat-mul n point))
         (curve-point-nat-mul n point))
  :hints (("Goal" :induct (curve-point-nat-mul n point)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(curve-point-nat-mul
                         curve-point-fix-of-infinity
                         curve-point-fix-of-curve-point-pair-output-point)))))

(defthm curve-point-pair-output-point-of-fix-left
  (equal (curve-point-pair-output-point (curve-point-fix first) second)
         (curve-point-pair-output-point first second))
  :hints (("Goal"
           :use ((:instance curve-point-pair-output-point-of-fixes
                            (first (curve-point-fix first)))
                 (:instance curve-point-pair-output-point-of-fixes
                            (first first)))
           :in-theory (enable curve-point-fix-idempotent))))

(defthm curve-point-nat-mul-of-fix
  (equal (curve-point-nat-mul n (curve-point-fix point))
         (curve-point-nat-mul n point))
  :hints (("Goal" :induct (curve-point-nat-mul n point)
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(curve-point-nat-mul
                         curve-point-pair-output-point-of-fix-left)))))

(defcong equal equal (curve-point-nat-mul n point) 2)

(defmacro def-curve-point-natural-scalar-theorem (name generic-theorem)
  `(acl2::def-functional-instance
     ,name ,generic-theorem
     ((abelian-group-context-p short-weierstrass-characteristic-p)
      (abelian-group-element-p short-weierstrass-curve-point-p)
      (abelian-group-op curve-point-pair-output-point)
      (abelian-group-identity curve-point-infinity)
      (abelian-group-inverse curve-point-neg)
      (abelian-group-nat-mul curve-point-nat-mul))
     :rule-classes nil
     :hints
     (("Goal" :in-theory (theory 'minimal-theory))
      (and stable-under-simplificationp
           '(:use
             (short-weierstrass-curve-point-p-of-infinity
              (:instance
               short-weierstrass-curve-point-p-of-curve-point-pair-output-point
               (first x) (second y))
              (:instance short-weierstrass-curve-point-p-of-neg (point x))
              (:instance curve-point-pair-output-point-identity-left (point x))
              (:instance curve-point-pair-output-point-associative
                         (a x) (b y) (c z))
              (:instance curve-point-pair-output-point-commutative
                         (first x) (second y))
              (:instance curve-point-pair-output-point-with-negate-left
                         (point x)))
             :in-theory (union-theories
                         (theory 'minimal-theory)
                         '(abelian-group-nat-mul
                           curve-point-nat-mul)))))
     :by-hint-p t))

(def-curve-point-natural-scalar-theorem
  short-weierstrass-curve-point-p-of-curve-point-nat-mul
  abelian-group-element-p-of-nat-mul)

(def-curve-point-natural-scalar-theorem
  curve-point-nat-mul-one
  abelian-group-nat-mul-one)

(def-curve-point-natural-scalar-theorem
  curve-point-nat-mul-of-sum
  abelian-group-nat-mul-of-sum)

(def-curve-point-natural-scalar-theorem
  curve-point-nat-mul-distributes-over-addition
  abelian-group-nat-mul-distributes-over-op)

(verify-guards curve-point-nat-mul)
