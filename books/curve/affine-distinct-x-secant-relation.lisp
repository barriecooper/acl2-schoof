(in-package "GFIELD")

(include-book "affine-distinct-x-closure")

; A classifier-free, division-free mathematical specification of the
; distinct-x secant case.  SLOPE is an explicit witness; OUTPUT is an affine
; coordinate value rather than a tagged full point.  Accessors and FIELD-FIX
; give arbitrary ACL2 objects the established total fixing semantics, while
; the three curve-membership conjuncts and distinct-x conjunct keep the
; geometric domain explicit.
(defun affine-distinct-x-secant-relation-p (first second slope output)
  (and
   (short-weierstrass-affine-point-p first)
   (short-weierstrass-affine-point-p second)
   (not (equal (affine-coordinates-x first)
               (affine-coordinates-x second)))
   (equal
    (field-mul
     (field-fix slope)
     (field-sub (affine-coordinates-x second)
                (affine-coordinates-x first)))
    (field-sub (affine-coordinates-y second)
               (affine-coordinates-y first)))
   (equal
    (field-add
     (field-add (affine-coordinates-x output)
                (affine-coordinates-x first))
     (affine-coordinates-x second))
    (field-mul (field-fix slope) (field-fix slope)))
   (equal
    (field-add (affine-coordinates-y output)
               (affine-coordinates-y first))
    (field-mul
     (field-fix slope)
     (field-sub (affine-coordinates-x first)
                (affine-coordinates-x output))))
   (short-weierstrass-affine-point-p output)))

(defthm affine-distinct-x-secant-relation-p-of-fixes
  (equal
   (affine-distinct-x-secant-relation-p
    (affine-coordinates-fix first)
    (affine-coordinates-fix second)
    (field-fix slope)
    (affine-coordinates-fix output))
   (affine-distinct-x-secant-relation-p first second slope output))
  :hints
  (("Goal"
    :use
    ((:instance short-weierstrass-affine-point-p-of-fix
                (coordinates first))
     (:instance short-weierstrass-affine-point-p-of-fix
                (coordinates second))
     (:instance short-weierstrass-affine-point-p-of-fix
                (coordinates output)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-coordinates-x-of-fix
       affine-coordinates-y-of-fix
       field-fix-idempotent)))))

; This bridge is proof-local: the executable reconstruction and closure
; theorems predate the semantic relation and select their branch through the
; structural classifier.  The public soundness statement below remains purely
; mathematical.
(local
 (defthm distinct-affine-x-implies-distinct-x-classification
   (implies
    (not (equal (affine-coordinates-x first)
                (affine-coordinates-x second)))
    (equal (affine-pair-classify first second) :distinct-x))
   :rule-classes nil
   :hints
   (("Goal"
     :use (affine-pair-classify-distinct-x-characterization)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-coordinates-x-of-fix))))))

(defthm affine-distinct-x-output-satisfies-secant-relation
  (implies
   (and (short-weierstrass-affine-point-p first)
        (short-weierstrass-affine-point-p second)
        (not (equal (affine-coordinates-x first)
                    (affine-coordinates-x second))))
   (affine-distinct-x-secant-relation-p
    first
    second
    (affine-distinct-x-slope first second)
    (affine-distinct-x-output first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (distinct-affine-x-implies-distinct-x-classification
     affine-distinct-x-slope-reconstructs-y-difference
     affine-distinct-x-output-x-rearrangement
     affine-distinct-x-output-y-rearrangement
     short-weierstrass-affine-point-p-of-affine-distinct-x-output)
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       field-fix-of-affine-distinct-x-slope
       affine-coordinates-x-of-affine-distinct-x-output
       affine-coordinates-y-of-affine-distinct-x-output)))))

(verify-guards affine-distinct-x-secant-relation-p)
