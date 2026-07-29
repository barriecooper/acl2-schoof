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

; These three proof-local algebraic bridges put the kernel's left-oriented
; cancellation interface into exactly the shapes used by the relation
; equations.  They add no field assumptions or public field API.
(local
 (defthm field-mul-right-cancel-forward-local
   (implies
    (and (not (equal (field-fix denominator) (field-zero)))
         (equal (field-mul left denominator)
                (field-mul right denominator)))
    (equal (field-fix left) (field-fix right)))
   :hints
   (("Goal"
     :use ((:instance field-mul-left-cancel-forward
                      (x denominator) (y left) (z right))
           (:instance field-mul-commutative
                      (x left) (y denominator))
           (:instance field-mul-commutative
                      (x right) (y denominator)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm field-add-right-cancel-forward-local
   (implies
    (equal (field-add left common) (field-add right common))
    (equal (field-fix left) (field-fix right)))
   :hints
   (("Goal"
     :use ((:instance field-add-left-cancel-forward
                      (x common) (y left) (z right))
           (:instance field-add-commutative (x left) (y common))
           (:instance field-add-commutative (x right) (y common)))
     :in-theory (theory 'minimal-theory)))))

(local
 (defthm distinct-fixed-values-imply-nonzero-difference-local
   (implies
    (not (equal (field-fix first) (field-fix second)))
    (not (equal (field-sub second first) (field-zero))))
   :hints
   (("Goal"
     :use ((:instance field-sub-equal-zero-implies-fixed-equal
                      (first second) (second first)))
     :in-theory (theory 'minimal-theory)))))

(defthm affine-distinct-x-secant-relation-slope-unique
  (implies
   (and (affine-distinct-x-secant-relation-p
         first second slope-a output-a)
        (affine-distinct-x-secant-relation-p
         first second slope-b output-b))
   (equal (field-fix slope-a) (field-fix slope-b)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance distinct-fixed-values-imply-nonzero-difference-local
                (first (affine-coordinates-x first))
                (second (affine-coordinates-x second)))
     (:instance field-mul-right-cancel-forward-local
                (left (field-fix slope-a))
                (right (field-fix slope-b))
                (denominator
                 (field-sub (affine-coordinates-x second)
                            (affine-coordinates-x first)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-sub
       field-fix-of-add
       field-fix-of-neg
       field-fix-idempotent)))))

(defthm affine-distinct-x-secant-relation-output-unique-at-fixed-slope
  (implies
   (and (affine-distinct-x-secant-relation-p
         first second slope-a output-a)
        (affine-distinct-x-secant-relation-p
         first second slope-b output-b)
        (equal (field-fix slope-a) (field-fix slope-b)))
   (equal (affine-coordinates-fix output-a)
          (affine-coordinates-fix output-b)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance field-add-right-cancel-forward-local
                (left
                 (field-add (affine-coordinates-x output-a)
                            (affine-coordinates-x first)))
                (right
                 (field-add (affine-coordinates-x output-b)
                            (affine-coordinates-x first)))
                (common (affine-coordinates-x second)))
     (:instance field-add-right-cancel-forward-local
                (left (affine-coordinates-x output-a))
                (right (affine-coordinates-x output-b))
                (common (affine-coordinates-x first)))
     (:instance field-add-right-cancel-forward-local
                (left (affine-coordinates-y output-a))
                (right (affine-coordinates-y output-b))
                (common (affine-coordinates-y first))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-distinct-x-secant-relation-p
       affine-coordinates-fix
       affine-coordinates-make
       field-fix-when-field-element-p
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-fix-of-add
       field-fix-idempotent
       field-mul-fixed-congruence
       field-sub
       field-neg-of-fix)))))

(defthm affine-distinct-x-secant-relation-unique
  (implies
   (and (affine-distinct-x-secant-relation-p
         first second slope-a output-a)
        (affine-distinct-x-secant-relation-p
         first second slope-b output-b))
   (and (equal (field-fix slope-a) (field-fix slope-b))
        (equal (affine-coordinates-fix output-a)
               (affine-coordinates-fix output-b))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    (affine-distinct-x-secant-relation-slope-unique
     affine-distinct-x-secant-relation-output-unique-at-fixed-slope)
    :in-theory (theory 'minimal-theory))))

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
