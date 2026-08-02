(in-package "GFIELD")

(include-book "xcert-semantics")
(include-book "affine-distinct-x-secant-relation")

; Package the canonical all-distinct-x certificate for four arbitrary semantic
; secant witnesses.  All alignment below is by relation determinacy modulo
; fixing; the only equality between the two association trees is X-CERT's
; certified canonical-output equality.
(local
 (defthm secant-relation-consequences-local
   (implies
    (affine-distinct-x-secant-relation-p first second slope output)
    (and (short-weierstrass-affine-point-p first)
         (short-weierstrass-affine-point-p second)
         (not (equal (affine-coordinates-x first)
                     (affine-coordinates-x second)))
         (equal (affine-pair-classify first second) :distinct-x)))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance affine-pair-classify-distinct-x-characterization))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(affine-distinct-x-secant-relation-p
                       affine-coordinates-x-of-fix))))))

(local
 (defthm secant-relation-under-fixed-operands-local
   (implies
    (and (affine-distinct-x-secant-relation-p
          first-a second-a slope output)
         (equal (affine-coordinates-fix first-a)
                (affine-coordinates-fix first-b))
         (equal (affine-coordinates-fix second-a)
                (affine-coordinates-fix second-b)))
    (affine-distinct-x-secant-relation-p
     first-b second-b slope output))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance affine-distinct-x-secant-relation-p-of-fixes
                      (first first-a) (second second-a))
           (:instance affine-distinct-x-secant-relation-p-of-fixes
                      (first first-b) (second second-b)))
     :in-theory
     (union-theories (theory 'minimal-theory)
                     '(affine-coordinates-fix-idempotent))))))

(defthm affine-dd-secant-relation-associative-when-all-distinct-x
  (implies
   (and
    (affine-distinct-x-secant-relation-p a b p-slope ab)
    (affine-distinct-x-secant-relation-p b c r-slope bc)
    (affine-distinct-x-secant-relation-p ab c q-slope left)
    (affine-distinct-x-secant-relation-p a bc tt-slope right))
   (equal (affine-coordinates-fix left)
          (affine-coordinates-fix right)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance secant-relation-consequences-local
                (first a) (second b) (slope p-slope) (output ab))
     (:instance secant-relation-consequences-local
                (first b) (second c) (slope r-slope) (output bc))
     (:instance affine-distinct-x-output-satisfies-secant-relation
                (first a) (second b))
     (:instance affine-distinct-x-output-satisfies-secant-relation
                (first b) (second c))
     (:instance affine-distinct-x-secant-relation-unique
                (first a) (second b)
                (slope-a p-slope) (output-a ab)
                (slope-b (affine-distinct-x-slope a b))
                (output-b (xcert-ab a b)))
     (:instance affine-distinct-x-secant-relation-unique
                (first b) (second c)
                (slope-a r-slope) (output-a bc)
                (slope-b (affine-distinct-x-slope b c))
                (output-b (xcert-bc b c)))
     (:instance secant-relation-under-fixed-operands-local
                (first-a ab) (second-a c) (slope q-slope) (output left)
                (first-b (xcert-ab a b)) (second-b c))
     (:instance secant-relation-under-fixed-operands-local
                (first-a a) (second-a bc) (slope tt-slope) (output right)
                (first-b a) (second-b (xcert-bc b c)))
     (:instance secant-relation-consequences-local
                (first (xcert-ab a b)) (second c)
                (slope q-slope) (output left))
     (:instance secant-relation-consequences-local
                (first a) (second (xcert-bc b c))
                (slope tt-slope) (output right))
     (:instance affine-distinct-x-output-satisfies-secant-relation
                (first (xcert-ab a b)) (second c))
     (:instance affine-distinct-x-output-satisfies-secant-relation
                (first a) (second (xcert-bc b c)))
     (:instance affine-distinct-x-secant-relation-unique
                (first (xcert-ab a b)) (second c)
                (slope-a q-slope) (output-a left)
                (slope-b (affine-distinct-x-slope (xcert-ab a b) c))
                (output-b (xcert-left a b c)))
     (:instance affine-distinct-x-secant-relation-unique
                (first a) (second (xcert-bc b c))
                (slope-a tt-slope) (output-a right)
                (slope-b (affine-distinct-x-slope a (xcert-bc b c)))
                (output-b (xcert-right a b c)))
     (:instance xcert-untagged-outputs-equal))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(xcert-ab xcert-bc xcert-left xcert-right
       affine-coordinates-fix-of-affine-distinct-x-output)))))
