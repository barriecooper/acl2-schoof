(in-package "GFIELD")

(include-book "affine-distinct-x-secant-relation")
(include-book "affine-doubling-relation")
(include-book "exceptional-addition-relations")

; The two slope terms below select the unique field element described by the
; division-free branch relations.  They select no output and perform no case
; dispatch; FIELD-DIV is part of the mathematical field interface.
(defun curve-point-addition-relation-p (first second output)
  (let* ((first (curve-point-fix first))
         (second (curve-point-fix second))
         (output (curve-point-fix output))
         (first-affine (curve-point-affine-coordinates-get first))
         (second-affine (curve-point-affine-coordinates-get second))
         (output-affine (curve-point-affine-coordinates-get output)))
    (and
     (short-weierstrass-curve-point-p first)
     (short-weierstrass-curve-point-p second)
     (or
      (curve-point-left-infinity-identity-relation-p first second output)
      (curve-point-right-infinity-identity-relation-p first second output)
      (and
       (equal first (curve-point-affine-coordinates first-affine))
       (equal second (curve-point-affine-coordinates second-affine))
       (or
        (and
         (equal output (curve-point-affine-coordinates output-affine))
         (affine-distinct-x-secant-relation-p
          first-affine second-affine
          (field-div (field-sub (affine-coordinates-y second-affine)
                                (affine-coordinates-y first-affine))
                     (field-sub (affine-coordinates-x second-affine)
                                (affine-coordinates-x first-affine)))
          output-affine))
        (affine-opposite-y-infinity-relation-p
         first-affine second-affine output)
        (and
         (equal output (curve-point-affine-coordinates output-affine))
         (equal (affine-coordinates-fix first-affine)
                (affine-coordinates-fix second-affine))
         (affine-doubling-relation-p
          first-affine
          (field-div
           (field-add
            (field-mul
             (field-add (field-add (field-one) (field-one)) (field-one))
             (field-mul (affine-coordinates-x first-affine)
                        (affine-coordinates-x first-affine)))
            (field-fix (short-weierstrass-a)))
           (field-add (affine-coordinates-y first-affine)
                      (affine-coordinates-y first-affine)))
          output-affine))))))))

(defthm curve-point-addition-relation-p-of-fixes
  (equal (curve-point-addition-relation-p
          (curve-point-fix first) (curve-point-fix second)
          (curve-point-fix output))
         (curve-point-addition-relation-p first second output))
  :hints (("Goal" :in-theory (enable curve-point-addition-relation-p))))

; This theorem exposes the complete mathematical case split without choosing
; an output.  The cases overlap only when both operands are infinity.
(local
 (defthm curve-point-shape-and-affine-membership-local
   (implies
    (short-weierstrass-curve-point-p point)
    (or (curve-point-infinity-p point)
        (and (equal point
                    (curve-point-affine-coordinates
                     (curve-point-affine-coordinates-get point)))
             (short-weierstrass-affine-point-p
              (curve-point-affine-coordinates-get point)))))
   :rule-classes nil
   :hints (("Goal" :in-theory
            (enable short-weierstrass-curve-point-p
                    curve-point-representation-p
                    curve-point-fix
                    curve-point-affine-coordinates-get)))))

(local
 (defthm curve-point-membership-implies-representation-local
   (implies (short-weierstrass-curve-point-p point)
            (curve-point-representation-p point))
   :hints (("Goal" :in-theory (enable short-weierstrass-curve-point-p)))))

(local
 (defthm infinity-not-affine-local
   (not (equal (curve-point-infinity)
               (curve-point-affine-coordinates coordinates)))
   :hints (("Goal" :in-theory (enable curve-point-infinity
                                      curve-point-affine-coordinates)))))

(defthm curve-point-addition-case-coverage
  (implies
   (and (short-weierstrass-curve-point-p first)
        (short-weierstrass-curve-point-p second))
   (or (curve-point-infinity-p first)
       (curve-point-infinity-p second)
       (not (equal
             (affine-coordinates-x
              (curve-point-affine-coordinates-get first))
             (affine-coordinates-x
              (curve-point-affine-coordinates-get second))))
       (equal
        (affine-coordinates-y
         (curve-point-affine-coordinates-get second))
        (field-neg
         (affine-coordinates-y
          (curve-point-affine-coordinates-get first))))
       (and
        (equal
         (affine-coordinates-x
          (curve-point-affine-coordinates-get first))
         (affine-coordinates-x
          (curve-point-affine-coordinates-get second)))
        (equal
         (affine-coordinates-y
          (curve-point-affine-coordinates-get first))
         (affine-coordinates-y
          (curve-point-affine-coordinates-get second)))
        (not
         (equal
          (affine-coordinates-y
           (curve-point-affine-coordinates-get first))
          (field-neg
           (affine-coordinates-y
            (curve-point-affine-coordinates-get first))))))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance curve-point-shape-and-affine-membership-local
                (point first))
     (:instance curve-point-shape-and-affine-membership-local
                (point second))
     (:instance affine-pair-classify-exhaustive
                (first (curve-point-affine-coordinates-get first))
                (second (curve-point-affine-coordinates-get second)))
     (:instance affine-pair-classify-distinct-x-characterization
                (first (curve-point-affine-coordinates-get first))
                (second (curve-point-affine-coordinates-get second)))
     (:instance affine-pair-classify-opposite-y-characterization
                (first (curve-point-affine-coordinates-get first))
                (second (curve-point-affine-coordinates-get second)))
     (:instance affine-pair-classify-same-point-non-opposite-characterization
                (first (curve-point-affine-coordinates-get first))
                (second (curve-point-affine-coordinates-get second)))
     (:instance affine-pair-classify-not-same-x-other-for-curve-points
                (first (curve-point-affine-coordinates-get first))
                (second (curve-point-affine-coordinates-get second))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(affine-coordinates-fix-idempotent
       affine-coordinates-x-of-fix
       affine-coordinates-y-of-fix
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-fix-when-field-element-p
       car-cons
       cdr-cons)))))

(local
 (defthm affine-pair-output-satisfies-addition-cases-local
   (implies
    (and (short-weierstrass-affine-point-p first)
         (short-weierstrass-affine-point-p second))
    (let ((output (affine-pair-output-point first second)))
      (or
       (and (equal output
                   (curve-point-affine-coordinates
                    (curve-point-affine-coordinates-get output)))
            (affine-distinct-x-secant-relation-p
             first second
             (field-div (field-sub (affine-coordinates-y second)
                                   (affine-coordinates-y first))
                        (field-sub (affine-coordinates-x second)
                                   (affine-coordinates-x first)))
             (curve-point-affine-coordinates-get output)))
       (affine-opposite-y-infinity-relation-p first second output)
       (and (equal (affine-coordinates-fix first)
                       (affine-coordinates-fix second))
            (equal output
                   (curve-point-affine-coordinates
                    (curve-point-affine-coordinates-get output)))
            (affine-doubling-relation-p
             first
             (field-div
              (field-add
               (field-mul
                (field-add (field-add (field-one) (field-one)) (field-one))
                (field-mul (affine-coordinates-x first)
                           (affine-coordinates-x first)))
               (field-fix (short-weierstrass-a)))
              (field-add (affine-coordinates-y first)
                         (affine-coordinates-y first)))
             (curve-point-affine-coordinates-get output))))))
   :rule-classes nil
   :hints
   (("Goal"
     :use (affine-pair-classify-exhaustive
           (:instance short-weierstrass-affine-point-p-definition
                      (coordinates first))
           (:instance short-weierstrass-affine-point-p-definition
                      (coordinates second))
           affine-pair-classify-not-same-x-other-for-curve-points
           affine-pair-classify-distinct-x-characterization
           affine-pair-classify-opposite-y-characterization
           affine-pair-classify-same-point-non-opposite-characterization
           affine-distinct-x-output-satisfies-secant-relation
           (:instance affine-opposite-y-output-point-satisfies-infinity-relation
                      (first first) (second second))
           (:instance affine-same-point-non-opposite-output-satisfies-doubling-relation
                      (input first)))
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(affine-pair-output-point-when-distinct-x
        affine-pair-output-point-when-opposite-y
        affine-pair-output-point-when-same-point-non-opposite
        affine-distinct-x-output-point
        affine-same-point-non-opposite-output-point
        affine-opposite-y-output-point-is-infinity
        curve-point-affine-coordinates-get-of-constructor
        affine-coordinates-fix-idempotent
        affine-coordinates-fix
        affine-coordinates-make
        affine-coordinates-fix-of-affine-distinct-x-output
        affine-coordinates-fix-of-affine-same-point-non-opposite-output
        affine-coordinates-x-of-fix
        affine-coordinates-y-of-fix
        affine-distinct-x-slope
        affine-same-point-non-opposite-slope))))))

(defthm curve-point-pair-output-point-satisfies-addition-relation
  (implies
   (and (short-weierstrass-curve-point-p first)
        (short-weierstrass-curve-point-p second))
   (curve-point-addition-relation-p
    first second (curve-point-pair-output-point first second)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance curve-point-shape-and-affine-membership-local
                     (point first))
          (:instance curve-point-shape-and-affine-membership-local
                     (point second))
          (:instance curve-point-membership-implies-representation-local
                     (point first))
          (:instance curve-point-membership-implies-representation-local
                     (point second))
          (:instance short-weierstrass-curve-point-p-of-fix (point first))
          (:instance short-weierstrass-curve-point-p-of-fix (point second))
          (:instance affine-pair-output-satisfies-addition-cases-local
                     (first (curve-point-affine-coordinates-get first))
                     (second (curve-point-affine-coordinates-get second)))
          (:instance affine-opposite-y-infinity-relation-p-of-fixes
                     (first (curve-point-affine-coordinates-get first))
                     (second (curve-point-affine-coordinates-get second))
                     (output (affine-pair-output-point
                              (curve-point-affine-coordinates-get first)
                              (curve-point-affine-coordinates-get second)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-addition-relation-p
       curve-point-left-infinity-identity-relation-p
       curve-point-right-infinity-identity-relation-p
       affine-opposite-y-infinity-relation-p-of-fixes
       affine-opposite-y-infinity-relation-p
       curve-point-fix-idempotent
       curve-point-fix-when-representation-p
       curve-point-infinity-p
       curve-point-pair-output-point
       curve-point-pair-output-point-of-infinity-left
       curve-point-pair-output-point-of-infinity-right
       curve-point-pair-output-point-of-affines
       curve-point-fix-of-affine-coordinates
       curve-point-affine-coordinates-get-of-constructor
       affine-coordinates-fix-idempotent)))))

(local
 (defthm secant-relation-implies-distinct-x-local
   (implies (affine-distinct-x-secant-relation-p first second slope output)
            (not (equal (affine-coordinates-x first)
                        (affine-coordinates-x second))))
   :hints (("Goal" :in-theory
            (enable affine-distinct-x-secant-relation-p)))))

(local
 (defthm doubling-relation-implies-non-opposite-local
   (implies (affine-doubling-relation-p input slope output)
            (not (equal (affine-coordinates-y input)
                        (field-neg (affine-coordinates-y input)))))
   :hints (("Goal" :in-theory (enable affine-doubling-relation-p)))))

(local
 (defthm equal-affine-fixes-implies-equal-x-local
   (implies (equal (affine-coordinates-fix first)
                   (affine-coordinates-fix second))
            (equal (affine-coordinates-x first)
                   (affine-coordinates-x second)))
   :hints (("Goal" :use ((:instance affine-coordinates-x-of-fix
                                     (coordinates first))
                          (:instance affine-coordinates-x-of-fix
                                     (coordinates second)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm equal-affine-fixes-implies-equal-y-local
   (implies (equal (affine-coordinates-fix first)
                   (affine-coordinates-fix second))
            (equal (affine-coordinates-y first)
                   (affine-coordinates-y second)))
   :hints (("Goal" :use ((:instance affine-coordinates-y-of-fix
                                     (coordinates first))
                          (:instance affine-coordinates-y-of-fix
                                     (coordinates second)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm secant-same-slope-output-unique-local
   (implies
    (and (affine-distinct-x-secant-relation-p first second slope output-a)
         (affine-distinct-x-secant-relation-p first second slope output-b))
    (equal (affine-coordinates-fix output-a)
           (affine-coordinates-fix output-b)))
   :hints (("Goal" :use
            ((:instance affine-distinct-x-secant-relation-unique
                        (slope-a slope) (slope-b slope)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm equal-affine-fixes-exclude-secant-local
   (implies
    (equal (affine-coordinates-fix first)
           (affine-coordinates-fix second))
    (not (affine-distinct-x-secant-relation-p
          first second slope output)))
   :hints (("Goal" :use (secant-relation-implies-distinct-x-local
                          equal-affine-fixes-implies-equal-x-local)
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm doubling-same-slope-output-unique-local
   (implies
    (and (affine-doubling-relation-p input slope output-a)
         (affine-doubling-relation-p input slope output-b))
    (equal (affine-coordinates-fix output-a)
           (affine-coordinates-fix output-b)))
   :hints (("Goal" :use
            ((:instance affine-doubling-relation-unique
                        (slope-a slope) (slope-b slope)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defun full-secant-slope-local (first second)
   (field-div
    (field-sub
     (affine-coordinates-y (curve-point-affine-coordinates-get second))
     (affine-coordinates-y (curve-point-affine-coordinates-get first)))
    (field-sub
     (affine-coordinates-x (curve-point-affine-coordinates-get second))
     (affine-coordinates-x (curve-point-affine-coordinates-get first))))))

(local
 (defun full-doubling-slope-local (first)
   (let ((p (curve-point-affine-coordinates-get first)))
     (field-div
      (field-add
       (field-mul
        (field-add (field-add (field-one) (field-one)) (field-one))
        (field-mul (affine-coordinates-x p) (affine-coordinates-x p)))
       (field-fix (short-weierstrass-a)))
      (field-add (affine-coordinates-y p) (affine-coordinates-y p))))))

(local
 (defthm affine-fix-of-curve-point-get-local
   (equal (affine-coordinates-fix
           (curve-point-affine-coordinates-get point))
          (curve-point-affine-coordinates-get point))
   :hints (("Goal" :in-theory
            (enable curve-point-affine-coordinates-get)))))

(defthm curve-point-addition-relation-output-determinate
  (implies
   (and (curve-point-addition-relation-p first second output-a)
        (curve-point-addition-relation-p first second output-b))
   (equal (curve-point-fix output-a) (curve-point-fix output-b)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance affine-distinct-x-secant-relation-unique
                (first (curve-point-affine-coordinates-get
                        (curve-point-fix first)))
                (second (curve-point-affine-coordinates-get
                         (curve-point-fix second)))
                (slope-a
                 (field-div
                  (field-sub
                   (affine-coordinates-y
                    (curve-point-affine-coordinates-get
                     (curve-point-fix second)))
                   (affine-coordinates-y
                    (curve-point-affine-coordinates-get
                     (curve-point-fix first))))
                  (field-sub
                   (affine-coordinates-x
                    (curve-point-affine-coordinates-get
                     (curve-point-fix second)))
                   (affine-coordinates-x
                    (curve-point-affine-coordinates-get
                     (curve-point-fix first))))))
                (slope-b
                 (field-div
                  (field-sub
                   (affine-coordinates-y
                    (curve-point-affine-coordinates-get
                     (curve-point-fix second)))
                   (affine-coordinates-y
                    (curve-point-affine-coordinates-get
                     (curve-point-fix first))))
                  (field-sub
                   (affine-coordinates-x
                    (curve-point-affine-coordinates-get
                     (curve-point-fix second)))
                   (affine-coordinates-x
                    (curve-point-affine-coordinates-get
                     (curve-point-fix first))))))
                (output-a (curve-point-affine-coordinates-get
                           (curve-point-fix output-a)))
                (output-b (curve-point-affine-coordinates-get
                           (curve-point-fix output-b))))
     (:instance affine-doubling-relation-unique
                (input (curve-point-affine-coordinates-get
                        (curve-point-fix first)))
                (output-a (curve-point-affine-coordinates-get
                           (curve-point-fix output-a)))
                (output-b (curve-point-affine-coordinates-get
                           (curve-point-fix output-b))))
     (:instance secant-relation-implies-distinct-x-local
                (first (curve-point-affine-coordinates-get
                        (curve-point-fix first)))
                (second (curve-point-affine-coordinates-get
                         (curve-point-fix second))))
     (:instance doubling-relation-implies-non-opposite-local
                (input (curve-point-affine-coordinates-get
                        (curve-point-fix first))))
     (:instance equal-affine-fixes-implies-equal-x-local
                (first (curve-point-affine-coordinates-get
                        (curve-point-fix first)))
                (second (curve-point-affine-coordinates-get
                         (curve-point-fix second))))
     (:instance equal-affine-fixes-implies-equal-y-local
                (first (curve-point-affine-coordinates-get
                        (curve-point-fix first)))
                (second (curve-point-affine-coordinates-get
                         (curve-point-fix second))))
     (:instance infinity-not-affine-local
                (coordinates (curve-point-affine-coordinates-get
                              (curve-point-fix output-a))))
     (:instance infinity-not-affine-local
                (coordinates (curve-point-affine-coordinates-get
                              (curve-point-fix output-b))))
     (:instance infinity-not-affine-local
                (coordinates (curve-point-affine-coordinates-get
                              (curve-point-fix first))))
     (:instance infinity-not-affine-local
                (coordinates (curve-point-affine-coordinates-get
                              (curve-point-fix second))))
     (:instance secant-same-slope-output-unique-local
                (first (curve-point-affine-coordinates-get
                        (curve-point-fix first)))
                (second (curve-point-affine-coordinates-get
                         (curve-point-fix second)))
                (slope (full-secant-slope-local
                        (curve-point-fix first) (curve-point-fix second)))
                (output-a (curve-point-affine-coordinates-get
                           (curve-point-fix output-a)))
                (output-b (curve-point-affine-coordinates-get
                           (curve-point-fix output-b))))
     (:instance doubling-same-slope-output-unique-local
                (input (curve-point-affine-coordinates-get
                        (curve-point-fix first)))
                (slope (full-doubling-slope-local
                        (curve-point-fix first)))
                (output-a (curve-point-affine-coordinates-get
                           (curve-point-fix output-a)))
                (output-b (curve-point-affine-coordinates-get
                           (curve-point-fix output-b)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(curve-point-addition-relation-p
       secant-relation-implies-distinct-x-local
       doubling-relation-implies-non-opposite-local
       equal-affine-fixes-implies-equal-x-local
       equal-affine-fixes-implies-equal-y-local
       equal-affine-fixes-exclude-secant-local
       full-secant-slope-local
       full-doubling-slope-local
       affine-fix-of-curve-point-get-local
       curve-point-left-infinity-identity-relation-p
       curve-point-right-infinity-identity-relation-p
       affine-opposite-y-infinity-relation-p
       curve-point-fix-idempotent
       curve-point-fix-of-infinity
       affine-coordinates-fix-idempotent
       affine-coordinates-fix
       affine-coordinates-make
       affine-coordinates-x-of-fix
       affine-coordinates-y-of-fix
       field-element-p-of-affine-coordinates-x
       field-element-p-of-affine-coordinates-y
       field-fix-when-field-element-p
       car-cons
       cdr-cons)))))

(verify-guards curve-point-addition-relation-p)
