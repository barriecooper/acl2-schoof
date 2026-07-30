(in-package "GFIELD")

(include-book "../field/xcert-final-y-reconstruction")
(include-book "affine-distinct-x-closure")

; The two ordered, total distinct-x calculation trees.  These names abbreviate
; only existing operations; they neither test a branch nor implement addition.
(defun xcert-ab (a b) (affine-distinct-x-output a b))
(defun xcert-bc (b c) (affine-distinct-x-output b c))
(defun xcert-left (a b c) (affine-distinct-x-output (xcert-ab a b) c))
(defun xcert-right (a b c) (affine-distinct-x-output a (xcert-bc b c)))

(defun xcert-p (a b) (affine-distinct-x-slope a b))
(defun xcert-q (a b c) (affine-distinct-x-slope (xcert-ab a b) c))
(defun xcert-r (b c) (affine-distinct-x-slope b c))
(defun xcert-tt (a b c) (affine-distinct-x-slope a (xcert-bc b c)))

(defun xcert-xa (a) (affine-coordinates-x a))
(defun xcert-xb (b) (affine-coordinates-x b))
(defun xcert-xc (c) (affine-coordinates-x c))
(defun xcert-xab (a b) (affine-coordinates-x (xcert-ab a b)))
(defun xcert-xbc (b c) (affine-coordinates-x (xcert-bc b c)))
(defun xcert-xl (a b c) (affine-coordinates-x (xcert-left a b c)))
(defun xcert-xr (a b c) (affine-coordinates-x (xcert-right a b c)))

(defthm xcert-curve-dx-specialization
  (equal (xcert-dx (xcert-xl a b c) (xcert-xr a b c))
         (field-sub (affine-coordinates-x (affine-distinct-x-output
                                           (affine-distinct-x-output a b) c))
                    (affine-coordinates-x (affine-distinct-x-output
                                           a (affine-distinct-x-output b c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(xcert-dx xcert-xl xcert-xr xcert-left
                                      xcert-right xcert-ab xcert-bc
                                      affine-coordinates-x-of-affine-distinct-x-output)))))

(defthm xcert-gxl-curve-specialization
  (equal (xcert-gxl (xcert-xl a b c) (xcert-xab a b) (xcert-xc c)
                     (xcert-q a b c))
         (field-sub
          (field-add (field-add (affine-distinct-x-output-x (xcert-ab a b) c)
                                (affine-coordinates-x (xcert-ab a b)))
                     (affine-coordinates-x c))
          (field-mul (affine-distinct-x-slope (xcert-ab a b) c)
                     (affine-distinct-x-slope (xcert-ab a b) c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(xcert-gxl xcert-xl xcert-xab xcert-xc
                                      xcert-q xcert-left
                                      affine-coordinates-x-of-affine-distinct-x-output)))))

(defthm xcert-gxr-curve-specialization
  (equal (xcert-gxr (xcert-xr a b c) (xcert-xa a) (xcert-xbc b c)
                     (xcert-tt a b c))
         (field-sub
          (field-add (field-add (affine-distinct-x-output-x a (xcert-bc b c))
                                (affine-coordinates-x a))
                     (affine-coordinates-x (xcert-bc b c)))
          (field-mul (affine-distinct-x-slope a (xcert-bc b c))
                     (affine-distinct-x-slope a (xcert-bc b c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(xcert-gxr xcert-xr xcert-xa xcert-xbc
                                      xcert-tt xcert-right
                                      affine-coordinates-x-of-affine-distinct-x-output)))))

(defthm xcert-gxab-curve-specialization
  (equal (xcert-gxab (xcert-xab a b) (xcert-xa a) (xcert-xb b) (xcert-p a b))
         (field-sub
          (field-add (field-add (affine-distinct-x-output-x a b)
                                (affine-coordinates-x a))
                     (affine-coordinates-x b))
          (field-mul (affine-distinct-x-slope a b)
                     (affine-distinct-x-slope a b))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(xcert-gxab xcert-xab xcert-xa xcert-xb
                                      xcert-p xcert-ab affine-coordinates-x-of-affine-distinct-x-output)))))

(defthm xcert-gxbc-curve-specialization
  (equal (xcert-gxbc (xcert-xbc b c) (xcert-xb b) (xcert-xc c) (xcert-r b c))
         (field-sub
          (field-add (field-add (affine-distinct-x-output-x b c)
                                (affine-coordinates-x b))
                     (affine-coordinates-x c))
          (field-mul (affine-distinct-x-slope b c)
                     (affine-distinct-x-slope b c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(xcert-gxbc xcert-xbc xcert-xb xcert-xc
                                      xcert-r xcert-bc affine-coordinates-x-of-affine-distinct-x-output)))))

; Each zero result is only the already-certified output-x rearrangement followed
; by FIELD-SUB-SELF.  It needs no branch, curve, or denominator hypothesis.
(defthm xcert-gxl-curve-zero
  (equal (xcert-gxl (xcert-xl a b c) (xcert-xab a b) (xcert-xc c)
                     (xcert-q a b c)) (field-zero))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-distinct-x-output-x-rearrangement
                         (first (xcert-ab a b)) (second c))
                        (:instance xcert-gxl-curve-specialization))
           :in-theory (union-theories (theory 'minimal-theory) '(field-sub-self)))))
(defthm xcert-gxr-curve-zero
  (equal (xcert-gxr (xcert-xr a b c) (xcert-xa a) (xcert-xbc b c)
                     (xcert-tt a b c)) (field-zero))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-distinct-x-output-x-rearrangement
                         (first a) (second (xcert-bc b c)))
                        (:instance xcert-gxr-curve-specialization))
           :in-theory (union-theories (theory 'minimal-theory) '(field-sub-self)))))
(defthm xcert-gxab-curve-zero
  (equal (xcert-gxab (xcert-xab a b) (xcert-xa a) (xcert-xb b) (xcert-p a b))
         (field-zero))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-distinct-x-output-x-rearrangement
                         (first a) (second b))
                        (:instance xcert-gxab-curve-specialization))
           :in-theory (union-theories (theory 'minimal-theory) '(field-sub-self)))))
(defthm xcert-gxbc-curve-zero
  (equal (xcert-gxbc (xcert-xbc b c) (xcert-xb b) (xcert-xc c) (xcert-r b c))
         (field-zero))
  :rule-classes nil
  :hints (("Goal" :use ((:instance affine-distinct-x-output-x-rearrangement
                         (first b) (second c))
                        (:instance xcert-gxbc-curve-specialization))
           :in-theory (union-theories (theory 'minimal-theory) '(field-sub-self)))))

(defthm xcert-h-curve-specialization
  (equal (xcert-h (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                   (xcert-xa a) (xcert-xc c))
         (field-sub
          (field-mul (field-sub (affine-distinct-x-slope a b)
                                (affine-distinct-x-slope b c))
                     (field-add (affine-distinct-x-slope a b)
                                (affine-distinct-x-slope (xcert-ab a b) c)))
          (field-sub (affine-coordinates-x a) (affine-coordinates-x c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(xcert-h xcert-p xcert-q xcert-r
                                      xcert-xa xcert-xc)))))

(defthm xcert-h-curve-zero
  (implies
   (and (short-weierstrass-affine-point-p a)
        (short-weierstrass-affine-point-p b)
        (short-weierstrass-affine-point-p c)
        (equal (affine-pair-classify a b) :distinct-x)
        (equal (affine-pair-classify b c) :distinct-x)
        (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x))
   (equal (xcert-h (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                   (xcert-xa a) (xcert-xc c))
          (field-zero)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance short-weierstrass-affine-point-p-of-affine-distinct-x-output
                (first a) (second b))
     (:instance affine-distinct-x-input-secant-identity
                (first a) (second b))
     (:instance affine-distinct-x-input-secant-identity
                (first (xcert-ab a b)) (second c))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first a) (second b))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first b) (second c))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first (xcert-ab a b)) (second c))
     (:instance affine-distinct-x-output-x-rearrangement
                (first a) (second b))
     (:instance affine-distinct-x-output-y-rearrangement
                (first a) (second b))
     (:instance affine-pair-classify-distinct-x-implies-x-difference-nonzero
                (first b) (second c))
     (:instance xcert-h-scalar-reconstruction
                (p (xcert-p a b))
                (q (xcert-q a b c))
                (r (xcert-r b c))
                (xa (xcert-xa a))
                (xb (xcert-xb b))
                (xc (xcert-xc c))
                (xab (xcert-xab a b))
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yc (affine-coordinates-y c))
                (yab (affine-coordinates-y (xcert-ab a b)))
                (a (field-fix (short-weierstrass-a)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(xcert-h xcert-p xcert-q xcert-r xcert-xa xcert-xb xcert-xc
       xcert-xab xcert-ab affine-coordinates-x-of-affine-distinct-x-output
       affine-coordinates-y-of-affine-distinct-x-output field-sub-self)))))

(defthm xcert-s-curve-specialization
  (equal (xcert-s (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                   (xcert-tt a b c))
         (field-sub
          (field-add (affine-distinct-x-slope a b)
                     (affine-distinct-x-slope (xcert-ab a b) c))
          (field-add (affine-distinct-x-slope b c)
                     (affine-distinct-x-slope a (xcert-bc b c)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(xcert-s xcert-p xcert-q xcert-r xcert-tt)))))

(defthm xcert-s-curve-zero
  (implies
   (and (short-weierstrass-affine-point-p a)
        (short-weierstrass-affine-point-p b)
        (short-weierstrass-affine-point-p c)
        (equal (affine-pair-classify a b) :distinct-x)
        (equal (affine-pair-classify b c) :distinct-x)
        (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x)
        (equal (affine-pair-classify a (xcert-bc b c)) :distinct-x))
   (equal
    (field-sub
     (field-add (affine-distinct-x-slope a b)
                (affine-distinct-x-slope (xcert-ab a b) c))
     (field-add (affine-distinct-x-slope b c)
                (affine-distinct-x-slope a (xcert-bc b c))))
    (field-zero)))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance short-weierstrass-affine-point-p-of-affine-distinct-x-output
                (first a) (second b))
     (:instance short-weierstrass-affine-point-p-of-affine-distinct-x-output
                (first b) (second c))
     (:instance affine-distinct-x-input-secant-identity (first a) (second b))
     (:instance affine-distinct-x-input-secant-identity
                (first (xcert-ab a b)) (second c))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first a) (second b))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first (xcert-ab a b)) (second c))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first b) (second c))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first a) (second (xcert-bc b c)))
     (:instance affine-distinct-x-output-x-rearrangement (first a) (second b))
     (:instance affine-distinct-x-output-y-rearrangement (first a) (second b))
     (:instance affine-distinct-x-output-x-rearrangement (first b) (second c))
     (:instance affine-distinct-x-output-y-rearrangement (first b) (second c))
     (:instance affine-pair-classify-distinct-x-implies-x-difference-nonzero
                (first b) (second c))
     (:instance affine-pair-classify-distinct-x-implies-x-difference-nonzero
                (first a) (second (xcert-bc b c)))
     (:instance xcert-s-scalar-reconstruction
                (p (xcert-p a b)) (q (xcert-q a b c))
                (r (xcert-r b c)) (tt (xcert-tt a b c))
                (xa (xcert-xa a)) (xb (xcert-xb b)) (xc (xcert-xc c))
                (xab (xcert-xab a b)) (xbc (xcert-xbc b c))
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yc (affine-coordinates-y c))
                (yab (affine-coordinates-y (xcert-ab a b)))
                (ybc (affine-coordinates-y (xcert-bc b c)))
                (curve-a (field-fix (short-weierstrass-a)))))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(xcert-p xcert-q xcert-r xcert-tt xcert-xa xcert-xb xcert-xc
       xcert-xab xcert-xbc xcert-ab xcert-bc
       affine-coordinates-x-of-affine-distinct-x-output
       affine-coordinates-y-of-affine-distinct-x-output)))))

(defthm xcert-c-curve-specialization
  (equal (xcert-c (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                   (xcert-tt a b c))
         (field-add
          (field-sub (field-add (affine-distinct-x-slope a b)
                                (affine-distinct-x-slope (xcert-ab a b) c))
                     (affine-distinct-x-slope b c))
          (affine-distinct-x-slope a (xcert-bc b c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(xcert-c xcert-p xcert-q xcert-r xcert-tt)))))

(defthm xcert-curve-composition
  (equal
   (xcert-dx (xcert-xl a b c) (xcert-xr a b c))
   (field-add
    (field-sub
     (xcert-telescope (xcert-xl a b c) (xcert-xr a b c)
                      (xcert-xab a b) (xcert-xbc b c)
                      (xcert-xa a) (xcert-xb b) (xcert-xc c)
                      (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                      (xcert-tt a b c))
     (field-add
      (xcert-h (xcert-p a b) (xcert-q a b c) (xcert-r b c)
               (xcert-xa a) (xcert-xc c))
      (xcert-h (xcert-p a b) (xcert-q a b c) (xcert-r b c)
               (xcert-xa a) (xcert-xc c))))
    (field-mul
     (xcert-c (xcert-p a b) (xcert-q a b c) (xcert-r b c) (xcert-tt a b c))
     (xcert-s (xcert-p a b) (xcert-q a b c) (xcert-r b c) (xcert-tt a b c)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance xcert-composition
                         (xl (xcert-xl a b c)) (xr (xcert-xr a b c))
                         (xab (xcert-xab a b)) (xbc (xcert-xbc b c))
                         (xa (xcert-xa a)) (xb (xcert-xb b)) (xc (xcert-xc c))
                         (p (xcert-p a b)) (q (xcert-q a b c))
                         (r (xcert-r b c)) (tt (xcert-tt a b c))))
           :in-theory (theory 'minimal-theory))))

(local
 (defthm xcert-curve-telescope-zero-local
   (equal
    (xcert-telescope (xcert-xl a b c) (xcert-xr a b c)
                     (xcert-xab a b) (xcert-xbc b c)
                     (xcert-xa a) (xcert-xb b) (xcert-xc c)
                     (xcert-p a b) (xcert-q a b c) (xcert-r b c)
                     (xcert-tt a b c))
    (field-zero))
   :hints
   (("Goal"
     :use ((:instance xcert-gxl-curve-zero)
           (:instance xcert-gxr-curve-zero)
           (:instance xcert-gxab-curve-zero)
           (:instance xcert-gxbc-curve-zero))
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(xcert-telescope field-sub field-neg-of-zero field-add-zero-left
        field-add-zero-right field-fix-of-zero))))))

(local
 (defthm xcert-final-x-difference-zero-local
   (implies
    (and (short-weierstrass-affine-point-p a)
         (short-weierstrass-affine-point-p b)
         (short-weierstrass-affine-point-p c)
         (equal (affine-pair-classify a b) :distinct-x)
         (equal (affine-pair-classify b c) :distinct-x)
         (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x)
         (equal (affine-pair-classify a (xcert-bc b c)) :distinct-x))
    (equal (xcert-dx (xcert-xl a b c) (xcert-xr a b c))
           (field-zero)))
   :hints
   (("Goal"
     :use ((:instance xcert-curve-composition)
           (:instance xcert-curve-telescope-zero-local)
           (:instance xcert-h-curve-zero)
           (:instance xcert-s-curve-zero)
           (:instance xcert-s-curve-specialization))
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(field-sub field-neg-of-zero field-add-zero-left field-add-zero-right
        field-mul-zero-right field-fix-of-zero))))))

(defthm xcert-final-x-coordinates-equal
  (implies
   (and (short-weierstrass-affine-point-p a)
        (short-weierstrass-affine-point-p b)
        (short-weierstrass-affine-point-p c)
        (equal (affine-pair-classify a b) :distinct-x)
        (equal (affine-pair-classify b c) :distinct-x)
        (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x)
        (equal (affine-pair-classify a (xcert-bc b c)) :distinct-x))
   (equal (xcert-xl a b c) (xcert-xr a b c)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance xcert-final-x-difference-zero-local)
          (:instance field-sub-equal-zero-implies-fixed-equal
                     (first (xcert-xl a b c))
                     (second (xcert-xr a b c))))
    :in-theory
    (union-theories (theory 'minimal-theory)
     '(xcert-dx xcert-xl xcert-xr xcert-left xcert-right
       field-fix-of-affine-distinct-x-output-x
       affine-coordinates-x-of-affine-distinct-x-output)))))

; Turn the maintained semantic H-zero result back into the exact scalar
; equality expected by the field-only final-y theorem.  This is deliberately
; local: the public semantic interface remains the three curve memberships and
; four ordered distinct-x classifications.
(local
 (defthm equal-zero-reverse-local
   (implies (equal (field-zero) x)
            (equal x (field-zero)))
   :rule-classes nil))

(local
 (defthm xcert-h-scalar-equality-local
   (implies
    (and (short-weierstrass-affine-point-p a)
         (short-weierstrass-affine-point-p b)
         (short-weierstrass-affine-point-p c)
         (equal (affine-pair-classify a b) :distinct-x)
         (equal (affine-pair-classify b c) :distinct-x)
         (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x))
    (equal
     (field-mul (field-sub (xcert-p a b) (xcert-r b c))
                (field-add (xcert-p a b) (xcert-q a b c)))
     (field-sub (xcert-xa a) (xcert-xc c))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance xcert-h-curve-zero)
           (:instance xcert-h-curve-specialization)
           (:instance equal-zero-reverse-local
                      (x
                       (field-sub
                        (field-mul
                         (field-sub (xcert-p a b) (xcert-r b c))
                         (field-add (xcert-p a b) (xcert-q a b c)))
                        (field-sub (xcert-xa a) (xcert-xc c)))))
           (:instance field-sub-equal-zero-implies-fixed-equal
                      (first
                       (field-mul
                        (field-sub (xcert-p a b) (xcert-r b c))
                        (field-add (xcert-p a b) (xcert-q a b c))))
                      (second (field-sub (xcert-xa a) (xcert-xc c)))))
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(xcert-p xcert-q xcert-r xcert-xa xcert-xc
        field-sub field-fix-of-add field-fix-of-mul field-fix-of-neg
        field-fix-of-zero))))))

(local
 (defthm xcert-final-right-y-with-left-x-local
   (implies
    (and (short-weierstrass-affine-point-p a)
         (short-weierstrass-affine-point-p b)
         (short-weierstrass-affine-point-p c)
         (equal (affine-pair-classify a b) :distinct-x)
         (equal (affine-pair-classify b c) :distinct-x)
         (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x)
         (equal (affine-pair-classify a (xcert-bc b c)) :distinct-x))
    (equal
     (field-add (affine-coordinates-y (xcert-right a b c))
                (affine-coordinates-y a))
     (field-mul (xcert-tt a b c)
                (field-sub (xcert-xa a) (xcert-xl a b c)))))
   :rule-classes nil
   :hints
   (("Goal"
     :use ((:instance xcert-final-x-coordinates-equal)
           (:instance affine-distinct-x-output-y-rearrangement
                      (first a) (second (xcert-bc b c))))
     :in-theory
     (union-theories (theory 'minimal-theory)
      '(xcert-tt xcert-xa xcert-xl xcert-xr xcert-left xcert-right
        affine-coordinates-x-of-affine-distinct-x-output
        affine-coordinates-y-of-affine-distinct-x-output))))))

; Semantic map for the single field-theorem instantiation below:
; p/q/r/tt are the four ordered slopes; xa/xb/xc and ya/yb/yc are
; coordinates of A/B/C; xab/yab are coordinates of AB; and xl/yl/yr are
; respectively the final-left x/y coordinates and final-right y coordinate.
(defthm xcert-final-y-coordinates-equal
  (implies
   (and (short-weierstrass-affine-point-p a)
        (short-weierstrass-affine-point-p b)
        (short-weierstrass-affine-point-p c)
        (equal (affine-pair-classify a b) :distinct-x)
        (equal (affine-pair-classify b c) :distinct-x)
        (equal (affine-pair-classify (xcert-ab a b) c) :distinct-x)
        (equal (affine-pair-classify a (xcert-bc b c)) :distinct-x))
   (equal
    (field-fix (affine-coordinates-y (xcert-left a b c)))
    (field-fix (affine-coordinates-y (xcert-right a b c)))))
  :rule-classes nil
  :hints
  (("Goal"
    :use
    ((:instance xcert-field-only-final-y-equal
                (p (xcert-p a b)) (q (xcert-q a b c))
                (r (xcert-r b c)) (tt (xcert-tt a b c))
                (xa (xcert-xa a)) (xb (xcert-xb b)) (xc (xcert-xc c))
                (ya (affine-coordinates-y a))
                (yb (affine-coordinates-y b))
                (yc (affine-coordinates-y c))
                (xab (xcert-xab a b))
                (yab (affine-coordinates-y (xcert-ab a b)))
                (xl (xcert-xl a b c))
                (yl (affine-coordinates-y (xcert-left a b c)))
                (yr (affine-coordinates-y (xcert-right a b c))))
     (:instance affine-distinct-x-output-x-rearrangement
                (first (xcert-ab a b)) (second c))
     (:instance affine-distinct-x-output-x-rearrangement
                (first a) (second b))
     (:instance xcert-h-scalar-equality-local)
     (:instance xcert-s-curve-zero)
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first a) (second b))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first b) (second c))
     (:instance affine-distinct-x-slope-reconstructs-y-difference
                (first (xcert-ab a b)) (second c))
     (:instance affine-distinct-x-output-y-rearrangement
                (first (xcert-ab a b)) (second c))
     (:instance xcert-final-right-y-with-left-x-local))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(xcert-p xcert-q xcert-r xcert-tt xcert-xa xcert-xb xcert-xc
       xcert-xab xcert-xl xcert-ab xcert-bc xcert-left xcert-right
       affine-coordinates-x-of-affine-distinct-x-output
       affine-coordinates-y-of-affine-distinct-x-output)))))
