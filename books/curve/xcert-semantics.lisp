(in-package "GFIELD")

(include-book "../field/xcert-algebra")
(include-book "affine-distinct-x-output")

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
