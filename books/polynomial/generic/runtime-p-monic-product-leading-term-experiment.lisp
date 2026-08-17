(in-package "GPOLY")

(include-book "runtime-p-monic-product-leading-term")

; Certified, deliberately unregistered proof checkpoint for the intended
; production theorem RUNTIME-P-POLY-MUL-NONZERO-BY-MONIC-PROPERTIES.  The
; remaining task is the general raw final-coefficient induction described at
; the end of this book; no event here is a production interface.

(defun runtime-p-paired-list-induct-experiment (left right)
  (if (and (consp left) (consp right))
      (runtime-p-paired-list-induct-experiment (cdr left) (cdr right))
    (list left right)))

(defthm runtime-p-raw-add-when-left-atom-experiment
  (implies (and (not (consp left))
                (runtime-p-coefficient-list-p right p))
           (equal (runtime-p-raw-add left right p) right))
  :hints (("Goal"
           :use ((:instance runtime-p-fix-coefficients-when-recognized
                            (xs right)))
           :in-theory (enable runtime-p-raw-add))))

(defthm runtime-p-last-of-raw-add-when-right-longer-experiment
  (implies (and (runtime-p-coefficient-list-p left p)
                (runtime-p-coefficient-list-p right p)
                (< (len left) (len right)))
           (equal (car (last (runtime-p-raw-add left right p)))
                  (car (last right))))
  :hints (("Goal"
           :induct (runtime-p-paired-list-induct-experiment left right)
           :in-theory (enable runtime-p-raw-add
                              runtime-p-coefficient-list-p))))

(defthm runtime-p-len-of-raw-add-for-monic-product-experiment
  (equal (len (runtime-p-raw-add x y p))
         (max (len x) (len y)))
  :hints (("Goal" :induct (runtime-p-raw-add x y p)
           :in-theory (enable runtime-p-raw-add))))

(defthm runtime-p-len-of-raw-scale-for-monic-product-experiment
  (equal (len (runtime-p-raw-scale a x p)) (len x))
  :hints (("Goal" :induct (runtime-p-raw-scale a x p)
           :in-theory (enable runtime-p-raw-scale))))

(defthm runtime-p-len-of-raw-mul-for-monic-product-experiment
  (implies (and (true-listp x) (true-listp y))
           (equal (len (runtime-p-raw-mul x y p))
                  (if (or (endp x) (endp y)) 0
                    (+ -1 (len x) (len y)))))
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable runtime-p-raw-mul
                              runtime-p-len-of-raw-add-for-monic-product-experiment))))

(defthm runtime-p-strict-length-of-shifted-raw-product-experiment
  (implies (and (true-listp x) (consp x)
                (true-listp y) (consp y))
           (< (len (runtime-p-raw-scale a y p))
              (len (cons 0 (runtime-p-raw-mul x y p)))))
  :hints (("Goal"
           :use ((:instance runtime-p-len-of-raw-scale-for-monic-product-experiment
                            (x y))
                 (:instance runtime-p-len-of-raw-mul-for-monic-product-experiment))
           :do-not-induct t
           :in-theory (disable runtime-p-raw-scale runtime-p-raw-mul))))

(defthm runtime-p-last-of-raw-scale-experiment
  (implies (consp xs)
           (equal (car (last (runtime-p-raw-scale a xs p)))
                  (runtime-p-mul a (car (last xs)) p)))
  :hints (("Goal" :induct (runtime-p-raw-scale a xs p)
           :in-theory (enable runtime-p-raw-scale))))

(defthm runtime-p-coefficient-list-p-of-raw-scale-experiment
  (runtime-p-coefficient-list-p (runtime-p-raw-scale a xs p) p)
  :hints (("Goal" :induct (runtime-p-raw-scale a xs p)
           :in-theory (enable runtime-p-raw-scale
                              runtime-p-coefficient-list-p))))

(defthm runtime-p-raw-mul-last-by-monic-singleton-experiment
  (implies (and (runtime-p-coefficient-list-p x p)
                (consp x) (not (consp (cdr x)))
                (runtime-p-coefficient-list-p y p)
                (consp y)
                (equal (car (last y)) (runtime-p-one p)))
           (equal (car (last (runtime-p-raw-mul x y p)))
                  (car x)))
  :hints (("Goal"
           :use ((:instance runtime-p-last-of-raw-scale-experiment
                            (a (car x)) (xs y))
                 (:instance runtime-p-coefficient-fix-when-recognized
                            (x (car x))))
           :in-theory (enable runtime-p-raw-mul
                              runtime-p-raw-add
                              runtime-p-coefficient-list-p
                              runtime-p-mul-one-right))))

(defthm runtime-p-raw-mul-of-consp-experiment
  ; RUNTIME-P-RAW-MUL is nil when either operand is atomic, so the proposed
  ; X-only hypothesis would be false for atomic Y.
  (implies (and (consp x) (consp y))
           (equal (runtime-p-raw-mul x y p)
                  (runtime-p-raw-add
                   (runtime-p-raw-scale (car x) y p)
                   (cons 0 (runtime-p-raw-mul (cdr x) y p)) p)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable runtime-p-raw-mul))))

; First uncertified target: the non-inductive recursive-step lemma.  Earlier
; attempts expanded the singleton raw product into a zero-list checkpoint;
; the next proof must keep RUNTIME-P-RAW-MUL disabled and use the one-step
; equation above only in the recursive case.
