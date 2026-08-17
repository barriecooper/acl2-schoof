(in-package "GPOLY")
(include-book "runtime-p-monic-product-leading-term")
; Certified, deliberately unregistered checkpoint.  This book proves the
; intended arbitrary-multiplier theorem but has not yet been refactored into
; the production book without causing unacceptable certification cost.
; Arbitrary canonical multipliers: monicity prevents loss of the top term
; even over composite effective coefficient moduli.
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

(defthm consp-of-runtime-p-raw-mul-experiment
  (equal (consp (runtime-p-raw-mul x y p))
         (and (consp x) (consp y)))
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable runtime-p-raw-mul))))

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

(defthm runtime-p-coefficient-list-p-of-raw-mul-experiment
  (runtime-p-coefficient-list-p (runtime-p-raw-mul x y p) p)
  :hints (("Goal" :induct (runtime-p-raw-mul x y p)
           :in-theory (enable runtime-p-raw-mul
                              runtime-p-coefficient-list-p))))

(defthm true-listp-when-runtime-p-coefficient-list-p-experiment
  (implies (runtime-p-coefficient-list-p x p)
           (true-listp x))
  :hints (("Goal" :induct (runtime-p-coefficient-list-p x p)
           :in-theory (enable runtime-p-coefficient-list-p))))

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

(defthm runtime-p-last-of-cdr-when-cdr-consp-experiment
  (implies (consp (cdr x))
           (equal (car (last x))
                  (car (last (cdr x)))))
  :hints (("Goal" :in-theory (enable last))))

(defthm runtime-p-raw-mul-last-by-monic-step-experiment
  (implies
   (and (runtime-p-coefficient-list-p x p)
        (consp (cdr x))
        (runtime-p-coefficient-list-p y p)
        (consp y)
        (equal (car (last y)) (runtime-p-one p))
        (equal (car (last (runtime-p-raw-mul (cdr x) y p)))
               (car (last (cdr x)))))
   (equal (car (last (runtime-p-raw-mul x y p)))
          (car (last x))))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance runtime-p-raw-mul-of-consp-experiment)
          (:instance runtime-p-strict-length-of-shifted-raw-product-experiment
                     (x (cdr x)))
          (:instance runtime-p-last-of-raw-add-when-right-longer-experiment
                     (left (runtime-p-raw-scale (car x) y p))
                     (right (cons 0
                                  (runtime-p-raw-mul (cdr x) y p))))
          (:instance runtime-p-coefficient-list-p-of-raw-scale-experiment
                     (a (car x)) (xs y))
          (:instance runtime-p-coefficient-list-p-of-raw-mul-experiment
                     (x (cdr x)))
          (:instance true-listp-when-runtime-p-coefficient-list-p-experiment
                     (x (cdr x)))
          (:instance true-listp-when-runtime-p-coefficient-list-p-experiment
                     (x y))
          (:instance runtime-p-last-of-cdr-when-cdr-consp-experiment))
    :in-theory (disable runtime-p-raw-mul runtime-p-raw-add
                        runtime-p-raw-scale runtime-p-fix-coefficients
                        runtime-p-coefficient-fix runtime-p-effective-modulus
                        runtime-p-normalize))))

(defun runtime-p-raw-mul-last-induct-experiment (x)
  (if (consp (cdr x))
      (runtime-p-raw-mul-last-induct-experiment (cdr x))
    x))

(defthm runtime-p-last-of-singleton-experiment
  (implies (and (consp x) (not (consp (cdr x))))
           (equal (car (last x)) (car x)))
  :hints (("Goal" :in-theory (enable last))))

(defthm runtime-p-raw-mul-last-by-monic-experiment
  (implies (and (runtime-p-coefficient-list-p x p)
                (consp x)
                (runtime-p-coefficient-list-p y p)
                (consp y)
                (equal (car (last y)) (runtime-p-one p)))
           (equal (car (last (runtime-p-raw-mul x y p)))
                  (car (last x))))
  :rule-classes nil
  :hints (("Goal"
           :induct (runtime-p-raw-mul-last-induct-experiment x)
           :in-theory (union-theories
                       '(runtime-p-raw-mul-last-induct-experiment
                         runtime-p-coefficient-list-p)
                       (theory 'minimal-theory)))
          ("Subgoal *1/2"
           :use ((:instance
                  runtime-p-raw-mul-last-by-monic-singleton-experiment)
                 (:instance runtime-p-last-of-singleton-experiment)))
          ("Subgoal *1/1"
           :use ((:instance
                  runtime-p-raw-mul-last-by-monic-step-experiment)))))

(defthm runtime-p-raw-product-canonical-when-right-monic-experiment
  (implies (and (runtime-p-canonical-polynomial-p x p)
                (consp x)
                (runtime-p-canonical-polynomial-p y p)
                (consp y)
                (equal (car (last y)) (runtime-p-one p)))
           (runtime-p-canonical-polynomial-p
            (runtime-p-raw-mul x y p) p))
  :hints (("Goal"
           :use ((:instance runtime-p-raw-mul-last-by-monic-experiment)
                 (:instance runtime-p-coefficient-list-p-of-raw-mul-experiment))
           :in-theory (enable runtime-p-canonical-polynomial-p))))



(defthm runtime-p-poly-mul-nonzero-by-monic-properties
  (implies
   (and (runtime-p-canonical-polynomial-p multiplier p)
        (consp multiplier)
        (equal (runtime-p-poly-leading-coefficient divisor p)
               (runtime-p-one p)))
   (let ((product (runtime-p-poly-mul multiplier divisor p)))
     (and (runtime-p-canonical-polynomial-p product p)
          (consp product)
          (equal (runtime-p-poly-degree product p)
                 (+ (runtime-p-poly-degree multiplier p)
                    (runtime-p-poly-degree divisor p)))
          (equal (runtime-p-poly-leading-coefficient product p)
                 (runtime-p-poly-leading-coefficient multiplier p))
          (equal (len product)
                 (+ -1 (len multiplier)
                    (len (runtime-p-normalize divisor p)))))))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance runtime-p-raw-product-canonical-when-right-monic-experiment
                     (x multiplier)
                     (y (runtime-p-normalize divisor p)))
          (:instance runtime-p-len-of-raw-mul-for-monic-product-experiment
                     (x multiplier)
                     (y (runtime-p-normalize divisor p)))
          (:instance runtime-p-raw-mul-last-by-monic-experiment
                     (x multiplier)
                     (y (runtime-p-normalize divisor p)))
          (:instance consp-of-runtime-p-raw-mul-experiment
                     (x multiplier)
                     (y (runtime-p-normalize divisor p))))
    :in-theory (enable runtime-p-poly-mul runtime-p-poly-degree
                       runtime-p-poly-leading-coefficient
                       runtime-p-canonical-polynomial-p))))


(defthm runtime-p-poly-mul-nonzero-by-monic
  (implies (and (runtime-p-canonical-polynomial-p multiplier p)
                (consp multiplier)
                (equal (runtime-p-poly-leading-coefficient divisor p)
                       (runtime-p-one p)))
           (consp (runtime-p-poly-mul multiplier divisor p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          runtime-p-poly-mul-nonzero-by-monic-properties)))))

(defthm runtime-p-poly-mul-by-monic-degree-lower-bound
  (implies (and (runtime-p-canonical-polynomial-p multiplier p)
                (consp multiplier)
                (equal (runtime-p-poly-leading-coefficient divisor p)
                       (runtime-p-one p)))
           (<= (runtime-p-poly-degree divisor p)
               (runtime-p-poly-degree
                (runtime-p-poly-mul multiplier divisor p) p)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance
                          runtime-p-poly-mul-nonzero-by-monic-properties)))))
