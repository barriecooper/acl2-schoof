(in-package "GPOLY")

(include-book "runtime-p-polynomial-algebra")
(local (include-book "arithmetic-5/top" :dir :system))

; A monomial is represented in ascending coefficient order.  Fixing the
; coefficient before constructing the zero prefix makes zero collapse to the
; unique canonical zero polynomial, independently of the exponent.
(defun runtime-p-poly-monomial (a n p)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((a (runtime-p-coefficient-fix a p)))
    (cond ((equal a (runtime-p-zero p)) nil)
          ((zp (nfix n)) (list a))
          (t (cons (runtime-p-zero p)
                   (runtime-p-poly-monomial a (1- (nfix n)) p))))))

; Degree and leading coefficient are structural observations of the normalized
; dense representation.  In particular, they do not use evaluation semantics.
(defun runtime-p-poly-degree (poly p)
  (declare (xargs :guard t))
  (let ((poly (runtime-p-normalize poly p)))
    (if (consp poly) (1- (len poly)) -1)))

(defun runtime-p-poly-leading-coefficient (poly p)
  (declare (xargs :guard t))
  (let ((poly (runtime-p-normalize poly p)))
    (if (consp poly) (car (last poly)) (runtime-p-zero p))))

(defthm runtime-p-coefficient-list-p-of-poly-monomial
  (runtime-p-coefficient-list-p (runtime-p-poly-monomial a n p) p)
  :hints (("Goal" :induct (runtime-p-poly-monomial a n p)
           :in-theory (enable runtime-p-poly-monomial
                              runtime-p-coefficient-list-p))))

(defthm runtime-p-poly-monomial-nonzero-iff
  (equal (consp (runtime-p-poly-monomial a n p))
         (not (equal (runtime-p-coefficient-fix a p)
                     (runtime-p-zero p))))
  :hints (("Goal" :in-theory (enable runtime-p-poly-monomial))))

(local (defthm integerp-of-runtime-p-coefficient-fix-for-monomial
  (integerp (runtime-p-coefficient-fix a p))
  :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance runtime-p-coefficient-fix-bounds
                                   (x a)))))))

(defthm runtime-p-poly-monomial-last-when-nonzero
  (implies (not (equal (runtime-p-coefficient-fix a p)
                       (runtime-p-zero p)))
           (equal (car (last (runtime-p-poly-monomial a n p)))
                  (runtime-p-coefficient-fix a p)))
  :hints (("Goal" :induct (runtime-p-poly-monomial a n p)
           :in-theory (enable runtime-p-poly-monomial))))

(defthm runtime-p-canonical-polynomial-p-of-poly-monomial
  (runtime-p-canonical-polynomial-p
   (runtime-p-poly-monomial a n p) p)
  :hints (("Goal"
           :use ((:instance runtime-p-poly-monomial-last-when-nonzero))
           :in-theory (enable runtime-p-canonical-polynomial-p))))

(defthm runtime-p-normalize-of-poly-monomial
  (equal (runtime-p-normalize (runtime-p-poly-monomial a n p) p)
         (runtime-p-poly-monomial a n p)))

(defthm runtime-p-poly-monomial-when-fixed-zero
  (implies (equal (runtime-p-coefficient-fix a p) (runtime-p-zero p))
           (equal (runtime-p-poly-monomial a n p) nil))
  :hints (("Goal" :in-theory (enable runtime-p-poly-monomial))))

(defthm runtime-p-poly-monomial-of-nfix
  (equal (runtime-p-poly-monomial a (nfix n) p)
         (runtime-p-poly-monomial a n p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-monomial))))

(defthm len-of-runtime-p-poly-monomial
  (implies (not (equal (runtime-p-coefficient-fix a p)
                       (runtime-p-zero p)))
           (equal (len (runtime-p-poly-monomial a n p))
                  (+ 1 (nfix n))))
  :rule-classes nil
  :hints (("Goal" :induct (runtime-p-poly-monomial a n p)
           :in-theory (enable runtime-p-poly-monomial))))

(defthm runtime-p-poly-degree-of-nil
  (equal (runtime-p-poly-degree nil p) -1)
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree))))

(defthm runtime-p-poly-leading-coefficient-of-nil
  (equal (runtime-p-poly-leading-coefficient nil p) (runtime-p-zero p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-leading-coefficient))))

(defthm runtime-p-poly-degree-of-normalize
  (equal (runtime-p-poly-degree (runtime-p-normalize poly p) p)
         (runtime-p-poly-degree poly p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree))))

(defthm runtime-p-poly-leading-coefficient-of-normalize
  (equal (runtime-p-poly-leading-coefficient
          (runtime-p-normalize poly p) p)
         (runtime-p-poly-leading-coefficient poly p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-leading-coefficient))))

(defthm runtime-p-poly-degree-when-canonical-nonzero
  (implies (and (runtime-p-canonical-polynomial-p poly p) (consp poly))
           (equal (runtime-p-poly-degree poly p) (1- (len poly))))
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree))))

(defthm runtime-p-poly-leading-coefficient-when-canonical-nonzero
  (implies (and (runtime-p-canonical-polynomial-p poly p) (consp poly))
           (equal (runtime-p-poly-leading-coefficient poly p)
                  (car (last poly))))
  :hints (("Goal" :in-theory (enable runtime-p-poly-leading-coefficient))))

(defthm integerp-of-runtime-p-poly-degree
  (integerp (runtime-p-poly-degree poly p))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree))))

(defthm runtime-p-poly-degree-lower-bound
  (<= -1 (runtime-p-poly-degree poly p))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree))))

(defthm natp-of-runtime-p-poly-degree-when-normalize-nonzero
  (implies (consp (runtime-p-normalize poly p))
           (natp (runtime-p-poly-degree poly p)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree))))

(defthm runtime-p-poly-degree-equal-minus-one
  (equal (equal (runtime-p-poly-degree poly p) -1)
         (equal (runtime-p-normalize poly p) nil))
  :hints (("Goal" :in-theory (enable runtime-p-poly-degree))))

(local (defthm runtime-p-coefficient-p-of-last-when-coefficient-list-p
  (implies (and (runtime-p-coefficient-list-p xs p) (consp xs))
           (runtime-p-coefficient-p (car (last xs)) p))
  :hints (("Goal" :induct (runtime-p-coefficient-list-p xs p)
           :in-theory (enable runtime-p-coefficient-list-p)))))

(defthm runtime-p-coefficient-p-of-poly-leading-coefficient
  (runtime-p-coefficient-p (runtime-p-poly-leading-coefficient poly p) p)
  :hints (("Goal"
           :use ((:instance runtime-p-canonical-polynomial-p-of-normalize
                            (xs poly))
                 (:instance runtime-p-coefficient-p-of-last-when-coefficient-list-p
                            (xs (runtime-p-normalize poly p))))
           :in-theory (enable runtime-p-poly-leading-coefficient
                              runtime-p-canonical-polynomial-p
                              runtime-p-coefficient-list-p))))

(defthm runtime-p-poly-leading-coefficient-equal-zero
  (equal (equal (runtime-p-poly-leading-coefficient poly p)
                (runtime-p-zero p))
         (equal (runtime-p-normalize poly p) nil))
  :hints (("Goal"
           :use ((:instance runtime-p-consp-of-trim-implies-last-nonzero
                            (xs (runtime-p-fix-coefficients poly p))))
           :in-theory (enable runtime-p-poly-leading-coefficient
                              runtime-p-normalize))))

(defthm runtime-p-poly-degree-of-poly-monomial
  (implies (not (equal (runtime-p-coefficient-fix a p)
                       (runtime-p-zero p)))
           (equal (runtime-p-poly-degree
                   (runtime-p-poly-monomial a n p) p)
                  (nfix n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance len-of-runtime-p-poly-monomial)
                 (:instance runtime-p-poly-degree-when-canonical-nonzero
                            (poly (runtime-p-poly-monomial a n p)))))))

(defthm runtime-p-poly-leading-coefficient-of-poly-monomial
  (implies (not (equal (runtime-p-coefficient-fix a p)
                       (runtime-p-zero p)))
           (equal (runtime-p-poly-leading-coefficient
                   (runtime-p-poly-monomial a n p) p)
                  (runtime-p-coefficient-fix a p)))
  :hints (("Goal"
           :use ((:instance runtime-p-poly-monomial-last-when-nonzero)
                 (:instance runtime-p-poly-leading-coefficient-when-canonical-nonzero
                            (poly (runtime-p-poly-monomial a n p)))))))

(defthm runtime-p-poly-monomial-one-zero
  (equal (runtime-p-poly-monomial (runtime-p-one p) 0 p)
         (runtime-p-polynomial-one p))
  :hints (("Goal" :in-theory (enable runtime-p-poly-monomial
                                     runtime-p-polynomial-one))))

(verify-guards runtime-p-poly-monomial)
(verify-guards runtime-p-poly-degree)
(verify-guards runtime-p-poly-leading-coefficient)
