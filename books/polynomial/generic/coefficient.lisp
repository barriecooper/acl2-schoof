(in-package "GPOLY")
(include-book "base")

(defun poly-coefficient (n polynomial)
  (declare (xargs :measure (nfix n)))
  (if (zp (nfix n))
      (if (consp polynomial)
          (gfield::field-fix (car polynomial))
        (gfield::field-zero))
    (poly-coefficient
     (1- (nfix n))
     (if (consp polynomial) (cdr polynomial) nil))))

(defthm field-element-p-of-poly-coefficient
  (gfield::field-element-p (poly-coefficient n polynomial)))

(defthm poly-coefficient-of-nfix
  (equal (poly-coefficient (nfix n) polynomial)
         (poly-coefficient n polynomial)))

(defthm poly-coefficient-when-atom
  (implies (not (consp polynomial))
           (equal (poly-coefficient n polynomial)
                  (gfield::field-zero))))

(defthm poly-coefficient-of-cons-zero
  (equal (poly-coefficient 0 (cons coefficient polynomial))
         (gfield::field-fix coefficient)))

(defthm poly-coefficient-of-cons-successor
  (equal (poly-coefficient (+ 1 (nfix n))
                           (cons coefficient polynomial))
         (poly-coefficient n polynomial)))

(defthm poly-coefficient-of-successor
  (equal (poly-coefficient (+ 1 (nfix n)) polynomial)
         (poly-coefficient n
                           (if (consp polynomial)
                               (cdr polynomial)
                             nil))))

(defthm poly-coefficient-when-index-at-least-len
  (implies (<= (len polynomial) (nfix n))
           (equal (poly-coefficient n polynomial)
                  (gfield::field-zero))))

(defthm poly-coefficient-of-fix-coefficients
  (equal (poly-coefficient n (fix-coefficients polynomial))
         (poly-coefficient n polynomial)))

(local
 (defthm poly-coefficient-of-trim-trailing-zeros
   (equal (poly-coefficient n (trim-trailing-zeros polynomial))
          (poly-coefficient n polynomial))))

(defthm poly-coefficient-of-normalize
  (equal (poly-coefficient n (normalize polynomial))
         (poly-coefficient n polynomial))
  :hints (("Goal" :in-theory (enable normalize))))

(verify-guards poly-coefficient)

(defun same-polynomial-coefficients-p (count first second)
  (if (zp (nfix count))
      t
    (and (equal (poly-coefficient 0 first)
                (poly-coefficient 0 second))
         (same-polynomial-coefficients-p
          (1- (nfix count))
          (if (consp first) (cdr first) nil)
          (if (consp second) (cdr second) nil)))))

(defthm same-polynomial-coefficients-p-of-zero
  (same-polynomial-coefficients-p 0 first second))

(defthm same-polynomial-coefficients-p-of-successor
  (equal (same-polynomial-coefficients-p (+ 1 (nfix count)) first second)
         (and (equal (poly-coefficient 0 first)
                     (poly-coefficient 0 second))
              (same-polynomial-coefficients-p
               count
               (if (consp first) (cdr first) nil)
               (if (consp second) (cdr second) nil)))))

(defthm same-polynomial-coefficients-p-reflexive
  (same-polynomial-coefficients-p count polynomial polynomial))

(verify-guards same-polynomial-coefficients-p)

(local
 (defthm same-polynomial-coefficients-p-symmetric
   (equal (same-polynomial-coefficients-p count first second)
          (same-polynomial-coefficients-p count second first))
   :hints (("Goal" :induct (same-polynomial-coefficients-p count first second)
            :in-theory (enable same-polynomial-coefficients-p)))))

(local
 (defthm decrement-preserves-strict-less-than
   (implies (and (natp count) (natp n) (< 0 n) (< n count))
            (< (1- n) (1- count)))))

(local
 (defun coefficient-projection-induction (count n first second)
   (declare (xargs :measure (nfix n)))
   (if (and (posp count) (posp n))
       (coefficient-projection-induction
        (1- count) (1- n)
        (if (consp first) (cdr first) nil)
        (if (consp second) (cdr second) nil))
     (list count n first second))))

(local
 (defthm poly-coefficient-of-positive-natural
   (implies (and (natp n) (< 0 n))
            (equal (poly-coefficient n polynomial)
                   (poly-coefficient
                    (1- n)
                    (if (consp polynomial) (cdr polynomial) nil))))
   :hints (("Goal" :use ((:instance poly-coefficient-of-successor
                                    (n (1- n))))
            :in-theory (disable poly-coefficient)))))

(local
 (defthm agreement-of-positive-natural
   (implies (and (natp count) (< 0 count))
            (equal (same-polynomial-coefficients-p count first second)
                   (and (equal (poly-coefficient 0 first)
                               (poly-coefficient 0 second))
                        (same-polynomial-coefficients-p
                         (1- count)
                         (if (consp first) (cdr first) nil)
                         (if (consp second) (cdr second) nil)))))
   :hints (("Goal" :use ((:instance
                           same-polynomial-coefficients-p-of-successor
                           (count (1- count))))
            :in-theory (disable same-polynomial-coefficients-p)))))

(defthm poly-coefficient-equal-when-same-polynomial-coefficients-p
  (implies (and (natp count)
                (natp n)
                (same-polynomial-coefficients-p count first second)
                (< n count))
           (equal (poly-coefficient n first)
                  (poly-coefficient n second)))
  :hints
  (("Goal"
    :induct (coefficient-projection-induction count n first second)
    :in-theory (disable poly-coefficient same-polynomial-coefficients-p
                        normalize trim-trailing-zeros fix-coefficients
                        canonical-polynomial-p))))

(local
 (defun coefficient-list-pair-induction (first second)
   (if (and (consp first) (consp second))
       (coefficient-list-pair-induction (cdr first) (cdr second))
     (list first second))))

(defthm coefficient-list-extensionality-equal-length
  (implies (and (coefficient-list-p first)
                (coefficient-list-p second)
                (equal (len first) (len second))
                (same-polynomial-coefficients-p (len first) first second))
           (equal first second))
  :rule-classes nil
  :hints
  (("Goal"
    :induct (coefficient-list-pair-induction first second)
    :in-theory (disable canonical-polynomial-p last max normalize
                        trim-trailing-zeros poly-coefficient))))

(local
 (defthm canonical-polynomial-p-implies-coefficient-list-p
   (implies (canonical-polynomial-p polynomial)
            (coefficient-list-p polynomial))
   :hints (("Goal" :in-theory (enable canonical-polynomial-p)))))

(defthm canonical-polynomial-extensionality-equal-length
  (implies (and (canonical-polynomial-p first)
                (canonical-polynomial-p second)
                (equal (len first) (len second))
                (same-polynomial-coefficients-p (len first) first second))
           (equal first second))
  :rule-classes nil
  :hints (("Goal" :use coefficient-list-extensionality-equal-length
           :in-theory (disable canonical-polynomial-p))))

(local
 (defthm poly-coefficient-at-cons-tail-length
   (implies (consp tail)
            (equal (poly-coefficient (len tail) (cons coefficient tail))
                   (poly-coefficient (1- (len tail)) tail)))
   :hints (("Goal"
            :use ((:instance poly-coefficient-of-successor
                             (n (1- (len tail)))
                             (polynomial (cons coefficient tail))))
            :in-theory (disable poly-coefficient)))))

(defthm poly-coefficient-of-final-index
  (implies (and (coefficient-list-p polynomial)
                (consp polynomial))
           (equal (poly-coefficient (1- (len polynomial)) polynomial)
                  (car (last polynomial))))
  :rule-classes nil
  :hints (("Goal" :induct (coefficient-list-p polynomial)
           :in-theory (disable poly-coefficient))))

(local
 (defthm last-coefficient-nonzero-when-canonical
   (implies (and (canonical-polynomial-p polynomial)
                 (consp polynomial))
            (not (equal (car (last polynomial))
                        (gfield::field-zero))))
   :hints (("Goal" :in-theory (enable canonical-polynomial-p)))))

(defthm poly-coefficient-of-final-index-nonzero-when-canonical
  (implies (and (canonical-polynomial-p polynomial)
                (consp polynomial))
           (not (equal (poly-coefficient (1- (len polynomial)) polynomial)
                       (gfield::field-zero))))
  :rule-classes nil
  :hints (("Goal"
           :use (poly-coefficient-of-final-index
                 last-coefficient-nonzero-when-canonical)
           :in-theory (disable canonical-polynomial-p poly-coefficient last))))

(local
 (defthm shorter-length-index-at-least-first
   (implies (< (len first) (len second))
            (<= (len first) (1- (len second))))))

(local
 (defthm final-index-below-length-when-consp
   (implies (consp polynomial)
            (< (1- (len polynomial)) (len polynomial)))))

(local
 (defthm max-length-when-first-shorter
   (implies (< (len first) (len second))
            (equal (max (len first) (len second)) (len second)))))

(local
 (defthm final-coefficients-equal-when-first-shorter
   (implies
    (and (< (len first) (len second))
         (same-polynomial-coefficients-p
          (max (len first) (len second)) first second))
    (equal (poly-coefficient (1- (len second)) first)
           (poly-coefficient (1- (len second)) second)))
   :hints
   (("Goal"
     :use ((:instance poly-coefficient-equal-when-same-polynomial-coefficients-p
                      (count (max (len first) (len second)))
                      (n (1- (len second)))))
     :in-theory (disable poly-coefficient same-polynomial-coefficients-p
                         max canonical-polynomial-p
                         poly-coefficient-equal-when-same-polynomial-coefficients-p
                         agreement-of-positive-natural
                         poly-coefficient-of-positive-natural
                         same-polynomial-coefficients-p-of-successor
                         poly-coefficient-of-successor
                         poly-coefficient-of-cons-successor)))))

(local
 (defthm final-coefficient-zero-when-first-shorter
   (implies (< (len first) (len second))
            (equal (poly-coefficient (1- (len second)) first)
                   (gfield::field-zero)))
   :hints (("Goal"
            :use ((:instance poly-coefficient-when-index-at-least-len
                             (polynomial first) (n (1- (len second)))))
            :in-theory (disable poly-coefficient
                                poly-coefficient-when-index-at-least-len)))))

(local
 (defthm final-coefficient-nonzero-when-second-longer
   (implies (and (canonical-polynomial-p second)
                 (< (len first) (len second)))
            (not (equal (poly-coefficient (1- (len second)) second)
                        (gfield::field-zero))))
   :hints (("Goal"
            :use ((:instance
                    poly-coefficient-of-final-index-nonzero-when-canonical
                    (polynomial second)))
            :in-theory (disable canonical-polynomial-p poly-coefficient)))))

(local
 (defthm not-shorter-when-canonical-and-agree
   (implies
    (and (canonical-polynomial-p first)
         (canonical-polynomial-p second)
         (same-polynomial-coefficients-p
          (max (len first) (len second)) first second))
    (not (< (len first) (len second))))
   :hints
   (("Goal"
     :use (final-coefficients-equal-when-first-shorter
           final-coefficient-zero-when-first-shorter
           final-coefficient-nonzero-when-second-longer)
     :in-theory (disable poly-coefficient same-polynomial-coefficients-p
                         canonical-polynomial-p normalize trim-trailing-zeros
                         fix-coefficients last max
                         poly-coefficient-of-successor
                         poly-coefficient-of-cons-successor
                         poly-coefficient-of-positive-natural
                         agreement-of-positive-natural
                         same-polynomial-coefficients-p-of-successor
                         final-coefficients-equal-when-first-shorter
                         final-coefficient-zero-when-first-shorter
                         final-coefficient-nonzero-when-second-longer)))))

(defthm canonical-polynomials-have-equal-length-from-coefficient-agreement
  (implies
   (and (canonical-polynomial-p first)
        (canonical-polynomial-p second)
        (same-polynomial-coefficients-p
         (max (len first) (len second)) first second))
   (equal (len first) (len second)))
  :rule-classes nil
  :hints (("Goal"
           :use (not-shorter-when-canonical-and-agree
                 (:instance same-polynomial-coefficients-p-symmetric
                            (count (max (len first) (len second))))
                 (:instance not-shorter-when-canonical-and-agree
                            (first second) (second first)))
           :in-theory (disable canonical-polynomial-p
                               same-polynomial-coefficients-p
                               same-polynomial-coefficients-p-symmetric
                               not-shorter-when-canonical-and-agree))))

(local
 (defthm max-of-equal-arguments
   (equal (max value value) value)))

(defthm canonical-polynomial-extensionality
  (implies
   (and (canonical-polynomial-p first)
        (canonical-polynomial-p second)
        (same-polynomial-coefficients-p
         (max (len first) (len second)) first second))
   (equal first second))
  :rule-classes nil
  :hints
  (("Goal"
    :use (canonical-polynomials-have-equal-length-from-coefficient-agreement
          (:instance canonical-polynomial-extensionality-equal-length))
    :in-theory (disable same-polynomial-coefficients-p canonical-polynomial-p
                        poly-coefficient max last))))
