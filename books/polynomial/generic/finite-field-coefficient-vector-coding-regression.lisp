(in-package "GPOLY")

(include-book "finite-field-coefficient-vector-coding")
(include-book "f7-division")

(defthm finite-field-coefficient-vector-unrank-rank-minimal-theory-client
  (implies (and (natp width)
                (finite-field-coefficient-list-p coefficients)
                (equal (len coefficients) (nfix width)))
           (equal (finite-field-coefficient-vector-unrank
                   width
                   (finite-field-coefficient-vector-rank coefficients))
                  coefficients))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-coefficient-vector-unrank-of-rank)))

(defthm finite-field-coefficient-vector-rank-unrank-minimal-theory-client
  (implies (and (natp k)
                (< k (finite-field-coefficient-vector-coding-bound width)))
           (equal (finite-field-coefficient-vector-rank
                   (finite-field-coefficient-vector-unrank width k))
                  k))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-coefficient-vector-rank-of-unrank)))

(defthm finite-field-coefficient-vector-rank-bound-minimal-theory-client
  (implies (and (natp width)
                (finite-field-coefficient-list-p coefficients)
                (equal (len coefficients) (nfix width)))
           (< (finite-field-coefficient-vector-rank coefficients)
              (finite-field-coefficient-vector-coding-bound width)))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use finite-field-coefficient-vector-rank-upper-bound)))

(defun f7-coefficient-vector-coding-bound (width)
  (expt 7 (nfix width)))

(defun f7-coefficient-vector-rank (coefficients)
  (if (consp coefficients)
      (+ (gfield::f7-fix (car coefficients))
         (* 7 (f7-coefficient-vector-rank (cdr coefficients))))
    0))

(defun f7-coefficient-vector-unrank (width k)
  (if (zp (nfix width))
      nil
    (cons (gfield::f7-fix (mod (nfix k) 7))
          (f7-coefficient-vector-unrank (1- (nfix width))
                                       (floor (nfix k) 7)))))

(assert-event
 (and (equal (f7-coefficient-vector-coding-bound 0) 1)
      (equal (f7-coefficient-vector-rank nil) 0)
      (equal (f7-coefficient-vector-unrank 0 0) nil)
      (equal (f7-coefficient-vector-unrank 0 100) nil)
      (equal (f7-coefficient-vector-rank '(0 0)) 0)
      (equal (f7-coefficient-vector-rank '(3 4)) 31)
      (equal (f7-coefficient-vector-rank '(0 4)) 28)
      (equal (f7-coefficient-vector-rank '(3 0)) 3)
      (equal (f7-coefficient-vector-rank '(bad 9)) 14)
      (equal (f7-coefficient-vector-unrank 2 0) '(0 0))
      (equal (f7-coefficient-vector-unrank 2 31) '(3 4))
      (equal (f7-coefficient-vector-unrank 2 48) '(6 6))
      (equal (f7-coefficient-vector-unrank 2 'bad) '(0 0))
      (equal (f7-coefficient-vector-rank (f7-coefficient-vector-unrank 2 48)) 48)
      (equal (f7-coefficient-vector-unrank
              2 (f7-coefficient-vector-rank '(0 4)))
             '(0 4))))

(verify-guards f7-coefficient-vector-coding-bound)
(verify-guards f7-coefficient-vector-rank)
(verify-guards f7-coefficient-vector-unrank)
