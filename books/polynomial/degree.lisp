(in-package "HS")
(include-book "eval")

; NIL is the unique canonical zero polynomial.  POLY-ZEROP also recognizes
; noncanonical coefficient lists whose redundant high zeroes normalize away.
(defun poly-zerop (poly)
  (equal (poly-normalize poly) nil))

(defun poly-nonzero-p (poly)
  (not (poly-zerop poly)))

; Degree -1 is an explicit sentinel for the zero polynomial, not an ordinary
; nonnegative degree.  Every mathematical degree theorem below assumes that
; the polynomial is nonzero.  Coefficients are stored constant first.
(defun poly-degree (poly)
  (if (endp poly) -1 (1- (len poly))))

; The leading coefficient is the last (highest-degree) coefficient.  Its value
; on NIL is conventionally 0.
(defun poly-leading-coefficient (poly)
  (if (consp poly)
      (if (consp (cdr poly))
          (poly-leading-coefficient (cdr poly))
        (car poly))
    0))

(defthm canonical-zero-polynomial-is-nil
  (implies (and (canonical-polynomial-p poly p)
                (poly-zerop poly))
           (equal poly nil))
  :rule-classes nil)

(defthm canonical-poly-zerop
  (implies (canonical-polynomial-p poly p)
           (iff (poly-zerop poly)
                (equal poly nil))))

(defthm canonical-poly-nonzero-p
  (implies (canonical-polynomial-p poly p)
           (iff (poly-nonzero-p poly)
                (consp poly))))

(defthm positive-len-when-canonical-nonzero
  (implies (and (canonical-polynomial-p poly p)
                (poly-nonzero-p poly))
           (< 0 (len poly)))
  :rule-classes :linear)

(defthm poly-degree-of-nil
  (equal (poly-degree nil) -1))

(defthm poly-degree-is-final-index
  (implies (consp poly)
           (equal (poly-degree poly)
                  (1- (len poly)))))

(defthm len-is-poly-degree-plus-one
  (implies (and (canonical-polynomial-p poly p)
                (poly-nonzero-p poly))
           (equal (len poly)
                  (+ 1 (poly-degree poly)))))

(defthm poly-leading-coefficient-is-last
  (implies (consp poly)
           (equal (poly-leading-coefficient poly)
                  (car (last poly)))))

(defthm fep-of-poly-leading-coefficient
  (implies (and (canonical-polynomial-p poly p)
                (poly-nonzero-p poly))
           (pfield::fep (poly-leading-coefficient poly) p)))

(defthm poly-leading-coefficient-nonzero
  (implies (and (canonical-polynomial-p poly p)
                (poly-nonzero-p poly))
           (not (equal (poly-leading-coefficient poly) 0))))

(defthm fep-of-final-coefficient
  (implies (and (canonical-polynomial-p poly p)
                (poly-nonzero-p poly))
           (pfield::fep (car (last poly)) p)))

(defthm final-coefficient-nonzero
  (implies (and (canonical-polynomial-p poly p)
                (poly-nonzero-p poly))
           (not (equal (car (last poly)) 0))))

(defthm final-coefficient-nonzero-modulus
  (implies (and (canonical-polynomial-p poly p)
                (poly-nonzero-p poly))
           (not (equal (mod (car (last poly)) p) 0)))
  :hints (("Goal" :in-theory (enable pfield::fep))))

(defthm poly-normalize-zerop-iff
  (iff (equal (poly-normalize poly) nil)
       (poly-zerop poly))
  :rule-classes nil)

(defthm degree-of-nonzero-poly-normalize
  (implies (and (field-polynomial-p poly p)
                (poly-nonzero-p poly))
           (equal (poly-degree (poly-normalize poly))
                  (1- (len (poly-normalize poly)))))
  :hints (("Goal" :in-theory (disable len-is-poly-degree-plus-one))))

(defthm leading-coefficient-of-nonzero-poly-normalize
  (implies (and (field-polynomial-p poly p)
                (poly-nonzero-p poly))
           (equal (poly-leading-coefficient (poly-normalize poly))
                  (car (last (poly-normalize poly))))))

(defthm degree-normalize-bound
  (<= (poly-degree (poly-normalize poly)) (poly-degree poly))
  :rule-classes :linear)
