(in-package "GPOLY")

(include-book "f7x2-frobenius-witness")

(defun f7x2-fixed-elements (values)
  (if (endp values)
      nil
    (if (equal (f7x2-conjugate (car values)) (f7x2-fix (car values)))
        (cons (car values) (f7x2-fixed-elements (cdr values)))
      (f7x2-fixed-elements (cdr values)))))

(defun f7x2-embedded-image-elements (values)
  (if (endp values)
      nil
    (if (f7x2-embedded-image-p (car values))
        (cons (car values) (f7x2-embedded-image-elements (cdr values)))
      (f7x2-embedded-image-elements (cdr values)))))

(defthm f7x2-frobenius-embedded-representatives-regression
  (and (equal (f7x2-conjugate (f7x2-embed-f7 0))
              (f7x2-embed-f7 0))
       (equal (f7x2-conjugate (f7x2-embed-f7 1))
              (f7x2-embed-f7 1))
       (equal (f7x2-conjugate (f7x2-embed-f7 2))
              (f7x2-embed-f7 2))
       (equal (f7x2-conjugate (f7x2-embed-f7 3))
              (f7x2-embed-f7 3))
       (equal (f7x2-conjugate (f7x2-embed-f7 4))
              (f7x2-embed-f7 4))
       (equal (f7x2-conjugate (f7x2-embed-f7 5))
              (f7x2-embed-f7 5))
       (equal (f7x2-conjugate (f7x2-embed-f7 6))
              (f7x2-embed-f7 6)))
  :rule-classes nil)

(defthm f7x2-frobenius-operation-regressions
  (and (equal (f7x2-base-projection (f7x2-embed-f7 -1)) 6)
       (equal (f7x2-embed-f7 (gfield::f7-add 3 6))
              (f7x2-add (f7x2-embed-f7 3) (f7x2-embed-f7 6)))
       (equal (f7x2-embed-f7 (gfield::f7-mul 3 5))
              (f7x2-mul (f7x2-embed-f7 3) (f7x2-embed-f7 5)))
       (equal (f7x2-conjugate '(0 1)) '(0 6))
       (equal (f7x2-conjugate '(3 2)) '(3 5))
       (not (f7x2-embedded-image-p '(3 2)))
       (f7x2-embedded-image-p '(3 0))
       (f7x2-embedded-image-p 'malformed)
       (equal (f7x2-conjugate '(8 1 . malformed-tail)) '(1 6))
       (equal (f7x2-conjugate '(1 1 0))
              (f7x2-conjugate '(1 1))))
  :rule-classes nil)

(defthm f7x2-fixed-elements-exact-regression
  (equal (f7x2-fixed-elements (f7x2-elements))
         '(nil (1) (2) (3) (4) (5) (6)))
  :rule-classes nil)

(defthm f7x2-fixed-elements-count-regression
  (equal (len (f7x2-fixed-elements (f7x2-elements))) 7)
  :rule-classes nil)

(defthm f7x2-carrier-fixed-point-image-agreement-regression
  (equal (f7x2-fixed-elements (f7x2-elements))
         (f7x2-embedded-image-elements (f7x2-elements)))
  :rule-classes nil)

