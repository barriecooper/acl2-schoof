(in-package "GPOLY")
(include-book "f11-division-polynomial")

(defconst *f11-golden-division-polynomial-5*
  '(10 2 0 2 0 4 3 10 5 3 7 0 5))
(defconst *f11-golden-division-polynomial-6*
  '(4 0 1 0 8 0 9 9 8 0 9 0 10 6 6 0 3))
(defconst *f11-golden-division-polynomial-7*
  '(7 5 5 3 9 2 2 0 10 2 3 0 10 10 0 9 1 4 4 10 5 3 0 0 7))

(assert-event (equal (f11-division-polynomial 5 1 6)
                     *f11-golden-division-polynomial-5*))
(assert-event (equal (f11-division-polynomial 6 1 6)
                     *f11-golden-division-polynomial-6*))
(assert-event (equal (f11-division-polynomial 7 1 6)
                     *f11-golden-division-polynomial-7*))
(assert-event
 (equal (list (f11-division-polynomial 5 12 17)
              (f11-division-polynomial 6 12 17)
              (f11-division-polynomial 7 12 17))
        (list *f11-golden-division-polynomial-5*
              *f11-golden-division-polynomial-6*
              *f11-golden-division-polynomial-7*)))
(assert-event (equal (f11-division-polynomial 'malformed 1 6) nil))
(assert-event
 (let ((table (f11-division-polynomial-table 7 1 6)))
   (and (equal (len table) 8)
        (equal (nth 5 table) *f11-golden-division-polynomial-5*)
        (equal (nth 6 table) *f11-golden-division-polynomial-6*)
        (equal (nth 7 table) (f11-division-polynomial 7 1 6)))))
