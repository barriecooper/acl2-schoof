(in-package "GFIELD")

(include-book "two-line-telescope")

(defthm field-two-line-telescope-client-regression
  (implies
   (and
    (equal (field-sub second-y first-y)
           (field-mul first-slope difference))
    (equal (field-add first-y second-y)
           (field-mul second-slope difference)))
   (equal
    (field-add first-y first-y)
    (field-mul
     (field-sub second-slope first-slope)
     difference)))
  :rule-classes nil
  :hints
  (("Goal"
    :use ((:instance field-two-line-equations-imply-doubled-first-ordinate
                     (ya first-y) (yb second-y)
                     (p first-slope) (r second-slope)
                     (delta difference)))
    :in-theory (theory 'minimal-theory))))
