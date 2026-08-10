(in-package "GPOLY")

(include-book "f11-division-polynomial-correspondence")

; Regression-named compatibility client.  Reusable functional-instance
; transports live in the production book included above.
(defthm f11-division-polynomial-functional-instance-minimal-theory-client
  (equal (f11-division-polynomial-base
          n (gfield::f11-fix a) (gfield::f11-fix b))
         (f11-division-polynomial-base n a b))
  :hints
  (("Goal"
    :use f11-division-polynomial-base-of-coefficient-fixes-from-finite-field-instance
    :in-theory (theory 'minimal-theory))))


(defthm f11-division-polynomial-semantic-correspondence-minimal-theory-client
  (and (f11-division-polynomial-sequence-p
        n (f11-division-polynomial-table n a b) a b)
       (implies (and (f11-division-polynomial-sequence-p n table a b)
                     (natp k) (<= k (nfix n)))
                (equal (nth k table)
                       (f11-division-polynomial k a b))))
  :hints (("Goal"
           :use (f11-division-polynomial-table-satisfies-sequence-p
                 f11-division-polynomial-sequence-p-entry-correspondence)
           :in-theory (theory 'minimal-theory))))
