(in-package "GPOLY")

(include-book "runtime-p-coefficient-inverse")
(include-book "../../field/examples/f11")

(defthm runtime-p-inverse-minimal-theory-client
  (implies (and (dm::primep (runtime-p-effective-modulus p))
                (not (equal (runtime-p-coefficient-fix x p)
                            (runtime-p-zero p))))
           (equal (runtime-p-mul x (runtime-p-inv x p) p)
                  (runtime-p-one p)))
  :hints (("Goal" :use ((:instance runtime-p-mul-inv-right))
           :in-theory (theory 'minimal-theory))))

(assert-event (equal (list (runtime-p-inv 1 7) (runtime-p-inv 2 7)
                           (runtime-p-inv 3 7) (runtime-p-inv 4 7)
                           (runtime-p-inv 5 7) (runtime-p-inv 6 7))
                     '(1 4 5 2 3 6)))
(assert-event (equal (list (runtime-p-inv 2 11) (runtime-p-inv 5 11)
                           (runtime-p-inv 7 11) (runtime-p-inv 10 11))
                     '(6 9 8 10)))
(assert-event (equal (runtime-p-inv 0 7) 0))
(assert-event (equal (runtime-p-inv -2 7) 3))
(assert-event (equal (runtime-p-inv 16 7) 4))
(assert-event (equal (runtime-p-inv 'bad 7) 0))
(assert-event (equal (runtime-p-inv 3 'bad) 1))
(assert-event (equal (runtime-p-inv 8 9) 8)) ; composite unit
(assert-event (equal (runtime-p-inv 3 9) 0)) ; executable nonunit, no field claim

(defthm runtime-p-inv-f7-correspondence
  (equal (runtime-p-inv x 7) (gfield::f7-inv x))
  :hints (("Goal" :in-theory (enable runtime-p-inv gfield::f7-inv
                                     runtime-p-coefficient-fix
                                     runtime-p-effective-modulus
                                     gfield::f7-fix))))

(defthm runtime-p-inv-f11-correspondence
  (equal (runtime-p-inv x 11) (gfield::f11-inv x))
  :hints (("Goal" :in-theory (enable runtime-p-inv gfield::f11-inv
                                     runtime-p-coefficient-fix
                                     runtime-p-effective-modulus
                                     gfield::f11-fix))))
