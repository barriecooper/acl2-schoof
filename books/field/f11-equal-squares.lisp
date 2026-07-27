(in-package "GFIELD")

(include-book "equal-squares")
(include-book "examples/f11")

; Focused concrete validation only; the generic proof does not depend on F11.
(assert-event (and (equal (f11-mul 4 4) (f11-mul 4 4))
                   (equal (f11-fix 4) (f11-fix 4))))
(assert-event (and (equal (f11-mul 4 4) (f11-mul 7 7))
                   (equal (f11-fix 7) (f11-neg 4))))
(assert-event (and (equal (f11-mul 4 4) (f11-mul 15 15))
                   (equal (f11-fix 4) (f11-fix 15))))
(assert-event (and (equal (f11-mul 15 15) (f11-mul 18 18))
                   (equal (f11-fix 18) (f11-neg 15))))
(assert-event (and (equal (f11-mul 0 0) (f11-mul 11 11))
                   (equal (f11-fix 0) (f11-fix 11))))
(assert-event (and (not (equal (f11-mul 2 2) (f11-mul 3 3)))
                   (not (or (equal (f11-fix 2) (f11-fix 3))
                            (equal (f11-fix 3) (f11-neg 2))))))
