(in-package "GPOLY")

(include-book "runtime-p-monic-remainder-coset")

(defthm runtime-p-monic-remainder-coset-minimal-theory-client
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p)
               (runtime-p-one p)))
   (equal (runtime-p-monic-remainder
           (runtime-p-poly-add
            f (runtime-p-poly-mul q (runtime-p-normalize g p) p) p)
           g p)
          (runtime-p-monic-remainder f g p)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance
                  runtime-p-monic-remainder-of-poly-add-modulus-multiple))
           :in-theory (theory 'minimal-theory))))

; Multi-step division over F7, with a nonconstant multiplier.
(assert-event
 (and (equal (runtime-p-monic-remainder '(5 5 3 4 2) '(1 0 1) 7)
             '(4 1))
      (equal (runtime-p-monic-remainder
              (runtime-p-poly-add
               '(5 5 3 4 2)
               (runtime-p-poly-mul '(3 2 1) '(1 0 1) 7) 7)
              '(1 0 1) 7)
             '(4 1))))

; Composite coefficients and a reducible monic divisor require no domain law.
(assert-event
 (and (equal (runtime-p-monic-remainder
              (runtime-p-poly-add '(5 4 3 2) (runtime-p-poly-mul
                                               '(2 3) '(5 0 1) 6) 6)
              '(5 0 1) 6)
             (runtime-p-monic-remainder '(5 4 3 2) '(5 0 1) 6))
      (equal (runtime-p-monic-remainder
              (runtime-p-poly-add '(1 2 3 4) (runtime-p-poly-mul
                                               '(4 1) '(6 0 8 0) 7) 7)
              '(6 0 8 0) 7)
             (runtime-p-monic-remainder '(1 2 3 4) '(6 0 8 0) 7))))

; Malformed P follows the total effective-modulus-2 convention.
(assert-event
 (equal (runtime-p-monic-remainder
         (runtime-p-poly-add '(3 4 1)
                             (runtime-p-poly-mul '(3 2) '(1 1 0) 'bad)
                             'bad)
         '(1 1 0) 'bad)
        (runtime-p-monic-remainder '(3 4 1) '(1 1 0) 2)))

; Idempotence is total, including the monic and malformed-modulus cases.
(assert-event
 (and (equal (runtime-p-monic-remainder
              (runtime-p-monic-remainder '(5 5 3 4 2) '(1 0 1) 7)
              '(1 0 1) 7)
             (runtime-p-monic-remainder '(5 5 3 4 2) '(1 0 1) 7))
      (equal (runtime-p-monic-remainder
              (runtime-p-monic-remainder '(3 4 1) '(1 1) 'bad)
              '(1 1) 'bad)
             (runtime-p-monic-remainder '(3 4 1) '(1 1) 'bad))))

; Exact nontrivial modulus-multiple invariance, not merely an evaluation test.
(assert-event
 (let* ((f '(6 1 5 4 3))
        (q '(2 0 4))
        (g '(6 0 1))
        (shifted (runtime-p-poly-add f (runtime-p-poly-mul q g 7) 7)))
   (and (not (equal shifted f))
        (equal (runtime-p-monic-remainder shifted g 7)
               (runtime-p-monic-remainder f g 7)))))
