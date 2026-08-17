(in-package "GPOLY")

(include-book "runtime-p-monic-remainder-operations")

(defthm runtime-p-monic-remainder-operations-minimal-theory-client
  (implies
   (and (consp (runtime-p-normalize g p))
        (equal (runtime-p-poly-leading-coefficient
                (runtime-p-normalize g p) p) (runtime-p-one p)))
   (and (equal (runtime-p-monic-remainder
                (runtime-p-poly-add x y p) g p)
               (runtime-p-monic-remainder
                (runtime-p-poly-add
                 (runtime-p-monic-remainder x g p)
                 (runtime-p-monic-remainder y g p) p) g p))
        (equal (runtime-p-monic-remainder
                (runtime-p-poly-neg x p) g p)
               (runtime-p-monic-remainder
                (runtime-p-poly-neg
                 (runtime-p-monic-remainder x g p) p) g p))
        (equal (runtime-p-monic-remainder
                (runtime-p-poly-mul x y p) g p)
               (runtime-p-monic-remainder
                (runtime-p-poly-mul
                 (runtime-p-monic-remainder x g p)
                 (runtime-p-monic-remainder y g p) p) g p))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance runtime-p-monic-remainder-of-poly-add
                            (left x) (right y))
                 (:instance runtime-p-monic-remainder-of-poly-neg
                            (value x))
                 (:instance runtime-p-monic-remainder-of-poly-mul
                            (left x) (right y)))
           :in-theory (theory 'minimal-theory))))

; Multi-step F7 reduction; the raw product has degree eight, above degree two.
(assert-event
 (let* ((g '(1 0 1))
        (x '(5 0 3 0 2))
        (y '(6 1 0 4 3))
        (product (runtime-p-poly-mul x y 7)))
   (and (< (runtime-p-poly-degree g 7)
           (runtime-p-poly-degree product 7))
        (equal (runtime-p-monic-remainder product g 7)
               (runtime-p-monic-remainder
                (runtime-p-poly-mul
                 (runtime-p-monic-remainder x g 7)
                 (runtime-p-monic-remainder y g 7) 7) g 7)))))

; Composite coefficients, a reducible modulus, and raw trailing zeros.
(assert-event
 (and (equal (runtime-p-monic-remainder
              (runtime-p-poly-add '(5 4 3 0) '(4 3 2 . raw) 6)
              '(5 0 1 0) 6)
             (runtime-p-monic-remainder
              (runtime-p-poly-add
               (runtime-p-monic-remainder '(5 4 3 0) '(5 0 1 0) 6)
               (runtime-p-monic-remainder '(4 3 2 . raw) '(5 0 1 0) 6) 6)
              '(5 0 1 0) 6))
      (equal (runtime-p-monic-remainder
              (runtime-p-poly-neg '(1 2 3 0) 7) '(6 0 1 0) 7)
             (runtime-p-monic-remainder
              (runtime-p-poly-neg
               (runtime-p-monic-remainder '(1 2 3 0) '(6 0 1 0) 7) 7)
              '(6 0 1 0) 7))))

; Malformed P retains effective-modulus-2 execution.
(assert-event
 (equal (runtime-p-monic-remainder
         (runtime-p-poly-mul '(3 4 1) '(5 2 1) 'bad) '(1 1 0) 'bad)
        (runtime-p-monic-remainder
         (runtime-p-poly-mul
          (runtime-p-monic-remainder '(3 4 1) '(1 1 0) 'bad)
          (runtime-p-monic-remainder '(5 2 1) '(1 1 0) 'bad) 'bad)
         '(1 1 0) 'bad)))
