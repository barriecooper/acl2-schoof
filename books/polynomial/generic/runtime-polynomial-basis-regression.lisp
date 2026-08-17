(in-package "GPOLY")

(include-book "runtime-polynomial-basis")

(defconst *runtime-polynomial-basis-f7-linear*
  '(:polynomial-basis 7 (1 1)))
(defconst *runtime-polynomial-basis-f7x2*
  '(:polynomial-basis 7 (1 0 1)))
(defconst *runtime-polynomial-basis-composite*
  '(:polynomial-basis 6 (1 0 1)))
(defconst *runtime-polynomial-basis-reducible*
  '(:polynomial-basis 7 (6 0 1)))

(assert-event
 (and (runtime-polynomial-basis-descriptor-p
       *runtime-polynomial-basis-f7-linear*)
      (runtime-polynomial-basis-descriptor-p
       *runtime-polynomial-basis-f7x2*)
      (runtime-polynomial-basis-descriptor-p
       *runtime-polynomial-basis-composite*)
      (runtime-polynomial-basis-descriptor-p
       *runtime-polynomial-basis-reducible*)))

; Variable-length canonical representatives and exact-width vectors differ.
(assert-event
 (and (equal (runtime-polynomial-basis-fix
              '(3 0 0 . malformed) *runtime-polynomial-basis-f7x2*)
             '(3))
      (equal (runtime-polynomial-basis-vector
              '(3 0 0 . malformed) *runtime-polynomial-basis-f7x2*)
             '(3 0))))

; The composite and reducible examples are structurally admitted; no field
; property is involved in these calculations.
(assert-event
 (and (equal (runtime-polynomial-basis-add
              '(5 5) '(4 3) *runtime-polynomial-basis-composite*)
             '(3 2))
      (equal (runtime-polynomial-basis-mul
              '(1 1) '(1 1) *runtime-polynomial-basis-reducible*)
             '(2 2))))

; (3+2x)(4+5x) = 2+2x modulo x^2+1 over the effective modulus 7.
(assert-event
 (equal (runtime-polynomial-basis-mul
         '(3 2) '(4 5) *runtime-polynomial-basis-f7x2*)
        '(2 2)))

; Malformed descriptors have an explicit total default: F2[X]/(X).
(assert-event
 (and (equal (runtime-polynomial-basis-descriptor-fix
              '(:polynomial-basis bad (1 1)))
             '(:polynomial-basis 2 (0 1)))
      (equal (runtime-polynomial-basis-fix '(1 1) 'malformed) '(1))))

(assert-event
 (and (equal (runtime-polynomial-basis-bound
              *runtime-polynomial-basis-f7-linear*) 7)
      (equal (runtime-polynomial-basis-bound
              *runtime-polynomial-basis-f7x2*) 49)
      (equal (runtime-polynomial-basis-unrank
              0 *runtime-polynomial-basis-f7x2*) nil)
      (equal (runtime-polynomial-basis-unrank
              48 *runtime-polynomial-basis-f7x2*) '(6 6))
      (equal (runtime-polynomial-basis-rank
              '(6 6) *runtime-polynomial-basis-f7x2*) 48)))

; Minimal-theory clients consume the public statements explicitly.
(defthm runtime-polynomial-basis-minimal-client
  (and (runtime-polynomial-basis-element-p
        (runtime-polynomial-basis-mul x y descriptor) descriptor)
       (< (runtime-polynomial-basis-rank x descriptor)
          (runtime-polynomial-basis-bound descriptor)))
  :rule-classes nil
  :hints (("Goal"
           :use (runtime-polynomial-basis-element-p-of-mul
                 runtime-polynomial-basis-rank-bound)
           :in-theory (theory 'minimal-theory))))
