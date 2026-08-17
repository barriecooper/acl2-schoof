(in-package "GPOLY")

(include-book "runtime-polynomial-basis-operation-congruence")

(defconst *runtime-polynomial-basis-operation-f7x2*
  '(:polynomial-basis 7 (1 0 1)))
(defconst *runtime-polynomial-basis-operation-composite*
  '(:polynomial-basis 6 (5 0 1)))

(defthm runtime-polynomial-basis-operation-congruence-minimal-client
  (and (equal (runtime-polynomial-basis-add
               (runtime-polynomial-basis-fix x descriptor)
               (runtime-polynomial-basis-fix y descriptor) descriptor)
              (runtime-polynomial-basis-add x y descriptor))
       (equal (runtime-polynomial-basis-neg
               (runtime-polynomial-basis-fix x descriptor) descriptor)
              (runtime-polynomial-basis-neg x descriptor))
       (equal (runtime-polynomial-basis-sub
               (runtime-polynomial-basis-fix x descriptor)
               (runtime-polynomial-basis-fix y descriptor) descriptor)
              (runtime-polynomial-basis-sub x y descriptor))
       (equal (runtime-polynomial-basis-mul
               (runtime-polynomial-basis-fix x descriptor)
               (runtime-polynomial-basis-fix y descriptor) descriptor)
              (runtime-polynomial-basis-mul x y descriptor)))
  :rule-classes nil
  :hints (("Goal"
           :use (runtime-polynomial-basis-add-of-fixes
                 runtime-polynomial-basis-neg-of-fix
                 runtime-polynomial-basis-sub-of-fixes
                 runtime-polynomial-basis-mul-of-fixes)
           :in-theory (theory 'minimal-theory))))

(assert-event
 (and (equal (runtime-polynomial-basis-mul
              '(3 2 0 . raw) '(4 5 0) *runtime-polynomial-basis-operation-f7x2*)
             (runtime-polynomial-basis-mul
              (runtime-polynomial-basis-fix
               '(3 2 0 . raw) *runtime-polynomial-basis-operation-f7x2*)
              (runtime-polynomial-basis-fix
               '(4 5 0) *runtime-polynomial-basis-operation-f7x2*)
              *runtime-polynomial-basis-operation-f7x2*))
      (equal (runtime-polynomial-basis-add
              '(5 4 3) '(4 3 2) *runtime-polynomial-basis-operation-composite*)
             (runtime-polynomial-basis-add
              (runtime-polynomial-basis-fix
               '(5 4 3) *runtime-polynomial-basis-operation-composite*)
              (runtime-polynomial-basis-fix
               '(4 3 2) *runtime-polynomial-basis-operation-composite*)
              *runtime-polynomial-basis-operation-composite*))
      (equal (runtime-polynomial-basis-sub '(1 1) '(3 2) 'malformed)
             (runtime-polynomial-basis-sub
              (runtime-polynomial-basis-fix '(1 1) 'malformed)
              (runtime-polynomial-basis-fix '(3 2) 'malformed)
              'malformed))))
