(in-package "GPOLY")
(include-book "runtime-p-algebra")

(assert-event (equal (runtime-p-add 5 5 6) 4))
(assert-event (equal (runtime-p-mul 4 5 6) 2))
(assert-event (equal (runtime-p-add 'bad 3 'bad) 1))

(defthm runtime-p-add-associative-minimal-theory-client
  (equal (runtime-p-add (runtime-p-add x y p) z p)
         (runtime-p-add x (runtime-p-add y z p) p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-add-associative))
           :in-theory (theory 'minimal-theory))))
(defthm runtime-p-distributive-minimal-theory-client
  (equal (runtime-p-mul x (runtime-p-add y z p) p)
         (runtime-p-add (runtime-p-mul x y p)
                        (runtime-p-mul x z p) p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-mul-left-distributive))
           :in-theory (theory 'minimal-theory))))
(defthm runtime-p-sub-reconstruction-minimal-theory-client
  (equal (runtime-p-add y (runtime-p-sub x y p) p)
         (runtime-p-coefficient-fix x p))
  :rule-classes nil
  :hints (("Goal" :use ((:instance runtime-p-sub-reconstruction))
           :in-theory (theory 'minimal-theory))))
