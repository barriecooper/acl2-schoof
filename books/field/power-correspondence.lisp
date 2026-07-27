(in-package "GFIELD")

(include-book "kernel")

; Public-power comparison boundary.  Clients map only this function and the
; ordinary field operations; its constraints mention neither generated power
; specification nor fast-accumulator functions.
(encapsulate
 (((field-pow-instance * *) => *))
 (local (defun field-pow-instance (x n) (field-pow x n)))

 (defthm field-pow-instance-of-nfix
   (equal (field-pow-instance x (nfix n))
          (field-pow-instance x n)))
 (defthm field-pow-instance-zero
   (equal (field-pow-instance x 0) (field-one)))
 (defthm field-pow-instance-successor-total
   (equal (field-pow-instance x (+ 1 (nfix n)))
          (field-mul x (field-pow-instance x n)))
   :hints (("Goal" :use field-pow-successor-total))))

; The three total public equations uniquely determine power.  This is the one
; induction shared by all generated clients.
(local
 (defthm field-pow-instance-correspondence-natural
   (implies (natp n)
            (equal (field-pow-instance x n) (field-pow x n)))
   :hints (("Goal" :induct (field-pow-spec x n)
            :in-theory (enable field-pow-spec))
           ("Subgoal *1/2"
            :use ((:instance field-pow-instance-successor-total
                             (n (1- n)))
                  (:instance field-pow-successor-total (n (1- n))))))))

(defthm field-pow-instance-correspondence
  (equal (field-pow-instance x n) (field-pow x n))
  :hints (("Goal"
           :use ((:instance field-pow-instance-correspondence-natural
                            (n (nfix n)))))))

(defthm field-element-p-of-field-pow-instance
  (field-element-p (field-pow-instance x n))
  :hints (("Goal" :use field-pow-instance-correspondence)))
