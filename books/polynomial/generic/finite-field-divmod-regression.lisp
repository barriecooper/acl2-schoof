(in-package "GPOLY")

(include-book "finite-field-divmod")
(include-book "f7-division")

(local (in-theory (disable finite-field-poly-divmod-core
                           finite-field-poly-divmod
                           finite-field-poly-division-step-core
                           finite-field-poly-add
                           finite-field-poly-mul
                           finite-field-poly-normalize
                           finite-field-poly-raw-add
                           finite-field-poly-raw-mul)))

(defthm finite-field-divmod-quotient-canonical-minimal-theory-client
  (finite-field-canonical-polynomial-p
   (mv-nth 0 (finite-field-poly-divmod f g)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-divmod-quotient-canonical)))))

(defthm finite-field-divmod-remainder-canonical-minimal-theory-client
  (finite-field-canonical-polynomial-p
   (mv-nth 1 (finite-field-poly-divmod f g)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-divmod-remainder-canonical)))))

(defthm finite-field-divmod-reconstruction-minimal-theory-client
  (equal (finite-field-poly-add
          (finite-field-poly-mul
           (mv-nth 0 (finite-field-poly-divmod f g))
           (finite-field-poly-normalize g))
          (mv-nth 1 (finite-field-poly-divmod f g)))
         (finite-field-poly-normalize f))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-divmod-reconstruction)))))

(defthm finite-field-divmod-degree-bound-minimal-theory-client
  (implies (consp (finite-field-poly-normalize g))
           (or (equal (mv-nth 1 (finite-field-poly-divmod f g)) nil)
               (< (finite-field-poly-degree
                   (mv-nth 1 (finite-field-poly-divmod f g)))
                  (finite-field-poly-degree
                   (finite-field-poly-normalize g)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance finite-field-poly-divmod-final-remainder-degree-bound)))))

(defthm f7-divmod-public-interface-client
  (and (f7-canonical-polynomial-p (mv-nth 0 (f7-poly-divmod f g)))
       (f7-canonical-polynomial-p (mv-nth 1 (f7-poly-divmod f g)))
       (equal (f7-poly-add
               (f7-poly-mul (mv-nth 0 (f7-poly-divmod f g))
                            (f7-normalize g))
               (mv-nth 1 (f7-poly-divmod f g)))
              (f7-normalize f))
       (implies (consp (f7-normalize g))
                (or (equal (mv-nth 1 (f7-poly-divmod f g)) nil)
                    (< (f7-poly-degree (mv-nth 1 (f7-poly-divmod f g)))
                       (f7-poly-degree (f7-normalize g))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance f7-poly-divmod-quotient-canonical)
                         (:instance f7-poly-divmod-remainder-canonical)
                         (:instance f7-poly-divmod-reconstruction)
                         (:instance f7-poly-divmod-final-remainder-degree-bound)))))

(assert-event
 (mv-let (q r) (f7-poly-divmod '(1 0 1) '(1 1))
   (equal (list q r) '((6 1) (2)))))
(assert-event
 (mv-let (q r) (f7-poly-divmod '(1) '(0 1))
   (equal (list q r) '(nil (1)))))
(assert-event
 (mv-let (q r) (f7-poly-divmod nil '(1 1))
   (equal (list q r) '(nil nil))))
(assert-event
 (mv-let (q r) (f7-poly-divmod '(1 0 1) nil)
   (equal (list q r) '(nil (1 0 1)))))
(assert-event
 (mv-let (q r) (f7-poly-divmod '(1 0 1) '(1 0 1))
   (equal (list q r) '((1) nil))))
(assert-event
 (mv-let (q r) (f7-poly-divmod '(8 . bad-tail) '(1))
   (equal (list q r) '((1) nil))))
(assert-event (equal (f7-poly-quotient '(1 0 1) '(1 1))
                     '(6 1)))
(assert-event (equal (f7-poly-remainder '(1 0 1) '(1 1))
                     '(2)))
