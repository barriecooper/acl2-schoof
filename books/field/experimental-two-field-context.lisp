(in-package "GFIELD")

; This is an experimental relationship between two field-like structures, not
; a second field hierarchy and not an adopted ambient-field architecture.
(encapsulate
 (((two-field-context-p) => *)
  ((two-field-base-element-p *) => *)
  ((two-field-base-fix *) => *)
  ((two-field-base-zero) => *) ((two-field-base-one) => *)
  ((two-field-base-add * *) => *) ((two-field-base-mul * *) => *)
  ((two-field-base-neg *) => *)
  ((two-field-ambient-element-p *) => *)
  ((two-field-ambient-fix *) => *)
  ((two-field-ambient-zero) => *) ((two-field-ambient-one) => *)
  ((two-field-ambient-add * *) => *) ((two-field-ambient-mul * *) => *)
  ((two-field-ambient-neg *) => *)
  ((two-field-embed *) => *) ((two-field-q) => *)
  ((two-field-ambient-pow * *) => *) ((two-field-frobenius *) => *)
  ((two-field-base-projection *) => *)
  ((two-field-embedded-image-p *) => *)
  ((two-field-nonidentity-witness) => *))

 (local (defun two-field-context-p () nil))
 (local (defun two-field-base-element-p (x) (declare (ignore x)) nil))
 (local (defun two-field-base-fix (x) x))
 (local (defun two-field-base-zero () nil))
 (local (defun two-field-base-one () t))
 (local (defun two-field-base-add (x y) (declare (ignore y)) x))
 (local (defun two-field-base-mul (x y) (declare (ignore y)) x))
 (local (defun two-field-base-neg (x) x))
 (local (defun two-field-ambient-element-p (x) (declare (ignore x)) nil))
 (local (defun two-field-ambient-fix (x) x))
 (local (defun two-field-ambient-zero () nil))
 (local (defun two-field-ambient-one () t))
 (local (defun two-field-ambient-add (x y) (declare (ignore y)) x))
 (local (defun two-field-ambient-mul (x y) (declare (ignore y)) x))
 (local (defun two-field-ambient-neg (x) x))
 (local (defun two-field-embed (x) x))
 (local (defun two-field-q () 1))
 (local (defun two-field-ambient-pow (x n) (declare (ignore n)) x))
 (local (defun two-field-frobenius (x) x))
 (local (defun two-field-base-projection (x) x))
 (local (defun two-field-embedded-image-p (x) (declare (ignore x)) nil))
 (local (defun two-field-nonidentity-witness () nil))

 (defthm two-field-embed-of-base-fix
   (implies (two-field-context-p)
            (equal (two-field-embed (two-field-base-fix x))
                   (two-field-embed x))))
 (defthm two-field-embed-closure-and-fixing
   (implies (two-field-context-p)
            (and (two-field-ambient-element-p (two-field-embed x))
                 (equal (two-field-ambient-fix (two-field-embed x))
                        (two-field-embed x)))))
 (defthm two-field-embed-injective-modulo-base-fix
   (implies (two-field-context-p)
            (equal (equal (two-field-embed x) (two-field-embed y))
                   (equal (two-field-base-fix x)
                          (two-field-base-fix y)))))
 (defthm two-field-embed-preserves-operations
   (implies (two-field-context-p)
            (and (equal (two-field-embed (two-field-base-zero))
                        (two-field-ambient-zero))
                 (equal (two-field-embed (two-field-base-one))
                        (two-field-ambient-one))
                 (equal (two-field-embed (two-field-base-add x y))
                        (two-field-ambient-add (two-field-embed x)
                                               (two-field-embed y)))
                 (equal (two-field-embed (two-field-base-mul x y))
                        (two-field-ambient-mul (two-field-embed x)
                                               (two-field-embed y)))
                 (equal (two-field-embed (two-field-base-neg x))
                        (two-field-ambient-neg (two-field-embed x))))))
 (defthm two-field-q-positive
   (implies (two-field-context-p) (posp (two-field-q))))
 (defthm two-field-frobenius-is-qth-power
   (implies (two-field-context-p)
            (equal (two-field-frobenius x)
                   (two-field-ambient-pow x (two-field-q)))))
 (defthm two-field-frobenius-fixing-and-closure
   (implies (two-field-context-p)
            (and (equal (two-field-frobenius (two-field-ambient-fix x))
                        (two-field-frobenius x))
                 (two-field-ambient-element-p (two-field-frobenius x))
                 (equal (two-field-ambient-fix (two-field-frobenius x))
                        (two-field-frobenius x)))))
 (defthm two-field-frobenius-preserves-operations
   (implies (two-field-context-p)
            (and (equal (two-field-frobenius (two-field-ambient-zero))
                        (two-field-ambient-zero))
                 (equal (two-field-frobenius (two-field-ambient-one))
                        (two-field-ambient-one))
                 (equal (two-field-frobenius (two-field-ambient-add x y))
                        (two-field-ambient-add (two-field-frobenius x)
                                               (two-field-frobenius y)))
                 (equal (two-field-frobenius (two-field-ambient-mul x y))
                        (two-field-ambient-mul (two-field-frobenius x)
                                               (two-field-frobenius y)))
                 (equal (two-field-frobenius (two-field-ambient-neg x))
                        (two-field-ambient-neg (two-field-frobenius x))))))
 (defthm two-field-frobenius-fixes-embedded-base
   (implies (two-field-context-p)
            (equal (two-field-frobenius (two-field-embed x))
                   (two-field-embed x))))
 (defthm two-field-frobenius-nonidentity
   (implies (two-field-context-p)
            (and (two-field-ambient-element-p
                  (two-field-nonidentity-witness))
                 (not (equal
                       (two-field-frobenius
                        (two-field-nonidentity-witness))
                       (two-field-ambient-fix
                        (two-field-nonidentity-witness))))))
   :rule-classes nil)
 (defthm booleanp-of-two-field-embedded-image-p
   (implies (two-field-context-p)
            (booleanp (two-field-embedded-image-p x))))
 (defthm two-field-embedded-image-recognition
   (implies (two-field-context-p)
            (equal (two-field-embedded-image-p x)
                   (equal (two-field-ambient-fix x)
                          (two-field-embed
                           (two-field-base-fix
                            (two-field-base-projection x)))))))
 (defthm two-field-frobenius-fixed-iff-embedded-image
   (implies (two-field-context-p)
            (equal (equal (two-field-frobenius x)
                          (two-field-ambient-fix x))
                   (two-field-embedded-image-p x))))
 (defthm two-field-embedded-image-p-of-fix
   (implies (two-field-context-p)
            (equal (two-field-embedded-image-p
                    (two-field-ambient-fix x))
                   (two-field-embedded-image-p x)))))

(defthm two-field-frobenius-fixed-iff-embedded-fixed-projection
  (implies
   (two-field-context-p)
   (equal (equal (two-field-frobenius x) (two-field-ambient-fix x))
          (equal (two-field-ambient-fix x)
                 (two-field-embed
                  (two-field-base-fix
                   (two-field-base-projection x))))))
  :hints (("Goal" :use (two-field-frobenius-fixed-iff-embedded-image
                         two-field-embedded-image-recognition)
           :in-theory (theory 'minimal-theory))))
