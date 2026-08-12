(in-package "GPOLY")

(include-book "reduction")

; Evaluation descends through reduction at any root of the modulus.  No
; nonzero-modulus premise is needed: when the normalized modulus is zero the
; public remainder is just the normalized dividend.
(local
 (defthm eval-of-poly-divmod-reconstruction-congruence
   (equal
    (eval
     (poly-add
      (poly-mul (mv-nth 0 (poly-divmod polynomial modulus))
                (normalize modulus))
      (mv-nth 1 (poly-divmod polynomial modulus)))
     x)
    (eval (normalize polynomial) x))
   :rule-classes nil
   :hints (("Goal" :use ((:instance poly-divmod-reconstruction
                                    (f polynomial) (g modulus)))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm eval-of-poly-divmod-reconstruction
   (equal
    (gfield::field-add
     (gfield::field-mul
      (eval (mv-nth 0 (poly-divmod polynomial modulus)) x)
      (eval modulus x))
     (eval (mv-nth 1 (poly-divmod polynomial modulus)) x))
    (eval polynomial x))
   :rule-classes nil
   :hints
   (("Goal"
     :use (eval-of-poly-divmod-reconstruction-congruence)
     :in-theory
     (union-theories
      (theory 'minimal-theory)
      '(eval-of-poly-add eval-of-poly-mul eval-of-normalize))))))

(defthm eval-of-poly-remainder-at-root
  (implies (equal (eval modulus x) (gfield::field-zero))
           (equal (eval (poly-remainder polynomial modulus) x)
                  (eval polynomial x)))
  :rule-classes nil
  :hints
  (("Goal"
    :use (eval-of-poly-divmod-reconstruction
          (:instance poly-remainder-is-divmod-remainder
                     (dividend polynomial)))
    :in-theory
    (union-theories
     (theory 'minimal-theory)
     '(gfield::field-mul-zero-right gfield::field-add-zero-left
       gfield::field-fix-when-field-element-p field-element-p-of-eval)))))
