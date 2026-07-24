(in-package "GPOLY")
(include-book "reduction")

; These are representative-level operations, not quotient objects.  Each
; operation deliberately exposes the single operation-then-remainder path.
(defun poly-reduced-add (left right modulus)
  (poly-remainder (poly-add left right) modulus))

(defun poly-reduced-neg (polynomial modulus)
  (poly-remainder (poly-neg polynomial) modulus))

(defun poly-reduced-sub (left right modulus)
  (poly-remainder (poly-sub left right) modulus))

(defun poly-reduced-mul (left right modulus)
  (poly-remainder (poly-mul left right) modulus))

(defthm poly-reduced-add-definition
  (equal (poly-reduced-add left right modulus)
         (poly-remainder (poly-add left right) modulus))
  :hints (("Goal" :in-theory (enable poly-reduced-add))))

(defthm poly-reduced-neg-definition
  (equal (poly-reduced-neg polynomial modulus)
         (poly-remainder (poly-neg polynomial) modulus))
  :hints (("Goal" :in-theory (enable poly-reduced-neg))))

(defthm poly-reduced-sub-definition
  (equal (poly-reduced-sub left right modulus)
         (poly-remainder (poly-sub left right) modulus))
  :hints (("Goal" :in-theory (enable poly-reduced-sub))))

(defthm poly-reduced-mul-definition
  (equal (poly-reduced-mul left right modulus)
         (poly-remainder (poly-mul left right) modulus))
  :hints (("Goal" :in-theory (enable poly-reduced-mul))))

; Proofs below use the named public boundary theorems rather than expanding
; either arithmetic, division, or the four wrappers.
(local
 (in-theory (disable poly-reduced-add poly-reduced-neg
                     poly-reduced-sub poly-reduced-mul
                     poly-remainder poly-divmod poly-add poly-neg poly-sub
                     poly-mul normalize polynomial-one poly-degree)))

; The common structural interface follows only from the public remainder
; boundary.  Keeping the four statements explicit makes that provenance easy
; to inspect and avoids a second arithmetic generator.
(defthm canonical-polynomial-p-of-poly-reduced-add
  (canonical-polynomial-p (poly-reduced-add left right modulus)))
(defthm canonical-polynomial-p-of-poly-reduced-neg
  (canonical-polynomial-p (poly-reduced-neg polynomial modulus)))
(defthm canonical-polynomial-p-of-poly-reduced-sub
  (canonical-polynomial-p (poly-reduced-sub left right modulus)))
(defthm canonical-polynomial-p-of-poly-reduced-mul
  (canonical-polynomial-p (poly-reduced-mul left right modulus)))

(defthm normalize-of-poly-reduced-add
  (equal (normalize (poly-reduced-add left right modulus))
         (poly-reduced-add left right modulus)))
(defthm normalize-of-poly-reduced-neg
  (equal (normalize (poly-reduced-neg polynomial modulus))
         (poly-reduced-neg polynomial modulus)))
(defthm normalize-of-poly-reduced-sub
  (equal (normalize (poly-reduced-sub left right modulus))
         (poly-reduced-sub left right modulus)))
(defthm normalize-of-poly-reduced-mul
  (equal (normalize (poly-reduced-mul left right modulus))
         (poly-reduced-mul left right modulus)))

(defthm poly-remainder-of-poly-reduced-add
  (equal (poly-remainder (poly-reduced-add left right modulus) modulus)
         (poly-reduced-add left right modulus)))
(defthm poly-remainder-of-poly-reduced-neg
  (equal (poly-remainder (poly-reduced-neg polynomial modulus) modulus)
         (poly-reduced-neg polynomial modulus)))
(defthm poly-remainder-of-poly-reduced-sub
  (equal (poly-remainder (poly-reduced-sub left right modulus) modulus)
         (poly-reduced-sub left right modulus)))
(defthm poly-remainder-of-poly-reduced-mul
  (equal (poly-remainder (poly-reduced-mul left right modulus) modulus)
         (poly-reduced-mul left right modulus)))

(defthm poly-reduced-add-of-normalize
  (equal (poly-reduced-add (normalize left) (normalize right)
                           (normalize modulus))
         (poly-reduced-add left right modulus)))
(defthm poly-reduced-neg-of-normalize
  (equal (poly-reduced-neg (normalize polynomial) (normalize modulus))
         (poly-reduced-neg polynomial modulus)))
(defthm poly-reduced-sub-of-normalize
  (equal (poly-reduced-sub (normalize left) (normalize right)
                           (normalize modulus))
         (poly-reduced-sub left right modulus)))
(defthm poly-reduced-mul-of-normalize
  (equal (poly-reduced-mul (normalize left) (normalize right)
                           (normalize modulus))
         (poly-reduced-mul left right modulus)))

(defthm poly-reduced-add-zero-modulus
  (equal (poly-reduced-add left right nil) (poly-add left right)))
(defthm poly-reduced-neg-zero-modulus
  (equal (poly-reduced-neg polynomial nil) (poly-neg polynomial)))
(defthm poly-reduced-sub-zero-modulus
  (equal (poly-reduced-sub left right nil) (poly-sub left right)))
(defthm poly-reduced-mul-zero-modulus
  (equal (poly-reduced-mul left right nil) (poly-mul left right)))

(defthm poly-reduced-add-polynomial-one-modulus
  (equal (poly-reduced-add left right (polynomial-one)) nil))
(defthm poly-reduced-neg-polynomial-one-modulus
  (equal (poly-reduced-neg polynomial (polynomial-one)) nil))
(defthm poly-reduced-sub-polynomial-one-modulus
  (equal (poly-reduced-sub left right (polynomial-one)) nil))
(defthm poly-reduced-mul-polynomial-one-modulus
  (equal (poly-reduced-mul left right (polynomial-one)) nil))

(defthm poly-reduced-add-nonzero-constant-modulus
  (implies (and (consp (normalize modulus))
                (equal (poly-degree (normalize modulus)) 0))
           (equal (poly-reduced-add left right modulus) nil))
  :hints (("Goal" :use ((:instance poly-remainder-nonzero-constant-modulus
                                   (dividend (poly-add left right)))))))
(defthm poly-reduced-neg-nonzero-constant-modulus
  (implies (and (consp (normalize modulus))
                (equal (poly-degree (normalize modulus)) 0))
           (equal (poly-reduced-neg polynomial modulus) nil))
  :hints (("Goal" :use ((:instance poly-remainder-nonzero-constant-modulus
                                   (dividend (poly-neg polynomial)))))))
(defthm poly-reduced-sub-nonzero-constant-modulus
  (implies (and (consp (normalize modulus))
                (equal (poly-degree (normalize modulus)) 0))
           (equal (poly-reduced-sub left right modulus) nil))
  :hints (("Goal" :use ((:instance poly-remainder-nonzero-constant-modulus
                                   (dividend (poly-sub left right)))))))
(defthm poly-reduced-mul-nonzero-constant-modulus
  (implies (and (consp (normalize modulus))
                (equal (poly-degree (normalize modulus)) 0))
           (equal (poly-reduced-mul left right modulus) nil))
  :hints (("Goal" :use ((:instance poly-remainder-nonzero-constant-modulus
                                   (dividend (poly-mul left right)))))))

(defthm poly-reduced-add-strict-degree-bound
  (implies (consp (normalize modulus))
           (or (equal (poly-reduced-add left right modulus) nil)
               (< (poly-degree (poly-reduced-add left right modulus))
                  (poly-degree (normalize modulus)))))
  :hints (("Goal" :use ((:instance poly-remainder-strict-degree-bound
                                   (dividend (poly-add left right)))))))
(defthm poly-reduced-neg-strict-degree-bound
  (implies (consp (normalize modulus))
           (or (equal (poly-reduced-neg polynomial modulus) nil)
               (< (poly-degree (poly-reduced-neg polynomial modulus))
                  (poly-degree (normalize modulus)))))
  :hints (("Goal" :use ((:instance poly-remainder-strict-degree-bound
                                   (dividend (poly-neg polynomial)))))))
(defthm poly-reduced-sub-strict-degree-bound
  (implies (consp (normalize modulus))
           (or (equal (poly-reduced-sub left right modulus) nil)
               (< (poly-degree (poly-reduced-sub left right modulus))
                  (poly-degree (normalize modulus)))))
  :hints (("Goal" :use ((:instance poly-remainder-strict-degree-bound
                                   (dividend (poly-sub left right)))))))
(defthm poly-reduced-mul-strict-degree-bound
  (implies (consp (normalize modulus))
           (or (equal (poly-reduced-mul left right modulus) nil)
               (< (poly-degree (poly-reduced-mul left right modulus))
                  (poly-degree (normalize modulus)))))
  :hints (("Goal" :use ((:instance poly-remainder-strict-degree-bound
                                   (dividend (poly-mul left right)))))))

; Existing remainder arithmetic makes these unconditional representative
; invariance equations direct corollaries; no new division induction occurs.
(defthm poly-reduced-add-of-remainders
  (equal (poly-reduced-add (poly-remainder left modulus)
                           (poly-remainder right modulus) modulus)
         (poly-reduced-add left right modulus))
  :rule-classes nil
  :hints (("Goal" :use ((:instance poly-remainder-of-poly-add-remainders))
           :in-theory (enable poly-reduced-add))))
(defthm poly-reduced-neg-of-remainder
  (equal (poly-reduced-neg (poly-remainder polynomial modulus) modulus)
         (poly-reduced-neg polynomial modulus))
  :rule-classes nil
  :hints (("Goal" :use ((:instance poly-remainder-of-poly-neg-remainder))
           :in-theory (enable poly-reduced-neg))))
(defthm poly-reduced-sub-of-remainders
  (equal (poly-reduced-sub (poly-remainder left modulus)
                           (poly-remainder right modulus) modulus)
         (poly-reduced-sub left right modulus))
  :rule-classes nil
  :hints (("Goal" :use ((:instance poly-remainder-of-poly-sub-remainders))
           :in-theory (enable poly-reduced-sub))))
(defthm poly-reduced-mul-of-remainders
  (equal (poly-reduced-mul (poly-remainder left modulus)
                           (poly-remainder right modulus) modulus)
         (poly-reduced-mul left right modulus))
  :rule-classes nil
  :hints (("Goal" :use ((:instance poly-remainder-of-poly-mul-remainders))
           :in-theory (enable poly-reduced-mul))))

(verify-guards poly-reduced-add)
(verify-guards poly-reduced-neg)
(verify-guards poly-reduced-sub)
(verify-guards poly-reduced-mul)
