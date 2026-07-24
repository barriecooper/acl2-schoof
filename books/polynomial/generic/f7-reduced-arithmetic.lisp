(in-package "GPOLY")
(include-book "f7-division")

; Concrete execution witnesses use the same transparent operation/remainder
; chain as the generic boundary.  They do not introduce a concrete quotient
; object or duplicate the generic structural proofs.
(defun f7-poly-reduced-add (left right modulus)
  (f7-poly-remainder (f7-poly-add left right) modulus))
(defun f7-poly-reduced-neg (polynomial modulus)
  (f7-poly-remainder (f7-poly-neg polynomial) modulus))
(defun f7-poly-reduced-sub (left right modulus)
  (f7-poly-remainder (f7-poly-sub left right) modulus))
(defun f7-poly-reduced-mul (left right modulus)
  (f7-poly-remainder (f7-poly-mul left right) modulus))
(defun f7-poly-reduced-one (modulus)
  (f7-poly-remainder (f7-polynomial-one) modulus))

; Concrete execution spelling of the generic quotient-equality boundary.
(defun f7-poly-congruent-p (left right modulus)
  (equal (f7-poly-remainder left modulus)
         (f7-poly-remainder right modulus)))

(verify-guards f7-poly-reduced-add)
(verify-guards f7-poly-reduced-neg)
(verify-guards f7-poly-reduced-sub)
(verify-guards f7-poly-reduced-mul)
(verify-guards f7-poly-reduced-one)
(verify-guards f7-poly-congruent-p)

(defthm f7-poly-congruent-p-exact-regressions
  (and
   ; Different representations, the same exact representative.
   (equal (f7-poly-remainder '(8 -1 0 0) '(1 0 1)) '(1 6))
   (equal (f7-poly-remainder '(1 6) '(1 0 1)) '(1 6))
   (f7-poly-congruent-p '(8 -1 0 0) '(1 6) '(1 0 1))
   (not (equal '(8 -1 0 0) '(1 6)))
   ; Distinct already-reduced representatives do not compare equal.
   (not (f7-poly-congruent-p '(1 2) '(2 2) '(1 0 1)))
   (equal (f7-poly-remainder '(1 2) '(1 0 1)) '(1 2))
   (equal (f7-poly-remainder '(2 2) '(1 0 1)) '(2 2))
   ; Adding one modulus multiple, trailing zeros, malformed total inputs.
   (f7-poly-congruent-p '(2 2 1) '(1 2) '(1 0 1))
   (f7-poly-congruent-p '(1 2 0 0) '(1 2) '(1 0 1))
   (f7-poly-congruent-p 'malformed nil '(1 0 1))
   (f7-poly-congruent-p '(1 2 . 9) '(1 2) '(1 0 1))
   ; Exact total modulus semantics.
   (f7-poly-congruent-p '(8 -1 0) '(1 6) nil)
   (not (f7-poly-congruent-p '(1) '(2) nil))
   (f7-poly-congruent-p '(1 2) '(6 5) '(1))
   (f7-poly-congruent-p '(1 2) '(6 5) '(3))
   ; Reducible x^2-1 and irreducible-looking x^2+1 examples.
   (f7-poly-congruent-p '(0 0 1) '(1) '(6 0 1))
   (f7-poly-congruent-p '(0 0 1) '(6) '(1 0 1))
   ; Compatibility is checked at exact representative values.
   (equal (f7-poly-reduced-add '(8 -1 0 0) '(3) '(1 0 1))
          (f7-poly-reduced-add '(1 6) '(3) '(1 0 1)))
   (equal (f7-poly-reduced-neg '(8 -1 0 0) '(1 0 1))
          (f7-poly-reduced-neg '(1 6) '(1 0 1)))
   (equal (f7-poly-reduced-sub '(8 -1 0 0) '(3) '(1 0 1))
          (f7-poly-reduced-sub '(1 6) '(3) '(1 0 1)))
   (equal (f7-poly-reduced-mul '(8 -1 0 0) '(3) '(1 0 1))
          (f7-poly-reduced-mul '(1 6) '(3) '(1 0 1)))
   ; For fixed representatives, congruence is literal equality.
   (equal (f7-poly-congruent-p '(1 2) '(1 2) '(1 0 1))
          (equal '(1 2) '(1 2)))
   (equal (f7-poly-congruent-p '(1 2) '(2 2) '(1 0 1))
          (equal '(1 2) '(2 2))))
  :rule-classes nil)

; x^2+1 is used only as an irreducible-looking execution example.  No
; irreducibility or field conclusion is asserted.
(defthm f7-poly-reduced-arithmetic-exact-regressions
  (and
   ; Addition requiring reduction, addition below the bound, and cancellation.
   (equal (f7-poly-add '(0 0 1) '(3)) '(3 0 1))
   (equal (f7-poly-reduced-add '(0 0 1) '(3) '(1 0 1)) '(2))
   (equal (f7-poly-reduced-add '(1 2) '(3) '(1 0 1)) '(4 2))
   (equal (f7-poly-reduced-add '(1 2) '(6 5) '(1 0 1)) nil)
   ; Negation and subtraction retain their public arithmetic boundaries.
   (equal (f7-poly-reduced-neg '(1 2) '(1 0 1)) '(6 5))
   (equal (f7-poly-reduced-sub '(1 2) '(3 4) '(1 0 1)) '(5 5))
   ; A degree-four product substantially reduces; zero and one are explicit.
   (equal (f7-poly-mul '(1 1 1) '(1 1 1)) '(1 2 3 2 1))
   (equal (f7-poly-reduced-mul '(1 1 1) '(1 1 1) '(1 0 1)) '(6))
   (equal (f7-poly-reduced-mul '(1 2) nil '(1 0 1)) nil)
   (equal (f7-poly-reduced-mul '(3 4 5) '(1) '(1 0 1)) '(5 4))
   ; Total modulus semantics.
   (equal (f7-poly-reduced-add '(8 -1 0) '(3) nil) '(4 6))
   (equal (f7-poly-reduced-sub '(1 2) '(3 4) '(1)) nil)
   (equal (f7-poly-reduced-mul '(1 2) '(3 4) '(3)) nil)
   ; Trailing zeros, out-of-range coefficients, atoms, and dotted lists.
   (equal (f7-poly-reduced-add '(8 -1 0 0) '(3) '(1 0 1 0)) '(4 6))
   (equal (f7-poly-reduced-neg 'malformed '(1 0 1)) nil)
   (equal (f7-poly-reduced-add '(1 2) '(3) 'malformed-modulus) '(4 2))
   (equal (f7-poly-reduced-sub '(1 2 . 9) '(3 . 8) '(1 0 1)) '(5 2))
   (equal (f7-poly-reduced-add '(0 0 1) '(3) '(1 0 1 . 9)) '(2))
   ; A small reducible-modulus execution example, with no field claim.
   (equal (f7-poly-reduced-mul '(1 1) '(1 1) '(6 0 1)) '(2 2))))

(defthm f7-poly-reduced-arithmetic-boundary-regressions
  (let* ((modulus '(1 0 1))
         (result (f7-poly-reduced-mul '(1 1 1) '(1 1 1) modulus)))
    (and (f7-canonical-polynomial-p result)
         (equal (f7-normalize result) result)
         (equal (f7-poly-remainder result modulus) result)
         (or (equal result nil)
             (< (f7-poly-degree result)
                (f7-poly-degree (f7-normalize modulus))))
         (equal (f7-poly-reduced-add '(8 -1 0 0) '(3) '(1 0 1 0))
                (f7-poly-reduced-add
                 (f7-normalize '(8 -1 0 0))
                 (f7-normalize '(3))
                 (f7-normalize '(1 0 1 0)))))))

(defthm f7-poly-reduced-ring-law-regressions
  (let* ((m '(1 0 1))
         (a '(0 0 1))
         (b '(3 4 5))
         (c '(8 -1 0 0))
         (ra (f7-poly-remainder a m))
         (rb (f7-poly-remainder b m))
         (rc (f7-poly-remainder c m))
         (one (f7-poly-reduced-one m))
         (add-left (f7-poly-reduced-add
                    (f7-poly-reduced-add a b m) c m))
         (add-right (f7-poly-reduced-add
                     a (f7-poly-reduced-add b c m) m))
         (mul-left (f7-poly-reduced-mul
                    (f7-poly-reduced-mul a b m) c m))
         (mul-right (f7-poly-reduced-mul
                     a (f7-poly-reduced-mul b c m) m)))
    (and
     (equal ra '(6)) (equal rb '(5 4)) (equal rc '(1 6))
     (equal one '(1))
     (equal add-left '(5 3)) (equal add-right '(5 3))
     (equal (f7-poly-reduced-add 'malformed nil m) nil)
     (equal (f7-poly-reduced-add a (f7-poly-reduced-neg a m) m) nil)
     (equal (f7-poly-reduced-neg (f7-poly-reduced-neg c m) m) rc)
     (equal (f7-poly-reduced-sub b c m)
            (f7-poly-reduced-add b (f7-poly-reduced-neg c m) m))
     (equal mul-left '(5 1)) (equal mul-right '(5 1))
     (equal (f7-poly-reduced-mul b one m) rb)
     (equal (f7-poly-reduced-mul nil '(1 2 . 9) m) nil)
     (equal (f7-poly-reduced-mul a (f7-poly-reduced-add b c m) m)
            (f7-poly-reduced-add (f7-poly-reduced-mul a b m)
                                 (f7-poly-reduced-mul a c m) m))
     (equal (f7-poly-reduced-mul (f7-poly-reduced-add a b m) c m)
            (f7-poly-reduced-add (f7-poly-reduced-mul a c m)
                                 (f7-poly-reduced-mul b c m) m))
     (equal (f7-poly-reduced-one nil) '(1))
     (equal (f7-poly-reduced-one '(1)) nil)
     (equal (f7-poly-reduced-one '(3)) nil)
     (equal (f7-poly-reduced-one '(6 0 1)) '(1))
     (equal (f7-poly-reduced-mul '(1 1) '(1 1) '(6 0 1)) '(2 2))
     (f7-canonical-polynomial-p mul-left)
     (equal (f7-normalize mul-left) mul-left)
     (equal (f7-poly-remainder mul-left m) mul-left)))
  :rule-classes nil)

; Focused unit-law executions.  These record the complete canonical data for
; a unit modulo a reducible polynomial, an irreducible-looking execution-only
; modulus, total constant moduli, and normalized malformed representations.
(assert-event
 (let* ((first '(0 1))
        (modulus '(6 0 1))       ; x^2 - 1, deliberately reducible
        (inverse (f7-poly-modular-inverse first modulus))
        (one (f7-poly-reduced-one modulus))
        (left (f7-poly-reduced-mul inverse first modulus))
        (right (f7-poly-reduced-mul first inverse modulus)))
   (and (equal (f7-normalize first) '(0 1))
        (equal (f7-normalize modulus) '(6 0 1))
        (equal (f7-poly-monic-euclidean-gcd first modulus) '(1))
        (equal inverse '(0 1))
        (equal one '(1))
        (equal left '(1)) (equal right '(1))
        (equal left one) (equal right one)
        (f7-canonical-polynomial-p inverse)
        (equal (f7-normalize inverse) inverse)
        (equal (f7-poly-remainder inverse modulus) inverse))))

(assert-event
 (let* ((first '(1 0 0 0 1))
        (modulus '(1 1 1))       ; no irreducibility claim
        (inverse (f7-poly-modular-inverse first modulus))
        (one (f7-poly-reduced-one modulus))
        (left (f7-poly-reduced-mul inverse first modulus))
        (right (f7-poly-reduced-mul first inverse modulus)))
   (and (equal (f7-normalize first) '(1 0 0 0 1))
        (equal (f7-normalize modulus) '(1 1 1))
        (equal (f7-poly-monic-euclidean-gcd first modulus) '(1))
        (equal inverse '(0 6))
        (equal one '(1))
        (equal left '(1)) (equal right '(1))
        (equal left one) (equal right one)
        (f7-canonical-polynomial-p inverse)
        (equal (f7-normalize inverse) inverse)
        (equal (f7-poly-remainder inverse modulus) inverse))))

(assert-event
 (let ((modulus '(6 0 1)))
   (and (equal (f7-poly-monic-euclidean-gcd '(6 1) modulus) '(6 1))
        (not (equal (f7-poly-monic-euclidean-gcd '(6 1) modulus)
                    (f7-polynomial-one))))))

(assert-event
 (and
  ; Zero-normalized modulus: only normalized nonzero constants meet the
  ; monic-GCD-one condition; ordinary normalized multiplication remains.
  (equal (f7-normalize '(3)) '(3))
  (equal (f7-poly-monic-euclidean-gcd '(3) nil) '(1))
  (equal (f7-poly-modular-inverse '(3) nil) '(5))
  (equal (f7-poly-reduced-one nil) '(1))
  (equal (f7-poly-reduced-mul '(3) '(5) nil) '(1))
  (equal (f7-poly-reduced-mul '(5) '(3) nil) '(1))
  ; Polynomial-one and every normalized nonzero constant modulus are the
  ; trivial ring, including malformed/trailing input normalization.
  (equal (f7-poly-monic-euclidean-gcd '(8 -7 8) '(1)) '(1))
  (equal (f7-poly-modular-inverse '(8 -7 8) '(1)) nil)
  (equal (f7-poly-reduced-one '(1)) nil)
  (equal (f7-poly-reduced-mul '(8 -7 8) nil '(1)) nil)
  (equal (f7-poly-reduced-mul nil '(8 -7 8) '(1)) nil)
  (equal (f7-poly-monic-euclidean-gcd '(1 0 1 . bad) '(9 0 . tail)) '(1))
  (equal (f7-poly-modular-inverse '(1 0 1 . bad) '(9 0 . tail)) nil)
  (equal (f7-poly-reduced-one '(9 0 . tail)) nil)
  (equal (f7-poly-reduced-mul '(1 0 1 . bad) nil '(9 0 . tail)) nil)
  (equal (f7-poly-reduced-mul nil '(1 0 1 . bad) '(9 0 . tail)) nil)))
