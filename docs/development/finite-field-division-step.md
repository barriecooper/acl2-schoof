# Finite-field division-step development ledger

Retained staged book: `books/polynomial/generic/finite-field-division-step.lisp`.
The book is intentionally not registered in `books/top.lisp` until the full
one-step boundary through strict length decrease certifies.

## 2026-08-04 retained progress

| Group | Last certified event | First failing event | Result |
| --- | --- | --- | --- |
| Multiplication consp | `finite-field-consp-of-poly-mul-when-canonical-nonzero` | — | Certified |
| Multiplication degree | `finite-field-poly-degree-of-poly-mul` | — | Certified |
| Multiplication leading coefficient | `finite-field-poly-leading-coefficient-of-poly-mul` | — | Certified |
| Product properties | `finite-field-poly-division-step-core-product-properties` | — | Certified |
| Cancellation | `finite-field-poly-division-step-core-product-properties` | `finite-field-poly-division-step-core-next-canonical` | Deferred |
| Next canonicality | `finite-field-poly-division-step-core-product-properties` | `finite-field-poly-division-step-core-next-canonical` | Deferred |
| Reconstruction | `finite-field-poly-division-step-core-product-properties` | — | Not attempted after retained failure |
| Degree decrease | `finite-field-poly-division-step-core-product-properties` | — | Not attempted after retained failure |
| Length decrease | `finite-field-poly-division-step-core-product-properties` | — | Not attempted after retained failure |

First failing event attempted after the certified product layer:

```lisp
(defthm finite-field-poly-division-step-core-next-canonical
  (implies (finite-field-canonical-polynomial-p remainder)
           (finite-field-canonical-polynomial-p
            (cdr (finite-field-poly-division-step-core remainder divisor))))
  :hints (("Goal" :in-theory (enable finite-field-poly-division-step-core))))
```

The relevant residual checkpoint was:

```lisp
(IMPLIES
 (AND
  (FINITE-FIELD-COEFFICIENT-LIST-P REMAINDER)
  (NOT (EQUAL (CAR (LAST REMAINDER))
              (GFIELD::FINITE-FIELD-ZERO)))
  (CONSP REMAINDER)
  (CONSP DIVISOR)
  (CONSP (FINITE-FIELD-POLY-TRIM-TRAILING-ZEROS
              (FINITE-FIELD-POLY-FIX-COEFFICIENTS DIVISOR)))
  (<= (+ -1
         (LEN (FINITE-FIELD-POLY-TRIM-TRAILING-ZEROS
                   (FINITE-FIELD-POLY-FIX-COEFFICIENTS DIVISOR))))
      (+ -1 (LEN REMAINDER)))
  (EQUAL
   (GFIELD::FINITE-FIELD-MUL
       (CAR (LAST REMAINDER))
       (GFIELD::FINITE-FIELD-INV
            (CAR (LAST (FINITE-FIELD-POLY-TRIM-TRAILING-ZEROS
                            (FINITE-FIELD-POLY-FIX-COEFFICIENTS DIVISOR))))))
   (GFIELD::FINITE-FIELD-ZERO))
  (CONSP (FINITE-FIELD-POLY-TRIM-TRAILING-ZEROS REMAINDER)))
 (FINITE-FIELD-COEFFICIENT-LIST-P
      (FINITE-FIELD-POLY-TRIM-TRAILING-ZEROS
           (FINITE-FIELD-POLY-FIX-COEFFICIENTS
                (FINITE-FIELD-POLY-TRIM-TRAILING-ZEROS REMAINDER)))))
```

Attempted route: direct target proof by enabling
`finite-field-poly-division-step-core`, mirroring the generic
`poly-division-step-core-next-canonical` hint.  Outcome: ACL2 failed with the
checkpoint above.  The uncertified tail was removed and the last certifying
source state was retained.
