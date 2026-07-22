# Open proof obligations

No row marked open is admitted by the ACL2 books.

| Identifier | Theorem statement | Mathematical justification | ACL2 dependencies | Status | Next action |
|---|---|---|---|---|---|
| POLY-CLOSED-ADD | Canonical field polynomials are closed under `poly-add`. | Field addition is closed and normalisation removes a zero leader. | PFIELD closure rules; normaliser lemmas | Proved | `poly-add-is-canonical` in `books/polynomial/base.lisp`. |
| POLY-CLOSED-MUL | Canonical field polynomials are closed under `poly-mul`. | Convolution uses field sums/products. | POLY-CLOSED-ADD, scaling closure | Proved | `poly-mul-is-canonical` in `books/polynomial/base.lisp`. |
| POLY-EVAL-ADD | Evaluation maps polynomial addition to field addition. | Horner evaluation and distributivity. | PFIELD associativity/distributivity | Proved | `poly-eval-of-add` in `books/polynomial/eval.lisp`. |
| POLY-EVAL-MUL | Evaluation maps polynomial multiplication to field multiplication. | Horner evaluation and distributivity. | POLY-EVAL-ADD, scaling evaluation | Proved | `poly-eval-of-mul-raw` and `poly-eval-of-mul` in `books/polynomial/eval.lisp`. |
| GPOLY-MUL-LAWS | Prove generic formal commutativity, both distributive laws, and associativity for canonical GPOLY multiplication. | Structural raw-add interchange, scaling, zero-prefix, and raw-product identities; never evaluation extensionality. | Generic canonical multiplication and scalar action | Proved | `poly-mul-commutative`, `poly-mul-associative`, and both distributive theorems in `books/polynomial/generic/mul.lisp`, transported through PFIELD to F7. |
| GPOLY-DEGREE-STRUCTURAL | Generic normalized degree and leading coefficient, with zero, canonical-nonzero, closure, bounds, constants, PFIELD, and executable F7 bridges. | Inspect the unique canonical dense representative; no evaluation extensionality. | Generic normalization and constant embedding | Proved | `books/polynomial/generic/degree.lisp` and the PFIELD/F7 definitions in `generic/pfield-instance.lisp`. |
| POLY-DEGREE-MUL | For nonzero canonical polynomials, `degree(f*g)=degree(f)+degree(g)`. | The structural theorem `raw-leading-coefficient-of-raw-mul` identifies the final convolution coefficient; `equal-field-mul-zero` makes it nonzero. | Generic field no-zero-divisors; raw-product length | Proved | `canonical-polynomial-p-of-raw-mul-when-nonzero`, `normalize-of-raw-mul-when-canonical-nonzero`, `poly-leading-coefficient-of-poly-mul`, and `poly-degree-of-poly-mul` in `books/polynomial/generic/degree.lisp`. |
| GPOLY-NONZERO-MUL | A product of nonzero canonical generic polynomials is nonzero. | Its final raw coefficient is the product of two nonzero field elements. | POLY-DEGREE-MUL | Proved | `consp-of-poly-mul-when-canonical-nonzero` in `books/polynomial/generic/degree.lisp`. |
| PFIELD-ROOT-COUNT-BRIDGE | Transport `PFIELD::NUM-ROOTS-OF-POLY-UPPER-BOUND` to nonconstant canonical HS polynomials. | The certified conversion preserves evaluation and roots; canonical HS final coefficients are nonzero FEP representatives. | `books/polynomial/degree.lisp`; `books/polynomial/pfield-bridge.lisp` | Proved | `hs-pfield-polynomial-num-roots-upper-bound` gives the HS-facing result. |

# Abstract polynomial division reuse

The feasibility study in `docs/abstract-polynomial-bridge-feasibility.md`
found that the 2006 FUNPOL quotient/remainder books cannot be connected to the
explicit-modulus HS/PFIELD interface by a small functional instance.  A future
HS division development still owes canonical quotient and remainder outputs,
the quotient--remainder reconstruction identity, and the strict remainder-
degree bound for a nonzero divisor.  Do not treat inclusion of
`FUNPOL::QUOT-REM-REWRITE` alone as discharge of these obligations.
