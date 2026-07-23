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
| POLY-DEGREE-MUL | For nonempty canonical polynomials, `degree(f*g)=degree(f)+degree(g)`; their raw convolution is canonical and their product is nonzero. | The ordered product of the final coefficients is nonzero by the field no-zero-divisor law, so normalization preserves the complete raw convolution and its length. | `RAW-LEADING-COEFFICIENT-OF-RAW-MUL`; raw coefficient closure, nonemptiness, and length; `EQUAL-FIELD-MUL-ZERO`; normalization identity | Proved | The theorem group in `books/polynomial/generic/degree.lisp` proves raw canonicality, normalization identity, the public leading-coefficient formula, degree addition, and product nonemptiness without evaluation extensionality or commutativity. |
| GPOLY-MONOMIAL-SHIFT | Total canonical multiplication by `X^(nfix n)` and construction of `field-fix(a)*X^(nfix n)`, with closure, composition, length, degree, leading-coefficient, and nonzero laws. | Prepend field-zero coefficients to the normalized nonzero dense list; its nonzero final coefficient is unchanged. | Generic normalization, constants, degree, and leading coefficient | Proved | `books/polynomial/generic/monomial.lisp`; all three new functions have verified guards. |
| PFIELD-ROOT-COUNT-BRIDGE | Transport `PFIELD::NUM-ROOTS-OF-POLY-UPPER-BOUND` to nonconstant canonical HS polynomials. | The certified conversion preserves evaluation and roots; canonical HS final coefficients are nonzero FEP representatives. | `books/polynomial/degree.lisp`; `books/polynomial/pfield-bridge.lisp` | Proved | `hs-pfield-polynomial-num-roots-upper-bound` gives the HS-facing result. |

| GPOLY-DIV-CANCEL | Prove that subtracting the appropriate shifted leading-coefficient ratio cancels the current leading term and strictly lowers degree. | Field inverse and the certified monomial/shift leading-term laws. | `GPOLY-MONOMIAL-SHIFT`; certified product leading-term group | Proved | `books/polynomial/generic/division-step.lisp` certifies the one-step term, product, structural decrease, and reconstruction theorems. |
| GPOLY-DIV-RECURSION | Define the total deterministic `poly-divmod` returning canonical quotient and remainder, including the documented zero-divisor fallback. | Recurse on strict degree decrease, equivalently canonical natural length. | `GPOLY-DIV-CANCEL` | Open | Implement no earlier than the next division task. |
| GPOLY-DIV-RECONSTRUCTION | For nonzero canonical divisor, prove `f = q*g+r`; derive exact division when `r=nil`, zero-dividend, and divisor-one reductions. | Accumulate each certified cancellation step. | `GPOLY-DIV-RECURSION` | Open | Prove formal polynomial equality structurally. |
| GPOLY-DIV-DEGREE-BOUND | Prove `r=nil` or `degree(r)<degree(g)` for the result. | Recursion stops exactly below divisor degree. | `GPOLY-DIV-RECURSION`; strict cancellation | Open | Certify the remainder bound. |
| GPOLY-EUCLIDEAN | Complete polynomial division and remainder, then gcd and extended-gcd consequences. | Leading-term cancellation over a field with a strictly decreasing remainder degree. | All open GPOLY-DIV obligations above | Open | Keep gcd, Bézout, uniqueness, irreducibility, and extension-field reduction downstream; do not treat the monomial foundation as completed division. |

# Abstract polynomial division reuse

The feasibility study in `docs/abstract-polynomial-bridge-feasibility.md`
found that the 2006 FUNPOL quotient/remainder books cannot be connected to the
explicit-modulus HS/PFIELD interface by a small functional instance.  A future
HS division development still owes canonical quotient and remainder outputs,
the quotient--remainder reconstruction identity, and the strict remainder-
degree bound for a nonzero divisor.  Do not treat inclusion of
`FUNPOL::QUOT-REM-REWRITE` alone as discharge of these obligations.
