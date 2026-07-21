# Open proof obligations

No row marked open is admitted by the ACL2 books.

| Identifier | Theorem statement | Mathematical justification | ACL2 dependencies | Status | Next action |
|---|---|---|---|---|---|
| POLY-CLOSED-ADD | Canonical field polynomials are closed under `poly-add`. | Field addition is closed and normalisation removes a zero leader. | PFIELD closure rules; normaliser lemmas | Proved | `poly-add-is-canonical` in `books/polynomial/base.lisp`. |
| POLY-CLOSED-MUL | Canonical field polynomials are closed under `poly-mul`. | Convolution uses field sums/products. | POLY-CLOSED-ADD, scaling closure | Open | Establish scaling and shifted-add closure. |
| POLY-EVAL-ADD | Evaluation maps polynomial addition to field addition. | Horner evaluation and distributivity. | PFIELD associativity/distributivity | Proved | `poly-eval-of-add` in `books/polynomial/eval.lisp`. |
| POLY-EVAL-MUL | Evaluation maps polynomial multiplication to field multiplication. | Horner evaluation and distributivity. | POLY-EVAL-ADD, scaling evaluation | Open | Prove scaling evaluation first. |
| POLY-DEGREE-MUL | For nonzero canonical polynomials, `degree(f*g)=degree(f)+degree(g)`. | Product leading coefficient is nonzero in a field. | PFIELD no-zero-divisors; closure | Open | Prove the leading-coefficient convolution lemma without unsafe admission. |
