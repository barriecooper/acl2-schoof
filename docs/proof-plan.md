# Proof plan

Each milestone must remain independently certifiable.

The current certified development is only over prime fields `F_p`; the
long-term target is arbitrary finite fields `F_q`, where `q = p^n`.  Further
polynomial algebra is paused at the coefficient-field architecture decision in
`finite-field-architecture.md`.  A milestone is complete only when its stated
ACL2 obligations are genuinely proved and certified.

1. Prime-field polynomial arithmetic, canonical forms, evaluation, and degree
   (current certified implementation), followed by the abstract coefficient
   kernel and PFIELD instance described in the architecture decision.
2. Certified extension fields and generic polynomial instances, then rational
   functions over `F_q(t)` and well-defined operations.
3. Valuation at infinity, including product and cancellation laws.
4. Generic twisted elliptic curve over an abstract finite field and its
   rational-function group operations.
5. Frobenius/scalar-multiplication maps and their quadratic degree sequence.
6. Point-count connection, kernels, and the necessary separability results.
7. Integer quadratic conclusion yielding Hasse's bound.
8. Division polynomials and quotient-coordinate algebra.
9. Schoof trace residues and certified CRT reconstruction.
