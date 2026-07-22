# Proof plan

Each milestone must remain independently certifiable.

The current certified development is only over prime fields `F_p`; the
long-term target is arbitrary finite fields `F_q`, where `q = p^n`.  Further
polynomial algebra is paused at the coefficient-field architecture decision in
`finite-field-architecture.md`.  A milestone is complete only when its stated
ACL2 obligations are genuinely proved and certified.

1. Prime-field polynomial arithmetic, canonical forms, evaluation, and degree
   (current certified implementation), plus the completed abstract field
   kernel and its completed certified fixed-prime PFIELD adapter.  The generic dense-polynomial foundation (representation, normalization, and
   evaluation), its generic additive structure (addition, negation, and
   subtraction), generic canonical scalar multiplication, and the canonical
   polynomial multiplication definition with evaluation semantics are also
   complete.  Structural commutativity, distributivity, and associativity are
   the immediate next tiny proof-engineering PR; multiplication is not marked
   algebraically complete until those laws certify.  A small polynomial-ring
   consolidation and constant-polynomial embedding follows, then degree and
   leading coefficient.  The executable-instantiation policy is
   recorded in `executable-instantiation.md`: abstract algorithms, ordinary
   executable concrete definitions, and certified correctness bridges are all
   required for future computational layers.  Generic polynomial division,
   extension fields, and arbitrary finite fields are not complete.
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
