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
   complete.  Generic multiplication is now algebraically complete: its
   commutativity, associativity, and both distributive laws are certified and
   transported through PFIELD to executable F_7.  The explicit canonical
   constant embedding and compact commutative-ring consolidation are complete.
   Reusable natural exponentiation by squaring is complete: a linear proof
   specification, logarithmic executable algorithm, explicit `nfix` behavior,
   generic laws, canonical polynomial instance, and evaluation semantics are
   certified for reuse by fields and later extension fields.  The executable
   F_11 golden field/polynomial fixture for `y^2 = x^3 + x + 6` is complete.
   Generic canonical polynomial degree and leading coefficient, including the
   PFIELD adapter and executable F_7 instances, are complete.  The structural
   leading-term group is also complete for nonempty canonical factors: raw
   multiplication is canonical, normalization preserves the full convolution,
   leading coefficients multiply in operand order, degrees add, and products
   are nonzero.  This uses the field no-zero-divisor law and raw length theorem,
   not evaluation extensionality.  The total, canonical monomial and natural
   degree-shift foundation is also certified, including degree and leading-
   coefficient laws and explicit `nfix` behavior.  The maintained division
   contract is fixed, but recursive division is not implemented.  One-step
   leading-term cancellation is now certified, including exact reconstruction
   and strict structural degree decrease.  The next focused milestone is
   recursive division, then Euclidean theory.  Later power uses include
   extension-field arithmetic,
   Frobenius, derived finite-field inversion, irreducibility tests,
   elliptic-curve scalar/endomorphism calculations, and Schoof computations.
   The executable-instantiation policy is
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


## Generic recursive division (certified)

`books/polynomial/generic/division.lisp` certifies `POLY-DIVMOD-CORE` and the total `(mv q r)` public `POLY-DIVMOD`.  Canonical remainder length is the measure, the one-step decrease theorem supplies termination, and an accumulator invariant supplies normalized reconstruction without evaluation extensionality.  The final remainder is zero or strictly below the normalized nonzero divisor.  Guards are verified separately.  No executable boundary or concrete PFIELD/F7 instance is added; concrete generated division, uniqueness, gcd, and extended gcd remain open.
