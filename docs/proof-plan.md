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
   coefficient laws and explicit `nfix` behavior.  The maintained division contract, one-step cancellation, and recursive generic
   division are certified, including reconstruction and the final strict
   remainder-degree bound. Generic modular reduction and congruence are also
   certified, including compatibility with addition, negation, subtraction,
   and multiplication. The Euclidean remainder step now has a certified
   normalized-divisor-length descent theorem. The raw `POLY-EUCLIDEAN-GCD`
   recursion is now admitted on `(len (normalize second))`: it stops at an
   empty normalized second argument, otherwise transitions from `(a,b)` to
   `(b,poly-remainder(a,b))`, and has certified canonical output. It is not
   monic, and no divisibility or algebraic gcd correctness is claimed. The next
   focused milestone is the missing generic divisibility interface followed by
   common-divisor invariance across one Euclidean step; monic normalization,
   greatestness, associates/unit invariance, extended gcd, and Bézout remain
   open. Later power uses include
   extension-field arithmetic,
   Frobenius, derived finite-field inversion, irreducibility tests,
   elliptic-curve scalar/endomorphism calculations, and Schoof computations.
   The executable-instantiation policy is
   recorded in `executable-instantiation.md`: abstract algorithms, ordinary
   executable concrete definitions, and certified correctness bridges are all
   required for future computational layers.  Concrete generated division, extension fields, and arbitrary finite-field
   execution are not complete.
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

## Architecture and top-down interfaces

GPOLY is authoritative for new polynomial algebra. The older HS/PFIELD
polynomial stack remains a legacy/root-count bridge unless a specific bridge
requires it; gcd, derivative, quotient-ring, and
extension-field work should not be independently duplicated in both stacks.
The raw generic Euclidean computation now uses the certified normalized-divisor-
length descent and returns a canonical, potentially non-monic result. The
immediate mathematical milestone is a generic divisibility interface and the
two directions of common-divisor invariance across a remainder step. Algebraic
gcd correctness, monic normalization, extended gcd, and Bézout correctness are
still open. No concrete PFIELD/F7 gcd API was introduced, and recursive
concrete F7 divmod remains postponed. The first executable
Schoof path may target a named prime field; arbitrary finite-field execution is
a later architectural phase.

Top-down planning requires interfaces for base-to-extension-field embedding,
q-power Frobenius, Frobenius preservation of the curve, Frobenius fixed points
corresponding to rational points, finite splitting certificates, fibre-to-kernel
completeness, and endomorphism degree and separability. These are requirements,
not imported code or claims of proof.
