# Proof plan

This document owns forward mathematical dependency order. Current theorem-level
status is in the [obligation ledger](obligations.md); stable design is in
[architecture](architecture.md).

## Destination and shared seam

The long-term destinations are a Manin-style proof of Hasse's theorem and an
executable, certified Schoof point-counting algorithm. They share field,
polynomial, curve, rational-function, and Frobenius foundations. Beyond that
shared seam they are parallel: Hasse is not an implementation prerequisite for
Schoof.

## Current formalization boundary

The current certified base includes the generic field kernel, canonical dense
polynomial arithmetic, Euclidean division, GCD and XGCD, modular inversion,
irreducible fixed-modulus quotient fields, short-Weierstrass representations,
and the executable and independent semantic layers for full tagged-point
addition. Executable output closure, literal left/right infinity identity,
transparent point negation, involution, literal left/right inverse,
commutativity, associativity, and algebraic left/right cancellation are
complete. A carrier-based abstract abelian-group interface and its contextual
curve functional instance are also complete. Concrete F7, F7X2, and F11
books supply focused instantiation and execution regressions rather than
additional generic scope.

The certified curve boundary is a contextual abelian group with a transparent
linear natural repeated-addition operation whose scalar action satisfies
`m • (n • P) = (mn) • P`.  The generic polynomial boundary
also includes transparent formal differentiation with canonical output,
additivity, negation, subtraction, the product rule, and a characteristic-safe
length bound.  The first square-free boundary is complete: the total
derivative-coprime predicate has certified zero, constant, and normalization
semantics, and it excludes every supplied positive-degree square divisor.
Repeated-factor characterization and root-based separability remain distinct
later boundaries.

## Immediate sequence

Proceed with one bounded mathematical or execution boundary per proof change:

1. Audit the next downstream polynomial requirement before selecting between
   repeated-factor characterization and another shared Hasse/Schoof boundary;
   do not build factorization theory solely to strengthen the square-free
   predicate.
2. Add a polynomial natural-scaling interface when the derivative power rule
   or another concrete client requires it.
3. The separate finite-field coding context is complete, with coherent field
   operations and bounded rank/unrank evidence validated by PFIELD and F7.  The
   renamed `finite-field-*` operations now drive a certified transparent GPOLY
   core, and generated divmod cores expose a standardized recursive equation
   theorem. The finite-field recursive divmod and projection bridge is now certified by direct accumulator invariants; the public remainder/reduced-polynomial layer and fixed-modulus coefficient-vector extraction/reconstruction boundary are certified. A staged finite-field-prefixed explicit-modulus reduced-ring target interface is certified through transparent operation-then-remainder definitions, verified guards, definition equations, and reduced-add commutativity only; finite-field remainder/add compatibility and reduced-add associativity are the next reduced-ring seam.
   Generic mixed-radix rank/unrank for exact-width coefficient vectors is certified; generic
   finite-field fixed-modulus carriers and representative-count cardinality are certified.
   The full finite-field-prefixed reduced-ring instance, inverse transport, and field-facing generic extension packaging remain open because the existing quotient-field package is still tied to its separate nullary irreducible-modulus construction.
4. Only after actual cardinality evidence is available for the intended
   context, connect that cardinality (not `field-frobenius-exponent`) to the
   Frobenius equation.  Add field-facing generic extension-field cardinality and prime-power
   metadata before the Hasse/Schoof Frobenius clients that need them;
   alternatively select a
   Schoof torsion/division-polynomial boundary or an exact Hasse
   source/dependency audit.  Do not make signed scalar multiplication the
   default merely because natural scalar composition is complete.
5. Add fast natural scalar multiplication only when an executable quotient-
   coordinate or trace-test consumer makes it more than premature
   optimization.

Keep future derivative bridges bounded to their concrete coefficient laws; do
not replace them with a broad list-algebra project. Any later fast
scalar operation must remain separate from the linear specification and have a
semantic correspondence theorem. Guard verification and concrete evaluation
never substitute for these mathematical endpoints.

## Phase 2: common curve and function-field infrastructure

Once the curve laws are adequate for downstream use, develop only the common
infrastructure demanded by the two tracks: scalar multiplication when its
specification is clear, polynomial derivatives and separability, rational
functions and their equality/cancellation theory, and the required Frobenius
facts. Exact sequencing within this phase depends on the associativity audit
and on the chosen primary Hasse reference; no completion is implied here.

## Phase 3A: Manin-style Hasse track

Select and record the exact primary exposition, then formalize the needed
function-field or morphism degree theory, Frobenius/dual relationships, and the
degree inequality from which Hasse's bound follows. Reuse the common polynomial
and curve layers rather than rebuilding them inside the proof.

## Phase 3B: executable Schoof track

Develop division polynomials, quotient-coordinate arithmetic, Frobenius action,
trace-congruence tests, and bounded incremental CRT reconstruction. Each
logical/executable boundary needs an independent specification, a certified
correspondence theorem, verified guards, and focused execution evidence.
Practical benchmarks are performance evidence, not proof of point-count
correctness.

## Completion criteria

A phase is complete only when its books certify under the repository trust
policy and its open obligations are updated in the ledger. Concrete examples
may validate execution and functional instantiation, but cannot substitute for
generic correctness. Chronological PR narratives belong in Git history, not in
this plan.

Next boundary: bridge the finite-field-prefixed representative-count layer to a certified quotient-field package only after choosing the parameterization that connects explicit moduli to the existing nullary irreducible fixed-modulus field construction. Keep Frobenius and Schoof machinery separate.

## Finite-field division-step substrate

The finite-field-prefixed one-step polynomial division substrate is certified.
It uses transparent generated definitions for the core step and public term/next
projections, with verified guards, reconstruction, strict degree decrease, and a
strict core length theorem suitable for the future recursive divmod measure.  The
decisive cancellation proof is length/leading-coefficient based, not
coefficient-vector or coding based.  Recursive finite-field divmod and public quotient/remainder APIs are certified; fixed-modulus representations and coding/cardinality operations remain open and are not introduced here.
