# Proof plan

This document owns forward mathematical dependency order. Current theorem-level
status is in the [obligation ledger](obligations.md); stable design is in
[architecture](architecture.md).

## Destination and shared seam

The long-term destinations are a Manin-style proof of Hasse's theorem and an
executable, certified Schoof point-counting algorithm. They share field,
polynomial, curve, and some Frobenius foundations; whether they should share a
rational-function or morphism representation remains unresolved. Beyond that
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

1. Use the selected Silverman V.1.1 Frobenius/positive-quadratic-degree route
   for the first abstract Hasse theorem.  Before implementation, run the
   bounded ambient/base-field feasibility experiment specified by the
   [Hasse source and dependency audit](audits/hasse-source-and-dependency.md).
   It must resolve how non-rational ambient points, a nontrivial `q`-power
   Frobenius, the base-field embedding, and both fixed-point directions can be
   stated and realized.  Do not combine finite cardinality, `x^q=x`, the new
   two-field architecture, and curve Frobenius into one implementation change.
2. Add a polynomial natural-scaling interface when the derivative power rule
   or another concrete client requires it.
3. The separate finite-field coding context is complete, with coherent field
   operations and bounded rank/unrank evidence validated by PFIELD and F7.  The
   renamed `finite-field-*` operations now drive a certified transparent GPOLY
   core, and generated divmod cores expose a standardized recursive equation
   theorem. The finite-field recursive divmod and projection bridge is now certified by direct accumulator invariants; the public remainder/reduced-polynomial layer and fixed-modulus coefficient-vector extraction/reconstruction boundary are certified. A staged finite-field-prefixed explicit-modulus reduced-ring target interface is certified through transparent operation-then-remainder definitions, verified guards, definition equations, and reduced-add commutativity only; finite-field remainder/add compatibility and reduced-add associativity are the next reduced-ring seam.
   Generic mixed-radix rank/unrank for exact-width coefficient vectors is certified; generic
   finite-field fixed-modulus carriers and representative-count cardinality are certified.
   Concrete F7X2 is now a certified public nullary `GFIELD` instance, reusing
   its existing executable operations and the fixed-modulus inverse proof. The
   full finite-field-prefixed reduced-ring instance, inverse transport, and
   field-facing generic extension packaging remain open because the existing
   quotient-field package is still tied to its separate nullary
   irreducible-modulus construction.
4. The field-facing bridge between the explicit finite-field representative
   count and the nullary irreducible fixed-modulus field remains open, but is
   deferred from the immediate abstract Hasse critical path.  Develop it when
   a generic quotient-field Hasse instance, an ambient-field realization, or a
   Schoof client requires it.  Cardinality-based Frobenius must use actual
   certified cardinality rather than `field-frobenius-exponent`; prime-power
   and characteristic compatibility remain separate obligations.
5. Add fast natural scalar multiplication only when an executable quotient-
   coordinate or trace-test consumer makes it more than premature
   optimization.

Keep future derivative bridges bounded to their concrete coefficient laws; do
not replace them with a broad list-algebra project. Any later fast
scalar operation must remain separate from the linear specification and have a
semantic correspondence theorem. Guard verification and concrete evaluation
never substitute for these mathematical endpoints.

## Phase 2: common curve and function-field infrastructure

Once the ambient/base-field feasibility boundary is resolved, develop only the
common infrastructure demanded by a concrete client.  No broad
rational-function, morphism, or isogeny library is authorized yet; a
purpose-built representation remains a candidate.  Exact sequencing depends
on the risk-first experiment and no completion is implied here.

## Phase 3A: Manin-style Hasse track

The selected primary route is Silverman, *The Arithmetic of Elliptic Curves*,
V.1.1, using the positive quadratic degree form of III.6 (especially III.6.3)
and the required III.4--III.5 isogeny/dual-isogeny results.  After the
ambient/base-field boundary is resolved, formalize only the function-field or
morphism degree fragment actually required to derive the preferred first
endpoint `(q + 1 - N)^2 <= 4q`.  Reuse the common polynomial and curve layers.

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

Next Hasse boundary: perform the bounded ambient/base-field feasibility
specification from the Hasse audit.  It is a risk-first experiment, not an
implementation of field Frobenius or curve Frobenius.  Keep the deferred
extension-field carrier/fixer bridge, broad morphism infrastructure, and Schoof
machinery separate.

## Finite-field division-step substrate

The finite-field-prefixed one-step polynomial division substrate is certified.
It uses transparent generated definitions for the core step and public term/next
projections, with verified guards, reconstruction, strict degree decrease, and a
strict core length theorem suitable for the future recursive divmod measure.  The
decisive cancellation proof is length/leading-coefficient based, not
coefficient-vector or coding based.  Recursive finite-field divmod and public quotient/remainder APIs are certified; fixed-modulus representations and coding/cardinality operations remain open and are not introduced here.
