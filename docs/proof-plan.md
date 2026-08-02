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

## Completed foundations

The current certified base includes the generic field kernel, canonical dense
polynomial arithmetic, Euclidean division, GCD and XGCD, modular inversion,
irreducible fixed-modulus quotient fields, short-Weierstrass representations,
and the executable and independent semantic layers for full tagged-point
addition. Executable output closure, literal left/right infinity identity,
transparent point negation, involution, literal left/right inverse,
commutativity, associativity, and algebraic left/right cancellation are
complete. Concrete F7, F7X2, and F11
books supply focused instantiation and execution regressions rather than
additional generic scope.

## Phase 1: complete associativity

### Completed boundaries

The certified semantic base includes relation-witness original-infinity,
opposite/opposite, and repeated-triple structural predecessors, inverse/secant, inverse/tangent, the
complete D/D family, and the complete oriented mixed-inner D/T family.  Its
left-outer-secant boundary combines the distinct-x and coincident-x outcomes,
while its separate O/O boundary preserves the witness-free infinity result.
These results establish the intended division-free
certificate workflow. The reversed T/D family is also certified as a purely
structural mirror; exact current coverage is maintained in the
[associativity status matrix](status-associativity.md). The mixed D/T residuals,
countermodel, and endpoint derivations are preserved in the
[mixed D/T audit](audits/mixed-dt-certificate.md), not repeated here.

### Forward boundaries and completion criteria

The executable dispatcher lift is complete: soundness and closure provide four
dispatcher witnesses to `curve-point-addition-relation-associative`, and
canonical output turns its fixed-output equality into literal executable
equality. Proceed with one bounded boundary per proof change:

1. **Group packaging.** With cancellation and its public regressions complete,
   package the certified laws behind an abstract abelian-group interface.
2. **Scalar multiplication.** Specify and certify repeated addition only after
   the group boundary is complete.

The stopping conditions prevent semantic assembly from hiding unfinished
coordinate work and prevent dispatcher expansion from replacing the
independent semantic proof. New characteristic premises must be justified by a
real degeneration; existing characteristic-independent certificates must not
be weakened.

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
