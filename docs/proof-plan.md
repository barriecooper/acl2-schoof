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
linear natural repeated-addition operation. The next open formalization
boundary is **fast natural scalar multiplication with correspondence to
`curve-point-nat-mul`**.

## Immediate sequence

Proceed with one bounded mathematical or execution boundary per proof change:

1. Define a separate double-and-add natural scalar operation and certify its
   correspondence to `curve-point-nat-mul`, verified guards, and focused
   execution evidence.
2. Certify the generic nested natural-scalar theorem
   `m • (n • P) = (mn) • P` unless step 1 establishes it as a required
   supporting theorem.
3. Extend the generic and curve interfaces to signed scalar multiplication.
4. Return to the common Hasse/Schoof dependency plan below.

Stop step 1 unless the optimized operation remains separate from the linear
specification and has a semantic correspondence theorem. Stop steps 2 and 3
unless their group context and totalisation behavior are explicit. Guard
verification and concrete evaluation never substitute for these mathematical
endpoints.

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
