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

Proceed with one bounded mathematical or execution boundary per proof change.
The [ambient-domain and degree-representation audit](audits/ambient-domain-and-degree-representation.md)
adopts a hybrid split: geometric points are used only for fixed-point and
kernel-cardinality statements, while morphism equality and degree receive a
separate symbolic/function-field realization.  The exact point carrier for
`ker(1-pi)` remains open: a directed root-sufficient family is sufficient for a
general kernel theorem but is not mandated by the direct fixed-kernel
calculation.  The experimental F7/F49 context remains feasibility evidence,
not the generic realization.

1. Complete the division-polynomial table/evaluator seam: the sequential
   list-backed builder and its elementary length, stable-lookup, entry, fixing,
   and closure invariants are certified; next add the named full-sequence
   specification and retain a public evaluator only with its correspondence and
   public recurrence equations.
2. Add only the quotient-coordinate laws demanded when the first concrete
   trace-test client requires them.  Preserve arbitrary-ACL2-value and
   zero-normalized-modulus coverage at every public totalized endpoint, and keep
   trace tests in a separate change.
3. On the Hasse track, stage the pure discriminant argument behind explicitly
   abstract endomorphism/degree premises, without claiming Hasse or treating a
   false context guard as realization.
4. Realize those premises through the narrow rank-two short-Weierstrass
   function-field fragment, starting with canonical map equality and
   `deg(pi)=q`; then determine the weakest point-level realization for the
   concrete `ker(1-pi)`/separable-degree bridge, adding a directed carrier only
   if the selected proof genuinely needs arbitrary kernels.
5. Add polynomial natural scaling, fast scalar multiplication, or the deferred
   extension-field carrier/fixer bridge only when one of these concrete clients
   requires it.

Cardinality-based Frobenius must use certified actual cardinality and compatible
characteristic/prime-power metadata, never merely
`field-frobenius-exponent`.  Guard verification and concrete evaluation never
substitute for semantic correspondence.

## Phase 2: shared quotient-coordinate and narrow function-field infrastructure

Develop the finite-field quotient-coordinate laws required by Schoof independently
of Hasse.  For Hasse, the adopted narrow target is a rank-two
short-Weierstrass function-field representation, not a broad rational-map or
algebraic-geometry library.  The geometric-point carrier enters only at the
fixed-point and kernel-cardinality bridge.

## Phase 3A: Manin-style Hasse track

The selected primary route is Silverman, *The Arithmetic of Elliptic Curves*,
V.1.1, using the positive quadratic degree form of III.6 (especially III.6.3)
and the required III.4--III.6 isogeny/dual-isogeny results.  Formalize only the
adopted rank-two function-field/endomorphism degree fragment and the weakest
certified `ker(1-pi)`/degree bridge required to derive the preferred first
endpoint `(q + 1 - N)^2 <= 4q`.  Reuse the common polynomial and curve layers.

## Phase 3B: executable Schoof track

The certified first client represents division-polynomial data as dense univariate polynomials in `x`, with the conventional `2y` factor removed from even indices. It provides indices 0 through 4 and a certified transparent recurrence step over an ascending table, including the exact two odd orientations, the even formula, `C = 4(x^3+ax+b)`, fixing, and closure. The list-backed sequential table and its exact-length, stable-lookup, entry, fixing, and closure invariants are certified; retain a public all-index evaluator only together with its correspondence to the named recurrence. The builder constructs each new entry once and does not use overlapping recursion, while its repeated list extension still traverses prefixes. Add quotient-coordinate arithmetic only at the first trace-test dependency that requires it. Then develop Frobenius action, trace-congruence tests, and bounded incremental CRT reconstruction. Each
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

The next shared/Schoof repository boundary is the smallest additional
finite-field quotient-coordinate law required by a concrete Schoof client;
unconditional reduced-add associativity is certified and does not authorize
completion of the entire reduced-ring or field package.  The next Hasse boundary,
separately, is only an abstract arithmetic consumer for the quadratic degree
premises; no public Hasse claim is permitted until the rank-two symbolic map and
geometric kernel realizations are certified.

## Finite-field division-step substrate

The finite-field-prefixed one-step polynomial division substrate is certified.
It uses transparent generated definitions for the core step and public term/next
projections, with verified guards, reconstruction, strict degree decrease, and a
strict core length theorem suitable for the future recursive divmod measure.  The
decisive cancellation proof is length/leading-coefficient based, not
coefficient-vector or coding based.  Recursive finite-field divmod and public quotient/remainder APIs are certified; fixed-modulus representations and coding/cardinality operations remain open and are not introduced here.
