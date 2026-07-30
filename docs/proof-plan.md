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
addition. Output closure, infinity identity, inverse-to-infinity, and full
commutativity are complete. Concrete F7, F7X2, and F11 books supply focused
instantiation and execution regressions rather than additional generic scope.

## Completed semantic H reconstruction

The field-only theorem `xcert-h-scalar-reconstruction` derives the exact
factor-ordered equality `(p-r)(p+q)=xa-xc` from the audited seven scalar
equations and only `xc-xb != field-zero`; E2 is unused.  Its semantic
instantiation `xcert-h-curve-zero` maps `p`, `q`, and `r` to the ordered slopes
`(A,B)`, `(AB,C)`, and `(B,C)` and certifies the existing specialized H
expression as `field-zero`.  The field-only exact S reconstruction is complete as
`xcert-s-scalar-reconstruction`, and `xcert-s-curve-zero` specializes it to the
four ordered nested distinct-x pairs.  Its two ordered nonzero premises serve
the H and final-S cancellations separately.  The next coherent boundary is an
audit of the algebra needed after the separate H-zero and S-zero results;
  The same seven-hypothesis configuration now also certifies equality of the
  two final x-coordinates by simplifying the maintained composition with both
  H-zero and S-zero.  The next boundary is the field-only final-y
  reconstruction needed before semantic y-coordinate equality.  Its
  output-x/H coordinate bridge is now certified; the next boundary is the
  six-residual reduction of the final y difference, followed by their
  field-only composition.  Exceptional cases and associativity remain later
  work.

## Phase 1: prepare associativity

Associativity is not ready for a direct proof attempt. The next mathematical
task is a dedicated audit of the existing field and coordinate theory against
the identities required to compare the nested additions in all semantic cases.
That audit must:

1. inventory reusable denominator-nonzero, cancellation, substitution, fixing,
   and normalization lemmas already certified;
2. identify which branch combinations can share division-free algebra instead
   of expanding executable dispatchers;
3. determine the missing reusable polynomial/field identities and coordinate
   equivalences without weakening the associativity statement; and
4. record the resulting tight lemma groups in `docs/obligations.md` before
   beginning the full case proof.

The repository does not yet establish a sufficiently detailed associativity
strategy to predict the final case decomposition. The audit, not an
associativity theorem, is therefore the next boundary. After its prerequisites
are certified, prove semantic associativity first and derive the executable
statement through soundness and determinacy. Then consider cancellation and
abstract group/abelian-group packaging.

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
