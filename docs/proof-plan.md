# Proof plan

This document owns forward mathematical dependency order. Current theorem-level
status is in the [obligation ledger](obligations.md); stable design is in
[architecture](architecture.md).

## Destinations and shared seam

The long-term destinations are a Manin-style proof of Hasse's theorem and an
executable, certified Schoof point-counting algorithm. They share the generic
field, polynomial, curve, finite-cardinality, and Frobenius foundations, but
neither downstream track is a prerequisite for the other.

The Hasse track uses the adopted hybrid representation: canonical symbolic
maps over a narrow rank-two short-Weierstrass function field for equality,
composition, separability, and degree, and a separate geometric point seam for
Frobenius fixedness and the `ker(1-pi)`/degree bridge. The weakest sufficient
point carrier remains to be selected when that bridge is realized.

The Schoof track uses dense ascending univariate division-polynomial data with
the conventional `2y` factor removed from even indices. Its immediate forward
order is:

1. Complete the narrow **same-field** affine/group-law interpretation of
   the existing denominator-free cross equations.  The ordinary distinct-x
   field cross-add conclusion under valid-affine-point and explicit
   nonzero-denominator premises is certified.  Remaining in this boundary are
   the opposite/infinity conclusion, composition with the
   existing single-field quotient-coordinate semantic soundness theorem at a
   supplied modulus root and curve point in that same `GFIELD` instance.
   Reuse the existing affine curve books; introduce no root construction,
   algebraic closure, ambient carrier, or matrix theory.  Do not claim a useful
   concrete F11 ambient-root corollary: PR #347's ambient seam is only a
   commutative ring and the F11-to-ambient-field operation-preservation
   realization remains open.  Stop if this requires that realization,
   completeness of `E[3]`, or a general division-polynomial semantics layer
   rather than the bounded group-law bridge.  The route rationale and exact
   limits are recorded in the
   [trace-congruence route audit](audits/schoof-trace-congruence-routes.md).

2. Choose and certify the least expensive concrete F11 classical realization
   needed downstream: a narrow F11-to-ambient-field operation-preservation
   context, a universal-root construction, or a concrete certified extension
   witness.  This choice must supply an actual field-facing group-law instance;
   a compatibility lemma over the commutative-ring ambient seam alone is
   insufficient.
3. Supply the remaining classical `E[3]` coverage needed to turn the
   conditional point equation into a statement about every nonzero 3-torsion
   point, then identify the equation's scalar as the actual Frobenius trace
   modulo 3.  Completeness, square-freeness or a universal-root substitute,
   Frobenius preservation, and trace/determinant identification must be
   explicit.  A general algebraic closure and Cayley--Hamilton development are
   not independently on executable Schoof's critical path.
4. Generalize to enough torsion primes and certify the next required executable
   client.  No `ell=5` client is currently certified.
5. Certify enough correct residues that their modulus product exceeds the Hasse
   uniqueness bound.  Modulus 3 alone is insufficient for F11; numerically
   `3*5=15 > 4*sqrt(11)`, but this does not certify either residue's classical
   correctness or an `ell=5` implementation.
6. Reconstruct the unique trace in the Hasse interval by bounded CRT.
7. Compose the result into final point-count correctness and the executable
   Schoof boundary.

The generic and F11 generated-table, relational-sequence, uniqueness, and
all-index evaluator correspondence is certified. Cardinality-based Frobenius must use
certified actual cardinality and compatible characteristic/prime-power
metadata, never merely `field-frobenius-exponent`.

## Hasse dependency order

1. Stage the pure discriminant argument behind explicit abstract
   endomorphism/positive-degree premises, without claiming Hasse or treating a
   false context guard as a realization.
2. Build the narrow rank-two symbolic map fragment, beginning with canonical
   map equality and `deg(pi)=q`.
3. Realize the fixed-kernel/base-point and separable-degree bridge over the
   weakest adequate geometric carrier.
4. Instantiate the arithmetic consumer to derive the public Hasse inequality.

## Completion criteria

A phase is complete only when its registered books certify under repository
trust policy and the obligation ledger records its remaining dependencies.
Guard verification and concrete evaluation are execution evidence, not
semantic correspondence. Chronological completion narratives and proof-debug
history belong in commits, pull requests, and explicitly historical audits.
