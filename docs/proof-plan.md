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

1. Transport the certified single-field semantic soundness theorem for the
   complete quotient-coordinate trace candidate into the ambient field needed
   for classical torsion coordinates.  The existing boundary preserves the
   q-power and iterated q-power actions and both cross predicates at every root
   represented in the same field; it does not assert that this field contains
   all of `E[3]`.
2. Connect the semantically evaluated cross-multiplied predicate to the actual Frobenius
   trace congruence modulo `ell`.  A narrowly scoped classical `E[3]`
   interpretation remains open and should be introduced only where that
   correctness proof requires it; constructing a general ambient-field or
   algebraic-closure model is not on executable Schoof's critical path.
3. Generalize to enough torsion primes and certify the next required executable
   client.  No `ell=5` client is currently certified.
4. Certify enough correct residues that their modulus product exceeds the Hasse
   uniqueness bound.  Modulus 3 alone is insufficient for F11; numerically
   `3*5=15 > 4*sqrt(11)`, but this does not certify either residue's classical
   correctness or an `ell=5` implementation.
5. Reconstruct the unique trace in the Hasse interval by bounded CRT.
6. Compose the result into final point-count correctness and the executable
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
