# Proof plan

This document is forward-looking. Exact item-by-item status belongs only in
`obligations.md`; certified interfaces are summarized here only to establish
the starting boundary.

## Starting boundary

The shared generic field/polynomial kernel is certified through recursive
division, reduced representative arithmetic, GCD, XGCD, modular inverse,
logical irreducibility, the irreducibility-to-monic-GCD-one bridge, and
irreducible-modulus inverse laws. The concrete F7 stack carries those
algorithms through guard-verified modular inverse with exact execution
regressions, and `x^2+1` is certified irreducible over F7.

F7X2 currently supplies canonical representatives and transparent
addition/negation/subtraction/multiplication. Its certified laws include
zero/one distinctness, the additive group laws and cancellation,
multiplicative identities and zero, associativity and commutativity of
multiplication, and distributivity. This is not yet a field interface.

## Near-term shared algebra

1. Complete the minimal F7X2 field interface without treating isolated
   characteristic lemmas as an automatic next step. Keep logical field laws,
   executable operations, verified guards, and exact execution regressions
   explicit and separate.
2. **Architecture pause:** once that minimal interface certifies, extract or
   design a reusable construction for quotients by certified irreducible
   polynomials. F7X2 is a proving ground, not the final constructor, and no
   general quotient-field constructor exists yet.
3. Instantiate generic outer polynomials over the resulting field interface and
   add the finite-field metadata and Frobenius interfaces needed by both
   downstream tracks.
4. Develop short-Weierstrass curve coordinates and group operations for
   characteristic greater than three. Characteristics two and three are out of
   the initial scope.

General polynomial quotients used for Schoof coordinates are distinct from
irreducible quotients promoted to coefficient fields: their moduli need not be
irreducible.

## Parallel tracks after shared prerequisites

The common algebraic kernel supports both developments. Once the shared finite
field, polynomial, curve, and Frobenius prerequisites exist, proceed in
parallel:

### Manin-style Hasse track

Develop rational-function and valuation-at-infinity machinery, curve
endomorphisms and degree, Frobenius/scalar-map relations, kernel/fibre and
separability results, the point-count connection, and the integer quadratic
conclusion yielding Hasse's bound.

### Executable Schoof track

Develop quotient-coordinate arithmetic, Frobenius reduction, division
polynomials, trace-residue testing, and bounded incremental CRT reconstruction.
Completion of the Hasse proof is not an implementation prerequisite for this
track.

## Evidence and acceptance criteria

Certification establishes logical claims. Guard verification establishes that
an executable branch is admissible for its guard. Exact regressions establish
selected concrete behavior. None of these alone establishes practical
performance.

Before claiming a practical Schoof implementation, measure compiled ACL2
execution; polynomial remainder and modular-power workloads; normalization and
allocation costs in hot loops; quotient multiplication and Frobenius;
division-polynomial scaling as `ell` grows; incremental CRT; and end-to-end
results against direct point enumeration on small fields. These are future
acceptance criteria, not current certified achievements. Detailed performance
items are tracked in `obligations.md`.

## Historical records

Older audit and reconnaissance documents preserve design evidence and the
sequence appropriate at the revision when they were written. Their “next PR”
or proposed-sequence sections are historical unless restated above. They do
not override this plan or the status ledger.
