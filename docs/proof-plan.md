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
regressions, and `x^2+1` is certified irreducible over F7. A reusable
fixed-modulus field interface now packages canonical remainder representatives
and the complete GFIELD-shaped contract over a constrained nullary irreducible
modulus; an F7 regression simultaneously instantiates the coefficient field,
polynomial stack, modulus, and wrappers. A proof-only F7X2 regression also
simultaneously maps that complete stack and all nine existing F7X2 definitions
to the generic interface without changing their execution or public API.

F7X2 currently supplies canonical representatives, transparent
addition/negation/subtraction/multiplication, and a total executable inverse
candidate with an explicit zero branch. Its certified laws include
zero/one distinctness, the additive group laws and cancellation,
multiplicative identities and zero, associativity and commutativity of
multiplication, and distributivity. The generic nonzero inverse law is certified
for the unchanged operations under a regression-prefixed compatibility theorem,
but ordinary public F7X2 inverse theorems and formal field packaging remain
open; this is not yet a public field interface.

## Near-term shared algebra

1. Review the proof-only F7X2 compatibility evidence before deciding whether to
   replace bespoke proof bodies, export generic-derived inverse theorems under
   ordinary F7X2 names, or add formal GFIELD client packaging; do not treat
   either regression book as a public F7 API.
2. Instantiate generic outer polynomials over a resulting concrete field client and
   add the finite-field metadata and Frobenius interfaces needed by both
   downstream tracks.
3. Develop short-Weierstrass curve coordinates and group operations for
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
