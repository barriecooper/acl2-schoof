# Executable polynomial instantiation

## Current interface

Generic GPOLY algorithms are ordinary certified definitions over the GFIELD
operation interface. Named fields provide ordinary executable operations and
functional substitutions that transport the generic semantic theorems. A
concrete layer is complete only to the extent recorded in `obligations.md`.

For F7, the retained concrete polynomial interface includes guard-verified
recursive quotient/remainder and projections, raw and monic GCD, raw and monic
XGCD, and modular inverse. Focused exact executions cover their intended
runtime paths. The earlier inverse/division guard failure was resolved by the
named F7 field boundary and is historical, not a current blocker.

The generic remainder is the canonical representative operation. Reduced
addition, negation, subtraction, and multiplication compose an existing
polynomial operation with that remainder. F7X2 fixes representatives modulo
`x^2+1` and exposes transparent arithmetic through this architecture. These
ordinary definitions do not introduce an `MBE`, `DEFEXEC`, attachment, or
alternate logical/executable body.

## Assurance layers

Keep these claims separate:

1. **Logical specification:** generic algebraic statements and representation
   invariants.
2. **Executable implementation:** ordinary named functions for a concrete
   field or quotient presentation.
3. **Semantic bridge:** certified functional instances, invariants, or
   equivalence theorems connecting implementation to specification.
4. **Guard assurance:** explicit guard verification for executable functions.
5. **Execution regression:** exact concrete evaluations demonstrating the
   intended path and boundary behavior.
6. **Performance evidence:** compiled runs and benchmarks; this is empirical
   evidence and does not prove semantic correctness.

Guard verification is not semantic correctness, and regressions are not either.
Conversely, a logical theorem about constrained operations does not by itself
supply a useful concrete runtime.

## Extension-field direction

The certified F7 irreducibility result and generic irreducible-modulus inverse
laws support the current F7X2 proving ground. F7X2 is presentation-specific and
must not be advertised as a reusable quotient-field constructor. After the
minimal F7X2 field interface is complete, pause to extract or design a reusable
irreducible-quotient-field pattern, with named specification, implementation,
semantic bridge, verified guards, and focused regressions.

General quotient-coordinate rings for Schoof are a separate use of the same
remainder foundation and do not require irreducible moduli. Future executable
Schoof work requires quotient-coordinate arithmetic, Frobenius, division
polynomials, trace testing, and bounded incremental CRT.

## Performance boundary

No current certification implies practical complexity. Future acceptance must
include compiled ACL2 measurements of polynomial remainder and modular power,
normalization/allocation behavior in hot loops, quotient multiplication and
Frobenius, division-polynomial growth in `ell`, incremental CRT, and end-to-end
comparison with direct enumeration on small fields. The detailed open criteria
are maintained only in `obligations.md`.

## Historical note

Early experiments found that direct concrete F7 division inherited an
unverified inverse guard. That observation explained an earlier design pause;
it was superseded when the named F7 guard architecture, recursive division,
XGCD, and modular inverse certified. It must not be used as current planning
guidance. Generic modular reduction is likewise already certified and is not a
future mathematical PR.
