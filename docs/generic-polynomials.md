# Generic dense polynomials

`books/polynomial/generic/package.lisp` establishes the dedicated `GPOLY`
namespace, `base.lisp` defines the abstract theory over `GFIELD`, and
`pfield-instance.lisp` is its PFIELD/F_7 regression.  The existing `HS` books
are unchanged.

A list `(c0 ... cn)` is dense and constant-first.  `POLYNOMIAL-P` deliberately
means a proper list of fixed field elements; it does **not** imply canonicality.
`CANONICAL-POLYNOMIAL-P` additionally admits only `nil`, the unique zero, or a
list whose last coefficient is not `GFIELD::FIELD-ZERO`.  Internal zeroes are
retained.  Canonical polynomial equality is ordinary ACL2 `EQUAL` because all
coefficients are canonical representatives.

`FIX-COEFFICIENTS` applies `GFIELD::FIELD-FIX` elementwise.
`TRIM-TRAILING-ZEROS` recursively removes only the zero suffix, and `NORMALIZE`
composes those operations.  `EVAL` uses Horner recursion for constant-first
coefficients: the head plus the fixed point times the recursively evaluated
tail.  It fixes every coefficient and the point.

All functions are total.  Atoms terminate list recursion, so a dotted or other
malformed tail is discarded.  Normalization fixes arbitrary heads before
trimming.  Evaluation treats an atomic polynomial as field zero and otherwise
lets the total field fixer handle malformed coefficients and points.  Guards
are not part of logical correctness.

The certified structural results cover properness and identity of fixing,
trimming closure and its nonzero-last property, canonical normalization,
identity on canonical inputs, idempotence, the nil/nonzero conventions, and
non-increasing length.  Evaluation is field-valued and is invariant under point
fixing, coefficient fixing, trimming, and normalization; constant and zero
point formulas are also proved.

The adapter regression defines exact copies using the fixed-arity PFIELD
operations and transports normalization-preserves-evaluation with
`:functional-instance`.  Separate executable copies specialize the same
recurrences to F_7 and compute fixing, trimming, internal-zero, constant,
nonconstant, and wraparound examples.

## Relationship to HS and deferred bridge

Both GPOLY and HS are dense, constant-first coefficient lists with `nil` as the
canonical zero.  HS stores PFIELD elements and threads an explicit modulus;
GPOLY uses the abstract GFIELD interface and has no modulus parameter.  A later
bridge may therefore use the identity conversion at a fixed PFIELD instance,
but must prove equivalence of canonical predicates, normalization, evaluation,
and eventually addition and multiplication.

This foundation deliberately contains no polynomial addition, multiplication,
degree, leading coefficient, division, gcd, derivatives, root counting, field
enumeration, or extension-field implementation.  It provides syntax and
semantics over an assumed field, not an implementation of every finite field.

## Preliminary HS proof review

The reusable decomposition was classified before implementation.  Proper-list
recursion, suffix trimming, canonical-last reasoning, normalization identity,
idempotence, and length bounds are **structural (A)**.  Horner closure and
invariance under trimming use only zero, fixing, addition, and multiplication
laws and are **generic field arguments (B)**.  The existing root-count bridge
and PFIELD polynomial recognizers are **PFIELD-specific (C)**.  The HS closure
hypotheses and arithmetic calls that carry `p` through every operation are
**explicit-modulus dependent (D)**.  GPOLY adapts A and B, and intentionally
leaves C and D in the existing HS layer.
