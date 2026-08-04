# Generic field kernel

## Purpose and boundary

`books/field/kernel.lisp` is the project-local equational field interface.  It
contains no modulus, field specification, cardinality, characteristic,
enumeration, Frobenius operation, polynomial operation, or extension-field
representation.  It deliberately reuses the sound `encapsulate` and functional
instantiation pattern seen in Community Books' 2006 `FLD` development, but not
that development's large dependency chain, overloaded package symbols,
explicit quotient equivalence, or abstract-polynomial layer.

The constrained functions and exact arities are:

| Symbol | Arity | Meaning |
|---|---:|---|
| `field-element-p` | 1 | carrier predicate |
| `field-fix` | 1 | canonical representative |
| `field-zero` | 0 | additive identity |
| `field-one` | 0 | multiplicative identity |
| `field-add` | 2 | addition |
| `field-mul` | 2 | multiplication |
| `field-neg` | 1 | additive inverse |
| `field-inv` | 1 | total multiplicative inverse |

`field-equiv`, of arity 2, is a derived definition: it is equality of the two
fixed representatives.  It is not an independent constrained relation.
Consequently all mathematical equality is ordinary ACL2 `equal` after fixing,
and there is no second, potentially inconsistent equality model.

## Contracts

The encapsulate proves that the carrier predicate is Boolean, fixing always
produces a carrier element, fixes carrier elements unchanged, and is
idempotent.  Zero and one are fixed carrier elements and are distinct.
Addition, multiplication, negation, and inversion produce fixed values and are
unchanged when their arguments are fixed.

Addition is associative and commutative, has zero as identity, and negation
supplies an inverse.  Multiplication is associative and commutative, has one as
identity, and distributes over addition.  Every nonzero fixed value multiplied
by its inverse is one.  `field-inv` is total, with `field-inv(field-zero())`
fixed by contract to `field-zero()`; this convention has no mathematical
meaning beyond making the ACL2 function total.

The laws are stated for arbitrary ACL2 objects because each operation behaves
as though its arguments were first fixed.  Thus they immediately imply the
usual carrier-hypothesis form without forcing every downstream equational
proof to repeat recognizer hypotheses.

## Derived algebra

The kernel defines subtraction (`field-sub`, arity 2), division (`field-div`,
arity 2), and natural exponentiation (`field-pow`, arity 2).  It proves left
and right zero/one and inverse laws, additive inverse uniqueness and
cancellation, multiplication by zero, negation of zero and double negation,
subtraction by self and zero, multiplicative cancellation and inverse
uniqueness under a nonzero hypothesis, inverse of one, nonzeroness and double
inversion, division by one, power zero/successor/closure.  This is intentionally a compact algebra seam, not a comprehensive field
library.

## Instantiation and execution

Constrained operations are a logical theorem interface, not a directly
executable field implementation.  A concrete implementation defines executable
functions of exactly the arities above, proves the constraints, and reuses a
generic theorem with `:functional-instance`; theorem copies need not be
generated merely to reason about an instance.

`books/field/examples/f2.lisp` is the permanent regression: executable Boolean
`F_2` operations instantiate the kernel, and its double-negation theorem is
obtained by functional instantiation.  `tests/field-kernel.lisp` executes
addition, multiplication, negation, nonzero inversion, subtraction, division,
and exponentiation.

The separately constrained `finite-field-*` coding context uses renamed field
operations admitted together with bounded coding evidence.  It is not a
downstream strengthening of this unrestricted model.  This kernel remains the
source theorem universe, and finite-field results reuse its derived mathematics
by functional instantiation.

A future PFIELD adapter will close over (or otherwise select at its concrete
API boundary) an explicit prime modulus and expose matching unary/binary
wrappers for an instance proof.  The modulus does not become an extra argument
of generic operations.  Runtime APIs that select among fields may still carry
an explicit specification; this logical kernel does not hide a global field
constant.

Finite cardinality and Frobenius are deferred because they are not field laws:
they require a later finite-field interface with characteristic and certified
enumeration/rank data.  PFIELD adapters, extension fields, generic polynomials,
and migration of the existing HS polynomial layer are likewise separate
focused tasks.

## Trust

The only abstraction mechanism is ordinary ACL2 `encapsulate` with executable
local Boolean-field witnesses.  No skipped proof, axiom, trust tag, raw Lisp,
or uncertified include is used.  The existing trust scanner requires no change:
it scans trust-expanding forms, not sound encapsulates.
