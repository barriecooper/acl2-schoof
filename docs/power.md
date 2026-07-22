# Natural powers

## Audit and compatibility decision

Before this change the repository had three project power functions.  The
public `GFIELD::FIELD-POW(x,n)`, `GFIELD::PFIELD-POW(x,n)`, and executable
`GFIELD::F7-POW(x,n)` (plus the regression-only `F2-POW`) all had arity two and
used linear recursion through `1-`.  `ZP` made every non-natural exponent act
like zero, bases were not fixed on the recursive path, and all definitions were
directly executable.  `FIELD-POW-ZERO`, `FIELD-POW-SUCCESSOR`, and
`FIELD-ELEMENT-P-OF-POW` depended on the generic definition; the concrete
tests called F2/F7 power.  No downstream functional instance mapped a power
symbol, but changing `FIELD-POW`'s logical recursion would unnecessarily alter
future functional-instantiation obligations.

The Community Books audit found `PFIELD::POW` in
`kestrel/prime-fields/pow.lisp`.  It retains a linear logical definition while
its `MBE` executable branch calls the certified accumulator-based
`MOD-EXPT-FAST`; `arithmetic-5/lib/floor-mod/mod-expt-fast.lisp` documents the
same square-and-right-shift pattern.  Those implementations are tied to
integer modular arithmetic, so this development adopts their trusted ordinary
ACL2 pattern, not their incompatible operation framework.

Consequently the public names and arities are preserved, as is their total
behavior: malformed and negative exponents are explicitly mapped through
`NFIX` to zero.  The new logical body is a named linear specification and the
executable branch is the generated generic accumulator.  The generator expands
only to three ordinary `DEFUN` events.

## Specification, execution, and laws

`DEF-POW-INSTANCE` takes names for the linear specification, fast auxiliary,
and public operation, followed by explicit identity, multiplication, and base
fixer names.  The specification fixes the base and uses the equations
`a^0=one` and `a^(n+1)=a*a^n`.  The auxiliary maintains
`acc * base^n`: it squares `base`, conditionally multiplies `acc` for an odd
bit, and replaces `n` by `(floor n 2)` on every step.  Thus public compiled
execution makes logarithmically many recursive exponent reductions and never
calls the linear specification.  This is structural efficiency evidence, not
a wall-clock claim.

Fast/spec correctness needs multiplication associativity and both identity
directions; it does not need commutativity because every reordered factor is a
power of the same base.  Commutativity is used only for rearranging the separately disabled
exponent-addition law.  Exponent addition and implementation-bridge theorems are disabled to avoid expansion and
associativity/commutativity loops.  Reducing zero, one, fixer, and `NFIX` rules
remain available.

Natural powers use the conventional `0^0 = 1`; zero to a positive power is
zero.  There are no inverse, signed, or rational exponent semantics.

## Polynomial semantics and future reuse

`GPOLY::POLY-POW` fixes its input with `NORMALIZE`, uses canonical polynomial
one, and multiplies with canonical `POLY-MUL`.  It therefore returns canonical
constant-first polynomials without an extra normalization layer beyond the
existing multiplication operation.  Its evaluation theorem is proved first
for the linear specification and transported to the public operation:

`eval(poly-pow(f,n),x) = field-pow(eval(f,x),n)`.

This power kernel is intended for later extension-field arithmetic, Frobenius
maps, derived finite-field inverse computations, irreducibility tests,
elliptic-curve scalar and endomorphism calculations, and Schoof computations.
Exponentiation alone establishes neither field inverses nor extension-field
field structure.
