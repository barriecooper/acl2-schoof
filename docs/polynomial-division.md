# Generic polynomial division contract

This document records the certified generic long-division operation.  Its public name and shape are:

```lisp
(mv q r) = (poly-divmod f g)
```

`POLY-DIVMOD` is an ordinary, deterministic, total ACL2 function.  At its
public boundary it normalizes each polynomial input exactly once.  This
retains the established policy that an atom ends a coefficient list and a
dotted tail is discarded.  If normalized `g` is `nil`, it returns
`(mv nil (normalize f))`.  That result is a total fallback, **not**
field-theoretic division by zero.  Negative or malformed inputs may not cause a
partial function, assertion-based domain restriction, program-mode escape, or
raw execution mechanism.

For normalized `f` and nonzero canonical `g`, with `(mv q r)` the result, the
certified contract is all of the following:

* `q` and `r` are canonical polynomials, hence coefficient-list polynomials in
  the generic field carrier and true lists;
* formal canonical polynomial equality proves
  `f = poly-add(poly-mul(q,g),r)`;
* `r` is `nil` or `poly-degree(r) < poly-degree(g)`;
* when `r` is `nil`, the reconstruction theorem reduces to exact division;
* zero dividend reduces to `(mv nil nil)`, and divisor one reduces to
  `(mv (normalize f) nil)`;
* repeated calls on equal ACL2 inputs return the same concrete canonical pair.

The recursion cancels one current leading term at a time.  Its termination
proof exhibits strict decrease of the nonzero current remainder's degree;
the equivalent natural measure is its canonical length.  Guard verification separately establishes safe execution and will not substitute for the
reconstruction or degree-bound proofs.

## Certified foundation in this change

`books/polynomial/generic/monomial.lisp` supplies ordinary total
`ZERO-PREFIX`, `POLY-SHIFT`, and `MONOMIAL`.  Dense coefficients are
constant-first, so shifting prepends field zeros.  Every public exponent uses
`NFIX`: a negative exponent means shift zero, never a negative power or a
Laurent polynomial.  `POLY-SHIFT` normalizes its polynomial once, preserves
canonical zero as `nil`, and `MONOMIAL` fixes arbitrary coefficients with
`GFIELD::FIELD-FIX`; a fixed zero produces `nil`.

The book certifies coefficient/true-list closure, canonicality, zero and
exponent-zero behavior, shift composition, nonemptiness and length, degree
shift and leading-coefficient preservation, and the corresponding monomial
nonzero, degree, and leading-coefficient laws.  Its focused symbolic
regressions cover zero, one, and four-place shifts; zero and constant
monomials; a degree-two monomial; and negative-index behavior.  The abstract
theory now also has a certified named F7 instance (`f7-zero-prefix`,
`f7-poly-shift`, and `f7-monomial`) with a direct zero-prefix normalization
bridge.  F7 one-step division and recursive quotient/remainder remain open.

No `MBE`, `DEFEXEC`, attachment, or other logical/executable boundary is added,
and the ordinary concrete runtime classification is recorded in
`docs/execution-boundaries.md`.

## Certified recursive quotient/remainder

`GPOLY::POLY-DIVMOD-CORE` carries `(quotient remainder divisor)`, returns the transparent pair `(final-q . final-r)`, and measures `(len remainder)`.  It invokes `POLY-DIVISION-STEP-CORE` once per active iteration and reuses that pair.  `POLY-DIVMOD` normalizes each external operand once and returns `(mv q r)`.  The certified invariant is `final-q*g+final-r = accumulated-q*g+current-r`; the public consequence is `q*normalize(g)+r = normalize(f)`.  Canonicality, polynomial/true-list closure, the strict final remainder bound, inactive reductions, divisor-one reduction, determinism, and exact division are certified.  Both new ordinary `DEFUN`s have verified guards.

No `MBE`, `DEFEXEC`, attachment, or separate executable specification is used.  The divisor is fixed and is not normalized in recursion.  Concrete PFIELD division and recursive F7 divmod are postponed.

## Certified remainder interface

`GPOLY::POLY-REMAINDER` is the transparent remainder projection of a single
public `POLY-DIVMOD` call. It inherits divmod's normalization boundary and has
verified guards. Its semantic theorems establish canonical output, invariance
under normalizing either input, fallback to `NORMALIZE(dividend)` when the
normalized modulus is `nil`, a strict final degree bound when the normalized
modulus is nonempty, and idempotence. The proof uses certified remainder
canonicality and degree bounds, inactive lower-degree division, and the zero
fallback; it adds no recursive induction and uses no evaluation equality.

Polynomial congruence remains separate and open. The next PR will cover adding
a modulus multiple, the congruence relation itself, and addition and
multiplication compatibility. It will not be inferred from this reduction API.

## Explicitly downstream

This contract claims no uniqueness theorem, gcd or extended-gcd correctness,
Bézout identity, Euclidean-domain result, irreducibility result, factorization,
extension field, rational function, or curve operation.  One-step leading-term cancellation and generic recursive quotient/remainder, reconstruction, and final strict remainder-degree bound are certified. Concrete generated instances, uniqueness, gcd, and all broader Euclidean consequences remain open.

## Certified one-step cancellation API

`GPOLY::POLY-DIVISION-STEP-CORE` accepts canonical operands and returns the
transparent pair `(term . next)`.  It is active exactly when both operands are
nonempty and the divisor degree is at most the remainder degree.  In that case
`term` is `MONOMIAL(FIELD-DIV(lc(remainder),lc(divisor)), degree(remainder)-degree(divisor))`
and `next` subtracts `term*divisor`.  Otherwise it returns `(nil . remainder)`.
`GPOLY::POLY-DIVISION-STEP` is the total public wrapper and normalizes each
input once before calling the core; zero divisor therefore returns a zero term
and the normalized remainder unchanged.

The book certifies canonical/nonempty quotient-term and product facts, exact
formal reconstruction `normalize(remainder) = term*normalize(divisor)+next`,
and structural strict degree decrease in every active step.  The corresponding
strict canonical-length decrease is the intended measure for later recursion.
The recursive operation is implemented in `books/polynomial/generic/division.lisp`.
