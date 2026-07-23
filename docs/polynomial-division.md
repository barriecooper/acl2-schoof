# Generic polynomial division contract

This document fixes the contract for the **future** generic long-division
operation.  Division itself is not implemented yet.  The intended public name
and shape are:

```lisp
(mv q r) = (poly-divmod f g)
```

`POLY-DIVMOD` will be an ordinary, deterministic, total ACL2 function.  At its
public boundary it will normalize each polynomial input exactly once.  This
retains the established policy that an atom ends a coefficient list and a
dotted tail is discarded.  If normalized `g` is `nil`, it will return
`(mv nil (normalize f))`.  That result is a total fallback, **not**
field-theoretic division by zero.  Negative or malformed inputs may not cause a
partial function, assertion-based domain restriction, program-mode escape, or
raw execution mechanism.

For normalized `f` and nonzero canonical `g`, with `(mv q r)` the result, the
future certified contract is all of the following:

* `q` and `r` are canonical polynomials, hence coefficient-list polynomials in
  the generic field carrier and true lists;
* formal canonical polynomial equality proves
  `f = poly-add(poly-mul(q,g),r)`;
* `r` is `nil` or `poly-degree(r) < poly-degree(g)`;
* when `r` is `nil`, the reconstruction theorem reduces to exact division;
* zero dividend reduces to `(mv nil nil)`, and divisor one reduces to
  `(mv (normalize f) nil)`;
* repeated calls on equal ACL2 inputs return the same concrete canonical pair.

The recursion will cancel one current leading term at a time.  Its termination
proof must exhibit strict decrease of the nonzero current remainder's degree;
the equivalent natural measure is its canonical length.  Guard verification
will separately establish safe execution and will not substitute for the
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
field operations deliberately have no evaluator, so an ordinary concrete
generated copy is deferred to the division instance.

No `MBE`, `DEFEXEC`, attachment, or other logical/executable boundary is added,
and no update to `docs/execution-boundaries.md` is required.

## Explicitly downstream

This contract claims no uniqueness theorem, gcd or extended-gcd correctness,
Bézout identity, Euclidean-domain result, irreducibility result, factorization,
extension field, rational function, or curve operation.  The next task still
owes one-step leading-term cancellation, recursive quotient/remainder,
reconstruction, and the strict remainder-degree bound before any of those
downstream topics can begin.
