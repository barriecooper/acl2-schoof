# Finite-field recursive divmod development note

## Current retained boundary

`books/polynomial/generic/finite-field-divmod.lisp` certifies the generated
finite-field recursive divmod core, public divmod wrapper, generated recursive
equation theorem, non-recursive quotient/remainder projections, guards, and the
projection equations.  It also certifies the finite-field normalization and
degree bridges needed to state generated degree constraints without unfolding
the recursive divmod core.

## Abandoned high-level functional-instantiation route

The bundled theorem `poly-divmod-public-interface` is no longer the proof route
for the finite-field target.  The previous audit showed that a single high-level
functional instance of that aggregate theorem descends through generated
definition constraints for normalization, degree, addition, multiplication,
raw multiplication, division-step wrappers, and divmod wrappers.  That is
acceptable for concrete F7 only because executable definitions and specialized
hints discharge many residuals.  For the separately constrained
`finite-field-*` target it would reproduce most of the implementation graph and
break the intended opacity boundary.

The finite-field public semantics should instead be proved directly from the
recursive equation theorem, the already certified finite-field one-step division
interface, and explicit accumulator invariants.

## Accumulator semantics

The recursive core has signature:

```lisp
(finite-field-poly-divmod-core quotient-acc remainder divisor)
```

It returns a pair `(final-quotient . final-remainder)`.  In the active branch,
where all three arguments are canonical, both `remainder` and `divisor` are
nonempty, and the divisor degree is at most the remainder degree, the core
computes one division step:

```lisp
step = (finite-field-poly-division-step-core remainder divisor)
term = (car step)
next = (cdr step)
```

and recurs on:

```lisp
(finite-field-poly-divmod-core
 (finite-field-poly-add quotient-acc term)
 next
 divisor)
```

The quotient accumulator is therefore on the left of multiplication in the
reconstruction invariant.  The intended invariant orientation is:

```text
final-quotient * divisor + final-remainder
=
quotient-acc * divisor + current-remainder
```

The original dividend is not an explicit core parameter.  At the public wrapper,
`quotient-acc` is `nil`, `current-remainder` is `(finite-field-poly-normalize f)`,
and `divisor` is `(finite-field-poly-normalize g)`, so the invariant specializes
to the usual normalized reconstruction statement.

The current remainder is canonical in the recursive proof hypotheses.  The
public wrapper supplies that canonicality through normalization.  The recursive
case preserves canonicality by adding the canonical one-step term to the
canonical quotient accumulator and by using the certified next-remainder
canonicality theorem.

## Invariant table

| Invariant | Base case | Recursive preservation | Public consequence |
| --- | --- | --- | --- |
| Quotient accumulator/result canonical | The core returns `(cons quotient-acc remainder)`, so the final quotient is the canonical accumulator. | The one-step term is canonical and `finite-field-poly-add` preserves canonicality; induction applies to the updated accumulator. | Public quotient canonicality with initial accumulator `nil`. |
| Current/final remainder canonical | The core returns the canonical current remainder. | `finite-field-poly-division-step-core-next-canonical` makes the next remainder canonical; induction applies to `next`. | Public remainder canonicality after normalizing the dividend and divisor. |
| Reconstruction | Base result gives `quotient-acc * divisor + remainder` on both sides. | One-step reconstruction gives `term * divisor + next = remainder`; accumulator algebra should rewrite `(quotient-acc + term) * divisor + next` to `quotient-acc * divisor + remainder`. | Public reconstruction: quotient times normalized divisor plus remainder equals normalized dividend. |
| Final remainder degree/termination | Inactive branch means remainder is empty, divisor is empty, or `degree(remainder) < degree(divisor)`; under nonempty divisor the final remainder is zero or smaller. | The recursive call is exactly on the one-step `next` remainder, so the induction hypothesis supplies the final bound. | Public final remainder degree bound under `(consp (finite-field-poly-normalize g))`. |

## Core induction dependency graph

* Core canonicality depends on
  `finite-field-poly-divmod-core-functional-instance-equation`,
  `finite-field-poly-division-step-core-term-properties`,
  `finite-field-poly-division-step-core-next-canonical`, and
  `finite-field-canonical-polynomial-p-of-poly-add`.
* Core reconstruction additionally depends on
  `finite-field-poly-division-step-core-reconstruction` and a finite-field
  polynomial accumulator-algebra theorem analogous to
  `poly-divmod-accumulator-algebra`.
* Core final remainder degree bound depends on the recursive equation theorem,
  canonicality of the current remainder, and the inactive stopping condition.

## Current checkpoint

The last certified logical event in this checkpoint is
`finite-field-poly-divmod-core-accumulator-step-canonical`, which proves that
adding the one-step term to a canonical quotient accumulator preserves
canonicality.  The next target checkpoint remains the full core quotient output
canonicality theorem.

The first attempted full quotient-canonical theorem was:

```lisp
(defthm finite-field-poly-divmod-core-quotient-canonical
  (implies (and (finite-field-canonical-polynomial-p quotient)
                (finite-field-canonical-polynomial-p remainder)
                (finite-field-canonical-polynomial-p divisor))
           (finite-field-canonical-polynomial-p
            (car (finite-field-poly-divmod-core quotient remainder divisor)))))
```

The theorem was not retained.  With the recursive core disabled and only the
named equation theorem supplied, ACL2 did not simplify the top induction goal.
Combining `:induct` and `:use` for the equation theorem directly is rejected by
ACL2, and using a local rewrite copy of the equation theorem did not fire before
the top-level checkpoint.  No attempt unfolded the recursive core or raw
multiplication.  The current classification is: direct target proof remains
likely, but the recursive equation theorem needs to be integrated into the
induction scheme without an unstable subgoal-number hint.
