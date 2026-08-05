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
`finite-field-poly-divmod-final-remainder-degree-bound`.  The certified prefix
now includes core quotient canonicality, core remainder canonicality, core final
remainder degree bound, public quotient canonicality, public remainder
canonicality, and the public final remainder degree bound.

The revised permission to use the generic proof pattern locally was necessary:
the core canonicality and degree-bound proofs enable only
`finite-field-poly-divmod-core` for induction and continue to disable the
finite-field division-step core, raw multiplication, normalization internals,
and lower arithmetic definitions.

The remaining blocked endpoint is reconstruction.  A narrow attempt to import
the generic accumulator algebra theorem for finite-field polynomials first
exposed the generated public multiplication equation:

```lisp
(equal (finite-field-poly-mul x y)
       (finite-field-poly-normalize
        (finite-field-poly-raw-mul (finite-field-poly-normalize x)
                                   (finite-field-poly-normalize y))))
```

That first residual is definitional, not by itself evidence that
multiplication distributivity is missing.  Enabling only
`finite-field-poly-mul` discharges it, but the next complete ACL2 residual is a
raw multiplication definition obligation:

```lisp
(implies (not (consp x))
         (not (finite-field-poly-raw-mul x y)))
```

No named finite-field counterpart of the generic raw-multiplication atom facts
or of `poly-mul-right-distributive` is currently exposed by the finite-field
polynomial public layer.  Continuing the narrow functional instance would need
to import or unfold the raw multiplication support chain behind generic
`poly-mul-right-distributive`.  The uncertified accumulator-algebra tail was
removed.  The current classification is therefore a missing finite-field
polynomial algebra interface for the distributivity fragment needed by divmod
reconstruction, with the first two encountered obligations being the public
`poly-mul` definition followed by the raw-multiplication atom equation.
