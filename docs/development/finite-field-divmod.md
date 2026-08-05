# Finite-field recursive divmod development note

## Completed boundary

`books/polynomial/generic/finite-field-divmod.lisp` now certifies the generated
finite-field recursive divmod core, public divmod wrapper, quotient/remainder
projections, guards, canonicality, reconstruction, and final remainder degree
bound.  The production book is registered together with the focused regression
book.

The high-level functional instance of `poly-divmod-public-interface` was
abandoned for this constrained target because it descends through generated
implementation equations.  The final proof instead uses direct recursive core
invariants plus one reusable finite-field polynomial algebra seam.

## Algebra seam audit

The reconstruction accumulator algebra needs the public distributivity
orientation:

```lisp
(equal (finite-field-poly-mul (finite-field-poly-add x y) z)
       (finite-field-poly-add (finite-field-poly-mul x z)
                              (finite-field-poly-mul y z)))
```

The first failed accumulator-algebra transport exposed the public multiplication
definition.  Enabling `finite-field-poly-mul` discharged that obligation, after
which ACL2 exposed raw multiplication atom semantics.  Rather than carry those
raw equations locally in divmod, the reusable seam was placed in
`finite-field-instance.lisp`: `finite-field-poly-mul-right-distributive` is a
functional instance of the generic public theorem under a narrow theory made
from `finite-field-poly-definition-theory`, `minimal-theory`, and explicit
finite-field context constraints.

The divmod book consumes only the public distributivity theorem and
`finite-field-poly-add-associative` in
`finite-field-poly-divmod-accumulator-algebra`; raw multiplication is disabled in
that consumer.

## Accumulator semantics

The recursive core has signature:

```lisp
(finite-field-poly-divmod-core quotient-acc remainder divisor)
```

It returns a pair `(final-quotient . final-remainder)`.  In the active branch,
it computes one certified division step and recurs on:

```lisp
(finite-field-poly-divmod-core
 (finite-field-poly-add quotient-acc term)
 next
 divisor)
```

The certified reconstruction invariant is oriented as:

```text
final-quotient * divisor + final-remainder
=
quotient-acc * divisor + current-remainder
```

At the public wrapper, the accumulator is `nil`, the current remainder is
`(finite-field-poly-normalize f)`, and the divisor is
`(finite-field-poly-normalize g)`.

## Certified endpoint chain

* `finite-field-poly-divmod-core-quotient-canonical`.
* `finite-field-poly-divmod-core-remainder-canonical`.
* `finite-field-poly-divmod-core-final-remainder-degree-bound`.
* `finite-field-poly-divmod-accumulator-algebra`.
* `finite-field-poly-divmod-core-reconstruction-invariant`.
* `finite-field-poly-divmod-quotient-canonical`.
* `finite-field-poly-divmod-remainder-canonical`.
* `finite-field-poly-divmod-final-remainder-degree-bound`.
* `finite-field-poly-divmod-reconstruction`.
* Projection corollaries for `finite-field-poly-quotient` and
  `finite-field-poly-remainder`.

Core invariant proofs may narrowly enable `finite-field-poly-divmod-core` for
induction, following the generic proof pattern.  Public theorem clients and the
regression book keep the recursive core and raw arithmetic implementations
opaque.
