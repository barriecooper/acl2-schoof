# Finite-field recursive divmod development note

## Current retained boundary

`books/polynomial/generic/finite-field-divmod.lisp` certifies the generated
finite-field recursive divmod core, public divmod wrapper, generated recursive
equation theorem, non-recursive quotient/remainder projections, guards, and the
projection equations.

## Generic dependency table

| Generic theorem or constraint | Role | Existing finite-field counterpart | Missing? |
| --- | --- | --- | --- |
| `poly-degree-of-normalize` | Rewrites the degree of a normalized polynomial back to the original input. | `finite-field-poly-degree-of-poly-normalize` | No. |
| `poly-degree-when-canonical-nonzero` | Converts degree of a nonempty canonical polynomial to `1-` its length. | `finite-field-poly-degree-when-canonical-nonzero` | No. |
| `canonical-polynomial-p-of-normalize` | Supplies canonicality for normalized inputs. | `finite-field-canonical-polynomial-p-of-poly-normalize` | No. |
| Generated `poly-degree` definition from `def-degree-instance` | Produces the exact nonempty/empty normalized representation constraints seen in the public divmod functional-instance obligations. | `finite-field-poly-degree-definition-for-divmod` | Added in the divmod book. |
| Generated `normalize` definition from `def-normalize-eval-instance` | Exposes normalized values as trim-after-fix for exact expanded residuals. | `finite-field-poly-normalize-definition-for-divmod` | Added in the divmod book. |
| `poly-divmod-core-functional-instance-equation` | Supplies recursive proof evidence without unfolding the recursive core. | `finite-field-poly-divmod-core-functional-instance-equation` | No. |

## Source of the residual

The stable residual in the attempted `finite-field-poly-divmod-public-interface-from-generic`
functional instance comes from the generated `poly-degree` definition used in
supporting the generic divmod proof obligations, together with the generic
normalization representation.  The exact finite-field bridge theorem added for
that definitional dependency is `finite-field-poly-degree-definition-for-divmod`.

## Attempted aggregate-interface route

A retry of `def-divmod-public-interface-instance` used
`finite-field-poly-divmod-core-functional-instance-equation` while keeping
`finite-field-poly-divmod-core` disabled.  The new degree/normalization facts
fired, but the aggregate proof still exhausted ACL2's rewrite call-depth before
a stable checkpoint when applied as broad stable simplification support. Exact
subgoal hints progressed through several normalized degree/length residuals but
exposed more variants under inactive recursive-core constraints.

The next attempt should build a narrower public-instance theory that avoids
broad field rewrites and supplies the degree-definition bridge only to the
specific generated definitional obligations.
