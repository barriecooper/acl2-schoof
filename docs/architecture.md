# Architecture

This document owns the stable design of the formalization. Exact proved and
open status belongs in the [obligation ledger](obligations.md), execution
contracts in [execution boundaries](execution-boundaries.md), and future
ordering in the [proof plan](proof-plan.md).

## Algebraic layers

### Generic fields and concrete adapters

`GFIELD` is the constrained equational field kernel. Every public operation has
total ACL2 semantics through `field-fix`; field laws therefore state equality
of fixed representatives where arbitrary ACL2 inputs are admitted. Natural
power, generated power correspondence, characteristic exclusions, and the
minimal Frobenius-exponent certificate extend this kernel without asserting a
field cardinality or an executable enumeration.

PFIELD supplies canonical prime-field representatives. Named F2, F7, and F11
clients provide executable instances and regression evidence. Concrete
instances validate functional instantiation and execution, but generic claims
come only from the generic certified books.

### Field-only X-CERT algebra

`books/field/xcert-algebra.lisp` defines explicit output-coordinate residuals
and the field expressions `xcert-dx`, `xcert-telescope`, `xcert-remainder`,
`xcert-h`, `xcert-s`, and `xcert-c`.  The residuals are total expressions, not
assumed-zero hypotheses.  Certified component theorems establish the output
telescope and remainder identities, and `xcert-composition` combines those
components opaquely in the exact left-associated form.

The field-only book depends only on the generic field kernel.  The separate
`books/curve/xcert-semantics.lisp` bridge imports that book and the assembled
affine distinct-x output.  For inputs `A`, `B`, and `C`, it maps `xab` and `xbc`
to the x-coordinates of `AB = output(A,B)` and `BC = output(B,C)`, maps `xl`
and `xr` to the x-coordinates of `output(AB,C)` and `output(A,BC)`, and maps
`p,q,r,tt` to the ordered slopes `(A,B)`, `(AB,C)`, `(B,C)`, and `(A,BC)`.
It certifies the four residuals as zero from the existing output-x
rearrangement and specializes `D_x`, `H`, `S`, `C`, and the opaque composition.
The bridge adds no polynomial dependency and proves no associativity or
exceptional-case fact.

### Canonical dense polynomials

`GPOLY` is authoritative for new polynomial algebra. A polynomial is a dense
constant-first coefficient list. `normalize` fixes coefficients and removes
trailing zeroes; `nil` is the unique canonical zero. Public arithmetic returns
canonical polynomials, while raw helpers exist only to support definitions and
proofs. Polynomial equality in the generic layer is literal equality of
canonical representatives, not merely agreement under evaluation.

The certified stack is layered: arithmetic and evaluation; degree and leading
coefficient; division and remainder; congruence and reduced operations;
Euclidean and extended Euclidean GCD; logical irreducibility and modular
inverse. The HS/PFIELD polynomial layer is retained for concrete/root-count
bridges, not as a parallel home for new algorithms.

### Fixed-modulus quotient fields

The generic fixed-modulus construction constrains a nullary, canonical,
irreducible positive-degree modulus. Elements are canonical remainders and the
fixer is remainder modulo that modulus. Addition, negation, subtraction, and
multiplication use reduced operations; inverse is the total XGCD-derived
candidate with an explicit zero case. Certified irreducibility results provide
the nonzero inverse law.

F7X2, representing `F7[x]/(x^2+1)`, is a concrete proving instance. It should
not be confused with the reusable constructor or treated as an arbitrary
finite-field package.

## Curve representations

The initial curve layer uses constrained short-Weierstrass coefficients and
total field operations. It assumes the nonzero standard discriminant
expression and the separately certified exclusions of characteristics two and
three.

An **affine coordinate** is a canonical two-element list `(x y)` after field
fixing. Structural recognition is separate from satisfaction of the curve
equation. The affine fixer maps malformed outer values to the fixed zero pair;
it does not manufacture an on-curve point.

A **tagged curve point** is either canonical infinity `(:infinity)` or an
affine tag `(:affine (x y))`. Structural point recognition remains separate
from curve membership. The point fixer maps malformed tagged values to
infinity. Consequently public operations are total, and malformed inputs have
specified fixer-induced behavior rather than an implicit precondition.

Point negation fixes its input, preserves infinity, and negates the affine
`y` coordinate. Its involution and curve-membership results are modulo fixing;
raw equality follows when the input is already canonical.

## Full tagged-point addition layers

The addition development deliberately keeps execution and semantics separate.
The following names refer to different layers and should not be conflated:

1. **Branch classifier.** `affine-pair-classify` classifies fixed affine inputs
   as `:distinct-x`, `:opposite-y`, `:same-point-non-opposite`, or
   `:same-x-other`. Its ordering makes identical self-inverse points select the
   opposite-y branch. Classification is total and structural, including for
   off-curve inputs.
2. **Executable branch outputs.** Total slope and coordinate functions compute
   the distinct-x and doubling formulas. Tagged wrappers produce affine points
   or infinity. Outside a branch hypothesis, their values are programming
   semantics and are not geometric claims.
3. **Dispatchers.** `affine-pair-output-point` selects an affine branch;
   `curve-point-pair-output-point` first handles infinity and then delegates the
   affine/affine case. Both are transparent total executable operations. The
   affine fallback to infinity is unreachable for two on-curve affine inputs.
4. **Semantic branch relations.** Division-free relations independently state
   the secant, doubling, opposite/inverse, and ordered infinity cases. They do
   not call the classifier, slopes, executable outputs, or dispatcher.
5. **Independent full addition relation.** `curve-point-addition-relation-p`
   is the five-case semantic specification over two inputs and an output. It is
   independent of classifier priority and executable dispatch.

Branch soundness and case coverage prove that the dispatcher satisfies the
full relation for curve-point inputs. Fixed-output determinacy proves that two
semantic witnesses have equal fixed outputs. These theorems are the semantic
bridge to execution; guard verification alone is not that bridge.

## Present algebraic-law layer

For full tagged-point addition, the certified layer includes output closure,
left and right infinity identity, addition of a point and its negation to
infinity, semantic operand-reversal commutativity, and raw dispatcher
commutativity. The raw dispatcher theorem is possible because executable
outputs are canonical; semantic statements otherwise use fixer-level equality.

Associativity, cancellation, group or abelian-group packaging, and scalar
multiplication are absent. Until associativity is certified, documentation must
not call the dispatcher a certified group law.

## Design constraints for later work

- Preserve total fixer semantics at public ACL2 boundaries and state clearly
  when equality is raw or modulo fixing.
- Keep generic theorems separate from concrete F7/F11 execution regressions.
- Do not replace an independent semantic relation with the executable
  dispatcher or its classifier.
- Keep guard/termination assurance separate from semantic correctness.
- Extend `GFIELD`/`GPOLY` rather than duplicating new algebra in HS/PFIELD.
- Treat the Hasse and Schoof developments as downstream tracks sharing the
  field, polynomial, curve, and Frobenius foundations; neither track is a
  prerequisite for the other after that seam.
