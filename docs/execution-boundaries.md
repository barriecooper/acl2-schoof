# Execution boundaries

This document owns stable contracts between logical meaning and execution.
Representations and subsystem dependencies are in
[architecture.md](architecture.md); theorem status is in
[obligations.md](obligations.md).

## Evidence model

For an executable interface, keep these claims separate:

1. **Logical specification** — the mathematical meaning.
2. **Executable implementation** — the branch actually run by compiled ACL2.
3. **Correspondence invariant or theorem** — why execution implements the
   specification.
4. **Guard and termination verification** — why the executable path is
   admissible and safe for its declared guard.
5. **Execution regression** — evidence that a concrete path runs and returns
   expected values.

Guard verification does not prove semantic correctness, and a regression does
not replace a generic correspondence theorem. A new or changed public split
must document all applicable layers here.

## Totalisation and fixing

Public operations are total on ACL2 objects. Their intended carrier semantics
are expressed through fixers:

- `field-fix` maps arbitrary values to field representatives;
- polynomial normalization fixes coefficients, discards malformed tails, and
  removes trailing zeroes;
- fixed-modulus field fixing takes the canonical remainder;
- the affine-coordinate fixer maps malformed outer values to the fixed zero
  pair; and
- the tagged-point fixer maps malformed values to canonical infinity.

A theorem stated modulo a fixer is semantic equality of represented values, not
raw ACL2 equality. Raw equality is used only where canonicality or an explicit
canonical-input hypothesis justifies it.

## Canonical polynomial boundaries

Dense polynomial raw helpers may construct intermediate lists. Public GPOLY
operations normalize results, so canonical equality is the stable external
contract. Division, GCD, XGCD, modular inverse, and reduced arithmetic inherit
malformed-value behavior from normalization and total field operations.

The generic fixed-modulus field uses canonical remainder representatives.
F7X2 operations accept arbitrary ACL2 inputs, fix/reduce them, and return
canonical representatives. F7X2's inverse is an ordinary transparent,
guard-verified definition using the existing F7 modular inverse; the certified
fixed-modulus functional instance supplies semantic inverse evidence. Exact
F7X2 assertions establish execution only.

## Power fast/spec boundary

`DEF-POW-INSTANCE` generates a linear logical specification, a
square-and-multiply accumulator, and a public `MBE` wrapper. Public execution
fixes the base, applies `NFIX` to the exponent, and calls only the logarithmic
auxiliary. Negative or malformed exponents therefore have exponent-zero
semantics, and `0^0 = 1`.

Each productionized instance certifies an accumulator invariant and fast/spec
correctness before guard verification of the public wrapper. This applies to
the generic field and polynomial powers and their named PFIELD/F2/F7 clients.
There is no experimental unmatched fast branch.

## Field-only X-CERT logical layer

The X-CERT algebra book adds ordinary transparent total field expressions and
certified logical identities.  It introduces no `MBE`, attachment, alternate
executable branch, or new guard boundary.  Its residual generators are explicit
expressions and are not assumed to vanish; the curve-semantic bridge is
likewise a transparent logical layer.  It adds no executable branch or guard boundary; its four residual-zero results follow
from the total output-x rearrangement.

## Transparent executable interfaces

Most repository functions are ordinary transparent `DEFUN`/`DEFUND` events,
not logical/executable splits. Important examples include:

- PFIELD adapters and named F7/F11 field operations;
- generic and F7 polynomial division, GCD, XGCD, and modular inverse;
- generic field natural scaling and canonical polynomial differentiation;
- generic fixed-modulus operations and F7X2 arithmetic;
- affine and tagged-point fixers, constructors, accessors, and negation;
- affine classifiers, branch slopes and outputs; and
- `affine-pair-output-point` and `curve-point-pair-output-point`.

Verified guards and transparent definitions explain how these functions run.
Their semantic theorems, not transparency alone, justify mathematical claims.

`field-nat-mul`, `raw-derivative-aux`, and `poly-derivative` are transparent,
total, guard-verified definitions.  They have no alternate optimized branch or
logical/executable correspondence boundary.

`pfield-nat-mul` is likewise a transparent, guard-verified PFIELD adapter.  It
applies `nfix` to the scalar, fixes its field argument, and returns the
canonical modular product.  Its closed form on field one supports the logical
least-characteristic proof; it is not field enumeration or cardinality
metadata.

Tagged point negation is the transparent total data transformation
`curve-point-neg`: it fixes its input once, preserves infinity, and changes
only the affine ordinate by `field-neg`.  It calls neither the curve classifier
nor an addition dispatcher.  `curve-point-fix-of-neg` and
`curve-point-neg-of-fix` state its canonical-output and fixing contracts;
closure and involution are separately certified.  Malformed inputs therefore
inherit the tagged-point fixer's canonical-infinity convention.

## Curve-addition correspondence

The executable dispatcher is intentionally not the logical specification.
Independent semantic branch relations omit the classifier and executable
formulas, and `curve-point-addition-relation-p` combines those relations without
calling either dispatcher.

For curve-point inputs:

- branch closure establishes executable output membership;
- dispatcher soundness establishes the full relation for the executable
  output; and
- fixed-output determinacy equates any semantic witness with that output after
  point fixing.

The dispatcher always returns a canonical tagged representation. This
canonical-output invariant is what permits raw executable commutativity after
semantic commutativity and determinacy are applied. Off-domain branch and
fallback executions remain total programming conventions, not geometric
claims.

Executable associativity follows the same separation.  Four applications of
dispatcher soundness, with closure for the two inner results, instantiate the
independent theorem `curve-point-addition-relation-associative`.  Its
fixed-output conclusion is converted to literal dispatcher equality only by
the canonical-output theorem
`curve-point-fix-of-curve-point-pair-output-point`.  The lift replays no
classifier case split or affine branch algebra.  Concrete F11 triples and
finite F7/F11 enumeration validate execution separately; they do not establish
semantic correctness.

Inverse correctness uses the same semantic separation.  The narrow theorem
`curve-point-addition-relation-p-of-point-and-neg` splits only the tagged
infinity/affine representation and establishes the independent opposite-y
relation with infinity output.  Dispatcher soundness and fixed-output
determinacy then give the executable right inverse; executable commutativity
gives the left inverse.  No dispatcher branch tree, secant algebra, or tangent
algebra is expanded in this lift.  Concrete F11 inverse checks are execution
regressions, not the proof of these laws.

Executable left cancellation is derived purely by translating an equality by
the executable negation, reassociating, and applying the executable inverse
and identity laws.  Right cancellation is then derived by executable
commutativity.  These algebraic proofs do not revisit the semantic addition
relation, dispatcher branches, classifiers, or affine/field proofs.

Abstract abelian-group packaging introduces no new geometric operation and no
new executable boundary.  The contextual generic interface is instantiated
with the already executable tagged-point operation, infinity, and negation;
its obligations are discharged solely by the independently certified public
closure, identity, inverse, associativity, and commutativity laws.  The
nullary context maps to `short-weierstrass-characteristic-p`, so functional
instances retain that hypothesis rather than asserting an unconditional group
law.  The packaging regression is logical reuse evidence, not a new execution
or performance claim.

## Natural scalar multiplication

Natural scalar multiplication is a transparent, guard-verified linear
recursive specification.  Both generic and curve operations totalise the
scalar with `nfix`, return identity/infinity at zero, and add the point on the
left at each successor.  It is deliberately not double-and-add; a future fast
implementation requires the distinct function `curve-point-fast-nat-mul` and
a certified correspondence theorem to `curve-point-nat-mul`. Focused concrete
regressions must demonstrate that the fast branch executes with practical
behaviour, but do not replace that correspondence proof.

## Guard and termination boundaries

Recursive polynomial division uses a certified strict decrease of the
canonical remainder measure. Concrete F7 recursion and its complete operation
chain have verified guards. GCD and XGCD reuse that division boundary;
nonrecursive wrappers do not constitute alternate algorithms.

A `verify-guards` event establishes only guard correctness for the admitted
logical definition. Any staged `:verify-guards nil` generated for a power
instance remains acceptable only because the instance later supplies its
invariant, fast/spec theorem, dependency guard proofs, and final public guard
verification.

## Trust and scanner policy

The repository forbids skipped proofs, axioms, trust tags, executable
attachments, raw Lisp facilities, and equivalent escapes. The scanner is
intentionally lexical and also rejects prohibited spellings in comments and
strings. Ordinary sound ACL2 facilities such as `MBE`, `DEFEXEC`,
`ENCAPSULATE`, `VERIFY-GUARDS`, and functional instantiation are review
triggers rather than automatic violations.

The current project source uses `MBE` only through generated power instances
and contains no `DEFEXEC`, executable attachment, program-mode boundary, raw
Lisp inclusion, skipped proof, project axiom, or trust tag. Future changes to
this inventory must update this document and satisfy the evidence model above.
