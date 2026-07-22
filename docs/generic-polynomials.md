# Generic dense polynomials

`books/polynomial/generic/package.lisp` establishes the dedicated `GPOLY`
namespace, `base.lisp` defines the abstract theory over `GFIELD`, and
`add.lisp` supplies the additive structure, `scale.lisp` supplies the scalar
action, and `pfield-instance.lisp` is their
PFIELD/F_7 regression.  The existing `HS` books
are unchanged.

A list `(c0 ... cn)` is dense and constant-first.  `POLYNOMIAL-P` deliberately
means a proper list of fixed field elements; it does **not** imply canonicality.
`CANONICAL-POLYNOMIAL-P` additionally admits only `nil`, the unique zero, or a
list whose last coefficient is not `GFIELD::FIELD-ZERO`.  Internal zeroes are
retained.  Canonical polynomial equality is ordinary ACL2 `EQUAL` because all
coefficients are canonical representatives.

`FIX-COEFFICIENTS` applies `GFIELD::FIELD-FIX` elementwise.
`TRIM-TRAILING-ZEROS` recursively removes only the zero suffix, and `NORMALIZE`
composes those operations.  `EVAL` uses Horner recursion for constant-first
coefficients: the head plus the fixed point times the recursively evaluated
tail.  It fixes every coefficient and the point.

All functions are total.  Atoms terminate list recursion, so a dotted or other
malformed tail is discarded.  Normalization fixes arbitrary heads before
trimming.  Evaluation treats an atomic polynomial as field zero and otherwise
lets the total field fixer handle malformed coefficients and points.  Guards
are not part of logical correctness.

The certified structural results cover properness and identity of fixing,
trimming closure and its nonzero-last property, canonical normalization,
identity on canonical inputs, idempotence, the nil/nonzero conventions, and
non-increasing length.  Evaluation is field-valued and is invariant under point
fixing, coefficient fixing, trimming, and normalization; constant and zero
point formulas are also proved.

`RAW-ADD` adds coefficients and fixes an unequal-length remainder; `RAW-NEG`
negates coefficients.  Atomic tails stop either recursion, so malformed inputs
have deterministic total behavior without being assigned extra mathematical
meaning.  `POLY-ADD` and `POLY-NEG` normalize their raw results, and `POLY-SUB`
is addition with the canonical negation.  Consequently cancellation of a final
coefficient shortens the result and complete cancellation produces `nil`.

The certified homomorphism theorems say evaluation preserves addition,
negation, and subtraction.  On canonical inputs, ordinary ACL2 `EQUAL` supports
the commutative additive-group laws: zero identities, commutativity,
associativity, inverses, double negation, subtraction laws.
Canonicality hypotheses are used exactly where recovering an input list from
its normalized representative requires them.

`RAW-SCALE` multiplies each fixed coefficient by one fixed field element and
discards atomic tails exactly as `RAW-NEG` does.  `POLY-SCALE` is the sole
normalization boundary.  It is canonical on every ACL2 input, invariant under
the scalar fixer and polynomial fixing/normalization, and its evaluation is the
field product of the scalar and the original evaluation.  The certified scalar
action includes zero and one, the zero polynomial, nested scaling, and both
distributivity laws; the expanding composition and distribution rules are
proved but disabled by default.  These polynomial equalities are structural
normalization results, not consequences of equality at all field points.

This is a generic canonical generalization of two strands of Community Books
prior art.  `projects/linear/field.lisp` scales fixed-length lists over an
abstract field and proves the corresponding action laws, but preserves their
zero-filled length and has no polynomial normalization or evaluation.
`nonstd/polynomials/polynomial-defuns.lisp` has constant-first dense scaling,
while `nonstd/polynomials/polynomial-lemmas.lisp` proves its evaluation law for
specialized rational/real coefficients.  Neither supplies GFIELD-generic,
fixer-total, canonical, directly executable GPOLY operations.  GPOLY follows
the recurring semantic pattern: establish raw Horner semantics, then transport
it through evaluation-preserving normalization.

The adapter regression defines exact copies using the fixed-arity PFIELD
operations and transports normalization-preserves-evaluation with
`:functional-instance`.  Separate executable copies specialize the same
recurrences to F_7 and compute fixing, trimming, internal-zero, constant,
nonconstant, and wraparound examples.

## Relationship to HS and deferred bridge

Both GPOLY and HS are dense, constant-first coefficient lists with `nil` as the
canonical zero.  HS stores PFIELD elements and threads an explicit modulus;
GPOLY uses the abstract GFIELD interface and has no modulus parameter.  A later
bridge may therefore use the identity conversion at a fixed PFIELD instance,
but must prove equivalence of canonical predicates, normalization, evaluation,
and eventually addition and multiplication.

This additive-and-scaling layer deliberately contains no generic polynomial multiplication,
degree, leading coefficient, division, gcd, derivatives, root counting, field
enumeration, or extension-field implementation.  It provides syntax and
semantics over an assumed field, not an implementation of every finite field.

## HS addition proof review and future bridge

The HS `POLY-ADD-RAW` has the same coefficientwise, unequal-length recursion as
GPOLY `RAW-ADD`; GPOLY additionally fixes a copied remainder to honor its total
input policy.  Both public additions normalize the raw list.  Proper-list,
length, and recursion facts are **purely structural**.  Commutativity,
associativity, identities, inverse/cancellation, and Horner compatibility are
**generic field algebra**.  HS closure rules involving `FEP`, positivity or
primality hypotheses, and every operation carrying an explicit `p` are
**explicit-modulus PFIELD reasoning**.

The fixed-prime adapter removes that explicit argument with exact-arity
wrappers.  Functional instantiation transports raw-add commutativity; the transported
normalization/evaluation theorem and the specialized raw-add evaluation theorem
then establish addition-preserves-evaluation.  Executable F_7 copies check all
operations.  HS closure,
commutativity, associativity, and evaluation-of-add theorems should eventually
be concrete instances.  An identity-on-proper-lists bridge appears feasible
after proving that fixed HS coefficients make GPOLY's remainder fixing an
identity and that both normalizers coincide.  This PR intentionally neither
changes nor removes any HS theorem, and polynomial multiplication remains a
separate future task.

Scaling is intended to support later polynomial multiplication, division,
monic normalization, and extension-field reduction.  In particular,
`nonstd/polynomials/polynomial-defuns.lisp` recursively builds multiplication
from scaling, addition, and a zero-coefficient shift.  That construction is
prior art to compare with direct convolution in the next multiplication design
review; neither multiplication nor shifting is implemented by this milestone.
