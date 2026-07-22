# Generic dense polynomials

`books/polynomial/generic/package.lisp` establishes the dedicated `GPOLY`
namespace, `base.lisp` defines the abstract theory over `GFIELD`, and
`add.lisp` supplies the additive structure, `scale.lisp` supplies the scalar
action, `mul.lisp` supplies multiplication, and `pfield-instance.lisp` is their
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

Multiplication follows the recursive shifted-scaling construction in
`nonstd/polynomials/polynomial-defuns.lisp`: for constant-first coefficients,
`(a . f)g` is the raw sum of `a*g` and the zero-prefixed product `f*g`.
Compared with direct coefficient convolution, this choice is smaller and
reuses certified raw scaling and addition without a second coefficient-indexing
recursion.  `RAW-MUL` calls only raw operations, itself, and the minimal zero
prefix; `POLY-MUL` fixes both operands, invokes the raw algorithm, and
normalizes exactly once at its public boundary.  Evaluating a zero-prefixed
list multiplies its tail value by the point, supplying the shift step.  The
proof pattern is raw Horner semantics followed by transport across
evaluation-preserving normalization.

The structural multiplication laws were kept out of the executable
multiplication change so that the algorithm, total-input policy, and evaluation
bridge could be reviewed separately from the coefficient proof infrastructure.
They are now certified.  The actual dependency chain is raw-add middle-four
and nested interchange; scaling over addition and nested scaling; literal
zero-prefix addition/scaling; right recursion and raw commutativity; raw
distributivity; scaling/product compatibility and the small length lemmas that
remove a zero-scaled prefix; raw associativity; and finally transport through
normalization.  The central raw commutativity, distributivity, and associativity
equalities hold literally for proper fixed coefficient lists.  Normalized
congruence lemmas are still required at the public boundary because trimming
an input can change the length of a raw result.

Consequently `POLY-MUL` is a total commutative and associative operation and
distributes on both sides over `POLY-ADD`, as ordinary ACL2 `EQUAL` of canonical
representatives.  These are formal coefficient proofs: equality at every field
point cannot identify formal polynomials over a finite field, where distinct
polynomials can induce the same function.  Commutativity, associativity, both
distributive laws, raw-add interchange, and the rearranging shift lemmas are
disabled rules because their orientations either expand terms or invite
loops.  The constant-left multiplication rule remains enabled because it
strictly reduces multiplication to the existing scalar action.

Zero-prefix addition and scaling are stable, narrowly reusable raw facts.  No
public shift operation is introduced: shifted-product rearrangements and the
length/zero-scale lemmas remain local proof infrastructure until a later degree
or division development demonstrates a stable API need.  The completed public
laws are transported by certified functional instantiation to the fixed PFIELD
adapter and then to the executable F_7 instance; the existing computations
remain regressions rather than generic proofs.

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

This arithmetic layer deliberately contains no degree, leading coefficient,
division, gcd, derivatives, root counting, field
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
identity and that both normalizers coincide.  This work intentionally neither
changes nor removes any HS theorem.

The next intended work is the constant-polynomial embedding and a compact
polynomial commutative-ring consolidation, followed by degree and leading
coefficient.  Division, monic normalization, and extension-field reduction
remain later work.
