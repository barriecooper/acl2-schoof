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

Zero-prefix addition and scaling are stable, narrowly reusable raw facts. The
public `ZERO-PREFIX`, `POLY-SHIFT`, and `MONOMIAL` operations now provide the
certified shift API used by degree and division.  The completed public
laws are transported by certified functional instantiation to the fixed PFIELD
adapter and then to the executable F_7 instance; the existing computations
remain regressions rather than generic proofs.

The adapter regression defines exact copies using the fixed-arity PFIELD
operations and transports normalization-preserves-evaluation with
`:functional-instance`.  Separate executable copies specialize the same
recurrences to F_7 and compute fixing, trimming, internal-zero, constant,
nonconstant, and wraparound examples.

## Constant embedding and compact ring API

`CONST` is the explicit unital embedding of the coefficient field into
canonical GPOLY values.  It fixes its arbitrary ACL2 input once and returns a
singleton for a nonzero result, but returns canonical `nil` for field zero;
`(0)` is deliberately never exposed as polynomial zero.  `POLYNOMIAL-ONE`
names the existing singleton-one representation without introducing a second
zero constructor.  The constructor is directly executable and the same small
DEFUN-only template supplies the PFIELD and F_7 versions.

The embedding preserves field addition, negation, subtraction, multiplication,
zero, and one.  Multiplication by `CONST` on either side reduces to
`POLY-SCALE`; the right-hand statement follows mathematically from polynomial
commutativity rather than another coefficient proof.  These reducing bridge,
fixer, zero/one, and evaluation rules are enabled.  The operation-preservation
rules are disabled because expanding a field expression into polynomial
operations is not a useful global simplification.

Together, the established additive group laws, multiplicative zero and one,
commutativity, associativity, and both distributive laws are the compact public
commutative-ring API.  For every fixed point, `EVAL-OF-NIL`,
`EVAL-OF-POLYNOMIAL-ONE`, the existing addition/negation/subtraction/product
theorems, and `EVAL-OF-CONST` state that evaluation is a unital ring
homomorphism.  This is theorem-level consolidation, not a new executable
algebra algorithm.  Equality of canonical values remains ordinary ACL2
`EQUAL`.  It is formal polynomial equality and remains distinct from equality
of the functions induced over a finite field.

## Relationship to HS and deferred bridge

Both GPOLY and HS are dense, constant-first coefficient lists with `nil` as the
canonical zero.  HS stores PFIELD elements and threads an explicit modulus;
GPOLY uses the abstract GFIELD interface and has no modulus parameter.  A later
bridge may therefore use the identity conversion at a fixed PFIELD instance,
but must prove equivalence of canonical predicates, normalization, evaluation,
and eventually addition and multiplication.

The public structural operations `POLY-DEGREE` and
`POLY-LEADING-COEFFICIENT` each normalize arbitrary input exactly once.  Thus
atomic inputs and malformed tails follow the existing fixer policy: atoms end
the coefficient list and a malformed tail is discarded.  Degree of canonical
zero (`nil`) is the sentinel `-1`, and its leading coefficient is field zero.
For a canonical nonzero polynomial, degree is length minus one and leading
coefficient is the final coefficient, which is certified nonzero.  These are
formal structural properties of the constant-first dense representation, not
facts inferred from evaluation (which is not extensional over finite fields).
The same transparent two-`DEFUN` template supplies constrained PFIELD and
ordinary executable F7/F11 operations.

Leading coefficient now commutes unconditionally with generic scalar
multiplication: the leader of `POLY-SCALE(scalar, poly)` is `FIELD-MUL` of the
scalar and the leader of `poly`.  Total fixing and normalization include zero
scalars, zero-normalized polynomials, malformed atoms and tails, coefficients
requiring fixing, and trailing-zero representations.  The nonzero proof is
structural: `RAW-SCALE` preserves list shape and maps the final coefficient,
while canonical final-coefficient nonzeroness and the field no-zero-divisor
law show that normalization retains the scaled leader.  This completes the
scaling/leading-coefficient bridge used by generic monic normalization.

`POLY-MONIC-NORMALIZE` is total, transparent, nonrecursive, and explicitly
returns `nil` when its input normalizes to zero.  Otherwise it applies
`POLY-SCALE` with the inverse of `POLY-LEADING-COEFFICIENT`.  Thus malformed
atoms, dotted tails, unfixed coefficients, and trailing-zero representations
follow the existing normalization policy.  The result is canonical and already
normalized, and its `consp` characterization preserves zero/nonzero status
exactly.  Its unconditional leading-coefficient theorem returns
`FIELD-ZERO` in the zero branch and `FIELD-ONE` in the nonzero branch.

The proof composes the existing nonzero-leading-coefficient fact, field closure
and left inverse law, `POLY-LEADING-COEFFICIENT-OF-POLY-SCALE`, and scaling
canonicality; it adds no structural induction.  Raw Euclidean-gcd correctness
is unchanged, and raw gcd results may remain non-monic until this operation is
applied explicitly.  Divisibility/associate preservation is not yet certified,
and no monic predicate or monic gcd wrapper is introduced.

The certified multiplication consequences are structural.  For nonempty
canonical factors, `RAW-LEADING-COEFFICIENT-OF-RAW-MUL` identifies the final
raw coefficient, in input order, as the field product of the two final input
coefficients.  Coefficient closure and raw-product nonemptiness give the list
shape, while `EQUAL-FIELD-MUL-ZERO` and the nonzero canonical leaders show that
the raw product also has a nonzero final coefficient.  Thus the complete raw
convolution is canonical, normalization is its identity, the public leading
coefficient is the ordered product of the input leading coefficients, and the
raw length formula yields degree addition.  In particular, a product of two
nonempty canonical polynomials is nonempty: this is the polynomial
no-zero-divisor consequence.  No commutativity or evaluation extensionality is
used in this leading-term argument.

This arithmetic layer includes certified generic division and remainder, but
still contains no gcd, irreducibility, extension-field reduction, derivatives,
field enumeration, or extension-field implementation.  It provides
syntax and semantics over an assumed field, not an implementation of every
finite field.

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

The certified monomial foundation now provides total `ZERO-PREFIX`,
`POLY-SHIFT`, and `MONOMIAL` operations.  Shifts use `NFIX`, preserve canonical
zero, add the natural index to the degree of a canonical nonzero polynomial,
and preserve its leading coefficient.  Monomials fix arbitrary coefficients,
map fixed zero to `nil`, and have the expected degree and leading coefficient
when nonzero.  These are structural dense-list results, not evaluation
extensionality.  The certified quotient/remainder contract and zero-divisor fallback are
maintained in `polynomial-division.md`. Generic recursive division,
reconstruction, and the final remainder bound are certified. Generic modular
reduction is now certified; polynomial congruence is the immediate next
milestone. Gcd, irreducibility, monic normalization, and extension-field
reduction remain later work.

## One long-division step

`division-step.lisp` adds ordinary total `DEFUN` operations for one leading-term
cancellation.  The public wrapper normalizes its two inputs once; the canonical
core returns `(term . next)`.  Certified structural theorems establish the
ordered field quotient coefficient, degree difference, matching product leader,
strict degree decrease, and exact `EQUAL` reconstruction.  This step is the certified foundation used by complete generic recursive
division; it is not Euclidean gcd theory and introduces no split
logical/executable boundary.


## Generic recursive division (certified)

`books/polynomial/generic/division.lisp` certifies `POLY-DIVMOD-CORE` and the total `(mv q r)` public `POLY-DIVMOD`.  Canonical remainder length is the measure, the one-step decrease theorem supplies termination, and an accumulator invariant supplies normalized reconstruction without evaluation extensionality.  The final remainder is zero or strictly below the normalized nonzero divisor.  Guards are verified separately.  No executable boundary or concrete PFIELD/F7 instance is added; concrete generated division, uniqueness, gcd, and extended gcd remain open.

## Generic modular reduction (certified)

`books/polynomial/generic/reduction.lisp` defines `POLY-REMAINDER` as the
remainder projection of one call to public `POLY-DIVMOD`; it neither copies nor
reimplements division recursion and inherits that API's input normalization.
The certified package proves the direct divmod connection, unconditional
canonicality, invariance under normalizing either operand, normalized-zero and
literal-`nil` modulus fallback to `NORMALIZE(dividend)`, the strict degree bound
for a nonempty normalized modulus, and idempotence.  The lower-degree helper is
a public-division consequence, not a new induction. `POLY-REMAINDER` is an
ordinary transparent `DEFUN` with explicitly verified guards; the constrained
generic field is not claimed as a concrete runtime field.

Bounded Euclidean remainders are also uniquely characterized: when a
normalized dividend is reconstructed as a polynomial quotient times a
nonzero normalized modulus plus a canonical remainder of strictly lower
degree (or `nil`), `POLY-REMAINDER` returns that remainder.  This theorem is
derived from the certified division reconstruction together with generic
polynomial cancellation, nonzero-product, and degree algebra.  It introduces
neither a second reduction algorithm nor a concrete reduction API.

The same generic reduction book now defines `POLY-CONGRUENT-P` as structural
equality of canonical `POLY-REMAINDER` results.  The relation is certified as
reflexive, symmetric, and transitive and is invariant under normalizing either
representative or the modulus.  Every polynomial is congruent to its canonical
remainder; canonical representatives below a nonzero normalized modulus degree
are congruent exactly when structurally equal.  Adding an arbitrary polynomial
multiple of the normalized modulus preserves the remainder and therefore the
congruence class.  When the normalized modulus is zero, congruence is exactly
structural equality of the normalized inputs. Congruence is now compatible
with addition, additive negation, subtraction, and multiplication, and operands
may be replaced by their canonical remainders before each operation followed
by reduction. For multiplication, either or both factors may be replaced.
These unconditional laws include the normalized-equality semantics of a zero
modulus.

## Generic divisibility and one Euclidean step (certified)

`books/polynomial/generic/euclidean.lisp` defines the transparent Boolean
predicate `POLY-DIVIDES-P` with divisor first and dividend second.  It decides
divisibility by testing whether `POLY-REMAINDER(dividend,divisor)` is the unique
canonical zero, `nil`; no existential quotient witness or concrete
divisibility API is introduced.  Equivalently, the dividend is
`POLY-CONGRUENT-P` to zero modulo the divisor.  Divisibility is invariant under
normalizing either argument.  Every polynomial divides zero and itself, the
constant-first polynomial one divides every polynomial, and zero divides
exactly the polynomials whose normalization is `nil`.  The certified closure
laws cover addition, negation, subtraction, and multiplication by an arbitrary
polynomial.

Dividend scaling has the certified public law
`POLY-DIVIDES-P-OF-POLY-SCALE-DIVIDEND`: when `FIELD-FIX(scalar)` is not
`FIELD-ZERO`, a divisor divides `POLY-SCALE(scalar,dividend)` exactly when it
divides `dividend`. The forward construction multiplies the original dividend
by the constant polynomial for `scalar`. The reverse construction multiplies
the scaled dividend by the constant polynomial for `FIELD-INV(scalar)`, then
uses `POLY-MUL-CONST-RIGHT`, `POLY-SCALE-NESTED`,
`FIELD-MUL-INVERSE-LEFT`, and dividend-normalization invariance. The proof uses
only the public algebraic interface: it introduces no coefficient induction
and no quotient-witness API.

The theorem inherits total normalization semantics, including normalized zero,
atoms, dotted lists, trailing zeroes, and noncanonical coefficients. Its
nonzero hypothesis is necessary: zero scaling sends a nonzero polynomial to
`nil`, which the zero polynomial divides, although zero does not divide the
original polynomial. Divisor scaling now has the certified public law
`POLY-DIVIDES-P-OF-POLY-SCALE-DIVISOR`: under the same fixed-nonzero scalar
hypothesis, `POLY-SCALE(scalar,divisor)` divides a dividend exactly when the
unscaled divisor does. The preferred proof is entirely above division internals.
Reflexivity and multiplication closure show that the divisor divides its
scaling. Reflexivity plus dividend-scaling invariance show that the scaling
divides the original divisor, so inverse reasoning remains encapsulated in the
previous public theorem. `POLY-DIVIDES-P-TRANSITIVE`, proved from the public
Euclidean-remainder equivalence, composes these two directions. No coefficient
induction or quotient-witness API is introduced.

The divisor theorem inherits total normalization semantics for normalized zero,
atoms, dotted lists, trailing zeroes, and noncanonical coefficients. Its
nonzero hypothesis is necessary: zero scaling changes polynomial one into
`nil`, and zero does not divide polynomial one although one divides itself.
Raw Euclidean-gcd correctness and exact raw representatives, including the
negative-unit representative, are unchanged. `GPOLY-GCD`,
`GPOLY-GCD-COMPUTATION`, `GPOLY-MONIC-NORMALIZATION`, and both scaling
obligations remain Proved, and no monic gcd wrapper is introduced. General associate theory
remains open. The next focused PR should integrate monic normalization with
divisibility by composing both scaling laws with the exact zero/nonzero behavior
of `POLY-MONIC-NORMALIZE`; it should establish the precise two-sided
relationships before any monic gcd wrapper.

`POLY-DIVIDES-P-EUCLIDEAN-STEP-IFF` proves unconditionally that a candidate
divides both `first` and `second` exactly when it divides both `second` and
`POLY-REMAINDER(first,second)`.  The proof remains above recursive division:
public divmod reconstruction and the addition/multiplication congruence laws
show that `first` is congruent to its Euclidean remainder modulo every divisor
of `second`, and transitivity transfers congruence with zero in both
directions.  Reconstruction is unconditional, so the same proof includes a
zero-normalized second argument; in that boundary case the remainder is
`NORMALIZE(first)`.  It also includes zero candidate divisors and malformed or
noncanonical inputs through total normalization semantics.  Structural induction following `POLY-EUCLIDEAN-GCD` now proves the first
algebraic property of that raw computation: `POLY-EUCLIDEAN-GCD-DIVIDES-BOTH`
is unconditional, with one-sided `*-DIVIDES-FIRST` and `*-DIVIDES-SECOND`
corollaries.  The base case uses normalization, self-divisibility, and
zero-divisibility, including nonliteral normalized zero and malformed inputs.
The recursive case uses `POLY-DIVIDES-P-EUCLIDEAN-STEP-IFF` as its complete
algebraic bridge; it does not unfold recursive division or repeat
reconstruction or congruence reasoning.  The raw result may still be non-monic.

The complementary common-divisor greatestness direction is independently
certified by `POLY-COMMON-DIVISOR-DIVIDES-EUCLIDEAN-GCD`: every polynomial that
divides both inputs divides the raw Euclidean result.  Its induction follows
`POLY-EUCLIDEAN-GCD` while retaining an arbitrary candidate divisor.  The base
case rewrites the result to `NORMALIZE(first)` and uses dividend-normalization
invariance; the recursive case uses `POLY-DIVIDES-P-EUCLIDEAN-STEP-IFF` as the
entire algebraic bridge to the recursive pair.  It repeats neither
reconstruction and congruence algebra nor recursive division.
`POLY-COMMON-DIVISOR-P` now packages the finite, executable part of the public
raw-gcd specification: a candidate divides both inputs.  It is transparent,
nonrecursive, total, guarded by `t`, and has normalization laws for all three
arguments and forward rules for both divisibility facts.
`POLY-COMMON-DIVISOR-P-OF-EUCLIDEAN-GCD` is a direct instance of the certified
divides-both direction, and `POLY-COMMON-DIVISOR-P-GREATESTNESS` is a direct
instance of the independently certified greatestness direction.  The combined
`POLY-EUCLIDEAN-GCD-RAW-CORRECT` theorem exposes both facts at one public entry
point.  These packaging proofs use neither induction nor division reasoning.

The interface is unconditional over nil, malformed atoms and coefficients,
noncanonical lists, and trailing-zero representations.  Zero is a common
divisor exactly when both inputs normalize to zero.  The raw result is
canonical as a polynomial representation but need not be monic; it may be a
negative unit or another non-monic associate.  The specification therefore
determines a gcd only up to multiplication by nonzero field units.  It adds no
existential quotient witnesses, XGCD/Bézout machinery, or concrete PFIELD/F7
API.  Uniqueness, associate and unit-invariance theory, and monic normalization
remain open.

`GPOLY-MOD-CONGRUENCE` is proved by the one-sided and simultaneous
`POLY-REMAINDER-OF-POLY-MUL-*` laws, `POLY-CONGRUENT-P-OF-POLY-MUL` and its
one-sided corollaries, and
`POLY-MUL-POLY-CONGRUENT-P-WITH-REMAINDERS`. No quotient-ring operation, concrete
reduction/congruence API, gcd correctness, modular inverse, extension field, or concrete
F7/PFIELD division API is introduced here.

The Euclidean remainder step additionally has a certified natural-valued
descent measure: for a nonempty normalized divisor, the length of the
canonical remainder (and hence of its normalization) is strictly less than
the length of the normalized divisor.  This follows only from canonicality,
the strict degree bound, and the canonical degree/length characterization;
it does not unfold recursive division.  A zero normalized divisor is the
recursion base case.  Raw algebraic gcd correctness is now publicly packaged,
while monic normalization is not defined.  No quotient witnesses, extended
gcd, Bézout coefficients, modular inverses, or concrete PFIELD/F7 APIs are
introduced.  The next focused PR should inventory leading-coefficient,
scalar-multiplication, field-inversion, and nonzero-polynomial infrastructure
before introducing generic monic normalization.  Later stages should prove
that normalization preserves divisibility/associates, certify a monic gcd
wrapper, and only then develop XGCD/Bézout.
