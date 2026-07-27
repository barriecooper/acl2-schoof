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
invariance of normalization under prior coefficient fixing, identity on
canonical inputs, idempotence, the nil/nonzero conventions, and non-increasing
length.  Evaluation is field-valued and is invariant under point fixing,
coefficient fixing, trimming, and normalization; constant and zero point
formulas are also proved.

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

`books/polynomial/generic/division.lisp` certifies `POLY-DIVMOD-CORE` and the total `(mv q r)` public `POLY-DIVMOD`.  Canonical remainder length is the measure, the one-step decrease theorem supplies termination, and an accumulator invariant supplies normalized reconstruction without evaluation extensionality.  The final remainder is zero or strictly below the normalized nonzero divisor.  Guards are verified separately.  The separately certified F7 book now instantiates this recursion with ordinary definitions and verified guards. Concrete PFIELD division, F7 uniqueness, gcd, and extended gcd remain open.

The concrete F7 normalization interface exports `F7-NORMALIZE-NIL`, the
literal zero-input fixed point used by the unconditional
`F7-POLY-DIVMOD-ZERO-DIVIDEND` contract.  The divmod proof enters only the
top-level no-step core branch and uses that normalization fact explicitly;
normalization implementation remains closed when the divmod theorem is
proved and consumed.  The contract covers every modulus, including malformed
inputs through public normalization.  The ordinary rewrite
`F7-POLY-REMAINDER-ZERO-DIVIDEND` projects its remainder component directly,
unconditionally reducing `(F7-POLY-REMAINDER NIL MODULUS)` to `NIL` for the
same total range of moduli.  This adds no division algorithm reasoning: its
closed-theory consumer leaves normalization, divmod-core, division-step, and
arithmetic closed.

The F7 normalization/representation interface also exports the non-rewriting
`F7-CANONICAL-POLYNOMIAL-ATOM-IS-NIL` structural contract: under the canonical
dense representation, the only atomic polynomial is literal `NIL`.  The
existing F7X2 fixed-modulus remainder-idempotence proof and the public
variable-modulus F7 remainder-idempotence proof consume this theorem explicitly
instead of duplicating its normalization proof.  It is the representation
bridge used by that new public theorem; by itself it establishes no new
remainder or divmod behavior, degree bound, reducedness, divisibility,
congruence, unit/associate, irreducibility, GCD/XGCD, inverse, or F7X2
arithmetic/correctness result.

This narrow projection does not by itself establish the divisibility
equation, reduced nondivisibility, divisibility witnesses or transitivity,
units or associates, irreducibility-to-monic-GCD-one, modular-inverse
correctness, or F7X2 correctness.

The concrete F7 remainder projection now also exports the normalized-zero
modulus fallback, the strict degree bound for a nonempty normalized modulus,
and the canonical lower-degree no-op property.  The first two are shallow
projections of the public F7 divmod result.  The lower-degree theorem inspects
only the top-level divmod control to show that its recursive branch is
inactive; its public statement does not expose division recursion or
polynomial arithmetic.  Focused local symbolic consumers check each contract
independently with every executable definition closed.

This concrete foundation now also establishes unconditional public F7 remainder
idempotence for every dividend and modulus, including zero-normalizing,
nonzero-constant, positive-degree, malformed, canonical, and noncanonical
inputs.  Its bounded semantic proof uses the existing public canonicality,
strict degree-bound, zero-dividend, canonical lower-degree, normalized-zero
modulus, and canonical-atom representation contracts.  Both that proof and its
focused symbolic consumer keep normalization, canonicality, remainder/divmod,
division-step, degree, and arithmetic implementations closed.  This is stability
of the public remainder operation, not quotient/remainder reconstruction or
uniqueness.  It does not establish the quotient/remainder divisibility equation,
reduced nondivisibility, general quotient/remainder uniqueness, divisibility
witnesses or transitivity, congruence infrastructure, units or associates,
irreducibility-to-monic-GCD-one, modular-inverse correctness, or new F7X2
correctness.

## Generic modular reduction (certified)

`books/polynomial/generic/reduction.lisp` defines `POLY-REMAINDER` as the
remainder projection of one call to public `POLY-DIVMOD`; it neither copies nor
reimplements division recursion and inherits that API's input normalization.
The certified package proves the direct divmod connection, unconditional
canonicality and its explicit `NORMALIZE` fixed-point form, invariance under
normalizing either operand, normalized-zero and literal-`nil` modulus fallback
to `NORMALIZE(dividend)`, the strict degree bound for a nonempty normalized
modulus, and unconditional idempotence. Literal zero is preserved for every
modulus. Polynomial one is preserved exactly by the positive-degree theorem;
polynomial-one and every other normalized nonzero constant modulus instead
produce literal `nil`. The lower-degree helper is
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

This existing public remainder is therefore the canonical-representative
boundary; no `reduce` alias is introduced. It is total on every ACL2 object:
atoms and dotted tails are discarded by normalization, coefficients are fixed,
and trailing zeroes are trimmed before division. The boundary is shared by
possibly reducible Schoof coordinate quotients and by irreducible quotients
which may later be promoted to extension fields. Equality of representatives
is ordinary structural equality after reduction; `POLY-CONGRUENT-P` names the
separate quotient equivalence. Neither reduction nor congruence makes a field
claim.

Generic remainder is invariant under prior coefficient fixing of either its
dividend or its modulus.  Both rewrite laws are unconditional over the complete
total ACL2 input domain, including `nil`, atoms, improper and malformed lists,
normalized-zero and constant moduli, and positive-degree polynomials.

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
obligations remain Proved. General associate theory remains open.

Monic normalization now preserves divisibility in either argument position,
unconditionally.  `POLY-DIVIDES-P-OF-POLY-MONIC-NORMALIZE-DIVIDEND` and
`POLY-DIVIDES-P-OF-POLY-MONIC-NORMALIZE-DIVISOR` split explicitly on normalized
zero.  That branch uses the explicit `nil` result and normalization invariance;
the nonzero branch recognizes monic normalization as scaling by the fixed
nonzero inverse of the leading coefficient and directly applies the two
certified scaling laws.  Thus malformed atoms, dotted tails, zero-normalized
representations, trailing zeroes, and noncanonical coefficients inherit the
total normalization semantics.  No coefficient induction, quotient witness,
or low-level division reasoning is added.  Raw Euclidean-gcd correctness and
exact representatives, including the negative-unit result, remain unchanged,
and monic normalization remains explicit.  No associate predicate is
introduced.

`POLY-MONIC-EUCLIDEAN-GCD(a,b)` is now the transparent, total composition
`POLY-MONIC-NORMALIZE(POLY-EUCLIDEAN-GCD(a,b))`, not a new gcd algorithm.  Its
public structural interface states the exact composition, canonical and
normalized output, exact preservation of normalized zero/nonzero status, and
an unconditional leading coefficient of field zero or field one.  The raw
Euclidean result remains unchanged: in particular, its negative-unit example
still returns negative one, while the wrapper explicitly post-processes that
representative to polynomial one.  Atoms, dotted tails, trailing zeroes,
zero-normalized inputs, and malformed or noncanonical coefficients inherit the
existing component normalization semantics.  These proofs expand only the
wrapper and instantiate the monic-normalization structural API; they introduce
no recursion, induction, guards, coefficient reasoning, or low-level division
reasoning.

The wrapper is now certified to divide both inputs, and every common divisor
of the inputs is certified to divide the wrapper.  The proof is purely
compositional: divisor-position monic-normalization invariance transports each
raw-gcd divides-input theorem, while dividend-position invariance transports
raw-gcd greatestness.  Both equivalences are unconditional, so nil, malformed
atoms and coefficients, dotted tails, trailing zeroes, and other
zero-normalized or noncanonical representations retain the existing total
semantics.  Only the public wrapper equation and common-divisor definition are
controlled expansions.  No Euclidean recursion, induction, zero/nonzero split,
inverse or coefficient reasoning, quotient witness, multiplication/scaling
proof, or low-level division reasoning is introduced.  The raw representative,
including the visible negative-unit result, is unchanged.  This completes
monic-gcd correctness, not uniqueness; associate theory and a monic predicate
remain absent.

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
existential quotient witnesses or concrete PFIELD/F7 API.  The separate raw
XGCD layer described below now supplies Bézout coefficients.  Uniqueness,
associate theory, and unit-invariance theory remain open; the
subsequent certified layers now provide monic normalization and the transparent
monic-gcd wrapper described above.

`GPOLY-MOD-CONGRUENCE` is proved by the one-sided and simultaneous
`POLY-REMAINDER-OF-POLY-MUL-*` laws, `POLY-CONGRUENT-P-OF-POLY-MUL` and its
one-sided corollaries, and
`POLY-MUL-POLY-CONGRUENT-P-WITH-REMAINDERS`.

`generic/reduced-arithmetic.lisp` exposes `POLY-REDUCED-ADD`,
`POLY-REDUCED-NEG`, `POLY-REDUCED-SUB`, and `POLY-REDUCED-MUL`. Each is exactly
one existing normalized public operation followed by `POLY-REMAINDER`; there is
no recursion, modulus classification, GCD test, or alternate reducer. Zero
modulus recovers normalized polynomial arithmetic, polynomial one and every
normalized nonzero constant modulus return `nil`, and positive-degree moduli
return bounded canonical representatives. The certified interface includes
normalization and reduction fixed points, all-operand normalization invariance,
and representative invariance using the existing remainder arithmetic laws.
The F7 specializations exercise reducible and irreducible-looking moduli without
making irreducibility or field claims. These representative operations are now
emitted by the transparent project-local `def-reduced-ring-instance` generator
with their original names, bodies, total guards, and arbitrary-input semantics
unchanged.  Its expansion contains only ordinary DEFUN, VERIFY-GUARDS, and
independently selected DEFTHM events.  The public symbolic F7 ring-law instances
are `F7-POLY-REDUCED-ADD-COMMUTATIVE`,
`F7-POLY-REDUCED-ADD-ASSOCIATIVE`,
`F7-POLY-REDUCED-ADD-ZERO-LEFT`,
`F7-POLY-REDUCED-ADD-ZERO-RIGHT`,
`F7-POLY-REDUCED-ADD-INVERSE-LEFT`,
`F7-POLY-REDUCED-ADD-INVERSE-RIGHT`, and
`F7-POLY-REDUCED-MUL-RIGHT-DISTRIBUTIVE`, each transported directly from its
generic theorem by the explicit F7 functional substitution.  The remaining F7
theorem suite remains open; addition commutativity, associativity, the two
identity laws, and the two additive-inverse laws do not constitute the complete
additive interface.  The non-rewriting
`F7-POLY-REDUCED-MUL-DEFINITION` and
`F7-POLY-REDUCED-ONE-DEFINITION` equations expose only the concrete
remainder-level meaning of the generated multiplicative operations, while the
permutative `F7-POLY-REDUCED-MUL-COMMUTATIVE` rule supplies their unconditional
total-semantics symmetry.  The five public
`F7-CANONICAL-POLYNOMIAL-P-OF-POLY-REDUCED-{ADD,NEG,SUB,MUL,ONE}` rules certify
unconditional canonical-predicate output for every generated reduced-ring
operation.  The corresponding normalization rules and
`F7-POLY-REMAINDER-OF-POLY-REDUCED-{ADD,NEG,SUB,MUL,ONE}` rules certify
unconditional normalization and remainder fixed points for all five operations,
including every total modulus case.  The non-rewriting
`F7-POLY-REDUCED-ADD-OF-REMAINDERS`,
`F7-POLY-REDUCED-NEG-OF-REMAINDER`,
`F7-POLY-REDUCED-SUB-OF-REMAINDERS`, and
`F7-POLY-REDUCED-MUL-OF-REMAINDERS` theorems state that, for one fixed modulus,
simultaneously replacing every arithmetic operand by its F7 remainder leaves
the literal reduced output unchanged.  They are available only by explicit use
or through deliberately derived rules.  Fixer/remainder compatibility, full
equal-remainder congruence, modulus-representative independence, degree-bound
specializations, remaining ring laws, exponentiation, inversion, and field
promotion remain open.  These are
representative operations only until `generic/reduced-ring.lisp`, which now certifies the complete
literal-equality commutative-ring interface and modulus-dependent
`POLY-REDUCED-ONE`. Identity conclusions return the canonical remainder for
arbitrary representations, with focused fixed-representative corollaries.
Zero modulus gives normalized polynomial arithmetic; polynomial one and every
normalized nonzero constant give the trivial ring; positive-degree moduli are
covered regardless of reducibility. Irreducibility, unit characterization,
field promotion remains open. The runtime supports both
reducible Schoof coordinate quotients and moduli later proved irreducible.

`POLY-CONGRUENT-P` remains the only generic quotient-equality relation.  Its
meaning is exactly equality of `POLY-REMAINDER` results for every ACL2 input;
it is not defined through divisibility or witnesses and creates no ACL2
quotient object.  `generic/quotient-equivalence.lisp` packages equality
implication, remainder-fixed collapse, exact constant cases, and literal
result equality when any of the four reduced operations receives congruent
operands.  For normalized-zero modulus the relation is equality of normalized
polynomials; for polynomial one or any normalized nonzero constant every pair
is equivalent because both remainders are `nil`; for positive degree it is
equality of bounded canonical remainders.  No irreducibility premise occurs,
so this is neither field promotion nor a field-only equality relation.

The Euclidean remainder step additionally has a certified natural-valued
descent measure: for a nonempty normalized divisor, the length of the
canonical remainder (and hence of its normalization) is strictly less than
the length of the normalized divisor.  This follows only from canonicality,
the strict degree bound, and the canonical degree/length characterization;
it does not unfold recursive division.  A zero normalized divisor is the
recursion base case.  Raw algebraic gcd correctness is publicly packaged, and
the later transparent monic wrapper is mathematically certified.  No quotient
witnesses, modular inverses, or concrete PFIELD/F7 APIs are introduced by
those layers.

## Raw generic extended Euclidean gcd (certified)

`generic/xgcd.lisp` adds the transparent, total
`POLY-EXTENDED-EUCLIDEAN-GCD`.  It returns `(mv gcd s t)`, calls
`POLY-DIVMOD` once per nonzero step, recurses from `(first,second)` to
`(second,remainder)`, and uses `(len (normalize second))` as its measure.  Its
base result is exactly `(mv (normalize first) (polynomial-one) nil)`; its step
returns `t-next` and `s-next - t-next*quotient` as the two coefficients.

All three projections are canonical and normalized.  The gcd projection is
exactly the existing raw `POLY-EUCLIDEAN-GCD`, without monic rescaling, and the
unconditional certified identity is `s*first + t*second = gcd`.  Focused exact
regressions cover zero, malformed and dotted inputs, trailing zeros, coefficient
fixing, equal inputs, exact division, and a multi-step quotient chain.  This
completes the raw generic XGCD and its Bézout certificate.

## Monic generic extended Euclidean gcd (certified)

`generic/monic-xgcd.lisp` adds the single transparent, nonrecursive
`POLY-MONIC-EXTENDED-EUCLIDEAN-GCD` post-processing boundary.  It calls the raw
XGCD once and scales both raw coefficients by
`FIELD-INV(POLY-LEADING-COEFFICIENT(gcd))`, exactly the scalar used by
`POLY-MONIC-NORMALIZE`.  Its first projection is exactly
`POLY-MONIC-EUCLIDEAN-GCD`, all projections are canonical and normalized, and
its unconditional certificate reconstructs that monic gcd.  Total inverse and
scale conventions make a zero raw gcd return exactly `(mv nil nil nil)`.

This layer adds no recursion or division.  The concrete F7 specialization now
retains the same uniform body as `F7-POLY-MONIC-EXTENDED-EUCLIDEAN-GCD`: one
raw call followed only by leading coefficient/inverse, monic normalization, and
scaling of both coefficients.  Its guards, exact projection, unconditional
Bézout identity, structural interface, and total executions are certified.
Polynomial modular inversion, reduction modulo a defining polynomial, quotient
fields, extension fields, uniqueness, and general associate/unit theory remain
open.

## Monic XGCD reduction bridge (certified)

`generic/monic-xgcd-reduction.lisp` connects the first coefficient returned by
`POLY-MONIC-EXTENDED-EUCLIDEAN-GCD` to the existing public
`POLY-REMAINDER`.  When the monic gcd is `POLYNOMIAL-ONE`, reducing that
coefficient times the first input modulo the second input returns exactly
`POLY-REMAINDER(POLYNOMIAL-ONE, second)`.  The theorem is unconditional beyond
the gcd premise and therefore retains the library's total semantics for zero,
malformed, noncanonical, and constant moduli.

The result is literally `POLYNOMIAL-ONE` when `(normalize second)` is nonempty
and has degree greater than zero.  This qualification is essential: reduction
modulo normalized zero returns the normalized dividend, while reduction modulo
every nonzero constant is `nil` (in particular, one modulo
`POLYNOMIAL-ONE` is `nil`).  The division book's new total
`POLY-REMAINDER-OF-POLY-ADD-DIVISOR-MULTIPLE` packages remainder invariance
without a nonzero-modulus side condition.

## Generic modular-inverse candidate (certified)

`generic/modular-inverse.lisp` adds the single transparent, nonrecursive
`POLY-MODULAR-INVERSE`.  It calls `POLY-MONIC-EXTENDED-EUCLIDEAN-GCD` exactly
once, selects its first Bézout coefficient, and returns that coefficient's
public `POLY-REMAINDER` modulo the supplied modulus.  Thus every ACL2 input
produces a canonical, normalized reduced candidate; the function has no
success flag, gcd test, exceptional result, or new recursion.

Correctness is conditional.  When `POLY-MONIC-EUCLIDEAN-GCD(first,modulus)` is
`POLYNOMIAL-ONE`, multiplying the candidate by `first` and reducing returns
`POLY-REMAINDER(POLYNOMIAL-ONE,modulus)`.  The existing unconditional
multiplication/remainder compatibility theorem transports the certificate
from the Bézout coefficient to its reduced representative.  When the
normalized modulus is additionally nonempty and has positive degree, the
right-hand side is literally `POLYNOMIAL-ONE`.

The generic unit interface now states this certificate directly in reduced
ring notation.  Under that same exact monic-GCD-equals-`POLYNOMIAL-ONE`
condition, both `POLY-REDUCED-MUL(first, inverse, modulus)` and its symmetric
orientation are literally `POLY-REDUCED-ONE(modulus)`.  The first proof is a
direct restatement of the certified Bézout/remainder result, and the other is
derived from reduced multiplication commutativity.  Operands are arbitrary
ACL2 objects; no remainder-fixed, positive-degree, or irreducibility premise
is added.

For a zero-normalized modulus the candidate is the normalized monic-XGCD
coefficient.  For every nonzero constant modulus it is `nil`, including
modulus `POLYNOMIAL-ONE`; no literal-one claim is made for constants.
This proves that the existing computation is an inverse whenever its certified
monic GCD is one.  It neither proves the converse characterization of units nor
that every nonzero representative is invertible.  Reducible quotient rings can
still have nonzero nonunits and zero divisors; irreducibility remains the later
hypothesis for field promotion.  Irreducibility implying monic gcd one,
quotient-field laws, concrete polynomial-field instances, and extension fields
remain open.


## Concrete F7 modular inverse (certified)

`generic/f7-division.lisp` now specializes the generic modular-inverse candidate literally: one `F7-POLY-MONIC-EXTENDED-EUCLIDEAN-GCD` call selects its first Bezout coefficient and one existing `F7-POLY-REMAINDER` call canonicalizes it. The guard-verified total function does not separately test the GCD; correctness is conditional on `F7-POLY-MONIC-EUCLIDEAN-GCD` being polynomial one, and the literal-one remainder corollary additionally requires positive modulus degree. This supplies inversion only for units modulo a modulus. Later quotient-ring operations and field inversion under irreducibility remain open.

## Generic logical irreducibility boundary

`generic/irreducibility.lisp` defines a polynomial unit to mean formal degree
zero after the existing total normalization.  It defines `POLY-REDUCIBLE-P`
by an explicitly logical `DEFUN-SK` witness equation: two nonunit factors whose
existing `POLY-MUL` is the normalized input.  `POLY-IRREDUCIBLE-P` means
positive degree and absence of such a witness.  This is not an executable
factor search, certificate checker, factorization algorithm, or new equality,
division, or normalization operation.

The boundary is total.  Atoms, malformed/dotted tails, out-of-range
coefficients, and trailing zeros first receive the established coefficient
fixing and normalization semantics.  Normalized zero, polynomial one, and all
other constants are not irreducible.  Positive-degree nonmonic inputs are not
rejected syntactically: scalar associates are judged by the same factor
meaning.  The certified divisor bridge uses the existing division quotient as
the witness for `normalize(dividend) = quotient * normalize(divisor)`.  Thus a
divisor of an irreducible polynomial is either a degree-zero unit or scalar
associate in the focused, operational sense that the irreducible polynomial
divides it; no general associates predicate is introduced.

The concrete F7 predicate boundary exports the same three focused logical
views without making the quantified reducibility predicate executable:
`F7-POLY-IRREDUCIBLE-P-DEFINITION` is a non-rewriting equation,
`F7-POLY-IRREDUCIBLE-P-IMPLIES-POSITIVE-DEGREE` is a forward-chaining
consequence, and `F7-POLY-IRREDUCIBLE-P-FACTOR-CHARACTERIZATION` excludes a
factorization into two nonunits.  These events do not yet provide the F7
divisor alternative, the F7 irreducibility-to-monic-GCD-one bridge, concrete
modular-inverse correctness, F7X2 inversion correctness, or a quotient-field
construction.

Applying that alternative to the existing monic GCD proves that it is
`POLYNOMIAL-ONE` unless the irreducible modulus divides the first input.  In
particular, a nonzero representative fixed by `POLY-REMAINDER` cannot be so
divisible (idempotence would make its remainder simultaneously itself and
zero), and therefore has monic GCD one.  This is a logical bridge only: the
existing modular inverse remains the transparent XGCD-derived computation,
and no quotient field, concrete `F7[x]/(x^2+1)` interface, or new executable
boundary is added.
