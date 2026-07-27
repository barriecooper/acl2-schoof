# Execution-boundary audit

This is the maintained inventory of public logical/executable boundaries.
“Same DEFUN template” means abstract and concrete instances share the recursive
algorithm, so there is no separate `MBE` equivalence obligation. Guard status
is not a semantic claim. Complexity statements are inferred from recursion
shape, not benchmark measurements.

| Public operation or family | Logical specification | Concrete implementation | Correctness bridge | Guard status | Executable regression | Classification |
| --- | --- | --- | --- | --- | --- | --- |
| GFIELD constrained operations (`field-*`) | `encapsulate` constraints | Not intended as a concrete runtime implementation | Encapsulated field laws | Ordinary logical definitions | None intended | 1 — ordinary abstract specification |
| PFIELD adapter operations | Fixed-arity adapters over constrained `pfield-modulus` | Not intended as a concrete runtime implementation | `pfield-*` laws and GFIELD functional instance | Ordinary DEFUN guards; modulus constrained | Logical adapter tests | 1 — ordinary abstract specification |
| Concrete F2/F7 operations except power | Same ordinary DEFUN bodies | Named `f2-*` / `f7-*` DEFUNs | GFIELD functional instances; F7 addition, multiplication, and total inverse fixing-congruence bridges needed by polynomial instances | Default guards | Concrete field tests plus canonical/noncanonical, negative, zero-class, and malformed F7 congruence checks in `generic/f7-division.lisp` | 2 — ordinary concrete executable definition |
| Original HS explicit-modulus polynomial operations | DEFUNs in `polynomial/{base,eval,degree}.lisp` | Same explicit-`p` DEFUNs | Certified algebra/evaluation/degree theorems | Ordinary DEFUN guards | Smoke tests | 2 — ordinary concrete executable definition |
| GPOLY normalization and evaluation | GFIELD template instance | PFIELD/F7 instances of `def-normalize-eval-instance` | `pfield-normalize-preserves-eval-from-generic`; `f7-normalize-preserves-eval-from-generic` | GPOLY guards explicitly verified; concrete default guards | Generic-polynomial tests | 2 — same DEFUN template; no MBE split |
| GPOLY addition, negation, subtraction | GFIELD template instances | PFIELD/F7 shared-template instances | `eval-of-poly-{add,neg,sub}` and transported instances | Addition functions are ordinary DEFUNs | Generic-polynomial tests | 2 — same DEFUN templates; no MBE split |
| GPOLY scaling | GFIELD template instance | PFIELD/F7 shared-template instances | `eval-of-poly-scale` and transported instances | GPOLY explicitly verified; concrete default guards | Generic-polynomial tests | 2 — same DEFUN template; no MBE split |
| GPOLY multiplication | GFIELD template instance | PFIELD/F7 shared-template instances | `eval-of-poly-mul` and transported instances | GPOLY explicitly verified; concrete default guards | Generic-polynomial tests | 2 — same DEFUN template; no MBE split |
| Constant embedding | `const` over GFIELD | PFIELD/F7 shared-template instances | `eval-of-const` and preservation/transport theorems | Ordinary DEFUN guards | Generic-polynomial tests | 2 — same DEFUN template; no MBE split |
| Field power (`field-pow`) | `field-pow-spec` | `field-pow-fast`, selected by `field-pow` MBE | `field-pow-fast-accumulator-invariant`; `field-pow-fast-correct` | Staged, then explicitly verified | None directly; generated instances are separate below | 4 — justified logical/executable boundary over constrained operations |
| PFIELD adapter field power | `pfield-pow-spec` | `pfield-pow-fast`, selected by `pfield-pow` MBE | `pfield-pow-fast-accumulator-invariant`; `pfield-pow-fast-correct` | Fast and public guards explicitly verified (with `pfield-fix`, `pfield-one`, and `pfield-mul` verified as callees) | None: the constrained modulus is not a named runtime field | 4 — justified boundary over a constrained adapter |
| Generated F2/F7 field powers | `f2-pow-spec`; `f7-pow-spec` | `f2-pow-fast` / `f7-pow-fast`, selected by the corresponding public MBE wrapper | `f2-pow-fast-accumulator-invariant`, `f2-pow-fast-correct`; `f7-pow-fast-accumulator-invariant`, `f7-pow-fast-correct` | Both fast and public guards explicitly verified (with each concrete fix, one, and multiply callee verified first) | `tests/field-kernel.lisp` (F2); `tests/pfield-adapter.lisp` (F7) | 4 — named concrete executable fields; closed |
| Polynomial power (`poly-pow`) | `poly-pow-spec` | `poly-pow-fast`, selected by `poly-pow` MBE | `poly-pow-fast-accumulator-invariant`; `poly-pow-fast-correct`; `eval-of-poly-pow` | Staged, then explicitly verified | Concrete F7 polynomial-power tests | 4 — justified logical/executable boundary |
| PFIELD/F7 generated polynomial instances (non-power) | Shared templates | PFIELD is constrained-modulus; F7 is concrete | Operation-specific transported theorems | Ordinary/default guards | F7 operation tests | 2 — same DEFUN templates; no MBE split |
| Generic polynomial degree / leading coefficient | `def-degree-instance` expands to two ordinary DEFUNs, each calling `normalize` once | `poly-degree`; `poly-leading-coefficient` | Normalization invariance, canonical structural equations, zero/closure/bound theorems in `generic/degree.lisp` | Explicitly verified | Generic certification | 1 — abstract field operations; no logical/executable split |
| PFIELD polynomial degree / leading coefficient | Same transparent two-DEFUN template | `pfield-poly-degree`; `pfield-poly-leading-coefficient` | Named normalized structural semantics theorems | Explicitly verified | Certified adapter book | 2 — constrained-modulus adapter, not claimed as concrete runtime |
| F7 polynomial degree / leading coefficient | Same transparent two-DEFUN template | `f7-poly-degree`; `f7-poly-leading-coefficient` | Named semantics bridges specialized from the PFIELD shape | Explicitly verified | `tests/generic-polynomial.lisp` and adapter-book assertions | 2 — ordinary concrete runtime; no MBE split |
| F7 polynomial zero-prefix / shift / monomial | Same transparent three-DEFUN template as GPOLY | `f7-zero-prefix`; `f7-poly-shift`; `f7-monomial` | Direct F7 structural, normalization, canonicality, degree, and leading-coefficient theorems | All three explicitly verified | Focused assertions in `generic/pfield-instance.lisp` | 2 — ordinary concrete runtime; no MBE split |
| Generic polynomial zero-prefix / shift / monomial | Transparent `def-monomial-instance` over GFIELD | Generic ordinary DEFUNs; PFIELD/F7 instances share the template | Certified normalization, canonicality, degree, and leading-coefficient laws | `zero-prefix`, `poly-shift`, and `monomial` explicitly verified | Generic certification and focused F7 assertions | 1/2 — transparent generators; no MBE split |
| Generic one-step division | Transparent `def-division-step-instance` over GFIELD | Four ordinary DEFUNs: core, wrapper, term accessor, next accessor | Certified term, product, reconstruction, and active strict-decrease group | Dependencies and all four generic functions explicitly verified | Generic certification | 1 — abstract transparent generator; no MBE split |
| Generic recursive divmod | `poly-divmod-core` and public `poly-divmod` | Same ordinary recursive DEFUNs | Accumulator reconstruction invariant and final remainder-degree bound | Both functions explicitly verified after division dependencies | Generic certification | 1 — abstract ordinary definitions; no MBE split |
| Concrete F7 recursive divmod | Generated `f7-poly-divmod-core`, `f7-poly-divmod`, and projection wrappers | Same ordinary transparent DEFUN recursion and projections | Functional instance of the generic public canonicality, reconstruction, and degree package | Complete concrete call chain explicitly verified | Exact multi-step, remainder, constant, zero-normalized, malformed, dotted, and normalization assertions in `generic/f7-division.lisp` | 2 — ordinary concrete runtime; no MBE split |
| Generic polynomial canonical representative | Remainder component of public `poly-divmod` | Existing `poly-remainder`, an ordinary projection wrapper; no redundant reducer | Direct divmod connection, canonicality and normalized fixed point, operand-normalization invariance, unconditional idempotence, exact zero/constant/one behavior, and strict positive-degree bound | Wrapper guard explicitly verified after `poly-divmod` | Focused generic structural regressions in `generic/reduction.lisp`; concrete F7 edge and repeated-reduction assertions in `generic/f7-division.lisp` | 1 — abstract ordinary definition shared by reducible and irreducible quotients; no MBE or field claim |
| Generic reduced-polynomial carrier | Remainder fixed points, named by `poly-reduced-p` | Transparent binary recognizer over a polynomial and modulus; `poly-remainder` is the corresponding fixer | Exact fixed-point equation, unconditional fixer closure, and—when the normalized modulus is nonzero—equivalence with canonicality plus the strict degree bound; reduced zero, reduced one, and all four reduced operations are closed | Guard `T` explicitly verified; no logical/executable split | Existing generic and concrete remainder boundary regressions cover total zero, constant, non-monic, malformed, and noncanonical inputs | 1 — generic recognizer/fixer basis only; no fixed-modulus quotient-field instance, cardinality claim, or concrete specialization |
| Generic fixed-modulus field | Canonical remainder fixed points modulo one constrained nullary irreducible polynomial | Nine ordinary total `fixed-modulus-field-*` DEFUNs; inverse fixes first, returns reduced zero for fixed zero, and otherwise calls the existing modular inverse | Complete GFIELD-shaped fixer, closure, ring, and inverse contract, including the arbitrary-input nonzero inverse law | Guard `T`; logical and executable definitions are identical | F7 simultaneous-functional-instantiation regression plus exact `nil`, `(1)`, `(3)`, `(8 1)`, atomic, and improper-list checks in `generic/fixed-modulus-field-f7-regression.lisp` | 1/2 — transparent generic interface and concrete regression only; no public F7 quotient API, performance/complexity claim, finiteness, or reducible quotient-ring claim |
| Generic reduced representative arithmetic | Four transparent wrappers, each exactly one public `poly-add`/`poly-neg`/`poly-sub`/`poly-mul` call followed by `poly-remainder` | `poly-reduced-add`, `poly-reduced-neg`, `poly-reduced-sub`, and `poly-reduced-mul`; ordinary nonrecursive DEFUNs | Canonicality, normalization and reduction fixed points, all-input normalization invariance, exact zero/one/nonzero-constant behavior, strict positive-degree bounds, and unconditional representative invariance from the existing remainder arithmetic laws | All four wrappers explicitly verified after their public operation and remainder dependencies | Exact F7 executions in `generic/f7-reduced-arithmetic.lisp`, including reduction, boundaries, malformed/noncanonical inputs, idempotence, and bounds | 1/2 — generic and concrete representative runtimes; no MBE, quotient object, ring-law package, irreducibility, or field claim |
| Concrete F7 reduced-ring instance generator | `def-reduced-ring-instance` expands to the five existing operation/remainder wrappers and independently selected functional-instance theorems | The unchanged `f7-poly-reduced-add`, `f7-poly-reduced-neg`, `f7-poly-reduced-sub`, `f7-poly-reduced-mul`, and `f7-poly-reduced-one` ordinary DEFUNs | Existing ring selections; canonical-output, normalization, and remainder fixed points for all five operations; non-rewriting fixed-modulus operand-by-remainder independence for add, neg, sub, and mul; and non-rewriting full pairwise congruence for those four operations, each transported from its named generic theorem through the complete explicit 43-pair concrete substitution | All five generated functions retain explicit `VERIFY-GUARDS` events and guard `T`; the unchanged `f7-poly-congruent-p` DEFUN and `VERIFY-GUARDS` event were only relocated before the generator so generated theorem statements can name it | Explicit-instance regressions assume congruence and vary both binary representative pairs across malformed, dotted, noncanonical, trailing-zero, coefficient-fixing, zero/constant/atomic/improper moduli, and genuine multiplication-reduction cases in `generic/f7-reduced-arithmetic.lisp` | 2 — transparent source generation only; predicate relocation changes no executable body or semantics, executable boundary, logical/executable split, alternate implementation, fixed-modulus operation, or F7X2 bridge |
| Polynomial quotient equality | Equality of the two canonical `poly-remainder` results | Existing `poly-congruent-p`; ordinary total predicate, plus the directly analogous concrete `f7-poly-congruent-p` execution spelling | Exact defining equation, equivalence laws, normalization/remainder invariance, fixed-representative equality, total modulus cases, and literal-result compatibility of all four reduced operations | Guard `T`; no logical/executable split or separate guard theorem is needed | Exact F7 remainder, equality, malformed/dotted, modulus-boundary, reducible/irreducible-looking, and reduced-operation compatibility regressions in `generic/f7-reduced-arithmetic.lisp` | 1/2 — computational equality of representatives, not an ACL2 quotient object or irreducibility-dependent field equality |
| Reduced multiplicative identity | One `poly-remainder` call on `polynomial-one` | `poly-reduced-one`; ordinary total DEFUN | Defining equation, canonicality, normalization, remainder fixed point, and exact zero/one/nonzero-constant/positive-degree modulus laws | `polynomial-one` and `poly-reduced-one` guards explicitly verified | Exact generic and F7 total-modulus executions | 1/1 — transparent representative boundary; no MBE, alternate reducer, quotient object, or field claim |
| Generic raw Euclidean computation | Transparent recursive `poly-euclidean-gcd` | Same ordinary DEFUN; no concrete instance or API | Controlled zero/nonzero equations, canonicality, and result-normalization | Default guard `T`, verified during DEFUN admission | Focused constant-first structural regressions in `generic/euclidean.lisp` | 1 — abstract ordinary definition; no MBE split and no algebraic gcd claim |
| Concrete F7 raw Euclidean GCD | Same transparent Euclidean recursion specialized to F7 | `f7-poly-euclidean-gcd`, an ordinary DEFUN using `f7-poly-remainder` | Direct functional instance of `poly-euclidean-gcd-raw-correct`, with raw divisibility corollaries | Complete call chain and the raw function explicitly guard-verified | Exact common-factor, coprime, division, reversed-order, zero, constant, associate, noncanonical, malformed, dotted, and multi-step assertions in `generic/f7-division.lisp` | 2 — ordinary concrete runtime; no MBE split; its representative remains order-sensitive |
| Concrete F7 monic Euclidean wrapper | Transparent nonrecursive post-processing, exactly `f7-poly-monic-normalize` of the retained raw result | `f7-poly-monic-euclidean-gcd`, an ordinary DEFUN which calls the raw runtime once and performs no division | Structural functional instances plus common-divisor correctness transported from the certified raw package through the two existing monic-normalization divisibility equivalences | Wrapper and complete component call chain explicitly guard-verified | Exact-value regressions cover both input orders, coprime/dividing/multistep cases, zeroes, constants, scalar associates, trailing zeroes, noncanonical coefficients, atoms, and dotted lists; raw order sensitivity becomes monic agreement | 2 — ordinary concrete runtime; no recursion, MBE split, attachment, or alternate division path |
| Concrete F7 raw XGCD | Transparent specialization of the generic extended-Euclidean recursion; one existing `f7-poly-divmod` call per nonzero step | `f7-poly-extended-euclidean-gcd`, an ordinary recursive DEFUN returning `(mv g s t)` | Direct functional instances prove exact equality of `g` with `f7-poly-euclidean-gcd`, canonicality of all projections, and unconditional raw Bezout | Recursive function and its complete existing division/operation call chain are guard-verified | Exact triples and both products are certified for common-factor/reversed, coprime, dividing, multi-step, zero, constant, associate, trailing-zero, noncanonical, atomic, and dotted inputs | 2 — ordinary concrete runtime; no MBE, DEFEXEC, attachment, monic scaling, or alternate division path |
| Concrete F7 monic XGCD | Transparent nonrecursive post-processing: one retained raw XGCD call, then leading coefficient/inverse, monic normalization, and scaling of both coefficients | `f7-poly-monic-extended-euclidean-gcd`, an ordinary DEFUND returning `(mv g s t)` | Exact monic-GCD projection, canonical/normalized projections, leading-coefficient characterization, and unconditional scaled Bezout | Wrapper and complete raw-XGCD/leading-coefficient/inverse/normalization/scale call chain explicitly guard-verified | Exact triples, scale units, products, sums, projections, malformed inputs, both orders, and zero behavior in `generic/f7-division.lisp` | 2 — ordinary concrete runtime; no recursion, second Euclidean traversal, division outside raw XGCD, MBE, DEFEXEC, or attachment |
| Concrete F7 polynomial modular inverse | Transparent nonrecursive specialization of the generic candidate: one concrete monic XGCD followed by the retained F7 remainder projection | `f7-poly-modular-inverse`, an ordinary guard-verified DEFUND returning one canonical polynomial | Full generic modular-inverse substitution; conditional product-remainder correctness under monic-GCD one and literal-one specialization for positive-degree modulus | Wrapper, monic XGCD, raw XGCD, divmod, and final remainder chain are guard-verified | Exact unit, constant, multistep, non-unit, zero, constant-modulus, associate, noncanonical, atom, and dotted executions in `generic/f7-division.lisp` | 2 — ordinary concrete runtime; no MBE, search, exponentiation, second GCD/XGCD, or alternate division path |
| F7X2 total executable inverse candidate | Fix the arbitrary input once; return `F7X2-ZERO` explicitly when that fixed value is zero; otherwise make one call to the existing concrete F7 polynomial modular inverse at `(1 0 1)` | `f7x2-inv`, an ordinary guard-verified DEFUN; the nonzero result is returned directly without result-side fixing, remainder, normalization, or other reduction | A proof-only simultaneous functional-instantiation regression now certifies compatibility of the unchanged F7X2 operations with the generic irreducible fixed-modulus-field interface, including the nonzero left-inverse theorem `F7X2-FIXED-MODULUS-FIELD-REGRESSION-MUL-INVERSE-LEFT`; promotion under ordinary public F7X2 inverse theorem names, possible replacement or refactoring of bespoke proof provenance, and formal GFIELD client packaging remain open | Guard `T` is explicitly verified over the already guard-verified fixer and concrete modular inverse | Non-rewriting exact ground executions cover zero, `1`, `3`, `x`, `1+x`, trailing-zero, coefficient-fixed, and malformed-tail inputs in `generic/f7x2-inverse.lisp`; these establish execution only | 2 — ordinary concrete executable definition; no MBE, DEFEXEC, attachment, GCD test, second reduction, field claim, or alternate inverse path |
| Generic monic Euclidean wrapper | Transparent nonrecursive `poly-monic-euclidean-gcd`, exactly `poly-monic-normalize` of the raw result | Same ordinary DEFUND; no second algorithm or concrete gcd API | Public equation and structural laws; certified common-divisor correctness and greatestness transported from raw gcd through unconditional monic-normalization divisibility equivalences | Default guard `T` from total component functions; no separate guard event | Focused constant-first generic boundary and correctness regressions preserve the visible raw negative-unit representative, cover total malformed/noncanonical shapes, and exercise both public correctness directions | 1 — transparent generic boundary; no MBE split and no concrete PFIELD/F7 gcd API |
| Generic polynomial divisibility | Canonical-zero test on `poly-remainder` | `poly-divides-p`, a transparent ordinary nonrecursive DEFUN with divisor-first order | Boolean and zero-remainder characterizations, congruence-to-zero equivalence, normalization/boundary/closure laws, and unconditional Euclidean-step common-divisor invariance | Guard `T`, verified during DEFUN admission; no separate guard event is needed | Focused constant-first structural regressions in `generic/euclidean.lisp`, including malformed and normalized-zero cases | 1 — no logical/executable split, witness choice, attachment, or concrete API |
| Concrete F7 coefficient inverse/division | Total prime-field semantics; inverse of fixed zero is zero | Ordinary `f7-inv` / `f7-div` DEFUNs | `f7-inv-logical-definition`; left/right inverse cancellation | Both guards explicitly verified on `T` | Zero, noncanonical-zero, malformed atom, and dotted-object assertions in `tests/pfield-adapter.lisp` | 2 — ordinary concrete executable definitions; coefficient prerequisite closed |
| Concrete F7 one-step polynomial division | Transparent generated four-DEFUN one-step interface | `f7-poly-division-step-core`, public normalized wrapper, term and next accessors | Certified term/product cancellation, canonical next state, strict degree/length decrease, and reconstruction theorem group | All four guards explicitly verified on `T` | Exact applicable, fixing, trailing-zero, malformed/dotted, inactive, constant-divisor, and zero-divisor regressions | 2 — complete one-step prerequisite; recursive divmod is inventoried separately |
| F11 polynomial degree / leading coefficient | Same transparent two-DEFUN template | `f11-poly-degree`; `f11-poly-leading-coefficient` | Identical normalized structural equations | Explicitly verified | `books/curve/f11-golden.lisp` cubic assertions | 2 — golden concrete runtime; no MBE split |
| Named F11 golden field | PFIELD adapter specialized at modulus 11 | `f11-element-p`, `f11-fix`, `f11-zero`, `f11-one`, `f11-add`, `f11-mul`, `f11-neg` | PFIELD adapter laws and functional instantiation; primality of 11 is concrete | Every named DEFUN explicitly verified | `books/curve/f11-golden.lisp` | 2 — ordinary concrete named runtime code; no split |
| F11 golden polynomial and curve fixture | `def-normalize-eval-instance` ordinary DEFUN template | Four generated polynomial functions, fixed cubic helpers, and bounded enumerators | Generic normalization/evaluation semantics transported through PFIELD; curve data and nonsingularity are concrete computations | Every runtime DEFUN explicitly verified | `books/curve/f11-golden.lisp` | 2 — transparent ordinary DEFUNs; no MBE split |
| Generic/F11 short-Weierstrass parameter boundary | Ordinary transparent DEFUNs over the existing fixed field operations | Fixed-at-use parameters, cubic RHS, coordinate equality, and discriminant expression | Generic constrained nonzero expression certificate; focused F11 golden arithmetic validation | Every new executable DEFUN explicitly verified | `books/curve/short-weierstrass.lisp`; `books/curve/f11-short-weierstrass.lisp` | 2 — no new MBE, DEFEXEC, attachment, or alternate execution path |
| Generic/F11 finite affine-coordinate boundary | Ordinary transparent DEFUNs over the field fixer and existing curve equation | Canonical two-list constructor, total accessors, representation fixer/predicate, and separate equation recognizer | Generic canonicality, idempotence, accessor closure/agreement, and recognizer/fixer invariance; focused F11 executions | Every executable DEFUN explicitly verified with guard `T` | `books/curve/affine-coordinates.lisp`; `books/curve/f11-affine-coordinates.lisp` | 2 — transparent representation only; no logical/executable split or alternate path |
| Generic/F11 tagged full-point boundary | Ordinary transparent DEFUNs over the affine boundary | Explicit infinity and affine constructors, total affine accessor, structural fixer/predicate, and separate curve recognizer | Generic canonicality, idempotence, branch and membership interface; focused F11 executions | Every executable DEFUN explicitly verified with guard `T` | `books/curve/points.lisp`; `books/curve/f11-points.lisp` | 2 — transparent representation only; no logical/executable split, operation, or alternate path |
| Generated PFIELD/F7 polynomial powers | `pfield-poly-pow-spec`; `f7-poly-pow-spec` | `pfield-poly-pow-fast` / `f7-poly-pow-fast`, selected by the corresponding public MBE wrapper | `pfield-poly-pow-fast-accumulator-invariant`, `pfield-poly-pow-fast-correct`; `f7-poly-pow-fast-accumulator-invariant`, `f7-poly-pow-fast-correct` | Both dependency chains, fast auxiliaries, and public wrappers explicitly verified | `tests/generic-polynomial.lisp` (concrete F7 only) | 4 — PFIELD constrained adapter and F7 named concrete runtime; closed |
| PFIELD root counting | Imported root predicate/count specification | Executable finite enumeration in the certified PFIELD book | Conversion theorems and `hs-pfield-polynomial-num-roots-upper-bound` | Dependency-book status; no project MBE boundary | Root-count bridge tests | 4 — executable enumeration with certified semantic bridge |

## Full-point negation

`curve-point-neg` and its F11 client are ordinary transparent, guard-verified
definitions, not a logical/executable split.  Infinity is fixed, affine y uses
existing field negation, and arbitrary inputs use the existing point fixer.
F11 regressions cover canonical, noncanonical, off-curve, infinity, and
malformed inputs; generic certified theorems separately establish structural
and curve-membership closure and involution modulo fixing.

## Generated field-power correspondence

`books/field/power-correspondence.lisp` adds a logical comparison boundary for
public powers generated by `DEF-POW-INSTANCE`.  Its uniqueness theorem uses
only the public total equations for `NFIX`, zero, and successor.  Generated
public powers retain their existing `MBE` logical-specification/fast-accumulator
execution boundary unchanged; the theorem adds no executable branch.  F7 and a
regression-local modulus-11 instance certify that clients can map the public
power without mapping either recursive specifications or fast accumulators.
`books/field/frobenius-exponent.lisp` adds only a logical constrained
positive-exponent/fixed-point certificate over that comparison function. It
adds no executable branch and changes no generated implementation, guard, or
MBE boundary. F7 and the regression-local modulus-11 power instantiate it.

## Named generated polynomial-power expansions

| Instance | Specification | Fast auxiliary | Public wrapper | Accumulator invariant | Fast/spec theorem | Fast guards | Public guards | Runtime classification |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| PFIELD polynomial | `pfield-poly-pow-spec` | `pfield-poly-pow-fast` | `pfield-poly-pow` | `pfield-poly-pow-fast-accumulator-invariant` | `pfield-poly-pow-fast-correct` | Verified | Verified using the fast/spec theorem | Constrained-modulus adapter; not a named concrete field runtime |
| F7 polynomial | `f7-poly-pow-spec` | `f7-poly-pow-fast` | `f7-poly-pow` | `f7-poly-pow-fast-accumulator-invariant` | `f7-poly-pow-fast-correct` | Verified | Verified using the fast/spec theorem | Named concrete executable runtime |

Macro-expansion inspection confirms that each public executable branch calls
only its corresponding fast auxiliary after one base normalization and one
`NFIX`.  No specification call occurs in either executable branch.  Positive
fast recursion passes `(floor n 2)`, and squares and accumulator updates call
the existing canonical polynomial multiplication directly, without a redundant
post-multiplication normalization.

## Named concrete field-power expansions

| Instance | Specification | Fast auxiliary | Public wrapper | Accumulator invariant | Fast/spec theorem | Fast guards | Public guards |
| --- | --- | --- | --- | --- | --- | --- | --- |
| F2 | `f2-pow-spec` | `f2-pow-fast` | `f2-pow` | `f2-pow-fast-accumulator-invariant` | `f2-pow-fast-correct` | Verified | Verified using `f2-pow-fast-correct` |
| F7 | `f7-pow-spec` | `f7-pow-fast` | `f7-pow` | `f7-pow-fast-accumulator-invariant` | `f7-pow-fast-correct` | Verified | Verified using `f7-pow-fast-correct` |

Inspection of both macro expansions confirms the same execution shape. Each
public executable branch fixes its base once, applies `NFIX` once, and calls
only its corresponding fast auxiliary. It contains no specification call. Each
positive fast recursion replaces the exponent by `(floor n 2)`. Thus negative
public exponents retain the established `NFIX`-to-zero meaning, including
`0^0 = 1`, while compiled execution remains logarithmic in the fixed natural
exponent.

## Repository-wide form audit (ACL2 8.6)

All project `*.lisp` and executable certification-prelude `*.acl2` files were
searched. The only logical/executable split is the `MBE` emitted by
`DEF-POW-INSTANCE`; its expansions are field, PFIELD, F2, GPOLY, and PFIELD/F7
polynomial power. The two `:verify-guards nil` occurrences are inside that
macro and are classification 3 (intentional staging). Explicit `VERIFY-GUARDS`
occurs for `field-pow-fast`, `field-pow`, the PFIELD, F2, and F7 field-power
boundaries and their direct callees, the twelve GPOLY functions in `generic/power.lisp`, the generic and F7
monomial/shift functions, all four generic one-step division functions and
their arithmetic dependencies, and both generic recursive divmod functions;
those occurrences are classifications 1/2/3/4 as inventoried above.

The two `ENCAPSULATE` events (GFIELD operations and the PFIELD modulus) are
classification 1. There are no project occurrences of `DEFEXEC`, `DEFATTACH`
or its ACL2 8.6 variants, program-mode definitions or mode changes, raw-mode or
raw-inclusion facilities, `EC-CALL`, skipped proofs, axioms, or trust tags.
Concrete F2/F7 and explicit-modulus HS definitions are classification 2.
PFIELD-named adapters and generated PFIELD polynomial definitions still depend
on the constrained modulus and are not claimed as concrete runtime code.

The audit found no arithmetic defect. The named F2 and F7 field-power boundaries
are closed by direct specialized accumulator inductions, certified fast/spec
equalities, explicit guard verification, and focused execution regressions.
These proofs follow the PFIELD pattern and avoid mapping recursive power
functions because doing so generates definitional-equation compatibility
obligations with one-sided unfolding. The generated PFIELD and F7
polynomial-power gaps are now closed by direct specialized accumulator inductions, fast/spec theorems, explicit dependency
and boundary guard verification, and focused concrete F7 regressions.

## Scanner policy

The scanner deliberately treats matches in comments and strings as failures.
ACL2 8.6 source confirms these prohibited facility spellings:

* `SKIP-PROOFS` and `SET-LD-SKIP-PROOFSP` bypass proof obligations;
* `DEFAXIOM` adds an unproved logical axiom;
* `DEFTTAG` enables trust-tagged extensions;
* `SET-RAW-MODE`, its `-ON`, `-OFF`, and `-ON!` variants, `PROGN!`, and
  `INCLUDE-RAW` expose raw Lisp evaluation or inclusion; and
* `DEFATTACH`, `DEFATTACH!`, and `DEFATTACH-SYSTEM` install executable
  attachments hidden from ordinary logical definitions.

Ordinary sound facilities (`MBE`, `DEFEXEC`, `VERIFY-GUARDS`, `ENCAPSULATE`,
and functional instantiation) are not prohibited. They trigger the review and
evidence requirements instead.


## F7 division instantiation boundary

The original coefficient-level blocker is resolved. `F7-INV` now fixes its
argument once and branches explicitly at zero before calling the guarded
`PFIELD::INV`.  Its certified logical-definition theorem proves that this is
exactly the previous total value, including inverse-of-zero equal to zero;
malformed objects are fixed to zero.  `F7-INV` and `F7-DIV` now have verified
guards on guard `T`.

The concrete one-step definition and semantic theorem layer are retained, and
`F7-POLY-DIVISION-STEP-CORE-LENGTH-DECREASES` admits the generated ordinary
recursive `F7-POLY-DIVMOD`. Its quotient and remainder operations are transparent
projections. The generic public interface is functionally instantiated for
canonicality, reconstruction, and the conditional strict remainder bound;
guard verification remains separate execution assurance. Concrete F7 GCD,
F7 polynomial modular inverse, quotient/extension fields, curves, and Schoof remain open.
# F7X2 canonical representative fixer

# F7X2 transparent reduced arithmetic

`F7X2-ADD`, `F7X2-NEG`, `F7X2-SUB`, and `F7X2-MUL` are ordinary transparent DEFUNs.  Each calls the corresponding existing concrete F7 polynomial operation and immediately post-processes through `F7X2-FIX`, so total ACL2-object semantics inherit atomic and malformed-tail handling, dotted-list truncation, F7 coefficient fixing, trailing-zero normalization, arbitrary-degree reduction modulo `(1 0 1)`, and canonical equality through the fixer.  Public rewrite theorems certify that an `F7X2-FIX` wrapped around any individual operand can be removed, so operating before fixing has the same total interpretation as operating on fixed representatives. Raw noncanonical inputs are accepted by the executable functions, but they are not carrier elements unless recognized by `F7X2-ELEMENT-P` or replaced by their fixed representatives.  No MBE, DEFEXEC, attachment, raw Lisp, inverse operation, field law package, or GFIELD instance is added.

`F7X2-FIX` is a transparent, nonrecursive composition of the existing concrete
`F7-POLY-REMAINDER` with the fixed modulus `(1 0 1)`.  Its logical and
executable definitions are identical; no `MBE`, attachment, or alternate
runtime is involved.  Atoms and malformed/dotted tails are discarded by the
existing polynomial normalization, coefficients are fixed modulo 7, trailing
zeroes are trimmed, and polynomials of arbitrary degree are reduced modulo
`x^2+1`.  Thus zero and modulus multiples fix to `nil`, constants retain their
canonical singleton form, and already canonical degree-below-two lists are
fixed points.  The certified regressions cover atoms, dotted lists, coefficient
fixing, trailing zeroes, the modulus, and `x^3 = 6x`.  These checks establish
the intended execution path; the certified fixed-point, normalization, and
degree theorems establish the representation invariant.  No complexity claim
is made beyond reuse of the existing division runtime.

## Affine-pair classifier

`affine-pair-classify` and the focused `f11-affine-pair-classify` client are
ordinary transparent, total `DEFUN`s with verified guards. They fix both affine
inputs and perform canonical equality and the existing field negation only.
They introduce no `MBE`, `DEFEXEC`, attachment, raw Lisp, fast path, or
logical/executable split; therefore this is not a new split execution boundary.
Concrete F11 assertions are execution regressions, while the generic
characterization, result-recognition, fixing, exhaustiveness, and disjointness
theorems provide the logical evidence.
