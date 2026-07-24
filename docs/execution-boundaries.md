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
| Concrete F2/F7 operations except power | Same ordinary DEFUN bodies | Named `f2-*` / `f7-*` DEFUNs | GFIELD functional instances | Default guards | Concrete field tests | 2 — ordinary concrete executable definition |
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
| Generic polynomial remainder | Remainder component of public `poly-divmod` | `poly-remainder`, an ordinary projection wrapper | Direct divmod connection, canonicality, normalization laws, zero fallback, strict degree bound, and idempotence | Wrapper guard explicitly verified after `poly-divmod` | Focused generic structural regressions in `generic/reduction.lisp` | 1 — abstract ordinary definition; no MBE or concrete runtime claim |
| Generic raw Euclidean computation | Transparent recursive `poly-euclidean-gcd` | Same ordinary DEFUN; no concrete instance or API | Controlled zero/nonzero equations, canonicality, and result-normalization | Default guard `T`, verified during DEFUN admission | Focused constant-first structural regressions in `generic/euclidean.lisp` | 1 — abstract ordinary definition; no MBE split and no algebraic gcd claim |
| Generic monic Euclidean wrapper | Transparent nonrecursive `poly-monic-euclidean-gcd`, exactly `poly-monic-normalize` of the raw result | Same ordinary DEFUND; no second algorithm or concrete gcd API | Public equation and structural laws; certified common-divisor correctness and greatestness transported from raw gcd through unconditional monic-normalization divisibility equivalences | Default guard `T` from total component functions; no separate guard event | Focused constant-first generic boundary and correctness regressions preserve the visible raw negative-unit representative, cover total malformed/noncanonical shapes, and exercise both public correctness directions | 1 — transparent generic boundary; no MBE split and no concrete PFIELD/F7 gcd API |
| Generic polynomial divisibility | Canonical-zero test on `poly-remainder` | `poly-divides-p`, a transparent ordinary nonrecursive DEFUN with divisor-first order | Boolean and zero-remainder characterizations, congruence-to-zero equivalence, normalization/boundary/closure laws, and unconditional Euclidean-step common-divisor invariance | Guard `T`, verified during DEFUN admission; no separate guard event is needed | Focused constant-first structural regressions in `generic/euclidean.lisp`, including malformed and normalized-zero cases | 1 — no logical/executable split, witness choice, attachment, or concrete API |
| Concrete F7 coefficient inverse/division | Total prime-field semantics; inverse of fixed zero is zero | Ordinary `f7-inv` / `f7-div` DEFUNs | `f7-inv-logical-definition`; left/right inverse cancellation | Both guards explicitly verified on `T` | Zero, noncanonical-zero, malformed atom, and dotted-object assertions in `tests/pfield-adapter.lisp` | 2 — ordinary concrete executable definitions; coefficient prerequisite closed |
| Concrete F7 one-step polynomial division | Transparent generated four-DEFUN one-step interface | `f7-poly-division-step-core`, public normalized wrapper, term and next accessors | Certified term/product cancellation, canonical next state, strict degree/length decrease, and reconstruction theorem group | All four guards explicitly verified on `T` | Exact applicable, fixing, trailing-zero, malformed/dotted, inactive, constant-divisor, and zero-divisor regressions | 2 — complete one-step prerequisite; recursive divmod remains open |
| F11 polynomial degree / leading coefficient | Same transparent two-DEFUN template | `f11-poly-degree`; `f11-poly-leading-coefficient` | Identical normalized structural equations | Explicitly verified | `books/curve/f11-golden.lisp` cubic assertions | 2 — golden concrete runtime; no MBE split |
| Named F11 golden field | PFIELD adapter specialized at modulus 11 | `f11-element-p`, `f11-fix`, `f11-zero`, `f11-one`, `f11-add`, `f11-mul`, `f11-neg` | PFIELD adapter laws and functional instantiation; primality of 11 is concrete | Every named DEFUN explicitly verified | `books/curve/f11-golden.lisp` | 2 — ordinary concrete named runtime code; no split |
| F11 golden polynomial and curve fixture | `def-normalize-eval-instance` ordinary DEFUN template | Four generated polynomial functions, fixed cubic helpers, and bounded enumerators | Generic normalization/evaluation semantics transported through PFIELD; curve data and nonsingularity are concrete computations | Every runtime DEFUN explicitly verified | `books/curve/f11-golden.lisp` | 2 — transparent ordinary DEFUNs; no MBE split |
| Generated PFIELD/F7 polynomial powers | `pfield-poly-pow-spec`; `f7-poly-pow-spec` | `pfield-poly-pow-fast` / `f7-poly-pow-fast`, selected by the corresponding public MBE wrapper | `pfield-poly-pow-fast-accumulator-invariant`, `pfield-poly-pow-fast-correct`; `f7-poly-pow-fast-accumulator-invariant`, `f7-poly-pow-fast-correct` | Both dependency chains, fast auxiliaries, and public wrappers explicitly verified | `tests/generic-polynomial.lisp` (concrete F7 only) | 4 — PFIELD constrained adapter and F7 named concrete runtime; closed |
| PFIELD root counting | Imported root predicate/count specification | Executable finite enumeration in the certified PFIELD book | Conversion theorems and `hs-pfield-polynomial-num-roots-upper-bound` | Dependency-book status; no project MBE boundary | Root-count bridge tests | 4 — executable enumeration with certified semantic bridge |

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

Concrete recursive division is still open and no F7 divmod API is inventoried
as present.  The concrete one-step definition and semantic theorem-instance layer
are now retained.  The direct recursive experiment had exposed the exact prerequisite: the functional instance of
`POLY-DIVISION-STEP-CORE-LENGTH-DECREASES` is now available as `F7-POLY-DIVISION-STEP-CORE-LENGTH-DECREASES`, supported by the retained concrete cancellation, canonical-next, degree-decrease, and reconstruction group. Recursive F7 divmod and its quotient/remainder projections remain deliberately open. Guard verification alone does not establish the certified semantic decrease.
