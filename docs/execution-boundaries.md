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
| Generated PFIELD/F7 polynomial powers | Named generated `*-poly-pow-spec` | Named generated fast functions selected by MBE | No instance-specific certified accumulator/equivalence theorem; concrete equalities are regressions only | Staged but not later explicitly verified | F7 polynomial-power tests | 7 — unresolved execution-correctness assurance; follow-up required |
| PFIELD root counting | Imported root predicate/count specification | Executable finite enumeration in the certified PFIELD book | Conversion theorems and `hs-pfield-polynomial-num-roots-upper-bound` | Dependency-book status; no project MBE boundary | Root-count bridge tests | 4 — executable enumeration with certified semantic bridge |

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
boundaries and their direct callees, and the twelve GPOLY functions in `generic/power.lisp`;
those occurrences are classifications 3/4.

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
obligations with one-sided unfolding. The remaining power gap is deliberately
limited to generated PFIELD/F7 polynomial powers (and any other generated
polynomial-power instance): their concrete equalities are regressions, not
instance-specific certified bridges, and their staged guards remain open.

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
