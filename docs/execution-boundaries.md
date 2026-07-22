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
| Generated F2/F7 field powers | Named generated `*-pow-spec` | Named generated `*-pow-fast`, selected by `*-pow` MBE | No instance-specific certified accumulator/equivalence theorem | Staged but not later explicitly verified | F2/F7 concrete power tests | 7 — unresolved execution-correctness assurance; follow-up required |
| Polynomial power (`poly-pow`) | `poly-pow-spec` | `poly-pow-fast`, selected by `poly-pow` MBE | `poly-pow-fast-accumulator-invariant`; `poly-pow-fast-correct`; `eval-of-poly-pow` | Staged, then explicitly verified | Concrete F7 polynomial-power tests | 4 — justified logical/executable boundary |
| PFIELD/F7 generated polynomial instances (non-power) | Shared templates | PFIELD is constrained-modulus; F7 is concrete | Operation-specific transported theorems | Ordinary/default guards | F7 operation tests | 2 — same DEFUN templates; no MBE split |
| Generated PFIELD/F7 polynomial powers | Named generated `*-poly-pow-spec` | Named generated fast functions selected by MBE | No instance-specific certified accumulator/equivalence theorem; concrete equalities are regressions only | Staged but not later explicitly verified | F7 polynomial-power tests | 7 — unresolved execution-correctness assurance; follow-up required |
| PFIELD root counting | Imported root predicate/count specification | Executable finite enumeration in the certified PFIELD book | Conversion theorems and `hs-pfield-polynomial-num-roots-upper-bound` | Dependency-book status; no project MBE boundary | Root-count bridge tests | 4 — executable enumeration with certified semantic bridge |

## Repository-wide form audit (ACL2 8.6)

All project `*.lisp` and executable certification-prelude `*.acl2` files were
searched. The only logical/executable split is the `MBE` emitted by
`DEF-POW-INSTANCE`; its expansions are field, PFIELD, F2, GPOLY, and PFIELD/F7
polynomial power. The two `:verify-guards nil` occurrences are inside that
macro and are classification 3 (intentional staging). Explicit `VERIFY-GUARDS`
occurs for `field-pow-fast`, `field-pow`, the PFIELD power boundary and its
three direct callees, and the twelve GPOLY functions in `generic/power.lisp`;
those occurrences are classifications 3/4.

The two `ENCAPSULATE` events (GFIELD operations and the PFIELD modulus) are
classification 1. There are no project occurrences of `DEFEXEC`, `DEFATTACH`
or its ACL2 8.6 variants, program-mode definitions or mode changes, raw-mode or
raw-inclusion facilities, `EC-CALL`, skipped proofs, axioms, or trust tags.
Concrete F2/F7 and explicit-modulus HS definitions are classification 2.
PFIELD-named adapters and generated PFIELD polynomial definitions still depend
on the constrained modulus and are not claimed as concrete runtime code.

The audit found no arithmetic defect. It found one logical/executable assurance
gap for a separate small PR: generated F2/F7 field powers and PFIELD/F7
polynomial powers have concrete regressions, but do not have instance-specific
certified accumulator/equivalence theorems and do not later complete the guard
verification staged by the generator. The generic GFIELD and GPOLY invariants
show the required proof pattern but do not by themselves certify each generated
MBE boundary. A follow-up should functionally instantiate or prove those small
bridges, explicitly verify guards, and retain focused regressions without
changing the definitions or weakening theorem statements. Until then, claims
about those generated concrete powers are execution observations, not certified
semantic-correctness claims.  The PFIELD field-power boundary is no longer part
of that gap: its direct accumulator induction uses the generic natural low-bit
split, keeps `pfield-mul-commutative` disabled, and supports explicit guard
verification.  Direct specialization was chosen because replacing the two
recursive generic functions generated additional definitional-equation
obligations; uncontrolled unfolding reduced only one recursive side and turned
transport into separate recursive-equivalence proofs.

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
