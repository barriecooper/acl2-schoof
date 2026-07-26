# Executable polynomial instantiation decision

## Decision

Use the project-local `def-normalize-eval-instance` macro as the minimal
proof-of-concept.  It expands transparently to four predictably named ordinary
`DEFUN` events.  Both the generic theory and F_7 invoke the same templates, so
the normalization and evaluation recurrences have one source.  Correctness is
transported with ACL2's sound `:functional-instance` rule; execution needs no
attachment or mutable state.

The Community Books facilities inspected were:

* `books/kestrel/soft/{top,defun-inst,defthm-inst}.lisp` (SOFT);
* `books/make-event/defspec.lisp` (`defspec`/`definstance`);
* `books/tools/def-functional-instance.lisp`;
* `books/kestrel/apt/{top,copy-function,rename-calls}.lisp`; and
* ACL2's standard `defmacro`, `progn`, and functional-instantiation events.

Handwritten copies are transparent and light but provide no definition reuse.
SOFT provides excellent function and theorem instantiation, including guard
inheritance, but would require converting the established GFIELD interface and
generic functions to SOFT function variables.  `defspec`/`definstance` checks
constraints but does not generate executable algorithm definitions.
`def-functional-instance` generates theorem instances only.  APT can transform
definitions, but its dependency and transformation machinery are excessive for
four small definitions.  The local macro therefore has the lowest dependency
weight, obvious expansions, ordinary guard verification, and straightforward
debugging.  Its explicit operation arguments also scale to multiplication and
extension-field instances without committing this project to a framework.

The same policy now covers the deliberately narrow
`def-reduced-ring-instance` macro.  Its explicit `NORMALIZE` argument is
theorem-generation metadata and does not alter an executable body.  Its F7
invocation regenerates the five
existing variable-modulus reduced-operation DEFUNs, explicitly verifies their
unchanged guards, and independently selects addition commutativity, addition
associativity, the two addition identity laws, the two additive-inverse laws, the two core reduced-negation laws
(double negation and negation of zero), the three non-expansive subtraction
identities, a public subtraction-as-addition-plus-negation semantic bridge, and
right distributivity, the five independent normalization fixed points, and the five independent
remainder-stability rules for reduced addition, negation, subtraction,
multiplication, and one, the four operand-by-remainder independence theorems,
and four independent fixed-modulus pairwise-congruence theorems for addition,
negation, subtraction, and multiplication.  The congruence interface is
`F7-POLY-REDUCED-{ADD,NEG,SUB,MUL}-RESPECTS-POLY-CONGRUENT-P`; each theorem
concludes literal equality of reduced outputs from the corresponding
`F7-POLY-CONGRUENT-P` hypotheses.  The complete F7 functional substitution has
43 pairs, including the explicit `POLY-CONGRUENT-P` mapping.  The subtraction
bridge and the congruence theorems are deliberately `:rule-classes nil`: general
subtraction remains the preferred visible form, the three identities remain the
active simplifiers, and this matches the existing F7X2 presentation policy.  For
every supported selection the
caller supplies the public name, generic source, and rule classes, together with
the complete common functional substitution and narrow common and
theorem-specific hints.  There is no compulsory all-theorems mode; the rest of
the F7 reduced-ring laws remain open, including general fixer/remainder
compatibility, modulus-representative independence, degree-bound
specializations, and the remaining ring and field laws.
The public F7 remainder-stability interface is
`F7-POLY-REMAINDER-OF-POLY-REDUCED-{ADD,NEG,SUB,MUL,ONE}`; all five
rules are unconditional over arbitrary operands and total modulus cases.  These selected laws do not constitute a complete additive interface.

## Logical and executable boundary

The GFIELD-based `fix-coefficients`, `trim-trailing-zeros`, `normalize`, and
`eval` form the logical generic theory.  Because GFIELD operations are
constrained, direct generic execution is not required.  The PFIELD adapter now
generates the same four definitions at its exact-arity, constrained-modulus
boundary.  The generated
`f7-fix-coefficients`, `f7-trim-trailing-zeros`, `f7-normalize`, and `f7-eval`
are ordinary executable functions with verified default guards.  The theorem
`f7-normalize-preserves-eval-from-generic` transports the generic semantic
result through the already-certified PFIELD/F_7 field instance.  Values remain
canonical representatives and all statements use ordinary `EQUAL` after
fixing.

Runtime-parameterized implementations may remain useful utilities, but a
logical field instance uses fixed-arity wrappers for its modulus and operations
so that functional substitution preserves arities.  Each intended executable
instance must supply ordinary `DEFUN`s at that boundary and certified bridges.

Future computational layers are incomplete until they have all three:

1. an abstract theory;
2. ordinary executable concrete functions; and
3. certified correctness bridges between them.

More specifically, a public operation that separates logical and executable
implementations with `MBE`, `DEFEXEC`, an attachment, or another mechanism
normally lands together with named specification and implementation functions,
a certified invariant/equivalence theorem, verified guards for the executable
branch, focused concrete execution regressions, and documentation that keeps
logical correctness, guard/execution assurance, and performance/complexity
evidence distinct. Guard verification establishes guard obligations; it does
**not** establish that the executable algorithm implements the logical
specification. That fact must already follow from the certified bridge.
Likewise, an execution regression is evidence that the intended branch runs
and behaves practically, not a substitute for equivalence.

The additive migration is also complete.  Generic addition, negation, and
subtraction, the existing PFIELD addition adapter, and concrete F_7 addition,
negation, and subtraction now use two small shared templates.  Keeping the
addition template separate avoids inventing PFIELD negation/subtraction APIs
merely for symmetry.  That migration now includes scaling, multiplication, monomial/shift, and
generic division templates. The next mathematical PR should begin generic
modular reduction and congruence, not duplicate algorithms in HS/PFIELD.


## Current concrete-division guard decision

A generated F7 one-step experiment certified its complete semantic theorem
group, using the retained F7 monomial, ordered-product, subtraction-decrease,
normalized-addition, and reconstruction support. It was not retained because
explicit guard verification did not complete: `F7-INV` calls `PFIELD::INV` on
`F7-FIX x`, `F7-DIV` depends on `F7-INV`, and `VERIFY-GUARDS F7-INV` generated
obligations requiring an arbitrary integer input to be nonzero modulo 7. This
is an open field-interface/guard-contract decision. Verified guards would show
execution admissibility, not semantic correctness; conversely, the experimental
semantic certifications do not create an executable boundary. Neither guard nor
executable definition is changed here.
