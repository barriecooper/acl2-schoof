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
merely for symmetry.  No mathematical milestone is implied by this definition
refactoring; the smallest next mathematical PR is the first generic scaling
definition and its evaluation theorem, without yet adding multiplication.
