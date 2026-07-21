# Abstract-field polynomial bridge feasibility

## Result

This investigation targets ACL2 8.6 / Community Books commit
`7585056a0647c1ab8a45b1573c5cfe524acbda3f`, as checked by
`git -C .deps/acl2-8.6 rev-parse HEAD`.  Its conclusion is **not to connect HS
directly to the 2006 `FUNPOL` implementation**.  The mathematics is compatible,
but the 2006 books are an abstract theory whose executable definitions are
permanently wired to constrained `FLD` functions.  The Kestrel interface used
by HS passes its modulus explicitly.  ACL2 functional instantiation can
transport a theorem to same-arity replacement functions; it does not rewrite
the bodies of `FUNPOL::QUOT` and all of its mutually dependent operations into
a new executable library.  Doing that would require a generated/copying
instance of almost the complete development, including its long-division
definition, rather than a small conversion bridge.

This is a negative feasibility result, not a proof that quotient/remainder is
unavailable to HS.  No division implementation, axiom, skipped proof, trust
tag, raw Lisp, or uncertified include was added.

## Exact source inspection

The complete target chain was read locally, including both every book included
by `fuquot-rem.lisp` and its downstream consumer:

1. `workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/coe-fld.lisp`
2. `.../futermino.lisp`
3. `.../fumonomio.lisp`
4. `.../fupolinomio.lisp`
5. `.../fuforma-normal.lisp`
6. `.../fusuma.lisp`
7. `.../fucongruencias-suma.lisp`
8. `.../fuopuesto.lisp`
9. `.../fuproducto.lisp`
10. `.../fucongruencias-producto.lisp`
11. `.../fupolinomio-normalizado.lisp`
12. `.../fuquot-rem.lisp`
13. `workshops/2006/cowles-gamboa-euclid/Euclid/ed6a.lisp`, the only book in
    that workshop tree that includes `fuquot-rem`.

The concrete side was checked in
`kestrel/prime-fields/{fep,fep-fix,add,mul,neg,inv,prime-fields,
prime-fields-rules,prime-fields-alt,top}.lisp`, along with the HS books
`books/polynomial/{base,eval,degree,pfield-bridge}.lisp`.  A whole-Books search
for `coe-fld`, `FLD::Closure-Laws`, and functional instances found no concrete
instance of this `FLD` theory.  Thus there is no Community Books instantiation
pattern to adopt; `ed6a.lisp` merely reasons in the original abstract theory.

### Packages and abstract field

The chain uses five packages: `FLD`, `FUTER`, `FUMON`, `FUPOL`, and `FUNPOL`.
Their portcullises remove Common Lisp symbols such as `+`, `*`, `-`, `/`, and
`=` before defining package-local operations.

`coe-fld.lisp` introduces, in one `encapsulate`, these constrained symbols:

| Symbol | Arity | Meaning |
|---|---:|---|
| `FLD::FDP` | 1 | field-element recognizer |
| `FLD::+`, `FLD::*` | 2 | field operations |
| `FLD::-`, `FLD::/` | 1 | additive inverse and reciprocal |
| `FLD::0_F`, `FLD::1_F` | 0 | identities |
| `FLD::=` | 2 | coefficient equivalence |
| `FLD::C_=` | 1 | canonical equivalence-class representative |

The exported obligations are `BOOLEANP-FDP`, `CLOSURE-LAWS`,
`EQUIVALENCE-LAW`, `CONGRUENCE-LAWS`, `EQUIVALENCE-CLASS-LAWS`, `|0 != 1|`,
`COMMUTATIVITY-LAWS`, `ASSOCIATIVITY-LAWS`,
`LEFT-DISTRIBUTIVITY-LAW`, `LEFT-UNICITY-LAWS`, and
`RIGHT-INVERSE-LAWS`.  The local witnesses are ACL2 numbers with ordinary
arithmetic and equality.  Consequently the included executable functions call
those witnesses' constrained logical successors; an include does not select a
concrete field.

### Polynomial representation and operations

`FUTER` concretely represents an exponent by a natural number.  A `FUMON`
monomial is the dotted pair `(coefficient . exponent)`.  A raw `FUPOL`
polynomial is a proper list of monomials.  Normal form (`FUPOL::ORDENADOP`) has
strictly descending exponents and no zero monomial; `FUPOL::FN` sorts, combines
equal exponents, selects coefficient representatives with `FLD::C_=`, and
deletes zero coefficients.  `nil` is the unique normalized zero.  `FUPOL::=`
compares normal forms using coefficient equivalence, while `FUNPOL::=` is the
corresponding equality for normalized operations.

Thus conversion from HS would reverse the dense constant-first list, attach
descending natural exponents, and omit zero coefficients.  It preserves the
mathematical coefficient order but not list length: sparse FUNPOL deliberately
omits internal zeroes.  HS zero and FUNPOL zero are both `nil`.  On a nonzero
normalized FUNPOL polynomial, `FUNPOL::DEG` is the exponent of its first
monomial and `FUNPOL::LC` is its coefficient.  FUNPOL does not assign HS's
explicit `-1` degree sentinel to zero: `DEG` reaches the default term supplied
by its accessors, so the library states degree results only under nonzero
hypotheses.  No evaluator or polynomial fixing function is provided.  `FN` is
normalization, not evaluation.  Therefore an evaluation-preservation bridge
would first have to add and certify an evaluator on the sparse representation.

`FUNPOL::+`, `FUNPOL::-`, and `FUNPOL::*` normalize the corresponding `FUPOL`
operation.  `FUNPOL::QUOT` is the library's recursive long-division function;
`FUNPOL::REM` is defined as `p1 + -(p2 * quot(p1,p2))`.  This investigation did
not copy or wrap either function.

## Concrete PFIELD experiment and obstruction

The HS interface is parameterized:

* `PFIELD::FEP(x,p)` and `PFIELD::FEP-FIX(x,p)`;
* `PFIELD::ADD(x,y,p)` and `PFIELD::MUL(x,y,p)`;
* `PFIELD::NEG(x,p)` and `PFIELD::INV(x,p)`.

Its values are canonical natural representatives below `p`, so ordinary ACL2
`equal` is suitable after `FEP-FIX`; modular equivalence could alternatively be
used before fixing.  Under `primep(p)`, wrappers closed over a *nullary*
constrained prime could satisfy the FLD axioms and remain executable relative
to that constrained prime.  They cannot be ordinary functions closed over the
free theorem variable `p`: ACL2 functions do not form closures, and replacing
binary `FLD::+` with ternary `PFIELD::ADD` violates functional-instantiation
arity.

Community Books already demonstrates the only straightforward fixed-prime
shape in `kestrel/prime-fields/prime-fields-alt.lisp`: it constrains nullary
`PFIELD::PRIME` and defines unary/binary `FEP`, `ADD`, `MUL`, `NEG`, and `INV`.
But it reuses exactly the same package symbols as the explicit-modulus library
at incompatible arities.  `kestrel/prime-fields/top.lisp` explicitly comments
out `prime-fields-alt` as “incompatible”, and HS has already included the
explicit-modulus symbols.  The alternate book therefore cannot coexist in an
HS bridge world.

A fresh project-local fixed-prime wrapper package could avoid that name clash
and could prove all the FLD contracts.  That still only permits functional
instances of individual theorems.  `FUNPOL::QUOT-REM-REWRITE` contains calls to
`FUNPOL::REM`, `FUNPOL::*`, `FUNPOL::QUOT`, and `FUNPOL::+`; all those defined
functions ultimately contain the original `FLD` symbols.  A useful functional
instance must consequently substitute concrete copies for the whole reachable
definition graph.  ACL2 has no parameterized module/functor here and the
Community Books revision supplies no generated instance.  Maintaining that
copy would be more expensive and less auditable than proving the needed HS
algorithm directly, and copying `QUOT` would violate this task's prohibition on
a separate division implementation.

Including `fuquot-rem` itself succeeds and exposes
`FUNPOL::QUOT-REM-REWRITE`; it does not make the constrained operations equal
to PFIELD operations.  The attempted direct functional substitution is
rejected on the signature mismatch rather than creating a fixed modulus.
Temporary experiment books and their certificates are outside the commit.

## Exact quotient/remainder reuse boundary

The target facts are:

* `FUNPOL::POLINOMIOP-QUOT` and `FUNPOL::POLINOMIOP-REM`: quotient and remainder
  are normalized polynomials without input hypotheses.
* `FUNPOL::QUOT-REM-REWRITE`: if `FUNPOL::POLINOMIOP p1`, then
  `rem(p1,p2) + p2*quot(p1,p2) = p1` in `FUNPOL::=`.  Surprisingly, this final
  identity has no divisor-nonzero or divisor-well-formedness hypothesis.
* `FUNPOL::|deg rem(p1 p2) ACL2::< deg p2|`: if both inputs are normalized,
  the divisor and remainder are nonzero, then `deg(rem(p1,p2)) < deg(p2)`.

The permissive identity follows from the definition of remainder; the useful
division-algorithm content is the degree bound, whose divisor hypotheses are
essential.  Before either fact can become HS-facing, future work needs (1) an
actual concrete instance of every reachable operation, (2) a certified
dense-to-sparse conversion, (3) well-formedness/nonzero/degree/leading-
coefficient preservation, and (4) a sparse-to-dense reconstruction theorem for
quotient and remainder.  There is no target evaluator to shorten these through
semantic evaluation.

The downstream `ed6a.lisp` develops Euclid-domain divisibility and a Euclidean
function in the same abstract FUNPOL world.  It is potential gcd infrastructure
but does not solve concrete instantiation or conversion, and gcd is deliberately
outside this task.

## Recommendation and follow-up PRs

Direct reuse of the 2006 executable quotient is **not recommended**.  The
realistic choices are:

1. **Adapt/generate the 2006 library:** highest cost.  Introduce a maintained
   parameterized instance generator or systematically refactor twelve old
   books, then redo their certification and bridge sparse results back to HS.
2. **Build a fixed-prime instance:** proves the field contracts cleanly, but
   still needs concrete copies of all FUNPOL definitions.  It is useful only if
   several abstract developments justify that infrastructure.
3. **Implement division directly over HS later:** smallest likely certified
   path, preserves the executable explicit-modulus API, but must independently
   prove termination, reconstruction, and the degree bound.  This task does not
   implement it.
4. **Add a project-local abstract field layer:** worthwhile only before several
   algorithms are generalized.  Parameterize new HS algorithms by operations
   and prove a PFIELD instance; do not attempt retroactive substitution inside
   FUNPOL.

Recommended sequence of focused PRs:

1. Specify the HS quotient/remainder contract (canonical outputs,
   reconstruction, nonzero divisor, and remainder-degree bound), without an
   implementation.
2. Prove the small PFIELD inverse and cancellation lemmas required by that
   contract at an explicit prime parameter.
3. Implement and certify one HS-native long-division step and its degree-
   decrease lemma.
4. Add recursive division and reconstruction in a separate PR.
5. Only if a second substantial abstract-field consumer appears, prototype a
   project-local field interface and compare proof reuse against the concrete
   development.

No roadmap item marks polynomial division complete.  The unresolved
mathematical and engineering boundary is also recorded in
`docs/obligations.md`.
