# Certified PFIELD adapter

## Scope and architecture

`books/field/pfield-adapter.lisp` is a **generic adapter for one encapsulated
prime modulus (design A), followed by a concrete functional instance**.  An
ordinary ACL2 `encapsulate` introduces nullary `GFIELD::PFIELD-MODULUS`; local
value 3 witnesses consistency and the exported constraint is `DM::PRIMEP`.
Primality entails an integer modulus at least 2.  There is no mutable state,
attachment, raw Lisp, trust tag, or axiom.  Concrete adapters replace the
modulus and wrappers by functional instantiation; the executable `F_7`
definitions demonstrate that workflow.

| wrapper | arity | PFIELD boundary |
|---|---:|---|
| `pfield-element-p` | 1 | `PFIELD::FEP x (pfield-modulus)` |
| `pfield-fix` | 1 | `PFIELD::FEP-FIX x (pfield-modulus)` |
| `pfield-zero`, `pfield-one` | 0 | integers 0 and 1 |
| `pfield-add`, `pfield-mul` | 2 | PFIELD operation on fixed inputs |
| `pfield-neg`, `pfield-inv` | 1 | PFIELD operation on a fixed input |

Derived executable wrappers `pfield-sub`, `pfield-div`, and `pfield-pow`
mirror GFIELD.  Fixing inputs is essential because GFIELD equations are total
over all ACL2 objects while PFIELD guards describe canonical inputs.

## Exact Community Books basis

The inspected source is ACL2 8.6 / Community Books commit
`7585056a0647c1ab8a45b1573c5cfe524acbda3f`: `kestrel/prime-fields/{fep,
fep-fix,add,mul,neg,inv,prime-fields,prime-fields-rules}.lisp` and
`prime-fields-alt.lisp`.  The alternate book demonstrates a nullary
constrained prime but cannot coexist with the explicit interface because it
assigns different arities to the same PFIELD symbols, so this book reuses the
ordinary-ACL2 pattern under project-local symbols.

The proof uses exact results `FEP-OF-FEP-FIX`, `FEP-FIX-WHEN-FEP`,
`FEP-OF-0`, `FEP-OF-1`, operation closure theorems, `ADD-ASSOCIATIVE`,
`ADD-COMMUTATIVE`, `ADD-OF-0-ARG1`, `ADD-OF-NEG-SAME-ARG1`,
`MUL-ASSOCIATIVE`, `MUL-COMMUTATIVE`, `MUL-OF-1-ARG1`,
`MUL-OF-ADD-ARG2`, `INV-OF-0`, and `MUL-OF-INV-ARG1`.  Inverse correctness
requires `DM::PRIMEP p`; closure commonly needs only `POSP p`, while
`FEP-OF-INV` separately assumes integer `p` and `1 < p`.  The adapter exports
the single stronger prime constraint, making every fixed-boundary law
unconditional.

## Canonical representatives and certified laws

`PFIELD::FEP` recognizes exactly naturals below the modulus, hence unique
representatives rather than multiple integers modulo `p`.  `FEP-FIX` always
returns that range and is identity on it.  The book proves fixer idempotence,
zero/one membership and distinction, operation closure, fixed outputs,
fixing compatibility, and that equality of fixed outputs is ordinary ACL2
`EQUAL`; no quotient equivalence is needed.

The obligation group proves additive and multiplicative associativity and
commutativity, identities, additive inverse, distributivity, congruence,
inverse closure, total inverse-at-zero, and nonzero inverse correctness.
`pfield-double-negation-from-generic-kernel` functionally instantiates
`FIELD-NEG-OF-NEG`; `f7-double-negation-from-generic-kernel` then replaces the
encapsulated modulus with 7.  Smoke tests cover fixing, zero/one, wraparound,
negation, inverse, subtraction, division, powers, and that theorem.

## HS relationship and deferrals

No polynomial API changes.  `field-polynomial-p` corresponds to the carrier;
`poly-add-raw`, `poly-scale-raw`, `poly-mul-raw`, and `poly-eval` correspond
to adapter addition/multiplication and Horner evaluation with explicit `p`.
Their algebraic results can later be recovered from generic polynomial
theorems.  The 2022 root counter remains a prime-field corollary because it
uses explicit integer representatives, modulus, and PFIELD enumeration.

Only prime fields `F_p` are established.  Generic polynomials, arbitrary
`F_q`, cardinality, characteristic, enumeration, Frobenius, extensions,
irreducible quotients, and division remain deferred.  Algebraic closures and
geometric extensions remain after the basic elliptic-curve group-law layer
and before torsion, isogeny kernels, separability, and degree.
