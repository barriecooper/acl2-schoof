# Prime-field polynomial bridge

## Inspected Community Books interface

This boundary targets ACL2/Community Books 8.6 (Community Books commit
`7585056a0647c1ab8a45b1573c5cfe524acbda3f`) at
`workshops/2022/gamboa-primitive-roots/pfield-polynomial.lisp`.  That book is
in package `PFIELD` and directly includes:

* `nonstd/polynomials/polynomial-defuns.lisp` (package `ACL2`); and
* `kestrel/prime-fields/prime-fields.lisp` (package `PFIELD`).

Its proof additionally includes, locally, the nonstd polynomial lemmas,
Kestrel prime-field rules2, `projects/numbers/euclid.lisp`, and
`arithmetic-5/top.lisp`.  `order-constructions.lisp` is the directly relevant
downstream workshop book: it includes `pfield-polynomial.lisp` and uses its
root results.

The selected Community Books checkout contains the workshop source but does
not ship its generated certificate.  `make setup` therefore runs
`scripts/certify-system-deps.sh`, which uses the Community Books `cert.pl`
dependency scanner to certify this book and only its required include chain
before any project book is certified.  The operation is idempotent: `cert.pl`
does no certification work when the required certificates are current.
The exact immediate certificate prerequisites reported by `cert.pl` are
`nonstd/polynomials/polynomial-defuns.cert`,
`nonstd/polynomials/polynomial-lemmas.cert`,
`kestrel/prime-fields/prime-fields.cert`,
`kestrel/prime-fields/rules2.cert`, `projects/numbers/euclid.cert`, and
`arithmetic-5/top.cert`; `cert.pl` recursively handles their prerequisites.

The source definitions confirm the following interface (none of these details
is inferred from a theorem name):

| Property | 2022 library definition |
|---|---|
| Representation | A proper dense list `(c0 ... cn)` of integers, in package `ACL2` for the underlying list operations. |
| Coefficient order | Constant coefficient first; `ACL2::EVAL-POLYNOMIAL` uses Horner recursion on the cdr. |
| Zero | `nil` evaluates to zero, but zero is not canonical: `(0)`, `(0 0)`, and coefficients divisible by `p` can denote zero too. |
| Well-formedness | `ACL2::INTEGER-POLYNOMIAL-P`; coefficients need not satisfy `PFIELD::FEP`.  `PFIELD::NON-TRIVIAL-PFIELD-POLYNOMIAL-P` additionally requires a last coefficient whose `FEP-FIX` is nonzero. |
| Evaluation | `PFIELD::EVAL-PFIELD-POLYNOMIAL` is `(mod (ACL2::EVAL-POLYNOMIAL poly x) p)`. |
| Normalization/equality | No polynomial normalizer or quotient equality is supplied.  Lists retain syntactic equality, while evaluation and the non-trivial predicate account for reduction modulo `p`. |
| Root predicate | `PFIELD::PFIELD-POLYNOMIAL-ROOT-P` requires `PFIELD::FEP x p` and target evaluation equal to ACL2 integer zero. |

The exact root-count theorem is
`PFIELD::NUM-ROOTS-OF-POLY-UPPER-BOUND`:

```lisp
(implies (and (dm::primep p)
              (non-trivial-pfield-polynomial-p poly p)
              (<= 2 (len poly)))
         (<= (pfield-polynomial-num-roots poly p)
             (len (cdr poly))))
```

It has rule class `nil`.  In particular, importing it for HS will require a
proved connection between HS canonical nonzero polynomials and
`NON-TRIVIAL-PFIELD-POLYNOMIAL-P`, plus the elementary length/degree
interpretation needed to state its conclusion appropriately.

## Certified conversion boundary

HS and the target happen to share constant-first dense lists.  The explicit
one-way function `HS::HS-TO-PFIELD-POLYNOMIAL` copies that list rather than
exposing this representation coincidence to callers.  For HS field
polynomials the bridge proves:

* the result satisfies `ACL2::INTEGER-POLYNOMIAL-P`;
* `nil` converts to target `nil`;
* conversion reconstructs the original proper HS coefficient list, providing
  faithfulness (and hence injectivity on canonical HS inputs);
* conversion commutes with `HS::POLY-NORMALIZE`;
* `PFIELD::EVAL-PFIELD-POLYNOMIAL` agrees with `HS::POLY-EVAL`; and
* `PFIELD::PFIELD-POLYNOMIAL-ROOT-P` is equivalent to HS evaluation being
  zero, under the evaluator's exact `FEP`, field-polynomial, and positive
  modulus hypotheses.

The conversion accepts `HS::FIELD-POLYNOMIAL-P`, so the evaluation bridge also
applies before HS normalization.  On canonical inputs its reconstruction
theorem makes the boundary faithful without pretending that arbitrary target
lists have a unique semantic representation.

## Deliberately deferred work

This pull request does not transport the root-count bound.  The next focused
bridge obligation is to prove that a nonconstant canonical HS polynomial has
a final coefficient that remains nonzero under `PFIELD::FEP-FIX`, relate its
list length to the already separate HS degree layer, and then instantiate the
Community Books theorem.  No division, gcd, derivative, separability, or
elliptic-curve theory belongs in that step.

A reverse conversion is not currently needed for root-theorem reuse.  It may
be worthwhile later: it should map `PFIELD::FEP-FIX` across arbitrary integer
coefficients and then apply `HS::POLY-NORMALIZE`, with preservation stated in
terms of modular evaluation rather than raw-list equality.
