# X-CERT H reconstruction experiment

This unregistered proof-development book is intentionally temporary.  It
certifies the explicit-term-list additive normalization core for the scalar H
residual: a 52-term raw expansion is rearranged to 20 adjacent inverse pairs
and the 12 target monomials.  The local `field-sum-list` permutation-invariance
lemmas and `raw-sum-is-normal-sum` / `normal-sum-is-target-sum` all certify.

Immediate next step: add two bridge lemmas in the experiment book.  The first
expands the seven-residual right side to the existing 52-term raw list.  The
second expands
`(xc-xb)*((p-r)*(p+q)-(xa-xc))` to the existing 12-term target
list.  Then compose the certified list equalities, add the zero-residual and
left-cancellation steps, and only afterward promote/rename the book, add a
regression, registration, and documentation updates.

The last successful focused command was:

    make certify-one BOOK=books/field/xcert-h-reconstruction-experiment.lisp

The complete successful log is
`.deps/logs/books_field_xcert-h-reconstruction-experiment.log`.
