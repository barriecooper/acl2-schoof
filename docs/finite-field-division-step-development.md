# Historical finite-field division-step development note

This audit records the retained certifying prefix at its historical baseline for the finite-field one-step
division substrate.  The book `books/polynomial/generic/finite-field-division-step.lisp`
currently certifies the generated one-step definitions, guard verification,
inactive core equation, leading-coefficient nonzero support, inverse nonzero
support, and active step-term canonicality/nonzero/degree/leading-coefficient
properties.

The first non-retained failing route attempted a direct finite-field target
version of the source product-properties theorem from
`books/polynomial/generic/division-step.lisp`.  The exact missing reusable target
facts are finite-field counterparts of:

- `poly-leading-coefficient-of-poly-mul`
- `poly-degree-of-poly-mul`
- `consp-of-poly-mul-when-canonical-nonzero`

A later direct next-canonical attempt also failed without this product layer in
place.  At that recorded baseline, the recommended next step was to add small reusable finite-field multiplication
transport theorems, preferably by functional instantiation of the generic
multiplication theorems, then resume the source theorem order at
`finite-field-poly-division-step-core-product-properties`.

Current planning is maintained in [proof-plan.md](proof-plan.md); the recommendations above are historical and are not active task guidance.
