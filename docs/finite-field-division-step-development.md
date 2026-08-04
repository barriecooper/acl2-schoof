# Temporary finite-field division-step development note

This note records the retained certifying prefix for the finite-field one-step
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
place.  The likely next step is to add small reusable finite-field multiplication
transport theorems, preferably by functional instantiation of the generic
multiplication theorems, then resume the source theorem order at
`finite-field-poly-division-step-core-product-properties`.
