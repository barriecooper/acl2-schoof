# Working agreement

Certification is the definition of done. Work on one named theorem or a tight
lemma group at a time. Read both the books included by, and the books including,
the file you edit. After every significant change run:

    make check-trust
    make certify-one BOOK=books/polynomial/base.lisp
    make test
    make certify

Inspect the complete log in `.deps/logs`; never guess from a truncated ACL2
message. Prefer small reusable lemmas to huge hint lists, and do not globally
enable large theories without written justification. Never weaken a statement
just to get a proof through. Never introduce skipped proofs, axioms, trust tags,
raw Lisp, or equivalent escapes. Record unresolved mathematics in
`docs/obligations.md`. Clearly distinguish executable implementation theorems
from semantic bridge theorems.

Any PR that introduces a public logical/executable boundary (including `MBE`,
`DEFEXEC`, an attachment, or an equivalent mechanism) must normally include a
named logical specification, a named executable implementation, a certified
invariant or equivalence theorem, verified guards sufficient for the executable
branch, focused concrete execution regressions, and documentation separating
logical correctness, guard/execution assurance, and performance or complexity
evidence. Guard verification does not prove semantic correctness; that must
follow from the certified invariant or equivalence theorem. An execution
regression shows that the intended branch runs with practical behaviour, but
does not replace that proof. Update `docs/execution-boundaries.md` whenever a
PR adds or changes such a boundary.
