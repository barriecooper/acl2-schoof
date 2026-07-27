# F11 golden curve fixture

The curve `y^2 = x^3 + x + 6` over `F_11` is retained as a small,
independently inspectable execution regression for later elliptic-curve work.
It is not a generic curve interface, group-law development, Hasse proof, or
Schoof computation.

Field values use canonical representatives `0, 1, ..., 10`. Dense polynomials
are constant-first, so the fixed cubic is `(6 1 0 1)`. The fixture generates
only coefficient fixing, trailing-zero trimming, normalization, and Horner
evaluation. In particular it creates no F11 power operation or new
logical/executable boundary.

The twelve affine solutions, in certified enumeration order, are:

```
(2,4)  (2,7)  (3,5)  (3,6)  (5,2)  (5,9)
(7,2)  (7,9)  (8,3)  (8,8)  (10,2) (10,9)
```

The point at infinity is deliberately separate from affine pairs. One such
point gives `#E(F_11) = 12 + 1 = 13`; the golden trace data is
`t = 11 + 1 - 13 = -1`. The book separately validates every literal pair and
exhaustively enumerates all 121 canonical affine pairs. It also computes
`4(1)^3 + 27(6)^2 != 0` in F11 as a focused nonsingularity check, not a generic
discriminant theorem.

The generic short-Weierstrass boundary now reuses the same coefficients in
`books/curve/f11-short-weierstrass.lisp`.  Its total coordinate predicate also
checks a listed point, a nonpoint, fixed noncanonical integers, and malformed
objects.  This validation adds neither a packaged point type nor group
operations.

Generic polynomial degree and leading coefficient remain the next
mathematical milestone.
