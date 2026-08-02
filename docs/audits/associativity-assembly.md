# Finite affine semantic associativity assembly audit

## Repository baseline

This audit was performed on branch `work` at
`c57ca564ebb5ebadfd5204eaedbc33fb36e47eba`. That commit is the merge commit
for PR #265. The checkout had no configured remotes and the working tree was
clean before this audit.

## Selected endpoint

The intended public endpoint is candidate C: if `ab`, `bc`, `left`, and
`right` witness the two nested applications of
`curve-point-addition-relation-p`, then
`(curve-point-fix left) = (curve-point-fix right)`. It is independent of the
dispatcher, admits tagged infinity without fake affine coordinates, exposes no
slope or classifier witness, and is directly usable by the later dispatcher
lift. Candidate A unnecessarily chooses a direction and an output-existence
policy. Candidate B is stronger than the later lift needs and requires a new
nested existential interface. No checked-in candidate-D predicate exists.

One-step determinacy can align two witnesses for the same operand pair, but it
cannot supply the cross-tree equality in candidate C. Each matrix family must
first provide that bridge.

## Coverage and family map

`curve-point-addition-case-coverage` first separates either tagged infinity
operand, then distinct x, opposite ordinates, and equal non-opposite affine
points. Together with
`affine-pair-classify-not-same-x-other-for-curve-points`, valid affine inputs
therefore reduce exactly to D/O/T. D and T have affine outputs by their closure
theorems; O crosses immediately to tagged infinity. The two infinity identity
relations, not an affine surrogate, are then the outer semantic interface. The
semantic coverage theorem's final T clause explicitly excludes its overlap
with O at a self-inverse repeated point. T/T forces the fixed repeated triple.
Original infinity is handled before affine decomposition.

The audited principal map is:

| inner cell | certified family boundary |
| --- | --- |
| O/O | only `curve-point-pair-output-point-associative-when-both-inner-opposite-y` |
| O/D and D/O | `affine-inverse-secant-translation`, plus reversal |
| O/T and T/O | `affine-inverse-tangent-translation`, plus reversal |
| D/D | `affine-dd-t-translation` and both `affine-dd-opposite-y-propagates-*` theorems |
| D/T | `affine-dt-d-translation` and `affine-dt-left-output-opposite-y-propagates-to-right-output` |
| T/D | `affine-td-d-translation` and `affine-td-left-output-opposite-y-propagates-to-right-output` |
| T/T | only `curve-point-pair-output-point-associative-when-both-inner-doubling` |
| original infinity | only `curve-point-pair-output-point-associative-when-infinity-input` |

The inverse/secant row is the sole source of the required
`short-weierstrass-characteristic-p` premise. No stronger characteristic or
cardinality premise is indicated.

## Blocking semantic mismatch

Assembly stops at O/O, the first matrix corner. Its exact desired semantic
goal, for affine `a`, `b`, and `c`, inner infinity witnesses `ab` and `bc`, and
final witnesses `left` and `right`, is:

```text
O(a,b,ab) and O(b,c,bc)
and addition-relation(ab,c,left)
and addition-relation(a,bc,right)
imply fix(left)=fix(right).
```

The repository has no relation-level O/O bridge with this statement (nor a
common-output variant). The only complete O/O associativity theorem expands
the executable classifier/dispatcher tree. T/T and original-infinity have the
same semantic-versus-executable mismatch. Using those theorems would mix
layers and violate the required independent semantic boundary; unfolding the
dispatcher to manufacture predecessors would violate the task explicitly.

The missing tight lemma group is therefore semantic O/O, semantic T/T, and
semantic original-infinity associativity over explicit relation witnesses.
These are structural tagged-relation lemmas: they should use the existing
opposite-y and ordered infinity identities, fixed repeated-point facts,
commutativity, and determinacy. They require no coordinate formula, slope
formula, field normalization, cancellation, polynomial, H/S/X-CERT/final-y,
or executable expansion. No such algebra or expansion was attempted here.

## Finite validation

A temporary exhaustive script used the nonsingular curve
`y^2 = x^3 + x + 6` over F7 and the checked-in F11 curve. It compared the two
nested executable outputs only as validation, not as proof. The counts were:

| field | points incl. infinity | valid triples | original infinity | all affine | D/D | D/T | D/O | T/D | T/T | T/O | O/D | O/T | O/O | counterexamples |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| F7 | 11 | 1,331 | 331 | 1,000 | 640 | 80 | 80 | 80 | 10 | 10 | 80 | 10 | 10 | 0 |
| F11 | 13 | 2,197 | 469 | 1,728 | 1,200 | 120 | 120 | 120 | 12 | 12 | 120 | 12 | 12 | 0 |

The theorem premises intentionally exclude malformed tagged values and
off-curve affine coordinates. The temporary script was not committed.
