# Finite affine semantic associativity assembly audit

## Repository baseline

This audit was performed on branch `work` at
`c57ca564ebb5ebadfd5204eaedbc33fb36e47eba`. That commit is the merge commit
for PR #265. The checkout had no configured remotes and the working tree was
clean before this audit.

## Candidate C continuation baseline

The Candidate C continuation was inspected on branch `work` at
`10d2ebf35045ad15c902c675f09b516327ccd077`.  The checkout had no configured
remotes and its working tree was clean.  PR #269 is present as merge commit
`10d2ebf`; its second parent contributes the certified arbitrary-witness D/D
outer-secant/outer-secant interface described below.  No uncertified assembly
book or experimental proof was restored.

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
| O/O | `curve-point-addition-relation-associative-when-both-inner-opposite-y` |
| O/D and D/O | `affine-inverse-secant-translation`, plus reversal |
| O/T and T/O | `affine-inverse-tangent-translation`, plus reversal |
| D/D | `affine-dd-t-translation` and both `affine-dd-opposite-y-propagates-*` theorems |
| D/T | `affine-dt-d-translation` and `affine-dt-left-output-opposite-y-propagates-to-right-output` |
| T/D | `affine-td-d-translation` and `affine-td-left-output-opposite-y-propagates-to-right-output` |
| T/T | `curve-point-addition-relation-associative-when-both-inner-doubling` |
| original infinity | `curve-point-addition-relation-associative-when-original-infinity` |

The inverse/secant row is the sole source of the required
`short-weierstrass-characteristic-p` premise. No stronger characteristic or
cardinality premise is indicated.

## Resolved structural semantic interface

The former semantic mismatch is resolved by these certified public boundaries:

* `curve-point-addition-relation-associative-when-both-inner-opposite-y`;
* `curve-point-addition-relation-associative-when-both-inner-doubling`;
* `curve-point-addition-relation-associative-when-original-infinity`.

The O/O boundary has the exact audited shape for affine `a`, `b`, and `c`,
inner infinity witnesses `ab` and `bc`, and final witnesses `left` and `right`:

```text
O(a,b,ab) and O(b,c,bc)
and addition-relation(ab,c,left)
and addition-relation(a,bc,right)
imply fix(left)=fix(right).
```

O/O uses determinacy for each outer operand pair against its ordered infinity
identity witness. T/T first uses determinacy to align `ab` and `bc` after the
fixed repeated-triple premises align both input pairs, then reverses the left
outer witness by semantic commutativity and uses determinacy for the aligned
outer pair. Each ordered original-infinity proof uses determinacy only after
an infinity identity fixes an inner witness and thereby aligns the relevant
outer operand pair. The combined theorem packages the three positions.

Candidate C and the case map above are unchanged. Finite affine matrix
assembly, rather than any structural interface, is now the open task.

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

## Candidate C assembly attempt at `5952b4b`

The requested public endpoint was attempted with tagged affine constructors for
`a`, `b`, and `c`, the four explicit relation witnesses `ab`, `bc`, `left`, and
`right`, the single `short-weierstrass-characteristic-p` premise, and fixed
output equality.  The exact semantic coverage interface remains
`curve-point-addition-case-coverage`: for two curve points it returns original
infinity, distinct x, opposite ordinates, or equal non-opposite affine
coordinates.  A proof-local extraction from the full relation reduces affine
inputs to the corresponding secant, opposite-y, or doubling relation witness.

Assembly stopped at the D/D cell before any production theorem was admitted.
The advertised complete-D/D map does not contain a relation-level boundary for
the outer secant/secant subcase with arbitrary semantic witnesses.  In detail,
`affine-dd-t-translation` requires a doubling relation at the first inner
output; the two `affine-dd-opposite-y-propagates-*` theorems require an outer
opposite-y relation.  None consumes two inner secants plus supplied secant
relations on both outer trees.  The only checked-in equality for that remaining
subcase is `xcert-untagged-outputs-equal`, whose premises and conclusion name
canonical classifier-selected coordinate outputs rather than the four supplied
semantic relation witnesses.  Using it would require a new semantic bridge
from arbitrary secant witnesses to those canonical outputs; it is not one of
the audited principal family boundaries.

The mismatch is therefore a genuinely missing family-semantic interface, not
branch extraction, representation, orientation, infinity handling, fixing,
or characteristic scope.  The determinacy instance that would follow such a
bridge is well-typed: compare the supplied and derived outputs separately on
operand pairs `(ab,c)` and `(a,bc)`, after fixing determinacy has aligned each
inner secant witness with its derived tagged affine output.  Determinacy cannot
itself prove equality between those different outer operand pairs.

No coordinate, field, X-CERT, classifier, or executable dispatcher definition
was unfolded or added.  The prior exhaustive F7/F11 validation remains
unchanged: all 1,000 and 1,728 affine triples respectively have zero failures,
with the nine cell counts recorded above.  Candidate C remains open pending a
narrow semantic outer-secant/outer-secant D/D boundary (or an explicitly
approved semantic wrapper around the existing canonical X-CERT equality).

## D/D outer-secant/outer-secant interface resolution

The missing arbitrary-witness boundary is now certified as
`affine-dd-secant-relation-associative-when-all-distinct-x`. It uses the
canonical outputs `xcert-ab`, `xcert-bc`, `xcert-left`, and `xcert-right`.
Relation fixing congruence transports the supplied outer relations after the
inner outputs have been aligned. The four determinacy instances compare only
the same operand pairs: `(a,b)` aligns `ab` with `xcert-ab`; `(b,c)` aligns
`bc` with `xcert-bc`; `(xcert-ab,c)` aligns `left` with `xcert-left`; and
`(a,xcert-bc)` aligns `right` with `xcert-right`. The sole cross-tree equality
is the opaque public theorem `xcert-untagged-outputs-equal`. No X-CERT
definition, coordinate identity, field expression, classifier definition, or
dispatcher was unfolded to establish that equality.

Exhaustive validation on the existing affine triples partitions the 640 F7
D/D cases into 430 outer secant/secant, 140 tangent-related, and 70 O/O cases;
the 1,200 F11 D/D cases partition into 876, 216, and 108 respectively. All 430
and 876 cases applicable to the new theorem had zero associativity failures,
and exhaustive enumeration of semantic slope/output witnesses for each of the
four operand pairs had zero deviations from its canonical output. This finite
check is validation only. Candidate C matrix assembly remains open.
