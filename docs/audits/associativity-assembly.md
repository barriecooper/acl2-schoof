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

Candidate C and the case map above are unchanged. The finite affine matrix
assembly is certified below; full tagged representation reduction remains open.

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

## Certified Candidate C assembly

The public endpoint is certified as
`curve-point-addition-relation-associative-for-affine-inputs`.  Its final proof
instantiates `curve-point-addition-relation-affine-case-coverage` exactly twice,
for the inner outputs `ab` and `bc`, preserves the selected payload and slope
terms opaquely, and combines the resulting product with the nine local cells:

| first inner | second D | second O | second T |
| --- | --- | --- | --- |
| D | D/D | D/O | D/T |
| O | O/D | O/O | O/T |
| T | T/D | T/O | T/T |

The matrix combination is propositional under `minimal-theory`.  It introduces
no relation unfolding, dispatcher reasoning, classifier expansion, coordinate
identity, or field algebra.  A small proof-local fixing normalization connects
the exact fixed operands returned by extraction to the already-certified cell
interfaces; it changes no witness expression.

Only O/D and D/O use `short-weierstrass-characteristic-p`, inherited from
`affine-inverse-secant-translation`.  D/D, D/T, T/D, O/T, T/O, O/O, and T/T
are characteristic-independent, so Candidate C has exactly one characteristic
premise.

The exhaustive validation above was rerun after certification: all 1,000 F7
and 1,728 F11 affine triples retained the displayed matrix partition and had
zero failures.  This validation is evidence, not proof.  The focused public
regression invokes only Candidate C under `minimal-theory`.  The next bounded
boundary was the full tagged semantic wrapper.

## Final tagged representation wrapper

`short-weierstrass-curve-point-non-infinity-representation` now provides the
small public representation interface: a valid non-infinity fixed point has a
valid affine payload and reconstructs exactly from that payload.  The certified
theorem `curve-point-addition-relation-associative` splits only on original
infinity, transports the four supplied relations through fixing, and invokes
Candidate C once on the three extracted payloads.  No addition relation,
classifier, field operation, or executable dispatcher is unfolded.  Exhaustive
validation retained zero failures over all 1,331 valid F7 tagged triples and
all 2,197 valid F11 tagged triples; the original-infinity/affine partitions
were 331/1,000 and 469/1,728 respectively.  These counts are validation, not
proof.  The next boundary is the semantic-to-executable dispatcher lift.
