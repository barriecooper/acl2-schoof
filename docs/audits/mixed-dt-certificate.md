# Mixed D/T semantic certificate audit

This record preserves the derivation and validation evidence behind the
current mixed-inner D/T endpoints. Current status is maintained separately in
the [associativity matrix](../status-associativity.md); this document is an
audit, not a live roadmap.

## Orientation and witness

The certified orientation is exactly:

```text
A+B=P by p
B+B=Q by t
P+B=R by q
```

The opposite-tree witness is exactly:

```text
s=(p+q)-t
```

Here D/T names the inner secant and doubling. The certified branches reconstruct
`A+Q=R` as a secant when `xQ != xA` and as a doubling when `xQ=xA`. The outer
O/O degeneration is also certified in the required converse direction:
`P=-B` implies `A=-Q`.

## Why the bare scalar interface failed

The original bare field equation group was insufficient. A concrete F11
assignment satisfied all nine proposed scalar equations while falsifying the
wanted reconstruction, even when the apparent inner nonzero factors and
relevant tangent-domain condition held. No omitted equation among that group
fixed the issue. This was a countermodel to the proposed *interface*, not to
curve associativity: it did not satisfy the common-curve identities relating
the two secants and the tangent.

The repair was therefore not another arbitrary denominator premise. The curve
semantics supplies two confluent common-curve identities, which feed the H
bridge and exclude the countermodel.

## Field bridges

### Confluent H

`xcert-confluent-h-factored-reconstruction` exposes the two-factor residual;
`xcert-confluent-h-scalar-reconstruction` consumes the ordered curve-derived
input identities and reconstructs the maintained H equation. In the D/T
specialization the result is

```text
(p-t)*(p+q)=xA-xB.
```

Its multiplicative cancellations are exactly the certified secant differences
`xB-xA` and `xB-xP`, performed separately. It introduces no curve predicate,
classifier, division, inverse, characteristic premise, or independent public
nonzero hypothesis.

### Factored S

`xcert-s-factored-reconstruction-from-h` retains the outer factor and derives
the S balance from H and the oriented output equations. For the outer
secant specialization it yields

```text
(xQ-xA)*(p+q-(t+u))=0,
```

where `u` is the canonical slope for `A,Q`. Only the public outer disequality
cancels `xQ-xA`; bounded additive normalization then identifies `u=s`.

## Certified outer distinct-x chain

| Stage | Public theorem | Proof role |
|---|---|---|
| Slope | `affine-dt-d-outer-distinct-x-slope-equation` | Specializes confluent H and factored S, cancels `xQ-xA`, and identifies the canonical outer slope with s. |
| Output x | `affine-dt-d-outer-distinct-x-output-x-equation` | Uses H/S and X-CERT composition to identify the canonical secant output abscissa with `xR`. |
| Output y | `affine-dt-d-outer-distinct-x-output-y-equation` | Uses the field-only final-y reconstruction after the output-x equality. |
| Semantic package | `affine-dt-d-outer-distinct-x-translation` | Packages those three endpoints directly as the division-free secant relation for `A,Q,s,R`. |

The output-x composition introduces no new cancellation. The output-y residual
before bounded simplification is

```text
(yR-yE) - ((p-t)*(xR-xB) + (t-q)*(xA-xB)),
```

with `E` the canonical `A+Q` secant output. H and the left output-x equation
turn the two products into additive inverses; the S coefficient on `xA-xR`
vanishes. Final-y adds no multiplication cancellation.

## Certified coincident-x chain

### Ordinate exclusion and propagation

When `xQ=xA`, the common-curve equal-x dichotomy gives `yQ=yA` or
`yQ=-yA`. The theorem `affine-dt-opposite-y-propagates-to-left-output`
propagates the second alternative from `A=-Q` to `P=-B`; its x equality
contradicts the distinct-x clause of `P+B=R`. Thus
`affine-dt-d-coincident-x-implies-ordinate-equality` proves `yQ=yA`.

The same propagation proves the tangent domain in
`affine-dt-d-coincident-x-excludes-self-inverse`: if `yA=-yA`, the ordinate
equality packages `A=-Q`, propagation again gives `P=-B`, and the second
secant supplies the contradiction. Propagation internally cancels `xB-xA`;
the ordinate and domain wrappers introduce no cancellation.

### Tangent numerator and canonical slope

`affine-dt-d-coincident-x-tangent-equation` proves

```text
s*(yA+yA)=3*xA^2+a.
```

Writing `d=xB-xA` and `L=p+q`, the two oriented line equations give
`yA+yA=(t-p)*d`; confluent H gives `(t-p)*L=d`; and the witness gives
`L=t+s`. After the tangent numerator and doubling output equation at B, the
bounded residual is

```text
d^2-2*(xA+2*xB)*d+3*xB^2+a = 3*xA^2+a.
```

This stage adds no multiplication cancellation. The H theorem retains its two
internal secant cancellations.

The tangent-domain result makes `yA+yA` nonzero. Comparing the public numerator
for `s` with the canonical tangent numerator identifies `s` with the canonical
tangent slope; this single cancellation occurs in the output-x endpoint.

### Output coordinates and semantic package

| Stage | Public theorem | Proof role |
|---|---|---|
| Output x | `affine-dt-d-coincident-x-output-x-equation` | Canonical slope identification plus confluent X-CERT composition proves the doubling output-x equation for R. |
| Output y | `affine-dt-d-coincident-x-output-y-equation` | Canonical tangent output and field-only final-y reconstruction prove `yR+yA=s*(xA-xR)`. |
| Semantic package | `affine-dt-d-coincident-x-translation` | Packages tangent domain, numerator, output x, and output y as the division-free doubling relation for `A,s,R`. |

The output-y bridge adds no multiplication cancellation. The packaging theorem
replays none of the propagation, H/S, telescope, canonical-slope, X-CERT, or
final-y proofs.

## Cancellation inventory

The complete inventory across the certified mixed D/T endpoints is:

1. `xB-xA` and `xB-xP` inside confluent H;
2. `xQ-xA` in the outer distinct-x S/slope reconstruction;
3. `xB-xA` inside opposite-y propagation; and
4. `yA+yA` solely to identify the coincident-x witness with the canonical
   tangent slope; and
5. for the outer O/O converse, `xB-xA` inside the reused inverse/secant
   tangent-equation certificate and `yB+yB` to identify `p=t`.

Packaging and final-y add no multiplication cancellation. Additive
cancellations used to align canonical output coordinates require no nonzero
premise. No endpoint adds division, inverse, classifier assumptions, an
independent denominator, or a characteristic premise.

## Certified outer O/O converse

The associativity endpoint needs the converse of the older propagation
theorem: from `A+B=P`, `B+B=Q`, and `P=-B`, theorem
`affine-dt-left-output-opposite-y-propagates-to-right-output` derives `A=-Q`
with the same fixed infinity payload. Secant operand reversal and opposite-y
symmetry alone cannot reverse the older implication, so the proof uses a
staged coordinate certificate rather than an unproved reassociation.

After reversing `A+B=P` to `B+A=P` and symmetrizing `P=-B`, the certified
inverse/secant A-D4 theorem reconstructs the tangent numerator for `p` at B:
`p*(yB+yB)=3*xB^2+a`. Its internal common-curve step cancels only the original
secant factor `xB-xA`. The doubling relation supplies the same numerator for
`t` and its intrinsic domain clause `yB!=-yB`; the latter proves
`yB+yB!=0`, whose single cancellation yields `field-fix(p)=field-fix(t)`.
The secant and tangent output-x equations then give `xQ=xA` by additive
cancellation, and the two line/output-y equations give `yQ=-yA`. No
characteristic predicate, classifier, division, inverse, outer denominator,
or independent nonzero premise is used.

## Finite validation

Exhaustive enumeration of the checked configurations found 1,764 oriented D/T
inputs over F7 and 12,100 over F11. The paired outer outcomes were:

| Field | D/D | D/T coincident-x | O/O |
|---|---:|---:|---:|
| F7 | 1,296 | 216 | 252 |
| F11 | 10,000 | 1,000 | 1,100 |

All cases used `s=p+q-t` and the two trees agreed. In the coincident-x subsets,
all 216 F7 and 1,000 F11 cases satisfied the ordinate equality and tangent
domain conclusions. These exhaustive finite checks are validation and
regression guidance, **not proof** of the generic theorems.

## Open boundary

All three oriented mixed D/T outer outcomes are now individually certified.
The next boundary is their complete oriented branch combination; the T/D
mirror and finite semantic assembly follow later.
