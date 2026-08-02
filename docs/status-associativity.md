# Associativity status

This matrix is the at-a-glance source for current associativity coverage.
“Certified” means the named checked-in book is included by `books/top.lisp`;
“open” is the next semantic work; “deferred” depends on those open semantic
boundaries. Detailed obligations remain in [the ledger](obligations.md).

| Family | Inner/outer geometry | Status | Primary public theorem or boundary | Characteristic premise | Remaining dependency |
|---|---|---|---|---|---|
| Original infinity input | At least one original tagged input is infinity | **Certified semantically** | `curve-point-addition-relation-associative-when-original-infinity` | None | Later tagged assembly |
| O/O | Both inner affine additions are opposite-y and return infinity | **Certified semantically** | `curve-point-addition-relation-associative-when-both-inner-opposite-y` | None | Finite affine semantic assembly |
| T/T | Repeated fixed triple; both inner additions coincide | **Certified semantically** | `curve-point-addition-relation-associative-when-both-inner-doubling` | None | Finite affine semantic assembly |
| Inverse/secant | One inner pair is opposite-y; the other is a distinct-x secant | **Certified** | `affine-inverse-secant-translation` | `short-weierstrass-characteristic-p` | Later semantic assembly |
| Inverse/tangent | One inner pair is opposite-y; the other doubles | **Certified** | `affine-inverse-tangent-translation` | None | Later semantic assembly |
| D/D outer distinct-x | Two inner secants; opposite tree closes by a secant | **Certified** | `affine-dd-t-outer-distinct-x-translation` | None | Included in complete D/D family |
| D/D outer coincident-x/doubling | Two inner secants; opposite tree closes by doubling | **Certified** | `affine-dd-t-coincident-x-translation` | None | Included in complete D/D family |
| D/D outer O/O | Two inner secants; opposite-y propagates to the other tree | **Certified** | `affine-dd-opposite-y-propagates-to-other-tree` and `affine-dd-opposite-y-propagates-to-left-tree` | None | Included in complete D/D family |
| Complete D/D family | All derived outer outcomes for the two-inner-secant family | **Certified** | `affine-dd-t-translation`, together with the two `affine-dd-opposite-y-propagates-*` boundaries | None | Later semantic assembly |
| D/D arbitrary-witness outer secant/secant | Four arbitrary secant-relation witnesses aligned with the canonical all-distinct-x trees | **Certified semantically** | `affine-dd-secant-relation-associative-when-all-distinct-x` | None | Candidate C matrix assembly |
| Oriented D/T outer distinct-x | `A+B=P`, `B+B=Q`, `P+B=R`; `A+Q` is a secant | **Certified** | `affine-dt-d-outer-distinct-x-translation` | None | Included in `affine-dt-d-translation` |
| Oriented D/T coincident-x | Same orientation; `xQ=xA`, so `A+Q` doubles | **Certified** | `affine-dt-d-coincident-x-translation` | None | Included in `affine-dt-d-translation` |
| Oriented D/T outer O/O | Same orientation; outer opposite-y degeneration | **Certified** | `affine-dt-left-output-opposite-y-propagates-to-right-output` | None | Included in complete oriented D/T family |
| Complete oriented D/T | Left outer secant outcomes, plus the witness-free O/O outcome | **Certified** | `affine-dt-d-translation`, together with `affine-dt-left-output-opposite-y-propagates-to-right-output` | None | None for this family |
| T/D mirror | `A+A=P`, `A+B=Q`; mirrored right-outer secant outcomes and left-to-right O/O propagation | **Certified** | `affine-td-d-translation`, together with `affine-td-left-output-opposite-y-propagates-to-right-output` | None | Finite affine semantic assembly |
| Finite affine semantic assembly | Exhaustive affine O/T/D case combination | **Open** | Structural semantic predecessors are certified; see the [assembly audit](audits/associativity-assembly.md) | Expected union: `short-weierstrass-characteristic-p` | Candidate C matrix assembly |
| Executable dispatcher lift | Lift semantic equality to nested `curve-point-pair-output-point` | **Deferred** | Unrestricted dispatcher theorem not yet checked in | Inherited from semantic theorem | Finite affine semantic assembly, soundness, determinacy, closure, fixing |
| Unrestricted associativity | All valid tagged curve-point inputs | **Deferred** | No unrestricted theorem is checked in | Inherited from completed semantic coverage | Semantic assembly and executable lift |

The D/T notation describes the two **inner** geometries, not an outer
classifier. The maintained orientation and certificate details are in the
[mixed D/T audit](audits/mixed-dt-certificate.md).
