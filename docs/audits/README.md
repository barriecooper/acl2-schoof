# Architectural and proof audits

This directory preserves the evidence behind decisions that materially select,
reject, defer, or reshape a mathematical proof route or architectural boundary.
An audit may retain source comparisons, failed interfaces, counterexamples,
alternative designs, and risks after the live plan has moved on.  It is not the
authority for current proof status or implementation order.

The maintained documents have distinct responsibilities:

- [`../obligations.md`](../obligations.md) is the authoritative ledger of what
  is certified, open, or deferred.
- [`../proof-plan.md`](../proof-plan.md) is the authoritative forward sequence.
- [`../architecture.md`](../architecture.md) records only adopted stable
  architecture and dependency boundaries.
- this directory records the evidence and reasoning behind those maintained
  decisions.  Candidate designs and unresolved questions in an audit are not
  adopted architecture.

## Index

| Audit | Status | Scope |
|---|---|---|
| [`associativity-assembly.md`](associativity-assembly.md) | Historical decision and completion record | Selects the finite affine semantic associativity endpoint, records its D/O/T coverage and validation, and follows it through the certified tagged wrapper. Current theorem status lives in the obligation ledger and associativity status document. |
| [`mixed-dt-certificate.md`](mixed-dt-certificate.md) | Historical proof evidence | Preserves the mixed D/T countermodel, repaired field interface, cancellation inventory, finite validation, and structural T/D mirror behind the certified associativity lemmas. |
| [`hasse-source-and-dependency.md`](hasse-source-and-dependency.md) | Accepted route; realization design remains open | Preserves the corrected Hasse source/dependency audit, selects the Silverman Frobenius/degree route, and records the minimum ambient/base-field questions that must be resolved before implementation. |

The earlier extension-field/cardinality architectural audit is reflected only
through its merged code, live ledger, plan, and Git/PR history.  Its original
report is not reproduced here; reconstructing it without that evidence would
not restore a reliable audit record.

## Preservation policy

Preserve a substantive read-only audit when it materially changes a proof or
architecture decision—for example, by selecting a primary route, rejecting an
apparently natural interface, deferring a foundation from the critical path,
or exposing a new realization risk.  The preserved record should identify its
baseline and evidence, distinguish certified facts from proposals, and link to
the live status documents.  Ordinary reviews, routine implementation notes,
and every small PR do not each require a separate audit document.
