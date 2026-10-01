# Independent audit status

## Current preparation for v1.2

The active mandate is [the v1.2 request](EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.2.md).
It is **BLOCKED_PENDING_INTERNAL_AUDIT**, not ready to execute.
See [the target record](AUDIT_TARGET_v1.2.json) and
[the local reading boundary](LOCAL_INPUT_SCOPE_v1.2.json).

Results are reserved for `run_v1.2_r1/`; only preparation controls exist there.
The source content, author-build evidence across the reboot and final manuscript
package have distinct identities. The new manuscript identity is
`piv-v12-manuscripts-2451d43bface`; the complete author reconstruction and annex
inputs are bound. The new internal audit still must complete and be bound before
execution. Do not run the old `verify_audit_target.py` as
if it checked v1.2: it is tied to the historical v1.0.1 target.

The full isolated external build remains last, after the no-blocker checkpoint.
The v1.2 scope includes C′, E34/E35, the square-root obstruction, detailed
E.4/F.3a/F.5 checks and a verdict for each summarized derivation in A.2.
No audit has been launched by preparing this mandate.

## Historical v1.0.1 handoff and v1.0 Lean cut

The corrected handoff **r3**, manuscript version **1.0.1**, is ready to start,
**not executed**. Cycle r2 remains **FAIL** on attribution; its E4 build never
ran. See the [immutable r2 report](run_2026-09-28_v1.0.1_r2/30_REPORT/FINAL_AUDIT_REPORT.md)
and the separate [author response](../../04_integrity/revision_r3/AUTHOR_RESPONSE_r2.md).
The seven F-02 independent-rederivation items remain open. The exact input manifest is
[`AUDIT_TARGET_v1.0.1.json`](AUDIT_TARGET_v1.0.1.json). Run
[`verify_audit_target.py`](verify_audit_target.py) for a read-only identity
check before the auditor's independent work; it neither builds Lean nor
installs dependencies. The [readiness record](../../04_integrity/AUDIT_READINESS_v1.0.1.md)
distinguishes completed preparation from the open review and release gates.

The [local input allowlist](LOCAL_INPUT_SCOPE_v1.0.1.json) limits exposure to
unpublished working trees. A fresh auditor declares prior participation and
logs additional access. Substantive mathematics, conformance and attribution
review precede the full build. Confirmed blockers stop the run with a sealed
partial finding; unresolved serious concerns/timeouts remain inconclusive.
Theorem C versus [15] and later versions of [5]/[15] are explicit checks.

Renewed adversarial review is pending. The current
[request](EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.0.1.md) identifies the
unchanged v1.0 Lean source, the six v1.0.1 manuscript files, the
claim-to-declaration map, editorial delta and the completed
internal audit by hash. It asks for independent mathematical attack and an
isolated Paper IV project rebuild while **reusing the existing pinned
Mathlib installation on this computer**: no second Mathlib source checkout or
installation. This request is not an audit result. Preserve each review,
author response and recheck under a new run directory; do not replace the
v0.8 history. The earlier [v1.0 request](EXTERNAL_ADVERSARIAL_AUDIT_REQUEST_v1.0.md)
is retained as a historical target and must not be substituted for the new one.

AI adversarial review, author-side kernel verification, independent
reproduction and human mathematical peer review are different forms of
evidence. Report which was actually performed. A protocol or an optimization
return is not a final-cut adversarial PASS. Publication remains subject to
the [release checklist](../../RELEASE_PREPARATION_v1.0.md).

## Retained public-draft status

No independent clean-room reproduction or final external adversarial audit
of this exact public Paper IV draft package is claimed here. Review comments
on earlier manuscript snapshots do not replace such an audit.

The first three papers preserve their own external audit histories in their
respective directories. Their favorable verdicts must not be transferred to
Paper IV by analogy. This directory records the open gate instead of filling
it with unrelated reports.
