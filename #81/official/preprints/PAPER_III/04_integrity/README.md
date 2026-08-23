# Integrity — Paper III v1.5

The six-artifact manuscript sidecar is generated after final conversion and rendered QA.
The v1.5 residual audit records the v1.4 baseline hashes, protected editorial delta, exact
identity of the unchanged Lean tree and archive, and the hashes of the v1.5 publication
artifacts. `CURRENT_TARGET_SHA256.txt` is regenerated only after the residual report and
external-audit request are final.

The integrity record distinguishes the immutable formal source snapshot from later audit
results, so freeze metadata never makes a circular claim about an audit that postdates it.
The source v1.5 external report remains sealed with its original `CONDITIONAL_PASS`; the
separate closure run records `EXT-V15-M01` as closed and the consolidated verdict as `PASS`
without rewriting the source report.
