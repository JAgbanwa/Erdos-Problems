# Integrity — Paper III v1.4

`CURRENT_TARGET_SHA256.txt` is generated only after the final internal-audit report and
package are sealed. Lower-level checks are provided by the six-artifact manuscript sidecar,
the freeze source/package manifests, the formal archive sidecar, the received build-evidence
manifest and the per-gate internal-audit manifests.

The integrity record distinguishes the immutable formal source snapshot from audit results,
so freeze metadata never makes a circular claim about a later audit.
