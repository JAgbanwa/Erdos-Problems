# Integrity — Paper IV v1.23

Publication identity is bound by RELEASE_MANIFEST.json and its SHA-256
sidecar. [PUBLICATION_CHECKS.json](PUBLICATION_CHECKS.json) records the local
packaging checks. The repository-wide manifest_sha256.txt is regenerated
after the documentation is final; it excludes itself and Git metadata.

The source manifest remains
fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5.
The current manuscripts have the editorial-only delta documented in
CHANGELOG_v1.23.md. Exact v1.22-r4 artifacts are retained under
02_validation/02_IA_ADVERSARIAL_AUDITS/audit_inputs/published_v1.22/.
Neither frozen sources nor signed-off reports were edited.

[RELOCATION_MAP_v1.22.json](RELOCATION_MAP_v1.22.json) maps original paths to
the publication layout, with hashes. This allows intermediate versions to
live only inside audit inputs while preserving the original targets and
report paths as historical evidence. RELOCATION_DELTA_v1.23.json resolves
the six v1.22 manuscript files now kept in audit inputs. The old map itself
is unchanged. The final external report remains at its original path.

The original public v0.8 was recovered from Git commit
f783a792404a60983a7ef754d055fbe6c341188b, not from modified working files.
Its historical manifest and files remain unchanged in superseded/draft_v0.8.

No v1.23 commit, tag, publication date or Zenodo version DOI is asserted.
See [release checklist](../RELEASE_CHECKLIST_v1.23.md) and
[trust boundary](PROVENANCE_AND_TRUST.md).
