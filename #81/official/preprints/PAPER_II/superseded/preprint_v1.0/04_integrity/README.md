# Integrity

- `SHA256SUMS.txt` -- SHA-256 of every released file (paths relative to the
  package root).
- `RELEASE_MANIFEST.json` -- structured manifest of the release.
- `PROVENANCE.md` -- how the release artifacts were produced and verified.

Verify from the package root:

```bash
sha256sum -c 04_integrity/SHA256SUM