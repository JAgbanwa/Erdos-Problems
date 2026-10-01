# Integrity records

`PACKAGE_MANIFEST.sha256` binds every public file in this Paper IV package,
except itself and its own checksum sidecar. Paths are relative to `PAPER_IV/`.
`PACKAGE_MANIFEST.sha256.sha256` binds the manifest. Ignored caches, compiled
Lean files and Python bytecode are not release artifacts.

`baseline/LEAN_CUT.json` independently binds every frozen source and the
original ZIP. The extracted tree is byte-identical to that cut, not a newer
working directory copied under an old audit name.

The manuscript hashes are also recorded in `SOURCE_TO_PUBLICATION.json`.
The package uses status **draft** and preserves manuscript revision **v0.8**.
No old local Paper IV version is an active publication artifact.

The manifest is generated only after the test results, logs and reports are
final. A later edit invalidates the package manifest and must be resealed.
