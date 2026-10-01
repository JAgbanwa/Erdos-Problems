# Frozen Lean source — draft v0.8

`lean_draft_freeze/` contains exactly the 479 entries declared by
`../04_integrity/baseline/LEAN_CUT.json`. No mathematical source was edited
during publication preparation. The original source-only archive is retained
as `LEAN_SOURCE_SNAPSHOT_v0.8.zip` with SHA-256:

```text
4f6ba1b40ace1d926ae5fab7490c4bc0dc3f236dea28640de4cee0166da60afa
```

The archive also preserves its original evidence directory. The extracted
tree and the archive therefore serve different practical roles: the tree is
convenient to build; the unchanged archive establishes continuity with the
reviewed v0.8 cut. Neither contains Mathlib binaries or a `.lake` cache.

See [reproduction instructions](../03_reproducibility/README.md) for commands,
toolchain, public theorem contracts and the distinction between the default
root, separate audit targets and supplementary library closures.

This is the sole active Paper IV freeze in the draft package. Exploratory
return archives and earlier working trees remain outside the publication.
