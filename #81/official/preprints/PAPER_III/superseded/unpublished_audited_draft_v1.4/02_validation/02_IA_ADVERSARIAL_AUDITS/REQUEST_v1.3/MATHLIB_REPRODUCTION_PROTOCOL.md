# Optimized Mathlib reproduction protocol — Paper III v1.3

## Objective

Rebuild every Paper III project source in a short clean room while avoiding an unnecessary rebuild or repeated download of unchanged Mathlib dependencies. The dependency cache must be auditor-controlled and independently verified. No compiled Paper III artifact may be reused.

## Required immutable state

- Lean toolchain: `leanprover/lean4:v4.28.0`
- Mathlib tag/input revision: `v4.28.0`
- Mathlib exact commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`
- Formal ZIP SHA-256: `2eb0ff20a9dae6610a46026355374570d5afdfea89837ea7f9dd29da10b9d300`

The supplied `lake-manifest.json` pins Mathlib and all inherited packages. Preserve it byte-for-byte. Do not run `lake update` in the recommended cached path.

## Recommended Windows procedure

1. Use a short path, for example `C:\ea\P3`, to avoid Windows path-length failures.
2. Verify the formal ZIP hash, then extract it into that clean directory.
3. Confirm `lean --version`, `lake --version`, `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` before creating `.lake` state.
4. Populate `.lake/packages` from an auditor-controlled checkout/cache whose revisions match the supplied manifest. A directory junction to that verified package cache is acceptable if recorded. Do not use the author's candidate `.lake/build` or any author-built Paper III `.olean`/`.ilean` files.
5. At minimum execute and retain:

   ```powershell
   git -C .lake\packages\mathlib rev-parse HEAD
   git -C .lake\packages\mathlib status --porcelain
   ```

   The first output must be `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; the second must be empty. Verify the exact revision of every other manifest dependency as well.
6. Run `lake exe cache get` so Mathlib's official binary cache supplies dependency artifacts. Record its output and exit code. This cache is permitted because Mathlib is a pinned dependency, not the audited project.
7. Prove that the target project build is clean: `.lake/build` must be absent or empty immediately before the build. Record a recursive listing or hash inventory. Never import an author-supplied project `.lake/build`.
8. Run:

   ```powershell
   lake build PaperIII
   ```

   Record stdout, stderr, exit code, duration, CPU/RAM context, and final job count.
9. Independently run each query:

   ```powershell
   lake env lean FreezeAxioms.lean
   lake env lean FreezeAxiomsAuditClosure.lean
   lake env lean FreezeAxiomsAX1.lean
   lake env lean FreezeAxiomsAX1Closure.lean
   lake env lean FreezeAxiomsAX2.lean
   lake env lean FreezeAxiomsByproducts.lean
   lake env lean FreezeAxiomsCanonical.lean
   lake env lean FreezeAxiomsObstructions.lean
   ```

10. Search the extracted source and import closure for forbidden escape hatches and project-local axioms. Retain exact commands and results.

## Fallback when no verified dependency cache exists

A one-time dependency checkout is allowed. Use the supplied manifest, a short path, and the exact toolchain; then fetch the official Mathlib cache. Record every network command and revision. A network failure is an environmental `INCONCLUSIVE`, not a defect in the paper, unless the package's pins or metadata caused it.

## Claim boundary

The resulting evidence supports: “Paper III was rebuilt cleanly from its frozen project sources against the exact pinned Mathlib sources and official compiled dependency cache.” It does **not** support: “Mathlib itself was rebuilt from source.”

This optimization must not weaken independent verification of dependency commits, project-source cleanliness, import closure, axiom footprints, or manuscript-to-Lean conformance.
