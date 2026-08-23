# Paper III v1.4 Mathlib reproduction protocol

## Claim boundary

The protocol checks the Paper III project against the nine dependency revisions
already pinned in `lake-manifest.json`. `lake exe cache get` may obtain official
precompiled Mathlib artifacts. The protocol does not claim to rebuild Mathlib
from source.

## Clean-state boundary

The delivered `PROJECT/` contains sources and lockfiles only. Before invoking
Lake, the runner must record:

- no `.lake` directory in the copied project;
- no project `.olean`, `.ilean`, `.o`, `.c`, `.bc`, `.dll`, `.so` or `.dylib`;
- hashes of `lakefile.toml`, `lake-manifest.json` and `lean-toolchain`.

After `lake exe cache get`, the runner must again confirm that no project
`.lake/build` exists. Dependency checkouts under `.lake/packages` are expected.

## Build sequence

The first and only clean project build is:

```powershell
lake build PaperIII
```

Because `PaperIII.lean` explicitly imports `PaperIII.Theorem_1_1_Final` and
`PaperIII.PublicAPI`, this command must compile the headline theorem and public
API. Their object files are mandatory postconditions.

The following command is then incremental and completes every root needed by
the axiom queries:

```powershell
lake build BKLO.MainDenseUnconditional Nibble.AX1Closed `
  PaperIII.CanonicalTrianglePacking PaperIII.Obstructions `
  PaperIII.PaperImprovementsGate PaperIII.PublicAPI `
  PaperIII.Theorem_1_1_Final
```

## Axiom sequence

Run with `lake env lean`, independently and with a separate log:

1. `FreezeAxioms.lean`
2. `FreezeAxiomsAuditClosure.lean`
3. `FreezeAxiomsAX1.lean`
4. `FreezeAxiomsAX1Closure.lean`
5. `FreezeAxiomsAX2.lean`
6. `FreezeAxiomsByproducts.lean`
7. `FreezeAxiomsCanonical.lean`
8. `FreezeAxiomsObstructions.lean`

The combined output must contain exactly 42 `depends on axioms` reports. Every
reported axiom must be one of `propext`, `Classical.choice`, or `Quot.sound`.
The output must contain no `sorryAx`, and it must include the headline surface
`PaperIII.Theorem_1_1`.

## Import-closure sequence

The runner constructs the project import graph directly from the delivered
`.lean` files. It must establish:

- `PaperIII` reaches `PaperIII.Theorem_1_1_Final`;
- `PaperIII` reaches `PaperIII.PublicAPI`;
- `PaperIII.PublicAPI` reaches `PaperIII.Theorem_1_1_Final`;
- neither `Ax2.PartA.Wlog` nor `Ax2.PartB.Axioms` is reachable from any
  canonical build/query root.

## Acceptance

The run is PASS only if every command exits 0, all hashes and dependency
revisions remain fixed, all 42 axiom reports pass the whitelist, and every
import-closure assertion holds. A successful root build without these
postconditions is not a PASS.

