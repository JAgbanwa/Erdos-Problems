# Paper III — Lean 4 / Mathlib Formalization Report

*Deliverable per `ARISTOTLE_AGENT_INSTRUCTIONS.md` §6.* Machine-checked formalization of
*Linear-Error Clique Partitions of Split Graphs* (Erdős #81, Paper III), targeting
**Layer E sorry-free** and **Layer X = exactly the two named axioms AX1, AX2**.

Toolchain: Lean `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`. The whole library builds
(`lake build`, exit 0). Escape-hatch scan of the git object: the only `^axiom`
declarations are `AX1`, `AX2`; no `native_decide`, `admit`, `unsafe`, `opaque`.

## 1. Overall state — SORRY-FREE (2026-07-24)

- **The formalization is complete and `sorry`-free.** `lake build` = 8058 jobs, 0 errors,
  0 `sorry`s (verified on the git object). **All 25 ledger nodes are closed.** The trusted
  base is **exactly the two intended Layer-X axioms `AX1`, `AX2`** — no `sorryAx`, no
  `native_decide`, no `admit`, no third axiom anywhere.
- **Axiom footprint** (`#print axioms`, verbatim in `AXIOM_REPORT.txt`):
  - `Theorem_1_1`, `Corollary_1_2`, `E_8` → `[propext, Classical.choice, Quot.sound, AX1, AX2]`
  - `E_4_3` → `[propext, Classical.choice, Quot.sound, AX1]`
  - `E_7_1`, `Prop_10_1_low`, and all elementary lemmas → `[propext, Classical.choice, Quot.sound]`
- **M1 (audited algebraic heart)** — E-3.1, E-4.1, E-4.2 + finite LP-duality core
  (`lp_dual_bound_real`) — `sorry`-free, axiom-clean.
- **E-5 / Appendix D** — E-5.1/Cor 5.3/E-5.2; E-D.1/D.2/D.3 (kernel, Gale–Shapley,
  König/Galvin incl. `saturated_vertex_matching`) — `sorry`-free, axiom-clean.
- **§7.2 (E-7.1)** closed via three edge-disjoint triangle families `qqi_family`,
  `rrq_family`, `irq_family` (Galvin) + a coordinated edge-disjoint union.
- **§8 (E-8)** closed via KKI neighbourhood matchings (Dirac matching) + an `AX2`
  decomposition of the clique remainder, which is first made triangle-divisible
  (`E_8_Divisible`: parity via a Hamiltonian ordering + E-B; edge count ≡ 0 mod 3 via a
  short even cycle). Carries the ledger's `+O(n)` slack (the strict `Φ ≤ n²/6` is false —
  machine-checked disproof in `diagnostics/E_8_Disproof.lean`).
- **Prop 10.1 (low)** is unconditional (no axioms); **Theorem 1.1 / Corollary 1.2** are the
  full §9 minimal-counterexample assembly, relative to exactly `{AX1, AX2}`.
- **Reusable from-scratch additions not in Mathlib**: `DiracHamilton` (Hamiltonicity from
  min-degree) and `DiracMatching` (near-perfect matching from min-degree). Idiomatic,
  Mathlib-ready, self-contained drafts of both are in `PaperIII/Contrib/Submission/`
  (candidates to upstream; see that folder's README).

**Two findings this effort (both real, machine-checked):** (1) the Lean `E_8` had dropped the
ledger's `O(n)` slack, making an intermediate lemma false — corrected to match the ledger
(the main theorem's `+C·n` absorbs it); (2) the §8/`AX2` degree threshold requires the
very-sparse split at `12q < p` (not `10q < p`). Neither changes the public statements.

## 2. Node → status table

| Ledger node | Lean name | Status |
|-------------|-----------|--------|
| Infrastructure | `SplitGraph`, `graph`, `nu3/nu3Star/tau3Star`, `Phi`, `T`, `F`, `mu`, `rp` | ✅ sorry-free, axiom-clean |
| LP weak duality | `weak_duality`, `le_nu3Star_of_packing`, `tau3Star_le_of_cover`, `le_nu3_of_packing` | ✅ sorry-free, axiom-clean |
| Edge structure | `edgeFinset_eq`, `sum_edgeFinset`, `edgeCount_eq`, `triangle_cases` | ✅ sorry-free, axiom-clean |
| Identities | `T_key_identity`, `ineq_9_19`, `coeff_9_12/20`, `delta_ge_*`, `corridor_threshold` | ✅ sorry-free, axiom-clean |
| **E-3.1** (Thm 3.1) | `E_3_1` (`τ₃* = F`); `tau3Star_le_F`; `lp_dual_bound_real` | ✅ **sorry-free, axiom-clean** |
| **E-4.1** (Lem 4.1) | `E_4_1`; `Agg.class_bound` + 6 aggregation lemmas | ✅ **sorry-free, axiom-clean** |
| **E-4.2** (Thm 4.2) | `E_4_2`; `T_eq`; `F_branch_bound` (branches 1–3) | ✅ **sorry-free, axiom-clean** |
| **E-6.1** (Lem 6.1) | `E_6_1`, `dispersionV_eq` | ✅ sorry-free, axiom-clean |
| **E-B** (App B) | `pathCorrection_odd_iff` | ✅ sorry-free, axiom-clean |
| Factorization | `complete_graph_edge_coloring`, `exists_injection_ge_mean` | ✅ sorry-free, axiom-clean |
| **cp ≤ Φ** | `cp_le_Phi` (Cor 1.2 input) | ✅ sorry-free, axiom-clean |
| **E-D.1** (kernel) | `AppendixD.kernel_coloring` | ✅ sorry-free, axiom-clean |
| **E-D.2** (Gale–Shapley) | `AppendixD.gale_shapley` | ✅ sorry-free, axiom-clean |
| **E-D.3** (Galvin/König) | `konig_edge_coloring`, `galvin_max_degree`, `saturated_vertex_matching` | ✅ sorry-free, axiom-clean |
| **E-5.1** (Lem 5.1) | `E_5_1`, `cor_5_3` | ✅ sorry-free, axiom-clean |
| **E-5.2** (Lem 5.2) | `E_5_2` | ✅ sorry-free, axiom-clean |
| **E-7.1** (Lem 7.1) | `E_7_1` (via qqi/rrq/irq families) | ✅ **sorry-free, axiom-clean** |
| **E-8** (§8) | `E_8` (KKI matching + AX2 divisibility) | ✅ **sorry-free, `{AX1,AX2}`-relative** |
| **E-4.3** (bulk) | `E_4_3` | ✅ **sorry-free, `AX1`-relative** (no `sorryAx`) |
| **Prop 10.1 low** | `Prop_10_1_low` | ✅ **sorry-free, unconditional (no axioms)** |
| **Prop 10.1 mid** | `Prop_10_1_mid` | ✅ sorry-free, **no AX1/AX2** |
| **Theorem 1.1** (E-9) | `Theorem_1_1` | ✅ sorry-free, `{AX1,AX2}`-relative |
| **Corollary 1.2** | `Corollary_1_2` | ✅ sorry-free, `{AX1,AX2}`-relative |
| Addenda v0.9.1 | `Corollary_10_4`, `Corollary_10_4b`, `Corollary_12_2_bound` | Cor 10.4 ✅ clean; others assembled |

## 3. Remaining `sorry`s: NONE

The project is `sorry`-free (git-object scan: 0 matches for `\bsorry\b`). The two former
research-level residuals are now proved:
- `reserved_gain_packing_bound` (§7.2) — via `qqi_family` + `rrq_family` + `irq_family`
  (Galvin) and a coordinated edge-disjoint union (`E_7.lean`).
- the §8 core — via KKI neighbourhood matchings and an `AX2` decomposition of the
  triangle-divisible clique remainder (`E_8.lean`, `E_8_Core.lean`, `E_8_Divisible.lean`,
  `DiracHamilton.lean`, `DiracMatching.lean`).

## 4. `#print axioms` (headline results) — RELEASE GATE MET

See `AXIOM_REPORT.txt` for the verbatim output. Confirmed values:

- Elementary lemmas (`E_3_1`, `E_4_1`, `E_4_2`, `E_5_1`, `cor_5_3`, `E_5_2`, `E_6_1`,
  `E_7_1`, `cp_le_Phi`, `pathCorrection_odd_iff`, `konig_edge_coloring`, `galvin_max_degree`,
  `complete_graph_edge_coloring`, `clique_divisible_correction`) →
  `[propext, Classical.choice, Quot.sound]` (**no sorryAx, no AX1/AX2**).
- **`Prop_10_1_low` → `[propext, Classical.choice, Quot.sound]`** — fully unconditional.
- `Prop_10_1_mid` → `[propext, Classical.choice, Quot.sound]` (**no AX1/AX2, no sorryAx**).
- **`E_4_3` → `[propext, Classical.choice, Quot.sound, PaperIII.AX1]`** — relative to exactly `AX1`.
- **`Theorem_1_1`, `Corollary_1_2`, `E_8` →
  `[propext, Classical.choice, Quot.sound, PaperIII.AX1, PaperIII.AX2]`** — exactly the two
  intended Layer-X axioms, **no `sorryAx`**.

**Release gate (v1.0) — MET:** `#print axioms Theorem_1_1` =
`[propext, Classical.choice, Quot.sound, PaperIII.AX1, PaperIII.AX2]`, and
`#print axioms Prop_10_1_low` = `[propext, Classical.choice, Quot.sound]`.

## 5. Prose notes for the author (non-obvious Lean choices)

1. **`ν₃*` is formalized as the fractional COVER optimum `τ₃*`** (a `csInf`), not the
   packing `sSup`. Reason: Mathlib v4.28 has no finite LP **strong** duality / Farkas
   package, and the paper's §3–§4 arguments are all cover-side. Weak duality
   `ν₃* ≤ τ₃*` is proved (`nu3Star_le_tau3Star`); by classical LP duality they coincide.
   The two Layer-X axioms and the corridor all read consistently against `τ₃*`. *(Suggested
   manuscript sentence in §11.6: state that the machine perimeter uses the cover LP value,
   equal to the packing value by finite LP duality.)*
2. **Explicit small hypotheses.** E-3.1/E-4.x carry `p ≥ 3`, `q ≥ 1`, `d ≤ p` in Lean;
   the `q = 0` degenerate case of Corollary 10.4 (`H(p,0,d) = K_p`) is handled separately
   in the informal note (see editor note item 4).
3. **The 1-factorization `χ'(K_p)` is proved from scratch** (`complete_graph_edge_coloring`,
   round-robin), so it is **not** an axiom of the development — relevant to the §11.3
   "self-contained" wording (editor note item 1).
4. **`saturated_vertex_matching` is the true crux of König's theorem** (not a light
   lemma); the induction in `finite_bipartite_edge_coloring` depends on it, so it was
   proved independently (Hall / Δ-regular-extension style). It is now closed, so the whole
   Appendix D list-colouring chain is machine-verified.

## 6. Independent audit trail

Two audits complement (and are independent of) this formalization:
- `INTERNAL_AUDIT/` — 4 blocks (identities, common-profile LP, unified margin, corridor
  ILP), all PASS, hardened after external review; see `AUDIT_FINAL_REPORT.pdf`.
- `EXTERNAL_ADVERSARIAL_AUDIT_PACKAGE/` — package for an independent adversarial audit
  (Lean out of scope by instruction); the completed external audit returned
  `PASS_WITH_OBSERVATIONS`, 0 blocking/major findings, 0 counterexamples in ~2.55M
  instances.
