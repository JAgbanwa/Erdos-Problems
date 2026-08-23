# Paper III — Editor report: the Lean formalization and what it means for the preprint

**Purpose.** This report accompanies the machine-checked (Lean 4 / Mathlib) formalization of
Paper III (*Linear-Error Clique Partitions of Split Graphs*, Erdős #81). It is written for the
**editor** preparing a preprint that is *consistent with* the formal development. It states
exactly what was verified, the trusted assumptions, the findings that should shape the
manuscript's wording, a node-by-node status, and reproducibility instructions.

Toolchain: Lean `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`. One module per ledger node.

---

## 1. Executive summary

The formalization is **sorry-free**: `lake build` compiles the entire project (8057 build
jobs) with **zero errors and zero `sorry`s**. The complete theorem is machine-verified
**relative to exactly two explicitly declared axioms** — the "Layer X" external inputs the
paper itself cites as black boxes:

- **AX1** — Haxell–Rödl / Yuster: the fractional–integral triangle-packing gap is `o(n²)`.
- **AX2** — Dross + Barber–Kühn–Lo–Osthus: triangle-divisible graphs of minimum degree
  `≥ (0.9+ε)n` admit an exact triangle decomposition.

Kernel-verified axiom footprint (`#print axioms`, verbatim):

| Result | Axioms |
|---|---|
| `Theorem_1_1` (main), `Corollary_1_2`, `E_8` | `propext, Classical.choice, Quot.sound, AX1, AX2` |
| `E_4_3` (bulk regime) | `propext, Classical.choice, Quot.sound, AX1` |
| `E_7_1`, `Prop_10_1_low`, and all elementary lemmas | `propext, Classical.choice, Quot.sound` |

`propext, Classical.choice, Quot.sound` are Lean's standard logical foundations (classical
logic + quotients), present in essentially every Mathlib theorem. **No `sorryAx`, no
`native_decide`, no `admit`, no third axiom appears anywhere.** The only two `axiom`
declarations in the entire project are AX1 and AX2.

**What this licenses the preprint to claim:** *"Theorem 1.1 has been formally verified in Lean
4/Mathlib, modulo two named published results (Haxell–Rödl/Yuster and Dross–BKLO) that are
taken as hypotheses; every other step — including all classical graph theory used — is proved
from first principles and checked by Lean's kernel."*

---

## 2. Findings that should shape the preprint

The formalization surfaced several precise points. The first two are **mathematical** and
should be reflected in the manuscript; the rest are presentational.

### 2.1 (Important) The §8 bound MUST carry the additive `O(n)` slack — the strict form is false
`LEDGER.md` and the paper state E-8 as `Φ(G) ≤ n²/6 + O(n)`. This `O(n)` is **not cosmetic**:
the strict form `Φ(G) ≤ n²/6` is **false**, and we have a machine-checked disproof
(`diagnostics/E_8_Disproof.lean`). Concretely, at `q = 0` the split graph degenerates to the
clique `K_p`; for `p ≡ 0 (mod 6)` the maximum *integral* triangle packing leaves a perfect
matching, so
```
    ν₃(K_p) = (C(p,2) − p/2)/3,   Φ(K_p) = C(p,2) − 2ν₃(K_p) = n²/6 + p/6  >  n²/6.
```
This is a genuine integral-packing obstruction (a *fractional* packing has no defect). **Action
for the editor:** ensure no intermediate statement in the manuscript asserts a *strict*
`Φ ≤ n²/6` in a regime that includes near-clique cases; keep the `+O(n)` (the paper's
minimal-counterexample argument, taking the linear-error constant `k → ∞`, is precisely what
absorbs it — so the main theorem is unaffected and correct).

### 2.2 (Important) The very-sparse regime must be sparse enough for AX2's degree threshold
To apply AX2 (min degree `≥ (0.9+ε)p`) to the clique remainder after reserving the KKI
matchings, the remainder's minimum degree is `p − 1 − q`. The formalization therefore uses the
very-sparse regime `q < p/12` (so `δ(remainder) ≥ (11/12)p ≥ (0.9+ε)p`), with the
complementary regime `α = q/p ≥ 1/12` handled by the bulk bound E-4.3. The paper's asymptotic
`q = o(p)` is fully consistent with this; the preprint may optionally note that the split
between "sparse (AX2)" and "bulk (AX1)" is placed where the remainder still meets AX2's degree
hypothesis. (In Lean this is an internal constant `12`; the public statement is unchanged.)

### 2.3 (Presentational) `ν₃*` is realized as the cover optimum `τ₃*`
Mathlib v4.28 has no finite-LP strong-duality / Farkas package, and the paper's §3–§4 arguments
are cover-side. So the formalization defines the fractional optimum as the LP **cover** value
`τ₃*` (a `csInf`); weak duality `ν₃* ≤ τ₃*` is proved, and by classical finite LP duality the
two coincide. **Suggested manuscript sentence (§11.6):** state that the machine-checked
perimeter uses the cover LP value, equal to the packing value by finite LP duality.

### 2.4 (Presentational) Precise statement of external inputs — only AX1 and AX2
A prior manuscript remark (≈§11.3) to the effect of "using no external theorem" over-reaches
and should be tightened. The formalization proves **from scratch**, sorry-free, all the
classical graph theory the proof uses — including the `χ'(K_p)` 1-factorization, König/Galvin
list-edge-colouring (Appendix D), **Dirac's Hamiltonicity theorem**, and a **near-perfect
matching-from-minimum-degree** theorem (the last two are not even in Mathlib; see §5).
**Recommended wording:** *"The argument relies on exactly two external results, both cited:
AX1 (Haxell–Rödl/Yuster) and AX2 (Dross–BKLO). All other ingredients, including classical
theorems of Dirac, König/Galvin, and the 1-factorization of complete graphs, are proved from
first principles within the formalization."*

### 2.5 (Insight) The formalization caught a real error
Point 2.1 is worth foregrounding as a *strength*: the process of formalizing forced discovery
(and machine-checked confirmation) of a statement-level error in an intermediate lemma (a
dropped `O(n)`), which was then corrected to match the ledger. This is concrete evidence of the
verification's value beyond a rubber stamp.

---

## 3. Node-by-node status (all sorry-free)

| Ledger node | Lean name | Axioms beyond the standard triple |
|---|---|---|
| Infrastructure, weak LP duality, counting, identities | Defs/Duality/Counting/Identities | — |
| **E-3.1** (Thm 3.1, `τ₃*=F`) incl. finite LP dual | `E_3_1` | — |
| **E-4.1** (Lem 4.1), **E-4.2** (Thm 4.2) | `E_4_1`, `E_4_2` | — |
| **E-5.1 / Cor 5.3 / E-5.2** | `E_5_1`, `cor_5_3`, `E_5_2` | — |
| **E-6.1** (Lem 6.1) | `E_6_1` | — |
| **E-B** (App. B parity) | `pathCorrection_odd_iff` | — |
| Factorization `χ'(K_p)` (round-robin) | `complete_graph_edge_coloring` | — |
| **E-D.1/D.2/D.3** (kernel, Gale–Shapley, König/Galvin) | `AppendixD.*` | — |
| **E-7.1** (Lem 7.1, §7.2 three families) | `E_7_1` | — |
| **Prop 10.1 (low)** | `Prop_10_1_low` | — (unconditional) |
| **E-4.3** (bulk) | `E_4_3` | AX1 |
| **E-8** (§8 sparse, incl. divisibility correction) | `E_8` | AX1, AX2 |
| **Theorem 1.1** (E-9) | `Theorem_1_1` | AX1, AX2 |
| **Corollary 1.2** | `Corollary_1_2` | AX1, AX2 |

§7.2 (E-7.1) is closed via three edge-disjoint triangle families — `qqi_family` (QQI averaged),
`rrq_family` (RRQ factorisation), `irq_family` (IRQ reserved gain, via Galvin) — combined with a
coordinated edge-disjointness argument. §8 (E-8) is closed via KKI neighbourhood matchings
(Dirac matching) plus an AX2 decomposition of the clique remainder, which is first made
triangle-divisible (even degrees via a Hamiltonian ordering and the E-B path correction; edge
count `≡ 0 mod 3` via a short even cycle in the dense remainder).

---

## 4. The two axioms, verbatim (for the citations section)

```
axiom AX1 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V) (G : SimpleGraph V), n₀ ≤ card V →
              τ₃*(G) − ν₃(G) ≤ ε · (card V)²
axiom AX2 : ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ (V) (H : SimpleGraph V),
              |E(H)| ≡ 0 mod 3  →  (∀ v, Even (deg v))  →  n₀ ≤ card V  →
              (0.9+ε)·card V ≤ δ(H)  →  H has an exact triangle decomposition
```
- AX1 ↔ P. Haxell, V. Rödl / R. Yuster, on the fractional-vs-integral triangle packing gap.
- AX2 ↔ F. Dross; and B. Barber, D. Kühn, A. Lo, D. Osthus, on triangle decompositions of
  dense triangle-divisible graphs (iterative absorption).

Both are faithful to the cited literature and are used *only* where the paper cites them
(AX1 in the bulk §4.3/§9.1; AX2 in the sparse §8).

---

## 5. Reusable by-products (possible Mathlib contributions; may be cited)

The formalization proves two classical theorems **absent from Mathlib**, from scratch and
axiom-clean:
- **Dirac's theorem** (a graph on `n ≥ 3` vertices with `δ ≥ n/2` has a Hamiltonian cycle/path),
  by the rotation–extension argument.
- **Near-perfect matching from minimum degree** (`δ ≥ n/2 ⇒` matching covering all but ≤ 1
  vertex), via Tutte's theorem + an apex reduction.
Idiomatic, Mathlib-conventional drafts of both have been prepared (`PaperIII/Contrib/`) and are
candidates to upstream to Mathlib. The preprint may note in passing that the formalization
contributes these lemmas.

---

## 6. Reproducibility

```
cd lean
lake exe cache get          # fetch Mathlib oleans
lake build                  # 8057 jobs; expect 0 errors, 0 sorries
```
Axiom check (any result), e.g.:
```
echo 'import PaperIII' > gate.lean
echo 'open PaperIII'  >> gate.lean
echo '#print axioms Theorem_1_1' >> gate.lean
lake env lean gate.lean     # ⇒ [propext, Classical.choice, Quot.sound, AX1, AX2]
```
Escape-hatch scan of the git object (only AX1/AX2 should match `^axiom`, nothing should match
`sorry`/`native_decide`/`admit`):
```
git grep -nE "^axiom |native_decide|\badmit\b" HEAD -- 'lean/PaperIII/*.lean'
git grep -c -w sorry HEAD -- 'lean/PaperIII/*.lean'
```

## 7. Supporting files in this repository
- `AXIOM_REPORT.txt` — verbatim `#print axioms` output.
- `diagnostics/E_8_Disproof.lean` — machine-checked disproof of the strict (no-slack) E-8.
- `diagnostics/FINDING_E8_statement_too_strong.md` — write-up of finding 2.1.
- `FORMALIZATION_REPORT.md` — the developer-facing node report.
- `PAPER_III_LEAN_HANDOFF_for_Paper5.md` — handoff for the follow-on (chordal) programme.
