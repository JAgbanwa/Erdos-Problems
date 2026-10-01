# Gate E7 report — run_v1.2_r1 (Paper IV v1.2)

Verdict: **PASS with MINOR findings**. Evidence directory: `20_EVIDENCE/E7/`.

---

## E7 (attribution / literature) — first pass

Target: `01_manuscript/v1.2_full_rebuild_candidate/PAPER_IV_preprint_v1.2_en.md`, sha256 `a501d53b527da22f20112db2b05917fb61f46dd8e080faf14b69349b240cc152` (2464 lines). Audit date 2026-09-30. Labels: **SV** = SOURCE_VERIFIED (read in the saved source), **AI** = AUDITOR_INFERENCE, **UV** = UNVERIFIED. Line numbers refer to the manuscript unless prefixed by a source. Page numbers for [15] are those printed in arXiv:2609.20871v1. Quotes from sources are kept under 15 words; everything else is paraphrase.

## 0. Sources and later-version status

| Ref | URL | Version retrieved | Source date | sha256 (saved file) |
|---|---|---|---|---|
| [15] | https://arxiv.org/pdf/2609.20871v1 | v1 (cited) | 15 Sep 2026 | `9654af66…d5fa53` (okechukwu_v1.pdf) |
| [15] abs | https://arxiv.org/abs/2609.20871 | abs page | — | `e1ce80ea…b1b0` |
| [22] | https://arxiv.org/pdf/1902.06135v1 | v1 (cited) | 16 Feb 2019 | `df77c1d9…6934` (verclos_v1.pdf) |
| [22] abs | https://arxiv.org/abs/1902.06135 | abs page | — | `af8ac080…a1b0` |
| [5] PDF | raw.githubusercontent …/cbde8a0a…/manuscript/main.pdf | commit cbde8a0a | printed 8 Sep 2026 | `53e15161…3930` |
| [5] README / FORMALIZATION_STATUS | raw …/cbde8a0a…/README.md, lean/FORMALIZATION_STATUS.md | commit cbde8a0a | 2026-09-08 | `0e08ab41…0b30b` / `05cceb10…93f4` |
| [8] | https://www.erdosproblems.com/81 | live, 2026-09-30 | page last edited 28 Dec 2025 | `a02ca0e2…2543` |
| [21] | https://www.erdosproblems.com/forum/thread/81/proof-claims | live, 2026-09-30 | claim 201 dated 2026-08-10 | `69d52613…b329` |
| [23] | Crossref for 10.1137/06064888X | metadata | 2008 | `08dfd5ad…87cb` |

Full list with URLs and retrieval times: `SOURCES_SHA256.txt`. Queries: `SEARCH_LOG.md`.

Later-version status as of 2026-09-30 (SV):
- [15]: the arXiv submission history lists only v1 (15 Sep 2026 16:25:32 UTC), 24 pages, with no journal reference.
- [22]: the history lists only v1 (16 Feb 2019), with no journal reference or DOI. Crossref and web search found no journal version (UV that none exists; the dblp query failed).
- [5]: `main` HEAD is still `cbde8a0a` (committed 2026-09-08T10:47:29Z; repo pushed_at 2026-09-08T12:53:39Z). Tag `v0.1.0-proof-claim` points to the same commit. The only other branch is `codex/revise-manuscript-lean-audit` at 9944194c, an ancestor merged via PR #1. `manuscript/main.pdf` has the same sha256 at the cited commit, at `main` and in the release asset digest. **Nothing has changed since the cited commit.**
- [8]: Problem #81 is still marked **OPEN** on the site.

## A. Theorem C (l.82–97) vs [15, Theorem 1.1] — component table

| Component | [15] v1 (SV, p.1–2, 5–6, 19–20) | Manuscript v1.2 | Verdict |
|---|---|---|---|
| Graph class | s-simplicial: d(v) − ω(N(v)) ≤ s. rsd(G) is the least s such that, in every induced H and outside every proper clique of H, there is an s-simplicial vertex. "The empty clique is allowed." (p.2) | l.84: in every induced U, outside every prescribed clique R ⊊ U, some vertex's neighbourhood contains a clique omitting ≤ s neighbours. The empty root is allowed and the definition is credited to [15, §1]. | OK (equivalent formulation, attributed) |
| Target | F_n = ⌊n(n+1)/6⌋, Q_s(n) = F_{n+s} − C(s+1,2) (1.1) | Q_s(n) = M(n+s) − C(s+1,2), with notation credited to [15,(1.1)] (l.84, l.90) | OK |
| Quantifiers | ∀s ∃K_s ≥ 0, N_s. The bound cp ≤ Q_s + K_s holds at **all** orders; for n ≥ N_s the maximum is exactly Q_s(n). | ∀s ∃N_s ∀n ≥ N_s: cp ≤ c_4 ≤ Q_s(n). Eventual only. | OK. The eventual scope is stated; the all-orders clause is covered in §8.1 (see G). |
| Piece size | Statement is for cp only. The explicit constructions (Lemma 2.5, Lemmas 4.1–4.3, (5.11)) use only edges and triangles. Lemma 4.2 is stated for q_3. | c_4 (pieces of order ≤ 4) | See A.2. The stated strengthening is literally correct. |
| Attainment | Lemma 2.5, at every sufficiently large order | l.93: attainment for each sufficiently large order, also for unrestricted cp | OK. Credited at l.97. |
| Extremal classification | Equality holds exactly for (K_{k−s} ⊔ K̄_s) ∨ K̄_{n−k}, with k nearest to (2(n+s)+1)/6 (1.3). Complement bars confirmed visually from the rendered p.2. | (6.18): cp = Q_s ⟺ c_4 = Q_s ⟺ G ≅ (K_{k−s} ⊔ I_s) ∨ I_{n−k}, same k (l.1001–1004) | OK. Same family, credited at l.97 and l.1014. |
| Witness family | book graphs (K_{k−s} ⊔ K̄_s) ∨ K̄_b | same (Appendix E witness) | OK |
| Constants | K_s, N_s existential | N_s explicit (tower, Cor. 6.6) | OK, no overclaim (l.1126) |

### A.1 Role of the cutoff L in [15] (SV)
- **§3 (p.6).** L ≥ 3 is fixed and q_L and q_L^* are defined. Lemma 3.1 requires L ≥ 4. Its final assertion is q_L^* ≤ M_n + n·rsd(G).
- **Theorem 3.3 (p.8–9).** For every ε, it produces an integer L ≥ 4 and constants. In the proof, ξ is chosen first and then L, so that 33(ξ + 1/[2(L−1)]) < ε/4. Hence L grows as ε → 0.
- **Lemma 3.4 (p.10).** For every fixed L and ζ > 0, q_L ≤ q_L^* + ζ|G|² for all sufficiently large graphs. The proof bundles templates J and uses Haxell–Rödl/Yuster.
- **Proof of Theorem 1.3 (p.11).** L, δ_0, η_0 are taken from Theorem 3.3 ("The cutoff L is now fixed."). Lemma 3.4 is then applied with error η_0 n²/2. Its role is to turn a lower bound on cp (through q_L ≥ cp) into a lower bound on q_L^*.
- **Proposition 5.4 (p.17) and Theorem 1.1 (p.19).** Prop. 5.4 calls Theorem 1.3 to obtain the cliques needed by Lemma 5.1. Theorem 1.1 uses Prop. 5.4 in a smallest-counterexample argument. L appears nowhere else.
- **(1.5), p.11.** The source says to "use L = 4 in Lemmas 3.1 and 3.4". This is the only place where L = 4 is chosen.
- **Verdict on l.1255.** The statement is **accurate** (SV): Theorem 3.3 chooses L from the accuracy; Prop. 5.4 and Theorem 1.1 reach it through Theorem 1.3 and Lemma 3.4; and L = 4 is used only for (1.5).

### A.2 Is the order-four strengthening trivially available from [15]? (AI)
- **What [15] proves literally.** It proves cp ≤ Q_s(n) for n ≥ N_s and states no bound on c_4 or q_L for non-extremal graphs. In its near-extremal regime (hypotheses of Prop. 5.4: δ(G) ≥ n/3 − o(n) and cp ≥ Q_s), the construction (5.11) goes through Lemma 4.2, whose conclusion is a q_3 bound. Graphs with cp < Q_s(n) get no constructive treatment: the smallest-counterexample argument only needs the value of cp.
- **Why simple substitution fails.** Running the §5.4 argument with c_4 in place of cp would need Theorem 1.3 under a c_4 (= q_4) lower-bound hypothesis. Lemma 3.4 with L = 4 then bounds q_4^* from below. Theorem 3.3, however, needs a lower bound on q_L^* for a large L = L(ε), and q_L^* ≤ q_4^* goes the wrong way. So the literal chain does not give c_4 ≤ Q_s by substitution.
- **Limit of this finding.** This is a statement about the literal chain only, not a claim that [15]'s method cannot be adapted. The manuscript makes the same disclaimer at l.1245 and l.1255.
- **Verdict.** Calling Theorem C an order-four strengthening of the *stated* bound (l.95, l.1255) is **OK**.

### A.3 Mechanism description of [15] in Table 4 / l.1210 and l.1257 — **MINOR** (AI, grounded in SV reading)
- **What the manuscript says.** Table 4 gives [15]'s positive-gain pieces as "K_3,…,K_L in the far transfer", with "cp, via q_L in that branch". Line 1257 says Lemma 3.4 "pays the budget when ζn² ≤ M(n) − q_L^*(G)" and "is used in the branch with the corresponding margin".
- **What [15] actually does.** The proof of Theorem 1.1 has no far-regime branch in which a margin pays for a transfer loss. Lemma 3.4 enters only inside localization (proof of Thm 1.3), where it converts cp ≥ n²/6 − o(n²) into a lower bound on q_L^*. The one place it serves as an upper bound is (1.5), with L = 4. The explicit partitions [15] builds for Theorem 1.1 use only K_2 and K_3.
- **Why it matters.** The table therefore gives [15] an architecture it does not have. A reader could infer that [15]'s partitions use large cliques. This does not affect priority claims, and it arguably understates [15].
- **Recommendation.** Rewrite Table 4's [15] row and l.1257 to say that Lemma 3.4 is used for localization and for (1.5). Also say that the near-extremal constructions in [15] are edge/triangle constructions.

## B. Checks of cited items of [15]

| Manuscript claim | [15] v1 (SV) | Verdict |
|---|---|---|
| [15, Cor 1.2] is the chordal case (l.43); optimal cores nearest to (2n+1)/6 (l.1263) | Cor 1.2, p.2: cp ≤ F_n + O(1); eventual max F_n; equality exactly K_k ∨ K̄_{n−k}, k nearest to (2n+1)/6 | OK |
| [15, Thm 1.3] structural sequence result (l.43, l.1261) | Thm 1.3, p.4: rsd = o(n), cp ≥ n²/6 − o(n²) give cliques A_j with ‖A_j‖ = n/3 + o(n) and D_A + e(G−A) = o(n²); plus (1.5) | OK |
| [15, Cor 5.5] qualitative edit stability (l.43, l.1259) | Cor 5.5, p.20: for fixed s and ε, there are δ, N such that cp ≥ Q_s − δn² gives ≤ εn² edits to form (1.3). Qualitative. | OK |
| [15, Lemma 3.1] signed-star argument (l.45, l.1070, F.2 l.2150) | Lemma 3.1, p.7 (§3.1 "A maximal positive clique-star"). The manuscript's (F.2) rows, the α = 5c/12 split and the envelope c(5n−4c−1)/12 match [15] p.7–8. The manuscript adds the capped exception charge Σ min(s,j). | OK, adequately attributed ("cited as a method", l.1070) |
| [15, Lemma 3.4] q_L ≤ q_L^* + ζn² (l.1257); exact fractional partition ⟺ gain model | Lemma 3.4, p.10, including the "equivalently a fractional packing" remark in its proof | OK for the statement; mechanism framing MINOR (A.3) |
| [15, Theorem 3.3] n/6 + 1/24 term (l.1263) | p.9: ϱ ≤ (δ_0+η_0)n² + n/6 + 1/24 | OK |
| [15, §7] quantitative version of Cor 5.5 (l.1259) | §7, p.23: asks for the optimal dependence of edits on Q_s(n) − cp(G), n and s. Notes that the proof gives only qualitative stability. | OK |
| Table 6 (l.1249–1251): signed dual Thm 3.3; Haxell–Rödl + joint templates Lemma 3.4; list colouring + exceptions §§4–5 | Thm 3.3 uses the signed dual; Lemma 3.4 uses bundled templates J with Haxell–Rödl/Yuster; §4 uses Galvin's list-edge-colouring theorem and §5 a bounded exceptional set | OK |
| Order-three obstruction (Prop D.2, l.95, l.1748–1761) | Neither [15] nor [5] makes any claim about global order-3 sufficiency or insufficiency. [15]'s near-extremal constructions are order ≤ 3 (Lemma 4.2 is a q_3 bound). [5] builds a K_2/K_3 partition near the extremal family ((5.8): cp≤3 ≤ M(n)) and needs K_4 only through the fractional far functional (p.2 remark on complete graphs). | OK. No contradiction. The manuscript restricts the claim to s = 0 and uniformity (l.95). |

## C. Theorem C′ / Cor 6.3 / Prop 6.3a / Prop 6.4 / Thm 6.5 vs [15] — component table

| Aspect | [15] | Manuscript | Verdict |
|---|---|---|---|
| Defect regime | Cor 5.5: fixed s. Thm 1.3: rsd = o(n). | C′ / Cor 6.3: fixed s. Thm 6.5: s_j = o(n_j). | Parallel structure, correctly matched |
| Near-extremality hypothesis | on cp | on c_4 (c_4 ≥ Q_s − δ). This is implied by the cp hypothesis, so it is a **weaker** hypothesis and a stronger theorem. | See C.1 |
| Quantitative vs qualitative | Cor 5.5 qualitative (ε, δ); §7 explicitly says there is no rate | d_E ≤ A_sδ (non-optimal core) and d_E ≤ A_sδ + n√((1+4A_s)δ) (optimal size, 6.17); explicit γ_s, N_s^stab | Positioning as a "quantitative form" of Cor 5.5 (l.43, which explicitly includes Cor 6.3) is accurate |
| Square-root lower scale | none | Prop 6.3a family | No conflict with [15] |
| Partition control | [15] contains **no** statement about the structure of near-optimal partitions (whole text read) | (6.13), (6.26): one root controls all partitions | "adds simultaneous partition control" (l.43, l.1261) accurate |
| Linear / quantitative stability in [15]? | None. The only quantitative objects are Lemma 3.1 / (1.5) and Thm 6.2 (finite signed bound). | — | Manuscript does not misstate [15] here |
| Thm 1.3 vs Thm 6.5 | cliques A_j, ‖A_j‖ = n/3 + o(n), D_A + e(G−A) = o(n²) | R_j, ‖R_j‖ = n/3 + o(n), d_E(G_j, S_{R_j}) = o(n²), with weaker c_4 hypothesis | "recovers the structural conclusion" accurate |
| (1.5) vs Prop 6.4 + (6.24) | Stated for cp: (2n+1)²/24 + n·rsd + ϵ(n)n² for every n ≥ 8, with ϵ(n) → 0 graph-independent. Its proof uses L = 4 in Lemmas 3.1 and 3.4, so it proves a q_4 = c_4 bound. | c_4 ≤ M(n−s) + ns (−C(s+1,2) on 4s ≤ n) + εn², with N(ε) independent of G and s. Leading s-term ≈ 2ns/3 vs ns. | See C.2 |

### C.1 Wording error at l.1259 — **MINOR** (AI)
- **The wording.** Line 1259 calls the c_4 near-extremality hypothesis "the stronger near-extremality hypothesis on c_4". It then says the result also applies when the hypothesis is stated for cp, since cp ≤ c_4.
- **Why it is wrong.** The hypothesis c_4 ≥ Q_s − δ is implied by cp ≥ Q_s − δ, so it is the weaker hypothesis. The sentence contradicts itself.
- **Fix.** Replace "stronger" by "weaker" or "c_4-form of the".

### C.2 "order-four version of its approximation (1.5)" (l.1261) — **MINOR** (AI grounded in SV p.11)
- **Why the phrase overstates.** [15] states (1.5) for cp, but its one-line proof already uses L = 4, so it literally yields a q_4 bound. The manuscript itself acknowledges this at l.1255.
- **Fix.** Describe the contribution as a refined finite-order and s-dependence form of (1.5), noting that [15]'s proof of (1.5) already works with L = 4.

## D. [22] de Joannis de Verclos (SV unless noted)
- **What [22] proves.** Theorem 1 (p.2): chordality is testable with query complexity O(ε^{-37}), i.e. polynomial ("easily testable"). The contrapositive is a polynomial removal-type statement. The manuscript's wording "polynomial chordal-removal development" (l.1138) is fair (AI).
- **Lemma 3 (p.3).** It assumes ε > 0 and n ≥ ε^{-1}, and concludes that G is 6ε^{1/2}-close to chordal. The manuscript (F.10, l.2287) says constant 8 instead of 6, with no n ≥ 1/ε condition, and "neither uniformly stronger". This matches. **OK**
- **Lemma 4 (p.3).** It is the Gyárfás–Hubenko–Solymosi large-clique lemma, cited within [22]. Line 2280 says the manuscript "replaces the use of [22, Lemma 4]" and "is not presented as a new version of the full theorem cited there". **OK.** The manuscript could name GHS explicitly; optional.
- **Lemma 11 (p.10–14).** It concerns pinned chordal graphs, with T having at most k leaves and m11 = 2^40 ε^{-4} k^6 ln^4 k. Its proof has three parts that match the manuscript's three cases:
  - Claim 3: every colouring has ≥ δn² conflicts, so Theorem 2 (set colouring) applies. This is l11_caseA.
  - Claim 5: a section G[L_i,R_i] far from M2-free gives an induced C4 w.p. ≥ 1/2. This is l11_caseB1 / claim5_count.
  - Claim 6 and the gluing construction: F chordal and |E(F)△E(G)| ≤ δn² + (ε/2)n² ≤ εn². This is l11_caseB2 / (F.12).

  The manuscript's attribution ("retain their roles from the removal strategy of [22]"; no claim that the published Lemma 11 has the modified statement, l.2341) is **accurate**.
- **Table 10 (l.2291–2300).** Four claims were checked against [22]:
  - [22]'s pinned representation is on the fixed tree T (Definition 2, p.9), so "enlarged class" with a path-preserving map is a correct description of a change.
  - Lemma 11's Claim 1 (gate set of size ≤ 3k built from leaves) is correctly identified as "not imported".
  - Theorem 2 has m2 = 36k ln(max|L_u|)ε^{-2}, matching "published logarithmic bounds".
  - The manuscript's m11 = ⌈2^58(K+1)^15/ε^12⌉ is larger than [22]'s. The manuscript says so (l.2300).

  **OK**
- **Journal version.** None found (UV). The citation to arXiv v1 is correct and current.
- **Overall verdict D: OK.** The description of [22] is accurate.

## E. [5] (N0zoM1z0/erdos-81 @ cbde8a0a)
- **Eventual chordal maximum.** SV, [5] p.2 and p.15: Theorem 1.1 (eventual max M(n)), Theorem 9.1 (cp≤4 ≤ M(n) for n ≥ N) and Corollary 1.2 (all orders). The manuscript's l.43, l.61 and l.1265 are **OK**.
- **FORMALIZATION_STATUS.md.** It is dated 2026-09-08. Its theorems take `Erdos81.ExternalInputs.Inputs` with three fields: VizingInput, HaggkvistJanssenInput and PackingTransferInput. The last returns certified rational primal/dual optima and an attained integral optimum. These are stated to be explicit parameters, not axioms. The manuscript's l.1132 is **accurate**, including "does not assert that the mathematical proof of [5] is conditional on conjectures". Additional context: [5] attributes its transfer to Rohatgi–Urschel–Wellens [RUW21, Thm 3.4/3.6] (p.3).
- **Table 5 section locations** (l.1230–1238, l.1217):
  - §2: external inputs / transfer statement
  - §3: integral construction around a root (Vizing + Häggkvist–Janssen list colouring)
  - §4: strict root regularization
  - §5: quantitative local stability
  - §6: monotone copy path
  - §8: global stability by first entry
  - §9: main theorem, cp≤4 ≤ M(n)

  All **match** (SV headings).
- **Strict root regularization (l.1267).** [5] Lemma 4.2 (p.7) gives cp≤3(G) ≤ p′q′ − C(p′,2) − m′/9 − A′/2 for a new clique P′. This equals B_n(p′) − m′/9 − A′/2 with q′ = n − p′. **OK** (primes omitted in the manuscript; trivial).
- **Credits to the series (l.1241).** [5]'s introduction (p.1–2) cites Paper II [TG26a] (fractional functional), Paper III [TG26b] (split linear-error bound) and Cipollini. §6 (p.9) says the copy inequality, clone-class lift and complete-split terminal reduction follow the strategy of [TG26a, §§3–5]. **OK.**
- **Changes since cbde8a0a.** None (see §0).
- **Attribution of [5] as "Anonymous" (l.2428) — MINOR / disclosure note** (SV facts, AI assessment).
  - The printed PDF author is "ANONYMOUS", so the manuscript's choice follows the document.
  - Public attribution exists elsewhere, though. The README credits Morluto with the mathematical proof (GPT-assisted) and N0zoM1z0 with the manuscript and Lean. erdosproblems.com proof claim 285 (2026-09-08) is by "Morluto, Yang Luo, Yinzhen Huang, Grace Lee" and links this repository.
  - The manuscript's own tool reference [14] (Jacobian, github.com/morluto/jacobian, l.2414, l.2446) belongs to the same Morluto. [5]'s README and claim 285 say Jacobian played a substantial role in deriving [5].
  - **Suggestions.** (i) Add a pointer to proof claim 285 in [5]'s reference. (ii) Consider a one-line disclosure that the tool [14] is by an author of the [5] claim. This is not an accusation of dependence; the manuscript's ConeAudit (l.1136) concerns formal namespace exclusion only.

## F. Cipollini [21]
- **Anchor and date.** SV: anchor `#proof-claim-201` exists and is labelled a "partial proof claimed by Ricky Cipollini". It was submitted 2026-08-10 17:06:33.
- **Content.** The summary claims partition into n²/6 + o(n²) cliques and names the o(n²)-to-O(n) gap as the remaining difficulty. The external link is the same Overleaf ID `thjptfhgnmxc` (the site appends `#cc1388`).
- **Manuscript.** Lines 47 and 2460 are **accurate**. The Overleaf manuscript was not opened (coverage limit).

## G. Historical r2 blocker (Theorem C maximum coincides with [15, Thm 1.1]) — status in v1.2
- **Now resolved (SV, manuscript text).** The citation is explicit in five places:
  - abstract l.25: "recovers the unrestricted extremal family of Okechukwu [15, Theorem 1.1]" and "No priority for the extremal value is claimed"
  - §1 l.43, which lists all three clauses of [15, Thm 1.1] and Cor 1.2 with "No priority is claimed"
  - Theorem C l.84 (definition credited), l.95 (strengthening of [15, Thm 1.1]) and l.97 ("maximum and equality family are those of [15, Theorem 1.1]")
  - §8.1 l.1245
  - l.1014

  **Blocker resolved: OK.**
- **Logic of "Theorems C and C′ imply all three clauses" (l.1245) (AI).**
  - *All-orders clause.* For n < N_s, cp(G) ≤ c_4(G) ≤ e(G) ≤ C(N_s,2), and Q_s(n) ≥ −C(s+1,2) (Q_s can be negative at tiny n for s ≥ 1). So K_s = C(N_s,2) + C(s+1,2) gives c_4 ≤ Q_s(n) + K_s at all orders. **Valid.**
  - *Eventual maximum clause.* Given by Theorem C and the witness. **Valid.**
  - *Equality clause.* Given by Cor 6.3 (6.18), which relies on Theorem C′ at δ = 0 plus the unrestricted lower witness, for n above max(N_s^stab, N_s). **Valid as an eventual statement**, which is also how [15] states it.
  - *Wording.* Saying "Theorem C′ recovers the equality classification" (l.43, l.109) is slightly compressed, since the proof needs Cor 6.3 and the Appendix E witness. **OK.**
- **Residual — MINOR.** The abstract (l.25) and Theorem A (l.61) name only [5] as an alternative source for the all-orders Erdős-81 bound. [15, Cor 1.2] also states it, in cp form, at every order, and [15]'s abstract says it answers the EOZ question. §1 l.43 does credit this. Adding "[15, Corollary 1.2]" next to "[5]" at l.25 and l.61 would remove any residual asymmetry.

## H. Overclaim scan
- **Universal b = 0.** Not claimed. It is explicitly disclaimed at l.27, l.795, l.1379 and l.2349. **OK**
- **Universal linear mixed packing gap.** Not claimed. It is disclaimed at l.303 and l.2351. **OK**
- **Small or effective threshold.** None claimed. The thresholds are called "explicit but impractical" (l.27, l.795, l.1126, l.2139). **OK**
- **Unqualified superiority.** None found. The comparisons carry disclaimers (l.1215, l.1239, l.1245, l.1255, l.1267).
- **Ambiguity at l.314 — MINOR/UV.** The line says "The near threshold has been reduced from 10^32 to 4·10^12". It does not say whose 10^32. [5] uses N = max{10^32, T(η/2)} ([5] (1.3), p.2). The sentence may refer to an earlier version of the manuscript's own threshold, but readers may read it as an improvement over [5]. Recommend naming the baseline.

## Additional antecedents noticed (informational, not cited; no severity)
- erdosproblems #81 forum comments: Woett (19 Jun 2026), an explicit EOZ constant c ≥ 1/133; JamalAgbanwa (20 Jun 2026), a conditional n²/6 + O(n) bound under a "weak Clique-Drop Hypothesis" (Zenodo 20778270, not opened).
- Bo Ning, arXiv 2608.11536 / 2609.20305 (cp − cc difference): not related to chordal graphs.
- No 2026 work was found, besides [5] and [15], proving stability or c_4 bounds for rooted simplicial defect. This is not a completeness claim.

## Summary of verdicts

| Item | Verdict |
|---|---|
| A (Theorem C vs [15, Thm 1.1]; L-cutoff statement l.1255) | OK |
| A.3 (Table 4 / l.1257 description of [15]'s mechanism) | MINOR (fix recommended) |
| B (cited items of [15]; order-3 scope) | OK |
| C (positioning vs Cor 5.5 / Thm 1.3) | OK |
| C.1 ("stronger hypothesis" wording, l.1259) | MINOR |
| C.2 ("order-four version of (1.5)", l.1261) | MINOR |
| D ([22] description and Lemma 11 case mapping) | OK |
| E ([5] claims, trust boundary, sections, m/9, A/2, credits; unchanged HEAD) | OK |
| E (Anonymous attribution / Jacobian disclosure) | MINOR |
| F (Cipollini claim 201) | OK |
| G (r2 blocker) | Resolved (OK); residual abstract/Thm A asymmetry MINOR |
| H (overclaims) | OK; l.314 baseline ambiguity MINOR/UV |

No BLOCKER candidates and no MAJOR findings in E7.

## Coverage limits
- **Databases not searched.** No MathSciNet, zbMATH Open or Google Scholar. dblp failed. There was no full-text search of 2026 journals, and "no later version / no journal version" rests on arXiv, Crossref and a general web search only.
- **Linked sources not opened.** The Overleaf manuscript of [21] and Zenodo 20778270 were not opened.
- **[5] scope.** Only README.md and lean/FORMALIZATION_STATUS.md at cbde8a0a were read. docs/VERIFICATION_STATUS.md, the Lean sources and the certificates were not.
- **Depth of checks.** Proofs in [15], [22] and [5] were not re-verified. The comparisons check statements, numbering and the logical role of lemmas. The analysis in A.2 is an inference about the literal chain, not an impossibility claim.
- **Manuscript coverage.** Only the manuscript lines listed in the brief plus grep-located mentions of [5], [15], [21], [22] and [23] were read. Other appendices were not audited.

---

## E7 — Lead-auditor verification of the delegated first pass

The delegated first pass (`E7_FIRST_PASS.md`, same model family) was spot-checked by the lead auditor
against the saved literal sources `sources/okechukwu_v1.txt` (sha256 feff7419…, derived from PDF 9654af66…)
and `sources/verclos_v1.txt`.

## Independently confirmed from the literal text of [15] v1
- Definition (p.1–2): s-simplicial = d_H(v) − ω(H[N_H(v)]) ≤ s; rsd(G) ≤ s: in every induced H and outside every
  proper clique (empty allowed) an s-simplicial vertex exists. Equivalent to `RootedDefectAt` (∃ clique C ⊆ N_U(v)
  with |N_U(v)| ≤ |C| + s ⇔ ω(N) ≥ |N| − s). SOURCE_VERIFIED.
- Theorem 1.1 (p.2): constants K_s, N_s; cp(G) ≤ Q_s(n) + K_s at every order; for n ≥ N_s the maximum is exactly
  Q_s(n); equality exactly for (K_{k−s} ⊔ K̄_s) ∨ K̄_{n−k}, k nearest to (2(n+s)+1)/6. Corollary 1.2: chordal case,
  cp ≤ F_n + O(1) at every order, eventual max F_n with classification. SOURCE_VERIFIED.
- Abstract of [15] states the chordal all-orders bound "answering a question of Erdős, Ordman and Zalcstein".
- Theorem 1.3 (p.3): sequences, rsd = o(n), cp ≥ n²/6 − o(n²) ⇒ cliques A_j of size n/3+o(n) with D_A + e(G−A) = o(n²);
  and (1.5) cp(G) ≤ (2n+1)²/24 + n·rsd(G) + ϵ(n)n² for every graph of order n ≥ 8.
- Proof of Thm 1.3 (p.11): L fixed from Theorem 3.3 (L chosen from ε, p.9 "choose ξ > 0 and then L ≥ 4 …");
  "For (1.5), use L = 4 in Lemmas 3.1 and 3.4". Lemma 3.4 (p.10): q_L ≤ q*_L + ζn² (fixed L). SOURCE_VERIFIED.
- Proof of Thm 1.1 (p.19–20): minimal-counterexample argument via Proposition 5.4, whose final count (5.11) is
  produced by the edge-disjoint-triangle constructions of §4 (Lemma 4.1/4.2); Lemma 3.4 enters only through
  Theorem 1.3's localization. SOURCE_VERIFIED (reading).
- Corollary 5.5 (p.20): qualitative ε–δ edit stability for fixed s under cp ≥ Q_s(n) − δn². §7 (p.23) asks for a
  quantitative version. SOURCE_VERIFIED.
- Only v1 listed on the arXiv abs page retrieved 2026-09-30 12:28 UTC.

Consequences for the manuscript: the v1.2 text now credits [15, Theorem 1.1] for the class, Q_s, the eventual
unrestricted maximum and the equality family (abstract l.25, §1 l.43, Thm C l.84–97, Cor 6.3 l.1014, §8.1 l.1245).
**The historical r2 blocker F-01 is resolved in this target** (it remains a historical finding for v1.0.1).
The c4 upper bound is a genuine statement-level strengthening; neither the manuscript nor this audit asserts
that [15]'s method cannot yield it.

## Confirmed MINOR items from the delegated pass (lead auditor agrees)
- E7-M1 Table 4 (l.1210) and l.1257: describing [15]'s use of K_3…K_L as a "far transfer" branch that "pays the
  budget … in the branch with the corresponding margin" does not match [15]: Lemma 3.4 is used for localization
  (Thm 1.3) and for (1.5); Thm 1.1's partitions come from the §4–5 triangle constructions.
- E7-M2 l.1259 "stronger near-extremality hypothesis on c4": logically the weaker hypothesis (see E1-O3).
- E7-M3 l.1261 "order-four version of its approximation (1.5)": [15]'s own proof of (1.5) already uses L = 4;
  only its stated conclusion is for cp. Wording could mislead (OBSERVATION/MINOR).
- E7-M4 Abstract l.25 and Thm A l.61 name only [5] as an alternative source of the all-orders chordal bound;
  [15, Cor 1.2] (and [15]'s abstract) also claim it. §1 l.43 does credit [15, Cor 1.2], so this is MINOR.
- E7-M5 [5] authorship shown as "Anonymous"; the same group authored the Jacobian tool [14] used by the author.
  Transparent policy, but a one-line provenance note would help (MINOR; same as r2 E7-C6).
- E7-M6 l.314 "reduced from 10^32 to 4·10^12": the prior value's owner is unstated; [5] also uses 10^32 (per the
  delegated pass; not re-verified by the lead auditor) — clarity.

## [22] spot checks
- Lemma 3 (p.3): n ≥ ε^{-1}, G[Y] chordal, p_G(v) ≤ εn² on X ⇒ 6ε^{1/2}-close to chordal. Manuscript (F.10) states
  constant 8 and no n ≥ 1/ε; comparison accurate. SOURCE_VERIFIED.
- Lemma 11 (p.10): tree T with at most k leaves, G0 of size ≤ k, subsets sampled uniformly of size
  m11 = 2^40 ε^{-4} k^6 ln^4 k. The manuscript's adaptation (sequences with replacement, K nodes, enlarged pinned
  class, m11 = ⌈2^58(K+1)^15/ε^12⌉) is described as an adaptation, not a literal statement. Accurate.
- Only v1 on arXiv (abs page 2026-09-30).

**E7 first-pass status: PASS with MINOR findings (no attribution blocker).** Coverage limits: arXiv API,
Crossref, GitHub API, erdosproblems.com, one general web search; no MathSciNet/zbMATH/Scholar; Overleaf
manuscript of [21] not opened; [5]'s Lean sources not inspected. Not a complete novelty search.
