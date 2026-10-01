# E7 — Lead-auditor verification of the delegated first pass

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
