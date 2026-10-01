# E7 — citations and priority

**Obligation (request §4, §5).** Retrieve and verify the cited papers and the Erdős #81 record; compare
published solutions with Paper IV; separate logical independence, code provenance, mathematical antecedents
and bibliographic novelty; decide whether **Theorem C coincides in statement with a result of [15] for fixed
rooted defect** and whether §8.1's attribution matches; record later versions of [15] and [5] as of the audit
date (2026-09-28).

**Target inputs.** EN md `71417794…` (lines 46, 81–94, 921, 986–1046, 1573–1743, 1789); ES md `8448d14e…`
(the corresponding lines 46, 987–1043, 1712, 1788 — same content).

**Retrieved sources** (all saved in `sources/`, SHA-256 in `SOURCES_SHA256.txt`, retrieval 2026-09-28
11:11–11:17 −03:00):

| Ref | Retrieved | Version status on audit date |
|---|---|---|
| [15] Okechukwu, arXiv:2609.20871 | abs page + `v1` PDF (24 pp., 432 079 B) | Submission history lists **only v1** (15 Sep 2026). No later version. |
| [5] N0zoM1z0/erdos-81 | `manuscript/main.pdf`, `README.md`, `lean/FORMALIZATION_STATUS.md`, `lean/Erdos81/ExternalInputs.lean`, `docs/VERIFICATION_STATUS.md` at `cbde8a0a…`; tree listing | `main` HEAD **is** `cbde8a0a…` (2026-09-08T10:47Z); only other branch `codex/revise-manuscript-lean-audit` at an earlier commit. No later version. |
| [8] erdosproblems.com/81 | problem page, proof-claims thread, discussion thread | Problem status shown **OPEN**; 4 proof claims (Morluto et al. 2026-09-08 = [5]; Traverso 2026-09-22 = Paper IV v0.8; Traverso 2026-08-29 partial = Paper III; Cipollini 2026-08-10 partial n²/6+o(n²)). |
| [9],[12] lean-pool PRs | GitHub API | #348 merged 2026-08-25, commit `540d8e34…`; #420 merged 2026-09-13, commit `d1de6d2a…`. Match manuscript. |
| [2]–[4] | doi.org | `10.5281/zenodo.22064657` resolves (record 22064657); concept DOI `21273143` resolves to the same latest record. |
| [16] | Whitman research page | "Clique Partitions of Split Graphs … in preparation", no manuscript link. Matches manuscript. |
| Prior-art search | arXiv API (5 queries, `arxiv_search_2026-09-28.txt`), 1 web search | Only relevant arXiv hit: [15]. Coverage limit: arXiv + general web search only; no MathSciNet/zbMATH access; forum partial claims found via [8]. |

## Finding E7-F1 — Theorem C's eventual maximum coincides with [15, Theorem 1.1], which the manuscript never cites (MAJOR, attribution; release-blocking)

**Literal source ([15] v1 p. 2, rendered `sources/okechukwu_p2.png`).** With `F_n = ⌊n(n+1)/6⌋` and
`Q_s(n) = F_{n+s} − C(s+1,2)` (eq. 1.1): *"Theorem 1.1. For each integer s ≥ 0 there are constants K_s ≥ 0
and N_s with the following properties. Every graph G of order n with rsd(G) ≤ s satisfies cp(G) ≤ Q_s(n)+K_s.
For n ≥ N_s, the maximum is exactly Q_s(n). Equality at these orders holds precisely for the graphs
(K_{k−s} ⊔ K̄_s) ∨ K̄_{n−k}, k a nearest integer to (2(n+s)+1)/6."*

**Comparison with Theorem C (EN l. 81–94; Lean `rooted_defect_eventual`, `rooted_defect_maximum`).**

| Aspect | [15, Thm 1.1] | Paper IV Thm C | Same? |
|---|---|---|---|
| Graph class | rsd(G) ≤ s: in every induced H, outside every proper clique (empty allowed), an s-simplicial vertex (d − ω(N) ≤ s) | ∀U, ∀ clique R ⊊ U (empty allowed), ∃ v ∈ U\R with a clique C ⊆ N_U(v), |N_U(v)| ≤ |C|+s | **Identical** (ω(N) ≥ |N|−s ⟺ such C exists) |
| Target | Q_s(n) = F_{n+s} − C(s+1,2) | Q_s(n) := M(n+s) − C(s+1,2) (same symbol) | **Identical** |
| Quantifiers / threshold | ∀s ∃N_s ∀n ≥ N_s | ∀s ∃N_s ∀n ≥ N_s | **Identical** |
| Upper bound | cp(G) ≤ Q_s(n) eventually (and cp ≤ Q_s+K_s at all orders) | c₄(G) ≤ Q_s(n) eventually | Paper IV **stronger** in piece order (c₄ ≥ cp); [15] adds the all-orders form |
| Attainment / maximum | "the maximum is exactly Q_s(n)" | "the eventual maximum is Q_s(n), also when cliques of arbitrary order are allowed" | **Identical** statement |
| Witness | (K_{k−s} ⊔ K̄_s) ∨ K̄_{n−k} (Lemma 2.5) | C complete (k−s), D independent (s), H independent (n−k), all (C∪D)–H links, no C–D edges (E.3) | **Same graph family** |
| Equality classification | yes | explicitly not claimed beyond chordal | [15] stronger |
| Permitted piece orders | cp: unrestricted | upper bound order ≤ 4; lower bound unrestricted | Paper IV stronger on upper side |

**Conclusion (SOURCE_VERIFIED).** The *maximum* half of Theorem C coincides in statement with
[15, Theorem 1.1]; the *upper-bound* half is [15, Theorem 1.1]'s eventual upper bound strengthened from cp to
c₄. The class definition and the symbol Q_s are those of [15]. (Whether [15]'s method yields c₄ is not
asserted by [15]: its localization, Thm 3.3, needs a cutoff L = L(ε); AUDITOR_INFERENCE that the c₄ form is
a genuine formal strengthening.)

**Manuscript attribution (EN = ES).** [15] is cited only as: Cor 1.2 (chordal case, l. 46); Thm 1.3 and
Cor 5.5 (stability, l. 46, 1040); Thm 3.3, Lemma 3.4, Lemma 4.1/(4.4) (mechanisms, l. 1038, 1042, 1711); and
§8.1 l. 1028: *"Okechukwu [15] studies rooted simplicial defect. Our Theorem C uses that class … This is the
precise scope of the extension incorporated here. Comparing mechanisms is not a priority claim for the extremal
formula."* **[15, Theorem 1.1] is never cited** (grep: zero occurrences of "Theorem 1.1"/"Teorema 1.1"
attached to [15] in EN or ES). The abstract (l. 28) and the statement of Theorem C (l. 81–94, where the class
is defined as "We say that G has rooted simplicial defect at most s …") carry no citation of [15] at all.

**Why this is material.** Theorem C is one of the three headline theorems. A reader of the abstract,
introduction and §8.1 is told that [15] studies the class and proves the *chordal* corollary and stability
results, but not that [15]'s main theorem already establishes, for every fixed s, the same eventual maximum
Q_s(n) with the same extremal family (plus equality classification and an all-orders bound). The disclaimer
"not a priority claim for the extremal formula" does not identify the prior theorem. By contrast the manuscript
does explicitly acknowledge that [5] proves Theorem B's eventual maximum (l. 46, 1000). The attribution in §8.1
therefore **does not match** the finding requested by §5 of the mandate.

**Minimal repair (proposal only, not applied).** State at Theorem C (and in the abstract/§1 and §8.1) that
[15, Theorem 1.1] proves, for each fixed s, cp(G) ≤ Q_s(n) eventually with maximum Q_s(n) and classification of
equality graphs, and that Theorem C's contribution relative to [15] is the order-≤4 upper bound (c₄) and the
independent formal proof; attribute the definition of rooted simplicial defect and the notation Q_s to [15].
A corrected target requires a new revision ID and a new audit of E7/E6 (request §4.2).

## Other E7 checks

| ID | Claim (EN line) | Result | Severity |
|---|---|---|---|
| E7-C1 | l. 46: [5] establishes the eventual chordal maximum; [15, Cor 1.2] obtains it as a special case | SOURCE_VERIFIED: [5] Thm 1.1 (max = M(n)) and Thm 9.1 (cp₄ ≤ M(n), n ≥ N); [15] Cor 1.2 | OK |
| E7-C2 | l. 46/1040: [15, Thm 1.3] asymptotic stability, sublinear defect; [15, Cor 5.5] ε–δ edit stability, fixed s | SOURCE_VERIFIED (p. 3, p. 20). Also [15] §7 explicitly asks for a quantitative version of Cor 5.5; Thm 6.1 gives one for s = 0 with linear rate 16δ and hypothesis on c₄ (weaker hypothesis than on cp). The manuscript does not claim exclusivity. | OK (OBSERVATION: the text could note that [15, §7] poses this question) |
| E7-C3 | l. 921: [5]'s `FORMALIZATION_STATUS.md` declares verification conditional on `ExternalInputs.Inputs` (Vizing, Häggkvist–Janssen, packing transfer with rational optimality certificates) | SOURCE_VERIFIED at `lean/FORMALIZATION_STATUS.md` (path is under `lean/`, not the repo root) | OK / MINOR (path) |
| E7-C4 | Table 5 section locations of [5] (§§2,3,4–5,6,8,9) | Spot-checked: §3 root construction, §4 regularization, §5 local stability, §6 copy path crediting Traverso [TG26a], §8 first entry, §9 main theorem — SOURCE_VERIFIED | OK |
| E7-C5 | l. 1024: [5] credits Paper II for copy scheme and Paper III for split result | SOURCE_VERIFIED ([5] §1, §6 first paragraph) | OK |
| E7-C6 | [5] authorship "Anonymous" | [5]'s PDF prints "ANONYMOUS"; the erdosproblems proof claim names Morluto, Yang Luo, Yinzhen Huang, Grace Lee. The manuscript's policy (retain printed attribution) is transparent. Note: tool [14] Jacobian is by the same group (code-provenance context, disclosed). | OBSERVATION |
| E7-C7 | Antecedents for n²/6 + o(n²) | Cipollini's partial result (erdosproblems claim 2026-08-10; cited by [5] as [Cip26]) is not cited by Paper IV. Not a dependency; omitted antecedent. | MINOR |
| E7-C8 | l. 48 and Thm A: "answers Erdős Problem 81" | erdosproblems.com lists #81 as OPEN on 2026-09-28 with four unreviewed proof claims. The manuscript's [8] note disclaims certification of status. Claim is the author's mathematical claim, not a record status. | OBSERVATION |
| E7-C9 | [9],[12] PR numbers/merge commits/dates; DOIs; [16] | SOURCE_VERIFIED (table above) | OK |
| E7-C10 | [1] EOZ93, (1/4−ε)n² | Confirmed by [5], [15] and erdosproblems text (secondary); primary CPC article not retrieved (paywall) | UNVERIFIED (primary) — low weight |
| E7-C11 | [17] Behrend / Mathlib `Behrend.roth_lower_bound` | to be checked in the shared Mathlib source (read-only) — see E3/E4 note | deferred |

## Logical independence vs provenance vs novelty (separated)

* **Logical independence (Lean):** static reading found no `Erdos81.*` names in the freeze (the `ConeAudit`
  dynamic check is E4). Paper IV's formal chain does not import [5] or [15] — AUDITOR_INFERENCE from static
  source; dynamic confirmation pending.
* **Code provenance:** Paper III `Nibble` and Paper II chordal structure are the author's own series; Mathlib's
  regularity lemma and Behrend bound are third party; Aristotle (Harmonic) assisted the formalization
  (disclosed). The Jacobian tool [14] belongs to the [5] group (disclosed as a computational tool only).
* **Mathematical antecedents:** Paper II (copy scheme), Paper III (nibble, split case), [5] (same two-regime
  architecture: mixed K₃/K₄ functional with gains 2/5, copy path, local stability; [5] predates Paper IV v0.8
  by 14 days), [15] (class, Q_s(n), fixed-s maximum, stability), Cipollini (first-order bound).
* **Bibliographic novelty (as of 2026-09-28):** the eventual chordal maximum M(n) is in [5] and [15]; the
  fixed-s eventual maximum Q_s(n) is in [15]; what remains specific to Paper IV at statement level is the c₄
  (order ≤ 4) form of Theorem C, the explicit linear stability constants 16 and 48 (Thm 6.1, Cor 6.1a), the
  partition-stability statement with a partition-independent root, the explicit tower threshold, and the
  unconditional (interface-free) Lean formalization.

## Gate result

**E7 = FAIL** — confirmed material attribution defect E7-F1 (literal source evidence above). Other attribution
statements checked are accurate. Limitations: arXiv/web only; no human bibliographic database; [1] primary not
retrieved.
