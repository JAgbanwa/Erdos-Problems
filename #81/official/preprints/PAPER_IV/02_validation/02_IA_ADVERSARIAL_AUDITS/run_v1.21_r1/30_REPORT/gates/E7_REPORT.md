# Gate E7 report — run_v1.21_r1 (Paper IV v1.21)

Verdict: **PASS**. Evidence: `20_EVIDENCE/E7/`.

---

## E7 — Attribution revalidation

Sources: cited versions saved in run_v1.2_r1 (`20_EVIDENCE/E7/sources/`, hashes in its SOURCES_SHA256.txt; the
lead auditor re-read [15] v1 pp.1–3, 8–11, 17–20, 23 and the [5] README at the cited commit). Later-version
check on 2026-09-30 23:07 UTC: arXiv 2609.20871 abs page lists only [v1] (sha256 e1ce80ea…, identical to
the page saved on 2026-09-30 12:28 UTC); arXiv 1902.06135 only [v1]; N0zoM1z0/erdos-81 latest commits
cbde8a0a (2026-09-08), 2dd0615a, fc7712b1 — HEAD unchanged. Saved in `sources/`.

| ID | v1.2 issue | v1.21 text | Check against source | Resolution |
|---|---|---|---|---|
| X-06 | Table 4 / l.1257 described [15]'s K₃…K_L use as a far-transfer branch paying the budget | Table 4 row: "K₃…K_L in the approximation used for localization; q_L in Lemma 3.4; cp in Theorem 1.1; Δ_{3..L} for the auxiliary model"; §8.1: conditional calculation "is not a description of the final construction in [15, Theorem 1.1]: that proof uses Lemma 3.4 through structural localization, then a minimum-counterexample argument and the triangle constructions of [15, §§4–5]" | [15] p.10–11 (Lemma 3.4 inside Thm 1.3 localization; (1.5) with L=4), p.19–20 (minimal counterexample K→∞ via Prop 5.4; (5.11) from §4 triangle constructions) | **RESOLVED** |
| X-07 | "stronger" c₄ hypothesis | "under the weaker near-extremality hypothesis on c₄: the corresponding lower bound on cp implies it, since cp ≤ c₄" | Logic: cp(G) ≥ Q−δ ⇒ c₄(G) ≥ Q−δ | **RESOLVED** |
| X-08 | "order-four version of (1.5)" | "recovers its approximation (1.5) with a conclusion stated for c₄ … The proof of (1.5) in [15] already chooses L=4; that choice is not a new ingredient here" | [15] p.11 "For (1.5), use L = 4 in Lemmas 3.1 and 3.4" | **RESOLVED** |
| X-09 | Abstract/Thm A omitted [15, Cor 1.2] | Abstract: "also obtained in [5] and [15, Corollary 1.2]"; Theorem A remark likewise | [15] Cor 1.2 (p.2) and abstract (p.1) | **RESOLVED** |
| X-10 | [5] authorship / Jacobian | Ref [5] keeps printed "Anonymous" and adds the README credits (Morluto proof; N0zoM1z0 manuscript and Lean; Jacobian at Preference Labs); AI/tools section: "Jacobian is also credited by the project behind [5]" | README at cbde8a0a, "## Credits": proof by Morluto with GPT assistance; Jacobian "a research tool developed at Preference Labs, played a substantial role"; manuscript and Lean by N0zoM1z0; "a Preference Labs research project" | **RESOLVED** (OBSERVATION: the manuscript writes "PreferenceLabs"; the README writes "Preference Labs"; the README also says the proof had GPT assistance — not required to be repeated) |
| X-11 | "reduced from 10³² to 4·10¹²" ambiguous | "During the development of our near constructor … This compares versions of that constructor, not the global thresholds of different papers." | — | **RESOLVED** |
| [15] Theorem C attribution (historical r2 F-01) | — | Unchanged from v1.2 (credited) | — | Remains resolved |
| Localization vs final construction | — | §8.1 as above | [15] pp.9–11, 17–20 | Accurate |
| cp ≤ c₄ direction | — | §8.1 (X-07) | — | Accurate |
| Prior use of L=4 | — | §8.1 (X-08) | — | Accurate |
| [23] and the classification wrappers | — | [23] note now names the unrestricted-classification wrappers | AuditorASProbe.log | Accurate (see E3, X-27) |

No inference of bibliographic originality is drawn from dependency cones. Coverage limits as in run_v1.2_r1
(no MathSciNet/zbMATH/Scholar; not a complete novelty search).

**E7 verdict: PASS** (X-06–X-11 resolved; one OBSERVATION on spelling "PreferenceLabs").
