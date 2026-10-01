# Gate E2 report — run_v1.22_r1 (Paper IV v1.22-r1)

Verdict: **PASS**. Evidence: `20_EVIDENCE/E2/`. Auditor: Claude Opus 5.5, same session as run_v1.2_r1/run_v1.21_r1; no Lean executed.

---

# E2 — Focused mathematics revalidation (v1.22 against v1.21)

Method. I compared v1.21 → v1.22 with my own unified diffs (`auditor_diff_en.diff` and `auditor_diff_es.diff`). I then rederived the new C.3 text by hand, block by block. For definitions, I compared it with the pinned Mathlib source `Mathlib/Combinatorics/SimpleGraph/Regularity/Bound.lean` (git rev 8f9d9cff, sha256 c6395362…; read-only). For the formal statements, I compared it with `E18/Numeric.lean` and `E19/Main.lean` in the frozen cut. The arithmetic was checked exactly (`20_EVIDENCE/E5/e5_v122_c3.py`: 14 checks, each with a rejected negative control once the negfix and supplement files are counted; see E5). I read the author response (`RESPONSE_TO_REVALIDATION_v1.22.md`) only after reaching these conclusions. No Lean was run (mandate §2).

## Diff scope (v1.21 → v1.22)
- Status paragraphs (title page and §7 "Audit status"): no mathematics.
- §5.1 heading and the A.2 row: formatting only.
- A.2 scope paragraph: now refers to C.3.
- C.2 now includes the R-02 clarification sentence.
- C.3: new definitions of I, H, t_j and B, plus three new paragraphs ("The regularity iterate at the chosen accuracy", "Absorbing the five terms" and "Converting the iterate to a tower").
- X-12, X-15 and NEW-02 fixes: presentation only.
- No theorem statement, hypothesis, final constant, equation tag or Lean block changed (E6_PARITY.json: tags and Lean blocks are equal to v1.21; no display removed).

## C.3 — the six mandated checks

| # | Check | Rederivation | Result |
|---|---|---|---|
| 1 | I(ε,k₀), H(ε), t₀, t_{j+1} and B against `SzemerediRegularity.initialBound`, `stepBound` and `bound` | Mathlib (Bound.lean): `stepBound n = n * 4 ^ n` (l.42); `initialBound ε l = max 7 (max l (⌊log (100/ε^5) / log 4⌋₊ + 1))` (l.167); `bound ε l = stepBound^[⌊4/ε^5⌋₊] (initialBound ε l) * 16 ^ (stepBound^[⌊4/ε^5⌋₊] (initialBound ε l))` (l.190). In the manuscript, I = max{7, k₀, ⌊log(100/ε⁵)/log 4⌋₊ + 1}, H = ⌊4/ε⁵⌋₊, t_{j+1} = t_j 4^{t_j} and B = t_H 16^{t_H}. | **Match** (the order inside max is immaterial) |
| 2 | At η₀: I = k₀, and H equals h of §6.3 (`E18.Numeric.initialBound_eq`, `floor_iter_eq`, `BE_eta0`) | ε = δ/8, with 1/δ = 2208(9·10¹⁹)²¹ exactly. 100/ε⁵ ≤ 4⁴⁰⁰⁰ (exact), so the floor term is ≤ 4001 < k₀ = 3·10¹⁹+1, and I = k₀. 4/ε⁵ is an integer equal to 4·8⁵·2208⁵·(9·10¹⁹)¹⁰⁵ = h, using 9·10¹⁹ = 4500·2·10¹⁶ (E5 C3a–C3c). The E18 statements have the same content. | **Correct** |
| 3 | The lower bound after two iterations dominates G₁, G₂, G₃; no claim that two steps suffice | x·4^x ≥ 2^x and the iterates are nondecreasing, so R = t_h ≥ t₂ ≥ 2^{t₁} ≥ 2^{2^{k₀}} ≥ 2^{2^{59517}} ≥ G_i. This uses Table C.1: G₃ ≤ 2^{U+67} ≤ 2^{2^{59517}}, and h ≥ 2. The text says explicitly that this is "a lower bound for the regularity iterate, not an upper bound on the number of iterations needed by regularity". | **Correct** (C3g, C3h) |
| 4 | Substitution into the five terms of (C.1), including the ceilings and the final unit (`E18.Numeric.NfarE_eta0_le`) | k₀ is exact. ⌈B/δ⌉ = αB exactly (B is an integer; α = 2208(9·10¹⁹)²¹). ⌈(12+10D_*)/z⌉ = G₃ exactly, with z = 1/(2·10¹⁷). The fourth term is ⌈4B⁵G₁(a₃+a₄)/(a₃a₄)⌉, using 1/γ = G₁. Exactly, (a₃+a₄)/(a₃a₄) ≤ 2(9·10¹⁹)⁶ with slack ≥ 10⁻¹⁰(9·10¹⁹)⁶, so 4G₁B⁵ times the slack is far above 1 and the ceiling is absorbed into βG₁B⁵, β = 8(9·10¹⁹)⁶ (C3d). ⌈50(1+2C)/ξ⌉ = 10¹⁸(1+2G₂) exactly, since 50/ξ = 10¹⁸ at ξ = η₀/2 (C3e). The leading 1 of N_E and the max ≤ sum give the displayed N_far(η₀) ≤ k₀ + αB + G₃ + βG₁B⁵ + 10¹⁸(1+2G₂) + 1. The Lean statement `NfarE_eta0_le` is literally this sum. The rational bound for the fourth term (the "sharper direct substitution") is correct. | **Correct** |
| 5 | B⁶/4 + 7B² ≤ B⁶ and the induction 4t_j ≤ T(j+5) give T(h+7) (`E19.absorb_abstract`, `four_mul_Tnum_le`, `B6_le_two_pow_two_pow`, `NfarE_eta0_le_tower`) | k₀, α, β and 10¹⁸ are all ≤ 2²⁰⁰⁰ ≤ R (C3f). 16^R ≥ 4R, so B ≥ 4R² and B ≥ 4. Then βG₁B⁵ ≤ R²B⁵ ≤ B⁶/4. The other terms are ≤ B², B², B², 3B² and B², i.e. 7B² in total, and 256B² ≤ B⁶, so the sum is ≤ (1/4+7/256)B⁶ ≤ B⁶ (C3i, C3j). The tower step: 4k₀ ≤ 2⁶⁷ ≤ T(5), and 4(x4^x) ≤ 2^{4x}, so 4t_j ≤ T(j+5) (C3k, C3l). With q = T(h+5): 4R ≤ q and q ≥ 6. B⁶ = R⁶2^{24R} ≤ 2^{30R} ≤ 2^{8q} … ≤ 2^{2^q} = T(h+7), using 30R ≤ 8q ≤ 2^q (C3m, C3n). This matches the E19 hypotheses: 2²⁰⁰⁰ ≤ T and g_i ≤ T in `absorb_abstract`; 8 ≤ T and 4T ≤ t in `B6_le_two_pow_two_pow`. | **Correct** |
| 6 | The A.2 pointer now goes to C.3; the account can be reconstructed without delegating to theorem names | A.2 (EN p40 / ES p40) now reads "Revision 1.22 defines the regularity recurrence in C.3 …". The dangling "recurrence in §6.3" is gone. Every step above can be followed from the printed text and Table C.1 alone; the Lean names serve only as cross-references. | **Correct** |

**A2-4 → ACCEPTABLE_SUMMARY. X-05 → RESOLVED.** The explicit values T(h+7) and T(h+8) of §6.3 are now derived in the text.

## Other A.2 rows (inherited)
The diff confirms that the text of A2-1, A2-2, A2-3, A2-5, A2-6 and A2-7 is unaltered, apart from the R-02 sentence inside A2-3. They therefore inherit their run_v1.21_r1 verdict of **ACCEPTABLE_SUMMARY**. The inheritance rests on identity: unchanged text in an identified target and an unchanged Lean source cut (E0: 615/615).

## C.2 — R-02 and R-01
- R-02: the new sentence, "here the sum includes every active profile containing both classes of q, not one selected pair per profile" (EN p47 / ES p48), matches `PatternTransfer.servingT`. **R-02 RESOLVED.**
- R-01: the second-moment inputs B_q u²a₃² ≤ 11δt² and 23δt² are still cited, not derived. As the mandate requests, this is kept as a declared expository limit (**OBSERVATION, KEPT**). I found no new reason to raise it.

## E2 verdict
**PASS.** All seven A.2 rows are ACCEPTABLE_SUMMARY. No mathematical error was found. The scope remains a summary-level written proof checked against frozen formal statements; it is not a replacement for human referee review.
