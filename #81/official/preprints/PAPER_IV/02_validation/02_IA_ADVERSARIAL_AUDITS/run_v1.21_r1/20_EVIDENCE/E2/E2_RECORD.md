# E2 — Mathematics revalidation (v1.21 against v1.2 findings)

Method: the auditor's own unified diff of v1.2 → v1.21 (`auditor_diff_en.diff`, `auditor_diff_es.diff`),
pen-and-paper rederivation of every added passage, and exact checks of the new numerics
(`20_EVIDENCE/E5/e5_v121_numerics.py`, 21 checks, all PASS, all negative controls rejected). The author
response (`RESPONSE_TO_AUDIT_v1.21.md`) was read only after these conclusions were written.
No Lean was run (mandate §2).

## Theorems unchanged
No theorem statement, hypothesis, constant, equation tag or Lean code block changed (diff). The only formula
edits are the declared descriptive subscripts: N_lej/N_lejano→N_far, e_cruz→e_cross, x^limpio→x^clean,
E_cub→E_covered. These are semantic no-ops (N_far already named the same far-branch threshold in (C.4)).

## A.2 items — rederivation and verdicts

| Item | v1.21 location | Rederivation performed | Verdict | Explanation |
|---|---|---|---|---|
| A2-1 | §5.1, new sentence before "The retained columns…" | Yes. X-columns miss ≥a/4 of ≤129a/64 old exterior vertices ⇒ ≤113a/64; non-Y exterior degree <7a/4 ≤113a/64; +\|X\| | **ACCEPTABLE_SUMMARY** | X-23 closed. |
| A2-2 | C.2 (3.10), unchanged | As in run_v1.2_r1 | **ACCEPTABLE_SUMMARY** | Unchanged; standard bookkeeping. |
| A2-3 | C.2, four new paragraphs after (3.13) | Yes, complete. (i) Load: surviving copies through a good root ≤(1+u)A_{H,q}=(1+u)V_H/d_q, weight ψ_H/((1+u)V_H) ⇒ contribution ≤ψ_H/d_q; with Σ_{H serving q}ψ_H ≤ d_q the load is ≤1. (ii) Retention: B_q ≤ 11δt²/(u²a₃²) (K₄: 23δt²/(u²a₄²)); ≤t (resp. t²) copies per root; 3 (resp. 6) pairs ⇒ ≤33δt³/(u²a₃²), 138δt⁴/(u²a₄²) deleted; with V_H ≥ a₃t³ (a₄t⁴) the deleted fraction is ≤ v under 33δ ≤ vu²a₃³, 138δ ≤ vu²a₄³. (iii) Schedule: d=u=v=a, δ=a²¹/2208, a₃≥a³/2, a₄≥a⁶/2, 138δ=a²¹/16 ≤ a²¹/8 (E5 C2-1…C2-3). (iv) Weight retained ≥(1−v)/(1+u). | **ACCEPTABLE_SUMMARY** | **X-01 resolved.** Residual OBSERVATION R-01: the second-moment inputs "B_q u²a₃² ≤ 11δt², B_q u²a₄² ≤ 23δt²" are cited from the rooted second-moment (counting-lemma) estimates, not derived; they are standard consequences of δ-regularity. Wording note R-02: "H serving q" must mean every active profile containing the pair q (the load bound needs all profiles through q); with the earlier sentence "every active profile serves a pair of classes" the reader could take it as one pair per profile. Checked in the frozen source: `PatternTransfer.servingT` is exactly the set of patterns containing both parts of the pair, so the argument is correct under that reading. |
| A2-4 | C.3, new schedule definitions and numerical chain | Yes for the schedule → selector → three integers: β₀ ≥ 2⁻⁶⁶, L_T ≤ 46, M_T ≤ 5153, γ_T ≥ 2⁻⁵⁹⁴⁸⁵, T_T ≤ 2^{a₀+13}, 2G_T ≤ 2^{4a₀+5}, (2G_T)^{T_T} ≤ 2^Y, η_T ≥ 2^{−(Y+69)}, ℓ_T ≥ 2⁻¹²⁷⁴⁹, D₀ ≤ 2^{a₀+146}, c₀ ≥ 2^{−(Y+3a₀+220)}, Z = 191424, U = Y+191432, G₃ ≤ 2^{U+67} (E5 C3-1…C3-16). **Not possible** for the last step: "The regularity recurrence, iterated h times …, dominates these three quantities after just its first two iterations. Absorbing the five terms of (C.1) then gives N_far(η₀) ≤ T(h+7)." The regularity bound B (C.3 l.1646) and its recurrence are never defined in the manuscript, and A.2 (l.1355) refers to "the recurrence in §6.3", but §6.3 defines only T and h. | **REQUIRES_EXPANSION** (MINOR impact, narrowed) | X-05 **partially resolved**. Exact remaining step: state the regularity bound used (the recurrence whose h-fold iterate bounds B at parameters (δ/8, k₀); h = 4/(δ/8)⁵ in the displayed factorization), prove the two-iteration domination of G₁…G₃, and show the absorption of the five (C.1) terms into T(h+7). Affects only the explicit values T(h+7), T(h+8) (§6.3) and the c_far/h_iter part of P(s) (6.28), not the existence of thresholds or any theorem. The author's response also says this comparison "remains symbolic". |
| A2-5 | E.1, three new paragraphs (normalization counts) and σ, τ, D, L | Yes, complete: εn²=λ²/10⁴¹, nλ=ρ²; \|A∖A₀\| ≤ λ/10³¹; \|A₀\| window; e(R₀) ≤ 2ρ²/10³¹; \|Y\| ≤ 4ρ/10²⁷; Y_c/Y_r/W partition; \|c−n/3\| ≤ ρ/10²⁰; light-vertex missing ≤ ρ/10⁴+2λ/10⁴¹ < ρ/200; σ ≤ ρ/200+12ρ/10²⁷; τ ≤ ρ/40+12ρ/10²⁷; D ≤ (ρ/10¹³)²; L = ⌊√D⌋+1 (E5 E1-1). | **ACCEPTABLE_SUMMARY** | **X-02 resolved.** The localization input (clique A with ε-bounds and minimum degree) is named as produced by fixed-defect localization (E33/E34, [22]); that is a separately attributed component, not part of A2-5. |
| A2-6 | E.1, new derivation of (E.2d) | Yes, complete: choice of a_w (w ∈ W misses >ρ/200 in A₀), Z = common light neighbours of U₀, three-case elimination with charges s−ν, ω+s, (ω+s)x, each incidence charged once; e(Z,X') ≤ (s−ν)\|Z\|+2(ω+s)x; restoration \|𝓛∖Z\| ≤ 2νρ/40 + xλ/10¹⁰; error ≤ n/10+4n/10⁴+4ρ/10¹⁰+4ρ/10⁵⁰ ≤ n/9 (E5 E2d-1, negative control n/12 rejected). | **ACCEPTABLE_SUMMARY** | **X-03 resolved.** |
| A2-7 | D.1, unchanged | As before | **ACCEPTABLE_SUMMARY** | Unchanged. |

## Other E2 items
- The added Figure 3 citation and the audit-status paragraphs carry no mathematics.
- X-24 (optional constant tightenings) not adopted: acceptable.

## E2 verdict
**INCONCLUSIVE**, narrowly: six of seven A.2 rows are now ACCEPTABLE_SUMMARY, and X-01, X-02, X-03, X-23 are
resolved. **A2-4 still REQUIRES_EXPANSION** at one exact step (regularity recurrence and final tower
comparison in C.3, plus the dangling "recurrence in §6.3" reference). No mathematical error was found.
