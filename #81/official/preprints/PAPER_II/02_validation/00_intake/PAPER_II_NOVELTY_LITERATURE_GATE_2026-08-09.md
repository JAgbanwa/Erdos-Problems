# Paper II — Prior-art / novelty literature gate (release-gate resolution)

**Date:** 2026-08-09
**Scope:** resolves the release gate the preprint itself defers — *"the prior-art/novelty
assessment remain separate release gates"* (v1.1.8 status line).
**Method:** the disciplined literature gate (existence / collapse / saturation), plus quantifier
and verification checks. Sources: erdosproblems.com/81 (authoritative, last edited 2025-12-28),
arXiv, and general web/scholar indexing. zbMATH Open could not be queried automatically
(Cloudflare bot-challenge; not bypassed).

---

## 0. Claims under test

- **N1 (main theorem).** For every integer \(n\ge1\),
  \(\displaystyle \max_{\,|V(G)|=n,\ G\text{ chordal}}\bigl(|E(G)|-2\tau_3^*(G)\bigr)=\big\lfloor(2n+1)^2/24\big\rfloor\),
  attained by a complete-split graph \(S_{p,q}=K_p\vee\overline{K_q}\), \(p\) nearest \((2n+1)/6\).
- **N2 (method).** The *cover-first* proof: a two-direction vertex-copy exchange inequality on
  nonadjacent pairs, lifted by discrete convexity to whole clone classes, reducing the chordal
  extremum to the complete-split family, then a two-branch LP + integer maximization.
- **N3 (formalization).** A machine-checked Lean 4 / Mathlib v4.28.0 proof of N1, unconditional
  and axiom-clean (`#print axioms PaperII.theorem_1_2 = [propext, Classical.choice, Quot.sound]`).

---

## 1. Existence gate — does N1 already appear in the literature?

**Verdict: PASS (no prior appearance found).** No source states the maximum of the fractional
cover functional \(\Phi_\tau=|E|-2\tau_3^*\) over chordal graphs, in any form, and no source
carries the closed form \(\lfloor(2n+1)^2/24\rfloor\) for a chordal/triangle extremal quantity.
The nearest neighbours in the literature are demonstrably about **different objects**:

- **Erdős–Ordman–Zalcstein 1993 [EOZ93]** and **Chen–Erdős–Ordman 1994 [CEO94]** concern the
  **integral clique-partition** number of chordal (resp. split) graphs — best known bounds
  \((1/4-\varepsilon)n^2\) (chordal) and \(3n^2/16+O(n)\) (split). These are counting *cliques*,
  not evaluating \(|E|-2\tau_3^*\).
- **Tuza's conjecture** and its chordal partial results (holds for \(K_8\)-free / large-clique
  chordal graphs) bound the **integral** ratio \(\tau_3\le 2\nu_3\); they do not compute an exact
  extremal *value* of a fractional functional.
- Fractional-triangle literature (fractional Tuza \(\tau_3^*=\nu_3^*\); fractional triangle
  *decomposition* thresholds) supplies the LP-duality identity the paper uses as notation, but
  none determines \(\max_{\text{chordal}}(|E|-2\tau_3^*)\).

*Epistemic label:* this is a **negative search result** (absence of a found prior), not a proof of
absence; standard caveat. But the search was broad and the object is specific.

## 2. Collapse gate — is N1 a known theorem reworded?

**Verdict: PASS (does not collapse), with one flag the paper already handles correctly.**
N1 is a genuine extremal computation, not a disguised classical statement: the reduction to
complete-split terminals and the two-branch LP evaluation produce the floor by an argument with no
named predecessor. The one real collapse-risk is the **leading constant \(1/6\)**: Corollary 1.2
gives \(\Phi_\tau^{\max}=n^2/6+O(n)\), the *same* constant as the EOZ target for #81. This is a
**coincidence of leading constants between two different quantities** (an exact fractional-cover
maximum vs. a conjectural integral clique-partition upper bound), **not** an equivalence. The
manuscript states this explicitly and refuses the integral conclusion ("This comparison is
numerical rather than a consequence of class containment"; "the passage to an integral
clique-partition bound is not made here"). That framing is exactly right and must be preserved —
it is the single place a reader could over-claim a solution to #81.

## 3. Saturation gate — who is working this, and what is it reduced to?

**Verdict: territory is genuinely open and lightly worked; the elementary *integral* paths are
swept, and Paper II wisely does not attempt them.**

- **Erdős #81 (the integral problem) is OPEN.** Authoritative status, verbatim:
  *"OPEN — This is open, and cannot be resolved with a finite computation."* (erdosproblems.com/81,
  last edited 2025-12-28). Statement: can the edges of a chordal graph on \(n\) vertices be
  partitioned into \(n^2/6+O(n)\) cliques? Best bounds unchanged since the 1990s
  ([EOZ93], [CEO94]); the page lists **"Currently working on this problem: None."**
- No AI-assisted sweep or busy thread on #81 was found (2 forum comments; the page's only
  formalisation entry is **jtraverso** under "working on formalising the results" — i.e. this
  very project, not external competition).
- The **fractional cover functional \(\Phi_\tau\)** is a narrower, series-internal object;
  externally essentially unworked. So N1 sits in open, unswept space — precisely *because* it is
  not the integral #81 question but a well-posed exact sibling.

**Consequence for positioning:** the paper's honest scoping is not a weakness to hide but the
source of its novelty — it extracts an *exact, finite, formally verified* result from a
neighbourhood whose headline (integral) problem remains out of reach.

## 4. Quantifier discipline (∀ vs ∃)

N1 is a **∀-type** claim: an upper bound holding for *all* chordal \(G\) on \(n\) vertices,
**plus** an ∃-witness attaining it. Both halves are discharged in Lean (the bound *and* the
complete-split existence side), so the universal is genuinely proved, not sampled. No
experiment-masquerading-as-theorem risk. **PASS.**

## 5. Verify-before-believe

The load-bearing verification is the machine check itself, and it is maximal: the proof is
**unconditional** (no project axiom, no external hypothesis) and axiom-clean. There is no
impressive-but-unchecked external lemma carrying the argument. **PASS.**

## 6. Novelty of N3 (formalization)

**Verdict: PASS.** Mathlib has no chordal-graph theory (the reason the companion `Contrib/`
upstreaming effort exists); the DeepMind `formal-conjectures` repository offers a formalisation
slot for #81 but no deposited proof of this functional. A machine-checked, axiom-clean extremal
theorem for the fractional cover functional on chordal graphs appears to be new as a formal
artifact, independent of the mathematical novelty of N1.

---

## 7. Gate verdict

| Gate | N1 (theorem) | N2 (method) | N3 (formalization) |
|---|---|---|---|
| Existence | PASS | PASS | PASS |
| Collapse | PASS (flag 1/6 coincidence — handled) | PASS | — |
| Saturation | PASS (open, unswept sibling of #81) | PASS | PASS |
| Quantifier | PASS (∀ + ∃, both proved) | — | — |
| Verify | PASS (unconditional, axiom-clean) | — | PASS |

**Novelty status: RESOLVED — supports a novelty claim.** On the evidence gathered, the exact
value \(\lfloor(2n+1)^2/24\rfloor\) for \(\max_{\text{chordal}}(|E|-2\tau_3^*)\), its cover-first
proof, and its formal verification have no located prior in the literature, do not collapse to a
named result, and occupy genuinely open (and externally unworked) space adjacent to the still-open
Erdős #81.

**Residual risk (honest):** (i) negative search evidence is not proof of absence — zbMATH Open was
not machine-searchable this pass and should be checked by hand before final submission; (ii) the
result is a *sibling* of #81, not a solution — any wording drift toward "resolves/settles the
Erdős–Ordman–Zalcstein problem" would be false and must be blocked in copy-editing.

## 8. Recommended wording for the editor (drop-in)

> To our knowledge, the exact finite maximum of the fractional triangle-cover functional
> \(\Phi_\tau=|E|-2\tau_3^*\) over chordal graphs, its complete-split extremizers, and the closed
> form \(\lfloor(2n+1)^2/24\rfloor\) do not appear in the prior literature. The leading constant
> \(1/6\) coincides with the Erdős–Ordman–Zalcstein target for *integral* clique partitions of
> chordal graphs [EOZ93], which remains open; this coincidence is numerical and no integral
> clique-partition conclusion is drawn here.

**Bibliographic actions before submission:** cite [EOZ93], [CEO94] for the integral constants;
Tuza's conjecture + its fractional identity \(\tau_3^*=\nu_3^*\) for the LP-duality remark; and
the erdosproblems.com/81 status (open) for the program framing. Manual zbMATH Open pass
outstanding.

---
*Prepared as the prior-art/novelty release-gate artifact referenced in the v1.1.8 status line.
Sources: erdosproblems.com/81 (2025-12-28); [EOZ93] CPC 2(4) 1993, 409–415; [CEO94] split
\(3n^2/16\); Tuza's conjecture literature; arXiv indexing. zbMATH Open pending (bot-challenge).*
