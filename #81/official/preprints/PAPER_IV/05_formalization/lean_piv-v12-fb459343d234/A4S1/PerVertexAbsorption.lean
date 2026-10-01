import A4S1.HostAbsorption

/-!
# Per-vertex link usage, balanced selection, and the apex arithmetic

`A4S1.HostAbsorption.card_commonHosts_le` charges the links of a root vertex `a` that lie in
pieces with a second host to **all** host edges, which gives the global term `2 e(G[H])` at
every root vertex.  Here the charge is localized:

* `card_commonHosts_le_perVertex` — the non-singleton links of `a` towards common hosts are
  at most `(|R| - 1) + 2 c_a`, where `c_a` is the number of host edges lying in a piece of
  `Q₀` that contains `a`;
* `sum_card_pieceHostEdges_le` — `∑_{a ∈ R} c_a ≤ 2 e(G[H])`, because a piece of order at
  most four that contains a host edge has at most two root vertices.

Two pure statements complete the toolkit used by `A4S1.ApexChordalSharp`:

* `exists_balanced_selection` — for arbitrary costs `e_a` on a finite set `P` and a supply
  `F`, there is `S ⊆ P` with `|S| + e_a ≤ F` on `S`, and either `S = P` in size or
  `(|P| - |S|)(F - |S|) ≤ ∑_{a ∈ P} e_a`;
* `apex_arith` — the exact integer inequality that turns this selection, the RD09 ledger
  and the shift identity into the sharp bound.
-/

namespace A4S1.PerVertex

open Finset PaperIV.FarRounding A4S1.HostAbsorption

section Setting

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {x : V} {R : Finset V}
variable {G₀ : SimpleGraph V} [DecidableRel G₀.Adj]

/-- Host edges lying in a piece of `Q₀` that contains the root vertex `a`. -/
def pieceHostEdges (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (R : Finset V)
    (Q₀ : CliquePartition G₀) (a : V) : Finset (Sym2 V) :=
  (hostEdges G x R).filter fun e => ∃ K ∈ Q₀.pieces, a ∈ K ∧ e ∈ pairs K

/-- **Per-vertex link-usage bound.**  Among the common hosts of the root vertex `a`, all
but at most `(|R| - 1) + 2 c_a` are good, where `c_a = |pieceHostEdges a|`. -/
theorem card_commonHosts_le_perVertex
    (hG₀ : ∀ u v, G₀.Adj u v ↔ G.Adj u v ∧ u ≠ x ∧ v ≠ x)
    (hxR : x ∉ R) (Q₀ : CliquePartition G₀) {a : V} (haR : a ∈ R) :
    (commonHosts G x R a).card ≤
      ((commonHosts G x R a).filter fun h => ({a, h} : Finset V) ∈ Q₀.pieces).card +
        (R.erase a).card + 2 * (pieceHostEdges G x R Q₀ a).card := by
  set C := commonHosts G x R a with hCdef
  set Bad := C.filter fun h => ¬ ({a, h} : Finset V) ∈ Q₀.pieces with hBad
  have hsplit := Finset.card_filter_add_card_filter_not (s := C)
    (p := fun h => ({a, h} : Finset V) ∈ Q₀.pieces)
  have hax : a ≠ x := fun h => hxR (h ▸ haR)
  have hbadPiece : ∀ h ∈ Bad, ∃ K ∈ Q₀.pieces, a ∈ K ∧ h ∈ K ∧ ∃ w ∈ K, w ≠ a ∧ w ≠ h := by
    intro h hh
    rw [hBad, Finset.mem_filter, hCdef, commonHosts, Finset.mem_filter, mem_hosts] at hh
    obtain ⟨⟨⟨hhx, hhR⟩, -, hah⟩, hnot⟩ := hh
    have hG0 : G₀.Adj a h := (hG₀ a h).2 ⟨hah, hax, hhx⟩
    have hmem : s(a, h) ∈ G₀.edgeFinset := by simpa using hG0
    rw [← Q₀.covers, Finset.mem_biUnion] at hmem
    obtain ⟨K, hK, hpK⟩ := hmem
    rw [mk_mem_pairs] at hpK
    refine ⟨K, hK, hpK.1, hpK.2.1, ?_⟩
    by_contra hcon
    push_neg at hcon
    have hKeq : K = {a, h} := by
      ext w
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hw
        by_cases hwa : w = a
        · exact Or.inl hwa
        · exact Or.inr (hcon w hw hwa)
      · rintro (rfl | rfl)
        · exact hpK.1
        · exact hpK.2.1
    exact hnot (hKeq ▸ hK)
  set Bad2 := Bad.filter fun h => ∃ K ∈ Q₀.pieces, a ∈ K ∧ h ∈ K ∧
    ∃ h' ∈ K, h' ∈ hosts x R ∧ h' ≠ h with hBad2
  set Bad1 := Bad.filter fun h => ¬ ∃ K ∈ Q₀.pieces, a ∈ K ∧ h ∈ K ∧
    ∃ h' ∈ K, h' ∈ hosts x R ∧ h' ≠ h with hBad1
  have hsplit2 := Finset.card_filter_add_card_filter_not (s := Bad)
    (p := fun h => ∃ K ∈ Q₀.pieces, a ∈ K ∧ h ∈ K ∧ ∃ h' ∈ K, h' ∈ hosts x R ∧ h' ≠ h)
  -- `|Bad2| ≤ 2 c_a`
  have hB2 : Bad2.card * 1 ≤ (pieceHostEdges G x R Q₀ a).card * 2 := by
    refine Finset.card_mul_le_card_mul (fun h (e : Sym2 V) => h ∈ e) ?_ ?_
    · intro h hh
      rw [hBad2, Finset.mem_filter] at hh
      obtain ⟨hhB, K, hK, haK, hhK, h', hh'K, hh'H, hh'h⟩ := hh
      have hhH : h ∈ hosts x R := by
        rw [hBad, Finset.mem_filter, hCdef, commonHosts, Finset.mem_filter] at hhB
        exact hhB.1.1
      have hadj : G.Adj h h' :=
        ((hG₀ h h').1 (Q₀.isClique K hK h hhK h' hh'K hh'h.symm)).1
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
      refine ⟨s(h, h'), ?_⟩
      simp only [Finset.mem_bipartiteAbove, pieceHostEdges, hostEdges, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      refine ⟨⟨⟨hadj, ?_⟩, K, hK, haK, mk_mem_pairs.mpr ⟨hhK, hh'K, hh'h.symm⟩⟩,
        Sym2.mem_mk_left _ _⟩
      intro v hv
      rw [Sym2.mem_iff] at hv
      rcases hv with rfl | rfl
      · exact hhH
      · exact hh'H
    · intro e _
      induction e using Sym2.ind with
      | _ u v =>
        have hsub : Finset.bipartiteBelow (fun h (e : Sym2 V) => h ∈ e) Bad2 s(u, v) ⊆
            {u, v} := by
          intro w hw
          rw [Finset.mem_bipartiteBelow, Sym2.mem_iff] at hw
          rcases hw.2 with rfl | rfl <;> simp
        exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
  -- `|Bad1| ≤ |R| - 1`
  have hB1 : Bad1.card ≤ (R.erase a).card := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun h w => ∃ K ∈ Q₀.pieces, a ∈ K ∧ h ∈ K ∧ w ∈ K) ?_ ?_
    · intro h hh
      rw [hBad1, Finset.mem_filter] at hh
      obtain ⟨hhB, hno⟩ := hh
      obtain ⟨K, hK, haK, hhK, w, hwK, hwa, hwh⟩ := hbadPiece h hhB
      have hwx : w ≠ x := by
        intro hwx
        exact notMem_piece hG₀ Q₀ hK (hwx ▸ hwK)
      have hwR : w ∈ R := by
        by_contra hwR
        exact hno ⟨K, hK, haK, hhK, w, hwK, mem_hosts.mpr ⟨hwx, hwR⟩, hwh⟩
      exact ⟨w, Finset.mem_erase.mpr ⟨hwa, hwR⟩, K, hK, haK, hhK, hwK⟩
    · intro w hw h1 hh1 h2 hh2
      obtain ⟨hh1B, K1, hK1, haK1, hh1K1, hwK1⟩ := hh1
      obtain ⟨hh2B, K2, hK2, haK2, hh2K2, hwK2⟩ := hh2
      have hwa : w ≠ a := Finset.ne_of_mem_erase hw
      have hK : K1 = K2 := by
        by_contra hne
        have hd := Q₀.edgeDisjoint K1 hK1 K2 hK2 hne
        exact Finset.disjoint_left.mp hd (mk_mem_pairs.mpr ⟨haK1, hwK1, hwa.symm⟩)
          (mk_mem_pairs.mpr ⟨haK2, hwK2, hwa.symm⟩)
      subst hK
      by_contra h12
      have hh2H : h2 ∈ hosts x R := by
        rw [hBad1, Finset.mem_filter, hBad, Finset.mem_filter, hCdef, commonHosts,
          Finset.mem_filter] at hh2B
        exact hh2B.1.1.1
      rw [hBad1, Finset.mem_filter] at hh1B
      exact hh1B.2 ⟨K1, hK1, haK1, hh1K1, h2, hh2K2, hh2H, Ne.symm h12⟩
  have hs1 : ((C.filter fun h => ({a, h} : Finset V) ∈ Q₀.pieces).card) + Bad.card = C.card :=
    hsplit
  have hs2 : Bad2.card + Bad1.card = Bad.card := hsplit2
  omega

/-- **The per-vertex charges sum to at most `2 e(G[H])`.**  A host edge lies in exactly one
piece of `Q₀`; that piece has order at most four and contains the two hosts of the edge,
so it contains at most two root vertices. -/
theorem sum_card_pieceHostEdges_le (Q₀ : CliquePartition G₀) (hQ₀ : Q₀.OrderAtMost 4) :
    ∑ a ∈ R, (pieceHostEdges G x R Q₀ a).card ≤ 2 * (hostEdges G x R).card := by
  classical
  have hdc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := R) (t := hostEdges G x R)
    (r := fun a e => ∃ K ∈ Q₀.pieces, a ∈ K ∧ e ∈ pairs K)
  have hAbove : ∀ a ∈ R, (pieceHostEdges G x R Q₀ a).card =
      (Finset.bipartiteAbove (fun a e => ∃ K ∈ Q₀.pieces, a ∈ K ∧ e ∈ pairs K)
        (hostEdges G x R) a).card := by
    intro a _
    rfl
  rw [Finset.sum_congr rfl hAbove, hdc, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum ?_
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    have heH := (Finset.mem_filter.mp he)
    have huv : u ≠ v := by
      have hadj : G.Adj u v := by simpa using heH.1
      exact hadj.ne
    have huH : u ∈ hosts x R := heH.2 u (Sym2.mem_mk_left _ _)
    have hvH : v ∈ hosts x R := heH.2 v (Sym2.mem_mk_right _ _)
    by_cases hex : ∃ K ∈ Q₀.pieces, s(u, v) ∈ pairs K
    · obtain ⟨K, hK, heK⟩ := hex
      have hsub : Finset.bipartiteBelow (fun a e => ∃ K ∈ Q₀.pieces, a ∈ K ∧ e ∈ pairs K)
          R s(u, v) ⊆ (K.erase u).erase v := by
        intro a ha
        rw [Finset.mem_bipartiteBelow] at ha
        obtain ⟨haR, L, hL, haL, heL⟩ := ha
        have hLK : L = K := by
          by_contra hne
          exact Finset.disjoint_left.mp (Q₀.edgeDisjoint L hL K hK hne) heL heK
        subst hLK
        have hau : a ≠ u := fun h => (mem_hosts.mp huH).2 (h ▸ haR)
        have hav : a ≠ v := fun h => (mem_hosts.mp hvH).2 (h ▸ haR)
        exact Finset.mem_erase.mpr ⟨hav, Finset.mem_erase.mpr ⟨hau, haL⟩⟩
      have hueK := (mk_mem_pairs.mp heK)
      have h1 : ((K.erase u).erase v).card = K.card - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨huv.symm, hueK.2.1⟩),
          Finset.card_erase_of_mem hueK.1]
        omega
      have h2 := hQ₀ K hK
      have := Finset.card_le_card hsub
      omega
    · have hempty : Finset.bipartiteBelow (fun a e => ∃ K ∈ Q₀.pieces, a ∈ K ∧ e ∈ pairs K)
          R s(u, v) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_bipartiteBelow] at ha
        obtain ⟨-, L, hL, -, heL⟩ := ha
        exact hex ⟨L, hL, heL⟩
      rw [hempty]
      simp

end Setting

/-! ### Balanced selection -/

/-- **Balanced selection.**  For arbitrary costs `e` on a finite set `P` and an integer
supply `F`, there is `S ⊆ P` such that `|S| + e_a ≤ F` for every `a ∈ S`, and either
`|S| = |P|` or `(|P| - |S|)(F - |S|) ≤ ∑_{a ∈ P} e_a`. -/
theorem exists_balanced_selection {α : Type*} [DecidableEq α] (P : Finset α) (e : α → ℕ)
    (F : ℤ) :
    ∃ S ⊆ P, (∀ a ∈ S, (S.card : ℤ) + e a ≤ F) ∧
      (S.card = P.card ∨
        ((P.card : ℤ) - S.card) * (F - S.card) ≤ ∑ a ∈ P, (e a : ℤ)) := by
  classical
  let good : ℕ → Finset α := fun k => P.filter fun a => (k : ℤ) + e a ≤ F
  let Pr : ℕ → Prop := fun k => k ≤ (good k).card
  set s := Nat.findGreatest Pr P.card with hsdef
  have hsP : Pr s := Nat.findGreatest_spec (P := Pr) (m := 0) (Nat.zero_le _) (Nat.zero_le _)
  have hsle : s ≤ P.card := Nat.findGreatest_le _
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hsP
  have hSP : S ⊆ P := hSsub.trans (Finset.filter_subset _ _)
  refine ⟨S, hSP, ?_, ?_⟩
  · intro a ha
    have := (Finset.mem_filter.mp (hSsub ha)).2
    rw [hScard]; exact this
  · rw [hScard]
    by_cases hs : s = P.card
    · exact Or.inl hs
    right
    have hlt : s < P.card := lt_of_le_of_ne hsle hs
    have hnot : ¬ Pr (s + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self s) hlt
    have hnot' : (P.filter fun a => ((s + 1 : ℕ) : ℤ) + e a ≤ F).card < s + 1 := by
      simpa [Pr, good] using hnot
    have hsplit := Finset.card_filter_add_card_filter_not (s := P)
      (p := fun a => ((s + 1 : ℕ) : ℤ) + e a ≤ F)
    have hBcard : P.card - s ≤ (P.filter fun a => ¬ ((s + 1 : ℕ) : ℤ) + e a ≤ F).card := by
      omega
    have hBle : ∀ a ∈ P.filter fun a => ¬ ((s + 1 : ℕ) : ℤ) + e a ≤ F,
        F - s ≤ (e a : ℤ) := by
      intro a ha
      have := (Finset.mem_filter.mp ha).2
      push_cast at this
      linarith
    have hsum : ∑ a ∈ P.filter (fun a => ¬ ((s + 1 : ℕ) : ℤ) + e a ≤ F), (e a : ℤ) ≤
        ∑ a ∈ P, (e a : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.cast_nonneg _)
    have hsumB := Finset.card_nsmul_le_sum _ (fun a => (e a : ℤ)) (F - s) hBle
    rw [nsmul_eq_mul] at hsumB
    have hBc : ((P.card : ℤ) - s) ≤
        ((P.filter fun a => ¬ ((s + 1 : ℕ) : ℤ) + e a ≤ F).card : ℤ) := by
      have h := (Nat.cast_le (α := ℤ)).mpr hBcard
      rw [Nat.cast_sub hsle] at h; exact h
    by_cases hF : F - s ≤ 0
    · have h0 : 0 ≤ ∑ a ∈ P, (e a : ℤ) := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      have : ((P.card : ℤ) - s) * (F - s) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by omega) hF
      linarith
    · push_neg at hF
      have := mul_le_mul_of_nonneg_right hBc hF.le
      linarith

/-! ### The apex arithmetic -/

/-- **The apex arithmetic.**  Write `h = n - 1 - r` for the number of hosts, `q = 3r - n`,
`t = ρ + ν - h - 2s`.  Assume the window gap satisfies `gap ≥ 0`, `6 gap ≥ q(q+3)` and
`gap ≥ q` when `q ≥ 1`, and that the selection gives `s = ρ` or
`(ρ - s)(ν - r + 1 - s) ≤ E`.  Then `t ≤ gap + (117/7300) E` for `n ≥ 1000`. -/
theorem apex_arith (n r ρ ν s : ℤ) (gap E : ℚ)
    (hn : 1000 ≤ n) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s) (hsρ : s ≤ ρ) (hρr : ρ ≤ r)
    (hνh : ν ≤ n - 1 - r)
    (hgap0 : 0 ≤ gap) (hgapq : 1 ≤ 3 * r - n → ((3 * r - n : ℤ) : ℚ) ≤ gap)
    (hgapsq : (((3 * r - n) * (3 * r - n + 3) : ℤ) : ℚ) ≤ 6 * gap)
    (hE0 : 0 ≤ E) (hsel : s = ρ ∨ (((ρ - s) * (ν - r + 1 - s) : ℤ) : ℚ) ≤ E) :
    (((ρ + ν - (n - 1 - r) - 2 * s : ℤ)) : ℚ) ≤ gap + 117 / 7300 * E := by
  set t : ℤ := ρ + ν - (n - 1 - r) - 2 * s with ht
  by_cases htpos : t ≤ 0
  · have : (t : ℚ) ≤ 0 := by exact_mod_cast htpos
    nlinarith
  push_neg at htpos
  rcases hsel with hsρ' | hE
  · exfalso; subst hsρ'; omega
  set u : ℤ := ρ - s with hu
  set w : ℤ := n - 2 * r with hw
  set q : ℤ := 3 * r - n with hq
  have hid : ν - r + 1 - s = w - u + t := by rw [ht, hu, hw]; ring
  rw [hid] at hE
  have hut : t ≤ u := by omega
  have hur : u ≤ r := by omega
  by_cases huw : u ≤ w
  · have hg : t * w ≤ u * (w - u + t) := by nlinarith
    have hgQ : ((t * w : ℤ) : ℚ) ≤ E := le_trans (by exact_mod_cast hg) hE
    by_cases hw63 : 63 ≤ w
    · have h1 : ((t * 63 : ℤ) : ℚ) ≤ ((t * w : ℤ) : ℚ) := by
        exact_mod_cast (by nlinarith : t * 63 ≤ t * w)
      push_cast at h1 hgQ ⊢
      nlinarith
    · push_neg at hw63
      have hr469 : 469 ≤ r := by omega
      have hqr : r - 62 ≤ q := by omega
      have hkey : 6 * t ≤ q * (q + 3) := by nlinarith
      have hkeyQ : ((6 * t : ℤ) : ℚ) ≤ ((q * (q + 3) : ℤ) : ℚ) := by exact_mod_cast hkey
      push_cast at hkeyQ hgapsq ⊢
      nlinarith
  · push_neg at huw
    have hg : r * (t - q) ≤ u * (w - u + t) := by
      have : u * (w - u + t) - r * (t - q) = (r - u) * (u + r - w - t) := by
        rw [hq, hw]; ring
      nlinarith
    have hgQ : ((r * (t - q) : ℤ) : ℚ) ≤ E := le_trans (by exact_mod_cast hg) hE
    by_cases hq0 : q ≤ 0
    · by_cases hr63 : 63 ≤ r
      · have h1 : 63 * t ≤ r * (t - q) := by nlinarith
        have h1Q : ((63 * t : ℤ) : ℚ) ≤ E := le_trans (by exact_mod_cast h1) hgQ
        push_cast at h1Q ⊢
        nlinarith
      · push_neg at hr63
        have hkey : 6 * t ≤ q * (q + 3) := by nlinarith
        have hkeyQ : ((6 * t : ℤ) : ℚ) ≤ ((q * (q + 3) : ℤ) : ℚ) := by exact_mod_cast hkey
        push_cast at hkeyQ hgapsq ⊢
        nlinarith
    · push_neg at hq0
      have hgq := hgapq (by omega)
      by_cases htq : t ≤ q
      · have : (t : ℚ) ≤ (q : ℚ) := by exact_mod_cast htq
        push_cast at hgq ⊢
        nlinarith
      · push_neg at htq
        have h1 : 63 * (t - q) ≤ r * (t - q) := by
          have : 63 ≤ r := by omega
          nlinarith
        have h1Q : ((63 * (t - q) : ℤ) : ℚ) ≤ E := le_trans (by exact_mod_cast h1) hgQ
        push_cast at h1Q hgq ⊢
        nlinarith

end A4S1.PerVertex
