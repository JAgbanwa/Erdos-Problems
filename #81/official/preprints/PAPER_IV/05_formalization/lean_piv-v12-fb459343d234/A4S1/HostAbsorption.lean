import PaperIV.FarRounding
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Host absorption of the edges from a defective vertex into a root

Let `x` be a vertex of `G`, let `G₀` be the spanning subgraph of `G` that keeps exactly
the edges avoiding `x`, and let `Q₀` be an **arbitrary** clique partition of `G₀` with
pieces of order at most four.  Fix a set `R ∌ x` (the root) and put
`H = V ∖ (R ∪ {x})` (the hosts) and `m = e(G[H])`.

For a root vertex `a`, a host `h` is *common* if `x ~ h` and `a ~ h`, and *good* if
moreover the link `ah` is a singleton `K₂` piece of `Q₀`.

* `card_commonHosts_le` — **the link-usage bound.**  Whatever `Q₀` is,
  `|common(a)| ≤ |good(a)| + (|R| - 1) + 2m`.  A link `ah` lying in a larger piece `K`
  forces a third vertex of `K`: either a root vertex `w` (then the root edge `aw`
  identifies `h`) or a second host (then an edge of `G[H]` inside `K` is charged, at
  most twice).
* `exists_absorbed_partition` — **the absorption.**  If `S` is a set of root neighbours of
  `x` and every `a ∈ S` has at least `|S|` good hosts, then choosing distinct good hosts
  greedily and promoting every `x a h_a` to a triangle gives a clique partition of `G`
  with pieces of order at most four and exactly
  `|Q₀| + deg(x) - 2|S|` pieces.

Everything is physical: the triangles are triangles of the original graph `G`, and the
link `a h_a` is removed from `Q₀` only because it was a singleton piece there.
-/

namespace A4S1.HostAbsorption

open Finset PaperIV.FarRounding

/-! ### Greedy distinct representatives -/

/-- If each of the sets `L a` (`a ∈ S`) has at least `|S|` elements, there are distinct
representatives. -/
theorem exists_injOn_choice {α β : Type*} [DecidableEq α] [DecidableEq β] [Nonempty β]
    (S : Finset α) (L : α → Finset β) (hL : ∀ a ∈ S, S.card ≤ (L a).card) :
    ∃ f : α → β, (∀ a ∈ S, f a ∈ L a) ∧ Set.InjOn f S := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.arbitrary β, by simp, by simp⟩
  | @insert a S haS ih =>
    have hcard : (insert a S).card = S.card + 1 := Finset.card_insert_of_notMem haS
    obtain ⟨f', hf'L, hf'inj⟩ := ih (fun b hb => by
      have := hL b (Finset.mem_insert_of_mem hb); omega)
    have hlt : (S.image f').card < (L a).card := by
      have h1 := Finset.card_image_le (s := S) (f := f')
      have h2 := hL a (Finset.mem_insert_self a S)
      omega
    obtain ⟨v, hvL, hvnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨Function.update f' a v, ?_, ?_⟩
    · intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · simpa using hvL
      · have hba : b ≠ a := fun h => haS (h ▸ hb)
        rw [Function.update_of_ne hba]
        exact hf'L b hb
    · intro b hb c hc hbc
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hb hc
      rcases hb with rfl | hb <;> rcases hc with rfl | hc
      · rfl
      · have hca : c ≠ b := fun h => haS (h ▸ hc)
        rw [Function.update_self, Function.update_of_ne hca] at hbc
        exact absurd (hbc ▸ Finset.mem_image_of_mem f' hc) hvnot
      · have hba : b ≠ c := fun h => haS (h ▸ hb)
        rw [Function.update_self, Function.update_of_ne hba] at hbc
        exact absurd (hbc.symm ▸ Finset.mem_image_of_mem f' hb) hvnot
      · have hba : b ≠ a := fun h => haS (h ▸ hb)
        have hca : c ≠ a := fun h => haS (h ▸ hc)
        rw [Function.update_of_ne hba, Function.update_of_ne hca] at hbc
        exact hf'inj hb hc hbc

section Setting

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Two vertex sets sharing at most one vertex have disjoint pair sets. -/
theorem pairs_disjoint_of_inter_card_le_one {K L : Finset V} (h : (K ∩ L).card ≤ 1) :
    Disjoint (pairs K) (pairs L) := by
  rw [Finset.disjoint_left]
  intro e he hl
  induction e using Sym2.ind with
  | _ a b =>
    rw [mk_mem_pairs] at he hl
    have hsub : ({a, b} : Finset V) ⊆ K ∩ L := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨he.1, hl.1⟩
      · exact Finset.mem_inter.mpr ⟨he.2.1, hl.2.1⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair he.2.2] at h2
    omega

variable (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (R : Finset V)

/-- The hosts `H = V ∖ (R ∪ {x})`, written as in the comparator `{x}ᶜ ∖ R`. -/
def hosts : Finset V := ({x}ᶜ : Finset V) \ R

/-- The edges of `G[H]`. -/
def hostEdges : Finset (Sym2 V) := G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ hosts x R

/-- Hosts adjacent to both `x` and the root vertex `a`. -/
def commonHosts (a : V) : Finset V := (hosts x R).filter fun h => G.Adj x h ∧ G.Adj a h

/-- The **host-supply margin** of the root vertex `a`:
`|N_H(x) ∩ N_H(a)| - (|R| - 1) - 2 e(G[H])`. -/
def supplyMargin (a : V) : ℤ :=
  ((commonHosts G x R a).card : ℤ) - ((R.card : ℤ) - 1) - 2 * ((hostEdges G x R).card : ℤ)

variable {G x R}
variable {G₀ : SimpleGraph V} [DecidableRel G₀.Adj]

theorem mem_hosts {h : V} : h ∈ hosts x R ↔ h ≠ x ∧ h ∉ R := by
  simp [hosts]

omit [DecidableRel G.Adj] in
/-- Pieces of a partition of `G₀` avoid `x`. -/
theorem notMem_piece (hG₀ : ∀ u v, G₀.Adj u v ↔ G.Adj u v ∧ u ≠ x ∧ v ≠ x)
    (Q₀ : CliquePartition G₀) {K : Finset V} (hK : K ∈ Q₀.pieces) : x ∉ K := by
  classical
  intro hxK
  have h2 := Q₀.two_le_card K hK
  obtain ⟨b, hbK, hbx⟩ : ∃ b ∈ K, b ≠ x := by
    by_contra hcon
    push_neg at hcon
    have : K ⊆ {x} := fun b hb => Finset.mem_singleton.mpr (hcon b hb)
    have := Finset.card_le_card this
    simp at this; omega
  exact ((hG₀ x b).1 (Q₀.isClique K hK x hxK b hbK hbx.symm)).2.1 rfl

/-- **The link-usage bound**, valid for an arbitrary order-four partition `Q₀` of `G₀`.
Among the common hosts of a root vertex `a`, all but at most `(|R| - 1) + 2 e(G[H])` are
good, i.e. their link to `a` is a singleton piece of `Q₀`. -/
theorem card_commonHosts_le (hG₀ : ∀ u v, G₀.Adj u v ↔ G.Adj u v ∧ u ≠ x ∧ v ≠ x)
    (hxR : x ∉ R) (Q₀ : CliquePartition G₀) {a : V} (haR : a ∈ R) :
    (commonHosts G x R a).card ≤
      ((commonHosts G x R a).filter fun h => ({a, h} : Finset V) ∈ Q₀.pieces).card +
        (R.erase a).card + 2 * (hostEdges G x R).card := by
  set C := commonHosts G x R a with hCdef
  set Bad := C.filter fun h => ¬ ({a, h} : Finset V) ∈ Q₀.pieces with hBad
  have hsplit := Finset.card_filter_add_card_filter_not (s := C)
    (p := fun h => ({a, h} : Finset V) ∈ Q₀.pieces)
  have hax : a ≠ x := fun h => hxR (h ▸ haR)
  -- every bad host lies in a larger piece with `a`
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
  -- `|Bad2| ≤ 2 e(G[H])`
  have hB2 : Bad2.card * 1 ≤ (hostEdges G x R).card * 2 := by
    refine Finset.card_mul_le_card_mul (fun h (e : Sym2 V) => h ∈ e) ?_ ?_
    · intro h hh
      rw [hBad2, Finset.mem_filter] at hh
      obtain ⟨hhB, K, hK, -, hhK, h', hh'K, hh'H, hh'h⟩ := hh
      have hhH : h ∈ hosts x R := by
        rw [hBad, Finset.mem_filter, hCdef, commonHosts, Finset.mem_filter] at hhB
        exact hhB.1.1
      have hadj : G.Adj h h' :=
        ((hG₀ h h').1 (Q₀.isClique K hK h hhK h' hh'K hh'h.symm)).1
      rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
      refine ⟨s(h, h'), ?_⟩
      simp only [Finset.mem_bipartiteAbove, hostEdges, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      refine ⟨⟨hadj, ?_⟩, Sym2.mem_mk_left _ _⟩
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

/-- **Absorption of the root edges of `x`.**  Let `S` be a set of root vertices adjacent
to `x` such that each `a ∈ S` has at least `|S|` good hosts for `Q₀`.  Then `G` has a clique
partition with pieces of order at most four and exactly `|Q₀| + deg(x) - 2|S|` pieces:
the triangles `x a h_a` (distinct good hosts `h_a`) replace the singleton links `a h_a`,
and every other edge at `x` is a singleton piece. -/
theorem exists_absorbed_partition (hG₀ : ∀ u v, G₀.Adj u v ↔ G.Adj u v ∧ u ≠ x ∧ v ≠ x)
    (hxR : x ∉ R) (Q₀ : CliquePartition G₀) (hQ₀ : Q₀.OrderAtMost 4)
    (S : Finset V) (hSR : S ⊆ R) (hSx : ∀ a ∈ S, G.Adj x a)
    (hgood : ∀ a ∈ S, S.card ≤
      ((commonHosts G x R a).filter fun h => ({a, h} : Finset V) ∈ Q₀.pieces).card) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + 2 * S.card = Q₀.size + (G.neighborFinset x).card := by
  haveI : Nonempty V := ⟨x⟩
  obtain ⟨f, hfL, hfinj⟩ := exists_injOn_choice S
    (fun a => (commonHosts G x R a).filter fun h => ({a, h} : Finset V) ∈ Q₀.pieces) hgood
  -- properties of the chosen hosts
  have hf : ∀ a ∈ S, f a ∈ hosts x R ∧ G.Adj x (f a) ∧ G.Adj a (f a) ∧
      ({a, f a} : Finset V) ∈ Q₀.pieces := by
    intro a ha
    have := hfL a ha
    simp only [commonHosts, Finset.mem_filter] at this
    exact ⟨this.1.1, this.1.2.1, this.1.2.2, this.2⟩
  have hSxne : ∀ a ∈ S, a ≠ x := fun a ha h => hxR (h ▸ hSR ha)
  have hfx : ∀ a ∈ S, f a ≠ x := fun a ha => (mem_hosts.mp (hf a ha).1).1
  have hfS : ∀ a ∈ S, f a ∉ S := fun a ha h => (mem_hosts.mp (hf a ha).1).2 (hSR h)
  have hfa : ∀ a ∈ S, f a ≠ a := fun a ha h => hfS a ha (by rw [h]; exact ha)
  set Fs := S.image f with hFs
  set Rem := S.image fun a => ({a, f a} : Finset V) with hRem
  set Tri := S.image fun a => ({x, a, f a} : Finset V) with hTri
  set Nx := (G.neighborFinset x) \ (S ∪ Fs) with hNx
  set Spk := Nx.image fun y => ({x, y} : Finset V) with hSpk
  set Old := Q₀.pieces \ Rem with hOld
  have hmemFs : ∀ {y}, y ∈ Fs ↔ ∃ a ∈ S, f a = y := by
    intro y; rw [hFs, Finset.mem_image]
  have hxOld : ∀ K ∈ Old, x ∉ K := fun K hK =>
    notMem_piece hG₀ Q₀ (Finset.mem_sdiff.mp hK).1
  -- the three families
  have hRemsub : Rem ⊆ Q₀.pieces := by
    intro K hK
    rw [hRem, Finset.mem_image] at hK
    obtain ⟨a, ha, rfl⟩ := hK
    exact (hf a ha).2.2.2
  have hRemcard : Rem.card = S.card := by
    rw [hRem]
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have hab' : ({a, f a} : Finset V) = {b, f b} := hab
    have : a ∈ ({b, f b} : Finset V) := hab' ▸ Finset.mem_insert_self a _
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact h
    · exact absurd (by rw [← h]; exact ha) (hfS b hb)
  have hTricard : Tri.card = S.card := by
    rw [hTri]
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    have hab' : ({x, a, f a} : Finset V) = {x, b, f b} := hab
    have : a ∈ ({x, b, f b} : Finset V) := hab' ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h
    · exact absurd h (hSxne a ha)
    · exact h
    · exact absurd (by rw [← h]; exact ha) (hfS b hb)
  have hFscard : Fs.card = S.card := Finset.card_image_of_injOn hfinj
  have hSFs : Disjoint S Fs := by
    rw [Finset.disjoint_left]
    intro a ha haF
    obtain ⟨b, hb, rfl⟩ := hmemFs.mp haF
    exact hfS b hb ha
  have hSFsub : S ∪ Fs ⊆ G.neighborFinset x := by
    intro y hy
    rw [SimpleGraph.mem_neighborFinset]
    rcases Finset.mem_union.mp hy with hy | hy
    · exact hSx y hy
    · obtain ⟨a, ha, rfl⟩ := hmemFs.mp hy
      exact (hf a ha).2.1
  have hNxcard : Nx.card + 2 * S.card = (G.neighborFinset x).card := by
    rw [hNx, Finset.card_sdiff_of_subset hSFsub, Finset.card_union_of_disjoint hSFs, hFscard]
    have := Finset.card_le_card hSFsub
    rw [Finset.card_union_of_disjoint hSFs, hFscard] at this
    omega
  have hSpkcard : Spk.card = Nx.card := by
    rw [hSpk]
    refine Finset.card_image_of_injOn ?_
    intro y hy z hz hyz
    have hyz' : ({x, y} : Finset V) = {x, z} := hyz
    have hyx : y ≠ x := fun h => by
      have := (Finset.mem_sdiff.mp hy).1
      rw [SimpleGraph.mem_neighborFinset, h] at this
      exact G.irrefl this
    have : y ∈ ({x, z} : Finset V) := hyz' ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h
    · exact absurd h hyx
    · exact h
  -- membership descriptions
  have hTrimem : ∀ {K}, K ∈ Tri ↔ ∃ a ∈ S, ({x, a, f a} : Finset V) = K := by
    intro K; rw [hTri, Finset.mem_image]
  have hSpkmem : ∀ {K}, K ∈ Spk ↔ ∃ y ∈ Nx, ({x, y} : Finset V) = K := by
    intro K; rw [hSpk, Finset.mem_image]
  have hNxmem : ∀ {y}, y ∈ Nx ↔ G.Adj x y ∧ y ∉ S ∧ y ∉ Fs := by
    intro y
    rw [hNx, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset, Finset.mem_union]
    tauto
  have hyNx : ∀ {y}, y ∈ Nx → y ≠ x := fun {y} hy h =>
    G.irrefl (h ▸ (hNxmem.mp hy).1)
  -- cardinality of the new pieces
  have htri3 : ∀ a ∈ S, ({x, a, f a} : Finset V).card = 3 := by
    intro a ha
    rw [Finset.card_insert_of_notMem, Finset.card_pair (hfa a ha).symm]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(hSxne a ha).symm, (hfx a ha).symm⟩
  have hspk2 : ∀ y ∈ Nx, ({x, y} : Finset V).card = 2 := fun y hy =>
    Finset.card_pair (hyNx hy).symm
  -- disjointness of the three families
  have hOT : Disjoint Old Tri := by
    rw [Finset.disjoint_left]
    intro K hK hKT
    obtain ⟨a, -, rfl⟩ := hTrimem.mp hKT
    exact hxOld _ hK (by simp)
  have hOS : Disjoint Old Spk := by
    rw [Finset.disjoint_left]
    intro K hK hKS
    obtain ⟨y, -, rfl⟩ := hSpkmem.mp hKS
    exact hxOld _ hK (by simp)
  have hTS : Disjoint Tri Spk := by
    rw [Finset.disjoint_left]
    intro K hKT hKS
    obtain ⟨a, ha, rfl⟩ := hTrimem.mp hKT
    obtain ⟨y, hy, hEq⟩ := hSpkmem.mp hKS
    have h1 := htri3 a ha
    rw [← hEq, hspk2 y hy] at h1
    omega
  set pieces := Old ∪ Tri ∪ Spk with hpieces
  have hcard : pieces.card = Old.card + Tri.card + Spk.card := by
    rw [hpieces, Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hOS, hTS⟩),
      Finset.card_union_of_disjoint hOT]
  have hOldcard : Old.card + S.card = Q₀.size := by
    rw [hOld, Finset.card_sdiff_of_subset hRemsub, hRemcard]
    have := Finset.card_le_card hRemsub
    rw [hRemcard] at this
    show Q₀.pieces.card - S.card + S.card = Q₀.pieces.card
    omega
  -- cliques
  have hcl : ∀ K ∈ pieces, ∀ u ∈ K, ∀ v ∈ K, u ≠ v → G.Adj u v := by
    intro K hK u hu v hv huv
    rcases Finset.mem_union.mp hK with hK | hK
    · rcases Finset.mem_union.mp hK with hK | hK
      · exact ((hG₀ u v).1 (Q₀.isClique K (Finset.mem_sdiff.mp hK).1 u hu v hv huv)).1
      · obtain ⟨a, ha, rfl⟩ := hTrimem.mp hK
        obtain ⟨-, hxf, haf, -⟩ := hf a ha
        have hxa := hSx a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
          first
          | exact absurd rfl huv
          | assumption
          | exact G.symm ‹_›
    · obtain ⟨y, hy, rfl⟩ := hSpkmem.mp hK
      have hxy := (hNxmem.mp hy).1
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact absurd rfl huv
      · exact hxy
      · exact hxy.symm
      · exact absurd rfl huv
  -- pairwise edge-disjointness, one ordered case at a time
  have hTT : ∀ a ∈ S, ∀ b ∈ S, a ≠ b →
      Disjoint (pairs ({x, a, f a} : Finset V)) (pairs {x, b, f b}) := by
    intro a ha b hb hab
    apply pairs_disjoint_of_inter_card_le_one
    have hsub : ({x, a, f a} : Finset V) ∩ {x, b, f b} ⊆ {x} := by
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      obtain ⟨h1, h2⟩ := hv
      rcases h1 with rfl | rfl | rfl
      · rfl
      · rcases h2 with h | h | h
        · exact h
        · exact absurd h hab
        · exact absurd (h ▸ ha) (hfS b hb)
      · rcases h2 with h | h | h
        · exact h
        · exact absurd (h.symm ▸ hb) (hfS a ha)
        · exact absurd (hfinj ha hb h) hab
    exact (Finset.card_le_card hsub).trans (by simp)
  have hTSp : ∀ a ∈ S, ∀ y ∈ Nx, Disjoint (pairs ({x, a, f a} : Finset V)) (pairs {x, y}) := by
    intro a ha y hy
    apply pairs_disjoint_of_inter_card_le_one
    have hsub : ({x, a, f a} : Finset V) ∩ {x, y} ⊆ {x} := by
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      obtain ⟨h1, h2⟩ := hv
      rcases h2 with h | rfl
      · exact h
      · exfalso
        obtain ⟨-, hyS, hyF⟩ := hNxmem.mp hy
        rcases h1 with h | h | h
        · exact hyNx hy h
        · exact hyS (h ▸ ha)
        · exact hyF (hmemFs.mpr ⟨a, ha, h.symm⟩)
    exact (Finset.card_le_card hsub).trans (by simp)
  have hSS : ∀ y ∈ Nx, ∀ z ∈ Nx, y ≠ z → Disjoint (pairs ({x, y} : Finset V)) (pairs {x, z}) := by
    intro y _ z _ hyz
    apply pairs_disjoint_of_inter_card_le_one
    have hsub : ({x, y} : Finset V) ∩ {x, z} ⊆ {x} := by
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      rcases hv with ⟨h1 | rfl, h2 | h2⟩
      · exact h1
      · exact h1
      · exact h2
      · exact absurd h2 hyz
    exact (Finset.card_le_card hsub).trans (by simp)
  have hOSp : ∀ K ∈ Old, ∀ y ∈ Nx, Disjoint (pairs K) (pairs {x, y}) := by
    intro K hK y _
    apply pairs_disjoint_of_inter_card_le_one
    have hsub : K ∩ {x, y} ⊆ {y} := by
      intro v hv
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      rcases hv with ⟨hvK, rfl | rfl⟩
      · exact absurd hvK (hxOld K hK)
      · rfl
    exact (Finset.card_le_card hsub).trans (by simp)
  have hOTr : ∀ K ∈ Old, ∀ a ∈ S, Disjoint (pairs K) (pairs ({x, a, f a} : Finset V)) := by
    intro K hK a ha
    rw [Finset.disjoint_left]
    intro e heK heT
    induction e using Sym2.ind with
    | _ u v =>
      rw [mk_mem_pairs] at heK heT
      obtain ⟨huK, hvK, huv⟩ := heK
      have hux : u ≠ x := fun h => hxOld K hK (h ▸ huK)
      have hvx : v ≠ x := fun h => hxOld K hK (h ▸ hvK)
      have hu : u = a ∨ u = f a := by
        have := heT.1; simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
      have hv : v = a ∨ v = f a := by
        have := heT.2.1; simp only [Finset.mem_insert, Finset.mem_singleton] at this; tauto
      have haK : a ∈ K ∧ f a ∈ K := by
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact absurd rfl huv
        · exact ⟨huK, hvK⟩
        · exact ⟨hvK, huK⟩
        · exact absurd rfl huv
      have hKmem := (Finset.mem_sdiff.mp hK)
      have hne : K ≠ {a, f a} := by
        intro h
        exact hKmem.2 (by rw [hRem, Finset.mem_image]; exact ⟨a, ha, h.symm⟩)
      have hd := Q₀.edgeDisjoint K hKmem.1 _ (hf a ha).2.2.2 hne
      exact Finset.disjoint_left.mp hd (mk_mem_pairs.mpr ⟨haK.1, haK.2, (hfa a ha).symm⟩)
        (mk_mem_pairs.mpr ⟨by simp, by simp, (hfa a ha).symm⟩)
  have hdisj : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L) := by
    intro K hK L hL hKL
    rcases Finset.mem_union.mp hK with hK | hK <;> rcases Finset.mem_union.mp hL with hL | hL
    · rcases Finset.mem_union.mp hK with hK | hK <;> rcases Finset.mem_union.mp hL with hL | hL
      · exact Q₀.edgeDisjoint K (Finset.mem_sdiff.mp hK).1 L (Finset.mem_sdiff.mp hL).1 hKL
      · obtain ⟨a, ha, rfl⟩ := hTrimem.mp hL
        exact hOTr K hK a ha
      · obtain ⟨a, ha, rfl⟩ := hTrimem.mp hK
        exact (hOTr L hL a ha).symm
      · obtain ⟨a, ha, rfl⟩ := hTrimem.mp hK
        obtain ⟨b, hb, rfl⟩ := hTrimem.mp hL
        exact hTT a ha b hb (fun h => hKL (h ▸ rfl))
    · obtain ⟨y, hy, rfl⟩ := hSpkmem.mp hL
      rcases Finset.mem_union.mp hK with hK | hK
      · exact hOSp K hK y hy
      · obtain ⟨a, ha, rfl⟩ := hTrimem.mp hK
        exact hTSp a ha y hy
    · obtain ⟨y, hy, rfl⟩ := hSpkmem.mp hK
      rcases Finset.mem_union.mp hL with hL | hL
      · exact (hOSp L hL y hy).symm
      · obtain ⟨a, ha, rfl⟩ := hTrimem.mp hL
        exact (hTSp a ha y hy).symm
    · obtain ⟨y, hy, rfl⟩ := hSpkmem.mp hK
      obtain ⟨z, hz, rfl⟩ := hSpkmem.mp hL
      exact hSS y hy z hz (fun h => hKL (h ▸ rfl))
  -- covering
  have hcov : pieces.biUnion pairs = G.edgeFinset := by
    ext e
    constructor
    · intro he
      rw [Finset.mem_biUnion] at he
      obtain ⟨K, hK, heK⟩ := he
      induction e using Sym2.ind with
      | _ u v =>
        rw [mk_mem_pairs] at heK
        simpa using hcl K hK u heK.1 v heK.2.1 heK.2.2
    · intro he
      rw [Finset.mem_biUnion]
      induction e using Sym2.ind with
      | _ u v =>
        have huv : G.Adj u v := by simpa using he
        -- edges at `x`
        have hat : ∀ y, G.Adj x y → ∃ K ∈ pieces, s(x, y) ∈ pairs K := by
          intro y hxy
          have hyx : y ≠ x := fun h => G.irrefl (h ▸ hxy)
          by_cases hyS : y ∈ S
          · refine ⟨{x, y, f y}, ?_, mk_mem_pairs.mpr ⟨by simp, by simp, hyx.symm⟩⟩
            exact Finset.mem_union_left _ (Finset.mem_union_right _ (hTrimem.mpr ⟨y, hyS, rfl⟩))
          · by_cases hyF : y ∈ Fs
            · obtain ⟨a, ha, rfl⟩ := hmemFs.mp hyF
              refine ⟨{x, a, f a}, ?_, mk_mem_pairs.mpr ⟨by simp, by simp, (hfx a ha).symm⟩⟩
              exact Finset.mem_union_left _
                (Finset.mem_union_right _ (hTrimem.mpr ⟨a, ha, rfl⟩))
            · refine ⟨{x, y}, ?_, mk_mem_pairs.mpr ⟨by simp, by simp, hyx.symm⟩⟩
              exact Finset.mem_union_right _ (hSpkmem.mpr ⟨y, hNxmem.mpr ⟨hxy, hyS, hyF⟩, rfl⟩)
        by_cases hux : u = x
        · subst hux; exact hat v huv
        · by_cases hvx : v = x
          · subst hvx
            obtain ⟨K, hK, hKp⟩ := hat u huv.symm
            exact ⟨K, hK, by rw [Sym2.eq_swap]; exact hKp⟩
          · have hG0 : G₀.Adj u v := (hG₀ u v).2 ⟨huv, hux, hvx⟩
            have hmem : s(u, v) ∈ G₀.edgeFinset := by simpa using hG0
            rw [← Q₀.covers, Finset.mem_biUnion] at hmem
            obtain ⟨K, hK, hKp⟩ := hmem
            by_cases hKR : K ∈ Rem
            · rw [hRem, Finset.mem_image] at hKR
              obtain ⟨a, ha, rfl⟩ := hKR
              refine ⟨{x, a, f a}, Finset.mem_union_left _
                (Finset.mem_union_right _ (hTrimem.mpr ⟨a, ha, rfl⟩)), ?_⟩
              rw [mk_mem_pairs] at hKp ⊢
              refine ⟨?_, ?_, hKp.2.2⟩
              · have := hKp.1; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
                tauto
              · have := hKp.2.1; simp only [Finset.mem_insert, Finset.mem_singleton] at this ⊢
                tauto
            · exact ⟨K, Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_sdiff.mpr ⟨hK, hKR⟩)), hKp⟩
  let Q : CliquePartition G :=
    { pieces := pieces
      isClique := hcl
      two_le_card := by
        intro K hK
        rcases Finset.mem_union.mp hK with hK | hK
        · rcases Finset.mem_union.mp hK with hK | hK
          · exact Q₀.two_le_card K (Finset.mem_sdiff.mp hK).1
          · obtain ⟨a, ha, rfl⟩ := hTrimem.mp hK
            rw [htri3 a ha]; omega
        · obtain ⟨y, hy, rfl⟩ := hSpkmem.mp hK
          rw [hspk2 y hy]
      edgeDisjoint := hdisj
      covers := hcov }
  refine ⟨Q, ?_, ?_⟩
  · intro K hK
    change K ∈ pieces at hK
    rcases Finset.mem_union.mp hK with hK | hK
    · rcases Finset.mem_union.mp hK with hK | hK
      · exact hQ₀ K (Finset.mem_sdiff.mp hK).1
      · obtain ⟨a, ha, rfl⟩ := hTrimem.mp hK
        rw [htri3 a ha]; omega
    · obtain ⟨y, hy, rfl⟩ := hSpkmem.mp hK
      rw [hspk2 y hy]; omega
  · show pieces.card + 2 * S.card = Q₀.pieces.card + (G.neighborFinset x).card
    rw [hcard, hTricard, hSpkcard]
    have : Q₀.pieces.card = Q₀.size := rfl
    omega

/-- **Absorption from the supply margin.**  If `S` is a set of root neighbours of `x` and
`|S|` does not exceed the host-supply margin of any `a ∈ S`, then for **every** order-four
partition `Q₀` of `G₀` there is an order-four partition of `G` with
`|Q₀| + deg(x) - 2|S|` pieces. -/
theorem exists_absorbed_partition_of_margin
    (hG₀ : ∀ u v, G₀.Adj u v ↔ G.Adj u v ∧ u ≠ x ∧ v ≠ x)
    (hxR : x ∉ R) (Q₀ : CliquePartition G₀) (hQ₀ : Q₀.OrderAtMost 4)
    (S : Finset V) (hSR : S ⊆ R) (hSx : ∀ a ∈ S, G.Adj x a)
    (hmargin : ∀ a ∈ S, (S.card : ℤ) ≤ supplyMargin G x R a) :
    ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧
      Q.size + 2 * S.card = Q₀.size + (G.neighborFinset x).card := by
  refine exists_absorbed_partition hG₀ hxR Q₀ hQ₀ S hSR hSx ?_
  intro a ha
  have h1 := card_commonHosts_le hG₀ hxR Q₀ (hSR ha)
  have h2 := hmargin a ha
  have h3 : (R.erase a).card = R.card - 1 := Finset.card_erase_of_mem (hSR ha)
  have h4 : 1 ≤ R.card := Finset.card_pos.mpr ⟨a, hSR ha⟩
  unfold supplyMargin at h2
  omega

end Setting

end A4S1.HostAbsorption
