/-
# The general web wall: any routing with at most five free clusters fails

`BKLO/HexWall.lean` refutes the corner mechanism and `BKLO/CrossHexWall.lean` refutes the closed
cross-patch gadget of `BKLO/CrossHexGadget.lean`.  Both refutations run the same argument, and this
file isolates it once and for all, for an arbitrary routing.

Whatever gadget a reservoir is asked to place at a leftover six-cycle, its clusters are found one
after another, each new one pinned to the ones already found.  Three kinds of step are allowed:

* `WebInstr.free` — a cluster chosen freely in the family: at most `|𝒞| ≤ |V| m / 7` ways;
* `WebInstr.meets i` — a cluster meeting an already-chosen cluster: at most `7m` ways;
* `WebInstr.dbl i j` — a cluster meeting two already-chosen clusters in two *distinct* vertices:
  at most `49` ways, because two distinct vertices lie in at most one common cluster.

`BKLO.card_websOf_le` counts the resulting webs, and `BKLO.card_webCovered_le` the six-cycles they
serve: at most `7^{10+2D} |V| m⁵ / 7`, where `D` is the number of `dbl` steps, as soon as the
schedule has **one** free step and **at most four** `meets` steps.  `BKLO.not_webReservoir` turns
this into the wall: a cluster family of maximum reserved degree `d` with `1000 · 7^{10+2D} d ≤ |V|`
cannot serve every six-cycle of unreserved edges, no matter what the schedule and no matter which
of its clusters are asked to hold the six leftover vertices.

This is the definitive form of the obstruction met by the corner mechanism and by the cross-patch
mechanism alike: a leftover six-cycle has `|V|⁶` positions, and a *connected* web of clusters
through six prescribed vertices — one free cluster, four singly-pinned ones, all the rest doubly
pinned — has only `O(|V| m⁵)`.  What a gadget would need is a sixth degree of freedom, i.e. a fifth
`meets` step; the routings that close have at most four, since each further free step must be paid
for by an extra cluster and the clusters must still close up around the leftover cycle.

Everything in this file is `sorry`-free.
-/
import BKLO.CrossHexWall

open Finset

namespace BKLO

/-! ### Schedules -/

/-- One step of a web: a cluster chosen freely, a cluster meeting the `i`-th cluster chosen so far,
or a cluster meeting the `i`-th and the `j`-th in two distinct vertices.  Positions are counted
from the most recent choice. -/
inductive WebInstr where
  /-- a cluster chosen freely in the family -/
  | free : WebInstr
  /-- a cluster meeting the `i`-th cluster already chosen -/
  | meets : ℕ → WebInstr
  /-- a cluster meeting the `i`-th and the `j`-th already chosen, in two distinct vertices -/
  | dbl : ℕ → ℕ → WebInstr
  deriving DecidableEq

variable {V : Type*} [DecidableEq V]

/-- The clusters a step may choose from, given the choices made so far. -/
def instrSet (𝒞 : Finset (Finset V)) (l : List (Finset V)) : WebInstr → Finset (Finset V)
  | .free => 𝒞
  | .meets i => meetsCl 𝒞 (l.getD i ∅)
  | .dbl i j => dblMeets 𝒞 (l.getD i ∅) (l.getD j ∅)

theorem instrSet_subset {𝒞 : Finset (Finset V)} {l : List (Finset V)} {s : WebInstr} :
    instrSet 𝒞 l s ⊆ 𝒞 := by
  cases s with
  | free => exact Finset.Subset.refl _
  | meets i => exact meetsCl_subset
  | dbl i j => exact dblMeets_subset

/-- The number of choices a step offers. -/
def instrWeight (c m : ℕ) : WebInstr → ℕ
  | .free => c
  | .meets _ => 7 * m
  | .dbl _ _ => 49

theorem card_instrSet_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m)
    {l : List (Finset V)} (hl : ∀ C ∈ l, C.card ≤ 7) (s : WebInstr) :
    (instrSet 𝒞 l s).card ≤ instrWeight 𝒞.card m s := by
  cases s with
  | free => exact le_rfl
  | meets i => exact card_meetsCl_le hm (getD_card_le hl i)
  | dbl i j => exact card_dblMeets_le h𝒞 (getD_card_le hl i) (getD_card_le hl j)

/-- The webs a schedule can produce, recorded as lists of clusters, most recent first. -/
def websOf (𝒞 : Finset (Finset V)) (sched : List WebInstr) : Finset (List (Finset V)) :=
  sched.foldl (fun L s => cstep L (fun l => instrSet 𝒞 l s)) {[]}

/-- **The web count.**  Every cluster in a web is a cluster of the family, and the number of webs
is at most the product of the weights of the steps. -/
theorem card_websOf_aux {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) :
    ∀ (sched : List WebInstr) (L : Finset (List (Finset V))),
      (∀ l ∈ L, ∀ C ∈ l, C.card ≤ 7) →
        (∀ l ∈ sched.foldl (fun L s => cstep L (fun l => instrSet 𝒞 l s)) L, ∀ C ∈ l,
            C.card ≤ 7) ∧
          (sched.foldl (fun L s => cstep L (fun l => instrSet 𝒞 l s)) L).card ≤
            L.card * (sched.map (instrWeight 𝒞.card m)).prod := by
  have h7 : ∀ C ∈ 𝒞, C.card ≤ 7 := fun C hC => le_of_eq (h𝒞.1 C hC)
  intro sched
  induction sched with
  | nil => intro L hL; exact ⟨hL, by simp⟩
  | cons s rest ih =>
    intro L hL
    have hstep7 : ∀ l ∈ cstep L (fun l => instrSet 𝒞 l s), ∀ C ∈ l, C.card ≤ 7 :=
      cstep_seven h7 hL (fun _ => instrSet_subset)
    have hstepcard : (cstep L (fun l => instrSet 𝒞 l s)).card ≤ L.card * instrWeight 𝒞.card m s :=
      card_cstep (fun l hl => card_instrSet_le h𝒞 hm (hL l hl) s)
    obtain ⟨hrest7, hrestcard⟩ := ih (cstep L (fun l => instrSet 𝒞 l s)) hstep7
    refine ⟨hrest7, hrestcard.trans ?_⟩
    calc (cstep L (fun l => instrSet 𝒞 l s)).card * (rest.map (instrWeight 𝒞.card m)).prod
        ≤ (L.card * instrWeight 𝒞.card m s) * (rest.map (instrWeight 𝒞.card m)).prod :=
          Nat.mul_le_mul_right _ hstepcard
      _ = L.card * ((s :: rest).map (instrWeight 𝒞.card m)).prod := by
          simp [List.map_cons, List.prod_cons]; ring

theorem websOf_seven {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m)
    (sched : List WebInstr) : ∀ l ∈ websOf 𝒞 sched, ∀ C ∈ l, C.card ≤ 7 :=
  (card_websOf_aux h𝒞 hm sched {[]} (by simp)).1

theorem card_websOf_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m)
    (sched : List WebInstr) :
    (websOf 𝒞 sched).card ≤ (sched.map (instrWeight 𝒞.card m)).prod := by
  have := (card_websOf_aux h𝒞 hm sched {[]} (by simp)).2
  simpa using this

/-! ### The weight of a schedule -/

/-- Is the step a free choice? -/
def isFree : WebInstr → Bool
  | .free => true
  | _ => false

/-- Is the step a single meeting? -/
def isMeets : WebInstr → Bool
  | .meets _ => true
  | _ => false

/-- Is the step a double meeting? -/
def isDbl : WebInstr → Bool
  | .dbl _ _ => true
  | _ => false

/-- The product of the weights, read off the numbers of steps of each kind. -/
theorem prod_instrWeight (c m : ℕ) (sched : List WebInstr) :
    (sched.map (instrWeight c m)).prod =
      c ^ sched.countP isFree * (7 * m) ^ sched.countP isMeets * 49 ^ sched.countP isDbl := by
  induction sched with
  | nil => simp
  | cons s rest ih =>
    cases s with
    | free =>
      simp [isFree, isMeets, isDbl, instrWeight, ih, pow_succ]
      ring
    | meets i =>
      simp [isFree, isMeets, isDbl, instrWeight, ih, pow_succ]
      ring
    | dbl i j =>
      simp [isFree, isMeets, isDbl, instrWeight, ih, pow_succ]
      ring

/-! ### The six-cycles a schedule serves -/

variable [Fintype V]

/-- The six-cycles a family serves with a given schedule and a given choice of the clusters that
are to hold the six leftover vertices. -/
noncomputable def webCovered (𝒞 : Finset (Finset V)) (sched : List WebInstr) (idx : Fin 6 → ℕ) :
    Finset (V × V × V × V × V × V) :=
  open Classical in
  Finset.univ.filter
    (fun q => ∃ l ∈ websOf 𝒞 sched, ∀ i : Fin 6, hexTup q i ∈ l.getD (idx i) ∅)

theorem webCovered_subset {𝒞 : Finset (Finset V)} {sched : List WebInstr} {idx : Fin 6 → ℕ} :
    webCovered 𝒞 sched idx ⊆ (websOf 𝒞 sched).biUnion (fun l =>
      (l.getD (idx 0) ∅) ×ˢ ((l.getD (idx 1) ∅) ×ˢ ((l.getD (idx 2) ∅) ×ˢ
        ((l.getD (idx 3) ∅) ×ˢ ((l.getD (idx 4) ∅) ×ˢ (l.getD (idx 5) ∅)))))) := by
  classical
  intro q hq
  rw [webCovered, Finset.mem_filter] at hq
  obtain ⟨l, hl, hx⟩ := hq.2
  refine Finset.mem_biUnion.2 ⟨l, hl, ?_⟩
  simp only [Finset.mem_product]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hexTup] using hx 0
  · simpa [hexTup] using hx 1
  · simpa [hexTup] using hx 2
  · simpa [hexTup] using hx 3
  · simpa [hexTup] using hx 4
  · simpa [hexTup] using hx 5

/-- **The counting.**  With one free step and at most four single meetings, a cluster family in
which every vertex lies in at most `m ≥ 1` clusters serves at most `7^{10+2D} |V| m⁵ / 7`
six-cycles, `D` being the number of double meetings. -/
theorem card_webCovered_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) (hm1 : 1 ≤ m)
    {sched : List WebInstr} {idx : Fin 6 → ℕ} (hfree : sched.countP isFree = 1)
    (hmeets : sched.countP isMeets ≤ 4) :
    7 * (webCovered 𝒞 sched idx).card ≤
      7 ^ (10 + 2 * sched.countP isDbl) * (Fintype.card V * m ^ 5) := by
  classical
  set k := sched.countP isMeets with hk
  set D := sched.countP isDbl with hD
  have hfib : (webCovered 𝒞 sched idx).card ≤ (websOf 𝒞 sched).card * 7 ^ 6 := by
    refine (Finset.card_le_card webCovered_subset).trans (card_biUnion_le_mul ?_)
    intro l hl
    have hcl := websOf_seven h𝒞 hm sched l hl
    rw [Finset.card_product, Finset.card_product, Finset.card_product, Finset.card_product,
      Finset.card_product]
    calc (l.getD (idx 0) ∅).card * ((l.getD (idx 1) ∅).card * ((l.getD (idx 2) ∅).card *
          ((l.getD (idx 3) ∅).card * ((l.getD (idx 4) ∅).card * (l.getD (idx 5) ∅).card))))
        ≤ 7 * (7 * (7 * (7 * (7 * 7)))) :=
          Nat.mul_le_mul (getD_card_le hcl _) (Nat.mul_le_mul (getD_card_le hcl _)
            (Nat.mul_le_mul (getD_card_le hcl _) (Nat.mul_le_mul (getD_card_le hcl _)
              (Nat.mul_le_mul (getD_card_le hcl _) (getD_card_le hcl _)))))
      _ = 7 ^ 6 := by norm_num
  have hweb : (websOf 𝒞 sched).card ≤ 𝒞.card * (7 * m) ^ k * 49 ^ D := by
    refine (card_websOf_le h𝒞 hm sched).trans ?_
    rw [prod_instrWeight, hfree, pow_one]
  have hcl := seven_mul_card_le h𝒞 hm
  have hk4 : (7 * m) ^ k * 7 ^ 6 ≤ 7 ^ 10 * m ^ 4 := by
    have h1 : (7 * m) ^ k ≤ (7 * m) ^ 4 := Nat.pow_le_pow_right (by omega) hmeets
    calc (7 * m) ^ k * 7 ^ 6 ≤ (7 * m) ^ 4 * 7 ^ 6 := Nat.mul_le_mul_right _ h1
      _ = 7 ^ 10 * m ^ 4 := by ring
  calc 7 * (webCovered 𝒞 sched idx).card
      ≤ 7 * ((websOf 𝒞 sched).card * 7 ^ 6) := Nat.mul_le_mul_left _ hfib
    _ ≤ 7 * ((𝒞.card * (7 * m) ^ k * 49 ^ D) * 7 ^ 6) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hweb)
    _ = (7 * 𝒞.card) * (49 ^ D * ((7 * m) ^ k * 7 ^ 6)) := by ring
    _ ≤ (Fintype.card V * m) * (49 ^ D * (7 ^ 10 * m ^ 4)) :=
        Nat.mul_le_mul hcl (Nat.mul_le_mul_left _ hk4)
    _ = (49 ^ D * 7 ^ 10) * (Fintype.card V * m ^ 5) := by ring
    _ = 7 ^ (10 + 2 * D) * (Fintype.card V * m ^ 5) := by
        rw [pow_add, show (49 : ℕ) = 7 ^ 2 by norm_num, ← pow_mul]
        ring

/-! ### The wall -/

/-- **What a reservoir would have to supply**: for every six-cycle on `S` it does not already
meet, a web produced by the schedule whose prescribed clusters hold the six leftover vertices.
Every gadget of the corner and of the cross-patch kind demands an instance of this. -/
def WebReservoir (𝒞 : Finset (Finset V)) (S : Finset V) (sched : List WebInstr)
    (idx : Fin 6 → ℕ) : Prop :=
  ∀ x : Fin 6 → V, (∀ i j : Fin 6, i ≠ j → x i ≠ x j) → (∀ i, x i ∈ S) →
    Disjoint (famEdges 𝒞) (hexEdges x) →
      ∃ l ∈ websOf 𝒞 sched, ∀ i : Fin 6, x i ∈ l.getD (idx i) ∅

/-- **The wall.**  No sparse cluster family serves every six-cycle by a web with one free cluster
and at most four singly-pinned ones — whatever the schedule, whatever the clusters asked to hold
the leftover vertices, and however many doubly-pinned clusters the schedule uses.

This is the obstruction that kills the corner mechanism (`BKLO.not_hexChainReservoir`) and the
closed cross-patch gadget (`BKLO.not_crossHexReservoir`) alike. -/
theorem not_webReservoir {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {d : ℕ}
    {sched : List WebInstr} {idx : Fin 6 → ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hd : ∀ v : V, edeg (famEdges 𝒞) v ≤ d) (hd1 : 1 ≤ d)
    (hfree : sched.countP isFree = 1) (hmeets : sched.countP isMeets ≤ 4)
    (hdn : 1000 * 7 ^ (10 + 2 * sched.countP isDbl) * d ≤ Fintype.card V)
    (hn : 4000 ≤ Fintype.card V) :
    ¬ WebReservoir 𝒞 (Finset.univ : Finset V) sched idx := by
  classical
  intro hres
  have hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ d := by
    intro v
    have h1 := six_mul_card_clustersAt_le h𝒞 v
    have h2 := hd v
    omega
  have hcov := card_webCovered_le h𝒞 hm hd1 (idx := idx) hfree hmeets
  set Bad : Finset (V × V × V × V × V × V) :=
    webCovered 𝒞 sched idx ∪
      (Finset.univ : Finset (Fin 6)).biUnion (resEdgeSet (famEdges 𝒞)) with hBad
  have hBadcard : Bad.card ≤ (webCovered 𝒞 sched idx).card + 6 * (Fintype.card V ^ 5 * d) := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
    refine (card_biUnion_le_mul (fun i _ => card_resEdgeSet_le hd i)).trans ?_
    simp [Finset.card_univ]
  have hlt : Bad.card < (Fintype.card V).descFactorial 6 :=
    lt_of_le_of_lt hBadcard (crosswall_arith (Nat.one_le_pow _ _ (by norm_num)) hcov hdn hn)
  have hcardEmb : (Finset.univ : Finset (Fin 6 ↪ V)).card = (Fintype.card V).descFactorial 6 := by
    rw [Finset.card_univ, Fintype.card_embedding_eq]
    simp
  obtain ⟨f, hf⟩ : ∃ f : Fin 6 ↪ V, embTup f ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    have hle : (Finset.univ : Finset (Fin 6 ↪ V)).card ≤ Bad.card :=
      Finset.card_le_card_of_injOn embTup (fun f _ => hcon f)
        (fun a _ b _ h => embTup_injective h)
    omega
  have hx : ∀ i j : Fin 6, i ≠ j → (f : Fin 6 → V) i ≠ f j := fun i j hij h => hij (f.injective h)
  have hdisj : Disjoint (famEdges 𝒞) (hexEdges (f : Fin 6 → V)) := by
    rw [Finset.disjoint_right]
    intro e he heR
    obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
    refine hf (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ?_⟩))
    rw [resEdgeSet, Finset.mem_filter, hexTup_embTup]
    exact ⟨Finset.mem_univ _, heR⟩
  obtain ⟨l, hl, hxl⟩ := hres (f : Fin 6 → V) hx (fun i => Finset.mem_univ _) hdisj
  refine hf (Finset.mem_union_left _ ?_)
  rw [webCovered, Finset.mem_filter, hexTup_embTup]
  exact ⟨Finset.mem_univ _, l, hl, hxl⟩

/-! ### A finite repertoire of gadgets does not help -/

/-- The six-cycles served by any schedule of a finite repertoire. -/
noncomputable def webCoveredFam (𝒞 : Finset (Finset V))
    (L : Finset (List WebInstr × (Fin 6 → ℕ))) : Finset (V × V × V × V × V × V) :=
  open Classical in
  L.biUnion (fun p => webCovered 𝒞 p.1 p.2)

/-- **The counting for a repertoire.**  A routing that may pick, for each six-cycle, any gadget
from a finite list still serves only `|L| · 7^{10+2D} |V| m⁵ / 7` of them. -/
theorem card_webCoveredFam_le {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {m D : ℕ}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ m) (hm1 : 1 ≤ m)
    {L : Finset (List WebInstr × (Fin 6 → ℕ))} (hfree : ∀ p ∈ L, p.1.countP isFree = 1)
    (hmeets : ∀ p ∈ L, p.1.countP isMeets ≤ 4) (hdbl : ∀ p ∈ L, p.1.countP isDbl ≤ D) :
    7 * (webCoveredFam 𝒞 L).card ≤
      L.card * 7 ^ (10 + 2 * D) * (Fintype.card V * m ^ 5) := by
  classical
  have hstep : ∀ p ∈ L, 7 * (webCovered 𝒞 p.1 p.2).card ≤
      7 ^ (10 + 2 * D) * (Fintype.card V * m ^ 5) := by
    intro p hp
    refine (card_webCovered_le h𝒞 hm hm1 (hfree p hp) (hmeets p hp)).trans ?_
    exact Nat.mul_le_mul_right _
      (Nat.pow_le_pow_right (by norm_num) (by have := hdbl p hp; omega))
  calc 7 * (webCoveredFam 𝒞 L).card
      ≤ 7 * ∑ p ∈ L, (webCovered 𝒞 p.1 p.2).card :=
        Nat.mul_le_mul_left _ (Finset.card_biUnion_le)
    _ = ∑ p ∈ L, 7 * (webCovered 𝒞 p.1 p.2).card := by rw [Finset.mul_sum]
    _ ≤ ∑ _p ∈ L, 7 ^ (10 + 2 * D) * (Fintype.card V * m ^ 5) := Finset.sum_le_sum hstep
    _ = L.card * 7 ^ (10 + 2 * D) * (Fintype.card V * m ^ 5) := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_assoc]

/-- **What a reservoir would have to supply**, allowing the routing to choose, for each six-cycle,
any gadget from a fixed finite repertoire `L`. -/
def WebReservoirFam (𝒞 : Finset (Finset V)) (S : Finset V)
    (L : Finset (List WebInstr × (Fin 6 → ℕ))) : Prop :=
  ∀ x : Fin 6 → V, (∀ i j : Fin 6, i ≠ j → x i ≠ x j) → (∀ i, x i ∈ S) →
    Disjoint (famEdges 𝒞) (hexEdges x) →
      ∃ p ∈ L, ∃ l ∈ websOf 𝒞 p.1, ∀ i : Fin 6, x i ∈ l.getD (p.2 i) ∅

/-- **The wall, for a finite repertoire of gadgets.**  Even a routing free to choose a different
gadget for each six-cycle, out of any fixed finite list of schedules with one free and at most four
singly-pinned clusters, is not supplied by a sparse reservoir. -/
theorem not_webReservoirFam {E : Finset (Sym2 V)} {𝒞 : Finset (Finset V)} {d D : ℕ}
    {L : Finset (List WebInstr × (Fin 6 → ℕ))}
    (h𝒞 : ClusterFamilyIn E 𝒞) (hd : ∀ v : V, edeg (famEdges 𝒞) v ≤ d) (hd1 : 1 ≤ d)
    (hL : 1 ≤ L.card) (hfree : ∀ p ∈ L, p.1.countP isFree = 1)
    (hmeets : ∀ p ∈ L, p.1.countP isMeets ≤ 4) (hdbl : ∀ p ∈ L, p.1.countP isDbl ≤ D)
    (hdn : 1000 * (L.card * 7 ^ (10 + 2 * D)) * d ≤ Fintype.card V)
    (hn : 4000 ≤ Fintype.card V) :
    ¬ WebReservoirFam 𝒞 (Finset.univ : Finset V) L := by
  classical
  intro hres
  have hm : ∀ v : V, (clustersAt 𝒞 v).card ≤ d := by
    intro v
    have h1 := six_mul_card_clustersAt_le h𝒞 v
    have h2 := hd v
    omega
  have hcov : 7 * (webCoveredFam 𝒞 L).card ≤
      (L.card * 7 ^ (10 + 2 * D)) * (Fintype.card V * d ^ 5) := by
    have := card_webCoveredFam_le h𝒞 hm hd1 hfree hmeets hdbl
    calc 7 * (webCoveredFam 𝒞 L).card
        ≤ L.card * 7 ^ (10 + 2 * D) * (Fintype.card V * d ^ 5) := this
      _ = (L.card * 7 ^ (10 + 2 * D)) * (Fintype.card V * d ^ 5) := by ring
  set Bad : Finset (V × V × V × V × V × V) :=
    webCoveredFam 𝒞 L ∪
      (Finset.univ : Finset (Fin 6)).biUnion (resEdgeSet (famEdges 𝒞)) with hBad
  have hBadcard : Bad.card ≤ (webCoveredFam 𝒞 L).card + 6 * (Fintype.card V ^ 5 * d) := by
    refine (Finset.card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
    refine (card_biUnion_le_mul (fun i _ => card_resEdgeSet_le hd i)).trans ?_
    simp [Finset.card_univ]
  have hK1 : 1 ≤ L.card * 7 ^ (10 + 2 * D) :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  have hlt : Bad.card < (Fintype.card V).descFactorial 6 :=
    lt_of_le_of_lt hBadcard (crosswall_arith hK1 hcov hdn hn)
  have hcardEmb : (Finset.univ : Finset (Fin 6 ↪ V)).card = (Fintype.card V).descFactorial 6 := by
    rw [Finset.card_univ, Fintype.card_embedding_eq]
    simp
  obtain ⟨f, hf⟩ : ∃ f : Fin 6 ↪ V, embTup f ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    have hle : (Finset.univ : Finset (Fin 6 ↪ V)).card ≤ Bad.card :=
      Finset.card_le_card_of_injOn embTup (fun f _ => hcon f)
        (fun a _ b _ h => embTup_injective h)
    omega
  have hx : ∀ i j : Fin 6, i ≠ j → (f : Fin 6 → V) i ≠ f j := fun i j hij h => hij (f.injective h)
  have hdisj : Disjoint (famEdges 𝒞) (hexEdges (f : Fin 6 → V)) := by
    rw [Finset.disjoint_right]
    intro e he heR
    obtain ⟨i, rfl⟩ := mem_hexEdges.1 he
    refine hf (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ?_⟩))
    rw [resEdgeSet, Finset.mem_filter, hexTup_embTup]
    exact ⟨Finset.mem_univ _, heR⟩
  obtain ⟨p, hp, l, hl, hxl⟩ := hres (f : Fin 6 → V) hx (fun i => Finset.mem_univ _) hdisj
  refine hf (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨p, hp, ?_⟩))
  rw [webCovered, Finset.mem_filter, hexTup_embTup]
  exact ⟨Finset.mem_univ _, l, hl, hxl⟩

/-! ### The cross-patch gadget is an instance -/

/-- The schedule of the closed cross-patch gadget of `BKLO/CrossHexGadget.lean`: the closing
cluster `P`, then `G 1, G 3, G 5` meeting it, then `G 2, G 4, G 0`, then `B 0`, then the twelve
clusters `A i, B i` walking around the hexagon. -/
def crossSched : List WebInstr :=
  [.free, .meets 0, .meets 1, .meets 2, .dbl 2 3, .dbl 2 4, .dbl 2 4, .meets 0,
   .dbl 0 6, .dbl 0 7, .dbl 0 5, .dbl 0 6, .dbl 0 9, .dbl 0 10, .dbl 0 8, .dbl 0 9,
   .dbl 0 12, .dbl 0 13, .dbl 0 11]

/-- The positions of the six clusters `A 0, …, A 5` holding the leftover vertices. -/
def crossIdx : Fin 6 → ℕ := ![0, 10, 8, 6, 4, 2]

/-- One free cluster, four singly-pinned ones, fourteen doubly-pinned ones: the cross-patch gadget
lands exactly on the boundary the wall forbids. -/
theorem crossSched_counts :
    crossSched.countP isFree = 1 ∧ crossSched.countP isMeets = 4 ∧
      crossSched.countP isDbl = 14 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

omit [Fintype V] in
/-- **The cross-patch demand is a web demand.**  The nineteen clusters of the gadget, in the order
of `BKLO.crossSched`. -/
theorem webMem_of_crossChain {𝒞 : Finset (Finset V)} {x : Fin 6 → V} (h : CrossChain 𝒞 x) :
    ∃ l ∈ websOf 𝒞 crossSched, ∀ i : Fin 6, x i ∈ l.getD (crossIdx i) ∅ := by
  classical
  obtain ⟨P, G0, G1, G2, G3, G4, G5, A0, A1, A2, A3, A4, A5, B0, B1, B2, B3, B4, B5,
    hP, hG1, hG3, hG5, hG2, hG4, hG0, hB0, hA1, hB1, hA2, hB2, hA3, hB3, hA4, hB4, hA5, hB5, hA0,
    hx0, hx1, hx2, hx3, hx4, hx5⟩ := h
  refine ⟨[A0, B5, A5, B4, A4, B3, A3, B2, A2, B1, A1, B0, G0, G4, G2, G5, G3, G1, P], ?_, ?_⟩
  · simp only [websOf, crossSched, List.foldl_cons, List.foldl_nil]
    have m1 : [P] ∈ cstep ({[]} : Finset (List (Finset V)))
        (fun l => instrSet 𝒞 l WebInstr.free) := mem_cstep (by simp) (by simpa [instrSet] using hP)
    refine mem_cstep (mem_cstep (mem_cstep (mem_cstep (mem_cstep (mem_cstep (mem_cstep
      (mem_cstep (mem_cstep (mem_cstep (mem_cstep (mem_cstep (mem_cstep (mem_cstep (mem_cstep
      (mem_cstep (mem_cstep (mem_cstep m1 ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_) ?_)
      ?_) ?_) ?_) ?_) ?_
    · simpa [instrSet] using hG1
    · simpa [instrSet] using hG3
    · simpa [instrSet] using hG5
    · simpa [instrSet] using hG2
    · simpa [instrSet] using hG4
    · simpa [instrSet] using hG0
    · simpa [instrSet] using hB0
    · simpa [instrSet] using hA1
    · simpa [instrSet] using hB1
    · simpa [instrSet] using hA2
    · simpa [instrSet] using hB2
    · simpa [instrSet] using hA3
    · simpa [instrSet] using hB3
    · simpa [instrSet] using hA4
    · simpa [instrSet] using hB4
    · simpa [instrSet] using hA5
    · simpa [instrSet] using hB5
    · simpa [instrSet] using hA0
  · intro i
    fin_cases i <;> simpa [crossIdx, List.getD] using ‹_›

omit [Fintype V] in
/-- **The cross-patch reservoir is a web reservoir.**  So `BKLO.not_webReservoir` refutes it, with
the same constant `7³⁸ = 7^{10 + 2·14}` as the direct argument of `BKLO/CrossHexWall.lean`. -/
theorem webReservoir_of_crossHexReservoir {𝒞 : Finset (Finset V)} {S : Finset V}
    (h : CrossHexReservoir 𝒞 S) : WebReservoir 𝒞 S crossSched crossIdx :=
  fun x hinj hS hdisj => webMem_of_crossChain (crossChain_of_placement (h x hinj hS hdisj))

end BKLO
