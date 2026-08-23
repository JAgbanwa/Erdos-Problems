/-
# Nibble — the density `9/10` of the Dross cut route cannot be lowered

The dense route of this development consumes its density hypothesis `9|V| ≤ 10 δ(G)` in exactly one
place: the master cut inequality `Nibble.cut_master`, which turns the six combinatorial inputs of
`Nibble/DrossCutCount.lean` and `Nibble/DrossCutPartners.lean` into the cut condition
`3n(LA − KC) ≤ 2mX` of the Dross transfer certificate.  Every constant appearing there is a
function of the density `θ` at which the route is run:

* the codegree defect of an edge is at most `(2 − 2θ)n − 2` (from `codeg(e) ≥ 2δ(G) − n`);
  at `θ = 9/10` this is the `n/5 − 2` of `Nibble.cut_master`;
* the total codegree defect is at least `((3θ − 1)/2)·n` times the number of non-adjacent pairs
  (`Nibble.sum_card_outsideOf_ge`); at `θ = 9/10` this is `17n/20`;
* the number of edges is at least `(θ/2)n²`; at `θ = 9/10` this is `(9/20)n²`;
* the non-partner bound `Nibble.cutPhi` uses the coefficient `q·n` with `q = 21/20`; no bound of
  this shape can have `q < 1`, since already `|W|·n − |W|²/2` edges may meet a set `W`.

`Nibble.CutMasterAt θ q` below is precisely that `θ`-parametrised system, and
`Nibble.cutMasterAt_nine_tenths` records that `Nibble.cut_master` is the case `θ = 9/10`,
`q = 21/20`.

The two negative results say that the system becomes *false* below `9/10`:

* `Nibble.not_cutMasterAt_89_100` — at `θ = 89/100` the system fails for **every** `q ≥ 1`, i.e.
  no sharpening of the non-partner bound can rescue it;
* `Nibble.not_cutMasterAt_897_1000` — at `θ = 897/1000`, i.e. `0.3 %` below the threshold actually
  used, the system already fails for the route's own `q = 21/20`.

So the headline constant `9/10` of `BKLO.triangle_decomposition_dense` is not an artefact of the
particular positivity certificates used in `Nibble/DrossCutArith.lean`: the linear-programming
relaxation that those certificates witness is infeasible below `≈ 0.898`, and improving the
constant requires a genuinely different argument, not a reweighting of these inputs.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Nibble.DrossCutArith

namespace Nibble

/-- **The master cut inequality at density `θ`, with non-partner coefficient `q`.**

This is the statement of `Nibble.cut_master` with every `9/10`-specific constant replaced by its
value at density `θ`: the defect bound `(2 − 2θ)n − 2`, the total-defect coefficient `(3θ − 1)/2`
and the edge-count bound `(θ/2)n²`; the non-partner bound uses `q·n` in place of `21n/20`. -/
def CutMasterAt (θ q : ℝ) : Prop :=
  ∀ {n K L A C X : ℝ}, 20 ≤ n → 0 ≤ K → 0 ≤ L → 0 ≤ A → 0 ≤ C →
    A ≤ ((2 - 2 * θ) * n - 2) * K → C ≤ ((2 - 2 * θ) * n - 2) * L →
    ((3 * θ - 1) / 2) * n * (n * (n - 1) - 2 * (K + L)) ≤ A + C →
    (θ / 2) * n ^ 2 ≤ K + L → 0 ≤ X →
    2 * K * (K * L - (A + 2 * K) * (q * n) + A) + A ^ 2 ≤ 2 * K * X →
    2 * L * (K * L - (C + 2 * L) * (q * n) + C) + C ^ 2 ≤ 2 * L * X →
    3 * n * (L * A - K * C) ≤ 2 * (K + L) * X

/-- **The proved case.**  `Nibble.cut_master` is exactly `CutMasterAt (9/10) (21/20)`. -/
theorem cutMasterAt_nine_tenths : CutMasterAt (9 / 10) (21 / 20) := by
  intro n K L A C X hn hK hL hA0 hC0 hA hC hAC hm1 hX0 hXK hXL
  refine cut_master hn hK hL hA0 hC0 ?_ ?_ ?_ ?_ hX0 ?_ ?_
  · linarith only [hA]
  · linarith only [hC]
  · linarith only [hAC]
  · linarith only [hm1]
  · linarith only [hXK]
  · linarith only [hXL]

/-- **Failure at `θ = 89/100`, for every non-partner coefficient `q ≥ 1`.**

The witness is `n = 10⁴`, a cut with `K = 10 428 000`, `L = 36 972 000` (so `m = 0.474 n²`),
defect sums `A = 2196·K` and `C = 570·L`, and the smallest crossing count `X` allowed by the two
flow inputs. -/
theorem not_cutMasterAt_89_100 {q : ℝ} (hq : 1 ≤ q) : ¬ CutMasterAt (89 / 100) q := by
  intro h
  have key := h (n := 10000) (K := 10428000) (L := 36972000) (A := 22899888000)
      (C := 21074040000) (X := 181503552912000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ?_ ?_
  · norm_num at key
  · nlinarith only [hq]
  · nlinarith only [hq]

/-- **Failure at `θ = 897/1000` for the route's own non-partner coefficient `q = 21/20`.**

Only `0.3 %` below the density at which the development runs, the six inputs no longer imply the
cut condition: the witness is `n = 10⁴`, `K = 8 640 000`, `L = 39 360 000` (so `m = 0.48 n²`),
`A = 2054·K`, `C = 411·L`. -/
theorem not_cutMasterAt_897_1000 : ¬ CutMasterAt (897 / 1000) (21 / 20) := by
  intro h
  have key := h (n := 10000) (K := 8640000) (L := 39360000) (A := 17746560000)
      (C := 16176960000) (X := 172726302240000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  norm_num at key

end Nibble
