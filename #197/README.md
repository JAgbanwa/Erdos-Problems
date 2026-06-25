I formalized the paper *"A Dyadic Partition Avoiding Monotone Three-Term Arithmetic Progressions"* in Lean 4 (Mathlib). All results are fully proved with no `sorry`, and the main theorems depend only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The project builds cleanly with no warnings.

The formalization lives in `RequestProject/Main.lean` (namespace `DyadicMono`).

Core definitions:
- `Pos` — the positive integers.
- `HasMono π` — `π : ℕ → ℕ` has a one-sided monotone three-term AP: indices `i < j < k` with `π i < π j < π k` and `π i + π k = 2 * π j` (values forming an increasing AP appearing in that same index order, matching Definition 1).
- `AdmitsAvoiding S` — `S` admits a permutation (injective `π : ℕ → ℕ` with range `S`) with no such progression.
- `col p` — the colour class of positive integers whose dyadic block index `Nat.log 2 n` has parity `p`; `Aset = col 0`, `Bset = col 1`.
- `rev` — the within-block reversal map used to build the avoiding permutations.

Main results:
- `dyadic_localization` — Lemma 4 (dyadic localization): for `x < y < z` with `x + z = 2y` whose block indices share the parity of `Nat.log 2 z`, if `x` is not in the top block then `y` is.
- `main_theorem` — Theorem 3: `Pos` partitions into two sets (`Aset`, `Bset`) that are disjoint, cover `Pos`, and each admit an avoiding permutation. The permutations are realized explicitly as `rev` composed with the increasing enumeration of each colour class.
- `every_perm_hasMono` / `not_admitsAvoiding_pos` — Proposition 6: every permutation of `Pos` contains a one-sided monotone three-term AP, so `Pos` admits no avoiding permutation. (The proof in fact only needs surjectivity onto `Pos`, so the stated lemma is slightly more general than required.)
- `least_parts_eq_two` — Corollary 7: `IsLeast {n | CanPartition n} 2`, i.e. the least number of parts in such a partition is exactly 2 (one part is impossible, two parts suffice).

Supporting lemmas (`pow_log_le`, `lt_pow_log`, `log_mid`, `log_rev`, `rev_pos`, `rev_rev`, `rev_anti`, `rev_mem_col`, `col_infinite`, `no_inc_AP_in_col`, `col_admitsAvoiding`) establish the dyadic block estimates, the properties of the reversal map, infinitude of the colour classes, and the case analysis (Cases 1 and 2) of the main proof.

(Credit to Aristotle-Harmonic)
