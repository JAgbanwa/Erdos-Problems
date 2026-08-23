# E2 -- independent mathematical rederivation

**Verdict: `INCONCLUSIVE`.** Section 9 is closed; three kill switches were not attempted.

See `results/section9.json` for every expression, root and margin. Summary:

- **`K-COVER` CLOSED.** Four levels of the case split checked and found exhaustive and
  non-overlapping: the integer split `q >= 2p-1`; the subsequence trichotomy, which is
  Bolzano-Weierstrass on the compact `[0,2]` with `eps = min(L, 2-L)/2` in the interior case;
  the `sqrt p` split inside Case D, complementary by construction with `s = Theta(p)` excluded
  because `alpha -> 2` forces `s = o(p)`; and the dispersion dichotomy.
- **Ten numbered inequalities verified exactly.** Highlights: the constant `2304` in (9.4) is
  *forced*, since the window `6 sqrt p <= s <= p/8` is non-empty exactly when `p >= 2304`;
  (9.19) is an exact identity, so the bound `s^2/24` is attained at `rho = s/4`; (9.18)
  reduces exactly to the hypothesis `s <= p/8`, consuming the whole budget; and (9.16) holds
  at about `1.229 s/p` against the allowed `1.25 s/p`, which is valid but not generous.
- **One PARTIAL.** The Lemma 7.1 hypothesis chain: the arithmetic is exact, but
  `2 rho + t_i + 1 <= 3m + 1 <= s - 2` needs `rho <= m` and `t_i <= m` from Section 7, which
  were not rederived.

**Not attempted, named individually:** `K-EPS` (the epsilon ledger), `K-CORRIDOR`
(Sections 5-7 themselves), `K-SPARSE` (Section 8). `K-GLOBAL` is PARTIAL: the frame and the
formal counterpart were checked, the deletion step and small orders were not.

Auditor error recorded: a first version of the (9.12) check used `subs(s**2, 36*p)`, which also
rewrites the linear `-2s/3` term and reported a spurious FAIL. Substituting `s = 6 sqrt p` on
both sides gives identical values, and the coefficient arithmetic is exact
(`5*36/288 = 5/8`, `1/2 - 5/8 = -1/8`). The item is PASS.

Evidence: `scripts/v13_E2_section9.py`, `results/section9.json`.
