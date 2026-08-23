# Editorial evaluation — Paper II v1.1.8

The researcher’s clarification resolves the only remaining editorial ambiguity.

The final wording now separates two roles of the same formula:

- for \(n\ge1\), \(M(n)\) is the graph-theoretic extremal value from Theorem 1.1;
- for every \(n\in\mathbb Z\), the floor expression satisfies the sharpened arithmetic inequalities.

This is preferable to restricting the corollary to \(n\ge1\), because the Lean theorem `phiTau_max_sandwich (n : ℤ)` is genuinely unrestricted. The revised text therefore matches the formal statement exactly without extending the graph-theoretic interpretation beyond its natural domain.

The domain distinctions across the post-freeze module are now explicit and coherent:

- `phiTau_max_sandwich`: all \(n\in\mathbb Z\);
- `odd_sq_emod_24` and `phiTau_max_closed`: all \(n\in\mathbb Z\);
- `phiTau_max_le_paperI_bound`: \(n\ge1\).

No further editorial query remains from this pass.
