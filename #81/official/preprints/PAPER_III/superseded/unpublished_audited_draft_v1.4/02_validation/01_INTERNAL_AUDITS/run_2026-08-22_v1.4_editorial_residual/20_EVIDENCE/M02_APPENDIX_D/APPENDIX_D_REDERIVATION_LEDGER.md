# EXT-V14-M02 Appendix D rederivation ledger

## Claim under review

For a simple bipartite graph of maximum degree `Delta`, edge lists of size at least
`Delta` admit a proper list edge coloring. Appendix D claims a self-contained proof of
this maximum-degree case, apart from the explicitly proved or cited classical ingredients.

## D.1 Kernel coloring lemma

- In each round, the chosen color class induces a subdigraph with a kernel because the
  current digraph is induced in the original kernel-perfect digraph.
- A kernel is independent, so assigning its vertices the same color is proper.
- Every remaining vertex that loses the chosen color also loses an out-neighbor in the
  kernel; therefore `|L(v)| >= d+(v)+1` is preserved.
- Vertices outside the color class lose no list entry and cannot gain out-degree.
- Each nonempty round colors at least one vertex, so finiteness gives termination.

**Result:** valid.

## D.2 Stable matching lemma

- Deferred acceptance terminates because every edge is proposed along at most once.
- If an unmatched edge was proposed, its right endpoint finishes with a strictly preferred
  held edge because held proposals improve monotonically.
- If it was never proposed, its left endpoint must finish matched to an edge preceding it
  in that endpoint's strict order.
- Thus every unmatched edge is dominated at an endpoint by a preferred matched edge,
  exactly the stated stability condition.

**Result:** valid.

## D.3 Step 1: proper Delta-edge-coloring

- Induction may use the fixed palette of `Delta` colors after deleting one edge.
- If the endpoints miss distinct colors `alpha` and `beta`, the alternating path beginning
  at the first endpoint starts with `beta` because that endpoint misses `alpha`.
- If the path ended at the second endpoint, which misses `beta`, its last edge would have
  color `alpha`, hence the path would have even length. Bipartiteness makes every path
  between the endpoints of the deleted edge odd. Therefore the path cannot end there.
- Swapping the two colors on the maximal path preserves properness, leaves the second
  endpoint untouched, and frees `beta` at the first endpoint.

**Result:** valid, including the parity point most susceptible to reversal.

## D.3 Steps 2--4: orientation and kernels

- For an edge of base color `c`, higher colors at its `U` endpoint contribute at most
  `Delta-c` out-neighbors, while lower colors at its `R` endpoint contribute at most
  `c-1`. Hence its out-degree is at most `Delta-1`.
- Two incident edges are joined in exactly one direction because each endpoint order is
  linear. Independent vertex sets of the line orientation are therefore matchings.
- For every induced edge set, kernel domination `f -> e` says precisely that a matched
  edge `e` is preferred to `f` at a shared endpoint. Kernels are exactly stable matchings.
- The stable matching lemma supplies a kernel in every induced subdigraph, so the
  orientation is kernel-perfect.
- Lists of size at least `Delta` consequently satisfy the kernel coloring lemma.

**Result:** valid.

## Application in Section 7.2

The gain graph is simple and bipartite on `U` and `R`. Equation (7.2) gives
`|L(v_i r)| = b-t_i >= max{rho,u}`. Its endpoint degrees satisfy
`d(v_i)=g_i <= rho` and `d(r) <= |U|=u`, so every list has size at least the actual
maximum degree. Theorem D.3 applies with no unstated strengthening.

**Internal verdict:** `PASS_INTERNAL`.

This ledger is author-side review evidence. It does not replace the independent Appendix D
check requested from the external challenger.
