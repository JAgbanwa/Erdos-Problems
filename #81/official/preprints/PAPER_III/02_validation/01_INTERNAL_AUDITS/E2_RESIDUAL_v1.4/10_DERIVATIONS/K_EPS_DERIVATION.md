# `K-EPS` rederivation and loss ledger

## Manuscript bulk interface

Fix a bulk window `epsilon_0<=alpha<=2-epsilon_0`.  Theorem 4.2 supplies

`nu_3^*(G)>=T(G)+c p^2-Bp`

for constants `c>0`, `B` depending only on the fixed window.  Since
`n=(1+alpha)p<=3p`, apply the uniform Haxell–Rödl/Yuster statement with
accuracy `eta=c/18`.  For all sufficiently large `n`,

`nu_3^*-nu_3 <= eta n^2 <= (c/2)p^2`.

Also choose `p>=2B/c`, so `Bp<=(c/2)p^2`.  The two losses fit inside the
margin, giving `nu_3>=T`.  The quantifier order is

`epsilon_0 -> (c,B) -> eta -> N_HR`,

followed by a single threshold enlarged to absorb `B`; none of these choices
depends on the graph after its order is quantified.

## Formal AX1 ledger

This is an internal source-level rederivation of the quantitative proof path;
external independence is still required.  The order of choices is:

1. requested AX1 accuracy;
2. nibble parameters for `beta=3 epsilon`;
3. regularity/triangle-removal scales;
4. `delta`, `epsilon_2`, and the coupled residual window;
5. `epsilon_1`, then the residual-selected `alpha`;
6. the order threshold, equipartition, block length, box size, and `tau`;
7. floors/ceilings and the family itself.

No parameter is selected using a graph appearing later in the quantifier
chain.

### Box-placement residual

For requested box error `e`, fixed copy-size bound `s_0`, set

`beta=e/(18s_0^2)` and
`theta=min(1/2, gamma/18, e/(6C))`.

The nibble leaves at most `3 beta n^2P^2+C` unplaced copies and each has area
at most `3s_0^2`.  The variable part is exactly

`3 beta * 3s_0^2 = e/2`.

From `s_0<=theta P` and `theta^2<=e/(6C)`, the constant part satisfies

`3s_0^2 C <= (e/2)P^2 <= (e/2)n^2P^2`.

Thus the two halves give the required `e n^2P^2`.  Floors and ceilings are
bounded on their correct sides, and `theta<=1/2` also forces `P>=2`.

### Coarse-cell residual

Put `e=min(1,epsilon)`,

`K=ceil(640/e)+1`, `s_0=ceil(K/delta)`,

and choose

`alpha=min(1/16,e/3200,theta delta/(16K),delta e/(32K))`.

The order threshold simultaneously ensures the minimum cluster size, the
`tau` lower bound, and `16/epsilon<=n`.  With
`l=ceil(2 alpha m_max)`, `P=floor(m_min/l)`, and `tau=lK/delta`, the proof
derives `P>=1/(4alpha)`, `s_0<=theta P`, `1/K<=e/640`, and `2/P<=e/400`.
These are exactly the margins needed for pair demand at most
`(1-e/64)P^2`.

After floors, exceptional copies and the LP recovery, the covering error is

`e n^2/48 + delta n^2/2 + k_p^2 tau^2 + e n^2/64
 + 1 + k(2tau+1)`.

The independently traced bounds are

`k_p^2 tau^2<=epsilon n^2/16`,
`1<=epsilon n^2/16`, and
`k(2tau+1)<=epsilon n^2/8`.

Using `e<=epsilon` and `delta<=epsilon`, the total coefficient is

`1/48+1/2+1/16+1/64+1/16+1/8 = 151/192 < 1`.

Hence every rounding, exceptional-set, and finite-size loss fits strictly
inside `epsilon n^2`.

### Coupled residual to AX1

The coupled residual is invoked with accuracy `epsilon/2`.  Its covering
clause therefore contributes at most `(epsilon/2)n^2`.  Transport from cluster
densities to block densities has coefficient

`(epsilon_1/8+4(epsilon_1/8)/alpha)/3<=epsilon`;

disjoint rectangles have total area at most `n^2/2`, so this contributes at
most the other `(epsilon/2)n^2`.

Finally the regular-decomposition reduction itself invokes the reduced
residual at `epsilon/2`; cleaning costs at most the complementary half.  In
the last nibble step, for `epsilon<1/3`,

`(1-3epsilon)(nu_3^*-(epsilon/2)n^2)<=nu_3`.

Since `nu_3^*<=n^2/6`, expansion gives
`nu_3^*-nu_3<=epsilon n^2`; for `epsilon>=1/3` the elementary
`nu_3^*<=|E|/3<=n^2/6` branch is stronger than required.

This closes the internal quantitative ledger without using compilation as a
substitute for the inequalities.  The Lean surfaces provide a separate
machine check of the same chain.

