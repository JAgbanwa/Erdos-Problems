# `K-SPARSE` rederivation

First, (8.2) really follows eventually from (8.1).  Because `n=p+q`, the
strict lower bound in (8.1) exceeds `2q+1` as soon as

`2p-10q+6k>7`.

Here `q=o(p)` and `k>=1`, so this holds eventually; integrality then gives
`d(v)>=2q+2` uniformly over the independent vertices.

For the `i`-th independent vertex, every clique vertex has lost at most
`i-1` incident edges to earlier matchings.  Thus the graph induced on `N_i`
has minimum degree at least `d_i-i`.  From `d_i>=2q+2` and `i<=q`,

`d_i-i >= d_i/2+1 > d_i/2`.

Dirac therefore supplies a Hamilton cycle (with the tiny orders already
excluded by this bound), and hence a matching of size `floor(d_i/2)`.  The
matchings are selected after deleting earlier ones, so they are mutually
edge-disjoint.  Consequently

`|F|>= (sum d_i-q)/2` and `Delta(F)<=q`.

For `R_0=K_p-F`, this gives `delta(R_0)>=p-1-q`.  A Hamilton path in `R_0`
orders its vertices `x_1,...,x_p`.  Put an edge `x_j x_{j+1}` in `J` exactly
when the prefix contains an odd number of odd-degree vertices of `R_0`.
The incidence parity changes precisely at members of that even set, including
the two endpoints.  Hence `Odd(J)=Odd(R_0)`, `Delta(J)<=2`, and `|J|<=p-1`.
Therefore `R_1=R_0-J` is Eulerian and
`delta(R_1)>=p-1-q-2`.

Eventually this minimum degree exceeds `3p/4`; a `K_5` follows from the
contrapositive of Turán's `K_5` bound.  Removing no cycle, a `C_4`, or a `C_5`
according as `|E(R_1)|` is `0,1,2 mod 3` makes the edge count divisible by
three.  A cycle changes every affected degree by two, so even degrees remain
even.  The total degree loss from `R_0` is at most four and

`delta(H)>=p-1-q-4`.

The numerical threshold in (8.9) is explicit: if `q<=p/20` and `p>=125`,

`p-1-q-4 >= 0.95p-5 >= 0.91p`.

Thus Theorem 2.3 applies on the original `p` vertices.  Combining the
`|F|` anchored triangles with the exact decomposition of `H` gives

`nu_3 >= binom(p,2)/3 + 2|F|/3 - O(p)`
`      >= binom(p,2)/3 + (sum d_i)/3 - O(p+q)`.

Using `sum d_i<=pq` yields

`Phi <= binom(p,2)/3+pq/3+O(p+q)
      = (p+q)^2/6-(p+q^2)/6+O(p+q)`.

The coefficient in the discarded term is nonpositive, and in the regime
`q=o(p)` one has `p+q=Theta(p)`, so this is `n^2/6+O(n)` with an absolute
linear constant after the eventual threshold is fixed.

The path parity construction was exhaustively checked for every even subset
through order 12; the threshold and final identity were checked in exact
rational arithmetic.  These tests support, but do not replace, the argument
above.
