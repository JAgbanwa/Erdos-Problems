# `K-GLOBAL` rederivation

Deleting an independent vertex `v` removes exactly `d(v)` graph edges.  Any
triangle packing of `G-v` remains a triangle packing of `G`; hence

`nu_3(G)>=nu_3(G-v)`

and therefore

`Phi(G)<=Phi(G-v)+d(v)`.

Let `C=max(2,N)` and induct strongly on `m=n(G)`.  The empty graph has
`Phi=0`.  If all independent degrees satisfy the high-degree condition and
`m>=N`, apply the eventual estimate with coefficient 2 and use `C>=2`.  If
`m<N`, then `Phi<=|E|<=m^2`, while `C>=N>m`; consequently

`m^2 <= m^2/6+C m`.

Otherwise choose an independent vertex with

`d(v)<= (2m-1)/6+1`.

By induction and the deletion inequality,

`Phi(G)<= (m-1)^2/6+C(m-1)+(2m-1)/6+1
        = m^2/6+C m-(C-1)`.

Because `C>=2`, the induction closes with slack at least one.  This verifies
the deletion branch, the base case, the small orders, and the same uniform
constant for every split graph.

