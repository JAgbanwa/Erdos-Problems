# `K-CORRIDOR` rederivation

## Lemma 5.1

Let `F_1,...,F_{r_p}` be a matching factorization of `K_p`.  An injection of
the factors into the `q` independent vertices is chosen uniformly.  For fixed
`i` and fixed edge of `K[N_i]`, its factor is sent to `i` with probability
`1/q`.  Linearity of expectation therefore gives

`E X = q^{-1} sum_i binom(d_i,2)`.

Every retained factor is a matching and different factors are edge-disjoint,
so the retained triples are an integral triangle packing.  No independence of
the indicator variables is used.  The argument remains valid at `q=r_p`; for
`q>r_p` the unused hosts cause no collision.

Writing `x_i=|S_i|`, `M=sum x_i`, and `S_2=sum x_i^2`,

`sum_i binom(p-x_i,2) = [q(p^2-p)-(2p-1)M+S_2]/2`.

Substitution in `Phi=|E|-2 nu_3`, followed by `q=2p-s` and `n=3p-s`, gives
(5.2) exactly.  Since `S_2>=M^2/q`, the remaining expression in `M` is the
concave parabola `((s-1)M-M^2/q)/q`, whose unrestricted maximum is
`(s-1)^2/4`.  This proves (5.3); maximizing on a larger real domain is safe.

## Lemma 5.2

For a clique edge with `b_e` bad hosts, a singly hosted factor loses the edge
with probability `b_e/q`.  Conditional on a doubly hosted factor, the two
ordered distinct hosts are both bad with probability
`b_e(b_e-1)/(q(q-1))`.  A uniformly chosen proportion `delta=h/r_p` of the
factors is doubled.  Hence

`E U = sum_e b_e/q - delta sum_e b_e(q-b_e)/(q(q-1))`.

The two hosts assigned to one factor see a matching, so each retained clique
edge can be assigned to an admitting host without sharing an incident
clique–independent edge.  Distinct factors contain distinct clique edges.
Subtracting twice the extra expected gain gives (5.4).  At `h=0` it reduces
to Lemma 5.1; `q>=2` is automatic whenever the displayed double-host
denominator is active.

## Lemma 6.1

For ordered `i,j`, put `a=|S_i\S_j|`.  The edges in
`B_i\B_j` lie in `K_p-S_j` and meet the `a` marked vertices, so their number is

`a(2(p-|S_j|)-a-1)/2`.

Because `|S_j|<=m`, `a<=m`, and `2p-3m-1>=0`, this is at least
`(2p-3m-1)a/2`.  Summing ordered pairs and using
`sum |S_i\S_j| = (1/2) sum |S_i triangle S_j|` proves (6.2).  Separately, a
fixed clique edge contributes to `sum_{i,j}|B_i\B_j|` once for every ordered
bad/good pair, namely `b_e(q-b_e)` times; this proves (6.1).

## Lemma 7.1

For a selected reserve-host set `U`, the construction produces at least

`binom(b,2) - r_b^{-1} sum_{i notin U} beta_i
 + B_U + binom(rho,2) - theta_R B_U`

triangles.  The first family uses `QQ` clique edges, the second uses `RQ`
edges with an independent apex, and the third uses `RR` edges with a `Q`
apex.  Proper list edge coloring prevents reuse of `RQ` edges; factorization
and forbidden-color deletion prevent all remaining collisions.

Choosing `U` from the largest `u` values of
`2 beta_i/r_b + 2(1-theta_R)g_i` gives at least `u/q` of the total.  Thus

`nu_3 >= binom(b,2)+binom(rho,2)
          - (1/q) sum_i beta_i
          + (u/q)(1-theta_R)B_R`,

where `q=r_b+u`.  Since

`2 sum beta_i=(2b-1)A_R-A_{2,R}`

and `sum d_i=qb+B_R-A_R`, substitution in `Phi` yields (7.6) identically.

The hypothesis chain left partial externally is also closed.  In §9.3,
`R=S_j`, hence `rho=|S_j|<=m`; and `T_i=S_i\R`, hence `t_i<=|S_i|<=m`.
Therefore

`2rho+t_i+1 <= 3m+1 <= s-2`.

The first inequality implies `2rho+t_i<=s-3<=p`, and hence
`b-t_i=p-rho-t_i>=rho`.  It also gives
`s>=2rho+t_i+3`, so from `u<=p-s+rho+1` one obtains
`b-t_i>=u+2`.  Finally `r_b<=b<=p<=q`, while
`chi'(K_rho)<=rho<=b`.  Thus all hypotheses (7.1)–(7.2), including the small
values of `rho`, are accounted for.

The symbolic identities and exhaustive small-set falsifiers are recorded in
`30_RESULTS/exact_checks.json`.
