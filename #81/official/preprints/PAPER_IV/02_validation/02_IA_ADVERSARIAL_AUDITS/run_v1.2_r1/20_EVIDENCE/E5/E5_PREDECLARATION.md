# E5 predeclared tests and kill-switches (written 2026-09-30 before any E5 computation)

Evidence type for all: exact rational (Python `fractions`, integers) or exhaustive finite; exact ILP/LP only
with exact certificate re-verification. Finite tests never establish universal (∀n) claims.
"FAIL" of a positive test ⇒ suspend the claim and open a finding. "PASS" of a negative control is
REQUIRED (the corrupted variant must be rejected); a negative control that is accepted invalidates the test.

| ID | Claim (EN md line) | Test | Confirming outcome | Falsifying outcome | Limits |
|---|---|---|---|---|---|
| T01 | (4.6a) l.380-386 | exact eval at n=4e12; monotone LHS; failure at 3.6e12 | holds at 4e12, fails at 3.6e12 | holds at 3.6e12 or fails at 4e12 | exact |
| T02 | Lemma 4.2 l.366-368 | 16·117/1825>1, 16·12687/20000>10 | both true | either false | exact |
| T03 | Lemma 5.3 coefficients l.672-688 | recompute all four coefficient pairs from Table 2 | equal to −19/365, −253/500, −117/1825, −12687/20000 | mismatch | exact |
| T04 | (5.12)-(5.14) l.618-655 | exact evaluation of both coefficient bounds, (5.13) value, (5.12a) | ≤ 11/100, ≤ 29/1000, ≥393/100, < a/48 | any violated | exact; given the premises |
| T05 | Thm 5.0 size window l.440 | from a≥33n/100 (and \|n-3a\|≤a/64), 99a≤100p, 48(2p−q)+≤a derive 3267n≤10000p, 3539p≤1188n, \|3p−n\|≤n/50 | LP/rational derivation succeeds | a counter-assignment exists satisfying premises and violating a conclusion | exact LP over rationals (z3) |
| T06 | (5.1)-(5.4) scalar steps l.456-514 | 1e-12+1.5e-6 ≤ (0.33)^2/65536 ; u(u+1)/2≤ε0n² ⇒ u≤3n/(2·10^6) ; 7a/2−129a/64=95a/64; (5.1a) branch bounds vs (2n+1)^2/24−n²/40 for n≥9 | all true | any false | exact / symbolic |
| T07 | identity (6.3)/(6.8), (D.8), E.5 identity, (E.3) increments, (6.4) core sizes | exhaustive n≤400, all k | identities hold | any mismatch | finite exhaustive |
| T08 | (6.7a) identity and C(a+b,2)≤10·d_R when d_R>0; zero iff canonical; sharp at (3,2) | exhaustive a,b≤60 | holds, (3,2) equality | violation; factor 9 (neg. control) must fail | finite |
| T09 | (6.19) dist(k,K)^2 ≤ Q_s(n)−B_{s,n}(k) | exhaustive s≤20, n≤300, admissible k | holds | violation | finite |
| T10 | Prop 6.3a (6.20)-(6.21) | symbolic (sympy) + exhaustive small (s,q,d); brute-force rsd of G_{s,q,d} for small; exact cp via ILP for tiny instances | formulas hold; rsd≤s; cp=c4=Q_s−δ_d | any mismatch | ILP only tiny n |
| T11 | E.3 witness rsd≤s and cp=Q_s(n) (tiny n exact cp) | brute force | holds | fails | tiny n |
| T12 | Lemma F.3a (F.5a) | exhaustive all graphs n≤7 (labelled up to iso via networkx atlas n≤7), all s with rsd≤s, all D | holds | counterexample | finite; neg. control: replace s by s−1 must fail somewhere |
| T13 | (F.7) indCopies(C_k,G) ≤ 2ks n^{k−1} | exhaustive n≤7 | holds | violation | finite, weak test |
| T14 | (F.9) chordal clique extraction | exhaustive chordal n≤7 | holds | violation | finite |
| T15 | Prop 6.4 (6.22),(6.23) F_4 ≤ ... | all graphs n≤7 (atlas) with rsd≤s: compute F_4 exactly (LP + exact dual/primal certificate) | holds | violation | finite |
| T16 | Prop D.1 c4(K_n)≤M(n) small n; Prop D.2 K_n order≤3 needs >M(n) for n≡4 mod 6 | ILP small n (≤13) / parity argument check n=10 | D.1: packing found; D.2: ILP min with ≤3 pieces = M(n)+1 at n=10 | otherwise | small n |
| T17 | D.3 W*(S)=W(S)=2C(k,2) for K_k∨I_h, 2≤k≤h | exact LP small k,h | equality | mismatch | small |
| T18 | Thm C′ constants: max{40000(s+1)^3, 2/ε_s}=2e41(s+1)^8 ∀s≥0; E.4 coefficient 1+32s+800(3+32s)(s+1)^2 ≤ 38000(s+1)^3; total ≤40000(s+1)^3 | symbolic polynomial inequality over s≥0 | true | false | exact |
| T19 | F.1 deletion invariant algebra l.2141-2146 | symbolic check with γ0 ≤ ε/4, ε N0 ≥ 1 | invariant preserved | not | exact symbolic |
| T20 | (E.2e) and (E.13) arithmetic; (E.12) finite core alternative | exhaustive small c,s (graphs on c≤8 vertices, s≤2) for CoreCliqueAlternative hypothesis c≥20(s+1)^2 is too large → test the combinatorial induction claim "missing graph max degree ≤2s and no matching s+1 ⇒ ≤(4s+1)s edges" exhaustively on small graphs | holds | counterexample | finite |
| T21 | Lemma 2.1/(1.3a) accounting; (2.4); Table 1 | symbolic | ok | – | trivial |
| T22 | Theorem 6.1/Cor 6.1a constants: r+A+3m≤48δ from (6.7); LP optimum of the account | exact LP | 48 optimal from (6.7); 47 fails (neg. control) | otherwise | exact |
| T23 | (G.4),(G.5) | exhaustive chordal K4-free n≤8 e≤2n−3 ; algebra of (G.5) | holds | violation | finite |
| T24 | (6.5a)/(6.5) and Thm A arithmetic: M(n)≥n(n+1)/6−1 ; N^2 ≤ 2^N for N≥4 | exact | ok | – | trivial |
| T25 | Certo | Only if a Certo certificate is bound in the target; else record NOT_APPLICABLE with reason | – | – | – |
