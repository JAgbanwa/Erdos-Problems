# CTRL-04  Paper II, Lemma 5.1 (terminal characterization)
# Claim: a finite chordal graph in which every two NONADJACENT SIMPLICIAL vertices have
#        equal open neighborhoods is complete-split (K_p join empty_q).
# Exhaustive over ALL graphs on n<=6 vertices; combinatorial (no LP).
from itertools import combinations as C, product
def is_clique(adj,S):
    return all((b in adj[a]) for a,b in C(S,2))
def is_chordal(adj,n):
    order=[];wt=[0]*n;rem=set(range(n))
    for _ in range(n):
        u=max(rem,key=lambda x:(wt[x],x)); rem.discard(u); order.append(u)
        for w in adj[u]:
            if w in rem: wt[w]+=1
    pos={v:i for i,v in enumerate(order)}
    for v in order:
        later=[w for w in adj[v] if pos[w]>pos[v]]
        if later:
            u=min(later,key=lambda w:pos[w])
            for w in later:
                if w!=u and w not in adj[u]: return False
    return True
def simplicial(adj,v): return is_clique(adj,sorted(adj[v]))
def is_complete_split(adj,n):
    # exists K subset that is a clique, complement independent, all cross edges present
    V=list(range(n))
    for r in range(n+1):
        for Kset in C(V,r):
            Ks=set(Kset); I=[v for v in V if v not in Ks]
            if not is_clique(adj,list(Ks)): continue
            if any((b in adj[a]) for a,b in C(I,2)): continue          # I independent
            ok=all((i in adj[k]) for k in Ks for i in I)               # complete join
            if ok: return True
    return False
tot=0; chordal=0; hyp=0; viol=0
for n in range(1,7):
    pairs=list(C(range(n),2)); m=len(pairs)
    for bits in range(1<<m):
        adj=[set() for _ in range(n)]
        for i,(a,b) in enumerate(pairs):
            if bits>>i & 1: adj[a].add(b);adj[b].add(a)
        tot+=1
        if not is_chordal(adj,n): continue
        chordal+=1
        simp=[v for v in range(n) if simplicial(adj,v)]
        # hypothesis (H): every two NONADJACENT simplicial vertices share N
        H=True
        for a,b in C(simp,2):
            if b not in adj[a] and adj[a]!=adj[b]: H=False; break
        if H:
            hyp+=1
            if not is_complete_split(adj,n): viol+=1
print("Exhaustive over ALL labelled graphs on n=1..6 vertices")
print(f"graphs enumerated              : {tot}")
print(f"chordal graphs                 : {chordal}")
print(f"chordal & satisfy hypothesis(H): {hyp}")
print(f"of those, NOT complete-split   : {viol}  (violations of Lemma 5.1)")
print("RESULT:", "PASS" if viol==0 else "FAIL")
