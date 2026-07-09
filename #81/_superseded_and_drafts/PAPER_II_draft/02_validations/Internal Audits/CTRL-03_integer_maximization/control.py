# CTRL-03  Paper II, Proposition 7.1 (exact integer maximization)
# Claim: max_{p+q=n} Phi_tau(S_{p,q}) = floor((2n+1)^2/24), attained in branch q>=p-1;
#        the nonsaturated branch q<=p-1 never exceeds it.
# Phi_tau branches (Cor 6.3): q>=p-1: p(2n+1-3p)/2 ; q<=p-1 (p>=3): p(2n-p-1)/6 ;
#        degenerate p<=1 or (2,0): Phi_tau = |E| = C(p,2)+pq.
from math import floor
def Cp2(p): return p*(p-1)//2
def phi(p,q):
    n=p+q
    if p<=1 or (p==2 and q==0):      # triangle-free: Phi=|E|
        return Cp2(p)+p*q
    if q>=p-1:                        # saturated branch
        return p*(2*n+1-3*p)/2
    else:                             # nonsaturated branch (q<=p-1, p>=3)
        return (Cp2(p)+p*q)/3
bad=0; nns=0
for n in range(1,3001):
    fl=floor((2*n+1)**2/24)
    vals=[phi(p,n-p) for p in range(0,n+1)]
    mx=max(vals)
    if abs(mx-fl)>1e-9:
        bad+=1
        if bad<=5: print(f"MISMATCH n={n}: max_p Phi={mx} floor={fl}")
    # nonsaturated branch never exceeds floor
    for p in range(0,n+1):
        q=n-p
        if p>=3 and q<=p-1 and phi(p,q) > fl+1e-9:
            nns+=1
print(f"n range: 1..3000")
print(f"max_p Phi_tau(S_p,n-p) == floor((2n+1)^2/24) : mismatches = {bad}")
print(f"nonsaturated-branch values exceeding floor      : {nns}")
# spot table
print("n | floor((2n+1)^2/24) | max_p Phi | argmax p")
for n in [3,10,30,99,300,1000,3000]:
    fl=floor((2*n+1)**2/24); vals=[(phi(p,n-p),p) for p in range(0,n+1)]
    m,pp=max(vals); print(f"{n:5d} | {fl:9d} | {m:9.1f} | {pp}")
print("(8n+1)/24 > 1 for n>=3 (nonsaturated gap):", all((8*n+1)/24>1 for n in range(3,3001)))
print("RESULT:", "PASS" if bad==0 and nns==0 else "FAIL")
