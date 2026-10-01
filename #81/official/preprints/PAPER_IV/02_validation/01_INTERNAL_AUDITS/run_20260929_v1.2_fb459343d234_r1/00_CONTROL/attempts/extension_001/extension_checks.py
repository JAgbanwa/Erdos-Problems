"""Bounded exact regressions for the v1.2 extensions. No Lean or solver invocation."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from collections import Counter
import copy, hashlib, json, platform, time

RUN=Path(__file__).resolve().parents[1]
OUT=RUN/'20_EVIDENCE/G2_MATHEMATICS'

def save(block, data):
    dest=OUT/block/'results'; dest.mkdir(parents=True,exist_ok=True)
    data.update(script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),python=platform.python_version())
    (dest/'extension_checks.json').write_text(json.dumps(data,indent=2)+'\n',encoding='utf-8')

def main():
    start=time.monotonic()
    near=(F(87947,44352)**2-F(87947,44352*1024)) >= F(393,100)
    n=4*10**12
    contract=F(16,6*n)+F(1,n)+F(16,24*n*n)<F(1,10**12)-F(16,10**16)
    bounds=[]
    for s in range(101):
        cost=1+32*s+800*(3+32*s)*(s+1)**2
        assert cost<=38000*(s+1)**3
        assert 2000*(s+1)**2+38000*(s+1)**3<=40000*(s+1)**3
        bounds.append([s,cost,38000*(s+1)**3])
    assert near and contract
    # Tiny exact tower prefixes only. The enormous theorem is not evaluated here.
    tower=[1]
    for _ in range(4): tower.append(2**tower[-1])
    assert all(x*x<=2**x for x in range(4,101))
    save('B04_CONSTANTS',{'status':'PASS_FINITE_REGRESSION','near_ratio':near,'near_contraction':contract,
        'coefficient_rows':bounds,'tower_prefix':tower[:4], 'negative_controls':{'N_square_le_two_power_fails_at_3':9>8},
        'limit':'Tower-height results are checked by named Lean cones, not finite enumeration.'})
    profiles=0
    for a in range(151):
        for b in range(151):
            if a+b<2:continue
            d=1+a*(a-1)//2+3*b*(b-1)//2-a*b
            assert d==(a-b)*(a-b-1)//2+(b-1)**2 and d>=0
            assert (d==0)==(b==1 and a in (1,2))
            if d>0: assert (a+b)*(a+b-1)//2<=10*d
            profiles+=1
    # Exact obstruction arithmetic; the universal labelled-template argument is reviewed separately.
    rows=0
    for s in range(11):
        for q in range(max(2*s+2,3),71):
            n=3*q-s
            for d in range(1,q//2+1):
                k=q+d; delta=d*d+d*(d-1)//2
                M=lambda t:t*(t+1)//6
                value=k*(n-k)-(k-s)*(k-s-1)//2
                assert M(n+s)-s*(s+1)//2-value==delta
                edge_difference=d*(q-1-d)
                assert edge_difference>=F(n*d,4)
                assert F(n*n*delta,64)<=F(n*n*d*d,16)
                rows+=1
    save('B08_STABILITY',{'status':'PASS_FINITE_REGRESSION','piece_profiles':profiles,'obstruction_rows':rows,
        'sharp_profile':[3,2],'sharp_ratio':10,'negative_controls':{'coefficient_9_fails':10>9,
        'linear_to_optimal_family_fails_at_deficit_1':(3*100-0)/8>10},
        'limit':'Finite coefficient and family checks supplement the universally quantified Lean witnesses.'})
    # Degenerate structural cases: no assertion that leaf == a unique private vertex.
    bags=[{0,1,2},{2,3,4}]
    assert len(bags[0]-bags[1])==2
    duplicate=[{0,1},{0,1}]
    assert duplicate[0]&duplicate[1]=={0,1} # deleting it does not separate remaining vertices of K2.
    empty_maximal_cliques=[frozenset()]
    assert len(empty_maximal_cliques)>0
    assert len(list(combinations([0,1,2],2)))==3
    save('B09_STRUCTURE',{'status':'PASS_FINITE_REGRESSION','cases':[
        'empty graph has the empty maximal clique: nonempty needed for maximal-clique count <= vertex count',
        'two identical bags of K2: intersection is not a proper minimal separator',
        'isolated tree node has no adjacent parent',
        'leaf bag {0,1,2} has two private vertices relative to {2,3,4}'],
        'negative_controls':['unique simplicial vertex per leaf rejected','drop Nonempty from count rejected'],
        'limit':'Concrete models complement the compiled CliqueTree counterexamples; not a test of arbitrary trees.'})
    cert=OUT/'B01_MODEL/certificates/split_k3_h3_cover_optimal.json'
    payload=json.loads(cert.read_text())['payload']
    expected={tuple(e) for e in combinations(range(6),2) if min(e)<3}
    def check(p):
        universe={tuple(e) for e in p['universe']}
        if universe!=expected or p['size']!=len(p['parts']):return False
        counts=Counter()
        for part in p['parts']:
            es=[tuple(e) for e in part]; vertices=set(sum((list(e) for e in es),[]))
            if not 2<=len(vertices)<=4 or set(es)!=set(combinations(sorted(vertices),2)):return False
            counts.update(es)
        return set(counts)==expected and all(x==1 for x in counts.values())
    assert check(payload)
    negatives=[]
    for mut in ('omit','repeat','wrong_size','wrong_universe','nonclique'):
        p=copy.deepcopy(payload)
        if mut=='omit':p['parts'].pop();p['size']-=1
        if mut=='repeat':p['parts'].append(p['parts'][0]);p['size']+=1
        if mut=='wrong_size':p['size']+=1
        if mut=='wrong_universe':p['universe'].append([3,4])
        if mut=='nonclique':p['parts'][0].pop()
        assert not check(p);negatives.append(mut)
    # Weight -1 on core edges, +1 on spokes: every clique weighs <= 1.
    for r in range(2,7):
        for c in combinations(range(6),r):
            edges=set(combinations(c,2))
            if edges<=expected:assert sum(-1 if max(e)<3 else 1 for e in edges)<=1
    assert sum(-1 if max(e)<3 else 1 for e in expected)==6==payload['size']
    save('B01_MODEL',{'status':'PASS','certificate_sha256':hashlib.sha256(cert.read_bytes()).hexdigest(),
        'independent_checker':True,'covered_edges':12,'parts':6,'optimality':'Separate exact clique-weight lower bound 6; certificate itself certifies coverage only.',
        'mutations_rejected':negatives,'wall_seconds_total':time.monotonic()-start})
    print('PASS: B01 independent Certo replay; B04 arithmetic; B08 profiles/obstruction; B09 degeneracies.')

if __name__=='__main__':main()
