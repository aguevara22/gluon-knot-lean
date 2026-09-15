import itertools, json
from pathlib import Path

def subsets(xs):
    xs=list(xs)
    for mask in range(1 << len(xs)):
        yield {x for i,x in enumerate(xs) if mask & (1 << i)}
def children(cuts):
    xs=sorted(cuts)
    return list(zip(xs,xs[1:]))

general=spanning=unary=other=0
by_n={}
for n in range(3,10):
    tally=0
    for s in range(n):
        A,B=s,s+1
        old=lambda k:k if k<=s else k+1
        collapse=lambda p:p if p<=s else p-1
        for l,r in itertools.combinations(range(n+1),2):
            if (l,r)==(A,B): continue
            cl,cr=collapse(l),collapse(r)
            assert cl<cr
            for middle in subsets(range(cl+1,cr)):
                C={cl,cr}|middle
                if s in C: continue
                E={p for p in range(l,r+1) if collapse(p) in C and collapse(p)!=s}
                assert E=={old(k) for k in C}
                assert {l,r}<=E
                cc=children(C); ee=children(E)
                assert ee==[(old(x),old(y)) for x,y in cc]
                assert {collapse(p) for p in E}==C
                assert A not in E and B not in E
                general+=1
                if not l<A<B<r: continue
                spanning+=1; tally+=1
                chosen=[K for K in cc if K[0]<s<K[1]]
                assert len(chosen)==1
                K0=chosen[0]; J0=(old(K0[0]),old(K0[1]))
                assert J0 in ee and J0[0]<A<B<J0[1]
                assert [J for J in ee if J[0]<A<B<J[1]]==[J0]
                for K,J in zip(cc,ee):
                    if K!=K0:
                        assert K[1]<s or s<K[0]
                        assert J[1]<A or B<J[0]
                        other+=1
                assert all(J==J0 or J[1]<A or B<J[0] for J in ee)
                if len(cc)==1:
                    unary+=1
                    assert K0==(cl,cr) and J0==(l,r) and ee==[J0]
    by_n[str(n)]=tally

result={'scope':'Independent arithmetic enumeration of actual finite cut lists; supplementary, not a Lean proof or source acceptance.',
        'core_n_range':[3,9],'all_passed':True,'general_no_cut_configurations':general,
        'strict_spanning_configurations':spanning,'strict_spanning_by_n':by_n,
        'unary_strict_spanning_configurations':unary,'other_child_checks':other,
        'checks':['complete old-image cut equality','all actual consecutive children preserved',
                  'exact collapse and omission of both duplicate cuts','unique actual core and expanded spanning child',
                  'every other child lies strictly on one side','unary full interval retained'],
        'source_claim_acceptance_increment':0}
dest=Path(__file__).with_suffix('.json')
assert not dest.exists()
dest.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
