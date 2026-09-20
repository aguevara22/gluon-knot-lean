import itertools
def check(n):
    s = lambda i: (i+1) % n
    bad_fr = bad_cls = total = 0
    pats = {}
    for lab in itertools.permutations(range(n), 6):
        a1,b1,a2,c1,b2,c2 = lab
        if not (s(a1)==a2 or s(a2)==a1): continue
        if not (s(b1)==b2 or s(b2)==b1): continue
        if not (s(c1)==c2 or s(c2)==c1): continue
        total += 1
        L = set(lab); N = [u for u in range(n) if u not in L]
        def mk(p,q):
            def f(u):
                if u==p: u=q
                elif u==q: u=p
                return s(u)
            return f
        f1, f2 = mk(a1,b1), mk(a2,b2)
        def fr(f,v):
            w=f(v)
            while w in L: w=f(w)
            return w
        def cyc(f,x):
            c={x}; y=f(x)
            while y!=x: c.add(y); y=f(y)
            return c
        ok1 = all(fr(f1,v)==fr(f2,v) for v in N)
        # classes
        C1=[cyc(f1,a1),cyc(f1,b1)]; C2=[cyc(f2,a2),cyc(f2,b2)]
        two1 = (C1[0]|C1[1]==set(range(n))) and not (C1[0]&C1[1])
        two2 = (C2[0]|C2[1]==set(range(n))) and not (C2[0]&C2[1])
        ok2 = two1 and two2 and all(((v in C1[0])==(v in C2[0])) for v in N)
        pat=(s(a1)==a2, s(b1)==b2, s(c1)==c2)
        pats[pat]=pats.get(pat,0)+1
        if not ok1: bad_fr+=1
        if not ok2: bad_cls+=1
    return total,bad_fr,bad_cls,pats
for n in range(6,11):
    t,b1,b2,p=check(n)
    print(n, "configs",t,"firstReturn failures",b1,"class failures",b2, "patterns", len(p))
