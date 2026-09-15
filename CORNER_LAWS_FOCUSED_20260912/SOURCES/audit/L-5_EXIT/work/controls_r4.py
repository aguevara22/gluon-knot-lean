import sympy as sp
from sympy import Rational, binomial, cancel, together
q, a = sp.symbols('q a')
def jbang(j, mode):
    if j <= 0: return sp.Integer(1)
    if mode == "jones": return sp.prod([1 - q**i for i in range(1, j+1)])
    if mode == "qint":  return sp.prod([sp.cancel((1 - q**i)/(1 - q)) for i in range(1, j+1)])
def X(n, m, mode="jones", sign="beta", expo="betam", lam_expr=None, pref_pow=None):
    lam = lam_expr if lam_expr is not None else a**-2/q
    tot = 0
    for gam in range(0, n):
        bet = n - 1 - gam
        s = (-1)**(bet if sign=="beta" else gam)
        e = bet*m + Rational(gam*(gam+1),2) if expo=="betam" else gam*m + Rational(bet*(bet+1),2)
        pr = sp.prod([q**i - lam*q for i in range(-gam, bet+1)])
        tot += s*q**e*pr/(jbang(gam,mode)*jbang(bet,mode))
    pp = Rational((n-1)*(m-1),2) if pref_pow is None else pref_pow
    return cancel(together(((1-q)/(1-q**n))*lam**pp/(1-lam*q)*tot))
def corner(n, m, **kw):
    f = cancel(X(n,m,**kw)*a**((n-1)*(m+1)))
    f1 = sp.cancel(sp.limit(f,q,1)) if f.has(q) else f
    return sp.expand(f1).subs(a,0)
r=4; n,m=r,2*r+1
print("r=4 correct answer:", corner(n,m), " (expect -14)")
for label, kw in [("[j]! as q-integer factorial", dict(mode="qint")),
                  ("sign (-1)^gamma", dict(sign="gamma")),
                  ("exponent gamma*m+beta(beta+1)/2", dict(expo="gamm")),
                  ("lambda=a^-2 (drop q^-1)", dict(lam_expr=a**-2)),
                  ("prefactor lambda power off by one", dict(pref_pow=Rational((n-1)*(m-1),2)+1))]:
    try: print(f"  {label}: {corner(n,m,**kw)}")
    except Exception as e: print(f"  {label}: singular ({type(e).__name__})")
