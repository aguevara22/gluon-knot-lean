"""Evaluate Jones 1987, Theorem 9.7 EXACTLY AS PRINTED (Ann. of Math. 126, p. 359),
carried into the campaign normalisation, and compare its corner coefficient with
SM6 hsm:terminal-value and lit:torus.  Positive control + broken controls.
This evaluates the SOURCE's printed formula; it proves nothing new."""
import sympy as sp
from sympy import Rational, binomial, cancel, together

q, a = sp.symbols('q a')

def jbang(j, mode):
    if j <= 0: return sp.Integer(1)
    if mode == "jones":  return sp.prod([1 - q**i for i in range(1, j+1)])
    if mode == "qint":   return sp.prod([sp.cancel((1 - q**i)/(1 - q)) for i in range(1, j+1)])
    raise ValueError(mode)

def X_thm97(n, m, mode="jones", sign="beta", expo="betam", lam_expr=None):
    lam = lam_expr if lam_expr is not None else a**-2/q     # t = a^-1  <=>  lambda = a^-2 q^-1
    tot = 0
    for gam in range(0, n):
        bet = n - 1 - gam
        s = (-1)**(bet if sign == "beta" else gam)
        e = bet*m + Rational(gam*(gam+1), 2) if expo == "betam" else gam*m + Rational(bet*(bet+1), 2)
        pr = sp.prod([q**i - lam*q for i in range(-gam, bet+1)])
        tot += s * q**e * pr / (jbang(gam, mode) * jbang(bet, mode))
    pref = ((1-q)/(1-q**n)) * lam**Rational((n-1)*(m-1), 2) / (1 - lam*q)
    return cancel(together(pref * tot))

def corner(n, m, **kw):
    """z=0 <=> q=1.  Shift by a^{(n-1)(m+1)} and read the constant term."""
    X = X_thm97(n, m, **kw)
    num, den = sp.fraction(cancel(X * a**((n-1)*(m+1))))
    num, den = sp.Poly(sp.expand(num), q, a), sp.Poly(sp.expand(den), q, a)
    # divide out (q-1) powers, then set q=1
    f = cancel(num.as_expr()/den.as_expr())
    f1 = sp.cancel(sp.limit(f, q, 1)) if f.has(q) else f
    return sp.expand(f1).subs(a, 0)

def cat(r): return binomial(2*r, r)//(r+1)

print("Jones Thm 9.7 (as printed) -> campaign corner  [a^{-(r-1)(2r+2)} z^0]")
print(" r | from Jones 9.7 | SM6 hsm:terminal-value | (-1)^{r-1}Cat_r | match")
for r in range(2, 7):
    n, m = r, 2*r+1
    c = corner(n, m)
    sm = sp.Integer((-1)**(r-1)) * Rational(1, r) * binomial(2*r, r-1)
    print(f" {r} | {c} | {sm} | {(-1)**(r-1)*cat(r)} | {sp.simplify(c-sm)==0}")

print("\nBROKEN CONTROLS at r=3 (correct answer is +5):")
for label, kw in [("[j]! read as the q-integer factorial", dict(mode="qint")),
                  ("sign (-1)^gamma in place of (-1)^beta", dict(sign="gamma")),
                  ("exponent gamma*m+beta(beta+1)/2", dict(expo="gamm")),
                  ("lambda = a^-2 (dropping q^-1)", dict(lam_expr=a**-2))]:
    try:
        print(f"  {label}: {corner(3, 7, **kw)}")
    except Exception as e:
        print(f"  {label}: singular/failed ({type(e).__name__})")
