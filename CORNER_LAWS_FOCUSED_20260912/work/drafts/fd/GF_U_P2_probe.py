# Numerical probe for GF_U_P2_REPORT.md §2: the counterexample to leaf P2.2 `stage1_stable` as stated.
# Pure Python (math only).  Run: python3 GF_U_P2_probe.py
import math
pi = math.pi
# Legendrian curve L(θ) = (sin 2θ, sin θ, cos θ - cos 3θ/3):  z' = y x'  since 2 sinθ cos2θ = sin3θ - sinθ
x  = lambda t: math.sin(2*t);        y  = lambda t: math.sin(t);       z = lambda t: math.cos(t) - math.cos(3*t)/3
xp = lambda t: 2*math.cos(2*t);      yp = lambda t: math.cos(t);       zp = lambda t: -math.sin(t) + math.sin(3*t)
xpp = lambda t: -4*math.sin(2*t)
N = 4000
T = [2*pi*i/N for i in range(N)]
print("Legendrian max|z'-y x'| =", max(abs(zp(t) - y(t)*xp(t)) for t in T))
print("NoDoubleZero min(x'^2+x''^2) =", min(xp(t)**2 + xpp(t)**2 for t in T))
print("immersion min|L'| =", min(math.sqrt(xp(t)**2+yp(t)**2+zp(t)**2) for t in T))
# injectivity of L mod 2π (grid check)
worst = min((abs(x(a)-x(b))+abs(y(a)-y(b))+abs(z(a)-z(b)))/min(abs(a-b), 2*pi-abs(a-b)) for i,a in enumerate(T[::20]) for b in T if 1e-9 < min(abs(a-b), 2*pi-abs(a-b)))
print("embedded: min |L a - L b|_1 / circDist =", worst)
def circ(a, b):
    d = a - b
    return abs(d - 2*pi*round(d/(2*pi)))
def newton2(F, J, v, it=60):
    for _ in range(it):
        f = F(v); j = J(v)
        det = j[0][0]*j[1][1] - j[0][1]*j[1][0]
        if abs(det) < 1e-14: return None
        dv = [( j[1][1]*f[0] - j[0][1]*f[1])/det, (-j[1][0]*f[0] + j[0][0]*f[1])/det]
        v = [v[0]-dv[0], v[1]-dv[1]]
        if abs(dv[0])+abs(dv[1]) < 1e-15: break
    return v if max(abs(c) for c in F(v)) < 1e-12 else None
# double points of the front
F0 = lambda v: [x(v[0]) - x(v[1]), z(v[0]) - z(v[1])]
J0 = lambda v: [[xp(v[0]), -xp(v[1])], [zp(v[0]), -zp(v[1])]]
sols = []
G = [2*pi*i/60 for i in range(60)]
for a in G:
    for b in G:
        if circ(a, b) < 0.3: continue
        s = newton2(F0, J0, [a, b])
        if s is None: continue
        th, et = s[0] % (2*pi), s[1] % (2*pi)
        if circ(th, et) > 1e-6 and not any(abs(th-p)<1e-6 and abs(et-q)<1e-6 for p,q in sols):
            sols.append((th, et))
sols.sort()
print("front double points (θ, η), circDist, x'(θ), x'(η), det:")
for th, et in sols:
    det = xp(th)*zp(et) - zp(th)*xp(et)
    print(f"  θ={th:.6f} η={et:.6f} circDist={circ(th,et):.6f} x'θ={xp(th):+.4f} x'η={xp(et):+.4f} det={det:+.4f}")
dstar = min(circ(a, b) for a, b in sols)
print("δ* = min circDist over double points =", dstar)
# collar for δ*: pairs with 1e-3 < circDist < δ*-1e-3 have distinct fronts (grid check)
worst = math.inf
for a in T[::10]:
    for b in T:
        c = circ(a, b)
        if 1e-3 < c < dstar - 1e-3:
            worst = min(worst, (abs(x(a)-x(b)) + abs(z(a)-z(b)))/c)
print("collar δ*: min |front a - front b|_1 / circDist over 1e-3<circDist<δ*-1e-3 =", worst)
# perturbation by H = -(y - y_q) bumped near q = L(η0): flow there = translation by (a, 0, a*y_q); identity near L(θ0)
th0, et0 = [p for p in sols if abs(circ(*p) - dstar) < 1e-9][0]
yq = y(et0)
print(f"double point at distance δ*: θ0={th0:.6f} η0={et0:.6f}; y(θ0)={y(th0):+.4f} y(η0)={yq:+.4f} (distinct spatial points)")
for a in [1e-2, -1e-2, 1e-3, -1e-3, 1e-4, -1e-4]:
    F = lambda v: [x(v[0]) - (x(v[1]) + a), z(v[0]) - (z(v[1]) + a*yq)]
    s = newton2(F, J0, [th0, et0])
    c = circ(s[0], s[1])
    print(f"  Hx a={a:+.4f}: new double point θ={s[0]:.6f} η={s[1]:.6f} circDist={c:.6f} < δ*: {c < dstar}")
for a in [1e-2, -1e-2]:
    F = lambda v: [x(v[0]) - x(v[1]), z(v[0]) - (z(v[1]) + a)]
    s = newton2(F, J0, [th0, et0])
    c = circ(s[0], s[1])
    print(f"  Hz a={a:+.4f}: new double point θ={s[0]:.6f} η={s[1]:.6f} circDist={c:.6f} < δ*: {c < dstar}")
