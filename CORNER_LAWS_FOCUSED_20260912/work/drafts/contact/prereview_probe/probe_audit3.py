"""Third probe: resolved Gauss integrals with eps << kink size (s0 = 0.3), finer grids, and a proper self-approach metric."""
import numpy as np
from probe_audit import (self_linking, front_crossings, cusps_of_front, TWO_PI)
from probe_audit2 import make_legendrian, make_annulus
import probe_audit2

def self_approach(T, N=3000, frac=0.3):
    """min |T(u)-T(u')| over pairs whose circular parameter separation exceeds frac*2pi"""
    t = (np.arange(N) + 0.5) * TWO_PI / N
    X = T(t)
    idx = np.arange(N)
    sep = np.minimum(np.abs(idx[:, None] - idx[None, :]), N - np.abs(idx[:, None] - idx[None, :])) * (TWO_PI / N)
    D = np.linalg.norm(X[:, None, :] - X[None, :, :], axis=2)
    return float(D[sep > frac * TWO_PI].min())

def run(name, a, gam, dlt, eta, s0, eps_list, N_list, k_list=range(1, 13)):
    L, dL, x, xp, xpp, y, z = make_legendrian(a, gam, dlt, eta)
    probe_audit2.xpp_global = xpp
    t = np.linspace(0, TWO_PI, 8000, endpoint=False)
    cusps = cusps_of_front(x, z, TWO_PI, 8000)
    D = sum(1 for c in cusps if c[1] == 'down'); U = sum(1 for c in cusps if c[1] == 'up')
    w, f = front_crossings(L, dL, TWO_PI, 8000, 'slope')
    print(f"\n=== {name}: D={D}, U={U}, w={w};  w-D={w-D}, w-U={w-U};  L self-approach (param sep>0.3*2pi) = {self_approach(L):.3f} ===")
    ok_k = None
    for k in k_list:
        if (s0 * xp(t) ** 2 + s0 ** 2 * np.cos(k * t)).min() > 0:
            ok_k = k; break
    if ok_k is None:
        print("  no k gives a positive circle"); return
    B, dB = make_annulus(L, dL, xp, +1.0, ok_k)
    Ts = lambda th: B(th, s0); dTs = lambda th: dB(th, s0)
    X = Ts(t); V = dTs(t)
    print(f"  s0={s0}, W=sin({ok_k}t)/{ok_k}: min alpha = {(V[:,2]-X[:,1]*V[:,0]).min():.4f};  circle self-approach = {self_approach(Ts):.3f};  max speed = {np.linalg.norm(V,axis=1).max():.2f}")
    wT, fT = front_crossings(Ts, dTs, TWO_PI, 16000, 'y')
    gaps = [abs(yo - yu) for *_, yo, yu in fT]
    print(f"  circle front writhe (over = smaller y) = {wT}; crossings (t_o,t_u,sgn,y_o,y_u) = {[(round(p,3), round(q,3), s, round(yo,2), round(yu,2)) for p,q,s,yo,yu in fT]}; min y-gap = {min(gaps):.3f}")
    for eps in eps_list:
        vals = [self_linking(Ts, dTs, eps, N, method='B') for N in N_list]
        print(f"  eps={eps}: sl(Gauss) at N={N_list} -> {[round(v,4) for v in vals]}    [w-D={w-D}, w-U={w-U}]")

if __name__ == '__main__':
    run("L4 (a=1, gam=0.3)", 1.0, 0.3, 0.0, 0.0, s0=0.2, eps_list=(0.1,), N_list=(8000, 16000))
    run("crossing Legendrian (a=2.4, gam=-0.8)", 2.4, -0.8, 0.0, 0.0, s0=0.3, eps_list=(0.05, 0.1), N_list=(12000, 16000))

    print("\n=== transverse curve T3'' = (2cos t + cos 2t, -3x', sin 6t/6 + 0.2 sin 3t + 0.3 cos t + 0.25 sin t) ===")
    def T3(t):
        xp_ = -2 * np.sin(t) - 2 * np.sin(2 * t)
        return np.stack([2 * np.cos(t) + np.cos(2 * t), -3 * xp_, np.sin(6 * t) / 6 + 0.2 * np.sin(3 * t) + 0.3 * np.cos(t) + 0.25 * np.sin(t)], 1)
    def dT3(t):
        xp_ = -2 * np.sin(t) - 2 * np.sin(2 * t)
        xpp_ = -2 * np.cos(t) - 4 * np.cos(2 * t)
        return np.stack([xp_, -3 * xpp_, np.cos(6 * t) + 0.6 * np.cos(3 * t) - 0.3 * np.sin(t) + 0.25 * np.cos(t)], 1)
    t = np.linspace(0, TWO_PI, 8000, endpoint=False)
    X = T3(t); V = dT3(t)
    print(f"  min alpha = {(V[:,2]-X[:,1]*V[:,0]).min():.4f};  self-approach = {self_approach(T3):.3f};  max speed = {np.linalg.norm(V,axis=1).max():.2f}")
    w, f = front_crossings(T3, dT3, TWO_PI, 16000, 'y')
    gaps = [abs(yo - yu) for *_, yo, yu in f]
    print(f"  front writhe (over = smaller y) = {w}; #crossings = {len(f)}; min y-gap = {min(gaps):.3f}")
    print(f"  crossings = {[(round(p,3), round(q,3), s, round(yo,2), round(yu,2)) for p,q,s,yo,yu in f]}")
    for eps in (0.1, 0.2):
        vals = [self_linking(T3, dT3, eps, N, method='B') for N in (8000, 16000)]
        print(f"  eps={eps}: sl(Gauss) at N=8000,16000 -> {[round(v,4) for v in vals]}")
