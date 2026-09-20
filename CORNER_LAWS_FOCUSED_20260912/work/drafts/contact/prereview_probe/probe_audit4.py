"""Fourth probe: crossing Legendrian pushoff with a phase-shifted W (positive circle at s0~0.25), and a positive
transverse multi-crossing curve (A = 4)."""
import numpy as np
from probe_audit import (self_linking, front_crossings, cusps_of_front, TWO_PI)
from probe_audit2 import make_legendrian
from probe_audit3 import self_approach

def run_phase(name, a, gam, dlt, eta, s0_list, eps, N_list):
    L, dL, x, xp, xpp, y, z = make_legendrian(a, gam, dlt, eta)
    t = np.linspace(0, TWO_PI, 8000, endpoint=False)
    cusps = cusps_of_front(x, z, TWO_PI, 8000)
    D = sum(1 for c in cusps if c[1] == 'down'); U = sum(1 for c in cusps if c[1] == 'up')
    w, f = front_crossings(L, dL, TWO_PI, 8000, 'slope')
    print(f"\n=== {name}: cusps={[(round(c[0],3),c[1]) for c in cusps]} D={D}, U={U}, w={w};  w-D={w-D}, w-U={w-U} ===")
    for s0 in s0_list:
        best = None
        for k in range(1, 13):
            for ph in np.linspace(0, TWO_PI, 16, endpoint=False):
                m = (s0 * xp(t) ** 2 + s0 ** 2 * np.cos(k * t + ph)).min()
                if best is None or m > best[0]:
                    best = (m, k, ph)
        m, k, ph = best
        if m <= 0:
            print(f"  s0={s0}: best min alpha {m:.4f} <= 0, skipped"); continue
        W = lambda tt: np.sin(k * tt + ph) / k
        Wp = lambda tt: np.cos(k * tt + ph)
        B = lambda tt, s: L(tt) + s * np.stack([0 * tt, -xp(tt), 1 + 0 * tt], 1) + s ** 2 * np.stack([0 * tt, 0 * tt, W(tt)], 1)
        dB = lambda tt, s: dL(tt) + s * np.stack([0 * tt, -xpp(tt), 0 * tt], 1) + s ** 2 * np.stack([0 * tt, 0 * tt, Wp(tt)], 1)
        Ts = lambda th: B(th, s0); dTs = lambda th: dB(th, s0)
        X = Ts(t); V = dTs(t)
        print(f"  s0={s0}, W=sin({k}t+{ph:.2f})/{k}: min alpha (exact/numeric) = {m:.4f}/{(V[:,2]-X[:,1]*V[:,0]).min():.4f}; circle self-approach = {self_approach(Ts):.3f}; max speed = {np.linalg.norm(V,axis=1).max():.1f}")
        wT, fT = front_crossings(Ts, dTs, TWO_PI, 16000, 'y')
        gaps = [abs(yo - yu) for *_, yo, yu in fT]
        print(f"     circle front writhe (over = smaller y) = {wT}; #crossings = {len(fT)} (L had {len(f)}); min y-gap = {min(gaps):.3f}")
        for e in eps:
            if e >= 0.8 * min(gaps):
                continue
            vals = [self_linking(Ts, dTs, e, N, method='B') for N in N_list]
            print(f"     eps={e}: sl(Gauss) at N={N_list} -> {[round(v,4) for v in vals]}   [w-D={w-D}, w-U={w-U}]")

if __name__ == '__main__':
    run_phase("crossing Legendrian (a=2.4, gam=-0.8)", 2.4, -0.8, 0.0, 0.0, s0_list=(0.25, 0.3), eps=(0.05, 0.08), N_list=(12000, 20000))

    print("\n=== transverse curve T3 (A=4): (2cos t + cos 2t, -4x', sin 6t/6 + 0.2 sin 3t + 0.3 cos t + 0.25 sin t) ===")
    def T3(t):
        xp_ = -2 * np.sin(t) - 2 * np.sin(2 * t)
        return np.stack([2 * np.cos(t) + np.cos(2 * t), -4 * xp_, np.sin(6 * t) / 6 + 0.2 * np.sin(3 * t) + 0.3 * np.cos(t) + 0.25 * np.sin(t)], 1)
    def dT3(t):
        xp_ = -2 * np.sin(t) - 2 * np.sin(2 * t)
        xpp_ = -2 * np.cos(t) - 4 * np.cos(2 * t)
        return np.stack([xp_, -4 * xpp_, np.cos(6 * t) + 0.6 * np.cos(3 * t) - 0.3 * np.sin(t) + 0.25 * np.cos(t)], 1)
    t = np.linspace(0, TWO_PI, 8000, endpoint=False)
    X = T3(t); V = dT3(t)
    print(f"  min alpha = {(V[:,2]-X[:,1]*V[:,0]).min():.4f};  self-approach = {self_approach(T3):.3f}")
    w, f = front_crossings(T3, dT3, TWO_PI, 16000, 'y')
    gaps = [abs(yo - yu) for *_, yo, yu in f]
    print(f"  front writhe (over = smaller y) = {w}; #crossings = {len(f)}; min y-gap = {min(gaps):.3f}; crossings = {[(round(p,3), round(q,3), s) for p,q,s,_,_ in f]}")
    for eps in (0.1, 0.2):
        vals = [self_linking(T3, dT3, eps, N, method='B') for N in (8000, 16000)]
        print(f"  eps={eps}: sl(Gauss) at N=8000,16000 -> {[round(v,4) for v in vals]}")
