"""Second independent probe: (i) the 4-cusp Legendrian L4 (D=1, U=3, w=0) at admissible larger eps and finer grids,
(ii) a Legendrian with front crossings found by a small parameter search, (iii) a transverse curve with several
generic crossings.  Same accepted conventions as probe_audit.py."""
import numpy as np
from probe_audit import (gauss_linking_B, self_linking, front_crossings, cusps_of_front, embedded_check, TWO_PI)


def fft_antiderivative(fprime, N=256):
    """exact antiderivative (zero mean) of a trigonometric polynomial of degree < N/2, as a callable"""
    t = np.arange(N) * TWO_PI / N
    c = np.fft.rfft(fprime(t)) / N
    k = np.arange(len(c))
    assert abs(c[0]) < 1e-9, f"nonzero mean {c[0]}: not periodic"
    ck = np.zeros_like(c); ck[1:] = c[1:] / (1j * k[1:])
    def f(s):
        s = np.asarray(s, dtype=float)
        val = np.zeros_like(s)
        for kk in range(1, len(ck)):
            val = val + 2 * (ck[kk].real * np.cos(kk * s) - ck[kk].imag * np.sin(kk * s))
        return val
    return f


def make_legendrian(a, gam, dlt, eta):
    """x = cos 2t + a cos t;  y = sin t - (a/2) sin 2t + gam sin 3t + dlt cos t + eta cos 2t;  z' = x' y (periodic by the -(a/2) choice)"""
    def x(t): return np.cos(2 * t) + a * np.cos(t)
    def xp(t): return -2 * np.sin(2 * t) - a * np.sin(t)
    def xpp(t): return -4 * np.cos(2 * t) - a * np.cos(t)
    def y(t): return np.sin(t) - (a / 2) * np.sin(2 * t) + gam * np.sin(3 * t) + dlt * np.cos(t) + eta * np.cos(2 * t)
    def yp(t): return np.cos(t) - a * np.cos(2 * t) + 3 * gam * np.cos(3 * t) - dlt * np.sin(t) - 2 * eta * np.sin(2 * t)
    def zp(t): return xp(t) * y(t)
    z = fft_antiderivative(zp)
    def L(t): return np.stack([x(t), y(t), z(t)], 1)
    def dL(t): return np.stack([xp(t), yp(t), zp(t)], 1)
    return L, dL, x, xp, xpp, y, z


def make_annulus(L, dL, xprime, vz, Wp_k):
    """B = L + s (0, -x', vz) + s^2 (0, 0, sin(k t)/k);  alpha(d_t B_s) = s x'^2 + s^2 cos(k t) exactly"""
    def W(t): return np.sin(Wp_k * t) / Wp_k
    def Wp(t): return np.cos(Wp_k * t)
    def B(t, s): return L(t) + s * np.stack([0 * t, -xprime(t), vz + 0 * t], 1) + s ** 2 * np.stack([0 * t, 0 * t, W(t)], 1)
    def dB(t, s):
        d = dL(t)
        return d + s * np.stack([0 * t, -xpp_global(t), 0 * t], 1) + s ** 2 * np.stack([0 * t, 0 * t, Wp(t)], 1)
    return B, dB


def pushoff_report(name, L, dL, xp, xpp, x, z, s0_list, k_list=(2, 4, 6, 8), N_gauss=(6000, 12000)):
    global xpp_global
    xpp_global = xpp
    t = np.linspace(0, TWO_PI, 8000, endpoint=False)
    print(f"\n=== {name} ===")
    print(f"  max |alpha(L')| = {np.abs(dL(t)[:,2] - L(t)[:,1]*dL(t)[:,0]).max():.2e};  min |L'| = {np.linalg.norm(dL(t),axis=1).min():.3f};  min far-apart distance = {embedded_check(L, TWO_PI):.4f}")
    cusps = cusps_of_front(x, z, TWO_PI, 8000)
    D = sum(1 for c in cusps if c[1] == 'down'); U = sum(1 for c in cusps if c[1] == 'up')
    w, f = front_crossings(L, dL, TWO_PI, 8000, 'slope')
    wy, _ = front_crossings(L, dL, TWO_PI, 8000, 'y')
    print(f"  cusps = {[(round(a,4), kind) for a,kind,_ in cusps]}  -> D = {D}, U = {U}")
    print(f"  front crossings (slope rule) = {[(round(a,3), round(b,3), s, round(yo,3), round(yu,3)) for a,b,s,yo,yu in f]};  w = {w} (y-rule: {wy})")
    print(f"  Etnyre: r = (D-U)/2 = {(D-U)/2}, tb = w-(D+U)/2 = {w-(D+U)/2}, tb-r = w-D = {w-D};   [w-U = {w-U}]")
    for s0 in s0_list:
        # choose k with alpha > 0 on the circle
        ok_k = None
        for k in k_list:
            al = s0 * xp(t) ** 2 + s0 ** 2 * np.cos(k * t)
            if al.min() > 0:
                ok_k = k; break
        if ok_k is None:
            print(f"  s0={s0}: no k in {k_list} gives a positive circle; skipped"); continue
        B, dB = make_annulus(L, dL, xp, +1.0, ok_k)
        Ts = lambda th, s0=s0: B(th, s0)
        dTs = lambda th, s0=s0: dB(th, s0)
        X = Ts(t); V = dTs(t)
        al_num = V[:, 2] - X[:, 1] * V[:, 0]
        wT, fT = front_crossings(Ts, dTs, TWO_PI, 12000, 'y')
        gaps = [abs(yo - yu) for _, _, _, yo, yu in fT]
        gap = min(gaps) if gaps else np.inf
        print(f"  s0={s0}, W = sin({ok_k}t)/{ok_k}: min alpha (exact) = {(s0*xp(t)**2 + s0**2*np.cos(ok_k*t)).min():.4f}, (numeric) = {al_num.min():.4f};  "
              f"circle min far-apart dist = {embedded_check(Ts, TWO_PI, N=4000):.4f}")
        print(f"     front writhe of the circle (over = smaller y) = {wT};  crossings = {[(round(a,3), round(b,3), s, round(yo,3), round(yu,3)) for a,b,s,yo,yu in fT]};  min y-gap = {gap:.3f}")
        eps_list = [e for e in (0.05, 0.1, 0.2, 0.3) if e < 0.8 * gap][:2] or [0.5 * gap]
        for eps in eps_list:
            vals = [self_linking(Ts, dTs, eps, N, method='B') for N in N_gauss]
            print(f"     eps={eps:.3f}: sl(Gauss) at N={list(N_gauss)} -> {[round(v,4) for v in vals]}    [w-D = {w-D}, w-U = {w-U}]")


if __name__ == '__main__':
    # (i) L4 again, properly resolved
    L, dL, x, xp, xpp, y, z = make_legendrian(1.0, 0.3, 0.0, 0.0)
    pushoff_report("L4: a=1, gam=0.3 (D=1, U=3, w=0 expected)", L, dL, xp, xpp, x, z, s0_list=(0.1, 0.2))

    # (ii) search for a 4-cusp Legendrian with front crossings
    print("\n=== search: 4-cusp Legendrians with crossings (embedded, generic) ===")
    cands = []
    t = np.linspace(0, TWO_PI, 4000, endpoint=False)
    for a in (0.6, 1.0, 1.6, 2.4):
        for gam in (-0.8, -0.3, 0.3, 0.8):
            for dlt in (0.0, 0.7):
                for eta in (0.0, 0.5):
                    L, dL, x, xp, xpp, y, z = make_legendrian(a, gam, dlt, eta)
                    if np.linalg.norm(dL(t), axis=1).min() < 0.05:
                        continue
                    dist = embedded_check(L, TWO_PI, N=1500)
                    if dist < 0.02:
                        continue
                    w, f = front_crossings(L, dL, TWO_PI, 3000, 'slope')
                    if not f:
                        continue
                    gaps = [abs(yo - yu) for _, _, _, yo, yu in f]
                    if min(gaps) < 0.1:
                        continue
                    cands.append((a, gam, dlt, eta, w, len(f), round(dist, 3)))
    for c in cands:
        print("  a=%.1f gam=%.1f dlt=%.1f eta=%.1f : w=%d, #crossings=%d, min dist=%.3f" % c)
    # take up to two candidates with nonzero writhe
    picked = [c for c in cands if c[4] != 0][:2]
    for (a, gam, dlt, eta, *_rest) in picked:
        L, dL, x, xp, xpp, y, z = make_legendrian(a, gam, dlt, eta)
        pushoff_report(f"Legendrian a={a}, gam={gam}, dlt={dlt}, eta={eta}", L, dL, xp, xpp, x, z, s0_list=(0.08, 0.15), N_gauss=(6000, 12000))

    # (iii) a transverse curve with several generic crossings: x = 2cos t + cos 2t, y = -3 x', z = sin 6t/6 + 0.2 sin 3t + 0.3 cos t
    print("\n=== transverse curve T3' = (2cos t + cos 2t, -3x', sin 6t/6 + 0.2 sin 3t + 0.3 cos t) ===")
    def T3(t):
        xp_ = -2 * np.sin(t) - 2 * np.sin(2 * t)
        return np.stack([2 * np.cos(t) + np.cos(2 * t), -3 * xp_, np.sin(6 * t) / 6 + 0.2 * np.sin(3 * t) + 0.3 * np.cos(t)], 1)
    def dT3(t):
        xp_ = -2 * np.sin(t) - 2 * np.sin(2 * t)
        xpp_ = -2 * np.cos(t) - 4 * np.cos(2 * t)
        return np.stack([xp_, -3 * xpp_, np.cos(6 * t) + 0.6 * np.cos(3 * t) - 0.3 * np.sin(t)], 1)
    t = np.linspace(0, TWO_PI, 8000, endpoint=False)
    X = T3(t); V = dT3(t)
    al = V[:, 2] - X[:, 1] * V[:, 0]
    print(f"  min alpha = {al.min():.4f};  min far-apart distance = {embedded_check(T3, TWO_PI, N=3000):.4f}")
    w, f = front_crossings(T3, dT3, TWO_PI, 12000, 'y')
    gaps = [abs(yo - yu) for _, _, _, yo, yu in f]
    print(f"  front writhe (over = smaller y) = {w}; #crossings = {len(f)}; min y-gap = {min(gaps) if gaps else None}")
    print(f"  crossings = {[(round(a,3), round(b,3), s, round(yo,2), round(yu,2)) for a,b,s,yo,yu in f]}")
    for eps in (0.1, 0.2):
        vals = [self_linking(T3, dT3, eps, N, method='B') for N in (6000, 12000)]
        print(f"  eps={eps}: sl(Gauss) at N=6000,12000 -> {[round(v,4) for v in vals]}")
