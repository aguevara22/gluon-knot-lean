"""Independent numeric probe (pre-review of SM.src_contact) -- written from the accepted definitions:

  linking P C1 C2 = (1/4pi) int_0^P int_0^P  G . (G_u x G_v) du dv,  G(u,v) = (C2 v - C1 u)/|C2 v - C1 u|
      (SM/LinkingCalculus.lean:361-380; cross = Mathlib crossProduct, right-handed)
  selfLinking P T eps = linking P T (T + eps * e_y)                         (line 574)
  slCircle T = selfLinking (2pi) T eps0  (eps0 = row-88 radius; value independent of eps by U1a)
  sl K = slCircle K.circle                                                  (Skeleton_FINAL.lean:140)
  Front of a TransverseKnot: plane (x,z), over = smaller y, crossSign = sgn det(vel_over, vel_under),
      det (u,v) = u.1*v.2 - u.2*v.1                                         (TransverseFront.lean:279,735; Polygon.lean:16)
  SmoothFront: over = smaller slope dz/dx; IsDownCusp <-> x''*det(g'',g''') < 0 (FrontSmooth.lean:457,516,526)
  slNg F = writhe F - downCount F                                            (FrontSmooth.lean:732)

Two independent implementations of the Gauss integrand:
  (A) finite differences of G itself, literally  G . (dG/du x dG/dv);
  (B) the closed form  (C2 v - C1 u) . (C2'(v) x C1'(u)) / |C2 v - C1 u|^3   (derived by hand).
"""
import numpy as np
import sys

TWO_PI = 2 * np.pi


def gauss_linking_B(C1, dC1, C2, dC2, P, N):
    """closed form (B), periodic trapezoid rule on an N x N grid"""
    u = (np.arange(N) + 0.5) * P / N
    A = C1(u); dA = dC1(u)
    Bv = C2(u); dB = dC2(u)
    total = 0.0
    chunk = 256
    for i in range(0, N, chunk):
        a = A[i:i + chunk][:, None, :]
        da = dA[i:i + chunk][:, None, :]
        r = Bv[None, :, :] - a                     # C2(v) - C1(u)
        n3 = np.linalg.norm(r, axis=2) ** 3
        cr = np.cross(np.broadcast_to(dB[None, :, :], r.shape), np.broadcast_to(da, r.shape))  # C2'(v) x C1'(u)
        total += np.sum(np.einsum('ijk,ijk->ij', r, cr) / n3)
    return total * (P / N) ** 2 / (4 * np.pi)


def gauss_linking_A(C1, C2, P, N, h=1e-5):
    """literal (A): G . (G_u x G_v) with central finite differences of G"""
    u = (np.arange(N) + 0.5) * P / N
    def G(uu, vv):
        r = C2(vv)[None, :, :] - C1(uu)[:, None, :]
        return r / np.linalg.norm(r, axis=2)[:, :, None]
    total = 0.0
    chunk = 128
    for i in range(0, N, chunk):
        uu = u[i:i + chunk]
        G0 = G(uu, u)
        Gu = (G(uu + h, u) - G(uu - h, u)) / (2 * h)
        Gv = (G(uu, u + h) - G(uu, u - h)) / (2 * h)
        total += np.sum(np.einsum('ijk,ijk->ij', G0, np.cross(Gu, Gv)))
    return total * (P / N) ** 2 / (4 * np.pi)


def numderiv(C, h=1e-6):
    return lambda t: (C(t + h) - C(t - h)) / (2 * h)


def self_linking(T, dT, eps, N, P=TWO_PI, method='B'):
    Tp = lambda t: T(t) + np.array([0.0, eps, 0.0])
    if method == 'B':
        return gauss_linking_B(T, dT, Tp, dT, P, N)
    return gauss_linking_A(T, Tp, P, N)


def front_crossings(T, dT, P, N, over_rule):
    """double points of the xz projection of the closed curve T, with the accepted rules.
    over_rule = 'y' (smaller y over: TransverseKnot.front) or 'slope' (smaller dz/dx over: SmoothFront).
    Returns list of (t_over, t_under, sign) and the writhe."""
    t = (np.arange(N) + 0.5) * P / N
    X = T(t); V = dT(t)
    pts = X[:, [0, 2]]
    nxt = np.roll(pts, -1, axis=0)
    d = nxt - pts
    found = []
    for i in range(N):
        p1 = pts[i]; d1 = d[i]
        js = np.arange(i + 2, N)
        if i == 0:
            js = js[js < N - 1]
        if len(js) == 0:
            continue
        q1 = pts[js]; d2 = d[js]
        den = d1[0] * d2[:, 1] - d1[1] * d2[:, 0]
        ok = np.abs(den) > 1e-14
        rp = q1 - p1
        s = (rp[:, 0] * d2[:, 1] - rp[:, 1] * d2[:, 0]) / np.where(ok, den, 1)
        r = (rp[:, 0] * d1[1] - rp[:, 1] * d1[0]) / np.where(ok, den, 1)
        hit = ok & (s >= 0) & (s < 1) & (r >= 0) & (r < 1)
        for j in js[hit]:
            if over_rule == 'y':
                over, under = (i, j) if X[i, 1] < X[j, 1] else (j, i)
            else:
                si = V[i, 2] / V[i, 0]; sj = V[j, 2] / V[j, 0]
                over, under = (i, j) if si < sj else (j, i)
            vo = V[over][[0, 2]]; vu = V[under][[0, 2]]
            sgn = int(np.sign(vo[0] * vu[1] - vo[1] * vu[0]))
            found.append((float(t[over]), float(t[under]), sgn, float(X[over, 1]), float(X[under, 1])))
    w = sum(f[2] for f in found)
    return w, found


def cusps_of_front(x, z, P, N):
    """cusps (x'=0) of a Legendrian front (x(t), z(t)) with the accepted classification
    cuspDisc = x'' * det(gamma'', gamma''') ; down iff < 0.  Derivatives by finite differences."""
    t = np.linspace(0, P, N, endpoint=False)
    h = 1e-3
    def g(tt): return np.stack([x(tt), z(tt)], -1)
    d1 = (g(t + h) - g(t - h)) / (2 * h)
    # find sign changes of x'
    xp = d1[:, 0]
    idx = np.where(np.sign(xp) != np.sign(np.roll(xp, -1)))[0]
    out = []
    for i in idx:
        # refine root of x' by bisection
        a, b = t[i], t[(i + 1) % N] if i + 1 < N else P
        fa = (x(a + h) - x(a - h)) / (2 * h)
        for _ in range(60):
            m = (a + b) / 2
            fm = (x(m + h) - x(m - h)) / (2 * h)
            if np.sign(fm) == np.sign(fa):
                a, fa = m, fm
            else:
                b = m
        tc = (a + b) / 2
        H = 1e-2
        g2 = (g(tc + H) - 2 * g(tc) + g(tc - H)) / H ** 2
        g3 = (g(tc + 2 * H) - 2 * g(tc + H) + 2 * g(tc - H) - g(tc - 2 * H)) / (2 * H ** 3)
        det23 = g2[0] * g3[1] - g2[1] * g3[0]
        disc = g2[0] * det23
        tc_mod = tc % P
        if any(abs(((tc_mod - o[0] + P/2) % P) - P/2) < 1e-6 for o in out):
            continue
        out.append((float(tc_mod), 'down' if disc < 0 else 'up', float(disc)))
    return sorted(out)


def embedded_check(T, P, N=2000, tol=1e-3):
    t = (np.arange(N) + 0.5) * P / N
    X = T(t)
    D = np.linalg.norm(X[:, None, :] - X[None, :, :], axis=2)
    idx = np.arange(N)
    sep = np.minimum(np.abs(idx[:, None] - idx[None, :]), N - np.abs(idx[:, None] - idx[None, :]))
    mask = sep > 5
    return float(D[mask].min())


def report(title, T, dT, over_rule, eps_list=(0.05, 0.1), N_gauss=2500, N_front=6000, methodA=False):
    print(f"--- {title} ---")
    t = np.linspace(0, TWO_PI, 4000, endpoint=False)
    X = T(t); V = dT(t)
    alpha = V[:, 2] - X[:, 1] * V[:, 0]
    print(f"  min alpha(T') = {alpha.min():.5f}   (positive transverse iff > 0)")
    print(f"  min distance between far-apart points = {embedded_check(T, TWO_PI):.4f}")
    w, found = front_crossings(T, dT, TWO_PI, N_front, over_rule)
    print(f"  front writhe (over = smaller {over_rule}) = {w};  crossings (t_over, t_under, sgn, y_over, y_under) = "
          f"{[(round(a,3), round(b,3), s, round(yo,3), round(yu,3)) for a,b,s,yo,yu in found]}")
    for eps in eps_list:
        slB = self_linking(T, dT, eps, N_gauss, method='B')
        line = f"  eps={eps}: sl (closed form B) = {slB:.4f}"
        if methodA:
            slA = self_linking(T, dT, eps, 1200, method='A')
            line += f"   sl (finite-diff G, method A) = {slA:.4f}"
        print(line)
    return w


if __name__ == '__main__':
    np.set_printoptions(precision=4, suppress=True)

    # 0. normalization sanity: positive Hopf link => +1; two pushoff-of-kink checks
    C1 = lambda t: np.stack([np.cos(t), np.sin(t), 0 * t], 1)
    C2 = lambda t: np.stack([1 + np.cos(t), 0 * t, np.sin(t)], 1)
    lkB = gauss_linking_B(C1, numderiv(C1), C2, numderiv(C2), TWO_PI, 800)
    lkA = gauss_linking_A(C1, C2, TWO_PI, 600)
    print(f"Hopf link C1=(cos,sin,0), C2=(1+cos,0,sin): lk(B)={lkB:.4f}  lk(A)={lkA:.4f}")
    # orientation check of this Hopf link by the crossing formula with observer nu = -e_y (looking in +y):
    # project to (x,z): C1 -> segment on z=0 traversed +x at t=3pi/2 (y=-1, near observer) and -x at t=pi/2 (y=+1, far)
    # C2 -> circle centered (1,0). Mixed crossings where C2 hits z=0 at x in [-1,1]: x=0 (t=pi) with C2 velocity (0,0,-1)-> (0,-1) in (x,z)
    #  over/under by y: C2 has y=0; C1 at x=0: two branches y=+1 (t=pi/2) and y=-1 (t=3pi/2) -> both branches of C1 pass x=0,
    #  but only the point x=0,z=0 counts twice (C1 at t=pi/2 and 3pi/2 both project to (0,0)) -> the projection along y is NOT generic
    #  for C1 alone, but lk only needs mixed crossings: (C1(pi/2)=(0,1,0) vs C2(pi)=(0,0,0)): C2 nearer (y=0<1): over=C2: det((0,-1),(-1,0)) = 0*0-(-1)(-1) = -1
    #  (C1(3pi/2)=(0,-1,0) vs C2(pi)): C1 nearer: over=C1 vel (1,0): det((1,0),(0,-1)) = -1.   lk = (1/2)(-1-1) = -1  => expect -1.
    print("  hand crossing-formula for this Hopf link with nu=-e_y: -1  (so Gauss must return -1 for consistency)")

    # 1. transverse unknots (transverse clause)
    TB = lambda t: np.stack([np.cos(t), np.sin(t), np.sin(2 * t) / 4], 1)
    dTB = lambda t: np.stack([-np.sin(t), np.cos(t), np.cos(2 * t) / 2], 1)
    report("transverse unknot T1 = (cos t, sin t, sin 2t / 4)   [alpha = 1/2]", TB, dTB, 'y', methodA=True)
    TA = lambda t: np.stack([-np.sin(t), 2 * np.cos(t), -np.sin(t) * np.cos(t)], 1)
    report("transverse unknot T2 = (-sin t, 2cos t, -sin t cos t)   [alpha = 1]", TA, numderiv(TA), 'y')
    # a positive transverse curve with several front crossings: x = 2cos t + cos 2t, z = sin 6t/6, y = -3 x'
    # (alpha = z' - y x' = cos 6t + 3 x'^2 > 0: cos 6t = 1 at all four zeros of x', checked numerically below)
    def T3(t):
        x = 2 * np.cos(t) + np.cos(2 * t)
        xp = -2 * np.sin(t) - 2 * np.sin(2 * t)
        return np.stack([x, -3 * xp, np.sin(6 * t) / 6], 1)
    def dT3(t):
        xp = -2 * np.sin(t) - 2 * np.sin(2 * t)
        xpp = -2 * np.cos(t) - 4 * np.cos(2 * t)
        return np.stack([xp, -3 * xpp, np.cos(6 * t)], 1)
    tt = np.linspace(0, TWO_PI, 4000, endpoint=False); XX = T3(tt); VV = dT3(tt)
    al = VV[:, 2] - XX[:, 1] * VV[:, 0]
    if al.min() > 0:
        report("transverse curve T3 = (2cos t + cos 2t, -3x', sin 6t/6)", T3, dT3, 'y', eps_list=(0.05, 0.1), N_gauss=4000, N_front=8000)
    else:
        print(f"T3 not positive transverse (min alpha {al.min():.3f}); skipped")

    # convergence table for T1 (transverse clause), grid N vs eps
    print("--- convergence of sl(T1) in the grid size N (closed form B) ---")
    for eps in (0.05, 0.1):
        vals = [self_linking(TB, dTB, eps, N, method='B') for N in (1000, 2000, 4000)]
        print(f"  eps={eps}: N=1000,2000,4000 -> {[round(v,5) for v in vals]}")

    # 2. Legendrian eye and pushoff annuli  (pushoff clause)
    def L(t): return np.stack([np.cos(t), -np.sin(2 * t) / 2, np.sin(t) ** 3 / 3], 1)
    def dL(t): return np.stack([-np.sin(t), -np.cos(2 * t), np.sin(t) ** 2 * np.cos(t)], 1)
    t = np.linspace(0, TWO_PI, 4000, endpoint=False)
    print("\n=== Legendrian eye L = (cos t, -sin 2t/2, sin^3 t/3) ===")
    print(f"  max |alpha(L')| = {np.abs(dL(t)[:,2] - L(t)[:,1]*dL(t)[:,0]).max():.2e}")
    cusps = cusps_of_front(lambda s: np.cos(s), lambda s: np.sin(s) ** 3 / 3, TWO_PI, 4000)
    print(f"  cusps (t, type, cuspDisc) = {cusps}")
    wL, fL = front_crossings(L, dL, TWO_PI, 4000, 'slope')
    D = sum(1 for c in cusps if c[1] == 'down'); U = sum(1 for c in cusps if c[1] == 'up')
    print(f"  front writhe w = {wL}, D = {D}, U = {U}  =>  Etnyre: r=(D-U)/2={(D-U)/2}, tb=w-(D+U)/2={wL-(D+U)/2}, tb-r={wL-(D+U)/2-(D-U)/2} ; slNg = w-D = {wL-D}")

    def make_annulus(L, dL, xprime, vz_sign, wfun, dwfun):
        """B(t,s) = L + s*(0, -x'(t), vz_sign) + s^2*(0,0,w(t)); alpha(d_t B_s) = s x'^2 + s^2 w'(t) exactly"""
        def B(t, s):
            return L(t) + s * np.stack([0 * t, -xprime(t), vz_sign + 0 * t], 1) + (s ** 2) * np.stack([0 * t, 0 * t, wfun(t)], 1)
        def dB(t, s):
            d = numderiv(lambda tt: B(tt, s))
            return d(t)
        return B, dB

    xprime_eye = lambda t: -np.sin(t)
    for vz_sign, label in [(+1.0, "V = e_z - x' e_y (Etnyre's L+ direction, alpha(V)=+1)"),
                           (-1.0, "V = -e_z - x' e_y (alpha(V)=-1, same first-order y-push)")]:
        B, dB = make_annulus(L, dL, xprime_eye, vz_sign, lambda t: np.sin(2 * t) / 2, lambda t: np.cos(2 * t))
        print(f"\n  annulus {label}:  B = L + s V + s^2 (sin 2t/2) e_z")
        for s0 in [0.1, 0.3]:
            Ts = lambda th, s0=s0: B(th, s0)
            dTs = lambda th, s0=s0: dB(th, s0)
            # exact alpha along circle: s x'^2 + s^2 cos 2t
            al_exact = s0 * np.sin(t) ** 2 + s0 ** 2 * np.cos(2 * t)
            print(f"   s0={s0}: exact min alpha = {al_exact.min():.4f}")
            w = report(f"positive circle B(., {s0})", Ts, dTs, 'y', eps_list=(0.02, 0.05), N_gauss=3000, methodA=(s0 == 0.3 and vz_sign > 0))
            print(f"   => compare: w - D = {wL - D},  w - U = {wL - U}")

    # 3. A 4-cusp Legendrian knot (D != U): x = cos 2t + cos t, y = sin t - sin 2t/2 + b sin 3t (b=0.3), z' = x' y.
    #    y'(t) != 0 at every zero of x' (t = 0, pi, arccos(-1/4)), so the cusps are non-degenerate.
    b = 0.3
    print(f"\n=== 4-cusp Legendrian L4: x = cos 2t + cos t, y = sin t - sin 2t/2 + {b} sin 3t, z = int x' y ===")
    def x4(t): return np.cos(2 * t) + np.cos(t)
    def xp4(t): return -2 * np.sin(2 * t) - np.sin(t)
    def y4(t): return np.sin(t) - np.sin(2 * t) / 2 + b * np.sin(3 * t)
    # z' = x' y expanded in cosines (constant term 0, so z is 2pi-periodic):
    #   (-3/4 - b) cos t + (1/2 - b/2) cos 2t + (3/4) cos 3t + (-1/2 + b/2) cos 4t + b cos 5t
    def zp4(t):
        return (-0.75 - b) * np.cos(t) + (0.5 - b / 2) * np.cos(2 * t) + 0.75 * np.cos(3 * t) + (-0.5 + b / 2) * np.cos(4 * t) + b * np.cos(5 * t)
    def z4(t):
        return (-0.75 - b) * np.sin(t) + (0.5 - b / 2) * np.sin(2 * t) / 2 + 0.75 * np.sin(3 * t) / 3 + (-0.5 + b / 2) * np.sin(4 * t) / 4 + b * np.sin(5 * t) / 5
    def L4(t): return np.stack([x4(t), y4(t), z4(t)], 1)
    def dL4(t):
        yp = np.cos(t) - np.cos(2 * t) + 3 * b * np.cos(3 * t)
        return np.stack([xp4(t), yp, zp4(t)], 1)
    print(f"  check z' = x' y: max error = {np.abs(zp4(t) - xp4(t) * y4(t)).max():.2e};  max |alpha(L4')| = {np.abs(dL4(t)[:,2] - L4(t)[:,1]*dL4(t)[:,0]).max():.2e}")
    print(f"  min |L4'| = {np.linalg.norm(dL4(t), axis=1).min():.4f} (immersion iff > 0);  min far-apart distance = {embedded_check(L4, TWO_PI):.4f}")
    cusps4 = cusps_of_front(x4, z4, TWO_PI, 8000)
    print(f"  cusps = {[(round(a,4), k, round(d,3)) for a,k,d in cusps4]}")
    w4, f4 = front_crossings(L4, dL4, TWO_PI, 8000, 'slope')
    w4y, f4y = front_crossings(L4, dL4, TWO_PI, 8000, 'y')
    D4 = sum(1 for c in cusps4 if c[1] == 'down'); U4 = sum(1 for c in cusps4 if c[1] == 'up')
    print(f"  front writhe (slope rule) w = {w4}  [y-rule gives {w4y}], crossings (t_over,t_under,sgn,y_over,y_under) = {[(round(a,3), round(b_,3), s, round(yo,3), round(yu,3)) for a,b_,s,yo,yu in f4]}")
    print(f"  D = {D4}, U = {U4}  =>  r = {(D4-U4)/2}, tb = {w4-(D4+U4)/2}, tb - r = w - D = {w4 - D4};  w - U = {w4 - U4}")
    B4, dB4 = make_annulus(L4, dL4, xp4, +1.0, lambda t: np.sin(4 * t) / 4, lambda t: np.cos(4 * t))
    for s0 in [0.1, 0.2]:
        Ts = lambda th, s0=s0: B4(th, s0)
        dTs = lambda th, s0=s0: dB4(th, s0)
        al_exact = s0 * xp4(t) ** 2 + s0 ** 2 * np.cos(4 * t)
        print(f"\n   annulus B4 = L4 + s(0,-x',1) + s^2 (sin 4t/4) e_z, s0={s0}: exact min alpha = {al_exact.min():.4f}")
        report(f"positive circle B4(., {s0})", Ts, dTs, 'y', eps_list=(0.03, 0.05), N_gauss=4000, N_front=8000)
        print(f"   => compare: w - D = {w4 - D4},  w - U = {w4 - U4}")

    # convergence table for the eye pushoff circle B(.,0.3), V = e_z - x' e_y
    print("\n--- convergence of sl(B(.,0.3)) for the eye, closed form B ---")
    B, dB = make_annulus(L, dL, xprime_eye, +1.0, lambda t: np.sin(2 * t) / 2, lambda t: np.cos(2 * t))
    Ts = lambda th: B(th, 0.3); dTs = lambda th: dB(th, 0.3)
    for eps in (0.05, 0.1):
        vals = [self_linking(Ts, dTs, eps, N, method='B') for N in (2000, 4000, 6000)]
        print(f"  eps={eps}: N=2000,4000,6000 -> {[round(v,5) for v in vals]}")
