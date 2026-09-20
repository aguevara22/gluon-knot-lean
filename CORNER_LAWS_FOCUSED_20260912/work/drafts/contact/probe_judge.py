import numpy as np
# Accepted conventions (SM/LinkingCalculus.lean): linking P C1 C2 = (1/4pi) ∫∫ G·(G_u × G_v), G=(C2(v)-C1(u))/|.|
# selfLinking P T eps = linking P T (T + eps*e_y).  Front conventions (row 92 / FrontSmooth): plane=(x,z),
# over = smaller y (transverse) / smaller slope (Legendrian), sign = sgn det(vel_over, vel_under), det(u,v)=u1 v2 - u2 v1.
def gauss_linking(C1, C2, P, N):
    u = (np.arange(N)+0.5)*P/N
    A = C1(u); B = C2(u)            # shape (N,3)
    dA = (C1(u+1e-6)-C1(u-1e-6))/2e-6
    dB = (C2(u+1e-6)-C2(u-1e-6))/2e-6
    total = 0.0
    chunk = 512
    for i in range(0, N, chunk):
        a = A[i:i+chunk][:,None,:]; da = dA[i:i+chunk][:,None,:]
        r = B[None,:,:] - a           # C2(v)-C1(u)
        n = np.linalg.norm(r, axis=2)
        # classical: det(dC1, dC2, C1-C2)/|C1-C2|^3 ; G·(G_u×G_v) equals -det(dC1,dC2,r)/|r|^3 ... compute directly:
        # G = r/|r|; G_u = -(da - (da·G)G)/|r| ; G_v = (dB - (dB·G)G)/|r|;  G·(G_u×G_v) = -det(G, da, dB)/|r|^2 (projections drop)
        G = r/n[:,:,None]
        num = np.einsum('ijk,ijk->ij', G, np.cross(np.broadcast_to(da, r.shape), np.broadcast_to(dB[None,:,:], r.shape)))
        total += np.sum(-num/(n**2))
    return total*(P/N)**2/(4*np.pi)

def sanity_hopf():
    # two unlinked/linked circles with known linking number +1 (right-handed)
    C1 = lambda t: np.stack([np.cos(t), np.sin(t), 0*t],1)
    C2 = lambda t: np.stack([1+np.cos(t), 0*t, np.sin(t)],1)
    return gauss_linking(C1, C2, 2*np.pi, 1500)

def front_writhe(T, P, N, legendrian=False):
    # crude double point finder on the xz projection with the accepted over/sign rules
    t = (np.arange(N)+0.5)*P/N
    X = T(t); 
    dT = (T(t+1e-6)-T(t-1e-6))/2e-6
    pts = X[:,[0,2]]
    w = 0; found=[]
    # segment intersection search
    from itertools import product
    segs = np.stack([pts, np.roll(pts,-1,axis=0)],1)
    for i in range(N):
        p1,p2 = segs[i]
        d1 = p2-p1
        # vectorized against all j>i+1
        js = np.arange(i+2, N)
        if i==0: js = js[js<N-1]
        q1 = segs[js,0]; q2 = segs[js,1]; d2 = q2-q1
        den = d1[0]*d2[:,1]-d1[1]*d2[:,0]
        ok = np.abs(den)>1e-14
        rp = q1-p1
        s = (rp[:,0]*d2[:,1]-rp[:,1]*d2[:,0])/np.where(ok,den,1)
        r = (rp[:,0]*d1[1]-rp[:,1]*d1[0])/np.where(ok,den,1)
        hit = ok & (s>=0)&(s<1)&(r>=0)&(r<1)
        for j in js[hit]:
            yi, yj = X[i,1], X[j,1]
            if legendrian:
                si = dT[i,2]/dT[i,0]; sj = dT[j,2]/dT[j,0]
                over, under = (i,j) if si<sj else (j,i)
            else:
                over, under = (i,j) if yi<yj else (j,i)
            vo = dT[over][[0,2]]; vu = dT[under][[0,2]]
            sgn = np.sign(vo[0]*vu[1]-vo[1]*vu[0])
            w += sgn; found.append((t[i],t[j],sgn, X[i,1], X[j,1]))
    return w, found

print("Hopf sanity (expect +1 or -1 consistently):", round(sanity_hopf(),4))

# --- Transverse unknot probes (transverse clause) ---
TB = lambda t: np.stack([np.cos(t), np.sin(t), np.sin(2*t)/4],1)   # z'-yx' = 1/2
TA = lambda t: np.stack([-np.sin(t), 2*np.cos(t), -np.sin(t)*np.cos(t)],1)  # z'-yx' = 1
for name,T in [("B's unknot",TB),("A's unknot",TA)]:
    t=np.linspace(0,2*np.pi,2000,endpoint=False); X=T(t); dX=(T(t+1e-6)-T(t-1e-6))/2e-6
    alpha = dX[:,2]-X[:,1]*dX[:,0]
    for eps in [0.05,0.1]:
        sl = gauss_linking(T, lambda s: T(s)+np.array([0,eps,0]), 2*np.pi, 1500)
        print(name, "min alpha", alpha.min().round(3), "eps",eps,"sl=",round(sl,4), "front writhe=", front_writhe(T,2*np.pi,3000)[0])

# --- Legendrian eye unknot L and an explicit IsPushoffAnnulus B(t,s) = L + s(e_z - k x' e_y) + s^2 c(t) e_z ---
k=1.0; gam=1.0
def L(t): return np.stack([np.cos(t), -np.sin(2*t)/2, np.sin(t)**3/3],1)
def xprime(t): return -np.sin(t)
def c(t): return gam*np.sin(2*t)/2       # c' = gam cos 2t > 0 at t=0,pi
def B(t,s): 
    base=L(t); return base + s*np.stack([0*t, -k*xprime(t), 1+0*t],1) + (s**2)*np.stack([0*t,0*t,c(t)],1)
t=np.linspace(0,2*np.pi,4000,endpoint=False)
dL=(L(t+1e-6)-L(t-1e-6))/2e-6
print("Legendrian check max|z'-yx'| =", np.abs(dL[:,2]-L(t)[:,1]*dL[:,0]).max())
# front of L: cusps and writhe
wL,_ = front_writhe(L,2*np.pi,3000,legendrian=True)
print("front writhe of L =", wL, " (cusps at t=0 [up], t=pi [down]: D=1,U=1)")
for s0 in [0.15,0.3]:
    Ts = lambda th, s0=s0: B(th,s0)
    X=Ts(t); dX=(Ts(t+1e-6)-Ts(t-1e-6))/2e-6
    alpha = dX[:,2]-X[:,1]*dX[:,0]
    # embeddedness: min distance between non-adjacent points
    Xs=X[::4]; n=len(Xs); D=np.linalg.norm(Xs[:,None,:]-Xs[None,:,:],axis=2); idx=np.arange(n); sep=np.minimum(np.abs(idx[:,None]-idx[None,:]), n-np.abs(idx[:,None]-idx[None,:])); bad=np.argwhere((D<1e-2)&(sep>3))
    w, found = front_writhe(Ts,2*np.pi,6000)
    sl = gauss_linking(Ts, lambda th, s0=s0: Ts(th)+np.array([0,0.05,0]), 2*np.pi, 2500)
    print(f"s0={s0}: min alpha={alpha.min():.4f}, near-collisions={len(bad)}, front writhe={w}, crossings at t≈{[ (round(a,2),round(b,2),int(sg)) for a,b,sg,_,_ in found]}, sl(Gauss)={sl:.4f}  [Etnyre: tb-r = w-D = 0-1 = -1]")
