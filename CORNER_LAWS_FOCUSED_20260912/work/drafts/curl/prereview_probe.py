import math, random
random.seed(20260914)
FAILS=[]
def chk(name, cond, info=""):
    if not cond:
        FAILS.append((name, info))
def close(a,b,tol=1e-9): return abs(a-b) <= tol*max(1.0,abs(a),abs(b))
def vclose(a,b,tol=1e-9): return close(a[0],b[0],tol) and close(a[1],b[1],tol)
def det(u,v): return u[0]*v[1]-u[1]*v[0]
def dot(u,v): return u[0]*v[0]+u[1]*v[1]
def add(u,v): return (u[0]+v[0],u[1]+v[1])
def sub(u,v): return (u[0]-v[0],u[1]-v[1])
def smul(r,u): return (r*u[0],r*u[1])
def norm(u): return math.hypot(u[0],u[1])
def normalize(u): n=norm(u); return (u[0]/n,u[1]/n)

# ---------- Unit M: rational model ----------
def cModel(t): return (t*t-1, t-t**3)
def bModel(t): return (3*(t*t+7)/11, -3*t)
def cD(t): return (2*t, 1-3*t*t)
def bD(t): return (6*t/11, -3.0)
u0=(0.0,-1.0); v0=(-1.0,0.0); q=4/11
chk("det(v0,u0)=1", close(det(v0,u0),1))
chk("c(2)=(3,-6)", vclose(cModel(2),(3,-6))); chk("c(-2)=(3,6)", vclose(cModel(-2),(3,6)))
chk("b(2)=(3,-6)", vclose(bModel(2),(3,-6))); chk("b(-2)=(3,6)", vclose(bModel(-2),(3,6)))
for _ in range(2000):
    t=random.uniform(-2.5,2.5); h=1e-6
    fd=smul(1/(2*h), sub(cModel(t+h),cModel(t-h)))
    chk("hasDerivAt_cModel", vclose(fd,cD(t),1e-5),(t,fd,cD(t)))
    fd=smul(1/(2*h), sub(bModel(t+h),bModel(t-h)))
    chk("hasDerivAt_bModel", vclose(fd,bD(t),1e-5),(t,fd,bD(t)))
    chk("det(c',c'')=-2(1+3t^2)", close(det(cD(t),(2,-6*t)), -2*(1+3*t*t)))
    chk("det(b',b'')=18/11", close(det(bD(t),(6/11,0)), 18/11))
chk("b'(2)=3/11 c'(2)", vclose(bD(2), smul(3/11,cD(2)))); chk("b'(-2)=3/11 c'(-2)", vclose(bD(-2), smul(3/11,cD(-2))))
chk("c'(-2)=11(q v0+u0)", vclose(cD(-2), smul(11, add(smul(q,v0),u0))))
chk("c'(2)=11(-q v0+u0)", vclose(cD(2), smul(11, add(smul(-q,v0),u0))))
chk("c'(0)=-u0", vclose(cD(0), smul(-1,u0)))
chk("det(c'(1),c'(-1))=-8", close(det(cD(1),cD(-1)),-8))
chk("c(1)=c(-1)=0", vclose(cModel(1),(0,0)) and vclose(cModel(-1),(0,0)))
# cModel_double: c(s)=c(t) => s=t or {s,t}={-1,1}; scan pairs
grid=[i/50 for i in range(-125,126)]
for s in grid:
    for t in grid:
        if abs(s-t)>1e-12 and vclose(cModel(s),cModel(t),1e-12):
            chk("cModel_double", (abs(s+1)<1e-12 and abs(t-1)<1e-12) or (abs(s-1)<1e-12 and abs(t+1)<1e-12),(s,t))
# algebraic: c(s)=c(t): s^2=t^2 => s=-t; then t-t^3 = -t+t^3 => 2t(1-t^2)=0 => t in {0,±1}; t=0 gives s=t. ok.

# ---------- Unit F: affine fit ----------
def xFit(a,b,c,d): return 2*a*c/(q*(b*c+a*d))
def yFit(a,b,c,d): return (b*c-a*d)/(q*(b*c+a*d))
def fitA(u,v,x,y,z): return add(smul(-z[0], add(smul(x,v),smul(y,u))), smul(-z[1],u))
def frame(th0):
    u=(math.cos(th0),math.sin(th0)); Ju=(-u[1],u[0]); v=(-Ju[0],-Ju[1]); return u,v
for _ in range(3000):
    a,b,c,d=[10**random.uniform(-3,3) for _ in range(4)]
    th0=random.uniform(-math.pi,math.pi); u,v=frame(th0)
    chk("det(v,u)=1", close(det(v,u),1)); chk("<v,u>=0", abs(dot(v,u))<1e-12)
    x=xFit(a,b,c,d); y=yFit(a,b,c,d); H=2*a*c/(b*c+a*d)
    L=fitA(u,v,x,y,add(smul(q,v0),u0)); R=smul(H/a, add(smul(a,v),smul(b,u)))
    chk("fitA_ray_minus", vclose(L,R,1e-8),(a,b,c,d))
    L=fitA(u,v,x,y,add(smul(-q,v0),u0)); R=smul(H/c, add(smul(-c,v),smul(d,u)))
    chk("fitA_ray_plus", vclose(L,R,1e-8),(a,b,c,d))
    chk("det_fitA_pos", det(fitA(u,v,x,y,v0),fitA(u,v,x,y,u0))>0)
    chk("det_fitA=x", close(det(fitA(u,v,x,y,v0),fitA(u,v,x,y,u0)),x,1e-8))
    chk("yFit_bound", abs(q*y)<1); chk("xFit_pos", x>0)
    chk("1-(qy)^2=4abcd/(bc+ad)^2", close(1-(q*y)**2, 4*a*b*c*d/(b*c+a*d)**2,1e-8))
    chk("fitA_u0=u", vclose(fitA(u,v,x,y,u0),u)); chk("fitA_v0=xv+yu", vclose(fitA(u,v,x,y,v0),add(smul(x,v),smul(y,u))))
    z=(random.uniform(-5,5),random.uniform(-5,5)); w=(random.uniform(-5,5),random.uniform(-5,5)); r=random.uniform(-5,5)
    chk("fitA_add", vclose(fitA(u,v,x,y,add(z,w)), add(fitA(u,v,x,y,z),fitA(u,v,x,y,w)),1e-8))
    chk("fitA_smul", vclose(fitA(u,v,x,y,smul(r,z)), smul(r,fitA(u,v,x,y,z)),1e-8))
    # orderedRay_condition for arbitrary-sign a,b,c,d
    a2,b2,c2,d2=[random.uniform(-5,5) for _ in range(4)]
    chk("orderedRay det1=2q", close(det(add(smul(q,v0),u0), add(smul(-q,v0),u0)), 2*q))
    chk("orderedRay det2=ad+bc", close(det(add(smul(a2,v),smul(b2,u)), add(smul(-c2,v),smul(d2,u))), a2*d2+b2*c2,1e-8))

# ---------- inserted_arc_props (Unit R statement, built on MF) ----------
def inserted(pm,l,u,v,x,y,t): return add(pm, smul(l/12, fitA(u,v,x,y, sub(cModel(t),bModel(-2)))))
for _ in range(1500):
    a,b,c,d=[10**random.uniform(-2,2) for _ in range(4)]
    th0=random.uniform(-math.pi,math.pi); u,v=frame(th0); x=xFit(a,b,c,d); y=yFit(a,b,c,d)
    p=(random.uniform(-3,3),random.uniform(-3,3)); pm=add(p,(random.uniform(-1,1),random.uniform(-1,1)))
    l=10**random.uniform(-3,1)
    pp=add(pm,smul(l,u)); xi1=dot(sub(pm,p),v)
    Phi=lambda t: inserted(pm,l,u,v,x,y,t)
    chk("Phi(-2)=p-", vclose(Phi(-2),pm,1e-8)); chk("Phi(2)=p+", vclose(Phi(2),pp,1e-8))
    h=1e-6
    dm=smul(1/(2*h),sub(Phi(-2+h),Phi(-2-h))); Tm=add(smul(a,v),smul(b,u)); Tm=normalize(Tm)
    r=dot(dm,Tm); chk("deriv Phi(-2)=r T-, r>0", r>0 and vclose(dm,smul(r,Tm),1e-5))
    dp=smul(1/(2*h),sub(Phi(2+h),Phi(2-h))); Tp=normalize(add(smul(-c,v),smul(d,u)))
    r=dot(dp,Tp); chk("deriv Phi(2)=r T+, r>0", r>0 and vclose(dp,smul(r,Tp),1e-5))
    chk("Phi(-1)=Phi(1)", vclose(Phi(-1),Phi(1),1e-8))
    d1=smul(1/(2*h),sub(Phi(1+h),Phi(1-h))); dm1=smul(1/(2*h),sub(Phi(-1+h),Phi(-1-h)))
    chk("det(Phi'(1),Phi'(-1))<0", det(d1,dm1)<0)
    for k in range(-40,41):
        t=k/20
        ex=dot(sub(Phi(t),p),v)-xi1
        if abs(t)<2: chk("excess>0", ex>0,(a,b,c,d,t,ex))
        chk("excess = l x (4-t^2)/12", close(ex, l*x*(4-t*t)/12, 1e-8))
        chk("diam <= l(x+2)", norm(sub(Phi(t),pm)) <= l*(x+2)+1e-12,(a,b,c,d,t))
        chk("6+t^3-t in [0,12]", 0-1e-12<=6+t**3-t<=12+1e-12)
print("Unit MF/R probes done; failures so far:", len(FAILS))

# ---------- Unit HT: collar inequalities (Mathlib Real.smoothTransition) ----------
def eng(x): return math.exp(-1/x) if x>0 else 0.0
def phi(x): return eng(x)/(eng(x)+eng(1-x))
def dphi(x,h=1e-6): return (phi(x+h)-phi(x-h))/(2*h)
def blend(f,g,e1,lam,eta): s=phi((eta-e1)/lam); return (1-s)*f(eta)+s*g(eta)
def nd(F,eta,h=1e-6): return (F(eta+h)-F(eta-h))/(2*h)
# check phi monotone & endpoint values
for k in range(0,101):
    xx=k/100
    chk("phi'>=0", dphi(xx)>=-1e-9)
chk("phi(0)=0", phi(0)==0 and phi(-0.3)==0); chk("phi(1)=1", close(phi(1),1) and close(phi(1.5),1))
# collar at p-: f(e1)=g(e1), f'>0 on [e1,e1+lam], f'<g' on (e1,e1+lam]
for _ in range(300):
    e1=random.uniform(-2,2); lam=10**random.uniform(-2,0.5)
    # f' positive random polynomial: f'(eta)=A+B*(eta-e1)+C*(eta-e1)^2 with A>0 ensured positive on interval
    A=random.uniform(0.1,3); B=random.uniform(-1,1); C=random.uniform(-1,1)
    f=lambda eta,A=A,B=B,C=C,e1=e1: A*(eta-e1)+B*(eta-e1)**2/2+C*(eta-e1)**3/3
    D=random.uniform(0.01,3); E=random.uniform(0,2)
    g=lambda eta,f=f,D=D,E=E,e1=e1: f(eta)+D*(eta-e1)**2/2+E*(eta-e1)**3/3   # g'-f' = D(eta-e1)+E(eta-e1)^2 >0 on (e1,..]
    ok=all(nd(f,e1+lam*k/50)>0 for k in range(0,51))
    if not ok: continue
    for k in range(0,51):
        eta=e1+lam*k/50
        hp=nd(lambda s: blend(f,g,e1,lam,s), eta)
        chk("deriv_blend_ge", hp >= nd(f,eta)-1e-6,(e1,lam,eta,hp,nd(f,eta)))
        fe=f(eta); ge=g(eta); he=blend(f,g,e1,lam,eta)
        chk("blend_between", fe-1e-9<=he<=ge+1e-9)
        if k>0: chk("sep_of_deriv", ge>fe)
    chk("blend_eq_left", blend(f,g,e1,lam,e1-0.3)==f(e1-0.3)); chk("blend_eq_right", close(blend(f,g,e1,lam,e1+lam+0.2),g(e1+lam+0.2)))
# collar at p+: blend g f (e2-lam) lam ; f(e2)=g(e2), f'<0 on [e2-lam,e2], g'<f' on [e2-lam,e2)
for _ in range(300):
    e2=random.uniform(-2,2); lam=10**random.uniform(-2,0.5)
    A=random.uniform(0.1,3); B=random.uniform(-1,1); C=random.uniform(-1,1)
    f=lambda eta,A=A,B=B,C=C,e2=e2: -A*(eta-e2)+B*(eta-e2)**2/2+C*(eta-e2)**3/3
    D=random.uniform(0.01,3); E=random.uniform(0,2)
    # want g'-f' <0 on [e2-lam,e2): g'-f' = D(eta-e2) - E(eta-e2)^2  (negative for eta<e2)
    g=lambda eta,f=f,D=D,E=E,e2=e2: f(eta)+D*(eta-e2)**2/2-E*(eta-e2)**3/3
    ok=all(nd(f,e2-lam+lam*k/50)<0 for k in range(0,51))
    if not ok: continue
    for k in range(0,51):
        eta=e2-lam+lam*k/50
        hp=nd(lambda s: blend(g,f,e2-lam,lam,s), eta)
        chk("deriv_blend_le", hp <= nd(f,eta)+1e-6,(e2,lam,eta,hp,nd(f,eta)))
        chk("mirror sep g>=f", g(eta)>=f(eta)-1e-12)
        he=blend(g,f,e2-lam,lam,eta); chk("mirror between", f(eta)-1e-9<=he<=g(eta)+1e-9)
print("Unit HT probes done; failures so far:", len(FAILS))

# ---------- Unit G chart formulas on a random curve ----------
# F(t) generic smooth closed curve; check eta' = |F'| cos(thetarel), xi' = -|F'| sin(thetarel)
for _ in range(200):
    A1,A2,B1,B2=[random.uniform(0.5,2) for _ in range(4)]; ph=random.uniform(0,6)
    F=lambda t: (A1*math.cos(2*math.pi*t)+0.3*B1*math.cos(4*math.pi*t+ph), A2*math.sin(2*math.pi*t)+0.3*B2*math.sin(4*math.pi*t))
    dF=lambda t: nd(lambda s: F(s)[0],t), 
    def dF(t): return (nd(lambda s: F(s)[0],t), nd(lambda s: F(s)[1],t))
    t0=random.uniform(0,1); u=normalize(dF(t0)); Ju=(-u[1],u[0]); v=(-Ju[0],-Ju[1]); p=F(t0)
    xi=lambda t: dot(sub(F(t),p),v); eta=lambda t: dot(sub(F(t),p),u)
    t=t0+random.uniform(-0.05,0.05)
    T=normalize(dF(t)); ang=math.atan2(det(u,T),dot(u,T))  # theta_rel
    chk("hasDerivAt_eta", close(nd(eta,t), norm(dF(t))*math.cos(ang),1e-4))
    chk("hasDerivAt_xi", close(nd(xi,t), -norm(dF(t))*math.sin(ang),1e-4))
    chk("endpoint_tangent", vclose(T, add(smul(-math.sin(ang),v),smul(math.cos(ang),u)),1e-8))
    chk("det(v,u)=1", close(det(v,u),1))
print("Unit G probes done; failures so far:", len(FAILS))

# ---------- Concrete site: unit circle, curl at p=(1,0), u=(0,1) ----------
def circle(t): return (math.cos(2*math.pi*t), math.sin(2*math.pi*t))
def dcircle(t): return (-2*math.pi*math.sin(2*math.pi*t), 2*math.pi*math.cos(2*math.pi*t))
t0=0.0; p=circle(t0); u=normalize(dcircle(t0)); Ju=(-u[1],u[0]); v=(-Ju[0],-Ju[1])
chk("site u=(0,1)", vclose(u,(0,1))); chk("site v=(1,0)", vclose(v,(1,0)))
alpha,beta=-1/8,1/8
# isolated: tangent = u iff t in Z
for k in range(-125,126):
    t=k/1000
    if abs(t)>1e-12: chk("site isolated", not vclose(normalize(dcircle(t)),u,1e-12))
# theta lift: 2 pi t + pi/2 strictly increasing; check
for k in range(-125,126):
    t=k/1000; th=2*math.pi*t+math.pi/2
    chk("site lift", vclose(normalize(dcircle(t)),(math.cos(th),math.sin(th))))
xi=lambda t: dot(sub(circle(t),p),v); eta=lambda t: dot(sub(circle(t),p),u)
for delta in [0.05,0.02,0.01,0.003]:
    s1,s2=-delta,delta
    chk("cuts xi equal", close(xi(s1),xi(s2)))
    l=eta(s2)-eta(s1); chk("l>0", l>0)
    thm=-2*math.pi*delta; thp=2*math.pi*delta
    a=-math.sin(thm); b=math.cos(thm); c=math.sin(thp); d=math.cos(thp)
    chk("a,b,c,d>0", a>0 and b>0 and c>0 and d>0)
    chk("T- = a v + b u", vclose(normalize(dcircle(s1)), add(smul(a,v),smul(b,u))))
    chk("T+ = -c v + d u", vclose(normalize(dcircle(s2)), add(smul(-c,v),smul(d,u))))
    x=xFit(a,b,c,d); y=yFit(a,b,c,d); pm=circle(s1); pp=circle(s2)
    Phi=lambda t: inserted(pm,l,u,v,x,y,t)
    chk("circle Phi ends", vclose(Phi(-2),pm,1e-8) and vclose(Phi(2),pp,1e-8))
    # new curve: old circle on [s2, s1+1], inserted arc for model t in [-2,2]
    # total turning: integrate angle increments along polyline
    pts=[]
    N=4000
    for i in range(N+1): pts.append(circle(s2+(1-2*delta)*i/N))
    for i in range(1,N+1): pts.append(Phi(-2+4*i/N))
    # pts closes: last = Phi(2)=pp=circle(s2)=first
    tot=0.0
    for i in range(len(pts)-1):
        d0=sub(pts[(i+1)%(len(pts)-1)],pts[i%(len(pts)-1)]); d1=sub(pts[(i+2)%(len(pts)-1)],pts[(i+1)%(len(pts)-1)])
        tot+=math.atan2(det(d0,d1),dot(d0,d1))
    rotp=tot/(2*math.pi)
    chk("circle rot(F')=0 (=1-1)", close(rotp,0.0,1e-3) or abs(rotp)<2e-3,(delta,rotp))
    # inserted arc inside disc of radius r about p, and old window arc too
    r=max(norm(sub(Phi(-2+4*i/N),p)) for i in range(N+1)); r=max(r,max(norm(sub(circle(s1+2*delta*i/N),p)) for i in range(N+1)))
    # disc meets rest only in arc: circle points within r of p have |t|<= arcsin-ish; ensure r small so params within [alpha,beta]
    chk("disc small", r < 2*math.sin(math.pi*(1/8)),(delta,r))
    # (ii) on inserted arc: tangent never u, exactly one -u
    cnt_neg=0; cnt_pos=0
    for i in range(N):
        ta=-2+4*i/N; tb=-2+4*(i+1)/N
        da=sub(Phi(tb),Phi(ta)); T=normalize(da)
        if dot(T,u)>0.999999 and abs(det(T,u))<1e-3: cnt_pos+=1
    # count -u crossings: sign changes of the v-component of tangent while u-component negative
    prev=None
    for i in range(N):
        ta=-2+4*i/N; tb=-2+4*(i+1)/N
        da=sub(Phi(tb),Phi(ta)); T=normalize(da)
        s=math.copysign(1,dot(T,v))
        if prev is not None and s!=prev and dot(T,u)<0: cnt_neg+=1
        prev=s
    chk("circle (ii): no tangent u on inserted arc", cnt_pos==0,(delta,cnt_pos))
    chk("circle (ii): exactly one -u", cnt_neg==1,(delta,cnt_neg))
    # tails inside disc have no -u tangent (angles in (-pi/2,pi/2))
    for k in range(-125,126):
        t=k/1000
        if norm(sub(circle(t),p))<=r and not (s1<t<s2): chk("tails no ±u", dot(normalize(dcircle(t)),u)>0)
    # (iii) unique double point: Phi(-1)=Phi(1), sign det(later, earlier)<0, and it lies in disc
    h=1e-6
    d1=smul(1/(2*h),sub(Phi(1+h),Phi(1-h))); dm1=smul(1/(2*h),sub(Phi(-1+h),Phi(-1-h)))
    chk("circle (iii) kink negative", det(d1,dm1)<0)
    chk("circle kink in disc", norm(sub(Phi(1),p))<=r)
    # inserted interior vs tails: excess xi > xi(s1) and tails xi<xi(s1)
    for i in range(1,N): chk("circle excess", dot(sub(Phi(-2+4*i/N),p),v) > xi(s1))
    for k in range(-125,126):
        t=k/1000
        if not (s1<=t<=s2): chk("circle tails xi<xi(s1)", xi(t)<xi(s1)-1e-15,(t,))
    # x -> 0, l -> 0 as delta -> 0 (diameter control)
    chk("x small", x < 1.0,(delta,x))
print("Circle site probes done; failures so far:", len(FAILS))

# ---------- Non-symmetric site: ellipse-ish curve with asymmetric cuts via IVT ----------
def Fe(t): return (1.3*math.cos(2*math.pi*t)+0.2*math.cos(4*math.pi*t), 0.8*math.sin(2*math.pi*t)+0.1*math.sin(4*math.pi*t+0.4))
def dFe(t): return (nd(lambda s: Fe(s)[0],t), nd(lambda s: Fe(s)[1],t))
for t0 in [0.03,0.21,0.37,0.5,0.66,0.8]:
    p=Fe(t0); u=normalize(dFe(t0)); Ju=(-u[1],u[0]); v=(-Ju[0],-Ju[1])
    xi=lambda t: dot(sub(Fe(t),p),v); eta=lambda t: dot(sub(Fe(t),p),u)
    # check positive turning near t0
    def ang(t): T=normalize(dFe(t)); return math.atan2(det(u,T),dot(u,T))
    turnpos=all(ang(t0+0.002*(k+1))>ang(t0+0.002*k) for k in range(-10,10))
    if not turnpos: continue
    for level in [-1e-3,-1e-4,-1e-5]:
        # find s1<t0 with xi(s1)=level via bisection on [t0-0.05,t0]; s2 on [t0,t0+0.05]
        lo,hi=t0-0.05,t0
        if xi(lo)>level: continue
        for _ in range(80):
            mid=(lo+hi)/2
            if xi(mid)<level: lo=mid
            else: hi=mid
        s1=(lo+hi)/2
        lo,hi=t0,t0+0.05
        if xi(hi)>level: continue
        for _ in range(80):
            mid=(lo+hi)/2
            if xi(mid)>level: lo=mid
            else: hi=mid
        s2=(lo+hi)/2
        l=eta(s2)-eta(s1); chk("ell l>0", l>0)
        am=ang(s1); ap=ang(s2)
        a=-math.sin(am); b=math.cos(am); c=math.sin(ap); d=math.cos(ap)
        chk("ell a,b,c,d>0", a>0 and b>0 and c>0 and d>0,(t0,level,a,b,c,d))
        x=xFit(a,b,c,d); y=yFit(a,b,c,d); pm=Fe(s1); pp=Fe(s2)
        Phi=lambda t: inserted(pm,l,u,v,x,y,t)
        chk("ell Phi(2)=p+", vclose(Phi(2),pp,1e-6),(t0,level,Phi(2),pp))
        h=1e-7
        dm=smul(1/(2*h),sub(Phi(-2+h),Phi(-2-h))); T1=normalize(dFe(s1)); r_=dot(dm,T1)
        chk("ell tangent ray -", r_>0 and vclose(normalize(dm),T1,1e-4))
        dp=smul(1/(2*h),sub(Phi(2+h),Phi(2-h))); T2=normalize(dFe(s2)); r_=dot(dp,T2)
        chk("ell tangent ray +", r_>0 and vclose(normalize(dp),T2,1e-4))
        # turning: old curve rot (should be 1) vs new (0)
        N=3000
        def rot_of(pts):
            tot=0.0; M=len(pts)
            for i in range(M):
                d0=sub(pts[(i+1)%M],pts[i]); d1=sub(pts[(i+2)%M],pts[(i+1)%M])
                tot+=math.atan2(det(d0,d1),dot(d0,d1))
            return tot/(2*math.pi)
        old=[Fe(i/N) for i in range(N)]
        new=[Fe(s2+(1-(s2-s1))*i/N) for i in range(N)]+[Phi(-2+4*i/N) for i in range(1,N)]
        r0=rot_of(old); r1=rot_of(new)
        chk("ell rot drops by 1", close(r1,r0-1,1e-2) or abs(r1-(r0-1))<2e-2,(t0,level,r0,r1))
        d1=smul(1/(2*h),sub(Phi(1+h),Phi(1-h))); dm1=smul(1/(2*h),sub(Phi(-1+h),Phi(-1-h)))
        chk("ell kink negative", det(d1,dm1)<0)
        for i in range(1,N): chk("ell excess", dot(sub(Phi(-2+4*i/N),p),v) > xi(s1)-1e-12,(t0,level))
print("Ellipse site probes done; failures so far:", len(FAILS))

# ---------- Unit T formula sanity: rot difference = (Δθ' − Δθ)/2π with Δθ' = Δθ − 2π ----------
for _ in range(100):
    dth=random.uniform(0.01,3); chk("rot diff -1", close(((dth-2*math.pi)-dth)/(2*math.pi), -1))

print("TOTAL FAILURES:", len(FAILS))
seen=set()
for n,i in FAILS:
    if n not in seen:
        seen.add(n); print("FAIL", n, i)
