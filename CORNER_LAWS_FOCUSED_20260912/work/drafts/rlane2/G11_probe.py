# Numerical truth checks for the G11 geometric leaves (Option A: single apex).
# Coordinates: strand m = x-axis oriented +x; x_mp=(0,0), x_mq=(1,0); x_pq=(u,h) with h>0 (triangle above m).
# m0=(mu,0) with 0<mu<1; apex w = m0 + lam*(x_pq - m0), lam>1; p_in=(-eps,0), p_out=(1+eps,0).
import random, math
def det(a,b): return a[0]*b[1]-a[1]*b[0]
def sub(a,b): return (a[0]-b[0],a[1]-b[1])
def seg_inter(A,B,C,D):
    # returns (s,t) params of intersection of segments AB and CD if they cross properly
    r=sub(B,A); q=sub(D,C); den=det(r,q)
    if abs(den)<1e-12: return None
    s=det(sub(C,A),q)/den; t=det(sub(C,A),r)/den
    if 0<s<1 and 0<t<1: return (s,t)
    return None
random.seed(1)
bad=0
for _ in range(20000):
    u=random.uniform(-3,4); h=random.uniform(0.05,3); mu=random.uniform(0.05,0.95)
    lam=random.uniform(1.01,3); eps=random.uniform(0.01,1)
    xmp=(0,0); xmq=(1,0); xpq=(u,h); m0=(mu,0)
    w=(mu+lam*(u-mu), lam*h); pin=(-eps,0); pout=(1+eps,0)
    # strands p through xmp and xpq, q through xmq and xpq, extended far
    def far(A,B,L=50):
        d=sub(B,A); n=math.hypot(*d); d=(d[0]/n,d[1]/n)
        return ((A[0]-L*d[0],A[1]-L*d[1]),(A[0]+L*d[0],A[1]+L*d[1]))
    pA,pB=far(xmp,xpq); qA,qB=far(xmq,xpq)
    # C2: p crosses [w,pout] exactly, not [pin,w]; q crosses [pin,w], not [w,pout]
    c1=seg_inter(pA,pB,w,pout); c2=seg_inter(pA,pB,pin,w)
    c3=seg_inter(qA,qB,pin,w); c4=seg_inter(qA,qB,w,pout)
    if not (c1 and not c2 and c3 and not c4): bad+=1; continue
    # C4: sign preservation: det(d_p, pout-w) vs det(d_p, d_m); det(d_q, w-pin) vs det(d_q,d_m)
    dp=sub(xpq,xmp); dq=sub(xpq,xmq); dm=(1,0)
    if det(dp,sub(pout,w))*det(dp,dm)<=0: bad+=1; continue
    if det(dq,sub(w,pin))*det(dq,dm)<=0: bad+=1; continue
    # D9: along p, x_pq lies strictly between x_mp and the new crossing x_mp'
    s_pq=0.5; # p parametrized from pA to pB: param of xpq vs xmp vs new crossing
    def par(pt,A,B):
        d=sub(B,A); return ((pt[0]-A[0])*d[0]+(pt[1]-A[1])*d[1])/(d[0]**2+d[1]**2)
    tp_mp=par(xmp,pA,pB); tp_pq=par(xpq,pA,pB); tp_new=c1[0]
    if not (min(tp_mp,tp_new)<tp_pq<max(tp_mp,tp_new)): bad+=1; continue
    tq_mq=par(xmq,qA,qB); tq_pq=par(xpq,qA,qB); tq_new=c3[0]
    if not (min(tq_mq,tq_new)<tq_pq<max(tq_mq,tq_new)): bad+=1; continue
    # x_pq in interior of Theta=conv(pin,w,pout): barycentric
    def bary(P,A,B,C):
        d=det(sub(B,A),sub(C,A)); 
        return (det(sub(B,P),sub(C,P))/d, det(sub(C,P),sub(A,P))/d, det(sub(A,P),sub(B,P))/d)
    b=bary(xpq,pin,w,pout)
    if not all(x>0 for x in b): bad+=1; continue
print("violations:",bad,"of 20000")
