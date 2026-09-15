"""Check Wenzl 1988 Lemma 2.1 (i),(ii),(vi) — asserted on p.362 as 'straightforward
computations', not printed — and SM6's hd:axial-sum / hd:axial-relation (sm-7:769-780).
Exact rational function arithmetic in Q(q).  Verifies a SOURCE's own algebra."""
import sympy as sp
q = sp.symbols('q')
def a(d):
    d = sp.Integer(d)
    return sp.cancel((1-q**(d+1))/((1+q)*(1-q**d)))
def aS(d):   # symbolic exponent
    return sp.cancel((1-q*d)/((1+q)*(1-d)))   # d stands for q^d

print("2.1(i)  a_d + a_-d = 1 :",
      all(sp.simplify(a(d)+a(-d)-1)==0 for d in range(-6,7) if d!=0))

print("2.1(vi) a_m = a_n  iff  q^(m-n)=1 (sample m!=n, generic q):",
      all(sp.simplify(a(m)-a(n))!=0 for m in range(-5,6) for n in range(-5,6)
          if m!=0 and n!=0 and m!=n))

# 2.1(ii): k,l,m in N with k+m=l  =>  q/(1+q)^2 = a_k a_m + a_l a_-m - a_k a_l
#                                             = a_k a_m + a_l a_-k - a_m a_l
target = sp.Rational(1,1)*q/(1+q)**2
ok1 = ok2 = True
for k in range(1,7):
    for m in range(1,7):
        l = k+m
        if sp.simplify(a(k)*a(m)+a(l)*a(-m)-a(k)*a(l) - target)!=0: ok1=False
        if sp.simplify(a(k)*a(m)+a(l)*a(-k)-a(m)*a(l) - target)!=0: ok2=False
print("2.1(ii) first form  :", ok1)
print("2.1(ii) second form :", ok2)
print("2.1(ii) a_d a_{-d-1} = q/(1+q)^2 :",
      all(sp.simplify(a(d)*a(-d-1)-target)==0 for d in range(-6,7) if d not in (0,-1)))

# SM6 hd:axial-sum / hd:axial-relation, with X=q^k, Y=q^m, ell=k+m
X, Y = sp.symbols('X Y')
def aX(v):  return sp.cancel((1-q*v)/((1+q)*(1-v)))
lhs = sp.simplify(1 - aX(X) - aX(Y))
rhs = -sp.cancel((1-q)*(1-X*Y)/((1+q)*(1-X)*(1-Y)))
print("hd:axial-sum        :", sp.simplify(lhs-rhs)==0)
rel = sp.simplify(aX(X)*aX(Y) + aX(X*Y)*(1-aX(X)-aX(Y)) - target)
print("hd:axial-relation   :", rel==0)
print("common numerator id : (1-qX)(1-qY)-(1-q)(1-qXY) == q(1-X)(1-Y) :",
      sp.simplify(sp.expand((1-q*X)*(1-q*Y)-(1-q)*(1-q*X*Y)) - sp.expand(q*(1-X)*(1-Y)))==0)

# the p.365 base case, from Wenzl's own (2.3)+a_d
print("pi_[2](e_1)   = a_{-1} =", sp.simplify(a(-1)), " (Wenzl p.365 prints 1)")
print("pi_[1^2](e_1) = a_{+1} =", sp.simplify(a(1)),  " (Wenzl p.365 prints 0)")

# (3.5) vs printed (3.6) numerators
eta, c = sp.symbols('eta c')
A = 1 - eta*(1+q); B = q - eta*(1+q)
qc = sp.symbols('qc')                       # qc stands for q^{j-i}
num35 = sp.expand(A - B*qc)
num36 = sp.expand((q - qc) - (1+q)*(1-qc)*eta)
print("(3.5) numerator  :", sp.simplify(num35))
print("(3.6) numerator  :", sp.simplify(num36))
print("difference       :", sp.simplify(num35-num36))
print("one box (qc=1): (3.5) ->", sp.simplify(num35.subs(qc,1)/(1-q)),
      "  (3.6) ->", sp.simplify(num36.subs(qc,1)/(1-q)))
# SM6 hd:correct-numerator
print("SM6 hd:correct-numerator equals (3.5) numerator :",
      sp.simplify(num35 - (1 - q*qc - (1+q)*(1-qc)*eta))==0)
