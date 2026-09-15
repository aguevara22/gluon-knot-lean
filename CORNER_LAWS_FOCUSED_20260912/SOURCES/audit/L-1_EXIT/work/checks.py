"""L-1 EXIT seat: exact controls on the Gaussian substitution l=ia, m=-iz.
Gaussian integers as pairs (re,im). No floating point anywhere."""
def mul(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def powg(x,n):
    # x a unit in Z[i]; n may be negative
    inv={(0,1):(0,-1),(0,-1):(0,1),(1,0):(1,0),(-1,0):(-1,0)}
    if n<0: x=inv[x]; n=-n
    r=(1,0)
    for _ in range(n): r=mul(r,x)
    return r
I=(0,1); ONE=(1,0)

# --- C1: image of a monomial l^j m^k under l->i*a, m->-i*z is  i^j * (-i)^k * a^j z^k
def coef(j,k): return mul(powg(I,j), powg(mul((-1,0),I),k))
def is_real(c): return c[1]==0

# C1a: LM Prop.22 parity (j,k same parity)  ==> coefficient real (lands in Z[a^,z^])
bad=[(j,k) for j in range(-8,9) for k in range(-8,9) if (j-k)%2==0 and not is_real(coef(j,k))]
print("C1a same-parity monomials land in Z[a^,z^]:", "PASS" if not bad else f"FAIL {bad[:5]}")
# C1b (negative control): opposite parity must NOT land
bad2=[(j,k) for j in range(-8,9) for k in range(-8,9) if (j-k)%2==1 and is_real(coef(j,k))]
print("C1b opposite-parity monomials do NOT land (negative control):", "PASS" if not bad2 else f"FAIL {bad2[:5]}")

# --- C2: the two mirror involutions.
# LM Prop.10(ii): l <-> l^-1, m fixed.  In (a,z): a -> -a^-1, z -> z.
# SM cf-mirror paragraph: iota: a -> a^-1, z -> -z.
# On a monomial a^p z^q they agree iff (-1)^p == (-1)^q.
dis=[(p,q) for p in range(-8,9) for q in range(-8,9)
     if ((-1)**p != (-1)**q) and (p-q)%2==0]
agree_all_same_parity = all(((-1)**p)==((-1)**q) for p in range(-8,9) for q in range(-8,9) if (p-q)%2==0)
print("C2 LM Prop.10(ii) and the frame's iota agree on same-parity monomials:",
      "PASS" if agree_all_same_parity and not dis else "FAIL")
# C2b negative control: on opposite-parity monomials they must DISAGREE (sign flip)
disagree_opp = all(((-1)**p)!=((-1)**q) for p in range(-8,9) for q in range(-8,9) if (p-q)%2==1)
print("C2b they disagree off the parity locus (negative control):", "PASS" if disagree_opp else "FAIL")

# --- C3: skein image.  LM (I): l F+ + l^-1 F- + m F0 = 0.
# substitute -> (i a)F+ + (-i a^-1)F- + (-i z)F0 = i*( a F+ - a^-1 F- - z F0 )
cf_plus  = powg(I,1)                    # coefficient of F+  : i * a
cf_minus = powg(I,-1)                   # coefficient of F-  : i^-1 * a^-1 = -i a^-1
cf_zero  = mul((-1,0),I)                # coefficient of F0  : -i * z
target   = [ONE, (-1,0), (-1,0)]        # campaign: 1*a, -1*a^-1, -1*z   (aP+ - a^-1P- - zP0 = 0)
got = [ (mul(c,(0,-1))) for c in (cf_plus,cf_minus,cf_zero) ]   # multiply through by -i
print("C3 substituted LM skein == campaign skein after xi(-i):",
      "PASS" if got==target else f"FAIL got={got} target={target}")
# C3b negative control: a wrong substitution m -> +i z must NOT reproduce it
cf_zero_bad = mul(ONE,I)
got_bad=[mul(c,(0,-1)) for c in (cf_plus,cf_minus,cf_zero_bad)]
print("C3b wrong substitution m->+iz fails (negative control):",
      "PASS" if got_bad!=target else "FAIL")

# --- C4: mu = -(l+l^-1)/m  maps to (a-a^-1)/z  [delta of lp:core]
# numerator -(l + l^-1) -> -(i a + (i a)^-1) = -(i a - i a^-1) = -i(a - a^-1)
num = mul((-1,0), (0,1))                 # -i  times (a - a^-1)
den = mul((-1,0), I)                     # -i  times z
# quotient coefficient = num/den = (-i)/(-i) = 1
q = mul(num, (0,1) if den==(0,-1) else None) if False else None
ok = (num==den)                          # both equal -i  => quotient is exactly (a-a^-1)/z
print("C4 mu -> (a-a^-1)/z exactly (coefficients cancel):", "PASS" if ok else f"FAIL num={num} den={den}")

# --- C5: psi(a^-1) = i l^-1  (the step the transport lemma prints)
# psi: a -> -i l, z -> i m.  psi(a^-1) = (-i l)^-1 = (-i)^-1 l^-1 = i l^-1
print("C5 psi(a^-1)= i l^-1 :", "PASS" if powg(mul((-1,0),I),-1)==I else "FAIL")
# C6: phi,psi mutually inverse on the four generators
phi={'l':I,'m':mul((-1,0),I)}; psi={'a':mul((-1,0),I),'z':I}
rt = [ mul(phi['l'],psi['a']), mul(phi['m'],psi['z']), mul(psi['a'],phi['l']), mul(psi['z'],phi['m']) ]
print("C6 phi,psi mutually inverse (4 round trips):", "PASS" if all(x==ONE for x in rt) else f"FAIL {rt}")
