# R local complement — extreme selected empty/full couple

Status: **PROVED intermediate lemma**, conditional on accepted R-LOC-2, R-PAR,
R-EXTERIOR and the manuscript's `ax:gausscode`, HOMFLY, grouped-carrier,
rotation and carrier-floor interfaces.  This is not yet a sealed R-chain claim
pack.

The establishing statements and proofs of R-LOC-2, R-PAR-v6, and
R-EXTERIOR-1 are printed in `R_ATTACHMENT_WARRANTS.md`, sections
"R-LOC-2 — localization", "R-PAR-v6 — parity and availability", and
"R-EXTERIOR-1 — the triangle-disjoint factor". The shorter names R-LOC,
R-PAR, and R-EXTERIOR below denote those same statements.

## Statement

Fix a full-availability fiber at a simple RIII wall in the extreme graph orbit.
Let `H` denote the side whose local graph is `K3`, let `L` denote the side whose
local graph is empty, and fix the outside support `Q`.  After smoothing `Q`
first, relabel the local crossings and the three intervening successor strings
so the triangle-touching carrier has the exact words

```text
H = x y A z x B y z C,
L = y x A x z B z y C.                              (1)
```

Full availability is a hypothesis of the statement, not merely scene-setting:
it says every member of `T={x,y,z}` is nonadjacent to `Q`, and therefore makes
`Q union T` an independent support on `L`.  On `H`, `T` is not independent
because its induced graph is `K3`.  R-LOC-2 clause 4 identifies these as the
two complementary extreme graphs: `H[T]=K3` if and only if `L[T]` is empty.

Write `T_nu(J)` for the complete X1 term of `Q union J` on side `nu`, with an
absent row read as zero.  Then

```text
T_H(empty) - T_L(empty) = T_L(xyz).                  (2)
```

Since `xyz` is absent on the `K3` side, (2) is exactly the extreme selected
empty/full complementary-couple identity.  Equation (2), whose sides are named
by their graphs, is independent of coorientation; only its directed-wall
residue form is multiplied by `-1` when the parameter coorientation reverses.

Here is the signed local ledger used below.  Let the oriented strand directions
be `u1,u2,u3`, with

```text
x=(u1,u2),       y=(u1,u3),       z=(u2,u3),
s_x=sgn det(u1,u2), s_y=sgn det(u1,u3),
s_z=sgn det(u2,u3).
```

For completeness, the exact line-order calculation gives, if `delta` is the
sign of the three-line determinant and `q_i` records the order of the other two
intersections along `u_i`,

```text
(q_1,q_2,q_3)=-delta(s_x s_y, s_x s_z, s_y s_z).
```

This follows by putting the two Cramer formulas over a common denominator; for
example `t_12-t_13=-Delta/(det(u1,u2)det(u1,u3))`, and the other two rows are
its cyclic permutations.  Directly reading the six local visits says the three
local graph indicators agree exactly for `q=(-,+,-)` or `(+,-,+)`.  Thus the
extreme orbit is precisely

```text
s_x=s_z=-s_y=:sigma.                                  (1a)
```

The divide over-orders in the two possible sign branches are

```text
sigma   x                 y                 z             after switching x
  +     u1 over u2        u3 over u1        u2 over u3    u2 > u3 > u1
  -     u2 over u1        u1 over u3        u3 over u2    u1 > u3 > u2.
                                                               (1b)
```

In particular the original order is cyclic and switching `x` makes it
transitive.  Smoothing all three local crossings gives the signed port table

```text
outer A: u2 -> u1, sign -s_x;
outer B: u3 -> u2, sign -s_z;
outer C: u1 -> u3, sign  s_y.                          (1c)
```

All three outer corners therefore have the common sign
`s_o=-sigma`; the three central-triangle corners have sign `sigma=-s_o`.

## 1. Arbitrary Q and the grouped contact diagrams

Full availability makes every member of `Q` nonadjacent to `x,y,z`.  As in the
generic successor lift, its two visits lie in one macro-gap `A`, `B`, or `C`,
so the `Q` reconnections act independently inside the three printed strings.
Internal successor cycles with no triangle visit are the exterior carriers of
R-EXTERIOR and contribute one common scalar `C_Q`; it may be zero and will
never be divided out.

The three local crossings are connected in the `K3` residual graph, hence all
six visits lie on one `Q`-carrier.  The same lifted skeleton in (1) gives one
triangle-touching empty-row carrier on `L`.  On each side, group every residual
piece owned by that carrier with `cor:groupedknot`, clauses (A) and (B).  Call
the resulting positive knot diagrams `D_H,D_L`, their
polynomials `F_H,F_L`, their common grouped writhe `w`, and their common
absolute carrier rotation `R`.

The writhe agrees because the retained label set agrees: R-LOC changes only
the three internal interlacement edges.  Rotation and the empty-row selector
agree by the guarded RIII path: polygon and Q-smoothing corner determinants
stay nonzero, the G3 collision creates no corner, and `lem:turnlift(ii)` keeps
the rotation of the matched carrier.  Put

```text
W = wt(empty contact carrier),
d = 1-w-R,
Omega_H = [a^d z^0] F_H,
Omega_L = [a^d z^0] F_L.                             (3)
```

All other factors are in `C_Q`.  Thus the left side of (2) is
`C_Q W (Omega_H-Omega_L)`.

## 2. Two matched switches and two subtracted skeins

Every retained crossing of `D_H,D_L` is positive by the divide convention.
The signed table (1b) shows that switching `x` breaks the cyclic over-order and
makes it transitive in each of the two extreme sign branches.  Apply the
ordinary oriented RIII change to this common transitive local over-order.
R-LOC-2 clauses 1 and 3, together with the matched exterior data, then give an
isomorphism of the full oriented traversal records of `D_H^{x-}` and
`D_L^{x-}`.  Both switched diagrams remain connected one-circle diagrams, so
`ax:gausscode` identifies their oriented knots and `ax:homfly` gives

```text
P(D_H^{x-}) = P(D_L^{x-}).                            (4)
```

Let `D_H^x,D_L^x` be the oriented smoothings at `x`.  Subtract the two HOMFLY
skein equations at `x`; (4) cancels the switched terms and gives

```text
F_H-F_L = a^(-1) z ( P(D_H^x)-P(D_L^x) ).            (5)
```

Now switch `y` in both smoothed diagrams.  The oriented smoothing at `x` uses
the same cross-pairing of the `u1,u2` ports on both sides.  Reading (1) after
that pairing gives the exact successor rows

```text
H after x:  y A z | B y z C   -> A | BC after deleting y,z,
L after x:  A | z B z y C y   -> A | BC after deleting y,z.       (5a)
```

The divide crossing `z` is positive, while switched `y` is negative;
their common `u3` strand and the smoothed `u1/u2` strand give the
orientation-compatible cross-pairing.  Thus on each side they bound an empty
oriented RII bigon.  Delete that bigon on each side, obtaining two-component
diagrams `E_H,E_L`.  The common successor row `A | BC` in (5a) gives the same
oriented pairing of the local boundary strands.  Outside the event disc, the
simple-event path is an isotopy of the retained strands and crossings, with
R-LOC-2 clauses 1 and 3 identifying their labels and order.  After the local
`y,z` pair is deleted, the RIII collision has disappeared, so this path extends
through the wall as an ambient isotopy from `E_H` to `E_L`.  Reidemeister-II
invariance on the two sides and isotopy invariance in `ax:homfly` therefore give

```text
P((D_H^x)^{y-}) = P((D_L^x)^{y-}).                   (6)
```

Let `D_H^{xy},D_L^{xy}` denote the further oriented smoothing at `y`.
Subtracting the two skein equations at `y` and using (6), then substituting in
(5), yields the exact polynomial identity

```text
F_H-F_L = a^(-2) z^2
            ( P(D_H^{xy})-P(D_L^{xy}) ).             (7)
```

This is the point missed by the false one-switch route: neither
`D_H^{x-}` nor `D_L^{x-}` is identified with the *unswitched* diagram on the
other side; only the two matched switched diagrams are identified.

Smoothing `x` in the `K3` word splits the contact knot into two components;
there `y` is mixed, so smoothing `y` joins them and `D_H^{xy}` is a knot.
Smoothing `x` in the empty word also splits once, but there `y` is a
self-crossing, so smoothing it splits again and `D_L^{xy}` has three
components.  The retained knot-parity clause of `ax:homfly`,
`P_K in Z[a^(+-1),z^2]`, gives

```text
[z^(-2)] P(D_H^{xy}) = 0.                             (8)
```

## 3. The three components and their lowest z-row

The three components of `J=D_L^{xy}` have successor skeletons

```text
A,                 C,                 z B z.          (9)
```

Classify each outside residual crossing on the contact carrier by its local
mask.  R-PAR gives mask zero or one of the three two-letter masks.  The exact
side vectors of (1) say:

- a mask-zero crossing has both visits in one of `A,B,C`;
- a two-letter-mask crossing has visits in the corresponding two distinct
  gap strings.

Consequently the self-crossing knot polynomials of the first two components
in (9) are the grouped full-state polynomials `f_A,f_C`.  For the third, use
the legitimate empty-side state `Q union {x,y}`.  The residual local crossing
`z` is a singleton: any outside residual neighbour of `z` would, by R-PAR,
also meet `x` or `y` and would therefore be dominated.  It is carried with the
mask-zero `B` pieces.  By `cor:groupedknot`, clauses (A) and (B), its grouped
knot polynomial is

```text
P_{zBz}(a,0) = P_{ {z} }(a,0) f_B(a) = f_B(a),        (10)
```

because the one-crossing positive piece is an unknot.  Thus the product of
the three component rows is

```text
K(a)=f_A(a) f_B(a) f_C(a).                            (11)
```

Every crossing between components of `J` is a retained two-letter-mask
crossing and is positive.  Put `Lambda=lk(J)`, the sum of its three pairwise
linking numbers.  Equivalently, `2 Lambda` is the number of such crossings;
in particular `Lambda>=0`.

The two-component switch argument can be repeated at the one lower row needed
here.  First, every two-component link `E` satisfies
`[z^(-3)]P(E)=0`: switch mixed crossings until the components split.  At each
switch the smoothing is a knot, so the right side at this row is
`[z^(-4)]P(K)=0` by the retained knot-parity clause of `ax:homfly`; at the split
diagram `((a-a^(-1))/z)P(K_1)P(K_2)` has no `z^(-3)` term for the same reason.

It follows that the exact three-component lowest row is

```text
[z^(-2)] P(J)
  = a^(-2 Lambda) (a-a^(-1))^2 K(a).                 (12)
```

Indeed, switch mixed crossings until the components split.  At `z^(-2)` the
smoothing term contributes `[z^(-3)]` of a two-component link, which is zero by
the preceding paragraph.  Hence each switch contributes the usual `a^(-2)`
linking factor.  Since the three components in (9) are oriented knots,
`lem:homflyrows(iii)` gives the split endpoint polynomial as
`((a-a^(-1))/z)^2` times the product of their HOMFLY polynomials; the
knot-parity clause of `ax:homfly` therefore makes its `z^(-2)` row
`(a-a^(-1))^2 K(a)`.  This proves (12).

Equations (7),(8),(12) give

```text
Omega_H-Omega_L
 = -[a^(d+2+2 Lambda)] (a-a^(-1))^2 K(a).             (13)
```

## 4. Selector, rotation and floor ledger

Let `s_o` be the common outer sign computed in (1c); the three
central-triangle corners have the opposite sign.  All nonlocal corners of the
empty contact carrier partition among the three outer carriers.  Let `W_full`
denote the product of the weights of these four triangle-touching full-state
carriers, excluding the exterior factor `C_Q`.

If the empty contact carrier is mixed, then `W=0`.  The full selector is also
zero: were all outer carriers uniform, their common local corner sign `s_o`
would force every inherited nonlocal corner to have sign `s_o`, contrary to
mixedness.  Thus (2) is immediate in this case.

Assume henceforth that the empty contact carrier is uniform.  Define `chi=1`
when its common corner sign is `s_o`, and `chi=0` when its sign is `-s_o`.
These are the two exhaustive branches.

**Live branch (`chi=1`).** Its nonlocal corners have sign `s_o`.  All outer
carriers and the central triangle are uniform.  If `s_o` is right, the outer
weights are `+1` and the all-left three-corner central weight is `-1`; if
`s_o` is left, the outer carriers together have three more left corners than
the parent and the all-right central weight is `+1`.  In both cases

```text
W_full = -W.                                          (14)
```

**Dead branch (`chi=0`).** The parent corners have the central sign, opposite
to `s_o`.  Each outer carrier has exactly one local smoothing corner and, by
`lem:selectorid(A)`, at least two further corners, all inherited from the
parent.  Hence every outer carrier is mixed (indeed exactly one-dissent), so
`W_full=0`.

At each oriented smoothing the two new principal turns have opposite signed
sum, while every inherited principal turn is unchanged.  Applying
`lem:turnlift(ii)` before and after each of the three smoothings therefore makes
the signed rotation additive and gives

```text
rot(A)+rot(B)+rot(C)+rot(central)=rot(parent).         (15)
```

By simplicity and R-LOC-2 clause 2(b), the event disc has no parent vertex on
its three local strand segments.  The central carrier therefore has exactly
the three same-sign smoothing corners described after (1c), so
`lem:uniformrot(i)` gives it absolute rotation one.  In the live branch every
outer carrier is uniform with the parent's sign, while the central has the
opposite sign.  In the dead branch every outer carrier is exactly one-dissent,
as just proved; after a possible global orientation reversal,
`lem:uniformrot(ii)` gives its rotation the sign of its inherited parent
corners, and the central has that same sign.  Therefore

```text
R_A+R_B+R_C = R+1   if chi=1,
R_A+R_B+R_C = R-1   if chi=0.                         (16)
```

Let `w_i,d_i=1-w_i-R_i,omega_i=[a^d_i]f_i` be the full
outer-carrier data and put `D=d_A+d_B+d_C`.  The empty grouped diagram retains
the three positive local crossings, the outer self-crossings, and exactly
`2 Lambda` positive crossings between the outer gap strings.  Hence

```text
w = 3+w_A+w_B+w_C+2 Lambda.                           (17)
```

Combining (3),(16),(17) gives

```text
D = d+4+2 Lambda   if chi=1,
D = d+6+2 Lambda   if chi=0.                          (18)
```

Each outer carrier is uniform in the live branch and exactly one-dissent in the
dead branch.  If it bears pieces, `cor:groupedknot` supplies a positive knot
diagram with that carrier as underlying curve and with no triple point;
genericity supplies finitely many transverse crossings, nonzero principal
turns of magnitude below `pi`, no crossing at a corner, and no corner on a
nonincident edge.  Thus, after a possible orientation reversal,
`thm:carrierfloor` applies.  If the carrier bears no piece,
`thm:carrierfloor(D)` supplies the same lower-support conclusion; if `f_i=0` it is
vacuous.  Hence no exponent below `d_i` occurs in `f_i`, so `K` has no exponent
below `D`, and

```text
[a^D]K = omega_A omega_B omega_C.                     (19)
```

Expand `(a-a^(-1))^2=a^2-2+a^(-2)` in (13).  In the live
branch the requested coefficient samples `K` at `D-4,D-2,D`; the first two
vanish by the floor and the last is (19).  In the dead branch it samples at
`D-6,D-4,D-2`, all below the floor.  Therefore

```text
Omega_H-Omega_L = -omega_A omega_B omega_C   if chi=1,
Omega_H-Omega_L = 0                           if chi=0. (20)
```

The conclusion also covers a zero `z^0` component row or a zero slot
coefficient: every equality is multiplicative and no factor is cancelled.

## 5. Complete-term identity

In the mixed-parent branch both sides of (2) are zero.  In the uniform dead
branch, (20) kills the empty-row difference and the full selector is zero.  In
the live branch, (14),(20), and the central carrier's empty polynomial, slot
zero and coefficient one give

```text
T_H(empty)-T_L(empty)
 = C_Q W (Omega_H-Omega_L)
 = -C_Q W omega_A omega_B omega_C
 = C_Q W_full omega_A omega_B omega_C
 = T_L(xyz).
```

This is (2).  No exterior scalar, selector, or coefficient was divided out.

## Boundary and circularity guards

This proves only the extreme selected empty/full couple.  Together with the
separate extreme pair-zero theorem, the three singleton rows still require
their common transports in the final assembly.  The proof invokes neither
`ax:R` nor an aggregate S7 statement.  Its two local isotopies are an ordinary
RIII after a matched switch and an ordinary RII after one smoothing and a
matched switch; all carrier, owner, rotation, selector and floor data used
afterward are re-established above.
