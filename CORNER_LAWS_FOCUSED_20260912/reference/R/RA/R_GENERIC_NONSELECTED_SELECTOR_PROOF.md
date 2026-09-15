# R local complement — generic nonselected pair rows are selector-dead

Status: **PROVED intermediate lemma**, from accepted R-LOC and the actual
corner/selector definition.  This is not yet an R-chain claim pack or a proof
of the selected complementary-couple identity.

## Statement

Fix a full-availability fiber at a simple RIII wall in the generic graph orbit
`P3 <-> (one edge plus one isolated vertex)`.  Among the three one-sided local
pair supports, one is the graph-selected pair complementary to the degree-two
singleton of `P3`.  Each of the other two pair rows has winding selector zero
on the side where it is present.  This holds for arbitrary exterior gaps and
outside independent support `Q`; no coefficient, exterior-factor division, or
nonvanishing hypothesis is used.

## Oriented line-order calculation

Let the oriented directions of the three strands, indexed `e<f<g`, be
`u_e,u_f,u_g`, and put

```text
D_ef = det(u_e,u_f),  D_eg = det(u_e,u_g),
D_fg = det(u_f,u_g),  Delta = G3(e,f,g).
```

All four quantities are nonzero on either chamber of a simple wall.  Write
`t_ij` for the parameter on oriented line `i` of its intersection with line
`j`.  Expanding the common numerator in the two Cramer formulas for `t_ij`
gives

```text
t_ef-t_eg = -Delta/(D_ef D_eg),
t_fe-t_fg = -Delta/(D_ef D_fg),
t_ge-t_gf = -Delta/(D_eg D_fg).                 (1)
```

For example, the first identity follows directly from

```text
t_ef = det(p_f-p_e,u_f)/D_ef,
t_eg = det(p_g-p_e,u_g)/D_eg;
```

after taking the common denominator, its numerator is the negative of the
three-line determinant defining `Delta`.  The other two identities are the
same calculation after the row permutations `(f,e,g)` and `(g,e,f)`; rewriting
their oriented determinants in the fixed order `ef,eg,fg` gives the displayed
signs.

Let

```text
s_a=sgn(D_ef), s_b=sgn(D_eg), s_c=sgn(D_fg),
delta=sgn(Delta),
q_e=sgn(t_ef-t_eg), q_f=sgn(t_fe-t_fg),
q_g=sgn(t_ge-t_gf).
```

Taking signs in (1) yields

```text
(q_e,q_f,q_g)
 = -delta (s_a s_b, s_a s_c, s_b s_c).          (2)
```

After erasing every outside visit, the traversal encounters the `e`, `f`, and
`g` two-crossing blocks in that order.  Hence direct reading of the six-letter
word gives

```text
edge(a,b) is present iff q_e=-1,
edge(a,c) is present iff q_f=+1,
edge(b,c) is present iff q_g=-1.                 (3)
```

Changing chamber changes the sign of `Delta`, so (2) negates all three `q`'s;
(3) therefore toggles exactly the three local graph edges, consistently with
R-LOC.

The local graph is extreme exactly when all three indicators in (3) agree.
That requires `(q_e,q_f,q_g)` to be `(-,+,-)` or `(+,-,+)`.  Dividing the
first and third entries of (2) by the middle one shows this is equivalent to

```text
s_a=s_c=-s_b,
```

namely one of the two alternating sign triples.  Therefore the generic orbit
is exactly the other six, nonalternating triples.  This is an algebraic
classification, not the measured census.

## Which pair is selected

For a pair of local crossings sharing a strand `u`, call `u` separating when
the other two oriented strand directions lie on opposite sides of `u`.  In the
fixed labels this says

```text
pair ab selected-condition: s_a=-s_b,
pair ac selected-condition: s_a= s_c,
pair bc selected-condition: s_b=-s_c.            (4)
```

For each nonalternating sign triple exactly one condition in (4) holds.  Using
(2)--(3), the `P3` graph on either chamber has as its degree-two vertex the
crossing complementary to that pair.  Thus the unique separating-strand pair
is precisely the graph-selected pair.  The six cases, with the other two pairs
listed as nonselected, are

| `(s_a,s_b,s_c)` | selected pair | nonselected pairs |
|---|---|---|
| `+++` or `---` | `ac` | `ab,bc` |
| `++-` or `--+` | `bc` | `ab,ac` |
| `+--` or `-++` | `ab` | `ac,bc` |

This table is just (4); no symmetry of the exterior gaps is assumed.

## The mixed carrier

Take either nonselected pair and let `u` be its shared strand, with the other
strand directions `v,w`.  Failure of the corresponding selected-condition in
(4) is exactly

```text
sgn det(u,v) = sgn det(u,w).                      (5)
```

R-LOC says that the two triangle-crossing visits on each bundle edge are
adjacent among all crossing-visits of the traversal circle.  Hence the open
`u`-strand arc between the two visits contains no outside crossing visit.
Smoothing `Q` acts only at outside crossing visits, so it cannot cut or rewire
this arc.  Smoothing the two local crossings attaches one end of the intact arc
to the incoming `v` branch and its other end to the outgoing `w` branch (or the
same description with the order reversed).  Consequently one carrier contains
the entire arc and both of its endpoint smoothing corners.  Exterior
reconnections may enlarge that carrier elsewhere but cannot separate these two
corners.

Traversing this carrier through the segment, one endpoint turns from `v` into
`u` and the other from `u` into `w` (or the same description with `v,w`
interchanged).  The two corner determinants are therefore

```text
det(v,u) = -det(u,v),  and  det(u,w).              (6)
```

By (5), the signs in (6) are opposite.  The carrier is mixed regardless of all
its other corners, so its weight is zero by `def:wind`.  The support's winding
selector, a product containing this weight, is zero.  Consequently its entire
X1 row is zero before any coefficient is read.

## Boundary of the result

The proof kills exactly the two generic nonselected pair rows.  It does not
kill the graph-selected generic pair: its shared strand is separating, so the
two local corner signs in (6) agree.  In the extreme orbit all three strands
are separating, so this argument kills none of the three pair rows; the
coefficient-zero subcases measured there still need their own proof.  The
generic selected `singleton/pair` coefficient identity and the extreme
`empty/full` identity also remain open.
