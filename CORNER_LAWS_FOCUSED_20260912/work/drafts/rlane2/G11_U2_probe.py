"""G11_U2_probe.py -- numeric check of the counterexample to the frozen leaf `G11_clear` (U2 report).

`G11_clear` has no `CarrierGeometry P` hypothesis in scope (the section variable `hG` is not mentioned
in its statement).  Take n = 8, P' = P, e = 0, f = 2, g = 4 and a fourth edge h = 6, all four edges
passing through the origin (a quadruple point; excluded by CarrierGeometry, allowed without it).
Checks: {e,f},{e,g},{f,g} are crossings (remote labels, closed segments meet); every same-edge
visit pair with union {e,f,g} has EQUAL parameters (so `t_v < t_w <-> t_w' < t_v'` holds with both
sides false, and all other pairs are carried trivially since P' = P): ExactTriangleVisitOrders holds;
the triangle conv{x_ef,x_eg,x_fg} is the single point {0}, whose frontier in R^2 is itself; the
foreign edge h contains 0.  Hence clause (i) of `G11_clear` fails for h = 6."""
import itertools
P = {0: (-1.0, 0.0), 1: (1.0, 0.0), 2: (0.0, 1.0), 3: (0.0, -1.0),
     4: (-1.0, -1.0), 5: (1.0, 1.0), 6: (1.0, -1.0), 7: (-1.0, 1.0)}
n = 8
def edge(i): a, b = P[i], P[(i + 1) % n]; return (b[0] - a[0], b[1] - a[1])
def det(u, v): return u[0] * v[1] - u[1] * v[0]
def adjacent(i, j): return (j - i) % n in (n - 1, 0, 1)
def seg_meet(i, j):
    """parameters (s,t) of the intersection of the lines of edges i, j if the closed segments meet"""
    a, b = P[i], P[j]; u, v = edge(i), edge(j); d = det(u, v)
    if abs(d) < 1e-12: return None
    w = (b[0] - a[0], b[1] - a[1]); s = det(w, v) / d; t = det(w, u) / d
    return (s, t) if -1e-12 <= s <= 1 + 1e-12 and -1e-12 <= t <= 1 + 1e-12 else None
crossings = {}
for i, j in itertools.combinations(range(n), 2):
    if not adjacent(i, j):
        m = seg_meet(i, j)
        if m is not None: crossings[(i, j)] = m
e, f, g, h = 0, 2, 4, 6
assert all(k in crossings for k in [(e, f), (e, g), (f, g)]), crossings
# visits on each edge: (crossing, parameter)
def param(c, i):
    s, t = crossings[c]; return s if c[0] == i else t
for i in range(n):
    vis = [(c, param(c, i)) for c in crossings if i in c]
    for (c1, t1), (c2, t2) in itertools.combinations(vis, 2):
        union = set(c1) | set(c2)
        if union == {e, f, g}:
            # P' = P: reversed clause requires  t1 < t2  <->  t2 < t1, i.e. t1 == t2
            assert abs(t1 - t2) < 1e-12, (i, c1, c2, t1, t2)
tri = [tuple(P[e][k] + param((e, f), e) * edge(e)[k] for k in range(2)),
       tuple(P[e][k] + param((e, g), e) * edge(e)[k] for k in range(2)),
       tuple(P[f][k] + param((f, g), f) * edge(f)[k] for k in range(2))]
assert all(abs(p[0]) < 1e-12 and abs(p[1]) < 1e-12 for p in tri), tri   # the triangle is {0}
# the foreign edge h = 6 passes through 0 = the whole frontier of the degenerate triangle
s = 0.5; pt = tuple(P[h][k] + s * edge(h)[k] for k in range(2))
assert abs(pt[0]) < 1e-12 and abs(pt[1]) < 1e-12
assert h not in (e, f, g) and all(not adjacent(h, x) for x in (e, f, g))
print("counterexample to the frozen G11_clear verified: n=8, e,f,g,h = 0,2,4,6, P' = P; "
      "triangle = {0}, edge 6 meets its frontier; crossings:", sorted(crossings))
