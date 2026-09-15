> COMPLETE: full def:deletion-halves and lem:children passed independent
> review after audit044. Final acceptance-map audit is045. Do not redo this
> plan; continue named-wall-definition-after-children.md.

# Next source claim: deletion/halves and lem:children

The full original cusp theorem is independently accepted after audit043. Do
not redo its local/arc/rotation work. Its complete evidence is tracked in STATUS.
The next source work is sm-1-polygons.tex:1227–1290, def:deletion-halves and
both clauses of lem:children. No literature input or author decision is needed.

## Reuse the completed deletion branch

SM.deleteVertex, deletionIndex, their injectivity/exhaustion and cyclic successor
lemmas already implement actual deletion. generic_deleteVertex and
flat_deletion_chamber prove the central Generic child and the nearby whole
interval chamber statement, including zero. Reuse these rather than reprove
lem:flat-sides. Keep every existing accepted proof file unchanged.

## Construct both actual halves

For ContactSeparated M a put d=(a-M).val. Prove 2 <= d <= n-3 from the four
excluded labels, ZMod.val_lt and exact residue identities. Thus the first
child has d+1 vertices and the second has n-d, both between3 and n-2. The
source's cyclic relabelling is used only for counting; keep original labels.

First vertex map: i maps to M+(i.val:ZMod n), for i:ZMod(d+1).
Second vertex map: 0 maps to M; every nonzero i:ZMod(n-d) maps to a+i.val.
Prove injectivity, exact ranges, first endpoints M/a, second endpoints M/M-1,
all internal successor identities and closing successor identities. The first
range excludes a+1; the second excludes a. Prove cyclic compatibility as needed
for source-permitted labelled child polygons, without arbitrary reorderings.

The first edge map to parent edges is M+i.val, including its final cut edge a.
The second edge map is a+i.val, including its initial cut edge a. Both maps
are injective because their sizes are strictly below n. All ordinary child
edges and edge interiors equal the mapped parent ones.

At the actual central contact M=A+lambda*(B-A), with0<lambda<1, the first
cut vector is lambda*d_a, and the second is(1-lambda)*d_a. Prove actual
edgePoint formulas: first parameter t maps to lambda*t; second parameter t
maps to lambda+(1-lambda)*t. For0<t<1 both parent parameters lie in(0,1).
Reuse AffineSegments/AffineSubdivision only where their exact direction and
domain match; neither half has an assumed abstract embedding or G2.

## Prove both Generic children and assemble

G1: any three distinct child labels map injectively to distinct parent labels.
If their determinant vanished, the parent's sole zero triple would be the
contact support {a,a+1,M}. The proved missing endpoint on each child makes
this impossible. Parent vertices are distinct by the reviewed singleton-zero
argument; no extra injectivity premise is needed.

G2: contact_g2 derives actual full parent G2 from source contact separation,
sole point-zero support and empty remote concurrence set. If three distinct
child edge interiors concur, the proved injective edge map and interior
inclusions create three distinct parent edge interiors at that same point.
This contradicts parent G2. No separate regular path or child transversality
assumption is allowed. contact_regular supplies the source parent Regular.

Assemble def:deletion-halves with exact inherited cyclic order and edges, then
lem:children with both flat deletion/chamber and V-half Generic/size/parent
Regular clauses. Obtain independent full statement/body review and a new
whole audit before accepting either original row. Partial halves never count.

Full def:walls remains pending: its K/newborn/empty side conventions can now
reuse the proved cusp theorem, but mutual exclusivity, centre classification
and all cyclic transports must also be completed. The separate original
lem:shift zero-turn obstruction remains local and does not affect this work.
