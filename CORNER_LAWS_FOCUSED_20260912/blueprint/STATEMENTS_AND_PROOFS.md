# Selected source statements and printed proofs

Read source context for unlabelled notation. Historical status tags are not acceptance.

## def:polygon — DEFINE

reference/SM/sm-1-polygons.tex:27–52

```tex
\begin{definition}[labelled tuples and polygons]\label{def:polygon}
Let $n\geq3$. A \emph{labelled tuple} is an element
$P=(\mu_1,\ldots,\mu_n)\in(\RR^2)^n$, indices in $\ZZ/n$ with $\mu_{n+1}=\mu_1$. The
\emph{cyclic shift} is $(\sigma P)_i=\mu_{i+1}$. A \emph{polygon} on $n$
vertices is an orbit $[P]=\{\sigma^kP:k\in\ZZ/n\}$ of labelled tuples; a
labelled tuple in the orbit is a \emph{representative}, and the space of
polygons is the quotient $(\RR^2)^n/(\ZZ/n)$. Every notion below is
introduced on a representative and is invariant under $\sigma$ (up to the
induced relabelling of indices, which is recorded where it matters); it
therefore defines a notion on polygons. A polygon has no distinguished vertex
and no distinguished edge; when a construction needs one (a root, a base
vertex), that choice is part of the construction's data.

For a representative, the \emph{edge vectors} are
\[
\lt_i=\mu_{i+1}-\mu_i\qquad(i\in\ZZ/n),
\]
so that $\sum_i\lt_i=0$, and the \emph{edge segments} are
$E_i=[\mu_i,\mu_{i+1}]=\{\mu_i+t\lt_i:0\leq t\leq1\}$. Vertex $i$ is
\emph{incident} to $E_{i-1}$ and $E_i$. Two edges $E_i,E_j$ are
\emph{adjacent} if $j-i\in\{-1,0,1\}$ and \emph{remote} otherwise; an edge
$E_j$ is \emph{remote to the vertex} $i$ if $j\notin\{i-1,i\}$, and
\emph{remote to the vertex and its two edges} if $j\notin\{i-2,i-1,i,i+1\}$.
No condition is imposed on the tuple by this definition; in particular
coincident vertices and zero edges are allowed at this level.
\end{definition}
```

## def:chirotope — DEFINE

reference/SM/sm-1-polygons.tex:63–70

```tex
\begin{definition}[chirotope and turns]\label{def:chirotope}
For $i,j,k\in\ZZ/n$ put
\[
\chi_{ijk}(P)=\sgn\det(\mu_j-\mu_i,\ \mu_k-\mu_i)\in\{-1,0,1\}.
\]
The \emph{turn} at vertex $i$ is $\tau_i(P)=\chi_{i-1,i,i+1}(P)$. The number
of \emph{left turns} is $\ell(P)=\#\{i:\tau_i(P)=1\}$.
\end{definition}
```

## lem:chi-basic — PROVE

reference/SM/sm-1-polygons.tex:72–87

```tex
\begin{lemma}[elementary properties of $\chi$]\label{lem:chi-basic}
For all $i,j,k$:
\begin{enumerate}
\item[(i)] $\chi_{ijk}$ is alternating: it changes sign under a transposition
of two of its indices and is unchanged under a cyclic permutation; it is $0$
when two indices coincide.
\item[(ii)] $\chi_{ijk}=\sgn\bigl([\mu_j-\mu_i,\ \mu_j-\mu_k]\bigr)$ with the
main text's bracket $[u,v]=u_2v_1-u_1v_2$.
\item[(iii)] $\chi_{i,i+1,k}=\sgn\det(\lt_i,\ \mu_k-\mu_i)$; when $\lt_i\neq0$
we say (a naming convention) that $\mu_k$ lies \emph{strictly to the left} of
the directed line through $E_i$ if this sign is $+1$ and \emph{strictly to the
right} if it is $-1$.
\item[(iv)] $\tau_i=\sgn\det(\lt_{i-1},\lt_i)$; $\tau_i=+1$ is a left turn.
\end{enumerate}
\status{proved (refereed: bench A 2026-09-12T06:44:52Z, bench B 2026-09-12T06:57:24Z; SM1-carried, read on SM12, repaired in round 12 (F-25-194), re-read on SM13)}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:88–96

```tex
\begin{proof}
(i) $\det$ is alternating and $\det(\mu_j-\mu_i,\mu_k-\mu_i)$ is the standard
area form of the ordered triple; a cyclic permutation of the triple is even.
(ii) $[\mu_j-\mu_i,\mu_j-\mu_k]=-\det(\mu_j-\mu_i,\mu_j-\mu_k)
=\det(\mu_j-\mu_i,\mu_k-\mu_j)=\det(\mu_j-\mu_i,\mu_k-\mu_i)$, the last step
by $\det(u,v-u)=\det(u,v)$. (iii) is the case $j=i+1$ of the definition.
(iv) $\det(\mu_i-\mu_{i-1},\mu_{i+1}-\mu_{i-1})=\det(\lt_{i-1},\lt_{i-1}+\lt_i)
=\det(\lt_{i-1},\lt_i)$.
\end{proof}
```

## def:generic — DEFINE

reference/SM/sm-1-polygons.tex:100–108

```tex
\begin{definition}[generic polygon]\label{def:generic}
A polygon $P$ is \emph{generic} if
\begin{enumerate}
\item[(G1)] $\chi_{ijk}(P)\neq0$ for all pairwise distinct $i,j,k\in\ZZ/n$;
\item[(G2)] there is no point of $\RR^2$ lying in the relative interiors of
three distinct edge segments.
\end{enumerate}
The set of generic polygons on $n$ vertices is $\mathcal U_n\subseteq(\RR^2)^n$.
\end{definition}
```

## lem:g1 — PROVE

reference/SM/sm-1-polygons.tex:110–125

```tex
\begin{lemma}[what (G1) gives]\label{lem:g1}
Let $P$ satisfy (G1). Then:
\begin{enumerate}
\item[(i)] all vertices are distinct and every edge vector is nonzero;
\item[(ii)] every turn $\tau_i$ is $\pm1$; consecutive edge vectors are
linearly independent, so no edge vector is a positive or negative multiple
(``flat'' or ``kink'') of its predecessor;
\item[(iii)] no vertex lies on the line spanned by an edge not incident to it;
in particular no vertex lies on a non-incident closed edge segment;
\item[(iv)] two distinct adjacent edges meet exactly in their common vertex;
\item[(v)] two remote edges are either disjoint or meet in exactly one point,
which lies in the relative interior of both and at which the two edge
directions are linearly independent.
\end{enumerate}
\status{proved (refereed: bench A 2026-09-12T06:44:52Z, bench B 2026-09-12T06:57:24Z; SM1-carried, read on SM12, repaired in round 12 (F-25-190, F-25-195), re-read on SM13)}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:126–136

```tex
\begin{proof}
(i) If $\mu_i=\mu_j$ with $i\neq j$, then $\chi_{ijk}=0$ for any third index
$k$ (there is one since $n\geq3$). (ii) $\tau_i=\sgn\det(\lt_{i-1},\lt_i)\neq0$.
(iii) If $\mu_k$ lies on the line through $\mu_i,\mu_{i+1}$ with
$k\notin\{i,i+1\}$ then $\chi_{i,i+1,k}=0$. (iv) By (ii) the two edges at a
vertex span the plane, so their lines meet only at the vertex. (v) Let
$E_i,E_j$ be remote and $x\in E_i\cap E_j$. By (iii) $x$ is not an endpoint
of either. If $\lt_i,\lt_j$ were parallel, the two segments would lie on one
line, and then an endpoint of one would lie on the line of the other, contrary
to (iii). Two segments on non-parallel lines meet in at most one point.
\end{proof}
```

## def:crossings — DEFINE

reference/SM/sm-1-polygons.tex:138–146

```tex
\begin{definition}[crossings]\label{def:crossings}
Let $P$ satisfy (G1). The \emph{crossing set} $X(P)$ is the set of unordered
pairs $\{i,j\}$ of remote edge indices with $E_i\cap E_j\neq\varnothing$. For
$\{i,j\}\in X(P)$ the \emph{crossing point} $x_{ij}$ is the unique point of
$E_i\cap E_j$, and its \emph{parameters} $t_{ij}\in(0,1)$ on $E_i$ and
$t_{ji}\in(0,1)$ on $E_j$ are defined by $x_{ij}=\mu_i+t_{ij}\lt_i
=\mu_j+t_{ji}\lt_j$. The \emph{crossing sign} of $\{i,j\}$ read from $E_i$ is
$\sgn\det(\lt_i,\lt_j)$.
\end{definition}
```

## lem:crossing-test — PROVE

reference/SM/sm-1-polygons.tex:148–157

```tex
\begin{lemma}[crossings through the chirotope]\label{lem:crossing-test}
Let $P$ satisfy (G1) and let $E_i,E_j$ be remote. Then $\{i,j\}\in X(P)$ if
and only if
\[
\chi_{i,i+1,j}\,\chi_{i,i+1,j+1}=-1\quad\text{and}\quad
\chi_{j,j+1,i}\,\chi_{j,j+1,i+1}=-1.
\]
If $P$ is generic, distinct crossings have distinct crossing points, and
$X(P)$ is finite. \status{proved (refereed: bench A 2026-09-12T06:44:52Z, bench B 2026-09-12T06:57:24Z; SM1-carried, read on SM12, repaired in round 12 (F-25-196), re-read on SM13)}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:158–176

```tex
\begin{proof}
By Lemma~\ref{lem:g1}(i),(iii) the edge vectors $\lt_i,\lt_j$ are nonzero and
none of the four endpoints of $E_i,E_j$ lies on the line of the other segment,
so the four chirotope entries in the display are $\pm1$. Separation
criterion: along $E_j$ the signed distance from the line of $E_i$,
$f(t)=\det(\lt_i,\ \mu_j+t\lt_j-\mu_i)$, is affine in $t$ with
$f(0),f(1)\neq0$, so $E_j$ meets the line of $E_i$ exactly when
$f(0)f(1)<0$, that is, when $\chi_{i,i+1,j}\,\chi_{i,i+1,j+1}=-1$
(Lemma~\ref{lem:chi-basic}(iii)); then $f$ has nonzero slope
$\det(\lt_i,\lt_j)$, the two lines meet in one point, and that point lies in
the relative interior of $E_j$. Symmetrically, $E_i$ meets the line of $E_j$
exactly when the second condition holds. If both conditions hold, the common
point of the two lines lies in the relative interior of both segments, so
$E_i\cap E_j\neq\varnothing$; conversely, a point of $E_i\cap E_j$ is a point
of $E_j$ on the line of $E_i$ and a point of $E_i$ on the line of $E_j$, so
both conditions hold. If two distinct crossings had the same point, that
point would lie in the relative interior of three distinct edges (the two
crossings share at most one edge), contrary to (G2). Finiteness is clear.
\end{proof}
```

## lem:wall-segment-stability — PROVE

reference/SM/sm-1-polygons.tex:178–188

```tex
\begin{lemma}[stability of separated segment intersections]
\label{lem:wall-segment-stability}
Consider finitely many continuously varying nonzero oriented segments.
For a specified pair, suppose that at the centre the segments are either
disjoint or meet transversely in both relative interiors. In the first case
they stay disjoint nearby. In the second case their unique intersection
persists, remains transverse and interior, and its two parameters vary
continuously. For finitely many such persistent crossings on a segment,
every pair with distinct central parameters keeps its parameter order nearby.
\status{new (round~4: no frozen-source statement carries this lemma --- the former locator RC tr:five-events is the five-event classification and does not state it, and the persistence argument appears only inside proofs (CV lem:dictionary, clause~(b); RC guard:canonical); the round-1 proof printed here is self-contained; F-25-139; cleared by bench~A on SM4 (2026-09-05T23:49:15Z))}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:189–204

```tex
\begin{proof}
Disjoint compact segments have positive distance. Moving their endpoints by
at most $\eta$ moves every convex combination of the endpoints by at most
$\eta$, so a sufficiently small perturbation preserves their disjointness.
For the second case write the segments as $A+uD$ and $B+vH$, where
$0\leq u,v\leq1$. Solving $A+uD=B+vH$ by taking determinants gives
\begin{equation}\label{wallgeo:parameters}
 u=\frac{\det(B-A,H)}{\det(D,H)},\qquad
 v=\frac{\det(B-A,D)}{\det(D,H)}.
\end{equation}
The central denominator is nonzero. These quotients are therefore continuous
near the centre, and their central values in $(0,1)$ remain in that interval.
A nonzero continuous difference of two central parameters has constant sign
after shrinking. There are only finitely many requirements, so one common
interval satisfies all of them.
\end{proof}
```

## def:chamber — DEFINE

reference/SM/sm-1-polygons.tex:206–211

```tex
\begin{definition}[chambers]\label{def:chamber}
A \emph{chamber} is a connected component of the space of generic polygons
$\mathcal U_n/(\ZZ/n)$; its preimage in $\mathcal U_n$ is a union of at most
$n$ components of $\mathcal U_n$ permuted by $\sigma$, the \emph{labelled
chambers}.
\end{definition}
```

## prop:chambers — PROVE

reference/SM/sm-1-polygons.tex:213–219

```tex
\begin{proposition}[chambers]\label{prop:chambers}
$\mathcal U_n$ is open in $(\RR^2)^n$, and every chamber is open and path
connected. Along any path in $\mathcal U_n$ the following data are constant:
the chirotope $(\chi_{ijk})$; the crossing set $X(P)$; and, for every edge
$E_i$, the order of the parameters $t_{ij}$, $\{i,j\}\in X(P)$, along $E_i$.
\status{new (round~5: the two persistence clauses of the proof cited to Lemma~\ref{lem:wall-segment-stability}, F-25-143; the remainder is the SM1 proof, audited there)}
\end{proposition}
```

reference/SM/sm-1-polygons.tex:220–245

```tex
\begin{proof}
The finitely many determinants $\det(\mu_j-\mu_i,\mu_k-\mu_i)$ are continuous
and nonzero on $\mathcal U_n$, so (G1) is open. Condition (G2) is open as well:
if three edge interiors had a common point at a limit of polygons, the three
segments would meet in the limit; we argue directly. Fix $P\in\mathcal U_n$.
By Lemma~\ref{lem:g1}(v) each pair of remote edges is either disjoint or
meets transversally in one interior point; the first condition persists under
small perturbation, and in the second the crossing persists and varies
continuously (Lemma~\ref{lem:wall-segment-stability}).
The finitely many crossing points of $P$ are pairwise distinct
(Lemma~\ref{lem:crossing-test}), hence remain distinct nearby; a common point
of three edge interiors nearby would be a coincidence of two crossing points
(any two of the three edges are remote, since an adjacent pair meets only at
its vertex by Lemma~\ref{lem:g1}(iv), and a vertex on a remote edge is excluded
by (G1) nearby). So $\mathcal U_n$ is open. An open subset of $\RR^{2n}$ is
locally path connected, so its components are open and path connected.

Along a path in $\mathcal U_n$ each $\chi_{ijk}$ is a continuous nonzero
integer-valued function, hence constant. The crossing set is a function of the
chirotope (Lemma~\ref{lem:crossing-test}). Two crossings on a common edge $E_i$
change their order only if their parameters coincide at some time; at that
time the two crossing points coincide, which puts a common point in three edge
interiors, contrary to (G2) --- the two other edges are remote to $E_i$ and,
if they were adjacent to each other, their only common point is their shared
vertex, which cannot lie on $E_i$ by (G1).
\end{proof}
```

## def:gauss — DEFINE

reference/SM/sm-1-polygons.tex:249–257

```tex
\begin{definition}[traversal circle and Gauss word]\label{def:gauss}
Let $P$ be generic. The \emph{traversal circle} $\Gamma(P)$ is the set of
pairs $(i,t)$, $i\in\ZZ/n$, $t\in[0,1)$, with the cyclic order in which
$(i,t)<(i,t')$ for $t<t'$ and $(i,t)<(i+1,t')$ for all $t,t'$; the point of
the plane at $(i,t)$ is $\mu_i+t\lt_i$. Each crossing $\{i,j\}\in X(P)$ has
two \emph{visits} $(i,t_{ij})$ and $(j,t_{ji})$ on $\Gamma(P)$. The
\emph{Gauss word} of $P$ is the cyclic sequence of the $2|X(P)|$ visits in
the order of $\Gamma(P)$, each visit labelled by its crossing.
\end{definition}
```

## def:interlace — DEFINE

reference/SM/sm-1-polygons.tex:259–268

```tex
\begin{definition}[interlacement]\label{def:interlace}
Two distinct crossings $x,y\in X(P)$ \emph{interlace} if the four visits
$x_0,y_0,x_1,y_1$ occur in the cyclic order $x_0<y_0<x_1<y_1$ (up to rotation),
that is, exactly one visit of $y$ lies between the two visits of $x$. The
\emph{interlacement graph} $G_P$ has vertex set $X(P)$ and an edge between
each interlacing pair. $\Ind(G_P)$ denotes the set of independent subsets of
$X(P)$, including $\varnothing$; for $S\subseteq X(P)$ let $N(S)$ be the set of
crossings interlacing some element of $S$, and let
$U(S)=X(P)\setminus(S\cup N(S))$.
\end{definition}
```

## def:visible — DEFINE

reference/SM/sm-1-polygons.tex:270–276

```tex
\begin{definition}[visible signature]\label{def:visible}
The \emph{visible signature} of a generic $P$ is the triple
\[
\bigl((\tau_i)_{i\in\ZZ/n},\ X(P),\ \text{the Gauss word of }P\bigr).
\]
By Proposition~\ref{prop:chambers} it is constant on chambers.
\end{definition}
```

## def:weak — DEFINE

reference/SM/sm-1-polygons.tex:279–288

```tex
\begin{definition}[weakly generic polygons and the silent locus]\label{def:weak}
A polygon $P$ is \emph{weakly generic} if every edge vector is nonzero, every
turn $\tau_i$ is nonzero, no vertex lies on a non-incident closed edge
segment, any two remote edges meet in at most one point and there
transversally, and (G2) holds. This is the main text's ``generic''. Every
generic polygon is weakly generic; the \emph{silent locus} is
$\mathcal S_n=\mathcal W_n\setminus\mathcal U_n$, where $\mathcal W_n$ is the
set of weakly generic polygons. A \emph{visible chamber} is a connected
component of $\mathcal W_n$.
\end{definition}
```

## def:regular — DEFINE

reference/SM/sm-1-polygons.tex:386–396

```tex
\begin{definition}[regular locus and principal turns]\label{def:regular}
For a polygon $P$ and an index $i$ with $\lt_{i-1},\lt_i\neq0$ and $\lt_i$
not a negative real multiple of $\lt_{i-1}$, the \emph{principal turn}
$\vartheta_i(P)\in(-\pi,\pi)$ is the unique angle with
$\cos\vartheta_i=\langle\lt_{i-1},\lt_i\rangle/(|\lt_{i-1}||\lt_i|)$ and
$\sgn\vartheta_i=\sgn\det(\lt_{i-1},\lt_i)$. The \emph{regular locus}
$\mathcal R_n$ is the set of polygons with all $\lt_i\neq0$ and no $\lt_i$ a
negative multiple of $\lt_{i-1}$; equivalently, all principal turns exist.
Every generic polygon lies in $\mathcal R_n$ (Lemma~\ref{lem:g1}(ii)), and
$\vartheta_i(P)=0$ exactly when $\lt_i$ is a positive multiple of $\lt_{i-1}$.
\end{definition}
```

## def:shift — DEFINE

reference/SM/sm-1-polygons.tex:398–405

```tex
\begin{definition}[reversal]\label{def:shift}
For a representative $P=(\mu_1,\ldots,\mu_n)$ the \emph{reversal} is
$(\overline P)_i=\mu_{2-i}$ ($i\in\ZZ/n$), which fixes $\mu_1$ and reverses
the traversal. Reversal commutes with the shift up
to a shift, so it is defined on polygons; it is not a relabelling but a change
of orientation, and no law below is asserted to be invariant under it except
where stated. Write $\rho(P)=\overline P$ for this reversal map.
\end{definition}
```

## lem:rot — PROVE

reference/SM/sm-1-polygons.tex:407–421

```tex
\begin{lemma}[rotation number]\label{lem:rot}
For $P\in\mathcal R_n$ put $\rot(P)=\frac1{2\pi}\sum_{i\in\ZZ/n}\vartheta_i(P)$.
Then:
\begin{enumerate}
\item[(i)] $\rot(P)\in\ZZ$;
\item[(ii)] $\rot$ is constant along every continuous path in $\mathcal R_n$;
\item[(iii)] inserting a vertex in the relative interior of an edge does not
change $\rot$; reversing the traversal negates
it;
\item[(iv)] if $n=3$ then $\rot(P)=\tau_1(P)=\tau_2(P)=\tau_3(P)\in\{\pm1\}$
and in particular $\rot(P)\neq0$;
\item[(v)] $2|\rot(P)|<n$.
\end{enumerate}
\status{proved (refereed: bench A 2026-09-12T06:44:52Z, bench B 2026-09-12T06:57:24Z; SM1-carried, read on SM12, no text change, re-read on SM13)}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:422–438

```tex
\begin{proof}
Identify $\RR^2$ with $\mathbb C$ and put $q_i=\lt_i/|\lt_i|$. The defining
property of the principal turn is $q_i=e^{\mathrm i\vartheta_i}q_{i-1}$.
Multiplying around the cycle gives $\exp(\mathrm i\sum_i\vartheta_i)=1$, so
the sum is in $2\pi\ZZ$: (i). The principal turn is a continuous function of
$(\lt_{i-1},\lt_i)$ on the open set where both are nonzero and not
antiparallel, so $\rot$ is a continuous integer-valued function on
$\mathcal R_n$: (ii). Inserting a vertex on an edge adds one zero turn and
changes no other turn; reversal reverses the cyclic order of the pairs and
replaces each $(\lt_{i-1},\lt_i)$ by $(-\lt_i,-\lt_{i-1})$, negating every
principal turn: (iii). For (iv), all three turn determinants of a triangle
equal $\det(\mu_2-\mu_1,\mu_3-\mu_1)$, which is nonzero for $P\in\mathcal R_3$
(three collinear points with nonzero edges have a doubled-back consecutive
pair); so the three turns have one sign, their sum lies strictly between $0$
and $3\pi$ in absolute value, and is a multiple of $2\pi$. For (v),
$2\pi|\rot(P)|\leq\sum_i|\vartheta_i|<n\pi$.
\end{proof}
```

## lem:uniformrot — PROVE

reference/SM/sm-1-polygons.tex:440–449

```tex
\begin{lemma}[rotation of uniform and one-dissent polygons]\label{lem:uniformrot}
Let $P\in\mathcal R_n$ have all turns nonzero.
\begin{enumerate}
\item[(i)] If all turns are left, then $\rot(P)\geq1$; if all are right, then
$\rot(P)\leq-1$.
\item[(ii)] If exactly one turn is right and all others are left, then
$\rot(P)\geq1$; symmetrically with left and right exchanged, $\rot(P)\leq-1$.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV lem:uniformrot (mirror clauses by reversal, C033))}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:450–464

```tex
\begin{proof}
(i) All $\vartheta_i>0$ and there are at least three of them, so the sum is
positive and $\rot(P)$ is a positive integer. (ii) Let $\alpha\in(0,\pi)$ be
the magnitude of the right turn and $\Pi$ the sum of the left turns, so
$\Pi-\alpha=2\pi\rot(P)$. If $\rot(P)\leq0$ then $\Pi\leq\alpha<\pi$. Cut the
traversal after the right-turn vertex; the edge directions from there on are
obtained by successive positive turns summing to $\Pi<\pi$, so all edge
vectors lie in a closed angular sector of width $<\pi$, whose dual cone is
nonempty: there is $u$ with $\langle u,\lt_i\rangle>0$ for all $i$. Summing
contradicts $\sum_i\lt_i=0$.

Both negative cases follow by reversing the traversal: this exchanges left
and right turns and negates rotation by Lemma~\ref{lem:rot}(iii). Applying
the respective positive case to the reversed polygon proves each claim.
\end{proof}
```

## lem:shift — PROVE

reference/SM/sm-1-polygons.tex:496–515

```tex
\begin{lemma}[behaviour under shift and reversal]\label{lem:shift}
\begin{enumerate}
\item[(i)] The chirotope identities are
\[
 \chi_{ijk}(\sigma P)=\chi_{i+1,j+1,k+1}(P),\qquad
 \chi_{ijk}(\overline P)=\chi_{2-i,2-j,2-k}(P).
\]
The edge $E_i(\sigma P)$ is $E_{i+1}(P)$, and the edge
$E_i(\overline P)$ is $E_{1-i}(P)$ traversed backwards.
\item[(ii)] $\sigma$ and $\rho$ map $\mathcal U_n$ onto itself and map chambers
onto chambers; they preserve $X(P)$ up to relabelling of edges.
\item[(iii)] $\tau_i(\sigma P)=\tau_{i+1}(P)$ and $\tau_i(\overline P)=-\tau_{2-i}(P)$;
hence $\ell(\overline P)=n-\ell(P)-z(P)$, where $z(P)=\#\{i:\tau_i(P)=0\}$;
in particular $\ell(\overline P)=n-\ell(P)$ for $P\in\mathcal U_n$
(Lemma~\ref{lem:g1}(ii)).
\item[(iv)] for $P\in\mathcal R_n$: $\sigma P$ and $\overline P$ lie in
$\mathcal R_n$, $\rot(\sigma P)=\rot(P)$ and $\rot(\overline P)=-\rot(P)$.
\end{enumerate}
\status{proved (refereed: bench A 2026-09-12T06:44:52Z, bench B 2026-09-12T06:57:24Z; SM1-carried, read on SM12, repaired in round 12 (F-25-189, F-25-193), re-read on SM13)}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:516–537

```tex
\begin{proof}
(i) is the definition; for the reversal, $\det(\mu_{2-j}-\mu_{2-i},\mu_{2-k}-\mu_{2-i})$
is the determinant of the triple $(2-i,2-j,2-k)$ of $P$. (ii): (G1) and (G2) are
conditions on the set of vertices and edges, which are preserved; both maps are
linear homeomorphisms of $(\RR^2)^n$. (iii): $\tau_i(\overline P)=
\chi_{i-1,i,i+1}(\overline P)=\chi_{3-i,2-i,1-i}(P)=-\chi_{1-i,2-i,3-i}(P)
=-\tau_{2-i}(P)$ by Lemma~\ref{lem:chi-basic}(i). Since $i\mapsto2-i$ is a
bijection of $\ZZ/n$, the turn multiset of $\overline P$ is the negative of
that of $P$: the left turns of $\overline P$ are the right turns of $P$, of
which there are $n-\ell(P)-z(P)$; on $\mathcal U_n$ every turn is $\pm1$
(Lemma~\ref{lem:g1}(ii)), so $z(P)=0$ there.
(iv): $\sigma$ permutes the edge vectors cyclically,
$\lt_i(\sigma P)=\lt_{i+1}(P)$, and $\rho$ negates and reverses them,
$\lt_i(\overline P)=-\lt_{1-i}(P)$, so the consecutive pairs
$(\lt_{i-1},\lt_i)$ of $\sigma P$ are those of $P$ and the consecutive pairs
of $\overline P$ are the pairs $(-\lt_k,-\lt_{k-1})$ of $P$; the condition of
Definition~\ref{def:regular} (every edge vector nonzero, no $\lt_k$ a negative
multiple of $\lt_{k-1}$) is symmetric in the pair and invariant under
negation, so it is preserved and $\sigma P,\overline P\in\mathcal R_n$. The
identity for $\rho$ is then Lemma~\ref{lem:rot}(iii), and for $\sigma$ the
multiset of principal turns is unchanged.
\end{proof}
```

## def:admissible — DEFINE

reference/SM/sm-1-polygons.tex:539–545

```tex
\begin{definition}[admissible pairs]\label{def:admissible}
A pair $(n,r)\in\ZZ^2$ is \emph{admissible} if $n\geq3$, $2|r|<n$ and
$(n,r)\neq(3,0)$. It is \emph{minimal} if moreover $n=2|r|+1$ (for $r\neq0$)
or $(n,r)=(4,0)$. For an admissible pair the \emph{fibre} is
$\mathcal U_{n,r}=\{P\in\mathcal U_n:\rot(P)=r\}$; a vertex of a fibre is a
generic polygon, a point of the quotient.
\end{definition}
```

## lem:fibres — PROVE

reference/SM/sm-1-polygons.tex:547–556

```tex
\begin{lemma}[nonempty fibres]
\label{lem:fibres}
For integers $n,r$, a generic polygon with $n$ vertices and rotation $r$
exists exactly when $n\geq3$, $2|r|<n$, and $(n,r)\ne(3,0)$.
Here genericity means that every determinant of three distinct vertices
is nonzero and no three distinct edge interiors meet. Moreover, for $n\geq3$
the generic polygons are dense in $(\RR^2)^n$: every nonempty open set of
labelled $n$-tuples contains a generic polygon.
\status{proved (refereed: bench A, 2026-09-05T23:45:25Z and 2026-09-06T01:58:43Z; transcribed from CV thm:zeroanchor(A) (C003); round~4 scope note: CV(A) supplies existence for CV's genericity (every relevant member of CV's guarded list nonzero, which constrains only vertex triples containing a cyclically consecutive pair), strictly weaker than the genericity stated here from $n=6$ on (bench~A's witness $((0,0),\allowbreak(8,-11),\allowbreak(2,0),\allowbreak(5,-9),\allowbreak(-7,0),\allowbreak(6,-11))$); the all-triple construction $D_{ijk}$ printed in the proof is this document's own strengthening, refereed sound by bench~A (F-25-138); round~5: the density clause its proof establishes (every nonempty open subset of $(\RR^2)^n$, $n\geq3$, contains a generic polygon) exported in the statement, with one sentence of the proof pointing the avoidance argument at an arbitrary open set, F-25-146)}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:557–676

```tex
\begin{proof}
We use only Lemma~\ref{lem:rot}: rotation is
integer-valued and constant on paths in the regular locus; subdivision
preserves it; regular triangles have rotation $\pm1$; and a regular
$n$-gon satisfies $2|\operatorname{rot}|<n$. The regular locus consists
of polygons with nonzero edges and without antiparallel consecutive
directions. Thus the three stated conditions are necessary. We print
the existence argument, including its polynomial-avoidance step.

\emph{Regular seeds.}
First let $r>0$ and put $m=2r+1$, $\alpha=2\pi r/m$, and
$q=\exp(\mathrm i\alpha)$. Identify the plane with $\mathbb C$ and take
the ordered vertices $z_j=q^{j-1}$ for $1\leq j\leq m$.
The integers $r,m$ are coprime, since a common divisor would divide
$m-2r=1$. These vertices are therefore distinct. With cyclic indices,
the edge directions satisfy
\begin{equation}\label{fibpr:directions}
d_j=z_{j+1}-z_j=q^{j-1}(q-1).
\end{equation}
Here $q^m=1$, so this includes the closing edge, and $q\ne1$, so every
edge is nonzero. Successive directions satisfy $d_j=q d_{j-1}$, also
across the closing corner. Since $0<\alpha<\pi$, every principal turn
is exactly $\alpha$. The seed is regular, and its total turn is
\begin{equation}\label{fibpr:rotation}
\sum_{j=1}^{m}\vartheta_j=m\alpha=2\pi r.
\end{equation}
Consequently its rotation is $r$. For negative $r$, reverse the seed
constructed for $|r|$; reversal negates rotation and preserves regularity.
This construction uses no genericity or concurrency claim about a
regular star and does not refer to a later star definition.

For $r=0$, use the four ordered vertices
$(0,0),(2,2),(0,2),(2,0)$. Its four directions are
$(2,2),(-2,0),(2,-2),(-2,0)$, and its principal turns, starting at the
first vertex, are respectively
\begin{equation}\label{fibpr:bowtie}
-3\pi/4,\quad 3\pi/4,\quad 3\pi/4,\quad-3\pi/4.
\end{equation}
Their sum is zero and none is antiparallel. This is a regular seed of
rotation zero. In each case let $m$ be the number of seed vertices.
The stated admissibility conditions imply $n\geq m$.

\emph{Subdivision and a regular neighbourhood.}
Insert $n-m$ distinct interior subdivision points in traversal order
on any seed edge. All refined edge vectors are positive multiples of
the former vector; each new principal turn is zero and all old turns
are unchanged. The resulting $n$-gon $P_0$ is regular with rotation $r$.
The regular locus is open: nonzero vectors form an open set, and for
two nonzero vectors the condition that their unit directions sum to a
nonzero vector is open and excludes exactly antiparallel directions.
Choose an open ball $B$ about $P_0$ contained in this locus.
Every point of $B$ is connected to $P_0$ by a straight path in $B$,
so it has rotation $r$ by the preceding rotation-number lemma.

\emph{Explicit nonzero polynomials.}
All coordinates of all $n$ vertices may vary in $B$.
For every three distinct indices $i,j,k$, let
\begin{equation}\label{fibpr:triple}
D_{ijk}=\det(\mu_j-\mu_i,\mu_k-\mu_i).
\end{equation}
This polynomial is not identically zero: assign these three vertices
the coordinates $(0,0),(1,0),(0,1)$, respectively, obtaining value $1$.
The remaining coordinates can be arbitrary for this test.

For an edge from $(x_i,y_i)$ to $(x_{i+1},y_{i+1})$, define its
homogeneous line-coefficient row by
\begin{equation}\label{fibpr:line}
\ell_i=(y_i-y_{i+1},\ x_{i+1}-x_i,\
               x_i y_{i+1}-x_{i+1}y_i).
\end{equation}
Both endpoints satisfy $\ell_i\cdot(x,y,1)=0$ by direct substitution.
For each unordered triple of pairwise remote edges $i,j,k$, put
\begin{equation}\label{fibpr:concurrence}
H_{ijk}=\det\begin{pmatrix}\ell_i\\\ell_j\\\ell_k\end{pmatrix}.
\end{equation}
These three edges have six distinct endpoint indices. Hence we can
assign their ordered endpoint pairs independently as
$(0,0),(1,0)$; $(0,0),(0,1)$; and $(0,1),(1,1)$.
The rows in this assignment are $(0,1,0)$, $(-1,0,0)$, and $(0,1,-1)$;
their determinant is $-1$. Thus each $H_{ijk}$ is a nonzero polynomial.
Coinciding coordinates in this witness are harmless: it proves a
polynomial identity is nonzero on the full coordinate space, rather
than purporting to be a generic polygon or a point of $B$.

If the three supporting lines have a common finite point $(x,y)$,
their coefficient matrix annihilates the nonzero vector $(x,y,1)$.
Its determinant then vanishes. Thus $H_{ijk}\ne0$ excludes triple
interior concurrence for these three edges. It is a sufficient
condition; no converse is used.

\emph{Simultaneous avoidance in the small ball.}
Let $F$ be the finite product of all the polynomials $D_{ijk}$, taking
one order for each index triple, and all the polynomials $H_{ijk}$.
An empty family of edge triples contributes the factor $1$.
The polynomial ring over $\mathbb R$ has no zero divisors (the highest
nonzero monomials in lexicographic order multiply to a nonzero highest
monomial), so $F$ is nonzero.
For completeness, a nonzero real polynomial cannot vanish on a
nonempty open box. For one variable this follows from the finite root
bound. Induct on the number of variables, writing the polynomial as a
polynomial in the last variable with coefficient polynomials in the
others. If it vanishes on a box, fixing the other variables makes it
vanish on an interval; all its coefficients vanish at that fixed
choice. They therefore vanish on the lower-dimensional box, and the
inductive hypothesis makes every coefficient identically zero, a
contradiction. Every open ball contains an open box. Hence some
$P\in B$ has $F(P)\ne0$. The same avoidance applies to any nonempty open
subset of $(\RR^2)^n$ in place of $B$, since it too contains an open box;
with the genericity of such a $P$ shown next, this proves the density clause.

At this $P$, the nonvanishing of every $D_{ijk}$ gives (G1), in
particular nonzero edges and noncollinear consecutive vertices.
Adjacent edges can meet only at their common endpoint: their lines
are distinct and nonparallel because the consecutive-vertex
determinant is nonzero. A point in three edge interiors therefore
would require three pairwise remote edges. Its concurrence would
force the corresponding $H_{ijk}$ to vanish, contrary to $F(P)\ne0$.
This proves (G2). The polygon is generic and has rotation $r$ because
it lies in $B$. This proves sufficiency and the lemma.
\end{proof}
```

## def:germ — DEFINE

reference/SM/sm-1-polygons.tex:680–695

```tex
\begin{definition}[wall germ; sides]\label{def:germ}
A \emph{wall germ} is a continuous map $P\colon(-\varepsilon,\varepsilon)\to
(\RR^2)^n$ such that $P(t)\in\mathcal U_n$ for $t\neq0$ and $P(0)\notin
\mathcal U_n$. Its \emph{sides} $P_-$ and $P_+$ are the chambers containing
$P((-\varepsilon,0))$ and $P((0,\varepsilon))$; each of these two sets is
connected and generic, hence lies in one chamber. For a function $F$ that is
constant on chambers, $F(P_\pm)$ denotes its value on the respective side.
At the centre $P(0)$ put
\begin{align*}
Z_{\rm pt}&=\bigl\{\{i,j,k\}\text{ pairwise distinct}:\chi_{ijk}(P(0))=0\bigr\},\\
Z_{\rm c}&=\bigl\{\{e,f,g\}\text{ pairwise remote}:
\operatorname{relint}E_e\cap\operatorname{relint}E_f\cap\operatorname{relint}E_g\neq\varnothing\text{ at }t=0\bigr\}.
\end{align*}
A real function $\phi$ of the germ \emph{changes sign at $0$} if there is
$\delta>0$ with $\phi(P(t))\phi(P(-t))<0$ for $0<t<\delta$.
\end{definition}
```

## lem:triple-sides — PROVE

reference/SM/sm-1-polygons.tex:697–704

```tex
\begin{lemma}[sides of a triple wall]\label{lem:triple-sides}
Let a wall germ have $Z_{\rm pt}=\varnothing$ and
$Z_{\rm c}=\{\{e,f,g\}\}$. Then for small $t\neq0$ the three pairs
$\{e,f\},\{e,g\},\{f,g\}$ are crossings, their three crossing points
are distinct, and on each of $E_e,E_f,E_g$ its two crossings occupy adjacent
positions among the crossing visits on that edge.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RA R-LOC-2, stated there for a simple transversal event; the printed proof covers every germ with $Z_{\rm pt}=\varnothing$ and $Z_{\rm c}$ the single triple $\{e,f,g\}$ (C015; F-25-44))}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:705–734

```tex
\begin{proof}
At the centre (G1) holds. In particular all vertices and edges are nonzero,
adjacent edges meet only at their common endpoint, and no vertex lies on the
line of a nonincident edge. The specified common point $q$ lies in all three
relative interiors. Two of their directions cannot be parallel: their lines
would then coincide, forcing an endpoint of one remote edge onto the line
of the other, contrary to (G1). Thus all three central intersections are
transverse. Lemma~\ref{lem:wall-segment-stability} makes them persistent
interior crossings. On either punctured side (G2) makes the three points
distinct.

In fact every remote edge pair at the centre is either disjoint or a transverse
interior pair: endpoint incidence or overlapping collinear remote edges would
contradict (G1). Thus the same stability lemma applies to all remote pairs and
gives a fixed finite crossing set with continuous parameters near the centre.

Suppose, contrary to the required adjacency on $E_e$, that for a sequence
$t_\nu\to0$ another crossing lies between $x_{ef}$ and $x_{eg}$ on $E_e$.
There are finitely many crossing labels, so after taking a subsequence this
crossing has one fixed other edge $h\notin\{e,f,g\}$. The two bounding
parameters converge to the parameter of $q$; the intervening parameter must
have the same limit. Continuity of its intersection parameters puts $q$ in
the relative interiors of $E_e$ and $E_h$. It is also interior to $E_f$.
The edges $E_h,E_f$ cannot be adjacent: under (G1) adjacent edges meet only
at their shared endpoint, whereas $q$ is interior to both. Hence $e,f,h$
are pairwise remote and define an element of $Z_{\rm c}$ distinct from
$\{e,f,g\}$, a contradiction. The same argument on $E_f$ and $E_g$ proves
all three adjacency assertions on one common punctured interval. No sign-change
hypothesis was used for this lemma.
\end{proof}
```

## def:walls — DEFINE

reference/SM/sm-1-polygons.tex:737–776

```tex
\begin{definition}[the named walls]\label{def:walls}
A wall germ is \emph{simple of one of the following types}; the types are
mutually exclusive.
\begin{enumerate}
\item[(F)] \emph{Flat at $j$} ($n\geq4$): $Z_{\rm pt}=\{\{j-1,j,j+1\}\}$,
$Z_{\rm c}=\varnothing$, $\mu_j(0)$ lies strictly between $\mu_{j-1}(0)$ and
$\mu_{j+1}(0)$, and $\tau_j$ changes sign at $0$. The \emph{right side} is the
side with $\tau_j=-1$ and the \emph{left side} the one with $\tau_j=+1$.
\item[(K)] \emph{Cusp at $j$} ($n\geq4$): $Z_{\rm pt}=\{\{j-1,j,j+1\}\}$,
$Z_{\rm c}=\varnothing$, the three points $\mu_{j-1}(0),\mu_j(0),\mu_{j+1}(0)$
are collinear with $\mu_j(0)$ outside the closed segment
$[\mu_{j-1}(0),\mu_{j+1}(0)]$, and $\tau_j$ changes sign at $0$. The
\emph{newborn pair} is $\{j-1,j+1\}$ if $\mu_{j+1}(0)$ lies between
$\mu_{j-1}(0)$ and $\mu_j(0)$, and $\{j-2,j\}$ if $\mu_{j-1}(0)$ lies between
$\mu_j(0)$ and $\mu_{j+1}(0)$. The \emph{loop side} $P_{\rm loop}$ is the side
on which the newborn pair is a crossing and the \emph{no-loop side}
$P_{\rm no}$ the other. The cusp is
\emph{empty} if on the loop side the two visits of the newborn crossing are
cyclically adjacent in the Gauss word.
\item[(V)] \emph{Vertex--edge at $(M;a)$}: $M\notin\{a-1,a,a+1,a+2\}$,
$Z_{\rm pt}=\{\{a,a+1,M\}\}$, $Z_{\rm c}=\varnothing$, $\mu_M(0)$ lies in the
relative interior of $E_a(0)$, and $\chi_{a,a+1,M}$ changes sign at $0$. The
germ is of \emph{bigon} type if $\chi_{a,a+1,M-1}(P(0))=\chi_{a,a+1,M+1}(P(0))$
and of \emph{sliding} type otherwise. The \emph{contact sign} is
$s=\chi_{a,a+1,M}(P_-)$.
\item[(T)] \emph{Triple at $\{e,f,g\}$}: $Z_{\rm pt}=\varnothing$,
$Z_{\rm c}=\{\{e,f,g\}\}$, and on each of the three edges the two crossing
parameters of the other two edges (which exist on both sides by
Lemma~\ref{lem:triple-sides}) have a difference that changes sign at $0$.
\item[(E)] \emph{Exterior extension at $(M;a)$}: $M\notin\{a-1,a,a+1,a+2\}$,
$Z_{\rm pt}=\{\{a,a+1,M\}\}$, $Z_{\rm c}=\varnothing$, $\mu_M(0)$ lies on the
line of $E_a(0)$ outside the closed segment $E_a(0)$, and $\chi_{a,a+1,M}$
changes sign at $0$.
\item[(C)] \emph{Pure cut at $\{i,j,k\}$}: no two of $i,j,k$ are consecutive
modulo $n$, $Z_{\rm pt}=\{\{i,j,k\}\}$, $Z_{\rm c}=\varnothing$, and
$\chi_{ijk}$ changes sign at $0$.
\end{enumerate}
The walls (E) and (C) are called \emph{silent}. The type is determined by the
centre; the sign-change conditions exclude tangential germs.
\end{definition}
```

## lem:flat-sides — PROVE

reference/SM/sm-1-polygons.tex:778–822

```tex
\begin{lemma}[flat-side geometry]\label{lem:flat-sides}
Let $n\geq4$ and let $P(t)=(\mu_1(t),\ldots,\mu_n(t))$ be continuous for
$|t|<\varepsilon$. Indices are cyclic modulo $n$; put
$E_i=[\mu_i,\mu_{i+1}]$ and $d_i=\mu_{i+1}-\mu_i$.
For $t\ne0$ assume that no three distinct vertices are collinear and no
three edge interiors concur. At $t=0$ suppose that the only collinear
triple is $\{j-1,j,j+1\}$, that no three pairwise remote edge interiors
concur, and that $\mu_j$ is strictly between $\mu_{j-1}$ and
$\mu_{j+1}$. Suppose also that
$\tau_j(t)=\operatorname{sgn}\det(d_{j-1}(t),d_j(t))$ changes sign at zero.
At a transverse crossing of $E_e,E_f$, the \emph{positive over/under
data} mean that $E_e$ is over $E_f$ exactly when $\det(d_e,d_f)>0$.
Then, after shrinking the interval:
\begin{enumerate}
\item[(i)] The central polygon has nonzero edges and no antiparallel
consecutive directions. Its only zero turn is at $j$, where the two
directions are positive multiples. Every other point-triple determinant
has constant nonzero sign on the whole interval.
\item[(ii)] The set of remote edge pairs that cross is constant,
including at zero. Each crossing is interior and transverse, no crossing
is a vertex, all crossing points are distinct, and the crossing visits
have constant order on every edge. Hence their cyclic Gauss word,
pairing, interlacement graph, and positive over/under data are constant.
Here the central crossing data are read from the segments of $P(0)$
exactly as for a generic polygon: a crossing is a transverse intersection
of the relative interiors of two remote edge segments, its two visits are
ordered along each edge by the intersection parameters, and the Gauss
word, pairing, interlacement graph and positive over/under data are formed
from these visits as in Definitions~\ref{def:crossings}, \ref{def:gauss}
and~\ref{def:interlace}; no function on the generic locus is evaluated at
the flat centre.
\item[(iii)] The deletion $Q=P(0)\setminus j$ is generic. The directions
$u=d_{j-1}(0)$ and $v=d_j(0)$ fuse to $w=\mu_{j+1}(0)-\mu_{j-1}(0)$,
and there is $0<\lambda<1$ with
\begin{equation}\label{flatpr:fusion}
u=\lambda w,\qquad v=(1-\lambda)w.
\end{equation}
Replacing either incident edge in a crossing label by the fused edge
gives a bijection with the crossings of $Q$, preserving their cyclic
visit order, pairing, determinant signs, and positive over/under data.
The deletions $P(t)\setminus j$ are generic on a smaller interval and
lie in the chamber of $Q$.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T23:45:25Z and 2026-09-06T04:22:56Z; transcribed from CV lem:flatdata --- (i),(ii) from its clauses (i),(ii); (iii) from its clause (ii) (the deletion is generic and carries the same data under the fused-edge identification) together with the fused-segment paragraph of its proof (the incident directions are positive multiples of the fused direction) and, for the nearby deletions lying in the chamber of the central one, CV thm:main(A)(i) (d9\_induction; stated there for CV's simple flat events under its guarded genericity, whereas this lemma asserts it under the all-triple genericity of its hypothesis, the printed proof carrying the wider scope; bench B, P-25-37/38, F-25-177) (P-25-3, C007); round~4: the flat-centre crossing data defined in clause~(ii), F-25-140; the proof's ``positive lift'' phrase replaced by the statement's positive over/under data, F-25-112)}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:824–921

```tex
\begin{proof}
Write $A=\mu_{j-1}(0)$, $M=\mu_j(0)$ and $B=\mu_{j+1}(0)$.
All central vertices are distinct: if two coincided, adjoining each
of two further indices would produce two distinct collinear triples;
there are two further indices because $n\geq4$. This contradicts the
unique-triple assumption. Thus all edges are nonzero. Every turn other
than the one at $j$ uses a different triple, so its determinant is
nonzero. Strict betweenness gives $M=A+\lambda(B-A)$ for exactly one
$\lambda\in(0,1)$, proving \eqref{flatpr:fusion}. In particular the
turn at $j$ is positive-flat, not antiparallel. Continuity and the
finitely many nonzero central determinants give (i).

\emph{No vertex contact at the centre.}
A vertex on the line of an edge not incident to it would give a
collinear triple. The sole permitted triple can occur in this way only
as $B$ on the line of $[A,M]$ or $A$ on the line of $[M,B]$.
Strict betweenness puts each such point outside the corresponding
closed segment. Thus no vertex lies on a nonincident closed segment.
Two adjacent edges other than the flat pair have nonparallel directions,
and meet only at their common endpoint. The flat pair consists of the
successive subsegments $[A,M]$ and $[M,B]$, also meeting only at their
common endpoint. Hence no adjacent edge interiors meet.

\emph{Crossing pairs.}
For a remote pair whose four endpoint-against-line triples avoid
$\{j-1,j,j+1\}$, those determinants have nonzero limits and constant
signs. Two segments with all endpoints off the other segment's line
cross if and only if each line separates the other segment's two
endpoints. This is the pair of strict opposite-sign tests. To see
sufficiency, intersect the two lines: opposite endpoint signs place
their unique intersection inside each segment. Necessity follows by
restricting the affine signed line equation to the other segment.
The tests therefore give the same crossing answer at zero and on both
sides. An actual intersection cannot be parallel: parallel intersecting
lines would coincide, forcing an endpoint determinant to vanish.

The only remote pairs whose tests can use the critical triple are
$\{j-2,j\}$ and $\{j-1,j+1\}$. The line of $E_{j-2}(0)$ meets the
flat line only at $A$; its other endpoint is off that line by the
unique-triple assumption. Since $A\notin[M,B]$, the compact segments
$E_{j-2}(0)$ and $E_j(0)$ are disjoint. Similarly the line of
$E_{j+1}(0)$ meets the flat line only at $B\notin[A,M]$, so
$E_{j-1}(0)$ and $E_{j+1}(0)$ are disjoint. Positive distances between
these compact segment pairs persist under small changes of their
endpoints. These pairs remain noncrossing on both sides. This covers
all remote pairs, including when $n=4$.

\emph{Order and crossing records.}
Each crossing at zero has two nonparallel directions. Solving its
two-by-two line-intersection system therefore gives continuous crossing
parameters, strictly between zero and one at zero. There are finitely
many pairs, so all these strict inequalities persist on one interval.
If two distinct central crossings had the same point, at least three
edge interiors would contain that point. None of those edges could be
adjacent, by the preceding paragraph. This would be a forbidden
concurrence of three pairwise remote edges. Thus crossing points are
distinct. In particular, on a fixed edge all crossing parameters are
distinct. The finitely many nonzero parameter differences retain their
signs by continuity; crossing visits neither collide nor reorder.
The Gauss word is just these edgewise lists concatenated in traversal
order. Pairing is indexed by the fixed edge pairs, and interlacement is
read from that word. For each actual crossing, the nonzero direction
determinant keeps its sign. The same physical strand therefore remains
over in the positive over/under data of the statement. This proves (ii)
without a triple-wall lemma.

\emph{Deletion and fusion.}
The deletion's point triples are central parent triples avoiding $j$,
so they are all noncollinear. At zero the oriented segment $[A,B]$
is precisely the traversal of $[A,M]$ followed by $[M,B]$.
No crossing of a remote edge with this segment can occur at $M$:
that would put the parent vertex $M$ on a nonincident edge, already
excluded. Thus such a crossing lies in exactly one of the two open
subsegments and inherits its transverse direction and its pairing.
An edge remote from $[A,B]$ is remote from both old subsegments.
The reverse implication needs care only for the neighbours at $A,B$:
their possible opposite-subsegment pairs are exactly the two compact
disjoint pairs treated above. They create no discarded crossing.
One remote straight edge cannot meet both old subsegments, since it
meets their common line at most once. Hence the crossing-label map is
bijective.

If a crossing parameter on $[A,M]$ is $a$, its parameter on $[A,B]$
is $\lambda a$; if it is $b$ on $[M,B]$, its fused parameter is
$\lambda+(1-\lambda)b$. Thus the old first-edge visits precede the
old second-edge visits, in exactly their original orders. Equation
\eqref{flatpr:fusion} shows that every direction determinant involved
changes only by a positive factor, preserving signs and over/under
data. No triple of deletion edge interiors can concur: away from $M$
it would give three parent edge interiors at the same point; at $M$
it would put a remote parent edge through that parent vertex. Both
are excluded. This proves genericity and all stated crossing data for
$Q$. Finally, the finitely many strict noncollinearity, transverse
crossing, disjointness and crossing-order conditions used above also
prove openness of genericity near $Q$. By continuity, the connected
small path $P(t)\setminus j$ stays in that open generic neighbourhood
and hence in the chamber of $Q$. This proves (iii).
\end{proof}
```

## lem:wall-sides — PROVE

reference/SM/sm-1-polygons.tex:923–951

```tex
\begin{lemma}[the sides of the named walls]\label{lem:wall-sides}
Let the germ be simple of type (F), (V), (T), (E) or (C). Then
$P(0)\in\mathcal R_n$. After shrinking the interval, every chirotope outside
$Z_{\rm pt}$ is nonzero with constant sign. Every crossing not involved in
the stated local degeneration persists, and the order of any two persistent
visits with distinct central parameters is constant. Moreover:
\begin{enumerate}
\item[(F)] The crossing set and Gauss word are the same on both sides and
at the centre.
\item[(V)] In the bigon branch,
\[
 X(P_+)\mathbin\triangle X(P_-)=\{\{a,M-1\},\{a,M\}\},
\]
with both pairs crossing on one side and neither on the other. In the sliding
branch exactly one of these two pairs crosses on each side, and the two sides
exchange them. No other crossing is created or lost, and no order changes
outside the contact neighbourhood.
\item[(T)] The crossing set is the same on both sides. The only visit-order
changes are the exchanges of the two triangle crossings on each of
$E_e,E_f,E_g$.
\item[(E),(C)] The crossing set and Gauss word are the same on both sides
and at the centre.
\end{enumerate}
Here, when crossing data are mentioned at a nongeneric centre, they mean the
transverse intersections of the relative interiors of the actual segments and
their traversal order. This does not evaluate a function defined only on
generic polygons at that centre.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV lem:flatdata; CV lem:silence, its proof, for (E),(C); RC tr:five-events, gw:germs (S3/S4/S7/R3 only), flat:pure (C015; F-25-45))}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:952–1047

```tex
\begin{proof}
Case (F), including its central regularity and crossing data, is
Lemma~\ref{lem:flat-sides}. We prove the remaining cases directly
in the one-based tail convention $d_i=\mu_{i+1}-\mu_i$.

\emph{Central distinctness and regularity.}
The remoteness requirements give $n\geq5$ in (V),(E) and $n\geq6$ in (T),(C).
If two central vertices coincided, adjoining each of two further indices
would give two different zero point triples. This contradicts the permitted
zero set, which has at most one member. Thus all central vertices are distinct
and every edge is nonzero. A zero turn would give a consecutive zero triple.
There is no such triple in any of (V),(T),(E),(C): the point zero set is empty
in (T), has no adjacent pair in (C), and has just the adjacent pair $a,a+1$
in (V),(E), because $M\notin\{a-1,a,a+1,a+2\}$. Hence every central turn
in these cases is nonzero. In particular the centre has no kink and belongs
to $\mathcal R_n$. Each other point determinant is nonzero at zero and is
continuous; finitely many such determinants retain their signs nearby.

\emph{Which segment pairs can change.}
No remote pair can have collinear overlapping segments at the centre: its
four distinct endpoint indices on a line would give more than one zero
point triple. Apart from an endpoint incidence, a remote pair is therefore
either disjoint or a transverse interior pair, and
Lemma~\ref{lem:wall-segment-stability} applies. An endpoint incidence requires
a zero point triple containing the two endpoints of its base edge. In (C)
the only zero triple contains no adjacent pair, and in (T) there is no zero
triple, so these cases have no endpoint incidence. In (V),(E), the only
possible incidence is the specified vertex $M$ on the line of $E_a$.
The only possibly affected remote pairs are consequently
$\{a,M-1\}$ and $\{a,M\}$. All other pairs satisfy the stability lemma.

\emph{The two vertex--edge branches, with the finite-segment test.}
Write $A=\mu_a$, $B=\mu_{a+1}$, $D=B-A$, $M=\mu_M$, and take in turn
$U=\mu_{M-1}$ and $U=\mu_{M+1}$. Put
\begin{equation}\label{wallgeo:heights}
 h=\det(D,M-A),\qquad h_U=\det(D,U-A).
\end{equation}
At the centre $h=0$ and $h_U\ne0$: another zero $h_U$ would give a second
point triple, since both neighbour indices differ from $a,a+1,M$.
Shrink so $h_U$ and $h_U-h$ are nonzero. The intersection of the supporting
line of $E_a$ with the line $MU$ has the exact form
\begin{equation}\label{wallgeo:contact-foot}
 q_U=M+r_U(U-M),\qquad r_U=-\frac{h}{h_U-h}.
\end{equation}
Indeed its height is $h+r_U(h_U-h)=0$. When $h$ and $h_U$ have opposite
signs, $r_U=|h|/(|h|+|h_U|)$ lies strictly between zero and one. When their
signs agree, the height of every point in the relative interior of $MU$ has
that common sign, so there is no such intersection. In the first case
$r_U\to0$ and $q_U\to M(0)$. In case (V), $M(0)$ is strictly inside $E_a(0)$.
The parameter of $q_U$ on the line $AB$ therefore tends to a number in $(0,1)$
and remains in $(0,1)$ nearby. This supplies the second, finite-segment
condition, not merely the straddling of the supporting line. The crossing is
transverse since the two line directions have determinant $h_U-h\ne0$.

Consequently each contact pair crosses precisely when the sign of $h$ is
opposite to its neighbour sign. The two neighbour signs are equal in the
bigon branch, giving both crossings or neither. They are opposite in the
sliding branch, giving precisely one crossing on each side. By the defining
sign change of $h$, the asserted exchanges follow. The predecessor leg is
$E_{M-1}$ and the successor leg is $E_M$, so these are exactly the displayed
tail-indexed pairs.

\emph{Exterior extension.}
At the centre in (E), each contact leg meets the supporting line of $E_a$
only at $M(0)$, because $h_U(0)\ne0$. That point is outside the closed
segment $E_a(0)$. Thus each contact leg is compact-disjoint from $E_a(0)$,
and both pairs remain disjoint by Lemma~\ref{lem:wall-segment-stability}.
All remote crossing pairs are therefore constant, including at the centre,
in (E), as they already are in (C) and (T).

\emph{Orders and localization.}
Consider two persistent crossings on a common edge whose central parameters
coincide. The other two edges then meet that base edge at the same point.
If those other edges are remote, their common interior point gives a member
of $Z_{\rm c}$. If they are adjacent, their nonzero central turn implies that
their lines meet only at their shared vertex. The coincidence would put that
vertex on the base edge. In (E),(C) no such endpoint incidence exists; in
(T) none exists either, and its only concurrence is the named triple.
It follows that all parameters in (E),(C) are centrally distinct and their
orders are constant. Their fixed edge order then gives a fixed cyclic Gauss
word, including at zero. In (T) the only possible ties are the two triangle
visits on a bundle edge. Lemma~\ref{lem:triple-sides} makes each such pair
adjacent. Their differences change sign by the definition of (T), so they
exchange order, and every other order is fixed by the stability lemma.

For (V), no persistent crossing has central point $M(0)$: any additional
edge through that point would give a second endpoint-incidence triple.
All persistent crossing parameters on $E_a$ are therefore separated from its
contact parameter. Those on either incident leg are separated from its
endpoint at $M$. Formula~\eqref{wallgeo:contact-foot} puts any newborn contact
crossings arbitrarily close to those contact parameters. Finiteness gives
neighbourhoods free of other crossings. Every other pair of persistent visits
has distinct central parameters, since a tie would give either a forbidden
triple concurrence or an additional vertex incidence. Their orders remain
fixed. This proves the claimed localization and completes all cases.
\end{proof}
```

## lem:cusp-sides — PROVE

reference/SM/sm-1-polygons.tex:1051–1099

```tex
\begin{lemma}[sides of a cusp]\label{lem:cusp-sides}
Let $n\geq4$ and let
$P(t)=(\mu_1(t),\ldots,\mu_n(t))$, $|t|<\varepsilon$, be continuous.
Indices are read modulo $n$, and
$E_i=[\mu_i,\mu_{i+1}]$,
$\widetilde\lambda_i=\mu_{i+1}-\mu_i$ and
$\tau_i=\operatorname{sgn}\det(\widetilde\lambda_{i-1},\widetilde\lambda_i)$.
Assume that $P(t)$ is generic for $t\ne0$: no three distinct vertices are
collinear and no three edge interiors concur. At $t=0$ assume that the only
collinear triple of distinct vertex indices is $\{j-1,j,j+1\}$, that no
three pairwise remote edge interiors concur, that $\mu_j$ lies outside the
closed segment $[\mu_{j-1},\mu_{j+1}]$, and that $\tau_j$ changes sign.
These are the simple-cusp hypotheses in the present conventions.

Use the following data, with the betweenness conditions imposed at $t=0$:
\begin{equation}\label{cusppr:data}
\begin{array}{c|c|c|c|c}
\text{case}&\text{middle point on the line}&(f,g)&(c_1,c_2)&\Delta(t)\\ \hline
\mathrm A&\mu_{j+1}\in(\mu_{j-1},\mu_j)&(j-1,j+1)&(j,j+1)&
 \det(\widetilde\lambda_{j-1},\widetilde\lambda_{j+1})\\
\mathrm B&\mu_{j-1}\in(\mu_j,\mu_{j+1})&(j-2,j)&(j-1,j)&
 \det(\widetilde\lambda_{j-2},\widetilde\lambda_j)
\end{array}
\end{equation}
Exactly one case applies. After shrinking the parameter interval:
\begin{enumerate}
\item[(i)] $\Delta$ is nonzero with constant sign. The remote pair
$\{f,g\}$ crosses precisely on the side with
$\tau_j=-\operatorname{sgn}\Delta$, called the loop side; it does not cross
on the side with $\tau_j=\operatorname{sgn}\Delta$, called the no-loop side.
No other crossing pair changes.
\item[(ii)] On the no-loop side the turns at $c_1,c_2$ have opposite signs.
On the loop side both have sign $\tau_j$.
\item[(iii)] On the loop side, one oriented traversal arc between the two
visits of the newborn crossing consists of a terminal portion of $E_f$,
the complete edge between $c_1$ and $c_2$, and an initial portion of $E_g$.
Its only polygon vertices are $\mu_{c_1},\mu_{c_2}$. This arc is allowed to
contain other crossing visits. If the two newborn visits are cyclically
adjacent in the Gauss word, this particular arc contains no other crossing
visit. In that case the complete edge between $c_1,c_2$ carries no crossing
on either side of the wall.
\item[(iv)] With rotation defined by the sum of principal turns,
\begin{equation}\label{cusppr:rotation-law}
\operatorname{rot}(P_{\rm loop})-\operatorname{rot}(P_{\rm no})
=\tau_j(P_{\rm loop})\in\{-1,1\}.
\end{equation}
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV lem:cuspcases; RC mt:s4 for the rotation clause, $\kappa=+\tau_j$ on the loop side (P-25-1, C004))}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:1101–1252

```tex
\begin{proof}
First, all vertex coordinates at the centre are distinct. If two coincided,
their triples with either of two further vertex indices would both be
collinear. Such further indices exist because $n\geq4$, contradicting the
sole-triple hypothesis. All edges at the centre are therefore nonzero.
Put $A=\mu_{j-1}$, $M=\mu_j$, $B=\mu_{j+1}$, and, as functions of $t$, put
\begin{equation}\label{cusppr:local-data}
u=M-A,\qquad v=B-M,\qquad T=\det(u,v).
\end{equation}
Thus $\tau_j=\operatorname{sgn}T$ on the punctured sides. The distinct
collinear points $A,M,B$ have a unique middle point; it is not $M$.
This proves the two-case assertion. On each punctured side every point-triple
determinant is nonzero, so its sign is constant by continuity.

\emph{The newborn crossing in case A.}
Let $w=\widetilde\lambda_{j+1}$, so that $E_g$ starts at $B$ and has
direction $w$. Here $\Delta=\det(u,w)$. If $\Delta(0)=0$, the nonzero
vector $w(0)$ would be parallel to the cusp line through $A,M,B$.
Its other endpoint $\mu_{j+2}(0)$ would lie on that line too. The indices
$j-1,j,j+2$ are distinct and give a second zero triple, a contradiction.
Therefore $\Delta(0)\ne0$; it has one nonzero sign on a smaller interval.

Write the intersection of the two supporting lines as $X=B+s w$.
Membership in the line through $E_f$ means $\det(u,X-A)=0$.
Since $B-A=u+v$, bilinearity gives, in separate steps,
\begin{equation}\label{cusppr:A-det}
\det(u,B-A)=\det(u,u)+\det(u,v)=T,
\end{equation}
\begin{equation}\label{cusppr:A-intersection}
0=\det(u,X-A)=T+s\Delta,
\qquad s=-\frac{T}{\Delta}.
\end{equation}
At $t=0$, $X=B$ lies strictly inside $E_f=[A,M]$ and $s=0$.
The line intersection varies continuously because $\Delta$ remains nonzero.
Consequently its parameter on $E_f$ remains strictly between $0$ and $1$,
and $|s|<1$ on a smaller interval. It lies in the interior of $E_g$ exactly
when $s>0$. Thus $E_f,E_g$ cross exactly when $T$ and $\Delta$ have
opposite signs. This also proves that the new crossing is interior and
transverse on the stated side.

\emph{The newborn crossing in case B.}
Let $h=\widetilde\lambda_{j-2}$, so that $E_f$ ends at $A$ and has
direction $h$. Here $\Delta=\det(h,v)$. If $\Delta(0)=0$, the other
endpoint $\mu_{j-2}(0)$ of $E_f$ would also lie on the cusp line, again
giving a second zero triple. Hence $\Delta$ is nonzero with constant sign
on a smaller interval. Write the intersection as $X=A-s h$, so $s>0$
means moving into $E_f$ from its endpoint $A$. The relevant determinant is
\begin{equation}\label{cusppr:B-det}
\det(v,A-M)=\det(v,-u)=-\det(v,u)=T.
\end{equation}
Because $\det(v,h)=-\Delta$, its line equation becomes
\begin{equation}\label{cusppr:B-intersection}
0=\det(v,X-M)=T-s\det(v,h)=T+s\Delta,
\qquad s=-\frac{T}{\Delta}.
\end{equation}
At $t=0$, $X=A$ is strictly inside $E_g=[M,B]$. Its parameter there
remains interior, and $|s|<1$ on a smaller interval. The two segments
therefore cross exactly when $s>0$, equivalently when $T$ and $\Delta$
have opposite signs. Since $T$ changes sign, the loop and no-loop sides
in both cases are distinct and have exactly the signs in (i).

\emph{No other crossing pair changes.}
For any remote pair, strict crossing is determined by the four signs of the
endpoint-against-line determinants: each segment must separate the endpoints
of the other. This criterion applies on both generic punctured sides.
If none of those four triples is $\{j-1,j,j+1\}$, all four signs have
the same nonzero limits and hence agree across the wall. Such a crossing
pair cannot change.

The only remote pairs whose tests can contain that triple are
$\{j-1,j+1\}$ and $\{j-2,j\}$. Indeed the only edges joining two critical
vertices are $[A,M]$ and $[M,B]$; adjoining the third critical vertex as an
endpoint of a remote edge gives precisely these two pairs. In case A,
the unused pair is $E_{j-2},E_j$. At the centre the supporting line of
$E_{j-2}$ meets the cusp line only at $A$, since its other endpoint is
off that line. But $A$ lies outside $[M,B]$, so the two compact segments
are disjoint and remain disjoint nearby. In case B the unused pair is
$E_{j-1},E_{j+1}$; the supporting line of $E_{j+1}$ meets the cusp line
only at $B$, which lies outside $[A,M]$. The same compact-disjointness
argument applies. This proves the last assertion of (i). It does not
assert that the order of thread crossings is unchanged.

\emph{The two needle turns.}
In case A there is $a>0$ with $v(0)=-a u(0)$, because $B$ lies strictly
between $A$ and $M$. The turn determinant at $B=\mu_{j+1}$ satisfies
\begin{equation}\label{cusppr:A-needle}
\det(v(0),w(0))=-a\det(u(0),w(0))=-a\Delta(0).
\end{equation}
It is nonzero and retains sign $-\operatorname{sgn}\Delta$ nearby.
The other needle corner is $M$, whose sign is $\tau_j$. By (i), these
signs are opposite on the no-loop side and equal on the loop side.
In case B there is $a>0$ with $u(0)=-a v(0)$. The turn determinant at
$A=\mu_{j-1}$ is therefore
\begin{equation}\label{cusppr:B-needle}
\det(h(0),u(0))=-a\det(h(0),v(0))=-a\Delta(0).
\end{equation}
It too retains sign $-\operatorname{sgn}\Delta$, while the other corner
is $M$. Applying (i) gives (ii) also in case B.

\emph{Threads and the empty condition.}
In case A, start at the newborn visit on $E_{j-1}$ and follow the
orientation. The traversal runs to $M$, along $E_j$ to $B$, and then
along $E_{j+1}$ to the other newborn visit. This is the arc in (iii).
In case B it runs from the newborn visit on $E_{j-2}$ to $A$, along
$E_{j-1}$ to $M$, and then along $E_j$ to the other visit.
Each description contains exactly the two specified polygon vertices.

No crossing other than the newborn can have both visits on this short
arc. The arc is contained in three consecutive edges. The two adjacent
pairs have no interior intersection because their incident directions
are linearly independent on a generic side. The remaining pair is the
newborn pair; its two nonparallel supporting lines meet only once, at
the newborn crossing itself. Thus any other crossing visit in the open
short arc has its partner in the complementary open arc.

If the newborn visits are cyclically adjacent in the Gauss word, at
least one of those two open arcs contains no crossing visit. A crossing
visit in the short arc would force a partner in the complementary arc,
so would make both nonempty. Hence the short arc is crossing-free.
In particular the complete edge between $c_1,c_2$ has no crossing on the
loop side. This middle edge belongs to neither member of the newborn
pair. By (i), every crossing pair involving it is unchanged, so it has
no crossing on the no-loop side either. This proves (iii) without
assuming that a general cusp is empty.

\emph{The rotation sign.}
Let $\vartheta_i(t)\in(-\pi,\pi)$ be the principal turn at vertex $i$
on a punctured side. The quotient of consecutive unit edge directions
is $\exp(\mathrm i\vartheta_i)$; multiplying around the polygon gives
$\exp(\mathrm i\sum_i\vartheta_i)=1$. Therefore
$\sum_i\vartheta_i$ is an integer multiple of $2\pi$, and
$\operatorname{rot}(P)=(2\pi)^{-1}\sum_i\vartheta_i$ is an integer.
Every principal turn is continuous away from an antiparallel pair of
incident edges. It follows that rotation is constant on each of the two
connected punctured sides.

At the centre, every turn determinant except that at $j$ is nonzero:
its three vertex indices would otherwise give a second collinear triple.
The corresponding principal turns therefore have the same limits from
the two sides. At $j$ the nonzero incident vectors are antiparallel.
The principal turn tends to $+\pi$ on the side with $T>0$ and to
$-\pi$ on the side with $T<0$. Set $s=\tau_j(P_{\rm loop})$.
Then the loop-side limit of $\vartheta_j$ is $s\pi$ and the no-loop-side
limit is $-s\pi$. Cancelling the common limits of all other turns gives
\begin{equation}\label{cusppr:rotation-limits}
2\pi\bigl(\operatorname{rot}(P_{\rm loop})-
                 \operatorname{rot}(P_{\rm no})\bigr)
=s\pi-(-s\pi)=2s\pi.
\end{equation}
Dividing by $2\pi$ proves (iv). No rotation is assigned to the singular
centre, and no differentiability or unthreadedness was used.
\end{proof}
```

## def:deletion-halves — DEFINE

reference/SM/sm-1-polygons.tex:1254–1267

```tex
\begin{definition}[deletion and halves]\label{def:deletion-halves}
For $n\geq4$ and $j\in\ZZ/n$, the \emph{deletion} $P\setminus j$ is the
$(n-1)$-tuple obtained by omitting $\mu_j$, with the induced cyclic order.
At a simple vertex--edge wall at $(M;a)$ with $b=a+1$, the \emph{halves} at
the centre $P^0=P(0)$ are the polygons
\[
\lambda_1=(\mu_M,\mu_{M+1},\ldots,\mu_a),\qquad
\lambda_2=(\mu_M,\mu_b,\mu_{b+1},\ldots,\mu_{M-1}),
\]
all vertices taken at $t=0$: $\lambda_1$ follows the edges $E_M,\ldots,E_{a-1}$
of $P^0$ and closes with the segment $[\mu_a,\mu_M]\subset E_a$; $\lambda_2$
opens with $[\mu_M,\mu_b]\subset E_a$, follows $E_b,\ldots,E_{M-2}$ and closes
with $E_{M-1}$.
\end{definition}
```

## lem:children — PROVE

reference/SM/sm-1-polygons.tex:1269–1279

```tex
\begin{lemma}[deletions and halves are generic]\label{lem:children}
\begin{enumerate}
\item[(i)] At a simple flat wall at $j$ with $n\geq4$, $P(0)\setminus j$
is generic, and for small $t\ne0$ the deletions $P(t)\setminus j$ lie in
the chamber of $P(0)\setminus j$.
\item[(ii)] At a simple vertex--edge wall at $(M;a)$, both halves of
Definition~\ref{def:deletion-halves} are generic and have between $3$ and
$n-2$ vertices. The central parent is automatically regular.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T18:22:57Z; transcribed from CV lem:flatdata(ii), thm:main(H); RC flat:s3, s7:halves (C015); the two locators use different index conventions --- CV one-based tail, identical to this document; RC zero-based head with a one-step shift, its vertex $r$ being vertex $r+1$ here and its incoming edge $e_r$ the edge $E_r$ (Section~\ref{sec:conventions}) --- and the deletion $P(0)\setminus j$ and the vertex counts of the halves are stated in this document's labels (F-25-104); round~5: clause (i)'s chamber conclusion is also CV thm:main(A)(i), stated there for CV's simple flat events under its guarded genericity (Convention conv:events), whereas this document asserts it for the simple flat wall of Definition~\ref{def:walls} under the all-triple genericity of Definition~\ref{def:generic} --- the printed proof (Lemma~\ref{lem:flat-sides}(iii) with the openness of the generic locus) carries the wider scope, F-25-104 (codex B-Q1-CHILD-AI))}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:1280–1314

```tex
\begin{proof}
Clause (i) is the deletion assertion in
Lemma~\ref{lem:flat-sides}(iii), which includes the fused-edge
genericity proof. Its chamber conclusion also follows directly from openness
of the generic locus and continuity of deletion: after shrinking, the image
of the whole parameter interval, including zero, is connected and generic,
so it lies in the connected component containing the central deletion.

For (ii), put $b=a+1$. By Lemma~\ref{lem:wall-sides} the central parent
has nonzero edges and nonzero turns. Relabel cyclically for the count only,
so $M=1$ and $a=k$. The imposed restriction
$M\notin\{a-1,a,a+1,a+2\}$ excludes $k=1,2,n-1,n$. Thus
$3\leq k\leq n-2$. The first half has $k$ vertices and the second has
$n-k+1$, which satisfies the same bounds. This count uses the stated SM1
remoteness condition; it does not add a separate regular-path hypothesis.

Each child vertex is a distinct inherited parent vertex. The only zero
parent point triple is $\{a,b,M\}$. The first half contains $a,M$ but not
$b$, and the second contains $M,b$ but not $a$, so neither contains this
triple. Every child point determinant is therefore a nonzero parent
determinant, proving (G1) for both halves.

Every inherited child edge is a parent edge. The one cut edge in either
half is a positive subsegment of $E_a$. More explicitly, for
$M=A+\lambda(B-A)$ with $0<\lambda<1$, its two possible directed vectors
are $\lambda d_a$ and $(1-\lambda)d_a$, respectively. A point in the
relative interior of either cut edge is in the relative interior of $E_a$.
If three distinct child edge interiors concurred, their parent edge images
would be three distinct parent edges with an interior concurrence: each
half has only one cut edge, so this edge map is injective. The parent edges
must be pairwise remote, because adjacent central parent edges with nonzero
turn meet only at their shared endpoint. Such a concurrence contradicts
$Z_{\rm c}=\varnothing$. Hence both halves satisfy (G2), and together with
their already proved (G1) this is exactly SM1 genericity.
\end{proof}
```

## lem:transport-polynomials — PROVE

reference/SM/sm-1-polygons.tex:1319–1343

```tex
\begin{lemma}[the polynomial controls for SM genericity]
\label{lem:transport-polynomials}
Write the scalar vertex coordinates as $x_1,\ldots,x_{2n}$.
For each unordered triple of distinct vertex indices use one ordered
representative of
\begin{equation}\label{transport:delta}
 \Delta_{ijk}=\det(\mu_j-\mu_i,\mu_k-\mu_i).
\end{equation}
For each unordered triple of pairwise remote edges use one ordered
representative of
\begin{equation}\label{transport:T}
 T_{efg}=\det\begin{pmatrix}\ell_e\\\ell_f\\\ell_g\end{pmatrix},
 \qquad \ell_i=(-d_{i,y},d_{i,x},\det(\mu_i,d_i)),
 \quad d_i=\mu_{i+1}-\mu_i.
\end{equation}
Let $\mathcal F$ be this finite family. Every member is nonzero and
irreducible over $\mathbb R$, and distinct named members are nonassociate.
Each is affine in every scalar coordinate separately. If $F$ depends on
$x_j$, write $F=a x_j+b$; then $a$ is a nonzero polynomial in the other
coordinates. If distinct $F=a x_j+b$ and $G=c x_j+d$ both depend on $x_j$,
the polynomial $ad-bc$ is nonzero. At a specialization with $a\ne0$,
the root of $F$ in $x_j$ is simple; at a specialization with $ad-bc\ne0$,
the two polynomials have no common root.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC tr:factors restricted to the $\Delta$ and $T$ classes, with RC tr:bezout for the per-coordinate certificates (C021); the coordinate-affine specialization and the irreducibility argument are printed here (F-25-183))}
\end{lemma}
```

reference/SM/sm-1-polygons.tex:1344–1410

```tex
\begin{proof}
The quadratic $q(u,v)=u_xv_y-u_yv_x$ has symmetric matrix, in the order
$(u_x,u_y,v_x,v_y)$,
\begin{equation}\label{transport:qmatrix}
 \frac12\begin{pmatrix}0&0&0&1\\0&0&-1&0\\0&-1&0&0\\1&0&0&0\end{pmatrix}.
\end{equation}
Its rank is four. A nontrivial factorization of a homogeneous quadratic is
a product of two homogeneous linear forms. If their coefficient vectors are
$a,b$, the symmetric matrix of their product is
$(ab^{\mathsf T}+ba^{\mathsf T})/2$, of rank at most two. Thus $q$ is
irreducible. The vector pairs defining $\Delta$ and the auxiliary remote
direction determinant $H_{ef}=\det(d_e,d_f)$ are independent linear coordinates:
complete either surjective linear map to an invertible coordinate change.
The polynomial is then $q$ with extra unused variables. A factorization cannot
depend on an unused variable because polynomial degrees in that variable add.
This proves irreducibility and nonzeroness of $\Delta$ and $H$.

For $T$, the six endpoint occurrences are independent. Use the invertible
tail/direction coordinates $(\mu_e,d_e),(\mu_f,d_f),(\mu_g,d_g)$.
Writing the cross product of the first two line rows as $(A,B,C)$ gives
$C=H_{ef}$. Expansion in the third row yields
\begin{equation}\label{transport:T-expand}
 T=d_{g,y}(\mu_{g,x}C-A)+d_{g,x}(B-\mu_{g,y}C).
\end{equation}
These two coefficients have no common nonconstant divisor. Indeed any
irreducible common divisor is independent of $\mu_{g,x}$ because the second
coefficient is, and independent of $\mu_{g,y}$ because the first is.
Comparing coefficients would make it divide $A,B,C$. But $C=H_{ef}$ is
irreducible and does not divide both $A,B$: take $d_e=d_f=(1,0)$ and tails on
different horizontal lines. Then $C=0$ while $A\ne0$. Therefore the two
coefficients in \eqref{transport:T-expand} are coprime. In a factorization
of a polynomial homogeneous of degree one in $(d_{g,x},d_{g,y})$, one factor
is independent of both variables and divides both coefficients. It must be
a unit. This proves irreducibility of $T$; the same expansion proves it is
nonzero.

Each $\Delta$ depends on every vertex in its three-element support. Each
$T$ depends on every endpoint in its six-element support: with one endpoint
fixed, the line through it can be varied by moving its other endpoint;
choose the other two lines to intersect away from the fixed endpoint to
make the determinant vary. Thus different supports cannot give associates,
and the three- and six-vertex families cannot give associates. For a fixed
six-vertex support, the three pairwise remote cycle edges form a perfect
matching. A proper subset of a cycle induces disjoint paths, each of which
has at most one perfect matching (remove its first edge recursively).
The only possible two matchings occur when $n=6$ and the support is the
whole cycle; they are the two alternating matchings. At the specialization
\begin{equation}\label{transport:T-n6-witness}
 (\mu_1,\ldots,\mu_6)=((1,0),(2,0),(0,1),(0,2),(1,1),(2,2))
\end{equation}
the tail-indexed values are $T_{135}=0$ and $T_{246}=2$. Hence they too are
nonassociate. One representative per unordered point triple already removes
the sign associates among the $\Delta$'s.

Every scalar endpoint coordinate occurs affinely in its edge line row, and
the three rows of $T$ have disjoint endpoint supports. Hence $T$ is affine
in each scalar coordinate. The same assertion for $\Delta$ follows by
expanding its area determinant. Genuine dependence therefore has a nonzero
slope $a$. Irreducibility of $a x_j+b$ implies that $a,b$ are coprime in
the polynomial ring of the other coordinates: a nonconstant common divisor
would factor $F$. Likewise $c,d$ are coprime. If $ad-bc=0$, coprimality
of $a,b$ in this unique factorization domain implies $a\mid c$; put $c=au$.
The identity then gives $d=bu$. Coprimality of $c,d$ forces $u$ to be a unit,
so $G=uF$, contradicting nonassociation. Thus $ad-bc$ is a nonzero polynomial.
After specialization, a nonzero slope makes a linear root simple, and
$cF-aG=cb-ad$ excludes a common root when $ad-bc\ne0$.
\end{proof}
```

## thm:relgp — PROVE

reference/SM/sm-1-polygons.tex:1412–1421

```tex
\begin{theorem}[relative general position and the wall dictionary]
\label{thm:relgp}
Let $\gamma:[0,1]\to\mathcal R_n$ be continuous with generic endpoints,
and let $\delta>0$. There is a piecewise-affine path in $\mathcal R_n$ with
the same labelled endpoints, uniformly within $\delta$ of $\gamma$, which
is collision-free and whose nongeneric parameters are finitely many isolated
simple wall germs, each of exactly one of the types (F), (V) bigon, (V)
sliding, (T), (E), (C). No cusp occurs. Every occurrence label is retained.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z and 2026-09-06T01:50:42Z; transcribed from RC tr:gp, tr:five-events (C021))}
\end{theorem}
```

reference/SM/sm-1-polygons.tex:1422–1566

```tex
\begin{proof}
\emph{Open neighbourhoods and endpoint collars.}
The regular locus is open: nonzero edge lengths and avoidance of antiparallel
direction pairs are open conditions. The generic locus is open as well.
To see this directly under SM (G1),(G2), finitely many nonzero point determinants
retain their signs near a generic tuple. Every central remote pair is either
compact-disjoint or an interior transverse pair (Lemma~\ref{lem:g1}(v));
disjointness persists, and a transverse interior crossing persists with
continuous parameters, by Lemma~\ref{lem:wall-segment-stability}. Distinct crossing points have positive pairwise separation, since
a coincidence would place at least three edge interiors at one point. Thus
no triple interior concurrence appears in a sufficiently small neighbourhood.
This proves openness even when a concurrence polynomial vanishes at an
inactive configuration, such as three line extensions concurrent outside the
segments. No all-polynomials-nonzero endpoint assumption is needed.

Cover the compact image of $\gamma$ by axis-parallel open cubes with closures
in $\mathcal R_n$ and diameters less than $\delta$. The endpoint cubes may
be chosen inside the generic locus. A sufficiently fine subdivision
$0=t_0<\cdots<t_N=1$ has each image
$\gamma([t_{i-1},t_i])$ inside one such cube $C_i$, with the first and last
cubes generic. Consecutive cubes overlap in a nonempty open set because they
both contain $\gamma(t_i)$. Refine if necessary so $N\geq3$.

Choose independent internal waypoints $z_i\in C_i\cap C_{i+1}$, while
$z_0=\gamma(0)$ and $z_N=\gamma(1)$ remain fixed. Connect $z_{i-1}$ to $z_i$
by changing their $2n$ scalar coordinates one at a time in a fixed order.
Every intermediate hybrid belongs to $C_i$, since an axis-parallel cube is
closed under coordinate hybridization. Parameterize these legs over
$[t_{i-1},t_i]$. The old and new points at each time belong to the same
cube, proving the uniform $\delta$ bound. All legs are regular. The first
and last coordinate polylines are entirely generic; they are endpoint collars.
Only legs joining two independently variable internal waypoints need further
conditions.

\emph{One joint algebraic choice for the central legs.}
The product of the open waypoint sets is an open subset of a finite-dimensional
real coordinate space. For each central leg moving scalar coordinate $x_j$,
impose the following nonvanishing requirements:
\begin{enumerate}
\item Every $F\in\mathcal F$ is nonzero at both endpoint hybrids.
\item For every $x_j$-dependent $F=a x_j+b$, the fixed-coordinate slope $a$
is nonzero; for every distinct such pair $F,G$, its fixed-coordinate
linear resultant $ad-bc$ is nonzero.
\item The scalar step is nonzero, and both coordinate differences of every
pair of vertex occurrences are nonzero at the endpoint hybrids.
\end{enumerate}
Every requirement is the nonvanishing of a nonzero polynomial in the joint
waypoint variables. For the first two assertions, a central hybrid selects
each coordinate from one of two independent internal waypoints; its projection
contains an open coordinate box. A nonzero polynomial in the hybrid coordinates,
or in the fixed coordinates of the leg, therefore cannot pull back to the zero
polynomial. The nonzero slopes and resultants are supplied by
Lemma~\ref{lem:transport-polynomials}. Coordinate-difference polynomials use
distinct occurrence variables; the scalar step uses two independent values
of the moving coordinate, so these polynomials also are nonzero.

There are finitely many conditions. Their product is a nonzero polynomial,
which cannot vanish on a nonempty real open set. For completeness, this last
fact follows by induction on the number of variables: a univariate nonzero
polynomial has finitely many roots; on a product of open intervals, fixing all
but one variable would force every coefficient polynomial to vanish, and the
induction hypothesis then forces the original polynomial to be zero.
Thus one joint waypoint choice satisfies all requirements. Fixed original
endpoints are excluded from this choice, which is why collars were separated.

\emph{Finite simple roots and collision avoidance.}
On a central leg a factor independent of $x_j$ stays at its nonzero endpoint
value. A dependent factor is a genuinely linear polynomial in the moving
coordinate with nonzero slope, hence has at most one root on the leg.
Different factors have no common root by their nonzero linear resultant.
No root is at a leg endpoint, and each root changes the sign of exactly one
named factor because the scalar step is nonzero. Consequently all central
roots are finite, isolated, smooth hypersurface crossings. Tangencies and
intersections of distinct control hypersurfaces have been avoided by the
explicit slope and resultant conditions, not by an unproved generic-position
assertion.

On a leg moving the $x$-coordinate of one vertex, its $y$-difference from
every other vertex is fixed and nonzero. It cannot collide with any of them.
All other vertex pairs are fixed and distinct. The same argument exchanges
$x,y$ on a $y$-coordinate leg. The collars are generic and hence have distinct
vertices. Thus the whole resulting path is collision-free, including its
fixed endpoints. Every physical edge occurrence stays nonzero because all
legs lie in their regular cubes. A chosen labelled edge can therefore be
followed along the path without relabelling or deletion; no root-independence
statement is used.

If all members of $\mathcal F$ are nonzero, (G1) holds. Any triple interior
concurrence would, under (G1), use pairwise remote edges and make one $T$
zero, so (G2) holds too. Hence every nongeneric parameter is among the finite
central roots. Some roots of an inactive $T$ may still be generic; they are
not declared wall events. Collars contain no nongeneric parameters even when
an inactive polynomial there has nonisolated zeros.

\emph{A point-determinant root.}
At a root of $\Delta_K$, exactly the point triple $K$ is collinear, all
vertices remain distinct, and all $T$'s are nonzero. Thus $Z_{\rm pt}=\{K\}$
and $Z_{\rm c}=\varnothing$. The determinant changes sign simply on the leg.
Count the cyclically adjacent pairs in $K$. If there are at least two and
$n\geq4$, $K=\{j-1,j,j+1\}$ is a consecutive triple. Its middle vertex
must lie strictly between its neighbours, because otherwise the two consecutive
directions there are antiparallel, contrary to regularity. This is exactly (F).
When $n=3$, a distinct collinear triple forms a closed collinear triangle and
necessarily has an antiparallel consecutive pair; such a root cannot lie in
the regular cube.

If there is exactly one adjacent pair, write it as $a,b=a+1$ and call the
third index $M$. The lack of a second adjacent pair is precisely
$M\notin\{a-1,a,a+1,a+2\}$. The contact point is not either endpoint, by
collision freedom. If $M$ is strictly inside $[\mu_a,\mu_b]$, this is (V).
Both neighbours of $M$ have nonzero heights over that line, since another
zero height would be another point triple. Equal height signs give the bigon
branch and opposite signs the sliding branch. If $M$ lies outside the closed
segment, this is (E). Finally, no adjacent pair gives exactly the pairwise
nonadjacent point triple of (C). These alternatives are exhaustive and disjoint.

\emph{An active concurrence root.}
At a root of a single $T_{efg}$ all point determinants are nonzero. If it is
nongeneric, some three edge interiors concur; they must be pairwise remote,
and their concurrence polynomial must be this unique zero member. Thus
$Z_{\rm pt}=\varnothing$ and $Z_{\rm c}=\{\{e,f,g\}\}$. At their common
interior point every pair is transverse, since coincident remote supporting
lines would force a point-determinant zero. All three crossing pairs persist
on nearby punctured sides by their continuous interior intersection parameters.

To verify the sign-change part of (T), put $H_{ef}=\det(d_e,d_f)$ and write
$q_{ef}=\mu_e+t_{ef}d_e$. The cross product of the first two line rows in
\eqref{transport:T} equals $H_{ef}(q_{ef,x},q_{ef,y},1)$, as follows from
its third coordinate $H_{ef}$ and the two line equations. Therefore
\begin{equation}\label{transport:T-order}
 T_{efg}=H_{ef}\det(d_g,q_{ef}-\mu_g)
        =-(t_{ef}-t_{eg})H_{ef}H_{eg}.
\end{equation}
The second equality subtracts $q_{eg}=\mu_e+t_{eg}d_e$, which lies on
the $g$ line, and uses $\det(d_g,d_e)=-H_{eg}$. The two $H$ factors are
nonzero with constant sign near the root. The simple sign change of $T$
therefore changes the sign of $t_{ef}-t_{eg}$. Apply the same calculation
after cyclic permutation of $(e,f,g)$ to obtain the other two required
parameter-difference sign changes. This is exactly (T).

Every nongeneric parameter has now been classified as one named simple wall.
There are no cusp walls, because their central antiparallel pair is excluded
throughout the regular cubes. Both the endpoints and every occurrence label
have been kept exactly as required.
\end{proof}
```

## def:root — DEFINE

reference/SM/sm-2-amplitude.tex:10–27

```tex
\begin{definition}[root and boundary word]\label{def:root}
A \emph{root} of a polygon is one of its edges; on a representative it is an
edge index $g\in\ZZ/n$, the root edge being $E_g$ from $\mu_g$ to
$\mu_{g+1}$, and the shift carries the root $g$ of $P$ to the root $g-1$ of
$\sigma P$. Everything in this section is a function of the pair (polygon,
root). The \emph{boundary word} of $(P,g)$ is the sequence of
vertices
\[
a_0=\mu_{g+1},\ a_1=\mu_{g+2},\ \ldots,\ a_{N}=\mu_{g+n}=\mu_g,\qquad N=n-1,
\]
so that consecutive boundary vertices $a_{k-1},a_k$ are joined by the
\emph{leaf} edge $E_{g+k}$, $1\leq k\leq N$; the leaves are the $n-1$ edges
other than the root, in traversal order. An \emph{interval} is a pair
$[i,j]$ of integers $0\leq i<j\leq N$; it has $j-i$ leaves. A
\emph{composition} of $[i,j]$ is a sequence $\pi=(r_0<r_1<\cdots<r_s)$ with
$r_0=i$, $r_s=j$, $s\geq1$; its \emph{parts} are the intervals
$[r_{k-1},r_k]$, and $|\pi|=s$.
\end{definition}
```

## def:gates — DEFINE

reference/SM/sm-2-amplitude.tex:29–44

```tex
\begin{definition}[gates]\label{def:gates}
Let $\pi=(r_0<\cdots<r_s)$ be a composition of $[i,j]$. At each interior cut
$r_k$, $1\leq k\leq s-1$, put
\[
d_k(\pi)=\chi\bigl(a_{r_{k+1}},a_{r_k},a_{r_{k-1}}\bigr),\qquad
h_k(\pi)=\chi\bigl(a_j,a_{r_k},a_i\bigr),
\]
where $\chi(x,y,z)=\sgn\det(y-x,z-x)$ for points $x,y,z$; $d_k$ is the
\emph{near sign} and $h_k$ the \emph{far sign}. The \emph{ordinary weight}
and the \emph{root weight} of $\pi$ are
\[
V^+(\pi)=\prod_{k=1}^{s-1}d_k\,\Theta\bigl(-h_kd_k\bigr),\qquad
V^-(\pi)=\prod_{k=1}^{s-1}d_k\,\Theta\bigl(h_kd_k\bigr),
\]
with empty products equal to $1$ (so $V^\pm(\pi)=1$ when $s=1$).
\end{definition}
```

## lem:gates-nonzero — PROVE

reference/SM/sm-2-amplitude.tex:46–55

```tex
\begin{lemma}[gates are defined on (G1)]\label{lem:gates-nonzero}
If $P$ satisfies (G1) then every near and far sign is $\pm1$ and every
$\Theta$ in Definition~\ref{def:gates} is evaluated at $\pm1$. On that
domain
\[
d\,\Theta(-hd)=\frac{d-h}{2},\qquad d\,\Theta(hd)=\frac{d+h}{2}\qquad(d,h\in\{\pm1\}),
\]
and $V^+(\pi)=0$ for every composition with exactly two parts.
\status{proved (refereed: bench A 2026-09-12T06:44:52Z, bench B 2026-09-12T06:57:24Z; SM1-carried, read on SM12, no text change, re-read on SM13)}
\end{lemma}
```

reference/SM/sm-2-amplitude.tex:56–62

```tex
\begin{proof}
The three boundary vertices entering a gate are pairwise distinct vertices of
$P$ (the cut positions are distinct and $a_0\neq a_N$ by (G1)), so the signs
are nonzero. The two identities are checked on the four sign pairs. For
$s=2$ the only cut is $r_1$ and $d_1=\chi(a_j,a_{r_1},a_i)=h_1$, so
$\Theta(-h_1d_1)=\Theta(-1)=0$.
\end{proof}
```

## def:treesum — DEFINE

reference/SM/sm-2-amplitude.tex:66–82

```tex
\begin{definition}[open sums and the tree coefficient]\label{def:treesum}
Let $P$ satisfy (G1) and fix a root $g$. Define $b_{[i,j]}\in\ZZ$ for every
interval by recursion on the number of leaves:
\[
b_{[i,i+1]}=1,\qquad
b_{[i,j]}=-\sum_{\substack{\pi\text{ composition of }[i,j]\\|\pi|\geq2}}
V^+(\pi)\prod_{[r_{k-1},r_k]\in\pi}b_{[r_{k-1},r_k]}\quad(j-i\geq2).
\]
The \emph{tree coefficient} of $P$ at the root $g$ is
\[
A_g(P)=\sum_{\pi\text{ composition of }[0,N]}
V^-(\pi)\prod_{[r_{k-1},r_k]\in\pi}b_{[r_{k-1},r_k]},
\]
the sum including the one-part composition, whose term is $b_{[0,N]}$. The main
text's $A(P)$ is $A_n(P)$, rooted at the last edge $E_n$ from $\mu_n$ to
$\mu_1$.
\end{definition}
```

## lem:treesum-trees — PROVE

reference/SM/sm-2-amplitude.tex:84–104

```tex
\begin{lemma}[equivalence with the plane-tree sum]\label{lem:treesum-trees}
Let $\mathfrak T_g(P)$ be the set of rooted plane trees whose leaves are the
$n-1$ leaf edges in traversal order, whose root vertex has one or more
children, and whose other internal vertices (the \emph{ordinary} vertices)
have at least two children each; every internal vertex is labelled by the
composition of its leaf interval into the leaf intervals of its children.
Then
\[
A_g(P)=\sum_{T\in\mathfrak T_g(P)}(-1)^{N_+(T)}\,
V^-(\pi_{\rm root})\prod_{v\text{ ordinary}}V^+(\pi_v),
\]
where $N_+(T)$ is the number of ordinary vertices. The identity is formal:
the bijection of the proof matches the terms of the recursion of
Definition~\ref{def:treesum} with the trees term by term, so it holds with
the gate values $V^\pm(\pi)$ replaced by independent formal variables, as an
identity in the polynomial ring over $\ZZ$ in those variables, and
specializes to every evaluation of them. This is \mt{eq:amplitude},
whose vertex weights are Definition~\ref{def:gates} with
$m=s$, $a_k$ the boundary vertices of the cuts, and whose sign
$(-1)^{N_+}$ is the one minus per ordinary vertex. \status{new (round~5: the formal-variable clause exported --- the grafting bijection of the proof uses nothing about the gate values, so the identity holds in the polynomial ring in those values and specializes to every evaluation, F-25-150; the remainder is the SM1 proof, audited there)}
\end{lemma}
```

reference/SM/sm-2-amplitude.tex:105–110

```tex
\begin{proof}
Removing the top vertex of an ordinary tree on $[i,j]$ leaves one subtree per
part of its composition; grafting is the inverse. The minus sign of the top
vertex is the minus sign in the recursion for $b$. The root vertex carries
$V^-$, no sign, and may have one child, which is the one-part composition.
\end{proof}
```

## prop:A-chamber — PROVE

reference/SM/sm-2-amplitude.tex:121–126

```tex
\begin{proposition}[chirotope chambers]\label{prop:A-chamber}
If two polygons satisfying (G1) have the same chirotope, then for every root
$g$ every composition weight, every $b_{[i,j]}$ and $A_g$ agree. In
particular $A_g$ is constant on every labelled chamber (the root fixed), and
constant along any path of (G1)-polygons with constant chirotope. \status{proved (refereed: bench A 2026-09-12T06:44:52Z, bench B 2026-09-12T06:57:24Z; SM1-carried, read on SM12, repaired in round 12 (F-25-191), re-read on SM13)}
\end{proposition}
```

reference/SM/sm-2-amplitude.tex:127–135

```tex
\begin{proof}
Every quantity in Definitions~\ref{def:gates} and~\ref{def:treesum} is a
function of the signs $\chi(a_x,a_y,a_z)$, which are chirotope entries. A
labelled chamber is a component of $\mathcal U_n$, an open set
(Proposition~\ref{prop:chambers}), hence path connected, and the chirotope
is constant along every path in $\mathcal U_n$
(Proposition~\ref{prop:chambers}); so $A_g$ is constant on each labelled
chamber.
\end{proof}
```

## def:nearfar — DEFINE

reference/SM/sm-2-amplitude.tex:137–149

```tex
\begin{definition}[the near--far arrays]\label{def:nearfar}
Over a commutative ring in which $2$ is invertible, let $D(x,y,z)$ and
$H(x,y,z)$ be arbitrary scalars indexed by increasing triples
$0\leq x<y<z\leq N$. For an array $X=(X_{ij})_{0\leq i<j\leq N}$ put
\[
\Phi_{D,H}(X)_{ij}=\sum_{\pi=(i=r_0<\cdots<r_s=j)}
\Bigl(\prod_{k=1}^{s-1}\frac{D(r_{k-1},r_k,r_{k+1})-H(i,r_k,j)}2\Bigr)
\prod_{k=1}^sX_{r_{k-1}r_k},
\]
$F_H=\Phi_{0,H}$, $G_D=\Phi_{D,0}$, and $E_{ij}=1$ if $j=i+1$ and $0$
otherwise. The \emph{geometric arrays} are $D(x,y,z)=\chi(a_z,a_y,a_x)$ and
$H(x,y,z)=\chi(a_z,a_y,a_x)$ with the boundary vertices of $(P,g)$.
\end{definition}
```

## lem:farout — PROVE

reference/SM/sm-2-amplitude.tex:151–173

```tex
\begin{lemma}[factorization and far-only output]\label{lem:farout}
\begin{enumerate}
\item[(i)] Over any commutative ring in which $2$ is invertible,
$\Phi_{D,H}$ has a two-sided polynomial inverse and
\begin{equation}\label{afr:factor}
\Phi_{D,H}=F_H\circ G_D.
\end{equation}
\item[(ii)] With the geometric arrays, $\Phi_{D,H}(b)=E$ and
$A_g(P)=\Phi_{D,-H}(b)_{0N}$. Consequently, with $c=F_H^{-1}(E)$,
\begin{equation}\label{afr:far-output}
A_g(P)=F_{-H}(c)_{0N}.
\end{equation}
The complete output is independent of $D$ when $H$ is held fixed.
\item[(iii)] For an interval $J=[i,j]$ put
$\mathcal E_J=F_H(c)_J$ and $\mathcal B_J=F_{-H}(c)_J$.
Then $\mathcal E_J=0$ if $j-i\geq2$, and
$\mathcal E_J=\mathcal B_J=1$ if $j-i=1$.
For $j-i\geq2$, if $(a_i,\ldots,a_j)$ satisfies (G1),
$\mathcal B_J$ is its tree coefficient rooted at its closing edge
from $a_j$ to $a_i$.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC mt:factorization, mt:far-only (C022))}
\end{lemma}
```

reference/SM/sm-2-amplitude.tex:174–232

```tex
\begin{proof}
For (i), the one-part composition in coordinate $[i,j]$ contributes
$X_{ij}$ with coefficient one. Every other composition has at least two
parts, all of shorter interval length. Given any target $Y$, first put
$X_{i,i+1}=Y_{i,i+1}$ and then, in increasing interval length, subtract
the already determined nonunary sum from $Y_{ij}$. This uniquely solves
$\Phi_{D,H}(X)=Y$, by polynomial operations in the finite arrays.
Writing the solution map as $\Psi$, construction gives
$\Phi_{D,H}\circ\Psi=\mathrm{id}$. Applying uniqueness to the target
$\Phi_{D,H}(X)$ gives $\Psi\circ\Phi_{D,H}(X)=X$, the other inverse.

Expand $F_H(G_D(X))_{ij}$. Its terms are indexed by an outer
composition of $[i,j]$ and an inner composition of each outer part.
Their ordered union is a refined composition
$\rho=(r_0<\cdots<r_s)$, with the subset of its interior cuts marked
as outer cuts. Conversely, cut $\rho$ at the marked cuts to recover
the outer parts and restrict $\rho$ to each part to recover its inner
composition. This is a bijection, including empty and full marked
subsets and unary inner or outer compositions.

At a marked cut $r_k$ the coefficient is $-H(i,r_k,j)/2$.
At an unmarked cut its immediate neighbors in $\rho$ are precisely
its neighbors inside the same inner part, since that part's endpoints
are also in $\rho$. Its coefficient is
$D(r_{k-1},r_k,r_{k+1})/2$. Each interior cut supplies one factor,
and the product of child coordinates is exactly the refined product.
Summing over every subset of marked cuts independently chooses the
near or negative far summand at each cut. Distributivity yields the
product of their sums, precisely the coefficient of $\rho$ in
Definition~\ref{def:nearfar}. This proves \eqref{afr:factor}, with all
neighboring near gates accounted for.

For (ii), the identities $d\Theta(-hd)=(d-h)/2$ and
$d\Theta(hd)=(d+h)/2$, for $d,h\in\{\pm1\}$, turn the open-sum
recursion into $\Phi_{D,H}(b)=E$ and the full root sum into
$\Phi_{D,-H}(b)_{0N}$. In particular its unary root term is retained.
By \eqref{afr:factor}, $F_H(G_D(b))=E$; uniqueness of the inverse
gives $G_D(b)=c$. Applying the factorization with $-H$ gives
\begin{equation}\label{afr:near-freedom}
\Phi_{D,-H}(b)=F_{-H}(G_D(b))=F_{-H}(c).
\end{equation}
This proves the assertion about the complete output. It asserts no
near-array independence for individual trees or open sums.

For (iii), restriction to $J$ commutes with all coordinate equations:
each equation on a subinterval of $J$ reads only its own subintervals
and triples. Triangular uniqueness therefore identifies the restriction
of $c$ with the inverse constructed directly on that restricted word.
The equation $F_H(c)=E$ gives the claimed $\mathcal E$ values.
On a one-leaf interval the only composition is unary, its inverse
coordinate is one, and both transforms equal one. This is a formal
open-word convention, not a two-gon amplitude.
On an interval with at least two leaves, the closed endpoint polygon
has at least three vertices. Cutting its closing edge from $a_j$ to
$a_i$ gives exactly the word $a_i,\ldots,a_j$. If it satisfies (G1),
part (ii) on that word identifies $\mathcal B_J$ with its amplitude
at that specified physical root. The auxiliary coordinates $c$ may be
rational and their binary coordinates need not vanish.
\end{proof}
```

## thm:single-triple — PROVE

reference/SM/sm-2-amplitude.tex:234–274

```tex
\begin{theorem}[single-triple wall response]\label{thm:single-triple}
Let $t\mapsto P(t)$ be a wall germ with $Z_{\rm c}=\varnothing$,
$Z_{\rm pt}=\{K\}$ a single triple of pairwise distinct vertices,
and $\chi_K$ changing sign at zero. This includes types (F), (K),
(V), (E), and (C). Cut at a fixed physical root $g$ and let
$x<y<z$ be the critical boundary positions. Put
$I_*=[x,z]$, $L=[x,y]$, $R=[y,z]$, $F=[0,N]$, and
\begin{equation}\label{afr:wall-data}
\delta=\frac{H^+(x,y,z)-H^-(x,y,z)}2\in\{-1,1\}.
\end{equation}
Write the three wall points as $a_v=p_*+\xi_v\omega$ with
$\omega\ne0$ and distinct $\xi_v$. Set
\begin{equation}\label{afr:wall-epsilons}
\epsilon_L=\sgn\frac{\xi_y-\xi_x}{\xi_z-\xi_x},\qquad
\epsilon_R=\sgn\frac{\xi_z-\xi_y}{\xi_z-\xi_x}.
\end{equation}
For $J=L,R$ use the unchanged interval values of
Lemma~\ref{lem:farout}, and put
\begin{equation}\label{afr:wall-uv}
\mathcal U_J=\begin{cases}\mathcal E_J,&\epsilon_J=1,\\
\mathcal B_J,&\epsilon_J=-1,\end{cases}\qquad
\mathcal V_J=\begin{cases}\mathcal B_J,&\epsilon_J=1,\\
\mathcal E_J,&\epsilon_J=-1.\end{cases}
\end{equation}
If $I_*\ne F$, let $Q$ be the polygon obtained at $t=0$ by
replacing the boundary arc $a_x,\ldots,a_z$ with the single edge
from $a_x$ to $a_z$. Then $Q$ satisfies (G1), has at least three
vertices, retains the physical root $g$, and
\begin{equation}\label{afr:wall-proper}
A_g(P_+)-A_g(P_-)=\delta\mathcal U_L\mathcal U_R A_g(Q).
\end{equation}
If $I_*=F$, instead
\begin{equation}\label{afr:wall-full}
A_g(P_+)-A_g(P_-)
=\delta(\mathcal U_L\mathcal U_R+\mathcal V_L\mathcal V_R).
\end{equation}
Here $P_\pm$ are on sufficiently close punctured sides of the germ;
all gap and contracted coefficients are evaluated at their nondegenerate
wall data, equivalently at the same signs on either sufficiently close side.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z and 2026-09-05T19:42:49Z; transcribed from RC mt:wall-response (C022))}
\end{theorem}
```

reference/SM/sm-2-amplitude.tex:275–378

```tex
\begin{proof}
The wall hypothesis makes every distinct-triple determinant except the
critical one nonzero at zero; after a common shrink its sign is the
same on both punctured sides. Neither gap contains the entire critical
triple, so both gap arrays and every nontrivial closed gap polygon are
nondegenerate and unchanged. Singleton gap values have only their formal
open-word meaning. At least one epsilon is positive: otherwise both
summands in $\xi_z-\xi_x=(\xi_y-\xi_x)+(\xi_z-\xi_y)$ would have
sign opposite to their nonzero sum.

Use the far-only representation of Lemma~\ref{lem:farout} on each side.
The changing triple appears as far data in exactly one coordinate formula
of $F_H$, namely $[x,z]$.  Induction in interval length therefore shows
that $c$ is unchanged on every interval not containing $I_*$.

In the $[x,z]$ equation every proper child is unchanged.  A composition
has a changing coefficient exactly when it cuts at $y$.  Splitting its
cut list at $y$ is a bijection with a pair of arbitrary compositions of
$L$ and $R$; concatenating the two lists is its inverse.  Its one
changing far gate $-H(x,y,z)/2$ has difference $-\delta$.
For every other cut in these compositions, the wall geometry gives
\begin{align}
 H(x,r,z)&=\epsilon_L H(x,r,y) &&(x<r<y),\label{afr:wall-left-sign}\\
 H(x,r,z)&=\epsilon_R H(y,r,z) &&(y<r<z).\label{afr:wall-right-sign}
\end{align}
For the first identity, the vectors from $a_x$ to $a_z$ and to $a_y$
differ by the scalar $(\xi_z-\xi_x)/(\xi_y-\xi_x)$.
Taking their determinants with $a_r-a_x$ gives the indicated sign ratio.
For the second use the vectors from $a_z$ to $a_x$ and to $a_y$;
their scalar ratio has sign $\epsilon_R$.  All these determinants are
nonzero at the wall.  Their signs on both sufficiently close sides are
therefore the wall signs, proving both displayed identities on those
sides without evaluating a zero gate.

Consequently the composition sum on a gap is $F_H(c)_J=\mathcal E_J$ if
$\epsilon_J=1$, and $F_{-H}(c)_J=\mathcal B_J$ if $\epsilon_J=-1$.
The changed nonunary sum in $F_H(c)_{xz}=E_{xz}=0$ is thus
$-\delta \mathcal U_L\mathcal U_R$.  Since the unary coefficient is $1$, moving this
sum to the other side gives
\begin{equation}\label{afr:wall-source}
 c^+_{xz}-c^-_{xz}=s_*,
 \qquad s_*=\delta \mathcal U_L\mathcal U_R.
\end{equation}
The nonunary part of $F_{-H}(c)_{xz}$ must be calculated separately.
Its changing gate is $+H(x,y,z)/2$, with difference $+\delta$;
all proper children are still unchanged.  Reversing the remaining far
signs exchanges $\mathcal E_J$ with $\mathcal B_J$ in each of the two gap sums.
Its direct coefficient change is therefore $+\delta \mathcal V_L\mathcal V_R$.

It remains to propagate \eqref{afr:wall-source} through larger intervals.
Contract $I_*$ in the boundary word to the formal leaf $e_*$, and let
$c^Q$ be the inverse $F_{H^Q}^{-1}(E)$ on that contracted word.
This inverse is defined even when the contracted word has only one
leaf; that is an open-word convention, not a two-gon amplitude.
For an interval containing $I_*$ write $I/e_*$ for its contraction.
We prove by interval length that
\begin{equation}\label{afr:wall-propagation}
 c^+_I-c^-_I=s_*c^Q_{I/e_*}\quad(I\supseteq I_*),
 \qquad c^+_I-c^-_I=0\quad(I\not\supseteq I_*).
\end{equation}
The smallest containing interval is $I_*$ itself.  Its contracted
coordinate is the leaf value $1$, so this is \eqref{afr:wall-source}.
For a strictly larger $I$, its far coefficient formula is unchanged.
In a top composition at most one child can contain the positive-length
interval $I_*$, because distinct children have disjoint interiors.
If no child contains it, every child coordinate is unchanged.  Otherwise
the product difference is exactly the difference of that unique child
times all other, unchanged child coordinates.  There is no product of
two changing factors or choice of side for the others.

The compositions having such a child are in bijection with compositions
of $I/e_*$.  Forward, erase the interior vertices of $I_*$ inside that
one child; no top cut lies there.  Backward, the distinguished leaf
$e_*$ belongs to one unique contracted child, and expanding it
recovers the original child and top cut list.  The operations are
inverse.  All top endpoints and cut vertices survive, so every far
gate has the same indices and signs.  Every other child is disjoint
from the interior of $I_*$, and its $c$ coordinate agrees with $c^Q$
by restriction and uniqueness of the unchanged triangular equations.
Insert the induction hypothesis on the changing child.  The difference
of the equation $F_H(c)_I=0$ becomes $s_*$ times the equation
$F_{H^Q}(c^Q)_{I/e_*}=0$.  The contracted interval has at least two
leaves when $I$ strictly contains $I_*$, so this latter right-hand
side is indeed zero.  Equivalently, its unary term is the negative
of its full nonunary sum, giving precisely
$c^+_I-c^-_I=s_*c^Q_{I/e_*}$.  This proves the induction with its sign.

When $I_*\ne F$, the same composition bijection, now including the
unary term, applies to the barred transform $F_{-H}$ on $F$.
Its coefficients are unchanged because its endpoints are not both $x,z$.
Substitution of \eqref{afr:wall-propagation} gives
$s_*F_{-H^Q}(c^Q)_{F/e_*}$.  At least one further leaf survives outside
$I_*$, so $Q$ has at least three vertices.  Its vertices have no zero
triple, since the only critical triple lost its middle occurrence.
Its endpoints and hence physical root survive.  Lemma~\ref{lem:farout}
identifies the last output with $s_*A_g(Q)$, proving
\eqref{afr:wall-proper}.

When $I_*=F$, all proper children are unchanged and the unary
contribution is \eqref{afr:wall-source}.  Add the separately computed
direct barred coefficient change $+\delta \mathcal V_L\mathcal V_R$ to obtain
\eqref{afr:wall-full}.  In this case there is no closed contracted
amplitude of arity at least three.
\end{proof}
```

## def:induced-roots — DEFINE

reference/SM/sm-2-amplitude.tex:385–399

```tex
\begin{definition}[induced roots]\label{def:induced-roots}
At a simple flat or cusp wall at $j$, the \emph{deletion map} on roots is
\[
D_j(g)=\begin{cases}\text{the fused edge }[\mu_{j-1},\mu_{j+1}]\text{ of }P\setminus j,& g\in\{j-1,j\},\\
\text{the edge of }P\setminus j\text{ with the same endpoints as }E_g,&\text{otherwise.}\end{cases}
\]
At a simple vertex--edge wall at $(M;a)$, with $d_1=[\mu_a,\mu_M]$ the
closing edge of $\lambda_1$ and $d_2=[\mu_M,\mu_{a+1}]$ the opening edge of
$\lambda_2$, the \emph{half map} on roots is
\[
H(g)=\begin{cases}(d_1,d_2),&g=a,\\
(E_g\text{ in }\lambda_1,\ d_2),&g\in\{M,M+1,\ldots,a-1\},\\
(d_1,\ E_g\text{ in }\lambda_2),&g\in\{a+1,\ldots,M-1\}.\end{cases}
\]
\end{definition}
```

## thm:A-S3 — PROVE

reference/SM/sm-2-amplitude.tex:401–410

```tex
\begin{theorem}[flat law for $A_g$]\label{thm:A-S3}
At a simple flat wall at $j$ with $n\geq4$, for every root $g$,
\begin{equation}\label{afr:S3}
A_g(P_{\rm right})-A_g(P_{\rm left})
=A_{D_j(g)}(P(0)\setminus j),
\end{equation}
where $P_{\rm right}$ is the side with $\tau_j=-1$, and
$D_j$ is the physical deletion map of Definition~\ref{def:induced-roots}.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC mt:s3 (C022))}
\end{theorem}
```

reference/SM/sm-2-amplitude.tex:411–458

```tex
\begin{proof}
Put $Q=P(0)\setminus j$. Its vertices are a subset of the wall
vertices missing the middle occurrence of the sole zero triple. Hence
all its distinct-triple determinants are nonzero, so it satisfies (G1),
and $n-1\geq3$. The flat hypothesis puts the deleted vertex strictly
between its neighbors. Let $P^\pm$ denote the sides on which
$\chi(\mu_{j-1},\mu_j,\mu_{j+1})=\pm1$, and write
$u=(\mu_{j-1},\mu_j)$, $v=(\mu_j,\mu_{j+1})$,
$w=(\mu_{j-1},\mu_{j+1})$. The determinant defining this chirotope
is $\det(\widetilde\lambda_{j-1},\widetilde\lambda_j)$, since
$\mu_{j+1}-\mu_{j-1}=\widetilde\lambda_{j-1}+\widetilde\lambda_j$.
Thus it is $\tau_j$, and $P^-=P_{\rm right}$,
$P^+=P_{\rm left}$.

Write $A=\mu_{j-1}$, $M=\mu_j$, $B=\mu_{j+1}$.  In any root cut the
three critical occurrences have a cyclic permutation of the order
$A,M,B$.  A cyclic permutation is even, so their reverse-ordered far
sign is always $-\chi(A,M,B)$.  Thus the $\delta$ of
\eqref{afr:wall-data}, for $P^+$ minus $P^-$, is $-1$.

If $g$ is neither $u$ nor $v$, the cut order is $A,M,B$, with no
root seam between these consecutive edges.  Both gaps are singleton
leaves, and strict betweenness gives
$(\epsilon_L,\epsilon_R)=(1,1)$.  Hence $\mathcal U_L\mathcal U_R=1$.
Their span is proper: if both extreme vertices were the root endpoints,
the remaining root edge would close a three-vertex polygon, contrary
to $n\geq4$.  Contracting the two-edge span deletes exactly $M$
and retains $g$.  Formula~\eqref{afr:wall-proper} gives
$A_g(P^+)-A_g(P^-)=-A_g(Q)$.

If $g=u$, the cut order is $M,B,\ldots,A$, so the critical span is
full.  The gap $L=(M,B)$ is singleton and
$(\epsilon_L,\epsilon_R)=(-1,1)$: with $A=0$, $B=1$,
$M=t\in(0,1)$, the first ratio has numerator $1-t>0$ and
denominator $-t<0$, and the second has numerator $-1<0$.
The other gap $R$ has $n-2\geq2$ leaves; its closing root is
$w=(A,B)$ and its closed polygon is $Q$.  Therefore
$\mathcal U_L\mathcal U_R=0$ and $\mathcal V_L\mathcal V_R=A_w(Q)$.
Formula~\eqref{afr:wall-full} gives the desired negative of $A_w(Q)$.

If $g=v$, the cut order is $B,\ldots,A,M$.  Now $L$ is the
nontrivial deletion word with closing root $w$, $R=(A,M)$ is
singleton, and $(\epsilon_L,\epsilon_R)=(1,-1)$.
Indeed their numerators are $-1$ and $t$ with common denominator
$t-1<0$.  Again $\mathcal U_L\mathcal U_R=0$ and $\mathcal V_L\mathcal V_R=A_w(Q)$.
These three cases exhaust the physical roots and prove
\eqref{afr:S3} with precisely Definition~\ref{def:induced-roots}.
\end{proof}
```

## thm:A-S4 — PROVE

reference/SM/sm-2-amplitude.tex:460–469

```tex
\begin{theorem}[cusp law for $A_g$]\label{thm:A-S4}
At a simple cusp wall at $j$ with $n\geq4$ whose deletion
$Q=P(0)\setminus j$ satisfies (G1), for every root $g$,
\begin{equation}\label{afr:S4}
A_g(P_{\rm loop})-A_g(P_{\rm no})
=-\kappa A_{D_j(g)}(Q),\qquad
\kappa=\rot(P_{\rm loop})-\rot(P_{\rm no})\in\{-1,1\}.
\end{equation}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC mt:s4 (C022))}
\end{theorem}
```

reference/SM/sm-2-amplitude.tex:470–523

```tex
\begin{proof}
Let $u=(\mu_{j-1},\mu_j)$, $v=(\mu_j,\mu_{j+1})$ and
$w=(\mu_{j-1},\mu_{j+1})$. These are physical edges; they are not
renumbered root slots. The cusp hypothesis places the deleted vertex
outside its neighbors' closed segment. As in the preceding theorem,
$\chi(\mu_{j-1},\mu_j,\mu_{j+1})=\tau_j$ by bilinearity.

First prove the signed consecutive identity directly, without assuming
the betweenness calculation from S3.  Write $A=\mu_{j-1}$, $M=\mu_j$,
$B=\mu_{j+1}$, and take line coordinates $A=0$, $B=1$, $M=t$,
where $t<0$ or $t>1$.  Name sides by $\chi(A,M,B)=-1,+1$ as in
S3.  The reverse-ordered far sign again gives $\delta=-1$ for
$P^+$ minus $P^-$.  For a nonincident root the two gaps are
singletons, regardless of their epsilon signs; hence $\mathcal U_L\mathcal U_R=1$.
The proper-span formula gives the signed deletion identity.

For the incident roots the following full-span table computes all four
cases from \eqref{afr:wall-epsilons}:
\begin{equation}\label{afr:s4-table}
\begin{array}{c|c|c|cc|c}
 \text{root}&\text{critical cut order}&t&
 \epsilon_L&\epsilon_R&
 \text{possibly nonzero summand}\\\hline
 u&M,B,A&t>1&1&1&\mathcal V_L\mathcal V_R=\mathcal B_R\\
 u&M,B,A&t<0&1&-1&\mathcal U_L\mathcal U_R=\mathcal B_R\\
 v&B,A,M&t>1&-1&1&\mathcal U_L\mathcal U_R=\mathcal B_L\\
 v&B,A,M&t<0&1&1&\mathcal V_L\mathcal V_R=\mathcal B_L
\end{array}
\end{equation}
For $u$, $L$ is singleton and $R$ is the deletion word closed by
$w=(A,B)$; the epsilon ratios are $(1-t)/(-t)$ and $(-1)/(-t)$.
For $v$, $R$ is singleton and $L$ is that deletion word; the
ratios are $(-1)/(t-1)$ and $t/(t-1)$.  These four ratio tests give
the table.  The other summand contains the nontrivial deletion
word's $E=0$.  Formula~\eqref{afr:wall-full} therefore gives
$A_g(P^+)-A_g(P^-)=-A_{D_j(g)}(Q)$ in each incident case also.

For the rotation sign, the principal local turn at $M$ tends to
$+\pi$ on the positive-chirotope side and to $-\pi$ on the
negative side, since its determinant is $\det(M-A,B-M)$ and
has sign $\chi(A,M,B)$.  Every other local turn is continuous at
this sole consecutive degeneration: its consecutive triple is distinct
from the critical triple because $n\geq4$, and is nonzero at the wall.
The edges are nonzero and the two incident directions at $M$ tend to
opposites. Thus the sum of all principal turns on the positive side
minus that on the negative side tends to $2\pi$. By
Lemma~\ref{lem:rot}, each punctured-side rotation is an integer constant
on its sufficiently small connected regular side. Their difference is
therefore its limit, namely $1$.  If the loop side is $P^+$, then
$\kappa=1$ and the just-proved signed formula is
\eqref{afr:S4}.  If it is $P^-$, then $\kappa=-1$ and
reversing the same formula gives \eqref{afr:S4}.
No root-independence or transport theorem is used.
\end{proof}
```

## thm:A-S7 — PROVE

reference/SM/sm-2-amplitude.tex:525–534

```tex
\begin{theorem}[vertex--edge law for $A_g$]\label{thm:A-S7}
At a simple vertex--edge wall at $(M;a)$, of bigon or sliding type,
let $s=\chi_{a,a+1,M}(P_-)$ and let $\lambda_1,\lambda_2$ be the
halves in Definition~\ref{def:deletion-halves}. For every physical root
$g$ with $H(g)=(h_1,h_2)$ as in Definition~\ref{def:induced-roots},
\begin{equation}\label{as7:law}
A_g(P_+)-A_g(P_-)=s A_{h_1}(\lambda_1)A_{h_2}(\lambda_2).
\end{equation}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC mt:s7 (C024))}
\end{theorem}
```

reference/SM/sm-2-amplitude.tex:535–591

```tex
\begin{proof}
Write $A=\mu_a(0)$, $B=\mu_{a+1}(0)$, $X=\mu_M(0)$,
$d=(A,B)$, $d_1=(A,X)$ and $d_2=(X,B)$. The original cyclic order
of the three critical vertices is $A,B,X$. Both original arc words,
from $X$ to $A$ and from $B$ to $X$, have at least two leaves:
their closing halves are generic and have at least three vertices by
Lemma~\ref{lem:children}(ii). Each nontrivial closed word below has
only nonzero point-triple determinants. Its amplitude at the indicated
closing edge is therefore the interval value of Lemma~\ref{lem:farout}(iii).

In any root cut, the critical order is a cyclic permutation of $A,B,X$.
Such a permutation is even, whereas the reverse ordering in the far
sign is odd. The critical far sign is consequently
$-\chi(A,B,X)$. It equals $-s$ on $P_-$ and $s$ on $P_+$.
The quantity $\delta$ in \eqref{afr:wall-data} is therefore $s$.
Choose affine line coordinates $A=0$, $B=1$, $X=t$ with $0<t<1$.

For $g=d$, the boundary word begins at $B$, passes through $X$,
and ends at $A$. The critical span is full. The two ratios in
\eqref{afr:wall-epsilons} are $(t-1)/(-1)>0$ and $(-t)/(-1)>0$.
Both gaps are nontrivial, so both $\mathcal U$ factors are zero
$\mathcal E$ factors. The $\mathcal V$ factors are respectively
$A_{d_2}(\lambda_2)$ and $A_{d_1}(\lambda_1)$.
The full-span formula \eqref{afr:wall-full} gives the desired product.
Writing it in the prescribed half order uses commutativity of scalar
multiplication; it does not interchange the named halves.

If $g$ lies on the original arc from $X$ to $A$, the critical cut
order is $A,B,X$. The first gap is the singleton edge $d$, and the
second is the nontrivial arc from $B$ to $X$. Its epsilon ratios are
$1/t>0$ and $(t-1)/t<0$, so
$\mathcal U_L\mathcal U_R=A_{d_2}(\lambda_2)$.
The critical span is proper. Otherwise the physical root would be an
edge from $X$ to $A$, making that original arc a singleton and its
closing half a two-gon, contrary to the arity just established.
Contracting the span replaces the arc $A,B,\ldots,X$ by $d_1$.
The surviving polygon is exactly $\lambda_1$ with the same physical
root $g$. Formula~\eqref{afr:wall-proper} gives
$sA_g(\lambda_1)A_{d_2}(\lambda_2)$.

If $g$ lies on the original arc from $B$ to $X$, the critical cut
order is $X,A,B$. The first gap is the nontrivial arc from $X$ to
$A$, and the second is the singleton $d$. The ratios are
$-t/(1-t)<0$ and $1/(1-t)>0$. Thus
$\mathcal U_L\mathcal U_R=A_{d_1}(\lambda_1)$.
The span is proper, since a full span would make the original
$B$-to-$X$ arc a singleton. Contraction replaces $X,\ldots,A,B$
by $d_2$, leaving exactly $\lambda_2$ at the same physical root.
The proper-span formula gives $sA_{d_1}(\lambda_1)A_g(\lambda_2)$.

Every original root belongs to exactly one of these three cases.
The inherited-arc cases include the edges incident to the named
endpoints, so no additional root-seam case remains. No step restricts
the side of the contact line occupied by either neighbour of $X$.
Both bigon and sliding branches are therefore covered. The three
products are precisely the three rows of the stated half-root map.
\end{proof}
```

## thm:A-R3E — PROVE

reference/SM/sm-2-amplitude.tex:593–601

```tex
\begin{theorem}[triple law and silence for $A_g$]\label{thm:A-R3E}
\begin{enumerate}
\item[(i)] At a simple triple wall every composition weight, every
$b_{[i,j]}$ and $A_g$ are identical on the two sides, for every root $g$.
\item[(ii)] At a simple exterior-extension wall or a simple pure cut,
$A_g(P_+)=A_g(P_-)$ for every root $g$.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from (ii) RC mt:extension, mt:pure; (i) as in SM1 (C024))}
\end{theorem}
```

reference/SM/sm-2-amplitude.tex:602–656

```tex
\begin{proof}
For (i), every point-triple determinant has a nonzero central value,
so finitely many continuity conditions give a common interval on
which all signs read by Definition~\ref{def:gates} agree across the
wall. Every gate and composition weight agrees. Starting with the
one-leaf value and inducting on interval length in the open recursion
then gives equality of all $b$'s. Substituting them in the finite root
sum gives equality of $A_g$. Crossing-visit order is not an input to
any of these formulas.

For an exterior-extension wall, use $A,B,X,d$ as in the preceding
proof, but now $t<0$ or $t>1$. By the remoteness condition in
Definition~\ref{def:walls}(E), both full original arcs from $X$ to
$A$ and from $B$ to $X$ have at least two leaves. A singleton in
either would give a second adjacent pair in the critical triple and
would be a consecutive-triple wall instead. Closed nontrivial gap
and contracted words have (G1), since they omit at least one member
of the sole zero triple.

If $g=d$, the critical order is $B,X,A$, the span is full and both
gaps are nontrivial. Their epsilon ratios are $1-t$ and $t$.
Exactly one is negative. Hence $\mathcal U_L\mathcal U_R$ and
$\mathcal V_L\mathcal V_R$ each contain a nontrivial $\mathcal E$
factor, which is zero by Lemma~\ref{lem:farout}(iii).
The full-span formula gives zero jump.
If $g$ lies on the original $X$-to-$A$ arc, the cut order is $A,B,X$;
$L$ is singleton, $R$ is nontrivial, and
$\epsilon_R=\operatorname{sgn}((t-1)/t)=1$ for both allowed ranges
of $t$. Thus $\mathcal U_R=\mathcal E_R=0$. The span is proper,
since a full span would make the original $X$-to-$A$ arc a singleton.
Formula~\eqref{afr:wall-proper} gives zero jump.
For a root on the other arc, the cut order is $X,A,B$; $L$ is
nontrivial and $\epsilon_L=\operatorname{sgn}(-t/(1-t))=1$.
The span is proper for the analogous endpoint reason, and
$\mathcal U_L=\mathcal E_L=0$. This exhausts all exterior roots.
No assertion here applies to a consecutive cusp or flat wall.

Finally consider a pure cut. In the fixed root word write its critical
positions as $x<y<z$, with $N=n-1$. Pairwise nonadjacency gives
\begin{equation}\label{as7:pure-gaps}
y-x\geq2,\qquad z-y\geq2,\qquad N+1+x-z\geq2.
\end{equation}
The first two inequalities make both gaps nontrivial. The third shows
that the span cannot be full: full-span extremes would be the two
adjacent endpoints of the physical root. At least one epsilon is
positive, since the two nonzero line displacements from $x$ to $y$
and from $y$ to $z$ cannot both have sign opposite to their sum from
$x$ to $z$. Therefore the source product
$\mathcal U_L\mathcal U_R$ contains a zero $\mathcal E_L$ or
$\mathcal E_R$. Formula~\eqref{afr:wall-proper} again gives zero.
The argument allows $x=0$ or $z=N$ separately, so it includes roots
incident to a critical vertex and all six possible line orders.
The conclusion concerns the complete root output; no constancy of
the original open sums at a silent point-triple wall is asserted.
\end{proof}
```

## def:soft — DEFINE

reference/SM/sm-2-amplitude.tex:996–1015

```tex
\begin{definition}[soft insertion]\label{def:soft}
Let $P$ satisfy (G1), fix a vertex index $j$ and a vector $q\neq0$. The
\emph{soft insertion} of $q$ at $j$ is the family of $(n+1)$-gons
\[
P^{(j,q)}_\varepsilon=(\mu_1,\ldots,\mu_j,\ \mu_j+\varepsilon q,\ \mu_{j+1},\ldots,\mu_n),
\qquad\varepsilon>0,
\]
with the new vertex $\mu_*=\mu_j+\varepsilon q$ inserted immediately after
$\mu_j$; its edges are $\lt_{j-1}$, the \emph{soft edge} $\varepsilon q$, and
the \emph{return edge} $\lt_j-\varepsilon q$, the others unchanged. The
\emph{attachment signs} are
\[
\chi_-=\chi_{*,j,j-1}\bigl(P_\varepsilon\bigr)=-\sgn\det(\lt_{j-1},q),\qquad
\chi_+=\chi_{*,j,j+1}\bigl(P_\varepsilon\bigr)=-\sgn\det(q,\lt_j),
\]
the two equalities holding for every $\varepsilon>0$ (they are the turns at
the two ends of the soft edge, with the sign reversed). The vector $q$ is
\emph{admissible} if $\det(\lt_{j-1},q)\neq0$, $\det(q,\lt_j)\neq0$, and
$\det(q,\mu_k-\mu_j)\neq0$ for all $k\neq j$.
\end{definition}
```

## lem:soft-generic — PROVE

reference/SM/sm-2-amplitude.tex:1017–1052

```tex
\begin{lemma}[the soft family is generic]\label{lem:soft-generic}
Let $P$ be generic, $j$ a vertex, and $q$ admissible in
Definition~\ref{def:soft}. Put $M=\mu_j$, $A=\mu_{j-1}$,
$B=\mu_{j+1}$, $u=M-A$, $v=B-M$, and $\tau=\tau_j(P)$.
Write $M_\varepsilon=M+\varepsilon q$ and
$D_\varepsilon=v-\varepsilon q$. There is $\varepsilon_0>0$
such that, for every $0<\varepsilon<\varepsilon_0$:
\begin{enumerate}
\item[(i)] $P_\varepsilon=P^{(j,q)}_\varepsilon$ is generic,
and all these polygons lie in one chamber. The soft edge meets
other edges only at its incident endpoints.
\item[(ii)] Every original vertex other than $M$ retains its
original turn sign. The turns at $M$ and $M_\varepsilon$ are
$-\chi_-$ and $-\chi_+$, respectively. The unchanged edge
 directions are fixed, $D_\varepsilon\to v$, and
$\sgn\det(u,D_\varepsilon)=\tau$, while
$\sgn\det(D_\varepsilon,u)=-\tau$.
\item[(iii)] Identify each unchanged edge with its parent edge
and the return edge with the parent edge $E_j$. Every parent
crossing persists. Its point and its parameters on the corresponding
edges converge to the parent values. Inherited visits retain their
order along each directed edge, and the determinant sign of the
ordered edge directions at each inherited crossing is unchanged.
\item[(iv)] If $\chi_-=\chi_+=-\tau$ (same-sign sector), or
$\chi_-\ne\chi_+$ (mixed sector), these are all the crossings
and the Gauss word is the parent's Gauss word. If
$\chi_-=\chi_+=\tau$ (loop sector), there is exactly one
additional crossing $y$, between the return edge and $E_{j-1}$.
It tends to $M$. Its incoming-edge visit $a$ and return-edge
visit $b$ bound the oriented traversal arc from $a$ through
$M,M_\varepsilon$ to $b$, containing no other crossing visit.
Thus the two newborn visits are cyclically adjacent; deleting
 them gives the parent's Gauss word.
\end{enumerate}
\status{new (round~4: the geometric facts consumed by Theorem~\ref{thm:C-soft} exported as clauses (i)--(iv) --- turn signs, soft-edge contacts, inherited crossings with their parameters, order and direction-determinant signs, the unique newborn crossing and its short arc; adopted from the Codex proposal sm4\_round4\_exports\_v1, P-25-24, F120-GEOMETRY, re-read by the author; F-25-120; cleared by bench~A on SM5 (2026-09-06T00:32:58Z))}
\end{lemma}
```

reference/SM/sm-2-amplitude.tex:1053–1155

```tex
\begin{proof}
Retain the original names of vertices and edges, replacing only
$E_j$ by the soft and return edges. The positive parameter interval
may be shortened finitely many times in the argument.

First establish (G1). Original vertex triples are unchanged.
For distinct original indices $k,l\ne j$, the area determinant for
$(M_\varepsilon,\mu_k,\mu_l)$ tends to the nonzero determinant
for $(M,\mu_k,\mu_l)$. For $k\ne j$, the determinant for
$(M_\varepsilon,M,\mu_k)$ is
$-\varepsilon\det(q,\mu_k-M)$, nonzero by admissibility.
These exhaust the new triples. Finiteness gives one interval
on which (G1) holds and all signs are constant.

The soft edge lies within $\varepsilon|q|$ of $M$.
Every parent segment not incident to $M$ has positive distance
from $M$, by compactness and (G1) of $P$. Hence the soft edge
misses all such segments for small $\varepsilon$. It meets the
incoming edge only at $M$, since $\det(u,q)\ne0$, and the return
edge only at $M_\varepsilon$, since
$\det(q,D_\varepsilon)=\det(q,v)\ne0$. The return edge and the
unchanged edge following $B$ meet only at $B$: their directions
tend to the independent directions at the parent corner $B$.
All pairs of unchanged edges retain their parent intersections.

For each parent edge remote to $E_j$, compare it with the return
edge. A disjoint parent pair has positive compact distance;
the return segment converges uniformly at each affine parameter
to $E_j$, so that distance remains positive. No independence
of the directions is required for a disjoint pair. For a crossing
parent pair, the directions have nonzero determinant and both
intersection parameters lie in $(0,1)$. The intersection equations
form an invertible two-by-two linear system. Its coefficients
converge to the parent coefficients and its determinant remains
nonzero, so its inverse varies continuously. The two parameters
converge to the parent values and stay in $(0,1)$; the point
converges as well, and the ordered direction determinant keeps
its sign.

These are all return-edge pairs except the incoming edge
$E_{j-1}$. Put $T=\det(u,v)$, of sign $\tau$. The return
edge meets $E_{j-1}$ precisely when each supporting line
strictly separates the endpoints of the other segment; the
directions are independent since $\det(u,D_\varepsilon)\to T\ne0$.
For the incoming line the signed heights are
\begin{equation}\label{eq:soft-first-straddle}
\det(u,M_\varepsilon-A)=\varepsilon\det(u,q),\qquad
\det(u,B-A)=T.
\end{equation}
They are opposite exactly when $\chi_-=\tau$. For the return
line based at $M_\varepsilon$, the height of $M$ is
\begin{equation}\label{eq:soft-second-straddle}
\det(D_\varepsilon,M-M_\varepsilon)
=\varepsilon\det(q,v).
\end{equation}
The height of $A$ tends to $\det(v,-u)=T\ne0$, so has sign
$\tau$ throughout a sufficiently small interval. This pair of
heights is opposite exactly when $\chi_+=\tau$. Both tests
are required: their conjunction is exactly the loop sector.
There is no intersection of this pair in the other two sectors.
In the loop sector its supporting-line equations remain
invertible as $\varepsilon\to0$. At zero the unique intersection
is $M$, with incoming parameter one and return parameter zero.
Thus $y\to M$, and these two parameters tend to one and zero.

All parent crossing points are away from $M$, since (G1)
excludes a vertex on a nonincident edge, and they are pairwise
distinct by (G2). The finitely many inherited points therefore
remain pairwise distinct and away from $M$. The newborn, when
present, stays distinct from them after another shrink.
Every possible crossing has been enumerated. A concurrence of
three distinct edge interiors would involve pairwise remote
edges, since (G1) makes distinct adjacent interiors disjoint.
It would identify the points of two distinct unordered crossing
pairs, which was excluded. Hence (G2) holds. The connected
parameter interval now maps continuously into the labelled
generic locus, so its image lies in one labelled chamber and
hence one polygon chamber. This proves (i).

The turn determinants at $M$ and $M_\varepsilon$ are
$\varepsilon\det(u,q)$ and
$\varepsilon\det(q,D_\varepsilon)=\varepsilon\det(q,v)$;
Definition~\ref{def:soft} gives their signs $-\chi_-$ and
$-\chi_+$. At $B$, the incoming direction tends to $v$ and
the outgoing one is unchanged, so the old nonzero turn sign
persists. Every other old vertex except $M$ has unchanged
incident directions. Finally $\det(u,D_\varepsilon)\to T$
gives sign $\tau$, and antisymmetry gives $-\tau$ for the
opposite ordered pair. This proves (ii).

Distinct parent crossing parameters on each edge have positive
pairwise separations and positive distances from zero and one.
Their convergence preserves their order on the corresponding
edges, including every edge whose crossing points move.
This proves (iii). Without a newborn, concatenating these
edgewise visit lists recovers the parent's cyclic Gauss word.
With a newborn, its incoming visit is after all inherited visits
on the incoming edge, and its return visit is before all inherited
visits on the return edge. The intervening soft edge has no crossing.
Thus the arc from $a$ through $M,M_\varepsilon$ to $b$ has no
other crossing visit. Deleting $a,b$ leaves exactly the inherited
lists, proving (iv).
\end{proof}
```

## thm:A-soft — PROVE

reference/SM/sm-2-amplitude.tex:1157–1169

```tex
\begin{theorem}[soft theorem for $A_g$]\label{thm:A-soft}
Let $P$ be generic, $q$ admissible, and $\varepsilon_0$ as in
Lemma~\ref{lem:soft-generic}. For every root $g$ of $P_\varepsilon$ other than
the soft edge, with $g'$ the corresponding root of $P$ (the return edge
corresponds to $E_j$), there is $\varepsilon_1\in(0,\varepsilon_0]$ with
\begin{equation}\label{aspr:soft-law}
A_g(P_\varepsilon)=\frac{\chi_-+\chi_+}{2}A_{g'}(P)
\qquad(0<\varepsilon<\varepsilon_1).
\end{equation}
Equivalently, in the same-sign, mixed and loop sectors the multipliers are
$-\tau_j(P)$, $0$ and $\tau_j(P)$, respectively.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC mt:pruning, mt:soft-duplication (C017))}
\end{theorem}
```

reference/SM/sm-2-amplitude.tex:1170–1473

```tex
\begin{proof}
We prove the finite duplication identity used below, including its two
boundary cases. This proof uses the definitions of the boundary word,
gates, open sums and soft insertion. It does not use a wall law or root
independence. All formal arrays in the next two paragraphs are over
$\mathbb Q$; their near entries need not be geometric signs.

\emph{Finite transforms and freedom to choose a near array.}
For a linearly ordered list with boundary positions $0,\ldots,L$, define
\begin{equation}\label{aspr:Phi}
\Phi_{D,H}(X)_{ij}=
\sum_{\pi=(i=r_0<\cdots<r_s=j)}
\prod_{k=1}^{s-1}
\frac{D(r_{k-1},r_k,r_{k+1})-H(i,r_k,j)}2
\prod_{k=1}^sX_{r_{k-1},r_k}.
\end{equation}
Put $F_H=\Phi_{0,H}$, $G_D=\Phi_{D,0}$, and let $E_{ij}$ be $1$ when
$j=i+1$ and $0$ otherwise. The one-part composition contributes $X_{ij}$;
every other term uses only shorter intervals. Thus one solves
$\Phi_{D,H}(X)=Y$ uniquely in increasing interval length, by subtracting
the already determined nonunary terms from $Y_{ij}$. This gives a
polynomial inverse on the finite array space. The constructed solution
map is a right inverse; uniqueness applied to the target
$\Phi_{D,H}(X)$ makes it a left inverse too.

The following factorization holds for arbitrary near and far arrays:
\begin{equation}\label{aspr:factorization}
\Phi_{D,H}=F_H\circ G_D.
\end{equation}
Indeed, expand the right side using an outer composition of $[i,j]$ and
an inner composition of each outer part. Their ordered union is a refined
composition $\rho$, together with a subset of its interior cuts marked as
outer cuts. Conversely, that subset recovers the outer composition, and
restricting $\rho$ to each part recovers the inner compositions. These
operations are inverse, including empty or full outer-cut subsets and
one-part inner or outer compositions. At an outer cut $r_k$ the factor is
$-H(i,r_k,j)/2$. At a nonouter cut its immediate neighbors in $\rho$
are exactly its neighbors inside its inner part, so the factor is
$D(r_{k-1},r_k,r_{k+1})/2$. Each interior cut supplies one factor, and the
child-interval product is the refined product. Summing independently over
the outer-cut subset gives the product of their sums, which is
\eqref{aspr:Phi}.

Write $b=\Phi_{D,H}^{-1}(E)$ and $c=F_H^{-1}(E)$. Applying
\eqref{aspr:factorization} to the equation for $b$ gives
$F_H(G_D(b))=E$; uniqueness gives $G_D(b)=c$. Applying the same
factorization with $-H$ then gives
\begin{equation}\label{aspr:near-free}
\Phi_{D,-H}(b)=F_{-H}(c).
\end{equation}
Thus the complete root transform is independent of $D$ with $H$ fixed.
For geometric arrays
$D(x,y,z)=H(x,y,z)=\chi(a_z,a_y,a_x)$, the elementary gate identities
$d\Theta(-hd)=(d-h)/2$ and $d\Theta(hd)=(d+h)/2$ show that
$\Phi_{D,H}(b)=E$ is exactly the open-sum recursion, and its full
$\Phi_{D,-H}(b)$ coordinate is $A_g$, including the one-part root term.
The freedom in \eqref{aspr:near-free} concerns the complete transform;
it asserts no equality of individual auxiliary and geometric open sums.

\emph{The formal duplication problem.}
Take a core ordered list $z_0,\ldots,z_M$, $M\geq2$, and distinguish
$A=z_s$, where $0\leq s\leq M$. Insert a new occurrence $B$ immediately
after $A$. The collapse $r$ sends $B$ to $A$ and fixes the other
occurrences. Let $H^0$ be any core far array of signs, and let
$t(X)\in\{-1,1\}$ be arbitrary for each core occurrence $X\ne A$.
Assume the parent far array $H^1$ has the following entries, where order
relations refer to positions in the linear lists:
\begin{equation}\label{aspr:far-data}
\begin{array}{ll}
H^1\text{ on a triple not containing both }A,B
   &\text{is the pullback of }H^0,\\
H^1(X,A,B)=t(X)&(X<A),\\
H^1(A,B,Y)=t(Y)&(B<Y).
\end{array}
\end{equation}
Only the neighbors in the next display are read cyclically in the core:
\begin{equation}\label{aspr:neighbor-data}
\eta_-=t(z_{s-1\bmod(M+1)}),\qquad
\eta_+=t(z_{s+1\bmod(M+1)}),\qquad
k=\frac{\eta_-+\eta_+}{2}.
\end{equation}
We will prove that the full parent root output is $k$ times the core one.

Choose auxiliary near arrays as follows. On core triples with middle
occurrence $A$, set $D^0(X,A,Y)=t(X)$; on other core triples set $D^0=0$.
On parent triples not containing both $A,B$, pull back $D^0$, and set
\begin{equation}\label{aspr:near-data}
D^1(X,A,B)=t(X)\ (X<A),\qquad
D^1(A,B,Y)=t(Y)\ (B<Y).
\end{equation}
These are formal arrays, not a claimed chirotope. Keep the far arrays
fixed. Let $b^0=\Phi_{D^0,H^0}^{-1}(E^0)$, and propose the following
parent ordinary array:
\begin{equation}\label{aspr:ordinary-table}
\begin{array}{c|c}
\text{parent interval }I&b^1_I\\\hline
I\text{ not containing both }A,B&b^0_{r(I)}\\
{[A,B]}&1\\
{[A,Y]},\ B<Y&\dfrac{\eta_+-t(Y)}2\,b^0_{[A,Y]}\\
{[X,B]},\ X<A&\dfrac{\eta_--t(X)}2\,b^0_{[X,A]}\\
{[X,Y]},\ X<A<B<Y&k\,b^0_{[X,Y]}
\end{array}
\end{equation}
Consecutiveness of $A,B$ makes these cases exhaustive. Apart from the
explicit singleton $[A,B]$, the collapsed endpoints are distinct. We
verify $\Phi_{D^1,H^1}(b^1)=E^1$ on every interval before identifying
$b^1$ with the actual auxiliary ordinary solution.

\emph{Intervals without the duplicate and the singleton.}
On an interval not containing both occurrences, collapse is an
order-preserving bijection on vertices, compositions, gates and child
intervals. Thus its transform is the corresponding core $E^0$ entry,
which equals its parent $E^1$ entry. On $[A,B]$ the sole composition has
one part and value $1$, as required.

\emph{Intervals starting at $A$.}
Fix $[A,Y]$ with $B<Y$. For a core composition of $[A,Y]$, write $X$
for its first boundary after $A$. There are exactly two parent
presentations. Without a cut at $B$, its first child contains $A,B$ and
has multiplier $(\eta_+-t(X))/2$. With a cut at $B$, the first child is
the singleton $[A,B]$, and the rest is the core composition with its
first endpoint renamed $B$. Its new gate at $B$ has near entry $t(X)$
and far entry $t(Y)$. Removing the cut at $B$, when present, recovers
the core composition; its presence distinguishes the two inverse
expansions. All other children agree, the neighboring near gate pulls
$B$ back to $A$, and all other far entries are the stipulated pullbacks.
The sum of the two local multipliers is, for an ordinary top vertex,
\begin{equation}\label{aspr:first-ordinary}
\frac{\eta_+-t(X)}2+\frac{t(X)-t(Y)}2
=\frac{\eta_+-t(Y)}2,
\end{equation}
and for a root top vertex it is
\begin{equation}\label{aspr:first-root}
\frac{\eta_+-t(X)}2+\frac{t(X)+t(Y)}2
=\frac{\eta_++t(Y)}2.
\end{equation}
In each case $t(X)$ cancels, leaving a composition-independent multiplier
of the corresponding core transform. The ordinary transform vanishes
when the core has at least two leaves, since its $E^0$ entry is zero.
When the core has one leaf, $Y$ is the actual successor of $A$, so
$t(Y)=\eta_+$ and the ordinary multiplier itself vanishes. Thus every
such parent ordinary coordinate has its required zero value, including
the two-leaf parent interval.

\emph{Intervals ending at $B$.}
Fix $[X,B]$ with $X<A$. In a core composition of $[X,A]$, let $Y$
be the last boundary before $A$. Without a cut at $A$ the last child
contains the soft edge and has multiplier $(\eta_--t(Y))/2$.
With that cut it ends in the singleton $[A,B]$; the new gate has near
entry $t(Y)$ and far entry $t(X)$. Remove the cut $A$ when present
and rename the endpoint $B$ as $A$ to recover the core list. The cut's
presence distinguishes the two expansions. The neighboring near gate
pulls $B$ back to $A$ and all other factors agree. Consequently the
ordinary and root multipliers are, respectively,
\begin{equation}\label{aspr:last-ordinary}
\frac{\eta_--t(Y)}2+\frac{t(Y)-t(X)}2
=\frac{\eta_--t(X)}2,
\end{equation}
\begin{equation}\label{aspr:last-root}
\frac{\eta_--t(Y)}2+\frac{t(Y)+t(X)}2
=\frac{\eta_-+t(X)}2.
\end{equation}
For a core interval with at least two leaves its ordinary transform is
zero. For one leaf, $X$ is the actual predecessor of $A$, so
$t(X)=\eta_-$ and the multiplier is zero. This checks the other
two-leaf parent boundary as well.

\emph{Intervals strictly spanning $A,B$.}
Fix $[X,Y]$ with $X<A<B<Y$. Collapse every parent cut list, retaining
only one copy when both $A,B$ are cuts. If the resulting core
composition does not cut at $A$, it has exactly one child spanning $A$.
It has exactly one parent presentation, with neither $A$ nor $B$ a cut;
that child strictly spans the duplicate and has multiplier $k$.
All top gates pull back unchanged. This includes the one-part
composition: the proposed leading $b^1$ coordinate is being checked,
not assumed to satisfy a recurrence.

If the core composition cuts at $A$, let $L,R$ be its neighboring cuts
and put $a=t(L)$, $b=t(R)$ and $h=H^0(X,A,Y)$. Its core near entry at
$A$ is $a$. There are precisely three parent presentations:
\begin{equation}\label{aspr:three-presentations}
\begin{array}{c|c}
\text{cuts among }A,B&\text{exceptional child multiplier}\\\hline
B\text{ only}&(\eta_--a)/2\\
A\text{ only}&(\eta_+-b)/2\\
A\text{ and }B&1\quad([A,B]\text{ is a singleton})
\end{array}
\end{equation}
Collapse recovers the core composition, while its subset of cuts among
$A,B$ recovers the row; expanding according to each row is the inverse.
The fourth subset, neither cut, gives the preceding no-core-cut case
and cannot occur here. The neighboring gate at $L$ has right neighbor
$A$ or $B$, both pulling back to $A$; the neighboring gate at $R$
has the analogous left neighbor. Their near entries are unchanged.
The far entries at $A$ and $B$ both pull back to $h$, and all exterior
gates and remaining child factors agree with the core.

For an ordinary top, either one-cut row has the core gate $(a-h)/2$;
the two-cut row replaces it by $(a-h)(b-h)/4$. The two one-cut child
multipliers sum to $k-(a+b)/2$. After subtracting $k$ times the core
gate, the residual is therefore
\begin{equation}\label{aspr:ordinary-residual}
R_{\rm o}=-\frac{a+b}{2}\frac{a-h}{2}
               +\frac{(a-h)(b-h)}4.
\end{equation}
Factoring $(a-h)/4$ leaves $-(a+b)+(b-h)=-a-h$, so
\begin{equation}\label{aspr:ordinary-factor}
R_{\rm o}=\frac{(a-h)(-a-h)}4=\frac{h^2-a^2}{4}=0.
\end{equation}
The last equality uses exactly $a,h\in\{-1,1\}$.
For a root top the corresponding residual is
\begin{equation}\label{aspr:root-residual}
R_{\rm r}=-\frac{a+b}{2}\frac{a+h}{2}
               +\frac{(a+h)(b+h)}4.
\end{equation}
Factoring $(a+h)/4$ leaves $-(a+b)+(b+h)=-a+h$, so
\begin{equation}\label{aspr:root-factor}
R_{\rm r}=\frac{(a+h)(-a+h)}4=\frac{h^2-a^2}{4}=0.
\end{equation}
Thus both transforms equal $k$ times their respective core transforms
on every strictly spanning interval. Such a core interval has at least
two leaves, so its ordinary $E^0$ entry is zero. No relation among
different remote values of $t$ was used.

All interval cases have now verified
$\Phi_{D^1,H^1}(b^1)=E^1$. Finite triangular uniqueness proved above
identifies \eqref{aspr:ordinary-table} with the actual auxiliary
ordinary solution. The root transforms already checked therefore
compute the actual auxiliary root outputs. We did not assume that any
auxiliary binary open sum vanishes.

For the full interval, if $0<s<M$ the strictly spanning multiplier is
$k$. If $s=0$, the final endpoint $Y=z_M$ is the cyclic predecessor of
$A$, so $t(Y)=\eta_-$ and \eqref{aspr:first-root} gives $k$. If $s=M$,
the initial endpoint $X=z_0$ is the cyclic successor of $A$, so
$t(X)=\eta_+$ and \eqref{aspr:last-root} gives $k$. These are all
positions. Finally \eqref{aspr:near-free}, applied separately to the
parent and core, restores their geometric near arrays without changing
their complete root outputs. This proves the formal duplication identity.

\emph{Specialization to the soft polygon.}
Write $A=\mu_j$ and $B=A+\varepsilon q$, and let the parent have
$n+1$ vertices, so the fixed core $P$ has $n\geq3$ vertices. Every
parent determinant not containing both $A,B$ either is a core
determinant or replaces $A$ by $A+\varepsilon q$ in one. For example,
bilinearity gives
\begin{equation}\label{aspr:det-clearance}
\det(X-A-\varepsilon q,Y-A-\varepsilon q)
=\det(X-A,Y-A)-\varepsilon\det(q,Y-X).
\end{equation}
The potential quadratic term vanishes because $\det(q,q)=0$;
alternation gives the same bound when $A$ is in another position.
The core has finitely many nonzero distinct-triple determinants, so
their absolute values have a positive minimum $\delta$. The finitely
many coefficients $\det(q,Y-X)$ have a finite maximum absolute value
$K$. Choose a common positive tail with $\varepsilon K<\delta$ when
$K>0$; if $K=0$, no restriction is needed. On this tail every such
parent sign equals its pulled-back core sign. All core edges have a
positive minimum length; shrinking further if necessary also keeps
the return edge $\widetilde\lambda_j-\varepsilon q$ nonzero. Take this
tail inside $(0,\varepsilon_0)$.

For every other core vertex $X$, set
\begin{equation}\label{aspr:geometric-t}
t(X)=\chi(B,A,X)=-\operatorname{sgn}\det(q,X-A).
\end{equation}
Indeed $A-B=-\varepsilon q$ and $X-B=X-A-\varepsilon q$, so their
determinant is $-\varepsilon\det(q,X-A)$. Admissibility makes it
nonzero. For a boundary triple $(X,A,B)$ the far entry is $t(X)$;
for $(A,B,Y)$ it is $\chi(Y,B,A)=\chi(B,A,Y)=t(Y)$ by a cyclic
permutation. Together with the common-tail calculation, these are
exactly \eqref{aspr:far-data}.

The two cyclic neighboring values are the stated attachments. Writing
$u=\mu_j-\mu_{j-1}$ and $v=\mu_{j+1}-\mu_j$, the predecessor gives
\begin{equation}\label{aspr:attachment-minus}
t(\mu_{j-1})=-\operatorname{sgn}\det(q,-u)
             =-\operatorname{sgn}\det(u,q)=\chi_-;
\end{equation}
the equality follows from bilinearity and antisymmetry. The successor
gives directly
\begin{equation}\label{aspr:attachment-plus}
t(\mu_{j+1})=-\operatorname{sgn}\det(q,v)=\chi_+.
\end{equation}

Cut the boundary word immediately after the specified nonsoft root.
The occurrences $A,B$ are consecutive in this linear word. If the root
is the incoming edge ending at $A$, the word is soft-first ($s=0$).
If it is the return edge starting at $B$, the word is soft-last
($s=M$). Every other nonsoft root gives the strictly spanning case.
Here the core word has $M=n-1\geq2$, so the formal result applies even
to a triangle core; no two-gon amplitude is invoked. Collapse of $B$
to $A$ retains each other root's physical endpoints, except that the
return edge becomes the core edge $E_j=[\mu_j,\mu_{j+1}]$. Thus the
collapsed word is exactly the boundary word of $(P,g')$, including
cyclic wraparound. The soft root itself would put $A,B$ at opposite
ends of the cut word and has been excluded throughout.

The duplication identity now gives \eqref{aspr:soft-law} with
$k=(\chi_-+\chi_+)/2$. Evaluating this expression on the three
attachment-sign patterns gives the sector multipliers in the
statement. Neither the crossing classification of the soft family
nor a rotation formula for it was needed in this calculation.
\end{proof}
```

## prop:A-reversal — PROVE

reference/SM/sm-2-amplitude.tex:1508–1519

```tex
\begin{proposition}[reversal and cyclic shift]\label{prop:A-reversal}
For every polygon satisfying (G1) and every root $g$:
\begin{enumerate}
\item[(i)] $A_g(\sigma P)=A_{g+1}(P)$.
\item[(ii)] With $\overline P_i=\mu_{2-i}$ and $g^\vee=1-g$,
\begin{equation}\label{arpr:reversal}
A_{g^\vee}(\overline P)=(-1)^nA_g(P).
\end{equation}
\end{enumerate}
All vertex and edge indices in this statement are read modulo $n$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC mt:covariance; appendix\_v7 eq:treecuts (C017; F-25-20))}
\end{proposition}
```

reference/SM/sm-2-amplitude.tex:1520–1574

```tex
\begin{proof}
The relabellings preserve (G1), because they permute distinct vertex
triples. Put $N=n-1$. For the shift, the boundary vertex at position
$k$ of $(\sigma P,g)$ is $\mu_{g+2+k}$, which is precisely position
$k$ of $(P,g+1)$. Every interval composition, near sign and far sign
is therefore identical. Induction on interval length in the open-sum
recursion gives equality of all open sums, and the complete root sums
agree, proving (i).

For reversal, edge $g^\vee$ runs from
$\mu_{2-g^\vee}=\mu_{g+1}$ to
$\mu_{1-g^\vee}=\mu_g$, the reverse of the original physical root.
If $a_k=\mu_{g+1+k}$ is the original boundary word and $a'_k$ the
word at this reversed root, then
\begin{equation}\label{arpr:boundary}
a'_k=\overline\mu_{g^\vee+1+k}
     =\mu_{1-g^\vee-k}=\mu_{g-k}=a_{N-k}
\qquad(0\leq k\leq N).
\end{equation}
In the last equality the indices differ by $n$.

Use the tree expression of Lemma~\ref{lem:treesum-trees}.
Reflect the order of the children at every internal vertex of a
rooted plane tree, and relabel boundary positions by $k\mapsto N-k$.
This is an involution on the tree set: the root is still allowed one
or more children, ordinary vertices still have at least two, and leaf
order is exactly the reversed boundary order. A composition
$(r_0<\cdots<r_s)$ becomes
$(N-r_s<\cdots<N-r_0)$ on the reflected interval. At corresponding
cuts its ordered near triple reverses its first and last entries;
the same is true of its ordered far triple. Thus $d'=-d$ and $h'=-h$.
The product $h'd'=hd$, so either gate retains its step-function
argument and acquires precisely one minus sign:
\begin{equation}\label{arpr:gate}
d'\Theta(\mp h'd')=-d\Theta(\mp hd).
\end{equation}
This holds for both ordinary and root gates, including zero factors.
The separate factor $(-1)$ for each ordinary internal vertex is
unchanged by the involution.

If the tree has $I$ internal vertices and $N$ leaves, its number of
child edges is $I+N-1$. The sum of the arities over internal vertices
counts each child edge once. A vertex of arity $s$ contributes $s-1$
gates, so the total number of gates is
\begin{equation}\label{arpr:gate-count}
\sum_{v\text{ internal}}(s_v-1)
=(I+N-1)-I=N-1=n-2.
\end{equation}
A unary root contributes zero to this count, so its allowed presence
creates no exception. Every corresponding tree term therefore differs
by $(-1)^{n-2}=(-1)^n$. Summing over the involution gives
\eqref{arpr:reversal}. For $n=3$ the same count is one; no exceptional
base convention is required. Neither part proves or assumes root
independence on a fixed polygon.
\end{proof}
```

## def:decomposition — DEFINE

reference/SM/sm-3-statesum.tex:9–12

```tex
\begin{definition}[decomposition]\label{def:decomposition}
A \emph{decomposition} of $P$ is an independent set $S\in\Ind(G_P)$ of
crossings (Definition~\ref{def:interlace}): no two crossings of $S$ interlace.
\end{definition}
```

## def:smoothing — DEFINE

reference/SM/sm-3-statesum.tex:14–27

```tex
\begin{definition}[oriented smoothing and subpolygons]\label{def:smoothing}
Let $S\in\Ind(G_P)$. Cutting the traversal circle $\Gamma(P)$ at the two
visits of each $x\in S$ and reconnecting the arc arriving at one visit of $x$
to the arc leaving the other visit of $x$ (for both visits) partitions
$\Gamma(P)$ into closed cycles; the \emph{subpolygons} (or \emph{carriers})
of $S$ are the closed polygonal curves in $\RR^2$ traced by these cycles. Each
subpolygon $Q$ is a closed polygon whose corners are the vertices of $P$ it
passes through and the crossing points of $S$ it turns at (its
\emph{smoothing corners}); at a smoothing corner between $E_i$ and $E_j$ it
arrives along one of $\lt_i,\lt_j$ and leaves along the other. The
\emph{crossings of $Q$} are the crossings $x\in X(P)\setminus S$ both of whose
visits lie on $Q$; their number is $m_Q$. A crossing in $N(S)$ has its two
visits on different subpolygons and is a crossing of no subpolygon.
\end{definition}
```

## conv:selected-visits — DEFINE

reference/SM/sm-3-statesum.tex:29–39

```tex
\begin{convention}[ownership of a selected visit]\label{conv:selected-visits}
At a selected crossing with traversal visits $a,b$, reconnect the incoming
arc at $a$ to the outgoing arc at $b$, and the incoming arc at $b$ to the
outgoing arc at $a$. Assign the original visit $a$ to the resulting cycle
containing the incoming one-sided arc at $a$; assign $b$ by the analogous
rule. Unselected visits retain their ordinary traversal ownership.
Thus a selected visit is assigned to one abstract carrier, even though
the two carriers through that smoothing site have the same point of the
plane in their polygonal images. This is the \emph{incoming-visit convention}.
It specifies endpoint ownership only; the geometric reconnection is unchanged.
\end{convention}
```

## lem:carriers — PROVE

reference/SM/sm-3-statesum.tex:54–93

```tex
\begin{lemma}[subpolygons and their visit assignment]\label{lem:carriers}
Let $P=(\mu_1,\ldots,\mu_n)$, $n\geq3$, be a generic polygon: for every
three distinct indices the vertex determinant is nonzero, and no three
edge interiors concur.
Use one-based cyclic indices, directed edges
$E_i=[\mu_i,\mu_{i+1}]$, directions $d_i=\mu_{i+1}-\mu_i$, and turns
$\tau_i=\operatorname{sgn}\det(d_{i-1},d_i)$.
Let $X(P)$ be its set of transverse crossings of remote edges. The
traversal circle has two visits for each crossing, in the order of the
oriented traversal. Crossings interlace when their two pairs of visits
alternate on that circle. Let $S\subseteq X(P)$ be independent: no two
elements of $S$ interlace. Perform the above oriented reconnections,
tracing the resulting cycles by inherited straight subsegments, with
corners at original vertices and selected smoothing sites. Call these
polygonal cycles the carriers, and use the incoming-visit convention.
Then:
\begin{enumerate}
\item[(i)] There are exactly $|S|+1$ carriers, independent of the order
of reconnections. Each carrier traverses the visits assigned to it in
their cyclic order inherited from the original traversal circle.
The two visits of a selected crossing belong to different carriers.
\item[(ii)] Every carrier has nonzero edges, at least three corners,
and no antiparallel consecutive directions. All its corner turns are
nonzero. At an original vertex $i$ the turn sign is $\tau_i$.
At a selected crossing of $E_i,E_j$, the two smoothing corners have
signs $\operatorname{sgn}\det(d_i,d_j)$ and
$\operatorname{sgn}\det(d_j,d_i)$, one left and one right.
\item[(iii)] A carrier's self-intersections are exactly the unselected
crossings both of whose visits are assigned to it. They are transverse,
none is a corner, and no carrier has a triple point. An unselected
crossing interlacing some element of $S$ has its visits on different
carriers; an unselected crossing interlacing no element of $S$ has
both visits on one carrier.
\item[(iv)] The assignment of \emph{all} crossing visits is noncrossing.
There are no four distinct visits $u_1$, $u_2$, $u_3$, $u_4$ in that cyclic order
with $u_1,u_3$ on one carrier and $u_2,u_4$ on a different carrier.
This includes selected visits under the stated convention.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T19:48:09Z; transcribed from CV lem:carriers, lem:carrierword (d7\_anchors, d6\_vertexedge); RC def:canonical-total) for clauses (i)--(iii); clause (iv), ``including every selected visit'', is a new argument of round~1 with no frozen-source locator, cleared by bench~A on SM4 (2026-09-05T19:48:09Z) and listed in Section~\ref{sec:newlist} (F-25-133, F-25-134; with Convention~\ref{conv:selected-visits}, C005)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:95–240

```tex
\begin{proof}
\emph{Finite successor model.}
Mark the traversal circle at every original vertex and every crossing
visit. This is a nonempty finite cyclic list, even if there are no
crossings. Each consecutive pair bounds an oriented straight
subsegment. Write $\rho$ for the successor permutation of the list.
At the two distinct marked visits $a,b$ of a selected crossing, replace
the two arrows by
\begin{equation}\label{carrierpr:successors}
\rho_S(a)=\rho(b),\qquad \rho_S(b)=\rho(a).
\end{equation}
At an unselected marked point keep its outgoing arrow. Selected
crossings have disjoint pairs of marked visits. Thus these swaps
operate on disjoint outgoing slots, commute, and give a permutation
$\rho_S$ independent of their order. Its cycles are precisely the
oriented reconnections: the node $a$ retains its incoming arc and
leaves along the old outgoing arc at $b$. This also implements the
incoming-visit convention explicitly.

\emph{Splitting and induced order.}
We prove by induction as selected pairs are processed that the cycles
traverse their marked nodes in the cyclic order inherited from the
original list, and that the two endpoints of each unprocessed selected
pair lie on one current cycle. Initially there is the one original
cycle. Suppose a current selected pair has endpoints $a,b$ on a cycle
$L$. In its inherited cyclic order write that cycle as
\begin{equation}\label{carrierpr:split-list}
(a,A_1,\ldots,A_p,b,B_1,\ldots,B_q).
\end{equation}
Either of the lists between the endpoints may be empty. Swapping the
outgoing arrows gives exactly the two cycles
\begin{equation}\label{carrierpr:split-cycles}
(a,B_1,\ldots,B_q),\qquad (b,A_1,\ldots,A_p).
\end{equation}
Each retains the induced cyclic order. Every remaining selected pair
has both endpoints in one of the two open arcs between $a,b$ on the
original circle, since it does not interlace this selected pair.
If it was on $L$, its two endpoints therefore enter the same new cycle;
if it was on another cycle, it is unaffected. This proves the inductive
claims and shows that every selected reconnection splits one cycle
into two, never merging cycles. Hence the final count is $|S|+1$.
The endpoints $a,b$ enter different cycles in
\eqref{carrierpr:split-cycles}, and all later operations only split.
They remain on different final carriers. This proves (i).

\emph{Noncrossing away from selected endpoints.}
The preceding induction also gives noncrossing ownership of the
unmarked open traversal arcs. Here are the details, including arbitrary
points on those arcs. For no selected pairs there is one carrier, so
there is nothing to check. In a splitting step the one old carrier
$L$ is divided between the two open arcs cut out by $a,b$, with the
endpoints omitted for this paragraph. All other carrier sets are
unchanged. If two new carrier blocks alternated with four points,
and at most one of them came from splitting $L$, the same four points
would violate the previous partition's noncrossing property, using
$L$ for that new block. If both came from splitting $L$, their points
would alternate between the two open arcs of $a,b$. The four disjoint
cyclic transitions between these four points would then each contain
one of $a,b$. Two endpoints cannot lie in four disjoint transitions.
This is impossible. Induction proves noncrossing for all traversal
points away from preimages of $S$.

\emph{Including every selected visit.}
Assume four distinct crossing visits violated (iv). Move any of these
that are selected a sufficiently small distance backwards along the
original traversal circle; leave the unselected ones fixed. There are
finitely many selected visits and four distinct chosen points, so the
distances can be chosen positive and small enough that no selected
endpoint is passed and the cyclic order of the four points is unchanged.
By the incoming-visit convention, each moved point has exactly the
carrier assignment of its original selected visit. Now all four points
avoid preimages of $S$ and give the forbidden alternation of the
previous paragraph. This contradiction proves the all-visits assertion.

\emph{Ownership of unselected crossings.}
Let $x\notin S$. If it interlaces no selected pair, its two endpoints
start on the same original cycle and remain together after every split:
at a split whose carrier contains them, noninterlacement puts them in
one open arc of that selected pair. Thus they end on one carrier.
If $x$ interlaces a selected pair $s$, process $s$ first, which is
permitted by order independence. Its split puts the two visits of $x$
on different cycles. Later reconnections only split, so they can never
be reunited. This proves both ownership assertions in (iii).

\emph{Nonzero segments and corner signs.}
Genericity makes all original vertices distinct: coincident vertices
would give a zero triple with any third index. It also makes every
edge nonzero and every original turn nonzero. No vertex lies on a
nonincident closed edge: such an incidence would give a zero triple.
Two remote edges meeting at a point have neither endpoint there, and
their directions cannot be parallel, since coincident lines would
give collinear original vertices. Thus their intersection is an
interior transverse crossing. Distinct crossings have distinct points,
as a coincident pair of crossing points would lie on at least three
edge interiors, contrary to genericity.

Consequently consecutive marked points on an original edge are
distinct in the plane, with strictly increasing parameters; their
connecting subsegment has positive length. At a selected node $a$,
the point of the plane agrees with its twin $b$, but its new successor
is the old successor of $b$, which is at positive distance along
$b$'s outgoing subsegment. Equation~\eqref{carrierpr:successors}
does not insert a zero segment from $a$ to $b$.
Omitting unselected crossing marks joins successive positive subsegments
of the same original edge in the same direction. Hence every edge
between consecutive carrier corners is nonzero and inherits an
original oriented direction up to a positive scalar.

At an original vertex $i$ no reconnection occurs. The incoming and
outgoing carrier directions are positive multiples of $d_{i-1}$ and
$d_i$, so their determinant has sign $\tau_i$. At a selected crossing
of $E_i,E_j$, the node assigned by incoming $E_i$ leaves along $E_j$;
its determinant is a positive multiple of $\det(d_i,d_j)$. The twin
node has a positive multiple of the opposite determinant
$\det(d_j,d_i)=-\det(d_i,d_j)$. Transversality makes these nonzero,
with opposite signs. These are all corner types. In particular none
is antiparallel or flat.

Each cycle contains a corner: a cycle having only unselected visits
would follow the unchanged original successor around the full parent
traversal, which contains original vertices. Thus its nonzero segments
form a closed polygonal cycle with the indicated corners. One nonzero
segment cannot close. A closed polygon of exactly two nonzero segments
has opposite segment vectors and hence antiparallel corners, already
excluded. Every carrier therefore has at least three corners. This
proves (ii), including membership in the regular locus.

\emph{Exactly the retained self-intersections.}
Every traced carrier segment is an original straight subsegment with
its inherited parameter direction. Distinct traversal subsegments of
one original edge have disjoint interiors, so no overlap is introduced.
Original adjacent edges meet only at their common original vertex,
which has one traversal occurrence and lies on one carrier. All other
possible intersections are original crossings. At a selected crossing
the two incoming visits belong to different carriers by (i); a single
carrier therefore passes through that smoothing point only once.
An unselected crossing is visited twice by a carrier precisely when
both of its original visits are assigned to that carrier. Otherwise
it is a meeting of two distinct carriers, not a self-intersection of
either. Every retained self-crossing is still transverse with its
unchanged straight germs. It is not a corner because original vertices
and selected crossing sites are all distinct from it. No carrier can
have a triple point, since no point of the parent has three traversal
preimages and each selected site is used only once by a given carrier.
These statements prove the remaining assertions of (iii).
\end{proof}
```

## def:uniform — DEFINE

reference/SM/sm-3-statesum.tex:242–248

```tex
\begin{definition}[uniform subpolygons; retained data]\label{def:uniform}
A subpolygon $Q$ is \emph{uniform} if all its turns have one sign and
\emph{mixed} otherwise. A decomposition $S$ is \emph{uniform} if all its
subpolygons are. For a subpolygon $Q$ write $r_Q=\rot(Q)$
(Lemma~\ref{lem:rot}, applicable by Lemma~\ref{lem:carriers}), $m_Q$ for its
number of crossings, and $\ell_Q$ for its number of left turns.
\end{definition}
```

## def:positive-lift — DEFINE

reference/SM/sm-3-statesum.tex:325–335

```tex
\begin{definition}[positive crossing; positive lift]\label{def:positive-lift}
An oriented link diagram in the plane is a finite collection of closed
oriented curves with finitely many transverse double points, no triple points,
and at each double point a choice of the \emph{over} strand. A double point
with over-strand direction $u_{\rm o}$ and under-strand direction $u_{\rm u}$
is \emph{positive} if $\det(u_{\rm o},u_{\rm u})>0$ and \emph{negative}
otherwise. The \emph{positive lift} of a subpolygon $Q$ is the oriented knot
diagram whose curve is $Q$, whose double points are the crossings of $Q$, and
in which at every double point the over strand is chosen so that the crossing
is positive. Its writhe (the sum of crossing signs) is $m_Q$.
\end{definition}
```

## def:gauss-record — DEFINE

reference/SM/sm-3-statesum.tex:352–370

```tex
\begin{definition}\label{def:gauss-record}
Let $\gamma:C\to S^2$ be an actual generic immersion of an oriented
circle in an oriented sphere, with over/under choices at its transverse
double points. Its finite crossing-occurrence set $M$ has forward successor
$s$, pairing involution $\tau$ without fixed points, an over/under bit at
each occurrence, and crossing signs
\begin{equation}\label{eq:gauss-cross-sign}
 \sigma(c)=\sgn\det(u_{c,O},u_{c,U}).
\end{equation}
A named record isomorphism is a bijection $\Phi:M\to M'$ preserving
successor, pairing, over/under bits and these signs. The parametrizing
circles are oriented; the finite bijection must preserve their cyclic
orders. It does not prescribe a map at every unmarked parameter and
does not permit traversal reversal. After a finite subdivision we choose
an orientation-preserving piecewise-linear circle map
$\overline\Phi:C\to C'$ extending $\Phi$: on each interval between
successive marked points use the positive affine map in oriented interval
coordinates. If $M$ is empty, choose any positive circle parametrization.
\end{definition}
```

## lem:gauss-two-discs — PROVE

reference/SM/sm-3-statesum.tex:428–436

```tex
\begin{lemma}[Constructive polygonal two-disc theorem]
\label{lem:gauss-two-discs}
A simple polygonal circle in the oriented sphere has exactly two
complementary regions, and both closures are PL discs. Finite prescribed
positive PL boundary maps between such discs extend to positive PL disc
maps. A continuous positive boundary map also extends to a topological
disc map. The statement includes the exterior region.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC fd:pl-discs (C016))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:437–542

```tex
\begin{proof}
Here is a finite triangulation and disc construction, so no Jordan or
Schoenflies conclusion is being assumed. Remove one point off the curve
and put the polygon inside a large rectangle. Extend its finitely many
edge lines, and also lines through its vertices in a generic auxiliary
direction, across that rectangle. The arrangement has convex cells;
subdivide boundary segments at all intersections and triangulate each
convex cell by a fan from an interior point. Collinear redundant vertices
are simply retained as subdivisions, never used to claim a strict ear.
The circle is now a simple edge cycle $C$ in a finite triangulation of
the rectangle. Cap the rectangular boundary by a second triangulated disc.
This cap represents the actual one-point-compactified exterior: from
the rectangle's center, write its boundary as $r=R(u)$ and map an
exterior point $ru$ to $(R(u)/r)u$, with infinity sent to zero.
This has a continuous radial inverse and identifies the exterior with a
disc. The two-disc model is a triangulated sphere by radial identification
with the upper and lower hemispheres. The original exterior is part of this same
triangulation, not just a collar of $C$.

Work with chains over $\mathbb F_2$. If the sphere triangulation has
$V,E,F$ cells, then $V-E+F=2$. This follows first for the two-disc
rectangle model and is unchanged by subdividing an edge, adding a vertex
inside a face, or drawing a diagonal; these are precisely the finite
arrangement and fan subdivisions just used. The vertex-edge graph and
the face-adjacency graph are connected. The incidence map on edges has
rank $V-1$, since a spanning tree gives $V-1$ independent boundary
columns and every edge boundary has even coordinate sum. Hence its
cycle space has dimension $E-V+1=F-1$. The face-boundary map has
kernel exactly the two constant face assignments: across every edge a
boundary-zero face assignment has equal coefficients on its two adjacent
faces, and the face-adjacency graph is connected. Its rank is therefore
$F-1$. Face boundaries are cycles, so every cycle, in particular $C$,
is the boundary of a face assignment, unique up to complement.

Color faces by that assignment. Across an edge of $C$ the colors differ;
across any other edge they agree. At a vertex of $C$ its two cycle
edges divide the cyclic triangle fan into exactly two consecutive fans,
one of each color. At every other vertex all incident faces have one
color. Thus each color closure is a compact triangulated surface whose
boundary is $C$, with no pinch point. Following $C$ through those local
fans shows that all boundary-adjacent faces of a given color lie in one
connected face component. Any further face component would have no
boundary edge and hence no adjacency to its complement, contradicting
connectedness of the full dual graph. Thus there are exactly two
connected color regions, $R_0,R_1$, each with its single boundary $C$.

We next prove, rather than assume, that each is a disc. For any connected
triangulated surface $R$ with nonempty boundary, take a spanning tree
of its triangle-adjacency graph, rooted at a triangle having a boundary
edge. Remove that triangle across that boundary edge, and then remove
each triangle after its parent, across their common edge. At its turn
the chosen edge is free: the parent triangle is gone and no third
triangle is incident to that edge. A triangle and its free edge collapse
onto its other two edges. This preserves connectedness and Euler
characteristic and leaves, after finitely many steps, a connected graph
$K$. Consequently $\chi(R)=\chi(K)=1-\beta_1(K)\leq1$.
Since the two regions meet in $C$ and $\chi(C)=0$, cell counting gives
$\chi(R_0)+\chi(R_1)=2$. Both inequalities are therefore equalities,
so both residual graphs are trees.

For completeness these collapses also construct disc parametrizations,
not only a homotopy equivalence. Maintain a small closed regular
neighbourhood of the current collapsed complex, with vertex polygons
and edge rectangles. A free-triangle collapse changes its neighbourhood
by removing a boundary notch, which gives a boundary-compatible PL
homeomorphism. In the standard triangle
$x,y\geq0$, $x+y\leq1$, whose free edge is $x+y=1$, use the
neighbourhood of the other two edges
\begin{equation}\label{eq:gauss-triangle-notch}
 \{x,y\geq0, x+y\leq1,\ \min(x,y)\leq\varepsilon\},
 \qquad 0<\varepsilon<1/2.
\end{equation}
Its new boundary path runs from $(1,0)$ through
$(1-\varepsilon,\varepsilon),(\varepsilon,\varepsilon),
(\varepsilon,1-\varepsilon)$ to $(0,1)$.
Subdivide the old free edge at the intersections of the rays from
$(0,0)$ through those three corners. Map the resulting triangle fan
affinely to the corresponding fan of the notched region, fixing the two
retained edges pointwise. Every triangle map has positive determinant,
the fans meet on their common radial edges, and the images cover the
notched region. Thus the map is a PL homeomorphism, fixed where that
triangle joins the rest. In thin edge rectangles use the same product
map, with identity on the outer attaching boundary. This proves by
induction the stated regular-neighbourhood invariant for every free
collapse. Choose widths successively smaller than the positive distances
between disjoint cells; finiteness makes all choices compatible.

A regular neighbourhood of a tree is a disc by an explicit leaf
induction. One vertex gives a polygonal disc. Adding a leaf attaches
one edge rectangle and one leaf disc along a single boundary interval.
Triangulate that rectangle and disc into a fan along the interval; the
same positive fan maps identify their union with a longer boundary
collar. Thus each step is a disc and records its boundary parametrization.
Reverse the finite free-collapse maps to parametrize $R_0$ and $R_1$.
This completes both the interior and exterior constructions.

Finally identify two resulting discs with convex polygonal unit discs.
Subdivide their boundaries until a specified positive PL boundary map
is affine on each segment, choose one interior vertex in each, and map
the corresponding boundary fans affinely, interior vertex to interior
vertex. Their cyclic order makes all determinants positive. For a
continuous positive boundary map instead use radial coordinates and
$(r,u)\mapsto(r,b(u))$; the inverse uses $b^{-1}$ and continuity at
the center follows from the radial bound. This proves both extension
claims with the prescribed boundary, not just an unlabelled disc type.
\end{proof}
```

## def:flat-carriers — DEFINE

reference/SM/sm-3-statesum.tex:788–803

```tex
\begin{definition}[carriers of the flat configurations]\label{def:flat-carriers}
Under the hypotheses of Lemma~\ref{lem:flat-sides}, identify the crossing
visits of the two sides, of the centre $P(0)$ and of the deletion
$P(0)\setminus j$ through the common cyclic Gauss word of that lemma's
clauses (ii) and (iii), and fix an independent set $S$ in their common
interlacement graph. In each of these four configurations mark the
traversal circle at every original vertex and every crossing visit,
exchange the two outgoing successors at the two visits of every selected
crossing --- the reconnection of Definition~\ref{def:smoothing} with
Convention~\ref{conv:selected-visits} --- and trace the resulting oriented
closed cycles by the inherited straight subsegments. These oriented closed
polygonal cycles are the \emph{carriers} of $S$ in that configuration. On
the two generic sides they are the carriers of
Definition~\ref{def:smoothing}; at the centre and on the deletion the same
words define them, no genericity being assumed.
\end{definition}
```

## cor:flat-carriers — PROVE

reference/SM/sm-3-statesum.tex:805–836

```tex
\begin{corollary}[flat carrier data]\label{cor:flat-carriers}
Under the hypotheses of Lemma~\ref{lem:flat-sides}, fix an independent
set $S$ in the common interlacement graph and form the carriers of $S$ on
both sides, at the centre and on the deletion
(Definition~\ref{def:flat-carriers}). Then:
\begin{enumerate}
\item[(i)] The carriers correspond under their named traversal arcs.
Exactly one contains $\mu_j$. The central copy of that carrier differs
from its deletion copy only by the positive-flat subdivision at $\mu_j$;
every other central carrier is unchanged by deletion. Every carrier
has nonzero segments and no antiparallel corner; except for that one
central zero turn, all corner turns are nonzero.
\item[(ii)] Corresponding carriers have the same retained self-crossing
visits, pairing, signs and positive over/under bits. They have the same
signed rotation and hence the same absolute rotation. Every corresponding
corner away from $\mu_j$ has the same turn sign on both sides and in
the deletion. The extra corner at $\mu_j$ is right on the right side
and left on the left side.
\item[(iii)] Define a carrier's selector to be $1$ if all its turns are
right, $(-1)^c$ if all its $c$ turns are left, and $0$ if its turns are
mixed. For the carrier through $\mu_j$, let $W_{\rm right}$,
$W_{\rm left}$, and $W_{\rm del}$ be these selectors on the two sides
and on the deletion. Then
\begin{equation}\label{flatpr:selector-identity}
W_{\rm right}-W_{\rm left}=W_{\rm del}.
\end{equation}
All other corresponding carrier selectors agree.
\end{enumerate}
These assertions concern geometric and combinatorial carrier data.
They make no assignment of a state-sum value at the flat centre.
\status{proved (refereed: bench A, 2026-09-05T23:45:25Z; transcribed from CV lem:flatdata, carrier data (P-25-3, C007); round~3: the carriers are those of Definition~\ref{def:flat-carriers}, F-25-102; round~4: clause~(ii)'s rotation sentence covers the centre copy as well, which CV lem:flatdata(iv) omits --- a broadening of this document, refereed sound by bench~A (F-25-141))}
\end{corollary}
```

reference/SM/sm-3-statesum.tex:838–913

```tex
\begin{proof}
The common cyclic word identifies the visits and the successor
permutation before smoothing. Exchanging the same selected successors
in that permutation gives the same cycles afterwards. This is an
explicit correspondence and needs no ambient knot-equivalence theorem.
Noninterlacement ensures that each selected pair separates two carriers:
cut at one selected pair; each other selected pair lies entirely on one
of the two resulting arcs, since it does not interlace that pair.
Apply the same argument recursively on those arcs. It gives $|S|+1$
cycles, with the two reconnections at any selected crossing on distinct
cycles. Thus no carrier visits a selected smoothing point twice.

An original vertex appears once on the parent traversal; selected
crossing points are distinct and avoid all vertices. The subsegments
between successive vertices or crossing visits therefore have positive
length. The occurrence $\mu_j$ lies on exactly one cycle. Its incoming
and outgoing directions at the centre are positive multiples by
\eqref{flatpr:fusion}; removing it merely fuses those segments.
At another original corner the determinant is a positive multiple of
the nonzero original turn determinant. At a selected smoothing corner
it is a positive multiple of either $\det(d_e,d_f)$ or
$\det(d_f,d_e)$ at that transverse crossing. These exhaust the corners.
They prove the stated nonzero turns and absence of antiparallel corners,
including in the deletion. A deletion carrier has at least three
corners: one nonzero segment cannot close, and a closed two-segment
polygon has antiparallel directions. No such deletion carrier occurs.

An unselected crossing is a self-crossing of a carrier exactly when
both its visits belong to that cycle. The common successor permutation
preserves this condition and the two visits' inherited positive
over/under bits. Tracing inherited straight subsegments introduces no
other self-intersection: every intersection was already a parent
crossing, and a selected crossing lies on two different carriers, as
proved above. The nonzero determinants just listed have constant
signs on a smaller interval. Replacing either old incident direction
by the fused direction multiplies the relevant determinant by a
positive scalar. Hence all surviving corner signs and all retained
crossing data agree among the configurations in (ii).

For completeness, the rotation comparison uses limits of every affected
turn, not equality of finite-parameter angles. For a closed polygonal
carrier with nonzero segments and no antiparallel consecutive directions,
let $\vartheta_k\in(-\pi,\pi)$ be its principal turns. The successive
unit directions satisfy $q_{k+1}=e^{\mathrm i\vartheta_k}q_k$.
Multiplying around the closed cycle gives
\begin{equation}\label{flatpr:rotation-integer}
e^{\mathrm i\sum_k\vartheta_k}=1,\qquad
\frac1{2\pi}\sum_k\vartheta_k\in\mathbb Z.
\end{equation}
Principal turns are continuous when the two incident directions are
nonzero and not antiparallel. On the carrier through $\mu_j$ its
distinguished turn tends to zero, and each other principal turn tends
to the corresponding deletion turn. On every other carrier all turns
have their common deletion limits. Thus each side's signed rotation
tends to the deletion's integer rotation. An integer with distance
less than $1/2$ from that integer must equal it. There are finitely
many supports and carriers, so a common sufficiently small interval
works for all of them. This proves the signed and absolute rotation
equalities in (ii).

It remains to evaluate the selector. Let $c$ be the number of surviving
corners in the distinguished carrier. Their signs agree in all three
configurations. Its extra turn is right or left according to the named
side. The exhaustive table is
\begin{equation}\label{flatpr:selector-table}
\begin{array}{c|ccc}
\text{surviving turns}&W_{\rm right}&W_{\rm left}&W_{\rm del}\\\hline
\text{mixed}&0&0&0\\
\text{all right}&1&0&1\\
\text{all left}&0&(-1)^{c+1}&(-1)^c
\end{array}
\end{equation}
In the last row $0-(-1)^{c+1}=(-1)^c$; the other two rows have the
same first-minus-second identity immediately. All other carriers
retain all their corner signs and counts. This proves (iii).
\end{proof}
```

## lit:homfly — AXIOM

reference/SM/sm-3-statesum.tex:916–923

```tex
\begin{literature}[HOMFLY--PT polynomial]\label{lit:homfly}
There is a map $D\mapsto H_D(a,z)\in\ZZ[a^{\pm1},z^{\pm1}]$ on oriented
link diagrams that is invariant under the three Reidemeister moves and planar
isotopy, takes the value $1$ on the crossing-free circle, and satisfies
$aH_{D_+}-a^{-1}H_{D_-}=zH_{D_0}$ for every skein triple. Its value depends
only on the oriented link presented by $D$.
\status{lit: Registry~\ref{reg:homfly}; existence, the skein, the unknot value and Reidemeister invariance: Lickorish--Millett \cite[Theorem, pp.~112--113; proof pp.~113--120; isotopy-class descent p.~120]{LickorishMillett}, the coefficient ring $\ZZ[a^{\pm1},z^{\pm1}]$ under $l=ia$, $m=-iz$ from LM property~(1), p.~110, proved as their Proposition~22 \cite[statement p.~133, proof pp.~133--134]{LickorishMillett}, whose parity clause holds at every component count (seat L-1 EXIT; F-25-169), the descent through Reidemeister's theorem \cite{Reidemeister,Reidemeister1927}; the former uniqueness clause over $\ZZ[a^{\pm1},z^{\pm1}]$ was stated in no source, was consumed by no proof of this document from round~3 on, every consumer taking uniqueness from Lemma \texttt{lp:coefficient-transport}, and was struck from the statement in round~4 (R-25-33, F-25-131); F-25-110, F-25-54, F-25-55}
\end{literature}
```

## lp:lm — AXIOM

reference/SM/sm-3-statesum.tex:935–960

```tex
\begin{literature}[Exact local LM construction projection]\label{lp:lm}\label{src:lm}
For every such diagram $D$, let $F_D(l,m)$ be the function constructed in
Section~1 of Lickorish--Millett~\cite{LickorishMillett}, not an arbitrary function with similar
values. The source constructs it in
$\mathbb Z[l^{\pm1},m^{\pm1}]$, independently of the auxiliary component
order, nonsingular basepoints, and order of required crossing switches.
It is defined modulo positive page isotopy, satisfies
\begin{equation}\label{lp:source-skein}
 l F_{D_+}+l^{-1} F_{D_-}+m F_{D_0}=0,
 \qquad \mu=-(l+l^{-1})m^{-1},
\end{equation}
and has the initialization $F_D=\mu^{c-1}$ for every based ordered
$c$-component UNDER-first diagram. UNDER-first means that, traversing
components in their order, from their basepoints and in their orientations,
the first encounter with each crossing is the underpass. In particular
every crossing-free $c$-component diagram has that value, regardless of
nesting or orientations. Here $c\geq1$.

The same function is invariant under each actual ordinary oriented
Reidemeister move. For a supplied finite sequence, take the maximum of the
finitely many crossing counts and apply source Proposition~4 at that level
one move at a time. No bound by the endpoint crossing counts is required.
The imported construction and its Propositions~1--6 stop before the final
p120 inference from arbitrary ambient isotopy to a finite move sequence.
\status{lit: Registry~\ref{reg:homfly}; local construction only}
\end{literature}
```

## lp:lm-uniqueness — AXIOM

reference/SM/sm-3-statesum.tex:962–979

```tex
\begin{literature}[Uniqueness of the source polynomial over its own ring]\label{lp:lm-uniqueness}
Lickorish--Millett prove \cite[Theorem, pp.~112--113, with the uniqueness
argument on p.~120]{LickorishMillett} that the function $F_D$ of Literature
input~\ref{lp:lm} is the only map from oriented link diagrams (modulo plane
isotopy) to $T=\ZZ[l^{\pm1},m^{\pm1}]$ that depends only on the isotopy class
of the oriented link, takes the value $1$ on the unknot, and satisfies
$lF_{D_+}+l^{-1}F_{D_-}+mF_{D_0}=0$ on every skein triple; the same statement
is Theorem~15.2 of Lickorish~\cite{LickorishGTM}. Uniqueness is asserted
among all such maps, with no restriction on the support or on the
coefficients of a competitor. A map on diagrams that is invariant under
planar isotopy and the three Reidemeister moves depends only on the isotopy
class of the oriented link by Reidemeister's theorem~\cite{Reidemeister}, the
source's own input for its descent on p.~120; the uniqueness therefore
applies to every such invariant map with the source skein and the unknot
value. The ring is the source's: no statement over $\ZZ[a^{\pm1},z^{\pm1}]$
is imported here (registry L-1, ledger row F-25-54).
\status{lit: Registry~\ref{reg:homfly}; uniqueness over the source ring only, with Reidemeister's theorem}
\end{literature}
```

## lp:coefficient-transport — PROVE

reference/SM/sm-3-statesum.tex:981–992

```tex
\begin{lemma}[Gaussian coefficient transport of skein uniqueness]
\label{lp:coefficient-transport}
Put $R=\ZZ[a^{\pm1},z^{\pm1}]$. Any two maps $D\mapsto Q_D\in R$ on oriented
link diagrams that are invariant under planar isotopy and the three
Reidemeister moves, take the value $1$ on the crossing-free circle, and
satisfy $aQ_{D_+}-a^{-1}Q_{D_-}=zQ_{D_0}$ on every skein triple coincide.
No restriction on the support or on the coefficients of the maps is imposed.
The lemma transports the uniqueness clause of Literature
input~\ref{lp:lm-uniqueness} to the ring $R$; it asserts no existence, no
ambient-isotopy invariance and no descent theorem.
\status{new (author, round~2; adapted from Codex S54-P1 = P-25-10, sealed lane candidate\_source\_findings\_51\_58\_v1; declared campaign step transporting Literature input~\ref{lp:lm-uniqueness} to $R$, flagged for source cross-check under rule~8; consumed in round~3 by Theorem \texttt{lp:core} (the identification $P=H$) and Theorem \texttt{cf:thm-carrierfloor} (clause~(R) and the mirror paragraph), and through clause~(R) by Proposition \texttt{prop:C-reversal}; F-25-54)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:993–1039

```tex
\begin{proof}
Adjoin a formal $\mathrm i$ with $\mathrm i^2=-1$ and put
$T_G=\ZZ[\mathrm i][l^{\pm1},m^{\pm1}]$ and
$R_G=\ZZ[\mathrm i][a^{\pm1},z^{\pm1}]$. Since $1,\mathrm i$ is a free
integer basis of $\ZZ[\mathrm i]$, every element of $T_G$ is uniquely
$u+\mathrm iv$ with $u,v\in T$, and the inclusions $T\subset T_G$,
$R\subset R_G$ are injective.

\emph{Uniqueness over $T_G$.} Let $G$ be a map from oriented link diagrams
to $T_G$, invariant under planar isotopy and the three moves, with
$G_{\bigcirc}=1$ and $lG_{D_+}+l^{-1}G_{D_-}+mG_{D_0}=0$ on every skein
triple. Write $G_D=U_D+\mathrm iV_D$ with $U_D,V_D\in T$. Both coordinates
inherit the invariance, and since the three coefficients $l,l^{-1},m$ lie
in $T$, comparing coordinates gives the source skein for $U$ and for $V$
separately, with $U_{\bigcirc}=1$ and $V_{\bigcirc}=0$. The skein is linear,
so $U$ and $F+V$ are both invariant $T$-valued maps satisfying the source
skein with unknot value $1$. Literature input~\ref{lp:lm-uniqueness} gives
$U=F$ and $F+V=F$, hence $V=0$ and $G=F$. No division by $2$ is used.

\emph{Transport.} The assignments
\begin{equation}\label{lp:ring-transports}
 \phi:T_G\to R_G,\quad l\mapsto\mathrm ia,\ m\mapsto-\mathrm iz,
 \qquad
 \psi:R_G\to T_G,\quad a\mapsto-\mathrm il,\ z\mapsto\mathrm im,
\end{equation}
both fixing $\mathrm i$, send the Laurent generators to units and therefore
define ring homomorphisms. On generators,
$\psi(\phi(l))=\mathrm i(-\mathrm il)=l$,
$\psi(\phi(m))=-\mathrm i(\mathrm im)=m$,
$\phi(\psi(a))=-\mathrm i(\mathrm ia)=a$ and
$\phi(\psi(z))=\mathrm i(-\mathrm iz)=z$, so $\phi$ and $\psi$ are mutually
inverse isomorphisms. Let $Q$ be a map as in the statement, regarded as
$R_G$-valued, and put $\widetilde Q_D=\psi(Q_D)\in T_G$. It is invariant
under planar isotopy and the three moves, and
$\widetilde Q_{\bigcirc}=1$. Since $\psi(a^{-1})=(-\mathrm il)^{-1}
=\mathrm il^{-1}$, applying $\psi$ to
$aQ_{D_+}-a^{-1}Q_{D_-}-zQ_{D_0}=0$ gives
\begin{equation}\label{lp:transported-skein}
 (-\mathrm il)\widetilde Q_{D_+}-(\mathrm il^{-1})\widetilde Q_{D_-}
 -(\mathrm im)\widetilde Q_{D_0}=0,
\end{equation}
and multiplying by the unit $\mathrm i$ gives
$l\widetilde Q_{D_+}+l^{-1}\widetilde Q_{D_-}+m\widetilde Q_{D_0}=0$.
By the first step, $\widetilde Q=F$, hence $Q_D=\phi(F_D)$ for every
diagram $D$. Two maps as in the statement are therefore equal in $R_G$,
and by injectivity of $R\subset R_G$ equal in $R$.
\end{proof}
```

## lp:core — PROVE

reference/SM/sm-3-statesum.tex:1041–1062

```tex
\begin{theorem}[Local campaign polynomial, algebraic part]\label{lp:core}
Set $R=\mathbb Z[a^{\pm1},z^{\pm1}]$. The same source construction has
an evaluation $P_D\in R$ with
\begin{equation}\label{lp:skein}
 aP_{D_+}-a^{-1}P_{D_-}=zP_{D_0},
 \qquad \delta=(a-a^{-1})z^{-1}.
\end{equation}
Its value on every UNDER-first $c$-component diagram is $\delta^{c-1}$.
It equals $H_D$ of Literature input~\ref{lit:homfly}. It is also the unique
function on this exact diagram domain satisfying this
skein and all these initialization values. This uniqueness statement
explicitly includes the initialization hypothesis; it is not a claim
proved from only an unknot value and unspecified ambient invariance.
For every $c$-component diagram,
\begin{equation}\label{lp:support}
 P_D\in z^{1-c}\mathbb Z[a^{\pm1},z^2],\qquad P_D\ne0.
\end{equation}
In particular $P_{\bigcirc}=1$, and knot evaluations are polynomials in
$z^2$, with no negative $z$ exponents. All local invariances in
Literature input~\ref{lp:lm} are retained.
\status{new (round~3: the identification paragraph of the proof consumes Lemma~\ref{lp:coefficient-transport}, F-25-54; the remainder of the proof is the round-1 transcription of RC lp:core, \path{d2b_local_polynomial} (C026), held by bench~A; consumes Literature inputs~\ref{lp:lm} and~\ref{lit:homfly})}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:1063–1178

```tex
\begin{proof}
Start in $R_G=\mathbb Z[\mathrm i][a^{\pm1},z^{\pm1}]$ with
$\mathrm i^2=-1$. The elements $\mathrm ia$ and $-\mathrm iz$ are units,
so they define a Laurent-ring homomorphism and a first evaluation
\begin{equation}\label{lp:gaussian}
 \phi(l)=\mathrm ia,\qquad \phi(m)=-\mathrm iz,
 \qquad P_D^G=\phi(F_D).
\end{equation}
Inverting the first unit gives $(\mathrm ia)^{-1}=-\mathrm ia^{-1}$.
The image of the source skein is therefore
\begin{equation}\label{lp:gaussian-skein}
 \mathrm iaP_+^G-\mathrm ia^{-1}P_-^G-\mathrm izP_0^G=0.
\end{equation}
Multiplying by $-\mathrm i$ gives the campaign skein in~\eqref{lp:skein}.
For the source initialization, the numerator $l+l^{-1}$ maps to
$\mathrm i(a-a^{-1})$ and the denominator $m$ maps to $-\mathrm iz$.
Their quotient with its preceding minus sign is $(a-a^{-1})/z$.
Thus $P_D^G=\delta^{c-1}$ for every UNDER-first diagram. This calculation
does not yet assert integral coefficients for arbitrary diagrams.

Choose auxiliary basepoints and a component order. Let $N(D)$ be the
crossing count and let $b(D)$ count first encounters which are OVER.
The initialization is exactly $b=0$. A switch at the first bad crossing
keeps the parameter circles and their traversal order. It changes that
first encounter from OVER to UNDER and leaves every other first-encounter
designation unchanged. Thus $D^{\rm sw}$ has complexity $(N,b-1)$.
Its chosen crossing sign is negated, since the two ordered over/under
tangents are exchanged.

Oriented smoothing reconnects each incoming strand to the other strand's
outgoing end. It removes just the selected crossing and creates no other
crossing in its clean disc. A self crossing splits one parameter circle
into two; a mixed crossing joins two into one. This can be checked by
writing a self-crossing cycle as $(x A y B)$ and replacing it by the
two cycles $(x B),(y A)$ before erasing $x,y$. For a mixed crossing,
the cycles $(x A),(y B)$ become $(x B y A)$ before erasing the marks.
Empty resulting occurrence words are still circles. Thus the resulting
component counts are $c+1$, or $c-1\geq1$ in the mixed case, and the
smoothing always remains in the nonempty domain. Its crossing count is
$N-1$. New orders and basepoints can be chosen because the first
complexity coordinate has decreased. These facts justify lexicographic
induction on $(N,b)$, for every finite number of components.

At a positive chosen crossing the skein is
$aP_D^G-a^{-1}P_{D^{\rm sw}}^G=zP_{D^0}^G$.
Move the second term to the right and divide by the unit $a$ to obtain
\begin{equation}\label{lp:positive}
 P_D^G=a^{-2}P_{D^{\rm sw}}^G+a^{-1}zP_{D^0}^G.
\end{equation}
At a negative chosen crossing the positive diagram is $D^{\rm sw}$,
so the skein is $aP_{D^{\rm sw}}^G-a^{-1}P_D^G=zP_{D^0}^G$.
Move the latter two terms across and multiply by $a$. This gives
\begin{equation}\label{lp:negative}
 P_D^G=a^2P_{D^{\rm sw}}^G-azP_{D^0}^G.
\end{equation}

For integral descent let $M_c=z^{1-c}\mathbb Z[a^{\pm1},z^2]$,
viewed as an additive subgroup of $R_G$. The initialization belongs to
$M_c$, since $\delta^{c-1}=z^{1-c}(a-a^{-1})^{c-1}$.
The switched term has the same component count, so induction puts it in
$M_c$; multiplication by any $a$ unit preserves this subgroup. For a self
smoothing, induction puts the smoothed value in $M_{c+1}$, and
\begin{equation}\label{lp:self-support}
 zM_{c+1}=z\,z^{-c}\mathbb Z[a^{\pm1},z^2]=M_c.
\end{equation}
For a mixed smoothing, induction puts it in $M_{c-1}$, and
\begin{equation}\label{lp:mixed-support}
 zM_{c-1}=z\,z^{2-c}\mathbb Z[a^{\pm1},z^2]
             =z^2M_c\subseteq M_c.
\end{equation}
Both recurrences therefore put $P_D^G$ in $M_c$. The standard inclusion
$R\hookrightarrow R_G$ is injective (the Gaussian coefficient ring has
the free integer basis $1,\mathrm i$). There is consequently one $P_D\in R$
with image $P_D^G$. This proves support and integral descent simultaneously.
The local source equalities remain equalities after $\phi$ and, by
injectivity, are equalities in $R$.

For uniqueness, let $Q_D\in R$ satisfy the stated skein and every
UNDER-first initialization. Apply the same induction. At $b=0$ its value
is the specified $\delta^{c-1}=P_D$. Otherwise its value is given by the
same positive or negative solved recurrence. The switched and smoothed
values agree with $P$ by the inner and outer induction respectively.
Substitution gives $Q_D=P_D$. No existence or confluence is inferred from
this uniqueness argument; existence was the literal source construction.

Finally map $R$ to $\mathbb Q(a)$ by fixing the indeterminate $a$ and
sending $z$ to $a-a^{-1}$. This target is a field, and $a-a^{-1}$ is a
nonzero rational function, so the Laurent specialization is well-defined.
The initialized $\delta$ maps to $1$. The same induction shows that
every nonempty diagram specializes to $1$. In the positive case the two
inductively specialized smaller values are each $1$, and
\begin{equation}\label{lp:nonzero-positive}
 a^{-2}+a^{-1}(a-a^{-1})
       =a^{-2}+1-a^{-2}=1.
\end{equation}
In the negative case they are also each $1$, and
\begin{equation}\label{lp:nonzero-negative}
 a^2-a(a-a^{-1})=a^2-a^2+1=1.
\end{equation}
A zero element of $R$ would specialize to zero. This proves $P_D\ne0$.

Finally, $D\mapsto P_D$ and $D\mapsto H_D$ are maps from oriented link
diagrams into $R$ that take the value $1$ on the crossing-free circle,
satisfy the campaign skein~\eqref{lp:skein}, and are invariant under
planar isotopy and the three Reidemeister moves: for $P$ these properties
were proved above from Literature input~\ref{lp:lm}, and for $H$ they are
the existence and invariance clauses of Literature input~\ref{lit:homfly}.
Lemma~\ref{lp:coefficient-transport} identifies two such maps, so
$P_D=H_D$ on every actual diagram. This identification consumes the
uniqueness transported to $R$ by that lemma from Literature
input~\ref{lp:lm-uniqueness}, together with the existence clause of
Literature input~\ref{lit:homfly}; the uniqueness clause of the latter is
not used. It does not derive arbitrary ambient-isotopy invariance from the
local construction alone. The support proof itself used only the local
construction and the displayed induction.
\end{proof}
```

## lp:split-circle — PROVE

reference/SM/sm-3-statesum.tex:1180–1191

```tex
\begin{lemma}[A diagrammatically split circle]\label{lp:split-circle}
Let $D'$ be the actual diagram formed from $D$ by adding one simple
crossing-free component having no crossings with $D$. It may surround
some components of $D$; it need not lie in the unbounded complementary
face. Then
\begin{equation}\label{lp:split}
 P_{D'}=\delta P_D.
\end{equation}
In particular every crossing-free $c$-component diagram has value
$\delta^{c-1}$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2b\_local\_polynomial, split circle (C026))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1192–1207

```tex
\begin{proof}
Order and base $D$, and put the added component last with any basepoint.
This adds no crossing encounter, so $N$ and $b$ are unchanged. Induct on
$(N,b)$ for $D$. If $b=0$, the two source initialization values are
$\delta^{c-1}$ and $\delta^c$, which have the required relationship.
Otherwise choose the same first bad crossing in $D$ and $D'$. Switching
or smoothing does not touch the extra component. The switched pair and
the smoothed pair are therefore again related by adding exactly that
crossing-free component. In either solved recurrence the coefficients
are scalar elements of the commutative ring $R$. Substitute the inductive
factor $\delta$ for both smaller values of $D'$, and factor it out; the
remaining expression is the solved recurrence for $P_D$. This proves
the formula. Nesting never enters this induction. This lemma does not
claim that an arbitrary spatially split presentation already has this
diagram form; such a use requires its own certificate or product proof.
\end{proof}
```

## rp:record-polynomial — PROVE

reference/SM/sm-3-statesum.tex:1215–1227

```tex
\begin{lemma}[Polynomial equality from a named decorated record]
\label{rp:record-polynomial}
Let $D,D'$ be two actual nonempty finite generic oriented link diagrams.
Suppose there is a bijection of their components and crossing occurrences
which preserves oriented cyclic successor, crossing pairing, over/under
bits and crossing signs. The component bijection must also include all
components with no crossing occurrences. Then $F_D(l,m)=F_{D'}(l,m)$.
Consequently any common Laurent-ring substitution of these two source
values, and every coefficient of the substituted values, agrees.
This statement does not require or assert realizability of an arbitrary
abstract record or an ambient isotopy between the two diagrams.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2b/d2c, named-record polynomial equality (C026))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1228–1304

```tex
\begin{proof}
Choose an order on the components of $D$, and one basepoint outside the
crossings on each component. Transfer the order to $D'$. On a component
with crossings, choose its new basepoint in the interval just preceding
the image of the old first crossing occurrence. On a crossing-free
component choose any point. These choices make the complete traversal
orders of crossing occurrences correspond. They are allowed because the
source construction is independent of component order and basepoint.

Call a crossing bad if its first encounter in this ordered traversal is
the overpass. Write $N$ for the total number of crossings and $b$ for the
number of bad crossings. Both numbers agree for the two based diagrams.
We use lexicographic induction on $(N,b)$. If $b=0$, both diagrams are
under-first ascending and have the same number $c\geq1$ of components.
Their two source values are therefore separately $\mu^{c-1}$ by the
initialization. This includes $N=0$ and any crossing-free components;
no value for an empty link is introduced.

For $b>0$, choose the first bad crossing in $D$ and its named image in
$D'$. Switching that crossing preserves each traversed component and its
basepoint. It swaps the two over/under bits at just that crossing.
Hence that crossing ceases to be bad and every other first-encounter
designation is unchanged: the switched diagrams have complexity
$(N,b-1)$ and still have isomorphic decorated records. Their values
are equal by the inner induction.

Oriented smoothing removes the two occurrences of the chosen crossing.
Cut each traversed strand there into an incoming and an outgoing end.
The oriented smoothing connects each incoming end to the outgoing end
of the other strand. The given bijection preserves these ends and their
orientation, so it preserves this precise recombination of successors.
All other paired crossings retain their over/under bits and signs.
The resulting actual smoothed diagrams thus have isomorphic decorated
records, including their component bijection. A self-crossing splits
one traversed component into two; a mixed crossing joins two into one.
Crossing-free resulting circles are retained as components rather than
discarded. The smoothed diagram is always nonempty: in the mixed case
the original component number is at least two, and in the self case
the number increases. The new crossing number is $N-1$.

Choose new component orders and basepoints on one smoothed diagram and
transfer them through its induced record bijection as above. The outer
induction applies regardless of their new bad-crossing count. It gives
equal values for the two smoothed diagrams. No relation between the old
and new component orders is needed, and no topological classification
is used to supply the record bijection.

It remains to insert these two equalities into the same scalar recursion.
The crossing signs are part of the record, so the chosen crossings in
$D,D'$ have the same sign. For a positive chosen crossing the source
skein reads
\begin{equation}\label{rp:positive-skein}
 lF_D+l^{-1}F_{D^{\rm sw}}+mF_{D^0}=0.
\end{equation}
Subtract the last two terms and divide by the unit $l$. This gives
\begin{equation}\label{rp:positive-recursion}
 F_D=-l^{-2}F_{D^{\rm sw}}-l^{-1}mF_{D^0}.
\end{equation}
For a negative chosen crossing the positive diagram is the switched one,
and the source skein instead reads
\begin{equation}\label{rp:negative-skein}
 lF_{D^{\rm sw}}+l^{-1}F_D+mF_{D^0}=0.
\end{equation}
Subtract the other two terms and multiply by $l$, obtaining
\begin{equation}\label{rp:negative-recursion}
 F_D=-l^2F_{D^{\rm sw}}-lmF_{D^0}.
\end{equation}
The identical formula with primes holds in the corresponding sign case.
The two switched terms agree by the inner induction and the two smoothed
terms by the outer induction. Substitution therefore proves $F_D=F_{D'}$.
This completes the induction, including both signs and both smoothing
component cases. No division by a polynomial value is performed.

A common Laurent-ring homomorphism preserves equality. Coefficient
extraction is an additive map defined also at zero and therefore preserves
that resulting equality. These give the last assertions.
\end{proof}
```

## lc:presentations — PROVE

reference/SM/sm-3-statesum.tex:1306–1319

```tex
\begin{lemma}[Presentations of the same decorated record]
\label{lc:presentations}
Suppose two actual finite nonempty decorated diagrams have a specified
bijection of their oriented parameter circles and crossing occurrences,
preserving cyclic successor, pairing, over/under designations and signs.
Their evaluations by the same local LM construction agree. This includes
positive page-chart changes of an actual spherical diagram, clean
crossing-free replacements and different compatible height choices,
whenever the endpoint page diagrams belong to the finite-page domain.
All crossing-free circles must be included in the component bijection.
No arbitrary ambient isotopy is a hypothesis or conclusion of this scalar
statement.
\status{proved (refereed: bench A, 2026-09-05T19:35:00Z; transcribed from RC d2b\_local\_polynomial, lc:presentations (C026))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1320–1343

```tex
\begin{proof}
Apply Lemma~\ref{rp:record-polynomial} and the common substitution
$l=\mathrm ia$, $m=-\mathrm iz$. For the stated presentation examples,
the bijections can be checked directly. A positive regular page chart
does not alter a parameter circle or its order; its positive differential
multiplies a crossing determinant by a positive number. An orientation
preserving finite piecewise-linear chart has the same cyclic ray order,
so after its regular finite-page model the signs are the same. The
specified crossing decorations retain the over/under bits. Choosing a
different point in a face to omit inserts no crossing occurrence.
These are comparisons of two actual diagrams, not a realization of an
arbitrary word or a claim that a continuous chart is differentiable.

A clean replacement of one crossing-free interval, fixed on its endpoint
collars and missing every other strand, inserts no visit. The original
circle parameter therefore supplies the same successor between its two
collars and identifies every old crossing germ. Each crossing-free circle
is explicitly retained. Finally, compatible heights mean precisely that
the prescribed over branch remains higher than the under branch in the
chosen positive projection frame. Changing those heights changes none
of the decorated record, even if the heights themselves are only
continuous. No smoothness of such a height change, or polynomial
invariance under its ambient extension, is inferred.
\end{proof}
```

## lc:single-crossing — PROVE

reference/SM/sm-3-statesum.tex:1345–1351

```tex
\begin{lemma}[A single self crossing has scalar value one]
\label{lc:single-crossing}
An actual oriented one-circle diagram with just one self crossing has
local LM evaluation $P_D=1$, for either crossing sign. A crossing-free
one-circle diagram also has value one.
\status{proved (refereed: bench A, 2026-09-05T19:35:00Z; transcribed from RC d2b\_local\_polynomial, lc:single-crossing (C026))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1352–1360

```tex
\begin{proof}
In the one-crossing case choose the nonsingular basepoint in the cyclic
interval immediately before its under occurrence. That occurrence is
first; there is no other crossing. The diagram is therefore UNDER-first
with one component and has source value $\mu^0=1$. The common Laurent
substitution keeps this value. The zero-crossing case is the same
one-component initialization. This does not assume that a selected
planar monogon is the bounded face, or discard another component.
\end{proof}
```

## mp:join — PROVE

reference/SM/sm-3-statesum.tex:1427–1437

```tex
\begin{theorem}[Simultaneous marked product]\label{mp:join}
For two nonempty actual marked diagrams and any actual clean marked
join $J(A,B)$ just specified,
\begin{equation}\label{mp:join-value}
 P_{J(A,B)}=P_AP_B.
\end{equation}
This includes smoothing-created multi-component factors and an arbitrary
crossing-free marked component. No assertion about a marked terminal
tangle being ambient-trivial is needed.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2c\_polynomial\_products, marked join (C026))}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:1438–1492

```tex
\begin{proof}
Use induction on the sum $N=N(A)+N(B)$, with an inner induction on the
sum $b=b(A)+b(B)$ of bad crossings for chosen based orders. In EACH
factor put the marked component first and base it at its marked gap.
Choose arbitrary orders and bases for the remaining components.

If $b=0$, traverse the joined component starting just before the $A$
portion, then its $B$ portion. Traverse the remaining $A$ components
in their chosen order, then the remaining $B$ components in their
chosen order. For crossings of $A$, the relative order of all visits is
the same as in its factor traversal; visits of $B$ inserted between
some of them do not change which of the two visits to an $A$ crossing
comes first. The identical observation holds for $B$. There are no
crossings with one visit in each factor. Thus the entire joined diagram
is UNDER-first. Its source base gives
\begin{equation}\label{mp:join-base}
 P_{J(A,B)}=\delta^{c(A)+c(B)-2}
             =\delta^{c(A)-1}\delta^{c(B)-1}=P_AP_B.
\end{equation}
This is a scalar computation on an actual ascending diagram, not a
claim identifying its marked arcs with a trivial tangle.

If $b>0$, choose a bad crossing in one factor, say $A$. Its disc is
disjoint from the mark and from the joining operation. Switching it
gives $A^{\rm sw}$ with the same component number, same marked interval
and smaller $b$. In $J(A,B)$ it is precisely the corresponding crossing
switch. Smoothing gives $A^0$, of crossing number $N(A)-1$, with the
same interval on one unique component. In the joint diagram, smoothing
has exactly the record of $J(A^0,B)$: both operations are recombinations
at disjoint incoming/outgoing ends. All other successor relations and
all other crossings are unchanged. If the selected crossing involves the marked component, a self-smoothing
places the interval on exactly one of its two output components, and a
mixed smoothing joins that component to another while retaining the
interval. If the selected crossing involves no strand of the marked
component, that component and its interval are unchanged: a self-smoothing
splits one unmarked component into two, and a mixed smoothing merges two
unmarked components. In all four cases every output component is retained,
including all crossing-free components. These are the exhaustive
self/mixed and marked/unmarked cases; nonemptiness was checked in
Theorem~\ref{lp:core}.

Use the actual smoothed diagram as the realization of $J(A^0,B)$, or
apply Lemma~\ref{lc:presentations} to a newly chosen clean realization. Inner
induction gives $P_{J(A^{\rm sw},B)}=P_{A^{\rm sw}}P_B$; outer
induction gives $P_{J(A^0,B)}=P_{A^0}P_B$. Apply the appropriate solved
skein to the joint diagram and substitute these two equalities. Its
right side is respectively
$(a^{-2}P_{A^{\rm sw}}+a^{-1}zP_{A^0})P_B$ or
$(a^2P_{A^{\rm sw}}-azP_{A^0})P_B$. The factor in parentheses is
$P_A$ by the same solved skein in $A$. This proves the identity. If
the selected bad crossing is in $B$, the identical argument with the
two factor names interchanged applies. For each outer induction case
new auxiliary choices can again put its marked component first,
because the source value is independent of those choices.
\end{proof}
```

## mp:stack — PROVE

reference/SM/sm-3-statesum.tex:1494–1511

```tex
\begin{theorem}[Ordered stacked blocks, including split unions]
\label{mp:stack}
Let $D$ be an actual nonempty diagram whose components are partitioned
into $q\geq1$ nonempty tagged blocks. Assume that at every crossing
between different blocks the smaller-index block is under the larger
one. Let $D_i$ be the actual restriction retaining all components in
block $i$ and all crossings internal to it. Then
\begin{equation}\label{mp:stack-value}
 P_D=\delta^{q-1}\prod_{i=1}^qP_{D_i}.
\end{equation}
There is no bound on the number of components in a block, no restriction
on crossings inside a block, and no requirement that their page images
be separated. A crossing-free disjoint union is the special case with
no crossings between blocks. In particular
$P_{A\sqcup B}=\delta P_AP_B$ for two nonempty diagrams presented
without mixed crossings.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2c\_polynomial\_products, stack (C026))}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:1512–1536

```tex
\begin{proof}
Order components block by block, choosing any based order within each.
All between-block crossings are first encountered under. Let $N$ be
the sum of the INTERNAL crossing numbers and $b$ the sum of their bad
crossing numbers. These need not be the total crossing number of $D$.

If $b=0$, the full diagram is ascending. With $c_i=c(D_i)$ its scalar
is $\delta^{\sum_i c_i-1}$. Each factor has scalar
$\delta^{c_i-1}$, so their product times $\delta^{q-1}$ has the same
exponent $q-1+\sum_i(c_i-1)=\sum_i c_i-1$.

Otherwise resolve a bad internal crossing. Switching it lowers $b$,
preserves the block assignment and the between-block hypothesis, and
is the same switch in its block restriction. Smoothing lowers $N$.
Every new component inherits the same block as the strands smoothed;
no two blocks merge, and no block becomes empty. All between-block
crossing visits persist on their original strands, so their under/over
relation still has the required block order. The restriction of the
smoothed diagram in that block is exactly the oriented smoothing of
the old block restriction; the other restrictions do not change.
Lexicographic induction and the appropriate solved skein now give
\eqref{mp:stack-value}, since its factors outside the resolved block
and the scalar $\delta^{q-1}$ are identical in all three terms.
This proof supplies the scalar without moving any component in space.
\end{proof}
```

## mp:zero-link — PROVE

reference/SM/sm-3-statesum.tex:1538–1545

```tex
\begin{lemma}[Mixed signed crossings in a stack]\label{mp:zero-link}
For two distinct components of an actual generic oriented plane diagram,
the sum of $\operatorname{sgn}\det(u_1,u_2)$ over their transverse
intersections, in this fixed component order, is zero. Consequently
the half-sum of decorated crossing signs is an integer, and it is zero
if one component is always over the other.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2c\_polynomial\_products (C026))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1546–1580

```tex
\begin{proof}
Use finite polygonal page models preserving all transverse crossing
signs; the clean crossing-disc and strip construction cited above
does not change any signed intersection. Write the oriented edges of
component 2 as $[v_j,v_{j+1}]$. Choose an auxiliary point $o$ off the
finitely many lines and intersections that would make a fan triangle
degenerate or a radial edge nongeneric against component 1. A finite
union of proper lines and points cannot fill the plane, so such $o$
exists. Include further finite forbidden lines through a vertex of
component 1 and a vertex of component 2 to exclude radial-edge hits
at the former vertices. Orient the triangle chain
$[o,v_j,v_{j+1}]$ by this order. Its coefficient relative to the usual
positive plane orientation is its determinant sign.

For one positively oriented triangle, a closed transverse path has
as many entries into its interior as exits, counted with sign. At an
entry the ordered tangent pair (path, triangle boundary) has the
opposite determinant sign from an exit: the triangle lies consistently
on the left of its positive boundary. Thus its algebraic intersection
sum with that boundary is zero. Reversing triangle orientation negates
the sum and still gives zero. Summing over the finitely many fan
triangles, each radial edge occurs once in each orientation and
cancels. Their boundary chain is exactly component 2. Hence the
intersection sum of components 1 and 2 is zero. This remains valid for
self-intersecting components: the argument counts traversed occurrences,
not distinct points of an embedded boundary for either component.

At each mixed crossing the decorated sign is either the fixed-order
determinant sign or its negative, according to which component is
over. Their total differs from the zero fixed-order sum by twice an
integer. Its half is therefore integral. If the over-component is
constant, all signs use the same one of those two conventions and
the total is zero. This proves the assertions using the original mixed
crossings of this coambient pair, not a replacement split pair.
\end{proof}
```

## mp:lowest — PROVE

reference/SM/sm-3-statesum.tex:1582–1597

```tex
\begin{theorem}[All-component lowest mixed row]\label{mp:lowest}
Let $D$ be an actual diagram with $c\geq1$ tagged oriented components,
and let $D_i$ be their actual knot restrictions. Define
$\ell_{ij}=\tfrac12\sum\sigma(x)$ using ALL mixed crossings between
the original components $i,j$, and put $\Lambda=\sum_{i<j}\ell_{ij}$.
Then
\begin{equation}\label{mp:lowest-value}
 [z^{1-c}]P_D
 =a^{-2\Lambda}(a-a^{-1})^{c-1}
       \prod_{i=1}^c[z^0]P_{D_i}.
\end{equation}
For $c=2$ this is the two-component mixed row; the two
tagged restrictions are intrinsic knot diagrams while $\ell_{12}$ is
computed in their original common diagram.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2c\_polynomial\_products, lowest mixed row (C026))}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:1598–1622

```tex
\begin{proof}
Set $h(D)=[z^{1-c}]P_D$. At a mixed crossing the smoothed diagram has
$c-1\geq1$ components and support at least $z^{2-c}$ by
Theorem~\ref{lp:core}. Its multiplication by $z$ therefore has
support at least $z^{3-c}$, so contributes nothing to the $1-c$ row
of the skein. Hence $a h(D_+)=a^{-1}h(D_-)$ and
$h(D_-)=a^2h(D_+)$. The switch from positive to negative changes one
mixed sign from $+1$ to $-1$, and hence changes $\Lambda$ by $-1$.
It follows that $a^{2\Lambda}h$ is unchanged by that switch. Reversing
the equality proves the same for a negative-to-positive switch.

Switch exactly the mixed crossings necessary to put each smaller-index
component UNDER every larger-index component. These are finitely many
switches of an actual diagram, and no self-crossing or intrinsic
component restriction changes. By Lemma~\ref{mp:zero-link} every pair
of final components has linking number zero, hence final $\Lambda=0$.
Apply Theorem~\ref{mp:stack} with each component as one block. Its
value is $\delta^{c-1}\prod_iP_{D_i}$. Knot support is nonnegative
and even in $z$, so the $1-c$ coefficient of this expression is exactly
$(a-a^{-1})^{c-1}\prod_i[z^0]P_{D_i}$: any positive $z$ power in one
factor raises that exponent. Restoring the preserved weight
$a^{2\Lambda}$ proves the formula. For $c=1$ there are no switches,
$\Lambda=0$, and the assertion is the identity $[z^0]P_D=[z^0]P_D$.
No coefficient or whole polynomial has been assumed nonzero or divided out.
\end{proof}
```

## mp:blocks — PROVE

reference/SM/sm-3-statesum.tex:1624–1634

```tex
\begin{lemma}[Nested connected interlacement blocks]\label{mp:blocks}
Let an actual oriented one-circle decorated record have a nonempty
crossing set, partitioned into the connected components of its
interlacement graph. Suppose that for every component $H$ an actual retained diagram
$C_H$ with exactly that restricted named cyclic record is supplied.
Then a finite succession of clean marked joins of these actual diagrams
realizes the full record, and every actual diagram with that full record
has polynomial $\prod_H P_{C_H}$. The joins preserve the sign of every
crossing and the writhe is the sum of the writhes of $C_H$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2c\_polynomial\_products (C026))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1635–1684

```tex
\begin{proof}
First fix a connected component $A$ of the interlacement graph and a
chord $b$ outside it. Cutting the circle at the endpoints of $b$ gives
two open intervals. Since $b$ interlaces no chord of $A$, each chord
of $A$ has both endpoints in one of them. If chords of $A$ occupied
both intervals, an interlacement path in $A$ would have an adjacent
pair in different intervals. Such chords cannot alternate. Thus all
endpoints of $A$ lie in just one interval, which means both endpoints
of $b$ lie in one cyclic gap between successive endpoints of $A$.

If $b,b'$ are interlacing chords outside $A$, they must occupy the same
gap of $A$: distinct gaps are disjoint intervals and cannot contain
alternating endpoints. Applying this along an interlacement path shows
that every other connected component $B$ has all its endpoints in one
gap of $A$. This argument needs connectedness of $A$ as well as $B$;
noninterlacement of individual chords alone would not suffice.

Choose a base gap for the full cyclic record and let $A$ be the block
containing its first occurrence. The other blocks lie in gaps of $A$.
Within a nonempty such linear gap take the block $B$ containing its
first occurrence. Every other block inside the interval lies either in
an internal gap of $B$ or after its last occurrence: it cannot precede
its first occurrence, and the one-gap property excludes a block
straddling two such gaps. Recurse on the internal gaps, and then on
the suffix after that last occurrence. The same description for the
outer cyclic gap is made by cutting at the chosen base gap. Each step
removes at least one nonempty connected block from the pending list,
so the resulting finite nested forest, attached to root $A$, terminates.

Start with the actual $C_A$. For each gap attach the recursively
constructed actual diagrams for that gap in their inherited order,
using small disjoint crossing-free intervals in that gap. Each clean
join concatenates just the chosen cyclic blocks and introduces no new
crossing. Multiple insertions can use successively smaller intervals;
there are only finitely many. The construction of marked joins above
supplies actual planar realizations at every step, including nested
and exterior gaps. Thus the final oriented named record is literally
the full given record, with no assumption that an arbitrary restricted
word is realizable. Every leaf was an already supplied actual diagram.

Repeated use of Theorem~\ref{mp:join} gives the product value for the
constructed diagram. Lemma~\ref{lc:presentations} equates it with any actual
diagram having the same full data. Every old crossing is present once,
with its old sign, and no joining arc has a crossing, so writhe adds.
In the canonical application each sign is positive; its sum is
$\sum_H|H|$. If there are no owned blocks, the grouped value remains
the separately defined algebraic empty product $1$ and empty sum $0$.
No empty link is introduced and no knot is asserted to represent that
empty product by this lemma.
\end{proof}
```

## def:C — DEFINE

reference/SM/sm-3-statesum.tex:1688–1700

```tex
\begin{definition}[corner coefficient and the state sum]\label{def:C}
For a subpolygon $Q$ of a decomposition of the generic polygon $P$, let
$H^+_Q$ be the HOMFLY--PT polynomial of its positive lift and put
\[
d_Q=1-m_Q-|r_Q|,\qquad c(Q)=\bigl[a^{d_Q}z^0\bigr]H^+_Q(a,z)\in\ZZ,
\]
the coefficient of $a^{d_Q}z^0$ (zero if that monomial is absent). The
\emph{corner state sum} of $P$ is
\[
C(P)=(-1)^{\ell(P)}\sum_{\substack{S\in\Ind(G_P)\\ S\text{ uniform}}}
(-1)^{|S|}\prod_{Q\text{ subpolygon of }S}c(Q).
\]
\end{definition}
```

## lem:C-X1 — PROVE

reference/SM/sm-3-statesum.tex:1787–1798

```tex
\begin{lemma}[selector form of the carrier state sum]\label{lem:C-X1}
For a carrier $L$ of an independent support $S$, let $k(L)$ be its number
of corners. Put $\mathrm{wt}(L)=1$ if all its turns are right,
$(-1)^{k(L)}$ if all are left, and $0$ if its turns are mixed.
Set $\operatorname{wind}(S)=\prod_L\mathrm{wt}(L)$. Then
\begin{equation}\label{eq:C-selector-form}
C(P)=\sum_{S\in\Ind(G_P)}\operatorname{wind}(S)\prod_L c(L),
\end{equation}
where $c(L)$ remains the coefficient of the actual positive carrier lift
in Definition~\ref{def:C}.
\status{new (restricted in round 1 to the selector identity, C018; F-25-38)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1799–1810

```tex
\begin{proof}
Every original vertex belongs to exactly one carrier and retains its turn.
Every selected crossing contributes one left and one right smoothing
corner by Lemma~\ref{lem:carriers}. Thus the total number of left carrier
corners is $\ell(P)+|S|$. If $S$ is uniform, precisely its all-left
carriers contribute to this count. Their selector product is therefore
$(-1)^{\ell(P)+|S|}$, the sign of this support in Definition~\ref{def:C}.
If $S$ is not uniform, a mixed carrier makes its selector product zero;
this support is absent from that definition. The coefficient factors
are unchanged in both cases. Summing these term identities proves
\eqref{eq:C-selector-form}.
\end{proof}
```

## ng:front-domain — DEFINE

reference/SM/sm-3-statesum.tex:1825–1841

```tex
\begin{definition}[Finite oriented fronts]\label{ng:front-domain}
A front $F$ is an actual map of a nonempty finite union of parameter
circles to the oriented $(x,z)$ plane, with finitely many transverse
double points and ordinary semicubical cusps, no other singularities,
and no vertical tangencies on regular arcs. The limiting tangent at every
cusp is also nonvertical: in a semicubical parameter $u$ with cusp at
$u=0$, require $x''(0)\ne0$. Cusps meet no other strand or singularity.
At a crossing the branch with smaller $dz/dx$ is over. A downward cusp is
traversed from its locally upper arm to its locally lower arm. Write
$D(F)$ for the number of downward cusps, $w(F)$ for the sum of the
over-first tangent-determinant crossing signs, and $s(F)$ for the number
of crossings plus cusps.

In disjoint clean cusp discs replace each cusp by a simple regular arc
with the same oriented attachments and no crossing. The resulting
ordinary diagram is denoted $S(F)$.
\end{definition}
```

## ng:smoothing-record — PROVE

reference/SM/sm-3-statesum.tex:1843–1851

```tex
\begin{lemma}[independence of the rounding]\label{ng:smoothing-record}
Let $F$ be a front on the domain of Definition~\ref{ng:front-domain}. Any two
ordinary diagrams $S(F)$ obtained by the cusp replacement of that definition
have the same full named record: the same component circles, including
crossing-free ones, and the same crossing occurrences, cyclic orders,
over/under bits and signs. Consequently $P_{S(F)}$ does not depend on the
choice of rounding.
\status{new (round~5: the prose paragraph after Definition~\ref{ng:front-domain} wrapped as a statement so that the users of the symbol $P_{S(F)}$ cite it; F-25-136)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1852–1863

```tex
\begin{proof}
A cusp replacement inside a clean cusp disc creates no crossing and changes
no successor of an old crossing visit along the oriented parameter circle:
the replacing arc has the same oriented attachments as the cusp it replaces.
Every crossing pairing, sign and over/under bit is determined by germs
outside the cusp discs, which are unchanged, and the component
correspondence is the identity on the parameter circles, including those
without crossings. Thus any two such diagrams have a named decorated-record
isomorphism, and Lemma~\ref{rp:record-polynomial} identifies their
polynomial values. This does not use an ambient identification with a
spatial cusp-shaped link.
\end{proof}
```

## def:adeg — DEFINE

reference/SM/sm-3-statesum.tex:1887–1893

```tex
\begin{definition}[degrees in $a$]\label{def:adeg}
For a nonzero Laurent polynomial $f$ in $a$ with coefficients in the
integral domain $\ZZ[z^{\pm1}]$, $\deg_af=\max\deg_af$ denotes the largest
$a$-exponent with nonzero coefficient and $\mindeg_af$ the smallest; both
are integers. The same symbols with the subscript $z$ denote the largest and
smallest $z$-exponents of a nonzero element of $\ZZ[a^{\pm1},z^{\pm1}]$.
\end{definition}
```

## ng:commutation — PROVE

reference/SM/sm-3-statesum.tex:1921–1927

```tex
\begin{lemma}[Commutations and nonsingular deformation]
\label{ng:commutation}
Disjoint-gadget commutations and deformations through fronts without a
singular event preserve $D,w,d$, and hence $B$. Every supplied finite
front can be represented by a finite elementary front word.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ng\_front (C029))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1928–1948

```tex
\begin{proof}
Disjoint gadgets commute by sliding their empty rectangles. The index
changes track the same physical positions after insertion or removal of
two strands. After cusp rounding this is a positive page isotopy;
equivalently, the full named records are the same. The cusp directions
and crossing signs are unchanged, so $D$ and $w$ are unchanged as well.

A deformation without a singular event preserves the records, $D$ and
$w$: signs, cusp directions and cyclic attachments cannot change.
Lemma~\ref{rp:record-polynomial} gives scalar equality, without a global
move-generation theorem.

If singularities have equal $x$ coordinates, separate them by small local
$x$ translations, constant near the singularities and interpolated on
the intervening graph arcs. There are finitely many clean discs and
compact regular graph pieces. Their nonzero $x$ derivatives and
transverse crossings persist for sufficiently small translations, and
constant translations preserve the cusp germs. Reading successive
vertical cuts then gives the finite elementary word. No classification
of fronts is used.
\end{proof}
```

## ng:front-I — PROVE

reference/SM/sm-3-statesum.tex:1950–1953

```tex
\begin{lemma}[Front type I]\label{ng:front-I}
The front type-I moves preserve $B$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ng\_front (C029))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1954–1970

```tex
\begin{proof}
Each word $l_m\sigma_{m-1}r_m$ or $l_m\sigma_{m+1}r_m$ replaces one
through-strand. After rounding its two cusps, the unique crossing bounds
an empty ordinary monogon. In the first word, the strand crosses over
heading right, passes the right cusp and then the left cusp, and returns
under heading right. Both crossing arrows are therefore rightward, or
both are leftward when the entire strand is reversed. The other word
interchanges the over/under order along the through-strand but again
has simultaneously directed crossing tangents. Its crossing is also
positive. Exactly one of the two cusps is downward and one is upward.
Ordinary Reidemeister I gives, in the direction creating this front curl,
\begin{equation}\label{ng:type-I-counts}
 \Delta w=1,\qquad \Delta D=1,\qquad \Delta d=0.
\end{equation}
Equation~\eqref{ng:defect} now gives $\Delta B=0$.
An arbitrary front zigzag is not a type-I move.
\end{proof}
```

## ng:front-II — PROVE

reference/SM/sm-3-statesum.tex:1972–1975

```tex
\begin{lemma}[Front type II]\label{ng:front-II}
The front type-II moves preserve $D,w,d$, and hence $B$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ng\_front (C029))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1976–1988

```tex
\begin{proof}
The words $l_{m-1}\sigma_m\sigma_{m-1}$ and
$l_{m+1}\sigma_m\sigma_{m+1}$ replace $l_m$. In the first, the
through-strand is under at both crossings; in the second, it is over
at both. The other crossing branches are the oppositely directed arms
of the same cusp. Their signs are opposite for every permitted
through-strand and cusp orientation. After rounding the cusp, the arcs
bound an empty ordinary bigon with one common over-strand: an oriented
Reidemeister-II site. The same upper and lower cusp arms remain after
deletion. Thus $\Delta w=\Delta D=\Delta d=0$.
For right-cusp versions, follow these same local strands backwards;
no global reversal identity for $P$ is assumed.
\end{proof}
```

## ng:front-III — PROVE

reference/SM/sm-3-statesum.tex:1990–1993

```tex
\begin{lemma}[Front type III]\label{ng:front-III}
The front type-III moves preserve $D,w,d$, and hence $B$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ng\_front (C029))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:1994–2006

```tex
\begin{proof}
The words $\sigma_{m+1}\sigma_m\sigma_{m+1}$ and
$\sigma_m\sigma_{m+1}\sigma_m$ form an actual ordinary
Reidemeister-III configuration. Label the three physical strands by
their initial top-to-bottom order. The three over/under choices give
one strict height order, not a cyclic order. Each physical pair crosses
on both sides with the same over/under bit and transported arrows.
An ordinary oriented Reidemeister-III move therefore applies, with
unchanged $D,w,d$ and $B$. In a reflected local template the strict
height order reverses, and an ordinary Reidemeister-III move still
applies. Checking this local template does not identify an entire
diagram with its reflection.
\end{proof}
```

## ng:deletions — PROVE

reference/SM/sm-3-statesum.tex:2008–2013

```tex
\begin{lemma}[Zigzag and crossed-cusp deletion]
\label{ng:deletions}
Deleting an empty zigzag lowers $s$ by two and cannot increase $B$; applying
the crossed-cusp shortcut lowers $s$ by one and cannot increase $B$.
\status{proved (refereed: bench A, 2026-09-05T23:45:25Z and 2026-09-06T01:58:43Z; transcribed from RC ng\_front (C029); round~5: the $s$ consequence of both branches carried into the statement ($\Delta s=-2$ for the zigzag deletion, $-1$ for the crossed-cusp shortcut) and printed at the two displays of the proof, with the citation of Ng at its point of use, F-25-142)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:2014–2044

```tex
\begin{proof}
A zigzag consists of two consecutive cusps with no crossing in an empty
rectangle. Their directions are both downward or both upward: the
strand reverses its $x$ direction twice while continuing its vertical
passage. After rounding, it is a simple ordinary arc, positively page
isotopic relative to its endpoints to the straightened arc. Deletion
therefore gives
\begin{equation}\label{ng:zigzag-counts}
 \Delta w=\Delta d=0,\qquad \Delta D\in\{0,-2\}.
\end{equation}
Thus it cannot increase $B$; the two cusps are removed and no crossing is
touched, so $s$ decreases by two. This covers either oriented destabilization
without a knot-type assertion.

The word procedure also encounters $l_i\sigma_i$ or $\sigma_i r_i$,
a cusp whose own arms cross once. Replace it by the uncrossed cusp with
the same two oriented boundary attachments. After rounding, ordinary
Reidemeister I deletes its empty monogon. The arms are oppositely
directed, so the old crossing has sign $-1$. Deletion raises $w$ by one
and flips the cusp direction because the boundary arms exchange places.
If the old cusp was downward, $\Delta D=-1$; otherwise $\Delta D=1$.
Consequently
\begin{equation}\label{ng:crossed-cusp-counts}
 \Delta d=0,\qquad \Delta w=1,\qquad \Delta B\in\{-2,0\}.
\end{equation}
One crossing is removed and the cusp count is unchanged, so $s$ decreases
by one; this is the compressed dashed-arrow case of Ng's Figure~1
\cite{Ng}. It is not asserted to be a Legendrian isotopy. The direct
ordinary certificate avoids inserting a temporary higher-complexity
front merely to recognize its stabilization.
\end{proof}
```

## ng:circle — PROVE

reference/SM/sm-3-statesum.tex:2046–2051

```tex
\begin{lemma}[Standard front circles]\label{ng:circle}
Deleting a separated standard front circle with nonempty remainder
preserves $B$. A single standard front circle, and any union of such
circles, has $B=0$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ng\_front (C029))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:2052–2071

```tex
\begin{proof}
A simple crossing-free component with exactly one left and one right
cusp has $D=1$, $w=0$ and ordinary value one, in either orientation.
A standard circle separated by the word procedure has no mixed
crossings. Its smoothed component may lie in a bounded face of the
remainder; Lemma~\ref{lp:split-circle} permits this nesting.

For nonempty remainder, $P_{\rm before}=\delta P_{\rm after}$.
The leading $a$ coefficient of $\delta$ is $z^{-1}$, in degree one.
Its product with the leading coefficient of $P_{\rm after}$ is nonzero
because the coefficient ring is an integral domain. Therefore
\begin{equation}\label{ng:circle-counts}
 d_{\rm before}=d_{\rm after}+1,\qquad
 D_{\rm before}=D_{\rm after}+1.
\end{equation}
The writhe is unchanged, so $B_{\rm before}=B_{\rm after}$.
If this is the last component, stop instead: $D=1$ and $w=d=0$ give
$B=0$. Repeated deletion shows that a union of standard front circles
also has $B=0$. No empty-link polynomial or degree is used.
\end{proof}
```

## ng:cusp-skein — PROVE

reference/SM/sm-3-statesum.tex:2076–2083

```tex
\begin{lemma}[Cusp-skein inequality]\label{ng:cusp-skein}
For either principal direction of an oriented cusp-skein interchange,
$B$ of the earlier branch is at least the minimum of $B$ of the other
principal branch and $B$ of the unique compatible smoothing. The
smoothing has one fewer singularity; the principal branches have the
same singularity count.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ng\_front (C029))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:2084–2165

```tex
\begin{proof}
Omitting spectator strands, label one left endpoint $L$ and three
right endpoints $1,2,3$ from top to bottom. Put
\begin{equation}\label{ng:cusp-words}
 A=l_2\sigma_1,\qquad A'=l_1\sigma_2,\qquad
 C_{\rm top}=l_1,\qquad C_{\rm bottom}=l_2.
\end{equation}
Both $A$ and $A'$ pair $L$ with $2$ and $1$ with $3$. The $L$--$2$
strand is the through-strand; the other contains the cusp. In $A$ the
through-strand is over, whereas in $A'$ the cusp strand is over.
Each strand encounters the one crossing once. Exchanging over and under
at that crossing makes their local ordered crossing records identical,
including the boundary attachments. After gluing any same actual
exterior, the full named records are identical. Thus their polynomial
values are the two crossing choices at one ordinary skein site. The
move before that over/under exchange is not asserted to be page isotopy.

Let $t=1$ for the orientation from $L$ to $2$, and $t=-1$ otherwise.
Let $u=1$ for the orientation from $1$ to $3$, a downward cusp, and
$u=-1$ otherwise. In $A$, the cusp's upper arm has $x$ direction $-u$;
in $A'$, the cusp's lower arm has $x$ direction $u$. The crossing
determinant rule gives signs $-tu$ and $tu$, respectively:
\begin{center}
\begin{tabular}{@{}ccccc@{}}
$(t,u)$ & $\operatorname{sign}(A)$ & $\operatorname{sign}(A')$
 & Compatible smoothing & Local $D$ in $A,A',C$\\
\hline
$(+,+)$ & $-1$ & $+1$ & $C_{\rm top}$    & $1$\\
$(+,-)$ & $+1$ & $-1$ & $C_{\rm bottom}$ & $0$\\
$(-,+)$ & $+1$ & $-1$ & $C_{\rm bottom}$ & $1$\\
$(-,-)$ & $-1$ & $+1$ & $C_{\rm top}$    & $0$
\end{tabular}
\end{center}
Oriented smoothing joins each incoming strand to the other outgoing
strand. If $t=u$, it pairs $1$ with $2$ and $L$ with $3$: the top cusp
and through-strand. If $t=-u$, it pairs $L$ with $1$ and $2$ with $3$:
the bottom cusp and through-strand. The new cusp direction is $u$ in
either case, from $1$ to $2$ or from $2$ to $3$. This proves the last
column without any hypothesis on how the exterior joins the two strands.
Smoothing may split or join parameter components, but cannot create an
empty diagram. Only the one compatible smoothing is used, never both
unoriented smoothings.

Let $E_+,E_-,E_0$ be these actual ordinary skein diagrams. Their writhes
are $w_0+1,w_0-1,w_0$, where $w_0$ is the common exterior writhe.
Solving the skein relation separately in the two directions gives
\begin{equation}\label{ng:skein-plus}
 P_+=a^{-2}P_-+a^{-1}zP_0
\end{equation}
and
\begin{equation}\label{ng:skein-minus}
 P_-=a^2P_+-azP_0.
\end{equation}
The degree of a nonzero sum is at most the maximum of the summand
degrees. Multiplication by $a^k$ shifts degree by $k$, and multiplication
by $z$ does not change it. Equation~\eqref{ng:skein-plus} yields
$d_+\leq\max\{d_--2,d_0-1\}$. Adding $w_0+2$ gives
\begin{equation}\label{ng:degree-plus}
 d_++1+(w_0+1)
 \leq\max\{d_-+1+(w_0-1),\ d_0+1+w_0\}.
\end{equation}
Equation~\eqref{ng:skein-minus} instead yields
$d_-\leq\max\{d_++2,d_0+1\}$. Adding $w_0$ gives
\begin{equation}\label{ng:degree-minus}
 d_-+1+(w_0-1)
 \leq\max\{d_++1+(w_0+1),\ d_0+1+w_0\}.
\end{equation}
The table and unchanged exterior give the same downward-cusp count
in all three diagrams. Subtracting~\eqref{ng:degree-plus} and,
respectively,~\eqref{ng:degree-minus} from this common number proves
\begin{equation}\label{ng:skein-defect}
 \begin{aligned}
 B(A)&\geq\min\{B(A'),B(C)\},\\
 B(A')&\geq\min\{B(A),B(C)\}.
 \end{aligned}
\end{equation}
Here $C$ is the compatible smoothing. It has one fewer crossing and
the same number of cusps, so $s(C)=s(A)-1=s(A')-1$; the principal
crossing-change branch preserves $s$. Reflected and right-cusp templates
follow by relabeling their actual attachments and arrows in this local
calculation, not from a global reflection equality for $P$.
\end{proof}
```

## ng:finite-word — AXIOM

reference/SM/sm-3-statesum.tex:2170–2206

```tex
\begin{literature}[Finite front-word reduction]\label{ng:finite-word}
For an actual finite front word on the domain of
Definition~\ref{ng:front-domain}, the procedure of Ng
\cite[pp.~6--8 and Figure~1]{Ng} and the elementary-word proof of
Rutherford \cite[Lemma~3.2, pp.~8--12 of the arXiv version]{Rutherford}
supplies a finite principal chain using:
\begin{enumerate}
\item typed disjoint-gadget commutations and the three local front moves
  in Lemmas~\ref{ng:front-I}, \ref{ng:front-II} and~\ref{ng:front-III};
\item the cusp-skein crossing interchange~\eqref{ng:cusp-words}, or its
  reflected pattern;
\item zigzag deletion, the crossed-cusp shortcut of
  Lemma~\ref{ng:deletions}, or deletion of a separated standard front
  circle.
\end{enumerate}
Stop at the first strict decrease of $s$ or at the standard-circle base.
Before that decrease the selected procedure does not increase $s$.
Secondary progress is measured at the boundaries of complete finite
blocks of the word procedure: a completed nonterminal block moves a
singularity to the left of the selected rightmost left cusp, and hence
decreases the number on its right. This is not a strict decrease at
every individual elementary move. Arm-string extension within a block
is bounded by the active strand count. Thus every nonbase front has a
finite principal chain to a front of smaller $s$. At each cusp-skein
interchange, the compatible smoothing branch has smaller $s$ than the
front at that stage.

This is the constructive word procedure, not a quantification over
arbitrary Legendrian isotopies. The imported content is the source's finite
descent, not its printed sentence: Ng's Lemma~1 gives one step, iterated
here until $s$ decreases; Rutherford's two ruling-polynomial terminal
branches are replaced here by the geometric shortcuts of
Lemma~\ref{ng:deletions}; and the finiteness of arm-string extension, which
Rutherford asserts, is given its reason here (seat L-3/L-4 on SM2, R6;
F-25-83).
\status{lit: finite Ng--Rutherford word procedure; Registry~\ref{reg:slbound}; round~3: the scope of the import stated, F-25-83}
\end{literature}
```

## ng:local-front-bound — PROVE

reference/SM/sm-3-statesum.tex:2305–2313

```tex
\begin{theorem}[Individual-front polynomial bound]
\label{ng:local-front-bound}
For every front $F$ on the domain of Definition~\ref{ng:front-domain},
with the same polynomial evaluated on its actual ordinary cusp rounding,
\begin{equation}\label{ng:front-inequality}
 w(F)-D(F)\leq-\deg_a P_{S(F)}-1.
\end{equation}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z, 2026-09-06T00:12:27Z and 2026-09-06T01:50:42Z; transcribed from RC ng:local-front-bound (C029); consumes Literature input~\ref{ng:finite-word})}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:2314–2348

```tex
\begin{proof}
Use strong induction on $s(F)$; the quantity $d(F)=\deg_aP_{S(F)}$ of
display~\eqref{ng:defect} does not depend on the rounding $S(F)$, by
Lemma~\ref{ng:smoothing-record}. Every nonempty component has at least
one left and one right cusp. Thus the base $s=2$ is a standard circle,
and Lemma~\ref{ng:circle} gives $B=0$. Any union of standard front
circles encountered as a terminal base also has $B=0$. An empty object
is never evaluated.

Suppose the assertion holds for all fronts with smaller $s$ than $F$.
Take the finite principal chain of Literature input~\ref{ng:finite-word},
stopped at its first strict decrease or at a standard-circle base.
Every preterminal principal front has $s$ at most $s(F)$. At each
cusp-skein step, its compatible smoothing therefore has strictly smaller
$s$ than $F$, and strong induction gives nonnegative $B$ for it. The
final principal front has nonnegative $B$ by the same induction or by
its explicit standard-circle base.

Traverse the chain backwards. Commutations and local front moves
preserve $B$ by Lemmas~\ref{ng:commutation}, \ref{ng:front-I}, \ref{ng:front-II}
and~\ref{ng:front-III}.
A deletion cannot increase $B$ in the forward direction, by
Lemmas~\ref{ng:deletions} and~\ref{ng:circle}; nonnegativity after
deletion therefore implies nonnegativity before it. At a cusp-skein
step, the later principal branch and its smaller smoothing branch both
have nonnegative $B$. The appropriate inequality
of Lemma~\ref{ng:cusp-skein}, display~\eqref{ng:skein-defect}, gives nonnegative $B$ for the earlier
principal branch. These are all possible operations. Finite backward
propagation yields $B(F)\geq0$, completing strong induction.
Substituting~\eqref{ng:defect} gives~\eqref{ng:front-inequality}.

Nonvanishing is used before every degree, including both skein branches
and the split product. Cancellation in sums was allowed. The proof
covers arbitrary positive component counts and all orientations.
\end{proof}
```

## fd:transverse-neighborhood — PROVE

reference/SM/sm-3-statesum.tex:2395–2410

```tex
\begin{lemma}[A transverse neighbourhood and its Legendrian pushoff]
\label{fd:transverse-neighborhood}
Let $\alpha=dz-y\,dx$ and let
$T:\RR/(2\pi\mathbb Z)\to\RR^3$ be a smooth embedded oriented circle
with $\alpha(T')>0$. There are $\delta>0$ and a smooth embedding
$H:S^1\times D_\delta\to\RR^3$ fixing the parametrized core $T$ such that
\begin{equation}\label{fd:transverse-model}
 H^*\alpha=h\alpha_0,\qquad
 \alpha_0=d\theta+u\,dv-v\,du,\qquad h>0.
\end{equation}
There is an oriented Legendrian knot $L$ in this neighbourhood whose
positive transverse pushoff is transversely isotopic to $T$. An explicit
compactly supported ordinary ambient isotopy carries the parametrized
$L$ to the parametrized $T$, preserving their orientations.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2d\_contact\_constructions (C030))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:2411–2559

```tex
\begin{proof}
Write $T=(x,y,z)$, $a=\alpha(T')>0$, and $c=\sqrt{2a}$.
The global frame $E_1=\partial_x+y\partial_z$, $E_2=\partial_y$ spans
$\ker\alpha$, and $d\alpha(E_1,E_2)=1$. Set
\begin{equation}
 F(\theta,u,v)=T(\theta)+c(\theta)
       \bigl(uE_1(T(\theta))+vE_2(T(\theta))\bigr).
\end{equation}
At the core its derivative has independent columns $T',cE_1,cE_2$:
applying $\alpha$ to a relation first kills the $T'$ coefficient.
The inverse function theorem and compactness give a common radius on
which every derivative is invertible. This radius can be decreased so
that $F$ is injective: otherwise two distinct points with disc radii
tending to zero have equal images; limiting circle parameters coincide
because $T$ is embedded, placing both points in one local inverse chart,
a contradiction. Thus $F$ embeds a product neighbourhood.

Put $\beta=F^*\alpha/a(\theta)$. At the core $\beta=d\theta$ and
\begin{equation}
 d\beta(\partial_u,\partial_v)
 =a^{-1}d\alpha(cE_1,cE_2)=c^2/a=2.
\end{equation}
The derivative of $a^{-1}$ vanishes on this vertical pair. Consequently
$\alpha_t=(1-t)\alpha_0+t\beta$ satisfies
$(\alpha_t\wedge d\alpha_t)(\partial_\theta,\partial_u,\partial_v)=2$
on the core. Compactness of $[0,1]\times S^1$ supplies a common smaller
neighbourhood where every $\alpha_t$ is contact and
$\alpha_t(\partial_\theta)>0$.

Let $\nu=\beta-\alpha_0$ and define
\begin{align}
 X_1&=\partial_u-
   \frac{\alpha_t(\partial_u)}{\alpha_t(\partial_\theta)}\partial_\theta,
 &X_2&=\partial_v-
   \frac{\alpha_t(\partial_v)}{\alpha_t(\partial_\theta)}\partial_\theta,
 \\
 D_t&=d\alpha_t(X_1,X_2),
 &V_t&=\frac{\nu(X_1)X_2-\nu(X_2)X_1}{D_t}.
\end{align}
The $X_i$ form a basis of $\ker\alpha_t$; contactness makes $D_t\ne0$.
Evaluation on each $X_i$ gives
\begin{equation}
(\iota_{V_t}d\alpha_t)|_{\ker\alpha_t}=-\nu|_{\ker\alpha_t}
\end{equation}
The vector field $V_t$ vanishes on the core, since $\nu$ does.
Choose $\rho>0$ so that $S^1\times\overline D_\rho$ lies strictly
inside the common neighbourhood where $V_t$ is smooth for every
$t\in[0,1]$. On this closed product its norm is at most
$C\sqrt{u^2+v^2}$ uniformly in $t,\theta$. Along a trajectory,
$(u^2+v^2)'\leq2C(u^2+v^2)$, hence
$r(t)\leq e^{Ct}r(0)$. Choosing the initial disc radius below
$\rho e^{-C}/2$ keeps the flow in a compact inner product neighbourhood
for $0\leq t\leq1$. Smooth ODE existence, continuation and uniqueness
give a flow $\Phi_t$, fixing the core and invertible onto its image.

The covector $\nu+\iota_{V_t}d\alpha_t$ annihilates $\ker\alpha_t$,
so it is $\mu_t\alpha_t$ for a smooth scalar $\mu_t$.
Since $\alpha_t(V_t)=0$, Cartan's differentiation identity gives
\begin{align}
 \frac{d}{dt}\Phi_t^*\alpha_t
 &=\Phi_t^*(\nu+\mathcal L_{V_t}\alpha_t)\notag\\
 &= (\mu_t\circ\Phi_t)\Phi_t^*\alpha_t.
\end{align}
Solving this scalar equation gives
$\Phi_1^*\beta=\exp(\int_0^1\mu_t\circ\Phi_t\,dt)\alpha_0$.
For $H=F\circ\Phi_1$, the additional factor
$a\circ\operatorname{pr}_\theta\circ\Phi_1$ is also positive, proving
\eqref{fd:transverse-model}, including coorientation and core orientation.

Choose an integer $N>0$ with $b=N^{-1/2}<\delta$. The embedded circle
\begin{equation}
 L_0(\theta)=(\theta,b\cos N\theta,-b\sin N\theta)
\end{equation}
has $\alpha_0(L_0')=1-Nb^2=0$; its degree-one first coordinate makes it
an embedding. Hence $L=H\circ L_0$ is Legendrian. Fix $\kappa\ne0$ and
a small $\epsilon>0$ with $b+\epsilon<\delta$, and put
\begin{equation}
 B(\theta,s)=
 (\theta+\kappa s,(b-s)\cos N\theta,-(b-s)\sin N\theta),
 \qquad -\epsilon<s\leq b.
\end{equation}
Radius $b-s$ and the first coordinate prove injectivity. The radial
derivative proves immersion for $s<b$; at $s=b$ it remains independent
of $\partial_\theta$, and the Cartesian formula is smooth there.
Direct differentiation yields
\begin{equation}\label{fd:pushoff-annulus}
 B^*\alpha_0=\bigl(1-N(b-s)^2\bigr)d\theta+\kappa\,ds.
\end{equation}
Thus the annulus is transverse to the contact planes, even along $s=0$.
Its circles are negative transverse for $s<0$, Legendrian at $s=0$,
and positive transverse for $0<s\leq b$. A sufficiently small positive
circle is therefore the positive pushoff in the source convention.
The whole family from that circle to $s=b$ is a transverse isotopy to
$T(\theta+\kappa b)$, which is the same oriented transverse knot.
Finally $H\circ B$ on $S^1\times[0,b]$ is an embedded oriented annulus
with boundary $L-T$. To prove the stronger ambient-isotopy conclusion
needed by the polynomial, we give such an isotopy explicitly.
Write $v(\theta)=b(\cos N\theta,-\sin N\theta)$, choose
$\epsilon_0=(\delta-b)/4$, and put
$R_1=b+\epsilon_0$, $R_2=b+2\epsilon_0$.
Thus $b<R_1<R_2<\delta$. For
$\eta(s)=e^{-1/s}$ when $s>0$ and $\eta(s)=0$ when $s\leq0$, set
\begin{equation}
 \chi(s)=\frac{\eta(R_2^2-s)}
 {\eta(R_2^2-s)+\eta(s-R_1^2)}.
\end{equation}
Every positive-side derivative of $\eta$ is $e^{-1/s}$ times a
polynomial in $1/s$, tending to zero at zero; hence $\eta$ is smooth.
The denominator is positive because $R_1<R_2$. Thus $\chi$ is smooth,
equals one for $s\leq R_1^2$ and zero for $s\geq R_2^2$.
The smooth product vector field
\begin{equation}
 V(\theta,w)=\bigl(0,-\chi(|w|^2)v(\theta)\bigr)
\end{equation}
is well defined on the circle since $N$ is integral. Squared radius
makes it smooth at $w=0$; its support lies in
$S^1\times\overline D_{R_2}$. The embedding $H$ has an open image
$U$ and a smooth inverse there by the inverse function theorem.
Push $V$ forward by $H$ on $U$ and extend by zero outside $U$.
This field $X$ is globally smooth: its support lies in the compact
set $K=H(S^1\times\overline D_{R_2})\subset U$, and it vanishes
on a neighbourhood of every point outside $K$.

The field $X$ is bounded, so a trajectory moves a distance at most
$M|t|$ on any finite time interval. Smooth ODE continuation gives
its global flow $\Psi_t$ for every real $t$. Uniqueness gives the
smooth inverse $\Psi_{-t}$; thus these are ambient diffeomorphisms.
They fix every point outside $K$. Their derivative determinants
start positive and never vanish, so they preserve ambient orientation.
Extending them by the identity at infinity gives an ambient isotopy
of the oriented three-sphere, with the same compact support.

For $0\leq t\leq1$, the path $(\theta,(1-t)v(\theta))$ stays
at radius at most $b<R_1$, where $\chi=1$, and its time derivative
is exactly $V$. The chain rule and ODE uniqueness therefore give
\begin{equation}\label{fd:helix-ambient-isotopy}
 \Psi_t(L(\theta))=H(\theta,(1-t)v(\theta)),\qquad
 \Psi_1(L(\theta))=T(\theta).
\end{equation}
The parameter $\theta$ is unchanged, so the endpoint circle orientation
is exactly that of $T$. The core need not be fixed: its own track is
$\Psi_t(T(\theta))=H(\theta,-t v(\theta))$ on this interval.
There is thus no collapse of two distinct curves by a diffeomorphism.
This is an ordinary ambient isotopy, not a contact isotopy. Indeed
the model form on its tracked knot has value
$1-Nb^2(1-t)^2=2t-t^2>0$ for $0<t\leq1$, whereas the initial
knot is Legendrian. The preceding twisted annulus, not this ambient
extension, remains the positive-pushoff and transverse-isotopy producer.
\end{proof}
```

## fd:parameter-avoidance — PROVE

reference/SM/sm-3-statesum.tex:2561–2570

```tex
\begin{lemma}[Compact parameter avoidance]\label{fd:parameter-avoidance}
Let $K$ be a compact subset of a smooth $d$-dimensional coordinate
manifold and $B\subset\RR^m$ a closed parameter ball. Suppose that
$F$ is smooth on a neighbourhood of $K\times B$, takes values in
$\RR^q$, and has derivative of rank $q>d$ at every zero in that product.
The parameters $a$ for which $F(t,a)=0$ for some $t\in K$ form a closed
set with empty interior. The same assertion holds simultaneously for
a finite collection of such maps.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC d2d\_contact\_constructions (C030))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:2571–2584

```tex
\begin{proof}
The zero set is compact, so its parameter projection is closed.
At each zero a nonzero $q$-minor and the inverse function theorem express
the local zero set as a smooth graph of $e=d+m-q<m$ variables.
Finitely many such charts restricted to compact cubes cover the zero
set; their parameter projections are Lipschitz maps of those cubes.
Subdividing an $e$-cube into $O(n^e)$ pieces of side $O(n^{-1})$ covers
its projected image by $m$-boxes of total volume $O(n^{e-m})$.
This tends to zero. The image cannot contain a fixed open $m$-box,
because any finite box cover has total volume at least the covered
volume: partition at the finitely many box faces to prove this inequality.
A finite union of the chart images has the same estimate. This proves
empty interior and the finite-collection assertion without Sard's theorem.
\end{proof}
```

## fd:contact-motions — PROVE

reference/SM/sm-3-statesum.tex:2586–2597

```tex
\begin{lemma}[Explicit contact motions]\label{fd:contact-motions}
For a smooth compactly supported $H:\RR^3\to\RR$, the vector field
\begin{equation}
 X_H=-H_y\partial_x+(H_x+yH_z)\partial_y+(H-yH_y)\partial_z
\end{equation}
has a global flow $\phi_H^s$ of coorientation-preserving contact
diffeomorphisms for $\alpha=dz-y\,dx$: $(\phi_H^s)^*\alpha=c^H_s\,\alpha$
with a smooth positive function $c^H_s$, its \emph{conformal factor}. Finite compositions of their
small-time flows depend smoothly on the times and are arbitrarily
$C^k$-close to the identity on compact sets for each fixed finite $k$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z and 2026-09-06T01:50:42Z; transcribed from RC d2d\_contact\_constructions (C030))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:2598–2611

```tex
\begin{proof}
Substitution gives $\alpha(X_H)=H$ and
$\iota_{X_H}d\alpha=H_z\alpha-dH$; therefore
$\mathcal L_{X_H}\alpha=H_z\alpha$. Differentiating the pullback and
solving the resulting scalar ODE gives
\begin{equation}
 (\phi_H^s)^*\alpha
 =\exp\left(\int_0^s H_z\circ\phi_H^v\,dv\right)\alpha.
\end{equation}
This exponential is the conformal factor $c^H_s$; it is positive. The vector field is smooth, compactly supported
and bounded; trajectories cannot escape to infinity in finite time.
ODE continuation gives all finite times, and backwards uniqueness gives
the inverse. Smooth ODE dependence proves the last assertion.
\end{proof}
```

## fd:generic-front — PROVE

reference/SM/sm-3-statesum.tex:2613–2630

```tex
\begin{theorem}[A generic front preserving the chosen positive pushoff]
\label{fd:generic-front}
Every smooth oriented Legendrian embedding $L:S^1\to\RR^3$ admits
a smooth ambient coorientation-preserving contact isotopy to a
Legendrian embedding $L_g$ whose $xz$ front has only finitely many
semicubical cusps and transverse double points, with no triple point
and no cusp on another branch. At each cusp there is a smooth local
coordinate $u=y-y_0$ in which
\begin{equation}\label{fd:generic-exact-germ}
 x=x_0+Au^2,\qquad y=y_0+u,\qquad
 z=z_0+Ay_0u^2+\tfrac23 Au^3,\qquad A\ne0;
\end{equation}
the coordinate $u$ may increase or decrease along the prescribed
orientation. The isotopy carries a chosen thin
positive-pushoff annulus and preserves its positive-pushoff transverse
isotopy class, as well as the oriented topological knot type.
\status{proved (refereed: bench A, 2026-09-06T00:35:51Z and 2026-09-06T01:58:43Z; transcribed from RC d2d\_contact\_constructions (C030); round~3: the exact cusp germ its last proof step establishes exported to the conclusion, F-25-86 (Codex R-P5, P-25-11); round~5: the conformal factor of the concatenated contact isotopy named $c_s$ and derived from Lemma~\ref{fd:contact-motions}, the cusp-germ function renamed $\psi$ and the second-derivative matrix $M$, a departure from RC's letters, F-25-154)}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:2631–2783

```tex
\begin{proof}
Write $L=(x,y,z)$, so $z'=yx'$. For finitely many compactly supported
Hamiltonians, let $\Phi_a$ be the composition of their time-$a_i$ flows.
At $a=0$, the $a_i$ derivative of $\Phi_a\circ L$ is $X_{H_i}\circ L$.
The path $s\mapsto\Phi_{sa}$ is an ambient contact isotopy by
Lemma~\ref{fd:contact-motions}; its images are exactly Legendrian
embeddings, without an approximation or an area-closing correction.

First remove simultaneous zeros of $(x',x'')$. At such a point
$\theta_0$, immersion and $z'=yx'=0$ imply $y'(\theta_0)\ne0$.
With $y_0=y(\theta_0)$, choose Hamiltonians equal near $L(\theta_0)$ to
\begin{equation}
 H_2=-\tfrac12(y-y_0)^2,\qquad H_3=-\tfrac16(y-y_0)^3,
\end{equation}
and multiply them by a smooth bump equal to one there. Their
infinitesimal $x$ changes are $y-y_0$ and $(y-y_0)^2/2$.
Thus their derivative columns for $(x',x'')$ at $\theta_0$ are
$(y',y'')^T$ and $(0,(y')^2)^T$, with determinant $(y')^3\ne0$.
Finitely many such minor neighbourhoods cover the initial compact zero
set. On their compact complement $|(x',x'')|$ has a positive minimum.
Continuity therefore supplies a small parameter ball in which every
possible zero retains one of the nonzero minors. Apply
Lemma~\ref{fd:parameter-avoidance} with $d=1,q=2$ to choose a small
parameter avoiding all these zeros. If the initial zero set is empty,
this step is unnecessary. Call the result $L_1$.
Every zero of $x_1'$ is simple, so compactness makes their number finite.
At each of them $y_1'\ne0$ by immersion and Legendrianity.

We next supply a uniform collar of the parameter diagonal. Cover $S^1$
by finitely many interiors of closed intervals of two kinds: regular
intervals where $x_1'$ has fixed nonzero sign, and critical intervals
where $x_1''$ and $y_1'$ have fixed nonzero signs and the endpoint signs
of $x_1'$ are opposite. On the first kind $x_1$ is strictly monotone.
On a critical interval there is one critical point $\theta_c$.
For two points on opposite sides with equal $x$ coordinate $X$,
the inverse branches and $dz=y\,dx$ give
\begin{equation}
 z_1(\theta_+)-z_1(\theta_-)
 =\int_{x_1(\theta_c)}^X
     \bigl[y_1(\theta_+(v))-y_1(\theta_-(v))\bigr]\,dv\ne0.
\end{equation}
The integrand has a fixed strict sign by monotonicity of $y_1$;
the integration interval has nonzero length. The formula also handles
a maximum by reversing the integration sign. The front is therefore
injective on each interval. Retaining the finitely many derivative and
endpoint-sign margins preserves this argument for every sufficiently
$C^2$-close Legendrian embedding. A Lebesgue number $\delta>0$ of the
finite interval cover gives uniform front injectivity for every pair
of distinct parameters at circular distance less than $\delta$.
This Lebesgue number follows from compactness: a sequence of pairs of
diameter tending to zero and contained in no cover interval would
converge to a point inside one of those open intervals.

Let $K_2$ be the compact ordered-pair set with distance at least $\delta$,
and $K_3$ the compact ordered-triple set with every pairwise distance at
least $\delta$. Write $p_a=(x_a,z_a)$. The bad configurations are zeros of
\begin{align}
 C(\theta,\eta,a)&=
  \bigl(x_a'(\theta),p_a(\theta)-p_a(\eta)\bigr)\in\RR^3,
 \\
 R(\theta,\eta,\tau,a)&=
  \bigl(p_a(\theta)-p_a(\eta),p_a(\theta)-p_a(\tau)\bigr)\in\RR^4.
\end{align}
At a zero of $C$ for $a=0$, use disjoint small balls about the two
distinct spatial points. The preceding $H_2$ at the first point
changes $x'(\theta)$ by $y_1'(\theta)\ne0$ but changes neither $x,z$
there. At the second point $q$, Hamiltonians equal locally to
$H^x=-(y-y_q)$ and $H^z=1$ have independent $(x,z)$ velocities
$(1,y_q)^T$ and $(0,1)^T$. Their supports avoid the first point.
Hence $C$ has parameter rank three. At a zero of $R$, choose disjoint
balls at the three distinct spatial points and use the same two
Hamiltonians at the second and third points only. The two independent
blocks give parameter rank four.

Choose finitely many such Hamiltonians covering both initial compact
zero sets. A zero-free initial map has a positive norm minimum and
needs no Hamiltonians. The nonzero minors persist near those zero
sets; the positive norm on their compact complements excludes new
zeros there for small parameters. Shrink the parameter ball also to
retain the preceding uniform local-injectivity margins. Apply
Lemma~\ref{fd:parameter-avoidance} simultaneously with $(d,q)=(2,3)$
and $(3,4)$, and choose a parameter outside both bad projections.
The resulting $L_2$ has no cusp on another branch and no triple point.

At any remaining double point both parameters are regular. Their
$y$ values differ, since otherwise all three spatial coordinates
coincide, contradicting embeddedness. The two front tangents have
determinant
\begin{equation}
 x'(\theta)x'(\eta)\bigl(y(\eta)-y(\theta)\bigr)\ne0.
\end{equation}
Thus every double point is transverse and isolated by the inverse
function theorem applied to $p(\theta)-p(\eta)$. Their ordered-pair
set is closed in compact $K_2$, so there are finitely many: an infinite
set would accumulate at another zero, contradicting isolation.
All properties so far persist under sufficiently small $C^2$
Legendrian perturbations. Indeed the local-injectivity margins persist,
and the now nowhere-zero maps $C,R,(x',x'')$ have positive norm minima
on their respective compact domains.

We finally make each cusp germ exactly semicubical, without a
singularity-normal-form assumption. At an $x$-critical point,
$y'\ne0$ allows $y$ as a local parameter. Write $x=f(y)$ and put
\begin{equation}
 u=y-y_0,\quad A=\tfrac12 f''(y_0)\ne0,\quad
 q(y)=f(y_0)+Au^2,\quad
 \psi(y)=\int_{y_0}^y(f(v)-q(v))\,dv.
\end{equation}
Here $\psi=O(u^4)$ and its first three derivatives have orders
$O(u^3),O(u^2),O(u)$. Where $H=\psi(y)$ the contact flow is exactly
\begin{equation}
 (x,y,z)\longmapsto
 (x-s\psi'(y),y,z+s(\psi(y)-y\psi'(y))).
\end{equation}
At time one, $x=q(y)$ and Legendrianity gives
\begin{equation}
 x=x_0+Au^2,\qquad z=z_0+Ay_0u^2+\tfrac23Au^3.
\end{equation}
The invertible affine page coordinates
$X=(x-x_0)/A$ and $Z=3(z-z_0-y_0(x-x_0))/(2A)$ give $(X,Z)=(u^2,u^3)$.

Multiply $\psi(y)$ by a smooth spatial cutoff equal to one on an inner
ball about the cusp and supported in a ball of radius $O(\epsilon)$
meeting no other portion of the embedded knot. Its derivatives of
order $k$ are $O(\epsilon^{-k})$, so the derivatives of $H$ through
order three are $O(\epsilon^{4-k})$. The vector field and its first
two derivatives are consequently $O(\epsilon)$ on the support.
The time-one flow is $C^2$-close to the identity: differentiating its
ODE gives $J'=DX_H J$ and
$M'=DX_H M+D^2X_H[J,J]$, with initial values $I,0$, and the elementary
exponential estimate bounds $J-I,M$ by $O(\epsilon)$.
An inner subarc has displacement $O(\epsilon^3)$ and a gap of order
$\epsilon$ to the boundary of the region where the cutoff equals one.
Its whole flow therefore uses the exact displayed formula.
Finitely many disjoint cusp balls and sufficiently small radii retain
all previous genericity margins, including those in the transition
regions. This gives the required exact cusp germs without new crossings.

Concatenate the constructed contact isotopies, using smooth time
reparametrizations flat at the joins. Each of them is a composition of
flows of Lemma~\ref{fd:contact-motions}, so $\Phi_s^*\alpha=c_s\,\alpha$ with
$c_s>0$ the product of their conformal factors. If $B$ is the chosen thin
pushoff annulus and $K$ its positive parallel circle, then
$\Phi_s\circ B$ remains a transverse annulus and
\begin{equation}
 \alpha((\Phi_s\circ K)')=(c_s\circ K)\,\alpha(K')>0.
\end{equation}
Its central circle is the Legendrian isotope and its positive parallel
circle is a positive pushoff thereof. Thus the chosen pushoff moves
through positive transverse embeddings. The ambient isotopy also
preserves the oriented topological knot type. No contact-isotopy
extension or approximation-uniqueness theorem is used.
\end{proof}
```

## fd:linking-calculus — PROVE

reference/SM/sm-3-statesum.tex:2785–2826

```tex
\begin{lemma}[Linking calculus and uniform transverse framing]
\label{fd:linking-calculus}
For two disjoint smooth oriented parametrized circles $C_1,C_2$ in
oriented $\RR^3$, use the normalized linking pairing
\begin{equation}\label{fd:gauss-linking}
 \ell(C_1,C_2)=\frac1{4\pi}\int_{S^1\times S^1}
       G\cdot(G_u\times G_v)\,du\,dv,
 \qquad G(u,v)=\frac{C_2(v)-C_1(u)}{|C_2(v)-C_1(u)|}.
\end{equation}
It is symmetric and is constant under smooth families of disjoint
oriented pairs. Call a direction $\nu\in S^2$ \emph{generic for the pair} if at
every parameter pair $(u,v)$ at which $C_2(v)-C_1(u)$ is parallel to $\nu$
the tangents of the two circles projected along $\nu$ are linearly
independent; the projection along such a $\nu$ displays the pair with
finitely many transverse mixed crossings. Let $\nu$ point toward the
observer and orient the projection plane so that its positive basis followed
by $\nu$ is positive in $\RR^3$; at a mixed crossing the strand nearer the
observer is over. Then $\ell(C_1,C_2)$ equals one half the sum over the
mixed crossings of the overpass-first sign $\sgn\det(u_{\rm o},u_{\rm u})$
of the projected over and under tangents.
Thus it has exactly the linking normalization used in the source's
front calculations.

More generally, let $C_s$, $0\leq s\leq1$, be a smooth family of embedded oriented
circles and let $v_s$ be a smooth vector field along them, everywhere
linearly independent of $\partial_uC_s$. One common sufficiently small
positive $\epsilon$ gives disjoint framed pairs
$(C_s,C_s+\epsilon v_s)$ throughout the family. Their pairing is
independent of that radius and of $s$. This includes a homotopy of
normal framings on a fixed curve.

If $T_s:S^1\to\RR^3$, $0\leq s\leq1$, is a smooth family of
embeddings with $(dz-y\,dx)(\partial_uT_s)>0$, there is one
$\epsilon_0>0$ such that $T_s$ and $T_s+\epsilon\partial_y$ are
disjoint positive transverse embeddings for every $s$ and
$0<\epsilon\leq\epsilon_0$. The number
\begin{equation}\label{fd:framed-linking}
            sl(T_s)=\ell(T_s,T_s+\epsilon\partial_y)
\end{equation}
is independent of such $\epsilon$ and of $s$.
\status{proved (refereed: bench A, 2026-09-06T00:35:51Z and 2026-09-06T01:58:43Z; transcribed from RC d2d\_contact\_constructions (C030); round~3: the convention sentence moved to Remark~\ref{rem:sl-convention}, F-25-81; round~5: the projection-genericity class of the mixed-crossing clause defined in the statement (a direction regular for the pair) and the observer direction and plane orientation that fix its sign stated there, as its proof uses them, F-25-155)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:2827–3010

```tex
\begin{proof}
The denominator in \eqref{fd:gauss-linking} is bounded away from zero
on the compact parameter torus. It remains so uniformly in any compact
smooth family of disjoint pairs. All derivatives and differentiations
under the integral are therefore ordinary smooth calculus on a compact
domain. The integrand can equivalently be written
\begin{equation}\label{fd:gauss-integrand}
 \frac{(C_1(u)-C_2(v))\cdot(C'_1(u)\times C'_2(v))}
 {|C_1(u)-C_2(v)|^3}.
\end{equation}
Indeed radial derivative terms disappear in the determinant, and the
derivative in $u$ has the sign from $-C'_1$. Exchanging the two curves
negates both the difference vector and the cross product, leaving this
scalar unchanged after exchanging the integration variables. This proves
symmetry, including the source's possible ordering of the pushoff first.

For a smooth family $G(u,v,s)$ into the unit sphere set
\begin{equation}
 A=G\cdot(G_u\times G_v),\qquad
 B=G\cdot(G_s\times G_v),\qquad
 C=G\cdot(G_u\times G_s).
\end{equation}
The vectors $G_u,G_v,G_s$ all lie in the two-dimensional plane
orthogonal to $G$. Hence every scalar triple product of these three
vectors vanishes. On expanding the three derivatives, the two terms
containing $G_{uv}$ cancel because the cross product is antisymmetric;
the remaining terms match by equality of mixed derivatives. Explicitly,
\begin{align}
 \partial_s A
 &=G\cdot(G_{us}\times G_v+G_u\times G_{vs}),\notag\\
 \partial_u B+\partial_v C
 &=G\cdot(G_{su}\times G_v+G_s\times G_{vu}
                   +G_{uv}\times G_s+G_u\times G_{sv})\notag\\
 &=\partial_s A.
 \label{fd:gauss-divergence}
\end{align}
Integrating a full period in $u$ kills $\partial_u B$ by the
fundamental theorem of calculus; integrating a full period in $v$
kills $\partial_v C$. Thus the derivative of
\eqref{fd:gauss-linking} is zero. This is a direct calculation, not
an appeal to invariance of degree or to an ambient-isotopy theorem.

We verify the normalization used in a generic diagram. Let $\omega$
be the outward sphere area form divided by $4\pi$. In positively
oriented Cartesian coordinates $(X,Y,Z)$ on the unit sphere, put
\begin{equation}\label{fd:sphere-primitive}
 \lambda_N=-\frac{X\,dY-Y\,dX}{4\pi(1-Z)}
          \quad\hbox{on }S^2\setminus\{N\},\qquad N=(0,0,1).
\end{equation}
This is smooth also at the south pole. In polar coordinates about
$N$, it is $-(1+\cos\theta)d\phi/(4\pi)$; differentiation
gives $\sin\theta\,d\theta\wedge d\phi/(4\pi)=\omega$.
On the positively oriented boundary of a cap of angular radius $h$,
its integral is $-(1+\cos h)/2$, tending to $-1$ as $h\to0$.

Suppose $N$ is a regular value of the particular map $G$ under
consideration. Its preimage is a finite set: the inverse function
theorem makes it discrete, and it is closed in a compact torus.
Choose disjoint inverse charts there. Compactness of their complement
then gives a small cap whose full inverse image lies in those charts.
Delete the inverse cap discs from the torus. On what remains,
$G^*\omega=d(G^*\lambda_N)$. The boundary integral formula gives
the integral as the sum of the integrals around the deleted discs
with negative boundary orientation. A disc whose local orientation
sign is $\sigma$ contributes $\sigma(1+\cos h)/2$.
The omitted disc integrals tend to zero: the pullback form is smooth
and their areas tend to zero in the fixed inverse charts. Consequently
\begin{equation}\label{fd:regular-pole-count}
                  \int_{S^1\times S^1}G^*\omega
                     =\sum_{p\in G^{-1}(N)}\sigma(p).
\end{equation}
The empty-preimage case uses the primitive on the entire torus and
has both sides zero. No assertion that an arbitrary value is regular
was used. A positive rotation of the coordinates proves the same
formula for any specified regular pole, including the opposite pole.

For completeness, the boundary integral formula just used requires
only planar Green's formula. Cover the compact punctured torus by
finitely many interior or boundary coordinate patches and choose
smooth bump functions supported in the patches whose sum is positive
there; division by that sum gives a finite partition of unity.
Apply the planar formula to each supported one-form. For an interior
patch the two integrals of partial derivatives vanish by the
fundamental theorem and Fubini. In a boundary patch straighten the
smooth boundary to a coordinate graph; the same one-variable
integration leaves exactly its oriented boundary integral.
The derivatives of the partition functions cancel because their sum
is one. This proves the required formula without a topological
degree theorem, general transversality theorem or source assumption.

Now let $\nu$ point toward the observer, and orient the projection
plane so that its positive basis followed by $\nu$ is positive in
$\RR^3$. In a generic projection, a crossing between the components
is exactly a preimage of $\nu$ or $-\nu$ under $G$; the projected
tangents are independent, so both poles are regular values, with
the empty-preimage case allowed. At $G=\nu$, the second component
is over. Up to a positive common factor the projected derivatives
of $G$ are $-C'_1,C'_2$. Their determinant in the tangent plane
oriented by $\nu$ is
\begin{equation}
       \det_\nu(-C'_1,C'_2)=\det_\nu(C'_2,C'_1),
\end{equation}
the overpass-first crossing sign. At $G=-\nu$, the first component
is over and the sphere tangent orientation is reversed. Its sign is
therefore
\begin{equation}
       \det_{-\nu}(-C'_1,C'_2)=\det_\nu(C'_1,C'_2),
\end{equation}
again the overpass-first sign. Formula~\eqref{fd:regular-pole-count}
at each pole says that each of these two signed crossing sums equals
$\ell$. Adding them and dividing by two proves the claimed mixed
crossing formula. The argument concerns the generic diagrams actually
used in the source computations, and does not invoke a theorem asserting
genericity of every projection.

It remains to supply a uniform framed pair, rather than assume that
pointwise small pushoffs assemble into a family. For the general
framing assertion put $n_s=\partial_uC_s\times v_s$ and
\begin{equation}\label{fd:family-normal-chart}
 F(s,u,r,t)=\bigl(s,C_s(u)+r v_s(u)+t n_s(u)\bigr).
\end{equation}
At $(r,t)=(0,0)$ its derivative is invertible: the last three
columns have determinant $|\partial_uC_s\times v_s|^2>0$.
The inverse function theorem, continuity and compactness give a
common small closed normal disc on which every derivative remains
invertible. For the interval endpoints use a smooth local extension
in $s$; the same estimates restrict back to $[0,1]$.
There is a still smaller common radius on which every fixed-$s$
normal chart is injective. Otherwise choose collisions at normal
radii tending to zero. Compactness gives subsequences with
$s_j\to s_*$, $u_j\to u_*$, and $u'_j\to u'_*$.
Equality of their limits gives $C_{s_*}(u_*)=C_{s_*}(u'_*)$;
embeddedness gives $u_*=u'_*$ on the circle. Both colliding points
then lie in one inverse chart of the four-dimensional map $F$
near $(s_*,u_*,0,0)$, a contradiction. This argument includes
both nearby and remotely separated parameter pairs.

Thus for a common $\epsilon_0>0$, the normal charts embed the
closed disc of radius $2\epsilon_0$ at every $s$. Restriction to
the circles with normal coordinates $(0,0)$ and $(\epsilon,0)$,
$0<\epsilon\leq\epsilon_0$, gives disjoint oriented embedded
pushoff pairs varying smoothly in $s$. Interpolating between two
positive radii stays in the same disc. The already proved paired
invariance therefore gives both family and radius independence.
This proves the general framing assertion, including homotopies
of normal fields without any ambient extension theorem.

In particular, for a Legendrian knot choose a smooth contact field
$w$ independent of its tangent. Such a field exists explicitly:
if $L'=A(\partial_x+y\partial_z)+B\partial_y$, take
$w=-B(\partial_x+y\partial_z)+A\partial_y$; $A^2+B^2>0$.
The homotopy $v_\theta=\cos\theta\,w+\sin\theta\,\partial_z$,
$0\leq\theta\leq\pi/2$, never becomes tangent to $L$.
For $\theta>0$ its contact-form evaluation is $\sin\theta>0$;
at zero independence follows from the choice of $w$.
The general framing assertion therefore justifies the replacement
by the $z$-direction pushoff in the source's front calculation of
$tb$, without an assumption about homotopic framings.

For $C_s=T_s$ and $v_s=\partial_y$, independence of the two
columns follows by applying $dz-y\,dx$ to a linear relation:
it is positive on $\partial_uT_s$ and zero on $\partial_y$.
Write $T_s=(x_s,y_s,z_s)$. Let $a_0>0$ be the minimum of
$z'_s-y_sx'_s$ and let $M$ bound $|x'_s|$ on the same compact
cylinder. Decrease $\epsilon_0$ until
$\epsilon_0M<a_0/2$ (no restriction from this inequality if $M=0$).
Then
\begin{equation}\label{fd:pushoff-positive-clearance}
 (dz-y\,dx)_{T_s+\epsilon\partial_y}
                   (\partial_uT_s)
       =(z'_s-y_sx'_s)-\epsilon x'_s>a_0/2>0.
\end{equation}
The uniform normal-chart construction has already proved that
these are disjoint embedded pairs with the required orientations.
Fixing any $0<\epsilon\leq\epsilon_0$ now gives the smooth family
to which \eqref{fd:gauss-divergence} applies. Interpolating between
two such positive radii stays inside the same normal chart and
proves radius independence as well. Finally $\partial_y$ is a
globally nonzero section of $\ker(dz-y\,dx)$, exactly the source's
standard-space framing. Its local linking computations use the
mixed-crossing formula proved above. This fixes the convention in
\eqref{fd:framed-linking} and proves the required smooth-family
self-linking invariance without importing it as a separate theorem.
\end{proof}
```

## ce:rounding — PROVE

reference/SM/sm-3-statesum.tex:3029–3058

```tex
\begin{lemma}[Ordinary rounding of the exact cusp germs]
\label{ce:rounding}
Let $L$ be a smooth oriented spatial embedding of a finite nonempty union
of parameter circles in $\mathbb R^3$, and write $p=(x,z)$ for its
projection. Its only failures of regularity are finitely many isolated
cusps; all other projected coincidences are finitely many transverse
double points. Assume there are no triple points or cusps on another
branch, and the two $y$ heights at every double point are distinct.
At every cusp assume the exact germ, on a parameter interval with smooth
coordinate $u=y-y_0$,
\begin{equation}\label{ce:exact-germ}
 x=x_0+Au^2,\qquad y=y_0+u,\qquad
 z=z_0+Ay_0u^2+\frac{2A}{3}u^3,\qquad A\ne0.
\end{equation}
The coordinate $u$ may increase or decrease along the prescribed component
orientation, which is not changed. The formula is a hypothesis, not an
appeal to a classification of singularities.

There is a jointly smooth family $L_\lambda$, $0\leq\lambda\leq1$, of
oriented spatial embeddings with $L_0=L$, fixed outside disjoint cusp
parameter intervals, such that for every $\lambda>0$ its $xz$ projection
is an ordinary finite regular generic diagram. It cleanly smooths the
cusps, creates no crossing, and retains every original crossing with
its oriented decorated data. All original parameter circles, component
labels and traversal orientations are retained. With no cusps take the
constant family.
This is an ordinary spatial deformation, not asserted Legendrian or
positive transverse, and it carries no self-linking transport statement.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ce\_rounding (C030))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:3059–3169

```tex
\begin{proof}
\par\noindent\emph{Disjoint clean supports and positive charts.} 
Restrict one exact-germ interval so that $u$ is a coordinate throughout.
The affine page chart
\begin{equation}\label{ce:positive-chart}
 X=\frac{x-x_0}{A},\qquad
 Z=\frac{3\bigl(z-z_0-y_0(x-x_0)\bigr)}{2A}
\end{equation}
sends the front to $(u^2,u^3)$. Its linear determinant is
$3/(2A^2)>0$ for either sign of $A$, so it preserves page orientation.
The cubic coordinate is injective, hence the full local arc is injective
even at its cusp.

Choose a smaller closed parameter interval about the cusp inside the
chart. The cusp image is absent from the compact image of the complement
of that interval's interior: local injectivity and the no-other-branch
hypothesis exclude
every other preimage, including on different components. Its distance
from that complement is positive. Thus a sufficiently small open page
neighbourhood $V$ meets only the exact-chart arc. The finitely many cusp
images are distinct; shrink their neighbourhoods to make them pairwise
disjoint and disjoint from every double point. Choose $b>0$ so small
that the closed subarc $|u|\leq b$ lies inside $V$ and the exact chart.

Let $\rho$ be a smooth real cutoff equal to one near zero, with support
strictly inside $(-b,b)$. The image of its compact support has positive
distance $d$ from the closed complement of $V$. Put
$M=\max|u\rho(u)|$ on that support; $M>0$ because $\rho=1$ near zero.
Choose $\epsilon>0$ with
\begin{equation}\label{ce:support-clearance}
 |A|\epsilon M\sqrt{1+y_0^2}<d/2.
\end{equation}
Make these choices at each of the finitely many cusps. No continuous
selection over a further family or generic projection theorem is used.

\par\noindent\emph{The complete rounding family.} 
In the normalized chart set
\begin{equation}\label{ce:rounding-formula}
 X_\lambda(u)=u^2+\lambda\epsilon u\rho(u),\qquad
 Z_\lambda(u)=u^3,\qquad y_\lambda(u)=y_0+u.
\end{equation}
Inverting \eqref{ce:positive-chart} shows that the physical changes are
\begin{equation}\label{ce:physical-displacement}
 \Delta x=A\lambda\epsilon u\rho(u),\qquad \Delta y=0,\qquad
 \Delta z=Ay_0\lambda\epsilon u\rho(u).
\end{equation}
The cutoff vanishes on collars of the chart ends, so every derivative
of the change vanishes there. Pasting to the unchanged $L$ therefore
gives a jointly smooth family on all parameter circles and the closed
$\lambda$ interval. The formula even extends smoothly as a map to a
slightly larger time interval; embeddedness outside $[0,1]$ is not claimed.

For $u\ne0$ one has $dZ_\lambda/du=3u^2>0$. At $u=0$,
$dX_\lambda/du=\lambda\epsilon$, since $\rho(0)=1$. Thus the two
projected derivatives are never simultaneously zero for $\lambda>0$,
regardless of the size or sign of a cutoff derivative. Composing with
the smooth coordinate $u$ preserves this when $du/d\theta<0$ as well.
At $\lambda=0$ the only local projected singularity is the original
cusp. Spatial immersion holds for every $\lambda$ because
$dy_\lambda/du=1$ in each modified chart and the rest of $L$ is unchanged.

Throughout the whole exact chart, including cutoff collars and unchanged
tails, the coordinate $Z_\lambda$ is exactly $u^3$. For $u<v$,
\begin{equation}\label{ce:cubic-difference}
 v^3-u^3=(v-u)(u^2+uv+v^2)>0.
\end{equation}
Indeed the second factor is $(u+v/2)^2+3v^2/4$ and can vanish only when
$u=v=0$, excluded here. Hence distinct parameters anywhere in that
chart have different projected points at every $\lambda$. This proves
injectivity, not merely a tangent test at the centre or at an endpoint.

Equations~\eqref{ce:support-clearance} and~\eqref{ce:physical-displacement}
keep every moved point inside $V$, since its projected displacement norm
is at most $|A|\epsilon M\sqrt{1+y_0^2}<d/2$. No parameter outside the
exact chart projects into $V$. Therefore a moved point cannot meet a
remote parameter. The different cusp neighbourhoods are disjoint, so
different modifications cannot meet each other. Together with strict
local injectivity these facts exclude every new projected crossing for
every $\lambda\in[0,1]$, including pairs on different components.
All old double points are outside the chosen supports. Their exact
branches, tangent determinants and $y$ heights remain unchanged, so
transversality, crossing signs and O/U choices persist. There are no
other coincidences by hypothesis. For positive $\lambda$ the result is
therefore precisely a finite regular generic diagram.

Any spatial coincidence would project to a new coincidence or to an
old double point. The former were excluded; at the latter the two
unchanged $y$ heights are distinct. Spatial injectivity follows for the
whole family. Combined with the immersion already proved, compactness
of the finite parameter union and the Hausdorff target give an embedding:
the continuous bijection to its image has continuous inverse.
Parameters and component labels have never changed.

Each modified portion is one regular embedded oriented arc in a clean
cusp neighbourhood, agreeing with the old arc in its endpoint collars
and containing no crossing. It is exactly a clean cusp smoothing.
There is no assertion that it stays in the contact plane. For example,
where $\rho=1$, differentiating the physical formulas gives
\begin{align}
 x'_\lambda&=2Au+A\lambda\epsilon,
 &y_\lambda&=y_0+u,\label{ce:contact-derivatives}\\
 z'_\lambda&=2Ay_0u+2Au^2+Ay_0\lambda\epsilon.
 \label{ce:contact-z-derivative}
\end{align}
Subtracting $y_\lambda x'_\lambda$ from the second line yields
\begin{equation}\label{ce:ordinary-not-contact}
 z'_\lambda-y_\lambda x'_\lambda=-A\lambda\epsilon u.
\end{equation}
This can have either sign and vanishes at the centre. It cannot justify
Legendrian or positive-transverse invariance, nor transport self-linking.
\end{proof}
```

## ce:smoothing-record — PROVE

reference/SM/sm-3-statesum.tex:3171–3182

```tex
\begin{corollary}[Scalar independence of clean cusp smoothing]
\label{ce:smoothing-record}
For a front satisfying Lemma~\ref{ce:rounding}, define a permitted
smoothed-front diagram by replacing each cusp with one regular embedded
oriented arc in a clean cusp neighbourhood, agreeing with the old germs
in endpoint collars and creating no crossing. Retain every double point
with its original height choice. Every such actual diagram has the same
named decorated record as the diagram $D_\epsilon=p(L_1)$ of the lemma,
including crossing-free components. Consequently their source values
$F_D(l,m)$ and campaign polynomials $P_D(a,z)$ agree.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ce\_rounding (C030))}
\end{corollary}
```

reference/SM/sm-3-statesum.tex:3183–3195

```tex
\begin{proof}
A cusp replacement introduces no crossing visit and changes no successor
of an old visit along the oriented parameter circle. All crossing
pairings, signs and O/U bits remain unchanged because their germs lie
outside the cusp neighbourhoods. The component correspondence is the
identity on the original circles, including those without crossings.
Thus the two actual diagrams have a named decorated-record isomorphism.
Lemma~\ref{rp:record-polynomial}, with the same source construction of
Literature input~\ref{lp:lm}, gives equality of $F_D$; the common substitution
of Theorem~\ref{lp:core} preserves it. This is a scalar statement, not
a classification of arbitrary relative arc embeddings or an ambient
completeness assertion.
\end{proof}
```

## cp:finite-contact-path — PROVE

reference/SM/sm-3-statesum.tex:3210–3233

```tex
\begin{lemma}[The supplied contact-path diagram endpoints]
\label{cp:finite-contact-path}
Let $C$ be a finite nonempty disjoint union of oriented parameter circles,
and let $L:C\to\RR^3$ be a smooth embedding with nonvanishing parameter
derivative. Assume its $xz$ projection $F$ is regular except at finitely
many cusps, each with the exact germ
\begin{equation}\label{cp:exact-cusp}
 x=x_0+Au^2,\qquad y=y_0+u,\qquad
 z=z_0+Ay_0u^2+\frac23Au^3,\qquad A\ne0.
\end{equation}
Assume the only multiple points of $F$ are finitely many transverse
double points, none at a cusp, and the two $y$ values differ at every
double point. Suppose a supplied jointly
smooth family of oriented spatial embeddings $G_t$ starts at this
parametrized $L$ and ends at $T$, whose specified $xz$ projection $D_T$
is an ordinary finite regular generic diagram. Then every clean ordinary
cusp smoothing $S(F)$, with smaller $y$ over at the unchanged crossings,
has the same campaign polynomial as $D_T$:
\begin{equation}\label{cp:endpoint-polynomial}
                    P_{S(F)}=P_{D_T}.
\end{equation}
No contact condition is imposed on $G_t$ or on the rounding family.
\status{new (round~5: the uniform normal-injectivity radius of the ambient extension supplied, by the argument of the uniform normal chart in the proof of Lemma~\ref{fd:linking-calculus} applied to the family $H_s$ of embeddings of the finite union $C$, F-25-151; Corollary~\ref{ce:smoothing-record} cited for the smoothing-independence of $P_{S(F)}$, F-25-136; the remainder is the round-1 transcription of RC d2e\_contact\_bound (C030), held by bench~A; round~9: the status word at the L1 premise removed, F-25-180)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:3234–3326

```tex
\begin{proof}
Use Lemma~\ref{ce:rounding} on the exact germs
\eqref{cp:exact-cusp}. It supplies a jointly smooth family $L_\lambda$
of spatial embeddings, $L_0=L$, fixed outside finitely many clean cusp
neighbourhoods. Its endpoint $L_1$ has an ordinary finite regular generic
diagram $D_\epsilon$, with all old crossings and every component retained.
The construction keeps $y=y_0+u$ and, in the positive affine page chart,
uses $X_\lambda=u^2+\lambda\epsilon u\rho(u)$, $Z_\lambda=u^3$.
The determinant of this chart is $3/(2A^2)>0$, so it has not changed the
crossing convention. Lemma~\ref{ce:rounding} proves injectivity on the
whole chart, including cutoff collars, and excludes remote intersections
for every parameter value; an endpoint tangent check alone would not do so.

The two actual diagrams $S(F)$ and $D_\epsilon$ have identical named
decorated records. Each clean cusp replacement inserts no crossing visit
and keeps the same oriented attachments. All crossing pairings, cyclic
successors, signs, O/U bits and crossing-free component circles agree.
Corollary~\ref{ce:smoothing-record} (through
Lemma~\ref{rp:record-polynomial}) therefore gives
\begin{equation}\label{cp:smoothing-record}
                    P_{S(F)}=P_{D_\epsilon}.
\end{equation}
This is scalar record equality, not a claimed classification of arbitrary
relative arc embeddings.

Let $\eta:[0,1]\to[0,1]$ be smooth and increasing, with its endpoint
values $0,1$ and every positive-order derivative zero at both endpoints.
For example normalize the integral of the bump
$\exp(-1/(s(1-s)))$ on $(0,1)$, extended by zero. Put
\begin{equation}\label{cp:flattened-family}
 H_s=\begin{cases}
       L_{1-\eta(2s)},&0\leq s\leq\tfrac12,\\
       G_{\eta(2s-1)},&\tfrac12\leq s\leq1.
      \end{cases}
\end{equation}
Both branches equal $L$ at the join. Every positive-order time derivative
vanishes there; mixed parameter derivatives have the same property,
while pure circle derivatives agree with those of $L$. Thus the chain
rule gives joint smoothness, including at the join. Every slice is one
of the supplied or proved embeddings. The literal endpoints are $L_1,T$,
with their given parameter orientations, not unidentified nearby knots.

Literature input~\ref{lit:homfly} retains the original full global
HOMFLY interface. The supplied smooth family $H_s$ is a smooth isotopy
of the actual oriented embedded circles. To make the ambient premise
explicit, extend its velocity to a compactly supported ambient field
as follows. At each $(s,u)$ choose a local normal chart for the embedded
circle, smoothly also in $s$, by the inverse function theorem; finitely
many charts cover the compact parameter cylinder. Restrict every chart to
one common normal radius on which a spatial point at time $s$ has at most
one normal-bundle preimage. Such a radius exists by the argument of the
uniform normal chart in the proof of Lemma~\ref{fd:linking-calculus},
applied to the normal bundle of the jointly smooth family $H_s$ of
embeddings of the finite union $C$: two distinct normal-bundle points at a
common time with a common image and normal lengths tending to zero would
accumulate, by compactness of the cylinder, at one point of the cylinder
--- the slice $H_{s_*}$ being an embedding of $C$ --- near which a single
normal chart is injective, a contradiction. Below that radius a point of
the tracked curve lies in a chart only as its own foot point. In each
chart extend
$\partial_sH_s(u)$ constantly in its two normal coordinates. Choose
smooth spatial-time cutoffs supported in those charts whose sum is
positive on the tracked curve, and divide by their sum near that curve.
Their weighted sum equals $\partial_sH_s(u)$ on the curve, because every
local extension has that same value there. Multiply by a further cutoff
equal to one near the whole compact tracked cylinder and zero outside a
compact neighbourhood. This gives a jointly smooth bounded spatial
vector field, with bounded derivatives on the compact time interval.
At the time endpoints extend the given flattened family smoothly to a
small interval; the same construction restricts to $[0,1]$.

Smooth ODE existence and continuation give its flow for the full compact
time interval. Uniqueness and reverse-time evolution give an ambient
diffeomorphism at each time. The chain rule and uniqueness imply that
the flow carries the parametrized $H_0$ to $H_s$. It fixes the complement
of a compact set and preserves ambient orientation, since its derivative
determinant starts positive and never vanishes. Thus its endpoint gives
an actual ambient isotopy between the two oriented links. The retained
global source premise yields $H_{D_\epsilon}=H_{D_T}$.
Theorem~\ref{lp:core} identifies these original values with $P$ on both
actual diagrams, proving $P_{D_\epsilon}=P_{D_T}$. Combining this equality
with~\eqref{cp:smoothing-record} proves~\eqref{cp:endpoint-polynomial}.
This step explicitly consumes the global L1 premise,
Literature input~\ref{lit:homfly}; it is not a source-free replacement
or an application of the local LM theorem beyond its stated domain.

Only the endpoints were assumed to have ordinary generic diagrams. The
cusped diagram at the join causes no problem because $H_s$ is a spatial
embedding throughout. The rounding is ordinary, not Legendrian or
positive transverse: where $\rho=1$ its contact-form evaluation in the
$u$ coordinate is $-A\lambda\epsilon u$. No self-linking number is
transported along this family.
\end{proof}
```

## def:transverse-front — DEFINE

reference/SM/sm-3-statesum.tex:3328–3339

```tex
\begin{definition}[generic positive transverse front]\label{def:transverse-front}
In $(\RR^3,\ker(dz-y\,dx))$, a \emph{generic positive transverse front} is
the oriented knot diagram in the $(x,z)$ plane obtained from a smooth oriented
embedded knot $T$ with $z'-yx'>0$ whose $xz$ projection is an immersion of
the parameter circle with finitely many transverse double points and no
triple point, the over strand at each double point being the branch of
smaller $y$. It has no cusp. At a vertical tangent, $x'=0$, the inequality
gives $z'>0$: every vertical tangent of a generic positive transverse front
points upward, a consequence and not a hypothesis. The diagram determines
its writhe and its over/under counts; the knot $T$ is named separately where
it is used.
\end{definition}
```

## src:contact — AXIOM

reference/SM/sm-3-statesum.tex:3341–3365

```tex
\begin{literature}[Front and positive-pushoff inputs]\label{src:contact}
Use standard contact space
$(\RR^3,\ker(dz-y\,dx))$, with positive transverse orientation
$z'-yx'>0$ (Etnyre~\cite[Sections~2.1 and~2.4]{Etnyre} for the
conventions). Etnyre's front and pushoff
statements~\cite[Section~2.6.2, equations~(5) and~(7); Section~2.6.4,
equation~(9); Section~2.9, Lemma~2.22, equation~(17)]{Etnyre} give, for
an oriented Legendrian front with downward and upward cusp counts $D,U$
--- every cusp of an oriented front is traversed either downward or
upward, so the total cusp count in his $tb$ formula is $D+U$ ---
\begin{equation}\label{fd:contact-inputs}
 r=\frac{D-U}{2},\qquad tb=w-\frac{D+U}{2},\qquad
 sl(T_+(L))=tb(L)-r(L).
\end{equation}
(For the second formula, the Legendrian $tb$, the printed proof used is
Geiges~\cite[Proposition~3.5.9, p.~117]{Geiges}; Etnyre's equation~(7)
reduces to his Remark~2.14, which is stated there without proof.)
For a generic positive transverse front
(Definition~\ref{def:transverse-front}), self-linking equals its front
writhe: Geiges~\cite[Section~3.1, Lemma~3.3, p.~46]{GeigesContact} (printed
proof) and Geiges~\cite[Proposition~3.5.32, p.~127]{Geiges}; Etnyre's
equation~(9), Section~2.6.4, states it. These are the local front and
pushoff source formulas only.
\status{lit: Etnyre and Geiges local front and pushoff formulas; Registry~\ref{reg:etnyre}; round~3: page-precise locators, the cusp count $D+U$ and the front class named, F-25-82, F-25-83, F-25-84}
\end{literature}
```

## fd:ng-bound — PROVE

reference/SM/sm-3-statesum.tex:3379–3390

```tex
\begin{lemma}[the individual-front bound in self-linking form]\label{fd:ng-bound}
Let $F$ be a front on the domain of Definition~\ref{ng:front-domain}, with
$c_\downarrow(F)=D(F)$ its number of downward cusps, and let $S(F)$ be an
actual clean ordinary cusp smoothing of $F$ as in that definition. Then
\begin{equation}\label{fd:ng-input}
 sl_{\rm Ng}(F):=w(F)-c_\downarrow(F)
          \leq-\max\deg_a P_{S(F)}(a,z)-1.
\end{equation}
This is not an application of an ambient-invariant hypothesis to the
local diagram construction, nor a maximum over front representatives.
\status{new (round~3; Theorem~\ref{ng:local-front-bound} restated in Ng's self-linking form, so that the closure of Theorem \texttt{fd:contact} contains it; consumes Literature input~\ref{ng:finite-word} through that theorem; F-25-107; round~5: Lemma~\ref{ng:smoothing-record} cited for the symbol $P_{S(F)}$, F-25-136)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:3391–3399

```tex
\begin{proof}
Theorem~\ref{lp:core} gives $P_{S(F)}\neq0$, and $P_{S(F)}$ does not depend
on the rounding by Lemma~\ref{ng:smoothing-record}, so $\deg_a P_{S(F)}$ of
display~\eqref{ng:defect} is the largest $a$ exponent with nonzero
coefficient, $\max\deg_a P_{S(F)}$. Inequality~\eqref{ng:front-inequality}
of Theorem~\ref{ng:local-front-bound} reads
$w(F)-D(F)\leq-\deg_aP_{S(F)}-1$, which is the display with
$c_\downarrow(F)=D(F)$.
\end{proof}
```

## fd:contact — PROVE

reference/SM/sm-3-statesum.tex:3404–3423

```tex
\begin{theorem}[The contact dictionary and finite-diagram representative bound]
\label{fd:contact}
In the $xz$ front page the smaller-$y$ branch is over, and its crossing
sign is $\sgn\det_{xz}(u_O,u_U)$. For a generic positive transverse front
(Definition~\ref{def:transverse-front}) one has
\begin{equation}\label{fd:front-writhe}
 sl(T)=\sum_q\sgn\det_{xz}(u_O(q),u_U(q)).
\end{equation}
Let $T$ be an individual smooth positive transverse knot whose specified
$xz$ projection $D_T$ is an ordinary finite regular generic diagram.
With $P_T$ denoting the original campaign polynomial of this actual
diagram, one has
\begin{equation}\label{fd:representative-bound}
 sl(T)\leq-\max\deg_a P_T(a,z)-1.
\end{equation}
The finite specified-diagram hypothesis is part of this auxiliary bound;
no assertion that every smooth knot has a generic specified projection
is required. The carrier-floor construction supplies such a diagram.
\status{new (round~6: the crossing from the source's self-linking number to the number of \eqref{fd:framed-linking} cites Remark~\ref{rem:sl-convention}, F-25-168; round~5: the domain hypothesis of Lemma~\ref{fd:ng-bound} discharged for $F_T$ from Theorem~\ref{fd:generic-front} and the lemma cited by label, F-25-153; the sentence after \eqref{fd:front-writhe} restored to RC's wording, F-25-152; the remainder is the round-1 transcription of RC fd:contact, d2e\_contact\_bound (C030), held by bench~A; consumes Literature inputs~\ref{src:contact} and~\ref{lit:homfly}; round~3: the front class of \eqref{fd:front-writhe} named, F-25-82)}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:3424–3499

```tex
\begin{proof}
Writing $\alpha=dz-y\,dx$ gives $d\alpha=dx\wedge dy$ and
\begin{equation}
 \alpha\wedge d\alpha=dz\wedge dx\wedge dy=dx\wedge dy\wedge dz.
\end{equation}
The source observer is on the negative-$y$ side looking in the positive
$y$ direction, so smaller $y$ is over. For a Legendrian front this is also
the smaller-slope rule $y=dz/dx$. The normal toward the observer is
$\nu=-\partial_y$ and
$\det_{xyz}(\partial_x,\partial_z,\nu)=1$.
For projected over and under tangents $(a,c)$ and $(b,d)$,
\begin{equation}
 \det\begin{pmatrix}a&b&0\\0&0&-1\\c&d&0\end{pmatrix}
 =ad-bc=\det_{xz}((a,c),(b,d)).
\end{equation}
This identifies each source crossing sign with the campaign sign.
Summing the source transverse-front writhe formula, whose $sl$ is the
number of \eqref{fd:framed-linking} by Remark~\ref{rem:sl-convention},
proves \eqref{fd:front-writhe}. Absence of downward tangencies alone is not a
converse transverse-lift theorem: the crossing-height inequalities will be
checked separately in the carrier-floor proof.

With the same vertical coordinate, Ng's downward cusp count is $D$.
Substitute the first two formulas of \eqref{fd:contact-inputs} into the third:
\begin{align}
 tb-r&=w-\frac{D+U}{2}-\frac{D-U}{2}\notag\\
     &=w-\frac{2D}{2}=w-D=sl_{\rm Ng}(F).
\end{align}
This identifies Ng's pushoff as Etnyre's positive pushoff, fixing the
possible exchange of names in other conventions.

Fix $T$ with the stated finite ordinary generic diagram $D_T$.
Lemma~\ref{fd:transverse-neighborhood} gives the original Legendrian
helix $L$ and a chosen positive pushoff transversely isotopic to $T$.
Let $\Phi_s$ be the ambient contact isotopy of
Theorem~\ref{fd:generic-front}; write $L_T=\Phi_1\circ L$ and let
$F_T$ be its finite generic front, with the exact cusp germs
\eqref{cp:exact-cusp}. The isotopy carries the chosen pushoff through
positive transverse embeddings, so $T_+(L_T)$ is transversely isotopic
to the same $T$. Lemma~\ref{fd:linking-calculus} preserves self-linking
along this smooth positive transverse family. The preceding cusp
calculation identifies its value with $sl_{\rm Ng}(F_T)$. The front
$F_T$ lies on the domain of Definition~\ref{ng:front-domain}:
Theorem~\ref{fd:generic-front} gives finitely many semicubical cusps with
the germ \eqref{cp:exact-cusp}, whose $x''(0)=2A\neq0$, transverse double
points, no triple point and no cusp on another branch, and Legendrianity
$z'=yx'$ makes the front tangent vanish wherever $x'=0$, so that every such
point is one of these cusps and no regular arc has a vertical tangency.
Lemma~\ref{fd:ng-bound}, applied to $F_T$, bounds it by
$-\max\deg_a P_{S(F_T)}-1$.

Let $\Psi_t$ be the ordinary ambient flow of
\eqref{fd:helix-ambient-isotopy}. The maps
\begin{equation}\label{fd:contact-ambient-composition}
 \Theta_t=\Psi_t\circ\Phi_{1-t}\circ\Phi_1^{-1},
 \qquad 0\leq t\leq1,
\end{equation}
give the supplied family $G_t=\Theta_t\circ L_T$.
Indeed $\Phi_1^{-1}\circ L_T=L$, so
$G_t=\Psi_t\circ\Phi_{1-t}\circ L$; at zero it equals $L_T$ and
at one it equals the parametrized $T$. The two smooth compactly
supported ambient flows make $G$ jointly smooth, and each slice is an
embedding with nonzero parameter derivative. They transport the given
circle orientation. The generic front theorem supplies all other cusp
and crossing hypotheses of Lemma~\ref{cp:finite-contact-path}; the
specified ordinary diagram $D_T$ is the endpoint hypothesis already
included in the present statement. Consequently that lemma gives
$P_{S(F_T)}=P_{D_T}=P_T$. Substitution proves
\eqref{fd:representative-bound}.

The polynomial equality explicitly uses the original global
HOMFLY source premise in Literature input~\ref{lit:homfly}. The positive transverse family alone
transports self-linking; the distinct ordinary flow and cusp rounding
are used only for the polynomial. No maximum over representatives,
mirror, variable change or new owner assumption enters this composition.
\end{proof}
```

## cf:def-turning — DEFINE

reference/SM/sm-3-statesum.tex:3514–3535

```tex
\begin{definition}[direction loops and smooth rotation]\label{cf:def-turning}
A \emph{direction loop} is a continuous map $T\colon\RR/\ZZ\to S^1$ into
the unit circle of the oriented plane. A \emph{tangent-angle lift} of $T$
at a seam is a continuous $\theta\colon[0,1]\to\RR$ with
$T(s)=(\cos\theta(s),\sin\theta(s))$ for $0\leq s\leq1$; put
\[
   \operatorname{tw}(T)=\frac{\theta(1)-\theta(0)}{2\pi}.
\]
For a closed $C^1$ regular oriented curve $\gamma\colon\RR/\ZZ\to\RR^2$,
that is, with $\gamma'\neq0$ everywhere, put
\[
   T_\gamma=\frac{\gamma'}{|\gamma'|},\qquad
   \rot(\gamma)=\operatorname{tw}(T_\gamma).
\]
For a polygon in the regular locus, $\rot$ remains that of
Lemma~\ref{lem:rot}. For either a polygon or a $C^1$ regular closed curve
put $R(L)=|\rot(L)|$. The lemma that follows constructs the lift and
proves that these values do not depend on its choice, on the seam, or on
an orientation-preserving regular reparametrisation. (Transcribed from CV
def:rot, paragraph ``Direction loops and smooth curves'', d1\_setup;
F-25-88.)
\end{definition}
```

## cf:lem-turnlift — PROVE

reference/SM/sm-3-statesum.tex:3542–3578

```tex
\begin{lemma}[tangent lifts and principal turns]\label{cf:lem-turnlift}
Here $\rot$ is as in Lemma~\ref{lem:rot} for polygons and
Definition~\ref{cf:def-turning} for direction loops and closed $C^1$
regular curves.
\begin{enumerate}
\item[(i)] Every continuous direction loop has a tangent-angle lift.
The integer $\operatorname{tw}(T)$ is independent of the lift and seam,
is unchanged by an orientation-preserving reparametrisation, and is constant
under a continuous homotopy through direction loops. Consequently the rotation
of a closed $C^1$ regular curve is invariant under regular homotopy, and
reversing its orientation negates it.
\item[(ii)] If $L\in\mathcal R_c$ has principal turns $\vartheta_i$, then
\[
   2\pi\rot(L)=\sum_i\vartheta_i.
\]
Consequently rotation is constant along every path in $\mathcal R_c$, is
unchanged by a positive flat subdivision, and is negated by orientation
reversal. Every regular three-corner polygon has rotation $+1$ or $-1$
according to the common sign of its three turns.
\item[(iii)] Suppose a closed $C^1$ regular curve is obtained from $L$ by
replacing every corner by a regular arc whose compatible tangent-angle lift
has increment $\vartheta_i$. Its rotation equals $\rot(L)$.

More generally, let $b,c$ be regular oriented arcs having the same endpoints
and the same oriented tangent rays at both endpoints, and suppose replacing
$b$ by $c$ in a closed curve gives closed $C^1$ regular curves $F_b,F_c$.
For compatible tangent lifts with equal initial values, write their increments
as $\Delta_b,\Delta_c$. Then
\[
   \rot(F_c)-\rot(F_b)=\frac{\Delta_c-\Delta_b}{2\pi}.
\]
If $A_t$, $0\leq t\leq1$, is a supplied continuous path in
$\mathrm{GL}^+(2,\mathbb R)$ with $A_0=I$ and $A_1=A$, applying $A$ to both
arcs leaves $\Delta_c-\Delta_b$ unchanged.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T18:22:57Z and 2026-09-06T04:22:56Z; transcribed from CV lem:turnlift (C032); round~3: the scoping sentence covers the smooth case, F-25-88)}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:3579–3642

```tex
\begin{proof}
For~(i), uniform continuity gives
$0=s_0<\cdots<s_m=1$ such that
$T(s)\cdot T(s_{j-1})>0$ on every
$[s_{j-1},s_j]$. After choosing $\theta(0)$, continue it there by
\[
 \theta(s)=\theta(s_{j-1})+
 \operatorname{atan2}\!\left(
   \det(T(s_{j-1}),T(s)),\,
   T(s_{j-1})\cdot T(s)\right).
\]
The second argument is positive, so the added angle lies in
$(-\pi/2,\pi/2)$; the formulas match at the subdivision points and construct a
continuous lift without a covering-space theorem. Since $T(1)=T(0)$, its
endpoint increment belongs to $2\pi\mathbb Z$. Two lifts differ continuously
by a value in $2\pi\mathbb Z$, hence by one constant.

If the increment is $2\pi k$, extend the lift by
$\theta(s+n)=\theta(s)+2\pi nk$. Every interval of length one then has the same
increment, proving seam independence. An orientation-preserving
reparametrisation of the circle has an increasing representative
$\phi\colon\mathbb R\to\mathbb R$ with
$\phi(s+1)=\phi(s)+1$; the lift $\theta\circ\phi$ has the same increment.

For a homotopy $T(s,t)$ fix $t_0$. Uniform continuity gives a neighbourhood of
$t_0$ on which
$T(s,t)\cdot T(s,t_0)>0$ for every $s$. There is therefore
a unique continuous relative angle
\[
 \alpha(s,t)=\operatorname{atan2}\!\left(
 \det(T(s,t_0),T(s,t)),\,
 T(s,t_0)\cdot T(s,t)\right)
 \in(-\pi/2,\pi/2).
\]
If $\theta_0$ lifts $T(\,\cdot\,,t_0)$, then
$\theta_0+\alpha(\,\cdot\,,t)$ lifts $T(\,\cdot\,,t)$.
Periodicity gives $\alpha(1,t)=\alpha(0,t)$, so the endpoint increment is
locally, hence globally, constant in $t$. A regular homotopy supplies such a
homotopy of normalised tangents. For the oppositely oriented curve,
$-T_\gamma(1-s)$ has lift $\theta(1-s)+\pi$, whose increment is the negative
of the original one.

For~(ii), the identity and all its polygonal consequences are exactly
Lemma~\ref{lem:rot}: polygonal rotation was defined there by the sum of
principal angles, whose integrality and continuity were proved there.

For~(iii), concatenate constant lifts on the straight pieces with the
prescribed corner lifts. Their total increment is $\sum_i\vartheta_i$, so~(ii)
proves the rounding assertion.

For the replacement assertion, use the same lift on the unchanged
complementary arc. Shifting that complementary lift at a join changes neither
its increment nor the computation; subtraction cancels it and leaves
$\Delta_c-\Delta_b$.

Finally follow the tangent path of $c$ and then the tangent path of $b$
backwards. This is a closed direction loop of increment
$\Delta_c-\Delta_b$. The maps
\[
   \nu_t(z)=\frac{A_tz}{|A_tz|}
\]
give a homotopy of that direction loop. Clause~(i) keeps its increment
constant, proving the last assertion without invoking degree.
\end{proof}
```

## cf:lem-rounding — PROVE

reference/SM/sm-3-statesum.tex:3644–3694

```tex
\begin{lemma}[rounding]\label{cf:lem-rounding}
Here $\rot$ is as in Lemma~\ref{lem:rot} for polygons and
Definition~\ref{cf:def-turning} for closed $C^1$ regular curves.
Let $L$ be a closed polygon with corners $q_1,\dots,q_c$, and let $D$ be an
oriented diagram whose underlying plane curve is $L$ --- $L$ together with an
over/under assignment at each of its double points. Assume the principal turns
of $L$ all exist and are \emph{nonzero}; that $L$ has finitely many double
points, all transversal, none of them a corner; and that no corner of $L$ lies
on an edge of $L$ other than the two incident to it. Then there is a \emph{clearance} $\varepsilon_0(L)>0$ such that for every
$\varepsilon\in\bigl(0,\varepsilon_0(L)\bigr)$ there is a $C^\infty$ regular
closed plane curve $L_\varepsilon$, and a diagram $D_\varepsilon$ carried by it, with
these properties.
\begin{enumerate}
\item[(a)] $L_\varepsilon$ coincides with $L$ outside the union of the discs of
radius $\varepsilon$ about the corners.
\item[(b)] Inside the disc about $q_i$ the unit tangent moves \emph{strictly}
monotonically, in the sense of $\sgn\vartheta_i$, from $\delta_{i-1}/|\delta_{i-1}|$
to $\delta_i/|\delta_i|$, sweeping an arc of length exactly $|\vartheta_i|$ and no
more, and attaining each direction of that arc at exactly one parameter.
Moreover the unit-tangent map is an \emph{immersion} on the open junction arc:
parametrized by arclength, its angular derivative is nonzero at every interior
parameter, while at the two ends it and all its derivatives vanish, the
junction meeting the straight edges flat to infinite order.

Both clauses are exported because both are read downstream, and the second does
not follow from the first: a strictly monotone angle may still have a vanishing
derivative at a parameter, and the direct count below needs the derivative
itself to be nonzero, not merely the monotonicity. "Moves monotonically" alone
is weaker still --- it is
satisfied by a junction that pauses on one direction for a whole sub-arc, and
then a count of the parameters carrying a prescribed direction is infinite. Both
hold because the profile fixed in the proof below is strictly increasing on
$(0,1)$ with $\varphi'>0$ there, and flat to infinite order at $0$ and $1$: the
tangent angle at arclength $\sigma$ along the junction of length $\ell$ is
$\theta_u+\vartheta_i\varphi(\sigma/\ell)$, whose derivative is
$\vartheta_i\varphi'(\sigma/\ell)/\ell\neq0$ for $0<\sigma<\ell$.
\item[(c)] $L_\varepsilon$ has the same double points as $L$, with the same
strands, the same over/under assignment and hence the same crossing signs and
the same writhe.
\item[(d)] $\rot(L_\varepsilon)=\rot(L)$.
\item[(e)] \emph{The disc package is returned.} There are pairwise disjoint
closed discs $D_1,\dots,D_c$, one about each corner $q_i$, such that each $D_i$
meets no edge of $L$ that is not incident to $q_i$, contains no double point of
$L$, meets the two incident edges exactly in the two sub-segments of length
$\varepsilon$ at $q_i$, and contains the whole of the modification made at
$q_i$. This clause is a conclusion of the lemma, not a package handed over by a
paragraph of its proof; its consumer asks for a disc meeting the diagram in one
embedded arc and reads it here.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z and 2026-09-06T00:12:27Z; transcribed from CV lem:rounding (C032))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:3695–3868

```tex
\begin{proof}
\emph{The junction, constructed.} Since $0<|\vartheta_i|<\pi$, the unit directions
$u=\delta_{i-1}/|\delta_{i-1}|$ and $v=\delta_i/|\delta_i|$ are neither parallel
nor antiparallel. Write $A_0=q_i-\varepsilon u$ and $A_1=q_i+\varepsilon v$ for
the two points at distance $\varepsilon$ from $q_i$ along the incident edges, so
that the displacement to be realized is
\[
   A_1-A_0=\varepsilon\,(u+v),
\]
a nonzero vector along the bisector of the convex angle at $q_i$. Fix once and
for all the \emph{transition profile}
\[
   \varphi(t)=\frac{f(t)}{f(t)+f(1-t)},
   \qquad
   f(t)=\begin{cases} e^{-1/t}, & t>0,\\ 0,& t\leq0,\end{cases}
\]
which is exhibited rather than posited, and which has the four properties every
use below reads. It is $C^\infty$ on $[0,1]$: $f$ is $C^\infty$ on $\mathbb R$
with all derivatives vanishing at $0$, and the denominator
$f(t)+f(1-t)$ is positive on $[0,1]$, being $f(1)>0$ at $t=0$ and $f(1)>0$ at
$t=1$ and a sum of two nonnegative terms not both zero in between. It has
$\varphi(0)=0$ and $\varphi(1)=1$. It satisfies $\varphi(1-t)=1-\varphi(t)$, by
inspection of the formula. And it is \emph{strictly increasing on $(0,1)$}:
\[
   \varphi'(t)=\frac{f'(t)f(1-t)+f(t)f'(1-t)}{\bigl(f(t)+f(1-t)\bigr)^2}>0
   \qquad (0<t<1),
\]
both terms of the numerator being positive there, since $f>0$ and
$f'(t)=t^{-2}e^{-1/t}>0$ on $(0,1)$. Every derivative of $\varphi$ vanishes at
$0$ and at $1$, because every derivative of $f$ vanishes at $0$ and the
denominator is smooth and nonvanishing.

Strict increase is not a convenience. An earlier revision asked only that
$\varphi$ be nondecreasing, and a nondecreasing profile may be constant on a
subinterval; the tangent direction would then be constant on a whole sub-arc of
the junction, so a direction attained there would be attained at a continuum of
parameters rather than at isolated ones, and every count of the points carrying
a prescribed tangent direction --- the counts this section takes later --- would
be infinite. With $\varphi$ strictly increasing on $(0,1)$ the tangent angle
$\theta_u+\vartheta_i\varphi(t/\ell)$ is strictly monotone across the junction, and
each direction in the swept arc is attained exactly once. Let
$\theta_u$ be the angle of $u$ and, for a length $\ell>0$, let
\[
   \gamma_\ell(s)=A_0+\int_0^{s}
   \bigl(\cos(\theta_u+\vartheta_i\varphi(t/\ell)),\,
         \sin(\theta_u+\vartheta_i\varphi(t/\ell))\bigr)\,\mathrm dt,
   \qquad s\in[0,\ell].
\]
Then $\gamma_\ell$ is a unit-speed $C^\infty$ arc. Its tangent equals $u$
\emph{at} $s=0$ and $v$ \emph{at} $s=\ell$, and agrees with those constants
\emph{to infinite order} at those two parameters, every derivative of $\varphi$
vanishing there; it does not equal them on a neighbourhood, and cannot, since
the angle is strictly monotone on $(0,\ell)$.
Infinite-order agreement at the endpoint is what the junction needs: it is
exactly the condition under which replacing the corner by the arc leaves a
$C^\infty$ regular curve, since all one-sided derivatives match those of the
straight edge. The tangent angle moves strictly monotonically through exactly
$\vartheta_i$ and no more, and its derivative
$\vartheta_i\varphi'(s/\ell)/\ell$ is nonzero on $(0,\ell)$, which is (b).

Its endpoint is $A_0+\ell\,m(\varphi)$ where
$m(\varphi)=\int_0^1(\cos(\theta_u+\vartheta_i\varphi),\sin(\theta_u+\vartheta_i\varphi))\,
\mathrm dt$. The symmetry $\varphi(1-t)=1-\varphi(t)$ makes the angles
$\theta_u+\vartheta_i\varphi(t)$ and $\theta_u+\vartheta_i\varphi(1-t)$ reflections of
each other in the bisector, so $m(\varphi)$ points along $u+v$; and
$|m(\varphi)|>0$ because all the directions integrated lie in a closed angular
interval of width $|\vartheta_i|<\pi$. Taking
$\ell=\varepsilon\,|u+v|/|m(\varphi)|$ makes the endpoint exactly $A_1$.

\emph{The arc lies in the triangle $A_0q_iA_1$, in coordinates.} Put
$\alpha=|\vartheta_i|/2\in(0,\pi/2)$ and $s=\sgn\vartheta_i$, let $w$ be the unit vector
along $u+v$ and $z$ the unit vector with $\det(w,z)=1$, and take $q_i$ as
origin, writing a point as $(x_w,x_z)$ in that frame. Then
\[
   u=\cos\alpha\,w-s\sin\alpha\,z,
   \qquad
   v=\cos\alpha\,w+s\sin\alpha\,z,
\]
because $u$ and $v$ are unit vectors whose sum is along $w$ and whose angle is
$|\vartheta_i|=2\alpha$, turning from $u$ to $v$ by $\vartheta_i$. Hence
$A_0=-\varepsilon u$ has coordinates $(-\varepsilon\cos\alpha,\ s\varepsilon
\sin\alpha)$ and $A_1=\varepsilon v$ has $(\varepsilon\cos\alpha,\
s\varepsilon\sin\alpha)$, and the closed triangle with vertices $A_0,q_i,A_1$
is exactly
\begin{equation}
   T_i=\bigl\{\,(x_w,x_z):\ |x_w|\leq\cot\alpha\cdot(s\,x_z),
   \quad 0\leq s\,x_z\leq\varepsilon\sin\alpha\,\bigr\},
\label{cf:eq-triangle}
\end{equation}
the first inequality being the pair of cone conditions at the apex $q_i$ and the
second the chord through $A_0$ and $A_1$: a point $\lambda(-u)+\mu v$ with
$\lambda,\mu\geq0$ has $x_w=(\mu-\lambda)\cos\alpha$ and
$s\,x_z=(\lambda+\mu)\sin\alpha$, so $|x_w|\leq(\lambda+\mu)\cos\alpha=\cot\alpha
\cdot(s\,x_z)$ with equality exactly on the two edges, and $\lambda+\mu\leq
\varepsilon$ is the chord.

The junction arc satisfies all three inequalities of \eqref{cf:eq-triangle}. Write
its unit tangent as $T(\sigma)=\cos\beta(\sigma)\,w+s\sin\beta(\sigma)\,z$ with
$\beta(\sigma)=-\alpha+2\alpha\,\varphi(\sigma/\ell)$, which is the tangent
angle constructed above read in this frame: at $\sigma=0$ it is $u$
($\beta=-\alpha$), at $\sigma=\ell$ it is $v$ ($\beta=\alpha$), and $\beta$ is
strictly increasing with values in $[-\alpha,\alpha]$.
\emph{The two cone inequalities.} Let $n_1$ be the unit normal to $u$ with
$\langle n_1,v\rangle>0$. The line $\mathbb Ru$ contains both $q_i$ and $A_0$,
and $T_i$ lies in $\{\langle\cdot,n_1\rangle\geq0\}$. Along the arc,
$\tfrac{d}{d\sigma}\langle\gamma,n_1\rangle=\langle T,n_1\rangle\geq0$, because
$T=au+bv$ with $a,b\geq0$ --- a direction at angle $\beta\in[-\alpha,\alpha]$
from $w$ lies in the closed cone of $u$ and $v$ --- so
$\langle T,n_1\rangle=b\langle v,n_1\rangle\geq0$; and
$\langle\gamma(0),n_1\rangle=\langle-\varepsilon u,n_1\rangle=0$. Hence
$\langle\gamma,n_1\rangle\geq0$ throughout. Symmetrically, with $n_2$ the unit
normal to $v$ with $\langle n_2,A_0\rangle>0$, one has $\langle
T,n_2\rangle=a\langle u,n_2\rangle\leq0$, so $\langle\gamma,n_2\rangle$ is
nonincreasing and equals $\langle\varepsilon v,n_2\rangle=0$ at $\sigma=\ell$;
hence it is $\geq0$ throughout. Those two are the first inequality of
\eqref{cf:eq-triangle}.
\emph{The chord inequality.} $s\,x_z(\sigma)=\varepsilon\sin\alpha+\int_0^\sigma
\sin\beta(t)\,dt$, and $\int_0^\sigma\sin\beta\leq0$ for every
$\sigma\in[0,\ell]$: $\beta$ is negative on $(0,\ell/2)$ and positive on
$(\ell/2,\ell)$, and the symmetry $\varphi(1-t)=1-\varphi(t)$ makes
$\beta(\ell-t)=-\beta(t)$, so the integral decreases to its minimum at
$\ell/2$ and increases back to $0$ at $\ell$. Hence $s\,x_z\leq\varepsilon
\sin\alpha$, which is the second. The lower bound $s\,x_z\geq0$ is implied by
the two cone inequalities, the apex being the origin.

Its bisector coordinate has derivative
$dx_w/d\sigma=\cos\beta(\sigma)\geq\cos\alpha>0$.
Thus that coordinate is strictly increasing and the junction arc is
injective; no self-intersection can be hidden inside its rounding disc.

So the arc lies in $T_i$, and $T_i$ lies in the closed disc $D_i$ of radius
$\varepsilon$ about $q_i$: the disc is convex and contains the three vertices,
$|A_0-q_i|=|A_1-q_i|=\varepsilon$. An earlier revision argued this by saying the
arc ``cannot leave the region cut off by the two tangent lines'', which names
the conclusion rather than proving it and leaves the chord side unaddressed.

For (a) and (c), let $\mathcal E_i$ be the union of the closed edges
not incident to $q_i$, and define the four clearances separately:
\[
\begin{aligned}
 \eta_v&=\min_i\min_{k\ne i}|q_k-q_i|,
 &\eta_e&=\min_i\operatorname{dist}(q_i,\mathcal E_i),\\
 \eta_\ell&=\min_i|\delta_i|,
 &\eta_X&=\min_{i,\,x\text{ a double point}}|x-q_i|.
\end{aligned}
\]
Set
\[
 \varepsilon_0(L)=\tfrac13\min\{\eta_v,\eta_e,\eta_\ell,\eta_X\},
\]
and require $\varepsilon<\varepsilon_0(L)$; the index $i$ is bound by the outer
minimum in every term.
Each minimum over an empty index set is $+\infty$ --- which is how the last
one is read when $L$ has no double point. Every listed quantity is positive: the
corners are finitely many and distinct; a corner is at positive distance from a
non-incident closed edge because the edges are compact and a corner on one would
contradict the hypothesis that no corner lies on a non-incident edge; the edges have positive length; and a double point lies
in the relative interiors of two edges, so it is distinct from every corner.
With this $\varepsilon$ the discs $D_i$ are pairwise disjoint, each $D_i$ meets
no edge not incident to $q_i$, each $D_i$ contains no double point, and each
$D_i$ meets the two incident edges in the two sub-segments of length
$\varepsilon$ at $q_i$, and each contains the whole modification made at its
corner, the replacement arc lying within distance $\varepsilon$ of $q_i$. That
is clause~(e). Hence the rounding changes the curve only inside those
discs, where it meets nothing else, so no double point is created or destroyed
and the strands through each surviving double point are unchanged as arcs, with
their orientations; the over/under assignment is inherited, so the crossing signs
and the writhe are unchanged. That is (a) and (c). For (d), the total turning of
$L_\varepsilon$ is the sum of the turnings of its arcs, which is
$\sum_i\vartheta_i$ because the tangent is constant along the straight parts; and the
rotation number of a $C^1$ regular closed curve is $\frac1{2\pi}$ times its
total turning (Lemma~\ref{cf:lem-turnlift}(iii)), which is also the value assigned to $L$
by Lemma~\ref{lem:rot}.
\end{proof}
```

## cf:lem-curl — PROVE

reference/SM/sm-3-statesum.tex:3870–3891

```tex
\begin{lemma}[exact negative-curl replacement]\label{cf:lem-curl}
Here $\rot$ is as in Lemma~\ref{lem:rot} for polygons and
Definition~\ref{cf:def-turning} for closed $C^1$ regular curves.
Let $F$ be a connected $C^\infty$ immersed circle in the plane --- one
component, with finitely many transverse double points and no triple points ---
given with an oriented diagram, and let $p$ be a point of $F$ at which the
tangent points in a fixed direction $u$, isolated among such points, lying in
an embedded arc of $F$ that contains no double point and along which the tangent
turns strictly positively. Then $F$ may be modified inside a disc $\Delta$
meeting the rest of the diagram only in that arc, so that the resulting
diagram $F'$
\begin{enumerate}
\item[(i)] is again such an oriented diagram, satisfies
$P_{F'}(a,z)=P_F(a,z)$, and has the same double points outside $\Delta$, with
the same signs;
\item[(ii)] has no point of $\Delta$ at which the tangent equals $u$, and exactly
one at which it equals $-u$;
\item[(iii)] has exactly one double point inside $\Delta$, and it is negative;
\item[(iv)] satisfies $\rot(F')=\rot(F)-1$ and $w(F')=w(F)-1$.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z and 2026-09-06T00:32:58Z; transcribed from CV lem:curl (C032))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:3892–4280

```tex
\begin{proof}
Work first in the rational model on $-2\leq t\leq2$,
\[
b(t)=\Bigl(\tfrac{3(t^2+7)}{11},\,-3t\Bigr),\qquad
c(t)=\bigl(t^2-1,\;t-t^3\bigr).
\]
The endpoints and endpoint tangent rays agree up to positive scale:
$b(\pm2)=c(\pm2)=(3,\mp6)$ and $b'(\pm2)=\frac3{11}c'(\pm2)$. The old arc turns
strictly positively and has exactly one tangent pointing straight down, at
$t=0$:
\[
\det\bigl(b'(t),b''(t)\bigr)=\tfrac{18}{11}>0,\qquad b'(0)=(0,-3).
\]
The replacement turns strictly negatively and has exactly one tangent pointing
straight up, at $t=0$:
\[
\det\bigl(c'(t),c''(t)\bigr)=-2(1+3t^2)<0,\qquad c'(0)=(0,1).
\]
In each arc the first derivative has vanishing first component only at $t=0$, so
neither arc has any other vertical tangent; this is (ii) in the model. The
replacement runs between the same endpoint rays along the complementary,
clockwise tangent path, so its compatible lift increment is the old one minus
$2\pi$; Lemma~\ref{cf:lem-turnlift}(iii) gives (iv) for $\rot$. It has exactly one double point,
\[
c(-1)=c(1)=(0,0),\qquad c'(-1)=(-2,-2),\qquad c'(1)=(2,-2),
\]
and putting the later branch over the earlier one makes it negative, since a
crossing sign is the sign of the determinant of the overpassing tangent followed
by the underpassing tangent and
$\det\bigl(c'(1),c'(-1)\bigr)=-8<0$; that is (iii), and with it (iv) for $w$.
Being a single Reidemeister-I monogon, the replacement does not change the knot
type, which is (i).

To insert the model at $p$ we first record the projective fact it needs, in the
form the insertion argument requires.

\emph{Ordered-ray lemma.} Let $(r_1,r_2,r_3)$ and $(s_1,s_2,s_3)$ be triples of
rays from the origin such that $r_2$ lies in the open convex cone spanned by
$r_1,r_3$ and $s_2$ lies in the open convex cone spanned by $s_1,s_3$, with
$r_1,r_3$ and $s_1,s_3$ independent, and suppose in addition that for positive
representatives
\begin{equation}
   \sgn\det(\rho_1,\rho_3)=\sgn\det(\sigma_1,\sigma_3),
\label{cf:eq-orderedray}
\end{equation}
a condition independent of the representatives chosen. Then there is a linear
map $A$ with $\det A>0$ carrying each $r_k$ into $s_k$.
\emph{Proof:} if both determinants in \eqref{cf:eq-orderedray} are negative,
exchange the names $1$ and $3$ \emph{in both triples simultaneously}; this
preserves the correspondence $r_k\mapsto s_k$ and makes both determinants
positive. The linear map $A_0$ with $A_0\rho_1=\sigma_1$, $A_0\rho_3=\sigma_3$
then has positive determinant and carries $r_1,r_3$ to $s_1,s_3$. It carries the
open cone of $r_1,r_3$ onto that of $s_1,s_3$, so $A_0r_2$ is a ray $\sigma$ in
the latter cone. Writing $s_2=\mathbb R_{>0}(x\sigma_1+y\sigma_3)$ and
$\sigma=\mathbb R_{>0}(x'\sigma_1+y'\sigma_3)$ with $x,y,x',y'>0$, the map
$D=\mathrm{diag}(x/x',\,y/y')$ in the basis $(\sigma_1,\sigma_3)$ has positive
determinant, fixes $s_1$ and $s_3$, and carries $\sigma$ to $s_2$. Take
$A=DA_0$. $\square$

An earlier revision of this lemma omitted \eqref{cf:eq-orderedray} and said the
positive determinants could be arranged ``after swapping the names once if
necessary''. A swap performed in one triple only destroys the correspondence it
is supposed to produce, and the peer refuted that step; the hypothesis is now
stated and the swap is simultaneous. In the application below the condition is
not inferred from the two cones: both determinants are computed and are
positive.

\emph{A positive-turn chart, and the cuts.} Parametrise the embedded arc by
arclength as $\gamma(s)$ with $\gamma(0)=p$ and unit tangent $\gamma'(0)=u$.
Because the tangent turns strictly positively, after shrinking the chart there
is a continuous strictly increasing lift $\theta$ with
\[
   \gamma'(s)=\cos\theta(s)\,u+\sin\theta(s)\,Ju,\qquad
   \theta(0)=0,\qquad |\theta(s)|<\tfrac\pi2,
\]
where $J$ is the positive quarter turn. Put $v=-Ju$, so that $(v,u)$ is a
positively oriented orthonormal basis, and set
\[
   \xi(s)=\langle\gamma(s)-p,\,v\rangle,\qquad
   \eta(s)=\langle\gamma(s)-p,\,u\rangle,
\]
so that $\xi'(s)=-\sin\theta(s)$ and $\eta'(s)=\cos\theta(s)$. Hence $\xi$
increases strictly for $s<0$ and decreases strictly for $s>0$, with a strict
maximum $\xi(0)=0$, while $\eta$ increases throughout. For every level
sufficiently close to $\xi(0)$ from below, strict monotonicity and the
intermediate value theorem give unique cuts $s_-<0<s_+$ with
$\xi(s_-)=\xi(s_+)$, and both tend to $0$ as the level tends to $\xi(0)$. Write
$p_\pm=\gamma(s_\pm)$. Equal transverse coordinates and monotone $\eta$ give
\[
   p_+-p_-=\ell u,\qquad \ell>0,\qquad \ell\to0 .
\]
Two side facts follow at once and are what the earlier revision lacked: the
central arc $\gamma((s_-,s_+))$ lies strictly in $\xi>\xi(s_-)$, and both
retained tails lie strictly in $\xi<\xi(s_-)$.

\emph{The affine fit, quantitatively.} In the positively oriented model basis
$v_0=(-1,0)$, $u_0=(0,-1)$ one has $q=\tfrac4{11}$ and
\[
   b'(-2)\in\mathbb R_{>0}(qv_0+u_0),\qquad
   b'(0)\in\mathbb R_{>0}u_0,\qquad
   b'(2)\in\mathbb R_{>0}(-qv_0+u_0).
\]
Write the two target endpoint tangents in the basis $(v,u)$ as
$T_-=\gamma'(s_-)=av+bu$ and $T_+=\gamma'(s_+)=-cv+du$; then
$a=-\sin\theta(s_-)>0$, $c=\sin\theta(s_+)>0$ and $b,d=\cos\theta(s_\mp)>0$,
and $a,c\to0$, $b,d\to1$ as the cuts approach $p$. The two outer determinants
are $\det(qv_0+u_0,-qv_0+u_0)=2q>0$ and $\det(T_-,T_+)=ad+bc>0$, so
\eqref{cf:eq-orderedray} holds; it is computed, not inferred. Define
\[
   H=\frac{2}{\tfrac ba+\tfrac dc}=\frac{2ac}{bc+ad},\qquad
   x=\frac Hq,\qquad
   y=\frac{\tfrac ba-\tfrac dc}{q\bigl(\tfrac ba+\tfrac dc\bigr)}
    =\frac{bc-ad}{q(bc+ad)},
\]
and let $A$ be the linear map with $A u_0=u$ and $Av_0=xv+yu$. Then
\[
   A(qv_0+u_0)=\tfrac Ha\,T_-,\qquad
   A(-qv_0+u_0)=\tfrac Hc\,T_+,\qquad
   \det A=x=\frac{2ac}{q(bc+ad)}>0,
\]
each by substitution, and
\[
   1-(qy)^2=\frac{4abcd}{(bc+ad)^2}>0,
\]
so $|y|<1/q$ uniformly, while $x\to0$ as the cuts approach $p$: the map $A$
stays bounded. This is the quantitative statement that the earlier revision
replaced by an unquantified ``fixed unit-normalized part of $A$''.

Since $b(2)-b(-2)=12u_0$, put $B=\tfrac{\ell}{12}A$ and
$\Phi(z)=p_-+B\bigl(z-b(-2)\bigr)$. Then $\Phi(b(-2))=p_-$,
$\Phi(b(2))=p_-+\ell A u_0=p_-+\ell u=p_+$, and the endpoint tangent rays match
with positive scale. Because $\ell\to0$ while $A$ stays bounded, the diameter of
$\Phi(c([-2,2]))$ tends to $0$, so the cuts may be chosen so that the whole
inserted arc lies in a preassigned disc $\Delta$ about $p$ whose intersection
with the diagram is contained in the embedded chart --- the disc is fixed first
and the cuts afterwards.

\emph{Only the model's own double point is created.} In the basis $(v_0,u_0)$
the transverse coordinate of $c(t)$ is $1-t^2$, which equals $-3$ at both
endpoints, so the model's transverse excess over its endpoint chord is
$4-t^2>0$ for $-2<t<2$. Since $Bv_0=\tfrac{\ell}{12}(xv+yu)$ with $x>0$ and
$Bu_0=\tfrac{\ell}{12}u$, the physical transverse excess of the inserted arc
over the chord $[p_-,p_+]$ is exactly
\[
   \frac{\ell x}{12}\bigl(4-t^2\bigr)>0 .
\]
So the inserted interior lies strictly in $\xi>\xi(s_-)$ while both retained
tails lie strictly in $\xi<\xi(s_-)$: they meet only at the two joins. Together
with the shrinking of the previous paragraph, which keeps the inserted arc away
from every nonlocal part of the diagram, this \emph{proves} rather than assumes
that the only double point created is the model's own.

\emph{The replacement, and why the curve stays $C^\infty$ regular.} Replace the
sub-arc of $F$ between $p_-$ and $p_+$ by $\Phi\circ c$, modified near its two
endpoints as follows. At each join the two one-sided unit tangents already
agree, $\Phi c'(\pm2)$ being a positive multiple of $\Phi b'(\pm2)$ and that of
the old tangent, so the concatenation is $C^1$; it need not be $C^\infty$, and
the collar that repairs that is constructed here rather than described. An
earlier revision said only that one may ``interpolate the tangent angle by the
same device'', which does not say what curve results, and interpolating angles
moves the endpoint.

Before choosing the two collars, take disjoint small neighbourhoods of
$p_-$ and $p_+$ meeting no part of the retained old curve or fitted model
outside their respective local endpoint intervals. These neighbourhoods
exist by compactness: each endpoint has a unique preimage in the joined
curve, the only model double point is away from the endpoints, and the
transverse-excess argument has excluded a model--tail intersection.
Delete small endpoint parameter intervals; each remaining compact image
has positive distance from that endpoint. Take a ball smaller than those
distances. As its length tends to zero, the region between the two local
graphs used for a collar shrinks to the endpoint, so both collars can be
chosen inside these balls. This also separates them from the monogon and
from one another.

\emph{The collar, as a graph.} Work at the join $p_-$ first; the join at
$p_+$ is constructed after property (3) below, with its own signs printed
rather than left to "roles exchanged". In the chart coordinates
$(\xi,\eta)$ of the positive-turn chart --- $\xi=\langle\gamma-p,v\rangle$ with
$v=-Ju$, $\eta=\langle\gamma-p,u\rangle$ --- the old arc is a graph
$\xi=f(\eta)$, since $\eta'=\langle\gamma',u\rangle=\cos\theta>0$ there. Its
slope carries a sign that is
load-bearing below, so it is computed:
$\xi'=\langle\gamma',v\rangle=-\sin\theta$, whence
\[
   f'(\eta)=\frac{\xi'}{\eta'}=-\tan\theta .
\]
For $\eta<\eta(p)$ the angle $\theta$ is strictly negative, $\theta$ being
strictly increasing with $\theta(0)=0$, so $f'>0$ there --- not $f'<0$, which is
what the earlier revision's $f'=\tan\theta$ gave. Let
$\eta_-=\eta(p_-)<\eta(p)$. The inserted arc leaves $p_-$ with the same unit
tangent, so near its start it is also a graph $\xi=g(\eta)$ with
$g(\eta_-)=f(\eta_-)$ and $g'(\eta_-)=f'(\eta_-)$; and because the model turns
strictly negatively its tangent angle only decreases from $\theta(s_-)<0$, so by
the same formula
\[
   g'>f'>0
\]
on that stretch. Two consequences are used below: $g>f$ on
$(\eta_-,\eta_-+\lambda]$, the two agreeing at $\eta_-$ with $g'>f'$; and at
every point of the collar the smaller slope is $f'(\eta)$, still positive. The
bound is pointwise of necessity: $f'=-\tan\theta$ \emph{decreases} along the
collar, $\theta$ increasing, so $0<f'(\eta)<f'(\eta_-)$ there and an endpoint
bound from the left end is unavailable. Fix
$\lambda>0$ small enough that $[\eta_-,\eta_-+\lambda]$ lies both below
$\eta(p)$ and inside the stretch on which the inserted arc is a graph, and set,
on $[\eta_-,\eta_-+\lambda]$,
\[
   h(\eta)=\bigl(1-\varphi_\lambda(\eta)\bigr)f(\eta)+\varphi_\lambda(\eta)\,
   g(\eta),
   \qquad
   \varphi_\lambda(\eta)=\varphi\Bigl(\frac{\eta-\eta_-}{\lambda}\Bigr),
\]
with $\varphi$ the transition profile of Lemma~\ref{cf:lem-rounding}. The modified
curve runs along the old arc up to $\eta_-$, along the graph of $h$ across the
collar, and along the inserted arc from $\eta_-+\lambda$ on. Three properties,
each proved from the formula.

\emph{(1) It is $C^\infty$ and regular, with positive speed.} $h$ is a $C^\infty$
function, and every derivative of $\varphi$ vanishes at $0$ and $1$, so $h$
agrees with $f$ to infinite order at $\eta_-$ and with $g$ to infinite order at
$\eta_-+\lambda$: the two joins are $C^\infty$. Parametrized by $\eta$, the
collar has velocity $h'(\eta)\,v+u$ in the frame $(v,u)$, of norm
$\sqrt{1+h'(\eta)^2}\geq1$, so its speed is positive and it is regular; being a
graph, it is embedded.

\emph{(2) No tangent of the collar equals $u$, and no smallness condition is
needed.} The tangent is parallel to $u$ exactly where $h'=0$, and
\[
   h'=(1-\varphi_\lambda)f'+\varphi_\lambda g'
      +\frac{\varphi'\bigl((\eta-\eta_-)/\lambda\bigr)}{\lambda}\,
       \bigl(g-f\bigr).
\]
Every term is nonnegative, and the sum of the first two is positive: it is the
convex combination $(1-\varphi_\lambda)f'+\varphi_\lambda g'$ of two positive
numbers --- each \emph{term} separately can vanish, $\varphi_\lambda$ being $0$
at the left end and $1$ at the right --- while the third term is
$\varphi'\cdot(g-f)/\lambda\geq0$, since $\varphi'\geq0$ and $g-f\geq0$ there,
the two agreeing at $\eta_-$ with $g'>f'$. Hence, pointwise,
\[
   h'(\eta)\geq(1-\varphi_\lambda)f'(\eta)+\varphi_\lambda g'(\eta)
   \geq f'(\eta)>0 ,
\]
the middle inequality because $g'>f'$, so $h'$ never vanishes and the collar
has no tangent equal to $u$; and none equal to $-u$ either, a graph over $\eta$ having
$\eta'>0$ throughout. An earlier revision, working from the wrong slope sign,
had both $f'$ and $g'$ negative, needed a Taylor bound on $g-f$ to control the
third term, and chose $\lambda$ small to make the sum negative. With the frame
computed the third term is on the same side as the other two and no choice of
$\lambda$ is required.

\emph{(3) It creates no double point and changes no turning.} Pointwise
$f\leq h\leq g$ on the collar --- the value is a convex combination and $g\geq f$
there, which is the separation the corrected slope chain supplies --- so the
collar lies in the region between the two graphs; that region is inside the
disc $\Delta$ and inside the embedded chart, where the only strands of the
diagram are the old arc --- whose collar stretch is removed --- and the inserted
arc. The collar is embedded by~(1) and meets those two only at its endpoints,
so no double point is created in it, and the model's own double point, at
$|t|=1$, is interior to the inserted arc and untouched. For the turning: the
collar's tangent angle is continuous, stays in $(-\pi/2,0)$ --- the slope
$h'$ being positive and finite, so the tangent angle $\theta$ has
$-\tan\theta=h'>0$ with $\cos\theta>0$ --- and takes at its ends exactly the
angles of the two arcs it joins, so the lift of the tangent
along the modified curve is the concatenation of the old lifts with an
interpolating stretch of the same endpoint values; the total tangent winding is
unchanged by its insertion. An earlier revision stopped at $C^1$
and the document then carried a lemma to recover smoothness. This sentence is what the downstream consumers of this
lemma read, the front construction below taking tangent directions of the
curve, and an intermediate revision of this proof deleted it while rewriting
the tail; it is restored here.

\emph{The collar at $p_+$.} The same three properties are now proved at the
other join, with its own signs printed: here the \emph{incoming} arc is the
inserted one and the \emph{outgoing} arc is the old one, and both slopes are
negative. Let $\eta_+=\eta(p_+)>\eta(p)$. On a stretch
$[\eta_+-\lambda_+,\eta_+]$ chosen above $\eta(p)$ and inside the stretches
on which both arcs are graphs, write $\xi=g(\eta)$ for the inserted arc and
$\xi=f(\eta)$ for the old arc extended backward from $p_+$; the two agree at
$\eta_+$ with common slope $m_+=-\tan\theta_+<0$, the angle
$\theta_+=\theta(s_+)$ lying in $(0,\tfrac\pi2)$. Just left of the join the
inserted arc turns strictly negatively into its endpoint, so its angle
exceeds $\theta_+$ there, while the old arc turns positively, so its angle
lies below $\theta_+$; by $\text{slope}=-\tan\theta$, decreasing in
$\theta$,
\[
   g'(\eta)<m_+<f'(\eta)<0
   \qquad\text{on }[\eta_+-\lambda_+,\eta_+),
\]
the outer inequality $f'<0$ because $\theta>0$ above $\eta(p)$. Integrating
$g'-f'<0$ backward from the common value at $\eta_+$ gives $g>f$ on
$[\eta_+-\lambda_+,\eta_+)$. Set
\[
   h=\bigl(1-\chi_{\lambda_+}\bigr)g+\chi_{\lambda_+}f,
   \qquad
   \chi_{\lambda_+}(\eta)=\varphi\Bigl(\frac{\eta-(\eta_+-\lambda_+)}{\lambda_+}\Bigr),
\]
with the same transition profile $\varphi$: the modified curve runs along the
inserted arc up to $\eta_+-\lambda_+$, along the graph of $h$ across the
collar, and along the old arc from $\eta_+$ on, the two joins $C^\infty$ by
the flat endpoint jets of $\varphi$ exactly as in (1). For the derivative,
\[
   h'=\bigl(1-\chi_{\lambda_+}\bigr)g'+\chi_{\lambda_+}f'
      +\frac{\varphi'\bigl((\eta-\eta_++\lambda_+)/\lambda_+\bigr)}{\lambda_+}
       \,\bigl(f-g\bigr),
\]
and the sign of $f-g$ in the cutoff term is exactly what the negativity of
the two slopes alone does not control: here $f-g\leq0$ by the separation just
integrated, and $\varphi'\geq0$, so the cutoff term is nonpositive, while the
convex part is a convex combination of two negative numbers. Hence,
pointwise,
\[
   h'(\eta)\leq\bigl(1-\chi_{\lambda_+}\bigr)g'(\eta)+\chi_{\lambda_+}f'(\eta)
   \leq f'(\eta)<0 ,
\]
the middle inequality because $g'<f'$, and the bound pointwise for the
mirrored reason: $f'$ varies along the collar and no endpoint bound is
available. So $h'$ never vanishes, and this collar --- a graph over $\eta$
with $\eta'>0$ throughout --- has no tangent equal to $u$ and none equal to
$-u$; its tangent angle stays in $(0,\tfrac\pi2)$, with
$-\tan\theta=h'<0$ and $\cos\theta>0$, and takes at its ends exactly the
angles of the two arcs it joins, so the lift concatenation of (3) applies to
it verbatim and the total tangent winding is unchanged. Pointwise
$f\leq h\leq g$, the value being a convex combination and $g\geq f$ there, so
the collar lies in the region between the two graphs, inside the disc
$\Delta$ and the embedded chart, and it is embedded and meets the two arcs
only at its endpoints: no double point is created, by the argument of (3)
unchanged.

\emph{The four conclusions, separately.} (ii): $c'(t)=(2t,1-3t^2)$ is parallel to
$u_0$ only at $t=0$, where $c'(0)=-u_0$; since $A$ is invertible with
$Au_0=u$, the inserted arc has no tangent $u$ and exactly one tangent $-u$, and
the retained tails have neither, their angles lying in $(-\tfrac\pi2,\tfrac\pi2)$
away from $0$.

(iii): if $c(s)=c(t)$ then $s=\pm t$, and the second coordinate forces
$2t(1-t^2)=0$, so the only pair of distinct parameters is $\{-1,1\}$: exactly
one double point. With the later branch over the earlier one its sign is that of
$\det(c'(1),c'(-1))=-8<0$, and $\det B>0$ preserves it.

(iv) for $\rot$: Let $R$ be the rotation carrying the positive orthonormal basis
$(v_0,u_0)$ to $(v,u)$ and put $C=R^{-1}A$. Relative to $(v_0,u_0)$,
$C$ has matrix
$\left(\begin{smallmatrix}x&0\\y&1\end{smallmatrix}\right)$ with $x>0$, so
$C_t=\left(\begin{smallmatrix}1-t+tx&0\\ty&1\end{smallmatrix}\right)$
joins $I$ to $C$ inside $\mathrm{GL}^+(2,\mathbb R)$. If $R_t$ rotates
through $t$ times any fixed angle representing $R$, first $C_t$ and then
$R_tC$ give a path $A_t$ from $I$ to $A=RC$ in that group. Apply
$z\mapsto A_tz/|A_tz|$ to the closed direction loop obtained by following
the tangent path of $c$ and the tangent path of $b$ backwards.
Lemma~\ref{cf:lem-turnlift}(iii) therefore preserves their compatible endpoint
lift-increment difference. The tangent of $b$ follows the short positive arc between the
endpoint rays; the tangent of $c$ follows the complementary clockwise arc, since
$\det(c',c'')=-2(1+3t^2)<0$ and it passes through $-u_0$ at $t=0$; so their
relative winding is $-1$. The old central arc also follows the short positive
arc, its lifted sweep $\theta(s_+)-\theta(s_-)$ lying in $(0,\pi)$. Hence Lemma~\ref{cf:lem-turnlift}(iii) says that the replacement changes the
closed curve's rotation by exactly $-1$. For
$w$: the removed arc was embedded and carried no crossing, so the writhe changes
by the one new negative crossing, that is by $-1$.

\emph{The polynomial conclusion, without a knot-category detour.}
The construction just completed also proves that $F'$ remains in the lemma's
input class.  It replaces one oriented arc by one $C^\infty$ regular oriented
arc, leaves the component count unchanged, and creates exactly one transverse
double point in a disc meeting no other strand.  Thus its double points remain
finite and transverse and no triple point is created.

Let $F^{\circ}$ be the oriented diagram obtained from $F'$ by deleting the
unique monogon in $\Delta$ by a Reidemeister-I move.  The move is available:
the preceding separation argument shows that the monogon is disjoint from
all other strands, and the crossing calculation shows it is the unique new
double point.  It replaces that monogon by one crossing-free regular arc in
$\Delta$, so $F^{\circ}$ is again a one-component immersed-circle diagram with
finite transverse double points and no triple points.  Reidemeister-I
invariance of the local polynomial $P$ (Theorem~\ref{lp:core}, from Literature
input~\ref{lp:lm}) gives $P_{F'}=P_{F^{\circ}}$.

Outside $\Delta$, the diagrams $F^{\circ}$ and $F$ coincide.  Inside
$\Delta$, each has one crossing-free oriented arc joining the same two
boundary points in the same traversal direction.  Match every marked
preimage outside that local traversal interval with the identical marked
preimage of the other diagram.  The local intervals contain no marked
preimage, so this bijection preserves cyclic order, crossing pairs,
over/under positions and signs: it is a record isomorphism.  Both actual diagrams have one component and finite transverse crossings.
Lemma~\ref{rp:record-polynomial} therefore gives
$P_{F^{\circ}}=P_F$ directly, and hence $P_{F'}=P_F$.
Equality outside $\Delta$ proves the
remaining clause of~(i).
\end{proof}
```

## cf:thm-carrierfloor — PROVE

reference/SM/sm-3-statesum.tex:4282–4339

```tex
\begin{theorem}[geometric carrier floor]\label{cf:thm-carrierfloor}
\begin{enumerate}
\item[(R)] Here $\rot$ is as in Lemma~\ref{lem:rot} for polygons and
Definition~\ref{cf:def-turning} for the underlying plane curve of a
smooth diagram. Let $D$ be an oriented knot diagram and $-D$ the same
diagram with every arrow reversed. Then $P_{-D}=P_D$; consequently an
oriented knot and its reverse have the same polynomial. Moreover $-D$ has
the same crossing signs and the same writhe as $D$, and the rotation of
its underlying plane curve is the negative of that of $D$.
\item[(A)] Let $L$ and $D$ satisfy the hypotheses of Lemma~\ref{cf:lem-rounding}. For every
$\varepsilon\in(0,\varepsilon_0(L))$, the construction in the proof of that
lemma returns \emph{one} curve and \emph{one} diagram at those data: the
junction inserted at the corner $q_i$ is determined by $\varepsilon$, by the
two incident unit directions and by the transition profile, which is fixed once
and for all in that proof and is not chosen per corner or per curve; the arc
length $\ell$ is then determined by the endpoint condition, and the rest of the
curve is $L$ itself. Write
\[
   \mathrm{Round}(L,D,\varepsilon)=(L_\varepsilon,D_\varepsilon)
\]
for that pair, the \emph{rounding record} of $(L,D)$ at $\varepsilon$, and call
$L_\varepsilon$ the rounded curve and $D_\varepsilon$ the rounded diagram.
\item[(B)] Here $\rot$ is as in Lemma~\ref{lem:rot}, applied to the polygon $L$.
Let $L$ be a closed polygon with nonzero edges and nonzero principal
turns, finitely many transverse double points, no triple points, no corner
at a double point and no corner on a non-incident edge, carrying a diagram
$D$. Assume, after reversing orientation if necessary, that either all
principal turns are positive, or exactly one is negative and all others
are positive. Put $R=|\rot(L)|$. Then
there are a direction $u\in S^1$ and an $\varepsilon_1>0$ such that \emph{for
every} $\varepsilon\in(0,\varepsilon_1)$ the rounded curve $L_\varepsilon$ of
the record $\mathrm{Round}(L,D,\varepsilon)$
from clause~(A) has exactly $R$ points at which its unit
tangent equals $u$ and exactly $R$ at which it equals $-u$; at each of them the
tangent crosses that direction in the positive sense.
\item[(C)] Here $\rot$ is as in Lemma~\ref{lem:rot}, applied to the polygon $L$.
Let $D$ be an oriented knot diagram all of whose crossings are positive, with
writhe $w$, whose underlying plane curve is a closed polygon $L$ with all
principal turns existing, \emph{nonzero}, and of magnitude below $\pi$, with
finitely many double points, all transversal, with no triple points, none of
them a corner of $L$, and no corner of $L$ lying on a non-incident edge; and let
$R$ be the absolute value of its Whitney rotation number.  The
finiteness/transversality and the two corner conditions are what
Lemma~\ref{cf:lem-rounding} asks of its input.  The no-triple condition is preserved by rounding and is needed below
when diagram records are compared.  These
conditions are stated here so that no generic parent polygon is assumed. Assume that, after reversing the
orientation if necessary --- which by clause~(R) changes neither
$P_D$, nor the crossings and their signs, nor $w$, nor $R$ --- either every
principal turn is positive, or exactly one is negative and every other is
positive. Then
\begin{equation}
\mindeg_a P_D(a,z)\;\geq\;1-w-R,
\label{cf:eq-floor}
\end{equation}
and the same bound holds for $f_D(a)=[z^0]P_D(a,z)$ whenever $f_D\neq0$.
\end{enumerate}
\status{new (round~3: clause~(R) and the mirror paragraph of the proof consume Lemma~\ref{lp:coefficient-transport}, F-25-54; the statement's commentary moved to Remark \texttt{rem:rounding-record} and the justification of~(R) into its proof, F-25-57, the rounding record and the determinacy clause of~(A) kept; the transverse knot named $K_T$, F-25-84; the $\rot$ scoping of~(R), F-25-88; the remainder is the round-1 transcription held by bench~A, with per-item locators: (R) the reversal and mirror deductions printed here; (A) CV thm:carrierfloor(A); (B) CV thm:carrierfloor(B); (C) CV thm:carrierfloor(C) (C032)); round~6: the spelling of the minimum $a$-degree unified with Definition~\ref{def:adeg} at three sites, F-25-173}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:4340–4560

```tex
\begin{proof}
\emph{Clause (R).}
Reversing all arrows of a diagram preserves every crossing sign: the sign
is $\sgn\det(u_{\mathrm{over}},u_{\mathrm{under}})$, and reversing both
strands replaces both vectors by their negatives, leaving the determinant
unchanged. Hence the writhe is preserved, and reversal sends a skein triple
$(D_+,D_-,D_0)$ of diagrams to the skein triple $(-D_+,-D_-,-D_0)$, the
oriented smoothing of the reversed diagram being the reverse of the
oriented smoothing. Consider the two maps $D\mapsto P_{-D}$ and
$D\mapsto P_D$ on all oriented link diagrams, with values in
$R=\ZZ[a^{\pm1},z^{\pm1}]$. Both take the value $1$ on the crossing-free
circle, both satisfy the campaign skein of Theorem~\ref{lp:core}, the
first by the preceding sentence, and both are invariant under planar
isotopy and the three Reidemeister moves, since $P$ is
(Theorem~\ref{lp:core}) and reversal carries each such move and isotopy
to one of the same kind. Lemma~\ref{lp:coefficient-transport} identifies
the two maps: $P_{-D}=P_D$ for every diagram $D$. Since $P_D$ is the
polynomial $H_D$ of the oriented link presented by $D$
(Theorem~\ref{lp:core}), an oriented knot and its reverse have the same
polynomial. For a polygonal underlying curve every principal turn changes
sign and Lemma~\ref{cf:lem-turnlift}(ii) negates rotation. For a $C^1$
regular curve, if $\theta$ lifts its normalised tangent, then
$\theta(1-s)+\pi$ lifts the reversed tangent with the negative endpoint
increment, as in Lemma~\ref{cf:lem-turnlift}(i).

\emph{Clause (A).} The transition profile is fixed once and for all in the proof of
Lemma~\ref{cf:lem-rounding}.  At each corner, $\varepsilon$ and the two incident
unit directions determine that profile's junction, and the endpoint condition
determines its length $\ell$; outside the rounding discs the curve is $L$, and
the diagram data are inherited.  Thus the named construction returns one
specified pair at every allowed $\varepsilon$.  This asserts uniqueness of the
fixed construction's record, not uniqueness among all possible smoothings.

\emph{Clause (B).}
Reversing the orientation of $L$ negates every principal turn and the signed rotation and
preserves every self-crossing sign, so perform the allowed normalization once. In the
uniform case $\rot(L)=R\geq1$ by Lemma~\ref{lem:uniformrot}(i); in the one-dissent case the same holds by Lemma~\ref{lem:uniformrot}(ii).

Take $\varepsilon_1=\varepsilon_0(L)$, the clearance of Lemma~\ref{cf:lem-rounding}.
Choose $u\in S^1$ so that neither $u$ nor $-u$ is an edge direction and, in the
one-dissent case, neither lies in the negative turn's closed swept arc $A$, of
length $\alpha:=|\vartheta_-|<\pi$. Such $u$ exists: in the one-dissent case $A\cup(-A)$
has length at most $2\alpha<2\pi$, while in the uniform case there is no such arc; the additional
forbidden set of edge directions and their antipodes is finite. This choice depends only on $L$. Fix an argument $\phi$ of $u$.

Fix $\varepsilon\in(0,\varepsilon_1)$, write
$(L_\varepsilon,D_\varepsilon)=\mathrm{Round}(L,D,\varepsilon)$, and let $T$ be
its unit-tangent map. Parameterize the rounded traversal by $s\in[0,1]$, with
$s=0$ in the interior of a straight part; because $u,-u$ are not edge directions, its tangent
is congruent to neither $\phi$ nor $\phi+\pi$. Concatenating straight-part arguments
with the junction lifts supplied by Lemma~\ref{cf:lem-rounding}(b) gives a continuous
$\theta\colon[0,1]\to\mathbb R$, starting at an argument $\theta(0)$ of $T(0)$.
Since $T(1)=T(0)$, write $\theta(1)=\theta(0)+2\pi m$ for an integer $m$.

Each straight portion contributes zero tangent increment, and each
rounding junction contributes its principal angle by
Lemma~\ref{cf:lem-rounding}(b). Thus
$2\pi m=\sum_i\vartheta_i=2\pi\rot(L)=2\pi R$, by
Lemma~\ref{lem:rot}.
Thus
\[
 \theta(1)=\theta(0)+2\pi R.                                  \tag{*}
\]

Fix $\beta=\phi$ or $\phi+\pi$. Because $u,-u$ are not edge directions, no
level $\beta+2\pi k$ is met on a straight part or at a junction endpoint; by
the choice of $u$, none is met on the decreasing junction. Hence floor jumps
occur only in increasing junctions and never elsewhere. Lemma~\ref{cf:lem-rounding}(b)
makes each occurrence unique with positive angular derivative. Put
\[
 x=\frac{\theta(0)-\phi}{2\pi},\qquad
 y=\frac{\theta(0)-(\phi+\pi)}{2\pi}.
\]
For $u$, (*) and the integer floor identity give, separately,
\[
 \#T^{-1}(u)=\lfloor x+R\rfloor-\lfloor x\rfloor=R.
\]
For $-u$, the same argument at the other levels gives
\[
 \#T^{-1}(-u)=\lfloor y+R\rfloor-\lfloor y\rfloor=R.
\]
There are finitely many junctions, so the preimages are finite; their positive derivatives prove the assertion for arbitrary $\varepsilon$.

\emph{Clause (C).} Fix $\varepsilon\in(0,\varepsilon_1)$ with $\varepsilon_1$ the clearance of
clause~(B) and pass to the rounding record
$(L_\varepsilon,D_\varepsilon)=\mathrm{Round}(L,D,\varepsilon)$ of
clause~(A) --- one curve and one diagram, not a member
of an unnamed family. Lemma~\ref{cf:lem-rounding}(c),(d) preserves all crossings and their
oriented decorated data, the writhe and the rotation number. The rounded
diagram and the original polygonal diagram have the same named record,
including the single original component, so
Lemma~\ref{rp:record-polynomial} gives equal $P$ values. By clause~(B) there is a direction $u$ met by the tangent of
$L_\varepsilon$ exactly $R$ times, each time positively, and likewise for
$-u$. Rotate coordinates so
that $u$ is the downward vertical. The rounded diagram then has exactly $R$
downward vertical tangencies and $R$ upward ones.

Switch every crossing. The result is a diagram $\overline D$ of the mirror knot,
with the same underlying plane curve --- hence the same tangencies --- and with
writhe $-w$; every crossing of $\overline D$ is negative. Apply
Lemma~\ref{cf:lem-curl} at each of the $R$ downward vertical tangencies; they are
isolated, lie in the interiors of positively turning rounding arcs
(clause~(B)), and each rounding junction sweeps an angle of magnitude below $\pi$, so it
contains at most one of these downward tangencies. The rounding discs
returned by Lemma~\ref{cf:lem-rounding}(e) are pairwise disjoint and meet no
crossing. Choose each curl disc inside its corresponding rounding disc.
Thus all $R$ replacements have disjoint supports and leave one another
intact. Call the result $T$. By
Lemma~\ref{cf:lem-curl}, $P_T=P_{\overline D}$, $T$ has no downward vertical
tangency, and it has writhe
\[
w(T)=-w-R .
\]
Every crossing of $T$ is negative: the old ones by the switch, the $R$ new ones by
Lemma~\ref{cf:lem-curl}(iii).

We now construct the transverse lift rather than import a
front criterion.  Write the smooth regular parametrisation of $T$ as
$s\mapsto(x(s),z(s))$, put
\[
 v(s)=\sqrt{x'(s)^2+z'(s)^2},\qquad
 y_0(s)=-\frac{x'(s)}{v(s)+z'(s)},
\]
and use the convention that, in the $xz$ projection, the branch with smaller
$y$-coordinate is drawn over.  Since $T$ has no downward vertical tangency,
$v+z'>0$ everywhere: equality would force $x'=0$ and $z'<0$.  Thus $y_0$ is
smooth and periodic, and direct algebra, with no division by $x'$, gives
\[
 z'-y_0x'=z'+\frac{x'^2}{v+z'}
 =z'+\frac{v^2-z'^2}{v+z'}=v>0.                 \tag{*}
\]

It remains only to impose the crossing order.  At a crossing branch there is
no vertical tangency, so put $m=z'/x'$.  The strict inequality in~(*) permits
$y<m$ on a rightward branch and $y>m$ on a leftward branch.  For every crossing
choose admissible constants $c_{\rm O}<c_{\rm U}$ at its over- and underpassing
preimages.  Such a choice is automatic if the overpass points right: after
choosing any admissible $c_{\rm U}$, take
$c_{\rm O}<\min\{m_{\rm O},c_{\rm U}\}$.  If both point left, choose any
$c_{\rm O}>m_{\rm O}$ and then
$c_{\rm U}>\max\{m_{\rm U},c_{\rm O}\}$.  The only remaining case has
$x'_{\rm O}<0<x'_{\rm U}$.  Every crossing of $T$ is negative, and here
\[
 0>\det(t_{\rm O},t_{\rm U})
   =x'_{\rm O}x'_{\rm U}(m_{\rm U}-m_{\rm O}).
\]
Since $x'_{\rm O}x'_{\rm U}<0$, this says $m_{\rm O}<m_{\rm U}$; choose
$m_{\rm O}<c_{\rm O}<c_{\rm U}<m_{\rm U}$.  These are exactly the two allowed
half-lines and the required over/under order.

There are finitely many crossing preimages.  Around each one $s_j$, choose
pairwise disjoint cyclic parameter intervals $(\alpha_j,\beta_j)$ so small that
$z'-c_jx'>0$ throughout.  Using the explicit flat transition profile
$\varphi$ displayed in the proof of Lemma~\ref{cf:lem-rounding}, define a smooth
bump on the circle by
\[
 \psi_j(s)=
 \begin{cases}
 \varphi\!\left((s-\alpha_j)/(s_j-\alpha_j)\right),&
       \alpha_j\le s\le s_j,\\
 \varphi\!\left((\beta_j-s)/(\beta_j-s_j)\right),&
       s_j\le s\le\beta_j,\\
 0,&\text{otherwise}.
 \end{cases}
\]
All endpoint derivatives are zero, so this is smooth, equals one at $s_j$ and
has support in that interval.  Set
\[
 y=y_0+\sum_j\psi_j(c_j-y_0).
\]
The supports are disjoint.  On the $j$-th one,
\[
 z'-yx'=(1-\psi_j)(z'-y_0x')+\psi_j(z'-c_jx')>0,
\]
and outside them this is~(*).  Hence $y$ is smooth and periodic and the lift
$s\mapsto(x(s),y(s),z(s))$ is positively transverse to $dz-y\,dx$.

Finally the lift is regular because its $xz$ projection is immersed.  If two
lifted points agreed, their projected points would agree; the only distinct
parameters with that property are the two preimages of a listed double point,
and there $c_{\rm O}<c_{\rm U}$.  Thus the lift is injective, hence, by
compactness of the parameter circle, an embedded transverse knot $K_T$.
Its front and its smaller-$y$ over/under assignments are exactly the
diagram $T$.

By Theorem~\ref{fd:contact}, $\operatorname{sl}(K_T)=w(T)=-w-R$. Since
$P_T=P_{\overline D}$, Theorem~\ref{fd:contact} applied to $K_T$ with its
actual finite regular generic diagram $T$ gives
\[
\max\deg_a P_{\overline D}\;\leq\;-\operatorname{sl}(K_T)-1\;=\;w+R-1 .
\]
For every oriented link diagram $D$ let $\overline D$ be its mirror, the
diagram with every crossing switched, and put
$\mathcal M(D)=P_{\overline D}(a,z)$. Mirroring exchanges $D_+$ with $D_-$
and fixes $D_0$, so the campaign skein of Theorem~\ref{lp:core} on the
mirrored triple, multiplied by $-1$, is
\[
 a^{-1}\mathcal M(D_+)-a\mathcal M(D_-)=-z\,\mathcal M(D_0),
 \qquad \mathcal M(\bigcirc)=1.
\]
Let $\iota$ be the involutive automorphism $(a,z)\mapsto(a^{-1},-z)$ of
the Laurent ring. If a map $Q$ on oriented link diagrams satisfies these
two conditions and is invariant under planar isotopy and the three
Reidemeister moves, then $\iota\circ Q$ satisfies the campaign skein and
the unknot value with the same invariance, because $\iota$ sends the
coefficients $a^{-1},-a,-z$ to $a,-a^{-1},z$. Two such maps $Q,Q'$
therefore have $\iota\circ Q=\iota\circ Q'$ by
Lemma~\ref{lp:coefficient-transport}, hence $Q=Q'$. Both $\mathcal M$
and $D\mapsto\iota(P_D)=P_D(a^{-1},-z)$ satisfy the two conditions and are
invariant --- the first because $P$ is and mirroring carries a planar
isotopy or a Reidemeister move to one of the same kind, the second because
$P$ is --- hence $P_{\overline D}(a,z)=P_D(a^{-1},-z)$ for every diagram
$D$. As a Laurent-ring automorphism, the
substitution negates every $a$-exponent and cannot cancel a nonzero extreme
coefficient. Hence
$\max\deg_a P_{\overline D}=-\mindeg_a P_D$, and the displayed bound becomes
$\mindeg_a P_D=-\max\deg_a P_{\overline D}\geq1-w-R$, which is
\eqref{cf:eq-floor}. Finally, the support of $f_D$ is contained in the support of
$P_D$, so the same bound holds for it when it is nonzero.

\end{proof}
```

## thm:floor — PROVE

reference/SM/sm-3-statesum.tex:4576–4585

```tex
\begin{theorem}[corner theorem; Theorem~2 of the main text]\label{thm:floor}
Let $Q$ be a subpolygon of a decomposition of a generic polygon, and suppose
that after possibly reversing its orientation either all turns are left, or
exactly one turn is right. Then
\[
\mindeg_a H^+_Q\geq 1-m_Q-|r_Q|=d_Q,\qquad
H^+_Q\in\ZZ[a^{\pm1},z^2],\ \text{so }\mindeg_zH^+_Q\geq0.
\]
\status{new (round~5: the general-polygon branch of the hypothesis removed --- its conclusion was stated in the symbols $H^+_Q$, $m_Q$, $d_Q$, defined only for a subpolygon of a decomposition, and no proof consumed it; the broader class stays available as clause~(C) of Theorem~\ref{cf:thm-carrierfloor} in diagram symbols, F-25-164; round~4: the non-incidence hypothesis of clause~(C) supplied at the site, F-25-132; the remainder is the round-1 transcription of CV thm:carrierfloor(A),(B),(C) via Theorem~\ref{cf:thm-carrierfloor}, lem:rounding, lem:curl (C032; F-25-47), held by bench~A; the $z$-parity clause is the knot clause of registry L-1, support half printed in Theorem~\ref{lp:core}, identification half consuming Literature input~\ref{lit:homfly} (F-25-48); lit: Registry~\ref{reg:etnyre}, \ref{reg:slbound}, \ref{reg:homfly}}
\end{theorem}
```

reference/SM/sm-3-statesum.tex:4586–4603

```tex
\begin{proof}
For a carrier, Lemma~\ref{lem:carriers} supplies every geometric
hypothesis of clause~(C) of Theorem~\ref{cf:thm-carrierfloor} except that
no corner lies on a non-incident edge, which holds directly: a carrier's
corners are original vertices and selected crossing points; an original
vertex lies on no non-incident edge segment of $P$ by (G1), and the only
subsegments containing it are its two incident ones; a selected crossing
point lies in exactly two edge interiors by (G2) and is an endpoint, not an
interior point, of the subsegments into which the crossing sites divide
those two edges. Its actual positive
lift has exactly $m_Q$ crossings, each positive, so its writhe is $m_Q$.
The rotation in that clause is $R=|r_Q|$. Thus its lower degree bound is
$1-m_Q-|r_Q|=d_Q$ for the polynomial of that actual diagram.
Theorem~\ref{lp:core} identifies this polynomial with $H_Q^+$ and proves
its nonvanishing and its support in $\ZZ[a^{\pm1},z^2]$.
Every supported $z$ exponent is therefore nonnegative, which gives the
second bound. A zero coefficient at the corner is permitted.
\end{proof}
```

## cb:blocks — DEFINE

reference/SM/sm-3-statesum.tex:4623–4636

```tex
\begin{definition}[Undominated blocks and their owners]\label{cb:blocks}
Fix a generic polygon $P$, its interlacement graph $G_P$, and an
independent support $S$. For a vertex set $T$ write $N_G(T)$ for the
union of its graph neighbourhoods, and put
\begin{equation}\label{cb:undominated}
 U(S)=V(G_P)\setminus\bigl(S\cup N_{G_P}(S)\bigr).
\end{equation}
The connected components of $G_P[U(S)]$ are called its \emph{blocks}.
An undominated crossing has both visits on one carrier by
Lemma~\ref{lem:carriers}; that carrier is its owner. Write $D_A$ for
the actual positive diagram of a carrier $A$, and $P_A=P_{D_A}$.
These polynomials equal the corresponding $H_A^+$ by
Theorem~\ref{lp:core}.
\end{definition}
```

## cb:products — PROVE

reference/SM/sm-3-statesum.tex:4638–4650

```tex
\begin{lemma}[Actual block diagrams and the carrier product]
\label{cb:products}
Every block $H$ has one owner and admits an actual positive carrier
diagram $D_H$ with exactly its restricted named cyclic record. Its
polynomial $P_H$ is independent of the further smoothings used to
produce it. For every original carrier $A$,
\begin{equation}\label{cb:product}
 P_A=\prod_{H\text{ owned by }A}P_H,
 \qquad m_A=\sum_{H\text{ owned by }A}|H|.
\end{equation}
With no owned blocks the actual diagram has value $1$ and $m_A=0$.
\status{proved (refereed: bench A, 2026-09-06T00:35:51Z and 2026-09-06T02:03:45Z; transcribed from RC d6\_vertexedge, carrier products (C035); round~3, per clause (F-25-105): (a) one owner per block --- printed here from Lemma~\ref{lem:carriers}(iii),(iv); in RC the assertion sits with its canonical definition (def:canonical, d1\_setup: ``each such component has a unique owner carrier'', ``each undominated crossing has one owner'') and the splitting argument of def:canonical-total, and is applied in the unlabelled carrier-realization paragraph immediately after the proof of mp:blocks (d2c\_polynomial\_products, lines 471--489; the proof ends at line 469), not inside it (bench B, P-25-36/37 F105-POSITION); the round-3 locators s7:owner-restriction (an owner-restricted-set display) and s7:singleton (the singleton-cut lemma) do not carry it (F-25-105, re-checked in round~5); (b) an actual block diagram with the restricted record --- the greedy support printed here (RC mp:blocks takes such diagrams as supplied); (c) independence of $P_H$ from the further smoothings --- printed here from Lemma~\ref{rp:record-polynomial}; the product identity --- Lemma~\ref{mp:blocks} (RC d2c\_polynomial\_products mp:blocks))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:4651–4695

```tex
\begin{proof}
The self-crossings of a carrier are exactly its owned undominated
labels, by Lemma~\ref{lem:carriers}(iii). If two such labels interlace,
their alternating four visits cannot lie on two different carriers,
by that lemma's noncrossing assertion. Applying this along an
interlacement path puts every connected block on one owner.

Fix one nonempty block $H$. Starting at $S$, choose any label
$c\in U(S)\setminus H$ and adjoin it to the support. It is adjacent
to no selected label, so the enlarged support is independent. At any
such step, with current support $T$, the new residual set is exactly
\begin{equation}\label{cb:greedy-step}
 U(T\cup\{c\})=U(T)\setminus\bigl(\{c\}\cup N_{G_P}(c)\bigr).
\end{equation}
No original label outside $H$ in $U(S)$ is adjacent to a label of $H$,
since $H$ is a connected component of the induced graph. Thus every
step preserves all labels of $H$ and removes at least the chosen label.
The sets only shrink. After at most $|U(S)\setminus H|$ steps there is
an independent support $S_H\supseteq S$ with $U(S_H)=H$.

Lemma~\ref{lem:carriers} supplies actual geometric carriers for $S_H$.
The preceding connectedness argument puts all labels of $H$ on one
of them. No other self-crossing label survives, so its actual positive
diagram is a required $D_H$. Successor splitting retains the cyclic
order inherited from the original traversal. The surviving crossing
germs have not changed. Therefore the complete record of $D_H$ is
exactly the original record restricted to $H$, with its signs, pairing
and over/under choices. This statement concerns an actually constructed
diagram; it does not assume arbitrary Gauss subwords are realizable.
Any other choices produce the same named record, so
Lemma~\ref{rp:record-polynomial} proves independence of $P_H$.

For the original owner $A$, the connected components of its own
interlacement graph are precisely the blocks owned by it: its
self-crossing labels are their union and there are no graph edges
between different blocks. The preceding construction has supplied an
actual diagram for every one of these restricted records.
Lemma~\ref{mp:blocks} now constructs clean marked joins with the full
record of $D_A$ and proves the product in~\eqref{cb:product}.
Every retained crossing is positive and appears once, proving the
crossing-count identity. If there are no owned blocks, $D_A$ is an
actual crossing-free one-circle diagram. Its local polynomial is $1$
by the initialization in Theorem~\ref{lp:core}, and its crossing count
is zero. No empty link is evaluated.
\end{proof}
```

## cb:singleton — PROVE

reference/SM/sm-3-statesum.tex:4697–4702

```tex
\begin{lemma}[An isolated crossing forces a zero corner coefficient]
\label{cb:singleton}
Let $A$ be a uniform carrier of $S$, and suppose one of its self-crossing
labels $c$ interlaces no other self-crossing of $A$. Then $c(A)=0$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z, 2026-09-06T01:50:42Z and 2026-09-06T05:12:19Z; transcribed from RC d6\_vertexedge, isolated crossing (C035))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:4703–4758

```tex
\begin{proof}
An undominated label interlacing $c$ would have the same owner $A$ by
Lemma~\ref{cb:products}. The hypothesis therefore makes $\{c\}$ a
singleton block of $G_P[U(S)]$. Since $c\in U(S)$,
$S'=S\cup\{c\}$ is independent. Equation~\eqref{cb:greedy-step} and
$N_{G_P}(c)\cap U(S)=\varnothing$ give $U(S')=U(S)\setminus\{c\}$.

Smoothing $c$ splits $A$ into two actual daughter carriers
$\Lambda_1,\Lambda_2$. Each other block owned by $A$ lies wholly in
one of the two intervals cut by $c$. Indeed none of its chords
interlaces $c$, and a connected interlacement path cannot connect
chords internal to different intervals. Successor splitting therefore
assigns that whole block to exactly one daughter. Blocks owned by
other carriers remain there. The singleton block's actual one-crossing
diagram has polynomial $1$ by Lemma~\ref{lc:single-crossing} and
positive writhe $1$. Applying Lemma~\ref{cb:products} before and after
the split consequently gives
\begin{equation}\label{cb:singleton-products}
 P_A=P_{\Lambda_1}P_{\Lambda_2},\qquad
 m_A=m_{\Lambda_1}+m_{\Lambda_2}+1.
\end{equation}
The two new smoothing turns are nonzero and opposite as real principal
angles. Every old turn of $A$ lies on exactly one daughter. Each
daughter has at least three corners by Lemma~\ref{lem:carriers},
including its one new corner, so it has at least two inherited turns.
One daughter is uniform with the old sign and the other has exactly
one dissent. Summing principal angles gives
$r_A=r_{\Lambda_1}+r_{\Lambda_2}$. Lemma~\ref{lem:uniformrot}, with
orientation reversal if the old sign is negative, puts all three
rotation integers on that old sign's ray. Hence
\begin{equation}\label{cb:singleton-rotations}
 |r_A|=|r_{\Lambda_1}|+|r_{\Lambda_2}|.
\end{equation}

Put $f_A=[z^0]P_A$ and $g_i=[z^0]P_{\Lambda_i}$. The knot support in
Theorem~\ref{lp:core} has no negative $z$ exponents, so the first
identity in~\eqref{cb:singleton-products} gives $f_A=g_1g_2$.
If $f_A=0$, the desired coefficient is zero without assigning a degree
to it. Otherwise both $g_i$ are nonzero in the Laurent integral domain.
Theorem~\ref{thm:floor} applies to the actual uniform and one-dissent
daughters: they are subpolygons of the decomposition $S'$ of $P$
(Lemma~\ref{lem:carriers}(i)), the theorem's domain, and their turn
patterns are the ones it requires. It gives
$\mindeg_a g_i\geq 1-m_{\Lambda_i}-|r_{\Lambda_i}|$ separately.
Every exponent of the product is at least the sum of these bounds;
coefficient cancellation cannot create a smaller exponent. Thus
\begin{align}
 \mindeg_a f_A
 &\geq 2-(m_{\Lambda_1}+m_{\Lambda_2})
                -(|r_{\Lambda_1}|+|r_{\Lambda_2}|)\notag\\
 &=2-(m_A-1)-|r_A|\notag\\
 &=(1-m_A-|r_A|)+2=d_A+2.
 \label{cb:singleton-gap}
\end{align}
The coefficient at degree $d_A$ is zero, which is exactly $c(A)$.
\end{proof}
```

## cb:embedded-rotation — PROVE

reference/SM/sm-3-statesum.tex:4760–4765

```tex
\begin{lemma}[Exterior-angle count for an embedded polygon]
\label{cb:embedded-rotation}
Every embedded regular polygon has rotation $+1$ or $-1$, according
to its traversal orientation around the bounded complementary region.
\status{proved (refereed: bench A, 2026-09-05T19:32:30Z; transcribed from the exterior-angle count as printed (C035; F-25-40))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:4766–4799

```tex
\begin{proof}
Lemma~\ref{lem:gauss-two-discs} supplies a finite straight triangulation
of the bounded complementary region, a disc with Euler characteristic
one. Its boundary is the polygon with possible straight subdivisions.
Write $I$ for the number of interior vertices, $B$ for boundary vertices,
$E$ for all edges and $F$ for triangular faces. A simple boundary cycle
has $B$ boundary edges. Euler's count is
\begin{equation}\label{cb:euler-disc}
 I+B-E+F=1.
\end{equation}
Every interior edge belongs to two triangles and every boundary edge
to one. Counting triangle-edge incidences gives
\begin{equation}\label{cb:edge-incidences}
 3F=2(E-B)+B=2E-B.
\end{equation}
Equation~\eqref{cb:euler-disc} first gives $E=I+B+F-1$.
Substituting this into~\eqref{cb:edge-incidences} gives
$3F=2I+B+2F-2$, and hence $F=2I+B-2$.

The sum of all Euclidean triangle angles is $\pi F$. At each
interior vertex the angles fill a full turn $2\pi$. If $\alpha_j$
is the angle of the bounded region at boundary vertex $j$, it follows
that $\sum_j\alpha_j=\pi F-2\pi I$. Substituting the preceding face
count yields $\sum_j\alpha_j=\pi(B-2)$.
Traverse the boundary with this disc on the left. Its principal turn
at $j$ is $\pi-\alpha_j$, including zero at a straight subdivision.
The region is an embedded disc, so $0<\alpha_j<2\pi$ and these are
the principal turns. Their sum is therefore
$\pi B-\pi(B-2)=2\pi$. Subdivision contributes zero and changes no
other turn. Lemma~\ref{lem:rot} gives rotation $1$ for the original
polygon. The opposite traversal negates every turn and gives $-1$.
This counts exterior angles directly; it makes no use of Whitney's
formula or of a bound depending on the number of polygon vertices.
\end{proof}
```

## lem:corner-values — PROVE

reference/SM/sm-3-statesum.tex:4801–4809

```tex
\begin{lemma}[elementary corner values]\label{lem:corner-values}
\begin{enumerate}
\item[(i)] If $Q$ is uniform and embedded ($m_Q=0$) then $|r_Q|=1$, $d_Q=0$
and $c(Q)=1$.
\item[(ii)] If $Q$ is uniform and $\{y\}$ is a crossing of $Q$ interlacing no
other crossing of $Q$, then $c(Q)=0$.
\end{enumerate}
\status{proved (refereed: bench A, 2026-09-05T18:22:57Z; transcribed from (i) via Lemma~\ref{cb:embedded-rotation}; (ii) CV thm:s7universal(D)(i) via Lemma~\ref{cb:singleton} (C035))}
\end{lemma}
```

reference/SM/sm-3-statesum.tex:4810–4818

```tex
\begin{proof}
(i) Lemma~\ref{cb:embedded-rotation} gives $|r_Q|=1$. Thus
$d_Q=1-0-1=0$. The actual positive diagram is crossing-free and has
polynomial $1$ by Theorem~\ref{lp:core}; its $a^0z^0$ coefficient is $1$.
(ii) The carrier $Q$ and its isolated self-crossing satisfy
Lemma~\ref{cb:singleton}, which gives the conclusion directly. The
condition is interlacement isolation; no visible planar monogon is
assumed or needed.
\end{proof}
```

## prop:C-chamber — PROVE

reference/SM/sm-4-knotlaws.tex:36–39

```tex
\begin{proposition}[chamber constancy]\label{prop:C-chamber}
The state sum $C$ of Definition~\ref{def:C} is constant on every chamber.
\status{proved (refereed: bench A, 2026-09-05T18:22:57Z; transcribed from CV prop:chamberinv, through Lemma~\ref{lem:carriers} and the named-record bridge (Lemma~\ref{rp:record-polynomial}, Theorem~\ref{lp:core}) (C020, C027); F-25-95; single convention, CV one-based tail = this document (F-25-104))}
\end{proposition}
```

reference/SM/sm-4-knotlaws.tex:40–99

```tex
\begin{proof}
First consider a continuous path of labelled generic polygons. By
Proposition~\ref{prop:chambers}, the crossing set and the order of its
visits along each directed edge are constant. Concatenating those edgewise
lists identifies the oriented cyclic traversal records, their crossing
pairings and interlacement graphs. It therefore gives a bijection of all
independent sets $S$, preserving $|S|$.

Fix one such support $S$. Include the original vertices as marked points
on the traversal circle and perform the same exchanges of outgoing
successors at its selected visits. By Lemma~\ref{lem:carriers}, with the
incoming-visit convention, this gives a fixed finite collection of oriented
carrier cycles. Corresponding original vertices and smoothing corners
have the same places on those cycles. An unselected crossing is retained
as a self-crossing of a cycle exactly when both its visits belong to that
cycle, so every carrier's retained crossing pairing and number $m_Q$ are
constant.

Each crossing point varies continuously: its two edge directions have
nonzero determinant, and solving the two-by-two intersection equations
gives continuous parameters in the relative interiors. Thus the corners
of each named carrier form a continuous ordered polygonal tuple.
Lemma~\ref{lem:carriers} puts it in the regular locus: its segments are
nonzero and no consecutive directions are antiparallel. Its signed
rotation is consequently constant by Lemma~\ref{lem:rot}(ii).
At an original corner the turn sign is the corresponding original turn;
at a smoothing corner it is the sign of the determinant of the inherited
ordered edge directions. These determinants are continuous and nonzero
along the path. All carrier corner signs, corner counts and uniformity
conditions therefore remain constant, as does the original left-turn
count $\ell(P)$.

At a retained self-crossing the two carrier directions are positive
multiples of the same ordered parent directions throughout. Their
nonzero determinant has constant sign. The physical over strand in the
positive lift therefore stays over, and the crossing sign stays positive.
Corresponding carrier lifts have a cyclic-order-, pairing-, sign- and
over/under-preserving bijection of crossing visits. The printed
scalar named-record Lemma~\ref{rp:record-polynomial}, followed by the
common substitution and Theorem~\ref{lp:core}, gives equal $H$ polynomials,
including for a carrier with no self-crossings.
Since $m_Q$ and $|\rot(Q)|$ are constant, the exponent
$d_Q=1-m_Q-|\rot(Q)|$ is constant. Hence the coefficient
$c(Q)=[a^{d_Q}z^0]H_Q^+$ is constant for every carrier, whether uniform
or mixed. Every term and the prefactor of Definition~\ref{def:C} are
now constant, proving constancy along the labelled path.

To pass to unlabelled chambers, first note that cyclically shifting the
vertex labels preserves $C$ directly from its definition. It merely
renames the same directed traversal, crossings and independent supports;
the corresponding carrier images and orientations, corner counts,
rotations, positive lifts and coefficients are unchanged. Openness of the
labelled generic locus gives each point a path-connected neighbourhood
inside it. The path argument makes $C$ locally constant there. Its
cyclic invariance makes it descend to a locally constant function on the
quotient by cyclic relabelling: the preimage of any value is an open
saturated subset, so its image is open in the quotient topology. A
locally constant function on a connected chamber is constant. This proves
the stated assertion without assuming a lift of an arbitrary quotient path.
\end{proof}
```

## prop:C-silent — PROVE

reference/SM/sm-4-knotlaws.tex:101–107

```tex
\begin{proposition}[silence]\label{prop:C-silent}
At a simple exterior-extension wall (E) or a simple pure cut (C),
\begin{equation}\label{ccf:silence}
C(P_+)=C(P_-).
\end{equation}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from exterior extension CV lem:silence; pure cut as printed (C020, C027))}
\end{proposition}
```

reference/SM/sm-4-knotlaws.tex:108–151

```tex
\begin{proof}
By Lemma~\ref{lem:wall-sides}(E),(C), the remote crossings and their
cyclic visit order agree on both sides and at the centre. Its proof also
gives the following geometric facts at the centre: vertices are distinct,
all edges and all original turns are nonzero, no vertex lies on a
nonincident closed edge, every actual crossing is transverse and interior,
and distinct crossings have distinct points. In (E) the sole vertex-line
incidence lies outside its closed base segment; in (C) its zero triple
contains no adjacent pair and hence gives no vertex-edge incidence.
Thus the same finite crossing records and independent supports are
identified through the entire small interval.

For each common support $S$, exchange the same successors to identify its
carriers. Original vertices and selected smoothing points remain distinct,
so the subsegments between successive marks have positive lengths at the
centre and on a smaller interval. At an original corner the two directed
segments are positive multiples of consecutive parent directions with
nonzero turn determinant. At a smoothing corner they are positive
multiples of the two transverse directions at its selected crossing,
again with nonzero determinant. Omitting unselected marks only joins
positive subsegments in the same direction. These observations verify
directly, including at the nongeneric parent centre, that every carrier
tuple is continuous, has nonzero segments, and has no antiparallel corner.
They do not apply a generic-polygon lemma outside its hypothesis.

It follows from Lemma~\ref{lem:rot}(ii) that each carrier's signed rotation
is the same on both sides. Every original and smoothing turn sign is
constant, and so are $\ell(P)$, uniformity and all corner counts. The
common successor cycles preserve which unselected crossing visits share
one carrier, hence all $m_Q$. At every retained crossing its direction
determinant is nonzero and continuous through zero; therefore its positive
over/under designation is also constant. Apply the scalar named-record equality of
Lemma~\ref{lc:presentations} and Theorem~\ref{lp:core} to corresponding
carrier diagrams on the two generic sides. This gives equal $H$ polynomials;
the equal $m_Q$ and $|\rot(Q)|$ give equality of their corner coefficients.
The independent supports, their uniformity, $|S|$ and the common prefactor
now identify the two sums term by term. There are finitely many supports
and carriers, so all interval shrinkings can be made simultaneously.

Only carrier geometry was used at the centre; the state sums in
\eqref{ccf:silence} are evaluated on the generic sides.
Proposition~\ref{prop:C-chamber} makes them independent of the chosen
representatives in the respective side chambers.
\end{proof}
```

## thm:C-S3 — PROVE

reference/SM/sm-4-knotlaws.tex:153–159

```tex
\begin{theorem}[flat law]\label{thm:C-S3}
At a simple flat wall at $j$, with $n\geq4$,
\begin{equation}\label{ccf:flat-law}
C(P_{\rm right})-C(P_{\rm left})=C(P(0)\setminus j).
\end{equation}
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV thm:main(A)(ii), lem:flatdata (C020, C027))}
\end{theorem}
```

reference/SM/sm-4-knotlaws.tex:160–228

```tex
\begin{proof}
We first rewrite the actual state sum using only the corner signs.
For a carrier $Q$ with $N_Q$ corners, define
\begin{equation}\label{ccf:selector}
W(Q)=
\begin{cases}
1,&\text{all its turns are right},\\
(-1)^{N_Q},&\text{all its turns are left},\\
0,&\text{its turns are mixed}.
\end{cases}
\end{equation}
If a support $S$ is uniform, the total number of left carrier corners is
$\ell(P)+|S|$: every original vertex belongs to exactly one carrier with
its original turn, and each selected crossing creates exactly one left
and one right smoothing corner, by Lemma~\ref{lem:carriers}. It follows
that the product of the selectors is $(-1)^{\ell(P)+|S|}$. If $S$ is
not uniform, at least one selector is zero. Consequently the definition
of $C$ gives, on every generic polygon,
\begin{equation}\label{ccf:selector-sum}
C(P)=\sum_{S\in\operatorname{Ind}(G_P)}
       \prod_{Q\text{ carrier of }S}W(Q)c(Q).
\end{equation}
This is an identity for the coefficients of the individual actual carrier
diagrams in Definition~\ref{def:C}; no factorization of one diagram's
polynomial into polynomials of other pieces has been used.

Put $D=P(0)\setminus j$. Lemma~\ref{lem:flat-sides} proves that $D$
is generic and identifies its crossings with those on both sides,
preserving cyclic order, pairing and positive over/under data. Hence it
identifies the three interlacement graphs and all independent supports,
including supports whose uniformity differs between the configurations.
For a fixed support, Corollary~\ref{cor:flat-carriers} gives corresponding
oriented carriers with the same retained crossing records and the same
signed rotations. Lemma~\ref{lc:presentations} and
Theorem~\ref{lp:core} therefore identify the $H$ polynomials of their
actual positive lifts. The numbers $m_Q$ and
$|\rot(Q)|$ agree, so the exponents $d_Q$ agree and each corresponding
coefficient $c(Q)$ is the same in all three configurations. This applies
also to mixed carriers and to crossing-free carriers.

Exactly one named carrier passes through the extra vertex $\mu_j$.
Call it $Q_*$ and call its corresponding deletion carrier $Q_*^D$.
All other corresponding selectors agree. The selectors of the
distinguished carrier satisfy
\begin{equation}\label{ccf:distinguished-selector}
W(Q_*^{\rm right})-W(Q_*^{\rm left})=W(Q_*^D)
\end{equation}
by Corollary~\ref{cor:flat-carriers}(iii). Explicitly, if the surviving
corners are mixed, all three entries are zero; if all are right, the
entries are $(1,0,1)$; if all $k$ surviving corners are left, the entries
are $(0,(-1)^{k+1},(-1)^k)$. In the last case the first minus the
second is $-(-1)^{k+1}=(-1)^k$. The deletion carrier has at least
three corners, so these alternatives do not involve an empty corner list.

For the fixed common support $S$, let $B_S$ be the common product of
all carrier coefficients, and let $U_S$ be the common product of all
selectors other than the distinguished one (with empty product $1$).
Its right-minus-left contribution to \eqref{ccf:selector-sum} is
\begin{equation}\label{ccf:term-difference}
B_SU_S\bigl(W(Q_*^{\rm right})-W(Q_*^{\rm left})\bigr)
=B_SU_SW(Q_*^D).
\end{equation}
The right side is exactly this support's contribution to the deletion
sum. No division by $B_S$, $U_S$ or a coefficient is performed; zeros
cause no exception. Summing over the finite common support set proves
\eqref{ccf:flat-law}. Proposition~\ref{prop:C-chamber} supplies the
well-defined side values. The only state sum on the right is that of
the generic deletion, not a value assigned to the flat centre.
\end{proof}
```

## lem:homflyrows — PROVE

reference/SM/sm-4-knotlaws.tex:230–236

```tex
\begin{lemma}[products and the two-component row]\label{lem:homflyrows}
For oriented knots $K,J$, $H_{K\#J}=H_KH_J$ and
$H_{K\sqcup J}=\frac{a-a^{-1}}zH_KH_J$. For a two-component oriented link
diagram $D=D_1\cup D_2$ with linking number $\lk$,
$[z^{-1}]H_D=(a-a^{-1})a^{-2\lk}[z^0](H_{D_1}H_{D_2})$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV lem:homflyrows via Theorems~\ref{mp:join}, \ref{mp:stack}, \ref{mp:lowest} (C028); its second sentence (the two-component row) consumes the knot clause of registry L-1 (F-25-48))}
\end{lemma}
```

reference/SM/sm-4-knotlaws.tex:237–265

```tex
\begin{proof}
Choose actual knot diagrams for $K,J$ with clean marked intervals. The
clean joining construction preceding Theorem~\ref{mp:join} gives a diagram
of their ordinary oriented connected sum. That theorem gives
$P_{K\#J}=P_KP_J$ on these actual representatives, and
Theorem~\ref{lp:core} identifies each $P$ with $H$. For split union, choose
representatives with disjoint page images. Theorem~\ref{mp:stack}, with
two one-component blocks and no mixed crossings, gives
$P_{K\sqcup J}=\delta P_KP_J$; the same identification gives the asserted
$H$ formula. Passing from these chosen representatives to the knot-class
notation uses the full global source premise explicitly retained in
Literature input~\ref{lit:homfly}; it is not a conclusion of the local
construction alone.

For the actual two-component diagram $D$, apply Theorem~\ref{mp:lowest}
with $c=2$. Its linking half-sum is computed from the original common
presentation, with the crossing signs of
Definition~\ref{def:positive-lift}, exactly the $\lk$ in the statement.
Its two intrinsic restrictions are the actual diagrams $D_1,D_2$.
Theorem~\ref{lp:core} identifies the result with
\[
[z^{-1}]H_D=(a-a^{-1})a^{-2\lk}[z^0]H_{D_1}\,[z^0]H_{D_2}.
\]
Both knot polynomials have only nonnegative even $z$ exponents by that
same theorem. Thus a product monomial has $z$ exponent zero precisely
when each factor does. It follows that the last two factors equal
$[z^0](H_{D_1}H_{D_2})$, which is the required expression. No division
by either knot polynomial or by a corner coefficient has been used.
\end{proof}
```

## thm:C-S7 — PROVE

reference/SM/sm-4-knotlaws.tex:267–275

```tex
\begin{theorem}[vertex--edge law]\label{thm:C-S7}
At a simple vertex--edge wall at $(M;a)$, of bigon or sliding type, with
halves $\lambda_1,\lambda_2$ (Definition~\ref{def:deletion-halves}) and
contact sign $s=\chi_{a,a+1,M}(P_-)$,
\[
C(P_+)-C(P_-)=s\,C(\lambda_1)\,C(\lambda_2).
\]
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z, 2026-09-06T06:11:53Z and 2026-09-06T07:18:25Z; transcribed from CV thm:s7universal(F) with its Section~6; RC d6\_vertexedge (C036))}
\end{theorem}
```

reference/SM/sm-4-knotlaws.tex:276–905

```tex
\begin{proof}
We use the actual carrier selector sum of Lemma~\ref{lem:C-X1}.
The geometric domain is exactly the simple SM vertex--edge wall in the
statement. Lemma~\ref{lem:wall-sides} supplies a clean contact disc,
stable old visits and the stated crossing changes. Lemma~\ref{lem:children}
supplies the actual generic ordered halves, each with at least three
vertices. No additional guarded-factor or parallel-direction hypothesis
is imposed.

In this proof write $\mathbf m=\mu_M$, $\mathbf a=\mu_a$ and
$\mathbf b=\mu_{a+1}$ for the positions along the germ, suppressing its parameter. Evaluations
at a specified side use that side's positions. The cyclic index $M$
in the theorem remains unchanged. A local diagram is always the actual
positive carrier diagram; its polynomial $P_A=H_A^+$ and writhe $m_A$
are those in the state sum. The blocks and their owners are those of
Definition~\ref{cb:blocks}; their products are proved in
Lemma~\ref{cb:products}. Equality of named scalar records uses
Lemma~\ref{rp:record-polynomial}, including crossing-free components.
Put $W(S)=\prod_L\operatorname{wt}(L)$ and let $\vartheta(u,v)$
denote the real principal angle from a nonzero vector $u$ to $v$.
All such local angles below are strictly between $-\pi$ and $\pi$.

\par\medskip\noindent\emph{Sliding: relocation and the exact selector difference.}\par

Put $r=\mathbf b-\mathbf a$, $u_{\rm in}=\mathbf m-\mu_{M-1}$ and
$u_{\rm out}=\mu_{M+1}-\mathbf m$ at the wall.  The two neighbours are on opposite
sides, while both tangents follow the oriented traversal through the
contact.  Therefore
\begin{equation}\label{s7c:sliding-signs}
 \sgn\det(r,u_{\rm in})=\sgn\det(r,u_{\rm out})\ne0.
\end{equation}
By continuity from the relative-interior contact, each incident line
meets the relative interior of the finite remote segment on a sufficiently
small event interval.  Exactly one incident segment reaches that line
intersection on each side; the two sides exchange which one.  Denote
the crossing on the chosen side $P_-$ by $x_-$ and its relocated mate
on $P_+$ by $x_+$.  Removing that label within the contact collar
leaves the same cyclic word.  Equation~\eqref{s7c:sliding-signs} also
fixes which visit is the remote overpass.  Thus the named map
$\varphi(x_-)=x_+$, identity on old labels, preserves cyclic order,
pairing, over/under, signs and the interlacement graph.  It transports
supports, undominated blocks, owners, actual carrier diagrams and writhes.

For a support avoiding this crossing, all successor cycles pass regularly
through the wall and all corner determinants stay nonzero.  Their
rotation integers and selectors are fixed, and so are their coefficient
reads.  This sector cancels term by term.

For a support containing $x_-$, the two visits cut the traversal into
the two half intervals.  Every other selected chord is internal to one
interval, by independence.  Conversely any two half supports together
with $x_-$ form a support.  This gives a bijection with explicit inverse
\begin{equation}\label{s7c:sliding-bijection}
 \{S\in\Ind(G_{P_-}):x_-\in S\}\longleftrightarrow
 \Ind(G_{\lambda_1})\times\Ind(G_{\lambda_2}),
 \quad S\longmapsto(S_1,S_2).
\end{equation}
Smoothing $x_-$ closes the two intervals separately.  All subsequent
selected smoothings are internal, and labels interlacing $x_-$ are
dominated.  Consequently
\begin{equation}\label{s7c:sliding-residual}
 G_{P_-}[U(S)]
 =G_{\lambda_1}[U(S_1)]\sqcup G_{\lambda_2}[U(S_2)].
\end{equation}
The named maps identify every residual diagram and every owner.  The
only changed direction list, on the carrier containing the short edge,
is one of
\begin{equation}\label{s7c:short-direction-lists}
 (r,u_{\rm in},u_{\rm out})\longrightarrow(r,u_{\rm out}),
 \qquad
 (u_{\rm in},u_{\rm out},r)\longrightarrow(u_{\rm in},r).
\end{equation}
The two incident tangents lie in one open angular half-plane bounded by
$r$.  Thus their principal turns satisfy the real equalities
\begin{align}
 \vartheta(r,u_{\rm in})+\vartheta(u_{\rm in},u_{\rm out})
       &=\vartheta(r,u_{\rm out}),\label{s7c:turn-short-a}\\
 \vartheta(u_{\rm in},u_{\rm out})+\vartheta(u_{\rm out},r)
       &=\vartheta(u_{\rm in},r).\label{s7c:turn-short-b}
\end{align}
There is no hidden multiple of $2\pi$.  The chamber and half carriers
have equal signed, and hence absolute, rotations.  Writing $C_\pm(S)$
for the complete coefficient product on the two sides, and $C_i(S_i)$
for its half versions, we get
\begin{equation}\label{s7c:sliding-coefficients}
 C_-(S)=C_+(\varphi S)=C_1(S_1)C_2(S_2).
\end{equation}

The half contact signs
$\eta_1=\sgn\det(r,u_{\rm out})$ and
$\eta_2=\sgn\det(u_{\rm in},r)$ are opposite.  In $P_-$ the
short-edge refinement is on the half with contact sign $s$, and in $P_+$
on the one with sign $-s$.  Let $h_\eta$ be that half-carrier weight,
$c_\eta$ its refined weight, and
$\tau=\sgn\det(u_{\rm in},u_{\rm out})$.  The refinement adds
the turn $\tau$, so the full selector table is
\begin{equation}\label{s7c:short-selector}
 c_\eta=\begin{cases}
 -\eta h_\eta,&\tau=\eta,\\
 0,&\tau=-\eta.
 \end{cases}
\end{equation}
Indeed a mixed original carrier stays mixed; if $\tau$ disagrees with
its contact sign it has both signs; if all signs are right the extra
right corner preserves weight $1$; and if all are left the extra left
corner reverses $(-1)^{\#\text{corners}}$.  These are all cases.
Let $Q_{\rm sp}$ be the product of the other carrier weights, without
assuming it nonzero.  For the row in \eqref{s7c:sliding-bijection},
\begin{equation}\label{s7c:sliding-selector-factors}
 W_1W_2=Q_{\rm sp}h_s h_{-s},\quad
 W_-=Q_{\rm sp}c_s h_{-s},\quad
 W_+=Q_{\rm sp}h_s c_{-s}.
\end{equation}
If $\tau=s$, then $c_s=-s h_s$ and $c_{-s}=0$; if $\tau=-s$,
then $c_s=0$ and $c_{-s}=s h_{-s}$.  Either way
\begin{equation}\label{s7c:sliding-selector-difference}
 W_+-W_-=sW_1W_2.
\end{equation}
Multiply by \eqref{s7c:sliding-coefficients} and sum over the finite
bijection.  Distributivity proves the stated product law for sliding,
with no spectator cancellation.

\par\medskip\noindent\emph{Bigon words and the two-newborn sector.}\par

Let $P_0$ be the side where $M$ and its two neighbours lie on the same
side of the remote line, and $P_2$ the other side, with two newborn
crossings $x,y$.  Set
\begin{equation}\label{s7c:bigon-signs}
 s_0=\sgn\det(r,\mathbf m-\mathbf a)\big|_{P_0},\qquad
 \delta_{\rm dir}=\begin{cases}+1&P_- =P_0,\\-1&P_-=P_2.
 \end{cases}
 \qquad s=\delta_{\rm dir}s_0.
\end{equation}
Write $\epsilon=1$ when the newborn chords interlace and $0$ otherwise.
Starting at the first visit of $x$, the two complete local words are
\begin{equation}\label{s7c:bigon-words-eq}
 \begin{array}{c|l}
 \epsilon=0&x_0y_0\,A\,y_1x_1\,B\\
 \epsilon=1&x_0y_0\,A\,x_1y_1\,B\\
 P_0&A\,B.
 \end{array}
\end{equation}
Each old label is internal to $A$, internal to $B$, or has one visit in
each.  The last set $N$ is the common old neighbourhood of $x,y$.
An old support $T$ is called eligible when $T\cap N=\varnothing$.
If $T$ meets $N$, both newborns are dominated and neither extension
by a newborn is a support.  Deleting their four visits identifies the
complete smoothing successor, owners, corners, rotations, carrier
diagrams and coefficient reads.  The entire ineligible returned sector
is therefore zero.

For eligible $T$, restriction to the intervals gives the bijection
\begin{equation}\label{s7c:eligible-bijection}
 T\longleftrightarrow(T_1,T_2)\in
 \Ind(G_{\lambda_1})\times\Ind(G_{\lambda_2}).
\end{equation}
Internal labels in the two intervals have disjoint induced graphs;
the halves close just these intervals.  Conversely the union of two
half supports is independent and misses $N$, proving the inverse.

If $\epsilon=0$, $T\cup\{x,y\}$ is a support.  Smoothing its four
newborn visits makes one local three-corner contact triangle and otherwise
exactly the successors of $T_1,T_2$.  Mixed old labels are dominated;
each unmixed residual label, owner and decorated diagram matches its half.
For $s_0=+1$ the triangle has three right turns; for $s_0=-1$ it has
three left turns.  Its complete data are
\begin{equation}\label{s7c:triangle-data}
 \rot=-s_0,\quad R=1,\quad P=1,\quad w=0,\quad
 [a^0z^0]1=1,\quad\operatorname{wt}=s_0.
\end{equation}
Every two-newborn support arises this way.  Put
$J=sC(\lambda_1)C(\lambda_2)$.  Finite distributivity and
\eqref{s7c:bigon-signs} show that the directed two-newborn sector is
$J$ when $\epsilon=0$.  When $\epsilon=1$ it is empty.  Hence, in
both branches,
\begin{equation}\label{s7c:sector-split}
 B=(1-\epsilon)J.
\end{equation}
It remains to show that the directed sum $R_{\rm ret}$ of all other
noncancelling rows equals $\epsilon J$.

\par\medskip\noindent\emph{Contact owners and one coambient smoothing diagram.}\par

Fix an eligible newborn-free support $T$.  Smooth its selected chords
inside $A$.  Choosing an innermost chord closes its inner subarc and
splices it out of the remaining boundary strand.  Induction leaves one
open boundary successor and internal cycles.  The same holds in $B$.
The two open boundary successors and contact stretches form one full
contact carrier $L^*$; closing them at the cut gives ordered half contact
carriers $L_1,L_2$.  All internal cycles are spectators.

For $i=1,2$, put $G_i=G_{\lambda_i}$ and
$U_i=V(G_i)\setminus(T_i\cup N_{G_i}(T_i))$.  Define the
owner-restricted sets
\begin{equation}\label{s7c:owner-restriction}
 O_i=\{c\in U_i:\text{the half owner of }c\text{ is }L_i\}.
\end{equation}
For an internal label, the successor correspondence gives full owner
$L^*$ if and only if its half owner is $L_i$.  Every surviving mixed
old label belongs to
$M_T=N\setminus N_{G_{P_2}}(T)$ and has owner $L^*$.
Thus the full high contact residual set is precisely
\begin{equation}\label{s7c:full-contact-set}
 O_1\sqcup O_2\sqcup M_T\sqcup\{x,y\}.
\end{equation}
The labels $U_i\setminus O_i$ are on spectator carriers and are never
inserted into a contact polynomial.

Let $L_L,D_L$ be the low full contact carrier and its actual positive carrier
diagram, and $L_H,D_H$ its high counterpart.  For this newborn-free support every selected crossing persists away
from the contact disc. Its successor carrier through the contact follows
the two original incident segments through $M$ on both sides. The edge
pieces have positive lengths at the centre, and all its corner turns
have nonzero determinants there. Thus this carrier is a continuous
regular family, including at the wall. Lemma~\ref{lem:rot}(ii) makes
its rotation locally constant. Consequently
\begin{equation}\label{s7c:full-rotation}
 \rot(L_L)=\rot(L_H)=\rot(L^*).
\end{equation}
The positive crossing $q=x$ of $D_H$ has oriented smoothing equal to
one actual ordered two-component diagram $D_A$.  Component 1 contains
the $A$-boundary successor and corresponds to $L_1$; component 2
contains the $B$-boundary successor and corresponds to $L_2$.
Retain every mixed crossing of this one ambient diagram.

If $\epsilon=1$ define $D_A^{\rm post}=D_A$.  If $\epsilon=0$,
component 1 contains the permitted positive self R-I curl $y$; delete
exactly that curl, retaining the two ordered tags and every mixed crossing,
to define $D_A^{\rm post}$.  Set
\begin{equation}\label{s7c:component-data}
 D_i=\operatorname{component}_i(D_A^{\rm post}),\quad
 Q_i=P_{D_i},\quad w_i=w(D_i),\qquad i=1,2.
\end{equation}
The successor words identify these as the actual carrier diagrams of
the ordered half contact carriers; their scalar identification is
Lemma~\ref{rp:record-polynomial}. The R-I deletion is in the supplied
clean curl disc. The local LM R-I equality applies to the entire
two-component diagram and to its component-1 restriction; component 2
is unchanged. It retains both component tags and every mixed crossing,
so the coambient mixed signed sum and hence linking number are unchanged.  Calling the latter $\ell$,
the full self/mixed crossing partition is
\begin{equation}\label{s7c:crossing-partition}
 \begin{array}{c|l}
 \text{component 1 self crossings}&O_1\cup(\{y\}\text{ if }\epsilon=0)\\
 \text{component 2 self crossings}&O_2\\
 \text{mixed crossings}&M_T\cup(\{y\}\text{ if }\epsilon=1).
 \end{array}
\end{equation}
In particular
\begin{align}
 P_{\operatorname{component}_i(D_A)}&=Q_i,\label{s7c:component-polynomial}\\
 \operatorname{lk}(D_A)&=\operatorname{lk}(D_A^{\rm post})=\ell,
 \label{s7c:ambient-linking}\\
 w(\operatorname{component}_1(D_A))&=w_1+1-\epsilon,
 \qquad w(\operatorname{component}_2(D_A))=w_2.
 \label{s7c:pre-curl-writhe}
\end{align}
Here $\operatorname{lk}(D_A)$ means the linking of its named ordered
components, not linking assigned to two separately embedded restrictions.

\par\medskip\noindent\emph{Turn and selector bookkeeping.}\par

Send $r$ to the positive horizontal ray.  If necessary reflect the
picture to place both neighbour vectors above it, with arguments
$\alpha,\beta\in(0,\pi)$.  Direct line intersection gives
\begin{equation}\label{s7c:angle-orders}
 \epsilon=0\ \Longleftrightarrow\ \alpha<\beta,
 \qquad
 \epsilon=1\ \Longleftrightarrow\ \beta<\alpha.
\end{equation}
The half contact turns are $\beta$ and $\pi-\alpha$; the full
contact turn is $\beta-\alpha-\pi$ in the noninterlacing case and
$\beta-\alpha+\pi$ in the interlacing case.  Both half signs are
$s_0$; the full sign is $-s_0$ or $s_0$, respectively.  Reflection
reverses all signs together and transports these statements back.
All noncontact turns partition between the halves.  If $Q_{\rm sp}$
is the common product of internal spectator selectors, the actual factors
are
\begin{equation}\label{s7c:selector-owners}
 W_T=Q_{\rm sp}\operatorname{wt}(L^*),\qquad
 W_1W_2=Q_{\rm sp}\operatorname{wt}(L_1)\operatorname{wt}(L_2).
\end{equation}
No factor is cancelled in these identities.

For interlacing the contact signs agree.  If any noncontact sign disagrees,
both the full weight and the relevant half product are zero.  Otherwise
all three carriers are uniform with the same sign.  For right turns each
weight is $1$ and $s_0=-1$; for left turns the full corner count is the
sum of the half counts minus one, giving a relative minus sign and
$s_0=+1$.  Thus, including all zero cases,
\begin{equation}\label{s7c:interlacing-selector}
 \operatorname{wt}(L^*)=-s_0\operatorname{wt}(L_1)
                       \operatorname{wt}(L_2),\qquad
 W_T=-s_0 W_1W_2.
\end{equation}
If $W_T\ne0$, \eqref{s7c:selector-owners} also shows that the spectator
product and all three contact weights are nonzero, so the just-described
uniform same-sign case applies.  Multiplication by a possibly zero
$Q_{\rm sp}$ proves the second identity without division.

For noninterlacing, a uniform full carrier gives each half one opposite
contact turn, while two uniform halves give the full carrier one opposite
turn.  Thus at least one of their selectors is zero:
\begin{equation}\label{s7c:noninterlacing-selector}
 W_T W_1W_2=0.
\end{equation}
Every carrier used here has at least three corners.  Two polygon corners
would force overlapping straight segments, a polygon and smoothing corner
would force vertex--edge incidence, and two smoothing corners would
contradict transversality of the crossing straight branches.  A one-corner
closed straight path is likewise impossible.  This also applies to the
daughter carriers used below.

Subtract the explicit full contact turn from the sum of the two half
turns, and add the unchanged noncontact turns.  Dividing by $2\pi$ gives
the signed identity
\begin{equation}\label{s7c:rotation-ledger}
 \rot(L_1)+\rot(L_2)-\rot(L^*)
 =\begin{cases}0&\epsilon=1,\\s_0&\epsilon=0.
 \end{cases}
\end{equation}
The second line contains a full-turn correction; unsigned angles would
not give this formula.

\par\medskip\noindent\emph{Universal skein extraction and the interlacing branch.}\par

For the fixed eligible row bind all polynomial and exponent objects:
\begin{align}
 F_L&=P_{D_L},&F_H&=P_{D_H},&F_A&=P_{D_A},\label{s7c:polynomial-binders}\\
 f_L&=[z^0]F_L,&f_H&=[z^0]F_H,&f_i&=[z^0]Q_i,\label{s7c:row-binders}\\
 w_L&=w(D_L),&w_H&=w(D_H),&R_i&=|\rot(L_i)|,\label{s7c:writhe-binders}\\
 R_L&=|\rot(L_L)|,&R_H&=|\rot(L_H)|,&&\label{s7c:rotation-binders}\\
 k_L&=1-w_L-R_L,&k_H&=1-w_H-R_H,&k_i&=1-w_i-R_i,\label{s7c:slot-binders}\\
 \Omega_L&=[a^{k_L}z^0]F_L,&\Omega_H&=[a^{k_H}z^0]F_H,
 &\omega_i&=[a^{k_i}]f_i,\label{s7c:coefficient-binders}\\
 K&=k_1+k_2.&&&&\label{s7c:product-slot}
\end{align}
These coefficient maps are total even when any Laurent polynomial is zero.
The two incident directions in this bigon branch have opposite
determinant signs against the remote direction. Their positive
decorations therefore put the remote strand over at exactly one
newborn crossing. Switching the positive contact crossing $q$ makes
the same strand over at both crossings, with opposite crossing signs.
The isolated contact disc contains no other strand; this is the actual
ordinary R-II template, not merely an opposite-sign pair. Delete it
using local LM invariance. The remaining diagram has the same complete
decorated record as $D_L$, including every old retained crossing;
Lemma~\ref{rp:record-polynomial} gives its value $F_L$. The actual
oriented smoothing is the tagged $D_A$. Thus the skein relation at $q$
first gives $aF_H-a^{-1}F_L=zF_A$, then
\begin{equation}\label{s7c:universal-skein}
 F_H=a^{-2}F_L+a^{-1}zF_A.
\end{equation}
The high writhe is $w_H=w_L+2$ and
\eqref{s7c:full-rotation} gives $R_H=R_L$, hence
$k_H=k_L-2$.  Extracting $[a^{k_L-2}z^0]$ in
\eqref{s7c:universal-skein} gives
$\Omega_H=\Omega_L+[a^{k_L-1}z^{-1}]F_A$.
Therefore
\begin{equation}\label{s7c:universal-extraction}
 \Omega_H-\Omega_L=[a^{k_L-1}z^{-1}]F_A.
\end{equation}
No selector or degree hypothesis is needed for this equality.

Assume first $\epsilon=1$.  The crossing partition
\eqref{s7c:crossing-partition} puts $y$ and all retained old mixed
crossings between the two components of $D_A$; none belongs to $Q_i$
or $w_i$.  Lemma~\ref{lem:homflyrows} and the writhe count yield
\begin{equation}\label{s7c:interlacing-writhe-row}
 [z^{-1}]F_A=a^{-2\ell}(a-a^{-1})f_1f_2,
 \qquad w_L=w_1+w_2+2\ell-1.
\end{equation}
The second equality follows also by counting $w_H$: the self crossings
contribute $w_1+w_2$, the mixed crossings of $D_A$ contribute $2\ell$,
and the smoothed crossing $q$ contributes one; subtract the two newborn
crossings to pass from high to low.

Let $U_{\rm sp}$ be the product of all spectator coefficient reads for
this newborn-free row.  Before using absolute-rotation or degree identities
tied to this row, test $W_T$ and $U_{\rm sp}$.  If $W_T=0$, the two
full terms vanish and \eqref{s7c:interlacing-selector} makes the half
selector product zero.  If $U_{\rm sp}=0$, both full terms and the
half product contain that same spectator zero.  Either case is finished.
Assume now $W_TU_{\rm sp}\ne0$.  The uniform same-sign implication
proved in the turn calculation above and
\eqref{s7c:rotation-ledger} imply
\begin{equation}\label{s7c:interlacing-absolute}
 R_L=R_1+R_2.
\end{equation}
Substitution of \eqref{s7c:interlacing-writhe-row} into the definition
of $k_L$, followed by \eqref{s7c:interlacing-absolute}, gives
\begin{align}
 k_L&=1-(w_1+w_2+2\ell-1)-(R_1+R_2)\notag\\
    &=(1-w_1-R_1)+(1-w_2-R_2)-2\ell
      =K-2\ell.\label{s7c:interlacing-slot}
\end{align}
In \eqref{s7c:universal-extraction}, the $a^{1-2\ell}$ term of
the mixed row requests degree $k_L+2\ell-2=K-2$ in $f_1f_2$;
its $-a^{-1-2\ell}$ term requests degree $k_L+2\ell=K$.
Consequently
\begin{equation}\label{s7c:interlacing-extraction}
 \Omega_H-\Omega_L=[a^{K-2}](f_1f_2)-[a^K](f_1f_2).
\end{equation}
If either $f_i=0$, both reads and $\omega_1\omega_2$ are zero;
no minimum degree is assigned.  Otherwise both half contact carriers
are uniform, and each is a subpolygon of a decomposition of its generic
half $\lambda_i$ (Lemma~\ref{lem:children}(ii), Lemma~\ref{lem:carriers}(i);
the hypothesis discharge below), the domain of Theorem~\ref{thm:floor},
which gives $\mindeg_a f_i\ge k_i$.
In the Laurent integral domain the product has degree at least
$k_1+k_2=K$.  Its degree $K-2$ coefficient is zero.  In the degree
$K$ convolution any nonzero pair has exponents at least $k_1,k_2$,
so the only possible pair is exactly $(k_1,k_2)$.  Thus
\begin{equation}\label{s7c:interlacing-coefficient-result}
 \Omega_H-\Omega_L=-\omega_1\omega_2.
\end{equation}

Both one-newborn sectors vanish by their selectors.  To check this
directly, take $\mathbf m=(0,0)$, $r=(1,0)$ on the line $y=c>0$, and
neighbour vectors $(u,h),(v,k)$ with $h,k>c$.  Interlacing means
$hv-uk>0$.  The corner determinants are
\begin{equation}\label{s7c:one-newborn-turns}
 \det((-u,-h),(v,k))=hv-uk>0,\quad
 \det(r,(-u,-h))=-h<0,\quad
 \det((v,k),r)=-k<0.
\end{equation}
The first turn is at $M$; the second or third is the smoothing turn
when $x$ or $y$ is selected.  Eligibility leaves the intervening collar
free of selected visits, so the opposite turns lie on the same daughter
carrier and make it mixed.  Reflection reverses all three signs and
proves the other orientation as well.

Let $\operatorname{Term}_H(T),\operatorname{Term}_L(T)$ denote complete
newborn-free support contributions, before multiplying by
$\delta_{\rm dir}$.  In the nonzero branch
\eqref{s7c:interlacing-coefficient-result} gives
\begin{equation}\label{s7c:interlacing-term}
 \operatorname{Term}_H(T)-\operatorname{Term}_L(T)
 =-W_TU_{\rm sp}\omega_1\omega_2.
\end{equation}
The same equation holds in the already discharged zero-factor branches,
with both sides zero.  Substitute $W_T=-s_0W_1W_2$, multiply by
$\delta_{\rm dir}$, and use $s=\delta_{\rm dir}s_0$.
The directed returned share is
$sW_1W_2U_{\rm sp}\omega_1\omega_2$.  The owner-restricted
decomposition puts each internal spectator into this half product
exactly once.  Summing over \eqref{s7c:eligible-bijection} gives
\begin{equation}\label{s7c:interlacing-return}
 R_{\rm ret}=sC(\lambda_1)C(\lambda_2)=J.
\end{equation}
This proves the required returned-sector identity for $\epsilon=1$.

\par\medskip\noindent\emph{Noninterlacing: full-twist, singleton and separate-block rows.}\par

Now $\epsilon=0$.  The two-newborn sector already equals $J$ by
\eqref{s7c:sector-split}; we show every remaining returned row is zero.

\par\noindent\emph{The same-block alternative.}\par
In $D_A$ the remaining newborn $y$ is a positive self curl on
component 1.  Its deletion gives the exact $Q_1,Q_2$ of
\eqref{s7c:component-data}, not polynomials with spectator factors
inserted.  Counting self and mixed crossings gives
\begin{equation}\label{s7c:noninterlacing-writhe}
 w_L=w_1+w_2+2\ell.
\end{equation}
Indeed $w_H$ includes the additional $q$ and the self curl $y$, for
a total of $w_1+w_2+2\ell+2$.
If the full selector or an actual spectator multiplier is zero, both
newborn-free terms vanish and the row stops before absolute-rotation
identities.  Otherwise the full carrier is uniform with sign
$\tau=-s_0$.  Every half inherits its old turns and has exactly one
new contact turn of sign $s_0$, hence exactly one dissent.  The
at-least-three-corner observation ensures inherited turns exist.
Lemma~\ref{lem:uniformrot}, reversing all orientations when
$\tau=-1$, puts the full and both half rotations on the $\tau$ ray.
Multiplying \eqref{s7c:rotation-ledger} by $\tau$ yields
\begin{equation}\label{s7c:noninterlacing-rotation}
 R_1+R_2-R_L=\tau s_0=-1.
\end{equation}
Let $\Delta_R=R_1+R_2-R_L$.  The slot definitions give separately
\begin{align}
 K-k_L
 &=2-w_1-w_2-R_1-R_2-(1-w_L-R_L)\notag\\
 &=1+2\ell-\Delta_R=2\ell+2.
 \label{s7c:noninterlacing-slot}
\end{align}
Combining the universal extraction \eqref{s7c:universal-extraction}
with the same two-component row of Lemma~\ref{lem:homflyrows}, its two requested degrees
are now $k_L+2\ell-2=K-4$ and $k_L+2\ell=K-2$.
Therefore
\begin{equation}\label{s7c:noninterlacing-extraction}
 \Omega_H-\Omega_L=[a^{K-4}](f_1f_2)-[a^{K-2}](f_1f_2).
\end{equation}
If either Laurent row $f_i$ is zero, both reads are zero immediately.
Otherwise apply Theorem~\ref{thm:floor} to the two one-dissent half
contact carriers, subpolygons of a decomposition of the generic side
(Lemma~\ref{lem:carriers}(i); the hypothesis discharge below); it puts
their nonzero product row at degree at least $K$.
Both displayed coefficients are below this floor.  Thus the returned
newborn-free row is zero.  The auxiliary half selectors may themselves
be zero: they are not multipliers of this full term, and the floor
requires their one-dissent turn patterns, not uniform selectors.



For eligible $T$ in the noninterlacing branch, $T\cup\{x\}$ is a
support since $x$ is adjacent to neither $T$ nor $y$.  Every old
neighbour of $y$ is also a neighbour of selected $x$, and hence is
dominated.  Thus $\{y\}$ is an isolated block; the
statement with $x,y$ exchanged is identical.  If a one-newborn
selector is zero its term vanishes.  Otherwise its owner is uniform,
and Lemma~\ref{cb:singleton} makes the required coefficient zero,
including the zero-polynomial case.  Every one-newborn term is zero.

\par\noindent\emph{The different-block alternative.}\par
If $x,y$ lie in different blocks of the newborn-free
high row, both components must be singletons.  Otherwise an undominated
old common neighbour gives a path of length two joining them; the
common-neighbour property follows directly from
\eqref{s7c:bigon-words-eq}.  Each singleton has polynomial $1$ and
writhe $1$.  Every other high block is old and is matched to
its low block by erasing the finger.  For $S=T\cup\{x,y\}$,
\begin{equation}\label{s7c:different-residual}
 U(S)=U(T)\setminus\{x,y\}.
\end{equation}
The triangle and half-factorization construction in
the two-newborn calculation above now distributes every old contact block
once, with its actual owner, between $L_1,L_2$.  It follows that
\begin{equation}\label{s7c:different-polynomials}
 f_H=f_L=f_1f_2,\qquad
 w_H=w_1+w_2+2,\qquad w_L=w_1+w_2.
\end{equation}
If the common full selector or a spectator multiplier is zero, both
newborn-free terms vanish before the row-tied absolute rotations are
used.  Otherwise the same noninterlacing turn computation gives
\eqref{s7c:noninterlacing-rotation}.  Thus
\begin{align}
 k_L
 &=1-(w_1+w_2)-R_L\notag\\
 &=K-1+(R_1+R_2-R_L)=K-2,\label{s7c:different-low-slot}\\
 k_H&=k_L-2=K-4.\label{s7c:different-high-slot}
\end{align}
If $f_1=0$ or $f_2=0$, \eqref{s7c:different-polynomials} makes both
full rows zero without a degree argument.  Otherwise the actual
one-dissent half floors give product degree at least $K$.  Both slots
$K-2,K-4$ are below it, so both reads vanish separately.  The
one-newborn rows already vanished by Lemma~\ref{cb:singleton}.
The same-block and different-block alternatives exhaust the residual
components containing the newborns.  Therefore
\begin{equation}\label{s7c:noninterlacing-return}
 R_{\rm ret}=0\qquad(\epsilon=0).
\end{equation}

\par\medskip\noindent\emph{Complete hypothesis discharge and assembly.}\par

Every floor polynomial above is that of an actual positive carrier
one-circle diagram supplied by Lemma~\ref{lem:carriers} and
Lemma~\ref{cb:products}, and every carrier to which
Theorem~\ref{thm:floor} is applied is a subpolygon of a decomposition of
a generic polygon (Lemma~\ref{lem:carriers}(i)), the theorem's domain.
For the two half contact carriers that polygon is the generic half
(Lemma~\ref{lem:children}(ii)), at either value of $\epsilon$: the
traversal circle of $\lambda_1$, respectively $\lambda_2$, is the interval
$A$, respectively $B$, closed at the cut $\mathbf m=\mu_M$
(Definition~\ref{def:deletion-halves}: $\lambda_1$ follows
$E_M,\ldots,E_{a-1}$ and closes with $[\mu_a,\mu_M]\subset E_a$;
$\lambda_2$ opens with $[\mu_M,\mu_b]\subset E_a$, follows
$E_b,\ldots,E_{M-2}$ and closes with $E_{M-1}$); $T_i$ is a support of
$\lambda_i$ all of whose selected visits are internal to that interval
(the bijection \eqref{s7c:eligible-bijection}); the oriented
reconnections of Definition~\ref{def:smoothing} at those visits act
inside the interval and leave the cut untouched, so closing the interval
at the cut closes the boundary successor of $T$ into the carrier of the
decomposition $T_i$ of $\lambda_i$ through the corner $\mathbf m$ ---
which is how $L_i$ was formed --- with the internal cycles as the other
carriers of $T_i$ (Lemma~\ref{lem:carriers}(i)); and the self-crossings
of $L_i$ are the owner-restricted set $O_i$ of
\eqref{s7c:owner-restriction} (Lemma~\ref{lem:carriers}(iii)).  When
$\epsilon=1$ the enlarged supports $T\cup\{x\}$, $T\cup\{y\}$ and
$T\cup\{x,y\}$ of the generic side do not take the place of this
discharge: $T\cup\{x,y\}$ is not a support, the newborn chords
interlacing, and the daughter of $T\cup\{x\}$ or of $T\cup\{y\}$ that
carries the turn at $\mathbf m$ also carries the opposite smoothing turn
of \eqref{s7c:one-newborn-turns} and is mixed, while a live half contact
carrier is uniform.  In the noninterlacing case the two half contact
carriers are the carriers of the newborn-free support $T$ enlarged by
the smoothed newborns --- of $T\cup\{x,y\}$ when
$\epsilon=0$, when the third carrier is the crossing-free local contact
triangle and the deletion of the curl $y$ from component~1 of $D_A$ is that
smoothing with the triangle discarded --- which is what the closure at the
cut and the successor words of \eqref{s7c:component-data} record; the
daughters of a singleton row are the carriers of the support enlarged by
the singleton (Lemma~\ref{cb:singleton}); and a crossing-free carrier is a
carrier of its own row's decomposition.  The construction in Theorem~\ref{thm:floor} supplies
the needed clean rounding and curl discs; no separate arc-contraction
or arbitrary-front lift is presumed.  Its turn hypotheses are exhausted
as follows: live interlacing rows have two uniform half contact carriers;
live noninterlacing rows have two one-dissent half contact carriers;
singleton rows have a uniform and a one-dissent daughter; and a
crossing-free carrier uses its separately proved $P=1,w=0$ branch.

A zero selector or spectator which actually multiplies the current full
or target term stops that row before a row-dependent absolute-rotation
or degree identity.  A zero Laurent row is checked before every
minimum-degree or coefficient-floor argument.  Independently valid
geometric rotation identities do not require nonzero polynomials,
and coefficient extraction itself is always total.  In particular an
auxiliary one-dissent half or daughter can have zero canonical selector:
it is not a multiplier in the current row, and its actual turn pattern
is precisely a permitted floor hypothesis.  No spectator, selector,
polynomial or coefficient has been divided out anywhere in the proof.

For a bigon, \eqref{s7c:sector-split},
\eqref{s7c:interlacing-return} and \eqref{s7c:noninterlacing-return}
give, with all factors already bound,
\begin{equation}\label{s7c:bigon-total}
 B+R_{\rm ret}=(1-\epsilon)J+\epsilon J
             =sC(\lambda_1)C(\lambda_2).
\end{equation}
The sliding calculation above gives the same result for sliding.
The nonzero neighbour-side signs are either equal or opposite; these
alternatives are exclusive and exhaustive.  Hence
the vertex--edge law holds on its full stated domain.
The three positions of every old label---internal to $A$, internal to
$B$, or mixed---retain all exterior crossing and threading data.
All support bijections have the explicit inverse union operation, and
every actual spectator occurs once.  There is no restriction to an
unthreaded drawing or to a preferred choice of the initial side.

\end{proof}
```

## thm:C-S5 — PROVE

reference/SM/sm-4-knotlaws.tex:910–913

```tex
\begin{theorem}[empty-cusp zero]\label{thm:C-S5}
At a simple empty cusp, $C(P_{\rm no})=0$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV thm:zeroanchor(S5) (P-25-2, C006))}
\end{theorem}
```

reference/SM/sm-4-knotlaws.tex:914–982

```tex
\begin{proof}
Let the cusp be at vertex $j$ of an $n$-gon, $n\geq4$, with tail-labelled
edges $E_i=[\mu_i,\mu_{i+1}]$. Choose a generic polygon $P$ sufficiently
near the wall on its no-loop side. In cusp case A, where
$\mu_{j+1}(0)$ lies strictly between $\mu_{j-1}(0)$ and $\mu_j(0)$,
put $(c_1,c_2)=(j,j+1)$. In case B, where $\mu_{j-1}(0)$ lies strictly
between $\mu_j(0)$ and $\mu_{j+1}(0)$, put $(c_1,c_2)=(j-1,j)$.
In both cases the corners $c_1,c_2$ are consecutive, with intervening
edge $E_{c_1}$.

By Lemma~\ref{lem:cusp-sides}(ii), their turns on $P$ satisfy
\begin{equation}\label{s5pr:opposed-turns}
\tau_{c_1}(P)=-\tau_{c_2}(P),\qquad
\tau_{c_1}(P),\tau_{c_2}(P)\in\{-1,1\}.
\end{equation}
The cusp is empty, meaning that the two newborn crossing visits on the
loop side are cyclically adjacent. Lemma~\ref{lem:cusp-sides}(iii)
therefore gives that $E_{c_1}$ has no crossing on $P$. This conclusion
uses the lemma's specified-short-arc argument; adjacency alone is not
silently assigned to one of the two complementary traversal arcs.

Fix any decomposition $S\in\operatorname{Ind}(G_P)$.
In the traversal circle, take the closed directed arc from the visit
of $\mu_{c_1}$ to the next vertex visit $\mu_{c_2}$, tracing the single
edge $E_{c_1}$. Its interior has no crossing visit, by the preceding
paragraph. Its endpoints are not crossing visits either: a generic
polygon has distinct vertices and no vertex on a nonincident edge.
Consequently this arc contains no visit of a selected crossing of $S$.

Oriented smoothing changes the traversal only at selected crossing
visits (Definition~\ref{def:smoothing}). Every directed segment of the
chosen arc, including its passages into the two vertex visits, is
therefore retained with the same direction. More explicitly, subdivide
the traversal circle at all polygon-vertex visits and all selected
crossing visits. At a selected pair smoothing interchanges the two
outgoing continuations; it leaves every other local continuation
unchanged. The arc joining $c_1$ to $c_2$ has no selected subdivision
point, so it remains a directed path in the reconnected graph. Each
vertex of that graph has one incoming and one outgoing edge, hence the
graph is a disjoint union of directed cycles. The path lies on one
such cycle. Thus both original vertices belong to the same subpolygon,
say $Q$, of the decomposition $S$.

At each of these original vertices, smoothing has changed neither of
the two incident edge directions. Both remain actual corners of $Q$,
since their original turn signs in~\eqref{s5pr:opposed-turns} are nonzero.
Their turns on $Q$ are the same as on $P$, so one is left and the other
right. Therefore $Q$ is mixed, and $S$ is not uniform
(Definition~\ref{def:uniform}). This argument also covers
$S=\varnothing$, when the one subpolygon is $P$ itself.

Since $S$ was arbitrary, no decomposition of $P$ is uniform. The sum
defining $C$ in Definition~\ref{def:C} has an empty index set, so
\begin{equation}\label{s5pr:empty-sum}
C(P)=(-1)^{\ell(P)}
\sum_{\substack{S\in\operatorname{Ind}(G_P)\\S\text{ uniform}}}
(-1)^{|S|}\prod_{Q'\text{ subpolygon of }S}c(Q')=0.
\end{equation}
No corner coefficient has been evaluated or divided out.

Finally, opposite turns at these consecutive vertices and absence of
crossings on their connecting edge depend only on the turn word and
the crossing set. Those data are constant on each labelled chamber
(Proposition~\ref{prop:chambers}). Hence the same argument applies to
every polygon in that labelled no-loop chamber. The existence of the
pair and the argument are preserved by cyclic relabelling, so they
also apply to its polygon chamber. This proves $C(P_{\rm no})=0$
without needing a separate polynomial-invariance argument.
\end{proof}
```

## thm:C-soft — PROVE

reference/SM/sm-4-knotlaws.tex:984–992

```tex
\begin{theorem}[soft theorem for $C$]\label{thm:C-soft}
Let $P$ be generic, $j$ a vertex, $q$ admissible, and $P_\varepsilon$ the
soft insertion of Definition~\ref{def:soft}, with attachment signs
$\chi_\pm$. Then for all sufficiently small $\varepsilon>0$
\[
C(P_\varepsilon)=\frac{\chi_-+\chi_+}{2}\,C(P).
\]
\status{new (round~4: the proof consumes the exported geometry of Lemma~\ref{lem:soft-generic}(i)--(iv), chamber constancy, the carrier correspondence of Lemma~\ref{lem:carriers} and the record bridge (Lemma~\ref{rp:record-polynomial}, Theorem~\ref{lp:core}); adopted from the Codex proposal sm4\_round4\_exports\_v1, P-25-24, F120-C-PROOF, re-read by the author; assembly: Lemma~\ref{lem:soft-generic}(i)--(iv) new (round~4; cleared by bench~A on SM5, 2026-09-06T00:32:58Z), Proposition~\ref{prop:C-chamber} held, Lemma~\ref{lem:carriers} (i)--(iii) refereed and (iv) new (cleared by bench~A on SM4), Lemma~\ref{lem:corner-values} held, Lemma~\ref{rp:record-polynomial} refereed, Theorem~\ref{lp:core} new (its identification paragraph refereed on SM4), Lemma~\ref{lem:rot} proved; F-25-120; round~5: ``Gauss word'' for ``crossing word'' in the proof, F-25-148)}
\end{theorem}
```

reference/SM/sm-4-knotlaws.tex:993–1129

```tex
\begin{proof}
Write $M=\mu_j$, $M_\varepsilon=M+\varepsilon q$,
$u=\lt_{j-1}$, $v=\lt_j$, $D_\varepsilon=v-\varepsilon q$
and $\tau=\tau_j(P)$. Lemma~\ref{lem:soft-generic} supplies
one initial generic interval. By Proposition~\ref{prop:C-chamber},
$C$ is constant on that chamber, so it suffices to prove the identity
on a smaller initial interval. All choices below can hold
simultaneously because there are finitely many supports and carriers.

\emph{Carrier records and coefficients.}
Use the marked successor model and inherited orientations of
Lemma~\ref{lem:carriers}. For corresponding carriers with the same
retained crossing visits, the cyclic successors and pairings agree.
Each carrier crossing germ follows its containing edge of its own
ambient polygon in the inherited direction, up to a positive scalar
multiple.
Lemma~\ref{lem:soft-generic}(iii) preserves the determinant sign
of each ordered pair of those directions. By
Definition~\ref{def:positive-lift}, the same corresponding visit
is therefore over, and every crossing sign is positive. These
are isomorphic named records, including the correspondence of
oriented crossing-free carriers when the visit sets are empty.
Lemma~\ref{rp:record-polynomial} equates their source polynomials;
the common Laurent substitution and Theorem~\ref{lp:core} identify
these with equal $H^+$-polynomials. If the corresponding rotations
also agree, their crossing counts $m_Q$, rotations $r_Q$ and
$d_Q=1-m_Q-|r_Q|$ agree. Definition~\ref{def:C} then gives equal
corner coefficients $c(Q)$. We now establish each needed carrier
correspondence and rotation assertion.

\emph{Same-sign sector: $\chi_-=\chi_+=-\tau$.}
The inherited Gauss words agree by Lemma~\ref{lem:soft-generic}(iv),
so the independent supports are precisely the same sets $S$.
In the successor cycles of Lemma~\ref{lem:carriers}(i), contracting
the inserted ordinary vertex $M_\varepsilon$ identifies each
carrier with its parent carrier. Exactly the carrier through $M$
gains that vertex. Its old turn $\tau$ is replaced by two turns
$\tau,\tau$, by Lemma~\ref{lem:soft-generic}(ii). All other
original and smoothing corner signs persist by clauses (ii),(iii)
and Lemma~\ref{lem:carriers}(ii). Thus uniformity is equivalent
on the two sides of this correspondence.

For rotation, let $\theta$ be the old principal turn from $u$ to
$v$, and let $\alpha$ be that from $u$ to $q$. The same-sign
determinant conditions put $q$ in the oriented turn wedge:
$0<\alpha<\theta<\pi$ if $\tau=1$, and
$-\pi<\theta<\alpha<0$ if $\tau=-1$.
Indeed the two strict half-plane inequalities choose precisely
the intersection between the rays of $u,v$ inside their principal
angular sector. The two new principal turns tend to $\alpha$
and $\theta-\alpha$, whose sum is $\theta$, with no wrap.
Every other carrier corner has directions converging to its old
regular directions, including smoothing corners involving the
return edge and the successor corner at $B=\mu_{j+1}$.
The full turn sum therefore converges to its parent turn sum.
Lemma~\ref{lem:carriers}(ii) gives regularity of the nearby
carriers, and Lemma~\ref{lem:rot}(i) makes their rotations
integers. Convergence to the old integer implies equality for
all sufficiently small parameters. This applies to every carrier,
including geometrically moving carriers that do not pass through $M$.

Their retained visit records agree by the successor correspondence
and Lemma~\ref{lem:soft-generic}(iii). The preceding coefficient
comparison gives equal products of $c(Q)$. Support sizes do not
change, while $\ell(P_\varepsilon)=\ell(P)+[\tau=1]$.
Substituting in Definition~\ref{def:C} gives
$C(P_\varepsilon)=(-1)^{[\tau=1]}C(P)=-\tau C(P)$,
the required multiplier in this sector.

\emph{Mixed sector: $\chi_-\ne\chi_+$.}
The soft edge has no crossing by Lemma~\ref{lem:soft-generic}(i).
Every selected reconnection therefore leaves the directed path
from $M$ to $M_\varepsilon$ intact. These are consecutive corners
of one carrier, and their turns $-\chi_-$ and $-\chi_+$ are
opposite. No support is uniform, so Definition~\ref{def:C} gives
$C(P_\varepsilon)=0$, the required mixed-sector value.

\emph{Loop sector: $\chi_-=\chi_+=\tau$.}
Let $y$ be the newborn crossing. Its visits are adjacent in the
Gauss word by Lemma~\ref{lem:soft-generic}(iv), so it interlaces
no crossing. The independent supports are exactly $S$ and
$S\cup\{y\}$, with $S\in\Ind(G_P)$.
For a support omitting $y$, Lemma~\ref{lem:carriers}(iii) puts
both visits of $y$ on one carrier $Q'$. Its short arc through
$M,M_\varepsilon$ has no other crossing visit; hence $y$ remains
isolated in the interlacement graph of $Q'$. If the decomposition
is not uniform its term is excluded. If it is uniform,
Lemma~\ref{lem:corner-values}(ii) gives $c(Q')=0$.
Thus every support omitting $y$ contributes zero, including those
whose corresponding parent support was not uniform.

For $S\cup\{y\}$, process $y$ first, using order independence
in Lemma~\ref{lem:carriers}(i). Let $a$ be its visit on the incoming
edge and $b$ its return-edge visit. The clean short arc is
$a\to M\to M_\varepsilon\to b$. Swapping the two outgoing
successors produces the triangle cycle $(b,M,M_\varepsilon)$
and the residual cycle containing $a$. The triangle smoothing
turn follows $D_\varepsilon$ into $u$ and has sign $-\tau$;
the turns at $M,M_\varepsilon$ also have sign $-\tau$.
The three noncollinear segments form an embedded triangle,
so Lemma~\ref{lem:corner-values}(i) gives its coefficient $1$.

All old crossing visits lie on the residual cycle. It replaces
the old corner $M$ by the smoothing corner $y$, whose incoming
and outgoing directions are $u,D_\varepsilon$, of turn sign
$\tau$ by Lemma~\ref{lem:soft-generic}(ii).
The remaining swaps $S$ act only on that residual cycle and give
carriers in bijection with the carriers of $S$ on $P$.
Their original and smoothing corner signs agree; at the distinguished
carrier, the corner $M$ is replaced by $y$ of the same sign.
Consequently $S\cup\{y\}$ is uniform exactly when $S$ is uniform.
No (G1) claim about the intermediate residual polygon is needed:
all resulting curves are carriers of the generic $P_\varepsilon$.

As $y\to M$ and $D_\varepsilon\to v$, every residual principal
turn converges to its old regular counterpart. Integer-valuedness
from Lemma~\ref{lem:rot}(i) again gives equality of all rotations
on a common small interval. Their retained crossing successors and pairings agree under the
inherited correspondence, and the corresponding directed germs
retain their ordered determinant signs,
so the earlier named-record argument gives equal positive-lift
polynomials and corner coefficients. This also covers all other
corresponding carriers, whose positions may have moved.

Every surviving term thus gains exactly one selected crossing and
one triangle coefficient $1$. The original left-turn count changes by
$\ell(P_\varepsilon)-\ell(P)=-[\tau=1]+2[\tau=-1]$.
Definition~\ref{def:C} gives
\[
C(P_\varepsilon)
=(-1)^{-[\tau=1]+2[\tau=-1]+1}C(P).
\]
For $\tau=1$ the exponent is zero; for $\tau=-1$ it is three.
The multiplier is therefore $\tau$, as required. The three sector
multipliers are exactly $(\chi_-+\chi_+)/2$, completing the proof
on the unchanged domain.
\end{proof}
```

## hyp:R — HYPOTHESIS

reference/SM/sm-4-knotlaws.tex:1149–1151

```tex
\begin{hypothesis}[R]\label{hyp:R}
At every simple triple wall, $C(P_+)=C(P_-)$. \status{hyp}
\end{hypothesis}
```

## def:star — DEFINE

reference/SM/sm-5-transport.tex:5–14

```tex
\begin{definition}[stars and the bow-tie]\label{def:star}
For $r\geq1$ put $N=2r+1$, $u_k=(\cos\frac{2\pi k}N,\sin\frac{2\pi k}N)$ for
$k\in\ZZ/N$, and
\[
K_r=(\mu_1,\ldots,\mu_N),\qquad \mu_t=u_{r(t-1)},
\]
the polygon visiting every $r$-th point of the regular $N$-gon in turn. Put
$K_{-r}=\overline{K_r}$. The \emph{bow-tie} is
$K_0=\bigl((0,0),(2,2),(0,2),(2,0)\bigr)$.
\end{definition}
```

## lem:star-generic — PROVE

reference/SM/sm-5-transport.tex:16–33

```tex
\begin{lemma}[the stars are generic]\label{lem:star-generic}
Let $r\geq1$ and $N=2r+1$. Then $\gcd(r,N)=1$, and the following hold.
\begin{enumerate}
\item[(i)] $\sigma K_r=R(K_r)$, where $R$ is the rotation of the plane by
$2\pi r/N$ about the origin. Consequently every principal turn of $K_r$
equals $2\pi r/N\in(0,\pi)$, all turns are left, and $\rot(K_r)=r$.
\item[(ii)] Every edge line of $K_r$ is tangent to the circle of radius
$\rho=\cos(\pi r/N)$ about the origin, at the midpoint of the edge, and the
origin lies strictly to the left of every directed edge.
\item[(iii)] $K_r$ is generic; hence $K_{-r}$ is generic with all turns
right and $\rot(K_{-r})=-r$.
\item[(iv)] $K_0$ is generic, with
$(\chi_{123},\chi_{124},\chi_{134},\chi_{234})=(+1,-1,-1,+1)$, turns
$(\tau_1,\tau_2,\tau_3,\tau_4)=(-1,+1,+1,-1)$, $\rot(K_0)=0$ and
$X(K_0)=\{\{1,3\}\}$.
\end{enumerate}
\status{new (round~4: $\gcd(r,2r+1)=1$ stated, proved and cited at its two uses; adopted from the Codex proposal sm4\_round4\_triple\_star\_v1 (seal 9a82b59a\ldots), F125, re-read by the author; F-25-125; cleared by bench~A on SM5 (2026-09-06T00:32:58Z))}
\end{lemma}
```

reference/SM/sm-5-transport.tex:34–70

```tex
\begin{proof}
First, every common positive divisor of $r$ and $N$ divides
$N-2r=1$, so $\gcd(r,N)=1$.
For integer indices $j,k$, if $rj\equiv rk\pmod N$ then
$N$ divides $r(j-k)$. Multiplying that divisibility by $2$ and
using $2r=N-1$ shows that $N$ divides $j-k$.
Thus multiplication by $r$ permutes the residue classes modulo $N$,
so the displayed star vertices are distinct.
Moreover $R^k$ is the identity precisely when $kr/N$ is an integer.
The same divisibility argument makes this equivalent to $N\mid k$;
the least positive such $k$ is $N$, proving that $R$ has order $N$.

(i) $(\sigma K_r)_t=\mu_{t+1}=u_{rt}=R(u_{r(t-1)})=R(\mu_t)$. Hence
$\lt_t=R(\lt_{t-1})$ for every $t$, so each principal turn is the angle of
$R$ reduced to $(-\pi,\pi)$, which is $2\pi r/N$ itself because $2r<N$; the
$N$ turns sum to $2\pi r$. (ii) $E_t$ is the chord from $u_a$ to $u_{a+r}$
with $a=r(t-1)$. The counterclockwise arc from $u_a$ to $u_{a+r}$ has angle
$2\pi r/N<\pi$, so the midpoint of the chord is at distance $\cos(\pi r/N)$
from the origin and the chord line is tangent there to the circle of that
radius; a chord directed along a counterclockwise arc of angle less than
$\pi$ has the centre on its left. (iii) (G1): the residue permutation proved above gives $N$ distinct
vertices on the unit circle, and no three points of a circle are collinear.
(G2): the $N$ edge lines are pairwise distinct tangent lines of the circle of
radius $\rho$ (their tangency points are the $N$ distinct images of one
midpoint under the powers of $R$, whose order was proved to be $N$). Through a point
outside a circle pass exactly two tangent lines of the circle, so no three of
the edge lines are concurrent, and a fortiori no three edge interiors are.
The statements for $K_{-r}$ are Lemma~\ref{lem:shift}(ii)--(iv). (iv) The
four determinants are $\det((2,2),(0,2))=4$, $\det((2,2),(2,0))=-4$,
$\det((0,2),(2,0))=-4$, $\det((-2,0),(0,-2))=4$; the turns are
$\tau_1=\chi_{412}=\chi_{124}$, $\tau_2=\chi_{123}$, $\tau_3=\chi_{234}$,
$\tau_4=\chi_{341}=\chi_{134}$ (Lemma~\ref{lem:chi-basic}(i)). The edges
$E_1=[(0,0),(2,2)]$ and $E_3=[(0,2),(2,0)]$ meet at $(1,1)$, while $E_2$ and
$E_4$ are disjoint parallel segments; there is one crossing point, so (G2)
holds. The principal turns are $-\frac{3\pi}4,\frac{3\pi}4,\frac{3\pi}4,-\frac{3\pi}4$,
which sum to $0$.
\end{proof}
```

## lem:transport-lengths — PROVE

reference/SM/sm-5-transport.tex:75–83

```tex
\begin{lemma}[positive closing lengths along a direction path]
\label{lem:transport-lengths}
Let $u_1(t),\ldots,u_n(t)$ be continuous unit vectors on a compact interval,
lying in no closed semicircle at any parameter. There are continuous strictly
positive lengths $l_i(t)$ with $\sum_i l_i(t)u_i(t)=0$. At either endpoint,
any prescribed positive closing lengths can be joined to the selected lengths
while keeping the directions fixed.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV thm:mycyclic, prose proof in d8\_transport (C021))}
\end{lemma}
```

reference/SM/sm-5-transport.tex:84–130

```tex
\begin{proof}
For finitely many planar unit vectors, lying in no closed semicircle is
equivalent to the origin being in the interior of their convex hull.
Indeed a supporting line through the origin for a boundary point of that
convex polygon, or a separating line if the origin is outside it, puts all
vectors in one closed half-plane through the origin. Conversely, a closed
half-plane through the origin cannot contain a neighbourhood of the origin.
This is also valid for a segment or a point as convex hull, since either is
contained in a closed half-plane through the origin whenever the origin is
not an interior point in the plane.

Fix a parameter and put $b=\sum_i u_i$. Interiority gives an $\epsilon>0$
such that $-\epsilon b$ belongs to the convex hull. Write
$-\epsilon b=\sum_i a_i u_i$ with $a_i\geq0$. Then
\begin{equation}\label{transport:positive-close}
 \sum_i(a_i+\epsilon)u_i=-\epsilon b+\epsilon\sum_i u_i=0,
 \qquad a_i+\epsilon>0.
\end{equation}
Thus there is a strictly positive closing vector at each parameter.

Fix such a vector $l$ at $t_0$. Choose $p,q$ with
$\det(u_p(t_0),u_q(t_0))\ne0$, possible because the vectors are not all
parallel. Let $E(t)=\sum_i l_i u_i(t)$ and
$D(t)=\det(u_p(t),u_q(t))$. Correct just two coordinates by
\begin{equation}\label{transport:cramer}
 \delta_p(t)=-\frac{\det(E(t),u_q(t))}{D(t)},\qquad
 \delta_q(t)=-\frac{\det(u_p(t),E(t))}{D(t)}.
\end{equation}
The determinant expansion of a vector in the basis $(u_p,u_q)$ gives
$E+\delta_pu_p+\delta_qu_q=0$. The correction is continuous and vanishes
at $t_0$, so all corrected lengths remain positive on a neighbourhood of
$t_0$. This constructs local continuous positive closing vectors.

For a one-point parameter interval the pointwise choice already suffices.
Otherwise choose a finite cover by proper smaller relative intervals, with
nonempty complements, whose closures lie in these neighbourhoods.
Continuous nonnegative weights subordinate to the smaller
intervals, summing to one, can be obtained by taking distances to their
complements and normalizing their sum. Multiply each weight by the local
closing vector on its neighbourhood and sum. The products extend continuously
by zero outside the smaller intervals because the local vectors are bounded
on their closures. The result is a continuous positive closing vector: closure
is linear and every positively weighted local vector has all entries positive.
Finally, for fixed directions the set of strictly positive closing lengths is
convex. Straight segments in that set join any prescribed endpoint lengths
to the selected ones.
\end{proof}
```

## lem:transport-angle-interval — PROVE

reference/SM/sm-5-transport.tex:132–140

```tex
\begin{lemma}[lifting a semicircle to one real interval]
\label{lem:transport-angle-interval}
If a finite real sequence $\theta_0,\ldots,\theta_N$ has
$|\theta_{i+1}-\theta_i|<\pi$, and all its unit directions lie in a closed
semicircle, then all its real entries lie in one interval of length $\pi$.
Conversely, containment of all entries in such an interval puts their unit
directions in a closed semicircle.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV thm:mycyclic, prose proof in d8\_transport (C021))}
\end{lemma}
```

reference/SM/sm-5-transport.tex:141–148

```tex
\begin{proof}
The inverse image of a fixed closed semicircle under
$\theta\mapsto(\cos\theta,\sin\theta)$ is a union of intervals
$[\alpha+2\pi k,\alpha+\pi+2\pi k]$. Distinct consecutive intervals have
a gap of length $\pi$. A step of absolute size strictly less than $\pi$
cannot move from one interval to another, so induction fixes one interval
for the whole sequence. The converse follows by projection of that interval.
\end{proof}
```

## thm:mycyclic — PROVE

reference/SM/sm-5-transport.tex:150–159

```tex
\begin{theorem}[connectivity of the fibres]\label{thm:mycyclic}
Let $(n,r)$ be admissible and let $P,P'\in\mathcal R_n$ be labelled tuples
with $\rot(P)=\rot(P')=r$. If $(n,r)\ne(4,0)$, a continuous path in
$\mathcal R_n\cap\rot^{-1}(r)$ joins $P$ to $P'$. If $(n,r)=(4,0)$,
there is a $k\in\mathbb Z/4$ and such a path from $P$ to $\sigma^kP'$.
The four shifts of $K_0$ lie in the four distinct labelled components,
distinguished by their turn words. Thus every fibre of cyclic polygon orbits
is path connected.
\status{proved (refereed: bench A, 2026-09-05T19:29:31Z; transcribed from CV thm:mycyclic --- the $k=0$ refinement from CV's proof, not its statement --- with RC root:four-components for the realizability of the four words at $(4,0)$; the two locators compose, each supplying a half (C021; F-25-49, F-25-104, F-25-129))}
\end{theorem}
```

reference/SM/sm-5-transport.tex:160–287

```tex
\begin{proof}
Use tail directions $d_i=\mu_{i+1}-\mu_i$, unit directions $u_i=d_i/|d_i|$,
and principal turns $\vartheta_i\in(-\pi,\pi)$ from $u_{i-1}$ to $u_i$.
Multiplication of $u_i=e^{\mathrm i\vartheta_i}u_{i-1}$ around the cycle
shows that $\sum_i\vartheta_i$ is an integer multiple of $2\pi$.
Principal turns vary continuously on the regular locus, so their normalized
sum is constant on every path there. The symbols $\tau_i$ remain the signs
of these real principal turns, not the angles themselves.

\emph{Reconstructing a polygon from directions.}
A direction path with no antiparallel successive pair and with no closed
semicircle containment can be closed using
Lemma~\ref{lem:transport-lengths}. Starting at any continuous base point,
successively add the positive vectors $l_i(t)u_i(t)$; the final sum is zero,
so this gives a continuous closed labelled $n$-tuple. Every edge is nonzero,
and every successive pair has the prescribed principal turn in $(-\pi,\pi)$.
Consequently the tuple stays in $\mathcal R_n$. Interpolate the base point
between those of $P,P'$ and use the endpoint length segments of that lemma
to recover the exact endpoint tuples. No vertex is inserted or deleted.

\emph{Nonzero rotation.}
Choose real arguments $\beta,\beta'$ for the first unit directions and
interpolate these arguments and all principal turns linearly. The interpolated
turns lie strictly between $-\pi$ and $\pi$ and have sum $2\pi r$.
The lifted edge arguments, starting with $\theta_0(t)=\beta(t)$, are
\begin{equation}\label{transport:prefix}
 \theta_k(t)=\beta(t)+\sum_{m=1}^{k}\vartheta_{m+1}(t),
 \quad 0\leq k\leq n,
 \qquad \theta_n(t)-\theta_0(t)=2\pi r,
\end{equation}
where turn indices are cyclic. The first $n$ entries give the unit directions;
the last repeats the first direction because $r$ is an integer. If these
directions lay in a closed semicircle,
Lemma~\ref{lem:transport-angle-interval} would put the whole lifted sequence
in one interval of length $\pi$, implying $|2\pi r|\leq\pi$.
This contradicts $r\ne0$. The reconstruction above therefore joins the exact
labelled endpoints, with no cyclic shift.

\emph{The zero-rotation angle domain.}
For $r=0$, the lifted angles close as real numbers and form a cyclic vector
$\theta=(\theta_1,\ldots,\theta_n)$ satisfying
\begin{equation}\label{transport:zero-angle-domain}
 |\theta_{i+1}-\theta_i|<\pi\quad\text{cyclically}.
\end{equation}
The directions of any regular closed polygon lie in no closed semicircle.
For if a normal $v\ne0$ had $\langle v,d_i\rangle\geq0$ for every edge,
closure would force every scalar product to be zero. All directions would
then be on the two rays of one line. Antiparallel adjacent directions are
forbidden, so every edge would point along the same ray. Their positive
length sum could not be zero. By
Lemma~\ref{lem:transport-angle-interval}, the cyclic angle vector of a
zero-rotation polygon consequently has
$\max_i\theta_i-\min_i\theta_i>\pi$.

For an ordered pair of indices with forward cyclic distance
$d\in\{2,\ldots,n-2\}$, define
\begin{equation}\label{transport:chart}
 \mathcal A(h,d)=\{\theta:\eqref{transport:zero-angle-domain}\text{ holds},
                  \ \theta_h-\theta_{h+d}>\pi\}.
\end{equation}
These open convex charts cover all zero-rotation endpoints: take a maximum
and a minimum; they cannot be cyclically adjacent by
\eqref{transport:zero-angle-domain}. Conversely every chart point has
directions lying in no closed semicircle, by
Lemma~\ref{lem:transport-angle-interval}. Every continuous angle path inside
the union can thus be reconstructed as above.

\emph{Connected chart overlaps for $n\geq5$.}
For $2\leq d\leq n-3$, both of the following chart pairs intersect:
\begin{equation}\label{transport:chart-moves}
 \mathcal A(h,d),\mathcal A(h,d+1);
 \qquad \mathcal A(h,d+1),\mathcal A(h+1,d).
\end{equation}
Here is an explicit witness, reading indices $s=0,\ldots,n-1$ from $h$.
Set the high value to $3\pi/2$ and the low value to zero. For the first pair,
put the high value at $s=0$, descend linearly to zero at $s=d$, keep zero
through $s=d+1$, and rise linearly back to the high value at $s=n$.
For the second pair, keep the high value at $s=0,1$, descend linearly to zero
at $s=d+1$, and rise linearly back to the high value at $s=n$.
Every ramp has at least two steps, so each step has magnitude at most
$3\pi/4<\pi$. Each specified high-minus-low difference is $3\pi/2>\pi$,
proving both overlaps. The cyclic last step is one of these ramp steps.

The first moves reduce any distance to two. At distance two, the two moves
$\mathcal A(h,2)\to\mathcal A(h,3)\to\mathcal A(h+1,2)$ advance the high
index by one, and are valid even for $n=5$. Hence their overlap graph is
connected. Join endpoint angle vectors to consecutive overlap witnesses by
straight segments in their convex charts. The resulting finite path of
feasible angle vectors reconstructs a regular path from $P$ to $P'$, again
with no relabelling.

\emph{The exceptional four-vertex fibre.}
For $n=4$ the charts are just $\mathcal A(h,2)$ for four indices $h$.
They are nonempty: values $3\pi/2,3\pi/4,0,3\pi/4$, beginning at $h$,
satisfy all their inequalities. If $\theta_h-\theta_{h+2}>\pi$, the two
intermediate entries satisfy
\begin{equation}\label{transport:four-orders}
 \theta_h>\theta_{h+1}>\theta_{h+2},\qquad
 \theta_h>\theta_{h+3}>\theta_{h+2}.
\end{equation}
For example $\theta_{h+1}>\theta_h-\pi>\theta_{h+2}$, and
$\theta_{h+1}<\theta_{h+2}+\pi<\theta_h$; the other case is identical.
Thus the turn signs, beginning at vertex $h$, are $(+,-,-,+)$.
The four charts force the four distinct cyclic rotations of this word.
They are therefore disjoint, and every rotation-zero four-tuple belongs to
one of them. In particular no such tuple has a zero turn. Along a regular
zero-rotation path all four nonzero turn signs remain fixed by continuity,
so different words cannot be joined. Two tuples with the same word belong
to the same convex angle chart; their real argument choices can differ by
a common multiple of $2\pi$, which changes neither the chart inequalities
nor the reconstruction. Interpolation inside that chart and the positive-length
construction join them. There are exactly four components.

For $K_0=((0,0),(2,2),(0,2),(2,0))$ the corner determinants are
$(-4,4,4,-4)$. Its principal turns are the corresponding signs times
$3\pi/4$, so its rotation is zero. Cyclic shifts rotate this sign word and
exhibit all four components. Shifting $P'$ to match the word of $P$ gives
the asserted path in the exceptional case.

Finally a regular triangle is noncollinear: three collinear nonzero closing
edges must reverse direction at a vertex. All three turn determinants of a
noncollinear triangle equal its oriented area determinant, so the three
principal turns have one sign. Their sum is a nonzero multiple of $2\pi$
of absolute value less than $3\pi$; its rotation is $+1$ or $-1$.
There is no zero-rotation case at $n=3$. These cases exhaust admissible
arities. Passing any constructed path to the cyclic quotient identifies
its shifted target with the original target orbit, proving the orbit statement.
\end{proof}
```

## lem:transport — PROVE

reference/SM/sm-5-transport.tex:299–306

```tex
\begin{lemma}[transport]\label{lem:transport}
Let $P,Z$ be generic labelled tuples in the same fibre $(n,r)$. There are
$k\in\ZZ/n$, with $k=0$ unless $(n,r)=(4,0)$, and a piecewise-affine path in
$\mathcal R_n$ from $P$ to $\sigma^kZ$ that is generic except at finitely
many parameters, at each of which it is a simple wall germ of type (F), (V),
(T), (E) or (C); at each (F) the deletion is generic, and at each (V) both
halves are generic, all with fewer than $n$ vertices. \status{proved (refereed: bench A, 2026-09-05T18:22:57Z; transcribed from SM1 lem:transport, from Theorems~\ref{thm:mycyclic}, \ref{thm:relgp} and Lemma~\ref{lem:children}; proof paraphrased in the base (C021); F-25-76)}
\end{lemma}
```

reference/SM/sm-5-transport.tex:307–313

```tex
\begin{proof}
Theorem~\ref{thm:mycyclic} supplies the path from $P$ to $\sigma^kZ$
in $\mathcal R_n$. Its rotation is constant by Lemma~\ref{lem:rot}(ii).
Theorem~\ref{thm:relgp} replaces it by a path with only the five listed
simple wall types. Lemma~\ref{lem:children} gives generic deletions and
halves.
\end{proof}
```

## lem:soft-rotation — PROVE

reference/SM/sm-5-transport.tex:317–326

```tex
\begin{lemma}[rotation of a soft insertion]\label{lem:soft-rotation}
Let $P$ be generic, $q$ admissible at $j$, and $\varepsilon$ small
(Lemma~\ref{lem:soft-generic}). Then $\rot(P_\varepsilon)=\rot(P)$ in the
same-sign and mixed sectors, and $\rot(P_\varepsilon)=\rot(P)-\tau_j(P)$ in
the loop sector. Moreover the same-sign sector is the open cone of directions
strictly between $\lt_{j-1}$ and $\lt_j$ (the wedge of the turn), the loop
sector is the open cone strictly between $-\lt_{j-1}$ and $-\lt_j$, and the
mixed sector is the complement of the closures of these two cones.
\status{new}
\end{lemma}
```

reference/SM/sm-5-transport.tex:327–371

```tex
\begin{proof}
Put $u=\lt_{j-1}$, $v=\lt_j$, and
$\theta=\operatorname{Arg}(v/u)\in(-\pi,\pi)$, using the complex
identification of the oriented plane. Let
$\alpha=\operatorname{Arg}(q/u)$ and
$\beta_0=\operatorname{Arg}(v/q)$ be principal turns. All three
exist because admissibility makes the relevant pairs nonparallel.
At the new point the actual turn is
$\beta_\varepsilon=\operatorname{Arg}((v-\varepsilon q)/q)$,
which converges to $\beta_0$. The turn at the successor vertex also
changes, but converges to its old value because its incoming direction
$v-\varepsilon q$ tends to $v$ and the old corner is regular.
All other original turns except the replaced turn at $j$ are unchanged.
By Lemmas~\ref{lem:soft-generic} and~\ref{lem:rot}(ii), the rotation
of $P_\varepsilon$ is one fixed integer on a sufficiently small
positive interval. Taking the limit of the full sum of turns therefore
gives the exact integer identity
\begin{equation}\label{eq:soft-rotation-limit}
2\pi\bigl(\rot(P_\varepsilon)-\rot(P)\bigr)
=\alpha+\beta_0-\theta.
\end{equation}
The left side is constant on that interval, not an assertion that the
successor turn is unchanged at finite $\varepsilon$.

The three direction ratios multiply as $(q/u)(v/q)=v/u$, so
$\alpha+\beta_0-\theta$ is a multiple of $2\pi$.
Moreover $\sgn\alpha=-\chi_-$ and $\sgn\beta_0=-\chi_+$.
In the same-sign sector both have the sign $\tau_j=\sgn\theta$.
Their sum and $\theta$ lie in the same open interval of length $2\pi$,
so the multiple is zero. In the mixed sector $\alpha,\beta_0$ have
opposite signs, making their sum lie in $(-\pi,\pi)$; the difference
from $\theta$ is again strictly between $-2\pi$ and $2\pi$, so is zero.
In the loop sector both signs are $-\tau_j$. When $\tau_j=1$,
the difference lies in $(-3\pi,0)$ and must be $-2\pi$; when
$\tau_j=-1$ it lies in $(0,3\pi)$ and must be $2\pi$.
Equation~\eqref{eq:soft-rotation-limit} gives exactly the stated rotations.

For the cone description, set the angle of $u$ equal to zero and that
of $v$ equal to $\theta$. The determinant signs change only at the
four rays $u,v,-u,-v$. The same-sign inequalities put $q$ strictly
inside the turn wedge from $u$ to $v$ of angular width $|\theta|<\pi$;
the loop inequalities put it inside the opposite wedge. The remaining
two open angular intervals are exactly the mixed sector. This proves
the cone statements as well.
\end{proof}
```

## def:anchors — DEFINE

reference/SM/sm-5-transport.tex:373–397

```tex
\begin{definition}[anchors]\label{def:anchors}
Let $(n,r)$ be admissible with $n\geq4$.
\begin{enumerate}
\item[(Z)] If $(n-1,r)$ is admissible, a \emph{zero anchor} is a generic
$n$-gon of the form $P^{(j,q)}_\varepsilon$ (Definition~\ref{def:soft}) in
the mixed sector, for some generic $(n-1)$-gon $P$ of rotation $r$, some
vertex $j$ of $P$, some admissible $q$ and some small $\varepsilon>0$.
\item[(L)] If $(n,r)$ is minimal with $|r|\geq2$, a \emph{loop anchor} is a
generic $n$-gon of the form $P^{(j,q)}_\varepsilon$ in the loop sector, for
some generic $(n-1)$-gon $P$ of rotation $r-\sgn(r)$ and some vertex $j$ of
$P$ with $\tau_j(P)=-\sgn(r)$.
\item[(L$_0$)] If $(n,r)=(4,0)$, a \emph{loop anchor} is a generic $4$-gon
of the form $P^{(j,q)}_\varepsilon$ in the loop sector for a triangle $P$
and any of its vertices $j$.
\end{enumerate}
In all three cases $q$ is admissible and $0<\varepsilon<\varepsilon_0$, where
$\varepsilon_0=\varepsilon_0(P,j,q)>0$ is the bound of
Lemma~\ref{lem:soft-generic}: on $(0,\varepsilon_0)$ the insertion is generic
and lies in one chamber, so that Lemma~\ref{lem:soft-rotation} gives its
rotation throughout. This geometric bound is part of the anchor data; it is
not a bound uniform over the functions to which a soft theorem is applied.
In each case $P$ is the \emph{parent} of the anchor, $j$ its \emph{insertion
vertex}, and the soft edge of the anchor is its edge $E_j$ (from $\mu_j$ to
$\mu_*=\mu_{j+1}$ in the labelling of the anchor).
\end{definition}
```

## prop:anchors-exist — PROVE

reference/SM/sm-5-transport.tex:399–405

```tex
\begin{proposition}[anchors exist]\label{prop:anchors-exist}
For every admissible $(n,r)$ with $n\geq4$, exactly one of the cases
(Z), (L), (L$_0$) of Definition~\ref{def:anchors} applies. An anchor
of that type exists, is generic, has $n$ vertices and rotation $r$. For a given generic parent $P$ and vertex $j$, the mixed
sector and the loop sector both contain admissible vectors $q$, so in case
(Z) the insertion vertex may be prescribed. \status{new (round~4: the exhaustion of the three cases printed, adopted from the Codex proposal sm4\_round4\_core\_v1, P-25-23, F118, re-read by the author; F-25-118; cleared by bench~A on SM5 (2026-09-06T00:32:58Z) before the round-5 disjointness sentence of the exhaustion paragraph (F-25-150) and the citations of Proposition~\ref{prop:chambers} and of the density clause of Lemma~\ref{lem:fibres} in the loop-anchor construction (F-25-146))}
\end{proposition}
```

reference/SM/sm-5-transport.tex:406–459

```tex
\begin{proof}
\emph{Exhaustion.} If $(n-1,r)$ is admissible, case (Z) applies.
Otherwise $n-1\geq3$, so Definition~\ref{def:admissible} says that
either $2|r|\geq n-1$ or $(n-1,r)=(3,0)$. In the first case,
$2|r|<n$ and integrality give $2|r|=n-1$. Thus
$n=2|r|+1$, and $n\geq4$ forces $|r|\geq2$, giving (L).
The exceptional predecessor gives exactly $(n,r)=(4,0)$, case
(L$_0$). These alternatives are disjoint: in case (L) the predecessor
$(n-1,r)=(2|r|,r)$ has $2|r|=n-1$ and in case (L$_0$) it is $(3,0)$, so in
neither is it admissible (Definition~\ref{def:admissible}), which excludes
(Z); and (L) has $|r|\geq2$ while (L$_0$) has $r=0$. In particular $(4,1)$
and $(4,-1)$ have admissible triangular predecessors and belong
 to (Z), not (L).

\emph{Sectors.} By Lemma~\ref{lem:soft-rotation} each sector is a nonempty
open cone of directions; admissibility removes finitely many lines
($\det(q,\mu_k-\mu_j)=0$, $k\neq j$), so each sector contains admissible
vectors. For such $q$ and $0<\varepsilon<\varepsilon_0$, as Definition~\ref{def:anchors}
requires, Lemma~\ref{lem:soft-generic} makes $P_\varepsilon$ generic and
Lemma~\ref{lem:soft-rotation} gives its rotation.

(Z) A generic $(n-1)$-gon of rotation $r$ exists by Lemma~\ref{lem:fibres};
in the mixed sector the rotation is preserved.

(L) Let $r\geq2$. The star $K_{r-1}$ is generic with all turns left and
rotation $r-1$ (Lemma~\ref{lem:star-generic}; for $r=2$ it is the
counterclockwise triangle). Subdivide one edge at its midpoint, obtaining a
$2r$-gon in $\mathcal R_{2r}$ with one zero turn and rotation $r-1$
(Lemma~\ref{lem:rot}(iii)). Write the subdivided edge as $B-A=w$
and its moved midpoint as $M=(A+B)/2+\delta v$, where $\delta>0$
and $\det(w,v)>0$: the displacement is to the left of the directed edge.
The new corner determinant is
\begin{equation}\label{eq:anchor-midpoint-turn}
\det(M-A,B-M)=-\delta\det(w,v)<0.
\end{equation}
Thus its turn is right. The two neighbouring turn determinants are
strictly positive at $\delta=0$ and remain positive for a short move.
All edge lengths remain positive; the initially positive-flat new
corner and all other regular corners stay in the open regular locus.
Rotation therefore remains $r-1$ by Lemma~\ref{lem:rot}(ii). The
generic locus is open (Proposition~\ref{prop:chambers}) and dense (the
density clause of Lemma~\ref{lem:fibres}), so a
small perturbation gives a generic $2r$-gon $P$ of rotation $r-1$ with a
vertex $j$ of turn $\tau_j=-1=-\sgn(r)$. A loop-sector insertion at $j$ gives
a generic $(2r+1)$-gon of rotation $r-1-\tau_j=r$. For $r\leq-2$ apply the
reflection $(x,y)\mapsto(x,-y)$ to the construction for $-r$: it negates every
chirotope and every rotation number, maps generic polygons to generic
polygons, and maps a loop-sector insertion to a loop-sector insertion (the
sectors are defined by sign patterns relative to $\tau_j$, which all flip
together).

(L$_0$) Insert a loop at any vertex of the counterclockwise triangle: the
rotation becomes $1-1=0$, and the result is generic with four vertices.
\end{proof}
```

## prop:anchor-values — PROVE

reference/SM/sm-5-transport.tex:461–476

```tex
\begin{proposition}[anchor values]\label{prop:anchor-values}
Let $F$ be a function on generic polygons of all arities, constant
on chambers and satisfying the soft theorem in the form of
Theorem~\ref{thm:C-soft} at every admissible soft insertion into
a generic polygon. With $P$ the parent and $j$ the insertion vertex,
\[
F(Z)=0\quad\text{for every zero anchor},\qquad
F(Y)=\tau_j(P)F(P)\quad\text{for every loop anchor}.
\]
In case (L), $\tau_j(P)=-\sgn(r)$; in case (L$_0$), it is the
orientation sign of the parent triangle. The function $C$ satisfies
these hypotheses. The same identities hold for $A_g$ at every
anchor root other than the soft edge, with the corresponding
parent root used on the right-hand side.
\status{new (round~4: chamber constancy added to the hypothesis and the function-dependent soft threshold handled by transport along the initial chamber; adopted from the Codex proposal sm4\_round4\_core\_v1, P-25-23, F119, re-read by the author; F-25-119; cleared by bench~A on SM5 (2026-09-06T00:32:58Z))}
\end{proposition}
```

reference/SM/sm-5-transport.tex:477–503

```tex
\begin{proof}
Fix an anchor with parameter $\varepsilon$ and geometric bound
$\varepsilon_0$ from Definition~\ref{def:anchors}. For its fixed
parent, vertex and admissible vector, the soft hypothesis for $F$
supplies a bound $\delta_F>0$. Choose
$0<\varepsilon'<\min\{\varepsilon,\delta_F\}$.
The whole parameter interval between $\varepsilon'$ and
$\varepsilon$ is contained in $(0,\varepsilon_0)$, so both tuples
lie in the same chamber by Lemma~\ref{lem:soft-generic}.
Chamber constancy equates their $F$ values. At $\varepsilon'$ the
soft theorem applies. Its multiplier is zero in the mixed sector,
since the attachment signs are opposite. In the loop sector both
attachment signs equal $\tau_j(P)$, so the multiplier is
$\tau_j(P)$. This proves both identities at the original
$\varepsilon$, without requiring a bound uniform over functions.

Proposition~\ref{prop:C-chamber} and Theorem~\ref{thm:C-soft}
supply the two hypotheses for $C$. For $A_g$, fix the physical
nonsoft edge throughout the labelled family and its corresponding
edge of the parent. Theorem~\ref{thm:A-soft} gives the required
identity on an initial interval for that root. Throughout the
geometric interval the tuple remains generic, so every initially
nonzero determinant keeps its sign along the connected parameter
interval. Proposition~\ref{prop:A-chamber} therefore makes $A_g$
constant along that family. The same smaller-parameter argument
proves the rooted assertion, without using root independence.
\end{proof}
```

## lem:A-small-values — PROVE

reference/SM/sm-6-comparison.tex:5–13

```tex
\begin{lemma}[triangle and bow-tie values]\label{lem:A-small-values}
\begin{enumerate}
\item[(i)] For every labelled triangle satisfying (G1), all turns
have a common sign $\tau$, and $A_g=-\tau$ at every physical root.
\item[(ii)] For the bow-tie of Definition~\ref{def:star},
$A_g(\sigma^kK_0)=-1$ for every physical root $g$ and every integer $k$.
\end{enumerate}
\status{new (round~4; extracted from the SM4 proof of Theorem~\ref{thm:root-indep-proof}; adopted from the Codex proposal sm4\_round4\_exports\_v1, P-25-24, F117-SMALL-LEMMA, re-read by the author; F-25-117; cleared by bench~A on SM5 (2026-09-06T00:32:58Z))}
\end{lemma}
```

reference/SM/sm-6-comparison.tex:14–51

```tex
\begin{proof}
For a noncollinear triangle the three turn triples are cyclic
permutations of one ordered triple. Lemma~\ref{lem:chi-basic}(i)
therefore gives the common sign $\tau$. For any physical root,
the boundary word has two leaves. Its unary root contribution is
$b_{[0,2]}=0$, since its only ordinary composition has two parts
and vanishes by Lemma~\ref{lem:gates-nonzero}. The binary root
has $d=h=\chi(a_2,a_1,a_0)=-\tau$, so its factor
$(d+h)/2$ is $-\tau$. This proves (i) directly on (G1).

For (ii), use the four coordinates of Definition~\ref{def:star}.
All two-leaf open sums vanish, because their near
and far signs agree. On a boundary word $(a_0,a_1,a_2,a_3)$, put
$d_1=\chi(a_2,a_1,a_0)$, $d_2=\chi(a_3,a_2,a_1)$,
$h_1=\chi(a_3,a_1,a_0)$ and $h_2=\chi(a_3,a_2,a_0)$.
Every two-part composition has a two-leaf child and vanishes.
The unary root term is therefore minus the ordinary three-part gate
product, and the three-part root term is its barred counterpart. Hence
\begin{equation}\label{eq:root-bowtie-recursion}
A_g=\frac{(d_1+h_1)(d_2+h_2)-(d_1-h_1)(d_2-h_2)}4.
\end{equation}
Expanding the two products cancels $d_1d_2$ and $h_1h_2$ and leaves
$2d_1h_2+2h_1d_2$. Thus $A_g=(d_1h_2+h_1d_2)/2$.
At the four physical roots of $K_0$, direct determinants of its displayed
coordinates give
\begin{equation}\label{eq:root-bowtie-signs}
\begin{array}{c|rrrr|r}
g&d_1&d_2&h_1&h_2&A_g\\\hline
1&-1&1&-1&1&-1\\
2&1&1&-1&-1&-1\\
3&1&-1&1&-1&-1\\
4&-1&-1&1&1&-1
\end{array}
\end{equation}
Cyclic shifts merely permute these four root words by
Proposition~\ref{prop:A-reversal}(i). Consequently every root of every
$\sigma^kK_0$ has value $-1$.
\end{proof}
```

## thm:root-indep-proof — PROVE

reference/SM/sm-6-comparison.tex:53–56

```tex
\begin{theorem}[root independence]\label{thm:root-indep-proof}
For every generic polygon $P$ and any two of its edges $g,h$, $A_g(P)=A_h(P)$.
\status{new (round~4: the anchor parameter chosen below the geometric bound and the two root-specific soft bounds, F-25-119; the triangle value and the bow-tie table extracted to Lemma~\ref{lem:A-small-values} and the negative stars handled by reversal, F-25-117; Codex proposals P-25-23 and P-25-24 adopted or adapted)}
\end{theorem}
```

reference/SM/sm-6-comparison.tex:57–103

```tex
\begin{proof}
Strong induction on $n$. The case $n=3$ follows from
Lemma~\ref{lem:A-small-values}(i).

Let $n\geq4$, let $P$ be generic of rotation $r$, and let $g\neq h$ be two
edge labels. For a generic labelled tuple $Q$ with $n$ vertices put
$\Delta_{gh}(Q)=A_g(Q)-A_h(Q)$. Choose a target $Z$ in the fibre $(n,r)$ as
follows.
\begin{itemize}
\item If $(n,r)$ is not minimal: $Z$ is a zero anchor whose insertion vertex
$j$ is chosen with $j\notin\{g,h\}$ (Proposition~\ref{prop:anchors-exist};
there are $n-1\geq3$ choices of $j$). Its soft edge is $E_j(Z)$.
Choose its parameter below the geometric bound of
Definition~\ref{def:anchors} and below the two bounds in
Theorem~\ref{thm:A-soft} for the roots $g$ and $h$.
All three bounds are positive, so such a choice exists.
\item If $(n,r)$ is minimal with $|r|\geq2$: $Z=K_r$.
\item If $(n,r)=(4,0)$: $Z=K_0$.
\end{itemize}
Lemma~\ref{lem:transport} gives $k$ ($k=0$ in the first two cases) and a path
from $P$ to $\sigma^kZ$ with finitely many simple walls. Along the path
$\Delta_{gh}$ is constant: on generic segments by
Proposition~\ref{prop:A-chamber}; at (T), (E), (C) by
Theorem~\ref{thm:A-R3E}, which gives zero jump for each root separately; at a
flat wall at $i$ the jump of $\Delta_{gh}$ is
$A_{D_i(g)}(Q)-A_{D_i(h)}(Q)$ with $Q$ the generic deletion
(Theorem~\ref{thm:A-S3}), which vanishes by induction; at a vertex--edge wall
the jump is
$s\bigl(A_{h_1}(\lambda_1)A_{h_2}(\lambda_2)-A_{h_1'}(\lambda_1)A_{h_2'}(\lambda_2)\bigr)$
with $(h_1,h_2)=H(g)$, $(h_1',h_2')=H(h)$ and generic halves
(Theorem~\ref{thm:A-S7}), which vanishes by induction applied to each half.
Hence $\Delta_{gh}(P)=\Delta_{gh}(\sigma^kZ)$.

At the target: in the non-minimal case $k=0$ and neither $E_g$ nor $E_h$ is
the soft edge of $Z$, so Theorem~\ref{thm:A-soft} in the mixed sector gives
$A_g(Z)=A_h(Z)=0$. For $Z=K_r$ with $r\geq2$: by Lemma~\ref{lem:star-generic}(i) and
Proposition~\ref{prop:A-reversal}(i),
$A_{g+1}(K_r)=A_g(\sigma K_r)=A_g(R(K_r))=A_g(K_r)$, the last step because
every chirotope, hence every gate, is invariant under a rotation of the plane;
so all roots of $K_r$ have one value. For $r\leq-2$, $K_r=\overline{K_{|r|}}$
by Definition~\ref{def:star}, and Proposition~\ref{prop:A-reversal}(ii) gives
$A_h(K_r)=(-1)^NA_{1-h}(K_{|r|})=-A_{1-h}(K_{|r|})$ with $N=2|r|+1$ odd; since
$h\mapsto1-h$ is a bijection of $\ZZ/N$, all roots of $K_r$ have one value as
well. Cyclic covariance, Proposition~\ref{prop:A-reversal}(i), covers every
shift. For $Z=K_0$, Lemma~\ref{lem:A-small-values}(ii) gives $-1$ at every
root of every shift. In every target case $\Delta_{gh}(\sigma^kZ)=0$.
\end{proof}
```

## cor:A-lawful — PROVE

reference/SM/sm-6-comparison.tex:105–116

```tex
\begin{corollary}[$A$ is a chamber function on polygons]\label{cor:A-lawful}
$A(P):=A_g(P)$ (any $g$) is well defined on generic polygons and satisfies:
chamber constancy and silence (Proposition~\ref{prop:A-chamber},
Theorem~\ref{thm:A-R3E}(ii)); the flat law
$A(P_{\rm right})-A(P_{\rm left})=A(P(0)\setminus j)$; the cusp law
$A(P_{\rm loop})-A(P_{\rm no})=-\kappa A(P(0)\setminus j)$ when the deletion
satisfies (G1); the vertex--edge law $A(P_+)-A(P_-)=sA(\lambda_1)A(\lambda_2)$;
the triple law $A(P_+)=A(P_-)$; the soft theorem
$A(P_\varepsilon)=\frac{\chi_-+\chi_+}2A(P)$ in every sector; reversal
$A(\overline P)=(-1)^nA(P)$; and $A(K_1)=-1$, $A(K_{-1})=+1$ on the
counterclockwise and clockwise triangles. \status{new (round~4 assembly: Theorem~\ref{thm:root-indep-proof} (new) removes the root choice; Proposition~\ref{prop:A-reversal}(i),(ii), Theorems~\ref{thm:A-S3}, \ref{thm:A-S4}, \ref{thm:A-S7}, \ref{thm:A-R3E} and~\ref{thm:A-soft} refereed; Proposition~\ref{prop:A-chamber} proved; Lemma~\ref{lem:A-small-values} (new) supplies the triangle values; F-25-117)}
\end{corollary}
```

reference/SM/sm-6-comparison.tex:117–124

```tex
\begin{proof}
Theorem~\ref{thm:root-indep-proof} removes the root choice, and
Proposition~\ref{prop:A-reversal}(i) gives cyclic descent.
Theorems~\ref{thm:A-S3}, \ref{thm:A-S4}, \ref{thm:A-S7}, \ref{thm:A-R3E},
\ref{thm:A-soft} (evaluated at any root other than the soft edge),
Proposition~\ref{prop:A-reversal}(ii), and the triangle values in
Lemma~\ref{lem:A-small-values}(i) give the listed laws and base values.
\end{proof}
```

## thm:uniqueness — PROVE

reference/SM/sm-6-comparison.tex:201–218

```tex
\begin{theorem}[uniqueness; Theorem~1 of the main text]\label{thm:uniqueness}
Let $F$ be a function assigning an integer to every generic polygon of every
arity $n\geq3$ and satisfying:
\begin{enumerate}
\item[(a)] $F$ is constant on chambers and unchanged across simple silent
walls (types (E) and (C));
\item[(b)] the flat law $F(P_{\rm right})-F(P_{\rm left})=F(P(0)\setminus j)$
at every simple flat wall;
\item[(c)] the vertex--edge law $F(P_+)-F(P_-)=s\,F(\lambda_1)F(\lambda_2)$
at every simple vertex--edge wall, both branches;
\item[(d)] $F(P_+)=F(P_-)$ at every simple triple wall;
\item[(e)] the soft theorem $F(P_\varepsilon)=\frac{\chi_-+\chi_+}2F(P)$ for
all small $\varepsilon$, at every soft insertion of an admissible vector into
a generic polygon;
\item[(f)] $F(K_1)=-1$ and $F(K_{-1})=+1$.
\end{enumerate}
Then $F(P)=A(P)$ for every generic polygon $P$. \status{new (round~4: the anchor step cites hypotheses (a) and (e), as Proposition~\ref{prop:anchor-values} now requires, F-25-119)}
\end{theorem}
```

reference/SM/sm-6-comparison.tex:219–247

```tex
\begin{proof}
$A$ satisfies (a)--(f) by Corollary~\ref{cor:A-lawful}. Put $\Delta=F-A$, a
function on generic polygons, and argue by strong induction on $n$.

\emph{Base $n=3$.} The generic triangles form two chambers, the
counterclockwise and the clockwise triangles, containing $K_1$ and $K_{-1}$
respectively; by (a) and (f), $\Delta=0$ on both.

\emph{Step.} Let $n\geq4$ and assume $\Delta=0$ on every generic polygon with
fewer than $n$ vertices. Let $P$ be generic with $\rot(P)=r$, so that $(n,r)$
is admissible, and let $Z$ be an anchor for $(n,r)$
(Definition~\ref{def:anchors}, Proposition~\ref{prop:anchors-exist}).
Lemma~\ref{lem:transport} gives a path from $P$ to $\sigma^kZ$, which as a
path of polygons ends at $Z$, with finitely many simple walls of types (F),
(V), (T), (E), (C). Between walls $\Delta$ is constant by (a); at (E), (C) it
is unchanged by (a); at (T) by (d). At a flat wall at $j$ the jump of
$\Delta$ is $\Delta(P(0)\setminus j)=0$ by induction, the deletion being
generic with $n-1$ vertices. At a vertex--edge wall the jump is
$s\bigl(F(\lambda_1)F(\lambda_2)-A(\lambda_1)A(\lambda_2)\bigr)
=s\bigl(\Delta(\lambda_1)F(\lambda_2)+A(\lambda_1)\Delta(\lambda_2)\bigr)=0$
by induction, the halves being generic with fewer than $n$ vertices. Hence
$\Delta(P)=\Delta(Z)$. At the anchor, Proposition~\ref{prop:anchor-values}
applies to $F$ and to $A$ (hypotheses (a) and (e),
Corollary~\ref{cor:A-lawful}):
for a zero anchor both values are $0$; for a loop anchor with parent $P'$
(a generic polygon with $n-1$ vertices) and insertion vertex $j$,
$F(Z)=\tau_j(P')F(P')$ and $A(Z)=\tau_j(P')A(P')$, and $\Delta(P')=0$ by
induction. So $\Delta(Z)=0$ and $\Delta(P)=0$.
\end{proof}
```

## thm:comparison — PROVE

reference/SM/sm-6-comparison.tex:299–302

```tex
\begin{theorem}[comparison]\label{thm:comparison}
Assume Hypothesis~R. Then $C(P)=A(P)$ for every generic polygon $P$.
\status{new (assembly; Proposition~\ref{prop:C-silent}, Theorems~\ref{thm:C-S3} and~\ref{thm:C-S7} refereed; Proposition~\ref{prop:C-chamber} and Lemma~\ref{lem:corner-values} held; Theorem~\ref{thm:C-soft} new (round~4), unrefereed; Theorem~\ref{thm:uniqueness} new; conditional on Hypothesis~R; round~5: hypothesis (d) discharged by citing Hypothesis~\ref{hyp:R} by label, so that the ordering instrument records the consumption, F-25-160)}
\end{theorem}
```

reference/SM/sm-6-comparison.tex:303–311

```tex
\begin{proof}
$C$ satisfies (a)--(f) of Theorem~\ref{thm:uniqueness}: (a)
Propositions~\ref{prop:C-chamber}, \ref{prop:C-silent}; (b)
Theorem~\ref{thm:C-S3}; (c) Theorem~\ref{thm:C-S7}; (d) Hypothesis~\ref{hyp:R}; (e)
Theorem~\ref{thm:C-soft}; (f) Lemma~\ref{lem:corner-values}(i)
gives corner coefficient $1$ for either oriented triangle. Its only
decomposition is empty, so Definition~\ref{def:C} gives $-1$ when
$\ell=3$ and $+1$ when $\ell=0$, as required.
\end{proof}
```

## cor:C-inherits — PROVE

reference/SM/sm-6-comparison.tex:313–319

```tex
\begin{corollary}[laws inherited by $C$]\label{cor:C-inherits}
Under Hypothesis~R, $C$ satisfies every identity of
Corollary~\ref{cor:A-lawful} on the domains stated there, in particular
the cusp law
$C(P_{\rm loop})-C(P_{\rm no})=-\kappa\,C(P(0)\setminus j)$.
\status{new (printed in round~1, C013; restricted to Corollary~\ref{cor:A-lawful}, F-25-11; round~3: proof completed with the domain checks on bench~A's named step, adapted from the Codex proposal P-25-19, F-25-11)}
\end{corollary}
```

reference/SM/sm-6-comparison.tex:320–369

```tex
\begin{proof}
Theorem~\ref{thm:comparison} identifies $C$ with $A$ on every generic
polygon, and Definition~\ref{def:C} defines $C$ on generic polygons only;
so before $C=A$ is substituted in an identity of
Corollary~\ref{cor:A-lawful}, every argument of that identity must be
shown generic. The two sides of a wall germ are generic by
Definition~\ref{def:germ}. At a simple flat wall the deletion
$P(0)\setminus j$ is generic by Lemma~\ref{lem:children}(i), and at a
simple vertex--edge wall both halves are generic by
Lemma~\ref{lem:children}(ii). The soft family $P_\varepsilon$ is generic
for all sufficiently small $\varepsilon>0$ in every sector by
Lemma~\ref{lem:soft-generic}. Reversal permutes the vertex triples and
preserves the edge segments, so it preserves (G1) and (G2). The two
triangles $K_{\pm1}$ are generic by Lemma~\ref{lem:star-generic}(iii).

For the cusp law let the simple cusp wall be at $j$ and write
$A=\mu_{j-1}(0)$, $M=\mu_j(0)$ and $B=\mu_{j+1}(0)$. The deletion
$Q=P(0)\setminus j$ has the vertices $\mu_i(0)$, $i\neq j$, and its edges
are the parent edges $E_i(0)$, $i\notin\{j-1,j\}$, together with the fused
edge $[A,B]$; it satisfies (G1) by the hypothesis of the cusp law. For (G2):
by Definition~\ref{def:walls}(K) the three points are collinear with $M$
outside the closed segment $[A,B]$, so $[A,B]$ is contained in the longer of
$[A,M]=E_{j-1}(0)$ and $[M,B]=E_j(0)$, and its relative interior in the
relative interior of that edge. Suppose three distinct edges of $Q$ had a
common point in their relative interiors. Two adjacent edges of $Q$ are not
collinear, by (G1) for $Q$, and so meet only at their common vertex; hence
the three edges are pairwise remote in $Q$. Send the fused edge, if it is
among them, to the longer parent edge containing it, and every other edge
to itself. This map is injective, since neither $E_{j-1}(0)$ nor $E_j(0)$
is an edge of $Q$, and the common point lies in the relative interiors of
the three image edges. The image edges are pairwise remote in $P(0)$: two
surviving edges are adjacent in $P(0)$ exactly when they share a vertex,
which is a vertex of $Q$, hence exactly when they are adjacent in $Q$; and
the parent neighbours of the longer cusp edge are the other cusp edge,
which is not an edge of $Q$, and one of the two edges of $Q$ adjacent to
the fused edge, both excluded because the three edges are pairwise remote
in $Q$. This is a point in the relative interiors of three pairwise remote
edges of the centre, contrary to $Z_{\rm c}=\varnothing$ in
Definition~\ref{def:walls}(K). Thus $Q$ is generic; the argument does not
require the cusp to be empty.

Now apply each identity of Corollary~\ref{cor:A-lawful} to its stated
arguments and substitute $C=A$ at every one of them, including the
deletions and halves just checked. For a chamber-side identity each
sufficiently small punctured side lies in one generic chamber, on which
$C=A$ holds pointwise, so the constant side values of $C$ and of $A$
agree; no value at the wall centre and no limit is used. This gives every
identity for $C$ on the domain stated in Corollary~\ref{cor:A-lawful},
including the displayed cusp law.
\end{proof}
```

## CV:def:polygon — DEFINE

reference/R/CV/d1_setup.tex:8–20

```tex
\begin{definition}[polygon]\label{def:polygon}
Let $n\geq3$. A \emph{polygon} on $n$ vertices is a tuple
$P=(p_1,\dots,p_n)\in(\mathbb{R}^2)^n$ with $p_{i+1}\neq p_i$ for every $i$,
indices read cyclically modulo $n$ throughout. Its \emph{edges} are the closed
segments $e_i=[p_i,p_{i+1}]$ and its \emph{edge directions} are
$d_i=p_{i+1}-p_i\in\mathbb{R}^2\setminus\{0\}$. Two edges are \emph{consecutive}
if their index sets meet, and \emph{remote} otherwise. An edge is \emph{remote
to a vertex} $p_M$ when it is remote to both edges incident to $M$ --- the
stronger of the two possible readings, and the one every consumer of the phrase
uses: it excludes an edge that merely avoids $p_M$ while sharing a vertex with
one of its edges. We write
$\det(u,v)=u_1v_2-u_2v_1$.
\end{definition}
```

## CV:def:regular — DEFINE

reference/R/CV/d1_setup.tex:22–40

```tex
\begin{definition}[principal turns and the regular locus]\label{def:regular}
\begin{enumerate}
\item[(A)] Let $L$ be a closed polygon with corners $q_0,\dots,q_{c-1}$ and edge directions
$\delta_i=q_{i+1}-q_i$. The \emph{principal turn} at $q_i$ is the unique
$\tau_i\in(-\pi,\pi)$ with
$\cos\tau_i=\frac{\langle\delta_{i-1},\delta_i\rangle}{|\delta_{i-1}||\delta_i|}$
and $\sgn\tau_i=\sgn\det(\delta_{i-1},\delta_i)$. It exists precisely when
$\delta_i$ is not a negative multiple of $\delta_{i-1}$: if
$\det(\delta_{i-1},\delta_i)\neq0$ it is nonzero, and if $\delta_i$ is a
positive multiple of $\delta_{i-1}$ it is $0$. The excluded case
$\delta_i\in\mathbb R_{<0}\delta_{i-1}$ is the \emph{kink}, where the two
candidate values $\pm\pi$ are both excluded from the open interval.
\item[(B)] The \emph{regular locus} $\mathcal R_n\subseteq(\mathbb R^2)^n$ is the set of
$P=(p_1,\dots,p_n)$ with $d_i\neq0$ for all $i$ and $d_{i+1}\neq-\lambda d_i$
for all $i$ and all $\lambda>0$: nonzero edges and no consecutive pair that
doubles back. Equivalently, every principal turn of
clause~(A) exists.
\end{enumerate}
\end{definition}
```

## CV:def:guarded — DEFINE

reference/R/CV/d1_setup.tex:42–218

```tex
\begin{definition}[the guarded list $\mathcal G$]\label{def:guarded}
Fix $n$. The \emph{guarded list} is a finite family of real polynomial functions
on $(\mathbb R^2)^n$, indexed once and for all by combinatorial data that does
not depend on the configuration. Write $d_i=p_{i+1}-p_i$ and, for an edge index
$e$, write $\ell_e(x)=\det(d_e,\,x-p_e)$ for the affine form vanishing on the
line of $e$, with coefficient row
$\bigl(A_e,B_e,C_e\bigr)=\bigl(-d_{e,2},\;d_{e,1},\;d_{e,2}p_{e,1}-d_{e,1}p_{e,2}\bigr)$,
so that $\ell_e(x)=A_ex_1+B_ex_2+C_e$.

\emph{Unconditional members.}
\begin{enumerate}
\item[(G1)] $\mathrm{G1}_i=\det(d_{i-1},d_i)$, for every $i\in\{1,\dots,n\}$.
\item[(G2)] $\mathrm{G2}_{e,i}=\ell_e(p_i)=\det(d_e,\,p_i-p_e)$, for every edge
index $e$ and every $i\notin\{e,e+1\}$.
\end{enumerate}

\emph{Activation.} Two remote edges $e,f$ are \emph{defined} to cross when
\[
   \mathrm{G2}_{e,f}\,\mathrm{G2}_{e,f+1}<0
   \quad\text{and}\quad
   \mathrm{G2}_{f,e}\,\mathrm{G2}_{f,e+1}<0 ,
\]
a condition on unconditional members alone. The products are \emph{strict}, and
that is a decision, not a formality: an earlier revision wrote
$\sgn\neq\sgn$, which is undecided exactly where it is consumed. At a wall
point one of the four members vanishes, and the three available readings
disagree there. The strict product makes the pair \emph{inactive} at such a
point; a three-valued $\sgn\in\{-1,0,+1\}$ would make it active, and then the
sliding bundle of the wall dictionary of
Section~\ref{sec:dictionary} would be $\{\mathrm{G2},\mathrm{G4}\}$ rather than
the singleton that dictionary's item~(iii) records;
and the shipped evaluator's test treats a zero as negative, which is asymmetric
between the two edges. The strict product is taken, and the divergence from the
evaluator is recorded here rather than left silent. What can be said about its
consequences is scoped to this document: every statement below evaluates $X_1$
at \emph{generic} polygons, where no $\mathrm{G2}$ vanishes and the two
readings agree, so no statement below depends on which reading the code takes.
What an external caller passes to that code is outside this document's claims
--- a caller that hands it a collinear configuration reaches the divergence, and
nothing here says otherwise. An earlier revision wrote that the code "never
reaches" such a configuration, which is a claim about the code's callers and not
about this document. It is the sign
condition, and not the geometric phrase ``their relative interiors meet'', that
every consumer below reads and that the shipped evaluator computes.

The two agree wherever the four members are nonzero, and there they say that
each edge has its two endpoints strictly on opposite sides of the other's line,
which for segments is exactly a transverse interior crossing. They do
\emph{not} agree everywhere in $\mathcal R_n$, and an earlier revision wrote
``exactly when'' as though they did: two collinear overlapping remote edges have
meeting relative interiors while all four members vanish, so the sign condition
fails. Such a configuration is not generic --- those vanishing members are
unconditional, hence relevant --- so the generic locus defined below and the
discriminant $\mathcal D$ of Section~\ref{sec:dictionary} are the same sets under
either reading, and no statement
below changes. What changes is that activation is now decided by a formula.

\emph{Conditional members.}
\begin{enumerate}
\item[(G5)] $\mathrm{G5}_{e,f}=\det(d_e,d_f)$, for every pair of remote edge
indices with $1\leq e<f\leq n$ as integers --- the comparison is between the
integer representatives $1,\dots,n$ of the edge indices and not a cyclic
comparison, there being no such thing; adjacency and remoteness continue to be
read modulo $n$. This fixes one \emph{ordered representative} per pair, and an
unordered pair will not do, because
$\det(d_f,d_e)=-\det(d_e,d_f)$ and the family is used where signs are read, in
the sign-change condition that defines a transversal event below; \emph{active} when $e$
and $f$ cross. Making it
conditional rather than unconditional is a fidelity point: the specification
guards the turn at a smoothing site, and a smoothing site exists only where two
edges cross. Demanding $\det(d_e,d_f)\neq0$ for a pair that does not cross
would shrink the generic locus below the specification's and exclude polygons
the laws are stated about.
\item[(G3)] $\mathrm{G3}_{e,f,g}=\det\begin{pmatrix}A_e&B_e&C_e\\
A_f&B_f&C_f\\ A_g&B_g&C_g\end{pmatrix}$, the rows being the line-coefficient
rows bound at the head of this definition, one for each of $e$, $f$ and $g$;
for every triple of pairwise remote edges $1\leq e<f<g\leq n$, ordered by their
integer representatives; \emph{active} when $e,f,g$ pairwise cross. It vanishes exactly when the
three lines share a point of the projective plane: either they are concurrent in
the plane, or all three are parallel. A parallel \emph{pair} with a transverse
third does \emph{not} make it vanish --- an earlier revision said it did, and the
configuration $p_0=(0,0)$, $p_1=(1,0)$, $p_2=(0,1)$, $p_3=(1,1)$, $p_4=(2,-1)$,
$p_5=(2,2)$ refutes it, the rows of $e_0,e_2,e_4$ being $(0,1,0)$, $(0,1,-1)$
and $(-3,0,6)$ with determinant $3$. On the active domain the three edges
pairwise cross, so no two of the lines are parallel and the vanishing is exactly
a concurrence at a finite point, which is what every consumer reads.
\item[(G4)] $\mathrm{G4}_{e;f,g}
=\det(d_f,\,p_f-p_e)\,\det(d_g,d_e)-\det(d_g,\,p_g-p_e)\,\det(d_f,d_e)$,
for every edge $e$ and every pair of edges remote to $e$ with
$1\leq f<g\leq n$ as integers --- again the comparison is between integer
representatives, and again one ordered representative per pair, since
$\mathrm{G4}_{e;g,f}=-\mathrm{G4}_{e;f,g}$; \emph{active} when $f$ and $g$ both
cross $e$.

\emph{Normalization of cyclic aliases.} Edge indices are read cyclically, so
one edge has many names: $e_0$, $e_n$ and $e_{2n}$ are the same edge. Every
comparison of indices in this document --- the $f<g$ of (G5), the $e<f<g$ of
(G3), the $f<g$ of (G4) --- is a comparison of \emph{representatives}: each
index is first reduced to the unique integer in $\{1,\dots,n\}$ naming that
edge, and the reduced integers are compared. Adjacency, remoteness and the
edges themselves are unaffected by the reduction; only the choice of ordered
representative depends on it, and only that choice carries a sign.

\emph{The two accessors.} Consumers meet a pair of edges in the order the
geometry gives, which after reduction may be the reverse of the representative
order. Let $f,g$ be distinct edges remote to $e$, presented in some order and
possibly under aliases, and let $\bar f,\bar g\in\{1,\dots,n\}$ be their
representatives. Define
\[
   \mathrm{G4}\langle e;f,g\rangle
   =\mathrm{G4}_{e;\min(\bar f,\bar g),\,\max(\bar f,\bar g)}\in\mathcal G,
   \qquad
   \epsilon(f,g)=\begin{cases}+1,&\bar f<\bar g,\\ -1,&\bar f>\bar g,\end{cases}
\]
the first a \emph{member-valued} accessor --- it returns an element of the
guarded list, the one indexed by the ordered representative pair --- and the
second an \emph{orientation sign} in $\{\pm1\}$, a constant of the index data
and not a function of the configuration. Their product
\[
   \widehat{\mathrm{G4}}_{e;f,g}
   =\epsilon(f,g)\cdot\mathrm{G4}\langle e;f,g\rangle
\]
is the \emph{oriented value}: a real polynomial function on $(\mathbb R^2)^n$,
antisymmetric in the ordered pair, equal to the member up to the orientation
sign.

The two are used in different places and the distinction is not cosmetic.
Every set of guarded predicates formed below --- in particular the zero set of
an event, defined later in this section --- is a set of \emph{members} of
$\mathcal G$, and membership there is by \emph{index}: the element is
$\mathrm{G4}\langle e;f,g\rangle$, the member indexed by the ordered
representative pair, and not the oriented value, which when $\epsilon=-1$ is
that member's negative and is indexed by nothing. The distinction is one of
indexing and not of polynomials, and the difference matters: as polynomials a
negated member can coincide with another member, since for three pairwise
remote edges $\mathrm{G4}_{e;f,g}=-\mathrm{G3}_{e,f,g}$ --- an identity of
polynomials, proved in the dictionary section where the canonical factors are
analysed --- so $-\mathrm{G4}_{e;f,g}$ is the polynomial $\mathrm{G3}_{e,f,g}$,
which \emph{is} a member. An earlier revision said the
oriented value "is not a member of $\mathcal G$ when $\epsilon=-1$", which as a
statement about polynomials is false.

Statements about vanishing, activation and relevance are statements about the
member and are insensitive to the presentation order. Statements about
\emph{sign} --- a sign change across an event, a factorization whose two sides
must agree in sign, the order of two crossings along an edge --- read the
oriented value, and there the orientation sign $\epsilon$ is carried
explicitly. Both kinds occur below, and the next display is of the first kind.

Two illustrations of the reduction, both used below. At $j=0$ the pair
$(e_{j-1},e_j)$ is $(e_{n-1},e_n)$, whose representatives are already
increasing: $\epsilon=+1$, and the oriented value is the member. At $j=1$ it is
$(e_0,e_1)$, whose representatives are $(n,1)$: $\epsilon=-1$, and the member
is $\mathrm{G4}_{e;1,n}$. An earlier revision wrote
$\mathrm{G4}_{h;e_{j-1},e_j}$ where the reduction makes that name empty and the
sign opposite, and a later one placed the wrap at $j=0$, where there is none. When active, both
$\det(d_f,d_e)$ and $\det(d_g,d_e)$ are nonzero, the crossing of $e$ with $f$
sits at the parameter $t_f=\det(d_f,p_f-p_e)/\det(d_f,d_e)$ along $e$, and, for
the ordered representative pair $\bar f<\bar g$ that indexes the member,
\[
   \mathrm{G4}_{e;\bar f,\bar g}
      =(t_{\bar f}-t_{\bar g})\det(d_{\bar f},d_e)\det(d_{\bar g},d_e),
\]
so its vanishing is exactly a tie $t_{\bar f}=t_{\bar g}$ in the order of
crossings along $e$. Presented in the other order the same identity holds for the oriented value,
both sides changing sign. Two kinds of consumer read this display, and they read
different things. Those that need only the \emph{vanishing} --- the two collision arguments
below, in the chamber-invariance proposition and in the silence lemma --- read
the member, and the presentation order is irrelevant to them. Those that
need the \emph{sign} --- the order of the two crossings along $e$, and the
bigon-bundle computation of Section~\ref{sec:dictionary} --- read the oriented
value $\widehat{\mathrm{G4}}_{e;f,g}=\epsilon(f,g)\,\mathrm{G4}\langle
e;f,g\rangle$ and carry $\epsilon$. An earlier revision said the vanishing was
"the only reading the consumers of this display take", which the sign-reading
sites contradict.
\end{enumerate}
\end{definition}
```

## CV:def:generic — DEFINE

reference/R/CV/d1_setup.tex:220–237

```tex
\begin{definition}[relevant members, generic polygons and chambers]\label{def:generic}
\begin{enumerate}
\item[(A)] A member of $\mathcal G$ is \emph{relevant} at a polygon $P$ if it is
unconditional, or if it is conditional and active at $P$
(Definition~\ref{def:guarded}). A polygon $P$
(Definition~\ref{def:polygon}) is \emph{generic} if every member relevant at
$P$ is nonzero at $P$; equivalently, if every unconditional member of
$\mathcal G$ is nonzero at $P$ and every conditional member that is active at
$P$ is nonzero at $P$. We write $\mathcal U_n$ for the set of generic polygons
on $n$ vertices.

\item[(B)] A \emph{chamber} is a connected component of the set $\mathcal U_n$ of generic
polygons on $n$ vertices (clause~(A)). It is \emph{not} in
general a component of the set where every member of $\mathcal G$ is nonzero:
a conditional member that is inactive may vanish, or vanish identically, at a
perfectly generic polygon, and nothing in this document asks it not to.
\end{enumerate}
\end{definition}
```

## CV:def:diagrammatic — DEFINE

reference/R/CV/d1_setup.tex:315–344

```tex
\begin{definition}[diagrammatic polygon]\label{def:diagrammatic}
A polygon $P$ is \emph{diagrammatic} if its self-intersections are finitely
many, each of them an isolated transverse crossing of two edges with exactly two
preimages on the traversal circle, no two of them sharing an image or a
preimage, none of them at a corner, and no vertex of $P$ lying on an edge not
incident to it. The clause about preimages and shared images is not implied by
the others, and an earlier revision omitted it: the polygon
$((-3,0),(3,0),(0,-3),(0,3),(-2,-2),(2,2))$ has its edges $e_0,e_2,e_4$ meeting
pairwise transversally --- the three determinants are $36$, $24$, $-24$ --- at
the \emph{single} point $(0,0)$, so three strands pass through one point, and the
$2m$-letter Gauss word does not exist.

Every generic polygon is diagrammatic: the (G2) members forbid a vertex on a
remote edge, the (G5) members make each crossing transversal, and a triple point
would make a (G3) member vanish while all three pairs cross, so that member is
active, hence relevant, hence nonzero. So is the polygon at a simple positive
flat wall, whose only degeneracy is a vanishing turn with the middle vertex
\emph{inside} the segment. That last qualification matters: at an exterior
collinear vertex the two incident edges overlap and the far one carries the
middle vertex, as in $((0,0),(2,0),(1,0),(0,1))$, which is not diagrammatic ---
an earlier revision said "any polygon whose only degeneracy is a vanishing
turn".

The class is named because the Gauss word, the interlacement graph, the
independent sets, the undominated sets, the residual pieces and their diagrams
are read off a diagrammatic polygon and need nothing more; genericity is what
$X_1$ needs, through the guards, and is a strictly stronger condition. Three
sections use exactly this class: the flat law at its wall, the rounding lemma,
and the carrier floor.
\end{definition}
```

## CV:def:interlace — DEFINE

reference/R/CV/d1_setup.tex:346–353

```tex
\begin{definition}[interlacement graph]\label{def:interlace}
The \emph{interlacement graph} $G_P$ has vertex set $[m]=\{1,\dots,m\}$, with
$c\sim c'$ if and only if exactly one of the two occurrences of $c'$ lies between
the two occurrences of $c$ in the Gauss word. (The relation is symmetric.) We
write $\Ind(G_P)$ for the set of independent sets of $G_P$, including
$\varnothing$, and $N_{G_P}(S)$ for the set of vertices adjacent to some element
of $S$.
\end{definition}
```

## CV:def:smoothing — DEFINE

reference/R/CV/d1_setup.tex:355–360

```tex
\begin{definition}[oriented smoothing]\label{def:smoothing}
For $S\in\Ind(G_P)$, the \emph{oriented smoothing of $P$ along $S$} replaces, at
each double point of $S$, the two transversally crossing arcs by the two arcs
that respect the orientation of $P$ and do not cross. The result is a disjoint
union of closed oriented curves, called the \emph{carriers} of $S$.
\end{definition}
```

## CV:lem:carriers — PROVE

reference/R/CV/d1_setup.tex:362–383

```tex
\begin{lemma}[the carriers of a support]\label{lem:carriers}
Let $P$ be diagrammatic (Definition~\ref{def:diagrammatic}) and
$S\in\Ind(G_P)$ --- genericity is not needed here and an earlier revision
assumed it; what the argument reads is the Gauss word. Let $\Gamma$ be the
\emph{traversal circle}: an abstract oriented circle
together with the traversal map $\Gamma\to\mathbb R^2$ that runs once around
$P$, on which each double point of $P$ has exactly two preimages, so that
$\Gamma$ carries $2m$ marked points. (No coordinate is placed on $\Gamma$; in
particular the crossing-free case $m=0$ is allowed, with no marked points.) Then:
\begin{enumerate}
\item[(i)] the oriented smoothing of $P$ along $S$ has exactly $|S|+1$ carriers;
\item[(ii)] the assignment of traversal points to carriers is \emph{non-crossing}:
there are no four points $u_1,u_2,u_3,u_4$ of $\Gamma$ in this cyclic order,
none of them a preimage of an element of $S$, with $u_1,u_3$ on one carrier and
$u_2,u_4$ on a different carrier;
\item[(iii)] if $c\in[m]\setminus S$ is non-adjacent in $G_P$ to every element of
$S$, then both occurrences of $c$ lie on the same carrier;
\item[(iv)] if $H$ is a connected component of the induced graph
$G_P\bigl[[m]\setminus(S\cup N_{G_P}(S))\bigr]$, then there is exactly one
carrier on which both occurrences of every $c\in H$ lie.
\end{enumerate}
\end{lemma}
```

reference/R/CV/d1_setup.tex:384–448

```tex
\begin{proof}
Induct on $|S|$, proving (i), (ii) and (iii) together; the induction is on the
conjunction, and (iii) is what makes the step go through.

\emph{Base $S=\varnothing$.} There is one carrier, namely $P$ itself: (i) and
(iii) are immediate and (ii) is vacuous, all four points lying on that one
carrier.

\emph{Step.} Let $|S|\geq1$, fix $c\in S$ and put $S'=S\setminus\{c\}$, so
$S'\in\Ind(G_P)$ and $|S'|=|S|-1$. Since $S$ is independent, $c$ is non-adjacent
to every element of $S'$, so the inductive hypothesis (iii) applies to $S'$ and
$c$: both occurrences of $c$ lie on one and the same carrier $L$ of $S'$. Write $x_1,x_2\in\Gamma$ for its two preimages; they cut $\Gamma$ into two
arcs $\alpha,\beta$.

(i) Oriented smoothing at $c$ replaces the two crossing arcs at that double point
by the two non-crossing arcs respecting the orientation, which severs $L$ at
$x_1$ and $x_2$ and reconnects it as the two closed curves carried by
$L\cap\alpha$ and $L\cap\beta$; every other carrier of $S'$ is untouched, since
$c$ meets none of them. So the number of carriers rises by exactly one, from
$|S'|+1$ to $|S|+1$.

(ii) The carriers of $S$ are those of $S'$ with the single block $L$ replaced by
the two blocks $L\cap\alpha$ and $L\cap\beta$. Suppose $u_1,u_2,u_3,u_4$ in cyclic
order violate (ii) for $S$, with $u_1,u_3$ on a carrier $A$ and $u_2,u_4$ on a
carrier $B\neq A$, none of the $u_k$ an occurrence of an element of $S$. If
neither $A$ nor $B$ is one of the two new blocks, the same four points violate
(ii) for $S'$, contradicting the inductive hypothesis. If exactly one of them, say
$A$, is a new block, then $A\subseteq L$ and $B$ is a carrier of $S'$ distinct
from $L$, so the four points again violate (ii) for $S'$ with $L$ in place of $A$.
If both are new blocks, then $\{A,B\}=\{L\cap\alpha,\,L\cap\beta\}$, so
$u_1,u_3\in\alpha$ and $u_2,u_4\in\beta$ (or the same with $\alpha,\beta$
exchanged). None of the $u_k$ equals $x_1$ or $x_2$, so each of the four cyclic
transitions $u_1\to u_2\to u_3\to u_4\to u_1$ passes from $\alpha$ to $\beta$ or
back, and every such passage contains one of the two points $x_1,x_2$ in its
interior. Four disjoint open arcs would then each contain a point of the
two-element set $\{x_1,x_2\}$, which is impossible

(iii) Let $c''\in[m]\setminus S$ be non-adjacent to every element of $S$, hence to
every element of $S'$. By the inductive hypothesis both occurrences of $c''$ lie
on one carrier $L''$ of $S'$. If $L''\neq L$ then $L''$ is a carrier of $S$ as
well and the claim holds. If $L''=L$, use that $c''$ is non-adjacent to $c$:
exactly one occurrence of $c$ lying between the two occurrences of $c''$ is what
adjacency means, so non-adjacency puts both occurrences of $c''$ strictly inside
the same arc, $\alpha$ or $\beta$. Hence both lie on the same one of
$L\cap\alpha$, $L\cap\beta$.

(iv) Put $U=[m]\setminus(S\cup N_{G_P}(S))$. For $c\in H$, clause~(iii) puts
both occurrences of $c$ on one carrier, which we call $L(c)$. If $c,c'\in H$
are adjacent in $G_P[U]$, exactly one occurrence of $c'$ lies between the two
occurrences of $c$. Thus their four occurrences alternate on $\Gamma$, and none
is an occurrence of an element of $S$. If $L(c)\neq L(c')$, those four points
violate clause~(ii). Hence $L(c)=L(c')$. The assignment $c\mapsto L(c)$ is
therefore constant on every edge of the connected graph $H$, hence constant on
$H$.

It is one carrier, not two, because it is a function. Uniqueness is immediate:
the carriers partition $\Gamma$, so distinct carriers are disjoint \emph{as
subsets of the traversal circle} --- not as subsets of the plane, where two
distinct carriers can meet only at \emph{dominated} crossings, those of
$N_{G_P}(S)$. At a crossing outside $S\cup N_{G_P}(S)$ both visits lie on one
carrier by clause~(iii), so distinct carriers cannot meet there, and the
crossings of $S$ are smoothed. An earlier revision said distinct carriers meet
at every shared double point \emph{outside} $S\cup N_{G_P}(S)$, which names
exactly the set where they cannot.
\end{proof}
```

## CV:lem:carrierword — PROVE

reference/R/CV/d1_setup.tex:450–459

```tex
\begin{lemma}[smoothing preserves the induced cyclic order]\label{lem:carrierword}
Let $C$ be a closed curve with a traversal circle $\Gamma_C$ and finitely many
transverse double points, and let $S$ be a set of them no two of which
interlace. Then each closed curve produced by smoothing $C$ along $S$ traverses
the marked points of $\Gamma_C$ lying on it in the cyclic order they have on
$\Gamma_C$.

In particular, taking $C=P$ generic and $S\in\Ind(G_P)$, each carrier of $S$
traverses the marked points lying on it in the order induced from $\Gamma$.
\end{lemma}
```

reference/R/CV/d1_setup.tex:460–485

```tex
\begin{proof}
Induction on $|S|$. If $S=\varnothing$ the only curve is $C$ itself, traversing
$\Gamma_C$, and there is nothing to prove.

Let $|S|\geq1$ and pick $c\in S$, with traversal preimages $c_1,c_2$. Smoothing
$c$ alone joins the incoming branch at $c_1$ to the outgoing branch at $c_2$ and
the incoming at $c_2$ to the outgoing at $c_1$, so the two resulting closed
curves traverse exactly the two arcs $\Gamma_1=(c_1,c_2)$ and
$\Gamma_2=(c_2,c_1)$ of $\Gamma_C$, each in the order induced from $\Gamma_C$;
no marked point changes arcs and none is visited twice.

Every other $e\in S$ is nonadjacent to $c$, so its two preimages do not separate
$c_1$ from $c_2$: both lie in $\Gamma_1$ or both in $\Gamma_2$. Hence
$S\setminus\{c\}$ is partitioned into two sets, one carried by each of the two
closed curves, no two members of either interlacing; and the remaining
smoothings are performed inside those two curves separately. Each is a closed
curve with a traversal circle and finitely many transverse double points, which
is the hypothesis of this lemma, so the induction hypothesis applies to each and
gives the induced order there; composing with the previous paragraph gives it on
$\Gamma_C$.

The statement was restated at this generality because the induction applies it
to curves obtained by smoothing, which are not polygons; an earlier revision
quantified it over generic polygons only, and the peer was right that its own
proof then stepped outside its domain.
\end{proof}
```

## CV:def:wind — DEFINE

reference/R/CV/d1_setup.tex:487–512

```tex
\begin{definition}[corner, turn sign, and $\wind$]\label{def:wind}
Let $P$ be \emph{generic} and $S\in\Ind(G_P)$ --- the binders under which the
definition is read, and which an earlier revision left to the ambient
subsection, whose standing hypothesis is only that $P$ is diagrammatic. A
\emph{corner} of a carrier of $S$ is either a vertex $p_i$ of $P$ traversed by
it or a smoothing site of $S$ traversed by it. At each corner the carrier turns
\emph{left} or \emph{right} according to the sign of the determinant of the
incoming and outgoing directions, which under genericity is nonzero: at a
vertex by (G1), unconditional and hence relevant, at a smoothing site by (G5),
active at a crossing. On a merely diagrammatic polygon the vertex clause is
false --- $((0,0),(1,0),(2,0),(0,1))$ is diagrammatic and its turn at $p_2$ is
exactly zero --- which is why the generic binder is part of this definition and
not decoration. A carrier is \emph{uniform} if all its corners turn the
same way and \emph{mixed} otherwise. Its \emph{weight} is
\[
   \mathrm{wt}(L)=\begin{cases}
     +1, & L \text{ uniform, all turns right},\\
     (-1)^{c(L)}, & L \text{ uniform, all turns left, } c(L)=\#\text{corners},\\
     0, & L \text{ mixed},
   \end{cases}
\]
and $\wind(S)=\prod_{L}\mathrm{wt}(L)$, the product over the $|S|+1$ carriers of
$S$. In particular $\wind(S)\neq0$ forces every carrier of $S$ to be
uniform: $\wind(S)$ is a product of integers, a product of integers is
nonzero only if every factor is, and the weight of a mixed carrier is $0$.
\end{definition}
```

## CV:def:pieces — DEFINE

reference/R/CV/d1_setup.tex:514–518

```tex
\begin{definition}[undominated set and residual pieces]\label{def:pieces}
For $S\in\Ind(G_P)$ put $U(S)=[m]\setminus\bigl(S\cup N_{G_P}(S)\bigr)$. The
\emph{residual pieces} of $S$ are the connected components
$H\in\pi_0\bigl(G_P[U(S)]\bigr)$ of the induced subgraph on $U(S)$.
\end{definition}
```

## CV:def:record — DEFINE

reference/R/CV/d1_setup.tex:522–550

```tex
\begin{definition}[record, and record isomorphism]\label{def:record}
A \emph{record} consists of an oriented circle $\Gamma$; a finite subset
$V\subset\Gamma$ of \emph{marked points}; a partition of $V$ into two-element
sets, the \emph{double points}; for each double point a designation of one of
its two points as the \emph{over} position and the other as the \emph{under}
position; and for each double point a \emph{sign} in $\{\pm1\}$. The record of a
link diagram is the one obtained by taking $\Gamma$ to be its traversal circle,
$V$ the preimages of its crossings, the partition the crossing correspondence,
and the over/under and sign data those of the diagram.

A \emph{record isomorphism} from $(\Gamma,V,\dots)$ to $(\Gamma',V',\dots)$ is a
bijection $\varphi:V\to V'$ that
\begin{enumerate}
\item[(a)] preserves the cyclic order: for all $v_1,v_2,v_3\in V$ occurring in
that cyclic order on $\Gamma$, the points $\varphi v_1,\varphi v_2,\varphi v_3$
occur in that cyclic order on $\Gamma'$;
\item[(b)] carries double points to double points;
\item[(c)] carries over positions to over positions and under to under;
\item[(d)] preserves signs.
\end{enumerate}
Condition (a) says exactly that $\varphi$ extends to an orientation-preserving
homeomorphism $\Gamma\to\Gamma'$ carrying $V$ onto $V'$, and any two such
extensions are isotopic through such homeomorphisms: an orientation-preserving
circle homeomorphism is determined up to isotopy by the cyclic-order-preserving
bijection it induces on a finite subset, the complementary arcs being carried to
the complementary arcs in the induced order and any two orientation-preserving
homeomorphisms of a closed arc rel endpoints being isotopic. Records are
\emph{isomorphic} when such a $\varphi$ exists; the relation is an equivalence.
\end{definition}
```

## CV:def:homfly — DEFINE

reference/R/CV/d1_setup.tex:552–563

```tex
\begin{definition}[HOMFLY--PT normalization]\label{def:homfly}
$P_H$ is normalized by the first two identities below; the third is their
consequence, obtained by applying the skein relation at a crossing between $L$
and a split unknot, and is displayed because it fixes the reader's convention
for a split component:
\begin{equation}
P(\bigcirc)=1,\qquad
aP(L_+)-a^{-1}P(L_-)=zP(L_0),\qquad
P(L\sqcup\bigcirc)=\frac{a-a^{-1}}{z}\,P(L).
\label{eq:homfly}
\end{equation}
\end{definition}
```

## CV:def:piecediagram — DEFINE

reference/R/CV/d1_setup.tex:565–590

```tex
\begin{definition}[piece diagram, positivity, writhe]\label{def:piecediagram}
For a diagrammatic parent $P$, the diagram of a residual piece $H$ is the parent
curve $P$ with every double
point outside $H$ erased --- the two strands drawn as passing without
interaction --- and every double point of $H$ resolved by the divide convention:
the branch whose direction $u_{\mathrm{over}}$ satisfies
$\det(u_{\mathrm{over}},u_{\mathrm{under}})>0$ passes over. Under this convention
every crossing of the diagram is positive, so its writhe is
$w(H)=|H|$, the number of double points of $H$. We write $P_H(a,z)$ for the
HOMFLY--PT polynomial of the link so presented, normalized as in
Definition~\ref{def:homfly}.

\emph{What ``erased'' means, stated once, and where the statement comes from.}
The evaluator that defines $X_1$ builds a piece's datum as the parent Gauss word
restricted to the crossings of $H$, in the parent's cyclic order, together with
the parent's per-crossing counter-clockwise half-edge order restricted to the
surviving half-edges and re-expressed in the restricted word's arc labels
(\texttt{sub\_word\_and\_rot},
\texttt{engines/polygon\_motivic/ruling\_dp\_statesum\_fin.py:28} of the shipped
code). So the datum is a word \emph{together with a rotation system}, not a bare
word, and the definition above is to be read as naming that pair.

To erase a double point is to omit it from that datum. The combinatorial shadow
of the datum --- the word with its over/under and signs and nothing else --- is
Definition~\ref{def:record}.
\end{definition}
```

## CV:lem:piececurve — PROVE

reference/R/CV/d1_setup.tex:592–610

```tex
\begin{lemma}[a residual piece is carried by an actual closed curve]
\label{lem:piececurve}
Let $P$ be diagrammatic (Definition~\ref{def:diagrammatic}),
$S\in\Ind(G_P)$, and let $H$ be a residual piece of $S$. Let $C_H$ be the closed
plane curve that the proof's own route constructs, and nothing else: smooth
every crossing of $S$ --- of $S$ \emph{only} --- so that the curve falls into
the $|S|+1$ carriers of $S$; take the one carrier that carries $H$, which is
unique by Lemma~\ref{lem:carriers}(iv); and apply to it Step 5's iteration,
smoothing at each step one double point outside $H$ and keeping the daughter
curve that carries $H$, which Step 5 shows is well defined. Then $C_H$ is a
closed plane curve whose double points are exactly the crossings of $H$ and
whose Gauss word is the parent word restricted to $H$ in the parent's cyclic
order.

This binding is the construction and not a description of its result. The
route above smooths nothing but $S$, so $H$ lies on one carrier before the
iteration begins, and each subsequent step preserves that. In particular that restricted word is realizable, and the datum of
Definition~\ref{def:piecediagram} is the datum of $C_H$.
\end{lemma}
```

reference/R/CV/d1_setup.tex:611–667

```tex
\begin{proof}
\emph{Step 1: a dominated crossing has its two visits on different carriers.}
Let $c\notin S$ interlace some $s\in S$. Smoothing $s$ alone splits the curve
into two closed curves traversing the two arcs $(s_1,s_2)$ and $(s_2,s_1)$ of
$\Gamma$, and $c$ interlacing $s$ means one visit of $c$ lies in each. Smoothing
the remaining elements of $S$ only ever splits: the carriers number $|S|+1$ by
Lemma~\ref{lem:carriers}(i), which is the count reached when every one of the
$|S|$ smoothings increases the component count, so none of them merges two
components. Hence the two visits of $c$ lie on different carriers.

\emph{Step 2: the double points of a carrier are exactly the undominated
crossings it carries.} A double point of a carrier $L$ is a crossing outside $S$
both of whose visits lie on $L$. Step 1 excludes the dominated ones, and
Lemma~\ref{lem:carriers}(iii) puts both visits of each undominated one on a
single carrier.

\emph{Step 3: a carrier's Gauss word is realizable and is a restriction.} A
carrier is a closed plane curve with transverse double points, so its Gauss word
is realizable, being read off an actual curve. By Step 2 its double points are
the undominated crossings it carries, and by Lemma~\ref{lem:carrierword} it
traverses them in the cyclic order they have on $\Gamma$. So the carrier's word
is the parent word restricted to those crossings.

\emph{Step 4: a residual piece interlaces nothing else in that word.} $H$ is a
connected component of $G_P[U(S)]$, so an undominated crossing interlacing a
member of $H$ lies in $H$; and $H$ lies on one carrier by
Lemma~\ref{lem:carriers}(iv).

\emph{Step 5: restricting to such a set is realizable, constructively.} Let $C$
be a closed plane curve and $K$ a nonempty set of its double points such that no
member of $K$ interlaces a double point outside $K$ \emph{and $K$ induces a
connected interlacement subgraph}. If $C$ has a double point $d$ outside $K$,
smooth it. The curve becomes two closed curves, traversing the two arcs of $d$.
Since $d$ interlaces no member of $K$, each member of $K$ has both visits in one
of those two arcs; and two members lying in different arcs have their visits in
disjoint arcs, so they do not interlace. Connectedness of $K$ therefore forces
all of $K$ into one arc, hence onto one of the two curves. Keep that one and
discard the other, which carries no member of $K$; the retained visits keep
their cyclic order by Lemma~\ref{lem:carrierword} applied to the single smoothed
chord. The hypotheses persist: $K$ is unchanged, so it is still connected, and
it still interlaces no surviving double point outside it. Each step removes at
least one double point outside $K$, so after finitely many steps the curve
$C_H$ has double points exactly $K$ and Gauss word the restriction.

The connectedness hypothesis is not decoration. Without it the step is false,
and the peer's exact witness is the word $d\,a\,a\,d\,b\,b$ with
$K=\{a,b\}$: neither $a$ nor $b$ interlaces $d$, yet $a$ lies inside the arc
$(d_1,d_2)$ and $b$ outside it, so $K$ is not on one side. A residual piece
supplies the hypothesis by Step 4, being a connected component.

Applying Step 5 to the carrier of $H$ with $K=H$, which Steps 3 and 4
licence --- Step 4 supplying both the non-interlacing and the connectedness
hypotheses --- performs exactly the statement's third operation and gives
$C_H$. Its rotation system at each surviving crossing is the carrier's,
which is the parent's, since smoothing at other points does not disturb the
half-edge order at a survivor; that is the second half of the datum.
\end{proof}
```

## CV:def:rot — DEFINE

reference/R/CV/d1_setup.tex:726–787

```tex
\begin{definition}[rotation number, computably]\label{def:rot}
Let $L$ be a closed polygon through corner points $q_0,\dots,q_{c-1}$, lying
in the regular locus $\mathcal R_c$ of Definition~\ref{def:regular}(B) ---
nonzero edges, no consecutive pair doubling back; equivalently, every
principal turn of Definition~\ref{def:regular}(A) exists --- and put
$\delta_i=q_{i+1}-q_i$. Choose $r\in\mathbb{R}^2$ with $\det(r,\delta_i)\neq0$
for all $i$; such $r$ exists because the $\delta_i$ are finitely many. Then
\[
   \rot(L)=\sum_{i}\epsilon_i,\qquad
   \epsilon_i=\begin{cases}
     +1,&\det(\delta_{i-1},\delta_i)>0,\ \det(\delta_{i-1},r)>0,\ \det(r,\delta_i)>0,\\
     -1,&\det(\delta_{i-1},\delta_i)<0,\ \det(\delta_{i-1},r)<0,\ \det(r,\delta_i)<0,\\
     0,&\text{otherwise.}
   \end{cases}
\]
All comparisons are exact sign tests of determinants: no angles and no
tolerances occur.

\emph{Why regularity is part of the definition.} The sum is independent of
the admissible $r$, and regularity is what makes it so; a vanishing turn is
harmless. First delete flat corners: if $\delta_i=\lambda\delta_{i-1}$ with
$\lambda>0$ then $\det(\delta_{i-1},\delta_i)=0$, so $\epsilon_i=0$ for every
$r$, and deleting $q_i$ merges the two edges into one of the same direction,
changing no other $\epsilon_j$, since every determinant a surviving term
reads is altered only by a positive scale. The deletion lands in
$\mathcal R_{c-1}$, and no polygon of any $\mathcal R_c$ is all-flat --- a
closed polygon with every turn flat would traverse one direction forever and
could not close --- so finitely many deletions reach a polygon with every
$\det(\delta_{i-1},\delta_i)\neq0$ and the same sum. On that polygon,
$\epsilon_i$ depends on $r$ only through $\det(\delta_{i-1},r)$ and
$\det(r,\delta_i)$, so it moves only as $r$ crosses the line of
$\delta_{i-1}$ or of $\delta_i$. Crossing the line of $\delta_j$ moves
exactly $\epsilon_j$ and $\epsilon_{j+1}$, and in each of the four sign cases
one gains what the other loses, so the sum is unchanged; if several edges
share that line they are pairwise nonconsecutive --- consecutive ones would
be flat or doubling back, and both are gone --- so their pairs are disjoint
and each is preserved separately. Regularity is not decoration: the polygon
$((-7,4),(-9,6),(9,-9),(3,3),(9,-9),(-7,-7),(-7,-6))$, whose consecutive
pair $(-6,12),(6,-12)$ doubles back, returns both $-1$ and $0$ at admissible
rays.

\emph{Direction loops and smooth curves.}
For a continuous loop $T\colon\mathbb R/\mathbb Z\to S^1$, a
\emph{tangent-angle lift} at a seam is a continuous
$\theta\colon[0,1]\to\mathbb R$ such that
$T(s)=(\cos\theta(s),\sin\theta(s))$. Put
\[
   \operatorname{tw}(T)=\frac{\theta(1)-\theta(0)}{2\pi}.
\]
For a closed $C^1$ regular oriented curve
$\gamma\colon\mathbb R/\mathbb Z\to\mathbb R^2$, put
\[
   T_\gamma=\frac{\gamma'}{|\gamma'|},
   \qquad
   \rot(\gamma)=\operatorname{tw}(T_\gamma).
\]
Lemma~\ref{lem:turnlift} constructs the lift and proves that these values do
not depend on its choices, on the seam, or on an orientation-preserving regular
reparametrisation. For either a polygon or a $C^1$ regular closed curve put
$R(L)=|\rot(L)|$.

\end{definition}
```

## CV:lem:turnlift — PROVE

reference/R/CV/d1_setup.tex:789–822

```tex
\begin{lemma}[tangent lifts and principal turns]\label{lem:turnlift}
Here $\rot$ is as in Definition~\ref{def:rot}.
\begin{enumerate}
\item[(i)] Every continuous direction loop has a tangent-angle lift.
The integer $\operatorname{tw}(T)$ is independent of the lift and seam,
is unchanged by an orientation-preserving reparametrisation, and is constant
under a continuous homotopy through direction loops. Consequently the rotation
of a closed $C^1$ regular curve is invariant under regular homotopy, and
reversing its orientation negates it.
\item[(ii)] If $L\in\mathcal R_c$ has principal turns $\tau_i$, then
\[
   2\pi\rot(L)=\sum_i\tau_i.
\]
Consequently rotation is constant along every path in $\mathcal R_c$, is
unchanged by a positive flat subdivision, and is negated by orientation
reversal. Every regular three-corner polygon has rotation $+1$ or $-1$
according to the common sign of its three turns.
\item[(iii)] Suppose a closed $C^1$ regular curve is obtained from $L$ by
replacing every corner by a regular arc whose compatible tangent-angle lift
has increment $\tau_i$. Its rotation equals $\rot(L)$.

More generally, let $b,c$ be regular oriented arcs having the same endpoints
and the same oriented tangent rays at both endpoints, and suppose replacing
$b$ by $c$ in a closed curve gives closed $C^1$ regular curves $F_b,F_c$.
For compatible tangent lifts with equal initial values, write their increments
as $\Delta_b,\Delta_c$. Then
\[
   \rot(F_c)-\rot(F_b)=\frac{\Delta_c-\Delta_b}{2\pi}.
\]
If $A_t$, $0\leq t\leq1$, is a supplied continuous path in
$\mathrm{GL}^+(2,\mathbb R)$ with $A_0=I$ and $A_1=A$, applying $A$ to both
arcs leaves $\Delta_c-\Delta_b$ unchanged.
\end{enumerate}
\end{lemma}
```

reference/R/CV/d1_setup.tex:823–906

```tex
\begin{proof}
For~(i), uniform continuity gives
$0=s_0<\cdots<s_m=1$ such that
$T(s)\cdot T(s_{j-1})>0$ on every
$[s_{j-1},s_j]$. After choosing $\theta(0)$, continue it there by
\[
 \theta(s)=\theta(s_{j-1})+
 \operatorname{atan2}\!\left(
   \det(T(s_{j-1}),T(s)),\,
   T(s_{j-1})\cdot T(s)\right).
\]
The second argument is positive, so the added angle lies in
$(-\pi/2,\pi/2)$; the formulas match at the subdivision points and construct a
continuous lift without a covering-space theorem. Since $T(1)=T(0)$, its
endpoint increment belongs to $2\pi\mathbb Z$. Two lifts differ continuously
by a value in $2\pi\mathbb Z$, hence by one constant.

If the increment is $2\pi k$, extend the lift by
$\theta(s+n)=\theta(s)+2\pi nk$. Every interval of length one then has the same
increment, proving seam independence. An orientation-preserving
reparametrisation of the circle has an increasing representative
$\phi\colon\mathbb R\to\mathbb R$ with
$\phi(s+1)=\phi(s)+1$; the lift $\theta\circ\phi$ has the same increment.

For a homotopy $T(s,t)$ fix $t_0$. Uniform continuity gives a neighbourhood of
$t_0$ on which
$T(s,t)\cdot T(s,t_0)>0$ for every $s$. There is therefore
a unique continuous relative angle
\[
 \alpha(s,t)=\operatorname{atan2}\!\left(
 \det(T(s,t_0),T(s,t)),\,
 T(s,t_0)\cdot T(s,t)\right)
 \in(-\pi/2,\pi/2).
\]
If $\theta_0$ lifts $T(\,\cdot\,,t_0)$, then
$\theta_0+\alpha(\,\cdot\,,t)$ lifts $T(\,\cdot\,,t)$.
Periodicity gives $\alpha(1,t)=\alpha(0,t)$, so the endpoint increment is
locally, hence globally, constant in $t$. A regular homotopy supplies such a
homotopy of normalised tangents. For the oppositely oriented curve,
$-T_\gamma(1-s)$ has lift $\theta(1-s)+\pi$, whose increment is the negative
of the original one.

For~(ii), give the admissible reference vector $r$ of
Definition~\ref{def:rot} an angle $\rho$, and let
$\beta_i\in(\rho,\rho+2\pi)$ represent the direction of the $i$th edge.
The three cases in that definition give exactly
\[
   \tau_i=\beta_i-\beta_{i-1}+2\pi\epsilon_i:
\]
a positive crossing of the reference ray contributes $+2\pi$, a negative
crossing contributes $-2\pi$, and otherwise no correction occurs.
Summing cyclically cancels the $\beta$ terms and proves the displayed identity.

Along a path in $\mathcal R_c$, every $\tau_i$ varies continuously in
$(-\pi,\pi)$; hence the displayed integer is constant. A positive flat
subdivision inserts one zero turn and changes no other turn. Reversal negates
and reverses the turn list.

For the three-corner claim, if the vertices are $A,B,C$, all three cyclic turn
determinants equal $\det(B-A,C-A)$. This determinant cannot vanish: otherwise
the three nonzero collinear edge scalars sum to zero, and a cyclic sign change
is a consecutive negative-multiple pair, contrary to regularity. Thus all
three turns have one sign. Their sum is nonzero and has magnitude below
$3\pi$; being $2\pi$ times an integer, it has rotation $+1$ or $-1$ according
to that sign.

For~(iii), concatenate constant lifts on the straight pieces with the
prescribed corner lifts. Their total increment is $\sum_i\tau_i$, so~(ii)
proves the rounding assertion.

For the replacement assertion, use the same lift on the unchanged
complementary arc. Shifting that complementary lift at a join changes neither
its increment nor the computation; subtraction cancels it and leaves
$\Delta_c-\Delta_b$.

Finally follow the tangent path of $c$ and then the tangent path of $b$
backwards. This is a closed direction loop of increment
$\Delta_c-\Delta_b$. The maps
\[
   \nu_t(z)=\frac{A_tz}{|A_tz|}
\]
give a homotopy of that direction loop. Clause~(i) keeps its increment
constant, proving the last assertion without invoking degree.
\end{proof}
```

## CV:def:X1 — DEFINE

reference/R/CV/d1_setup.tex:908–930

```tex
\begin{definition}[the slot, the factor, and $X_1$]\label{def:X1}
Let $P$ be generic and $S\in\Ind(G_P)$. For a carrier $L$ of $S$ set
\[
  P_{S,L}=\prod_{H\text{ carried by }L}P_H,\qquad
  w_{S,L}=\sum_{H\text{ carried by }L}w(H),
\]
the products and sums taken over the residual pieces assigned to $L$ by
Lemma~\ref{lem:carriers}(iv), with the empty product $P_{S,L}=1$ and the empty
sum $w_{S,L}=0$ when no piece is carried by $L$. Here $P_H$ is the HOMFLY--PT
polynomial of the link that the piece $H$ presents, in the normalization of
Definition~\ref{def:homfly}; that such a polynomial exists at all is
Axiom~\ref{ax:homfly}, and this definition is where it is first read. The \emph{slot} of $L$ is the
integer $1-w_{S,L}-R(L)$, the \emph{factor} is
\[
   \Omega_1(S,L)=\bigl[a^{\,1-w_{S,L}-R(L)}z^{0}\bigr]P_{S,L}(a,z)
\]
--- the coefficient itself, taken as a value, with no sign gate and no
zero-gate applied --- and
\[
   X_1(P)\;=\;\sum_{S\in\Ind(G_P)}\wind(S)\prod_{L}\Omega_1(S,L),
\]
the inner product running over the $|S|+1$ carriers of $S$.
\end{definition}
```

## CV:prop:chamberinv — PROVE

reference/R/CV/d1_setup.tex:932–939

```tex
\begin{proposition}[chambers and chamber invariance]\label{prop:chamberinv}
Fix $n\geq3$.
\begin{enumerate}
\item[(i)] The generic locus $\mathcal U_n$ is open in $(\mathbb R^2)^n$, and
every chamber --- every connected component of it --- is open and path connected.
\item[(ii)] $X_1$ is constant on each chamber.
\end{enumerate}
\end{proposition}
```

reference/R/CV/d1_setup.tex:940–1070

```tex
\begin{proof}
For clause (i), fix $P\in\mathcal U_n$. The argument must control the members that are
\emph{not} relevant at $P$ as well as those that are: openness of an activation
region says that a member active at $P$ stays active nearby, and says nothing
about one that is inactive at $P$ becoming active. An earlier revision inferred
the second from the first.

What controls both is the unconditional layer. Every unconditional member ---
every $\mathrm{G1}_i$ and every $\mathrm{G2}_{e,i}$ --- is relevant at every
polygon, so all of them are nonzero at $P$, they are finitely many, and they are
polynomials; let $N$ be a neighbourhood of $P$ on which each of them keeps its
sign. On $N$ the crossing status of every pair of remote edges is constant,
being the four-sign condition of Definition~\ref{def:guarded} in exactly those
members; hence the activation of every conditional member is constant on $N$,
and so is the set of members relevant at a point. Shrinking $N$ so that the
finitely many members relevant at $P$ --- now the members relevant everywhere on
$N$ --- also keep their signs, every point of $N$ is generic. So
$\mathcal U_n$ is open.

A connected component of an open subset of $\mathbb R^N$ is open, the space
being locally connected, and an open connected subset of $\mathbb R^N$ is path
connected: the set of points reachable from a fixed one by a path in it is open
and its complement in the component is open, and the component is connected. An
earlier revision asserted both facts inside the proof that consumes them,
rather than proving them.

For clause (ii), let $P^{0},P^{1}$ lie in one chamber and choose a path
$t\mapsto P(t)$, $t\in[0,1]$, between them inside it, as clause (i) allows.
Every statement below is proved along that path.

\emph{The combinatorics.} Each unconditional member $g\in\mathcal G$ is a
polynomial, so the composite $t\mapsto g(P(t))$ is continuous and, by genericity,
nowhere zero along the path. Its sign is therefore constant on the connected
interval $[0,1]$. The four-sign crossing test of
Definition~\ref{def:guarded} therefore fixes the set of crossing pairs
along the path, and hence a conditional member is active at one parameter
exactly when it is active at every parameter. Each $g$ in this now-fixed active
set is a polynomial relevant at every $P(t)$, so $t\mapsto g(P(t))$ is likewise
continuous and nowhere zero by genericity. Its sign is therefore constant as
well. So: the set of double points, indexed by the pairs of edges carrying them, is
constant; and no two of them collide, for the following reason, which splits in
two cases and uses (G3) in one and (G4) in the other --- an earlier revision
announced it as "the (G4) one and not the (G3) one", which is the half that is
true when the two double points share an edge. Two double points can collide in two ways, and an earlier revision admitted
only one of them, saying that four distinct edges through a point "is not a
coincidence of any member". It is one. \emph{If the four edges are distinct}, the collision puts four edges through a
single point, and there are two sub-cases. If some three of the four are
pairwise nonparallel, they cross pairwise at that point, so their
$\mathrm{G3}$ member is active, and it vanishes, three concurrent lines sharing
a projective point; being active it is relevant, so genericity forbids it. If
no such triple exists, then two of the four are parallel, and being parallel
lines through a common point they are the same line: two distinct edges lying
on one line, each containing that point in its relative interior, hence
overlapping in a segment. Then an endpoint of one lies on the other, an
\emph{unconditional} $\mathrm{G2}$ vanishes, and genericity forbids that as
well. Either way no such collision occurs along a path of generic polygons.
\emph{Otherwise the two double points share an edge}, and there the concurrency
member says nothing --- the two carrying edges may be parallel --- so the
argument is the (G4) one: let them lie on a common edge
$e$, carried by $f$ and $g$, in the order the path presents them. The member
that decides their order along $e$ is
$\mathrm{G4}\langle e;f,g\rangle$, the member-valued accessor of
Definition~\ref{def:guarded}, and the order itself is the sign of the oriented
value $\widehat{\mathrm{G4}}_{e;f,g}=(t_f-t_g)\det(d_f,d_e)\det(d_g,d_e)$,
which is that member times the orientation sign $\epsilon(f,g)$. The member is
active exactly when both $f$ and $g$ cross $e$, which is the case, so it is
relevant and hence nonzero of constant sign along the path; and since
$\epsilon(f,g)$ is a constant of the index data, the oriented value is of
constant sign too. Only the nonvanishing is used below, so the conclusion is
the same under either reading. A collision would be $t_f=t_g$, so no collision occurs and the
order along each edge is constant. When $f$ and $g$ share a vertex $M$ the same
member does the work, its vanishing being that of
$\mathrm{G2}_{e,M}\mathrm{G1}_M$. Both factors are unconditional members, so on
this path --- along which every polygon is \emph{generic} --- both are nonzero;
in particular $\mathrm{G1}_M\neq0$, and that is genericity and not regularity.
Membership of $\mathcal R_n$ (Definition~\ref{def:regular}(B)) excludes only zero
edges and a consecutive pair that doubles back, and a flat vertex with
$\mathrm{G1}_M=0$ is regular. So the product vanishes only if
$\mathrm{G2}_{e,M}$ does, which puts $M$ on the edge $e$ and is forbidden here.
An earlier revision of this sentence said "the turn is nonzero on a regular
polygon", which is false of $\mathcal R_n$. An earlier revision credited
the constancy of the active (G3) signs for all of this; a concurrency member is
inactive when its three edges do not pairwise cross, and then it says nothing,
while two crossings on one edge can still swap. Hence the cyclic sequence of crossing visits along
the traversal --- the Gauss word --- is constant, and so are $G_P$, $\Ind(G_P)$,
each $U(S)$, each family of residual pieces, and, by
Lemma~\ref{lem:carriers}(iv), the assignment of pieces to carriers. Each
carrier is determined by the Gauss word and the smoothing sites, so the carriers
correspond canonically along the path, with corners varying continuously.

\emph{The weights.} At a vertex corner the turn sign is $\sgn\mathrm{G1}_i$,
constant; at a smoothing corner of the crossing of $e,f$ it is the sign of
$\mathrm{G5}_{e,f}$ up to the fixed sign of the smoothing convention, also
constant. So each carrier is uniform on the whole path or mixed on the whole
path, its corner count is constant, and $\mathrm{wt}(L)$ and $\wind(S)$ are
constant (Definition~\ref{def:wind}).

\emph{The rotations.} Turn signs alone do \emph{not} determine a rotation
number --- the convex regular pentagon and the regular pentagram have the same
five positive turn signs and rotations $1$ and $2$ --- so this step is a path
argument, not a sign count. Along the path each carrier $L(t)$ has corners
varying continuously and no vanishing turn determinant, so each principal turn
$\tau_k(t)$ is continuous with values in $(-\pi,\pi)$, and
$\rot(L(t))=\frac1{2\pi}\sum_k\tau_k(t)$ by Lemma~\ref{lem:turnlift}(ii) is a
continuous integer-valued function of $t$ on the connected interval, hence
constant. So each $R(L)$ is constant.

\emph{The piece polynomials.} Fix two parameters $t_0,t_1$ and a residual
piece $H$, identified at the two parameters by the common Gauss word. By
Lemma~\ref{lem:piececurve}, each piece datum is realized by a connected closed
plane curve whose double points are exactly the crossings of $H$ and whose
cyclic word is the parent word restricted to $H$. Match each marked crossing--
carrying-edge incidence $(c,e)$ at $t_0$ with $(c,e)$ at $t_1$. This bijection
preserves cyclic order, and the two incidences bearing $c$ remain its crossing
pair. It preserves signs because every piece crossing is positive, and it
preserves over/under
positions because the divide convention chooses them from the sign of the
active $\mathrm{G5}$ member of the two carrying edges, which is constant along
the chamber. Thus it is an orientation-preserving record isomorphism
(Definition~\ref{def:record}). Lemma~\ref{lem:piececurve} retains exactly
the finite, distinct transverse crossings of $H$
and creates no self-intersection when it smooths locally; hence each realizing
curve has one component and no triple points. Axiom~\ref{ax:gausscode}
therefore says that the piece diagrams present the same oriented link. Hence
$P_H$ is constant by Axiom~\ref{ax:homfly}, while $w(H)=|H|$ is constant because
$H$ is.

Hence every $\Omega_1(S,L)=[a^{1-w_{S,L}-R(L)}z^0]P_{S,L}$ is constant along the
path, and so is the finite sum defining $X_1$. In particular
$X_1(P^0)=X_1(P^1)$.
\end{proof}
```

## CV:def:event — DEFINE

reference/R/CV/d1_setup.tex:1072–1097

```tex
\begin{definition}[event, and its zero set]\label{def:event}
An \emph{event} is a continuous path $t\mapsto P(t)$ of polygons on $n$
vertices, $t\in(-\varepsilon,\varepsilon)$, such that $P(t)$ is generic for
every $t\neq0$ and $P(0)$ is not. Its \emph{zero set} is
\[
   Z=\bigl\{g\in\mathcal G:\ g(P(0))=0\ \text{ and }\ g\ \text{is relevant at }
   P(t)\ \text{for some }t\neq0\bigr\}.
\]
The \emph{two chambers of the event} are the chambers containing
$P\bigl((-\varepsilon,0)\bigr)$ and $P\bigl((0,\varepsilon)\bigr)$; each of
those two sets is connected and consists of generic polygons, so each does lie
in one chamber. We say the event is \emph{guarded relative
to $Z$}, and every appeal to simplicity below names its $Z$.

The event is \emph{transversal} if every member of $Z$ changes sign at $t=0$.
Every named event of the convention that lists them is required to be
transversal. Without that requirement the definition admits a tangency: the
path
\[
   p_1=(0,0),\quad p_2(t)=(2,-t^2),\quad p_3=(1,0),\quad p_4=(3,2)
\]
is generic for $t\neq0$ and has exactly the cusp zero bundle at $t=0$, yet
$P(t)=P(-t)$, so its two punctured sides are the same chamber and no crossing
is created. A tangency is not a wall crossing and every wall law would be
vacuous or false there.
\end{definition}
```

## CV:lem:guardconst — PROVE

reference/R/CV/d1_setup.tex:1107–1113

```tex
\begin{lemma}[the guards outside the zero set]\label{lem:guardconst}
Let $t\mapsto P(t)$, $t\in(-\varepsilon,\varepsilon)$, be an event with zero set
$Z$, and let $g\in\mathcal G$ be relevant at $P(t)$ for some $t\neq0$ and not a
member of $Z$. Then $g(P(0))\neq0$, and there is
$\varepsilon'\in(0,\varepsilon]$ such that $g$ is nonzero and of constant sign
on the whole of $(-\varepsilon',\varepsilon')$.
\end{lemma}
```

reference/R/CV/d1_setup.tex:1114–1122

```tex
\begin{proof}
By Definition~\ref{def:event}, $Z$ consists of the members that vanish at
$P(0)$ \emph{and} are relevant at some $t\neq0$. The hypothesis supplies the
second clause and denies membership, so the first clause fails: $g(P(0))\neq0$.
Since $g$ is a polynomial in the coordinates and $t\mapsto P(t)$ is continuous,
$g\circ P$ is continuous and nonzero at $0$, hence nonzero on some interval
$(-\varepsilon',\varepsilon')$, on which, being continuous and nowhere zero, it
has constant sign.
\end{proof}
```

## CV:def:silent — DEFINE

reference/R/CV/d1_setup.tex:1265–1271

```tex
\begin{definition}[silent event]\label{def:silent}
An event is \emph{silent} if every member of its zero set $Z$ is a predicate
$\mathrm{G2}_{e,i}$ whose vanishing at $t=0$ places $p_i$ on the \emph{line} of
$e$ but not on the segment $e$. In particular no member of $Z$ is a turn (G1),
a crossing-order predicate (G4), a concurrency (G3) or a direction determinant
(G5).
\end{definition}
```

## CV:lem:silence — PROVE

reference/R/CV/d1_setup.tex:1300–1302

```tex
\begin{lemma}[$X_1$ is unchanged across a silent event]\label{lem:silence}
Let $t\mapsto P(t)$ be a silent event. Then $X_1(P_+)=X_1(P_-)$.
\end{lemma}
```

reference/R/CV/d1_setup.tex:1303–1416

```tex
\begin{proof}
By the proof of Proposition~\ref{prop:chamberinv}(ii), $X_1$ is determined by the
set of double points indexed by the pairs of edges carrying them, their order
along each edge, the turn signs at vertices and at smoothing sites, the
\emph{absolute rotation} $R(L)$ of each carrier, and the polynomial $P_H$ of each
residual piece. An earlier revision omitted $R(L)$ from this list,
although the slot of Definition~\ref{def:X1} reads it. It suffices to show each is
constant on the whole interval, $t=0$ included.

A double point of the pair $(e,f)$ exists exactly when the relative interiors of
$e$ and $f$ meet, and by continuity it can appear or disappear only through a
configuration in which an endpoint of one segment lies on the other segment ---
a $\mathrm{G2}$ predicate vanishing \emph{with the vertex on the segment}.
Definition~\ref{def:silent} excludes that --- a member of $Z$ may put $p_i$ on
the line of $e$ but never on the segment --- and every other relevant
$\mathrm{G2}$ is nonzero throughout by Lemma~\ref{lem:guardconst}.
So the set of double points is constant, and with it the set of active
conditional members. Nor do two double points on \emph{disjoint} pairs of edges collide: that puts
four edges through one point, and the two sub-cases are those of
Proposition~\ref{prop:chamberinv}(ii). If some three of the four are pairwise
nonparallel they cross pairwise there, so their $\mathrm{G3}$ member is active
and vanishes, and an active member is relevant, hence lies in $Z$ if it
vanishes at $t=0$ --- which Definition~\ref{def:silent} forbids, its zero sets
containing no (G3). Otherwise two of the four are collinear and overlap at the
point, so an unconditional $\mathrm{G2}$ vanishes there with the vertex on the
\emph{segment}, which Definition~\ref{def:silent} also forbids.
The collision would leave the Gauss word alone but would destroy the
diagrammatic hypothesis the isotopy step below reads.

Two double points on a common edge exchange order only by colliding, which puts
three segments through one common point. Fix the common edge $e$ and the two edges $f,g$ carrying the colliding double
points; both are remote to $e$, a crossing requiring remoteness. The predicate
that decides the order of those two crossings along $e$ is the member
$\mathrm{G4}\langle e;f,g\rangle$ --- the accessor, since $f$ and $g$ are
presented in the order the geometry gives and their representatives need not be
increasing --- and it is the right tool: it is \emph{active} exactly when $f$
and $g$ both cross $e$, which is the situation in hand, and it vanishes exactly
when the two crossing parameters coincide, which is the collision. Being active
it is relevant, so if it vanished at $t=0$ it would lie in the zero set $Z$;
and $Z$ contains no (G4) member, by Definition~\ref{def:silent} --- the zero
set holds members, so it is membership of the accessor's value that is
excluded, and the orientation sign is irrelevant to it. So it does not
vanish, and by Lemma~\ref{lem:guardconst} it keeps its sign: no collision.

An earlier revision reached instead for the concurrency member
$\mathrm{G3}_{e,f,g}$ and argued by cases on whether $f$ and $g$ are remote or
consecutive. That misses a configuration, and the peer's chart is exact: with
$e$ from $(-2,0)$ of direction $(4,0)$, $f_t$ from $(t,-1)$ of direction
$(0,2)$ and $g_t$ from $(-t,-2)$ of direction $(0,4)$, the triple is pairwise
remote, $f$ and $g$ are \emph{parallel} so $\mathrm{G3}$ is inactive and says
nothing, yet both cross $e$ and their crossings swap at $t=0$;
$\mathrm{G3}=-64t$ and $\mathrm{G4}_{e;f,g}=64t$, and it is the (G4) that is
active and in the zero set's way.

The two edges $f,g$ may also share a vertex $M$, and then the same predicate
does the work, being indexed for any pair remote to $e$. Its vanishing is then
the vanishing of $\mathrm{G2}_{e,M}\,\mathrm{G1}_M$. The second factor is a
turn, and it is nonzero here because $\mathrm{G1}_M$ is unconditional and every
polygon of a silent event's punctured sides is generic, with $\mathrm{G1}_M$
outside the zero set by Definition~\ref{def:silent} and so nonzero at $t=0$ as
well by Lemma~\ref{lem:guardconst} --- regularity alone would not give it, a
flat vertex being regular. So a collision would need $M$ on the line of $e$, and
on the \emph{segment}, since the collision point is the common crossing
--- a $\mathrm{G2}$ vanishing with the vertex on the segment, which
Definition~\ref{def:silent} excludes from $Z$ while $\mathrm{G2}$ is
unconditional and hence relevant.

So no collision occurs, the order along each edge is constant, and the Gauss
word with it.

The turn sign at a vertex is $\sgn\mathrm{G1}_i$, which is unconditional,
hence relevant, and lies in no $Z$ of a silent event, so it is nonzero of
constant sign by Lemma~\ref{lem:guardconst}. The
turn sign at a smoothing site of the crossing of $e$ and $f$ is the sign of
$\mathrm{G5}_{e,f}$ up to the fixed sign of the smoothing convention. That
predicate is not in $Z$, so by the same dichotomy either it is nonzero on a
neighbourhood, or $e$ and $f$ carry no double point for $t\neq0$ and hence no
smoothing site whose turn could change.

The absolute rotation $R(L)$ of a carrier is next, and it needs its own
argument: turn signs alone do not determine a rotation number, and link
isotopy cannot substitute for it, plane rotation not being a knot-type
invariant. Each carrier $L(t)$ has, by the no-birth and no-collision facts
above, a fixed finite cyclic corner set, each corner varying continuously in
$t$. Each corner's turn determinant --- the $\mathrm{G1}$ at a vertex, the
$\mathrm{G5}$ at a smoothing site --- is nonzero through the wall by the two
preceding paragraphs, $t=0$ included, so each principal turn $\tau_k(t)$ is
continuous with values in $(-\pi,\pi)$, and
$\rot(L(t))=\frac1{2\pi}\sum_k\tau_k(t)$ by Lemma~\ref{lem:turnlift}(ii) is a
continuous integer-valued function on the connected event interval, hence
constant. This is the path argument of Proposition~\ref{prop:chamberinv}(ii) run
through the wall, and it is printed rather than cited because a silent wall
lies inside no chamber. So each $R(L)$ is constant.

Finally, the common Gauss word identifies every residual piece $H$ on the two
sides. The edge-pair indexing is constant as proved above: a silent zero puts its vertex
off the remote segment, so no crossing changes carrying edge at the wall.
Lemma~\ref{lem:piececurve} realizes its datum on each side by a connected
closed plane curve whose double points are exactly the crossings of $H$. Match each marked crossing--carrying-edge
incidence $(c,e)$ on the first side with the same incidence $(c,e)$
on the second. The common restricted word makes this bijection cyclic-order
preserving; the two incidences bearing $c$ remain its crossing pair. Every sign
is positive, and the $\mathrm{G5}$ argument above shows that the divide
convention designates the same visit as over on the two sides. Thus the map is
an orientation-preserving record isomorphism
(Definition~\ref{def:record}). Lemma~\ref{lem:piececurve} retains exactly
the finite, distinct transverse crossings of $H$ from the two generic parents
and creates no self-intersection when it smooths locally; hence each realizing
curve has one component and no triple points. Axiom~\ref{ax:gausscode} says that the piece diagrams present the same
oriented link, so Axiom~\ref{ax:homfly} gives the same $P_H$; and
$w(H)=|H|$ is unchanged because $H$ is.
Every input to $X_1$ is therefore constant on $(-\varepsilon,\varepsilon)$, and
$X_1(P_+)=X_1(P_-)$.
\end{proof}
```

## CV:lem:rounding — PROVE

reference/R/CV/d3_floor.tex:31–93

```tex
\begin{lemma}[rounding]\label{lem:rounding}
Here $\rot$ is as in Definition~\ref{def:rot}.
Let $L$ be a closed polygon with corners $q_1,\dots,q_c$, and let $D$ be an
oriented diagram whose underlying plane curve is $L$ --- $L$ together with an
over/under assignment at each of its double points. Assume the principal turns
of $L$ all exist and are \emph{nonzero}; that $L$ has finitely many double
points, all transversal, none of them a corner; and that no corner of $L$ lies
on an edge of $L$ other than the two incident to it. Then there is a \emph{clearance} $\varepsilon_0(L)>0$ such that for every
$\varepsilon\in\bigl(0,\varepsilon_0(L)\bigr)$ there is a $C^\infty$ regular
closed plane curve $L_\varepsilon$, and a diagram $D_\varepsilon$ carried by it, with
these properties. The clearance is part of the conclusion and is quantified
here: an earlier revision wrote "below the bound displayed in the proof", which
names an object chosen inside a proof as though the statement supplied it.

The hypothesis names a curve \emph{and} a diagram: clause~(c) speaks of an
over/under assignment, of crossing signs and of a writhe, none of which a plane
curve carries, and an earlier revision bound only $L$. It does \emph{not} name a
generic parent polygon. An earlier revision did, and then
Theorem~\ref{thm:carrierfloor}(C) applied this lemma on its own hypotheses, which
do not mention one --- the peer's polygon $((0,0),(1,0),(-2,-2),(2,0),(-2,1))$
satisfies the floor's hypotheses and is not a carrier of a support of a generic
polygon. What genericity was supplying is written out instead: finitely many
transverse double points, none at a corner, and no corner on a non-incident
edge, which is exactly what makes the finitely many distances in the proof
positive.
\begin{enumerate}
\item[(a)] $L_\varepsilon$ coincides with $L$ outside the union of the discs of
radius $\varepsilon$ about the corners.
\item[(b)] Inside the disc about $q_i$ the unit tangent moves \emph{strictly}
monotonically, in the sense of $\sgn\tau_i$, from $\delta_{i-1}/|\delta_{i-1}|$
to $\delta_i/|\delta_i|$, sweeping an arc of length exactly $|\tau_i|$ and no
more, and attaining each direction of that arc at exactly one parameter.
Moreover the unit-tangent map is an \emph{immersion} on the open junction arc:
parametrized by arclength, its angular derivative is nonzero at every interior
parameter, while at the two ends it and all its derivatives vanish, the
junction meeting the straight edges flat to infinite order.

Both clauses are exported because both are read downstream, and the second does
not follow from the first: a strictly monotone angle may still have a vanishing
derivative at a parameter, and the direct count below needs the derivative
itself to be nonzero, not merely the monotonicity. "Moves monotonically" alone
is weaker still --- it is
satisfied by a junction that pauses on one direction for a whole sub-arc, and
then a count of the parameters carrying a prescribed direction is infinite. Both
hold because the profile fixed in the proof below is strictly increasing on
$(0,1)$ with $\varphi'>0$ there, and flat to infinite order at $0$ and $1$: the
tangent angle at arclength $\sigma$ along the junction of length $\ell$ is
$\theta_u+\tau_i\varphi(\sigma/\ell)$, whose derivative is
$\tau_i\varphi'(\sigma/\ell)/\ell\neq0$ for $0<\sigma<\ell$.
\item[(c)] $L_\varepsilon$ has the same double points as $L$, with the same
strands, the same over/under assignment and hence the same crossing signs and
the same writhe.
\item[(d)] $\rot(L_\varepsilon)=\rot(L)$.
\item[(e)] \emph{The disc package is returned.} There are pairwise disjoint
closed discs $D_1,\dots,D_c$, one about each corner $q_i$, such that each $D_i$
meets no edge of $L$ that is not incident to $q_i$, contains no double point of
$L$, meets the two incident edges exactly in the two sub-segments of length
$\varepsilon$ at $q_i$, and contains the whole of the modification made at
$q_i$. This clause is a conclusion of the lemma, not a package handed over by a
paragraph of its proof; its consumer asks for a disc meeting the diagram in one
embedded arc and reads it here.
\end{enumerate}
\end{lemma}
```

reference/R/CV/d3_floor.tex:94–261

```tex
\begin{proof}
\emph{The junction, constructed.} Since $0<|\tau_i|<\pi$, the unit directions
$u=\delta_{i-1}/|\delta_{i-1}|$ and $v=\delta_i/|\delta_i|$ are neither parallel
nor antiparallel. Write $A_0=q_i-\varepsilon u$ and $A_1=q_i+\varepsilon v$ for
the two points at distance $\varepsilon$ from $q_i$ along the incident edges, so
that the displacement to be realized is
\[
   A_1-A_0=\varepsilon\,(u+v),
\]
a nonzero vector along the bisector of the convex angle at $q_i$. Fix once and
for all the \emph{transition profile}
\[
   \varphi(t)=\frac{f(t)}{f(t)+f(1-t)},
   \qquad
   f(t)=\begin{cases} e^{-1/t}, & t>0,\\ 0,& t\leq0,\end{cases}
\]
which is exhibited rather than posited, and which has the four properties every
use below reads. It is $C^\infty$ on $[0,1]$: $f$ is $C^\infty$ on $\mathbb R$
with all derivatives vanishing at $0$, and the denominator
$f(t)+f(1-t)$ is positive on $[0,1]$, being $f(1)>0$ at $t=0$ and $f(1)>0$ at
$t=1$ and a sum of two nonnegative terms not both zero in between. It has
$\varphi(0)=0$ and $\varphi(1)=1$. It satisfies $\varphi(1-t)=1-\varphi(t)$, by
inspection of the formula. And it is \emph{strictly increasing on $(0,1)$}:
\[
   \varphi'(t)=\frac{f'(t)f(1-t)+f(t)f'(1-t)}{\bigl(f(t)+f(1-t)\bigr)^2}>0
   \qquad (0<t<1),
\]
both terms of the numerator being positive there, since $f>0$ and
$f'(t)=t^{-2}e^{-1/t}>0$ on $(0,1)$. Every derivative of $\varphi$ vanishes at
$0$ and at $1$, because every derivative of $f$ vanishes at $0$ and the
denominator is smooth and nonvanishing.

Strict increase is not a convenience. An earlier revision asked only that
$\varphi$ be nondecreasing, and a nondecreasing profile may be constant on a
subinterval; the tangent direction would then be constant on a whole sub-arc of
the junction, so a direction attained there would be attained at a continuum of
parameters rather than at isolated ones, and every count of the points carrying
a prescribed tangent direction --- the counts this section takes later --- would
be infinite. With $\varphi$ strictly increasing on $(0,1)$ the tangent angle
$\theta_u+\tau_i\varphi(t/\ell)$ is strictly monotone across the junction, and
each direction in the swept arc is attained exactly once. Let
$\theta_u$ be the angle of $u$ and, for a length $\ell>0$, let
\[
   \gamma_\ell(s)=A_0+\int_0^{s}
   \bigl(\cos(\theta_u+\tau_i\varphi(t/\ell)),\,
         \sin(\theta_u+\tau_i\varphi(t/\ell))\bigr)\,\mathrm dt,
   \qquad s\in[0,\ell].
\]
Then $\gamma_\ell$ is a unit-speed $C^\infty$ arc. Its tangent equals $u$
\emph{at} $s=0$ and $v$ \emph{at} $s=\ell$, and agrees with those constants
\emph{to infinite order} at those two parameters, every derivative of $\varphi$
vanishing there; it does not equal them on a neighbourhood, and cannot, since
the angle is strictly monotone on $(0,\ell)$ --- an earlier revision wrote
"near $s=0$", which contradicts the strictness this same construction exports.
Infinite-order agreement at the endpoint is what the junction needs: it is
exactly the condition under which replacing the corner by the arc leaves a
$C^\infty$ regular curve, since all one-sided derivatives match those of the
straight edge. The tangent angle moves strictly monotonically through exactly
$\tau_i$ and no more, and its derivative
$\tau_i\varphi'(s/\ell)/\ell$ is nonzero on $(0,\ell)$, which is (b).

Its endpoint is $A_0+\ell\,m(\varphi)$ where
$m(\varphi)=\int_0^1(\cos(\theta_u+\tau_i\varphi),\sin(\theta_u+\tau_i\varphi))\,
\mathrm dt$. The symmetry $\varphi(1-t)=1-\varphi(t)$ makes the angles
$\theta_u+\tau_i\varphi(t)$ and $\theta_u+\tau_i\varphi(1-t)$ reflections of
each other in the bisector, so $m(\varphi)$ points along $u+v$; and
$|m(\varphi)|>0$ because all the directions integrated lie in a closed angular
interval of width $|\tau_i|<\pi$. Taking
$\ell=\varepsilon\,|u+v|/|m(\varphi)|$ makes the endpoint exactly $A_1$. This is
where the circular arc of an earlier revision has been replaced: that arc is
$C^1$ and not $C^\infty$ at the two junctions, and the document then carried a
lemma to repair the loss.

\emph{The arc lies in the triangle $A_0q_iA_1$, in coordinates.} Put
$\alpha=|\tau_i|/2\in(0,\pi/2)$ and $s=\sgn\tau_i$, let $w$ be the unit vector
along $u+v$ and $z$ the unit vector with $\det(w,z)=1$, and take $q_i$ as
origin, writing a point as $(x_w,x_z)$ in that frame. Then
\[
   u=\cos\alpha\,w-s\sin\alpha\,z,
   \qquad
   v=\cos\alpha\,w+s\sin\alpha\,z,
\]
because $u$ and $v$ are unit vectors whose sum is along $w$ and whose angle is
$|\tau_i|=2\alpha$, turning from $u$ to $v$ by $\tau_i$. Hence
$A_0=-\varepsilon u$ has coordinates $(-\varepsilon\cos\alpha,\ s\varepsilon
\sin\alpha)$ and $A_1=\varepsilon v$ has $(\varepsilon\cos\alpha,\
s\varepsilon\sin\alpha)$, and the closed triangle with vertices $A_0,q_i,A_1$
is exactly
\begin{equation}
   T_i=\bigl\{\,(x_w,x_z):\ |x_w|\leq\cot\alpha\cdot(s\,x_z),
   \quad 0\leq s\,x_z\leq\varepsilon\sin\alpha\,\bigr\},
\label{eq:triangle}
\end{equation}
the first inequality being the pair of cone conditions at the apex $q_i$ and the
second the chord through $A_0$ and $A_1$: a point $\lambda(-u)+\mu v$ with
$\lambda,\mu\geq0$ has $x_w=(\mu-\lambda)\cos\alpha$ and
$s\,x_z=(\lambda+\mu)\sin\alpha$, so $|x_w|\leq(\lambda+\mu)\cos\alpha=\cot\alpha
\cdot(s\,x_z)$ with equality exactly on the two edges, and $\lambda+\mu\leq
\varepsilon$ is the chord.

The junction arc satisfies all three inequalities of \eqref{eq:triangle}. Write
its unit tangent as $T(\sigma)=\cos\beta(\sigma)\,w+s\sin\beta(\sigma)\,z$ with
$\beta(\sigma)=-\alpha+2\alpha\,\varphi(\sigma/\ell)$, which is the tangent
angle constructed above read in this frame: at $\sigma=0$ it is $u$
($\beta=-\alpha$), at $\sigma=\ell$ it is $v$ ($\beta=\alpha$), and $\beta$ is
strictly increasing with values in $[-\alpha,\alpha]$.
\emph{The two cone inequalities.} Let $n_1$ be the unit normal to $u$ with
$\langle n_1,v\rangle>0$. The line $\mathbb Ru$ contains both $q_i$ and $A_0$,
and $T_i$ lies in $\{\langle\cdot,n_1\rangle\geq0\}$. Along the arc,
$\tfrac{d}{d\sigma}\langle\gamma,n_1\rangle=\langle T,n_1\rangle\geq0$, because
$T=au+bv$ with $a,b\geq0$ --- a direction at angle $\beta\in[-\alpha,\alpha]$
from $w$ lies in the closed cone of $u$ and $v$ --- so
$\langle T,n_1\rangle=b\langle v,n_1\rangle\geq0$; and
$\langle\gamma(0),n_1\rangle=\langle-\varepsilon u,n_1\rangle=0$. Hence
$\langle\gamma,n_1\rangle\geq0$ throughout. Symmetrically, with $n_2$ the unit
normal to $v$ with $\langle n_2,A_0\rangle>0$, one has $\langle
T,n_2\rangle=a\langle u,n_2\rangle\leq0$, so $\langle\gamma,n_2\rangle$ is
nonincreasing and equals $\langle\varepsilon v,n_2\rangle=0$ at $\sigma=\ell$;
hence it is $\geq0$ throughout. Those two are the first inequality of
\eqref{eq:triangle}.
\emph{The chord inequality.} $s\,x_z(\sigma)=\varepsilon\sin\alpha+\int_0^\sigma
\sin\beta(t)\,dt$, and $\int_0^\sigma\sin\beta\leq0$ for every
$\sigma\in[0,\ell]$: $\beta$ is negative on $(0,\ell/2)$ and positive on
$(\ell/2,\ell)$, and the symmetry $\varphi(1-t)=1-\varphi(t)$ makes
$\beta(\ell-t)=-\beta(t)$, so the integral decreases to its minimum at
$\ell/2$ and increases back to $0$ at $\ell$. Hence $s\,x_z\leq\varepsilon
\sin\alpha$, which is the second. The lower bound $s\,x_z\geq0$ is implied by
the two cone inequalities, the apex being the origin.

So the arc lies in $T_i$, and $T_i$ lies in the closed disc $D_i$ of radius
$\varepsilon$ about $q_i$: the disc is convex and contains the three vertices,
$|A_0-q_i|=|A_1-q_i|=\varepsilon$. An earlier revision argued this by saying the
arc ``cannot leave the region cut off by the two tangent lines'', which names
the conclusion rather than proving it and leaves the chord side unaddressed.

For (a) and (c) put
\[
   \varepsilon_0(L)=\tfrac13\min\Bigl\{
 \min_{i}\min_{k\neq i}|q_k-q_i|,\;
 \min_{i}\operatorname{dist}\bigl(q_i,\,\textstyle\bigcup\{\text{closed edges of }L\text{ not incident to }q_i\}\bigr),\;
 \min_i|\delta_i|,\;
 \min_{i,\,x\text{ a double point}}|x-q_i|
\Bigr\},
\]
and require $\varepsilon<\varepsilon_0(L)$; the index $i$ is bound by the outer
minimum in every term, an earlier revision having left it free in the first.
Each minimum over an empty index set is $+\infty$ --- which is how the last
one is read when $L$ has no double point. Every listed quantity is positive: the
corners are finitely many and distinct; a corner is at positive distance from a
non-incident closed edge because the edges are compact and a corner on one would
contradict the hypothesis that no corner lies on a non-incident edge; the edges have positive length; and a double point lies
in the relative interiors of two edges, so it is distinct from every corner.
With this $\varepsilon$ the discs $D_i$ are pairwise disjoint, each $D_i$ meets
no edge not incident to $q_i$, each $D_i$ contains no double point, and each
$D_i$ meets the two incident edges in the two sub-segments of length
$\varepsilon$ at $q_i$, and each contains the whole modification made at its
corner, the replacement arc lying within distance $\varepsilon$ of $q_i$. That
is clause~(e). Hence the rounding changes the curve only inside those
discs, where it meets nothing else, so no double point is created or destroyed
and the strands through each surviving double point are unchanged as arcs, with
their orientations; the over/under assignment is inherited, so the crossing signs
and the writhe are unchanged. That is (a) and (c). For (d), the total turning of
$L_\varepsilon$ is the sum of the turnings of its arcs, which is
$\sum_i\tau_i$ because the tangent is constant along the straight parts; and the
rotation number of a $C^1$ regular closed curve is $\frac1{2\pi}$ times its
total turning (Lemma~\ref{lem:turnlift}(iii)), which is also the value assigned to $L$
by Definition~\ref{def:rot}.
\end{proof}
```

## CV:lem:uniformrot — PROVE

reference/R/CV/d3_floor.tex:263–276

```tex
\begin{lemma}[rotation bounds for uniform and one-dissent polygons]
\label{lem:uniformrot}
Here $\rot$ is as in Definition~\ref{def:rot}.
\begin{enumerate}
\item[(i)] Let $L$ be a closed polygon all of whose principal turns exist and are
positive. Then $\rot(L)\geq1$, with equality if $L$ has three corners. If all
turns are negative, $\rot(L)\leq-1$, again with equality in absolute value for
three corners.
\item[(ii)] Let $L$ be a closed polygon whose principal turns all exist, with
exactly one negative principal turn, of magnitude $\alpha\in(0,\pi)$, and let
$\Pi$ be the sum of the positive ones. Then
$\Pi-\alpha=2\pi r$ with $r=\rot(L)$ an integer, and $r\geq1$.
\end{enumerate}
\end{lemma}
```

reference/R/CV/d3_floor.tex:277–300

```tex
\begin{proof}
(i) By Lemma~\ref{lem:turnlift}(ii),
$2\pi\rot(L)=\sum_i\tau_i$. A polygon has at least three corners and each
$\tau_i>0$, so the sum is positive and $\rot(L)>0$; being an integer,
$\rot(L)\geq1$. With three corners the sum is also below $3\pi$, forcing
$\rot(L)=1$. Orientation reversal in the same lemma gives both negative
claims.

(ii) The identity is Lemma~\ref{lem:turnlift}(ii). Suppose $r\leq0$. Then
$\Pi\leq\alpha<\pi$. Cut the traversal of $L$ immediately after the negative
corner and follow it once around: the direction of the edge is turned by the
successive principal turns, all of which are \emph{nonnegative} --- the
hypothesis names one negative turn and admits turns equal to zero, which $\Pi$
omits, and an earlier revision said "all of which are positive", which is false
as written when a zero turn is present --- and they sum to $\Pi<\pi$, so every
edge direction of $L$ lies in a closed angular interval $I$ of width $\Pi<\pi$.
A zero turn does not widen that interval, so the argument is unchanged. An
interval of width less than $\pi$ has a nonempty open dual: there is
$u\in\mathbb R^2$ with $\langle u,\delta\rangle>0$ for every direction
$\delta\in I$, hence for every edge of $L$. But the edges of a closed polygon
sum to zero, so
$0=\langle u,\sum_i\delta_i\rangle=\sum_i\langle u,\delta_i\rangle>0$, a
contradiction. Hence $r\geq1$, and $R:=|\rot(L)|=r$.
\end{proof}
```

## CV:lem:curl — PROVE

reference/R/CV/d3_floor.tex:304–323

```tex
\begin{lemma}[exact negative-curl replacement]\label{lem:curl}
Here $\rot$ is as in Definition~\ref{def:rot}.
Let $F$ be a connected $C^\infty$ immersed circle in the plane --- one
component, with finitely many transverse double points and no triple points ---
given with an oriented diagram, and let $p$ be a point of $F$ at which the
tangent points in a fixed direction $u$, isolated among such points, lying in
an embedded arc of $F$ that contains no double point and along which the tangent
turns strictly positively. Then $F$ may be modified inside a disc $\Delta$
meeting the rest of the diagram only in that arc, so that the resulting
diagram $F'$
\begin{enumerate}
\item[(i)] is again such an oriented diagram, satisfies
$P_{F'}(a,z)=P_F(a,z)$, and has the same double points outside $\Delta$, with
the same signs;
\item[(ii)] has no point of $\Delta$ at which the tangent equals $u$, and exactly
one at which it equals $-u$;
\item[(iii)] has exactly one double point inside $\Delta$, and it is negative;
\item[(iv)] satisfies $\rot(F')=\rot(F)-1$ and $w(F')=w(F)-1$.
\end{enumerate}
\end{lemma}
```

reference/R/CV/d3_floor.tex:324–701

```tex
\begin{proof}
Work first in the rational model on $-2\leq t\leq2$,
\[
b(t)=\Bigl(\tfrac{3(t^2+7)}{11},\,-3t\Bigr),\qquad
c(t)=\bigl(t^2-1,\;t-t^3\bigr).
\]
The endpoints and endpoint tangent rays agree up to positive scale:
$b(\pm2)=c(\pm2)=(3,\mp6)$ and $b'(\pm2)=\frac3{11}c'(\pm2)$. The old arc turns
strictly positively and has exactly one tangent pointing straight down, at
$t=0$:
\[
\det\bigl(b'(t),b''(t)\bigr)=\tfrac{18}{11}>0,\qquad b'(0)=(0,-3).
\]
The replacement turns strictly negatively and has exactly one tangent pointing
straight up, at $t=0$:
\[
\det\bigl(c'(t),c''(t)\bigr)=-2(1+3t^2)<0,\qquad c'(0)=(0,1).
\]
In each arc the first derivative has vanishing first component only at $t=0$, so
neither arc has any other vertical tangent; this is (ii) in the model. The
replacement runs between the same endpoint rays along the complementary,
clockwise tangent path, so its compatible lift increment is the old one minus
$2\pi$; Lemma~\ref{lem:turnlift}(iii) gives (iv) for $\rot$. It has exactly one double point,
\[
c(-1)=c(1)=(0,0),\qquad c'(-1)=(-2,-2),\qquad c'(1)=(2,-2),
\]
and putting the later branch over the earlier one makes it negative, since a
crossing sign is the sign of the determinant of the overpassing tangent followed
by the underpassing tangent and
$\det\bigl(c'(1),c'(-1)\bigr)=-8<0$; that is (iii), and with it (iv) for $w$.
Being a single Reidemeister-I monogon, the replacement does not change the knot
type, which is (i).

To insert the model at $p$ we first record the projective fact it needs, in the
form the insertion argument requires.

\emph{Ordered-ray lemma.} Let $(r_1,r_2,r_3)$ and $(s_1,s_2,s_3)$ be triples of
rays from the origin such that $r_2$ lies in the open convex cone spanned by
$r_1,r_3$ and $s_2$ lies in the open convex cone spanned by $s_1,s_3$, with
$r_1,r_3$ and $s_1,s_3$ independent, and suppose in addition that for positive
representatives
\begin{equation}
   \sgn\det(\rho_1,\rho_3)=\sgn\det(\sigma_1,\sigma_3),
\label{eq:orderedray}
\end{equation}
a condition independent of the representatives chosen. Then there is a linear
map $A$ with $\det A>0$ carrying each $r_k$ into $s_k$.
\emph{Proof:} if both determinants in \eqref{eq:orderedray} are negative,
exchange the names $1$ and $3$ \emph{in both triples simultaneously}; this
preserves the correspondence $r_k\mapsto s_k$ and makes both determinants
positive. The linear map $A_0$ with $A_0\rho_1=\sigma_1$, $A_0\rho_3=\sigma_3$
then has positive determinant and carries $r_1,r_3$ to $s_1,s_3$. It carries the
open cone of $r_1,r_3$ onto that of $s_1,s_3$, so $A_0r_2$ is a ray $\sigma$ in
the latter cone. Writing $s_2=\mathbb R_{>0}(x\sigma_1+y\sigma_3)$ and
$\sigma=\mathbb R_{>0}(x'\sigma_1+y'\sigma_3)$ with $x,y,x',y'>0$, the map
$D=\mathrm{diag}(x/x',\,y/y')$ in the basis $(\sigma_1,\sigma_3)$ has positive
determinant, fixes $s_1$ and $s_3$, and carries $\sigma$ to $s_2$. Take
$A=DA_0$. $\square$

An earlier revision of this lemma omitted \eqref{eq:orderedray} and said the
positive determinants could be arranged ``after swapping the names once if
necessary''. A swap performed in one triple only destroys the correspondence it
is supposed to produce, and the peer refuted that step; the hypothesis is now
stated and the swap is simultaneous. In the application below the condition is
not inferred from the two cones: both determinants are computed and are
positive.

\emph{A positive-turn chart, and the cuts.} Parametrise the embedded arc by
arclength as $\gamma(s)$ with $\gamma(0)=p$ and unit tangent $\gamma'(0)=u$.
Because the tangent turns strictly positively, after shrinking the chart there
is a continuous strictly increasing lift $\theta$ with
\[
   \gamma'(s)=\cos\theta(s)\,u+\sin\theta(s)\,Ju,\qquad
   \theta(0)=0,\qquad |\theta(s)|<\tfrac\pi2,
\]
where $J$ is the positive quarter turn. Put $v=-Ju$, so that $(v,u)$ is a
positively oriented orthonormal basis, and set
\[
   \xi(s)=\langle\gamma(s)-p,\,v\rangle,\qquad
   \eta(s)=\langle\gamma(s)-p,\,u\rangle,
\]
so that $\xi'(s)=-\sin\theta(s)$ and $\eta'(s)=\cos\theta(s)$. Hence $\xi$
increases strictly for $s<0$ and decreases strictly for $s>0$, with a strict
maximum $\xi(0)=0$, while $\eta$ increases throughout. For every level
sufficiently close to $\xi(0)$ from below, strict monotonicity and the
intermediate value theorem give unique cuts $s_-<0<s_+$ with
$\xi(s_-)=\xi(s_+)$, and both tend to $0$ as the level tends to $\xi(0)$. Write
$p_\pm=\gamma(s_\pm)$. Equal transverse coordinates and monotone $\eta$ give
\[
   p_+-p_-=\ell u,\qquad \ell>0,\qquad \ell\to0 .
\]
Two side facts follow at once and are what the earlier revision lacked: the
central arc $\gamma((s_-,s_+))$ lies strictly in $\xi>\xi(s_-)$, and both
retained tails lie strictly in $\xi<\xi(s_-)$.

\emph{The affine fit, quantitatively.} In the positively oriented model basis
$v_0=(-1,0)$, $u_0=(0,-1)$ one has $q=\tfrac4{11}$ and
\[
   b'(-2)\in\mathbb R_{>0}(qv_0+u_0),\qquad
   b'(0)\in\mathbb R_{>0}u_0,\qquad
   b'(2)\in\mathbb R_{>0}(-qv_0+u_0).
\]
Write the two target endpoint tangents in the basis $(v,u)$ as
$T_-=\gamma'(s_-)=av+bu$ and $T_+=\gamma'(s_+)=-cv+du$; then
$a=-\sin\theta(s_-)>0$, $c=\sin\theta(s_+)>0$ and $b,d=\cos\theta(s_\mp)>0$,
and $a,c\to0$, $b,d\to1$ as the cuts approach $p$. The two outer determinants
are $\det(qv_0+u_0,-qv_0+u_0)=2q>0$ and $\det(T_-,T_+)=ad+bc>0$, so
\eqref{eq:orderedray} holds; it is computed, not inferred. Define
\[
   H=\frac{2}{\tfrac ba+\tfrac dc}=\frac{2ac}{bc+ad},\qquad
   x=\frac Hq,\qquad
   y=\frac{\tfrac ba-\tfrac dc}{q\bigl(\tfrac ba+\tfrac dc\bigr)}
    =\frac{bc-ad}{q(bc+ad)},
\]
and let $A$ be the linear map with $A u_0=u$ and $Av_0=xv+yu$. Then
\[
   A(qv_0+u_0)=\tfrac Ha\,T_-,\qquad
   A(-qv_0+u_0)=\tfrac Hc\,T_+,\qquad
   \det A=x=\frac{2ac}{q(bc+ad)}>0,
\]
each by substitution, and
\[
   1-(qy)^2=\frac{4abcd}{(bc+ad)^2}>0,
\]
so $|y|<1/q$ uniformly, while $x\to0$ as the cuts approach $p$: the map $A$
stays bounded. This is the quantitative statement that the earlier revision
replaced by an unquantified ``fixed unit-normalized part of $A$''.

Since $b(2)-b(-2)=12u_0$, put $B=\tfrac{\ell}{12}A$ and
$\Phi(z)=p_-+B\bigl(z-b(-2)\bigr)$. Then $\Phi(b(-2))=p_-$,
$\Phi(b(2))=p_-+\ell A u_0=p_-+\ell u=p_+$, and the endpoint tangent rays match
with positive scale. Because $\ell\to0$ while $A$ stays bounded, the diameter of
$\Phi(c([-2,2]))$ tends to $0$, so the cuts may be chosen so that the whole
inserted arc lies in a preassigned disc $\Delta$ about $p$ whose intersection
with the diagram is contained in the embedded chart --- the disc is fixed first
and the cuts afterwards.

\emph{Only the model's own double point is created.} In the basis $(v_0,u_0)$
the transverse coordinate of $c(t)$ is $1-t^2$, which equals $-3$ at both
endpoints, so the model's transverse excess over its endpoint chord is
$4-t^2>0$ for $-2<t<2$. Since $Bv_0=\tfrac{\ell}{12}(xv+yu)$ with $x>0$ and
$Bu_0=\tfrac{\ell}{12}u$, the physical transverse excess of the inserted arc
over the chord $[p_-,p_+]$ is exactly
\[
   \frac{\ell x}{12}\bigl(4-t^2\bigr)>0 .
\]
So the inserted interior lies strictly in $\xi>\xi(s_-)$ while both retained
tails lie strictly in $\xi<\xi(s_-)$: they meet only at the two joins. Together
with the shrinking of the previous paragraph, which keeps the inserted arc away
from every nonlocal part of the diagram, this \emph{proves} rather than assumes
that the only double point created is the model's own.

\emph{The replacement, and why the curve stays $C^\infty$ regular.} Replace the
sub-arc of $F$ between $p_-$ and $p_+$ by $\Phi\circ c$, modified near its two
endpoints as follows. At each join the two one-sided unit tangents already
agree, $\Phi c'(\pm2)$ being a positive multiple of $\Phi b'(\pm2)$ and that of
the old tangent, so the concatenation is $C^1$; it need not be $C^\infty$, and
the collar that repairs that is constructed here rather than described. An
earlier revision said only that one may ``interpolate the tangent angle by the
same device'', which does not say what curve results, and interpolating angles
moves the endpoint.

\emph{The collar, as a graph.} Work at the join $p_-$ first; the join at
$p_+$ is constructed after property (3) below, with its own signs printed
rather than left to "roles exchanged". In the chart coordinates
$(\xi,\eta)$ of the positive-turn chart --- $\xi=\langle\gamma-p,v\rangle$ with
$v=-Ju$, $\eta=\langle\gamma-p,u\rangle$ --- the old arc is a graph
$\xi=f(\eta)$, since $\eta'=\langle\gamma',u\rangle=\cos\theta>0$ there. Its
slope carries a sign that an earlier revision got wrong, and the sign is
load-bearing below, so it is computed:
$\xi'=\langle\gamma',v\rangle=-\sin\theta$, whence
\[
   f'(\eta)=\frac{\xi'}{\eta'}=-\tan\theta .
\]
For $\eta<\eta(p)$ the angle $\theta$ is strictly negative, $\theta$ being
strictly increasing with $\theta(0)=0$, so $f'>0$ there --- not $f'<0$, which is
what the earlier revision's $f'=\tan\theta$ gave. Let
$\eta_-=\eta(p_-)<\eta(p)$. The inserted arc leaves $p_-$ with the same unit
tangent, so near its start it is also a graph $\xi=g(\eta)$ with
$g(\eta_-)=f(\eta_-)$ and $g'(\eta_-)=f'(\eta_-)$; and because the model turns
strictly negatively its tangent angle only decreases from $\theta(s_-)<0$, so by
the same formula
\[
   g'>f'>0
\]
on that stretch. Two consequences are used below: $g>f$ on
$(\eta_-,\eta_-+\lambda]$, the two agreeing at $\eta_-$ with $g'>f'$; and at
every point of the collar the smaller slope is $f'(\eta)$, still positive. The
bound is pointwise of necessity: $f'=-\tan\theta$ \emph{decreases} along the
collar, $\theta$ increasing, so $0<f'(\eta)<f'(\eta_-)$ there and an endpoint
bound from the left end is unavailable --- an earlier revision claimed both
slopes bounded below by $f'(\eta_-)$, which $f'$ itself violates. Fix
$\lambda>0$ small enough that $[\eta_-,\eta_-+\lambda]$ lies both below
$\eta(p)$ and inside the stretch on which the inserted arc is a graph, and set,
on $[\eta_-,\eta_-+\lambda]$,
\[
   h(\eta)=\bigl(1-\varphi_\lambda(\eta)\bigr)f(\eta)+\varphi_\lambda(\eta)\,
   g(\eta),
   \qquad
   \varphi_\lambda(\eta)=\varphi\Bigl(\frac{\eta-\eta_-}{\lambda}\Bigr),
\]
with $\varphi$ the transition profile of Lemma~\ref{lem:rounding}. The modified
curve runs along the old arc up to $\eta_-$, along the graph of $h$ across the
collar, and along the inserted arc from $\eta_-+\lambda$ on. Three properties,
each proved from the formula.

\emph{(1) It is $C^\infty$ and regular, with positive speed.} $h$ is a $C^\infty$
function, and every derivative of $\varphi$ vanishes at $0$ and $1$, so $h$
agrees with $f$ to infinite order at $\eta_-$ and with $g$ to infinite order at
$\eta_-+\lambda$: the two joins are $C^\infty$. Parametrized by $\eta$, the
collar has velocity $h'(\eta)\,v+u$ in the frame $(v,u)$, of norm
$\sqrt{1+h'(\eta)^2}\geq1$, so its speed is positive and it is regular; being a
graph, it is embedded.

\emph{(2) No tangent of the collar equals $u$, and no smallness condition is
needed.} The tangent is parallel to $u$ exactly where $h'=0$, and
\[
   h'=(1-\varphi_\lambda)f'+\varphi_\lambda g'
      +\frac{\varphi'\bigl((\eta-\eta_-)/\lambda\bigr)}{\lambda}\,
       \bigl(g-f\bigr).
\]
Every term is nonnegative, and the sum of the first two is positive: it is the
convex combination $(1-\varphi_\lambda)f'+\varphi_\lambda g'$ of two positive
numbers --- each \emph{term} separately can vanish, $\varphi_\lambda$ being $0$
at the left end and $1$ at the right, which an earlier revision's "the first
two are positive" overlooked --- while the third term is
$\varphi'\cdot(g-f)/\lambda\geq0$, since $\varphi'\geq0$ and $g-f\geq0$ there,
the two agreeing at $\eta_-$ with $g'>f'$. Hence, pointwise,
\[
   h'(\eta)\geq(1-\varphi_\lambda)f'(\eta)+\varphi_\lambda g'(\eta)
   \geq f'(\eta)>0 ,
\]
the middle inequality because $g'>f'$, so $h'$ never vanishes and the collar
has no tangent equal to $u$; and none equal to $-u$ either, a graph over $\eta$ having
$\eta'>0$ throughout. An earlier revision, working from the wrong slope sign,
had both $f'$ and $g'$ negative, needed a Taylor bound on $g-f$ to control the
third term, and chose $\lambda$ small to make the sum negative. With the frame
computed the third term is on the same side as the other two and no choice of
$\lambda$ is required.

\emph{(3) It creates no double point and changes no turning.} Pointwise
$f\leq h\leq g$ on the collar --- the value is a convex combination and $g\geq f$
there, which is the separation the corrected slope chain supplies --- so the
collar lies in the region between the two graphs; that region is inside the
disc $\Delta$ and inside the embedded chart, where the only strands of the
diagram are the old arc --- whose collar stretch is removed --- and the inserted
arc. The collar is embedded by~(1) and meets those two only at its endpoints,
so no double point is created in it, and the model's own double point, at
$|t|=1$, is interior to the inserted arc and untouched. For the turning: the
collar's tangent angle is continuous, stays in $(-\pi/2,0)$ --- the slope
$h'$ being positive and finite, so the tangent angle $\theta$ has
$-\tan\theta=h'>0$ with $\cos\theta>0$ --- and takes at its ends exactly the
angles of the two arcs it joins, so the lift of the tangent
along the modified curve is the concatenation of the old lifts with an
interpolating stretch of the same endpoint values; the total tangent winding is
unchanged by its insertion. An earlier revision stopped at $C^1$
and the document then carried a lemma to recover smoothness. This sentence is what the downstream consumers of this
lemma read, the front construction below taking tangent directions of the
curve, and an intermediate revision of this proof deleted it while rewriting
the tail; it is restored here.

\emph{The collar at $p_+$.} The same three properties are now proved at the
other join, with its own signs printed: here the \emph{incoming} arc is the
inserted one and the \emph{outgoing} arc is the old one, and both slopes are
negative. Let $\eta_+=\eta(p_+)>\eta(p)$. On a stretch
$[\eta_+-\lambda_+,\eta_+]$ chosen above $\eta(p)$ and inside the stretches
on which both arcs are graphs, write $\xi=g(\eta)$ for the inserted arc and
$\xi=f(\eta)$ for the old arc extended backward from $p_+$; the two agree at
$\eta_+$ with common slope $m_+=-\tan\theta_+<0$, the angle
$\theta_+=\theta(s_+)$ lying in $(0,\tfrac\pi2)$. Just left of the join the
inserted arc turns strictly negatively into its endpoint, so its angle
exceeds $\theta_+$ there, while the old arc turns positively, so its angle
lies below $\theta_+$; by $\text{slope}=-\tan\theta$, decreasing in
$\theta$,
\[
   g'(\eta)<m_+<f'(\eta)<0
   \qquad\text{on }[\eta_+-\lambda_+,\eta_+),
\]
the outer inequality $f'<0$ because $\theta>0$ above $\eta(p)$. Integrating
$g'-f'<0$ backward from the common value at $\eta_+$ gives $g>f$ on
$[\eta_+-\lambda_+,\eta_+)$. Set
\[
   h=\bigl(1-\chi_{\lambda_+}\bigr)g+\chi_{\lambda_+}f,
   \qquad
   \chi_{\lambda_+}(\eta)=\varphi\Bigl(\frac{\eta-(\eta_+-\lambda_+)}{\lambda_+}\Bigr),
\]
with the same transition profile $\varphi$: the modified curve runs along the
inserted arc up to $\eta_+-\lambda_+$, along the graph of $h$ across the
collar, and along the old arc from $\eta_+$ on, the two joins $C^\infty$ by
the flat endpoint jets of $\varphi$ exactly as in (1). For the derivative,
\[
   h'=\bigl(1-\chi_{\lambda_+}\bigr)g'+\chi_{\lambda_+}f'
      +\frac{\varphi'\bigl((\eta-\eta_++\lambda_+)/\lambda_+\bigr)}{\lambda_+}
       \,\bigl(f-g\bigr),
\]
and the sign of $f-g$ in the cutoff term is exactly what the negativity of
the two slopes alone does not control: here $f-g\leq0$ by the separation just
integrated, and $\varphi'\geq0$, so the cutoff term is nonpositive, while the
convex part is a convex combination of two negative numbers. Hence,
pointwise,
\[
   h'(\eta)\leq\bigl(1-\chi_{\lambda_+}\bigr)g'(\eta)+\chi_{\lambda_+}f'(\eta)
   \leq f'(\eta)<0 ,
\]
the middle inequality because $g'<f'$, and the bound pointwise for the
mirrored reason: $f'$ varies along the collar and no endpoint bound is
available. So $h'$ never vanishes, and this collar --- a graph over $\eta$
with $\eta'>0$ throughout --- has no tangent equal to $u$ and none equal to
$-u$; its tangent angle stays in $(0,\tfrac\pi2)$, with
$-\tan\theta=h'<0$ and $\cos\theta>0$, and takes at its ends exactly the
angles of the two arcs it joins, so the lift concatenation of (3) applies to
it verbatim and the total tangent winding is unchanged. Pointwise
$f\leq h\leq g$, the value being a convex combination and $g\geq f$ there, so
the collar lies in the region between the two graphs, inside the disc
$\Delta$ and the embedded chart, and it is embedded and meets the two arcs
only at its endpoints: no double point is created, by the argument of (3)
unchanged.

\emph{The four conclusions, separately.} (ii): $c'(t)=(2t,1-3t^2)$ is parallel to
$u_0$ only at $t=0$, where $c'(0)=-u_0$; since $A$ is invertible with
$Au_0=u$, the inserted arc has no tangent $u$ and exactly one tangent $-u$, and
the retained tails have neither, their angles lying in $(-\tfrac\pi2,\tfrac\pi2)$
away from $0$.

(iii): if $c(s)=c(t)$ then $s=\pm t$, and the second coordinate forces
$2t(1-t^2)=0$, so the only pair of distinct parameters is $\{-1,1\}$: exactly
one double point. With the later branch over the earlier one its sign is that of
$\det(c'(1),c'(-1))=-8<0$, and $\det B>0$ preserves it.

(iv) for $\rot$: Let $R$ be the rotation carrying the positive orthonormal basis
$(v_0,u_0)$ to $(v,u)$ and put $C=R^{-1}A$. Relative to $(v_0,u_0)$,
$C$ has matrix
$\left(\begin{smallmatrix}x&0\\y&1\end{smallmatrix}\right)$ with $x>0$, so
$C_t=\left(\begin{smallmatrix}1-t+tx&0\\ty&1\end{smallmatrix}\right)$
joins $I$ to $C$ inside $\mathrm{GL}^+(2,\mathbb R)$. If $R_t$ rotates
through $t$ times any fixed angle representing $R$, first $C_t$ and then
$R_tC$ give a path $A_t$ from $I$ to $A=RC$ in that group. Apply
$z\mapsto A_tz/|A_tz|$ to the closed direction loop obtained by following
the tangent path of $c$ and the tangent path of $b$ backwards.
Lemma~\ref{lem:turnlift}(iii) therefore preserves their compatible endpoint
lift-increment difference. The tangent of $b$ follows the short positive arc between the
endpoint rays; the tangent of $c$ follows the complementary clockwise arc, since
$\det(c',c'')=-2(1+3t^2)<0$ and it passes through $-u_0$ at $t=0$; so their
relative winding is $-1$. The old central arc also follows the short positive
arc, its lifted sweep $\theta(s_+)-\theta(s_-)$ lying in $(0,\pi)$. Hence Lemma~\ref{lem:turnlift}(iii) says that the replacement changes the
closed curve's rotation by exactly $-1$. For
$w$: the removed arc was embedded and carried no crossing, so the writhe changes
by the one new negative crossing, that is by $-1$.

\emph{The polynomial conclusion, without a knot-category detour.}
The construction just completed also proves that $F'$ remains in the lemma's
input class.  It replaces one oriented arc by one $C^\infty$ regular oriented
arc, leaves the component count unchanged, and creates exactly one transverse
double point in a disc meeting no other strand.  Thus its double points remain
finite and transverse and no triple point is created.

Let $F^{\circ}$ be the oriented diagram obtained from $F'$ by deleting the
unique monogon in $\Delta$ by a Reidemeister-I move.  The move is available:
the preceding separation argument shows that the monogon is disjoint from
all other strands, and the crossing calculation shows it is the unique new
double point.  It replaces that monogon by one crossing-free regular arc in
$\Delta$, so $F^{\circ}$ is again a one-component immersed-circle diagram with
finite transverse double points and no triple points.  Reidemeister-I
invariance in Axiom~\ref{ax:homfly} gives $P_{F'}=P_{F^{\circ}}$.

Outside $\Delta$, the diagrams $F^{\circ}$ and $F$ coincide.  Inside
$\Delta$, each has one crossing-free oriented arc joining the same two
boundary points in the same traversal direction.  Match every marked
preimage outside that local traversal interval with the identical marked
preimage of the other diagram.  The local intervals contain no marked
preimage, so this bijection preserves cyclic order, crossing pairs,
over/under positions and signs: it is a record isomorphism.  Both underlying
curves are one-component immersed circles with transverse double points and
no triple points, so Axiom~\ref{ax:gausscode} says that the diagrams present
the same oriented link.  Axiom~\ref{ax:homfly} therefore gives
$P_{F^{\circ}}=P_F$, hence $P_{F'}=P_F$.  Equality outside $\Delta$ proves the
remaining clause of~(i).
\end{proof}
```

## CV:thm:carrierfloor — PROVE

reference/R/CV/d3_floor.tex:736–807

```tex
\begin{theorem}[global reversal, rounding record, vertical tangencies and the carrier floor]\label{thm:carrierfloor}
\begin{enumerate}
\item[(R)] Here $\rot$ is as in Definition~\ref{def:rot}.
Let $K$ be an oriented knot and $-K$ the same knot with its orientation
reversed. Then $P_{-K}=P_{K}$. Moreover a diagram of $-K$ obtained by reversing
the orientation of a diagram of $K$ has the same crossing signs, the same
writhe, and rotation number of the underlying plane curve negated.
\item[(A)] Let $L$ and $D$ satisfy the hypotheses of Lemma~\ref{lem:rounding}. For every
$\varepsilon\in(0,\varepsilon_0(L))$, the construction in the proof of that
lemma returns \emph{one} curve and \emph{one} diagram at those data: the
junction inserted at the corner $q_i$ is determined by $\varepsilon$, by the
two incident unit directions and by the transition profile, which is fixed once
and for all in that proof and is not chosen per corner or per curve; the arc
length $\ell$ is then determined by the endpoint condition, and the rest of the
curve is $L$ itself. Write
\[
   \mathrm{Round}(L,D,\varepsilon)=(L_\varepsilon,D_\varepsilon)
\]
for that pair, the \emph{rounding record} of $(L,D)$ at $\varepsilon$, and call
$L_\varepsilon$ the rounded curve and $D_\varepsilon$ the rounded diagram. The
record exists to be quantified over: an earlier revision, written when the
profile was a per-use choice, had every consumer say "every curve the lemma
produces", which is a quantifier over an unnamed family and reads differently
in each consumer.
\item[(B)] Here $\rot$ is as in Definition~\ref{def:rot}.
Let $L$ be a diagrammatic closed polygon (Definition~\ref{def:diagrammatic})
whose principal turns all exist and are nonzero, carrying a diagram $D$, and
assume, after reversing the orientation of $L$ if necessary, that either every
principal turn is positive, or exactly one is negative. Put $R=|\rot(L)|$. Then
there are a direction $u\in S^1$ and an $\varepsilon_1>0$ such that \emph{for
every} $\varepsilon\in(0,\varepsilon_1)$ the rounded curve $L_\varepsilon$ of
the record $\mathrm{Round}(L,D,\varepsilon)$
from clause~(A) has exactly $R$ points at which its unit
tangent equals $u$ and exactly $R$ at which it equals $-u$; at each of them the
tangent crosses that direction in the positive sense. The hypotheses are stated
here rather than imported by "as in Lemma~\ref{lem:rounding}", and the
clearance is produced here rather than borrowed from that lemma's existential
one. The object is named rather than quantified over: the record is one curve
and one diagram at each $\varepsilon$, the profile being fixed once and for all,
and an earlier revision said "every curve the lemma produces" because at the
time the profile was a per-use choice.
\item[(C)] Here $\rot$ is as in Definition~\ref{def:rot}.
Let $D$ be an oriented knot diagram all of whose crossings are positive, with
writhe $w$, whose underlying plane curve is a closed polygon $L$ with all
principal turns existing, \emph{nonzero}, and of magnitude below $\pi$, with
finitely many double points, all transversal, with no triple points, none of
them a corner of $L$, and no corner of $L$ lying on a non-incident edge; and let
$R$ be the absolute value of its Whitney rotation number.  The
finiteness/transversality and the two corner conditions are what
Lemma~\ref{lem:rounding} asks of its input.  The no-triple condition repeats the
shared-image clause of Definition~\ref{def:diagrammatic}; it is preserved by
rounding and is needed below when diagram records are compared.  These
conditions are stated here so that no generic parent polygon is assumed. Assume that, after reversing the
orientation if necessary --- which by clause~(R) changes neither
$P_D$, nor the crossings and their signs, nor $w$, nor $R$ --- either every
principal turn is positive, or exactly one is negative and every other is
positive. Then
\begin{equation}
\min\deg_a P_D(a,z)\;\geq\;1-w-R,
\label{eq:floor}
\end{equation}
and the same bound holds for $f_D(a)=[z^0]P_D(a,z)$ whenever $f_D\neq0$.
\item[(D)] Here $\rot$ is as in Definition~\ref{def:rot}.
Let $P$ be generic, let $S\in\Ind(G_P)$ and let $L$ be a carrier of $S$ carrying
no residual piece, so that $P_{S,L}=1$ and $w_{S,L}=0$ by
Definition~\ref{def:X1}'s empty conventions --- an earlier revision wrote those
two symbols with $S$ never introduced --- and suppose that all its principal turns are nonzero and that,
after reversing the orientation if necessary, either every turn is positive or
exactly one is negative. Then $R(L)\geq1$ and
$\min\deg_a P_{S,L}=0\geq 1-w_{S,L}-R(L)$.
\end{enumerate}
\end{theorem}
```

reference/R/CV/d3_floor.tex:808–1012

```tex
\begin{proof}
\emph{Clause (R).}
Reversing the orientation of all components of a link sends a skein triple
$(L_+,L_-,L_0)$ to a skein triple: the sign of a crossing is
$\sgn\det(u_{\mathrm{over}},u_{\mathrm{under}})$ and reversing both strands
replaces both vectors by their negatives, leaving the determinant unchanged, and
the oriented smoothing of the reversed diagram is the reverse of the oriented
smoothing. So $L\mapsto P_{-L}$ satisfies the defining skein of
Axiom~\ref{ax:homfly}, and it sends the unknot to $1$; by the uniqueness clause
it equals $L\mapsto P_L$. The diagram statements have the same scope. Every crossing sign is a
determinant of two reversed vectors, so the writhe is unchanged. For a
polygonal underlying curve every principal turn changes sign and
Lemma~\ref{lem:turnlift}(ii) negates rotation. For a $C^1$ regular curve,
if $\theta$ lifts its normalised tangent, then $\theta(1-s)+\pi$ lifts the
reversed tangent with the negative endpoint increment, as in
Lemma~\ref{lem:turnlift}(i).

\emph{Clause (A).} The transition profile is fixed once and for all in the proof of
Lemma~\ref{lem:rounding}.  At each corner, $\varepsilon$ and the two incident
unit directions determine that profile's junction, and the endpoint condition
determines its length $\ell$; outside the rounding discs the curve is $L$, and
the diagram data are inherited.  Thus the named construction returns one
specified pair at every allowed $\varepsilon$.  This asserts uniqueness of the
fixed construction's record, not uniqueness among all possible smoothings.

\emph{Clause (B).}
Reversing the orientation of $L$ negates every principal turn and the signed rotation and
preserves every self-crossing sign, so perform the allowed normalization once. In the
uniform case $\rot(L)=R\geq1$ by Lemma~\ref{lem:uniformrot}(i); in the one-dissent case the same holds by Lemma~\ref{lem:uniformrot}(ii).

Take $\varepsilon_1=\varepsilon_0(L)$, the clearance of Lemma~\ref{lem:rounding}.
Choose $u\in S^1$ so that neither $u$ nor $-u$ is an edge direction and, in the
one-dissent case, neither lies in the negative turn's closed swept arc $A$, of
length $\alpha:=|\tau_-|<\pi$. Such $u$ exists: in the one-dissent case $A\cup(-A)$
has length at most $2\alpha<2\pi$, while in the uniform case there is no such arc; the additional
forbidden set of edge directions and their antipodes is finite. This choice depends only on $L$. Fix an argument $\phi$ of $u$.

Fix $\varepsilon\in(0,\varepsilon_1)$, write
$(L_\varepsilon,D_\varepsilon)=\mathrm{Round}(L,D,\varepsilon)$, and let $T$ be
its unit-tangent map. Parameterize the rounded traversal by $s\in[0,1]$, with
$s=0$ in the interior of a straight part; because $u,-u$ are not edge directions, its tangent
is congruent to neither $\phi$ nor $\phi+\pi$. Concatenating straight-part arguments
with the junction lifts supplied by Lemma~\ref{lem:rounding}(b) gives a continuous
$\theta\colon[0,1]\to\mathbb R$, starting at an argument $\theta(0)$ of $T(0)$.
Since $T(1)=T(0)$, write $\theta(1)=\theta(0)+2\pi m$ for an integer $m$.

Choose a direction $r$ not parallel to any edge, with argument $\gamma$. The
change across junction $i$ of $\lfloor(\theta-\gamma)/(2\pi)\rfloor$ is $+1$,
$-1$ or $0$ in exactly the three determinant cases defining $\epsilon_i$ in
Definition~\ref{def:rot}. Indeed the same clause makes the lifted change
$\tau_i$, and $|\tau_i|<\pi$ permits at most one crossed level, in its
signed direction; there is no change on a straight part. Telescoping and
$\lfloor q+m\rfloor-\lfloor q\rfloor=m$ give
$m=\sum_i\epsilon_i=\rot(L)=R$. Thus
\[
 \theta(1)=\theta(0)+2\pi R.                                  \tag{*}
\]

Fix $\beta=\phi$ or $\phi+\pi$. Because $u,-u$ are not edge directions, no
level $\beta+2\pi k$ is met on a straight part or at a junction endpoint; by
the choice of $u$, none is met on the decreasing junction. Hence floor jumps
occur only in increasing junctions and never elsewhere. Lemma~\ref{lem:rounding}(b)
makes each occurrence unique with positive angular derivative. Put
\[
 x=\frac{\theta(0)-\phi}{2\pi},\qquad
 y=\frac{\theta(0)-(\phi+\pi)}{2\pi}.
\]
For $u$, (*) and the integer floor identity give, separately,
\[
 \#T^{-1}(u)=\lfloor x+R\rfloor-\lfloor x\rfloor=R.
\]
For $-u$, the same argument at the other levels gives
\[
 \#T^{-1}(-u)=\lfloor y+R\rfloor-\lfloor y\rfloor=R.
\]
There are finitely many junctions, so the preimages are finite; their positive derivatives prove the assertion for arbitrary $\varepsilon$.

\emph{Clause (C).} Fix $\varepsilon\in(0,\varepsilon_1)$ with $\varepsilon_1$ the clearance of
clause~(B) and pass to the rounding record
$(L_\varepsilon,D_\varepsilon)=\mathrm{Round}(L,D,\varepsilon)$ of
clause~(A) --- one curve and one diagram, not a member
of an unnamed family. By Lemma~\ref{lem:rounding}(c),(d) the diagram, its
crossings, its writhe and its rotation number are unchanged, and by
clause~(B) there is a direction $u$ met by the tangent of
$L_\varepsilon$ exactly $R$ times, each time positively, and likewise for
$-u$. Rotate coordinates so
that $u$ is the downward vertical. The rounded diagram then has exactly $R$
downward vertical tangencies and $R$ upward ones.

Switch every crossing. The result is a diagram $\overline D$ of the mirror knot,
with the same underlying plane curve --- hence the same tangencies --- and with
writhe $-w$; every crossing of $\overline D$ is negative. Apply
Lemma~\ref{lem:curl} at each of the $R$ downward vertical tangencies; they are
isolated, lie in the interiors of positively turning rounding arcs
(clause~(B)), and the rounding discs are pairwise disjoint and
meet no crossing, by the choice of $\varepsilon$ in the proof of
Lemma~\ref{lem:rounding}, so the $R$ discs are
disjoint and each replacement leaves the others intact. Call the result $T$. By
Lemma~\ref{lem:curl}, $P_T=P_{\overline D}$, $T$ has no downward vertical
tangency, and it has writhe
\[
w(T)=-w-R .
\]
Every crossing of $T$ is negative: the old ones by the switch, the $R$ new ones by
Lemma~\ref{lem:curl}(iii).

We now construct the transverse lift rather than import a
front criterion.  Write the smooth regular parametrisation of $T$ as
$s\mapsto(x(s),z(s))$, put
\[
 v(s)=\sqrt{x'(s)^2+z'(s)^2},\qquad
 y_0(s)=-\frac{x'(s)}{v(s)+z'(s)},
\]
and use the convention that, in the $xz$ projection, the branch with smaller
$y$-coordinate is drawn over.  Since $T$ has no downward vertical tangency,
$v+z'>0$ everywhere: equality would force $x'=0$ and $z'<0$.  Thus $y_0$ is
smooth and periodic, and direct algebra, with no division by $x'$, gives
\[
 z'-y_0x'=z'+\frac{x'^2}{v+z'}
 =z'+\frac{v^2-z'^2}{v+z'}=v>0.                 \tag{*}
\]

It remains only to impose the crossing order.  At a crossing branch there is
no vertical tangency, so put $m=z'/x'$.  The strict inequality in~(*) permits
$y<m$ on a rightward branch and $y>m$ on a leftward branch.  For every crossing
choose admissible constants $c_{\rm O}<c_{\rm U}$ at its over- and underpassing
preimages.  Such a choice is automatic if the overpass points right: after
choosing any admissible $c_{\rm U}$, take
$c_{\rm O}<\min\{m_{\rm O},c_{\rm U}\}$.  If both point left, choose any
$c_{\rm O}>m_{\rm O}$ and then
$c_{\rm U}>\max\{m_{\rm U},c_{\rm O}\}$.  The only remaining case has
$x'_{\rm O}<0<x'_{\rm U}$.  Every crossing of $T$ is negative, and here
\[
 0>\det(t_{\rm O},t_{\rm U})
   =x'_{\rm O}x'_{\rm U}(m_{\rm U}-m_{\rm O}).
\]
Since $x'_{\rm O}x'_{\rm U}<0$, this says $m_{\rm O}<m_{\rm U}$; choose
$m_{\rm O}<c_{\rm O}<c_{\rm U}<m_{\rm U}$.  These are exactly the two allowed
half-lines and the required over/under order.

There are finitely many crossing preimages.  Around each one $s_j$, choose
pairwise disjoint cyclic parameter intervals $(\alpha_j,\beta_j)$ so small that
$z'-c_jx'>0$ throughout.  Using the explicit flat transition profile
$\varphi$ displayed in the proof of Lemma~\ref{lem:rounding}, define a smooth
bump on the circle by
\[
 \psi_j(s)=
 \begin{cases}
 \varphi\!\left((s-\alpha_j)/(s_j-\alpha_j)\right),&
       \alpha_j\le s\le s_j,\\
 \varphi\!\left((\beta_j-s)/(\beta_j-s_j)\right),&
       s_j\le s\le\beta_j,\\
 0,&\text{otherwise}.
 \end{cases}
\]
All endpoint derivatives are zero, so this is smooth, equals one at $s_j$ and
has support in that interval.  Set
\[
 y=y_0+\sum_j\psi_j(c_j-y_0).
\]
The supports are disjoint.  On the $j$-th one,
\[
 z'-yx'=(1-\psi_j)(z'-y_0x')+\psi_j(z'-c_jx')>0,
\]
and outside them this is~(*).  Hence $y$ is smooth and periodic and the lift
$s\mapsto(x(s),y(s),z(s))$ is positively transverse to $dz-y\,dx$.

Finally the lift is regular because its $xz$ projection is immersed.  If two
lifted points agreed, their projected points would agree; the only distinct
parameters with that property are the two preimages of a listed double point,
and there $c_{\rm O}<c_{\rm U}$.  Thus the lift is injective, hence, by
compactness of the parameter circle, an embedded transverse knot.  Its front
and its smaller-$y$ over/under assignments are exactly $T$.

By Axiom~\ref{ax:etnyre}, $\operatorname{sl}(T)=w(T)=-w-R$. Since
$P_T=P_{\overline D}$, Axiom~\ref{ax:slbound} applied to $T$ gives
\[
\max\deg_a P_{\overline D}\;\leq\;-\operatorname{sl}(T)-1\;=\;w+R-1 .
\]
For every oriented-link isotopy class $K$, put
$\mathcal M(K)=P_{\overline K}(a,z)$. Mirroring exchanges $L_+$ with $L_-$
and fixes $L_0$, so the defining skein of Axiom~\ref{ax:homfly} on the
mirrored triple, multiplied by $-1$, is
\[
 a^{-1}\mathcal M(L_+)-a\mathcal M(L_-)=-z\,\mathcal M(L_0),
 \qquad \mathcal M(\bigcirc)=1.
\]
The substitution $(a,z)\mapsto(a^{-1},-z)$ is involutive, so applying it to
the uniqueness clause of Axiom~\ref{ax:homfly} gives uniqueness for these two
conditions. The assignment $K\mapsto P_K(a^{-1},-z)$ satisfies them; hence
$P_{\overline K}(a,z)=P_K(a^{-1},-z)$. As a Laurent-ring automorphism, the
substitution negates every $a$-exponent and cannot cancel a nonzero extreme
coefficient. Hence
$\max\deg_a P_{\overline D}=-\min\deg_a P_D$, and the displayed bound becomes
$\min\deg_a P_D=-\max\deg_a P_{\overline D}\geq1-w-R$, which is
\eqref{eq:floor}. Finally, the support of $f_D$ is contained in the support of
$P_D$, so the same bound holds for it when it is nonzero.

\emph{Clause (D).} In the uniform case $|\rot(L)|\geq1$ by Lemma~\ref{lem:uniformrot}(i); in the
one-dissent case $\rot(L)\geq1$ by Lemma~\ref{lem:uniformrot}(ii). Either way
$R(L)\geq1$, so $1-0-R(L)\leq0=\min\deg_a1$. In particular the hypothesis is met by every carrier of a live support
(Definition~\ref{def:wind}), and it is met by the marked halves of the
one-dissent geometry produced in the vertex-on-edge section, where that is
proved at the point of use.
\end{proof}
```

## CV:lem:pieceintrinsic — PROVE

reference/R/CV/d6_vertexedge.tex:56–74

```tex
\begin{lemma}[carrier restriction is the intrinsic piece diagram]
\label{lem:pieceintrinsic}
Let $P$ be generic, $S\in\Ind(G_P)$, and let $H$ be a residual piece of $S$,
carried by the carrier $L$ (Lemma~\ref{lem:carriers}(iv)). Let $D_L(H)$ be the
diagram obtained from $L$ by retaining exactly the crossings of $H$, each
resolved by the divide convention of Definition~\ref{def:piecediagram}, and
erasing all others; and let $D_P(H)$ be the intrinsic piece diagram of that
definition, obtained from the parent polygon $P$ by retaining exactly the same
crossings under the same convention. Throughout, that a crossing \emph{lies on}
a carrier means that both of its traversal preimages belong to that carrier,
which is the condition Lemma~\ref{lem:carriers}(iv) supplies.
Then the identity map on the visits of $H$ is a record isomorphism
(Definition~\ref{def:record}) from the record of $D_L(H)$ to the record of
$D_P(H)$. Consequently they present the same oriented link
(Axiom~\ref{ax:gausscode}), so
\[
   P_{D_L(H)}=P_H,\qquad w\bigl(D_L(H)\bigr)=|H| .
\]
\end{lemma}
```

reference/R/CV/d6_vertexedge.tex:75–115

```tex
\begin{proof}
\emph{Same double points.} Smoothing at a point $c\in S$ replaces the two
transversally crossing branches by two disjoint arcs inside a disc containing no
other double point, so it destroys the double point $c$ and creates none. Hence
the double points of $L$ are exactly the double points of $P$ that lie on $L$
and are not in $S$. Every label of $H$ has both of its visits on $L$ and
$H\cap S=\varnothing$, so each is a double point of $L$; and both diagrams
retain exactly those and no others.

\emph{Same over/under and signs.} The divide convention
(Definition~\ref{def:piecediagram}) reads the over/under at a double point from
the two branch directions there, and the sign of a crossing is read from the
same two directions with the orientation. Neither is changed by a smoothing
performed at a different point, which alters the curve only inside a disc
containing no other double point. Every crossing is positive in both diagrams,
so both writhes equal $|H|$.

\emph{Same cyclic order.} The traversal of $D_P(H)$ is the traversal circle
$\Gamma$ itself, so the cyclic order of the $2|H|$ visits is their order on
$\Gamma$. By Lemma~\ref{lem:carrierword} the marked points lying on $L$ are
traversed by $L$ in the order induced from $\Gamma$, and the visits of $H$ are
among them; restricting to those gives the same cyclic word.

\emph{The isomorphism.} The two records are not equal: their traversal circles
are different circles, one running around $P$ and one around $L$. What the three
paragraphs give is the map. Let $\varphi$ send each visit of $H$ on the
traversal circle of $D_L(H)$ to the same visit on the traversal circle of
$D_P(H)$ --- the same point of the plane, reached by the same branch --- which
is a bijection of marked-point sets by the first paragraph. It preserves the
cyclic order by the third, carries double points to double points because the
pairing is by label in both, and preserves the over/under designation and the
sign by the second. Those are conditions (a) to (d) of
Definition~\ref{def:record}, so $\varphi$ is a record isomorphism, and
Axiom~\ref{ax:gausscode} identifies the links.

An earlier revision of this lemma said the two records were \emph{equal}. They
are not: equality of records presupposes
one traversal circle, which is exactly what these two diagrams do not share.
Nothing in the three paragraphs changes; what changes is that the map they
produce is now named, and the definition it satisfies is printed.
\end{proof}
```

## CV:lem:homflyrows — PROVE

reference/R/CV/d6_vertexedge.tex:117–141

```tex
\begin{lemma}[HOMFLY products and the two-component $z^{-1}$ row]
\label{lem:homflyrows}
Put $R=\mathbb Z[a^{\pm1},z^{\pm1}]$ and
$\delta=(a-a^{-1})/z\in R$.
\begin{enumerate}
\item[(i)] For oriented knots $K,J$,
\[
 P_{K\# J}=P_KP_J;
\]
and for an oriented knot $K$ and an oriented link $J$,
\[
 P_{K\sqcup J}=\delta P_KP_J.
\]
\item[(ii)] Let $D$ be an oriented link diagram with ordered components
$D_1,D_2$ and linking number $\lambda$. Then
\[
 [z^{-1}]P_D=(a-a^{-1})a^{-2\lambda}
       [z^0]\bigl(P_{D_1}P_{D_2}\bigr).
\]
\item[(iii)] Consequently, for oriented knots $K_1,\dots,K_n$ ($n\geq1$),
\[
 P_{K_1\sqcup\dots\sqcup K_n}=\delta^{\,n-1}P_{K_1}\cdots P_{K_n}.
\]
\end{enumerate}
\end{lemma}
```

reference/R/CV/d6_vertexedge.tex:142–261

```tex
\begin{proof}
A \emph{based oriented link} is an oriented link with one distinguished
nonsingular point $p$ on one distinguished component; isotopies carry $p$ and
that component. Fix an oriented knot $K$. For a based link $(J,p)$ define
\[
   F_K(J,p)=P_{K\#_pJ},\qquad G_K(J,p)=P_KP_J.
\]
Here $K\#_pJ$ is made in a ball at $p$, disjoint from the rest of $J$, by
deleting a short oriented arc through $p$, cutting a copy of $K$ at a short
oriented arc, and using the orientation-compatible cross-pairing of incoming
and outgoing endpoints. Two sufficiently small choices of ball and arc are
related by an isotopy supported near $p$, and a based ambient isotopy carries
the ball and insertion with it. Thus $F_K$ is well defined on based isotopy
classes. Both $F_K$ and $G_K$ satisfy the HOMFLY--PT skein relation in every
disc disjoint from $p$ (Axiom~\ref{ax:homfly}): the insertion at $p$ is outside
the disc and therefore commutes with the local switch and oriented smoothing.

We use the following relative uniqueness argument, printed because unbased
uniqueness alone does not apply to a marked operation. Suppose two $R$-valued
invariants of based oriented links satisfy that skein relation away from the
mark and agree on every based unlink. Draw a based link diagram. Using $p$ as
the first traversal basepoint, choose auxiliary basepoints on the other
components and order those components after the marked one. Traverse the
oriented components in that order. Call a crossing \emph{bad} when its first
visit is on the underpassing branch. We prove equality by lexicographic
induction on
\[
   (\text{number of crossings},\ \text{number of bad crossings}).
\]
If a bad crossing is present, switch it. Its first visit becomes over, so the
crossing count is unchanged and the bad count drops by one; no other crossing
or first-visit order changes. The oriented smoothing has one fewer crossing.
Its disc misses $p$, so the marked point survives and the unique resulting
component containing it is distinguished; give all remaining components fresh
auxiliary basepoints and an order. For either invariant $Q$, if the original
crossing is $L_+$, solve the skein relation as
\[
   Q(L_+)=a^{-2}Q(L_-)+a^{-1}zQ(L_0);
\]
if it is $L_-$, solve it as
\[
   Q(L_-)=a^2Q(L_+)-azQ(L_0).
\]
Only the units $a^{\pm1}$ are used. The induction hypotheses for the switched
and smoothed diagrams give equality at the original diagram.

If there is no bad crossing, the ordered based diagram is descending. Keep a
small arc at the current component's basepoint fixed. Starting just after it
and following the orientation, pull each successive already-traversed arc
upward and across the still-untraversed diagram. At every crossing that moving
arc is the overpassing branch, so the pull crosses no strand. Successively
remove all self-crossings of that component; because its visits precede those
of every later component, it also passes over every later component and can be
slid into a disjoint ball as a round circle. For the first component the fixed
arc contains $p$, so this is rel the mark. Repeat in the chosen component
order. The result is the based unlink with the same number of components.
Thus agreement on based unlinks closes the induction.

Apply relative uniqueness first to $F_K,G_K$. On the based $r$-component
unlink $U_r$, with $U_0$ denoting no extra split component,
Definition~\ref{def:homfly} gives
\[
 F_K(U_r,p)=P_{K\sqcup U_{r-1}}=\delta^{r-1}P_K
 =P_KP_{U_r}=G_K(U_r,p).
\]
Hence $P_{K\#_pJ}=P_KP_J$. For the split operation put $K$ in a ball
disjoint from $J$ and define
\[
 F_K^{\sqcup}(J,p)=P_{K\sqcup J},\qquad
 G_K^{\sqcup}(J,p)=\delta P_KP_J.
\]
These again satisfy the skein relation away from $p$, and repeated use of the
split-circle identity in Definition~\ref{def:homfly} gives, on $U_r$,
\[
 F_K^{\sqcup}(U_r,p)=P_{K\sqcup U_r}=\delta^rP_K
 =\delta P_KP_{U_r}=G_K^{\sqcup}(U_r,p).
\]
Relative uniqueness proves $P_{K\sqcup J}=\delta P_KP_J$ for every based
oriented link $J$; this is the split identity of~(i). Clause~(iii) follows by
induction on $n$: the case $n=1$ is trivial, and
$K_1\sqcup(K_2\sqcup\dots\sqcup K_n)$ applies~(i)'s split identity with knot
$K_1$ and link $K_2\sqcup\dots\sqcup K_n$.

For~(ii), put $h(E)=[z^{-1}]P_E$. At a mixed crossing of a two-component
diagram, the oriented smoothing $E_0$ is a knot. Extracting the $z^{-1}$
coefficient from the skein relation gives
\[
 a h(E_+)-a^{-1}h(E_-)=[z^{-2}]P_{E_0}=0.
\]
The last equality uses the full retained clause
$P_{E_0}\in\mathbb Z[a^{\pm1},z^2]$: this is a polynomial ring in $z^2$, so
its $z$-powers are nonnegative as well as even. Thus
$h(E_+)=a^{-2}h(E_-)$. With the convention
$\lambda_+=\lambda_-+1$ at a positive versus negative mixed crossing,
$a^{2\lambda(E)}h(E)$ is invariant under every mixed crossing switch.
No self-crossing is switched: its oriented smoothing has three components,
not a knot, so the displayed vanishing is unavailable.

Switch precisely the mixed crossings at which component $D_1$ passes under
$D_2$. In the resulting diagram $D^\uparrow$, $D_1$ passes over $D_2$ at every
mixed projected intersection. Realize its self-crossings by strict local height
differences. Translate the whole first component upward and the whole second
component downward. Every mixed height gap strictly increases, the
self-crossing gaps are unchanged, and no other projected pair can collide.
This is an isotopy through embeddings; for a large translation a horizontal
plane separates the two components. Their knot types are still $D_1,D_2$ and
the endpoint is split, so its linking number is zero. Mixed-switch invariance
and~(i) now give
\[
\begin{aligned}
 h(D)
 &=a^{-2\lambda}h(D^\uparrow)
  =a^{-2\lambda}[z^{-1}]
       \bigl(\delta P_{D_1}P_{D_2}\bigr)\\
 &=a^{-2\lambda}(a-a^{-1})
       [z^0]\bigl(P_{D_1}P_{D_2}\bigr),
\end{aligned}
\]
which is~(ii).
\end{proof}
```

## CV:cor:groupedknot — PROVE

reference/R/CV/d6_vertexedge.tex:263–298

```tex
\begin{corollary}[interlacement connected sums and the grouped carrier]\label{cor:groupedknot}
\begin{enumerate}
\item[(A)] Let $S\in\Ind(G_P)$, let $L$ be a carrier of $S$ bearing at least one residual
piece, and let
\[
   W=\bigcup\{\,H: H\text{ a residual piece of }S\text{ carried by }L\,\}
\]
be the \emph{union of their label sets} --- a set of crossing labels, not a set
of pieces. By Lemma~\ref{lem:piececurve} Step 2, $W$ is exactly the set of
self-crossings of $L$, so the diagram $D(W)$ obtained from $L$ by retaining
exactly the labels of $W$, each resolved by the divide convention, and erasing
all others, is $L$ itself carrying all of its own crossings; no realization
argument is needed. Let $W=W_1\sqcup\dots\sqcup W_k$, $k\geq1$, be the partition
of $W$ into the connected components of the interlacement graph induced on $W$;
these are the label sets of the residual pieces. The components can be indexed
and equipped with a fixed ordered binary parenthesization $\mathcal T$ such that
\[
D(W)\;\cong\;\#_{\mathcal T}
   \bigl(D(W_1),\dots,D(W_k)\bigr),
\qquad
P_{D(W)}=\prod_{i=1}^{k}P_{D(W_i)} .
\]
Here $\#_{\mathcal T}$ is evaluated recursively: a leaf has value $D(W_i)$
and an internal node has the connected sum of its two ordered child values
with the displayed parenthesization. In particular, when $k=1$,
$\#_{\mathcal T}(D(W_1))=D(W_1)$.
\item[(B)] Let $S\in\Ind(G_P)$ and let $L$ be a carrier of $S$ bearing the residual pieces
$H_1,\dots,H_k$ with $k\geq1$. (If $L$ bears no piece the assertion is
Theorem~\ref{thm:carrierfloor}(D): $P_{S,L}=1$, $w_{S,L}=0$, and there is nothing to
decompose. Clause~(A) is stated for a nonempty label set and
is not applied in that case.) Then the diagram obtained from $L$ by retaining exactly the
crossings of $H_1\cup\dots\cup H_k$ is a knot diagram whose HOMFLY polynomial is
$P_{S,L}=\prod_iP_{H_i}$, whose writhe is $w_{S,L}=\sum_i|H_i|$, and whose
underlying plane curve is $L$, which has no triple points.
\end{enumerate}
\end{corollary}
```

reference/R/CV/d6_vertexedge.tex:299–439

```tex
\begin{proof}
\emph{Clause (A).}
Read the carrier as a cyclic word in the labels of $W$, each label occurring
twice. Call a \emph{gap} a position between two consecutive visits.

\emph{Gap lemma.} Fix a connected component $W_i$. A gap has no intrinsic pair
of sides, so the coordinate is taken per chord: for a gap $g$ and a chord
$x\in W_i$, record which of the two components of the traversal circle minus the
two visits of $x$ contains $g$. Ranging over $x\in W_i$ this is a binary vector
indexed by the chords of $W_i$, the \emph{side vector} of $g$. Distinct gaps of $W_i$ have
distinct side vectors. Suppose two distinct gaps had the same vector. The
oriented interval between the two cuts then contains either both or neither
endpoint of every chord of $W_i$; since the gaps are distinct, both the
interval and its complement contain visits of $W_i$. So the labels of $W_i$
split into two nonempty sets, one with both endpoints inside and one with both
endpoints outside, and no chord of one set interlaces a chord of the other.
That disconnects $W_i$, contrary to hypothesis.

\emph{Every other component sits inside one gap of $W_i$.} A chord outside
$W_i$ fails to interlace every chord of $W_i$ exactly when its two endpoint
gaps have the same side vector, hence, by the gap lemma, exactly when both its
endpoints lie in one and the same gap of $W_i$. If some component $W_j$,
$j\neq i$, occupied two different gaps of $W_i$, its chords in the two gaps
could not interlace each other, contradicting connectedness of $W_j$.

\emph{Closed-block tree.} Apply the preceding two paragraphs inside any
cyclic node word containing at least two of the components. They give a
nonempty proper label-closed linear block $\alpha$; its complementary linear
word $\beta$ is label-closed as well. Record the two closed cyclic child words
in the order $(\alpha,\beta)$. In each child, identifying its two cut ends
creates one distinguished \emph{join gap}. Both children have fewer labels,
so iteration gives a finite ordered binary tree $\mathcal T$ whose leaves are
exactly the $W_i$. Index the leaves in its order. Every non-root node also
remembers the one gap in its cyclic record prescribed when its parent was cut;
that output gap is distinct data from the two child join gaps used when the
node itself is assembled.

We induct upward with the following invariant. A node $V$ has a connected
generic oriented one-circle diagram $C_V$ and an orientation-preserving record
isomorphism from its record to the cyclic record of $V$; if $V$ is not the
root, it also has a clean open subarc in the exact output gap prescribed by its
parent.

For a leaf $V=W_i$, take the actual curve $C_{W_i}$ constructed by
Lemma~\ref{lem:piececurve}, with the inherited divide crossing data. It has
exactly the distinct inherited transverse double points of $W_i$, its
restricted cyclic word, and no triple point: the construction only smooths in
pairwise disjoint crossing discs and creates no intersection.
Lemma~\ref{lem:pieceintrinsic} supplies the record comparison with the carrier
factor $D(W_i)$. If the leaf is not the root, the extension clause in
Definition~\ref{def:record} carries its parent-prescribed output gap to a
complementary arc of its traversal circle. Choose an interior regular point
there and a sufficiently small subarc about it; a small disc meets the curve
in that arc alone, so it is clean. If the leaf is the root, the invariant
requires no output gap.

For an internal node with ordered children $A,B$, use their clean join arcs.
Take $C_A$ as the based host $J$, with $p$ in its join arc, and take $C_B$ as
$K$. At an interior point of $K$'s join arc choose an
orientation-preserving smooth chart of the sphere sending that point to
infinity. A sufficiently small spherical cap about infinity meets $K$ in one
embedded arc, so its complement is a compact long $K$-tangle with two oriented
ends. Shrink that tangle into the clean host disc, delete the short host arc
through $p$, place the tangle ends next to their prescribed host ends, and
cross-pair outgoing $A$ to incoming $B$ and outgoing $B$ to incoming $A$ by
two disjoint short arcs. Round the two joins inside disjoint smaller discs.
This is literally the orientation-compatible local insertion $K\#_pJ$ of
Lemma~\ref{lem:homflyrows}(i), not an unnamed planar splice.

The insertion disc contains no other point of $J$ and the inserted tangle and
connectors lie inside it. Thus it creates no crossing. The sphere chart is
orientation preserving, so all child crossing signs are preserved, and the
over/under designations are transported. Starting immediately before $A$, the
one traversal circle reads the linear word $\alpha$ and then $\beta$.
Pairings stay within a child. These are precisely conditions (a)--(d) of
Definition~\ref{def:record}. The child crossings remain transverse and
distinct, the connectors are disjoint, and the local rounding creates no
intersection, so the result is a generic one-circle diagram with no triple
point.

It remains to mark the node's output gap when the node is not the root. If that
gap is not one of the two split boundaries, it survives in the appropriate
child and is carried across by the record map. If it is a split boundary, use
the corresponding new connector subarc. In either case a smaller disc meeting
only that arc makes it clean. This proves the invariant.

Finally the actual diagram $D(W)$ has underlying curve $L$. The diagrammatic
parent has isolated transverse double points with no two sharing an image, so
the smoothing sites admit pairwise disjoint discs, each meeting the curve in
the two crossing arcs alone. Each local smoothing replaces them by two
noncrossing arcs and outside those discs the curve is unchanged. Hence $L$ is
a connected generic one-circle curve with no triple point. The constructed
root has the same properties by the invariant, and its record is isomorphic to
the record of $D(W)$: the traversal order is the tree's ordered concatenation,
labels and pairings never cross between children, and every over/under role and
sign is inherited. Axiom~\ref{ax:gausscode} identifies the two oriented links.
At the leaves Lemma~\ref{lem:pieceintrinsic} identifies $C_{W_i}$ with
$D(W_i)$. Thus the root is exactly the displayed
$\mathcal T$-parenthesized connected sum, without an associativity assumption.

The polynomial identity follows by applying
Lemma~\ref{lem:homflyrows}(i) at each internal node of the fixed tree
$\mathcal T$; every leaf is a knot diagram. Thus
$P_{D(W)}=\prod_iP_{D(W_i)}$.

\emph{Clause (B).}
Each $H_i$ has both visits of each of its labels on $L$ by
Lemma~\ref{lem:carriers}(iv), and the $H_i$ are exactly the connected
components of the interlacement graph induced on $H_1\cup\dots\cup H_k$, since
they are components of $G_P[U(S)]$ and interlacement is read from the same
word. Clause~(A) applies. The diagram has one component
because $L$ is one closed curve, the writhe is the crossing count because every
crossing is positive (Definition~\ref{def:piecediagram}), and the underlying
plane curve is $L$ because erasing a double point omits it from the record and
performs no operation on the curve (Definition~\ref{def:piecediagram}).

The generic parent polygon is diagrammatic by
Definition~\ref{def:diagrammatic}, so it has no triple points.  The parent's
self-intersections are isolated and no two share an image
(Definition~\ref{def:diagrammatic}), so they admit pairwise disjoint discs,
each meeting the curve in the two crossing arcs alone.  Inside each disc the
oriented smoothing of Definition~\ref{def:smoothing} replaces those two arcs
by two arcs that do not cross, and outside the discs the curve is unchanged;
so no intersection is created and $L$ has no triple points either.

The identification of the factors is Lemma~\ref{lem:pieceintrinsic}: the factor
$D(H_i)$ produced by clause~(A) is the diagram of $L$ with
only the crossings of $H_i$ retained, and the identity on the visits of $H_i$ is
a record \emph{isomorphism} from that diagram's record to the record of the
intrinsic piece diagram of $H_i$ on the parent polygon --- not an equality, the
two traversal circles being different --- so by Axiom~\ref{ax:gausscode} the two
present the same oriented link, whose polynomial is $P_{H_i}$ and whose writhe
is $|H_i|$. So the product in the display is a
product of the $P_{H_i}$ and not of some other family. An earlier revision
asserted this identification in one sentence, on the ground that both
constructions ``retain the crossings of $H_i$''; the peer refuted that ground
--- smoothing the support changes the traversal successor, so containment of
both visits does not identify the cyclic records --- and
Lemma~\ref{lem:pieceintrinsic} now supplies the three components of the record
separately.
\end{proof}
```

## CV:lem:fulltwist — PROVE

reference/R/CV/d6_vertexedge.tex:1981–2031

```tex
\begin{lemma}[the abstract full-twist triple]\label{lem:fulltwist}
Let $D_{\mathrm L},D_{\mathrm H},D_{\mathrm A}$ be oriented diagrams and let $q$
be a positive crossing of $D_{\mathrm H}$ such that
\begin{enumerate}
\item[(T1)] the oriented smoothing of $D_{\mathrm H}$ at $q$ is
$D_{\mathrm A}$;
\item[(T2)] switching $q$ in $D_{\mathrm H}$ gives a diagram carried to
$D_{\mathrm L}$ by oriented Reidemeister-II moves.
\end{enumerate}
The symbols this lemma reads off a diagram are bound here, from the diagrams it
quantifies over, and are not imported from any definition attached to a polygon
or a chamber. They are bound in two groups, because they have two domains. For
\emph{any} oriented diagram $D$ --- any number of components --- put
\[
   F_D=P_D ,
\]
the HOMFLY--PT polynomial of the link it presents (Axiom~\ref{ax:homfly}). For
a diagram $D$ carried by a \emph{single} closed plane curve $\Gamma_D$, and
only for such a diagram, put
\[
   d(D)=1-w(D)-R(\Gamma_D),\qquad
   \Omega(D)=\bigl[a^{d(D)}z^0\bigr]F_D ,
\]
with $w(D)$ the writhe and $R(\Gamma_D)=|\rot(\Gamma_D)|$ the absolute
rotation of that curve. An earlier revision bound all three on one domain,
which typed $d$ and $\Omega$ at a two-component diagram, where the rotation
number of Definition~\ref{def:rot} is not defined. Abbreviate $F_\nu=F_{D_\nu}$ for $\nu\in\{\mathrm L,\mathrm H,\mathrm A\}$,
and $d_\nu=d(D_\nu)$, $\Omega_\nu=\Omega(D_\nu)$ for
$\nu\in\{\mathrm L,\mathrm H\}$ \emph{only}. The restriction is not tidiness:
$D_{\mathrm A}$ is the oriented smoothing of $D_{\mathrm H}$ and is carried by a
\emph{two-component} link in the application, while $R(\Gamma_D)$ is the
absolute rotation of one closed curve (Definition~\ref{def:rot}), so $d$ and
$\Omega$ are not defined at $\mathrm A$ at all. Nothing below asks for them:
$D_{\mathrm A}$ enters only through $F_{\mathrm A}$ and through the coefficient
$[a^{d_{\mathrm L}-1}z^{-1}]F_{\mathrm A}$, which is a coefficient of that
polynomial and not a read at a slot of its own. An
earlier revision used $d_\nu$ and $\Omega_\nu$ in this statement while binding
them only in Definition~\ref{def:markeddata}, which is about the contact
carriers of an eligible support; the abstract triple has no support, and the
lemma was not readable on its own hypotheses. The two bindings agree wherever
both apply, that definition computing $d_\nu$ and $\Omega_\nu$ from these same
grouped diagrams. Then
\[
   F_{\mathrm H}=a^{-2}F_{\mathrm L}+a^{-1}zF_{\mathrm A}.
\]
If moreover $d_{\mathrm H}=d_{\mathrm L}-2$, then
\[
   \Omega_{\mathrm H}-\Omega_{\mathrm L}
   =\bigl[a^{d_{\mathrm L}-1}z^{-1}\bigr]F_{\mathrm A}.
\]
\end{lemma}
```

reference/R/CV/d6_vertexedge.tex:2032–2045

```tex
\begin{proof}
Apply the skein of Axiom~\ref{ax:homfly} at $q$: its $L_+$ is $D_{\mathrm H}$,
its $L_-$ is the switched diagram, whose polynomial is $F_{\mathrm L}$ by (T2)
and the Reidemeister-II invariance of the polynomial, and its $L_0$ is
$D_{\mathrm A}$ by (T1). So $aF_{\mathrm H}-a^{-1}F_{\mathrm L}=zF_{\mathrm A}$,
which is the first display.

For the second, $\Omega_{\mathrm H}=[a^{d_{\mathrm H}}z^0]F_{\mathrm H}
=[a^{d_{\mathrm L}-2}z^0]F_{\mathrm H}$. Taking $[a^{d_{\mathrm L}-2}z^0]$ of
the first display, the first term contributes
$[a^{d_{\mathrm L}-2}z^0](a^{-2}F_{\mathrm L})
=[a^{d_{\mathrm L}}z^0]F_{\mathrm L}=\Omega_{\mathrm L}$ and the second
contributes $[a^{d_{\mathrm L}-1}z^{-1}]F_{\mathrm A}$.
\end{proof}
```

## CV:ax:R — HYPOTHESIS

reference/R/CV/d10_axioms.tex:18–33

```tex
\begin{axiom}[Hypothesis R for $X_1$]\label{ax:R}
$X_1(P_+)=X_1(P_-)$ across every simple Reidemeister III event, i.e.\ every
event whose zero set is the forced bundle
$Z=\{\mathrm{G3}_{e,f,g},\mathrm{G4}_{e;f,g},\mathrm{G4}_{f;e,g},
\mathrm{G4}_{g;e,f}\}$ for three pairwise remote edges with
$1\leq e<f<g\leq n$, concurrent at $t=0$ at a point interior to all three, the
event being transversal in the sense of Definition~\ref{def:event}.

\emph{Why it is not proved here.} It is not a theorem of the literature and not
a claim of this document: it is a \emph{declared input} of the campaign, the
hypothesis under which the main theorem is stated. Proving it is the open
problem the campaign exists for, and a document that proved it would not need
the entry.
\emph{Used in:} Theorem~\ref{thm:main}(B), and there only --- in the Reidemeister
III case of its induction. No other statement of this document reads it.
\end{axiom}
```

## CV:ax:homfly — PROVE

reference/R/CV/d10_axioms.tex:342–364

```tex
\begin{axiom}[HOMFLY--PT]\label{ax:homfly}
There is a unique map $L\mapsto P_L(a,z)\in\mathbb Z[a^{\pm1},z^{\pm1}]$ from
isotopy classes of oriented links in $S^3$ satisfying
$P_{\bigcirc}=1$ and $aP_{L_+}-a^{-1}P_{L_-}=zP_{L_0}$ for every skein triple.
In particular $P_L$ is invariant under the Reidemeister moves. One consequence
is consumed as part of this entry: $P_K\in\mathbb Z[a^{\pm1},z^2]$ for a
\emph{knot} $K$, so that the $z^0$ coefficient of a product of knot
polynomials is the product of their $z^0$ coefficients.

\emph{Why it is not proved here.} The existence of the invariant is a theorem
about all links at once, proved by induction over the full skein tree with a
descending complexity. This document does not construct that invariant; the relative induction in
Lemma~\ref{lem:homflyrows} starts with $P$ already supplied and compares
based-link expressions only.
\emph{Used in:} Definition~\ref{def:X1} (to have $P_H$ at all);
Proposition~\ref{prop:chamberinv}(ii), Lemma~\ref{lem:flatdata} and
Lemma~\ref{lem:silence}; Lemma~\ref{lem:curl} and Theorem~\ref{thm:carrierfloor},
clauses~(C) and~(R); Lemma~\ref{lem:homflyrows},
Proposition~\ref{prop:sectortarget}(B), Lemma~\ref{lem:fulltwist},
Lemma~\ref{lem:triplebridge} and Lemma~\ref{lem:nitransport}, clause~(A); and, through the
knot-parity clause, Theorem~\ref{thm:s7universal}(D)(i) and
Theorem~\ref{thm:s7universal}(D)(iv)(c).
\end{axiom}
```

## CV:ax:etnyre — PROVE

reference/R/CV/d10_axioms.tex:387–397

```tex
\begin{axiom}[Etnyre; self-linking from a front]\label{ax:etnyre}
Let $T$ be a front diagram of a transverse knot with no downward vertical
tangency. Then $\operatorname{sl}(T)$ equals the writhe of $T$.

\emph{Why it is not proved here.} The identity is a computation of the
self-linking number from a front, which presupposes the contact-geometric
definition of $\operatorname{sl}$; this document never defines it, and reads
the identity only as a bridge from the diagram's writhe to the transverse
HOMFLY--PT bound of Axiom~\ref{ax:slbound}.
\emph{Used in:} Theorem~\ref{thm:carrierfloor}(C).
\end{axiom}
```

## CV:ax:slbound — PROVE

reference/R/CV/d10_axioms.tex:399–422

```tex
\begin{axiom}[the HOMFLY--PT bound on the self-linking number]\label{ax:slbound}
Let $T$ be a transverse knot in the standard contact $\mathbb R^3$ and let
$P_T(a,z)$ be the HOMFLY--PT polynomial of the knot it presents, in the
normalization of Axiom~\ref{ax:homfly}. Then
\[
   \operatorname{sl}(T)\;\leq\;-\max\deg_a P_T(a,z)-1 .
\]

\emph{Why it is not proved here.} The bound is a theorem about the whole
invariant, proved in the source by a skein template argument this document has
no machinery for. Source fidelity: the source states the bound for the maximal
self-linking number of a topological knot type and proves it representative by
representative, each front's self-linking number being that of the usual
positive transverse pushoff; the form assumed here, at a single transverse
representative $T$, is that maximum read at one of its values, and that
reading is quoted rather than renamed: every transverse knot is the positive
transverse pushoff of a Legendrian knot, by the Legendrian-pushoff
construction of Etnyre's survey, Section~2.9, and the positive pushoff's
self-linking number is $\operatorname{tb}-r$ of that Legendrian by Lemma~2.22
of the same section.  So $\operatorname{sl}(T)$ is one of the values the
maximum is taken over. The normalization of the source is that of Axiom~\ref{ax:homfly}
verbatim, in the same variable $a$; no variable conversion is assumed.
\emph{Used in:} Theorem~\ref{thm:carrierfloor}(C).
\end{axiom}
```

## CV:ax:gausscode — PROVE

reference/R/CV/d10_axioms.tex:525–568

```tex
\begin{axiom}[isomorphic records present the same link]\label{ax:gausscode}
Let $D$ and $D'$ be oriented link diagrams, each of whose underlying plane
curves is a connected generic immersed circle in the sphere --- one component,
transverse double points, no triple points --- and suppose there is an
orientation-preserving record isomorphism from the record of $D$ to the record
of $D'$ (Definition~\ref{def:record}). Then $D$ and $D'$ present the same
oriented link.
\emph{Used in:} Lemma~\ref{lem:pieceintrinsic}, Lemma~\ref{lem:curl},
Proposition~\ref{prop:chamberinv}(ii), Lemma~\ref{lem:flatdata},
Lemma~\ref{lem:silence}, Corollary~\ref{cor:groupedknot}(A) and~(B),
Proposition~\ref{prop:sectortarget}(B),
Lemma~\ref{lem:slidingcartesian},
clauses~(A) and~(C), Theorem~\ref{thm:s7universal}, clause~(A) and
Lemma~\ref{lem:triplebridge}. An earlier revision named the first and then said
``every consumer of a grouped carrier row'', which is a description and not a
list.
\emph{Why it is not proved here.} This is the classical statement that a
realizable classical signed Gauss code determines its oriented link. Its content
is Carter's classification of generic immersed curves by their Gauss data: two
such curves in a surface with isomorphic data differ by a homeomorphism of the
surface, \emph{provided the curves fill it}, that is, provided every
complementary region is a disc. The hypothesis above is the case in which that
proviso is automatic and is stated for that reason rather than dropped: the
underlying curve of each diagram is a connected four-valent graph embedded in
the sphere, and every face of a connected graph embedded in the sphere is a
disc, the crossing-free case being a circle with two disc faces. The resulting
homeomorphism carries diagram to diagram and so link to link, a priori only up
to reflection if it reverses orientation; the crossing signs, which the record
isomorphism preserves, exclude that. This document does not develop the
realizability theory, and the consumers need the conclusion for diagrams built
on different curves, whose traversal circles are compared by an explicit record
isomorphism rather than identified.
\emph{Two earlier revisions.} The first did not list this entry at all: the
identification it provides was asserted inside the proof of
Corollary~\ref{cor:groupedknot}(B) in one sentence, and the peer refuted the
sentence --- smoothing the support changes the traversal successor, so retaining
the same labels does not identify the cyclic signed records. The second listed
the entry but hypothesized that the two records were \emph{equal}, which
presupposes a shared traversal circle that these two diagrams do not have; the
peer refused that typing too. The combinatorial content is proved ---
Lemma~\ref{lem:carrierword} for the order, Lemma~\ref{lem:pieceintrinsic} for
the map --- and what remains, the passage from a record isomorphism to an
equality of links, is this entry.
\end{axiom}
```

## CV:selector_A — PROVE

reference/R/CV/d6_vertexedge.tex:1017–1020

```tex
\begin{lemma}[minimum carrier corners and selector identities]\label{lem:selectorid}
\begin{enumerate}
\item[(A)] Under the guards of Definition~\ref{def:generic}(A), every carrier of every
support has at least three corners.
```

reference/R/CV/d6_vertexedge.tex:1049–1060

```tex
\begin{proof}
\emph{Clause (A).} A carrier is a closed curve made of straight segments joined at corners of
nonzero turn. With two corners it would consist of two straight segments
joining the same two points, so the two segments would overlap, which puts an
endpoint of one on the other and vanishes a $\mathrm{G2}$. With one corner it
would contain a straight return of zero length, which is not a segment of a
generic polygon. With no corner at all it would be a closed curve made of a
single straight segment, whose two endpoints coincide, so that segment has zero
length --- excluded for the same reason, and by
Definition~\ref{def:regular}(B)'s requirement that every edge be nonzero. An
earlier revision omitted this case. So there are at least three. In particular a zero selector
means mixed turns, and no one- or two-corner convention is needed.
```

## CV:singleton_D_i — PROVE

reference/R/CV/d6_vertexedge.tex:2682–2687

```tex
\item[(i)] Let $S\in\Ind(G_P)$, let $A$ be a uniform carrier of $S$, and let $\{c\}$ be a
singleton residual piece of $S$ carried by $A$. Then
\[
   \min\deg_af_A\;\geq\;\bigl(1-w_{S,A}-R(A)\bigr)+2,
\]
so the factor $\Omega_1(S,A)$ of Definition~\ref{def:X1} is zero.
```

reference/R/CV/d6_vertexedge.tex:2885–2947

```tex
\emph{Clause (D).} \emph{Clause (i).} \emph{Pass to the larger support.} Put $S'=S\cup\{c\}$. It is independent: $c$
is residual, so it is adjacent to no member of $S$. Its undominated set is
\[
   U(S')=U(S)\setminus\bigl(\{c\}\cup N_{G_P}(c)\bigr)=U(S)\setminus\{c\},
\]
because $\{c\}$ is a component of $G_P[U(S)]$, so $c$ has no neighbour inside
$U(S)$. Deleting an isolated vertex leaves every other component of a graph
unchanged, so the residual pieces of $S'$ are exactly the residual pieces of $S$
other than $\{c\}$ --- the same label sets, hence by
Definition~\ref{def:piecediagram} the same piece diagrams, the same $P_H$ and
the same $|H|$. Nothing is being compared across a change of diagram here: the
pieces are literally the same objects.

\emph{The two loops are carriers.} Smoothing $c$ cuts the traversal of $A$ at
the two visits of $c$ and reconnects, so the carriers of $S'$ are those of $S$
with $A$ replaced by the two closed curves $\Lambda_1,\Lambda_2$ carrying the
two arcs of $A$ between the visits of $c$; every other carrier of $S$ is
untouched, $c$ lying on $A$. Each residual piece of $S'$ formerly on $A$
therefore lies on $\Lambda_1$ or on $\Lambda_2$, by
Lemma~\ref{lem:carriers}(iv) applied to $S'$; no separate no-straddle
argument is needed and no sub-loop is compared with its parent. Hence
\[
   P_{S,A}=P_{S',\Lambda_1}\,P_{S',\Lambda_2}\cdot P_{\{c\}}
   =P_{S',\Lambda_1}\,P_{S',\Lambda_2},
   \qquad
   w_{S,A}=w_{S',\Lambda_1}+w_{S',\Lambda_2}+1,
\]
the singleton contributing $P_{\{c\}}=1$ and one unit of writhe
(Definition~\ref{def:piecediagram}: a closed curve with one crossing is an
unknot diagram). Each factor is a knot polynomial, hence lies in
$\mathbb Z[a^{\pm1},z^2]$ and has no negative power of $z$ ---
Axiom~\ref{ax:homfly}, whose knot-parity consequence this step reads and which
an earlier revision used without naming --- so the zeroth rows multiply:
$f_A=f_{\Lambda_1}f_{\Lambda_2}$.

\emph{Turns and rotations.} $A$ has no corner at $c$, which is neither a
polygon vertex nor a member of $S$; the two smoothing corners of $\Lambda_1$ and
$\Lambda_2$ at the site of $c$ receive turning angles that are negatives of
each other, so by Lemma~\ref{lem:turnlift}(ii)
$\rot(A)=\rot(\Lambda_1)+\rot(\Lambda_2)$. Their determinants are $\det(u,v)$
and $\det(v,u)$ for the two branch directions at $c$, hence opposite and
nonzero by (G5). Let $\sigma$ be the common sign of $A$'s turns; every corner of
either loop other than the two new ones is a corner of $A$ and has sign
$\sigma$. So one loop is uniform and the other has exactly one dissenting
corner, of magnitude below $\pi$. Lemma~\ref{lem:uniformrot}(i) applies to the
uniform loop. Apply Lemma~\ref{lem:uniformrot}(ii) to the dissenting loop
directly when $\sigma=+1$ and after orientation reversal when $\sigma=-1$.
Thus $\sigma\rot(\Lambda_i)\geq1$ for both $i$, so the two rotations carry the
sign $\sigma$ and $R(A)=R(\Lambda_1)+R(\Lambda_2)$.

\emph{The bound.} Theorem~\ref{thm:carrierfloor}(C) applies to each loop as a
carrier of $S'$ --- through Corollary~\ref{cor:groupedknot}(B) if it bears a piece
and Theorem~\ref{thm:carrierfloor}(D) if it does not, one loop uniform and the other
one-dissent --- so
$\min\deg_af_{\Lambda_i}\geq1-w_{S',\Lambda_i}-R(\Lambda_i)$ when the row is
nonzero, and if either row vanishes then $f_A=0$ and the claim is trivial.
Adding the two bounds and substituting the two displays above,
\[
   \min\deg_af_A\;\geq\;2-\bigl(w_{S,A}-1\bigr)-R(A)
   =\bigl(1-w_{S,A}-R(A)\bigr)+2 .
\]
The factor $\Omega_1(S,A)$ reads the coefficient at $1-w_{S,A}-R(A)$, two
degrees below the row's lowest nonvanishing degree, so it is zero.
```
