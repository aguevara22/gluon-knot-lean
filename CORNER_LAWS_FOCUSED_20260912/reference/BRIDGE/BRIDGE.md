# Bridge from the frozen R theorem to SM11 Hypothesis R

Codex, Phase 2.5 bridge seat. Object of record: this Markdown document. Submitted for bench A's referee reading and the curator's registration; no acceptance or bridge freeze is self-issued.

## §0. Frozen inputs, coordinates, and scope

The three input frames are SM11, CV and RA. The three campaign outputs remain separate: SM11; the R statement/proof (CV/RA); and this bridge. These are the actual `shasum -a 256` outputs, copied without alteration:

```text
fa24398e5a0e992b273a4a7ba86c4f78977909f3c650ea0f9b02f7732a9f8cf4  phase25/frames/SM11/FRAMED_MANIFEST_SM11.sha256
```

```text
8c02692c9a52ffe5a7c549715e00bfbc29f997af62a074b36af1c2f4a4cf3706  phase199/manuscript/frames/CV/FRAMED_MANIFEST_CV.sha256
```

```text
0ba16c58ea07fdde5b3083b89a59cbd23f2152f6821b9f902100fb2817f678fa  phase1999/evidence/codex/w8_ra_frame_v1/RA/FRAMED_MANIFEST_RA.sha256
```

The corresponding checks returned 20/20, 13/13 and 20/20 payloads OK. Their complete outputs are `FRAME_1_CHECK.txt`, `FRAME_2_CHECK.txt` and `FRAME_3_CHECK.txt`. Here **SM11**, **CV** and **RA** in a locator mean, respectively:

- `phase25/frames/SM11/`
- `phase199/manuscript/frames/CV/`
- `phase1999/evidence/codex/w8_ra_frame_v1/RA/`

Every source quotation below is an exact UTF-8 line slice, including its line breaks; the surrounding locator and quote ID are not part of the quoted bytes. TeX source is quoted as source, without substituting notation or converting status tags into a fresh verdict. `QUOTATIONS.json` records the source-file and excerpt hashes. All displayed equations outside quotation fences are this bridge's deductions and have numbered references.

The imported antecedent is the already-frozen R result **in the precise CV `ax:R` form quoted in §1**, supplied as such by `BRIDGE_PACKET.md` §1–2. This bridge does not reconstruct its proof. RA's `R_ATTACHMENT_WARRANTS.md` supplies localization and the other warrants used by its four core proofs: `R_GENERIC_COMMON_TRANSPORT_PROOF.md`, `R_GENERIC_SELECTED_COUPLE_PROOF.md`, `R_EXTREME_SINGLETON_TRANSPORT_PROOF.md`, and `R_EXTREME_SELECTED_COUPLE_PROOF.md`. R-LOC-2 itself is a localization theorem, not the final scalar equality. Nor are the core proofs' full-availability row statements silently imposed as an extra restriction on the wall germ. The source theorem, including its accepted underlying inputs, is the antecedent of this implication; no new proof or acceptance of R is claimed here.

We work on the continuous labelled representative supplied by an SM wall germ. Set $p_i=\mu_i$, $d_i=p_{i+1}-p_i=\mu_{i+1}-\mu_i$, and identify CV's edge $e_i$ with SM's $E_i$. Each residue is represented in $\{1,\ldots,n\}$; when naming the central triple, choose $e<f<g$ in those representatives. This is the printed coordinate convention:

<!-- BEGIN QUOTE SM_MAP -->
**SM_MAP — SM11 `sm-1-polygons.tex:13–17`**

````tex
(Lemma~\ref{lem:gates-nonzero}). For $n\geq3$ indices of vertices and edges
are elements of $\ZZ/n$; $i+1$, $i-1$ are read modulo $n$. The main text
writes $[u,v]=u_2v_1-u_1v_2=-\det(u,v)$; this document uses $\det$ only.
The frozen source CV uses one-based tail labels: its edge $e_i$ runs
from $p_i$ to $p_{i+1}$, so $p_i=\mu_i$ requires no index shift.
````
<!-- END QUOTE SM_MAP -->

The object conventions on both sides are:

<!-- BEGIN QUOTE SM_OBJECT -->
**SM_OBJECT — SM11 `sm-1-polygons.tex:27–51`**

````tex
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
````
<!-- END QUOTE SM_OBJECT -->

<!-- BEGIN QUOTE CV_OBJECT -->
**CV_OBJECT — CV `d1_setup.tex:8–19`**

````tex
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
````
<!-- END QUOTE CV_OBJECT -->

In particular, SM permits degenerate tuples at the definition level whereas CV's polygon definition requires nonzero edges. B1 verifies the nonzero-edge requirement along the entire triple germ. The meanings of *remote edges* agree on distinct edge indices: their two endpoint index sets are disjoint. No remote-to-a-vertex convention is imported.

Write $\mathcal U_n^{\rm SM}$ and $\mathcal U_n^{\rm CV}$ for the two labelled generic loci. We prove only the relation needed here. B1 transfers **simple triple germs**, B2 identifies their zero set, B3 proves transversality, and B4 identifies scalar side values through the containing CV chambers. Neither equality of the generic loci nor equality of the chamber sets is assumed. The requested class inclusion is only from SM11 simple triple walls to the CV events on which the imported R theorem is stated.

## §1. The two statements and the RA domain, quoted

The target statement is:

<!-- BEGIN QUOTE SM_HYP -->
**SM_HYP — SM11 `sm-4-knotlaws.tex:1149–1151`**

````tex
\begin{hypothesis}[R]\label{hyp:R}
At every simple triple wall, $C(P_+)=C(P_-)$. \status{hyp}
\end{hypothesis}
````
<!-- END QUOTE SM_HYP -->

The mathematical statement of the imported antecedent, including every event-domain clause, is:

<!-- BEGIN QUOTE CV_R -->
**CV_R — CV `d10_axioms.tex:18–24`**

````tex
\begin{axiom}[Hypothesis R for $X_1$]\label{ax:R}
$X_1(P_+)=X_1(P_-)$ across every simple Reidemeister III event, i.e.\ every
event whose zero set is the forced bundle
$Z=\{\mathrm{G3}_{e,f,g},\mathrm{G4}_{e;f,g},\mathrm{G4}_{f;e,g},
\mathrm{G4}_{g;e,f}\}$ for three pairwise remote edges with
$1\leq e<f<g\leq n$, concurrent at $t=0$ at a point interior to all three, the
event being transversal in the sense of Definition~\ref{def:event}.
````
<!-- END QUOTE CV_R -->

For comparison, the RA localization interface reads:

<!-- BEGIN QUOTE RA_LOCAL -->
**RA_LOCAL — RA `R_ATTACHMENT_WARRANTS.md:16–29`**

````tex
Let $t\mapsto P(t)$ be a simple transversal Reidemeister-III event with zero set
exactly the forced bundle
$Z=\{\mathrm{G3}_{e,f,g},\mathrm{G4}_{e;f,g},\mathrm{G4}_{f;e,g},
\mathrm{G4}_{g;e,f}\}$, $e<f<g$ pairwise remote and concurrent at $t=0$ at a
point interior to all three. Let $T=\{x_{ef},x_{eg},x_{fg}\}$. Then on a
punctured neighbourhood of $t=0$:

1. the crossing set, indexed by carrying edge pairs, is constant;
2. on each of $e,f,g$ the two crossings of $T$ carried by that edge occupy
   adjacent crossing-visits of the traversal circle, and their order along that
   edge is opposite on the two sides;
3. every other pair of crossings keeps its order along every edge;
4. hence $G^{+}=G^{-}\ \triangle\ \binom{T}{2}$: the three internal pairs of $T$
   toggle and no other pair changes.
````
<!-- END QUOTE RA_LOCAL -->

The latter quotation establishes which event domain RA's local machinery reads. We invoke the scalar R theorem in CV's form, not the graph-toggle conclusion of R-LOC-2 in its place.

## §2. The four identification lemmas

### B1. Generic-locus inclusion and transfer of a triple germ

**Lemma B1.** With the labelled coordinate identification of §0,

$$
\mathcal U_n^{\rm SM}\subseteq\mathcal U_n^{\rm CV}.
$$

(1)

Every SM11 wall germ satisfying the central conditions of type $T$ is a CV event. This assertion is restricted to that central type; it does not assert that every type of SM wall is a CV event.

The relevant SM definitions and elementary geometry are:

<!-- BEGIN QUOTE SM_GENERIC -->
**SM_GENERIC — SM11 `sm-1-polygons.tex:99–108`**

````tex
\begin{definition}[generic polygon]\label{def:generic}
A polygon $P$ is \emph{generic} if
\begin{enumerate}
\item[(G1)] $\chi_{ijk}(P)\neq0$ for all pairwise distinct $i,j,k\in\ZZ/n$;
\item[(G2)] there is no point of $\RR^2$ lying in the relative interiors of
three distinct edge segments.
\end{enumerate}
The set of generic polygons on $n$ vertices is $\mathcal U_n\subseteq(\RR^2)^n$.
\end{definition}

````
<!-- END QUOTE SM_GENERIC -->

<!-- BEGIN QUOTE SM_G1 -->
**SM_G1 — SM11 `sm-1-polygons.tex:110–123`**

````tex
Let $P$ satisfy (G1). Then:
\begin{enumerate}
\item[(i)] all vertices are distinct and every edge vector is nonzero;
\item[(ii)] every turn $\tau_i$ is $\pm1$; consecutive edge vectors are
linearly independent, so no vertex is a positive or negative multiple
(``flat'' or ``kink'') of its neighbours;
\item[(iii)] no vertex lies on the line spanned by an edge not incident to it;
in particular no vertex lies on a non-incident closed edge segment;
\item[(iv)] two adjacent edges meet exactly in their common vertex;
\item[(v)] two remote edges are either disjoint or meet in exactly one point,
which lies in the relative interior of both and at which the two edge
directions are linearly independent.
\end{enumerate}
\status{proved}
````
<!-- END QUOTE SM_G1 -->

<!-- BEGIN QUOTE SM_GERM -->
**SM_GERM — SM11 `sm-1-polygons.tex:653–668`**

````tex
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
````
<!-- END QUOTE SM_GERM -->

<!-- BEGIN QUOTE SM_TRIPLE -->
**SM_TRIPLE — SM11 `sm-1-polygons.tex:735–738`**

````tex
\item[(T)] \emph{Triple at $\{e,f,g\}$}: $Z_{\rm pt}=\varnothing$,
$Z_{\rm c}=\{\{e,f,g\}\}$, and on each of the three edges the two crossing
parameters of the other two edges (which exist on both sides by
Lemma~\ref{lem:triple-sides}) have a difference that changes sign at $0$.
````
<!-- END QUOTE SM_TRIPLE -->

<!-- BEGIN QUOTE SM_TRIPLE_SIDES -->
**SM_TRIPLE_SIDES — SM11 `sm-1-polygons.tex:670–675`**

````tex
\begin{lemma}[sides of a triple wall]\label{lem:triple-sides}
Let a wall germ have $Z_{\rm pt}=\varnothing$ and
$Z_{\rm c}=\{\{e,f,g\}\}$. Then for small $t\neq0$ the three pairs
$\{e,f\},\{e,g\},\{f,g\}$ are crossings, their three crossing points
are distinct, and on each of $E_e,E_f,E_g$ its two crossings occupy adjacent
positions among the crossing visits on that edge.
````
<!-- END QUOTE SM_TRIPLE_SIDES -->

CV's guard polynomials, activation rule and genericity are:

<!-- BEGIN QUOTE CV_UNCONDITIONAL -->
**CV_UNCONDITIONAL — CV `d1_setup.tex:42–55`**

````tex
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
````
<!-- END QUOTE CV_UNCONDITIONAL -->

<!-- BEGIN QUOTE CV_ACTIVATION -->
**CV_ACTIVATION — CV `d1_setup.tex:58–64`**

````tex
\emph{Activation.} Two remote edges $e,f$ are \emph{defined} to cross when
\[
   \mathrm{G2}_{e,f}\,\mathrm{G2}_{e,f+1}<0
   \quad\text{and}\quad
   \mathrm{G2}_{f,e}\,\mathrm{G2}_{f,e+1}<0 ,
\]
a condition on unconditional members alone. The products are \emph{strict}, and
````
<!-- END QUOTE CV_ACTIVATION -->

<!-- BEGIN QUOTE CV_G5 -->
**CV_G5 — CV `d1_setup.tex:99–114`**

````tex
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
````
<!-- END QUOTE CV_G5 -->

<!-- BEGIN QUOTE CV_G3 -->
**CV_G3 — CV `d1_setup.tex:115–127`**

````tex
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
````
<!-- END QUOTE CV_G3 -->

<!-- BEGIN QUOTE CV_G4 -->
**CV_G4 — CV `d1_setup.tex:128–134`**

````tex
\item[(G4)] $\mathrm{G4}_{e;f,g}
=\det(d_f,\,p_f-p_e)\,\det(d_g,d_e)-\det(d_g,\,p_g-p_e)\,\det(d_f,d_e)$,
for every edge $e$ and every pair of edges remote to $e$ with
$1\leq f<g\leq n$ as integers --- again the comparison is between integer
representatives, and again one ordered representative per pair, since
$\mathrm{G4}_{e;g,f}=-\mathrm{G4}_{e;f,g}$; \emph{active} when $f$ and $g$ both
cross $e$.
````
<!-- END QUOTE CV_G4 -->

<!-- BEGIN QUOTE CV_GENERIC -->
**CV_GENERIC — CV `d1_setup.tex:220–237`**

````tex
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
````
<!-- END QUOTE CV_GENERIC -->

<!-- BEGIN QUOTE CV_EVENT -->
**CV_EVENT — CV `d1_setup.tex:1072–1086`**

````tex
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
````
<!-- END QUOTE CV_EVENT -->

**Proof.** First take an SM-generic labelled tuple. All of its distinct vertex-triple determinants are nonzero. Thus its vertices are distinct and its edges are nonzero by SM `lem:g1(i)`, so it is a polygon in CV's definition.

For CV's unconditional turn guard, write $d_{i-1}=p_i-p_{i-1}$ and $d_i=p_{i+1}-p_i$. Bilinearity gives

$$
\det(p_i-p_{i-1},p_{i+1}-p_{i-1})
=\det(d_{i-1},d_{i-1})+\det(d_{i-1},d_i).
$$

(2)

The first summand is zero by alternation, so the left side equals $\mathrm{G1}_i$. It is a determinant of three distinct consecutive vertices and is therefore nonzero. CV's $\mathrm{G2}_{a,i}$ is directly the determinant of the distinct vertices (a,a+1,i), so it too is nonzero. These arguments cover every unconditional member, not merely those near the nominated triple.

For two remote edges, the nonzero endpoint determinants and CV's two strict products express that each segment's endpoints lie strictly on opposite sides of the other's line. Such segments have a unique transverse intersection interior to both. Conversely an interior transverse intersection has those endpoint separations. This is also SM's printed crossing test:

<!-- BEGIN QUOTE SM_CROSSINGS -->
**SM_CROSSINGS — SM11 `sm-1-polygons.tex:137–155`**

````tex
\begin{definition}[crossings]\label{def:crossings}
Let $P$ satisfy (G1). The \emph{crossing set} $X(P)$ is the set of unordered
pairs $\{i,j\}$ of remote edge indices with $E_i\cap E_j\neq\varnothing$. For
$\{i,j\}\in X(P)$ the \emph{crossing point} $x_{ij}$ is the unique point of
$E_i\cap E_j$, and its \emph{parameters} $t_{ij}\in(0,1)$ on $E_i$ and
$t_{ji}\in(0,1)$ on $E_j$ are defined by $x_{ij}=\mu_i+t_{ij}\lt_i
=\mu_j+t_{ji}\lt_j$. The \emph{crossing sign} of $\{i,j\}$ read from $E_i$ is
$\sgn\det(\lt_i,\lt_j)$.
\end{definition}

\begin{lemma}[crossings through the chirotope]\label{lem:crossing-test}
Let $P$ satisfy (G1) and let $E_i,E_j$ be remote. Then $\{i,j\}\in X(P)$ if
and only if
\[
\chi_{i,i+1,j}\,\chi_{i,i+1,j+1}=-1\quad\text{and}\quad
\chi_{j,j+1,i}\,\chi_{j,j+1,i+1}=-1.
\]
If $P$ is generic, distinct crossings have distinct crossing points, and
$X(P)$ is finite. \status{proved}
````
<!-- END QUOTE SM_CROSSINGS -->

Hence CV activation and SM crossing agree on this tuple. An active G5 is nonzero because an interior crossing has linearly independent edge directions.

If an active G3 vanished, its three pairwise crossing lines would have a common projective point. Any crossing pair has independent directions, so their unique intersection is a finite point. That point must be the pairwise intersection on each of the three segments, hence interior to all three. SM (G2) excludes it.

If an active $\mathrm{G4}_{a;b,c}$ vanished, the two interior crossings on edge $a$ would have equal parameters. For completeness, this follows by solving the two line-intersection equations: the denominators $\det(d_b,d_a)$ and $\det(d_c,d_a)$ are nonzero, and clearing them makes equality of the two parameters exactly the defining G4 numerator. B3 below writes these algebraic steps explicitly, without any generic-locus premise beyond nonzero denominators. The resulting point lies in the interiors of three distinct segments $a,b,c$, again excluded by SM (G2). This also covers CV G4 members for which $b,c$ are adjacent; their adjacency does not evade SM's three-interior exclusion. Every relevant CV member is therefore nonzero. This proves (1).

Now take the SM triple germ. Its punctured values are CV-generic by (1). At the centre, $Z_{\rm pt}=\varnothing$ says that the SM point-triple condition still holds, so the centre has nonzero edges and is also a CV polygon. The sole member $\{e,f,g\}$ of $Z_{\rm c}$ specifies pairwise remote edges and a point $q$ interior to all three. No pair of their supporting lines can coincide: an endpoint of one remote edge would then lie on the other's line, contradicting the nonzero point-triple determinant. Their directions are therefore pairwise independent. The three pairs satisfy CV's strict crossing activation at the centre. Their coefficient matrix annihilates $(q_1,q_2,1)^T$, so its determinant G3 is zero. This is an active, hence relevant, zero guard; the centre is not CV-generic. Continuity is the same coordinate continuity in both definitions. We have verified every clause of CV `def:event`. ∎

### B2. Exactly the forced bundle

**Lemma B2.** For the germ in B1, its CV zero set is

$$
Z=\{\mathrm{G3}_{e,f,g},\mathrm{G4}_{e;f,g},
       \mathrm{G4}_{f;e,g},\mathrm{G4}_{g;e,f}\}.
$$

(3)

These are four **indexed members**. In particular their later polynomial identities do not collapse this set. CV says so explicitly:

<!-- BEGIN QUOTE CV_INDEX -->
**CV_INDEX — CV `d1_setup.tex:168–179`**

````tex
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
````
<!-- END QUOTE CV_INDEX -->

**Proof: the relevance quantifier.** On every punctured value SM (G1) holds, and at zero it holds because $Z_{\rm pt}=\varnothing$. The calculation in B1 therefore makes every unconditional CV G1/G2 polynomial nonzero at **every** time in the original germ interval. Each is continuous. A nonzero continuous real function on an interval has constant sign: if two values had opposite signs, the intermediate value theorem would give a zero between them. Thus every G2 sign is constant on that entire interval. CV's strict crossing tests are products of those G2 values, so every crossing activation predicate, and hence the activation of each conditional guard, is constant throughout the interval. For a conditional member, being relevant at *some* nonzero time is consequently equivalent to being active at the centre. This proves the needed treatment of the literal `for some` quantifier in CV's zero set; it does not discard distant times by an unjustified truncation.

**Forced bundle contained in $Z$.** The three central crossings found in B1 persist on both punctured sides; this follows either from the constant strict tests just proved or from SM `lem:triple-sides`. Thus the central G3 and all three G4 members are relevant at nonzero times. The G3 determinant vanishes because the lines contain $q$. On each edge the two central intersections are the same point $q$, so their two parameters are equal. The defining G4 polynomial is their difference multiplied by its two nonzero direction determinants, and is therefore zero. Every member displayed in (3) satisfies both clauses of CV's definition of $Z$.

**$Z$ contained in the forced bundle.** Take any member of $Z$, and exhaust CV's five guard families.

1. It cannot be G1 or G2: both unconditional families are nonzero at the centre.
2. It cannot be G5: relevance at some nonzero time implies central activation, and an active central pair crosses transversely, so its direction determinant is nonzero.
3. If it is G3, central activation gives three pairwise crossing, pairwise nonparallel lines. Their vanishing coefficient determinant makes their unique finite pairwise intersection a common point. Since each pair crosses in the interiors, the common point lies in all three interiors. Its index triple belongs to $Z_{\rm c}$, so it must be $\{e,f,g\}$. The unique increasing representative is the displayed G3 member.
4. If it is $\mathrm{G4}_{a;b,c}$, central activation gives two transverse interior crossings on $a$. The two nonzero denominators and the zero numerator force the parameters to be equal. There is consequently one point interior to $a,b,c$. The edges $b,c$ cannot be adjacent: under central SM (G1), adjacent edges meet only at their common endpoint, whereas this point is interior to both. They are distinct by the G4 indexing rule. All three edges are therefore pairwise remote and give a member of $Z_{\rm c}$. They are exactly $e,f,g$. The possible base edge $a$ is one of these three, and the remaining two indices are put in increasing representative order, giving exactly one of the three G4 members in (3).

There is no other guard family in the printed list. Both inclusions have now been proved. ∎

### B3. All four sign changes

**Lemma B3.** The three parameter-difference sign changes in SM type $T$, together with its central conditions, imply CV transversality for the zero set (3).

The parameter factorization is printed in CV:

<!-- BEGIN QUOTE CV_PARAMETERS -->
**CV_PARAMETERS — CV `d1_setup.tex:198–207`**

````tex
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
````
<!-- END QUOTE CV_PARAMETERS -->

The signed polynomial identities are also printed, with a fixed ordering, in CV's wall dictionary:

<!-- BEGIN QUOTE CV_IDENTITIES -->
**CV_IDENTITIES — CV `d8a_dictionary.tex:429–435`**

````tex
For three pairwise remote edges, the concurrency determinant and the three
order predicates satisfy, for a fixed ordering,
\[
 \mathrm{G4}_{e;f,g}=-\mathrm{G3}_{e,f,g},\qquad
 \mathrm{G4}_{f;e,g}=+\mathrm{G3}_{e,f,g},\qquad
 \mathrm{G4}_{g;e,f}=-\mathrm{G3}_{e,f,g}.
\]
````
<!-- END QUOTE CV_IDENTITIES -->

RA uses the corresponding nonzero-factor implication in the other direction inside its localization proof:

<!-- BEGIN QUOTE RA_PARAMETERS -->
**RA_PARAMETERS — RA `R_ATTACHMENT_WARRANTS.md:45–64`**

````tex
**(2a) The order along each bundle edge reverses — with the $\mathrm{G5}$
factors made explicit (repair 2).** `def:guarded` defines
$$\mathrm{G4}_{e;f,g}=\det(d_f,p_f-p_e)\det(d_g,d_e)-\det(d_g,p_g-p_e)\det(d_f,d_e).$$
Writing $t_f$ for the parameter along $e$ of the crossing $x_{ef}$, the line
intersection gives $t_f=\det(d_f,p_f-p_e)/\det(d_f,d_e)$, and hence the
factorization
$$\mathrm{G4}_{e;f,g}=(t_f-t_g)\,\det(d_f,d_e)\,\det(d_g,d_e)
 =(t_f-t_g)\,\mathrm{G5}_{e,f}\,\mathrm{G5}_{e,g},$$
the last equality up to the sign convention $\mathrm{G5}_{e,f}=\det(d_e,d_f)$,
whose two reversals cancel in the product. Therefore
$$\operatorname{sgn}\mathrm{G4}_{e;f,g}
=\operatorname{sgn}(t_f-t_g)\cdot\operatorname{sgn}\mathrm{G5}_{e,f}
\cdot\operatorname{sgn}\mathrm{G5}_{e,g}.$$
$\mathrm{G5}_{e,f}$ and $\mathrm{G5}_{e,g}$ are **active** ($f$ and $g$ both
cross $e$), hence relevant, and neither lies in $Z$; so by `lem:guardconst` each
is nonzero with constant sign on a neighbourhood of $t=0$. $\mathrm{G4}_{e;f,g}$
lies in $Z$ and changes sign at $t=0$ by transversality. With the two
$\mathrm{G5}$ signs constant, the sign change is carried by $t_f-t_g$ alone:
the order of $x_{ef}$ and $x_{eg}$ along $e$ reverses. Identically on $f$ and
$g$.
````
<!-- END QUOTE RA_PARAMETERS -->

We give the full algebra and the required direction here. For an edge $a$ and two edges $b,c$ crossing it near zero, put

$$
N_b=\det(d_b,p_b-p_a),\qquad D_b=\det(d_b,d_a),
\qquad N_c=\det(d_c,p_c-p_a),\qquad D_c=\det(d_c,d_a).
$$

(4)

These are functions of the germ parameter $t$. Denote the intersection parameters on $a$ by $\tau_b,\tau_c$, using a new letter to distinguish them from the germ parameter. The line equation at the first crossing is

$$
0=\det(d_b,p_a+\tau_b d_a-p_b)
  =-N_b+\tau_b D_b.
$$

(5)

The second equality uses bilinearity and $p_a-p_b=-(p_b-p_a)$. Since $D_b\ne0$, adding $N_b$ and dividing by $D_b$ gives $\tau_b=N_b/D_b$. The same steps give $\tau_c=N_c/D_c$. Subtracting these two fractions over their nonzero common denominator gives

$$
\tau_b-\tau_c=\frac{N_bD_c-N_cD_b}{D_bD_c}.
$$

(6)

The numerator is exactly the CV G4 formula in the order (a;b,c). Thus, when $b<c$ are the representative indices,

$$
\mathrm{G4}_{a;b,c}=(\tau_b-\tau_c)D_bD_c.
$$

(7)

If SM presents the difference in the opposite order, its negative gives the representative order. Multiplication by the constant $-1$ does not affect the sign-change test, because the product of the two values is multiplied by $(-1)^2=1$.

Apply this with base edge each of $e,f,g$. Every relevant central pair has independent directions by B1, so each denominator in (4) is nonzero at zero. Continuity and finiteness give one symmetric neighbourhood on which all six such determinants are nonzero and each keeps its central sign. For a chosen base edge put $K(t)=D_b(t)D_c(t)$. It is continuous, nonzero, and of one sign on that neighbourhood. Therefore $K(t)K(-t)>0$ for all sufficiently small positive $t$. Set $\delta_a(t)=\tau_b(t)-\tau_c(t)$. SM's exact sign-change definition gives $\delta_a(t)\delta_a(-t)<0$. Evaluating (7) at the two times and multiplying gives

$$
\mathrm{G4}_{a;b,c}(P(t))\mathrm{G4}_{a;b,c}(P(-t))
=\delta_a(t)\delta_a(-t)K(t)K(-t)<0.
$$

(8)

The inequality follows from one strictly negative factor and one strictly positive factor. This proves the sign change of each of the three indexed G4 members. All functions concerned are continuous and nonzero on either sufficiently small punctured half-interval, so the symmetric test also gives constant opposite signs on the two halves.

For the G3 member, we additionally derive the printed polynomial identity directly. Write $D=\mathrm{G3}_{e,f,g}$, and in (4) take $a=e,b=f,c=g$. In the line-coefficient matrix for $D$, add $p_{e,1}$ times column 1 and $p_{e,2}$ times column 2 to column 3. Adding multiples of other columns preserves a determinant. The three entries of the new column 3 are respectively $\ell_e(p_e)=0$, $\ell_f(p_e)=-N_f$, and $\ell_g(p_e)=-N_g$. Expansion along that column now gives

$$
D=N_f(A_eB_g-B_eA_g)-N_g(A_eB_f-B_eA_f).
$$

(9)

For each row $(A_i,B_i)=(-d_{i,2},d_{i,1})$, direct multiplication gives

$$
A_eB_j-B_eA_j=d_{e,1}d_{j,2}-d_{e,2}d_{j,1}
=\det(d_e,d_j).
$$

(10)

Alternation gives $\det(d_e,d_j)=-\det(d_j,d_e)=-D_j$. Substituting this separately into the two summands of (9) yields

$$
D=-N_fD_g+N_gD_f=-\mathrm{G4}_{e;f,g}.
$$

(11)

The last equality is the negative of the defining numerator in (7), not an assumption about a picture. Hence the product of the two G3 values equals the product of the two $e$-based G4 values, which is strictly negative by (8). G3 changes sign. Repeating (11) with $f$ and $g$ as base edge, and using the odd permutation ($f,e,g$) and even permutation ($g,e,f$) of the coefficient rows, gives respectively $\mathrm{G4}_{f;e,g}=+D$ and $\mathrm{G4}_{g;e,f}=-D$, agreeing with the quoted dictionary. This also checks the representative-order signs.

B2 lists all four members of $Z$, and we have proved their four sign changes. This is exactly CV transversality. No derivative, differentiability, nonzero speed, or additional wall hypothesis was used. ∎

### B4. Pointwise dictionary and side values

**Lemma B4.** On every SM-generic labelled representative, the two state sums have equal values. On either punctured side of a triple germ, this equality identifies the SM side value with the value on its containing CV chamber.

The printed legend establishes the source/coordinate conventions:

<!-- BEGIN QUOTE SM_LEGEND -->
**SM_LEGEND — SM11 `sm-0-legend.tex:56–65`**

````tex
{\raggedright
\paragraph{Frozen sources.} The transcription sources are CV,
\path{phase199/manuscript/frames/CV/}; RC,
\path{phase198/manuscript/RC_v4/}; and RA,
\path{phase1999/evidence/codex/w8_ra_frame_v1/RA/}.
The appendix source is the curator-posted read-only copy of appendix v7.
Locators name labels in those documents. CV uses the same one-based tail
labels as this document. RC uses zero-based head labels and
$[u,v]_*=-\det(u,v)$; its physical endpoint map is stated in
Section~\ref{sec:conventions}. No starred bracket is used here.\par}
````
<!-- END QUOTE SM_LEGEND -->

It does not itself print a $C=X_1$ theorem. Moreover SM explicitly warns against using the selector identity as that theorem:

<!-- BEGIN QUOTE SM_WARNING -->
**SM_WARNING — SM11 `sm-3-statesum.tex:1812–1820`**

````tex
\begin{remark}[well-definedness]
The positive lift of a subpolygon is an honest knot diagram on an actual
closed plane curve (Lemma~\ref{lem:carriers}); no realization of an abstract
Gauss word is involved, and Literature input~\ref{lit:homfly} is consumed
only on such diagrams. The selector lemma is an identity for this
definition. It asserts no equivalence with a residual-piece polynomial
construction in a frozen source; any use of such an equivalence would
require a separate printed factorization proof.
\end{remark}
````
<!-- END QUOTE SM_WARNING -->

The actual definitions being compared are:

<!-- BEGIN QUOTE SM_C -->
**SM_C — SM11 `sm-3-statesum.tex:1688–1700`**

````tex
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
````
<!-- END QUOTE SM_C -->

<!-- BEGIN QUOTE SM_SELECTOR -->
**SM_SELECTOR — SM11 `sm-3-statesum.tex:1787–1796`**

````tex
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
````
<!-- END QUOTE SM_SELECTOR -->

<!-- BEGIN QUOTE CV_X1 -->
**CV_X1 — CV `d1_setup.tex:908–930`**

````tex
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
````
<!-- END QUOTE CV_X1 -->

The actual CV definition of $X_1$ is at `d1_setup.tex:908–930`; `d8a_dictionary.tex` is the wall dictionary and supplies the B3 identities, not this state-sum definition. We prove the necessary cross-frame factorization below, using the printed carrier-product result, rather than assuming it from a label.

**Proof, part 1: crossings, words and supports.** By B1 the common labelled polygon is in both generic domains. The crossing tests quoted in B1 identify each crossing by its unordered pair of carrying edges. The point and its two affine parameters are the same geometric intersection. Both traversal constructions run through these parameters in increasing edge order and along each oriented edge, as printed:

<!-- BEGIN QUOTE SM_GAUSS -->
**SM_GAUSS — SM11 `sm-1-polygons.tex:237–255`**

````tex
\begin{definition}[traversal circle and Gauss word]\label{def:gauss}
Let $P$ be generic. The \emph{traversal circle} $\Gamma(P)$ is the set of
pairs $(i,t)$, $i\in\ZZ/n$, $t\in[0,1)$, with the cyclic order in which
$(i,t)<(i,t')$ for $t<t'$ and $(i,t)<(i+1,t')$ for all $t,t'$; the point of
the plane at $(i,t)$ is $\mu_i+t\lt_i$. Each crossing $\{i,j\}\in X(P)$ has
two \emph{visits} $(i,t_{ij})$ and $(j,t_{ji})$ on $\Gamma(P)$. The
\emph{Gauss word} of $P$ is the cyclic sequence of the $2|X(P)|$ visits in
the order of $\Gamma(P)$, each visit labelled by its crossing.
\end{definition}

\begin{definition}[interlacement]\label{def:interlace}
Two distinct crossings $x,y\in X(P)$ \emph{interlace} if the four visits
$x_0,y_0,x_1,y_1$ occur in the cyclic order $x_0<y_0<x_1<y_1$ (up to rotation),
that is, exactly one visit of $y$ lies between the two visits of $x$. The
\emph{interlacement graph} $G_P$ has vertex set $X(P)$ and an edge between
each interlacing pair. $\Ind(G_P)$ denotes the set of independent subsets of
$X(P)$, including $\varnothing$; for $S\subseteq X(P)$ let $N(S)$ be the set of
crossings interlacing some element of $S$, and let
$U(S)=X(P)\setminus(S\cup N(S))$.
````
<!-- END QUOTE SM_GAUSS -->

<!-- BEGIN QUOTE CV_GAUSS -->
**CV_GAUSS — CV `d1_setup.tex:305–313`**

````tex
Fix a \emph{diagrammatic} polygon $P$ --- the class defined below, of which
every generic polygon is a member --- and let $m=m(P)$ be the number of its
double points, labelled $1,\dots,m$. Everything in this subsection, up to and
including the residual pieces and their diagrams, is stated for that class:
genericity enters later, with the guards, and an earlier revision fixed a
generic polygon here and then claimed the wider scope downstream. Traversing $P$ once from $p_1$ in the direction of
increasing index visits each double point exactly twice; recording the labels in
the order visited gives a cyclic word of length $2m$ in which every letter occurs
twice, the \emph{Gauss word} of $P$.
````
<!-- END QUOTE CV_GAUSS -->

<!-- BEGIN QUOTE CV_INTERLACE -->
**CV_INTERLACE — CV `d1_setup.tex:346–353`**

````tex
\begin{definition}[interlacement graph]\label{def:interlace}
The \emph{interlacement graph} $G_P$ has vertex set $[m]=\{1,\dots,m\}$, with
$c\sim c'$ if and only if exactly one of the two occurrences of $c'$ lies between
the two occurrences of $c$ in the Gauss word. (The relation is symmetric.) We
write $\Ind(G_P)$ for the set of independent sets of $G_P$, including
$\varnothing$, and $N_{G_P}(S)$ for the set of vertices adjacent to some element
of $S$.
\end{definition}
````
<!-- END QUOTE CV_INTERLACE -->

If CV assigns integer crossing labels, use the bijection from those labels to the common edge-pair labels. The order of the two visits of every crossing is preserved under this relabelling. Interlacement tests whether their four visits alternate, equivalently whether exactly one visit of one lies between the two visits of the other. Thus every graph adjacency is identical under the bijection. Independent supports, their neighbour sets and their undominated sets are consequently identified without a choice of new graph.

**Part 2: carriers and their blocks.** The smoothing rules and owner data are:

<!-- BEGIN QUOTE SM_SMOOTH -->
**SM_SMOOTH — SM11 `sm-3-statesum.tex:9–27`**

````tex
\begin{definition}[decomposition]\label{def:decomposition}
A \emph{decomposition} of $P$ is an independent set $S\in\Ind(G_P)$ of
crossings (Definition~\ref{def:interlace}): no two crossings of $S$ interlace.
\end{definition}

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
````
<!-- END QUOTE SM_SMOOTH -->

<!-- BEGIN QUOTE CV_SMOOTH -->
**CV_SMOOTH — CV `d1_setup.tex:355–381`**

````tex
\begin{definition}[oriented smoothing]\label{def:smoothing}
For $S\in\Ind(G_P)$, the \emph{oriented smoothing of $P$ along $S$} replaces, at
each double point of $S$, the two transversally crossing arcs by the two arcs
that respect the orientation of $P$ and do not cross. The result is a disjoint
union of closed oriented curves, called the \emph{carriers} of $S$.
\end{definition}

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
````
<!-- END QUOTE CV_SMOOTH -->

<!-- BEGIN QUOTE SM_BLOCKS -->
**SM_BLOCKS — SM11 `sm-3-statesum.tex:4623–4648`**

````tex
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
````
<!-- END QUOTE SM_BLOCKS -->

<!-- BEGIN QUOTE CV_BLOCKS -->
**CV_BLOCKS — CV `d1_setup.tex:514–518`**

````tex
\begin{definition}[undominated set and residual pieces]\label{def:pieces}
For $S\in\Ind(G_P)$ put $U(S)=[m]\setminus\bigl(S\cup N_{G_P}(S)\bigr)$. The
\emph{residual pieces} of $S$ are the connected components
$H\in\pi_0\bigl(G_P[U(S)]\bigr)$ of the induced subgraph on $U(S)$.
\end{definition}
````
<!-- END QUOTE CV_BLOCKS -->

At each selected transverse crossing, an oriented smoothing joins each incoming branch to the other visit's outgoing branch. These are precisely the two reconnections specified by SM. Following the resulting successors therefore gives the same closed cycles of old directed arcs, one for each common carrier. Corners are the same original vertices and selected crossing turns. The common undominated graph has the same connected components $H$. CV_SMOOTH clauses (iii)–(iv) and SM_BLOCKS assign a block to the unique carrier containing both visits of every one of its crossings, so the owners agree.

Here the geometric corner carriers are regular:

<!-- BEGIN QUOTE SM_CARRIER_REGULAR -->
**SM_CARRIER_REGULAR — SM11 `sm-3-statesum.tex:73–91`**

````tex
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
````
<!-- END QUOTE SM_CARRIER_REGULAR -->

When a rounded representative of a CV carrier is used, choose the local rounding with the same principal-turn increments. The quoted CV turn-lift clause below verifies its rotation. No rotation identity is inferred from a Gauss word, polynomial, or arbitrary smoothing arc.

**Part 3: actual diagrams, polynomial convention, and products.** The sign conventions and actual piece construction are:

<!-- BEGIN QUOTE SM_POSITIVE -->
**SM_POSITIVE — SM11 `sm-3-statesum.tex:325–335`**

````tex
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
````
<!-- END QUOTE SM_POSITIVE -->

<!-- BEGIN QUOTE CV_PIECE -->
**CV_PIECE — CV `d1_setup.tex:565–575`**

````tex
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
````
<!-- END QUOTE CV_PIECE -->

<!-- BEGIN QUOTE CV_PIECE_CURVE -->
**CV_PIECE_CURVE — CV `d1_setup.tex:592–610`**

````tex
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
````
<!-- END QUOTE CV_PIECE_CURVE -->

<!-- BEGIN QUOTE CV_SURVIVING_RECORD -->
**CV_SURVIVING_RECORD — CV `d1_setup.tex:661–665`**

````tex
Applying Step 5 to the carrier of $H$ with $K=H$, which Steps 3 and 4
licence --- Step 4 supplying both the non-interlacing and the connectedness
hypotheses --- performs exactly the statement's third operation and gives
$C_H$. Its rotation system at each surviving crossing is the carrier's,
which is the parent's, since smoothing at other points does not disturb the
````
<!-- END QUOTE CV_SURVIVING_RECORD -->

The SM block construction records the inherited data explicitly:

<!-- BEGIN QUOTE SM_BLOCK_RECORD -->
**SM_BLOCK_RECORD — SM11 `sm-3-statesum.tex:4671–4681`**

````tex
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
````
<!-- END QUOTE SM_BLOCK_RECORD -->

For each nonempty block $H$, CV's $C_H$ and SM's $D_H$ are thus actual one-component diagrams. Their crossing occurrences correspond to the same restricted parent visits, in the same oriented cyclic order. Pairing is the same crossing label. Their surviving directions are inherited from the same parent branches; the positive-over rule is the same determinant inequality, so the over/under bits and crossing signs also agree. This supplies a named decorated-record isomorphism between actual diagrams, without claiming that an arbitrary restricted word is realizable.

The polynomial conventions and the equality/transport statements used here are:

<!-- BEGIN QUOTE CV_HOMFLY -->
**CV_HOMFLY — CV `d1_setup.tex:552–563`**

````tex
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
````
<!-- END QUOTE CV_HOMFLY -->

<!-- BEGIN QUOTE CV_HOMFLY_AXIOM -->
**CV_HOMFLY_AXIOM — CV `d10_axioms.tex:342–349`**

````tex
\begin{axiom}[HOMFLY--PT]\label{ax:homfly}
There is a unique map $L\mapsto P_L(a,z)\in\mathbb Z[a^{\pm1},z^{\pm1}]$ from
isotopy classes of oriented links in $S^3$ satisfying
$P_{\bigcirc}=1$ and $aP_{L_+}-a^{-1}P_{L_-}=zP_{L_0}$ for every skein triple.
In particular $P_L$ is invariant under the Reidemeister moves. One consequence
is consumed as part of this entry: $P_K\in\mathbb Z[a^{\pm1},z^2]$ for a
\emph{knot} $K$, so that the $z^0$ coefficient of a product of knot
polynomials is the product of their $z^0$ coefficients.
````
<!-- END QUOTE CV_HOMFLY_AXIOM -->

<!-- BEGIN QUOTE SM_COEFFICIENT_TRANSPORT -->
**SM_COEFFICIENT_TRANSPORT — SM11 `sm-3-statesum.tex:981–990`**

````tex
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
````
<!-- END QUOTE SM_COEFFICIENT_TRANSPORT -->

<!-- BEGIN QUOTE SM_LP -->
**SM_LP — SM11 `sm-3-statesum.tex:1041–1060`**

````tex
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
````
<!-- END QUOTE SM_LP -->

<!-- BEGIN QUOTE SM_RECORD -->
**SM_RECORD — SM11 `sm-3-statesum.tex:1215–1225`**

````tex
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
````
<!-- END QUOTE SM_RECORD -->

<!-- BEGIN QUOTE SM_GAUSSIAN_MAP -->
**SM_GAUSSIAN_MAP — SM11 `sm-3-statesum.tex:1064–1070`**

````tex
Start in $R_G=\mathbb Z[\mathrm i][a^{\pm1},z^{\pm1}]$ with
$\mathrm i^2=-1$. The elements $\mathrm ia$ and $-\mathrm iz$ are units,
so they define a Laurent-ring homomorphism and a first evaluation
\begin{equation}\label{lp:gaussian}
 \phi(l)=\mathrm ia,\qquad \phi(m)=-\mathrm iz,
 \qquad P_D^G=\phi(F_D).
\end{equation}
````
<!-- END QUOTE SM_GAUSSIAN_MAP -->

<!-- BEGIN QUOTE SM_INTEGRAL_DESCENT -->
**SM_INTEGRAL_DESCENT — SM11 `sm-3-statesum.tex:1133–1138`**

````tex
Both recurrences therefore put $P_D^G$ in $M_c$. The standard inclusion
$R\hookrightarrow R_G$ is injective (the Gaussian coefficient ring has
the free integer basis $1,\mathrm i$). There is consequently one $P_D\in R$
with image $P_D^G$. This proves support and integral descent simultaneously.
The local source equalities remain equalities after $\phi$ and, by
injectivity, are equalities in $R$.
````
<!-- END QUOTE SM_INTEGRAL_DESCENT -->

CV's HOMFLY assignment, evaluated on actual oriented diagrams, is invariant under the stated diagram moves and satisfies the displayed campaign skein and circle value. SM's polynomial has the same invariances, skein, and circle value by `lp:core`. The hypotheses of SM `lp:coefficient-transport` therefore apply to these two assignments on their common diagram domain, identifying their normalizations; this step uses the already-declared transport premise, not a new literature acceptance. The named-record isomorphism just constructed then gives equality of the source polynomial values by `rp:record-polynomial`; apply the displayed common map $\phi$ to those equal source values, then use the quoted injective integral descent to obtain equal campaign values in $\mathbb Z[a^{\pm1},z^{\pm1}]$. The normalization identification just proved gives equality with the CV HOMFLY values. In symbols, distinguishing the two definitions temporarily,

$$
P_H^{\rm CV}=P_H^{\rm SM}.
$$

(12)

For an original carrier $L$, SM `cb:products` now applies to its actual block diagrams. Its owner set is the CV owner set by part 2. Substitute (12) into that printed product identity, and separately use the crossing-count identity and CV $w(H)=|H|$. These two applications give

$$
H_L^+=\prod_{H\text{ owned by }L}P_H^{\rm CV}=P_{S,L}^{\rm CV},
\qquad m_L=\sum_{H\text{ owned by }L}|H|=w_{S,L}^{\rm CV}.
$$

(13)

Each final equality here is the corresponding definition in the CV `def:X1` quotation. If there are no blocks, SM `cb:products` explicitly gives the actual diagram value 1 and crossing count 0, exactly CV's algebraic empty product and empty sum. Thus (13) covers that case too; no empty link, arbitrary realization, or division by a coefficient has been used.

**Part 4: rotations, slots and selectors.** The definitions and turn identity are:

<!-- BEGIN QUOTE SM_PRINCIPAL -->
**SM_PRINCIPAL — SM11 `sm-1-polygons.tex:374–384`**

````tex
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
````
<!-- END QUOTE SM_PRINCIPAL -->

<!-- BEGIN QUOTE CV_PRINCIPAL -->
**CV_PRINCIPAL — CV `d1_setup.tex:22–39`**

````tex
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
````
<!-- END QUOTE CV_PRINCIPAL -->

<!-- BEGIN QUOTE SM_ROTATION -->
**SM_ROTATION — SM11 `sm-1-polygons.tex:395–406`**

````tex
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
````
<!-- END QUOTE SM_ROTATION -->

<!-- BEGIN QUOTE SM_RETAINED -->
**SM_RETAINED — SM11 `sm-3-statesum.tex:242–248`**

````tex
\begin{definition}[uniform subpolygons; retained data]\label{def:uniform}
A subpolygon $Q$ is \emph{uniform} if all its turns have one sign and
\emph{mixed} otherwise. A decomposition $S$ is \emph{uniform} if all its
subpolygons are. For a subpolygon $Q$ write $r_Q=\rot(Q)$
(Lemma~\ref{lem:rot}, applicable by Lemma~\ref{lem:carriers}), $m_Q$ for its
number of crossings, and $\ell_Q$ for its number of left turns.
\end{definition}
````
<!-- END QUOTE SM_RETAINED -->

<!-- BEGIN QUOTE CV_ABS_ROT -->
**CV_ABS_ROT — CV `d1_setup.tex:782–785`**

````tex
Lemma~\ref{lem:turnlift} constructs the lift and proves that these values do
not depend on its choices, on the seam, or on an orientation-preserving regular
reparametrisation. For either a polygon or a $C^1$ regular closed curve put
$R(L)=|\rot(L)|$.
````
<!-- END QUOTE CV_ABS_ROT -->

<!-- BEGIN QUOTE CV_TURN_SUM -->
**CV_TURN_SUM — CV `d1_setup.tex:798–808`**

````tex
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
````
<!-- END QUOTE CV_TURN_SUM -->

Corresponding carriers have the same incoming and outgoing corner directions. Both principal-turn definitions select the angle in $(-\pi,\pi)$ with the displayed cosine and determinant sign. Regularity ensures that this angle exists; uniqueness in that interval makes their turn angles equal corner by corner. CV `lem:turnlift(ii)` converts its rotation definition into the sum of those angles divided by $2\pi$, exactly SM's definition. Clause (iii) gives the same value on the compatible rounded carrier. Taking absolute values gives

$$
R^{\rm CV}(L)=|r_L^{\rm SM}|.
$$

(14)

Using the second equality of (13) first, and then (14), the CV slot becomes

$$
1-w_{S,L}^{\rm CV}-R^{\rm CV}(L)=1-m_L-|r_L^{\rm SM}|=d_L^{\rm SM}.
$$

(15)

The first equality in (13) identifies the whole polynomials, and (15) identifies the exponents at which the coefficient is read. Equality of coefficients at the identical monomial therefore gives

$$
\Omega_1^{\rm CV}(S,L)=c^{\rm SM}(L).
$$

(16)

This argument includes absent monomials, whose coefficients are zero. It imposes no sign gate or nonzero gate.

CV's selector is:

<!-- BEGIN QUOTE CV_WEIGHT -->
**CV_WEIGHT — CV `d1_setup.tex:487–512`**

````tex
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
````
<!-- END QUOTE CV_WEIGHT -->

The common corner directions give the same left/right signs and the same corner count. For each carrier, both selectors are consequently 1 if all turns are right, ((-1)^{\#\text{corners}}) if all are left, and 0 if mixed, exactly as in SM's selector quotation. Their products over the common carriers agree. Multiply (16) over those carriers and then by this common selector. For each independent support the summands in the two formulas agree, including a mixed support with zero selector. Finally sum over the common finite collection of independent supports established in part 1. By the two quoted formulas,

$$
C^{\rm SM}(P)=X_1^{\rm CV}(P)
\quad\text{for every }P\in\mathcal U_n^{\rm SM}.
$$

(17)

This is the separate factorization-based identification required by SM's warning, not a reinterpretation of the restricted selector lemma.

**Part 5: side chambers.** The chamber and constancy clauses are:

<!-- BEGIN QUOTE SM_CHAMBER -->
**SM_CHAMBER — SM11 `sm-1-polygons.tex:194–199`**

````tex
\begin{definition}[chambers]\label{def:chamber}
A \emph{chamber} is a connected component of the space of generic polygons
$\mathcal U_n/(\ZZ/n)$; its preimage in $\mathcal U_n$ is a union of at most
$n$ components of $\mathcal U_n$ permuted by $\sigma$, the \emph{labelled
chambers}.
\end{definition}
````
<!-- END QUOTE SM_CHAMBER -->

<!-- BEGIN QUOTE SM_C_LOCAL -->
**SM_C_LOCAL — SM11 `sm-4-knotlaws.tex:36–39`**

````tex
\begin{proposition}[chamber constancy]\label{prop:C-chamber}
The state sum $C$ of Definition~\ref{def:C} is constant on every chamber.
\status{proved (refereed: bench A, 2026-09-05T18:22:57Z; transcribed from CV prop:chamberinv, through Lemma~\ref{lem:carriers} and the named-record bridge (Lemma~\ref{rp:record-polynomial}, Theorem~\ref{lp:core}) (C020, C027); F-25-95; single convention, CV one-based tail = this document (F-25-104))}
\end{proposition}
````
<!-- END QUOTE SM_C_LOCAL -->

<!-- BEGIN QUOTE SM_C_SHIFT -->
**SM_C_SHIFT — SM11 `sm-4-knotlaws.tex:87–98`**

````tex
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
````
<!-- END QUOTE SM_C_SHIFT -->

<!-- BEGIN QUOTE CV_X_LOCAL -->
**CV_X_LOCAL — CV `d1_setup.tex:932–938`**

````tex
\begin{proposition}[chambers and chamber invariance]\label{prop:chamberinv}
Fix $n\geq3$.
\begin{enumerate}
\item[(i)] The generic locus $\mathcal U_n$ is open in $(\mathbb R^2)^n$, and
every chamber --- every connected component of it --- is open and path connected.
\item[(ii)] $X_1$ is constant on each chamber.
\end{enumerate}
````
<!-- END QUOTE CV_X_LOCAL -->

Take either connected punctured image of the labelled germ from SM `def:germ`. It lies in one labelled SM component. By (1), that component is a connected subset of the labelled CV generic locus, so it lies in a unique CV component. CV `def:event` defines its side chamber as exactly the component containing that same punctured image. Thus the component just found is its CV side chamber. The quotient by cyclic shifts in the SM chamber definition changes the names of representatives, not the value of $C$, whose invariance is quoted above. A fixed continuous labelled representative of the germ suffices on each side.

Choose $t_+>0$ and $t_-<0$ sufficiently near zero. SM's chamber constancy identifies $C(P(t_\pm))$ with its corresponding SM side value. Equation (17) identifies each of those point values with $X_1(P(t_\pm))$. CV's chamber constancy identifies the latter with its value on the containing CV side chamber. Consequently

$$
C^{\rm SM}(P_+^{\rm SM})=X_1^{\rm CV}(P_+^{\rm CV}),
\qquad
C^{\rm SM}(P_-^{\rm SM})=X_1^{\rm CV}(P_-^{\rm CV}).
$$

(18)

These are equalities of **values on corresponding sides**. They do not assert equality of a quotient SM chamber with a labelled CV chamber, or equality of their underlying generic loci. This proves B4. ∎

## §3. The displayed bridge theorem

**Theorem.** Take the frozen RA result in the exact CV `ax:R` form quoted in §1, with its declared inputs. Let $\mathcal E_{\rm SM11}^{T}$ denote the simple triple wall germs defined in SM11. Then

$$
\boxed{\begin{gathered}
\text{RA theorem in the quoted CV }\texttt{ax:R}\text{ form}
\\[2pt]
\Longrightarrow\quad
\forall P\in\mathcal E_{\rm SM11}^{T},\quad C(P_+)=C(P_-).
\end{gathered}}
$$

(19)

**Proof.** Fix any SM11 simple triple wall germ. B1 makes it a CV event of polygons, generic at every nonzero time and nongeneric at zero. B2 makes its zero set exactly the four indexed members in (3), with increasing edge representatives, pairwise remoteness, and a central point interior to all three. B3 proves that every member changes sign. The germ is therefore a simple transversal Reidemeister-III event with precisely the antecedent of the CV statement quoted in §1. The imported RA theorem applies and yields

$$
X_1^{\rm CV}(P_+^{\rm CV})=X_1^{\rm CV}(P_-^{\rm CV}).
$$

(20)

Use the positive-side equality from (18) to replace the left side of (20), and then the negative-side equality from (18) to replace its right side. The result is

$$
C^{\rm SM}(P_+^{\rm SM})=C^{\rm SM}(P_-^{\rm SM}).
$$

(21)

The germ was arbitrary in SM11's printed simple-triple class. This is exactly its quoted `hyp:R`. ∎

## §4. Deflation

**proves: RA's theorem ⟹ SM11 `hyp:R`, under identifications B1/B4, which are proved; does not prove: R itself, the converse inclusion, anything about the letter.**

The coordinate relabelling is literal; generic-locus inclusion, the event transfer, the state-sum identification and side-value correspondence are proved. The statement does not certify the underlying R package anew, remove any of its recorded obligations, or prove its literary inputs. No failure witness was found in B2 or B3. No frozen frame, manuscript, letter, or source was edited. Same-bench checks reported in §5 are not bench A's referee verdict.

## §5. Self-verification at the bytes

Final root verification at 2026-09-07T05:24:40Z: `python3 -B VERIFY.py --self-test` and `python3 -B VERIFY.py --preseal` both exited 0. `SELF_TEST.json` records **28 rejected negative controls and 5 clean positive groups**. `VERIFICATION.json` records **all 53 payload hashes in the three frames (20/13/20), their exact inventories, all 59 quoted line slices and their rendered blocks, all 3 literal shasum lines, and all 6 formal polynomial identities checked**. These are byte/algebra checks, not a mathematical acceptance verdict.

Every quoted source file was re-read from its frozen frame on both runs; its full hash and each listed excerpt hash were recomputed. No quotation is verified by a locator alone. The source SHA256s are in `QUOTATIONS.json`; the manifest self-hashes are reproduced in §0 and rechecked in both receipts. The final seal binds this document, the quote index, verifier, receipts, and same-bench review record. The channel post supplies that seal's hash. Missing or wrong seals are rejected by the required-seal replay; the actual command and unchanged-inventory check are recorded alongside the lane after sealing.

The complete re-read list is below. Full source-file hashes are also recorded in `QUOTATIONS.json` and verified against each frozen manifest.

| ID | Frame and exact line range | Quoted-byte SHA256 |
|---|---|---|
| SM_HYP | SM11 `sm-4-knotlaws.tex:1149–1151` | `58c0b3811763d8192e99a9038330c1e7e73305f4d978a205948c01da9e51a50e` |
| CV_R | CV `d10_axioms.tex:18–24` | `08cbfddd30a4a0e814a0d7888e05d513a32785037f1c91ed7e9117909a20182d` |
| RA_LOCAL | RA `R_ATTACHMENT_WARRANTS.md:16–29` | `54f61ad35017bac6cf6b4413db8af25cc316fea6bdd64591ab9365c8a45a4696` |
| SM_MAP | SM11 `sm-1-polygons.tex:13–17` | `6097b89daf082350088bc7d6aaba771780ca76ac3fa3caff86535832543bb9a5` |
| SM_OBJECT | SM11 `sm-1-polygons.tex:27–51` | `d19d0f632c7ca60ea623e9ef065830c2046135150cce05b65f6b6b2a285cbcf1` |
| SM_GENERIC | SM11 `sm-1-polygons.tex:99–108` | `ce6330dde8ebf1dc64e7fe18ffbd2053c8a1f373d37dc03a5c163020acb49df0` |
| SM_G1 | SM11 `sm-1-polygons.tex:110–123` | `451cfb4abaf73e40ba936f88f5206b193c1c0906356afc6a3ec2ebd6cb6f95d8` |
| SM_GERM | SM11 `sm-1-polygons.tex:653–668` | `1ffedf8e437dd9a905e7fa5f1cc03391b405b6e79cb41bcac9ebaa8372a179ba` |
| SM_TRIPLE | SM11 `sm-1-polygons.tex:735–738` | `e82358caf4130a75c4e2362128832ebb4b6e1429c092a6a202e1366111001339` |
| SM_TRIPLE_SIDES | SM11 `sm-1-polygons.tex:670–675` | `2167c8099c717dc9106e69f1b7d6393d5574b8b363bb06d7a05c74b52cac61c3` |
| CV_OBJECT | CV `d1_setup.tex:8–19` | `a2175107fe07e29481922115d579957107af5aeff7b8af74d92f85d3e2efdce3` |
| CV_UNCONDITIONAL | CV `d1_setup.tex:42–55` | `7c73a7274cc1409cb900009c6b2f874dbfe416f292b30c16bc6c52d96af125bd` |
| CV_ACTIVATION | CV `d1_setup.tex:58–64` | `09ca59ef0a7dcd71db39c858cf7ad9f83d6daac2b74913a3aad580dd550645c0` |
| CV_G5 | CV `d1_setup.tex:99–114` | `e5df462a45fd397d08e37f5a11dac160a81aa0b202beff83e85e5fcaae2118d7` |
| CV_G3 | CV `d1_setup.tex:115–127` | `8590a297d277c406100b4bf18865f64a07145a2dd041d4eae8b94a88e49b59c1` |
| CV_G4 | CV `d1_setup.tex:128–134` | `9f16f70090648dc3a21eee258a07012fac808dbb5490c1de14edcdf0b8123eb7` |
| CV_GENERIC | CV `d1_setup.tex:220–237` | `df5234b55c4782f8f811467f956ea32dace3b5f28d505f32108d78c1f18c6e6d` |
| CV_EVENT | CV `d1_setup.tex:1072–1086` | `2cbaa5cf8a72a24197cb5722026fa0aa0f60ffc4af74fc5b4280a2cd0f7fdee7` |
| CV_INDEX | CV `d1_setup.tex:168–179` | `71a818bf79b7922812d7e7ee57fae1f127bc4799fc0dfc9d62907111c10f87b7` |
| CV_PARAMETERS | CV `d1_setup.tex:198–207` | `b910a9ca455d9e96cbb0beae14c2956431302929d1f5ac6f93b1eb90faac6ea3` |
| CV_IDENTITIES | CV `d8a_dictionary.tex:429–435` | `daf54a5e4c41719b39c19192782114c31d3623d48087fe911ef288a43cb7d411` |
| SM_LEGEND | SM11 `sm-0-legend.tex:56–65` | `a57cf5b60809abb2dc6423fe52f31995a13058ccda010fa2c49c6dcd04fd79b1` |
| SM_C | SM11 `sm-3-statesum.tex:1688–1700` | `5600f2e93e417dff298b5593ef55c3ac3c0cfee21b1987da3cf8c5214c1d9ec5` |
| SM_SELECTOR | SM11 `sm-3-statesum.tex:1787–1796` | `230faeb00bf38484e9b4e5b7b85cc3c04f17ff4ee582fb737ab5f45352a0c945` |
| SM_WARNING | SM11 `sm-3-statesum.tex:1812–1820` | `7c23de1ad5b99b0a12ef8c132b825f03a3c9a98a142b2467920f2a02a58348ae` |
| CV_X1 | CV `d1_setup.tex:908–930` | `02780e645f835df85550797520e2daa03c630d6a09348c77eb6198d8ff05ec79` |
| SM_GAUSS | SM11 `sm-1-polygons.tex:237–255` | `ef776bcefb1611adcb71245dadf9f12f24088bb297f9bcf3c21ed08f971cf04b` |
| CV_GAUSS | CV `d1_setup.tex:305–313` | `03cb183dd4834d041e6cb8f8bed5a4b977ca09295d31b8b1935cab3252b98897` |
| CV_INTERLACE | CV `d1_setup.tex:346–353` | `c08196b21dd3194218dac795b757a2ca7f7b6f30b54d8e33a58d287901f46704` |
| SM_SMOOTH | SM11 `sm-3-statesum.tex:9–27` | `1b84af793817e437ba9f4e0dc000df25a5687e28319e4900a9c7a3993af3af2a` |
| CV_SMOOTH | CV `d1_setup.tex:355–381` | `406cb2daa12b7ec0c38944f7ffc64cb886a09e84527366e9d3a31dfb06ce9861` |
| SM_POSITIVE | SM11 `sm-3-statesum.tex:325–335` | `bfc2e045074ec73737795eaf7b3e3e89c69be6831ca857a10c78688ce9ce064d` |
| CV_PIECE | CV `d1_setup.tex:565–575` | `1a017c17a6ad554acab01d7ebe4a83e092ae0441a9af784530a6270b11d2788b` |
| CV_PIECE_CURVE | CV `d1_setup.tex:592–610` | `fa7d9ca3f743d718b3a0bbc64c0b20ec128bffe172d7c2ad5b0adff2d01f0591` |
| SM_BLOCKS | SM11 `sm-3-statesum.tex:4623–4648` | `98208e5ab442593e4652ad921999327c2e1726574a6382f740657e202a3b36dd` |
| CV_BLOCKS | CV `d1_setup.tex:514–518` | `0ddfd8b2708f7a2fe811e7cdb735ae7ceb01522495c94e54b4d2763f9b2d087e` |
| SM_LP | SM11 `sm-3-statesum.tex:1041–1060` | `9402c11980c960a142530d82a7e4dbae786ff8e2f8b12ddd5260bb53b02c7b37` |
| SM_RECORD | SM11 `sm-3-statesum.tex:1215–1225` | `5423eecc7c04037d3e1e450ac9252d9552ec4ac6e27a7176c1826126ce5476e1` |
| CV_HOMFLY | CV `d1_setup.tex:552–563` | `84485ff9cef3ae2f394ba9f6cafd6c70c7144b3d72ccef33da97c354b28454df` |
| SM_PRINCIPAL | SM11 `sm-1-polygons.tex:374–384` | `37c56dc18bbb7732fae9c0e568eb85ae62a2795b7f51b44f7fa540c689dd09e1` |
| CV_PRINCIPAL | CV `d1_setup.tex:22–39` | `05b9638a574b6308be0c146e9f9aa5e43aa1bc894ebfaf83292297568d5fe4b3` |
| SM_ROTATION | SM11 `sm-1-polygons.tex:395–406` | `b5e8e00155f2a52100d6c426a120afc9444c8e59513a5d4d577b4cff55156376` |
| SM_RETAINED | SM11 `sm-3-statesum.tex:242–248` | `62f830c6c90d7b15728edc7bb94617f0227cede27776abda8a182d635bf72794` |
| CV_ABS_ROT | CV `d1_setup.tex:782–785` | `43fd799979c8a59c3ba08eb3e9db63c8ae83a067ae6c0dad479976d72b561350` |
| CV_TURN_SUM | CV `d1_setup.tex:798–808` | `e83c843b2d907eb5719ec3918542f8a95e92bbf38dd504b8ef8774e65386b756` |
| CV_WEIGHT | CV `d1_setup.tex:487–512` | `bac66f0626651903dd096bddb629c7d6b6add8d2648ae24555184d93376071fa` |
| SM_CHAMBER | SM11 `sm-1-polygons.tex:194–199` | `326109fde629ec8368f529d669cedb639c787f31c00804d47ef326b2953a840a` |
| SM_C_LOCAL | SM11 `sm-4-knotlaws.tex:36–39` | `2c7af0a8184509c31841de989e1b85d2848370ddcf47418e5706dbbcc2d8760f` |
| CV_X_LOCAL | CV `d1_setup.tex:932–938` | `c92d68deb08f76e1fdd849b37dded63eb2ee0596d18d746a62fd52715b4ca74a` |
| SM_CROSSINGS | SM11 `sm-1-polygons.tex:137–155` | `75e0522311e2fd02392373cafc5252b03d0dba6d468ae9f5ed49d78ea6fc9217` |
| SM_CARRIER_REGULAR | SM11 `sm-3-statesum.tex:73–91` | `2071cc4d7f9e7def6381969a81bcd6e7c90554bc50b3cae755163c2192d40652` |
| SM_BLOCK_RECORD | SM11 `sm-3-statesum.tex:4671–4681` | `3a109c6aab836e7256cb39d8e59c316a44632452c40f20a99b1fc5bae2462f98` |
| CV_SURVIVING_RECORD | CV `d1_setup.tex:661–665` | `a8b9f34403838f575aa7e1325d9d9b583bc04ab03cfcac307e5994b9d69189f1` |
| SM_COEFFICIENT_TRANSPORT | SM11 `sm-3-statesum.tex:981–990` | `5d9c6b65d2722921b9f85549f0944d2dc4ccca6f3878d52f3e9791ea95cd1e94` |
| CV_HOMFLY_AXIOM | CV `d10_axioms.tex:342–349` | `33214b3464886256d97fc8ab21eb4a9cd5fbb8b8147a793a2c3afd825b077bfa` |
| RA_PARAMETERS | RA `R_ATTACHMENT_WARRANTS.md:45–64` | `5aaf93b33d6f12aa4d8889cf157c28c2810aa2d2e6205f3f6e6ac48c83136eb0` |
| SM_GAUSSIAN_MAP | SM11 `sm-3-statesum.tex:1064–1070` | `84ab857ec0ed2abf24226cc0fc8fa50f69d24422f961aae263aa12765cb8808a` |
| SM_INTEGRAL_DESCENT | SM11 `sm-3-statesum.tex:1133–1138` | `122ab6a04c00e1c14501bd7b6d257baca36775f3339fd030c50dba9fee02cffe` |
| SM_C_SHIFT | SM11 `sm-4-knotlaws.tex:87–98` | `2f6dbdfde7511c04031ba8beb4442f30c38e85a78c22a8ef1c8716a832f14999` |

`VERIFY.py` is read-only: it re-reads all three current frozen manifests and payloads, every quoted source-file range and every exact quotation embedded in this document; it also checks the signed G3/G4 polynomial identities by exact integer polynomial expansion. Its self-tests include clean positive cases and deliberately broken hash, quote, locator, inventory and algebra cases. These checks verify bytes and the stated algebraic identities; the prose proofs of B1–B4 require the named referee's reading.

The seal is `SHA256SUMS`, containing every payload in this lane and excluding only itself to avoid self-reference. Its self-hash is posted in `CHANNEL_codex.md`. From this directory, `shasum -a 256 -c SHA256SUMS` must read every row OK. For read-only replay, run `python3 -B VERIFY.py --require-seal <posted SHA256SUMS hash>`. No command in that replay writes into the lane. The lane is immutable after the single channel post; a later correction requires a new lane.
