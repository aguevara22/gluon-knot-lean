# Selected source statements and printed proofs

Read source context for unlabelled notation. Historical status tags are not acceptance.

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
