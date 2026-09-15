# Exact final target

Prove that the corner state sum C of SM `def:C` satisfies every wall law on
the domains of SM `cor:A-lawful`, together with SM `thm:C-soft` in every soft
sector. The final declaration is `SM.corner_laws_and_soft`. Define its conclusion
as the conjunction of these actual C identities, with their printed quantifiers,
signs and domains. Do not replace it by a theorem about a freely supplied lawful
function. Its only unproved nonstandard inputs may be the five listed literature
interfaces. It must not retain an R assumption or assume the desired laws.

Required coverage:
- Chamber constancy and silent-wall invariance.
- The flat deletion law.
- Both bigon branches and the sliding branch of the vertex-edge law, with the
  stated sign and the actual two child polygons.
- Triple-wall invariance at every source simple triple wall, after proving R.
- The full cusp jump on the source domain (the deletion satisfies G1), including
  threaded cusps; retain the direct empty-cusp zero result.
- The soft theorem in every sector, including zero-selector sectors.

Use the normalizations and reversal/cyclic identities inherited with
`cor:A-lawful` as stated there. No stronger cusp domain is commissioned.
Full cusp is obtained in the supplied proof through `cor:C-inherits`, so its
comparison/transport/amplitude prerequisites remain in scope. Equality C=A is
a helper in that route; it is not a replacement for the requested final laws.

The source calls R a hypothesis. This deliverable must prove it. The extracts
below preserve the source's conditional wording; the final assembly instantiates
that conditional theorem with the separately proved R result.

# Selected source statements and printed proofs

Read source context for unlabelled notation. Historical status tags are not acceptance.

## prop:C-chamber — PROVE

reference/SM/sm-4-knotlaws.tex:36–39

```tex
\begin{proposition}[chamber constancy]\label{prop:C-chamber}
The state sum $C$ of Definition~\ref{def:C} is constant on every chamber.
\status{proved (refereed: bench A, 2026-09-05T18:22:57Z; transcribed from CV prop:chamberinv, through Lemma~\ref{lem:carriers} and the named-record bridge (Lemma~\ref{rp:record-polynomial}, Theorem~\ref{lp:core}) (C020, C027); F-25-95; single convention, CV one-based tail = this document (F-25-104))}
\end{proposition}
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

## thm:C-S5 — PROVE

reference/SM/sm-4-knotlaws.tex:910–913

```tex
\begin{theorem}[empty-cusp zero]\label{thm:C-S5}
At a simple empty cusp, $C(P_{\rm no})=0$.
\status{proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from CV thm:zeroanchor(S5) (P-25-2, C006))}
\end{theorem}
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
