# L-3 EXIT — T1: does each cited page carry the cited statement?

T1 = full text on disk, hashed and logged, and **the statement at the cited
locator is what the manuscript uses**, checked word by word: hypotheses,
conclusion, objects, quantifiers. Frame SM6. Stamp 2026-09-06T01:56:31Z.

Every row below was read at this seat's own extraction
(`work/geiges_book_p108-132.txt`, `work/geiges_survey_p44-48.txt`,
`work/etnyre_p4-20.txt`); the two rows whose content turns on a single symbol
were re-read as rendered page images at 4× (`work/etnyre_p15_eq9.png`,
`work/geiges_p117_prop3559.png`). Text layer and image agree.

**Page mappings established by inspection, not assumed:** Geiges book printed
p = PDF page − 18; Geiges survey printed p = PDF page; Etnyre printed p = PDF
page.

---

## 1. The eleven cited locators, one row each

| # | SM6 cites | source statement at that page, as printed | verdict |
|---|---|---|---|
| 1 | Etnyre **§2.1, p. 4** — the contact form | "$\xi_{std}=\mathrm{span}\{\tfrac{\partial}{\partial y},\ \tfrac{\partial}{\partial x}+y\tfrac{\partial}{\partial z}\}$. Clearly $\xi_{std}$ is the kernel of the 1–from $\alpha=dz-y\,dx$" | **T1 exact** |
| 2 | Etnyre **§2.4, p. 10** — positive transversality, front page | "$T_xT\oplus\xi_x=T_xM$"; "we can orient $T$ so that it always intersects $\xi$ positively. When $T$ is so oriented we call $T$ a positive transverse knot"; "$\Pi:\RR^3\to\RR^2:(x,y,z)\mapsto(x,z)$" | **T1 exact for the class and the page**; the coordinate inequality $z'-yx'>0$ is the SM's own (correct) substitution, not a quoted sentence |
| 3 | Etnyre **eq. (5), §2.6.2, p. 14** | "$r(L)=\tfrac12(D-U)$, where $U$ is the number of up cusps in the front projection and $D$ is the number of down cusps" | **T1 exact** |
| 4 | Etnyre **eq. (7), §2.6.2, p. 14** | "$tb(L)=\mathrm{writhe}(\Pi(L))-\tfrac12(\text{number of cusps in }\Pi(L))$" | **T1 exact** (SM6's $D+U$ for the total cusp count is justified in the block itself) |
| 5 | Etnyre **eq. (9), §2.6.4, p. 15** | "$sl(T)=\mathrm{writhe}(\Pi(L))$" | **T1 with two defects**, both glyph-verified: the argument is `Π(L)` where the object is `T`; **no hypothesis** is stated on the front. SM6 says only that Etnyre "states it" — the verb is right |
| 6 | Etnyre **§§2.6.3–2.6.4, p. 15** — the $sl$ convention | §2.6.3: "let $T'$ be a copy of $T$ obtained by pushing $T$ slightly in the direction of $v$. The self-linking number $sl(T)$ of $T$ is the linking of $T'$ with $T$." §2.6.4: "the vector $v=\tfrac{\partial}{\partial y}$ is always in $\xi_{std}$ and thus can be used to trivialize $\xi_{std}$ independent of a Seifert surface for $T$" | **T1 exact.** This is the strongest single match in the entry: `rem:sl-convention` names $\partial_y$, and $\partial_y$ is the source's own choice at the cited page |
| 7 | Etnyre **§2.9, Lemma 2.22, eq. (17), p. 19** | "**Lemma 2.22.** The invariants of Legendrian knots and their transverse push offs are related by $sl(T_\pm(L))=tb(L)\mp r(L)$." | **T1 exact**; SM6 uses the $+$ instance |
| 8 | Geiges book **Prop. 3.5.9, p. 117** | "**Proposition 3.5.9** Let $K$ be a Legendrian knot in $(\RR^3,\xi_{st})$. Write $K_F$ for the knot diagram of $K$ obtained by the front projection. Then the Thurston–Bennequin invariant of $K$ is given by $\mathtt{tb}(K)=\mathrm{writhe}(K_F)-\tfrac12\#(\mathrm{cusps}(K_F))$." | **T1 exact** (glyph-verified). Same formula as Etnyre eq. (7) after $\#\mathrm{cusps}=D+U$ |
| 9 | Geiges survey **§3.1, Lemma 3.3, p. 46** | "**Lemma 3.3.** The self-linking number $l(\gamma)$ of a transverse knot is equal to the writhe $w(\gamma)$ of its front projection." | **T1 exact.** §3.1 opens p. 45; Lemma 3.3 and its proof are on p. 46 — the cited page is right |
| 10 | Geiges book **Prop. 3.5.32, p. 127** | "**Proposition 3.5.32** The self-linking number $\mathtt{sl}(K)$ of a transverse knot $K$ in $(\RR^3,\xi_{st})$ is equal to the writhe of its front projection." | **T1 exact** |
| 11 | Geiges survey **Def. 3.2 + the following paragraph, p. 45** | "**Definition 3.2.** The self-linking number $l(\gamma)$ of the transverse knot $\gamma$ is the linking number of $\gamma$ and $\gamma'$." Following paragraph: "in place of $\partial_x$ we could have chosen any nowhere zero vector field $X$ in $\xi_0$ to define $l(\gamma)$ …" | **T1 exact**, and the "following paragraph" is exactly where the independence lives |

Registry-only corroborations, also checked: Geiges book **Def. 3.5.28 p. 125**,
**Rem. 3.5.29(2) p. 126**, **Cor. 3.5.31 p. 127** — all three at the claimed
pages, and all three the same notion of $sl$ as Etnyre §2.6.3.

## 2. Quantifier and hypothesis check on the two identity clauses

**Front-writhe.** Geiges quantifies over *transverse knots in
$(\RR^3,\xi_{st})$*; SM6 quantifies over *generic positive transverse fronts*
(`def:transverse-front`). The instantiation is licensed in both directions:

- SM6's class is **at least as strong** as what Geiges's proof consumes. His
  proof invokes Prop. 3.4.14, which is stated "given by a link diagram", and a
  diagram is defined (Rem. 3.4.13, p. 112) as the image under a projection
  making the curves "immersed except for transverse double points". SM6's
  definition demands exactly that, plus no triple point.
- SM6's class is **non-empty and is what the frame produces**: the carrier-floor
  proof constructs an embedded transverse $K_T$ "whose front and whose
  smaller-$y$ over/under assignments are exactly the diagram $T$"
  (sm-3:4518–4520). No quantifier gap.

Geiges's own hypothesis "positively transverse" is not needed for the identity
(his statement says "transverse knot"); SM6's positivity is a strengthening,
harmless.

**tb.** Geiges Prop. 3.5.9 needs $K$ Legendrian in $(\RR^3,\xi_{st})$ and
homologically trivial for $\mathtt{tb}$ to be defined (Def. 3.5.4, p. 115) —
automatic in $\RR^3$. Etnyre eq. (7) is stated under the same standing
assumption ("null homologous", §2.6.1, p. 13). SM6 uses it for "an oriented
Legendrian front". No gap.

**The pushoff relation.** Etnyre Lemma 2.22 is stated for a Legendrian knot $L$
with a Seifert surface (used in the proof: $\tau$ extends over $\Sigma$);
$\RR^3$ supplies one. No gap.

## 3. Convention transport — checked, not assumed

Geiges (**both** texts) works in $\ker(dz+x\,dy)$, SM6 in $\ker(dz-y\,dx)$.
SM6's transport is printed at sm-3:2373–2375 and in registry L-3. Re-derived
here in full:

$$\Phi(x,y,z)=(X,Y,Z)=(-y,\;x,\;z)\tag{1}$$

$$\Phi^{*}(dZ+X\,dY)=dz+(-y)\,dx=dz-y\,dx\tag{2}$$

$$\det\Phi=\det\begin{pmatrix}0&-1&0\\1&0&0\\0&0&1\end{pmatrix}=+1\tag{3}$$

$$\partial_X=\frac{\partial y}{\partial X}\,\partial_y=-\partial_y\tag{4}$$

Consequences checked against the source pages:

- **The front page is unchanged.** Geiges's front projection is
  $\gamma_F=(y(s),z(s))$ in *his* letters (Def. 3.2.2, book p. 96, read), i.e.
  $(Y,Z)=(x,z)$ here — SM6's own $xz$ page, with the same orientation. Crossing
  signs are computed from the two oriented projected tangents in that oriented
  plane, so **the writhes agree**.
- **Over/under.** Geiges's Legendrian condition $Z'+X\,Y'=0$ gives
  $X=-dZ/dY$; SM6's $z'=yx'$ gives $y=dz/dx$. So "larger $X$" $=$ "smaller
  slope" $=$ "smaller $y$" — the registry's sentence, re-derived. **Caveat
  recorded honestly:** neither Geiges nor Etnyre *prints* the over/under rule of
  the front page in words at any locator SM6 cites; both convey it by figure
  (Etnyre Figs. 16–17, p. 14; Geiges Fig. 3.5, p. 100). SM6's proof sentence
  "The source observer is on the negative-$y$ side looking in the positive $y$
  direction, so smaller $y$ is over" (sm-3:3430–3431) is therefore a
  figure-level convention read, not a quoted source sentence. It is consistent
  with both sources and with SM6's own `def:transverse-front`, and the frame
  proves the sign identification it needs from it. Recorded, not filed as a
  defect: no locator is misquoted.
- **The section.** Geiges's survey pushes along $\partial_x$ (his letters) =
  $\partial_X$ = $-\partial_y$ here; SM6 pushes along $+\partial_y$. The two
  choices give the same number **because of the very independence SM6 cites for
  it** (survey p. 45; book Rem. 3.5.29(2)). This is the whole reason
  `rem:sl-convention` needs the Geiges citation, and it is correctly placed.

## 4. T1 verdict

**T1 is reached at all eleven cited locators.** One locator (Etnyre eq. (9))
is T1-with-defects, and SM6 describes it that way itself, both in the block
("states it") and in registry L-3 (the misprint and the deferral are named in
the entry). No locator is wrong, no page is off, no statement is misquoted.
