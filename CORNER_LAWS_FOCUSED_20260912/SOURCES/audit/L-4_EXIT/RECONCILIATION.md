# L-4 EXIT — RECONCILIATION: every L-4 row against SM6's bytes

Verdict vocabulary, per the charter: **addressed** (the row's defect is gone at
the exit frame's bytes, and the byte is quoted), **open** (still there),
**lapsed** (the row's premise no longer exists on this route, so the row has
nothing left to be about). Stamp 2026-09-06T01:56:55Z; frame SM6 verified
20/20 first.

A verdict here is **this seat's claim about the L-4 entry's bytes**. Nothing
below referees a printed proof; where a row's closure depends on a proof
referee, that is said.

---

## 1. The curator's ledger rows named in this seat's charge

| row | what it said | SM6 byte | verdict |
|---|---|---|---|
| **F-25-51** | as SM1 registered it, L-4 was **below T2**: no cited source stated what `thm:floor` used (Ng bounds $\overline{sl}$, the SM applied it to one constructed $T$); "Ng Thm. 1" was the wrong locator; $T$ unquantified; "audited at the root, Phase 1.99" overstated. Repairs R1–R5. | `sm-11`:255–316. The seam is gone **structurally**, not by citation: `ng:local-front-bound` (`sm-3`:2304) is per-front — *"We will prove $B(F)\ge0$ for each front, not a statement about a maximum over representatives"* (:1898–1899) — and `fd:ng-bound` (:3386–3388) repeats *"nor a maximum over front representatives"*. Locator corrected to Ng pp. 6–8 + Fig. 1 (:257) and, for the background role, §1.1 + Cor. 1 p. 8 (:292–295). The bounded object is named: *"The transverse knot bounded is the individual $T$ constructed in Theorem `cf:thm-carrierfloor`(C)"* (:288–290). The provenance parenthetical is withdrawn in terms (:300–304). | **addressed**, R1–R5 all satisfied or superseded — with **one residual inside R1's own repair**: the published statement of record named for the bridge is mis-sub-located (finding **X-1**, `T1_STATEMENT.md` §4.2). |
| **F-25-52** | "T3 available: RC ng:local-front-bound" was overstated: the engine `ng:finite-word` is itself a `sourcefact`, and RC's theorem is about a different front class, so replacing L-4 by it means re-proving `thm:floor`'s geometric half. | The phrase **"T3 available" occurs nowhere in SM6** (grep over all `.tex`, `README.md`, `DAG.md`, `DISCREPANCIES.md`: four `T3` hits, all disclaimers — `CONSUMPTION_MAP.md` §5). The registry preamble states the rule (`sm-11`:10–13) and L-4 states the resting and the buying (:275–283). | **addressed** |
| **F-25-56** | the three "T3 available" labels (L-1, L-3, L-4) each rested on a declared `sourcefact` and met no T3; R-25-13 ordered the rewording. | For L-4: `sm-11`:275–283 — *"**What the internal derivation buys** (R-25-13; seat R7): Theorem `ng:local-front-bound`, **resting on the source fact** Literature input `ng:finite-word`, is a per-front polynomial inequality; it removes the maximization over Legendrian representatives and every ambient-invariance premise, and narrows the literature dependence of this entry to the finite Ng–Rutherford word procedure together with the L-1 polynomial interface; **it does not remove Ng and Rutherford from the trusted base**."* | **addressed for L-4** (the L-1 and L-3 halves belong to those seats) |
| **F-25-83** | `ng:finite-word` was wider than either printed source sentence in three ways and did not say so; registry L-4 lacked R-25-13's "what it buys"; "author pp. 1–8" should be pp. 6–8 + Fig. 1. | The width disclosure is printed **inside the block**, `sm-3`:2196–2205, and repeated at `sm-11`:269–274. Each of the three clauses **re-verified at the sources by this seat** (`CONSUMPTION_MAP.md` §1): Ng p. 6 gives one step; Rutherford's two "(ii)" terminals are p. 11 C1S5-both-empty and p. 12 C2S3; the arm-extension finiteness is asserted at Rutherford p. 10. Locator is pp. 6–8 + Fig. 1 in both places. "What it buys" present. | **addressed** |
| **F-25-107** | the front bound entered `fd:contact`'s proof from a display labelled outside any environment, so `ng:local-front-bound` and `ng:finite-word` lay **outside** `thm:floor`'s closure — a load-bearing input invisible to the ordering instrument. | `fd:ng-bound` is a lemma (`sm-3`:3377) owning display `fd:ng-input`; `fd:contact`'s proof cites it **by label** at :3469–3470 (*"Lemma `fd:ng-bound`, applied to $F_T$"*). The ruler's leaf table (`DAG.md`) carries the row `ng:local-front-bound | ng:finite-word`, and `DAG.md`:292 records the chain `fd:contact → fd:ng-bound → ng:local-front-bound → ng:finite-word`. | **addressed** — with a **stale count** in the same sentence of the entry (finding **X-2**, §3 below) |
| **F-25-137** | `fd:ng-bound`'s exported display used $\max\deg_a$, whose only definition was prose inside no environment (`sm.tex` declares a typographic `\mindeg` only); all seven occurrences were uses. Repair: a definition environment before the first use. | `def:adeg` exists, `sm-3`:1887–1892, printed as **Definition 3.35 "degrees in $a$"** on PDF p. 72, before every use of $\deg_a$/$\max\deg_a$ in the frame (first use is inside the definition itself; the next is `ng:defect` at :1896). | **addressed for $\max\deg_a$**, **open in two residues** (finding **X-4**, §3 below): a second, undefined spelling `\min\deg_a` at six sites, and a $z$-degree use outside the definition's stated scope |
| **F-25-142** | `ng:deletions`' exportable statement was a $B$-statement only, while two consumers attributed an $s$-decrease to it; the only $s$ claim was proof-body prose for the crossed-cusp branch alone, uncited at the point of use. Codex's detail: zigzag $\Delta s=-2$, crossed-cusp $\Delta s=-1$. | Statement, `sm-3`:2009–2011: *"Deleting an empty zigzag **lowers $s$ by two** and cannot increase $B$; applying the crossed-cusp shortcut **lowers $s$ by one** and cannot increase $B$."* Proof carries the $s$ sentence at each display (:2023–2024 after `ng:zigzag-counts` (*"the two cusps are removed and no crossing is touched, so $s$ decreases by two"*); :2038–2039 after `ng:crossed-cusp-counts` (*"One crossing is removed and the cusp count is unchanged, so $s$ decreases by one"*)) and cites Ng at the point of use (*"this is the compressed dashed-arrow case of Ng's Figure 1 `\cite{Ng}`"*). Consumer 1, the table row at :2245 (*"Lower $s$ by Lemma `ng:deletions`"*), now reads against a statement that carries the claim; consumer 2, :2278–2281, reads *"Stabilized cusp cases use the direct shortcut of Lemma `ng:deletions` (display `ng:crossed-cusp-counts`; $\Delta s=-1$)"*. | **addressed**. One editorial slack, recorded not filed: the status tag says the $\Delta s$ values are *"printed at the two displays of the proof"*; they are printed in the sentence **adjacent to** each display, not inside it. |
| **F-25-153** | `fd:ng-bound`'s domain hypothesis for $F_T$ was never discharged: the proof cited the display, not the lemma — an obligation created in round 3 when the bare display became a lemma with a hypothesis. | `sm-3`:3460–3470, quoted in full in `CONSUMPTION_MAP.md` §3: *"**The front $F_T$ lies on the domain of Definition `ng:front-domain`:** Theorem `fd:generic-front` gives finitely many semicubical cusps with the germ `cp:exact-cusp`, whose $x''(0)=2A\neq0$, transverse double points, no triple point and no cusp on another branch, and Legendrianity $z'=yx'$ makes the front tangent vanish wherever $x'=0$ … **Lemma `fd:ng-bound`, applied to $F_T$**"*. Every clause of `ng:front-domain` is matched (six-row table in that file); the over/under convention is derived one paragraph earlier at :3427–3429. | **addressed** — the hypothesis is discharged **from statements `fd:generic-front` actually makes**. (Whether `fd:generic-front`'s own proof establishes them is a referee question; `fd:generic-front` is a held transcription and this seat does not clear it.) |

---

## 2. Escalations

| row | verdict on SM6 | evidence |
|---|---|---|
| **E-25-2** — Franks–Williams, Trans. AMS 303 (1987) 97–108 | **open, restated by name, not blocking.** Still not on disk (folder-wide sweep this pass). Routes tried this pass: AMS PDF → **HTTP 403**; open-access search → citing papers only. **Not a verdict on the source.** L-4 does not depend on it: SM6 cites `FranksWilliams` twice, both in `sm-11-registry.tex`, in **no proof**, and Morton p. 109 gives *"[2] J. FRANKS and R. F. WILLIAMS. Braids and the Jones polynomial. (Preprint 1985)"* with his Corollary 1 attributed to "[5], [2]" — so the registry's role clause is checkable without the source itself. | `ACCESS_AUDIT.md` §2 |
| **E-25-5** — Rutherford IMRN 2006, Art. ID 78591 (Lemma 3.3) | **open, low priority, not blocking — and now known to have no cheap route.** OUP article page returns abstract + references only; **`arxiv.org/abs/math/0511097` has exactly one version, v1**, so the published numbering and wording exist nowhere the campaign can reach without the operator. This is what the four typed index corrections (`sm-3`:2283–2291) would be checked against. | `ACCESS_AUDIT.md` §2; `T2_DELTA.md` §3 |
| **E-25-1, E-25-3, E-25-4, E-25-6** | **not this entry's.** E-25-1 (Roseman) is L-2's, E-25-4 (Kneser) is L-2's, E-25-6 (Reidemeister at proof depth) is L-1's. Recorded here only so the curator does not read L-4's silence as a claim about them. | — |

---

## 3. New on the exit frame — findings this seat files against L-4's bytes

| id | anchor (SM6 byte) | finding | severity |
|---|---|---|---|
| **X-1** | `sm-11-registry.tex`:283–287 (registry L-4) **and** :876–878 (the §11 rule-8 flagged list) | The bridge statement *"every transverse knot is transversely isotopic to the positive transverse pushoff of a Legendrian knot"* is attributed to `\cite[Section~2.9, **Lemma~2.22, equation~(17)**]{Etnyre}`, and the rule-8 cross-check of `fd:transverse-neighborhood` is flagged *"against Etnyre's Lemma 2.22"*. At Etnyre's bytes, **Lemma 2.22 / eq. (17) is $sl(T_\pm(L))=tb(L)\mp r(L)$** — the invariant relation, not the bridge. The bridge is at Etnyre **§2.9, p. 20**: *"By considering the obvious annulus between $T$ and $T_l$ it is easy to see that the positive transverse push off of $T_l$ is $T$"*, restated after Thm 2.23 as *"Since we know all transverse knots are the transverse push off of some Legendrian knot …"*. Nothing mathematical turns on it (SM6 constructs the bridge and consumes Etnyre in no proof for it), but **a rule-8 cross-check aimed at the wrong sentence cannot be performed as written**. Origin: the L-4 seat's R1 paired the bridge with Lemma 2.22 for the *sign*; the pair was transcribed as one locator. | editorial (locator), **two sites** |
| **X-2** | `sm-11-registry.tex`:307–310 | *"the ordering instrument's closure of Theorem `thm:floor` now contains … (**33 statements**; declared inputs …)"*. The frame's own `DAG.md`:5 reads *"closure of `thm:floor` **38** statements with the five literature inputs (SM5: 113 and 36 …)"*. Verified across frames: SM4 DAG 33 / registry 33 (**consistent**); SM5 DAG 36 / registry 33; **SM6 DAG 38 / registry 33**. The registry's number is the round-3 figure, unrefreshed through rounds 4 and 5. The declared-input list is correct. | editorial (stale count; frame self-inconsistency) |
| **X-3** | `sm-refs.bib` (`@article{Ng}`) | Every Ng locator in SM6 — `\cite[pp.~6--8 and Figure~1]{Ng}` at `sm-3`:2172 and `sm-11`:257, and the §1.1 / Cor. 1 / "proved on p. 8" locators at `sm-11`:292–295 — resolves on the retained **15-page author preprint, arXiv:0709.2141v1 (13 Sep 2007)**; the bib entry names the **IMRN 2008** printing (`note={article rnn116}`) with **no retained-version note**. The frame's three other preprint-based entries all carry one — `Etnyre` (added after **F-25-84**, this exact defect), `Rutherford`, `GeigesContact`. The arXiv stamp is in the retained file itself (this seat's diff of the two on-disk copies). | editorial (bibliography); same class as the repaired F-25-84 |
| **X-4** | `sm-3-statesum.tex`:1887–1892 (`def:adeg`) vs `sm-3`:4330, 4552, 4553, 4743, 4747 and `sm-4-knotlaws.tex`:682; also `sm-3`:4579 | F-25-137's repair defined **`\deg_a`, `\max\deg_a`, `\mindeg_a`** (`sm.tex`:47 declares the macro `\mindeg` = `\operatorname{mindeg}`; there is no `\maxdeg`). **Six** later sites write **`\min\deg_a`** instead — a fourth spelling the definition does not introduce. It is not cosmetic at the printed bytes: `sm.pdf` **p. 108** carries *"max deg$_a$ $P_D$ = −min deg$_a$ $P_D$ … min deg$_a$ $P_D$ = −max deg$_a$ $P_D$"* and, two lines below, *"mindeg$_a$ $H^+_Q$"* — two renderings of one functional on one page (`\mindeg` prints "mindeg", `\min\deg` prints "min deg"). Separately, `sm-3`:4579 uses **`\mindeg_z`**, a degree in $z$, while `def:adeg` is stated only *"For a nonzero Laurent polynomial $f$ **in $a$**"* — the symbol is used outside the definition's own scope. | convention (notation); the F-25-112 / F-25-137 class |
| **O-3** *(observation, offered rather than filed)* | `sm-11-registry.tex`:262–266 | *"the theorem and the front lemmas cleared by bench A, Lemma `ng:deletions` held"*. On SM6 the six front lemmas do carry `proved (refereed: bench A, 2026-09-05T15:51:04Z)`, and `ng:deletions` is held. But **`ng:local-front-bound` itself reverted to `transcribed (unrefereed)`** after the round-5 touch (its own tag records both clearances and the touch; `DAG.md`'s tag census lists it among the reverted). The registry preamble does say referee status is reported "on frame SM2", so the sentence is defensible as written; a reader of the exit frame nonetheless gets "cleared" with no sign of the reversion. Also unmentioned by the entry: the round-5 lemma `ng:smoothing-record`, now inside the L-4 chain and licensing the symbol $P_{S(F)}$ that `fd:ng-bound` exports. | convention (status summary) |

---

## 4. The predecessor seats' own findings, closed out

| row | verdict on SM6 | byte |
|---|---|---|
| F-L4-1 (locator "Ng Thm. 1" carries no polynomial) | **addressed** | `sm-11`:257, :292–295 |
| F-L4-2 ($\overline{sl}$ vs $sl(T)$) | **lapsed** — SM6 consumes neither Thm 1 nor Cor 1; the bound is per-front | `sm-3`:1898–1899, :3386–3388 |
| F-L4-3 (Morton is a diagram theorem; source roles) | **addressed** — roles split explicitly | `sm-11`:292–300 |
| F-L4-4 ($T$ unquantified) | **addressed** | `sm-11`:288–290; `sm-3`:3409–3413 |
| F-L4-5 ("audited at the root, Phase 1.99" overstates) | **addressed** — withdrawn in terms | `sm-11`:300–304 |
| F-L4-6 ("T3 available") | **addressed** | `CONSUMPTION_MAP.md` §5 |
| F-L4-7 (Franks–Williams unfetchable) | **open**, = E-25-2 | `ACCESS_AUDIT.md` §2 |
| F-L4-8 (Rutherford's malformed indices) | **disclosed and re-verified**; the residual is E-25-5 | `sm-3`:2283–2291; `T2_DELTA.md` §3 |
| SM2 seat R6 (scope the import) | **taken in round 3, inside the block** | `sm-3`:2196–2205 |
| SM2 seat R7 (what it buys) | **taken** | `sm-11`:275–283 |
| SM2 seat R8 (locator "author pp. 1–8" → pp. 6–8 + Fig. 1) | **taken in both places** | `sm-3`:2172; `sm-11`:257 |
| F-25-85 (the SM2 seat's five source-claim verifications, positive) | not re-checked here — those are L-3-side claims about Geiges/DeTurck–Gluck; the registry's citation of it at `sm-11`:266–269 concerns the **Rutherford index disclosure**, which this seat **did** re-verify independently | `T2_DELTA.md` §3 |
| F-25-136 (citation ranges; `ng:cusp-skein` reached only through an equation label in its own proof) | **addressed on the L-4 chain**: `ng:local-front-bound`'s proof now cites `ng:commutation`, `ng:front-I`, `ng:front-II`, `ng:front-III` individually (`sm-3`:2331–2333) and `ng:cusp-skein` by label (:2339–2340); `ng:smoothing-record` was created for the symbol $P_{S(F)}$ and is cited at :2314–2316 and :3390–3392 | as cited |

---

## 5. Rows of the charter's list that are **not** this entry's

F-25-80, 81, 82, 84 (Etnyre/Geiges citation and domain items) → **L-3**.
F-25-108, 109, 159 (torus/Wenzl) → **L-5**. F-25-110 (`lit:homfly` locator) →
**L-1**. F-25-138, 139, 140, 141, 143, 149 (polygon/transport/Hecke locators) →
outside every registry entry. F-25-144 (registry L-3's locator) → **L-3**.
F-25-145 (registry L-5's sentence) → **L-5**. F-25-152, 154, 155 (`fd:contact`
wording, `fd:generic-front` symbols, `fd:linking-calculus` genericity) →
proof-side items on the contact chain; this seat checked only that F-25-152's
restored sentence is present at `sm-3`:3439–3441 (*"Absence of downward
tangencies alone is not a converse transverse-lift theorem"*) because it sits
three lines from the L-4 hop. They are named here so the curator does not read
this lane's silence as a verdict.
