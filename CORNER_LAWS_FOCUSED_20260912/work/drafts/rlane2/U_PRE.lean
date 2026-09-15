import RProof.Cores
import CV.X1
import CV.ChamberInvII
import CV.SelectorA
import SM.CornerStateSum

/-! # R lane, part 2 — FINAL statements of the nine remaining obligation rows (judge's merge)

Judge's merge (2026-09-14) of the two panel designs `work/drafts/rlane2/Statements_A.lean` (TAG A,
spec-first) and `Statements_B.lean` (TAG B, consumer-first); the clause maps, readings, verdicts and
risks are in `NOTES_FINAL.md` next to this file. Checked with
`cd work/lean && lake env lean ../drafts/rlane2/Statements_FINAL.lean`: the only `sorry`s are the nine
row theorems; every auxiliary is a definition or PROVED.

Rows (blueprint/ORDER.md; fixed names, work/lean/axiom-policy.json `targets`):
`R:exterior → RProof.exterior`, `R:availability_0_1 → RProof.availability_zero_one`,
`R:generic_selector → RProof.generic_selector`, `R:generic_transport → RProof.generic_transport`,
`R:generic_selected → RProof.generic_selected`, `R:extreme_pair_zero → RProof.extreme_pair_zero`,
`R:extreme_transport → RProof.extreme_transport`, `R:extreme_selected → RProof.extreme_selected`,
`R:cv_theorem → RProof.cv_R` (of type `CV.hyp_R`, the fixed name of CV:ax:R, DECISION_FINAL.md R6).

Sources (frozen): R_ASSEMBLY_SPEC.md (displays (1)–(4), the availability paragraph, the assembly
paragraph); OPEN_WORK.md items 2–4; reference/R/RA/R_ATTACHMENT_WARRANTS.md ("R-EXTERIOR-1 — the
triangle-disjoint factor", Statement); R_GENERIC_NONSELECTED_SELECTOR_PROOF.md (Statement, "Which pair
is selected", "The mixed carrier"); R_GENERIC_COMMON_TRANSPORT_PROOF.md ("Statement and canonical
branch", (1)–(2)); R_GENERIC_SELECTED_COUPLE_PROOF.md (Statement, (GSC)); R_EXTREME_PAIR_ZERO_PROOF.md
(Statement, proof paragraphs 2–3); R_EXTREME_SINGLETON_TRANSPORT_PROOF.md ("Statement and canonical
data", (1)–(3)); R_EXTREME_SELECTED_COUPLE_PROOF.md (Statement, (1a), (2)); CV d1_setup.tex:908–930
(def:X1), d10_axioms.tex:18–24 (ax:R). Each bundle field quotes the clause it renders.

## Foundation consumed (all accepted or implemented)

* The four X₁-free cores `RProof.localization / parity / fibre_partition / generic_table`
  (work/lean/RProof/Cores.lean, accepted): the CV event locus `E : CV.Event n`,
  `E.IsSimpleRIII e f g h3 h4e h4f h4g`, the punctured radius `Punctured E δ t`, the sides
  `OppositeSides E t t'`, the triangle `triangleCrossings`, `xPair`, `visitOn`, `avail`,
  `outsideSupports`, `localFibre`, `fibreSum`, the sign data `strandSign`, `concurrenceSign`,
  `IsAlternating`, `SelectedAB/AC/BC`, the local edges `EdgeAB/AC/BC`, `ExtremeLocal`.
* CV:def:X1 (work/lean/CV/X1.lean, accepted): `CV.X1 hn P hG`, `CV.Omega1 hn hG hS q`, `CV.carrierR`,
  `CV.groupedPoly`, `CV.groupedWrithe`, `CV.slot`; CV:def:wind (CV/Carriers.lean): `CV.weight`,
  `CV.wind`, `CV.CarrierUniform`, `CV.CarrierMixed`; CV:def:pieces: `CV.U`, `CV.Piece`, `CV.pieceOf`,
  `CV.pieceLabels`, `CV.piecesOn`; the carriers `SM.GeoCarrier.GeoComponent`, `geoOwner`
  (def:flat-carriers).
* The total summand `CV.X1Summand hn hG S` (CV/ChamberInvII.lean): `wind(S) ∏_L Ω₁(S,L)` when
  `S ∈ Ind(G_P)` and `0` otherwise — literally the RA texts' "complete X₁ term of `Q ∪ J` on side
  `ν`, with an absent row read as zero" (`T_ν(J)`); `CV.X1_eq_sum_X1Summand`.
* Transport across the wall: `SM.crossingTransport hs` (support-preserving, `rfl`) and
  `SM.transportSupport hs Q = Q.map (crossingTransport hs).toEmbedding` (def:flat-carriers), the
  form of the accepted `FibrePartitionData.avail_same`.
* `Bridge.B1/B3`, `RProof.isSimpleRIII_eventOfTriple` and `SM.cornerStateSum` (the consumer chain of
  `Bridge.sm_R`, checked by `smR_shape_of_hyp_R` below).

## Notation map (RA text → Lean)

| RA text | Lean |
|---|---|
| `T_ν(J)`, "the complete X1 term of `Q ∪ J` on side `ν`, absent rows being zero" | `rowTerm hn (genericAt E t ht.1) (Q ∪ J)` (= `CV.X1Summand`) |
| `F_±(S)` "the complete summand of CV def:X1 at `S`" | `rowTerm hn (genericAt E t ht.1) S` |
| `Φ_±(Q)` | `fibreTerm hn E e f g t ht.1 Q` (= `fibreSum … (rowTerm …) Q`) |
| `X_1(P_±)` | `CV.X1 hn (E.curve t) (genericAt E t ht.1)` |
| "full-availability fiber", "full availability" | `FullAvail (geomAt E t ht.1) e f g Q` (`avail … Q = triangleCrossings …`) |
| "the side where `Q ∪ J` is present" / "absent" | `Q ∪ J ∈ CV.Ind …` / `∉` |
| `Q`, `S = Q ∪ A`, `S` read on the other side | `Q ∈ outsideSupports …`, `Q ∪ A`, `transportSupport hs (Q ∪ A)` |
| "a carrier `L` of `S`", `wt(L)`, `Ω₁(S,L)`, `R(L)`, `P_{S,L}`, `w_{S,L}` | `q : GeoComponent hP S`, `CV.weight hP S q`, `CV.Omega1 hn hG hS q`, `CV.carrierR hn hG hS q`, `CV.groupedPoly`, `CV.groupedWrithe` |
| "triangle-disjoint carrier" | `TriangleDisjoint hP S e f g q` |
| `C_{Q,σ}(A)`, `ρ_σ(A)`, `τ_σ(A)` | `exteriorFactor hn hG hS e f g`, `touchingFactor …`, `rowTerm hn hG (Q ∪ A)` |
| `K3` side / empty-graph side (`H` / `L`) | `CompleteLocal hP hef heg hfg` / `EmptyLocal hP hef heg hfg` |
| two-edge side `P` (edges `ab, bc`, centre `b`) / one-edge side `E` | `EdgeAB ∧ EdgeBC` / `EdgeAC ∧ ¬EdgeAB ∧ ¬EdgeBC` |
| `a = x_ef = x`, `b = x_eg = y`, `c = x_fg = z`; `u1, u2, u3 = e, f, g` | `xPair hef`, `xPair heg`, `xPair hfg` |
| "one carrier contains the entire arc and both of its endpoint smoothing corners" | `MixedSharedStrandCarrier` |
| "carrier/record, selector, rotation and coefficient transport" | `SummandTransport` |
| CV ax:R, "sides" = point values at every `tp > 0`, `tm < 0` (R6) | `CV.hyp_R` |
| "on a punctured neighbourhood" form of ax:R (`cv_R_near`, R6) | `CvRNear` (bundle `CvTheoremData`) |
| CV:prop:chamberinv (ii) "`X₁` is constant on each chamber" | `ChamberInvII` |

## Fixed labels

The RA files relabel the strands so that the printed words hold; here the labels are the fixed ones
of the accepted `generic_table`: `a = x_ef`, `b = x_eg`, `c = x_fg`, strands `u1 = e`, `u2 = f`,
`u3 = g`, signs `s_a = strandSign e f`, `s_b = strandSign e g`, `s_c = strandSign f g`. Where a text
states its result in relabelled canonical words ("every generic branch can be put in this form by
relabelling"), the bundle carries the canonical-branch clause (the selected pair `ac`, `s_a = s_b =
s_c`) AND the two relabelled instances (selected pair `ab`, `bc`), so that every branch of the event
is covered without narrowing (decision F2(A)). Sides are never named `P₊/P₋`: an identity symmetric
in the sides is stated for `t, t'` opposite; a side the text names by its graph (`H`/`K3`, `L`/empty,
`P` two-edge, `E` one-edge) is identified by the local-edge predicates.

`hn : 3 ≤ n` is an explicit parameter of every X₁-dependent row (needed by `CV.X1`; CV fixes `n ≥ 3`
globally, d1_setup.tex:932; R6 quantifies it in `CV.hyp_R`); `three_le_of_h3` shows it is derivable
from `h3`, so consumers holding only the accepted cores' data can supply it. -/

namespace CV

open SM

/-- **CV:ax:R (`CV.hyp_R`)**, the printed statement (d10_axioms.tex:18–24) in the shape fixed by the
CV-DOM decision (work/drafts/cvdom/DECISION_FINAL.md R6): "`X_1(P_+) = X_1(P_-)` across every simple
Reidemeister III event, i.e. every event whose zero set is the forced bundle `Z = {G3_{e,f,g},
G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}` for three pairwise remote edges with `1 ≤ e < f < g ≤ n`,
concurrent at `t = 0` at a point interior to all three, the event being transversal in the sense of
Definition def:event." The sides are the two chambers of the event (def:event d1:1080–1083), rendered
as `X₁` at every positive and every negative parameter (equal to the chamber values by
prop:chamberinv (ii)). This is the declaration of the row CV:ax:R (fixed name); it is stated here
because the R lane's final theorem `RProof.cv_R` has this type, and is to be placed once (CV row
module or here) by the assembler. -/
def hyp_R : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ rep e < rep f ∧ rep f < rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ rep f < rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ rep e < rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ rep e < rep f),
    E.IsSimpleRIII e f g h3 h4e h4f h4g →
    ∀ (tp tm : E.Parameter) (hp : 0 < tp.val) (hm : tm.val < 0),
      X1 hn (E.curve tp) (E.generic_punctured tp hp.ne') =
        X1 hn (E.curve tm) (E.generic_punctured tm hm.ne)

end CV

namespace RProof

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n]

/-! ## Part 0 — preliminaries shared by the nine rows -/

/-- CV fixes `n ≥ 3` (def:polygon); it follows from the sorted representatives of the bundle
(`1 ≤ rep e < rep f < rep g ≤ n`), so a consumer holding only the accepted cores' data can supply
the `hn` of the X₁-dependent rows. PROVED. -/
theorem three_le_of_h3 {e f g : ZMod n}
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g) :
    3 ≤ n := by
  have h1 := CV.rep_pos e
  have h2 := CV.rep_le g
  omega

section RowTerm

variable {P : LabelledTuple n}

/-- "`T_ν(J)` … the complete X1 term of `Q ∪ J` on side `ν`, absent rows being zero"
(R_GENERIC_SELECTED_COUPLE_PROOF.md Statement, R_EXTREME_*_PROOF.md), "`F_±(S)` … the **complete**
summand of CV def:X1 at `S` on that side, including the selector and every carrier coefficient with
the printed empty conventions" (R_ASSEMBLY_SPEC.md): the total summand `CV.X1Summand` of def:X1,
`wind(S) ∏_L Ω₁(S,L)` for `S ∈ Ind(G_P)` and `0` for an absent support. -/
noncomputable abbrev rowTerm (hn : 3 ≤ n) (hG : CV.Generic P) (S : Finset (Crossing P)) : ℤ :=
  CV.X1Summand hn hG S

/-- A present row is `wind(S) ∏_L Ω₁(S,L)` (def:X1). -/
theorem rowTerm_of_mem_Ind (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) :
    rowTerm hn hG S =
      CV.wind hG.crossingGeometry S * ∏ q : GeoComponent hG.crossingGeometry S, CV.Omega1 hn hG hS q := by
  unfold rowTerm CV.X1Summand
  rw [dite_eq_left hS]

/-- "absent rows being zero". -/
theorem rowTerm_of_not_mem_Ind (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∉ CV.Ind hG.crossingGeometry) : rowTerm hn hG S = 0 := by
  unfold rowTerm CV.X1Summand
  rw [dite_eq_right hS]

/-- def:X1's state sum is the sum of the row terms over `Ind(G_P)` (`CV.X1_eq_sum_X1Summand`). -/
theorem X1_eq_sum_rowTerm (hn : 3 ≤ n) (hG : CV.Generic P) :
    CV.X1 hn P hG = ∑ S ∈ CV.Ind hG.crossingGeometry, rowTerm hn hG S :=
  CV.X1_eq_sum_X1Summand hn hG

/-- "Full availability means that the availability set defined in R-PAR-v6 equals the three-element
local crossing set `T`" (R_ATTACHMENT_WARRANTS.md, preamble): `𝓐(Q) = T`. -/
def FullAvail (hP : CrossingGeometry P) (e f g : ZMod n) (Q : Finset (Crossing P)) : Prop :=
  avail hP e f g Q = triangleCrossings P e f g

/-- The `K3` side of the extreme orbit ("`H` … local graph `K3`"): all three local edges present. -/
def CompleteLocal (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) : Prop :=
  EdgeAB hP hef heg ∧ EdgeAC hP hef hfg ∧ EdgeBC hP heg hfg

/-- The empty-graph side of the extreme orbit ("`L` … local graph empty"). -/
def EmptyLocal (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) : Prop :=
  ¬ EdgeAB hP hef heg ∧ ¬ EdgeAC hP hef hfg ∧ ¬ EdgeBC hP heg hfg

omit [NeZero n] in
/-- The accepted `ExtremeLocal` is exactly "`K3` or empty". -/
theorem extremeLocal_iff (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    ExtremeLocal hP hef heg hfg ↔ CompleteLocal hP hef heg hfg ∨ EmptyLocal hP hef heg hfg :=
  Iff.rfl

/-- An outside independent support is independent (`Ind(G[W]) ⊆ Ind(G_P)`). -/
theorem mem_Ind_of_mem_outsideSupports {hP : CrossingGeometry P} {e f g : ZMod n}
    {Q : Finset (Crossing P)} (hQ : Q ∈ outsideSupports hP e f g) : Q ∈ CV.Ind hP :=
  ((F1.mem_outsideSupports hP e f g Q).mp hQ).1

end RowTerm

/-- "`Φ_±(Q) = Σ_{J ∈ Ind(G_±[𝓐(Q)])} F_±(Q ∪ J)`" (R_ASSEMBLY_SPEC.md (2)) with `F_±` the complete
summand: the accepted row-171 `fibreSum` at `rowTerm`. -/
noncomputable abbrev fibreTerm (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (t : E.Parameter)
    (ht : t.val ≠ 0) (Q : Finset (Crossing (E.curve t))) : ℤ :=
  fibreSum (geomAt E t ht) e f g (rowTerm hn (genericAt E t ht)) Q

/-- The support transport `transportSupport hs` as an embedding of supports (for `Finset.map`
reindexing of `Ind(G[W])` and of the local fibres across the wall). -/
abbrev supportEmb {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) :
    Finset (Crossing P) ↪ Finset (Crossing Q) :=
  (Finset.mapEmbedding (crossingTransport hs).toEmbedding).toEmbedding

omit [NeZero n] in
@[simp] theorem supportEmb_apply {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) : supportEmb hs S = transportSupport hs S :=
  Finset.mapEmbedding_apply

/-! ### The X₁ specialisation of R_ASSEMBLY_SPEC.md (3) (the "X₁ flag" of NOTES_FINAL.md §3, now closed)

"The finite bijection just established partitions the exact state sum, so
`X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)` (3)": `FibrePartitionData.state_sum_partition` at the summand
`F := F_±` = `rowTerm`, with def:X1 unfolded by `X1_eq_sum_rowTerm`. PROVED. -/
theorem X1_eq_sum_fibreTerm {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hF : FibrePartitionData E e f g δ) (hn : 3 ≤ n) (t : E.Parameter) (ht : Punctured E δ t) :
    CV.X1 hn (E.curve t) (genericAt E t ht.1) =
      ∑ Q ∈ outsideSupports (geomAt E t ht.1) e f g, fibreTerm hn E e f g t ht.1 Q := by
  rw [X1_eq_sum_rowTerm]
  exact hF.state_sum_partition t ht (rowTerm hn (genericAt E t ht.1))

/-! ## Unit PRE — helper lemmas for the X₁-free presupposition clauses (proof lane, 2026-09-14)

Shared by the field lemmas `PRE_<row>_<field>` placed before the row theorems of rows 170, 173,
175, 176, 177 below. Nothing in the fixed statements is changed. Inputs: `CV.mem_Ind_iff`,
`CV.mem_U_iff`, the accepted `F1.compose_geom` / `F1.mem_avail` / `F1.mem_localFibre` and the
`P1` triangle lemmas of work/lean/RProof/Cores.lean. -/

section PREHelpers

variable {P : LabelledTuple n}

/-- Independence is hereditary: a subset of an independent support is independent
(CV:def:interlace, `CV.mem_Ind_iff`). -/
theorem PRE_mem_Ind_of_subset {hP : CrossingGeometry P} {S J : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hP) (hJ : J ⊆ S) : J ∈ CV.Ind hP := by
  rw [CV.mem_Ind_iff] at hS ⊢
  exact fun x hx y hy hxy => hS x (hJ hx) y (hJ hy) hxy

/-- A support with at most one element is independent (no two distinct members). -/
theorem PRE_mem_Ind_of_card_le_one (hP : CrossingGeometry P) {J : Finset (Crossing P)}
    (hJ : J.card ≤ 1) : J ∈ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  intro x hx y hy hxy
  exact absurd (Finset.card_le_one.mp hJ x hx y hy) hxy

/-- Over an availability set with at most one element every subset is independent, so the local
fibre `Ind(G[𝓐(Q)])` is the whole power set of `𝓐(Q)`. -/
theorem PRE_localFibre_eq_powerset (hP : CrossingGeometry P) (e f g : ZMod n)
    (Q : Finset (Crossing P)) (h : (avail hP e f g Q).card ≤ 1) :
    localFibre hP e f g Q = (avail hP e f g Q).powerset := by
  ext J
  rw [F1.mem_localFibre, Finset.mem_powerset]
  exact ⟨fun h' => h'.2, fun hJ =>
    ⟨PRE_mem_Ind_of_card_le_one hP ((Finset.card_le_card hJ).trans h), hJ⟩⟩

/-- The sign case analysis behind R_GENERIC_COMMON_TRANSPORT_PROOF.md (1): for nonzero,
nonalternating signs, "`s_a = s_c`" (pair `ac` selected) holds iff all three signs agree
("If the `b` sign were opposite, the triple would be one of the two alternating triples"). -/
theorem PRE_selectedAC_iff_all_eq : ∀ sa sb sc : SignType, sa ≠ 0 → sb ≠ 0 → sc ≠ 0 →
    ¬ IsAlternating sa sb sc → (SelectedAC sa sc ↔ (sa = sb ∧ sb = sc)) := by
  decide

/-- In the `K3` local graph any two distinct triangle crossings interlace. -/
theorem PRE_interlaces_of_complete {hP : CrossingGeometry P} {e f g : ZMod n}
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hK : CompleteLocal hP hef heg hfg) {x y : Crossing P}
    (hx : x ∈ triangleCrossings P e f g) (hy : y ∈ triangleCrossings P e f g) (hxy : x ≠ y) :
    GeometricInterlaces hP x y := by
  obtain ⟨hAB, hAC, hBC⟩ := hK
  rcases (P1.mem_triangleCrossings_iff hef heg hfg x).mp hx with rfl | rfl | rfl <;>
    rcases (P1.mem_triangleCrossings_iff hef heg hfg y).mp hy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact hAB
  · exact hAC
  · exact geometricInterlaces_symm hP hAB
  · exact absurd rfl hxy
  · exact hBC
  · exact geometricInterlaces_symm hP hAC
  · exact geometricInterlaces_symm hP hBC
  · exact absurd rfl hxy

/-- In the empty local graph no two triangle crossings interlace. -/
theorem PRE_not_interlaces_of_empty {hP : CrossingGeometry P} {e f g : ZMod n}
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hL : EmptyLocal hP hef heg hfg) {x y : Crossing P}
    (hx : x ∈ triangleCrossings P e f g) (hy : y ∈ triangleCrossings P e f g) :
    ¬ GeometricInterlaces hP x y := by
  obtain ⟨hAB, hAC, hBC⟩ := hL
  rcases (P1.mem_triangleCrossings_iff hef heg hfg x).mp hx with rfl | rfl | rfl <;>
    rcases (P1.mem_triangleCrossings_iff hef heg hfg y).mp hy with rfl | rfl | rfl
  · exact geometricInterlaces_irrefl hP _
  · exact hAB
  · exact hAC
  · exact fun h => hAB (geometricInterlaces_symm hP h)
  · exact geometricInterlaces_irrefl hP _
  · exact hBC
  · exact fun h => hAC (geometricInterlaces_symm hP h)
  · exact fun h => hBC (geometricInterlaces_symm hP h)
  · exact geometricInterlaces_irrefl hP _

/-- "`J` is independent because the local graph is empty" (R_EXTREME_PAIR_ZERO_PROOF.md:22–23):
every subset of the triangle is independent on the empty-graph side. -/
theorem PRE_mem_Ind_of_empty {hP : CrossingGeometry P} {e f g : ZMod n}
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hL : EmptyLocal hP hef heg hfg) {J : Finset (Crossing P)}
    (hJ : J ⊆ triangleCrossings P e f g) : J ∈ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  exact fun x hx y hy _ => PRE_not_interlaces_of_empty hL (hJ hx) (hJ hy)

/-- "full availability says every member of `T` is nonadjacent to every member of `Q`": under
`𝓐(Q) = T` every local support `J ⊆ T` lies in `𝓐(Q)`, so `Q ∪ J` is independent as soon as `J`
is (the accepted `F1.compose_geom`). -/
theorem PRE_union_mem_Ind_of_fullAvail {hP : CrossingGeometry P} {e f g : ZMod n}
    {Q : Finset (Crossing P)} (hQ : Q ∈ outsideSupports hP e f g) (hfull : FullAvail hP e f g Q)
    {J : Finset (Crossing P)} (hJT : J ⊆ triangleCrossings P e f g) (hJ : J ∈ CV.Ind hP) :
    Q ∪ J ∈ CV.Ind hP := by
  have hfull' : avail hP e f g Q = triangleCrossings P e f g := hfull
  exact F1.compose_geom hP e f g Q J hQ hJ (by rw [hfull']; exact hJT)

/-- The triangle crossing outside a two-element local support `J ⊆ T` is unique: any triangle
crossing other than the "remaining crossing `z`" belongs to `J` (`|T| = 3`). -/
theorem PRE_mem_of_third {e f g : ZMod n} (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) {J : Finset (Crossing P)} (hJT : J ⊆ triangleCrossings P e f g)
    (hJ2 : J.card = 2) {z : Crossing P} (hz : z ∈ triangleCrossings P e f g) (hzJ : z ∉ J)
    {c : Crossing P} (hc : c ∈ triangleCrossings P e f g) (hcz : c ≠ z) : c ∈ J := by
  have hsub : insert z J ⊆ triangleCrossings P e f g := Finset.insert_subset hz hJT
  have hcard : (triangleCrossings P e f g).card ≤ (insert z J).card := by
    rw [Finset.card_insert_of_notMem hzJ, hJ2, P1.triangleCrossings_card hef heg hfg]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← heq, Finset.mem_insert] at hc
  exact hc.resolve_left hcz

/-- "The remaining crossing `z` is undominated by `S`: it is nonadjacent to `x, y` because the local
graph is empty, and nonadjacent to `Q` by full availability. Thus `z` belongs to the residual graph
of `S`" (R_EXTREME_PAIR_ZERO_PROOF.md:26–28): `z ∈ U(Q ∪ J)`. -/
theorem PRE_third_mem_U {hP : CrossingGeometry P} {e f g : ZMod n}
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hL : EmptyLocal hP hef heg hfg) {Q : Finset (Crossing P)}
    (hQ : Q ∈ outsideSupports hP e f g) (hfull : FullAvail hP e f g Q)
    {J : Finset (Crossing P)} (hJT : J ⊆ triangleCrossings P e f g)
    {z : Crossing P} (hz : z ∈ triangleCrossings P e f g) (hzJ : z ∉ J) :
    z ∈ CV.U hP (Q ∪ J) := by
  rw [CV.mem_U_iff]
  have hQT : Disjoint Q (triangleCrossings P e f g) :=
    ((F1.mem_outsideSupports hP e f g Q).mp hQ).2
  have hfull' : avail hP e f g Q = triangleCrossings P e f g := hfull
  have hzA : ∀ q ∈ Q, ¬ GeometricInterlaces hP q z :=
    ((F1.mem_avail hP e f g Q z).mp (by rw [hfull']; exact hz)).2
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_union, not_or]
    exact ⟨Finset.disjoint_right.mp hQT hz, hzJ⟩
  · intro x hx hzx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact hzA x hx (geometricInterlaces_symm hP hzx)
    · exact PRE_not_interlaces_of_empty hL hz (hJT hx) hzx

/-- A vertex without neighbours reaches only itself. -/
theorem PRE_eq_of_reachable_of_isolated {V : Type*} {G : SimpleGraph V} {u v : V}
    (hiso : ∀ w, ¬ G.Adj u w) (h : G.Reachable u v) : u = v := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hiso _)

/-- "It is a singleton component there … Hence `{z}` is a singleton residual piece": a crossing of
`U(S)` with no residual neighbour (no interlaced crossing in `U(S)`) is a singleton piece of
CV:def:pieces (`CV.pieceOf`, `CV.pieceLabels`). -/
theorem PRE_pieceLabels_eq_singleton_of_isolated (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {z : Crossing P} (hz : z ∈ CV.U hP S)
    (hiso : ∀ c ∈ CV.U hP S, ¬ GeometricInterlaces hP z c) :
    CV.pieceLabels hP S (CV.pieceOf hP S z hz) = {z} := by
  ext c
  rw [CV.mem_pieceLabels, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hcz⟩
    have hreach : (CV.residualGraph hP S).Reachable ⟨z, hz⟩ ⟨c, hc⟩ :=
      SimpleGraph.ConnectedComponent.eq.mp hcz.symm
    have hiso' : ∀ w : (↑(CV.U hP S) : Set (Crossing P)), ¬ (CV.residualGraph hP S).Adj ⟨z, hz⟩ w :=
      fun w h => hiso w.1 w.2 h
    exact (congrArg Subtype.val (PRE_eq_of_reachable_of_isolated hiso' hreach)).symm
  · rintro rfl
    exact ⟨hz, rfl⟩

end PREHelpers

/-! ## Row 168 (ORDER 170) — R:exterior (R_ATTACHMENT_WARRANTS.md, "R-EXTERIOR-1 — the triangle-disjoint
factor")

Printed statement: "Let `P_-` and `P_+` be the generic sides of a simple transversal RIII event, and
let `T` be the three crossings identified by their carrying edge pairs as in R-LOC-2. Fix an outside
independent set `Q`, disjoint from `T`. On either side `sigma`, let `A` be any subset of `T` for
which `S = Q union A` is independent. A carrier of `S` is *triangle-disjoint* when it contains none of
the six traversal visits belonging to `T`, including a selected triangle crossing's smoothing-site
visits. Define `C_{Q,sigma}(A) = product over triangle-disjoint carriers L of wt_sigma(L) *
Omega_{1,sigma}(S,L)`. Then `C_{Q,sigma}(A)` is independent of `A`, and its common value is the same
for `sigma=-` and `sigma=+`. Write that single value as `C_Q`; it may be zero. Consequently every
full-availability row factors exactly as `tau_sigma(A) = C_Q * rho_sigma(A)`, where `rho_sigma(A)` is
the product over the triangle-touching carriers." OPEN_WORK.md item 4: "Prove the common exterior
factor without division; handle absent supports, empty products, dead selectors, orientations, both
directions and arbitrary exterior geometry." -/

section Exterior

variable {P : LabelledTuple n}

/-- "A carrier of `S` is *triangle-disjoint* when it contains none of the six traversal visits
belonging to `T`, including a selected triangle crossing's smoothing-site visits": no visit of a
triangle crossing is owned by the carrier (`geoOwner` is defined on every mark, the smoothing-site
visits of a selected crossing included, by SM conv:selected-visits). -/
def TriangleDisjoint (hP : CrossingGeometry P) (S : Finset (Crossing P)) (e f g : ZMod n)
    (q : GeoComponent hP S) : Prop :=
  ∀ v : Visit P, v.1.val ∈ triangleSupports e f g → geoOwner hP S (Sum.inr v) ≠ q

open scoped Classical in
/-- "`C_{Q,sigma}(A) = product over triangle-disjoint carriers L of wt_sigma(L) *
Omega_{1,sigma}(S,L)`", `S = Q ∪ A`. -/
noncomputable def exteriorFactor (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (e f g : ZMod n) : ℤ :=
  ∏ q ∈ (Finset.univ : Finset (GeoComponent hG.crossingGeometry S)).filter
      (TriangleDisjoint hG.crossingGeometry S e f g),
    CV.weight hG.crossingGeometry S q * CV.Omega1 hn hG hS q

open scoped Classical in
/-- "`rho_sigma(A)` is the product over the triangle-touching carriers" (of `wt(L) Omega_1(S,L)`). -/
noncomputable def touchingFactor (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (e f g : ZMod n) : ℤ :=
  ∏ q ∈ (Finset.univ : Finset (GeoComponent hG.crossingGeometry S)).filter
      (fun q => ¬ TriangleDisjoint hG.crossingGeometry S e f g q),
    CV.weight hG.crossingGeometry S q * CV.Omega1 hn hG hS q

/-- "`def:wind` gives `wind(S) = product_L wt(L)`, while `def:X1` multiplies all carrier `Omega_1`
factors. Partitioning the carriers into disjoint and touching classes therefore gives
`tau_sigma(A) = C_{Q,sigma} * rho_sigma(A)` as an identity, including when either factor is zero"
(R-EXTERIOR-1, proof §3): the row term is the product of its own exterior and touching factors.
PROVED (a product split; the content of the row is that `C_{Q,σ}` is the same for every `A` and
both `σ`). -/
theorem rowTerm_eq_exterior_mul_touching (hn : 3 ≤ n) (hG : CV.Generic P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hG.crossingGeometry) (e f g : ZMod n) :
    rowTerm hn hG S = exteriorFactor hn hG hS e f g * touchingFactor hn hG hS e f g := by
  classical
  rw [rowTerm_of_mem_Ind hn hG hS]
  unfold exteriorFactor touchingFactor CV.wind
  rw [Finset.prod_filter_mul_prod_filter_not, Finset.prod_mul_distrib]

end Exterior

/-- **R-EXTERIOR-1**, clause by clause, for the event `E`, the triangle `e, f, g`, the radius `δ`.
`Q` ranges over the outside independent supports, `A` over the subsets of `T` with `Q ∪ A`
independent on the side in question; across the wall `Q` is read through `transportSupport hs`.
The independence hypotheses exclude "absent supports"; "empty products" and "dead selectors" are
covered because `wt` may be `0` and nothing is divided. -/
structure ExteriorData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Then `C_{Q,sigma}(A)` is independent of `A`" (on either side `σ`; any two `A, A' ⊆ T` with
  `Q ∪ A`, `Q ∪ A'` independent; not restricted to full availability, as printed). -/
  independent_of_A : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ A A' : Finset (Crossing (E.curve t)),
      A ⊆ triangleCrossings (E.curve t) e f g → A' ⊆ triangleCrossings (E.curve t) e f g →
      ∀ (hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1)) (hA' : Q ∪ A' ∈ CV.Ind (geomAt E t ht.1)),
        exteriorFactor hn (genericAt E t ht.1) hA e f g =
          exteriorFactor hn (genericAt E t ht.1) hA' e f g
  /-- "and its common value is the same for `sigma=-` and `sigma=+`. Write that single value as `C_Q`;
  it may be zero." — across the wall, for any `A` on one side and any `A'` on the other ("both
  directions", "arbitrary exterior geometry"). -/
  wall_invariant : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ (A : Finset (Crossing (E.curve t))) (A' : Finset (Crossing (E.curve t'))),
      A ⊆ triangleCrossings (E.curve t) e f g → A' ⊆ triangleCrossings (E.curve t') e f g →
      ∀ (hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1))
        (hA' : transportSupport hs Q ∪ A' ∈ CV.Ind (geomAt E t' ht'.1)),
        exteriorFactor hn (genericAt E t ht.1) hA e f g =
          exteriorFactor hn (genericAt E t' ht'.1) hA' e f g
  /-- "Consequently every full-availability row factors exactly as `tau_sigma(A) = C_Q *
  rho_sigma(A)`, where `rho_sigma(A)` is the product over the triangle-touching carriers": the single
  value `C_Q` is represented by the exterior factor of the base row `Q` (`A = ∅`) on the side `t` —
  equal to every other representative on either side by the two previous clauses — and serves every
  row `A` on both sides. (`rowTerm_eq_exterior_mul_touching` is the algebraic half.) -/
  factorization : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q, ∀ hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      (∀ A : Finset (Crossing (E.curve t)), A ⊆ triangleCrossings (E.curve t) e f g →
        ∀ hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1),
          rowTerm hn (genericAt E t ht.1) (Q ∪ A) =
            exteriorFactor hn (genericAt E t ht.1) (mem_Ind_of_mem_outsideSupports hQ) e f g *
              touchingFactor hn (genericAt E t ht.1) hA e f g) ∧
      (∀ A' : Finset (Crossing (E.curve t')), A' ⊆ triangleCrossings (E.curve t') e f g →
        ∀ hA' : transportSupport hs Q ∪ A' ∈ CV.Ind (geomAt E t' ht'.1),
          rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q ∪ A') =
            exteriorFactor hn (genericAt E t ht.1) (mem_Ind_of_mem_outsideSupports hQ) e f g *
              touchingFactor hn (genericAt E t' ht'.1) hA' e f g)

/-- **Row 168, R:exterior** (R-EXTERIOR-1). -/
theorem exterior (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExteriorData hn E e f g δ := by
  sorry

/-! ## Row 170 (ORDER 176) — R:availability_0_1 (R_ASSEMBLY_SPEC.md, the paragraph after (4);
OPEN_WORK.md item 2)

Specified text: "The local proof task, for each such `Q`, is `Φ_+(Q) = Φ_-(Q)` (4). At availability
zero or one the local supports themselves correspond, but that does **not** prove their summands
agree. Prove the required carrier/record, selector, rotation and coefficient transport. These cases
cannot be omitted because the four core proofs assume full availability." OPEN_WORK.md item 2:
"Prove the fibre identities for availability 0 and 1. The supplied core proofs assume full
availability and do not by themselves cover these cases." -/

/-- R_ASSEMBLY_SPEC.md: "Prove the required carrier/record, selector, rotation and coefficient
transport": the two complete summands are matched carrier by carrier — the selector (`wind`, and
`wt` per carrier), a bijection of carriers `τ` carrying the record data `w_{S,L}` (`groupedWrithe`)
and `P_{S,L}` (`groupedPoly`), the rotation `R(L)` (`carrierR`) and the coefficient `Ω₁(S,L)`
(`Omega1`). -/
def SummandTransport (hn : 3 ≤ n) {P Q : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic Q)
    {S : Finset (Crossing P)} {S' : Finset (Crossing Q)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry) : Prop :=
  CV.wind hG'.crossingGeometry S' = CV.wind hG.crossingGeometry S ∧
  ∃ τ : GeoComponent hG.crossingGeometry S ≃ GeoComponent hG'.crossingGeometry S',
    ∀ q, CV.weight hG'.crossingGeometry S' (τ q) = CV.weight hG.crossingGeometry S q ∧
      CV.carrierR hn hG' hS' (τ q) = CV.carrierR hn hG hS q ∧
      CV.groupedWrithe hG' (τ q) = CV.groupedWrithe hG q ∧
      CV.groupedPoly hn hG' hS' (τ q) = CV.groupedPoly hn hG hS q ∧
      CV.Omega1 hn hG' hS' (τ q) = CV.Omega1 hn hG hS q

/-- **The availability-0/1 fibre identities**, clause by clause, for every outside independent `Q`
with `|𝓐(Q)| ∈ {0, 1}` (`FibrePartitionData.avail_card` excludes `2`; `3` is full availability, rows
172–177), across the wall (`Q` read on the far side through `transportSupport hs`). -/
structure AvailabilityZeroOneData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "At availability zero … the local supports themselves correspond": `Ind(G[𝓐(Q)]) = {∅}`. -/
  fibre_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, (avail (geomAt E t ht.1) e f g Q).card = 0 →
      localFibre (geomAt E t ht.1) e f g Q = {∅}
  /-- "At availability … one the local supports themselves correspond": `𝓐(Q) = {z}` and
  `Ind(G[𝓐(Q)]) = {∅, {z}}`. -/
  fibre_one : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∃ z : Crossing (E.curve t), avail (geomAt E t ht.1) e f g Q = {z} ∧
        localFibre (geomAt E t ht.1) e f g Q = {∅, {z}}
  /-- "the local supports themselves correspond" across the wall: the local fibre over `Q` on one side
  is carried onto the local fibre over `Q` on the other side by the carrying edge pairs. -/
  fibre_correspond : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      localFibre (geomAt E t' ht'.1) e f g (transportSupport hs Q) =
        (localFibre (geomAt E t ht.1) e f g Q).map (supportEmb hs)
  /-- "but that does **not** prove their summands agree. Prove the required carrier/record, selector,
  rotation and coefficient transport": for every local support `J` of the fibre, the complete
  summands at `Q ∪ J` on the two sides are matched carrier by carrier (`SummandTransport`). -/
  summand_transport : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
      ∀ (hS : Q ∪ J ∈ CV.Ind (geomAt E t ht.1))
        (hS' : transportSupport hs (Q ∪ J) ∈ CV.Ind (geomAt E t' ht'.1)),
        SummandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS'
  /-- … so that "their summands agree": `F_+(Q ∪ J) = F_-(Q ∪ J)` for every `J` of the fibre
  (absent rows on both sides being `0`). -/
  summands_agree : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
        rowTerm hn (genericAt E t ht.1) (Q ∪ J) =
          rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ J))
  /-- "The local proof task, for each such `Q`, is `Φ_+(Q) = Φ_-(Q)` (4)" at availability zero or
  one (OPEN_WORK.md item 2 "the fibre identities for availability 0 and 1"). -/
  fibre_identity : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q)

/-! ### Unit PRE — the X₁-free presupposition fields of row 170 (`fibre_zero`, `fibre_one`,
`fibre_correspond`), each with exactly the field's type; the assembler plugs them into
`AvailabilityZeroOneData`. -/

/-- Field `fibre_zero` of `AvailabilityZeroOneData`, unconditionally: `𝓐(Q) = ∅`, so the local fibre
is `{∅}` (`∅` is independent). -/
theorem PRE_170_fibre_zero (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, (avail (geomAt E t ht.1) e f g Q).card = 0 →
      localFibre (geomAt E t ht.1) e f g Q = {∅} := by
  intro t ht Q _ hQ0
  rw [PRE_localFibre_eq_powerset _ e f g Q (by omega), Finset.card_eq_zero.mp hQ0,
    Finset.powerset_empty]

/-- Field `fibre_one` of `AvailabilityZeroOneData`, unconditionally: `𝓐(Q) = {z}`, so the local fibre
is `{∅, {z}}` (both subsets of a singleton are independent). -/
theorem PRE_170_fibre_one (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∃ z : Crossing (E.curve t), avail (geomAt E t ht.1) e f g Q = {z} ∧
        localFibre (geomAt E t ht.1) e f g Q = {∅, {z}} := by
  intro t ht Q _ hQ1
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hQ1
  refine ⟨z, hz, ?_⟩
  rw [PRE_localFibre_eq_powerset _ e f g Q (by omega), hz]
  ext J
  rw [Finset.mem_powerset, Finset.subset_singleton_iff, Finset.mem_insert, Finset.mem_singleton]

/-- Field `fibre_correspond` of `AvailabilityZeroOneData` from `FibrePartitionData.avail_same`: at
availability `≤ 1` the local fibre on either side is the power set of `𝓐(Q)`, and `𝓐(Q)` is carried
across the wall by the carrying edge pairs. -/
theorem PRE_170_fibre_correspond {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hF : FibrePartitionData E e f g δ) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      localFibre (geomAt E t' ht'.1) e f g (transportSupport hs Q) =
        (localFibre (geomAt E t ht.1) e f g Q).map (supportEmb hs) := by
  intro t t' ht ht' hop hs Q hQ hcard
  have h1 : (avail (geomAt E t ht.1) e f g Q).card ≤ 1 := by omega
  have havail : avail (geomAt E t' ht'.1) e f g (transportSupport hs Q) =
      (avail (geomAt E t ht.1) e f g Q).map (crossingTransport hs).toEmbedding :=
    hF.avail_same t t' ht ht' hop hs Q hQ
  have h1' : (avail (geomAt E t' ht'.1) e f g (transportSupport hs Q)).card ≤ 1 := by
    rw [havail, Finset.card_map]; exact h1
  rw [PRE_localFibre_eq_powerset _ e f g _ h1', PRE_localFibre_eq_powerset _ e f g Q h1, havail]
  ext J'
  rw [Finset.mem_powerset, Finset.mem_map, Finset.subset_map_iff]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Finset.mem_powerset.mpr hu, supportEmb_apply hs u⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Finset.mem_powerset.mp hu, (supportEmb_apply hs u).symm⟩

/-- **Row 170, R:availability_0_1**. -/
theorem availability_zero_one (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AvailabilityZeroOneData hn E e f g δ := by
  sorry

/-! ## Row 172 (ORDER 177) — R:generic_selector (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md)

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the generic graph orbit
`P3 <-> (one edge plus one isolated vertex)`. Among the three one-sided local pair supports, one is
the graph-selected pair complementary to the degree-two singleton of `P3`. Each of the other two pair
rows has winding selector zero on the side where it is present. This holds for arbitrary exterior gaps
and outside independent support `Q`; no coefficient, exterior-factor division, or nonvanishing
hypothesis is used."
"The mixed carrier": "Take either nonselected pair and let `u` be its shared strand, with the other
strand directions `v,w`. Failure of the corresponding selected-condition in (4) is exactly
`sgn det(u,v) = sgn det(u,w)` (5). … Consequently one carrier contains the entire arc and both of its
endpoint smoothing corners. … Traversing this carrier through the segment, one endpoint turns from
`v` into `u` and the other from `u` into `w` (or the same description with `v,w` interchanged). The two
corner determinants are therefore `det(v,u) = -det(u,v)`, and `det(u,w)` (6). By (5), the signs in (6)
are opposite. The carrier is mixed regardless of all its other corners, so its weight is zero by
`def:wind`. The support's winding selector, a product containing this weight, is zero. Consequently
its entire X1 row is zero before any coefficient is read." -/

section Selector

variable {P : LabelledTuple n}

/-- "one carrier contains the entire arc and both of its endpoint smoothing corners … one endpoint
turns from `v` into `u` and the other from `u` into `w` (or the same description with `v,w`
interchanged)": for the pair `x = x_{uv}`, `y = x_{uw}` sharing the strand `u`, a carrier of `S` owns
the smoothing corner of `x` at its `v`-visit (arriving along `v`, leaving along `u`) and that of `y`
at its `u`-visit (arriving along `u`, leaving along `w`) — or, the order along `u` reversed, the
corner of `y` at its `w`-visit and that of `x` at its `u`-visit — and "the carrier is mixed"
(CV:def:wind). The mark of a selected visit is the corner at which the carrier ARRIVES along that
visit's edge and leaves along the twin's edge (`CV.turn_visit_of_traced`; conv:selected-visits), so
the two corners lie on different edges (one on the shared strand `u`, one on `v` or `w`), never both
on `u`. -/
def MixedSharedStrandCarrier (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (x y : Crossing P) {u v w : ZMod n} (hxu : u ∈ x.val) (hxv : v ∈ x.val) (hyu : u ∈ y.val)
    (hyw : w ∈ y.val) : Prop :=
  ∃ q : GeoComponent hP S,
    ((geoOwner hP S (Sum.inr (visitOn x v hxv)) = q ∧ geoOwner hP S (Sum.inr (visitOn y u hyu)) = q) ∨
     (geoOwner hP S (Sum.inr (visitOn y w hyw)) = q ∧ geoOwner hP S (Sum.inr (visitOn x u hxu)) = q)) ∧
    CV.CarrierMixed hP S q

omit [NeZero n] in
/-- The strand signs `s_a, s_b, s_c` of the sign classification are the crossing signs
`sgn det(d_i, d_j)` of the corner turns (CV:def:wind reads `crossingSign` at a smoothing corner). -/
theorem strandSign_eq_crossingSign (P : LabelledTuple n) (i j : ZMod n) :
    strandSign P i j = crossingSign P i j := rfl

end Selector

/-- **The generic nonselected pair rows are selector-dead**, clause by clause. Labels: pair `ab`
shares `u = e` (others `f, g`), pair `ac` shares `u = f` (others `e, g`), pair `bc` shares `u = g`
(others `e, f`). -/
structure GenericSelectorData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Among the three one-sided local pair supports, one is the graph-selected pair complementary
  to the degree-two singleton of `P3`": in the generic orbit exactly one of the three
  selected-conditions (4) holds (the event-level instance of `GenericTableData.selected_unique`);
  that this pair is the graph-selected one — the complement of the degree-two vertex on the two-edge
  side, the present edge on the one-edge side — is the accepted
  `GenericTableData.selected_is_graph_selected`. -/
  selected_pair_unique : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ((SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) ∧
        ¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) ∧
        ¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g)) ∨
     (¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) ∧
        SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) ∧
        ¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g)) ∨
     (¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) ∧
        ¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) ∧
        SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g)))
  /-- (5)–(6): "Failure of the corresponding selected-condition in (4) is exactly `sgn det(u,v) =
  sgn det(u,w)` (5). … The two corner determinants are therefore `det(v,u) = -det(u,v)`, and `det(u,w)`
  (6). By (5), the signs in (6) are opposite" — for each nonselected pair, in both traversal orders. -/
  corner_signs_opposite : ∀ t : E.Parameter, Punctured E δ t →
    (¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      crossingSign (E.curve t) f e = -crossingSign (E.curve t) e g ∧
      crossingSign (E.curve t) g e = -crossingSign (E.curve t) e f) ∧
    (¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) →
      crossingSign (E.curve t) e f = -crossingSign (E.curve t) f g ∧
      crossingSign (E.curve t) g f = -crossingSign (E.curve t) f e) ∧
    (¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      crossingSign (E.curve t) e g = -crossingSign (E.curve t) g f ∧
      crossingSign (E.curve t) f g = -crossingSign (E.curve t) g e)
  /-- "R-LOC says that the two triangle-crossing visits on each bundle edge are adjacent … Smoothing
  `Q` acts only at outside crossing visits, so it cannot cut or rewire this arc. Smoothing the two
  local crossings attaches one end of the intact arc to the incoming `v` branch and its other end to
  the outgoing `w` branch … Consequently one carrier contains the entire arc and both of its endpoint
  smoothing corners. … The carrier is mixed regardless of all its other corners": for each nonselected
  pair present on the side, on the full-availability fibre of any outside `Q`. -/
  mixed_carrier : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      Q ∪ {xPair hef, xPair heg} ∈ CV.Ind (geomAt E t ht.1) →
      MixedSharedStrandCarrier (geomAt E t ht.1) (Q ∪ {xPair hef, xPair heg}) (xPair hef) (xPair heg)
        (mem_pair_left e f) (mem_pair_right e f) (mem_pair_left e g) (mem_pair_right e g)) ∧
    (¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) →
      Q ∪ {xPair hef, xPair hfg} ∈ CV.Ind (geomAt E t ht.1) →
      MixedSharedStrandCarrier (geomAt E t ht.1) (Q ∪ {xPair hef, xPair hfg}) (xPair hef) (xPair hfg)
        (mem_pair_right e f) (mem_pair_left e f) (mem_pair_left f g) (mem_pair_right f g)) ∧
    (¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      Q ∪ {xPair heg, xPair hfg} ∈ CV.Ind (geomAt E t ht.1) →
      MixedSharedStrandCarrier (geomAt E t ht.1) (Q ∪ {xPair heg, xPair hfg}) (xPair heg) (xPair hfg)
        (mem_pair_right e g) (mem_pair_left e g) (mem_pair_right f g) (mem_pair_left f g))
  /-- "Each of the other two pair rows has winding selector zero on the side where it is present"
  ("its weight is zero by `def:wind`. The support's winding selector, a product containing this
  weight, is zero"). -/
  selector_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      Q ∪ {xPair hef, xPair heg} ∈ CV.Ind (geomAt E t ht.1) →
      CV.wind (geomAt E t ht.1) (Q ∪ {xPair hef, xPair heg}) = 0) ∧
    (¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) →
      Q ∪ {xPair hef, xPair hfg} ∈ CV.Ind (geomAt E t ht.1) →
      CV.wind (geomAt E t ht.1) (Q ∪ {xPair hef, xPair hfg}) = 0) ∧
    (¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      Q ∪ {xPair heg, xPair hfg} ∈ CV.Ind (geomAt E t ht.1) →
      CV.wind (geomAt E t ht.1) (Q ∪ {xPair heg, xPair hfg}) = 0)
  /-- "Consequently its entire X1 row is zero before any coefficient is read" (on either side —
  absent rows are zero by convention, so no presence hypothesis is needed). -/
  row_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair heg}) = 0) ∧
    (¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair hfg}) = 0) ∧
    (¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg, xPair hfg}) = 0)

/-- **Row 172, R:generic_selector** (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md). -/
theorem generic_selector (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectorData hn E e f g δ := by
  sorry

/-! ## Row 173 (ORDER 178) — R:generic_transport (R_GENERIC_COMMON_TRANSPORT_PROOF.md, "Statement and
canonical branch")

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the generic graph orbit and
an exterior independent support `Q`. Relabel the local crossings so `P = a b A a c B b c C` (edges
ab,bc), `E = b a A c a B c b C` (edge ac). Write the three determinant signs in the crossing order
`a=(u1,u2)`, `b=(u1,u3)`, `c=(u2,u3)`. … In the displayed graph the selected pair is `ac`, so its
shared strand `u2` separates `u1,u3`, giving equality of the `a` and `c` determinant signs. If the `b`
sign were opposite, the triple would be one of the two alternating triples … Hence the generic branch
here has `sgn det(u1,u2) = sgn det(u1,u3) = sgn det(u2,u3) = sigma` (1). Every generic branch can be
put in this form by relabelling the strands in their transitive angular order. The same relabelling
carries the crossings and the exterior gap strings `A,B,C`; no symmetry of those strings is used.
Write `T_nu(J)` for the complete X1 term of `Q union J` on side `nu`. Then `T_P(empty)=T_E(empty)`,
`T_P(a)=T_E(a)`, `T_P(c)=T_E(c)` (2)." -/

/-- **The generic common-row transports**, clause by clause. The identities (2) are symmetric in the
two sides, so no side is named `P`; the canonical branch is `s_a = s_b = s_c` (selected pair `ac`,
endpoints `a, c`), and the relabelled branches are the selected pairs `ab` (endpoints `a, b`) and
`bc` (endpoints `b, c`) — "endpoint rows" = the singleton rows of the two members of the selected
pair (`GenericTableData.selected_is_graph_selected`). -/
structure GenericTransportData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- (1) "In the displayed graph the selected pair is `ac` … giving equality of the `a` and `c`
  determinant signs. If the `b` sign were opposite, the triple would be one of the two alternating
  triples … Hence the generic branch here has `sgn det(u1,u2) = sgn det(u1,u3) = sgn det(u2,u3) =
  sigma`": in the generic orbit, `ac` selected iff all three signs agree. -/
  canonical_branch : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    (SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) ↔
      (strandSign (E.curve t) e f = strandSign (E.curve t) e g ∧
        strandSign (E.curve t) e g = strandSign (E.curve t) f g))
  /-- (2) "`T_P(empty) = T_E(empty)`" (every generic branch: the empty row needs no relabelling). -/
  empty_row : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q = rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q)
  /-- (2) "`T_P(a) = T_E(a)`, `T_P(c) = T_E(c)`" in the canonical branch (1) `s_a = s_b = s_c`
  (selected pair `ac`): the two endpoint singleton rows transport. -/
  endpoint_rows_canonical : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg}))
  /-- "Every generic branch can be put in this form by relabelling the strands … The same relabelling
  carries the crossings": the two endpoint rows of the other four generic branches — selected pair
  `ab` (endpoints `a, b`) and selected pair `bc` (endpoints `b, c`). -/
  endpoint_rows_relabelled : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg}))) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg})))

/-! ### Unit PRE — the X₁-free presupposition field of row 173 (`canonical_branch`). -/

/-- Field `canonical_branch` of `GenericTransportData` from `GenericTableData` (`nonzero`,
`generic_iff_nonalternating`): in the generic orbit the three strand signs are nonzero and
nonalternating, so `s_a = s_c` forces `s_b = s_a` (`PRE_selectedAC_iff_all_eq`). -/
theorem PRE_173_canonical_branch {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hG : GenericTableData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    (SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) ↔
      (strandSign (E.curve t) e f = strandSign (E.curve t) e g ∧
        strandSign (E.curve t) e g = strandSign (E.curve t) f g)) := by
  intro t ht hef heg hfg hgen
  obtain ⟨h1, h2, h3, -⟩ := hG.nonzero t ht
  exact PRE_selectedAC_iff_all_eq _ _ _ (sign_ne_zero.mpr h1) (sign_ne_zero.mpr h2)
    (sign_ne_zero.mpr h3) ((hG.generic_iff_nonalternating t ht hef heg hfg).mp hgen)

/-- **Row 173, R:generic_transport** (R_GENERIC_COMMON_TRANSPORT_PROOF.md). -/
theorem generic_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ := by
  sorry

/-! ## Row 174 (ORDER 182) — R:generic_selected (R_GENERIC_SELECTED_COUPLE_PROOF.md, Statement)

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the generic graph orbit and
an exterior independent support `Q`. Relabel the three local crossings so the exact local words are
`P = a b A a c B b c C` (edges ab,bc), `E = b a A c a B c b C` (edge ac). Thus `b` is the degree-two
vertex of the path, and `ac` is its complementary independent pair on `P`. If `T_nu(J)` denotes the
complete X1 term of `Q union J` on side `nu`, absent rows being zero, then `T_E(b) = T_P(b) + T_P(ac)`
(GSC). This is exactly the selected `b/ac` complementary-couple identity, with the opposite
coorientation obtained by multiplying the equation by `-1`." The side `P` is the two-edge side
(`EdgeAB ∧ EdgeBC`, centre `b`), `E` the other side. -/

/-- **The generic selected complementary couple**, clause by clause: the canonical branch (selected
pair `ac`, centre `b`) and the two relabelled branches (selected `ab`, centre `c`; selected `bc`,
centre `a`). `t` is the two-edge side `P` (named by its graph), `t'` the one-edge side `E`. -/
structure GenericSelectedData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- (GSC) "`T_E(b) = T_P(b) + T_P(ac)`", canonical branch `s_a = s_b = s_c` ("`b` is the degree-two
  vertex of the path, and `ac` is its complementary independent pair on `P`"). -/
  couple_canonical : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    EdgeAB (geomAt E t ht.1) hef heg → EdgeBC (geomAt E t ht.1) heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair hfg})
  /-- "Relabel the three local crossings so the exact local words are …": the same couple in the
  other four generic branches — selected pair `ab` with centre `c` (two-edge side `ac, bc`), and
  selected pair `bc` with centre `a` (two-edge side `ab, ac`). -/
  couple_relabelled : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      EdgeAC (geomAt E t ht.1) hef hfg → EdgeBC (geomAt E t ht.1) heg hfg →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair heg})) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      EdgeAB (geomAt E t ht.1) hef heg → EdgeAC (geomAt E t ht.1) hef hfg →
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef})) =
        rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef}) +
          rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg, xPair hfg}))

/-- **Row 174, R:generic_selected** (R_GENERIC_SELECTED_COUPLE_PROOF.md). -/
theorem generic_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ := by
  sorry

/-! ## Row 175 (ORDER 183) — R:extreme_pair_zero (R_EXTREME_PAIR_ZERO_PROOF.md)

Printed statement: "Fix the two nearby generic chamber-side representatives of a simple RIII wall in
the extreme graph orbit `K3 <-> empty`, and fix a full-availability fiber. Each local pair support is
absent on the `K3` side and present on the empty-graph side. Its complete X1 term on the latter
generic polygon is zero, for arbitrary outside support and exterior geometry."
Proof, paragraphs 2–3: "The support `S` is independent. … The remaining crossing `z` is undominated by
`S` … It is a singleton component there. … Hence `{z}` is a singleton residual piece" — the hypothesis
under which `thm:s7universal(D)(i)` (CV:singleton_D_i) is read. -/

/-- **Every extreme one-sided pair row is zero**, clause by clause, on each side (the side is named by
its local graph: `K3` side = `CompleteLocal`, empty-graph side = `EmptyLocal`). -/
structure ExtremePairZeroData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Each local pair support is absent on the `K3` side". -/
  pair_absent_on_complete : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      Q ∪ J ∉ CV.Ind (geomAt E t ht.1)
  /-- "and present on the empty-graph side" ("The support `S` is independent. Indeed, `J` is
  independent because the local graph is empty, and full availability says every member of `T` is
  nonadjacent to every member of `Q`"). -/
  pair_present_on_empty : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      Q ∪ J ∈ CV.Ind (geomAt E t ht.1)
  /-- "The remaining crossing `z` is undominated by `S` … It is a singleton component there. … Hence
  `{z}` is a singleton residual piece" (the hypothesis under which thm:s7universal (D)(i),
  CV:singleton_D_i, is read). -/
  third_singleton_piece : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
    ∀ z ∈ triangleCrossings (E.curve t) e f g, z ∉ J →
      ∃ hz : z ∈ CV.U (geomAt E t ht.1) (Q ∪ J),
        CV.pieceLabels (geomAt E t ht.1) (Q ∪ J) (CV.pieceOf (geomAt E t ht.1) (Q ∪ J) z hz) = {z}
  /-- "Its complete X1 term on the latter generic polygon is zero, for arbitrary outside support and
  exterior geometry." -/
  pair_row_zero : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      rowTerm hn (genericAt E t ht.1) (Q ∪ J) = 0

/-! ### Unit PRE — the X₁-free presupposition fields of row 175 (`pair_absent_on_complete`,
`pair_present_on_empty`, `third_singleton_piece`). -/

/-- Field `pair_absent_on_complete` of `ExtremePairZeroData`, unconditionally: the two members of a
local pair interlace on the `K3` side, so `Q ∪ J` is not independent. -/
theorem PRE_175_pair_absent_on_complete (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      Q ∪ J ∉ CV.Ind (geomAt E t ht.1) := by
  intro t ht hef heg hfg hK Q _ _ J hJT hJ2 hind
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hJ2
  have hxJ : x ∈ ({x, y} : Finset (Crossing (E.curve t))) := Finset.mem_insert_self x {y}
  have hyJ : y ∈ ({x, y} : Finset (Crossing (E.curve t))) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  exact (CV.mem_Ind_iff _ _).mp hind x (Finset.mem_union_right _ hxJ) y
    (Finset.mem_union_right _ hyJ) hxy (PRE_interlaces_of_complete hK (hJT hxJ) (hJT hyJ) hxy)

/-- Field `pair_present_on_empty` of `ExtremePairZeroData`, unconditionally ("The support `S` is
independent. Indeed, `J` is independent because the local graph is empty, and full availability
says every member of `T` is nonadjacent to every member of `Q`"). -/
theorem PRE_175_pair_present_on_empty (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      Q ∪ J ∈ CV.Ind (geomAt E t ht.1) := by
  intro t ht hef heg hfg hL Q hQ hfull J hJT _
  exact PRE_union_mem_Ind_of_fullAvail hQ hfull hJT (PRE_mem_Ind_of_empty hL hJT)

/-- Field `third_singleton_piece` of `ExtremePairZeroData` from `ParityData.interlaced_pair`
(R-PAR (P1)): `z ∈ U(Q ∪ J)` by `PRE_third_mem_U`; "Suppose an outside residual crossing `c` were
adjacent to `z`. Accepted R-PAR(P1) is quantified over every crossing `c` outside `T` … Since `c` is
adjacent to `z`, it must therefore be adjacent to at least one of `x, y`. But `x, y` lie in the
support `S`, so `c` would be dominated and could not be residual" — and a local residual neighbour
is impossible because `T ∖ {z} = J ⊆ S`; hence `z` is isolated in the residual graph and its piece
is `{z}` (`PRE_pieceLabels_eq_singleton_of_isolated`). -/
theorem PRE_175_third_singleton_piece {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hPar : ParityData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
    ∀ z ∈ triangleCrossings (E.curve t) e f g, z ∉ J →
      ∃ hz : z ∈ CV.U (geomAt E t ht.1) (Q ∪ J),
        CV.pieceLabels (geomAt E t ht.1) (Q ∪ J) (CV.pieceOf (geomAt E t ht.1) (Q ∪ J) z hz) = {z} := by
  intro t ht hef heg hfg hL Q hQ hfull J hJT hJ2 z hz hzJ
  have hzU := PRE_third_mem_U hL hQ hfull hJT hz hzJ
  refine ⟨hzU, PRE_pieceLabels_eq_singleton_of_isolated _ _ hzU ?_⟩
  intro c hc hzc
  have hcU := (CV.mem_U_iff _ _ c).mp hc
  -- `c` is not a triangle crossing: a triangle crossing interlacing `z` is `≠ z`, hence in `J ⊆ S`.
  have hcT : c.val ∉ triangleSupports e f g := by
    intro hcT
    have hcT' : c ∈ triangleCrossings (E.curve t) e f g :=
      (F1.mem_triangleCrossings e f g c).mpr hcT
    have hcz : c ≠ z := fun h => geometricInterlaces_irrefl _ z (h ▸ hzc)
    exact hcU.1 (Finset.mem_union_right _ (PRE_mem_of_third hef heg hfg hJT hJ2 hz hzJ hcT' hcz))
  -- R-PAR (P1): the interlaced pair of the outside crossing `c` is a bundle pair `{x ∈ T : h ∈ x}`.
  have hne : (interlacedTriangle (geomAt E t ht.1) e f g c).Nonempty :=
    ⟨z, (G2.mem_interlacedTriangle_iff _ c z).mpr
      ⟨(F1.mem_triangleCrossings e f g z).mp hz, geometricInterlaces_symm _ hzc⟩⟩
  obtain ⟨h, hh, hpair⟩ := hPar.interlaced_pair t ht c hcT hne
  have hcard : (interlacedTriangle (geomAt E t ht.1) e f g c).card = 2 := by
    rw [hpair]; exact P1.filter_card_two hef heg hfg h hh
  obtain ⟨x, y, hxy, hI⟩ := Finset.card_eq_two.mp hcard
  -- the other member `y'` of the pair is a triangle crossing `≠ z`, hence in `J`, yet interlaces `c`.
  have key : ∀ y' ∈ interlacedTriangle (geomAt E t ht.1) e f g c, y' ≠ z → False := by
    intro y' hy' hy'z
    obtain ⟨hy'T, hcy'⟩ := (G2.mem_interlacedTriangle_iff _ c y').mp hy'
    have hy'J : y' ∈ J := PRE_mem_of_third hef heg hfg hJT hJ2 hz hzJ
      ((F1.mem_triangleCrossings e f g y').mpr hy'T) hy'z
    exact hcU.2 y' (Finset.mem_union_right _ hy'J) hcy'
  have hxI : x ∈ interlacedTriangle (geomAt E t ht.1) e f g c := by
    rw [hI]; exact Finset.mem_insert_self x {y}
  have hyI : y ∈ interlacedTriangle (geomAt E t ht.1) e f g c := by
    rw [hI]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
  by_cases hxz : x = z
  · exact key y hyI (fun h' => hxy (hxz.trans h'.symm))
  · exact key x hxI hxz

/-- **Row 175, R:extreme_pair_zero** (R_EXTREME_PAIR_ZERO_PROOF.md). -/
theorem extreme_pair_zero (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ := by
  sorry

/-! ## Row 176 (ORDER 175) — R:extreme_transport (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md, "Statement
and canonical data")

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the extreme graph orbit, an
outside support `Q`, and the canonical words `H = x y A z x B y z C` (local graph K3), `L = y x A x z B
z y C` (local graph empty) (1). Full availability is part of the statement: every member of
`T={x,y,z}` is nonadjacent to `Q`, so every `Q union {j}` is independent on both sides. R-LOC-2 clause
4 identifies the two extreme local graphs in (1): `H[T]=K3` if and only if `L[T]` is empty. … Write
`T_nu(J)` for the complete X1 term of `Q union J`, with an absent row read as zero. Then, separately
and without a symmetry assumption, `T_H(x)=T_L(x)`, `T_H(y)=T_L(y)`, `T_H(z)=T_L(z)` (2). Let the
oriented strand directions be `u1,u2,u3`, with `x=(u1,u2)`, `y=(u1,u3)`, and `z=(u2,u3)`. The exact
line-order calculation for the extreme orbit gives `s_x = sgn det(u1,u2) = sigma`, `s_y = sgn
det(u1,u3) = -sigma`, `s_z = sgn det(u2,u3) = sigma` (3)." Labels: `x = a = x_ef`, `y = b = x_eg`,
`z = c = x_fg`. The identities (2) are symmetric in the sides, so no side is named. -/

/-- **The extreme singleton transports**, clause by clause. -/
structure ExtremeTransportData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Full availability is part of the statement: every member of `T={x,y,z}` is nonadjacent to `Q`,
  so every `Q union {j}` is independent on both sides." -/
  singleton_rows_present : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ j ∈ triangleCrossings (E.curve t) e f g, Q ∪ {j} ∈ CV.Ind (geomAt E t ht.1)
  /-- "R-LOC-2 clause 4 identifies the two extreme local graphs in (1): `H[T]=K3` if and only if
  `L[T]` is empty." -/
  graphs_complementary : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g})
      (hef' : IsCrossing (E.curve t') {e, f}) (heg' : IsCrossing (E.curve t') {e, g})
      (hfg' : IsCrossing (E.curve t') {f, g}),
    (CompleteLocal (geomAt E t ht.1) hef heg hfg ↔ EmptyLocal (geomAt E t' ht'.1) hef' heg' hfg')
  /-- (3) "The exact line-order calculation for the extreme orbit gives `s_x = sigma`, `s_y = -sigma`,
  `s_z = sigma`" (the alternating triple of `GenericTableData.extreme_iff_alternating`). -/
  sign_branch : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
      strandSign (E.curve t) e f = strandSign (E.curve t) f g ∧
      strandSign (E.curve t) e g = -strandSign (E.curve t) e f
  /-- (2) "`T_H(x) = T_L(x)`", separately. -/
  transport_x : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef}))
  /-- (2) "`T_H(y) = T_L(y)`", separately. -/
  transport_y : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg}))
  /-- (2) "`T_H(z) = T_L(z)`", separately. -/
  transport_z : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg}))

/-! ### Unit PRE — the X₁-free presupposition fields of row 176 (`singleton_rows_present`,
`graphs_complementary`, `sign_branch`). -/

/-- Field `singleton_rows_present` of `ExtremeTransportData`, unconditionally: a singleton is
independent and lies in `𝓐(Q) = T` (`F1.compose_geom`). -/
theorem PRE_176_singleton_rows_present (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ j ∈ triangleCrossings (E.curve t) e f g, Q ∪ {j} ∈ CV.Ind (geomAt E t ht.1) := by
  intro t ht _ _ _ _ Q hQ hfull j hj
  exact PRE_union_mem_Ind_of_fullAvail hQ hfull (Finset.singleton_subset_iff.mpr hj)
    (PRE_mem_Ind_of_card_le_one _ (by rw [Finset.card_singleton]))

/-- Field `graphs_complementary` of `ExtremeTransportData` from
`LocalizationData.complement_on_triangle` (R-LOC-2 corollary, "The induced graph `G[T]` maps to its
complement in `T` across the wall"), the crossings identified across the wall by their carrying
edge pairs (`crossingTransport hs (xPair hef) = xPair hef'`, definitionally). -/
theorem PRE_176_graphs_complementary {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g})
      (hef' : IsCrossing (E.curve t') {e, f}) (heg' : IsCrossing (E.curve t') {e, g})
      (hfg' : IsCrossing (E.curve t') {f, g}),
    (CompleteLocal (geomAt E t ht.1) hef heg hfg ↔ EmptyLocal (geomAt E t' ht'.1) hef' heg' hfg') := by
  intro t t' ht ht' hop hef heg hfg hef' heg' hfg'
  have hs := hL.crossing_set_constant t t' ht ht'
  have key := hL.complement_on_triangle t t' ht ht' hop hs
  have hAB : EdgeAB (geomAt E t' ht'.1) hef' heg' ↔ ¬ EdgeAB (geomAt E t ht.1) hef heg :=
    key (xPair hef) (xPair heg) ((P1.mem_triangleSupports _).mpr (Or.inl rfl))
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))) (P1.xPair_ef_ne_eg hef heg hfg)
  have hAC : EdgeAC (geomAt E t' ht'.1) hef' hfg' ↔ ¬ EdgeAC (geomAt E t ht.1) hef hfg :=
    key (xPair hef) (xPair hfg) ((P1.mem_triangleSupports _).mpr (Or.inl rfl))
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))) (P1.xPair_ef_ne_fg hef heg hfg)
  have hBC : EdgeBC (geomAt E t' ht'.1) heg' hfg' ↔ ¬ EdgeBC (geomAt E t ht.1) heg hfg :=
    key (xPair heg) (xPair hfg) ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl)))
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))) (P1.xPair_eg_ne_fg hef heg hfg)
  unfold CompleteLocal EmptyLocal
  rw [hAB, hAC, hBC, not_not, not_not, not_not]

/-- Field `sign_branch` of `ExtremeTransportData`: the accepted
`GenericTableData.extreme_iff_alternating` read forwards (`IsAlternating sa sb sc` is
`sa = sc ∧ sb = -sa`). -/
theorem PRE_176_sign_branch {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hG : GenericTableData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg →
      strandSign (E.curve t) e f = strandSign (E.curve t) f g ∧
      strandSign (E.curve t) e g = -strandSign (E.curve t) e f :=
  fun t ht hef heg hfg hext => (hG.extreme_iff_alternating t ht hef heg hfg).mp hext

/-- **Row 176, R:extreme_transport** (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md). -/
theorem extreme_transport (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ := by
  sorry

/-! ## Row 177 (ORDER 174) — R:extreme_selected (R_EXTREME_SELECTED_COUPLE_PROOF.md, Statement)

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the extreme graph orbit.
Let `H` denote the side whose local graph is `K3`, let `L` denote the side whose local graph is empty,
and fix the outside support `Q`. … Full availability is a hypothesis of the statement, not merely
scene-setting: it says every member of `T={x,y,z}` is nonadjacent to `Q`, and therefore makes `Q union
T` an independent support on `L`. On `H`, `T` is not independent because its induced graph is `K3`.
… Write `T_nu(J)` for the complete X1 term of `Q union J` on side `nu`, with an absent row read as
zero. Then `T_H(empty) - T_L(empty) = T_L(xyz)` (2). Since `xyz` is absent on the `K3` side, (2) is
exactly the extreme selected empty/full complementary-couple identity. Equation (2), whose sides are
named by their graphs, is independent of coorientation." -/

/-- **The extreme selected empty/full couple**, clause by clause; `t` is the `K3` side `H`
(`CompleteLocal`), `t'` the opposite (empty) side `L` (sides named by their graphs; no coorientation
enters). -/
structure ExtremeSelectedData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Full availability … makes `Q union T` an independent support on `L`." -/
  full_present_on_empty : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      Q ∪ triangleCrossings (E.curve t) e f g ∈ CV.Ind (geomAt E t ht.1)
  /-- "On `H`, `T` is not independent because its induced graph is `K3`" ("`xyz` is absent on the
  `K3` side"; for every `Q`). -/
  full_absent_on_complete : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q : Finset (Crossing (E.curve t)),
      Q ∪ triangleCrossings (E.curve t) e f g ∉ CV.Ind (geomAt E t ht.1)
  /-- (2) "`T_H(empty) - T_L(empty) = T_L(xyz)`", "with an absent row read as zero". -/
  couple : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q - rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) =
        rowTerm hn (genericAt E t' ht'.1)
          (transportSupport hs Q ∪ triangleCrossings (E.curve t') e f g)

/-! ### Unit PRE — the X₁-free presupposition fields of row 177 (`full_present_on_empty`,
`full_absent_on_complete`). -/

/-- Field `full_present_on_empty` of `ExtremeSelectedData`, unconditionally: `T` is independent on
the empty-graph side and `T ⊆ 𝓐(Q) = T` (`F1.compose_geom`). -/
theorem PRE_177_full_present_on_empty (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      Q ∪ triangleCrossings (E.curve t) e f g ∈ CV.Ind (geomAt E t ht.1) := by
  intro t ht hef heg hfg hL Q hQ hfull
  exact PRE_union_mem_Ind_of_fullAvail hQ hfull (Finset.Subset.refl _)
    (PRE_mem_Ind_of_empty hL (Finset.Subset.refl _))

/-- Field `full_absent_on_complete` of `ExtremeSelectedData`, unconditionally: `x_ef, x_eg ∈ Q ∪ T`
are distinct and interlace on the `K3` side (edge `ab`). -/
theorem PRE_177_full_absent_on_complete (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    CompleteLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q : Finset (Crossing (E.curve t)),
      Q ∪ triangleCrossings (E.curve t) e f g ∉ CV.Ind (geomAt E t ht.1) := by
  intro t ht hef heg hfg hK Q hind
  have ha : xPair hef ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
  have hb : xPair heg ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
  exact (CV.mem_Ind_iff _ _).mp hind _ (Finset.mem_union_right _ ha) _
    (Finset.mem_union_right _ hb) (P1.xPair_ef_ne_eg hef heg hfg) hK.1

/-- **Row 177, R:extreme_selected** (R_EXTREME_SELECTED_COUPLE_PROOF.md). -/
theorem extreme_selected (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ := by
  sorry

/-! ## Row 178 (ORDER 185) — R:cv_theorem (R_ASSEMBLY_SPEC.md (3)–(4) and the closing paragraph;
OPEN_WORK.md item 4; CV ax:R)

Specified text: "The finite bijection just established partitions the exact state sum, so
`X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)` (3). … The local proof task, for each such `Q`, is
`Φ_+(Q) = Φ_-(Q)` (4). … Finally sum the proved identities (4) over the same finite outside-support
set in (3). Equality is preserved by finite summation, giving exactly CV ax:R. Review that all source
event-domain clauses survived the localization and assembly. Apply the independently proved bridge
afterwards." OPEN_WORK.md item 4: "Sum all fibre identities to prove CV ax:R on its entire printed
simple/transversal forced-bundle domain." Shape (DECISION_FINAL.md R6): `RProof.cv_R : CV.hyp_R`; the
R lane's own product is the punctured-neighbourhood form `CvRNear` (bundle `CvTheoremData`), and
`cv_R = cv_R_near + prop:chamberinv (ii)` (each side of the event lies in one CV chamber,
`CV.Event.sideChamber`): `hyp_R_of_near_of_chamberinv` below, PROVED. -/

/-- **The CV theorem in its punctured (R-lane) form**, clause by clause, for the event `E` and the
radius `δ`. Every field except `fibre_identities` is PROVED from the accepted rows 164/171
(`CvTheoremData.of_fibre_identities`). -/
structure CvTheoremData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- (3) at the summand `F_±`: "`X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)`" (the X₁ specialisation of
  `FibrePartitionData.state_sum_partition`; `X1_eq_sum_fibreTerm`). -/
  state_sum : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    CV.X1 hn (E.curve t) (genericAt E t ht.1) =
      ∑ Q ∈ outsideSupports (geomAt E t ht.1) e f g, fibreTerm hn E e f g t ht.1 Q
  /-- "sum … over the same finite outside-support set in (3)": `Ind(G[W])` is the same set on the two
  sides, by the carrying edge pairs (`FibrePartitionData.graph_on_W_same`;
  `outsideSupports_transport`). -/
  outside_supports_transport : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
      outsideSupports (geomAt E t' ht'.1) e f g =
        (outsideSupports (geomAt E t ht.1) e f g).map (supportEmb hs)
  /-- "the proved identities (4)": `Φ_+(Q) = Φ_-(Q)` for every outside independent `Q` (availability
  `0, 1` by row 170; availability `3` by rows 168, 172, 173, 174 in the generic orbit and 168, 175,
  176, 177 in the extreme orbit, through `FibrePartitionData.avail_card`). -/
  fibre_identities : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q)
  /-- "Finally sum the proved identities (4) over the same finite outside-support set in (3). Equality
  is preserved by finite summation, giving exactly CV ax:R": `X₁` agrees on the two punctured sides
  within `δ`. -/
  near : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
      CV.X1 hn (E.curve t) (genericAt E t ht.1) = CV.X1 hn (E.curve t') (genericAt E t' ht'.1)

/-- The R lane's punctured form of CV:ax:R (DECISION_FINAL.md R6's "`RProof.cv_R_near`"): for every
simple transversal RIII event, `CvTheoremData` on some punctured neighbourhood. -/
def CvRNear : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
    E.IsSimpleRIII e f g h3 h4e h4f h4g →
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ CvTheoremData hn E e f g δ

/-- CV:prop:chamberinv (ii) (d1_setup.tex:932–940), "`X₁` is constant on each chamber", in the form
the CV row 147 (ii) will take (`CV.X1_eq_of_mem_chamber_of_pieceHomfly` proves it modulo
`PieceHomflyTransported`). -/
def ChamberInvII : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : LabelledTuple n) (hP : CV.Generic P) (hQ : CV.Generic Q),
    Q ∈ CV.chamber P → CV.X1 hn P hP = CV.X1 hn Q hQ

/-- **Row 178, R:cv_theorem: `RProof.cv_R : CV.hyp_R`** — CV:ax:R as a theorem in its printed
chamber-value form, "on its entire printed simple/transversal forced-bundle domain" (fixed name,
work/lean/axiom-policy.json; consumed by `Bridge.sm_R` at the event `Bridge.eventOfTriple hn g h`,
see `smR_shape_of_hyp_R`). Proof shape (R6): `hyp_R_of_near_of_chamberinv cv_R_near chamberinv_ii`,
where `cv_R_near : CvRNear` is `CvTheoremData.of_fibre_identities` on the accepted rows 164/171 and
the fibre identities assembled from rows 168–177 (availability cases by
`FibrePartitionData.avail_card`). -/
theorem cv_R : CV.hyp_R := by
  sorry

/-! ### The finite summation of the fibre identities (R_ASSEMBLY_SPEC.md, last paragraph) and the
consumer chain — PROVED -/

section Assembly

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

omit [NeZero n] in
/-- Reading a support back and forth across the wall is the identity (`crossingTransport` is
support-preserving). -/
theorem transportSupport_transportSupport_symm {P Q : LabelledTuple n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (S : Finset (Crossing Q)) :
    transportSupport hs (transportSupport (fun s => (hs s).symm) S) = S := by
  unfold transportSupport
  rw [Finset.map_map]
  have : (crossingTransport (fun s => (hs s).symm)).toEmbedding.trans
      (crossingTransport hs).toEmbedding = Function.Embedding.refl _ :=
    Function.Embedding.ext fun x => Subtype.ext rfl
  rw [this, Finset.map_refl]

theorem OppositeSides.symm {t t' : E.Parameter} (h : OppositeSides E t t') : OppositeSides E t' t := by
  unfold OppositeSides at *
  rwa [mul_comm]

/-- "`Q` is independent in the outside graph" on both sides: `Ind(G[W])` is carried across the wall
(`FibrePartitionData.graph_on_W_same`; the triangle is carried by its supports). -/
theorem mem_outsideSupports_transport (hF : FibrePartitionData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) :
    transportSupport hs Q ∈ outsideSupports (geomAt E t' ht'.1) e f g := by
  rw [F1.mem_outsideSupports] at hQ ⊢
  obtain ⟨hind, hdisj⟩ := hQ
  have hT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := fun x hx h =>
    Finset.disjoint_left.mp hdisj hx ((F1.mem_triangleCrossings e f g x).mpr h)
  refine ⟨?_, ?_⟩
  · rw [CV.mem_Ind_iff] at hind ⊢
    intro x' hx' y' hy' hne
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hy'
    have h := hF.graph_on_W_same t t' ht ht' hop hs x y (hT x hx) (hT y hy)
    rw [Equiv.coe_toEmbedding]
    rw [h]
    exact hind x hx y hy (fun hxy => hne (by rw [hxy]))
  · rw [Finset.disjoint_left]
    intro x' hx' hxT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hx'
    have h1 := (F1.mem_triangleCrossings e f g ((crossingTransport hs).toEmbedding x)).mp hxT
    exact hT x hx h1

/-- "the same finite outside-support set" on the two sides: `Ind(G[W])` at `t'` is the image of
`Ind(G[W])` at `t` under the support transport. PROVED from the accepted row 171 — the
`outside_supports_transport` clause of `CvTheoremData`. -/
theorem outsideSupports_transport (hF : FibrePartitionData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s) :
    outsideSupports (geomAt E t' ht'.1) e f g =
      (outsideSupports (geomAt E t ht.1) e f g).map (supportEmb hs) := by
  ext Q'
  rw [Finset.mem_map]
  constructor
  · intro hQ'
    refine ⟨transportSupport (fun s => (hs s).symm) Q',
      mem_outsideSupports_transport hF ht' ht hop.symm (fun s => (hs s).symm) hQ', ?_⟩
    rw [supportEmb_apply]
    exact transportSupport_transportSupport_symm hs Q'
  · rintro ⟨Q, hQ, rfl⟩
    rw [supportEmb_apply]
    exact mem_outsideSupports_transport hF ht ht' hop hs hQ

/-- **"Finally sum the proved identities (4) over the same finite outside-support set in (3).
Equality is preserved by finite summation"**: from (3) on both sides (`X1_eq_sum_fibreTerm`) and
the fibre identities (4) at one pair of opposite parameters, `X₁` agrees there. PROVED. -/
theorem near_of_fibre_identities (hF : FibrePartitionData E e f g δ) (hn : 3 ≤ n)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hfib : ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q)) :
    CV.X1 hn (E.curve t) (genericAt E t ht.1) = CV.X1 hn (E.curve t') (genericAt E t' ht'.1) := by
  rw [X1_eq_sum_fibreTerm hF hn t ht, X1_eq_sum_fibreTerm hF hn t' ht',
    outsideSupports_transport hF ht ht' hop hs, Finset.sum_map]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [supportEmb_apply]
  exact hfib Q hQ

/-- The bundle of row 178 from the accepted rows 164/171 and the fibre identities of rows 168–177:
`state_sum`, `outside_supports_transport` and `near` are PROVED; only `fibre_identities` is
supplied. -/
theorem CvTheoremData.of_fibre_identities (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hF : FibrePartitionData E e f g δ)
    (hfib : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
      OppositeSides E t t' →
      ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
      ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
        fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q)) :
    CvTheoremData hn E e f g δ where
  state_sum := fun t ht => X1_eq_sum_fibreTerm hF hn t ht
  outside_supports_transport := fun _ _ ht ht' hop hs => outsideSupports_transport hF ht ht' hop hs
  fibre_identities := hfib
  near := fun t t' ht ht' hop =>
    near_of_fibre_identities hF hn ht ht' hop (hL.crossing_set_constant t t' ht ht')
      (hfib t t' ht ht' hop _)

end Assembly

/-- **R6, the relation `cv_R = cv_R_near + chamberinv(ii)`**, PROVED: the punctured form and the
chamber constancy of `X₁` give the printed all-parameters form, since each side image
`E.curve ((0, radius))`, `E.curve ((−radius, 0))` lies in one CV chamber (def:event;
`CV.Event.curve_mem_sideChamber_pos/neg`, `CV.chamber_eq_of_mem`). -/
theorem hyp_R_of_near_of_chamberinv (hnear : CvRNear) (hch : ChamberInvII) : CV.hyp_R := by
  intro n _ hn E e f g h3 h4e h4f h4g hE tp tm hp hm
  obtain ⟨δ, hδ, hδr, hD⟩ := hnear n hn E e f g h3 h4e h4f h4g hE
  have hr := E.radius_pos
  have hτ0 : 0 < δ / 2 := by positivity
  have hτδ : δ / 2 < δ := by linarith
  have hτr : δ / 2 < E.radius := by linarith
  let tp' : E.Parameter := ⟨δ / 2, by constructor <;> linarith⟩
  let tm' : E.Parameter := ⟨-(δ / 2), by constructor <;> linarith⟩
  have hp' : Punctured E δ tp' := ⟨hτ0.ne', by show |δ / 2| < δ; rw [abs_of_pos hτ0]; exact hτδ⟩
  have hm' : Punctured E δ tm' :=
    ⟨neg_ne_zero.mpr hτ0.ne', by show |-(δ / 2)| < δ; rw [abs_neg, abs_of_pos hτ0]; exact hτδ⟩
  have hop : OppositeSides E tp' tm' := by
    show δ / 2 * -(δ / 2) < 0
    nlinarith
  have hnear' := hD.near tp' tm' hp' hm' hop
  have h1 : E.curve tp ∈ CV.chamber (E.curve tp') := by
    have a := E.curve_mem_sideChamber_pos tp hp
    have b := E.curve_mem_sideChamber_pos tp' hτ0
    unfold CV.Event.sideChamber at a b
    rw [CV.chamber_eq_of_mem b]
    exact a
  have h2 : E.curve tm ∈ CV.chamber (E.curve tm') := by
    have a := E.curve_mem_sideChamber_neg tm hm
    have b := E.curve_mem_sideChamber_neg tm' (by show -(δ / 2) < 0; linarith)
    unfold CV.Event.sideChamber at a b
    rw [CV.chamber_eq_of_mem b]
    exact a
  calc CV.X1 hn (E.curve tp) (E.generic_punctured tp hp.ne')
      = CV.X1 hn (E.curve tp') (genericAt E tp' hp'.1) :=
        (hch n hn _ _ (genericAt E tp' hp'.1) (E.generic_punctured tp hp.ne') h1).symm
    _ = CV.X1 hn (E.curve tm') (genericAt E tm' hm'.1) := hnear'
    _ = CV.X1 hn (E.curve tm) (E.generic_punctured tm hm.ne) :=
        hch n hn _ _ (genericAt E tm' hm'.1) (E.generic_punctured tm hm.ne) h2

/-- **How `Bridge.sm_R` consumes `RProof.cv_R`** (BRIDGE.md §3, (19)–(21); DECISION_FINAL.md R6/R7):
with Bridge:B4's pointwise dictionary `X₁ = C` on SM-generic polygons (BRIDGE.md (17)), `CV.hyp_R` at
the CV event `Bridge.eventOfTriple hn g h` of an SM simple triple germ (Bridge:B1–B3,
`isSimpleRIII_eventOfTriple`) gives the printed SM hyp:R "At every simple triple wall, `C(P₊) = C(P₋)`"
(sm-4-knotlaws.tex:1149–1150), here at every side parameter `t`. The germ is named by its increasing
representatives (`Bridge.exists_sorted_tripleAt`), which does not change the event. This is the shape
of `Bridge.sm_R`, not the fixed row itself. PROVED (consistency check of the R lane with the bridge). -/
theorem smR_shape_of_hyp_R (hcv : CV.hyp_R)
    (hB4 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P),
      CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP) :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n), g.TripleAt e f k →
      ∀ t : g.SideParameter,
        SM.cornerStateSum hn (g.sideTuple true t).2 = SM.cornerStateSum hn (g.sideTuple false t).2 := by
  intro n _ hn g e f k h t
  obtain ⟨e', f', k', -, hef, hfk, h'⟩ := Bridge.exists_sorted_tripleAt g h
  have hE := isSimpleRIII_eventOfTriple hn g h' hef hfk
  have hp : 0 < (g.sideTime true t).val := by
    show 0 < (if (true : Bool) = true then _ else _ : g.Parameter).val
    simp only [ite_true]
    exact t.2.1
  have hm : (g.sideTime false t).val < 0 := by
    show (if (false : Bool) = true then _ else _ : g.Parameter).val < 0
    simp only [Bool.false_eq_true, ite_false]
    exact neg_neg_iff_pos.mpr t.2.1
  have key := hcv n hn (Bridge.eventOfTriple hn g h') e' f' k' _ _ _ _ hE
    (g.sideTime true t) (g.sideTime false t) hp hm
  exact (hB4 n hn _ (g.sideTuple true t).2).symm.trans
    (key.trans (hB4 n hn _ (g.sideTuple false t).2))

end RProof
