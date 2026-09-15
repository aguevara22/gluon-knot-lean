import RProof.Cores
import CV.X1
import CV.ChamberInvII
import CV.PieceHomflyTransport
import CV.SelectorA
import SM.CornerStateSum
import CV.GroupedKnot

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

/-! ### Assembler note (R-lane X₁ rows, wave 1, 2026-09-14)

`RLaneX1_Assembled.lean` = `Statements_FINAL.lean` + the proved hunks of the units `U_SEL` (row 172,
`RProof.generic_selector`, proved; `section SEL`), `U_PRE` (the twelve X₁-free presupposition field lemmas
`PRE_<row>_<field>` of rows 170, 173, 175, 176, 177; `section PREHelpers`) and `U_A2` (the assembly
`A2_fibre_identities` → `A2_cvTheoremData_of_rows` → `A2_cvRNear_of_rows`; `section A2`). Relative to the
frozen statement file every change is a pure insertion except the proof body of `generic_selector`
(`diff Statements_FINAL.lean RLaneX1_Assembled.lean | grep '^<'` prints that one line only); no statement,
definition, name, docstring or import was changed. The other eight row theorems (`exterior`,
`availability_zero_one`, `generic_transport`, `generic_selected`, `extreme_pair_zero`, `extreme_transport`,
`extreme_selected`, `cv_R`) keep their placeholder proofs here; the portable library file
`RLaneX1_Statements.lean` omits exactly those eight declarations and nothing else. -/

/-! ### Assembler note (R-lane X₁ rows, wave 2, 2026-09-14)

`RLaneX1_Assembled2.lean` = `RLaneX1_Assembled.lean` (wave 1) + the hunks of the two wave-2 units:
`W2_EXT` (row 168, `RProof.exterior`, PROVED; `section EXT`, 96 `EXT_` declarations, inserted between the
frozen `ExteriorData` bundle and the row theorem) and `W2_AV` (row 170, `RProof.availability_zero_one`,
PROVED; `section AV` + the six top-level lemmas `AV_rowTerm_eq_of_summandTransport`, `AV_summandTransport`,
`AV_170_summand_transport`, `AV_170_summands_agree`, `AV_170_fibre_identity`, `AV_ne_of_remote`, inserted
between the frozen `AvailabilityZeroOneData` bundle and the row theorem), plus the one import both units
added (`import CV.PieceHomflyTransport`). Relative to the wave-1 file every change is a pure insertion
except the two proof bodies (`diff RLaneX1_Assembled.lean RLaneX1_Assembled2.lean | grep '^<'` prints
exactly two `sorry` lines); no statement, definition, name, docstring or existing import was changed.
The six still-open row theorems (`generic_transport`, `generic_selected`, `extreme_pair_zero`,
`extreme_transport`, `extreme_selected`, `cv_R`) keep their placeholder proofs here; the portable
wave-2 module `RLaneX1Rows2.lean` (= `import RProof.X1Rows` + only the new material) omits them. -/

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

/-! ## Unit EXT — proof lane of row 168, R:exterior (2026-09-14)

Helper lemmas (prefix `EXT_`) for the three fields of `ExteriorData`, placed before the row theorem.
Nothing in the fixed statements is changed. Structure (NOTES_FINAL §2, R-EXTERIOR-1 proof §1–§4):
* `EXT_sameCycle_of_conj_on`, `EXT_block`, `EXT_corr*` — the carrier correspondence: on a set of marks
  invariant under one smoothing successor on which the other successor agrees (through an identification
  of marks), the cycles correspond (§1 "exterior carriers are fiber-stable", and §4 "erasing the six `T`
  visits gives the same marked traversal word on both sides");
* `EXT_markList_map`, `EXT_cornerList_map`, `EXT_cornerCount_eq`, `EXT_cornerMark_eq`,
  `EXT_cornerPolygon_eq` — mark lists, corner lists and the corner polygon are carried;
* `EXT_carrierCrossings_map`, `EXT_walk_transfer`, `EXT_PieceSetting`, `EXT_mem_labels_iff`,
  `EXT_pieceMap*`, `EXT_piecesOn_prod/sum`, `EXT_pieceSetting` — retained crossings and residual pieces
  are carried piece for piece (§2 "exterior residual pieces are fiber-stable", lem:carriers (iv) as
  `EXT_closed`);
* `EXT_weight_eq`, `EXT_carrierR_eq`, `EXT_groupedWrithe_eq`, `EXT_groupedPoly_eq`, `EXT_Omega1_eq`,
  `EXT_pieceHomfly_eq_of_labels`, `EXT_exteriorFactor_eq` — `wt`, `R`, `w_{S,L}`, `P_{S,L}`, `Ω₁` and the
  exterior factor are carried (§3), the piece polynomial at one polygon by choice independence
  (`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`, lem:pieceintrinsic);
* `EXT_exteriorFactor_eq_base`, `EXT_168_independent_of_A` — the same-polygon instance `Q ∪ A` vs `Q`
  (`geoSmoothingSuccessor_union_of_disjoint`) and the field `independent_of_A`;
* `EXT_key_lt_wall`, `EXT_markSucc_wall`, `EXT_succ_wall`, `EXT_turn_wall` — the wall: traversal order of
  non-bundle pairs (`ExactTriangleVisitOrders`, R-LOC-2 (2)–(3)), the successor of a good mark, the
  corner turns (`turn_vertex_of_traced`, `turn_visit_of_traced`);
* `EXT_GuardAt`, `EXT_exists_guardRadius` — lem:guardconst for `G1`/`G5` uniformly over the finitely many
  members, giving wall-invariant turn signs, crossing signs and divide signs;
* `EXT_homfly_wall`, `EXT_pieceHomfly_wall` — the identity on parent visits is a record isomorphism
  between the positive lifts on the two sides (CV:def:record (a)–(d), `recordIsoOfData`), so the piece
  polynomials agree by the accepted `gausscode_polynomial` (§4 "ax:gausscode gives the same oriented link
  and ax:homfly the same polynomial");
* `EXT_seg`, `EXT_familyEdge`, `EXT_pa_lt_pb_all`, `EXT_family_regular`, `EXT_family_continuous`,
  `EXT_rotation_wall` — the corner polygon of an exterior carrier deforms continuously and regularly
  through the wall along `t ↦ P(t)` (every edge a positive multiple of a polygon edge, corners at
  `G1 ≠ 0` / `G5 ≠ 0`), so its rotation number is constant (`rotationNumber_family_constant`; §4 "for
  rotation … lem:turnlift(ii)");
* `EXT_exteriorFactor_wall`, `EXT_168_wall_invariant`, `EXT_168_factorization` — the fields. -/

section EXT

open SM.Carrier

section EXTCore

variable {P P' : LabelledTuple n}

/-- Conjugation on an invariant set: for `a` in a set `U` invariant under `f`, on which `g ∘ e = e ∘ f`,
the `g`-cycle of `e a` is the image of the `f`-cycle of `a`. -/
theorem EXT_sameCycle_of_conj_on {α β : Type*} (f : Equiv.Perm α) (g : Equiv.Perm β) (e : α ≃ β)
    (U : Set α) (hU : Set.BijOn f U U) (h : ∀ a ∈ U, g (e a) = e (f a)) :
    ∀ a ∈ U, ∀ b, g.SameCycle (e a) (e b) ↔ f.SameCycle a b := by
  intro a ha b
  have hconj : ∀ x, (e.permCongr f) (e x) = e (f x) := by
    intro x
    simp [Equiv.permCongr_apply]
  have h1 := sameCycle_of_equiv_conj f (e.permCongr f) e hconj a b
  have hbij : Set.BijOn (e.permCongr f) (e '' U) (e '' U) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [hconj]
      exact ⟨f x, hU.mapsTo hx, rfl⟩
    · intro x _ y _ hxy
      exact (e.permCongr f).injective hxy
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hfx⟩ := hU.surjOn hy
      exact ⟨e x, ⟨x, hx, rfl⟩, by rw [hconj, hfx]⟩
  have heq : Set.EqOn (e.permCongr f) g (e '' U) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hconj, h x hx]
  exact (sameCycle_congr_of_eqOn_bijOn (e.permCongr f) g (e '' U) hbij heq (e a) ⟨a, ha, rfl⟩
    (e b)).trans h1

/-- A carrier avoids the bad marks: every mark it owns is good. -/
def EXT_Avoids (hP : CrossingGeometry P) (S : Finset (Crossing P)) (Good : Mark P → Prop)
    (q : GeoComponent hP S) : Prop :=
  ∀ a, geoOwner hP S a = q → Good a

/-- The block lemma: if the two smoothing successors commute with the identification `e` at every good
mark with good successor, then for a mark `a` of a good-avoiding carrier the images of the marks of the
carrier of `a` are exactly the marks of the carrier of `e a`. -/
theorem EXT_block (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) (a : Mark P) (ha : geoOwner hP S a = q)
    (b : Mark P) :
    geoOwner hP' S' (e a) = geoOwner hP' S' (e b) ↔ geoOwner hP S a = geoOwner hP S b := by
  rw [geoOwner_eq_iff, geoOwner_eq_iff]
  refine EXT_sameCycle_of_conj_on _ _ e {m | geoOwner hP S m = q}
    (geoSmoothingSuccessor_bijOn_owner hP S q) ?_ a ha b
  intro m hm
  refine hcomm m (hq m hm) (hq _ ?_)
  rw [geoOwner_successor]
  exact hm

/-- The corresponding carrier: the carrier of the image of any mark of `q`. -/
noncomputable def EXT_corr (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S) :
    GeoComponent hP' S' :=
  geoOwner hP' S' (e (Classical.choose (geoOwner_surjective hP S q)))

theorem EXT_corr_iff (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) (b : Mark P) :
    geoOwner hP' S' (e b) = EXT_corr hP hP' e S S' q ↔ geoOwner hP S b = q := by
  have ha := Classical.choose_spec (geoOwner_surjective hP S q)
  unfold EXT_corr
  rw [eq_comm, EXT_block hP hP' e S S' Good hcomm q hq _ ha b, ha, eq_comm]

theorem EXT_corr_iff' (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) (b' : Mark P') :
    geoOwner hP' S' b' = EXT_corr hP hP' e S S' q ↔ geoOwner hP S (e.symm b') = q := by
  have h := EXT_corr_iff hP hP' e S S' Good hcomm q hq (e.symm b')
  rwa [Equiv.apply_symm_apply] at h

/-- The corresponding carrier avoids the bad marks of `P'` (the images of the bad marks). -/
theorem EXT_corr_avoids (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) :
    EXT_Avoids hP' S' (fun b' => Good (e.symm b')) (EXT_corr hP hP' e S S' q) := by
  intro b' hb'
  exact hq _ ((EXT_corr_iff' hP hP' e S S' Good hcomm q hq b').mp hb')

/-- `EXT_corr` is inverted by the corresponding map in the other direction. -/
theorem EXT_corr_corr (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (Good : Mark P → Prop)
    (hcomm : ∀ a, Good a → Good (geoSmoothingSuccessor hP S a) →
      geoSmoothingSuccessor hP' S' (e a) = e (geoSmoothingSuccessor hP S a))
    (hcomm' : ∀ b', Good (e.symm b') → Good (e.symm (geoSmoothingSuccessor hP' S' b')) →
      geoSmoothingSuccessor hP S (e.symm b') = e.symm (geoSmoothingSuccessor hP' S' b'))
    (q : GeoComponent hP S) (hq : EXT_Avoids hP S Good q) :
    EXT_corr hP' hP e.symm S' S (EXT_corr hP hP' e S S' q) = q := by
  have ha := Classical.choose_spec (geoOwner_surjective hP S q)
  set a₀ := Classical.choose (geoOwner_surjective hP S q)
  have h1 : geoOwner hP' S' (e a₀) = EXT_corr hP hP' e S S' q :=
    (EXT_corr_iff hP hP' e S S' Good hcomm q hq a₀).mpr ha
  have h2 := EXT_corr_iff hP' hP e.symm S' S (fun b' => Good (e.symm b')) hcomm'
    (EXT_corr hP hP' e S S' q) (EXT_corr_avoids hP hP' e S S' Good hcomm q hq) (e a₀)
  rw [Equiv.symm_apply_apply] at h2
  exact (h2.mpr h1).symm.trans ha

end EXTCore


section EXTLists

variable {P P' : LabelledTuple n}

/-- The marks of a carrier are carried onto the marks of the corresponding carrier, in inherited order,
provided the traversal order of its marks is carried (`hkey`): both lists are the strictly increasing
enumerations of the same set of marks. -/
theorem EXT_markList_map (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hblock : ∀ b, geoOwner hP' S' (e b) = q' ↔ geoOwner hP S b = q)
    (hkey : ∀ a b, geoOwner hP S a = q → geoOwner hP S b = q →
      (geoMarkKey hP a < geoMarkKey hP b ↔ geoMarkKey hP' (e a) < geoMarkKey hP' (e b))) :
    (geoComponentMarkList hP S q).map e = geoComponentMarkList hP' S' q' := by
  classical
  have hnodup : ((geoComponentMarkList hP S q).map e).Nodup :=
    (geoComponentMarkList_nodup hP S q).map e.injective
  have hperm : ((geoComponentMarkList hP S q).map e).Perm (geoComponentMarkList hP' S' q') := by
    rw [List.perm_ext_iff_of_nodup hnodup (geoComponentMarkList_nodup hP' S' q')]
    intro x
    rw [List.mem_map, mem_geoComponentMarkList]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hblock a).mpr ((mem_geoComponentMarkList hP S q a).mp ha)
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [mem_geoComponentMarkList, ← hblock, e.apply_symm_apply]
      exact hx
  have hsorted' : (geoComponentMarkList hP' S' q').Pairwise
      (fun a b => geoMarkKey hP' a ≤ geoMarkKey hP' b) :=
    (geoMarkList_sorted hP').filter _
  have hsorted : ((geoComponentMarkList hP S q).map e).Pairwise
      (fun a b => geoMarkKey hP' a ≤ geoMarkKey hP' b) := by
    rw [List.pairwise_map]
    have h1 : (geoComponentMarkList hP S q).Pairwise (fun a b => geoMarkKey hP a ≤ geoMarkKey hP b) :=
      (geoMarkList_sorted hP).filter _
    have h2 : (geoComponentMarkList hP S q).Pairwise (fun a b => a ≠ b) :=
      geoComponentMarkList_nodup hP S q
    refine List.Pairwise.imp_of_mem ?_ (h1.and h2)
    intro a b ha hb hab
    have hlt : geoMarkKey hP a < geoMarkKey hP b :=
      lt_of_le_of_ne hab.1 (fun h => hab.2 (geoMarkKey_injective hP h))
    exact ((hkey a b ((mem_geoComponentMarkList hP S q a).mp ha)
      ((mem_geoComponentMarkList hP S q b).mp hb)).mp hlt).le
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ hab hba => geoMarkKey_injective hP' (le_antisymm hab hba)) hsorted hsorted' hperm

/-- The corner list is carried once the mark list is and corners correspond. -/
theorem EXT_cornerList_map (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hlist : (geoComponentMarkList hP S q).map e = geoComponentMarkList hP' S' q')
    (hcorner : ∀ a, geoOwner hP S a = q → (IsTrueCorner S' (e a) ↔ IsTrueCorner S a)) :
    (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q' := by
  unfold geoComponentCornerList
  rw [← hlist, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x hx
  simp only [Function.comp]
  exact decide_eq_decide.mpr (hcorner x ((mem_geoComponentMarkList hP S q x).mp hx)).symm

theorem EXT_cornerCount_eq (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q') :
    geoCornerCount hP' S' q' = geoCornerCount hP S q := by
  unfold geoCornerCount
  rw [← hcl, List.length_map]

theorem EXT_cornerMark_eq (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q')
    (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP' S' q'
        (Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' e S S' q q' hcl).symm) k) =
      e (geoCornerMark hP S q k) := by
  have hc := EXT_cornerCount_eq hP hP' e S S' q q' hcl
  have hlen : k.val < (geoComponentCornerList hP' S' q').length := by
    rw [← hcl, List.length_map]
    exact ZMod.val_lt k
  have h3 : k.val < ((geoComponentCornerList hP S q).map e).length := by
    rw [List.length_map]
    exact ZMod.val_lt k
  unfold geoCornerMark
  refine (geo_getElem_congr _ _ rfl _ _ _ hlen (geo_zmod_val_cast hc.symm k)).trans ?_
  refine (geo_getElem_congr _ _ hcl.symm _ _ hlen h3 rfl).trans ?_
  exact List.getElem_map _

theorem EXT_cornerMark_eq' (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q')
    (j : ZMod (geoCornerCount hP' S' q')) :
    geoCornerMark hP' S' q' j =
      e (geoCornerMark hP S q
        (Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' e S S' q q' hcl)) j)) := by
  have h := EXT_cornerMark_eq hP hP' e S S' q q' hcl
    (Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' e S S' q q' hcl)) j)
  rwa [geo_zmod_cast_cast (EXT_cornerCount_eq hP hP' e S S' q q' hcl) j] at h

/-- The corner polygon of the corresponding carrier is the polygon of the images of the corner marks,
recast along the equal corner counts. -/
theorem EXT_cornerPolygon_eq (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (e : Mark P ≃ Mark P')
    (S : Finset (Crossing P)) (S' : Finset (Crossing P')) (q : GeoComponent hP S)
    (q' : GeoComponent hP' S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP' S' q') :
    geoCornerPolygon hP' S' q' =
      geoRecast (EXT_cornerCount_eq hP hP' e S S' q q' hcl)
        (fun k => traversalEvaluation P' (geoMarkPosition hP' (e (geoCornerMark hP S q k)))) := by
  funext j
  show traversalEvaluation P' (geoMarkPosition hP' (geoCornerMark hP' S' q' j)) = _
  rw [EXT_cornerMark_eq' hP hP' e S S' q q' hcl j]
  rfl

/-- Same polygon, identity identification: the corner polygon is literally the recast corner polygon. -/
theorem EXT_cornerPolygon_eq_self (hP : CrossingGeometry P) (e : Mark P ≃ Mark P) (he : ∀ a, e a = a)
    (S S' : Finset (Crossing P)) (q : GeoComponent hP S) (q' : GeoComponent hP S')
    (hcl : (geoComponentCornerList hP S q).map e = geoComponentCornerList hP S' q') :
    geoCornerPolygon hP S' q' =
      geoRecast (EXT_cornerCount_eq hP hP e S S' q q' hcl) (geoCornerPolygon hP S q) := by
  rw [EXT_cornerPolygon_eq hP hP e S S' q q' hcl]
  congr 1
  funext k
  rw [he]
  rfl

end EXTLists

section EXTCrossings

variable {P P' : LabelledTuple n}

/-- The retained crossings of corresponding carriers correspond. -/
theorem EXT_carrierCrossings_map (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hblock : ∀ b, geoOwner hP' S' (markTransport hs b) = q' ↔ geoOwner hP S b = q)
    (hsel : ∀ x : Crossing P, (∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q) →
      (crossingTransport hs x ∈ S' ↔ x ∈ S)) :
    geoCarrierCrossings hP' S' q' =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding := by
  ext x'
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_geoCarrierCrossings, mem_geoCarrierCrossings]
  have hvis : (∀ w : Visit P', w.1 = crossingTransport hs x → geoOwner hP' S' (Sum.inr w) = q') ↔
      (∀ v : Visit P, v.1 = x → geoOwner hP S (Sum.inr v) = q) := by
    constructor
    · intro h v hv
      have := h (visitTransport hs v) (by rw [visitTransport_crossing, hv])
      rw [← markTransport_visit, hblock] at this
      exact this
    · intro h w hw
      obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
      rw [visitTransport_crossing] at hw
      rw [← markTransport_visit, hblock]
      exact h v ((crossingTransport hs).injective hw)
  rw [hvis]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun hx => h1 ((hsel x h2).mpr hx), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun hx => h1 ((hsel x h2).mp hx), h2⟩

/-- A walk of the induced graph on `U` starting in a closed set `X` stays in `X` and is carried to a
walk of the induced graph on `U'`. -/
theorem EXT_walk_transfer {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')
    (U : Set V) (U' : Set V') (X : Set V) (φ : V → V')
    (hXU' : ∀ c ∈ X, φ c ∈ U')
    (hadj : ∀ c ∈ X, ∀ d ∈ X, G.Adj c d → G'.Adj (φ c) (φ d))
    (hclosed : ∀ c ∈ X, ∀ d ∈ U, G.Adj c d → d ∈ X) :
    ∀ (a b : ↑U) (_ : (G.induce U).Walk a b) (ha : a.val ∈ X),
      ∃ hb : b.val ∈ X, (G'.induce U').Reachable ⟨φ a.val, hXU' _ ha⟩ ⟨φ b.val, hXU' _ hb⟩ := by
  intro a b w
  induction w with
  | nil =>
    intro ha
    exact ⟨ha, SimpleGraph.Reachable.refl _⟩
  | @cons a a₁ b h w ih =>
    intro ha
    have hadj₁ : G.Adj a.val a₁.val := h
    have ha₁ : a₁.val ∈ X := hclosed _ ha _ a₁.property hadj₁
    obtain ⟨hb, hr⟩ := ih ha₁
    refine ⟨hb, SimpleGraph.Reachable.trans ?_ hr⟩
    exact SimpleGraph.Adj.reachable (hadj _ ha _ ha₁ hadj₁)

/-- Membership in the piece of `c`, read through reachability in the residual graph. -/
theorem EXT_mem_pieceLabels_pieceOf (hP : CrossingGeometry P) (S : Finset (Crossing P)) {c : Crossing P}
    (hc : c ∈ CV.U hP S) (d : Crossing P) :
    d ∈ CV.pieceLabels hP S (CV.pieceOf hP S c hc) ↔
      ∃ hd : d ∈ CV.U hP S, (CV.residualGraph hP S).Reachable ⟨c, hc⟩ ⟨d, hd⟩ := by
  rw [CV.mem_pieceLabels]
  constructor
  · rintro ⟨hd, h⟩
    exact ⟨hd, (SimpleGraph.ConnectedComponent.eq.mp h).symm⟩
  · rintro ⟨hd, h⟩
    exact ⟨hd, SimpleGraph.ConnectedComponent.eq.mpr h.symm⟩

/-- The data under which the pieces with labels in `X` correspond across the identification of
crossings `crossingTransport hs`: `X` lies in both undominated sets, interlacement on `X` is carried,
and `X` is closed under interlacement with undominated crossings on both sides. -/
structure EXT_PieceSetting (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) : Prop where
  subU : ∀ c ∈ X, c ∈ CV.U hP S
  subU' : ∀ c ∈ X, crossingTransport hs c ∈ CV.U hP' S'
  adj_iff : ∀ c ∈ X, ∀ d ∈ X,
    GeometricInterlaces hP' (crossingTransport hs c) (crossingTransport hs d) ↔ GeometricInterlaces hP c d
  closed : ∀ c ∈ X, ∀ d ∈ CV.U hP S, GeometricInterlaces hP c d → d ∈ X
  closed' : ∀ c ∈ X, ∀ d' ∈ CV.U hP' S', GeometricInterlaces hP' (crossingTransport hs c) d' →
    (crossingTransport hs).symm d' ∈ X

/-- The labels of corresponding pieces correspond (for pieces with a label in `X`). -/
theorem EXT_mem_labels_iff (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X) {c : Crossing P} (hcX : c ∈ X)
    (d : Crossing P) :
    d ∈ CV.pieceLabels hP S (CV.pieceOf hP S c (hX.subU c hcX)) ↔
      crossingTransport hs d ∈
        CV.pieceLabels hP' S' (CV.pieceOf hP' S' (crossingTransport hs c) (hX.subU' c hcX)) := by
  rw [EXT_mem_pieceLabels_pieceOf, EXT_mem_pieceLabels_pieceOf]
  constructor
  · rintro ⟨hd, ⟨w⟩⟩
    obtain ⟨hdX, hr⟩ := EXT_walk_transfer (geometricInterlacementGraph hP)
      (geometricInterlacementGraph hP') (↑(CV.U hP S)) (↑(CV.U hP' S')) (↑X) (crossingTransport hs)
      (fun c hc => hX.subU' c hc) (fun c hc d hd h => (hX.adj_iff c hc d hd).mpr h)
      (fun c hc d hd h => hX.closed c hc d hd h) ⟨c, hX.subU c hcX⟩ ⟨d, hd⟩ w hcX
    exact ⟨hX.subU' d hdX, hr⟩
  · rintro ⟨hd', ⟨w⟩⟩
    have himg : ∀ c' ∈ ((fun x => crossingTransport hs x) '' (↑X : Set (Crossing P))),
        (crossingTransport hs).symm c' ∈ (↑X : Set (Crossing P)) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Equiv.symm_apply_apply]
      exact hx
    obtain ⟨hdX, hr⟩ := EXT_walk_transfer (geometricInterlacementGraph hP')
      (geometricInterlacementGraph hP) (↑(CV.U hP' S')) (↑(CV.U hP S))
      ((fun x => crossingTransport hs x) '' (↑X : Set (Crossing P))) (crossingTransport hs).symm
      (fun c' hc' => hX.subU _ (himg c' hc'))
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ h
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact (hX.adj_iff x hx y hy).mp h)
      (by
        rintro _ ⟨x, hx, rfl⟩ d' hd' h
        exact ⟨(crossingTransport hs).symm d', hX.closed' x hx d' hd' h, Equiv.apply_symm_apply _ _⟩)
      ⟨crossingTransport hs c, hX.subU' c hcX⟩ ⟨crossingTransport hs d, hd'⟩ w ⟨c, hcX, rfl⟩
    have hdX' : d ∈ X := by
      have := himg _ hdX
      rwa [Equiv.symm_apply_apply] at this
    refine ⟨hX.subU d hdX', ?_⟩
    exact hr

/-- The labels of a piece carried by `q` are retained crossings of `q`. -/
theorem EXT_pieceLabels_subset_of_mem_piecesOn (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (H : CV.Piece hP S) (hH : H ∈ CV.piecesOn hP S q) :
    CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q := by
  intro c hc
  rw [mem_geoCarrierCrossings]
  exact ⟨((CV.mem_U_iff hP S c).mp (CV.pieceLabels_subset hP S H hc)).1,
    (CV.mem_piecesOn hP S q H).mp hH c hc⟩

theorem EXT_mem_piecesOn_of_subset (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (H : CV.Piece hP S) (h : CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q) :
    H ∈ CV.piecesOn hP S q := by
  rw [CV.mem_piecesOn]
  intro c hc v hv
  exact ((mem_geoCarrierCrossings hP S q c).mp (h hc)).2 v hv

/-- Pieces with the same labels are equal. -/
theorem EXT_piece_eq_of_labels_eq (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (H H' : CV.Piece hP S) (h : CV.pieceLabels hP S H = CV.pieceLabels hP S H') : H = H' := by
  by_contra hne
  obtain ⟨c, hc⟩ := CV.pieceLabels_nonempty hP S H
  exact Finset.disjoint_left.mp (CV.pieceLabels_disjoint hP S H H' hne) hc (h ▸ hc)

/-- The piece corresponding to `H` (with labels in `X`): the piece of the image of a label of `H`. -/
noncomputable def EXT_pieceMap (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X)
    (H : CV.Piece hP S) (hH : CV.pieceLabels hP S H ⊆ X) : CV.Piece hP' S' :=
  CV.pieceOf hP' S' (crossingTransport hs (CV.pieceLabels_nonempty hP S H).choose)
    (hX.subU' _ (hH (CV.pieceLabels_nonempty hP S H).choose_spec))

theorem EXT_pieceMap_labels (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X)
    (H : CV.Piece hP S) (hH : CV.pieceLabels hP S H ⊆ X) :
    CV.pieceLabels hP' S' (EXT_pieceMap hP hP' hs S S' X hX H hH) =
      (CV.pieceLabels hP S H).map (crossingTransport hs).toEmbedding := by
  set c := (CV.pieceLabels_nonempty hP S H).choose with hcdef
  have hcH : c ∈ CV.pieceLabels hP S H := (CV.pieceLabels_nonempty hP S H).choose_spec
  have hcX : c ∈ X := hH hcH
  obtain ⟨hcU, hHc⟩ := (CV.mem_pieceLabels hP S H c).mp hcH
  ext d'
  obtain ⟨d, rfl⟩ := (crossingTransport hs).surjective d'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  unfold EXT_pieceMap
  rw [← EXT_mem_labels_iff hP hP' hs S S' X hX hcX d]
  have : CV.pieceOf hP S c (hX.subU c hcX) = H := hHc
  rw [this]

/-- The inverse piece map. -/
noncomputable def EXT_pieceMapRev (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X)
    (H' : CV.Piece hP' S') (hH' : CV.pieceLabels hP' S' H' ⊆ X.map (crossingTransport hs).toEmbedding) :
    CV.Piece hP S :=
  CV.pieceOf hP S ((crossingTransport hs).symm (CV.pieceLabels_nonempty hP' S' H').choose)
    (hX.subU _ (Finset.mem_map_equiv.mp (hH' (CV.pieceLabels_nonempty hP' S' H').choose_spec)))

theorem EXT_pieceMapRev_labels (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (X : Finset (Crossing P)) (hX : EXT_PieceSetting hP hP' hs S S' X)
    (H' : CV.Piece hP' S') (hH' : CV.pieceLabels hP' S' H' ⊆ X.map (crossingTransport hs).toEmbedding) :
    (CV.pieceLabels hP S (EXT_pieceMapRev hP hP' hs S S' X hX H' hH')).map (crossingTransport hs).toEmbedding =
      CV.pieceLabels hP' S' H' := by
  set c' := (CV.pieceLabels_nonempty hP' S' H').choose with hcdef
  have hcH : c' ∈ CV.pieceLabels hP' S' H' := (CV.pieceLabels_nonempty hP' S' H').choose_spec
  have hcX : (crossingTransport hs).symm c' ∈ X := Finset.mem_map_equiv.mp (hH' hcH)
  obtain ⟨hcU, hHc⟩ := (CV.mem_pieceLabels hP' S' H' c').mp hcH
  ext d'
  obtain ⟨d, rfl⟩ := (crossingTransport hs).surjective d'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  unfold EXT_pieceMapRev
  rw [EXT_mem_labels_iff hP hP' hs S S' X hX hcX d]
  have : CV.pieceOf hP' S' (crossingTransport hs ((crossingTransport hs).symm c'))
      (hX.subU' _ hcX) = H' := by
    have h2 : crossingTransport hs ((crossingTransport hs).symm c') = c' := Equiv.apply_symm_apply _ _
    rw [← hHc]
    congr 1
  rw [this]

/-- Reindexing a product over the pieces carried by `q` along the piece correspondence. -/
theorem EXT_piecesOn_prod {M : Type*} [CommMonoid M] (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hX : EXT_PieceSetting hP hP' hs S S' (geoCarrierCrossings hP S q))
    (hX' : geoCarrierCrossings hP' S' q' =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding)
    (F : CV.Piece hP S → M) (F' : CV.Piece hP' S' → M)
    (hF : ∀ (H : CV.Piece hP S) (H' : CV.Piece hP' S'),
      CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q →
      CV.pieceLabels hP' S' H' = (CV.pieceLabels hP S H).map (crossingTransport hs).toEmbedding →
      F' H' = F H) :
    ∏ H ∈ CV.piecesOn hP S q, F H = ∏ H' ∈ CV.piecesOn hP' S' q', F' H' := by
  refine Finset.prod_bij'
    (fun H hH => EXT_pieceMap hP hP' hs S S' _ hX H (EXT_pieceLabels_subset_of_mem_piecesOn hP S q H hH))
    (fun H' hH' => EXT_pieceMapRev hP hP' hs S S' _ hX H'
      (hX' ▸ EXT_pieceLabels_subset_of_mem_piecesOn hP' S' q' H' hH')) ?_ ?_ ?_ ?_ ?_
  · intro H hH
    apply EXT_mem_piecesOn_of_subset
    rw [EXT_pieceMap_labels, hX']
    exact Finset.map_subset_map.mpr (EXT_pieceLabels_subset_of_mem_piecesOn hP S q H hH)
  · intro H' hH'
    apply EXT_mem_piecesOn_of_subset
    have h := EXT_pieceMapRev_labels hP hP' hs S S' _ hX H'
      (hX' ▸ EXT_pieceLabels_subset_of_mem_piecesOn hP' S' q' H' hH')
    have h2 := EXT_pieceLabels_subset_of_mem_piecesOn hP' S' q' H' hH'
    rw [hX', ← h] at h2
    exact Finset.map_subset_map.mp h2
  · intro H hH
    apply EXT_piece_eq_of_labels_eq
    apply Finset.map_injective (crossingTransport hs).toEmbedding
    rw [EXT_pieceMapRev_labels, EXT_pieceMap_labels]
  · intro H' hH'
    apply EXT_piece_eq_of_labels_eq
    rw [EXT_pieceMap_labels, EXT_pieceMapRev_labels]
  · intro H hH
    exact (hF H _ (EXT_pieceLabels_subset_of_mem_piecesOn hP S q H hH)
      (EXT_pieceMap_labels hP hP' hs S S' _ hX H _)).symm

/-- The additive form of `EXT_piecesOn_prod`. -/
theorem EXT_piecesOn_sum {M : Type*} [AddCommMonoid M] (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (S : Finset (Crossing P)) (S' : Finset (Crossing P'))
    (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hX : EXT_PieceSetting hP hP' hs S S' (geoCarrierCrossings hP S q))
    (hX' : geoCarrierCrossings hP' S' q' =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding)
    (F : CV.Piece hP S → M) (F' : CV.Piece hP' S' → M)
    (hF : ∀ (H : CV.Piece hP S) (H' : CV.Piece hP' S'),
      CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q →
      CV.pieceLabels hP' S' H' = (CV.pieceLabels hP S H).map (crossingTransport hs).toEmbedding →
      F' H' = F H) :
    ∑ H ∈ CV.piecesOn hP S q, F H = ∑ H' ∈ CV.piecesOn hP' S' q', F' H' :=
  EXT_piecesOn_prod (M := Multiplicative M) hP hP' hs S S' q q' hX hX'
    (fun H => Multiplicative.ofAdd (F H)) (fun H' => Multiplicative.ofAdd (F' H'))
    (fun H H' h1 h2 => congrArg Multiplicative.ofAdd (hF H H' h1 h2))

/-- `X = geoCarrierCrossings q` is closed under interlacement with undominated crossings
(lem:carriers (iv): an undominated crossing interlacing a retained crossing of `q` lies on `q`). -/
theorem EXT_closed (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hP)
    (q : GeoComponent hP S) :
    ∀ c ∈ geoCarrierCrossings hP S q, ∀ d ∈ CV.U hP S, GeometricInterlaces hP c d →
      d ∈ geoCarrierCrossings hP S q := by
  intro c hc d hd hI
  have hcU : c ∈ CV.U hP S :=
    (CV.mem_U_iff hP S c).mpr ((mem_geoSupportUnselected_iff hP S c).mp
      (geoCarrierCrossings_subset_U hP (CV.geoIndependent_of_mem_Ind hP hS) q hc))
  rw [mem_geoCarrierCrossings] at hc ⊢
  refine ⟨((CV.mem_U_iff hP S d).mp hd).1, ?_⟩
  intro w hw
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  have := CV.owner_eq_of_interlaces_mem_U hP hS hcU hd hI ⟨c, i⟩ w rfl hw
  rw [← this]
  exact hc.2 ⟨c, i⟩ rfl

/-- The piece setting at the retained crossings of corresponding carriers of independent supports. -/
theorem EXT_pieceSetting (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hP) (hS' : S' ∈ CV.Ind hP')
    (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hX' : geoCarrierCrossings hP' S' q' =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding)
    (hadj : ∀ c ∈ geoCarrierCrossings hP S q, ∀ d ∈ geoCarrierCrossings hP S q,
      GeometricInterlaces hP' (crossingTransport hs c) (crossingTransport hs d) ↔
        GeometricInterlaces hP c d) :
    EXT_PieceSetting hP hP' hs S S' (geoCarrierCrossings hP S q) where
  subU c hc := (CV.mem_U_iff hP S c).mpr ((mem_geoSupportUnselected_iff hP S c).mp
    (geoCarrierCrossings_subset_U hP (CV.geoIndependent_of_mem_Ind hP hS) q hc))
  subU' c hc := (CV.mem_U_iff hP' S' _).mpr ((mem_geoSupportUnselected_iff hP' S' _).mp
    (geoCarrierCrossings_subset_U hP' (CV.geoIndependent_of_mem_Ind hP' hS') q'
      (by rw [hX']; exact Finset.mem_map_of_mem _ hc)))
  adj_iff := hadj
  closed := EXT_closed hP hS q
  closed' c hc d' hd' h := by
    have hc' : crossingTransport hs c ∈ geoCarrierCrossings hP' S' q' := by
      rw [hX']; exact Finset.mem_map_of_mem _ hc
    have := EXT_closed hP' hS' q' _ hc' d' hd' h
    rw [hX'] at this
    exact Finset.mem_map_equiv.mp this

end EXTCrossings

section EXTCarrierData

variable {P P' : LabelledTuple n}

/-- The bad marks: the six traversal visits of the triangle (including a selected triangle crossing's
smoothing-site visits, which are the same marks). -/
def EXT_TriVisit (e f g : ZMod n) : Mark P → Prop
  | Sum.inl _ => False
  | Sum.inr v => v.1.val ∈ triangleSupports e f g

omit [NeZero n] in
theorem EXT_triVisit_markTransport_symm {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} (e f g : ZMod n)
    (b' : Mark P') : EXT_TriVisit e f g ((markTransport hs).symm b') ↔ EXT_TriVisit e f g b' := by
  cases b' with
  | inl i => exact Iff.rfl
  | inr v => exact Iff.rfl

omit [NeZero n] in
theorem EXT_triVisit_markTransport {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} (e f g : ZMod n)
    (a : Mark P) : EXT_TriVisit e f g (markTransport hs a) ↔ EXT_TriVisit e f g a := by
  cases a with
  | inl i => exact Iff.rfl
  | inr v => exact Iff.rfl

theorem EXT_triangleDisjoint_iff (hP : CrossingGeometry P) (S : Finset (Crossing P)) (e f g : ZMod n)
    (q : GeoComponent hP S) :
    TriangleDisjoint hP S e f g q ↔ EXT_Avoids hP S (fun a => ¬ EXT_TriVisit e f g a) q := by
  constructor
  · intro h a ha
    cases a with
    | inl i => exact id
    | inr v => exact fun hv => h v hv ha
  · intro h v hv hq
    exact h _ hq hv

/-- `wt(L)` is determined by the turn sequence of the corner polygon. -/
theorem EXT_weight_eq (hP : CrossingGeometry P) (hP' : CrossingGeometry P') (S : Finset (Crossing P))
    (S' : Finset (Crossing P')) (q : GeoComponent hP S) (q' : GeoComponent hP' S')
    (hc : geoCornerCount hP' S' q' = geoCornerCount hP S q)
    (hturn : ∀ k, turn (geoCornerPolygon hP' S' q') k =
      turn (geoCornerPolygon hP S q) (Equiv.cast (congrArg ZMod hc) k)) :
    CV.weight hP' S' q' = CV.weight hP S q := by
  unfold CV.weight geoCarrierSelector
  rw [← cornerSelector_geoRecast hc.symm (geoCornerPolygon hP' S' q')]
  apply cornerSelector_congr_turn
  intro j
  rw [turn_geoRecast, hturn, geo_zmod_cast_cast' hc j]

/-- `R(L) = |rot(L)|` is determined by the rotation number of the corner polygon. -/
theorem EXT_carrierR_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')} (hS : S ∈ CV.Ind hG.crossingGeometry)
    (hS' : S' ∈ CV.Ind hG'.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (q' : GeoComponent hG'.crossingGeometry S')
    (hrot : rotationNumber (geoCornerPolygon hG'.crossingGeometry S' q') =
      rotationNumber (geoCornerPolygon hG.crossingGeometry S q)) :
    CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q := by
  unfold CV.carrierR CV.rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [CV.rot_eq_rotationNumber, CV.rot_eq_rotationNumber]
  exact hrot

theorem EXT_groupedWrithe_eq (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (hX : EXT_PieceSetting hG.crossingGeometry hG'.crossingGeometry hs S S'
      (geoCarrierCrossings hG.crossingGeometry S q))
    (hX' : geoCarrierCrossings hG'.crossingGeometry S' q' =
      (geoCarrierCrossings hG.crossingGeometry S q).map (crossingTransport hs).toEmbedding) :
    CV.groupedWrithe hG' q' = CV.groupedWrithe hG q := by
  unfold CV.groupedWrithe
  symm
  apply EXT_piecesOn_sum hG.crossingGeometry hG'.crossingGeometry hs S S' q q' hX hX'
  intro H H' _ h
  unfold CV.pieceWrithe
  rw [h, Finset.card_map]

theorem EXT_groupedPoly_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (hX : EXT_PieceSetting hG.crossingGeometry hG'.crossingGeometry hs S S'
      (geoCarrierCrossings hG.crossingGeometry S q))
    (hX' : geoCarrierCrossings hG'.crossingGeometry S' q' =
      (geoCarrierCrossings hG.crossingGeometry S q).map (crossingTransport hs).toEmbedding)
    (hPH : ∀ (H : CV.Piece hG.crossingGeometry S) (H' : CV.Piece hG'.crossingGeometry S'),
      CV.pieceLabels hG.crossingGeometry S H ⊆ geoCarrierCrossings hG.crossingGeometry S q →
      CV.pieceLabels hG'.crossingGeometry S' H' =
        (CV.pieceLabels hG.crossingGeometry S H).map (crossingTransport hs).toEmbedding →
      CV.pieceHomfly hn (hG'.diagrammatic hn) hS' H' = CV.pieceHomfly hn (hG.diagrammatic hn) hS H) :
    CV.groupedPoly hn hG' hS' q' = CV.groupedPoly hn hG hS q := by
  unfold CV.groupedPoly
  symm
  exact EXT_piecesOn_prod hG.crossingGeometry hG'.crossingGeometry hs S S' q q' hX hX' _ _ hPH

theorem EXT_Omega1_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')} (hS : S ∈ CV.Ind hG.crossingGeometry)
    (hS' : S' ∈ CV.Ind hG'.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (q' : GeoComponent hG'.crossingGeometry S')
    (hR : CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q)
    (hw : CV.groupedWrithe hG' q' = CV.groupedWrithe hG q)
    (hp : CV.groupedPoly hn hG' hS' q' = CV.groupedPoly hn hG hS q) :
    CV.Omega1 hn hG' hS' q' = CV.Omega1 hn hG hS q := by
  unfold CV.Omega1 CV.slot
  rw [hR, hw, hp]

/-- Two pieces of one polygon with the same labels have the same polynomial (choice independence of
the piece polynomial, `homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`). -/
theorem EXT_pieceHomfly_eq_of_labels (hn : 3 ≤ n) (hD : CV.Diagrammatic P) {S S' : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hD.crossingGeometry) (hS' : S' ∈ CV.Ind hD.crossingGeometry)
    (H : CV.Piece hD.crossingGeometry S) (H' : CV.Piece hD.crossingGeometry S')
    (h : CV.pieceLabels hD.crossingGeometry S' H' = CV.pieceLabels hD.crossingGeometry S H) :
    CV.pieceHomfly hn hD hS' H' = CV.pieceHomfly hn hD hS H := by
  unfold CV.pieceHomfly CV.pieceDiagram
  exact CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn (CarrierGeometry.ofDiagrammatic hD)
    (CV.pieceSupport_geoIndependent hD hS' H') (CV.pieceSupport_geoIndependent hD hS H) _ _
    (by rw [CV.pieceCarrier_geoCarrierCrossings, CV.pieceCarrier_geoCarrierCrossings, h])

/-- The reindexing of the exterior factor along the carrier correspondence. -/
theorem EXT_exteriorFactor_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry) (e f g : ZMod n)
    (hcomm : ∀ a, ¬ EXT_TriVisit e f g a → ¬ EXT_TriVisit e f g (geoSmoothingSuccessor hG.crossingGeometry S a) →
      geoSmoothingSuccessor hG'.crossingGeometry S' (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor hG.crossingGeometry S a))
    (hcomm' : ∀ b', ¬ EXT_TriVisit e f g ((markTransport hs).symm b') →
      ¬ EXT_TriVisit e f g ((markTransport hs).symm (geoSmoothingSuccessor hG'.crossingGeometry S' b')) →
      geoSmoothingSuccessor hG.crossingGeometry S ((markTransport hs).symm b') =
        (markTransport hs).symm (geoSmoothingSuccessor hG'.crossingGeometry S' b'))
    (hval : ∀ q : GeoComponent hG.crossingGeometry S, TriangleDisjoint hG.crossingGeometry S e f g q →
      CV.weight hG'.crossingGeometry S' (EXT_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' q) *
        CV.Omega1 hn hG' hS' (EXT_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' q) =
      CV.weight hG.crossingGeometry S q * CV.Omega1 hn hG hS q) :
    exteriorFactor hn hG' hS' e f g = exteriorFactor hn hG hS e f g := by
  classical
  have hcomm₁ : ∀ a, (fun a => ¬ EXT_TriVisit e f g a) a →
      (fun a => ¬ EXT_TriVisit e f g a) (geoSmoothingSuccessor hG.crossingGeometry S a) →
      geoSmoothingSuccessor hG'.crossingGeometry S' (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor hG.crossingGeometry S a) := hcomm
  have hcomm₂ : ∀ b', (fun a => ¬ EXT_TriVisit e f g a) ((markTransport hs).symm b') →
      (fun a => ¬ EXT_TriVisit e f g a)
        ((markTransport hs).symm (geoSmoothingSuccessor hG'.crossingGeometry S' b')) →
      geoSmoothingSuccessor hG.crossingGeometry S ((markTransport hs).symm b') =
        (markTransport hs).symm (geoSmoothingSuccessor hG'.crossingGeometry S' b') := hcomm'
  -- the avoiding predicate on `P'`
  have hav' : ∀ q : GeoComponent hG.crossingGeometry S, TriangleDisjoint hG.crossingGeometry S e f g q →
      TriangleDisjoint hG'.crossingGeometry S' e f g
        (EXT_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' q) := by
    intro q hq
    rw [EXT_triangleDisjoint_iff] at hq ⊢
    have h := EXT_corr_avoids hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' _ hcomm₁ q hq
    intro b' hb'
    have this : ¬ EXT_TriVisit e f g ((markTransport hs).symm b') := h b' hb'
    rwa [EXT_triVisit_markTransport_symm] at this
  have hav : ∀ q' : GeoComponent hG'.crossingGeometry S', TriangleDisjoint hG'.crossingGeometry S' e f g q' →
      TriangleDisjoint hG.crossingGeometry S e f g
        (EXT_corr hG'.crossingGeometry hG.crossingGeometry (markTransport hs).symm S' S q') := by
    intro q' hq'
    rw [EXT_triangleDisjoint_iff] at hq' ⊢
    have hq'' : EXT_Avoids hG'.crossingGeometry S' (fun b' => ¬ EXT_TriVisit e f g ((markTransport hs).symm b')) q' := by
      intro b' hb'
      show ¬ EXT_TriVisit e f g ((markTransport hs).symm b')
      rw [EXT_triVisit_markTransport_symm]
      exact hq' b' hb'
    have h := EXT_corr_avoids hG'.crossingGeometry hG.crossingGeometry (markTransport hs).symm S' S _ hcomm₂ q' hq''
    intro b hb
    have this : ¬ EXT_TriVisit e f g ((markTransport hs).symm ((markTransport hs).symm.symm b)) := h b hb
    rwa [Equiv.symm_symm, Equiv.symm_apply_apply] at this
  unfold exteriorFactor
  symm
  refine Finset.prod_nbij' (EXT_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S')
    (EXT_corr hG'.crossingGeometry hG.crossingGeometry (markTransport hs).symm S' S) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨Finset.mem_univ _, hav' q hq.2⟩
  · intro q' hq'
    rw [Finset.mem_filter] at hq' ⊢
    exact ⟨Finset.mem_univ _, hav q' hq'.2⟩
  · intro q hq
    rw [Finset.mem_filter, EXT_triangleDisjoint_iff] at hq
    exact EXT_corr_corr hG.crossingGeometry hG'.crossingGeometry (markTransport hs) S S' _ hcomm₁ hcomm₂ q hq.2
  · intro q' hq'
    rw [Finset.mem_filter, EXT_triangleDisjoint_iff] at hq'
    have hq'' : EXT_Avoids hG'.crossingGeometry S' (fun b' => ¬ EXT_TriVisit e f g ((markTransport hs).symm b')) q' := by
      intro b' hb'
      show ¬ EXT_TriVisit e f g ((markTransport hs).symm b')
      rw [EXT_triVisit_markTransport_symm]
      exact hq'.2 b' hb'
    exact EXT_corr_corr hG'.crossingGeometry hG.crossingGeometry (markTransport hs).symm S' S _ hcomm₂
      (by simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using hcomm₁) q' hq''
  · intro q hq
    rw [Finset.mem_filter] at hq
    exact (hval q hq.2).symm

end EXTCarrierData

section EXTSamePolygon

variable {P : LabelledTuple n}

omit [NeZero n] in
theorem EXT_markTransport_symm_self (hs : ∀ s, IsCrossing P s ↔ IsCrossing P s) (b : Mark P) :
    (markTransport hs).symm b = b := by
  cases b <;> rfl

omit [NeZero n] in
theorem EXT_map_self (hs : ∀ s, IsCrossing P s ↔ IsCrossing P s) (X : Finset (Crossing P)) :
    X.map (crossingTransport hs).toEmbedding = X := by
  ext x
  rw [Finset.mem_map_equiv]
  exact Iff.rfl

/-- Smoothing the triangle crossings of `A` as well as `Q` changes the successor only at the triangle
visits (`geoSmoothingSuccessor_union_of_disjoint`). -/
theorem EXT_succ_union (hP : CrossingGeometry P) {Q A : Finset (Crossing P)} (hQA : Disjoint Q A)
    {e f g : ZMod n} (hAT : ∀ x ∈ A, x.val ∈ triangleSupports e f g) (a : Mark P)
    (ha : ¬ EXT_TriVisit e f g a) :
    geoSmoothingSuccessor hP (Q ∪ A) a = geoSmoothingSuccessor hP Q a := by
  have h : geoSmoothingSuccessor hP (Q ∪ A) =
      (selectedMarkPerm A).trans (geoSmoothingSuccessor hP Q) := by
    convert geoSmoothingSuccessor_union_of_disjoint hP Q A hQA using 3
    congr 1
    exact Subsingleton.elim _ _
  rw [h, Equiv.trans_apply]
  congr 1
  cases a with
  | inl i => rfl
  | inr v =>
    rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem]
    intro hv
    exact ha (hAT v.1 hv)

/-- **Fibre stability of the exterior factor at one polygon**: the exterior factor of the row `Q ∪ A`
equals that of the base row `Q` (R-EXTERIOR-1, proof §1–§3). -/
theorem EXT_exteriorFactor_eq_base (hn : 3 ≤ n) (hG : CV.Generic P) {Q A : Finset (Crossing P)}
    {e f g : ZMod n} (hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g)
    (hAT : ∀ x ∈ A, x.val ∈ triangleSupports e f g)
    (hA : Q ∪ A ∈ CV.Ind hG.crossingGeometry) (hQ : Q ∈ CV.Ind hG.crossingGeometry) :
    exteriorFactor hn hG hQ e f g = exteriorFactor hn hG hA e f g := by
  classical
  set hP := hG.crossingGeometry
  set hs : ∀ s, IsCrossing P s ↔ IsCrossing P s := fun _ => Iff.rfl
  have hQA : Disjoint Q A := by
    rw [Finset.disjoint_left]
    intro x hxQ hxA
    exact hQT x hxQ (hAT x hxA)
  have hcomm : ∀ a, ¬ EXT_TriVisit e f g a →
      ¬ EXT_TriVisit e f g (geoSmoothingSuccessor hP (Q ∪ A) a) →
      geoSmoothingSuccessor hP Q (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor hP (Q ∪ A) a) := by
    intro a ha _
    rw [markTransport_self, markTransport_self, EXT_succ_union hP hQA hAT a ha]
  have hcomm' : ∀ b', ¬ EXT_TriVisit e f g ((markTransport hs).symm b') →
      ¬ EXT_TriVisit e f g ((markTransport hs).symm (geoSmoothingSuccessor hP Q b')) →
      geoSmoothingSuccessor hP (Q ∪ A) ((markTransport hs).symm b') =
        (markTransport hs).symm (geoSmoothingSuccessor hP Q b') := by
    intro b' hb' _
    rw [EXT_markTransport_symm_self] at hb' ⊢
    rw [EXT_markTransport_symm_self, EXT_succ_union hP hQA hAT b' hb']
  refine EXT_exteriorFactor_eq hn hG hG hs hA hQ e f g hcomm hcomm' ?_
  intro q hq
  set q' := EXT_corr hP hP (markTransport hs) (Q ∪ A) Q q
  have hqav : EXT_Avoids hP (Q ∪ A) (fun a => ¬ EXT_TriVisit e f g a) q :=
    (EXT_triangleDisjoint_iff hP (Q ∪ A) e f g q).mp hq
  have hblock : ∀ b, geoOwner hP Q (markTransport hs b) = q' ↔ geoOwner hP (Q ∪ A) b = q :=
    EXT_corr_iff hP hP (markTransport hs) (Q ∪ A) Q _ hcomm q hqav
  have hlist : (geoComponentMarkList hP (Q ∪ A) q).map (markTransport hs) = geoComponentMarkList hP Q q' := by
    refine EXT_markList_map hP hP (markTransport hs) (Q ∪ A) Q q q' hblock ?_
    intro a b _ _
    rw [markTransport_self, markTransport_self]
  have hcorner : ∀ a, geoOwner hP (Q ∪ A) a = q →
      (IsTrueCorner Q (markTransport hs a) ↔ IsTrueCorner (Q ∪ A) a) := by
    intro a ha
    rw [markTransport_self]
    cases a with
    | inl i => exact Iff.rfl
    | inr v =>
      rw [isTrueCorner_visit, isTrueCorner_visit, Finset.mem_union]
      have hv : v.1 ∉ A := fun hvA => hqav _ ha (hAT v.1 hvA)
      exact ⟨Or.inl, fun h => h.resolve_right hv⟩
  have hcl : (geoComponentCornerList hP (Q ∪ A) q).map (markTransport hs) =
      geoComponentCornerList hP Q q' :=
    EXT_cornerList_map hP hP (markTransport hs) (Q ∪ A) Q q q' hlist hcorner
  have hc := EXT_cornerCount_eq hP hP (markTransport hs) (Q ∪ A) Q q q' hcl
  have hpoly : geoCornerPolygon hP Q q' = geoRecast hc (geoCornerPolygon hP (Q ∪ A) q) :=
    EXT_cornerPolygon_eq_self hP (markTransport hs) (markTransport_self hs) (Q ∪ A) Q q q' hcl
  have hsel : ∀ x : Crossing P, (∀ v : Visit P, v.1 = x → geoOwner hP (Q ∪ A) (Sum.inr v) = q) →
      (crossingTransport hs x ∈ Q ↔ x ∈ Q ∪ A) := by
    intro x hx
    obtain ⟨i, -, -⟩ := crossing_visits_exist x
    have hxT : x.val ∉ triangleSupports e f g := hqav _ (hx ⟨x, i⟩ rfl)
    have hxA : x ∉ A := fun hxA => hxT (hAT x hxA)
    show x ∈ Q ↔ x ∈ Q ∪ A
    rw [Finset.mem_union]
    exact ⟨Or.inl, fun h => h.resolve_right hxA⟩
  have hX' : geoCarrierCrossings hP Q q' =
      (geoCarrierCrossings hP (Q ∪ A) q).map (crossingTransport hs).toEmbedding :=
    EXT_carrierCrossings_map hP hP hs (Q ∪ A) Q q q' hblock hsel
  have hX : EXT_PieceSetting hP hP hs (Q ∪ A) Q (geoCarrierCrossings hP (Q ∪ A) q) :=
    EXT_pieceSetting hP hP hs hA hQ q q' hX' (fun _ _ _ _ => Iff.rfl)
  have hweight : CV.weight hP Q q' = CV.weight hP (Q ∪ A) q := by
    refine EXT_weight_eq hP hP (Q ∪ A) Q q q' hc ?_
    intro k
    rw [hpoly, turn_geoRecast]
  have hR : CV.carrierR hn hG hQ q' = CV.carrierR hn hG hA q := by
    refine EXT_carrierR_eq hn hG hG hA hQ q q' ?_
    rw [hpoly, rotationNumber_geoRecast]
  have hw : CV.groupedWrithe hG q' = CV.groupedWrithe hG q :=
    EXT_groupedWrithe_eq hG hG hs q q' hX hX'
  have hp : CV.groupedPoly hn hG hQ q' = CV.groupedPoly hn hG hA q := by
    refine EXT_groupedPoly_eq hn hG hG hs hA hQ q q' hX hX' ?_
    intro H H' _ h
    rw [EXT_map_self] at h
    exact EXT_pieceHomfly_eq_of_labels hn (hG.diagrammatic hn) hA hQ H H' h
  rw [hweight, EXT_Omega1_eq hn hG hG hA hQ q q' hR hw hp]

/-- **Row 168, field `independent_of_A`**: "Then `C_{Q,sigma}(A)` is independent of `A`". -/
theorem EXT_168_independent_of_A (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ A A' : Finset (Crossing (E.curve t)),
      A ⊆ triangleCrossings (E.curve t) e f g → A' ⊆ triangleCrossings (E.curve t) e f g →
      ∀ (hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1)) (hA' : Q ∪ A' ∈ CV.Ind (geomAt E t ht.1)),
        exteriorFactor hn (genericAt E t ht.1) hA e f g =
          exteriorFactor hn (genericAt E t ht.1) hA' e f g := by
  intro t ht Q hQ A A' hAT hAT' hA hA'
  have hQ' : Q ∈ CV.Ind (geomAt E t ht.1) := mem_Ind_of_mem_outsideSupports hQ
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := by
    intro x hx hxT
    exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  have h1 := EXT_exteriorFactor_eq_base hn (genericAt E t ht.1) hQT
    (fun x hx => (P1.mem_triangleCrossings x).mp (hAT hx)) hA hQ'
  have h2 := EXT_exteriorFactor_eq_base hn (genericAt E t ht.1) hQT
    (fun x hx => (P1.mem_triangleCrossings x).mp (hAT' hx)) hA' hQ'
  rw [← h1, ← h2]

end EXTSamePolygon

section EXTWall

variable {P P' : LabelledTuple n}

/-- An empty oriented gap between distinct members of a finite linear order identifies the
sorted-list successor, including the last/first cut (a verbatim port of the accepted
`SM.sorted_next_of_no_cyclic_between`, SM/GaussNextFromEmptyArc.lean, which is not in the import
closure of this file; the same port as `SEL_sorted_next_of_no_cyclic_between`, which is declared later in
this file). -/
theorem EXT_sorted_next_of_no_cyclic_between {α : Type*} [LinearOrder α]
    (s : Finset α) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hgap : ∀ x ∈ s,
      ¬ ((a < x ∧ x < b) ∨ (x < b ∧ b < a) ∨ (b < a ∧ a < x))) :
    s.sort.next a ((Finset.mem_sort _).mpr ha) = b := by
  let e := s.orderIsoOfFin rfl
  let ia := e.symm ⟨a, ha⟩
  let ib := e.symm ⟨b, hb⟩
  have hcoe {i j : Fin s.card} (h : i < j) : (e i).val < (e j).val :=
    Subtype.coe_lt_coe.mpr (e.strictMono h)
  have hsize : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hne : ia.val ≠ ib.val := by
    intro he
    apply hab
    have hv := congrArg (fun k : Fin s.card => (e k).val) (Fin.ext he : ia = ib)
    simpa only [ia, ib, e.apply_symm_apply] using hv
  have haN := ia.isLt
  have hbN := ib.isLt
  have hindex : ib.val = (ia.val + 1) % s.card := by
    by_cases hcut : ia.val + 1 < s.card
    · let j : Fin s.card := ⟨ia.val + 1, hcut⟩
      have haj : a < (e j).val := by
        have h : ia < j := by change ia.val < ia.val + 1; omega
        simpa only [ia, e.apply_symm_apply] using hcoe h
      have hnone := hgap (e j).val (e j).property
      have hnotBack : ¬ ib.val < ia.val := by
        intro h
        have hba : b < a := by
          simpa only [ia, ib, e.apply_symm_apply] using
            hcoe (show ib < ia from h)
        exact hnone (Or.inr (Or.inr ⟨hba, haj⟩))
      have hnotGap : ¬ j.val < ib.val := by
        intro h
        have hjb : (e j).val < b := by
          simpa only [ib, e.apply_symm_apply] using
            hcoe (show j < ib from h)
        exact hnone (Or.inl ⟨haj, hjb⟩)
      have hj : j.val = ia.val + 1 := rfl
      rw [Nat.mod_eq_of_lt hcut]
      omega
    · have hlast : ia.val + 1 = s.card := by omega
      let j : Fin s.card := ⟨0, hsize⟩
      have hnone := hgap (e j).val (e j).property
      have hnotPos : ¬ 0 < ib.val := by
        intro h
        have hjb : (e j).val < b := by
          simpa only [ib, e.apply_symm_apply] using
            hcoe (show j < ib from h)
        have hba : b < a := by
          have hi : ib < ia := by change ib.val < ia.val; omega
          simpa only [ia, ib, e.apply_symm_apply] using hcoe hi
        exact hnone (Or.inr (Or.inl ⟨hjb, hba⟩))
      rw [hlast, Nat.mod_self]
      omega
  let nextIndex : Fin s.card := ⟨(ia.val + 1) % s.card, Nat.mod_lt _ hsize⟩
  have hvalue : s.sort.next a ((Finset.mem_sort _).mpr ha) = (e nextIndex).val := by
    rw [List.next_eq_getElem]
    simp only [e, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply, Finset.length_sort]
    rfl
  have hi : nextIndex = ib := Fin.ext hindex.symm
  rw [hvalue, hi]
  simp only [ib, e.apply_symm_apply]


/-- On the sorted mark list, key order is index order. -/
theorem EXT_geoMarkList_key_lt_iff (hP : CrossingGeometry P) {i j : ℕ}
    (hi : i < (geoMarkList hP).length) (hj : j < (geoMarkList hP).length) :
    geoMarkKey hP ((geoMarkList hP)[i]'hi) < geoMarkKey hP ((geoMarkList hP)[j]'hj) ↔ i < j := by
  have hs := List.pairwise_iff_getElem.mp (geoMarkList_sorted hP)
  have hnd : ∀ (i j : ℕ) (hi : i < (geoMarkList hP).length) (hj : j < (geoMarkList hP).length),
      i < j → (geoMarkList hP)[i] ≠ (geoMarkList hP)[j] :=
    List.pairwise_iff_getElem.mp (geoMarkList_nodup hP)
  constructor
  · intro h
    by_contra hij
    have hij' : j ≤ i := not_lt.mp hij
    rcases hij'.lt_or_eq with hlt | heq
    · exact absurd h (not_lt.mpr (hs j i hj hi hlt))
    · subst heq
      exact lt_irrefl _ h
  · intro hij
    exact lt_of_le_of_ne (hs i j hi hj hij)
      (fun h => hnd i j hi hj hij (geoMarkKey_injective hP h))

/-- No mark lies strictly between a mark and its `ρ`-successor. -/
theorem EXT_not_between_succ (hP : CrossingGeometry P) (a x : Mark P) :
    ¬ Link.cycBetween (geoMarkKey hP a) (geoMarkKey hP x) (geoMarkKey hP (geoMarkSuccessor hP a)) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP a)
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP x)
  rw [geoMarkSuccessor_getElem hP i hi]
  have hlen : 0 < (geoMarkList hP).length := lt_of_le_of_lt (Nat.zero_le i) hi
  have hk : (i + 1) % (geoMarkList hP).length < (geoMarkList hP).length := Nat.mod_lt _ hlen
  intro hc
  unfold Link.cycBetween at hc
  rw [EXT_geoMarkList_key_lt_iff hP hi hj, EXT_geoMarkList_key_lt_iff hP hj hk,
    EXT_geoMarkList_key_lt_iff hP hk hi] at hc
  by_cases hlt : i + 1 < (geoMarkList hP).length
  · rw [Nat.mod_eq_of_lt hlt] at hc
    omega
  · have h1 : i + 1 = (geoMarkList hP).length := by omega
    rw [h1, Nat.mod_self] at hc
    omega

omit [NeZero n] in
theorem EXT_markTransport_vertex (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (i : ZMod n) :
    markTransport hs (Sum.inl i) = Sum.inl i := rfl

/-- **Key order across the wall**: the traversal order of two marks is carried by the canonical
identification unless they are the two visits of a bundle pair on their common edge
(R-LOC-2 (2)–(3), `ExactTriangleVisitOrders`). -/
theorem EXT_key_lt_wall (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n}
    (hgw : ExactTriangleVisitOrders P P' e f g hs) (a b : Mark P)
    (hab : ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w → v.1.val ∪ w.1.val ≠ {e, f, g}) :
    geoMarkKey hP a < geoMarkKey hP b ↔
      geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs b) := by
  unfold geoMarkKey
  rw [traversalKey_lt_iff, traversalKey_lt_iff]
  cases a with
  | inl i =>
    cases b with
    | inl j => exact Iff.rfl
    | inr w =>
      have h0 : 0 < visitParameter w :=
        (crossingParameter_interior_of_geometry hP w.1 w.2.val w.2.property).1
      have h0' : 0 < visitParameter (visitTransport hs w) :=
        (crossingParameter_interior_of_geometry hP' _ _ _).1
      rw [EXT_markTransport_vertex, markTransport_visit, geoMarkPosition_vertex, geoMarkPosition_vertex,
        geoMarkPosition_visit, geoMarkPosition_visit]
      simp only [geometricVisitPosition_edge, geometricVisitPosition_parameter, visitTransport_edge, h0, h0',
        and_true]
  | inr v =>
    cases b with
    | inl j =>
      have h0 : 0 < visitParameter v :=
        (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h0' : 0 < visitParameter (visitTransport hs v) :=
        (crossingParameter_interior_of_geometry hP' _ _ _).1
      rw [EXT_markTransport_vertex, markTransport_visit, geoMarkPosition_vertex, geoMarkPosition_vertex,
        geoMarkPosition_visit, geoMarkPosition_visit]
      simp only [geometricVisitPosition_edge, geometricVisitPosition_parameter, visitTransport_edge]
      have hn0 : ¬ visitParameter v < 0 := not_lt.mpr h0.le
      have hn0' : ¬ visitParameter (visitTransport hs v) < 0 := not_lt.mpr h0'.le
      simp only [hn0, hn0', and_false, or_false]
    | inr w =>
      rw [markTransport_visit, markTransport_visit, geoMarkPosition_visit, geoMarkPosition_visit,
        geoMarkPosition_visit, geoMarkPosition_visit]
      simp only [geometricVisitPosition_edge, geometricVisitPosition_parameter, visitTransport_edge]
      apply or_congr Iff.rfl
      apply and_congr_right
      intro he
      exact (hgw v w he).2 (hab v w rfl rfl)

omit [NeZero n] in
/-- A good mark and any mark are never a bundle pair. -/
theorem EXT_hab_of_good_left {e f g : ZMod n} {a b : Mark P} (ha : ¬ EXT_TriVisit e f g a) :
    ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w → v.1.val ∪ w.1.val ≠ {e, f, g} := by
  rintro v w rfl _ hu
  exact ha (L.mem_triangleSupports_of_union hu).1

omit [NeZero n] in
theorem EXT_hab_of_good_right {e f g : ZMod n} {a b : Mark P} (hb : ¬ EXT_TriVisit e f g b) :
    ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w → v.1.val ∪ w.1.val ≠ {e, f, g} := by
  rintro v w _ rfl hu
  exact hb (L.mem_triangleSupports_of_union hu).2

/-- The marked circle has at least two marks (`n ≥ 3` vertices). -/
theorem EXT_two_le_geoMarkList_length (hn : 3 ≤ n) (hP : CrossingGeometry P) :
    2 ≤ (geoMarkList hP).length := by
  classical
  have h01 : (Sum.inl (0 : ZMod n) : Mark P) ≠ Sum.inl 1 := by
    intro h
    have h' : (0 : ZMod n) = 1 := Sum.inl_injective h
    have : Fact (1 < n) := ⟨by omega⟩
    exact zero_ne_one h'
  have hsub : ({Sum.inl 0, Sum.inl 1} : Finset (Mark P)) ⊆ (geoMarkList hP).toFinset := by
    intro x _
    exact List.mem_toFinset.mpr (mem_geoMarkList hP x)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair h01, List.toFinset_card_of_nodup (geoMarkList_nodup hP)] at hcard
  exact hcard

/-- `ρ` has no fixed point. -/
theorem EXT_geoMarkSuccessor_ne (hn : 3 ≤ n) (hP : CrossingGeometry P) (a : Mark P) :
    geoMarkSuccessor hP a ≠ a := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP a)
  rw [geoMarkSuccessor_getElem hP i hi]
  have hnd : ∀ (i j : ℕ) (hi : i < (geoMarkList hP).length) (hj : j < (geoMarkList hP).length),
      i < j → (geoMarkList hP)[i] ≠ (geoMarkList hP)[j] :=
    List.pairwise_iff_getElem.mp (geoMarkList_nodup hP)
  have hlen2 := EXT_two_le_geoMarkList_length hn hP
  have hlen : 0 < (geoMarkList hP).length := by omega
  intro h
  by_cases hlt : i + 1 < (geoMarkList hP).length
  · have hk : (i + 1) % (geoMarkList hP).length = i + 1 := Nat.mod_eq_of_lt hlt
    have h' : (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'(Nat.mod_lt _ hlen) =
        (geoMarkList hP)[i + 1]'hlt :=
      geo_getElem_congr _ _ rfl _ _ _ _ hk
    exact hnd i (i + 1) hi hlt (Nat.lt_succ_self i) (h'.symm.trans h).symm
  · have h1 : (i + 1) % (geoMarkList hP).length = 0 := by
      have : i + 1 = (geoMarkList hP).length := by omega
      rw [this, Nat.mod_self]
    have h' : (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'(Nat.mod_lt _ hlen) =
        (geoMarkList hP)[0]'hlen :=
      geo_getElem_congr _ _ rfl _ _ _ _ h1
    have hi0 : 0 < i := by omega
    exact hnd 0 i hlen hi hi0 (h'.symm.trans h)

/-- **`ρ` across the wall at a good mark with a good successor**: erasing the six triangle visits gives
the same marked traversal word on both sides (R-EXTERIOR-1 §4), so the successor of a good mark whose
successor is good is carried by the identification. -/
theorem EXT_markSucc_wall (hn : 3 ≤ n) (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n}
    (hgw : ExactTriangleVisitOrders P P' e f g hs) (a : Mark P)
    (ha : ¬ EXT_TriVisit e f g a) (hρ : ¬ EXT_TriVisit e f g (geoMarkSuccessor hP a)) :
    geoMarkSuccessor hP' (markTransport hs a) = markTransport hs (geoMarkSuccessor hP a) := by
  classical
  let _ := geoMarkLinearOrder hP'
  have hne : markTransport hs a ≠ markTransport hs (geoMarkSuccessor hP a) :=
    fun h => EXT_geoMarkSuccessor_ne hn hP a ((markTransport hs).injective h).symm
  have hgap : ∀ x ∈ (Finset.univ : Finset (Mark P')),
      ¬ ((markTransport hs a < x ∧ x < markTransport hs (geoMarkSuccessor hP a)) ∨
        (x < markTransport hs (geoMarkSuccessor hP a) ∧
          markTransport hs (geoMarkSuccessor hP a) < markTransport hs a) ∨
        (markTransport hs (geoMarkSuccessor hP a) < markTransport hs a ∧ markTransport hs a < x)) := by
    intro x _
    obtain ⟨y, rfl⟩ := (markTransport hs).surjective x
    have h1 := EXT_key_lt_wall hP hP' hgw a y (EXT_hab_of_good_left ha)
    have h2 := EXT_key_lt_wall hP hP' hgw y (geoMarkSuccessor hP a) (EXT_hab_of_good_right hρ)
    have h3 := EXT_key_lt_wall hP hP' hgw (geoMarkSuccessor hP a) a (EXT_hab_of_good_left hρ)
    change ¬ ((geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs y) ∧
        geoMarkKey hP' (markTransport hs y) < geoMarkKey hP' (markTransport hs (geoMarkSuccessor hP a))) ∨
      (geoMarkKey hP' (markTransport hs y) < geoMarkKey hP' (markTransport hs (geoMarkSuccessor hP a)) ∧
        geoMarkKey hP' (markTransport hs (geoMarkSuccessor hP a)) < geoMarkKey hP' (markTransport hs a)) ∨
      (geoMarkKey hP' (markTransport hs (geoMarkSuccessor hP a)) < geoMarkKey hP' (markTransport hs a) ∧
        geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs y)))
    rw [← h1, ← h2, ← h3]
    exact EXT_not_between_succ hP a y
  have hnext := EXT_sorted_next_of_no_cyclic_between (Finset.univ : Finset (Mark P'))
    (Finset.mem_univ _) (Finset.mem_univ _) hne hgap
  rw [geoMarkSuccessor_apply, geoNextMark_eq_list_next]
  convert hnext using 2
  rfl

/-- The selected exchange preserves the bad marks (a twin visit belongs to the same crossing). -/
theorem EXT_triVisit_selectedMarkPerm {e f g : ZMod n} (S : Finset (Crossing P)) (a : Mark P) :
    EXT_TriVisit e f g (selectedMarkPerm S a) ↔ EXT_TriVisit e f g a := by
  cases a with
  | inl i => exact Iff.rfl
  | inr v =>
    rw [selectedMarkPerm_visit]
    show (selectedVisitTwin S v).1.val ∈ triangleSupports e f g ↔ v.1.val ∈ triangleSupports e f g
    unfold selectedVisitTwin
    split_ifs <;> exact Iff.rfl

/-- **`ρ_Q` across the wall** at a good mark with a good successor (any support `Q`). -/
theorem EXT_succ_wall (hn : 3 ≤ n) (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n}
    (hgw : ExactTriangleVisitOrders P P' e f g hs) (Q : Finset (Crossing P)) (a : Mark P)
    (ha : ¬ EXT_TriVisit e f g a) (hρ : ¬ EXT_TriVisit e f g (geoSmoothingSuccessor hP Q a)) :
    geoSmoothingSuccessor hP' (transportSupport hs Q) (markTransport hs a) =
      markTransport hs (geoSmoothingSuccessor hP Q a) := by
  rw [geoSmoothingSuccessor_apply] at hρ
  rw [geoSmoothingSuccessor_apply, geoSmoothingSuccessor_apply, selectedMarkPerm_markTransport]
  exact EXT_markSucc_wall hn hP hP' hgw _ ((EXT_triVisit_selectedMarkPerm Q a).not.mpr ha) hρ

omit [NeZero n] in
theorem EXT_markTransport_symm_eq (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (b' : Mark P') :
    (markTransport hs).symm b' = markTransport (fun s => (hs s).symm) b' := by
  cases b' <;> rfl

omit [NeZero n] in
theorem EXT_transportSupport_symm (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (Q : Finset (Crossing P)) :
    transportSupport (fun s => (hs s).symm) (transportSupport hs Q) = Q := by
  ext x
  unfold transportSupport
  rw [Finset.mem_map_equiv, Finset.mem_map_equiv]
  exact Iff.rfl

/-- **Corner turns across the wall**: at a vertex corner the turn is `τ_i` of the polygon, at a
smoothing corner the crossing sign; both are wall-invariant on the punctured neighbourhood. -/
theorem EXT_turn_wall (hn : 3 ≤ n) (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hP)
    (hS' : transportSupport hs S ∈ CV.Ind hP') (q : GeoComponent hP S)
    (q' : GeoComponent hP' (transportSupport hs S))
    (hcl : (geoComponentCornerList hP S q).map (markTransport hs) =
      geoComponentCornerList hP' (transportSupport hs S) q')
    (hturnP : ∀ i, turn P' i = turn P i)
    (hsign : ∀ v : Visit P, v.1 ∈ S →
      crossingSign P' v.2.val (visitTwin v).2.val = crossingSign P v.2.val (visitTwin v).2.val) :
    ∀ k, turn (geoCornerPolygon hP' (transportSupport hs S) q') k =
      turn (geoCornerPolygon hP S q)
        (Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' (markTransport hs) S _ q q' hcl)) k) := by
  intro k
  have hm := EXT_cornerMark_eq' hP hP' (markTransport hs) S _ q q' hcl k
  set j := Equiv.cast (congrArg ZMod (EXT_cornerCount_eq hP hP' (markTransport hs) S _ q q' hcl)) k
  obtain ⟨_, hcorner⟩ := geoCornerMark_mem hP S q j
  rcases hmark : geoCornerMark hP S q j with i | v
  · rw [hmark, EXT_markTransport_vertex] at hm
    rw [CV.turn_vertex_of_traced hP' _ hn q' (CV.carrierword_traced hP' hS' q') k i hm,
      CV.turn_vertex_of_traced hP S hn q (CV.carrierword_traced hP hS q) j i hmark]
    exact hturnP i
  · rw [hmark, markTransport_visit] at hm
    rw [hmark, isTrueCorner_visit] at hcorner
    have hv' : (visitTransport hs v).1 ∈ transportSupport hs S := by
      rw [visitTransport_crossing, mem_transportSupport_iff]
      exact hcorner
    rw [CV.turn_visit_of_traced hP' _ hn q' (CV.carrierword_traced hP' hS' q') k _ hm hv',
      CV.turn_visit_of_traced hP S hn q (CV.carrierword_traced hP hS q) j v hmark hcorner,
      visitTransport_edge, ← visitTransport_visitTwin, visitTransport_edge]
    exact hsign v hcorner

end EXTWall

section EXTGuard

variable {E : CV.Event n}

/-- Sign constancy at a parameter `u` of the members outside the forced bundle: `G1` at every vertex and
`G5` at every crossing pair (lem:guardconst). -/
def EXT_GuardAt (E : CV.Event n) (u : E.Parameter) : Prop :=
  (∀ i : ZMod n, CV.G1 (E.curve u) i ≠ 0 ∧
    SignType.sign (CV.G1 (E.curve u) i) = SignType.sign (CV.G1 E.center i)) ∧
  (∀ i j : ZMod n, IsCrossing E.center {i, j} →
    CV.G5 (E.curve u) i j ≠ 0 ∧ SignType.sign (CV.G5 (E.curve u) i j) = SignType.sign (CV.G5 E.center i j))

theorem EXT_curve_eq_center (u : E.Parameter) (hu : u.val = 0) : E.curve u = E.center := by
  have : u = E.zeroParameter := Subtype.ext hu
  rw [this]
  rfl

/-- The four `G2` members of a remote pair are nonzero at every parameter (unconditional, outside `Z`). -/
theorem EXT_g2_ne_zero {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (u : E.Parameter) (a i : ZMod n) (h : i ≠ a ∧ i ≠ a + 1) : CV.G2 (E.curve u) a i ≠ 0 := by
  by_cases hu : u.val = 0
  · rw [EXT_curve_eq_center u hu]
    obtain ⟨t₀, ht₀⟩ := G1.exists_punctured_parameter E
    exact (CV.guardconst E (CV.Member.g2 a i h) ⟨t₀, ht₀, CV.Member.relevant_g2 _ a i h⟩
      (G1.g2_not_mem_zeroSet hE a i h)).1
  · exact (E.generic_punctured u hu).g2 h.1 h.2

/-- A crossing pair of one side is an active pair at every parameter, the centre included. -/
theorem EXT_crosses_all {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {t : E.Parameter} {i j : ZMod n} (hc : IsCrossing (E.curve t) {i, j}) (u : E.Parameter) :
    CV.Crosses (E.curve u) i j := by
  have hr : remote i j := crossing_pair_remote hc
  have hcu : IsCrossing (E.curve u) {i, j} := (hE.tripleEventData.crossing_set_constant t u _).mp hc
  obtain ⟨h0, h1, h2, h3'⟩ := remote_endpoints i j hr
  exact CV.crosses_of_meet hr ⟨EXT_g2_ne_zero hE u i j ⟨h0, h1⟩, EXT_g2_ne_zero hE u i (j + 1) ⟨h2, h3'⟩,
    EXT_g2_ne_zero hE u j i ⟨h0.symm, h2.symm⟩, EXT_g2_ne_zero hE u j (i + 1) ⟨h1.symm, h3'.symm⟩⟩
    ((isCrossing_pair _ i j hr).mp hcu)

/-- The Cramer parameter of an active pair is interior. -/
theorem EXT_edgeParameter_interior {P : LabelledTuple n} {i j : ZMod n} (hc : CV.Crosses P i j) :
    0 < edgeParameter P i j ∧ edgeParameter P i j < 1 := by
  obtain ⟨_, s, t, hs0, hs1, _, _, heq, hd⟩ := (CV.crosses_iff P i j).mp hc
  have h := (edgeParameters_of_intersection hd heq).1
  rw [h]
  exact ⟨hs0, hs1⟩

omit [NeZero n] in
theorem EXT_G5_swap (P : LabelledTuple n) (i j : ZMod n) : CV.G5 P i j = -CV.G5 P j i := by
  unfold CV.G5
  rw [det_swap]

/-- **The guard radius**: a radius on which `G1` at every vertex and `G5` at every crossing pair keep
their central signs (lem:guardconst, uniformly over the finitely many members). -/
theorem EXT_exists_guardRadius {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u := by
  rw [← E.eventually_center_iff_radius]
  obtain ⟨t₀, ht₀⟩ := G1.exists_punctured_parameter E
  apply Filter.Eventually.and
  · rw [Filter.eventually_all]
    intro i
    exact G1.eventually_sign_eq_of_not_mem (CV.Member.g1 i) ⟨t₀, ht₀, CV.Member.relevant_g1 _ i⟩
      (by rw [hE.1]; simp)
  · rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hc : IsCrossing E.center {i, j}
    · have hr : remote i j := crossing_pair_remote hc
      have hne : i ≠ j := (remote_endpoints i j hr).1.symm
      have hcross : CV.Crosses (E.curve t₀) i j := EXT_crosses_all hE hc t₀
      rcases CV.rep_lt_or_lt hne with hlt | hlt
      · have hev := G1.eventually_sign_eq_of_not_mem (CV.Member.g5 i j ⟨hr, hlt⟩)
          ⟨t₀, ht₀, Or.inr hcross⟩ (G1.g5_not_mem_zeroSet hE i j ⟨hr, hlt⟩)
        exact hev.mono fun u hu _ => hu
      · have hcross' : CV.Crosses (E.curve t₀) j i := EXT_crosses_all hE (by rw [Finset.pair_comm]; exact hc) t₀
        have hev := G1.eventually_sign_eq_of_not_mem (CV.Member.g5 j i ⟨remote_symm hr, hlt⟩)
          ⟨t₀, ht₀, Or.inr hcross'⟩ (G1.g5_not_mem_zeroSet hE j i ⟨remote_symm hr, hlt⟩)
        refine hev.mono fun u hu _ => ?_
        change CV.G5 (E.curve u) j i ≠ 0 ∧ SignType.sign (CV.G5 (E.curve u) j i) = SignType.sign (CV.G5 E.center j i) at hu
        rw [EXT_G5_swap (E.curve u) i j, EXT_G5_swap E.center i j, neg_ne_zero, Left.sign_neg, Left.sign_neg, hu.2]
        exact ⟨hu.1, rfl⟩
    · exact Filter.Eventually.of_forall fun u h => absurd h hc

/-- The vertex turns agree at any two guarded parameters. -/
theorem EXT_turn_eq_of_guard {u u' : E.Parameter} (hu : EXT_GuardAt E u) (hu' : EXT_GuardAt E u') (i : ZMod n) :
    turn (E.curve u') i = turn (E.curve u) i := by
  rw [turn_det, turn_det]
  exact ((hu'.1 i).2.trans (hu.1 i).2.symm)

/-- The crossing signs of a crossing pair agree at any two guarded parameters. -/
theorem EXT_G5_sign_eq_of_guard {u u' : E.Parameter} (hu : EXT_GuardAt E u) (hu' : EXT_GuardAt E u')
    {i j : ZMod n} (hc : IsCrossing E.center {i, j}) :
    SignType.sign (CV.G5 (E.curve u') i j) = SignType.sign (CV.G5 (E.curve u) i j) :=
  (hu'.2 i j hc).2.trans (hu.2 i j hc).2.symm

theorem EXT_det_pos_iff_of_guard {u u' : E.Parameter} (hu : EXT_GuardAt E u) (hu' : EXT_GuardAt E u')
    {i j : ZMod n} (hc : IsCrossing E.center {i, j}) :
    0 < det (edge (E.curve u) i) (edge (E.curve u) j) ↔ 0 < det (edge (E.curve u') i) (edge (E.curve u') j) := by
  have h := EXT_G5_sign_eq_of_guard hu hu' hc
  unfold CV.G5 at h
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

end EXTGuard

section EXTRecord

variable {P P' : LabelledTuple n}

/-- **Two carriers on the two sides with corresponding retained crossings have positive lifts with the same
HOMFLY polynomial** when the traversal order of the visits of those crossings and the divide signs at them
are carried by the identification: the identity on parent visits is a record isomorphism
(CV:def:record (a)–(d), assembled by `recordIsoOfData`) and the accepted `gausscode_polynomial` applies. -/
theorem EXT_homfly_wall (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
    (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
    (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
    (hX : geoCarrierCrossings hG'.cg T' q' =
      (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
    (hkey : ∀ v w : Visit P, v.1 ∈ geoCarrierCrossings hG.cg T q → w.1 ∈ geoCarrierCrossings hG.cg T q →
      (geometricVisitKey hG.cg v < geometricVisitKey hG.cg w ↔
        geometricVisitKey hG'.cg (visitTransport hs v) < geometricVisitKey hG'.cg (visitTransport hs w)))
    (hdet : ∀ v : Visit P, v.1 ∈ geoCarrierCrossings hG.cg T q →
      (0 < det (edge P v.2.val) (edge P (visitTwin v).2.val) ↔
        0 < det (edge P' v.2.val) (edge P' (visitTwin v).2.val))) :
    homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q) := by
  let ψ : {w : Visit P // w.1 ∈ geoCarrierCrossings hG.cg T q} ≃
      {w : Visit P' // w.1 ∈ geoCarrierCrossings hG'.cg T' q'} :=
    (visitTransport hs).subtypeEquiv fun w => by
      rw [hX, visitTransport_crossing, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  let Φ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit :=
    (CV.liftVisitEquiv hn hG hT q).trans (ψ.trans (CV.liftVisitEquiv hn hG' hT' q').symm)
  have hΦ : ∀ v, CV.liftVisit hn hG' hT' q' (Φ v) = visitTransport hs (CV.liftVisit hn hG hT q v) := by
    intro v
    show CV.liftVisit hn hG' hT' q'
      ((CV.liftVisitEquiv hn hG' hT' q').symm (ψ (CV.liftVisitEquiv hn hG hT q v))) = _
    rw [CV.liftVisit_symm]
    rfl
  have hmem : ∀ v, (CV.liftVisit hn hG hT q v).1 ∈ geoCarrierCrossings hG.cg T q :=
    CV.liftVisit_mem hn hG hT q
  have hdata : CV.IsRecordIsoData (geoPositiveLift hn hG hT q) (geoPositiveLift hn hG' hT' q') Φ :=
    { cyclic_order := fun v w u hb => by
        rw [CV.visitBetween_iff_key, hΦ, hΦ, hΦ]
        rw [CV.visitBetween_iff_key] at hb
        unfold Link.cycBetween at hb ⊢
        rw [← hkey _ _ (hmem v) (hmem w), ← hkey _ _ (hmem w) (hmem u), ← hkey _ _ (hmem u) (hmem v)]
        exact hb
      double_points :=
        (CV.carriesDoublePoints_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG' hT' q').record) Φ).2 fun v => by
          apply CV.liftVisit_injective hn hG' hT' q'
          change CV.liftVisit hn hG' hT' q' (Φ ((geoPositiveLift hn hG hT q).twin v)) =
            CV.liftVisit hn hG' hT' q' ((geoPositiveLift hn hG' hT' q').twin (Φ v))
          rw [hΦ, CV.liftVisit_twin, CV.liftVisit_twin, hΦ, visitTransport_visitTwin]
      over_under :=
        (CV.carriesOverUnder_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG' hT' q').record) Φ).2 fun v => by
          change (geoPositiveLift hn hG' hT' q').overBit (Φ v) = (geoPositiveLift hn hG hT q).overBit v
          rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΦ,
            visitTransport_edge, ← visitTransport_visitTwin, visitTransport_edge]
          exact (hdet _ (hmem v)).symm
      signs := fun v => by
        change (geoPositiveLift hn hG' hT' q').sign (Φ v).1 = (geoPositiveLift hn hG hT q).sign v.1
        rw [geoPositiveLift_sign, geoPositiveLift_sign] }
  exact (CV.gausscode_polynomial _ _ (geoPositiveLift_componentCount hn hG hT q)
    (geoPositiveLift_componentCount hn hG' hT' q')
    (CV.recordIsoOfData (geoPositiveLift_componentCount hn hG hT q)
      (geoPositiveLift_componentCount hn hG' hT' q') Φ hdata)).symm

/-- The piece polynomials of corresponding pieces with triangle-free labels agree across the wall. -/
theorem EXT_pieceHomfly_wall (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (hkey : ∀ v w : Visit P, v.1.val ∉ triangleSupports e f g → w.1.val ∉ triangleSupports e f g →
      (geometricVisitKey hG.crossingGeometry v < geometricVisitKey hG.crossingGeometry w ↔
        geometricVisitKey hG'.crossingGeometry (visitTransport hs v) <
          geometricVisitKey hG'.crossingGeometry (visitTransport hs w)))
    (hdet : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)))
    (H : CV.Piece hG.crossingGeometry S) (H' : CV.Piece hG'.crossingGeometry S')
    (hHT : ∀ c ∈ CV.pieceLabels hG.crossingGeometry S H, c.val ∉ triangleSupports e f g)
    (hH' : CV.pieceLabels hG'.crossingGeometry S' H' =
      (CV.pieceLabels hG.crossingGeometry S H).map (crossingTransport hs).toEmbedding) :
    CV.pieceHomfly hn (hG'.diagrammatic hn) hS' H' = CV.pieceHomfly hn (hG.diagrammatic hn) hS H := by
  unfold CV.pieceHomfly CV.pieceDiagram
  refine EXT_homfly_wall hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
    (CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn)) hs
    (CV.pieceSupport_geoIndependent (hG.diagrammatic hn) hS H)
    (CV.pieceSupport_geoIndependent (hG'.diagrammatic hn) hS' H') _ _ ?_ ?_ ?_
  · rw [CV.pieceCarrier_geoCarrierCrossings, CV.pieceCarrier_geoCarrierCrossings]
    exact hH'
  · intro v w hv hw
    rw [CV.pieceCarrier_geoCarrierCrossings] at hv hw
    exact hkey v w (hHT _ hv) (hHT _ hw)
  · intro v hv
    have hc : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rwa [visit_crossing_val_eq_pair v] at h
    exact hdet _ _ hc

end EXTRecord

section EXTRotation

variable {E : CV.Event n}

theorem EXT_seg_mem (t t' : E.Parameter) (u : unitInterval) :
    t.val + u.val * (t'.val - t.val) ∈ Set.Ioo (-E.radius) E.radius := by
  obtain ⟨hm0, hm1⟩ := t.property
  obtain ⟨hp0, hp1⟩ := t'.property
  have hu0 := unitInterval.nonneg u
  have hu1 := unitInterval.le_one u
  rcases le_total t.val t'.val with h | h
  · have h1 := mul_nonneg hu0 (sub_nonneg.mpr h)
    have h2 := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr h)
    constructor <;> nlinarith
  · have h1 := mul_nonpos_of_nonneg_of_nonpos hu0 (sub_nonpos.mpr h)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu1) (sub_nonpos.mpr h)
    constructor <;> nlinarith

/-- The affine parameter path `u ↦ t + u (t' − t)` through the wall. -/
def EXT_seg (t t' : E.Parameter) (u : unitInterval) : E.Parameter :=
  ⟨t.val + u.val * (t'.val - t.val), EXT_seg_mem t t' u⟩

theorem EXT_seg_zero (t t' : E.Parameter) : EXT_seg t t' 0 = t := by
  apply Subtype.ext
  simp [EXT_seg]

theorem EXT_seg_one (t t' : E.Parameter) : EXT_seg t t' 1 = t' := by
  apply Subtype.ext
  simp [EXT_seg]

theorem EXT_continuous_seg (t t' : E.Parameter) : Continuous (EXT_seg t t') :=
  (continuous_const.add (continuous_subtype_val.mul continuous_const)).subtype_mk _

theorem EXT_seg_abs_lt {δ : ℝ} {t t' : E.Parameter} (ht : |t.val| < δ) (ht' : |t'.val| < δ)
    (u : unitInterval) : |(EXT_seg t t' u).val| < δ := by
  have hu0 := unitInterval.nonneg u
  have hu1 := unitInterval.le_one u
  rw [abs_lt] at ht ht' ⊢
  change -δ < t.val + u.val * (t'.val - t.val) ∧ t.val + u.val * (t'.val - t.val) < δ
  have h1 := mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ t'.val + δ)
  have h2 := mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ δ - t'.val)
  have h3 := mul_nonneg (sub_nonneg.mpr hu1) (by linarith : (0 : ℝ) ≤ t.val + δ)
  have h4 := mul_nonneg (sub_nonneg.mpr hu1) (by linarith : (0 : ℝ) ≤ δ - t.val)
  constructor <;> nlinarith

omit [NeZero n] in
theorem EXT_regularPair_of_det {u v : Plane} (hd : det u v ≠ 0) : RegularPair u v := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply hd
    simp [det]
  · rintro rfl
    apply hd
    simp [det]
  · rintro ⟨r, _, rfl⟩
    exact hd (det_smul_self u r)

variable {P : LabelledTuple n}

/-- The parameter of a corner mark along the edge of its outgoing slot. -/
noncomputable def EXT_paOut (R : LabelledTuple n) : Mark P → ℝ
  | Sum.inl _ => 0
  | Sum.inr v => edgeParameter R (visitTwin v).2.val v.2.val

/-- The parameter of a corner mark along the edge of its incoming segment. -/
noncomputable def EXT_pbIn (R : LabelledTuple n) : Mark P → ℝ
  | Sum.inl _ => 1
  | Sum.inr w => edgeParameter R w.2.val (visitTwin w).2.val

theorem EXT_markPoint_out (hP : CrossingGeometry P) (S : Finset (Crossing P)) (R : LabelledTuple n)
    (a : Mark P) (hsel : ∀ v : Visit P, a = Sum.inr v → v.1 ∈ S)
    (hdet : ∀ v : Visit P, a = Sum.inr v → det (edge R v.2.val) (edge R (visitTwin v).2.val) ≠ 0) :
    geoMarkPoint R a = edgePoint R (geoOutSlot hP S a).1 (EXT_paOut R a) := by
  cases a with
  | inl i =>
    rw [geoOutSlot_vertex, geoMarkPoint_vertex]
    show R i = edgePoint R i 0
    rw [edgePoint_zero]
  | inr v =>
    rw [geoOutSlot_selected hP S v (hsel v rfl), geoMarkPoint_visit]
    exact edgeParameters_intersection R _ _ (hdet v rfl)

theorem EXT_markPoint_in (hn : 3 ≤ n) (hP : CrossingGeometry P) (R : LabelledTuple n) (b : Mark P) :
    geoMarkPoint R b = edgePoint R (geoInEdge hP b) (EXT_pbIn R b) := by
  cases b with
  | inl j =>
    rw [geoInEdge_vertex hn, geoMarkPoint_vertex]
    show R j = edgePoint R (j - 1) 1
    rw [edgePoint_one, sub_add_cancel]
  | inr w =>
    rw [geoInEdge_visit hn, geoMarkPoint_visit]
    rfl

/-- The `k`-th edge of the corner polygon read on any polygon `R`: a multiple of the edge of the
outgoing slot of the `k`-th corner. -/
theorem EXT_familyEdge (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (R : LabelledTuple n)
    (hdetR : ∀ v : Visit P, v.1 ∈ S → det (edge R v.2.val) (edge R (visitTwin v).2.val) ≠ 0)
    (k : ZMod (geoCornerCount hP S q)) :
    edge (fun j => geoMarkPoint R (geoCornerMark hP S q j)) k =
      (EXT_pbIn R (geoCornerMark hP S q (k + 1)) - EXT_paOut R (geoCornerMark hP S q k)) •
        edge R (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  have hab := geoCornerPolygon_outEdge_eq_inEdge_of_independent hn hP hS q k
  have hcorner := (geoCornerMark_mem hP S q k).2
  show geoMarkPoint R (geoCornerMark hP S q (k + 1)) - geoMarkPoint R (geoCornerMark hP S q k) = _
  rw [EXT_markPoint_in hn hP R, EXT_markPoint_out hP S R (geoCornerMark hP S q k) ?_ ?_, ← hab,
    edgePoint_sub_edgePoint]
  · intro v hv
    rw [hv, isTrueCorner_visit] at hcorner
    exact hcorner
  · intro v hv
    rw [hv, isTrueCorner_visit] at hcorner
    exact hdetR v hcorner

/-- At the polygon itself the corner parameters increase along every edge of the corner polygon
(`geoCornerPolygon_edge_smul`). -/
theorem EXT_pa_lt_pb_self (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    EXT_paOut P (geoCornerMark hP S q k) < EXT_pbIn P (geoCornerMark hP S q (k + 1)) := by
  obtain ⟨c, hc, hedge⟩ := geoCornerPolygon_edge_smul hn hP hS q k
  have hF : (fun j => geoMarkPoint P (geoCornerMark hP S q j)) = geoCornerPolygon hP S q := by
    funext j
    rw [geoMarkPoint_self hP]
    rfl
  have h := EXT_familyEdge hn hP hS q P (fun v _ => CV.det_visit_twin_ne_zero hP v) k
  rw [hF, hedge] at h
  have hne : edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1 ≠ 0 := hP.1 _
  have h0 : (EXT_pbIn P (geoCornerMark hP S q (k + 1)) - EXT_paOut P (geoCornerMark hP S q k) - c) •
      edge P (geoOutSlot hP S (geoCornerMark hP S q k)).1 = 0 := by
    rw [sub_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · linarith [sub_eq_zero.mp h1]
  · exact absurd h1 hne

/-- The corner parameters increase along every edge at every parameter of the event (the order of two
crossings of `S` on a common edge is wall-invariant, R-LOC-2 (3); an interior crossing parameter
stays in `(0,1)`). -/
theorem EXT_pa_lt_pb_all {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hn : 3 ≤ n) {t : E.Parameter} (ht : t.val ≠ 0) {S : Finset (Crossing (E.curve t))}
    (hS : GeoIndependent (geomAt E t ht) S) (hST : ∀ x ∈ S, x.val ∉ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht) S) (k : ZMod (geoCornerCount (geomAt E t ht) S q)) (u : E.Parameter) :
    EXT_paOut (E.curve u) (geoCornerMark (geomAt E t ht) S q k) <
      EXT_pbIn (E.curve u) (geoCornerMark (geomAt E t ht) S q (k + 1)) := by
  have h0 := EXT_pa_lt_pb_self hn (geomAt E t ht) hS q k
  have hab := geoCornerPolygon_outEdge_eq_inEdge_of_independent hn (geomAt E t ht) hS q k
  have hTE := hE.tripleEventData
  have hacorner := (geoCornerMark_mem (geomAt E t ht) S q k).2
  have hbcorner := (geoCornerMark_mem (geomAt E t ht) S q (k + 1)).2
  rcases hma : geoCornerMark (geomAt E t ht) S q k with i | v <;>
    rcases hmb : geoCornerMark (geomAt E t ht) S q (k + 1) with j | w
  · show (0 : ℝ) < 1
    exact zero_lt_one
  · show (0 : ℝ) < edgeParameter (E.curve u) w.2.val (visitTwin w).2.val
    have hc : IsCrossing (E.curve t) {w.2.val, (visitTwin w).2.val} := by
      rw [← visit_crossing_val_eq_pair]
      exact w.1.property
    exact (EXT_edgeParameter_interior (EXT_crosses_all hE hc u)).1
  · show edgeParameter (E.curve u) (visitTwin v).2.val v.2.val < 1
    have hc : IsCrossing (E.curve t) {(visitTwin v).2.val, v.2.val} := by
      rw [Finset.pair_comm, ← visit_crossing_val_eq_pair]
      exact v.1.property
    exact (EXT_edgeParameter_interior (EXT_crosses_all hE hc u)).2
  · show edgeParameter (E.curve u) (visitTwin v).2.val v.2.val <
      edgeParameter (E.curve u) w.2.val (visitTwin w).2.val
    rw [hma, isTrueCorner_visit] at hacorner
    rw [hma, hmb] at hab h0
    rw [geoOutSlot_selected _ S v hacorner, geoInEdge_visit hn] at hab
    change edgeParameter (E.curve t) (visitTwin v).2.val v.2.val <
      edgeParameter (E.curve t) w.2.val (visitTwin w).2.val at h0
    rw [← hab] at h0 ⊢
    rw [← CV.crossParam_eq_edgeParameter, ← CV.crossParam_eq_edgeParameter] at h0 ⊢
    have hvc : IsCrossing (E.curve t) {(visitTwin v).2.val, v.2.val} := by
      rw [Finset.pair_comm, ← visit_crossing_val_eq_pair]
      exact v.1.property
    have hwc : IsCrossing (E.curve t) {(visitTwin v).2.val, (visitTwin w).2.val} := by
      rw [hab, ← visit_crossing_val_eq_pair]
      exact w.1.property
    have hnot : ¬ (({(visitTwin v).2.val, v.2.val} : Finset (ZMod n)) ∈
        ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n))) ∧
        ({(visitTwin v).2.val, (visitTwin w).2.val} : Finset (ZMod n)) ∈
        ({{e, f}, {e, g}, {f, g}} : Finset (Finset (ZMod n)))) := by
      intro h
      apply hST v.1 hacorner
      rw [visit_crossing_val_eq_pair v, Finset.pair_comm]
      exact h.1
    exact (hTE.other_orders_persist t u _ _ _ hvc hwc hnot).mp h0

/-- **The corner family is regular at every parameter of the event** (the wall included): every edge is a
positive multiple of a polygon edge, and consecutive edges meet at a vertex turn `G1 ≠ 0` or at a crossing
`G5 ≠ 0`, both outside the forced bundle. -/
theorem EXT_family_regular {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hn : 3 ≤ n) {t : E.Parameter} (ht : t.val ≠ 0) {S : Finset (Crossing (E.curve t))}
    (hS : GeoIndependent (geomAt E t ht) S) (hST : ∀ x ∈ S, x.val ∉ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht) S) (u : E.Parameter) (hguard : EXT_GuardAt E u) :
    Regular (fun j => geoMarkPoint (E.curve u) (geoCornerMark (geomAt E t ht) S q j)) := by
  have hTE := hE.tripleEventData
  have hdetR : ∀ v : Visit (E.curve t), v.1 ∈ S →
      det (edge (E.curve u) v.2.val) (edge (E.curve u) (visitTwin v).2.val) ≠ 0 := by
    intro v _
    have hc : IsCrossing E.center {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rw [visit_crossing_val_eq_pair v] at h
      exact (hTE.crossing_set_constant t E.zeroParameter _).mp h
    exact (hguard.2 _ _ hc).1
  intro k
  rw [EXT_familyEdge hn _ hS q _ hdetR (k - 1), EXT_familyEdge hn _ hS q _ hdetR k, sub_add_cancel]
  apply EXT_regularPair_of_det
  rw [CV.det_smul_left', CV.det_smul_right']
  have hc1 := EXT_pa_lt_pb_all hE hn ht hS hST q (k - 1) u
  have hc2 := EXT_pa_lt_pb_all hE hn ht hS hST q k u
  rw [sub_add_cancel] at hc1
  refine mul_ne_zero (sub_pos.mpr hc1).ne' (mul_ne_zero (sub_pos.mpr hc2).ne' ?_)
  rw [geoCornerPolygon_outEdge_eq_inEdge_of_independent hn _ hS q (k - 1), sub_add_cancel]
  have hacorner := (geoCornerMark_mem (geomAt E t ht) S q k).2
  rcases hma : geoCornerMark (geomAt E t ht) S q k with i | v
  · rw [geoInEdge_vertex hn, geoOutSlot_vertex]
    exact (hguard.1 i).1
  · rw [hma, isTrueCorner_visit] at hacorner
    rw [geoInEdge_visit hn, geoOutSlot_selected _ S v hacorner]
    exact hdetR v hacorner

/-- The corner family is continuous along the parameter path (vertices by projection, crossing points by
Cramer's rule at nonvanishing `G5`). -/
theorem EXT_family_continuous {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    {t t' : E.Parameter} (ht : t.val ≠ 0) {S : Finset (Crossing (E.curve t))}
    (q : GeoComponent (geomAt E t ht) S) {δ : ℝ}
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u) (hδt : |t.val| < δ) (hδt' : |t'.val| < δ) :
    Continuous (fun u : unitInterval =>
      (fun j => geoMarkPoint (E.curve (EXT_seg t t' u)) (geoCornerMark (geomAt E t ht) S q j))) := by
  have hTE := hE.tripleEventData
  apply continuous_pi
  intro k
  have hγ : Continuous (fun u : unitInterval => E.curve (EXT_seg t t' u)) :=
    E.continuous_curve.comp (EXT_continuous_seg t t')
  rcases hma : geoCornerMark (geomAt E t ht) S q k with i | v
  · simp only [geoMarkPoint_vertex]
    exact (continuous_apply i).comp hγ
  · simp only [geoMarkPoint_visit]
    rw [continuous_iff_continuousAt]
    intro u
    have hc : IsCrossing E.center {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rw [visit_crossing_val_eq_pair v] at h
      exact (hTE.crossing_set_constant t E.zeroParameter _).mp h
    have hd : det (edge (E.curve (EXT_seg t t' u)) v.2.val)
        (edge (E.curve (EXT_seg t t' u)) (visitTwin v).2.val) ≠ 0 :=
      ((hguard _ (EXT_seg_abs_lt hδt hδt' u)).2 _ _ hc).1
    have hcont : ContinuousAt (fun R : LabelledTuple n =>
        edgePoint R v.2.val (edgeParameter R v.2.val (visitTwin v).2.val)) (E.curve (EXT_seg t t' u)) := by
      unfold edgePoint
      exact (continuous_vertex _).continuousAt.add
        ((continuousAt_edgeParameter_of_det hd).smul (continuous_edge _).continuousAt)
    exact hcont.comp (f := fun u : unitInterval => E.curve (EXT_seg t t' u)) hγ.continuousAt

/-- **The rotation number of an exterior carrier's corner polygon is the same on both sides of the wall**
(R-EXTERIOR-1 §4, "for rotation …"): the corner polygon deforms continuously and regularly through the
wall, so its rotation number (an integer) is constant (`rotationNumber_family_constant`). -/
theorem EXT_rotation_wall {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hn : 3 ≤ n) {t t' : E.Parameter} (ht : t.val ≠ 0) (ht' : t'.val ≠ 0) {δ : ℝ}
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u) (hδt : |t.val| < δ) (hδt' : |t'.val| < δ)
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ CV.Ind (geomAt E t ht))
    (hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g)
    (q : GeoComponent (geomAt E t ht) Q) (q' : GeoComponent (geomAt E t' ht') (transportSupport hs Q))
    (hcl : (geoComponentCornerList (geomAt E t ht) Q q).map (markTransport hs) =
      geoComponentCornerList (geomAt E t' ht') (transportSupport hs Q) q') :
    rotationNumber (geoCornerPolygon (geomAt E t' ht') (transportSupport hs Q) q') =
      rotationNumber (geoCornerPolygon (geomAt E t ht) Q q) := by
  have hS : GeoIndependent (geomAt E t ht) Q := CV.geoIndependent_of_mem_Ind _ hQ
  let F : unitInterval → LabelledTuple (geoCornerCount (geomAt E t ht) Q q) :=
    fun u j => geoMarkPoint (E.curve (EXT_seg t t' u)) (geoCornerMark (geomAt E t ht) Q q j)
  have hF0 : F 0 = geoCornerPolygon (geomAt E t ht) Q q := by
    funext j
    show geoMarkPoint (E.curve (EXT_seg t t' 0)) _ = _
    rw [EXT_seg_zero, geoMarkPoint_self (geomAt E t ht)]
    rfl
  have hF1 : geoCornerPolygon (geomAt E t' ht') (transportSupport hs Q) q' =
      geoRecast (EXT_cornerCount_eq (geomAt E t ht) (geomAt E t' ht') (markTransport hs) Q _ q q' hcl) (F 1) := by
    rw [EXT_cornerPolygon_eq (geomAt E t ht) (geomAt E t' ht') (markTransport hs) Q _ q q' hcl]
    congr 1
    funext j
    show _ = geoMarkPoint (E.curve (EXT_seg t t' 1)) _
    rw [EXT_seg_one, geoMarkPoint_eq (geomAt E t' ht') hs]
  have hcont : Continuous F := EXT_family_continuous hE ht q hguard hδt hδt'
  have hreg : ∀ u, Regular (F u) := fun u =>
    EXT_family_regular hE hn ht hS hQT q _ (hguard _ (EXT_seg_abs_lt hδt hδt' u))
  rw [hF1, rotationNumber_geoRecast, ← hF0]
  exact rotationNumber_family_constant hcont hreg 1 0

end EXTRotation

section EXTAssembly

variable {E : CV.Event n}

/-- The retained crossings of a triangle-disjoint carrier are triangle-free. -/
theorem EXT_carrierCrossings_triFree {P : LabelledTuple n} (hP : CrossingGeometry P)
    (S : Finset (Crossing P)) {e f g : ZMod n} (q : GeoComponent hP S)
    (hq : TriangleDisjoint hP S e f g q) :
    ∀ c ∈ geoCarrierCrossings hP S q, c.val ∉ triangleSupports e f g := by
  intro c hc hcT
  obtain ⟨i, -, -⟩ := crossing_visits_exist c
  exact hq ⟨c, i⟩ hcT (((mem_geoCarrierCrossings hP S q c).mp hc).2 ⟨c, i⟩ rfl)

theorem EXT_oppositeSides_symm {t t' : E.Parameter} (h : OppositeSides E t t') : OppositeSides E t' t := by
  unfold OppositeSides at h ⊢
  rw [mul_comm]
  exact h

/-- **The exterior factor of the base row is the same on both sides of the wall** (R-EXTERIOR-1 §4). -/
theorem EXT_exteriorFactor_wall {e f g : ZMod n} {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g)
    (hn : 3 ≤ n) {δ : ℝ} (hL : LocalizationData E e f g δ)
    (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ CV.Ind (geomAt E t ht.1))
    (hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g)
    (hQ' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1)) :
    exteriorFactor hn (genericAt E t' ht'.1) hQ' e f g = exteriorFactor hn (genericAt E t ht.1) hQ e f g := by
  classical
  have hTE := hE.tripleEventData
  set hG := genericAt E t ht.1
  set hG' := genericAt E t' ht'.1
  set hP := geomAt E t ht.1
  set hP' := geomAt E t' ht'.1
  set hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hgw : ExactTriangleVisitOrders (E.curve t) (E.curve t') e f g hs := hL.gauss_words t t' ht ht' hop hs
  have hgw' : ExactTriangleVisitOrders (E.curve t') (E.curve t) e f g hs' :=
    hL.gauss_words t' t ht' ht (EXT_oppositeSides_symm hop) hs'
  have hgt := hguard t ht.2
  have hgt' := hguard t' ht'.2
  have hcenter : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} → IsCrossing E.center {i, j} :=
    fun i j h => (hTE.crossing_set_constant t E.zeroParameter _).mp h
  have hcomm : ∀ a, ¬ EXT_TriVisit e f g a → ¬ EXT_TriVisit e f g (geoSmoothingSuccessor hP Q a) →
      geoSmoothingSuccessor hP' (transportSupport hs Q) (markTransport hs a) =
        markTransport hs (geoSmoothingSuccessor hP Q a) :=
    fun a ha hρ => EXT_succ_wall hn hP hP' hgw Q a ha hρ
  have hcomm' : ∀ b', ¬ EXT_TriVisit e f g ((markTransport hs).symm b') →
      ¬ EXT_TriVisit e f g ((markTransport hs).symm (geoSmoothingSuccessor hP' (transportSupport hs Q) b')) →
      geoSmoothingSuccessor hP Q ((markTransport hs).symm b') =
        (markTransport hs).symm (geoSmoothingSuccessor hP' (transportSupport hs Q) b') := by
    intro b' hb' hρ
    rw [EXT_triVisit_markTransport_symm] at hb' hρ
    rw [EXT_markTransport_symm_eq, EXT_markTransport_symm_eq]
    have h := EXT_succ_wall hn hP' hP hgw' (transportSupport hs Q) b' hb' hρ
    rwa [EXT_transportSupport_symm] at h
  have hkeyAll : ∀ v w : Visit (E.curve t), v.1.val ∉ triangleSupports e f g → w.1.val ∉ triangleSupports e f g →
      (geometricVisitKey hG.crossingGeometry v < geometricVisitKey hG.crossingGeometry w ↔
        geometricVisitKey hG'.crossingGeometry (visitTransport hs v) <
          geometricVisitKey hG'.crossingGeometry (visitTransport hs w)) := by
    intro v w hv hw
    exact EXT_key_lt_wall hP hP' hgw (Sum.inr v) (Sum.inr w)
      (EXT_hab_of_good_left (a := Sum.inr v) (b := Sum.inr w) hv)
  have hdetAll : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔ 0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hc => EXT_det_pos_iff_of_guard hgt hgt' (hcenter i j hc)
  refine EXT_exteriorFactor_eq hn hG hG' hs hQ hQ' e f g hcomm hcomm' ?_
  intro q hq
  set q' := EXT_corr hP hP' (markTransport hs) Q (transportSupport hs Q) q
  have hqav : EXT_Avoids hP Q (fun a => ¬ EXT_TriVisit e f g a) q :=
    (EXT_triangleDisjoint_iff hP Q e f g q).mp hq
  have hblock : ∀ b, geoOwner hP' (transportSupport hs Q) (markTransport hs b) = q' ↔ geoOwner hP Q b = q :=
    EXT_corr_iff hP hP' (markTransport hs) Q _ _ hcomm q hqav
  have hlist : (geoComponentMarkList hP Q q).map (markTransport hs) =
      geoComponentMarkList hP' (transportSupport hs Q) q' := by
    refine EXT_markList_map hP hP' (markTransport hs) Q _ q q' hblock ?_
    intro a b ha _
    exact EXT_key_lt_wall hP hP' hgw a b (EXT_hab_of_good_left (hqav a ha))
  have hcorner : ∀ a, geoOwner hP Q a = q →
      (IsTrueCorner (transportSupport hs Q) (markTransport hs a) ↔ IsTrueCorner Q a) :=
    fun a _ => isTrueCorner_markTransport hs Q a
  have hcl : (geoComponentCornerList hP Q q).map (markTransport hs) =
      geoComponentCornerList hP' (transportSupport hs Q) q' :=
    EXT_cornerList_map hP hP' (markTransport hs) Q _ q q' hlist hcorner
  have hc := EXT_cornerCount_eq hP hP' (markTransport hs) Q _ q q' hcl
  have hsel : ∀ x : Crossing (E.curve t), (∀ v : Visit (E.curve t), v.1 = x → geoOwner hP Q (Sum.inr v) = q) →
      (crossingTransport hs x ∈ transportSupport hs Q ↔ x ∈ Q) :=
    fun x _ => mem_transportSupport_iff hs Q x
  have hX' : geoCarrierCrossings hP' (transportSupport hs Q) q' =
      (geoCarrierCrossings hP Q q).map (crossingTransport hs).toEmbedding :=
    EXT_carrierCrossings_map hP hP' hs Q _ q q' hblock hsel
  have htri := EXT_carrierCrossings_triFree hP Q q hq
  have hX : EXT_PieceSetting hP hP' hs Q (transportSupport hs Q) (geoCarrierCrossings hP Q q) :=
    EXT_pieceSetting hP hP' hs hQ hQ' q q' hX'
      (fun c hc d hd => F1.graph_on_W_same hL t t' ht ht' hop hs c d (htri c hc) (htri d hd))
  have hturnP : ∀ i, turn (E.curve t') i = turn (E.curve t) i := EXT_turn_eq_of_guard hgt hgt'
  have hsign : ∀ v : Visit (E.curve t), v.1 ∈ Q →
      crossingSign (E.curve t') v.2.val (visitTwin v).2.val = crossingSign (E.curve t) v.2.val (visitTwin v).2.val := by
    intro v _
    have hc : IsCrossing (E.curve t) {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rwa [visit_crossing_val_eq_pair v] at h
    exact EXT_G5_sign_eq_of_guard hgt hgt' (hcenter _ _ hc)
  have hweight : CV.weight hP' (transportSupport hs Q) q' = CV.weight hP Q q :=
    EXT_weight_eq hP hP' Q _ q q' hc (EXT_turn_wall hn hP hP' hs hQ hQ' q q' hcl hturnP hsign)
  have hR : CV.carrierR hn hG' hQ' q' = CV.carrierR hn hG hQ q :=
    EXT_carrierR_eq hn hG hG' hQ hQ' q q'
      (EXT_rotation_wall hE hn ht.1 ht'.1 hguard ht.2 ht'.2 hs hQ hQT q q' hcl)
  have hw : CV.groupedWrithe hG' q' = CV.groupedWrithe hG q :=
    EXT_groupedWrithe_eq hG hG' hs q q' hX hX'
  have hp : CV.groupedPoly hn hG' hQ' q' = CV.groupedPoly hn hG hQ q := by
    refine EXT_groupedPoly_eq hn hG hG' hs hQ hQ' q q' hX hX' ?_
    intro H H' hHX hH'
    exact EXT_pieceHomfly_wall hn hG hG' hs hQ hQ' hkeyAll hdetAll H H' (fun c hc => htri c (hHX hc)) hH'
  rw [hweight, EXT_Omega1_eq hn hG hG' hQ hQ' q q' hR hw hp]

/-- **Row 168, field `wall_invariant`**: "and its common value is the same for `sigma=-` and `sigma=+`". -/
theorem EXT_168_wall_invariant (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u)
    {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ (A : Finset (Crossing (E.curve t))) (A' : Finset (Crossing (E.curve t'))),
      A ⊆ triangleCrossings (E.curve t) e f g → A' ⊆ triangleCrossings (E.curve t') e f g →
      ∀ (hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1))
        (hA' : transportSupport hs Q ∪ A' ∈ CV.Ind (geomAt E t' ht'.1)),
        exteriorFactor hn (genericAt E t ht.1) hA e f g =
          exteriorFactor hn (genericAt E t' ht'.1) hA' e f g := by
  intro t t' ht ht' hop hs Q hQ A A' hAT hAT' hA hA'
  have hQind : Q ∈ CV.Ind (geomAt E t ht.1) := mem_Ind_of_mem_outsideSupports hQ
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := by
    intro x hx hxT
    exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  have hQ'ind : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) :=
    PRE_mem_Ind_of_subset hA' Finset.subset_union_left
  have hQ'T : ∀ x ∈ transportSupport hs Q, x.val ∉ triangleSupports e f g := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact hQT y hy
  rw [← EXT_exteriorFactor_eq_base hn (genericAt E t ht.1) hQT
      (fun x hx => (P1.mem_triangleCrossings x).mp (hAT hx)) hA hQind,
    ← EXT_exteriorFactor_eq_base hn (genericAt E t' ht'.1) hQ'T
      (fun x hx => (P1.mem_triangleCrossings x).mp (hAT' hx)) hA' hQ'ind]
  exact (EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs hQind hQT hQ'ind).symm

/-- **Row 168, field `factorization`**: "Consequently every full-availability row factors exactly as
`tau_sigma(A) = C_Q * rho_sigma(A)`", with `C_Q` the exterior factor of the base row on side `t`. -/
theorem EXT_168_factorization (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hguard : ∀ u : E.Parameter, |u.val| < δ → EXT_GuardAt E u)
    {h3 h4e h4f h4g} (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
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
              touchingFactor hn (genericAt E t' ht'.1) hA' e f g) := by
  intro t t' ht ht' hop hs Q hQ _
  have hQT : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := by
    intro x hx hxT
    exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hx
      ((P1.mem_triangleCrossings x).mpr hxT)
  refine ⟨fun A hAT hA => ?_, fun A' hAT' hA' => ?_⟩
  · rw [rowTerm_eq_exterior_mul_touching hn _ hA e f g,
      EXT_exteriorFactor_eq_base hn (genericAt E t ht.1) hQT
        (fun x hx => (P1.mem_triangleCrossings x).mp (hAT hx)) hA (mem_Ind_of_mem_outsideSupports hQ)]
  · have hQ'ind : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) :=
      PRE_mem_Ind_of_subset hA' Finset.subset_union_left
    have hQ'T : ∀ x ∈ transportSupport hs Q, x.val ∉ triangleSupports e f g := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      exact hQT y hy
    rw [rowTerm_eq_exterior_mul_touching hn _ hA' e f g,
      ← EXT_exteriorFactor_eq_base hn (genericAt E t' ht'.1) hQ'T
        (fun x hx => (P1.mem_triangleCrossings x).mp (hAT' hx)) hA' hQ'ind,
      EXT_exteriorFactor_wall hE hn hL hguard ht ht' hop hs (mem_Ind_of_mem_outsideSupports hQ) hQT hQ'ind]

end EXTAssembly

end EXT

/-- **Row 168, R:exterior** (R-EXTERIOR-1). -/
theorem exterior (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExteriorData hn E e f g δ := by
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hguard⟩ := EXT_exists_guardRadius hE
  refine ⟨min δL δG, lt_min hδL hδG, (min_le_left _ _).trans hδLr, ?_⟩
  have hL' : LocalizationData E e f g (min δL δG) := F1.localizationData_mono (min_le_left δL δG) hL
  have hguard' : ∀ u : E.Parameter, |u.val| < min δL δG → EXT_GuardAt E u :=
    fun u hu => hguard u (lt_of_lt_of_le hu (min_le_right _ _))
  exact { independent_of_A := EXT_168_independent_of_A hn E e f g _
          wall_invariant := EXT_168_wall_invariant hn E e f g hL' hguard' hE
          factorization := EXT_168_factorization hn E e f g hL' hguard' hE }

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

/-! ## Unit AV — the transport across the wall at availability ≤ 1 (proof lane, 2026-09-14)

The wall data `AV_Wall` (abstracted from the event), the corner-successor transport of carriers, the
literal carriage of corner lists, turns, `wt`, `wind`, retained crossings and pieces, the record
isomorphism of the positive lifts (`AV_homfly_lift_eq`), the rotation by CV:def:rot's ray formula
(`AV_rotationNumber_tcp`), and the event data at a common radius (`AV_EventRadius`). Nothing in the
fixed statements is changed. -/

section AV

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

/-- A crossing *dominated* by the support `S` through a dominator outside the local set `T`
(R-PAR-v6: "`x` interlaces a member of `S'`"; the dominator is an outside crossing, so the
interlacement is wall-invariant). -/
def AV_Dom (hP : CrossingGeometry P) (T S : Finset (Crossing P)) (x : Crossing P) : Prop :=
  ∃ s ∈ S, s ∉ T ∧ GeometricInterlaces hP x s

/-- **Wall data for a support `S` across a simple RIII wall**, abstracted from the event: two
polygons `P`, `P'` on the record domain with the same crossing supports, a local crossing set `T`
(the triangle), and a support `S` such that (i) same-edge visit orders are carried except for the
pairs of distinct `T`-crossings on a common edge (R-LOC-2 (2)–(3), `ExactTriangleVisitOrders`),
(ii) interlacement is carried off the pairs inside `T` (R-LOC-2 (4)), (iii) of any two distinct
`T`-crossings one is dominated by `S` through an outside crossing (availability `≤ 1`),
(iv) vertex turns and crossing signs agree (lem:guardconst), (v) a common reference vector `r`
sees every edge direction with the same nonzero sign on both sides. -/
structure AV_Wall (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (T S : Finset (Crossing P)) : Prop where
  indep : GeoIndependent hP S
  key_lt : ∀ v w : Visit P, ¬ (v.1 ∈ T ∧ w.1 ∈ T ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val) →
    (geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hP' (visitTransport hs v) < geometricVisitKey hP' (visitTransport hs w))
  interlaces_iff : ∀ x y : Crossing P, ¬ (x ∈ T ∧ y ∈ T) →
    (GeometricInterlaces hP x y ↔
      GeometricInterlaces hP' (crossingTransport hs x) (crossingTransport hs y))
  dominated : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → AV_Dom hP T S x ∨ AV_Dom hP T S y
  turn_eq : ∀ i, turn P' i = turn P i
  sign_eq : ∀ i j, IsCrossing P {i, j} → crossingSign P' i j = crossingSign P i j
  ray : ∃ r : Plane, ∀ h : ZMod n, det r (edge P h) ≠ 0 ∧
    SignType.sign (det r (edge P' h)) = SignType.sign (det r (edge P h))

namespace AV_Wall

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}

omit [NeZero n] in
/-- Wall data pass to any larger independent support (domination is monotone in `S`). -/
theorem mono (W : AV_Wall hP hP' hs T S) {S₂ : Finset (Crossing P)} (hS : S ⊆ S₂)
    (hind : GeoIndependent hP S₂) : AV_Wall hP hP' hs T S₂ where
  indep := hind
  key_lt := W.key_lt
  interlaces_iff := W.interlaces_iff
  dominated x hx y hy hxy := by
    rcases W.dominated x hx y hy hxy with ⟨s, hs₁, hs₂, h⟩ | ⟨s, hs₁, hs₂, h⟩
    · exact Or.inl ⟨s, hS hs₁, hs₂, h⟩
    · exact Or.inr ⟨s, hS hs₁, hs₂, h⟩
  turn_eq := W.turn_eq
  sign_eq := W.sign_eq
  ray := W.ray

omit [NeZero n] in
/-- A selected crossing is not dominated (independence). -/
theorem not_dom_of_mem (W : AV_Wall hP hP' hs T S) {x : Crossing P} (hx : x ∈ S) :
    ¬ AV_Dom hP T S x := by
  rintro ⟨s, hsS, -, hxs⟩
  have hne : x ≠ s := fun h => geometricInterlaces_irrefl hP x (h ▸ hxs)
  exact W.indep x hx s hsS hne hxs

omit [NeZero n] in
/-- Domination is carried across the wall (the dominator is outside `T`). -/
theorem dom_transport (W : AV_Wall hP hP' hs T S) {x : Crossing P} (h : AV_Dom hP T S x) :
    AV_Dom hP' (transportSupport hs T) (transportSupport hs S) (crossingTransport hs x) := by
  obtain ⟨s, hsS, hsT, hxs⟩ := h
  refine ⟨crossingTransport hs s, (mem_transportSupport_iff hs S s).mpr hsS,
    fun h => hsT ((mem_transportSupport_iff hs T s).mp h), ?_⟩
  exact (W.interlaces_iff x s (fun h => hsT h.2)).mp hxs

omit [NeZero n] in
/-- The transported support is independent. -/
theorem indep' (W : AV_Wall hP hP' hs T S) : GeoIndependent hP' (transportSupport hs S) := by
  intro x' hx' y' hy' hne
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [mem_transportSupport_iff] at hx' hy'
  have hxy : x ≠ y := fun h => hne (h ▸ rfl)
  have hnT : ¬ (x ∈ T ∧ y ∈ T) := by
    rintro ⟨hxT, hyT⟩
    rcases W.dominated x hxT y hyT hxy with h | h
    · exact W.not_dom_of_mem hx' h
    · exact W.not_dom_of_mem hy' h
  exact fun h => W.indep x hx' y hy' hxy ((W.interlaces_iff x y hnT).mpr h)

/-- Mark keys are carried for every pair of marks that is not a same-edge pair of distinct
`T`-visits (the accepted `geoMarkKey_lt_transport_of_visitKey`, word for word, with the exception
built in). -/
theorem mark_key_lt (W : AV_Wall hP hP' hs T S) (a b : Mark P)
    (hab : ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w →
      ¬ (v.1 ∈ T ∧ w.1 ∈ T ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val)) :
    geoMarkKey hP a < geoMarkKey hP b ↔
      geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs b) := by
  cases a with
  | inl i =>
    cases b with
    | inl k => exact Iff.rfl
    | inr v =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hP' (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (i.val < v.2.val.val ∨ i = v.2.val ∧ (0 : ℝ) < visitParameter v) ↔
        (i.val < v.2.val.val ∨ i = v.2.val ∧ (0 : ℝ) < visitParameter (visitTransport hs v))
      exact or_congr Iff.rfl (and_congr Iff.rfl ⟨fun _ => h2, fun _ => h1⟩)
  | inr v =>
    cases b with
    | inl i =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hP' (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter v < (0 : ℝ)) ↔
        (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter (visitTransport hs v) < (0 : ℝ))
      exact or_congr Iff.rfl (and_congr Iff.rfl
        ⟨fun h => (lt_asymm h1 h).elim, fun h => (lt_asymm h2 h).elim⟩)
    | inr w => exact W.key_lt v w (hab v w rfl rfl)

end AV_Wall

/-- A *good* mark: its position relative to every corner is carried across the wall — every mark
except the visits of dominated `T`-crossings (the swap partners of the selected `T`-visit). -/
def AV_Good (hP : CrossingGeometry P) (T S : Finset (Crossing P)) (m : Mark P) : Prop :=
  ∀ v : Visit P, m = Sum.inr v → v.1 ∈ T → ¬ AV_Dom hP T S v.1

omit [NeZero n] in
theorem AV_good_vertex (hP : CrossingGeometry P) (T S : Finset (Crossing P)) (i : ZMod n) :
    AV_Good hP T S (Sum.inl i) := fun _ h => nomatch h

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}

omit [NeZero n] in
theorem AV_good_of_corner (W : AV_Wall hP hP' hs T S) {m : Mark P} (hm : IsTrueCorner S m) :
    AV_Good hP T S m := by
  intro v hv _
  subst hv
  exact W.not_dom_of_mem hm

/-- A good mark and a corner: their key order is carried, in both directions. -/
theorem AV_good_key_lt (W : AV_Wall hP hP' hs T S) {m d : Mark P} (hm : AV_Good hP T S m)
    (hd : IsTrueCorner S d) :
    (geoMarkKey hP m < geoMarkKey hP d ↔
        geoMarkKey hP' (markTransport hs m) < geoMarkKey hP' (markTransport hs d)) ∧
    (geoMarkKey hP d < geoMarkKey hP m ↔
        geoMarkKey hP' (markTransport hs d) < geoMarkKey hP' (markTransport hs m)) := by
  have hno : ∀ v w : Visit P, m = Sum.inr v → d = Sum.inr w →
      ¬ (v.1 ∈ T ∧ w.1 ∈ T ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val) := by
    rintro v w rfl rfl ⟨hvT, hwT, hne, -⟩
    have hwS : w.1 ∈ S := hd
    rcases W.dominated v.1 hvT w.1 hwT hne with h | h
    · exact hm v rfl hvT h
    · exact W.not_dom_of_mem hwS h
  exact ⟨W.mark_key_lt m d hno,
    W.mark_key_lt d m fun w v hw hv h => hno v w hv hw ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩

/-- Corners are carried to corners. -/
theorem AV_corner_transport (S : Finset (Crossing P)) (m : Mark P) :
    IsTrueCorner (transportSupport hs S) (markTransport hs m) ↔ IsTrueCorner S m := by
  cases m with
  | inl i =>
    rw [markTransport_vertex]
    exact iff_of_true (isTrueCorner_vertex _ i) (isTrueCorner_vertex S i)
  | inr v =>
    rw [markTransport_visit, isTrueCorner_visit, isTrueCorner_visit, visitTransport_crossing,
      mem_transportSupport_iff]

/-! ### The next corner along the traversal circle -/

/-- Some `ρ`-iterate of every mark is a corner (`ρ` is one cycle through the vertex `0`). -/
theorem AV_exists_corner_pow (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    ∃ k : ℕ, IsTrueCorner S ((geoMarkSuccessor hP ^ k) m) := by
  obtain ⟨i, -, hi⟩ := (geoMarkSuccessor_sameCycle hP m (Sum.inl 0)).exists_pow_eq'
  exact ⟨i, by rw [hi]; exact isTrueCorner_vertex S 0⟩

open scoped Classical in
/-- The first corner at or after a mark along the traversal circle (`ρ`-iteration). -/
noncomputable def AV_nextCorner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    Mark P :=
  (geoMarkSuccessor hP ^ Nat.find (AV_exists_corner_pow hP S m)) m

open scoped Classical in
theorem AV_nextCorner_corner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    IsTrueCorner S (AV_nextCorner hP S m) :=
  Nat.find_spec (AV_exists_corner_pow hP S m)

open scoped Classical in
theorem AV_nextCorner_of_corner {m : Mark P} (hm : IsTrueCorner S m) :
    AV_nextCorner hP S m = m := by
  unfold AV_nextCorner
  have h0 : Nat.find (AV_exists_corner_pow hP S m) = 0 := by
    rw [Nat.find_eq_zero]
    show IsTrueCorner S ((geoMarkSuccessor hP ^ 0) m)
    rw [pow_zero, Equiv.Perm.one_apply]
    exact hm
  rw [h0, pow_zero, Equiv.Perm.one_apply]

open scoped Classical in
theorem AV_find_succ {m : Mark P} (hm : ¬ IsTrueCorner S m) :
    Nat.find (AV_exists_corner_pow hP S (geoMarkSuccessor hP m)) =
      Nat.find (AV_exists_corner_pow hP S m) - 1 := by
  have hk0 : Nat.find (AV_exists_corner_pow hP S m) ≠ 0 := by
    intro h
    apply hm
    have := Nat.find_spec (AV_exists_corner_pow hP S m)
    rw [h, pow_zero, Equiv.Perm.one_apply] at this
    exact this
  rw [Nat.find_eq_iff]
  refine ⟨?_, ?_⟩
  · rw [← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
    exact Nat.find_spec (AV_exists_corner_pow hP S m)
  · intro j hj
    rw [← Equiv.Perm.mul_apply, ← pow_succ]
    exact Nat.find_min (AV_exists_corner_pow hP S m) (by omega)

open scoped Classical in
theorem AV_nextCorner_succ {m : Mark P} (hm : ¬ IsTrueCorner S m) :
    AV_nextCorner hP S (geoMarkSuccessor hP m) = AV_nextCorner hP S m := by
  have hk0 : Nat.find (AV_exists_corner_pow hP S m) ≠ 0 := by
    intro h
    apply hm
    have := Nat.find_spec (AV_exists_corner_pow hP S m)
    rw [h, pow_zero, Equiv.Perm.one_apply] at this
    exact this
  unfold AV_nextCorner
  rw [AV_find_succ hm, ← Equiv.Perm.mul_apply, ← pow_succ,
    Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]

/-- At a non-corner (an unselected visit) the smoothing successor is the plain successor. -/
theorem AV_smoothing_of_not_corner (hP : CrossingGeometry P) (S : Finset (Crossing P))
    {m : Mark P} (hm : ¬ IsTrueCorner S m) :
    geoSmoothingSuccessor hP S m = geoMarkSuccessor hP m := by
  cases m with
  | inl i => exact absurd (isTrueCorner_vertex S i) hm
  | inr v => exact geoSmoothingSuccessor_visit_of_not_mem hP S v hm

theorem AV_owner_pow_of_not_corner (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (m : Mark P) : ∀ k : ℕ, (∀ j < k, ¬ IsTrueCorner S ((geoMarkSuccessor hP ^ j) m)) →
    geoOwner hP S ((geoMarkSuccessor hP ^ k) m) = geoOwner hP S m := by
  intro k
  induction k with
  | zero => intro _; rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih =>
    intro h
    rw [pow_succ', Equiv.Perm.mul_apply,
      ← AV_smoothing_of_not_corner hP S (h k (Nat.lt_succ_self k)), geoOwner_successor]
    exact ih fun j hj => h j (Nat.lt_succ_of_lt hj)

open scoped Classical in
/-- The next corner lies on the carrier of the mark (the carrier follows `ρ` through unselected
visits). -/
theorem AV_nextCorner_owner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    geoOwner hP S (AV_nextCorner hP S m) = geoOwner hP S m :=
  AV_owner_pow_of_not_corner hP S m _ fun _ hj => Nat.find_min (AV_exists_corner_pow hP S m) hj

/-- The corner successor of a mark: the first corner strictly after its outgoing slot — the next
corner of its carrier after it. -/
noncomputable def AV_cornerSucc (hP : CrossingGeometry P) (S : Finset (Crossing P)) (c : Mark P) :
    Mark P :=
  AV_nextCorner hP S (geoSmoothingSuccessor hP S c)

theorem AV_cornerSucc_corner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (c : Mark P) :
    IsTrueCorner S (AV_cornerSucc hP S c) :=
  AV_nextCorner_corner hP S _

theorem AV_cornerSucc_owner (hP : CrossingGeometry P) (S : Finset (Crossing P)) (c : Mark P) :
    geoOwner hP S (AV_cornerSucc hP S c) = geoOwner hP S c := by
  unfold AV_cornerSucc
  rw [AV_nextCorner_owner, geoOwner_successor]

/-! ### Keys along the sorted marked circle -/

omit [NeZero n] in
theorem AV_key_nonneg (hP : CrossingGeometry P) (m : Mark P) : 0 ≤ geoMarkKey hP m :=
  add_nonneg (Nat.cast_nonneg _) (geoMarkPosition hP m).2.property.1

omit [NeZero n] in
theorem AV_key_inl_zero (hP : CrossingGeometry P) : geoMarkKey hP (Sum.inl 0) = 0 := by
  show ((0 : ZMod n).val : ℝ) + (0 : ℝ) = 0
  rw [ZMod.val_zero]
  simp

theorem AV_geoMarkList_pairwise_lt (hP : CrossingGeometry P) :
    (geoMarkList hP).Pairwise (fun a b => geoMarkKey hP a < geoMarkKey hP b) :=
  pairwise_lt_of_pairwise_le_nodup (geoMarkList_sorted hP) (geoMarkList_nodup hP)
    (geoMarkKey_injective hP)

theorem AV_geoMarkList_key_lt_iff (hP : CrossingGeometry P) {i j : ℕ}
    (hi : i < (geoMarkList hP).length) (hj : j < (geoMarkList hP).length) :
    geoMarkKey hP (geoMarkList hP)[i] < geoMarkKey hP (geoMarkList hP)[j] ↔ i < j := by
  have hpw := AV_geoMarkList_pairwise_lt hP
  rw [List.pairwise_iff_getElem] at hpw
  constructor
  · intro hlt
    by_contra hge
    rcases Nat.lt_or_ge j i with hji | hij
    · exact absurd (hpw j i hj hi hji) (not_lt.mpr hlt.le)
    · have : i = j := by omega
      subst this
      exact lt_irrefl _ hlt
  · exact hpw i j hi hj

/-- `ρ` increases the key with no mark strictly in between, except at the last mark, where it wraps
to the vertex `0` (the least mark). -/
theorem AV_succ_spec (hP : CrossingGeometry P) (m : Mark P) :
    (geoMarkKey hP m < geoMarkKey hP (geoMarkSuccessor hP m) ∧
      ∀ d, ¬ (geoMarkKey hP m < geoMarkKey hP d ∧
        geoMarkKey hP d < geoMarkKey hP (geoMarkSuccessor hP m))) ∨
    (geoMarkSuccessor hP m = Sum.inl 0 ∧ ∀ d, geoMarkKey hP d ≤ geoMarkKey hP m) := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP m)
  rw [geoMarkSuccessor_getElem hP i hi]
  have hpos : 0 < (geoMarkList hP).length := lt_of_le_of_lt (Nat.zero_le i) hi
  by_cases h : i + 1 < (geoMarkList hP).length
  · left
    have hmod : (i + 1) % (geoMarkList hP).length = i + 1 := Nat.mod_eq_of_lt h
    refine ⟨?_, ?_⟩
    · rw [AV_geoMarkList_key_lt_iff hP hi (Nat.mod_lt _ hpos), hmod]
      omega
    · intro d ⟨h1, h2⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP d)
      rw [AV_geoMarkList_key_lt_iff hP hi hj] at h1
      rw [AV_geoMarkList_key_lt_iff hP hj (Nat.mod_lt _ hpos), hmod] at h2
      omega
  · right
    have hlen : i + 1 = (geoMarkList hP).length := by omega
    have hmod : (i + 1) % (geoMarkList hP).length = 0 := by rw [hlen, Nat.mod_self]
    have hidx : (geoMarkList hP)[(i + 1) % (geoMarkList hP).length]'(Nat.mod_lt _ hpos) =
        (geoMarkList hP)[0]'hpos :=
      geo_getElem_congr _ _ rfl _ _ _ hpos hmod
    rw [hidx]
    refine ⟨?_, ?_⟩
    · apply geoMarkKey_injective hP
      apply le_antisymm
      · obtain ⟨j0, hj0, hj0e⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP (Sum.inl 0))
        rw [← hj0e]
        rcases Nat.eq_zero_or_pos j0 with hz | hz
        · rw [geo_getElem_congr _ _ rfl 0 j0 hpos hj0 hz.symm]
        · exact le_of_lt ((AV_geoMarkList_key_lt_iff hP hpos hj0).mpr hz)
      · rw [AV_key_inl_zero]
        exact AV_key_nonneg hP _
    · intro d
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp (mem_geoMarkList hP d)
      rcases Nat.lt_or_ge j i with hji | hji
      · exact le_of_lt ((AV_geoMarkList_key_lt_iff hP hj hi).mpr hji)
      · have : j = i := by omega
        subst this
        exact le_refl _

/-! ### The order-theoretic specification of the next corner and of the corner successor -/

/-- `d` is the first corner at or after `m`: either the least corner with key `≥ key m`, or — when
no corner has key `≥ key m` — the vertex `0`. -/
def AV_NCSpec (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m d : Mark P) : Prop :=
  IsTrueCorner S d ∧
  ((geoMarkKey hP m ≤ geoMarkKey hP d ∧
      ∀ d', IsTrueCorner S d' → geoMarkKey hP m ≤ geoMarkKey hP d' →
        geoMarkKey hP d ≤ geoMarkKey hP d') ∨
    ((∀ d', IsTrueCorner S d' → geoMarkKey hP d' < geoMarkKey hP m) ∧ d = Sum.inl 0))

theorem AV_ncspec_unique {m d₁ d₂ : Mark P} (h1 : AV_NCSpec hP S m d₁) (h2 : AV_NCSpec hP S m d₂) :
    d₁ = d₂ := by
  obtain ⟨hc1, h1⟩ := h1
  obtain ⟨hc2, h2⟩ := h2
  rcases h1 with ⟨hle1, hmin1⟩ | ⟨hall1, rfl⟩ <;> rcases h2 with ⟨hle2, hmin2⟩ | ⟨hall2, rfl⟩
  · exact geoMarkKey_injective hP (le_antisymm (hmin1 d₂ hc2 hle2) (hmin2 d₁ hc1 hle1))
  · exact absurd (lt_of_le_of_lt hle1 (hall2 d₁ hc1)) (lt_irrefl _)
  · exact absurd (lt_of_le_of_lt hle2 (hall1 d₂ hc2)) (lt_irrefl _)
  · rfl

open scoped Classical in
theorem AV_nextCorner_spec_aux (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    ∀ k : ℕ, ∀ m : Mark P, Nat.find (AV_exists_corner_pow hP S m) = k →
      AV_NCSpec hP S m (AV_nextCorner hP S m) := by
  intro k
  induction k with
  | zero =>
    intro m hk
    have hm : IsTrueCorner S m := by
      have := Nat.find_spec (AV_exists_corner_pow hP S m)
      rw [hk, pow_zero, Equiv.Perm.one_apply] at this
      exact this
    rw [AV_nextCorner_of_corner hm]
    exact ⟨hm, Or.inl ⟨le_refl _, fun d' _ h => h⟩⟩
  | succ k ih =>
    intro m hk
    have hm : ¬ IsTrueCorner S m := by
      intro hm
      have h0 : Nat.find (AV_exists_corner_pow hP S m) = 0 := by
        rw [Nat.find_eq_zero]
        show IsTrueCorner S ((geoMarkSuccessor hP ^ 0) m)
        rw [pow_zero, Equiv.Perm.one_apply]
        exact hm
      omega
    have hk' : Nat.find (AV_exists_corner_pow hP S (geoMarkSuccessor hP m)) = k := by
      rw [AV_find_succ hm, hk]
      rfl
    have hspec := ih (geoMarkSuccessor hP m) hk'
    rw [AV_nextCorner_succ hm] at hspec
    obtain ⟨hcorner, hspec⟩ := hspec
    refine ⟨hcorner, ?_⟩
    have hne : ∀ d', IsTrueCorner S d' → geoMarkKey hP d' ≠ geoMarkKey hP m := by
      intro d' hd' h
      exact hm (geoMarkKey_injective hP h ▸ hd')
    rcases AV_succ_spec hP m with ⟨hlt, hbetween⟩ | ⟨hwrap, hall⟩
    · rcases hspec with ⟨hle, hmin⟩ | ⟨hall, hzero⟩
      · left
        refine ⟨le_of_lt (lt_of_lt_of_le hlt hle), ?_⟩
        intro d' hd' hmd'
        have hmd'' : geoMarkKey hP m < geoMarkKey hP d' := lt_of_le_of_ne hmd' (hne d' hd').symm
        have : ¬ geoMarkKey hP d' < geoMarkKey hP (geoMarkSuccessor hP m) :=
          fun h => hbetween d' ⟨hmd'', h⟩
        exact hmin d' hd' (not_lt.mp this)
      · right
        refine ⟨?_, hzero⟩
        intro d' hd'
        have h1 := hall d' hd'
        have : ¬ geoMarkKey hP m < geoMarkKey hP d' := fun h => hbetween d' ⟨h, h1⟩
        exact lt_of_le_of_ne (not_lt.mp this) (hne d' hd')
    · right
      refine ⟨?_, ?_⟩
      · intro d' hd'
        exact lt_of_le_of_ne (hall d') (hne d' hd')
      · rw [← AV_nextCorner_succ hm, hwrap]
        exact AV_nextCorner_of_corner (isTrueCorner_vertex S 0)

open scoped Classical in
theorem AV_nextCorner_spec (hP : CrossingGeometry P) (S : Finset (Crossing P)) (m : Mark P) :
    AV_NCSpec hP S m (AV_nextCorner hP S m) :=
  AV_nextCorner_spec_aux hP S _ m rfl

/-- `d` is the first corner strictly after `x`: the least corner with key `> key x`, or the vertex
`0` when no corner has key `> key x`. -/
def AV_CSSpec (hP : CrossingGeometry P) (S : Finset (Crossing P)) (x d : Mark P) : Prop :=
  IsTrueCorner S d ∧
  ((geoMarkKey hP x < geoMarkKey hP d ∧
      ∀ d', IsTrueCorner S d' → geoMarkKey hP x < geoMarkKey hP d' →
        geoMarkKey hP d ≤ geoMarkKey hP d') ∨
    ((∀ d', IsTrueCorner S d' → geoMarkKey hP d' ≤ geoMarkKey hP x) ∧ d = Sum.inl 0))

theorem AV_csspec_unique {x d₁ d₂ : Mark P} (h1 : AV_CSSpec hP S x d₁) (h2 : AV_CSSpec hP S x d₂) :
    d₁ = d₂ := by
  obtain ⟨hc1, h1⟩ := h1
  obtain ⟨hc2, h2⟩ := h2
  rcases h1 with ⟨hlt1, hmin1⟩ | ⟨hall1, rfl⟩ <;> rcases h2 with ⟨hlt2, hmin2⟩ | ⟨hall2, rfl⟩
  · exact geoMarkKey_injective hP (le_antisymm (hmin1 d₂ hc2 hlt2) (hmin2 d₁ hc1 hlt1))
  · exact absurd (lt_of_lt_of_le hlt1 (hall2 d₁ hc1)) (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le hlt2 (hall1 d₂ hc2)) (lt_irrefl _)
  · rfl

/-- The next corner after `ρ x` is the first corner strictly after `x`. -/
theorem AV_nextCorner_succ_spec (hP : CrossingGeometry P) (S : Finset (Crossing P)) (x : Mark P) :
    AV_CSSpec hP S x (AV_nextCorner hP S (geoMarkSuccessor hP x)) := by
  obtain ⟨hcorner, hspec⟩ := AV_nextCorner_spec hP S (geoMarkSuccessor hP x)
  refine ⟨hcorner, ?_⟩
  rcases AV_succ_spec hP x with ⟨hlt, hbetween⟩ | ⟨hwrap, hall⟩
  · rcases hspec with ⟨hle, hmin⟩ | ⟨hall, hzero⟩
    · left
      refine ⟨lt_of_lt_of_le hlt hle, ?_⟩
      intro d' hd' hxd'
      have : ¬ geoMarkKey hP d' < geoMarkKey hP (geoMarkSuccessor hP x) :=
        fun h => hbetween d' ⟨hxd', h⟩
      exact hmin d' hd' (not_lt.mp this)
    · right
      refine ⟨?_, hzero⟩
      intro d' hd'
      have h1 := hall d' hd'
      have : ¬ geoMarkKey hP x < geoMarkKey hP d' := fun h => hbetween d' ⟨h, h1⟩
      exact not_lt.mp this
  · right
    refine ⟨fun d' _ => hall d', ?_⟩
    rw [hwrap]
    exact AV_nextCorner_of_corner (isTrueCorner_vertex S 0)

/-! ### Transport of the specifications across the wall -/

theorem AV_ncspec_transport (W : AV_Wall hP hP' hs T S) {m d : Mark P} (hm : AV_Good hP T S m)
    (h : AV_NCSpec hP S m d) :
    AV_NCSpec hP' (transportSupport hs S) (markTransport hs m) (markTransport hs d) := by
  obtain ⟨hc, h⟩ := h
  refine ⟨(AV_corner_transport S d).mpr hc, ?_⟩
  rcases h with ⟨hle, hmin⟩ | ⟨hall, rfl⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [← not_lt] at hle ⊢
      exact fun h' => hle (((AV_good_key_lt W hm hc).2).mpr h')
    · intro d'' hd'' hle''
      obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
      have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
      have hle' : geoMarkKey hP m ≤ geoMarkKey hP d' := by
        rw [← not_lt] at hle'' ⊢
        exact fun h' => hle'' (((AV_good_key_lt W hm hd').2).mp h')
      have hdd' := hmin d' hd' hle'
      rw [← not_lt] at hdd' ⊢
      exact fun h' => hdd' (((AV_good_key_lt W (AV_good_of_corner W hc) hd').2).mpr h')
  · right
    refine ⟨?_, markTransport_vertex hs 0⟩
    intro d'' hd''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    exact ((AV_good_key_lt W hm hd').2).mp (hall d' hd')

open scoped Classical in
/-- **The next corner of a good mark is carried across the wall.** -/
theorem AV_nextCorner_transport (W : AV_Wall hP hP' hs T S) {m : Mark P} (hm : AV_Good hP T S m) :
    AV_nextCorner hP' (transportSupport hs S) (markTransport hs m) =
      markTransport hs (AV_nextCorner hP S m) :=
  AV_ncspec_unique (AV_nextCorner_spec hP' _ _) (AV_ncspec_transport W hm (AV_nextCorner_spec hP S m))

theorem AV_csspec_transport (W : AV_Wall hP hP' hs T S) {x d : Mark P} (hx : IsTrueCorner S x)
    (h : AV_CSSpec hP S x d) :
    AV_CSSpec hP' (transportSupport hs S) (markTransport hs x) (markTransport hs d) := by
  obtain ⟨hc, h⟩ := h
  have hxg : AV_Good hP T S x := AV_good_of_corner W hx
  refine ⟨(AV_corner_transport S d).mpr hc, ?_⟩
  rcases h with ⟨hlt, hmin⟩ | ⟨hall, rfl⟩
  · left
    refine ⟨((AV_good_key_lt W hxg hc).1).mp hlt, ?_⟩
    intro d'' hd'' hlt''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    have hlt' : geoMarkKey hP x < geoMarkKey hP d' := ((AV_good_key_lt W hxg hd').1).mpr hlt''
    have hdd' := hmin d' hd' hlt'
    rw [← not_lt] at hdd' ⊢
    exact fun h' => hdd' (((AV_good_key_lt W (AV_good_of_corner W hc) hd').2).mpr h')
  · right
    refine ⟨?_, markTransport_vertex hs 0⟩
    intro d'' hd''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    have h1 := hall d' hd'
    rw [← not_lt] at h1 ⊢
    exact fun h' => h1 (((AV_good_key_lt W hxg hd').1).mpr h')

/-- The outgoing slot of a corner is a corner (itself, or the twin of a selected visit). -/
theorem AV_corner_selectedMarkPerm (S : Finset (Crossing P)) {c : Mark P} (hc : IsTrueCorner S c) :
    IsTrueCorner S (selectedMarkPerm S c) := by
  cases c with
  | inl i => exact isTrueCorner_vertex S i
  | inr v =>
    rw [selectedMarkPerm_visit, isTrueCorner_visit, selectedVisitTwin_crossing]
    exact hc

/-- **The corner successor of a corner is carried across the wall.** -/
theorem AV_cornerSucc_transport (W : AV_Wall hP hP' hs T S) {c : Mark P} (hc : IsTrueCorner S c) :
    AV_cornerSucc hP' (transportSupport hs S) (markTransport hs c) =
      markTransport hs (AV_cornerSucc hP S c) := by
  have h1 : AV_CSSpec hP' (transportSupport hs S) (markTransport hs (selectedMarkPerm S c))
      (AV_cornerSucc hP' (transportSupport hs S) (markTransport hs c)) := by
    unfold AV_cornerSucc
    rw [geoSmoothingSuccessor_apply, selectedMarkPerm_markTransport]
    exact AV_nextCorner_succ_spec hP' _ _
  have h2 : AV_CSSpec hP' (transportSupport hs S) (markTransport hs (selectedMarkPerm S c))
      (markTransport hs (AV_cornerSucc hP S c)) :=
    AV_csspec_transport W (AV_corner_selectedMarkPerm S hc)
      (by unfold AV_cornerSucc; rw [geoSmoothingSuccessor_apply]; exact AV_nextCorner_succ_spec hP S _)
  exact AV_csspec_unique h1 h2

/-! ### The carrier bijection across the wall -/

theorem AV_carrierMap_aux (W : AV_Wall hP hP' hs T S) (m : Mark P) :
    geoOwner hP' (transportSupport hs S)
        (markTransport hs (AV_nextCorner hP S (geoSmoothingSuccessor hP S m))) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := by
  by_cases hm : IsTrueCorner S m
  · change geoOwner hP' (transportSupport hs S) (markTransport hs (AV_cornerSucc hP S m)) = _
    rw [← AV_cornerSucc_transport W hm, AV_cornerSucc_owner, AV_nextCorner_of_corner hm]
  · rw [AV_smoothing_of_not_corner hP S hm, AV_nextCorner_succ hm]

theorem AV_carrierMap_pow (W : AV_Wall hP hP' hs T S) (m : Mark P) (k : ℕ) :
    geoOwner hP' (transportSupport hs S)
        (markTransport hs (AV_nextCorner hP S ((geoSmoothingSuccessor hP S ^ k) m))) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, AV_carrierMap_aux W, ih]

/-- The carrier map across the wall: the carrier of `P'` through the transported next corner. -/
noncomputable def AV_carrierMap (W : AV_Wall hP hP' hs T S) :
    GeoComponent hP S → GeoComponent hP' (transportSupport hs S) :=
  Quotient.lift
    (fun m => geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)))
    (fun a b hab => by
      obtain ⟨i, -, rfl⟩ :=
        (show (geoSmoothingSuccessor hP S).SameCycle a b from hab).exists_pow_eq'
      exact (AV_carrierMap_pow W a i).symm)

theorem AV_carrierMap_owner (W : AV_Wall hP hP' hs T S) (m : Mark P) :
    AV_carrierMap W (geoOwner hP S m) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := rfl

theorem AV_carrierInv_aux (W : AV_Wall hP hP' hs T S) (m' : Mark P') :
    geoOwner hP S ((markTransport hs).symm
        (AV_nextCorner hP' (transportSupport hs S) (geoSmoothingSuccessor hP' (transportSupport hs S) m'))) =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
  by_cases hm : IsTrueCorner (transportSupport hs S) m'
  · change geoOwner hP S ((markTransport hs).symm (AV_cornerSucc hP' (transportSupport hs S) m')) = _
    have hc : IsTrueCorner S ((markTransport hs).symm m') := by
      rw [← AV_corner_transport (hs := hs) S ((markTransport hs).symm m'), Equiv.apply_symm_apply]
      exact hm
    have := AV_cornerSucc_transport W hc
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply, AV_cornerSucc_owner, AV_nextCorner_of_corner hm]
  · rw [AV_smoothing_of_not_corner hP' _ hm, AV_nextCorner_succ hm]

theorem AV_carrierInv_pow (W : AV_Wall hP hP' hs T S) (m' : Mark P') (k : ℕ) :
    geoOwner hP S ((markTransport hs).symm
        (AV_nextCorner hP' (transportSupport hs S) ((geoSmoothingSuccessor hP' (transportSupport hs S) ^ k) m'))) =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, AV_carrierInv_aux W, ih]

/-- The inverse carrier map. -/
noncomputable def AV_carrierInv (W : AV_Wall hP hP' hs T S) :
    GeoComponent hP' (transportSupport hs S) → GeoComponent hP S :=
  Quotient.lift
    (fun m' => geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')))
    (fun a b hab => by
      obtain ⟨i, -, rfl⟩ :=
        (show (geoSmoothingSuccessor hP' (transportSupport hs S)).SameCycle a b from hab).exists_pow_eq'
      exact (AV_carrierInv_pow W a i).symm)

theorem AV_carrierInv_owner (W : AV_Wall hP hP' hs T S) (m' : Mark P') :
    AV_carrierInv W (geoOwner hP' (transportSupport hs S) m') =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := rfl

/-- **The carriers of `S` correspond to the carriers of the transported support across the wall**:
the corner cycles are carried (corner by corner, the non-corner marks may change carrier). -/
noncomputable def AV_carrierEquiv (W : AV_Wall hP hP' hs T S) :
    GeoComponent hP S ≃ GeoComponent hP' (transportSupport hs S) where
  toFun := AV_carrierMap W
  invFun := AV_carrierInv W
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h m =>
      change AV_carrierInv W (AV_carrierMap W (geoOwner hP S m)) = geoOwner hP S m
      rw [AV_carrierMap_owner, AV_carrierInv_owner,
        AV_nextCorner_of_corner ((AV_corner_transport S _).mpr (AV_nextCorner_corner hP S m)),
        Equiv.symm_apply_apply, AV_nextCorner_owner]
  right_inv q' := by
    induction q' using Quotient.inductionOn with
    | h m' =>
      change AV_carrierMap W (AV_carrierInv W (geoOwner hP' (transportSupport hs S) m')) =
        geoOwner hP' (transportSupport hs S) m'
      rw [AV_carrierInv_owner, AV_carrierMap_owner]
      have hc : IsTrueCorner S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
        rw [← AV_corner_transport (hs := hs) S, Equiv.apply_symm_apply]
        exact AV_nextCorner_corner hP' _ m'
      rw [AV_nextCorner_of_corner hc, Equiv.apply_symm_apply, AV_nextCorner_owner]

theorem AV_carrierEquiv_owner (W : AV_Wall hP hP' hs T S) (m : Mark P) :
    AV_carrierEquiv W (geoOwner hP S m) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := rfl

/-- **Ownership of good marks is carried**: a good mark lies on the copy of its carrier. -/
theorem AV_owner_transport (W : AV_Wall hP hP' hs T S) {m : Mark P} (hm : AV_Good hP T S m) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) =
      AV_carrierEquiv W (geoOwner hP S m) := by
  rw [AV_carrierEquiv_owner, ← AV_nextCorner_transport W hm, AV_nextCorner_owner]

theorem AV_owner_transport_corner (W : AV_Wall hP hP' hs T S) {m : Mark P} (hm : IsTrueCorner S m) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) =
      AV_carrierEquiv W (geoOwner hP S m) :=
  AV_owner_transport W (AV_good_of_corner W hm)

/-! ### The corner list of a carrier is carried literally -/

theorem AV_cornerList_pairwise (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) :
    (geoComponentCornerList hP S q).Pairwise (fun a b => geoMarkKey hP a < geoMarkKey hP b) := by
  unfold geoComponentCornerList geoComponentMarkList
  exact ((AV_geoMarkList_pairwise_lt hP).filter _).filter _

/-- **The corners of a carrier transport, in inherited order, to the corners of its copy**: both
lists are sorted by the key, have no duplicates and the same members (corner ownership is carried). -/
theorem AV_cornerList_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    (geoComponentCornerList hP S q).map (markTransport hs) =
      geoComponentCornerList hP' (transportSupport hs S) (AV_carrierEquiv W q) := by
  apply List.Perm.eq_of_pairwise (le := fun a b => geoMarkKey hP' a < geoMarkKey hP' b)
  · intro a b _ _ h1 h2
    exact absurd h2 (lt_asymm h1)
  · rw [List.pairwise_map]
    refine (AV_cornerList_pairwise hP S q).imp_of_mem ?_
    intro a b ha hb hab
    exact ((AV_good_key_lt W
      (AV_good_of_corner W ((mem_geoComponentCornerList hP S q a).mp ha).2)
      ((mem_geoComponentCornerList hP S q b).mp hb).2).1).mp hab
  · exact AV_cornerList_pairwise hP' _ _
  · rw [List.perm_ext_iff_of_nodup
      ((geoComponentCornerList_nodup hP S q).map (markTransport hs).injective)
      (geoComponentCornerList_nodup hP' _ _)]
    intro a'
    obtain ⟨a, rfl⟩ := (markTransport hs).surjective a'
    rw [List.mem_map_of_injective (markTransport hs).injective, mem_geoComponentCornerList,
      mem_geoComponentCornerList, AV_corner_transport]
    constructor
    · rintro ⟨hq, hc⟩
      exact ⟨by rw [AV_owner_transport_corner W hc, hq], hc⟩
    · rintro ⟨hq, hc⟩
      refine ⟨?_, hc⟩
      rw [AV_owner_transport_corner W hc] at hq
      exact (AV_carrierEquiv W).injective hq

theorem AV_cornerCount_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCornerCount hP' (transportSupport hs S) (AV_carrierEquiv W q) = geoCornerCount hP S q := by
  unfold geoCornerCount
  rw [← AV_cornerList_eq W q, List.length_map]

theorem AV_cornerMark_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP' (transportSupport hs S) (AV_carrierEquiv W q)
        (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q).symm) k) =
      markTransport hs (geoCornerMark hP S q k) := by
  have hL := AV_cornerList_eq W q
  have hlen : k.val < (geoComponentCornerList hP' (transportSupport hs S) (AV_carrierEquiv W q)).length := by
    rw [← hL, List.length_map]; exact ZMod.val_lt k
  have h3 : k.val < ((geoComponentCornerList hP S q).map (markTransport hs)).length := by
    rw [List.length_map]; exact ZMod.val_lt k
  unfold geoCornerMark
  refine (geo_getElem_congr _ _ rfl _ _ _ hlen (geo_zmod_val_cast (AV_cornerCount_eq W q).symm k)).trans ?_
  refine (geo_getElem_congr _ _ hL.symm _ _ hlen h3 rfl).trans ?_
  exact List.getElem_map _

theorem AV_cornerMark_eq' (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (j : ZMod (geoCornerCount hP' (transportSupport hs S) (AV_carrierEquiv W q))) :
    geoCornerMark hP' (transportSupport hs S) (AV_carrierEquiv W q) j =
      markTransport hs (geoCornerMark hP S q (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q)) j)) := by
  have h := AV_cornerMark_eq W q (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q)) j)
  rwa [geo_zmod_cast_cast (AV_cornerCount_eq W q) j] at h

/-- The corner polygon of `q` read at the geometry of `P'` (the accepted
`GeoMarkTransport.transportedCornerPolygon`, on the wall bijection). -/
noncomputable def AV_tcp (_W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    LabelledTuple (geoCornerCount hP S q) :=
  fun k => traversalEvaluation P' (geoMarkPosition hP' (markTransport hs (geoCornerMark hP S q k)))

theorem AV_cornerPolygon_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCornerPolygon hP' (transportSupport hs S) (AV_carrierEquiv W q) =
      geoRecast (AV_cornerCount_eq W q) (AV_tcp W q) := by
  funext j
  show traversalEvaluation P' (geoMarkPosition hP' (geoCornerMark hP' (transportSupport hs S)
    (AV_carrierEquiv W q) j)) = _
  rw [AV_cornerMark_eq' W q j]
  rfl

theorem AV_tcp_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    AV_tcp W q =
      geoRecast (AV_cornerCount_eq W q).symm
        (geoCornerPolygon hP' (transportSupport hs S) (AV_carrierEquiv W q)) := by
  rw [AV_cornerPolygon_eq W q]
  funext k
  rw [geoRecast_apply, geoRecast_apply, geo_zmod_cast_cast' (AV_cornerCount_eq W q) k]

theorem AV_turn_tcp_eq_turn_cast (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (AV_tcp W q) k =
      turn (geoCornerPolygon hP' (transportSupport hs S) (AV_carrierEquiv W q))
        (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q).symm) k) := by
  rw [AV_cornerPolygon_eq W q, turn_geoRecast_cast]

/-- **Corner turns are carried across the wall**: vertex corners by `turn_eq`, smoothing corners by
`sign_eq` (the accepted `GeoMarkTransport.turn_transportedCornerPolygon`, on the wall bijection). -/
theorem AV_turn_tcp (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (AV_tcp W q) k = turn (geoCornerPolygon hP S q) k := by
  have hS := W.indep
  have hS' := W.indep'
  rw [AV_turn_tcp_eq_turn_cast W q k]
  have hmark := AV_cornerMark_eq W q k
  have hcorner := isTrueCorner_geoCornerMark hP S q k
  cases hc : geoCornerMark hP S q k with
  | inl i =>
    rw [hc, markTransport_vertex] at hmark
    rw [geoCornerPolygon_turn_vertex hn hP' hS' _ _ i hmark,
      geoCornerPolygon_turn_vertex hn hP hS q k i hc]
    exact W.turn_eq i
  | inr v =>
    rw [hc] at hcorner
    have hv : v.1 ∈ S := (isTrueCorner_visit S v).mp hcorner
    rw [hc, markTransport_visit] at hmark
    have hv' : (visitTransport hs v).1 ∈ transportSupport hs S := by
      rw [visitTransport_crossing, mem_transportSupport_iff]; exact hv
    rw [geoCornerPolygon_turn_visit hn hP' hS' _ _ (visitTransport hs v) hv' hmark,
      geoCornerPolygon_turn_visit hn hP hS q k v hv hc, ← visitTransport_visitTwin,
      visitTransport_edge, visitTransport_edge]
    apply W.sign_eq
    rw [← visit_crossing_val_eq_pair v]
    exact v.1.property

theorem AV_turn_cornerPolygon_eq (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (j : ZMod (geoCornerCount hP' (transportSupport hs S) (AV_carrierEquiv W q))) :
    turn (geoCornerPolygon hP' (transportSupport hs S) (AV_carrierEquiv W q)) j =
      turn (geoCornerPolygon hP S q) (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q)) j) := by
  have h := AV_turn_tcp_eq_turn_cast W q (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q)) j)
  rw [geo_zmod_cast_cast (AV_cornerCount_eq W q) j] at h
  rw [← h, AV_turn_tcp W hn q]

/-- Uniformity of a carrier is carried across the wall. -/
theorem AV_carrierUniform_iff (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S) :
    geoCarrierUniform hP' (transportSupport hs S) (AV_carrierEquiv W q) ↔ geoCarrierUniform hP S q := by
  unfold geoCarrierUniform
  rw [AV_cornerPolygon_eq W q]
  refine exists_congr fun σ => and_congr_right fun _ => ?_
  rw [forall_turn_geoRecast]
  simp only [AV_turn_tcp W hn q]

/-- The selector (`wt`) of a carrier is carried across the wall. -/
theorem AV_selector_eq (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S) :
    geoCarrierSelector hP' (transportSupport hs S) (AV_carrierEquiv W q) = geoCarrierSelector hP S q := by
  unfold geoCarrierSelector
  rw [AV_cornerPolygon_eq W q, cornerSelector_geoRecast]
  exact cornerSelector_congr_turn (AV_turn_tcp W hn q)

/-- `wind(S)` is carried across the wall. -/
theorem AV_geoWind_eq (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) :
    geoWind hP' (transportSupport hs S) = geoWind hP S := by
  unfold geoWind
  exact (Fintype.prod_equiv (AV_carrierEquiv W) _ _ fun q => (AV_selector_eq W hn q).symm).symm

/-! ### Retained crossings, `U`, pieces -/

/-- A retained crossing of a carrier is not dominated (def:smoothing: a neighbour of `S` is a
crossing of no carrier). -/
theorem AV_not_dom_of_retained (W : AV_Wall hP hP' hs T S) {q : GeoComponent hP S} {x : Crossing P}
    (hx : x ∈ geoCarrierCrossings hP S q) (hd : AV_Dom hP T S x) : False := by
  obtain ⟨s, hsS, -, hxs⟩ := hd
  exact geo_neighbor_not_mem_geoCarrierCrossings hP W.indep
    ((mem_geoSupportNeighbors hP S x).mpr ⟨s, hsS, hxs⟩) q hx

theorem AV_not_mem_U_of_dom {x : Crossing P} (hd : AV_Dom hP T S x) : x ∉ CV.U hP S := by
  intro hx
  obtain ⟨s, hsS, -, hxs⟩ := hd
  exact ((CV.mem_U_iff hP S x).mp hx).2 s hsS hxs

omit [NeZero n] in
/-- The visits of an undominated crossing are good marks. -/
theorem AV_good_of_not_dom {x : Crossing P} (hx : ¬ AV_Dom hP T S x) (v : Visit P) (hv : v.1 = x) :
    AV_Good hP T S (Sum.inr v) := by
  intro w hw _
  obtain rfl := Sum.inr.inj hw
  rw [hv]
  exact hx

theorem AV_good_of_mem_U {x : Crossing P} (hx : x ∈ CV.U hP S) (v : Visit P) (hv : v.1 = x) :
    AV_Good hP T S (Sum.inr v) :=
  AV_good_of_not_dom (fun hd => AV_not_mem_U_of_dom hd hx) v hv

/-- **The retained crossings of a carrier are carried to those of its copy** (a dominated crossing
is retained by no carrier on either side; the visits of an undominated crossing are good marks). -/
theorem AV_geoCarrierCrossings_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCarrierCrossings hP' (transportSupport hs S) (AV_carrierEquiv W q) =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding := by
  classical
  ext x'
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hdom : AV_Dom hP T S x
  · refine iff_of_false ?_ ?_
    · obtain ⟨s', hsS', -, hxs'⟩ := W.dom_transport hdom
      exact geo_neighbor_not_mem_geoCarrierCrossings hP' W.indep'
        ((mem_geoSupportNeighbors hP' _ _).mpr ⟨s', hsS', hxs'⟩) _
    · exact fun h => AV_not_dom_of_retained W h hdom
  · rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings, mem_transportSupport_iff]
    apply and_congr Iff.rfl
    constructor
    · intro hw v hv
      have := hw (visitTransport hs v) (by rw [visitTransport_crossing, hv])
      rw [← markTransport_visit, AV_owner_transport W (AV_good_of_not_dom hdom v hv)] at this
      exact (AV_carrierEquiv W).injective this
    · intro hv w hw
      obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
      rw [visitTransport_crossing] at hw
      have hvx : v.1 = x := (crossingTransport hs).injective hw
      rw [← markTransport_visit, AV_owner_transport W (AV_good_of_not_dom hdom v hvx), hv v hvx]

theorem AV_card_geoCarrierCrossings_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    (geoCarrierCrossings hP' (transportSupport hs S) (AV_carrierEquiv W q)).card =
      (geoCarrierCrossings hP S q).card := by
  rw [AV_geoCarrierCrossings_eq W q, Finset.card_map]

/-- `U(S)` is carried across the wall. -/
theorem AV_mem_U_iff (W : AV_Wall hP hP' hs T S) (y : Crossing P) :
    crossingTransport hs y ∈ CV.U hP' (transportSupport hs S) ↔ y ∈ CV.U hP S := by
  rw [CV.mem_U_iff, CV.mem_U_iff, mem_transportSupport_iff]
  by_cases hyS : y ∈ S
  · exact iff_of_false (fun h => h.1 hyS) (fun h => h.1 hyS)
  by_cases hdom : AV_Dom hP T S y
  · refine iff_of_false ?_ ?_
    · obtain ⟨s', hs', -, h⟩ := W.dom_transport hdom
      exact fun h' => h'.2 s' hs' h
    · obtain ⟨s, hsS, -, h⟩ := hdom
      exact fun h' => h'.2 s hsS h
  · apply and_congr Iff.rfl
    have hnT : ∀ x ∈ S, ¬ (y ∈ T ∧ x ∈ T) := by
      intro x hxS ⟨hyT, hxT⟩
      have hne : y ≠ x := fun e => hyS (e ▸ hxS)
      rcases W.dominated y hyT x hxT hne with hd | hd
      · exact hdom hd
      · exact W.not_dom_of_mem hxS hd
    constructor
    · intro h x hxS h'
      exact h (crossingTransport hs x) ((mem_transportSupport_iff hs S x).mpr hxS)
        ((W.interlaces_iff y x (hnT x hxS)).mp h')
    · intro h x' hx' h'
      obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
      rw [mem_transportSupport_iff] at hx'
      exact h x hx' ((W.interlaces_iff y x (hnT x hx')).mpr h')

/-- **The residual graphs are isomorphic across the wall** (`U(S)` is carried and interlacement on
`U(S)` is carried: two undominated distinct `T`-crossings cannot both lie in `U(S)`). -/
noncomputable def AV_residualIso (W : AV_Wall hP hP' hs T S) :
    CV.residualGraph hP S ≃g CV.residualGraph hP' (transportSupport hs S) where
  toEquiv := Equiv.subtypeEquiv (crossingTransport hs) (fun y => (AV_mem_U_iff W y).symm)
  map_rel_iff' := by
    intro a b
    show GeometricInterlaces hP' (crossingTransport hs a.1) (crossingTransport hs b.1) ↔
      GeometricInterlaces hP a.1 b.1
    by_cases hab : a.1 = b.1
    · rw [hab]
      exact iff_of_false (geometricInterlaces_irrefl hP' _) (geometricInterlaces_irrefl hP _)
    · have hnT : ¬ (a.1 ∈ T ∧ b.1 ∈ T) := by
        rintro ⟨haT, hbT⟩
        rcases W.dominated a.1 haT b.1 hbT hab with hd | hd
        · exact AV_not_mem_U_of_dom hd a.2
        · exact AV_not_mem_U_of_dom hd b.2
      exact (W.interlaces_iff a.1 b.1 hnT).symm

theorem AV_residualIso_apply_val (W : AV_Wall hP hP' hs T S) (a : ↑(CV.U hP S)) :
    ((AV_residualIso W) a).1 = crossingTransport hs a.1 := rfl

/-- **The pieces of `S` correspond to the pieces of the transported support** across the wall. -/
noncomputable def AV_pieceEquiv (W : AV_Wall hP hP' hs T S) :
    CV.Piece hP S ≃ CV.Piece hP' (transportSupport hs S) :=
  (AV_residualIso W).connectedComponentEquiv

theorem AV_pieceEquiv_pieceOf (W : AV_Wall hP hP' hs T S) (c : Crossing P) (hc : c ∈ CV.U hP S) :
    AV_pieceEquiv W (CV.pieceOf hP S c hc) =
      CV.pieceOf hP' (transportSupport hs S) (crossingTransport hs c) ((AV_mem_U_iff W c).mpr hc) := by
  unfold AV_pieceEquiv CV.pieceOf
  rw [SimpleGraph.Iso.connectedComponentEquiv_apply, SimpleGraph.ConnectedComponent.map_mk]
  rfl

/-- The labels of a piece are carried. -/
theorem AV_pieceLabels_eq (W : AV_Wall hP hP' hs T S) (H : CV.Piece hP S) :
    CV.pieceLabels hP' (transportSupport hs S) (AV_pieceEquiv W H) =
      (CV.pieceLabels hP S H).map (crossingTransport hs).toEmbedding := by
  ext c'
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, CV.mem_pieceLabels, CV.mem_pieceLabels]
  constructor
  · rintro ⟨hc', hH⟩
    have hc : c ∈ CV.U hP S := (AV_mem_U_iff W c).mp hc'
    refine ⟨hc, (AV_pieceEquiv W).injective ?_⟩
    rw [AV_pieceEquiv_pieceOf]
    exact hH
  · rintro ⟨hc, hH⟩
    refine ⟨(AV_mem_U_iff W c).mpr hc, ?_⟩
    rw [← AV_pieceEquiv_pieceOf W c hc, hH]

theorem AV_pieceWrithe_eq (W : AV_Wall hP hP' hs T S) (H : CV.Piece hP S) :
    CV.pieceWrithe hP' (transportSupport hs S) (AV_pieceEquiv W H) = CV.pieceWrithe hP S H := by
  unfold CV.pieceWrithe
  rw [AV_pieceLabels_eq, Finset.card_map]

/-- The pieces assigned to a carrier are carried onto the pieces assigned to its copy (the visits of
the labels are good marks). -/
theorem AV_mem_piecesOn_transport_iff (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (H : CV.Piece hP S) :
    AV_pieceEquiv W H ∈ CV.piecesOn hP' (transportSupport hs S) (AV_carrierEquiv W q) ↔
      H ∈ CV.piecesOn hP S q := by
  rw [CV.mem_piecesOn, CV.mem_piecesOn, AV_pieceLabels_eq]
  constructor
  · intro hall c hc v hv
    have := hall (crossingTransport hs c) (Finset.mem_map_of_mem _ hc)
      (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit,
      AV_owner_transport W (AV_good_of_mem_U (CV.pieceLabels_subset hP S H hc) v hv)] at this
    exact (AV_carrierEquiv W).injective this
  · intro hall c' hc' w hw
    obtain ⟨c, hc, rfl⟩ := Finset.mem_map.mp hc'
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
    rw [visitTransport_crossing] at hw
    have hv : v.1 = c := (crossingTransport hs).injective hw
    rw [← markTransport_visit,
      AV_owner_transport W (AV_good_of_mem_U (CV.pieceLabels_subset hP S H hc) v hv), hall c hc v hv]

theorem AV_piecesOn_transport_eq (W : AV_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    CV.piecesOn hP' (transportSupport hs S) (AV_carrierEquiv W q) =
      (CV.piecesOn hP S q).map (AV_pieceEquiv W).toEmbedding := by
  ext H'
  obtain ⟨H, rfl⟩ := (AV_pieceEquiv W).surjective H'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, AV_mem_piecesOn_transport_iff]

/-! ### The HOMFLY polynomial of the positive lift is carried across the wall -/

section AVLift

variable (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (W : AV_Wall hG.cg hG'.cg hs T S) (hS : GeoIndependent hG.cg S)
  (hS' : GeoIndependent hG'.cg (transportSupport hs S)) (q : GeoComponent hG.cg S)

/-- The occurrences of the two lifts correspond through the parent visits and the canonical visit
identification ("the identity map on the visits", d6:67, across the wall). -/
noncomputable def AV_liftEquiv :
    (geoPositiveLift hn hG hS q).Γ.Visit ≃
      (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).Γ.Visit :=
  (CV.liftVisitEquiv hn hG hS q).trans
    ((Equiv.subtypeEquiv (visitTransport hs) (fun w => by
        rw [AV_geoCarrierCrossings_eq W q, visitTransport_crossing, Finset.mem_map_equiv,
          Equiv.symm_apply_apply])).trans
      (CV.liftVisitEquiv hn hG' hS' (AV_carrierEquiv W q)).symm)

theorem AV_liftVisit_liftEquiv (v : (geoPositiveLift hn hG hS q).Γ.Visit) :
    CV.liftVisit hn hG' hS' (AV_carrierEquiv W q) (AV_liftEquiv hn hG hG' W hS hS' q v) =
      visitTransport hs (CV.liftVisit hn hG hS q v) := by
  show CV.liftVisit hn hG' hS' _ ((CV.liftVisitEquiv hn hG' hS' _).symm _) = _
  rw [CV.liftVisit_symm]
  rfl

/-- **The HOMFLY polynomial of the positive lift of a carrier is carried across the wall**: the
occurrence bijection is a record isomorphism — (a) cyclic order by the carried visit keys (no two
retained crossings form a reversed same-edge pair), (b) double points by the twin pairing, (c) over/under
by the carried crossing signs, (d) all signs `+1` — and CV:ax:gausscode (`gausscode_polynomial`). -/
theorem AV_homfly_lift_eq :
    homfly (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)) = homfly (geoPositiveLift hn hG hS q) := by
  have hΦ := AV_liftVisit_liftEquiv hn hG hG' W hS hS' q
  have hkey : ∀ v w : (geoPositiveLift hn hG hS q).Γ.Visit,
      geometricVisitKey hG.cg (CV.liftVisit hn hG hS q v) <
          geometricVisitKey hG.cg (CV.liftVisit hn hG hS q w) ↔
        geometricVisitKey hG'.cg (visitTransport hs (CV.liftVisit hn hG hS q v)) <
          geometricVisitKey hG'.cg (visitTransport hs (CV.liftVisit hn hG hS q w)) := by
    intro v w
    apply W.key_lt
    rintro ⟨hvT, hwT, hne, -⟩
    rcases W.dominated _ hvT _ hwT hne with hd | hd
    · exact AV_not_dom_of_retained W (CV.liftVisit_mem hn hG hS q v) hd
    · exact AV_not_dom_of_retained W (CV.liftVisit_mem hn hG hS q w) hd
  have hdata : CV.IsRecordIsoData (geoPositiveLift hn hG hS q)
      (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)) (AV_liftEquiv hn hG hG' W hS hS' q) :=
    { cyclic_order := fun v w u hb => by
        rw [CV.visitBetween_iff_key, hΦ, hΦ, hΦ]
        rw [CV.visitBetween_iff_key] at hb
        unfold cycBetween at hb ⊢
        rw [← hkey, ← hkey, ← hkey]
        exact hb
      double_points :=
        (CV.carriesDoublePoints_iff (ρ := (geoPositiveLift hn hG hS q).record)
          (ρ' := (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).record)
          (AV_liftEquiv hn hG hG' W hS hS' q)).2 fun v => by
          apply CV.liftVisit_injective hn hG' hS' (AV_carrierEquiv W q)
          change CV.liftVisit hn hG' hS' _
              (AV_liftEquiv hn hG hG' W hS hS' q ((geoPositiveLift hn hG hS q).twin v)) =
            CV.liftVisit hn hG' hS' _
              ((geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).twin
                (AV_liftEquiv hn hG hG' W hS hS' q v))
          rw [hΦ, CV.liftVisit_twin hn hG hS q, CV.liftVisit_twin hn hG' hS', hΦ, visitTransport_visitTwin]
      over_under :=
        (CV.carriesOverUnder_iff (ρ := (geoPositiveLift hn hG hS q).record)
          (ρ' := (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).record)
          (AV_liftEquiv hn hG hG' W hS hS' q)).2 fun v => by
          change (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).overBit
              (AV_liftEquiv hn hG hG' W hS hS' q v) = (geoPositiveLift hn hG hS q).overBit v
          rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΦ,
            ← visitTransport_visitTwin, visitTransport_edge, visitTransport_edge]
          have hcross : IsCrossing P {(CV.liftVisit hn hG hS q v).2.val,
              (visitTwin (CV.liftVisit hn hG hS q v)).2.val} := by
            rw [← visit_crossing_val_eq_pair]
            exact (CV.liftVisit hn hG hS q v).1.property
          have hsign := W.sign_eq _ _ hcross
          unfold crossingSign at hsign
          constructor
          · intro h
            exact sign_eq_one_iff.mp (by rw [← hsign]; exact sign_pos h)
          · intro h
            exact sign_eq_one_iff.mp (by rw [hsign]; exact sign_pos h)
      signs := fun v => by
        change (geoPositiveLift hn hG' hS' (AV_carrierEquiv W q)).sign
            (AV_liftEquiv hn hG hG' W hS hS' q v).1 = (geoPositiveLift hn hG hS q).sign v.1
        rw [geoPositiveLift_sign, geoPositiveLift_sign] }
  exact (CV.gausscode_polynomial _ _ (geoPositiveLift_componentCount hn hG hS q)
    (geoPositiveLift_componentCount hn hG' hS' _)
    (CV.recordIsoOfData (geoPositiveLift_componentCount hn hG hS q)
      (geoPositiveLift_componentCount hn hG' hS' _) _ hdata)).symm

end AVLift

/-! ### The rotation of a carrier is carried across the wall (CV:def:rot's ray formula) -/

theorem AV_edge_geoRecast {k k' : ℕ} [NeZero k] [NeZero k'] (hk : k' = k) (f : LabelledTuple k)
    (j : ZMod k') : edge (geoRecast hk f) j = edge f (Equiv.cast (congrArg ZMod hk) j) := by
  subst hk
  rfl

/-- The edge label of the outgoing slot of a mark is carried (vertices by label, visits by edge). -/
theorem AV_outSlot_transport (S : Finset (Crossing P)) (a : Mark P) :
    (geoOutSlot hP' (transportSupport hs S) (markTransport hs a)).1 = (geoOutSlot hP S a).1 := by
  unfold geoOutSlot
  rw [selectedMarkPerm_markTransport]
  generalize selectedMarkPerm S a = b
  cases b <;> rfl

theorem AV_edge_tcp (W : AV_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      edge (AV_tcp W q) k = c • edge P' (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  rw [AV_tcp_eq W q, AV_edge_geoRecast]
  obtain ⟨c, hc, h⟩ := geoCornerPolygon_edge_smul hn hP' W.indep' (AV_carrierEquiv W q)
    (Equiv.cast (congrArg ZMod (AV_cornerCount_eq W q).symm) k)
  refine ⟨c, hc, ?_⟩
  rw [h, AV_cornerMark_eq' W q, geo_zmod_cast_cast' (AV_cornerCount_eq W q) k, AV_outSlot_transport]

theorem AV_sign_det_smul_left (c : ℝ) (hc : 0 < c) (u r : Plane) :
    SignType.sign (det (c • u) r) = SignType.sign (det u r) := by
  rw [CV.det_smul_left', sign_mul, sign_pos hc, one_mul]

theorem AV_sign_det_smul_right (c : ℝ) (hc : 0 < c) (r u : Plane) :
    SignType.sign (det r (c • u)) = SignType.sign (det r u) := by
  rw [det_smul_right, sign_mul, sign_pos hc, one_mul]

theorem AV_sign_det_swap (u r : Plane) : SignType.sign (det u r) = -SignType.sign (det r u) := by
  rw [det_swap r u, Left.sign_neg]

/-- **The rotation number of the corner polygon is carried across the wall**: `2π rot = Σ τ_i`
(lem:turnlift (ii)) and `rot = Σ_i ε_i(r)` with `ε_i` a function of three determinant signs
(CV:def:rot, `epsRot_eq_epsOfSigns`), each of which is carried — the corner turns by `AV_turn_tcp`,
the ray signs because both corner polygons run along the same original edges and `r` sees those
edges with the same sign on both sides. -/
theorem AV_rotationNumber_tcp (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (W : AV_Wall hG.cg hG'.cg hs T S) (q : GeoComponent hG.cg S) :
    rotationNumber (AV_tcp W q) = rotationNumber (geoCornerPolygon hG.cg S q) := by
  obtain ⟨r, hr⟩ := W.ray
  have hL : CV.Regular (geoCornerPolygon hG.cg S q) :=
    (CV.regular_iff_sm _).mpr (geoCornerPolygon_regular hn hG W.indep q)
  have hL'' : CV.Regular (AV_tcp W q) := by
    rw [CV.regular_iff_sm, AV_tcp_eq W q, regular_geoRecast]
    exact geoCornerPolygon_regular hn hG' W.indep' _
  have hr' : ∀ h : ZMod n, det r (edge P' h) ≠ 0 := by
    intro h h0
    have := (hr h).2
    rw [h0, sign_zero] at this
    exact (hr h).1 (sign_eq_zero_iff.mp this.symm)
  have hadm : CV.Admissible (geoCornerPolygon hG.cg S q) r := by
    intro k
    obtain ⟨c, hc, h⟩ := geoCornerPolygon_edge_smul hn hG.cg W.indep q k
    rw [h, det_smul_right]
    exact mul_ne_zero hc.ne' (hr _).1
  have hadm'' : CV.Admissible (AV_tcp W q) r := by
    intro k
    obtain ⟨c, hc, h⟩ := AV_edge_tcp W hn q k
    rw [h, det_smul_right]
    exact mul_ne_zero hc.ne' (hr' _)
  rw [← CV.rotRay_eq_rotationNumber hL hadm, ← CV.rotRay_eq_rotationNumber hL'' hadm'']
  congr 1
  unfold CV.rotRay
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [CV.epsRot_eq_epsOfSigns, CV.epsRot_eq_epsOfSigns]
  have hturn : SignType.sign (det (edge (AV_tcp W q) (k - 1)) (edge (AV_tcp W q) k)) =
      SignType.sign (det (edge (geoCornerPolygon hG.cg S q) (k - 1))
        (edge (geoCornerPolygon hG.cg S q) k)) := by
    rw [← turn_det, ← turn_det]
    exact AV_turn_tcp W hn q k
  have hray : ∀ j : ZMod (geoCornerCount hG.cg S q),
      SignType.sign (det r (edge (AV_tcp W q) j)) =
        SignType.sign (det r (edge (geoCornerPolygon hG.cg S q) j)) := by
    intro j
    obtain ⟨c, hc, h⟩ := AV_edge_tcp W hn q j
    obtain ⟨c', hc', h'⟩ := geoCornerPolygon_edge_smul hn hG.cg W.indep q j
    rw [h, h', AV_sign_det_smul_right c hc, AV_sign_det_smul_right c' hc']
    exact (hr _).2
  have hray' : ∀ j : ZMod (geoCornerCount hG.cg S q),
      SignType.sign (det (edge (AV_tcp W q) j) r) =
        SignType.sign (det (edge (geoCornerPolygon hG.cg S q) j) r) := by
    intro j
    rw [AV_sign_det_swap (edge (AV_tcp W q) j) r,
      AV_sign_det_swap (edge (geoCornerPolygon hG.cg S q) j) r, hray j]
  rw [hturn, hray' (k - 1), hray k]

/-! ### The per-carrier objects of def:X1 across the wall (`CV.Generic` binders) -/

omit [NeZero n] in
theorem AV_transportSupport_union {P P' : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
    (A B : Finset (Crossing P)) :
    transportSupport hs (A ∪ B) = transportSupport hs A ∪ transportSupport hs B := by
  ext x'
  simp only [transportSupport, Finset.mem_map, Finset.mem_union]
  constructor
  · rintro ⟨x, hx | hx, rfl⟩
    · exact Or.inl ⟨x, hx, rfl⟩
    · exact Or.inr ⟨x, hx, rfl⟩
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨x, Or.inl hx, rfl⟩
    · exact ⟨x, Or.inr hx, rfl⟩

/-- `Finset.subset_union_left` with the `DecidableEq` instance as an explicit argument (the CV
library's unions carry the classical instance, `RProof.Cores` the decidable one; passing the instance
avoids re-synthesis). -/
theorem AV_subset_union_left' {α : Type*} (inst : DecidableEq α) (s t : Finset α) :
    s ⊆ @Union.union _ (@Finset.instUnion _ inst) s t :=
  @Finset.subset_union_left _ inst s t

section AVGeneric

/-- `w_{S,L}` is carried across the wall (it is the number of retained crossings). -/
theorem AV_groupedWrithe_eq (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.groupedWrithe hG' (AV_carrierEquiv W q) = CV.groupedWrithe hG q := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG' hS',
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG hS, AV_card_geoCarrierCrossings_eq W q]

/-- **The piece polynomials are carried across the wall**: at `P'` the carrier of `S' ∪ K'` (the
support chosen at `P'`) and the wall copy of the carrier of `S ∪ K_H` (the support chosen at `P`)
retain exactly the labels of the piece, so their lifts have the same polynomial (CV:lem:pieceintrinsic,
`homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq`), and the wall copy's lift has the polynomial of
the lift at `P` (`AV_homfly_lift_eq`, the wall data passed to `S ∪ K_H`). -/
theorem AV_pieceHomfly_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (H : CV.Piece hG.crossingGeometry S) :
    CV.pieceHomfly hn (hG'.diagrammatic hn) hS' (AV_pieceEquiv W H) =
      CV.pieceHomfly hn (hG.diagrammatic hn) hS H := by
  have hSK := CV.pieceSupport_mem_Ind (hG.diagrammatic hn) hS H
  have W₂ := W.mono (AV_subset_union_left' _ S _) (CV.geoIndependent_of_mem_Ind _ hSK)
  have hK2 := W₂.indep'
  have hcross : geoCarrierCrossings hG'.crossingGeometry _
      (CV.pieceCarrier (hG'.diagrammatic hn) hS' (AV_pieceEquiv W H)) =
      geoCarrierCrossings hG'.crossingGeometry _
        (AV_carrierEquiv W₂ (CV.pieceCarrier (hG.diagrammatic hn) hS H)) := by
    rw [CV.pieceCarrier_geoCarrierCrossings, AV_pieceLabels_eq W H, AV_geoCarrierCrossings_eq W₂,
      CV.pieceCarrier_geoCarrierCrossings]
  unfold CV.pieceHomfly CV.pieceDiagram
  rw [CV.homfly_geoPositiveLift_eq_of_geoCarrierCrossings_eq hn
    (CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn))
    (CV.pieceSupport_geoIndependent (hG'.diagrammatic hn) hS' (AV_pieceEquiv W H)) hK2
    (CV.pieceCarrier (hG'.diagrammatic hn) hS' (AV_pieceEquiv W H)) _ hcross]
  exact AV_homfly_lift_eq hn (CarrierGeometry.ofDiagrammatic (hG.diagrammatic hn))
    (CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn)) W₂
    (CV.pieceSupport_geoIndependent (hG.diagrammatic hn) hS H) hK2
    (CV.pieceCarrier (hG.diagrammatic hn) hS H)

/-- `P_{S,L}` is carried across the wall. -/
theorem AV_groupedPoly_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.groupedPoly hn hG' hS' (AV_carrierEquiv W q) = CV.groupedPoly hn hG hS q := by
  unfold CV.groupedPoly
  rw [AV_piecesOn_transport_eq W q, Finset.prod_map]
  exact Finset.prod_congr rfl fun H _ => AV_pieceHomfly_eq hn hG hG' W hS hS' H

/-- `R(L) = |rot(L)|` is carried across the wall. -/
theorem AV_carrierR_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.carrierR hn hG' hS' (AV_carrierEquiv W q) = CV.carrierR hn hG hS q := by
  unfold CV.carrierR CV.rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [CV.rot_eq_rotationNumber, CV.rot_eq_rotationNumber, AV_cornerPolygon_eq W q,
    rotationNumber_geoRecast]
  exact AV_rotationNumber_tcp hn (CarrierGeometry.ofCV hG) (CarrierGeometry.ofCV hG') W q

/-- The slot `1 − w_{S,L} − R(L)` is carried across the wall. -/
theorem AV_slot_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.slot hn hG' hS' (AV_carrierEquiv W q) = CV.slot hn hG hS q := by
  unfold CV.slot
  rw [AV_groupedWrithe_eq hG hG' W hS hS' q, AV_carrierR_eq hn hG hG' W hS hS' q]

/-- The factor `Ω₁(S,L)` is carried across the wall. -/
theorem AV_Omega1_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.Omega1 hn hG' hS' (AV_carrierEquiv W q) = CV.Omega1 hn hG hS q := by
  unfold CV.Omega1
  rw [AV_slot_eq hn hG hG' W hS hS' q, AV_groupedPoly_eq hn hG hG' W hS hS' q]

/-- `wt` (CV:def:wind) is carried across the wall. -/
theorem AV_weight_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S) (q : GeoComponent hG.crossingGeometry S) :
    CV.weight hG'.crossingGeometry (transportSupport hs S) (AV_carrierEquiv W q) =
      CV.weight hG.crossingGeometry S q :=
  AV_selector_eq W hn q

/-- `wind(S)` (CV:def:wind) is carried across the wall. -/
theorem AV_wind_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S) :
    CV.wind hG'.crossingGeometry (transportSupport hs S) = CV.wind hG.crossingGeometry S :=
  AV_geoWind_eq W hn

end AVGeneric

/-! ### The event data: turn signs, crossing signs and a common reference vector near the wall -/

/-- The sign data of the event on a punctured radius `δ`: vertex turns and crossing signs agree at
any two punctured parameters (lem:guardconst on the unconditional `G1` members and on the active `G5`
members, none of which lies in the zero set of a simple RIII event), and one reference vector `r` sees
every edge direction with its central sign. -/
structure AV_EventRadius (E : CV.Event n) (δ : ℝ) : Prop where
  turn_eq : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' →
    ∀ i, turn (E.curve t') i = turn (E.curve t) i
  sign_eq : ∀ t t' : E.Parameter, Punctured E δ t → Punctured E δ t' →
    ∀ i j, IsCrossing (E.curve t) {i, j} → crossingSign (E.curve t') i j = crossingSign (E.curve t) i j
  ray : ∃ r : Plane, ∀ t : E.Parameter, Punctured E δ t → ∀ h : ZMod n,
    det r (edge (E.curve t) h) ≠ 0 ∧
      SignType.sign (det r (edge (E.curve t) h)) = SignType.sign (det r (edge E.center h))

theorem AV_eventRadius_mono {E : CV.Event n} {δ δ' : ℝ} (h : δ' ≤ δ) (hR : AV_EventRadius E δ) :
    AV_EventRadius E δ' where
  turn_eq t t' ht ht' := hR.turn_eq t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  sign_eq t t' ht ht' := hR.sign_eq t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  ray := by
    obtain ⟨r, hr⟩ := hR.ray
    exact ⟨r, fun t ht => hr t (F1.punctured_mono h ht)⟩

theorem AV_g1_not_mem_zeroSet {E : CV.Event n} {e f g : ZMod n} {h3 h4e h4f h4g}
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) (i : ZMod n) : CV.Member.g1 i ∉ E.zeroSet := by
  rw [hE.1]; simp

omit [NeZero n] in
theorem AV_turn_eq_sign_G1 (P : LabelledTuple n) (i : ZMod n) :
    turn P i = SignType.sign (CV.G1 P i) :=
  turn_det P i

/-- The continuity of a determinant with a fixed vector along the event. -/
theorem AV_continuous_det (E : CV.Event n) (r : Plane) (h : ZMod n) :
    Continuous fun t : E.Parameter => det r (edge (E.curve t) h) := by
  have h1 : Continuous fun t : E.Parameter => E.curve t (h + 1) :=
    (continuous_apply (h + 1)).comp E.continuous_curve
  have h0 : Continuous fun t : E.Parameter => E.curve t h :=
    (continuous_apply h).comp E.continuous_curve
  simp only [det, edge, Prod.fst_sub, Prod.snd_sub]
  exact (continuous_const.mul (h1.snd.sub h0.snd)).sub (continuous_const.mul (h1.fst.sub h0.fst))

/-- **The sign data exist on some punctured radius** for every simple RIII event. -/
theorem AV_exists_eventRadius {E : CV.Event n} {e f g : ZMod n} {h3 h4e h4f h4g}
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AV_EventRadius E δ := by
  obtain ⟨t0, ht0⟩ := G1.exists_punctured_parameter E
  -- (1) turns: the `G1` members are unconditional and outside `Z`
  have hturn : ∀ᶠ t in nhds E.zeroParameter, ∀ i : ZMod n,
      SignType.sign (CV.G1 (E.curve t) i) = SignType.sign (CV.G1 E.center i) := by
    rw [Filter.eventually_all]
    intro i
    exact (G1.eventually_sign_eq_of_not_mem (CV.Member.g1 i) ⟨t0, ht0, Or.inl trivial⟩
      (AV_g1_not_mem_zeroSet hE i)).mono fun t ht => ht.2
  obtain ⟨δ₁, hδ₁, hδ₁r, h1⟩ := (E.eventually_center_iff_radius _).mp hturn
  -- (2) crossing signs: the `G5` members active at some punctured parameter are outside `Z`
  have hsign : ∀ᶠ t in nhds E.zeroParameter, ∀ ab : ZMod n × ZMod n,
      (∃ t₁ : E.Parameter, t₁.val ≠ 0 ∧ IsCrossing (E.curve t₁) {ab.1, ab.2}) →
        SignType.sign (CV.G5 (E.curve t) ab.1 ab.2) = SignType.sign (CV.G5 E.center ab.1 ab.2) := by
    rw [Filter.eventually_all]
    rintro ⟨a, b⟩
    by_cases hex : ∃ t₁ : E.Parameter, t₁.val ≠ 0 ∧ IsCrossing (E.curve t₁) {a, b}
    · obtain ⟨t₁, ht₁, hab⟩ := hex
      have hr : remote a b := crossing_pair_remote hab
      have hcr : CV.Crosses (E.curve t₁) a b := ((genericAt E t₁ ht₁).crosses_iff a b).mpr hab
      rcases CV.rep_lt_or_lt (remote_endpoints a b hr).1.symm with hlt | hlt
      · exact (G1.eventually_sign_eq_of_not_mem (CV.Member.g5 a b ⟨hr, hlt⟩)
          ⟨t₁, ht₁, Or.inr hcr⟩ (G1.g5_not_mem_zeroSet hE a b ⟨hr, hlt⟩)).mono fun t ht _ => ht.2
      · have hab' : IsCrossing (E.curve t₁) {b, a} := by rwa [Finset.pair_comm]
        have hcr' : CV.Crosses (E.curve t₁) b a := ((genericAt E t₁ ht₁).crosses_iff b a).mpr hab'
        refine (G1.eventually_sign_eq_of_not_mem (CV.Member.g5 b a ⟨remote_symm hr, hlt⟩)
          ⟨t₁, ht₁, Or.inr hcr'⟩ (G1.g5_not_mem_zeroSet hE b a ⟨remote_symm hr, hlt⟩)).mono
          fun t ht _ => ?_
        have h5 : ∀ Q : LabelledTuple n, CV.G5 Q a b = -CV.G5 Q b a := fun Q => by
          unfold CV.G5; exact det_swap _ _
        rw [h5, h5, Left.sign_neg, Left.sign_neg]
        exact congrArg _ ht.2
    · exact Filter.Eventually.of_forall fun t h => absurd h hex
  obtain ⟨δ₂, hδ₂, -, h2⟩ := (E.eventually_center_iff_radius _).mp hsign
  -- (3) a reference vector admissible for the centre keeps its signs near the centre
  obtain ⟨r, hr⟩ := CV.exists_admissible (L := E.center) E.center_polygon
  have hray : ∀ᶠ t in nhds E.zeroParameter, ∀ h : ZMod n,
      det r (edge (E.curve t) h) ≠ 0 ∧
        SignType.sign (det r (edge (E.curve t) h)) = SignType.sign (det r (edge E.center h)) := by
    rw [Filter.eventually_all]
    intro h
    have hc : ContinuousAt (fun t : E.Parameter => det r (edge (E.curve t) h)) E.zeroParameter :=
      (AV_continuous_det E r h).continuousAt
    rcases lt_or_gt_of_ne (hr h) with hneg | hpos
    · have hev : ∀ᶠ t in nhds E.zeroParameter, det r (edge (E.curve t) h) < 0 :=
        hc.eventually_lt continuousAt_const hneg
      exact hev.mono fun t ht => ⟨ht.ne, by rw [sign_neg ht, sign_neg hneg]⟩
    · have hev : ∀ᶠ t in nhds E.zeroParameter, 0 < det r (edge (E.curve t) h) :=
        continuousAt_const.eventually_lt hc hpos
      exact hev.mono fun t ht => ⟨ht.ne', by rw [sign_pos ht, sign_pos hpos]⟩
  obtain ⟨δ₃, hδ₃, -, h3'⟩ := (E.eventually_center_iff_radius _).mp hray
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), (min_le_left _ _).trans hδ₁r, ?_⟩
  have hm1 : ∀ t : E.Parameter, Punctured E (min δ₁ (min δ₂ δ₃)) t → |t.val| < δ₁ :=
    fun t ht => lt_of_lt_of_le ht.2 (min_le_left _ _)
  have hm2 : ∀ t : E.Parameter, Punctured E (min δ₁ (min δ₂ δ₃)) t → |t.val| < δ₂ :=
    fun t ht => lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_left _ _))
  have hm3 : ∀ t : E.Parameter, Punctured E (min δ₁ (min δ₂ δ₃)) t → |t.val| < δ₃ :=
    fun t ht => lt_of_lt_of_le ht.2 ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨?_, ?_, ⟨r, fun t ht h => h3' t (hm3 t ht) h⟩⟩
  · intro t t' ht ht' i
    rw [AV_turn_eq_sign_G1, AV_turn_eq_sign_G1, h1 t (hm1 t ht) i, h1 t' (hm1 t' ht') i]
  · intro t t' ht ht' i j hij
    have hw : ∃ t₁ : E.Parameter, t₁.val ≠ 0 ∧ IsCrossing (E.curve t₁) {i, j} := ⟨t, ht.1, hij⟩
    show SignType.sign (CV.G5 (E.curve t') i j) = SignType.sign (CV.G5 (E.curve t) i j)
    rw [h2 t (hm2 t ht) (i, j) hw, h2 t' (hm2 t' ht') (i, j) hw]

/-! ### The wall data of an availability-`≤ 1` fibre -/

omit [NeZero n] in
theorem AV_card_triple {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ({e, f, g} : Finset (ZMod n)).card = 3 :=
  Finset.card_eq_three.mpr ⟨e, f, g, hef, heg, hfg, rfl⟩

omit [NeZero n] in
/-- A two-element subset of `{e, f, g}` is one of the three triangle supports. -/
theorem AV_pair_mem_triangleSupports {e f g a b : ZMod n}
    (ha : a ∈ ({e, f, g} : Finset (ZMod n))) (hb : b ∈ ({e, f, g} : Finset (ZMod n))) (hab : a ≠ b) :
    ({a, b} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  unfold triangleSupports
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hab
    | simp [Finset.pair_comm]

omit [NeZero n] in
/-- Two same-edge visits whose supports cover the triangle are visits of two distinct triangle
crossings (the reversed pairs of R-LOC-2 (2)). -/
theorem AV_triangle_of_union {e f g : ZMod n} (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (v w : Visit P) (hu : v.1.val ∪ w.1.val = {e, f, g}) :
    v.1.val ∈ triangleSupports e f g ∧ w.1.val ∈ triangleSupports e f g ∧ v.1 ≠ w.1 := by
  have h3 := AV_card_triple hef heg hfg
  have hpair : ∀ u : Visit P, u.1.val ⊆ ({e, f, g} : Finset (ZMod n)) →
      u.1.val ∈ triangleSupports e f g := by
    intro u hsub
    have hne : u.2.val ≠ (visitTwin u).2.val := by
      intro heq
      have hc := crossing_card_two u.1
      rw [visit_crossing_val_eq_pair u, ← heq, Finset.insert_eq_of_mem (Finset.mem_singleton_self _),
        Finset.card_singleton] at hc
      exact absurd hc (by norm_num)
    rw [visit_crossing_val_eq_pair u] at hsub ⊢
    exact AV_pair_mem_triangleSupports (hsub (Finset.mem_insert_self _ _))
      (hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) hne
  refine ⟨hpair v (hu ▸ Finset.subset_union_left), hpair w (hu ▸ Finset.subset_union_right), ?_⟩
  intro hvw
  have hc := congrArg Finset.card hu
  rw [hvw, Finset.union_self, crossing_card_two, h3] at hc
  exact absurd hc (by norm_num)

/-- The visit-key clause of the wall data from R-LOC-2's `ExactTriangleVisitOrders`. -/
theorem AV_key_lt_of_gauss (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) {e f g : ZMod n}
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) (hX : ExactTriangleVisitOrders P P' e f g hs)
    (v w : Visit P)
    (hvw : ¬ (v.1 ∈ triangleCrossings P e f g ∧ w.1 ∈ triangleCrossings P e f g ∧ v.1 ≠ w.1 ∧
      v.2.val = w.2.val)) :
    geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hP' (visitTransport hs v) < geometricVisitKey hP' (visitTransport hs w) := by
  unfold geometricVisitKey
  rw [traversalKey_lt_iff, traversalKey_lt_iff]
  change (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧ visitParameter v < visitParameter w) ↔
    (v.2.val.val < w.2.val.val ∨ v.2.val = w.2.val ∧
      visitParameter (visitTransport hs v) < visitParameter (visitTransport hs w))
  refine or_congr Iff.rfl (and_congr_right fun he => ?_)
  refine (hX v w he).2 fun hu => hvw ?_
  obtain ⟨hv, hw, hne⟩ := AV_triangle_of_union hef heg hfg v w hu
  exact ⟨(F1.mem_triangleCrossings e f g v.1).mpr hv, (F1.mem_triangleCrossings e f g w.1).mpr hw,
    hne, he⟩

theorem AV_fibrePartitionData_mono {E : CV.Event n} {e f g : ZMod n} {δ δ' : ℝ} (h : δ' ≤ δ)
    (hF : FibrePartitionData E e f g δ) : FibrePartitionData E e f g δ' where
  graph_on_W_same t t' ht ht' :=
    hF.graph_on_W_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  W_to_T_same t t' ht ht' := hF.W_to_T_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  avail_same t t' ht ht' := hF.avail_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  decompose t ht := hF.decompose t (F1.punctured_mono h ht)
  compose t ht := hF.compose t (F1.punctured_mono h ht)
  bijection t ht := hF.bijection t (F1.punctured_mono h ht)
  state_sum_partition t ht := hF.state_sum_partition t (F1.punctured_mono h ht)
  avail_card t ht := hF.avail_card t (F1.punctured_mono h ht)

/-- **The wall data of a fibre of availability `≤ 1`**: `Q ∪ J` independent (`F1.compose_geom`);
visit orders from R-LOC-2 (2)–(3) (`gauss_words`); interlacement off `T × T` from R-LOC-2 (4)
(`interlace_toggle`); of two distinct triangle crossings at most one is available, so the other
interlaces a member of `Q` (`mem_avail`), which is outside `T`; turns, signs and the ray from the
event radius. -/
theorem AV_wall_of_event {E : CV.Event n} {e f g : ZMod n} {δ : ℝ} (hL : LocalizationData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hcard : (avail (geomAt E t ht.1) e f g Q).card ≤ 1)
    {J : Finset (Crossing (E.curve t))} (hJ : J ∈ localFibre (geomAt E t ht.1) e f g Q) :
    AV_Wall (geomAt E t ht.1) (geomAt E t' ht'.1) hs (triangleCrossings (E.curve t) e f g) (Q ∪ J) where
  indep := by
    have hJ' := (F1.mem_localFibre _ e f g Q J).mp hJ
    exact (CV.mem_Ind_iff_geoIndependent _ _).mp (F1.compose_geom _ e f g Q J hQ hJ'.1 hJ'.2)
  key_lt := AV_key_lt_of_gauss _ _ hs hef heg hfg (hL.gauss_words t t' ht ht' hop hs)
  interlaces_iff x y hxy := by
    have h := hL.interlace_toggle t t' ht ht' hop hs x y
    rw [L.xor_iff_of_not_right (by
      rintro ⟨-, hx, hy⟩
      exact hxy ⟨(F1.mem_triangleCrossings e f g x).mpr hx,
        (F1.mem_triangleCrossings e f g y).mpr hy⟩)] at h
    exact h.symm
  dominated x hx y hy hxy := by
    have hQT : Disjoint Q (triangleCrossings (E.curve t) e f g) :=
      ((F1.mem_outsideSupports _ e f g Q).mp hQ).2
    have hdom : ∀ z ∈ triangleCrossings (E.curve t) e f g, z ∉ avail (geomAt E t ht.1) e f g Q →
        AV_Dom (geomAt E t ht.1) (triangleCrossings (E.curve t) e f g) (Q ∪ J) z := by
      intro z hz hza
      rw [F1.mem_avail] at hza
      have hzT := (F1.mem_triangleCrossings e f g z).mp hz
      obtain ⟨q, hq, hqz⟩ : ∃ q ∈ Q, GeometricInterlaces (geomAt E t ht.1) q z := by
        by_contra hcon
        exact hza ⟨hzT, fun q hq hqz => hcon ⟨q, hq, hqz⟩⟩
      exact ⟨q, Finset.mem_union_left J hq, Finset.disjoint_left.mp hQT hq,
        geometricInterlaces_symm _ hqz⟩
    by_cases hxa : x ∈ avail (geomAt E t ht.1) e f g Q
    · right
      apply hdom y hy
      intro hya
      exact hxy (Finset.card_le_one.mp hcard x hxa y hya)
    · exact Or.inl (hdom x hx hxa)
  turn_eq := hR.turn_eq t t' ht ht'
  sign_eq := hR.sign_eq t t' ht ht'
  ray := by
    obtain ⟨r, hr⟩ := hR.ray
    refine ⟨r, fun h => ⟨(hr t ht h).1, ?_⟩⟩
    rw [(hr t' ht' h).2, (hr t ht h).2]

end AV

/-! ### Unit AV — the X₁ fields of row 170 (`summand_transport`, `summands_agree`,
`fibre_identity`), each with exactly the field's type -/

/-- A `SummandTransport` gives the equality of the two present rows: `wind` agrees and the product of
the `Ω₁` is reindexed along the carrier bijection. -/
theorem AV_rowTerm_eq_of_summandTransport (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P)
    (hG' : CV.Generic P') {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (h : SummandTransport hn hG hG' hS hS') : rowTerm hn hG S = rowTerm hn hG' S' := by
  rw [rowTerm_of_mem_Ind hn hG hS, rowTerm_of_mem_Ind hn hG' hS']
  obtain ⟨hwind, τ, hτ⟩ := h
  rw [hwind]
  congr 1
  exact Fintype.prod_equiv τ _ _ fun q => ((hτ q).2.2.2.2).symm

/-- **The summand transport from wall data**: the carrier bijection `AV_carrierEquiv` with `wt`,
`R(L)`, `w_{S,L}`, `P_{S,L}` and `Ω₁(S,L)` carried. -/
theorem AV_summandTransport (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}
    (W : AV_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry) :
    SummandTransport hn hG hG' hS hS' :=
  ⟨AV_wind_eq hn hG hG' W, AV_carrierEquiv W, fun q =>
    ⟨AV_weight_eq hn hG hG' W q, AV_carrierR_eq hn hG hG' W hS hS' q, AV_groupedWrithe_eq hG hG' W hS hS' q,
      AV_groupedPoly_eq hn hG hG' W hS hS' q, AV_Omega1_eq hn hG hG' W hS hS' q⟩⟩

/-- Field `summand_transport` of `AvailabilityZeroOneData`. -/
theorem AV_170_summand_transport (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
      ∀ (hS : Q ∪ J ∈ CV.Ind (geomAt E t ht.1))
        (hS' : transportSupport hs (Q ∪ J) ∈ CV.Ind (geomAt E t' ht'.1)),
        SummandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' := by
  intro t t' ht ht' hop hs Q hQ hcard J hJ hS hS'
  exact AV_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1)
    (AV_wall_of_event hL hR hef heg hfg ht ht' hop hs hQ (by omega) hJ) hS hS'

/-- Field `summands_agree` of `AvailabilityZeroOneData`: the row is present on both sides
(`F1.compose_geom`; independence is carried by the wall data) and the summand transport gives the
equality. -/
theorem AV_170_summands_agree (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
        rowTerm hn (genericAt E t ht.1) (Q ∪ J) =
          rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ J)) := by
  intro t t' ht ht' hop hs Q hQ hcard J hJ
  have W := AV_wall_of_event hL hR hef heg hfg ht ht' hop hs hQ (by omega) hJ
  have hS : Q ∪ J ∈ CV.Ind (geomAt E t ht.1) := (CV.mem_Ind_iff_geoIndependent _ _).mpr W.indep
  have hS' : transportSupport hs (Q ∪ J) ∈ CV.Ind (geomAt E t' ht'.1) :=
    (CV.mem_Ind_iff_geoIndependent _ _).mpr W.indep'
  exact AV_rowTerm_eq_of_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS'
    (AV_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS')

/-- Field `fibre_identity` of `AvailabilityZeroOneData`: the far fibre is the image of the near
fibre (`PRE_170_fibre_correspond`), and the summands agree term by term. -/
theorem AV_170_fibre_identity (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hF : FibrePartitionData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  intro t t' ht ht' hop hs Q hQ hcard
  have hfib := PRE_170_fibre_correspond hF t t' ht ht' hop hs Q hQ hcard
  unfold fibreTerm fibreSum
  rw [hfib, Finset.sum_map]
  refine Finset.sum_congr rfl fun J hJ => ?_
  rw [supportEmb_apply, ← AV_transportSupport_union]
  exact AV_170_summands_agree hn hL hR hef heg hfg t t' ht ht' hop hs Q hQ hcard J hJ

omit [NeZero n] in
theorem AV_ne_of_remote {i j : ZMod n} (h : remote i j) : i ≠ j := by
  intro hij
  exact h (Or.inr (Or.inl (by rw [hij, sub_self])))

/-- **Row 170, R:availability_0_1**. -/
theorem availability_zero_one (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AvailabilityZeroOneData hn E e f g δ := by
  -- Unit AV: the common radius of rows 164 (`localization`), 171 (`fibre_partition`) and the sign
  -- data `AV_exists_eventRadius`; the three presupposition fields from unit PRE, the three X₁ fields
  -- from the wall transport.
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δF, hδF, -, hF⟩ := fibre_partition E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δF δR), lt_min hδL (lt_min hδF hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δF δR)) hL
  have hF' := AV_fibrePartitionData_mono ((min_le_right δL (min δF δR)).trans (min_le_left δF δR)) hF
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δF δR)).trans (min_le_right δF δR)) hR
  exact {
    fibre_zero := PRE_170_fibre_zero E e f g _
    fibre_one := PRE_170_fibre_one E e f g _
    fibre_correspond := PRE_170_fibre_correspond hF'
    summand_transport := AV_170_summand_transport hn hL' hR' hef heg hfg
    summands_agree := AV_170_summands_agree hn hL' hR' hef heg hfg
    fibre_identity := AV_170_fibre_identity hn hL' hF' hR' hef heg hfg }

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

/-! ## Unit SEL — proof lane of `generic_selector` (2026-09-14)

All five fields of `GenericSelectorData` from the accepted rows R:localization (`adjacent`, R-LOC-2
(2)) and R:generic_table (`nonzero`, `generic_iff_nonalternating`, `selected_unique`), CV:def:wind
(`weight_of_mixed`, `turn_visit_of_traced`) and def:flat-carriers (`geoSmoothingSuccessor`). The
ownership convention of `MixedSharedStrandCarrier` was re-checked on the skeleton before the proof:
`#eval (List.finRange 9).map (LocalTable.succ wordE {a, b}) = [8, 5, 3, 4, 2, 6, 7, 1, 0]` (cycles
`{0, 8}`, `{1, 5, 6, 7}`, `{2, 3, 4}`; `a(e) = 1` and `b(g) = 7` co-owned — the second disjunct —
while the two `e`-visits `b(e) = 0`, `a(e) = 1` lie on different carriers), likewise
`succ wordE {b, c} = [8, 2, 3, 7, 5, 6, 4, 1, 0]` (`c(f) = 3`, `b(g) = 7` co-owned, second disjunct)
and `succ wordP {a, c} = [4, 2, 3, 1, 8, 6, 7, 5, 0]` (`a(e) = 0`, `c(f) = 4` co-owned, first
disjunct). The geometric proof below reproduces exactly this: the `u`-visit that comes first along
`u` determines the disjunct. -/

section SEL

open SM.Carrier


/-- Finite sign facts. -/
theorem SEL_eq_zero_of_eq_neg : ∀ s : SignType, s = -s → s = 0 := by decide

theorem SEL_neg_ne_zero : ∀ s : SignType, s ≠ 0 → -s ≠ 0 := by decide

theorem SEL_eq_of_not_eq_neg : ∀ sa sb : SignType, sa ≠ 0 → sb ≠ 0 → ¬ sa = -sb → sa = sb := by
  decide

theorem SEL_eq_neg_of_not_eq : ∀ sa sc : SignType, sa ≠ 0 → sc ≠ 0 → ¬ sa = sc → sa = -sc := by
  decide

/-- An empty oriented gap between distinct members of a finite linear order identifies the
sorted-list successor, including the last/first cut (a verbatim port of the accepted
`SM.sorted_next_of_no_cyclic_between`, SM/GaussNextFromEmptyArc.lean, which is not in the import
closure of this file). -/
theorem SEL_sorted_next_of_no_cyclic_between {α : Type*} [LinearOrder α]
    (s : Finset α) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hgap : ∀ x ∈ s,
      ¬ ((a < x ∧ x < b) ∨ (x < b ∧ b < a) ∨ (b < a ∧ a < x))) :
    s.sort.next a ((Finset.mem_sort _).mpr ha) = b := by
  let e := s.orderIsoOfFin rfl
  let ia := e.symm ⟨a, ha⟩
  let ib := e.symm ⟨b, hb⟩
  have hcoe {i j : Fin s.card} (h : i < j) : (e i).val < (e j).val :=
    Subtype.coe_lt_coe.mpr (e.strictMono h)
  have hsize : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hne : ia.val ≠ ib.val := by
    intro he
    apply hab
    have hv := congrArg (fun k : Fin s.card => (e k).val) (Fin.ext he : ia = ib)
    simpa only [ia, ib, e.apply_symm_apply] using hv
  have haN := ia.isLt
  have hbN := ib.isLt
  have hindex : ib.val = (ia.val + 1) % s.card := by
    by_cases hcut : ia.val + 1 < s.card
    · let j : Fin s.card := ⟨ia.val + 1, hcut⟩
      have haj : a < (e j).val := by
        have h : ia < j := by change ia.val < ia.val + 1; omega
        simpa only [ia, e.apply_symm_apply] using hcoe h
      have hnone := hgap (e j).val (e j).property
      have hnotBack : ¬ ib.val < ia.val := by
        intro h
        have hba : b < a := by
          simpa only [ia, ib, e.apply_symm_apply] using
            hcoe (show ib < ia from h)
        exact hnone (Or.inr (Or.inr ⟨hba, haj⟩))
      have hnotGap : ¬ j.val < ib.val := by
        intro h
        have hjb : (e j).val < b := by
          simpa only [ib, e.apply_symm_apply] using
            hcoe (show j < ib from h)
        exact hnone (Or.inl ⟨haj, hjb⟩)
      have hj : j.val = ia.val + 1 := rfl
      rw [Nat.mod_eq_of_lt hcut]
      omega
    · have hlast : ia.val + 1 = s.card := by omega
      let j : Fin s.card := ⟨0, hsize⟩
      have hnone := hgap (e j).val (e j).property
      have hnotPos : ¬ 0 < ib.val := by
        intro h
        have hjb : (e j).val < b := by
          simpa only [ib, e.apply_symm_apply] using
            hcoe (show j < ib from h)
        have hba : b < a := by
          have hi : ib < ia := by change ib.val < ia.val; omega
          simpa only [ia, ib, e.apply_symm_apply] using hcoe hi
        exact hnone (Or.inr (Or.inl ⟨hjb, hba⟩))
      rw [hlast, Nat.mod_self]
      omega
  let nextIndex : Fin s.card := ⟨(ia.val + 1) % s.card, Nat.mod_lt _ hsize⟩
  have hvalue : s.sort.next a ((Finset.mem_sort _).mpr ha) = (e nextIndex).val := by
    rw [List.next_eq_getElem]
    simp only [e, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply, Finset.length_sort]
    rfl
  have hi : nextIndex = ib := Fin.ext hindex.symm
  rw [hvalue, hi]
  simp only [ib, e.apply_symm_apply]

section MarkOrder

variable {P : LabelledTuple n}

/-- Two distinct crossing visits on the same edge with no crossing visit in the oriented arc from
the first to the second are consecutive marks of the marked traversal circle: the `ρ`-successor of
the first is the second (no original vertex lies strictly inside an edge, and the arc cannot wrap
around the cut because the twin of the first visit lies on another edge). -/
theorem SEL_geoMarkSuccessor_eq_of_no_visit_between (hP : CrossingGeometry P)
    {v w : Visit P} (hvw : v ≠ w) (hedge : v.2.val = w.2.val)
    (hgap : ∀ u : Visit P, ¬ traversalBetween (geometricVisitPosition hP v)
      (geometricVisitPosition hP u) (geometricVisitPosition hP w)) :
    geoMarkSuccessor hP (Sum.inr v) = Sum.inr w := by
  classical
  have hkey_ne : traversalKey (geometricVisitPosition hP v) ≠
      traversalKey (geometricVisitPosition hP w) :=
    fun h => hvw (geometricVisitPosition_injective hP (traversalKey_injective h))
  have hv0 : 0 < visitParameter v :=
    (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
  have hw0 : 0 < visitParameter w :=
    (crossingParameter_interior_of_geometry hP w.1 w.2.val w.2.property).1
  -- Step 1: the first visit precedes the second in the traversal coordinate.
  have hlt : traversalKey (geometricVisitPosition hP v) < traversalKey (geometricVisitPosition hP w) := by
    rcases lt_or_gt_of_ne hkey_ne with h | h
    · exact h
    · exfalso
      have ht := hgap (visitTwin v)
      unfold traversalBetween at ht
      have h1 : traversalKey (geometricVisitPosition hP w) ≤
          traversalKey (geometricVisitPosition hP (visitTwin v)) := by
        by_contra hc
        exact ht (Or.inr (Or.inl ⟨not_le.mp hc, h⟩))
      have h2 : traversalKey (geometricVisitPosition hP (visitTwin v)) ≤
          traversalKey (geometricVisitPosition hP v) := by
        by_contra hc
        exact ht (Or.inr (Or.inr ⟨h, not_le.mp hc⟩))
      have hne_tw : (visitTwin v).2.val ≠ w.2.val := by
        rw [← hedge]
        exact visitTwin_edge_ne v
      have h1' : traversalKey (geometricVisitPosition hP w) <
          traversalKey (geometricVisitPosition hP (visitTwin v)) := by
        refine lt_of_le_of_ne h1 fun heq => hne_tw ?_
        have := congrArg Prod.fst (traversalKey_injective heq)
        exact this.symm
      have h2' : traversalKey (geometricVisitPosition hP (visitTwin v)) <
          traversalKey (geometricVisitPosition hP v) := by
        refine lt_of_le_of_ne h2 fun heq => visitTwin_ne v ?_
        exact geometricVisitPosition_injective hP (traversalKey_injective heq)
      rw [traversalKey_lt_iff] at h1' h2'
      simp only [geometricVisitPosition_edge] at h1' h2'
      rcases h1' with h1' | ⟨h1', -⟩
      · rcases h2' with h2' | ⟨h2', -⟩
        · rw [hedge] at h2'
          omega
        · exact visitTwin_edge_ne v h2'
      · exact hne_tw h1'.symm
  -- Step 2: no mark at all lies strictly between the two visits (cyclically).
  let _ := geoMarkLinearOrder hP
  have hgapM : ∀ x : Mark P, x ∈ (Finset.univ : Finset (Mark P)) →
      ¬ (((Sum.inr v : Mark P) < x ∧ x < Sum.inr w) ∨ (x < Sum.inr w ∧ (Sum.inr w : Mark P) < Sum.inr v) ∨
        ((Sum.inr w : Mark P) < Sum.inr v ∧ (Sum.inr v : Mark P) < x)) := by
    intro x _
    have hwv : ¬ ((Sum.inr w : Mark P) < Sum.inr v) := fun h => lt_asymm hlt h
    rintro (⟨h1, h2⟩ | ⟨_, h⟩ | ⟨h, _⟩)
    · cases x with
      | inr u => exact hgap u (Or.inl ⟨h1, h2⟩)
      | inl i =>
        change traversalKey (geometricVisitPosition hP v) < traversalKey (i, ⟨0, by norm_num⟩) at h1
        change traversalKey (i, ⟨0, by norm_num⟩) < traversalKey (geometricVisitPosition hP w) at h2
        rw [traversalKey_lt_iff] at h1 h2
        simp only [geometricVisitPosition_edge, geometricVisitPosition_parameter] at h1 h2
        rcases h1 with h1 | ⟨-, h1⟩
        · rcases h2 with h2 | ⟨h2, -⟩
          · rw [hedge] at h1
            omega
          · rw [h2, hedge] at h1
            exact lt_irrefl _ h1
        · exact absurd h1 (not_lt.mpr hv0.le)
    · exact hwv h
    · exact hwv h
  -- Step 3: the sorted-list successor.
  have hnext := SEL_sorted_next_of_no_cyclic_between (Finset.univ : Finset (Mark P))
    (Finset.mem_univ (Sum.inr v)) (Finset.mem_univ (Sum.inr w))
    (fun h => hvw (Sum.inr_injective h)) hgapM
  rw [geoMarkSuccessor_apply, geoNextMark_eq_list_next]
  convert hnext using 2
  rfl

end MarkOrder

section Corners

variable {P : LabelledTuple n}

/-- Every true corner mark owned by `q` is some corner `geoCornerMark q k` of `q`
(`geoCornerMark_exists` at an arbitrary name of the carrier). -/
theorem SEL_exists_cornerMark (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (a : Mark P) (hq : geoOwner hP S a = q) (ha : IsTrueCorner S a) :
    ∃ k : ZMod (geoCornerCount hP S q), geoCornerMark hP S q k = a := by
  subst hq
  exact geoCornerMark_exists hP S ha

/-- "The carrier is mixed regardless of all its other corners": a carrier of an independent
support owning two selected visits whose corner turns (`sgn det(d_in, d_out)`,
`turn_visit_of_traced`) are opposite and nonzero is `CarrierMixed`. -/
theorem SEL_carrierMixed_of_two_visits (hn : 3 ≤ n) (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hP) (q : GeoComponent hP S) (v₁ v₂ : Visit P)
    (h₁ : v₁.1 ∈ S) (h₂ : v₂.1 ∈ S)
    (hq₁ : geoOwner hP S (Sum.inr v₁) = q) (hq₂ : geoOwner hP S (Sum.inr v₂) = q)
    (hopp : crossingSign P v₁.2.val (visitTwin v₁).2.val =
      -crossingSign P v₂.2.val (visitTwin v₂).2.val)
    (hnz : crossingSign P v₂.2.val (visitTwin v₂).2.val ≠ 0) :
    CV.CarrierMixed hP S q := by
  rintro ⟨τ, -, hall⟩
  have htr := CV.tracedSuccessor_of_mem_Ind hn hP hS q
  obtain ⟨k₁, hk₁⟩ := SEL_exists_cornerMark hP S q (Sum.inr v₁) hq₁ h₁
  obtain ⟨k₂, hk₂⟩ := SEL_exists_cornerMark hP S q (Sum.inr v₂) hq₂ h₂
  have t₁ := CV.turn_visit_of_traced hP S hn q htr k₁ v₁ hk₁ h₁
  have t₂ := CV.turn_visit_of_traced hP S hn q htr k₂ v₂ hk₂ h₂
  rw [hall k₁] at t₁
  rw [hall k₂] at t₂
  apply hnz
  apply SEL_eq_zero_of_eq_neg
  rw [← hopp, ← t₁, ← t₂]

end Corners

section MixedLocal

variable {P : LabelledTuple n}

omit [NeZero n] in
/-- The twin of the `v`-visit of a crossing with a second edge `u ≠ v` is its `u`-visit. -/
theorem SEL_visitTwin_visitOn {x : Crossing P} {u v : ZMod n} (hxu : u ∈ x.val) (hxv : v ∈ x.val)
    (huv : u ≠ v) : visitTwin (visitOn x v hxv) = visitOn x u hxu :=
  (visitTwin_unique (visitOn x v hxv) (visitOn x u hxu) rfl
    fun h => huv (congrArg (fun z : Visit P => z.2.val) h)).symm

/-- **The mixed carrier of a nonselected pair** (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md, "The mixed
carrier"), on one polygon: `x = x_{uv}`, `y = x_{uw}` are two selected crossings of the independent
support `S` sharing the strand `u`, their two `u`-visits are adjacent among the crossing visits
(R-LOC-2 (2)), and the two corner determinants (6) have opposite nonzero signs (5). Then the
`u`-arc between the two visits is a single `ρ`-step, `ρ_S` carries the arc intact, and the carrier
through it owns the two endpoint smoothing corners — `(x, v)` and `(y, u)` if `x`'s `u`-visit comes
first, `(y, w)` and `(x, u)` otherwise — and is mixed. -/
theorem SEL_mixed_of_adjacent (hn : 3 ≤ n) (hP : CrossingGeometry P)
    {S : Finset (Crossing P)} (hS : S ∈ CV.Ind hP)
    {x y : Crossing P} {u v w : ZMod n} (hxu : u ∈ x.val) (hxv : v ∈ x.val) (hyu : u ∈ y.val)
    (hyw : w ∈ y.val) (hxS : x ∈ S) (hyS : y ∈ S) (huv : u ≠ v) (huw : u ≠ w)
    (hadj : AdjacentVisits hP (visitOn x u hxu) (visitOn y u hyu))
    (hs1 : crossingSign P v u = -crossingSign P u w)
    (hs2 : crossingSign P w u = -crossingSign P u v)
    (hnv : crossingSign P u v ≠ 0) (hnw : crossingSign P u w ≠ 0) :
    MixedSharedStrandCarrier hP S x y hxu hxv hyu hyw := by
  have htx : visitTwin (visitOn x v hxv) = visitOn x u hxu := SEL_visitTwin_visitOn hxu hxv huv
  have hty : visitTwin (visitOn y w hyw) = visitOn y u hyu := SEL_visitTwin_visitOn hyu hyw huw
  have htx' : visitTwin (visitOn x u hxu) = visitOn x v hxv := by
    rw [← htx, visitTwin_involutive]
  have hty' : visitTwin (visitOn y u hyu) = visitOn y w hyw := by
    rw [← hty, visitTwin_involutive]
  obtain ⟨hne, hcase | hcase⟩ := hadj
  · -- `x`'s `u`-visit immediately precedes `y`'s: the arc runs from `(x, u)` to `(y, u)`.
    have hsucc : geoMarkSuccessor hP (Sum.inr (visitOn x u hxu)) = Sum.inr (visitOn y u hyu) :=
      SEL_geoMarkSuccessor_eq_of_no_visit_between hP hne rfl hcase
    have hρ : geoSmoothingSuccessor hP S (Sum.inr (visitOn x v hxv)) = Sum.inr (visitOn y u hyu) := by
      rw [geoSmoothingSuccessor_visit_of_mem hP S _ hxS, htx, hsucc]
    have hown : geoOwner hP S (Sum.inr (visitOn x v hxv)) = geoOwner hP S (Sum.inr (visitOn y u hyu)) := by
      rw [← hρ, geoOwner_successor]
    refine ⟨geoOwner hP S (Sum.inr (visitOn y u hyu)), Or.inl ⟨hown, rfl⟩, ?_⟩
    refine SEL_carrierMixed_of_two_visits hn hP hS _ (visitOn x v hxv) (visitOn y u hyu) hxS hyS
      hown rfl ?_ ?_
    · rw [htx, hty']
      exact hs1
    · rw [hty']
      exact hnw
  · -- `y`'s `u`-visit immediately precedes `x`'s: the arc runs from `(y, u)` to `(x, u)`.
    have hsucc : geoMarkSuccessor hP (Sum.inr (visitOn y u hyu)) = Sum.inr (visitOn x u hxu) :=
      SEL_geoMarkSuccessor_eq_of_no_visit_between hP hne.symm rfl hcase
    have hρ : geoSmoothingSuccessor hP S (Sum.inr (visitOn y w hyw)) = Sum.inr (visitOn x u hxu) := by
      rw [geoSmoothingSuccessor_visit_of_mem hP S _ hyS, hty, hsucc]
    have hown : geoOwner hP S (Sum.inr (visitOn y w hyw)) = geoOwner hP S (Sum.inr (visitOn x u hxu)) := by
      rw [← hρ, geoOwner_successor]
    refine ⟨geoOwner hP S (Sum.inr (visitOn x u hxu)), Or.inr ⟨hown, rfl⟩, ?_⟩
    refine SEL_carrierMixed_of_two_visits hn hP hS _ (visitOn y w hyw) (visitOn x u hxu) hyS hxS
      hown rfl ?_ ?_
    · rw [hty, htx']
      exact hs2
    · rw [htx']
      exact hnv

/-- A support with a mixed carrier has `wind = 0` (def:wind: "a product containing this weight, is
zero"). -/
theorem SEL_wind_eq_zero_of_mixed (hP : CrossingGeometry P) (S : Finset (Crossing P))
    {x y : Crossing P} {u v w : ZMod n} {hxu : u ∈ x.val} {hxv : v ∈ x.val} {hyu : u ∈ y.val}
    {hyw : w ∈ y.val} (h : MixedSharedStrandCarrier hP S x y hxu hxv hyu hyw) :
    CV.wind hP S = 0 := by
  obtain ⟨q, -, hq⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ q) (CV.weight_of_mixed hP S q hq)

/-- "its entire X1 row is zero before any coefficient is read": a row whose selector vanishes
whenever it is present is zero (absent rows are zero by convention). -/
theorem SEL_rowTerm_eq_zero (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hw : S ∈ CV.Ind hG.crossingGeometry → CV.wind hG.crossingGeometry S = 0) :
    rowTerm hn hG S = 0 := by
  by_cases hS : S ∈ CV.Ind hG.crossingGeometry
  · rw [rowTerm_of_mem_Ind hn hG hS, hw hS, zero_mul]
  · exact rowTerm_of_not_mem_Ind hn hG hS

end MixedLocal

section SELFields

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- The generic-table row shrinks to any smaller radius (every clause is quantified over the
punctured neighbourhood). -/
theorem SEL_genericTableData_mono {δ' : ℝ} (h : δ' ≤ δ) (hG : GenericTableData E e f g δ) :
    GenericTableData E e f g δ' where
  nonzero t ht := hG.nonzero t (G2.punctured_of_le h ht)
  cramer t ht := hG.cramer t (G2.punctured_of_le h ht)
  sign_vector t ht := hG.sign_vector t (G2.punctured_of_le h ht)
  edges_iff t ht := hG.edges_iff t (G2.punctured_of_le h ht)
  chamber_change t t' ht ht' :=
    hG.chamber_change t t' (G2.punctured_of_le h ht) (G2.punctured_of_le h ht')
  extreme_iff_orders t ht := hG.extreme_iff_orders t (G2.punctured_of_le h ht)
  extreme_iff_alternating t ht := hG.extreme_iff_alternating t (G2.punctured_of_le h ht)
  generic_iff_nonalternating t ht := hG.generic_iff_nonalternating t (G2.punctured_of_le h ht)
  branch_count := hG.branch_count
  selected_unique := hG.selected_unique
  selected_is_graph_selected t ht := hG.selected_is_graph_selected t (G2.punctured_of_le h ht)
  local_word t ht := hG.local_word t (G2.punctured_of_le h ht)
  canonical_words t ht := hG.canonical_words t (G2.punctured_of_le h ht)
  local_supports t ht := hG.local_supports t (G2.punctured_of_le h ht)
  local_undominated t ht := hG.local_undominated t (G2.punctured_of_le h ht)
  mask_sharpening t ht := hG.mask_sharpening t (G2.punctured_of_le h ht)
  skeleton_table := hG.skeleton_table
  successor_table := hG.successor_table
  residual_table := hG.residual_table

/-- "All four quantities are nonzero on either chamber of a simple wall": the three strand signs
`s_a, s_b, s_c` are nonzero (`GenericTableData.nonzero`). -/
theorem SEL_strandSigns_ne_zero (hG : GenericTableData E e f g δ) (t : E.Parameter)
    (ht : Punctured E δ t) :
    strandSign (E.curve t) e f ≠ 0 ∧ strandSign (E.curve t) e g ≠ 0 ∧
      strandSign (E.curve t) f g ≠ 0 := by
  obtain ⟨h1, h2, h3, -⟩ := hG.nonzero t ht
  exact ⟨sign_ne_zero.mpr h1, sign_ne_zero.mpr h2, sign_ne_zero.mpr h3⟩

/-- Field `selected_pair_unique`: the event-level instance of `selected_unique` on the nonzero,
nonalternating sign triple of a generic side. -/
theorem SEL_selected_pair_unique (hG : GenericTableData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
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
        SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g))) := by
  intro t ht hef heg hfg hgen
  obtain ⟨ha, hb, hc⟩ := SEL_strandSigns_ne_zero hG t ht
  have hna := (hG.generic_iff_nonalternating t ht hef heg hfg).mp hgen
  exact (hG.selected_unique _ _ _ ha hb hc hna).1

/-- Field `corner_signs_opposite`: (5) "failure of the selected-condition is `sgn det(u,v) =
sgn det(u,w)`" (a nonzero `SignType` case split) and (6) `det(v,u) = −det(u,v)`
(`crossingSign_swap`), for the three pairs in both traversal orders. -/
theorem SEL_corner_signs_opposite (hG : GenericTableData E e f g δ) :
    ∀ t : E.Parameter, Punctured E δ t →
    (¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      crossingSign (E.curve t) f e = -crossingSign (E.curve t) e g ∧
      crossingSign (E.curve t) g e = -crossingSign (E.curve t) e f) ∧
    (¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) →
      crossingSign (E.curve t) e f = -crossingSign (E.curve t) f g ∧
      crossingSign (E.curve t) g f = -crossingSign (E.curve t) f e) ∧
    (¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      crossingSign (E.curve t) e g = -crossingSign (E.curve t) g f ∧
      crossingSign (E.curve t) f g = -crossingSign (E.curve t) g e) := by
  intro t ht
  obtain ⟨ha, hb, hc⟩ := SEL_strandSigns_ne_zero hG t ht
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have hab : crossingSign (E.curve t) e f = crossingSign (E.curve t) e g :=
      SEL_eq_of_not_eq_neg _ _ ha hb h
    constructor
    · rw [crossingSign_swap (E.curve t) e f, hab]
    · rw [crossingSign_swap (E.curve t) e g, hab]
  · have hac : crossingSign (E.curve t) e f = -crossingSign (E.curve t) f g :=
      SEL_eq_neg_of_not_eq _ _ ha hc h
    constructor
    · exact hac
    · rw [crossingSign_swap (E.curve t) f g, crossingSign_swap (E.curve t) e f, hac, neg_neg]
  · have hbc : crossingSign (E.curve t) e g = crossingSign (E.curve t) f g :=
      SEL_eq_of_not_eq_neg _ _ hb hc h
    constructor
    · rw [crossingSign_swap (E.curve t) f g, neg_neg, hbc]
    · rw [crossingSign_swap (E.curve t) e g, neg_neg, hbc]

/-- Field `mixed_carrier`: R-LOC-2 (2) `adjacent` + (5)–(6) through `SEL_mixed_of_adjacent`, for
each nonselected pair on the side where it is present. (The generic-orbit, outside-support and
full-availability hypotheses of the clause are not needed by the argument — "arbitrary exterior gaps
and outside independent support `Q`".) -/
theorem SEL_mixed_carrier (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
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
        (mem_pair_right e g) (mem_pair_left e g) (mem_pair_right f g) (mem_pair_left f g)) := by
  intro t ht hef heg hfg _ Q _ _
  obtain ⟨ha, hb, hc⟩ := SEL_strandSigns_ne_zero hG t ht
  obtain ⟨hadjE, hadjF, hadjG⟩ := hL.adjacent t ht hef heg hfg
  obtain ⟨hsAB, hsAC, hsBC⟩ := SEL_corner_signs_opposite hG t ht
  have hef' : e ≠ f := P1.ne_of_isCrossing_pair hef
  have heg' : e ≠ g := P1.ne_of_isCrossing_pair heg
  have hfg' : f ≠ g := P1.ne_of_isCrossing_pair hfg
  have hfe : crossingSign (E.curve t) f e ≠ 0 := by
    rw [crossingSign_swap]; exact SEL_neg_ne_zero _ ha
  have hge : crossingSign (E.curve t) g e ≠ 0 := by
    rw [crossingSign_swap]; exact SEL_neg_ne_zero _ hb
  have hgf : crossingSign (E.curve t) g f ≠ 0 := by
    rw [crossingSign_swap]; exact SEL_neg_ne_zero _ hc
  refine ⟨fun hns hind => ?_, fun hns hind => ?_, fun hns hind => ?_⟩
  · -- pair `ab`: shared strand `u = e`, others `v = f`, `w = g`
    obtain ⟨hs1, hs2⟩ := hsAB hns
    exact SEL_mixed_of_adjacent hn (geomAt E t ht.1) hind (mem_pair_left e f) (mem_pair_right e f)
      (mem_pair_left e g) (mem_pair_right e g)
      (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
      (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      hef' heg' hadjE hs1 hs2 ha hb
  · -- pair `ac`: shared strand `u = f`, others `v = e`, `w = g`
    obtain ⟨hs1, hs2⟩ := hsAC hns
    exact SEL_mixed_of_adjacent hn (geomAt E t ht.1) hind (mem_pair_right e f) (mem_pair_left e f)
      (mem_pair_left f g) (mem_pair_right f g)
      (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
      (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      hef'.symm hfg' hadjF hs1 hs2 hfe hc
  · -- pair `bc`: shared strand `u = g`, others `v = e`, `w = f`
    obtain ⟨hs1, hs2⟩ := hsBC hns
    exact SEL_mixed_of_adjacent hn (geomAt E t ht.1) hind (mem_pair_right e g) (mem_pair_left e g)
      (mem_pair_right f g) (mem_pair_left f g)
      (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
      (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      heg'.symm hfg'.symm hadjG hs1 hs2 hge hgf

/-- Field `selector_zero`: the mixed carrier's weight is `0` (`weight_of_mixed`), so is the product
`wind`. -/
theorem SEL_selector_zero (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
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
      CV.wind (geomAt E t ht.1) (Q ∪ {xPair heg, xPair hfg}) = 0) := by
  intro t ht hef heg hfg hgen Q hQ hfull
  obtain ⟨h1, h2, h3⟩ := SEL_mixed_carrier hn hL hG t ht hef heg hfg hgen Q hQ hfull
  exact ⟨fun hns hind => SEL_wind_eq_zero_of_mixed _ _ (h1 hns hind),
    fun hns hind => SEL_wind_eq_zero_of_mixed _ _ (h2 hns hind),
    fun hns hind => SEL_wind_eq_zero_of_mixed _ _ (h3 hns hind)⟩

/-- Field `row_zero`: "Consequently its entire X1 row is zero before any coefficient is read"
(present rows by `selector_zero`, absent rows by convention). -/
theorem SEL_row_zero (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) :
    ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair heg}) = 0) ∧
    (¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair hfg}) = 0) ∧
    (¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg, xPair hfg}) = 0) := by
  intro t ht hef heg hfg hgen Q hQ hfull
  obtain ⟨h1, h2, h3⟩ := SEL_selector_zero hn hL hG t ht hef heg hfg hgen Q hQ hfull
  exact ⟨fun hns => SEL_rowTerm_eq_zero hn _ (h1 hns), fun hns => SEL_rowTerm_eq_zero hn _ (h2 hns),
    fun hns => SEL_rowTerm_eq_zero hn _ (h3 hns)⟩

/-- **Assembly of the bundle** at a radius carrying R:localization and R:generic_table. -/
theorem SEL_genericSelectorData (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) : GenericSelectorData hn E e f g δ where
  selected_pair_unique := SEL_selected_pair_unique hG
  corner_signs_opposite := SEL_corner_signs_opposite hG
  mixed_carrier := SEL_mixed_carrier hn hL hG
  selector_zero := SEL_selector_zero hn hL hG
  row_zero := SEL_row_zero hn hL hG

end SELFields

end SEL

/-- **Row 172, R:generic_selector** (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md). -/
theorem generic_selector (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectorData hn E e f g δ := by
  -- Unit SEL: the common radius of rows 164 (R-LOC-2 (2), adjacency) and 172 (the sign
  -- classification); every field by `SEL_genericSelectorData`.
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hG⟩ := generic_table E e f g h3 h4e h4f h4g hE
  refine ⟨min δL δG, lt_min hδL hδG, (min_le_left _ _).trans hδLr, ?_⟩
  exact SEL_genericSelectorData hn (F1.localizationData_mono (min_le_left _ _) hL)
    (SEL_genericTableData_mono (min_le_right _ _) hG)

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

/-! ## Unit GT (wave 3, 2026-09-14) — row 173: the corner-level wall transport, the endpoint rows, G11

Inserted between the frozen field lemma `PRE_173_canonical_branch` and the row theorem. Report:
`W3_GT_REPORT.md`; portable module: `RLaneX1Rows3.lean`. -/

/-! ## Unit GT (row 173, wave 3) — the corner-level wall transport at full availability

Section `GT`: the AV toolkit's corner-cycle transport (`AV_nextCorner`, `AV_cornerSucc`, their order
specifications) rebuilt on **wall data without the availability-`≤ 1` clause `dominated`**: the reversed
same-edge pairs of `R-LOC-2 (2)` are the pairs of distinct `T`-visits on one edge (`GT_Rev`); a mark is
*good* when none of its reversed partners is a corner (`GT_Good`), and the wall data ask only that no two
corners form a reversed pair (`corners_apart`) — true whenever the support contains at most one triangle
crossing (rows `∅`, `a`, `b`, `c` of the full-availability fibre). Every lemma is the AV lemma with
`AV_good_key_lt` replaced by `GT_good_key_lt`. -/

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

/-- A *reversed pair* of the wall: two same-edge visits of two distinct `T`-crossings (R-LOC-2 (2)). -/
def GT_Rev (T : Finset (Crossing P)) (v w : Visit P) : Prop :=
  v.1 ∈ T ∧ w.1 ∈ T ∧ v.1 ≠ w.1 ∧ v.2.val = w.2.val

omit [NeZero n] in
theorem GT_Rev.symm {T : Finset (Crossing P)} {v w : Visit P} (h : GT_Rev T v w) : GT_Rev T w v :=
  ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩

omit [NeZero n] in
theorem GT_not_rev_of_not_mem_left {T : Finset (Crossing P)} {v w : Visit P} (hv : v.1 ∉ T) :
    ¬ GT_Rev T v w := fun h => hv h.1

omit [NeZero n] in
theorem GT_not_rev_of_not_mem_right {T : Finset (Crossing P)} {v w : Visit P} (hw : w.1 ∉ T) :
    ¬ GT_Rev T v w := fun h => hw h.2.1

omit [NeZero n] in
theorem GT_not_rev_of_edge_ne {T : Finset (Crossing P)} {v w : Visit P} (h : v.2.val ≠ w.2.val) :
    ¬ GT_Rev T v w := fun h' => h h'.2.2.2

/-- **Wall data for a support `S` across a simple RIII wall at full availability**: as `AV_Wall`
(visit-key orders carried except on the reversed pairs, turns, signs, a common ray), with the
transported support independent and — in place of `dominated` — no two corners of `S` forming a
reversed pair. -/
structure GT_Wall (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (T S : Finset (Crossing P)) : Prop where
  indep : GeoIndependent hP S
  indep' : GeoIndependent hP' (transportSupport hs S)
  key_lt : ∀ v w : Visit P, ¬ GT_Rev T v w →
    (geometricVisitKey hP v < geometricVisitKey hP w ↔
      geometricVisitKey hP' (visitTransport hs v) < geometricVisitKey hP' (visitTransport hs w))
  corners_apart : ∀ v w : Visit P, GT_Rev T v w → ¬ (v.1 ∈ S ∧ w.1 ∈ S)
  turn_eq : ∀ i, turn P' i = turn P i
  sign_eq : ∀ i j, IsCrossing P {i, j} → crossingSign P' i j = crossingSign P i j
  ray : ∃ r : Plane, ∀ h : ZMod n, det r (edge P h) ≠ 0 ∧
    SignType.sign (det r (edge P' h)) = SignType.sign (det r (edge P h))

/-- A *good* mark: none of its reversed partners is a corner, so its key order relative to every
corner is carried across the wall. -/
def GT_Good (T S : Finset (Crossing P)) (m : Mark P) : Prop :=
  ∀ v : Visit P, m = Sum.inr v → ∀ w : Visit P, GT_Rev T v w → ¬ IsTrueCorner S (Sum.inr w)

omit [NeZero n] in
theorem GT_good_vertex (T S : Finset (Crossing P)) (i : ZMod n) : GT_Good T S (Sum.inl i) :=
  fun _ h => nomatch h

omit [NeZero n] in
/-- A visit of a crossing outside `T` is good (it has no reversed partner). -/
theorem GT_good_of_not_mem (T S : Finset (Crossing P)) {v : Visit P} (hv : v.1 ∉ T) :
    GT_Good T S (Sum.inr v) := by
  intro v' hv' w hrev
  obtain rfl := Sum.inr.inj hv'
  exact absurd hrev.1 hv

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}

omit [NeZero n] in
theorem GT_good_of_corner (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : IsTrueCorner S m) :
    GT_Good T S m := by
  intro v hv w hrev hw
  subst hv
  exact W.corners_apart v w hrev ⟨hm, hw⟩

/-- Mark keys are carried for every pair of marks that is not a reversed pair (the accepted
`geoMarkKey_lt_transport_of_visitKey`, word for word, with the exception built in). -/
theorem GT_mark_key_lt (W : GT_Wall hP hP' hs T S) (a b : Mark P)
    (hab : ∀ v w : Visit P, a = Sum.inr v → b = Sum.inr w → ¬ GT_Rev T v w) :
    geoMarkKey hP a < geoMarkKey hP b ↔
      geoMarkKey hP' (markTransport hs a) < geoMarkKey hP' (markTransport hs b) := by
  cases a with
  | inl i =>
    cases b with
    | inl k => exact Iff.rfl
    | inr v =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hP' (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (i.val < v.2.val.val ∨ i = v.2.val ∧ (0 : ℝ) < visitParameter v) ↔
        (i.val < v.2.val.val ∨ i = v.2.val ∧ (0 : ℝ) < visitParameter (visitTransport hs v))
      exact or_congr Iff.rfl (and_congr Iff.rfl ⟨fun _ => h2, fun _ => h1⟩)
  | inr v =>
    cases b with
    | inl i =>
      have h1 := (crossingParameter_interior_of_geometry hP v.1 v.2.val v.2.property).1
      have h2 := (crossingParameter_interior_of_geometry hP' (visitTransport hs v).1
        (visitTransport hs v).2.val (visitTransport hs v).2.property).1
      unfold geoMarkKey
      rw [traversalKey_lt_iff, traversalKey_lt_iff]
      change (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter v < (0 : ℝ)) ↔
        (v.2.val.val < i.val ∨ v.2.val = i ∧ visitParameter (visitTransport hs v) < (0 : ℝ))
      exact or_congr Iff.rfl (and_congr Iff.rfl
        ⟨fun h => (lt_asymm h1 h).elim, fun h => (lt_asymm h2 h).elim⟩)
    | inr w => exact W.key_lt v w (hab v w rfl rfl)

/-- A good mark and a corner: their key order is carried, in both directions. -/
theorem GT_good_key_lt (W : GT_Wall hP hP' hs T S) {m d : Mark P} (hm : GT_Good T S m)
    (hd : IsTrueCorner S d) :
    (geoMarkKey hP m < geoMarkKey hP d ↔
        geoMarkKey hP' (markTransport hs m) < geoMarkKey hP' (markTransport hs d)) ∧
    (geoMarkKey hP d < geoMarkKey hP m ↔
        geoMarkKey hP' (markTransport hs d) < geoMarkKey hP' (markTransport hs m)) := by
  have hno : ∀ v w : Visit P, m = Sum.inr v → d = Sum.inr w → ¬ GT_Rev T v w := by
    rintro v w rfl rfl hrev
    exact hm v rfl w hrev hd
  exact ⟨GT_mark_key_lt W m d hno,
    GT_mark_key_lt W d m fun w v hw hv h => hno v w hv hw h.symm⟩

/-! ### Transport of the next-corner specifications (the AV proofs, `GT_good_key_lt` in place of
`AV_good_key_lt`) -/

theorem GT_ncspec_transport (W : GT_Wall hP hP' hs T S) {m d : Mark P} (hm : GT_Good T S m)
    (h : AV_NCSpec hP S m d) :
    AV_NCSpec hP' (transportSupport hs S) (markTransport hs m) (markTransport hs d) := by
  obtain ⟨hc, h⟩ := h
  refine ⟨(AV_corner_transport S d).mpr hc, ?_⟩
  rcases h with ⟨hle, hmin⟩ | ⟨hall, rfl⟩
  · left
    refine ⟨?_, ?_⟩
    · rw [← not_lt] at hle ⊢
      exact fun h' => hle (((GT_good_key_lt W hm hc).2).mpr h')
    · intro d'' hd'' hle''
      obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
      have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
      have hle' : geoMarkKey hP m ≤ geoMarkKey hP d' := by
        rw [← not_lt] at hle'' ⊢
        exact fun h' => hle'' (((GT_good_key_lt W hm hd').2).mp h')
      have hdd' := hmin d' hd' hle'
      rw [← not_lt] at hdd' ⊢
      exact fun h' => hdd' (((GT_good_key_lt W (GT_good_of_corner W hc) hd').2).mpr h')
  · right
    refine ⟨?_, markTransport_vertex hs 0⟩
    intro d'' hd''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    exact ((GT_good_key_lt W hm hd').2).mp (hall d' hd')

open scoped Classical in
/-- **The next corner of a good mark is carried across the wall.** -/
theorem GT_nextCorner_transport (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : GT_Good T S m) :
    AV_nextCorner hP' (transportSupport hs S) (markTransport hs m) =
      markTransport hs (AV_nextCorner hP S m) :=
  AV_ncspec_unique (AV_nextCorner_spec hP' _ _) (GT_ncspec_transport W hm (AV_nextCorner_spec hP S m))

theorem GT_csspec_transport (W : GT_Wall hP hP' hs T S) {x d : Mark P} (hx : IsTrueCorner S x)
    (h : AV_CSSpec hP S x d) :
    AV_CSSpec hP' (transportSupport hs S) (markTransport hs x) (markTransport hs d) := by
  obtain ⟨hc, h⟩ := h
  have hxg : GT_Good T S x := GT_good_of_corner W hx
  refine ⟨(AV_corner_transport S d).mpr hc, ?_⟩
  rcases h with ⟨hlt, hmin⟩ | ⟨hall, rfl⟩
  · left
    refine ⟨((GT_good_key_lt W hxg hc).1).mp hlt, ?_⟩
    intro d'' hd'' hlt''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    have hlt' : geoMarkKey hP x < geoMarkKey hP d' := ((GT_good_key_lt W hxg hd').1).mpr hlt''
    have hdd' := hmin d' hd' hlt'
    rw [← not_lt] at hdd' ⊢
    exact fun h' => hdd' (((GT_good_key_lt W (GT_good_of_corner W hc) hd').2).mpr h')
  · right
    refine ⟨?_, markTransport_vertex hs 0⟩
    intro d'' hd''
    obtain ⟨d', rfl⟩ := (markTransport hs).surjective d''
    have hd' : IsTrueCorner S d' := (AV_corner_transport S d').mp hd''
    have h1 := hall d' hd'
    rw [← not_lt] at h1 ⊢
    exact fun h' => h1 (((GT_good_key_lt W hxg hd').1).mpr h')

/-- **The corner successor of a corner is carried across the wall.** -/
theorem GT_cornerSucc_transport (W : GT_Wall hP hP' hs T S) {c : Mark P} (hc : IsTrueCorner S c) :
    AV_cornerSucc hP' (transportSupport hs S) (markTransport hs c) =
      markTransport hs (AV_cornerSucc hP S c) := by
  have h1 : AV_CSSpec hP' (transportSupport hs S) (markTransport hs (selectedMarkPerm S c))
      (AV_cornerSucc hP' (transportSupport hs S) (markTransport hs c)) := by
    unfold AV_cornerSucc
    rw [geoSmoothingSuccessor_apply, selectedMarkPerm_markTransport]
    exact AV_nextCorner_succ_spec hP' _ _
  have h2 : AV_CSSpec hP' (transportSupport hs S) (markTransport hs (selectedMarkPerm S c))
      (markTransport hs (AV_cornerSucc hP S c)) :=
    GT_csspec_transport W (AV_corner_selectedMarkPerm S hc)
      (by unfold AV_cornerSucc; rw [geoSmoothingSuccessor_apply]; exact AV_nextCorner_succ_spec hP S _)
  exact AV_csspec_unique h1 h2

/-! ### The carrier bijection across the wall -/

theorem GT_carrierMap_aux (W : GT_Wall hP hP' hs T S) (m : Mark P) :
    geoOwner hP' (transportSupport hs S)
        (markTransport hs (AV_nextCorner hP S (geoSmoothingSuccessor hP S m))) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := by
  by_cases hm : IsTrueCorner S m
  · change geoOwner hP' (transportSupport hs S) (markTransport hs (AV_cornerSucc hP S m)) = _
    rw [← GT_cornerSucc_transport W hm, AV_cornerSucc_owner, AV_nextCorner_of_corner hm]
  · rw [AV_smoothing_of_not_corner hP S hm, AV_nextCorner_succ hm]

theorem GT_carrierMap_pow (W : GT_Wall hP hP' hs T S) (m : Mark P) (k : ℕ) :
    geoOwner hP' (transportSupport hs S)
        (markTransport hs (AV_nextCorner hP S ((geoSmoothingSuccessor hP S ^ k) m))) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, GT_carrierMap_aux W, ih]

/-- The carrier map across the wall: the carrier of `P'` through the transported next corner. -/
noncomputable def GT_carrierMap (W : GT_Wall hP hP' hs T S) :
    GeoComponent hP S → GeoComponent hP' (transportSupport hs S) :=
  Quotient.lift
    (fun m => geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)))
    (fun a b hab => by
      obtain ⟨i, -, rfl⟩ :=
        (show (geoSmoothingSuccessor hP S).SameCycle a b from hab).exists_pow_eq'
      exact (GT_carrierMap_pow W a i).symm)

theorem GT_carrierMap_owner (W : GT_Wall hP hP' hs T S) (m : Mark P) :
    GT_carrierMap W (geoOwner hP S m) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := rfl

theorem GT_carrierInv_aux (W : GT_Wall hP hP' hs T S) (m' : Mark P') :
    geoOwner hP S ((markTransport hs).symm
        (AV_nextCorner hP' (transportSupport hs S) (geoSmoothingSuccessor hP' (transportSupport hs S) m'))) =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
  by_cases hm : IsTrueCorner (transportSupport hs S) m'
  · change geoOwner hP S ((markTransport hs).symm (AV_cornerSucc hP' (transportSupport hs S) m')) = _
    have hc : IsTrueCorner S ((markTransport hs).symm m') := by
      rw [← AV_corner_transport (hs := hs) S ((markTransport hs).symm m'), Equiv.apply_symm_apply]
      exact hm
    have := GT_cornerSucc_transport W hc
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply, AV_cornerSucc_owner, AV_nextCorner_of_corner hm]
  · rw [AV_smoothing_of_not_corner hP' _ hm, AV_nextCorner_succ hm]

theorem GT_carrierInv_pow (W : GT_Wall hP hP' hs T S) (m' : Mark P') (k : ℕ) :
    geoOwner hP S ((markTransport hs).symm
        (AV_nextCorner hP' (transportSupport hs S) ((geoSmoothingSuccessor hP' (transportSupport hs S) ^ k) m'))) =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
  induction k with
  | zero => rw [pow_zero, Equiv.Perm.one_apply]
  | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, GT_carrierInv_aux W, ih]

/-- The inverse carrier map. -/
noncomputable def GT_carrierInv (W : GT_Wall hP hP' hs T S) :
    GeoComponent hP' (transportSupport hs S) → GeoComponent hP S :=
  Quotient.lift
    (fun m' => geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')))
    (fun a b hab => by
      obtain ⟨i, -, rfl⟩ :=
        (show (geoSmoothingSuccessor hP' (transportSupport hs S)).SameCycle a b from hab).exists_pow_eq'
      exact (GT_carrierInv_pow W a i).symm)

theorem GT_carrierInv_owner (W : GT_Wall hP hP' hs T S) (m' : Mark P') :
    GT_carrierInv W (geoOwner hP' (transportSupport hs S) m') =
      geoOwner hP S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := rfl

/-- **The carriers of `S` correspond to the carriers of the transported support across the wall**:
the corner cycles are carried, corner by corner. -/
noncomputable def GT_carrierEquiv (W : GT_Wall hP hP' hs T S) :
    GeoComponent hP S ≃ GeoComponent hP' (transportSupport hs S) where
  toFun := GT_carrierMap W
  invFun := GT_carrierInv W
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h m =>
      change GT_carrierInv W (GT_carrierMap W (geoOwner hP S m)) = geoOwner hP S m
      rw [GT_carrierMap_owner, GT_carrierInv_owner,
        AV_nextCorner_of_corner ((AV_corner_transport S _).mpr (AV_nextCorner_corner hP S m)),
        Equiv.symm_apply_apply, AV_nextCorner_owner]
  right_inv q' := by
    induction q' using Quotient.inductionOn with
    | h m' =>
      change GT_carrierMap W (GT_carrierInv W (geoOwner hP' (transportSupport hs S) m')) =
        geoOwner hP' (transportSupport hs S) m'
      rw [GT_carrierInv_owner, GT_carrierMap_owner]
      have hc : IsTrueCorner S ((markTransport hs).symm (AV_nextCorner hP' (transportSupport hs S) m')) := by
        rw [← AV_corner_transport (hs := hs) S, Equiv.apply_symm_apply]
        exact AV_nextCorner_corner hP' _ m'
      rw [AV_nextCorner_of_corner hc, Equiv.apply_symm_apply, AV_nextCorner_owner]

theorem GT_carrierEquiv_owner (W : GT_Wall hP hP' hs T S) (m : Mark P) :
    GT_carrierEquiv W (geoOwner hP S m) =
      geoOwner hP' (transportSupport hs S) (markTransport hs (AV_nextCorner hP S m)) := rfl

/-- **Ownership of good marks is carried**: a good mark lies on the copy of its carrier. -/
theorem GT_owner_transport (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : GT_Good T S m) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) =
      GT_carrierEquiv W (geoOwner hP S m) := by
  rw [GT_carrierEquiv_owner, ← GT_nextCorner_transport W hm, AV_nextCorner_owner]

theorem GT_owner_transport_corner (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : IsTrueCorner S m) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) =
      GT_carrierEquiv W (geoOwner hP S m) :=
  GT_owner_transport W (GT_good_of_corner W hm)

/-- Ownership of a good mark, as an equivalence of "lies on `q`" and "lies on the copy of `q`". -/
theorem GT_owner_iff (W : GT_Wall hP hP' hs T S) {m : Mark P} (hm : GT_Good T S m)
    (q : GeoComponent hP S) :
    geoOwner hP' (transportSupport hs S) (markTransport hs m) = GT_carrierEquiv W q ↔
      geoOwner hP S m = q := by
  rw [GT_owner_transport W hm]
  exact (GT_carrierEquiv W).injective.eq_iff

/-! ### The corner list of a carrier is carried literally; turns, selector, `wind` -/

theorem GT_cornerList_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    (geoComponentCornerList hP S q).map (markTransport hs) =
      geoComponentCornerList hP' (transportSupport hs S) (GT_carrierEquiv W q) := by
  apply List.Perm.eq_of_pairwise (le := fun a b => geoMarkKey hP' a < geoMarkKey hP' b)
  · intro a b _ _ h1 h2
    exact absurd h2 (lt_asymm h1)
  · rw [List.pairwise_map]
    refine (AV_cornerList_pairwise hP S q).imp_of_mem ?_
    intro a b ha hb hab
    exact ((GT_good_key_lt W
      (GT_good_of_corner W ((mem_geoComponentCornerList hP S q a).mp ha).2)
      ((mem_geoComponentCornerList hP S q b).mp hb).2).1).mp hab
  · exact AV_cornerList_pairwise hP' _ _
  · rw [List.perm_ext_iff_of_nodup
      ((geoComponentCornerList_nodup hP S q).map (markTransport hs).injective)
      (geoComponentCornerList_nodup hP' _ _)]
    intro a'
    obtain ⟨a, rfl⟩ := (markTransport hs).surjective a'
    rw [List.mem_map_of_injective (markTransport hs).injective, mem_geoComponentCornerList,
      mem_geoComponentCornerList, AV_corner_transport]
    constructor
    · rintro ⟨hq, hc⟩
      exact ⟨by rw [GT_owner_transport_corner W hc, hq], hc⟩
    · rintro ⟨hq, hc⟩
      refine ⟨?_, hc⟩
      rw [GT_owner_transport_corner W hc] at hq
      exact (GT_carrierEquiv W).injective hq

theorem GT_cornerCount_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCornerCount hP' (transportSupport hs S) (GT_carrierEquiv W q) = geoCornerCount hP S q := by
  unfold geoCornerCount
  rw [← GT_cornerList_eq W q, List.length_map]

theorem GT_cornerMark_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    geoCornerMark hP' (transportSupport hs S) (GT_carrierEquiv W q)
        (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q).symm) k) =
      markTransport hs (geoCornerMark hP S q k) := by
  have hL := GT_cornerList_eq W q
  have hlen : k.val < (geoComponentCornerList hP' (transportSupport hs S) (GT_carrierEquiv W q)).length := by
    rw [← hL, List.length_map]; exact ZMod.val_lt k
  have h3 : k.val < ((geoComponentCornerList hP S q).map (markTransport hs)).length := by
    rw [List.length_map]; exact ZMod.val_lt k
  unfold geoCornerMark
  refine (geo_getElem_congr _ _ rfl _ _ _ hlen (geo_zmod_val_cast (GT_cornerCount_eq W q).symm k)).trans ?_
  refine (geo_getElem_congr _ _ hL.symm _ _ hlen h3 rfl).trans ?_
  exact List.getElem_map _

theorem GT_cornerMark_eq' (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (j : ZMod (geoCornerCount hP' (transportSupport hs S) (GT_carrierEquiv W q))) :
    geoCornerMark hP' (transportSupport hs S) (GT_carrierEquiv W q) j =
      markTransport hs (geoCornerMark hP S q (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q)) j)) := by
  have h := GT_cornerMark_eq W q (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q)) j)
  rwa [geo_zmod_cast_cast (GT_cornerCount_eq W q) j] at h

/-- The corner polygon of `q` read at the geometry of `P'`. -/
noncomputable def GT_tcp (_W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    LabelledTuple (geoCornerCount hP S q) :=
  fun k => traversalEvaluation P' (geoMarkPosition hP' (markTransport hs (geoCornerMark hP S q k)))

theorem GT_cornerPolygon_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    geoCornerPolygon hP' (transportSupport hs S) (GT_carrierEquiv W q) =
      geoRecast (GT_cornerCount_eq W q) (GT_tcp W q) := by
  funext j
  show traversalEvaluation P' (geoMarkPosition hP' (geoCornerMark hP' (transportSupport hs S)
    (GT_carrierEquiv W q) j)) = _
  rw [GT_cornerMark_eq' W q j]
  rfl

theorem GT_tcp_eq (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S) :
    GT_tcp W q =
      geoRecast (GT_cornerCount_eq W q).symm
        (geoCornerPolygon hP' (transportSupport hs S) (GT_carrierEquiv W q)) := by
  rw [GT_cornerPolygon_eq W q]
  funext k
  rw [geoRecast_apply, geoRecast_apply, geo_zmod_cast_cast' (GT_cornerCount_eq W q) k]

theorem GT_turn_tcp_eq_turn_cast (W : GT_Wall hP hP' hs T S) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (GT_tcp W q) k =
      turn (geoCornerPolygon hP' (transportSupport hs S) (GT_carrierEquiv W q))
        (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q).symm) k) := by
  rw [GT_cornerPolygon_eq W q, turn_geoRecast_cast]

/-- **Corner turns are carried across the wall**: vertex corners by `turn_eq`, smoothing corners by
`sign_eq`. -/
theorem GT_turn_tcp (W : GT_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    turn (GT_tcp W q) k = turn (geoCornerPolygon hP S q) k := by
  have hS := W.indep
  have hS' := W.indep'
  rw [GT_turn_tcp_eq_turn_cast W q k]
  have hmark := GT_cornerMark_eq W q k
  have hcorner := isTrueCorner_geoCornerMark hP S q k
  cases hc : geoCornerMark hP S q k with
  | inl i =>
    rw [hc, markTransport_vertex] at hmark
    rw [geoCornerPolygon_turn_vertex hn hP' hS' _ _ i hmark,
      geoCornerPolygon_turn_vertex hn hP hS q k i hc]
    exact W.turn_eq i
  | inr v =>
    rw [hc] at hcorner
    have hv : v.1 ∈ S := (isTrueCorner_visit S v).mp hcorner
    rw [hc, markTransport_visit] at hmark
    have hv' : (visitTransport hs v).1 ∈ transportSupport hs S := by
      rw [visitTransport_crossing, mem_transportSupport_iff]; exact hv
    rw [geoCornerPolygon_turn_visit hn hP' hS' _ _ (visitTransport hs v) hv' hmark,
      geoCornerPolygon_turn_visit hn hP hS q k v hv hc, ← visitTransport_visitTwin,
      visitTransport_edge, visitTransport_edge]
    apply W.sign_eq
    rw [← visit_crossing_val_eq_pair v]
    exact v.1.property

/-- The selector (`wt`) of a carrier is carried across the wall. -/
theorem GT_selector_eq (W : GT_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S) :
    geoCarrierSelector hP' (transportSupport hs S) (GT_carrierEquiv W q) = geoCarrierSelector hP S q := by
  unfold geoCarrierSelector
  rw [GT_cornerPolygon_eq W q, cornerSelector_geoRecast]
  exact cornerSelector_congr_turn (GT_turn_tcp W hn q)

/-- `wind(S)` is carried across the wall. -/
theorem GT_geoWind_eq (W : GT_Wall hP hP' hs T S) (hn : 3 ≤ n) :
    geoWind hP' (transportSupport hs S) = geoWind hP S := by
  unfold geoWind
  exact (Fintype.prod_equiv (GT_carrierEquiv W) _ _ fun q => (GT_selector_eq W hn q).symm).symm

/-! ### The rotation of a carrier is carried (CV:def:rot's ray formula, as `AV_rotationNumber_tcp`) -/

theorem GT_edge_tcp (W : GT_Wall hP hP' hs T S) (hn : 3 ≤ n) (q : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S q)) :
    ∃ c : ℝ, 0 < c ∧
      edge (GT_tcp W q) k = c • edge P' (geoOutSlot hP S (geoCornerMark hP S q k)).1 := by
  rw [GT_tcp_eq W q, AV_edge_geoRecast]
  obtain ⟨c, hc, h⟩ := geoCornerPolygon_edge_smul hn hP' W.indep' (GT_carrierEquiv W q)
    (Equiv.cast (congrArg ZMod (GT_cornerCount_eq W q).symm) k)
  refine ⟨c, hc, ?_⟩
  rw [h, GT_cornerMark_eq' W q, geo_zmod_cast_cast' (GT_cornerCount_eq W q) k, AV_outSlot_transport]

theorem GT_rotationNumber_tcp (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (W : GT_Wall hG.cg hG'.cg hs T S) (q : GeoComponent hG.cg S) :
    rotationNumber (GT_tcp W q) = rotationNumber (geoCornerPolygon hG.cg S q) := by
  obtain ⟨r, hr⟩ := W.ray
  have hL : CV.Regular (geoCornerPolygon hG.cg S q) :=
    (CV.regular_iff_sm _).mpr (geoCornerPolygon_regular hn hG W.indep q)
  have hL'' : CV.Regular (GT_tcp W q) := by
    rw [CV.regular_iff_sm, GT_tcp_eq W q, regular_geoRecast]
    exact geoCornerPolygon_regular hn hG' W.indep' _
  have hr' : ∀ h : ZMod n, det r (edge P' h) ≠ 0 := by
    intro h h0
    have := (hr h).2
    rw [h0, sign_zero] at this
    exact (hr h).1 (sign_eq_zero_iff.mp this.symm)
  have hadm : CV.Admissible (geoCornerPolygon hG.cg S q) r := by
    intro k
    obtain ⟨c, hc, h⟩ := geoCornerPolygon_edge_smul hn hG.cg W.indep q k
    rw [h, det_smul_right]
    exact mul_ne_zero hc.ne' (hr _).1
  have hadm'' : CV.Admissible (GT_tcp W q) r := by
    intro k
    obtain ⟨c, hc, h⟩ := GT_edge_tcp W hn q k
    rw [h, det_smul_right]
    exact mul_ne_zero hc.ne' (hr' _)
  rw [← CV.rotRay_eq_rotationNumber hL hadm, ← CV.rotRay_eq_rotationNumber hL'' hadm'']
  congr 1
  unfold CV.rotRay
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [CV.epsRot_eq_epsOfSigns, CV.epsRot_eq_epsOfSigns]
  have hturn : SignType.sign (det (edge (GT_tcp W q) (k - 1)) (edge (GT_tcp W q) k)) =
      SignType.sign (det (edge (geoCornerPolygon hG.cg S q) (k - 1))
        (edge (geoCornerPolygon hG.cg S q) k)) := by
    rw [← turn_det, ← turn_det]
    exact GT_turn_tcp W hn q k
  have hray : ∀ j : ZMod (geoCornerCount hG.cg S q),
      SignType.sign (det r (edge (GT_tcp W q) j)) =
        SignType.sign (det r (edge (geoCornerPolygon hG.cg S q) j)) := by
    intro j
    obtain ⟨c, hc, h⟩ := GT_edge_tcp W hn q j
    obtain ⟨c', hc', h'⟩ := geoCornerPolygon_edge_smul hn hG.cg W.indep q j
    rw [h, h', AV_sign_det_smul_right c hc, AV_sign_det_smul_right c' hc']
    exact (hr _).2
  have hray' : ∀ j : ZMod (geoCornerCount hG.cg S q),
      SignType.sign (det (edge (GT_tcp W q) j) r) =
        SignType.sign (det (edge (geoCornerPolygon hG.cg S q) j) r) := by
    intro j
    rw [AV_sign_det_swap (edge (GT_tcp W q) j) r,
      AV_sign_det_swap (edge (geoCornerPolygon hG.cg S q) j) r, hray j]
  rw [hturn, hray' (k - 1), hray k]

/-! ### The def:X1 objects on `CV.Generic` binders -/

theorem GT_carrierR_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : GT_Wall hG.crossingGeometry hG'.crossingGeometry hs T S)
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : transportSupport hs S ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) :
    CV.carrierR hn hG' hS' (GT_carrierEquiv W q) = CV.carrierR hn hG hS q := by
  unfold CV.carrierR CV.rotAbs
  congr 1
  apply Int.cast_injective (α := ℝ)
  rw [CV.rot_eq_rotationNumber, CV.rot_eq_rotationNumber, GT_cornerPolygon_eq W q,
    rotationNumber_geoRecast]
  exact GT_rotationNumber_tcp hn (CarrierGeometry.ofCV hG) (CarrierGeometry.ofCV hG') W q

theorem GT_weight_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : GT_Wall hG.crossingGeometry hG'.crossingGeometry hs T S) (q : GeoComponent hG.crossingGeometry S) :
    CV.weight hG'.crossingGeometry (transportSupport hs S) (GT_carrierEquiv W q) =
      CV.weight hG.crossingGeometry S q :=
  GT_selector_eq W hn q

theorem GT_wind_eq (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
    (W : GT_Wall hG.crossingGeometry hG'.crossingGeometry hs T S) :
    CV.wind hG'.crossingGeometry (transportSupport hs S) = CV.wind hG.crossingGeometry S :=
  GT_geoWind_eq W hn

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}
variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {T S : Finset (Crossing P)}

/-! ### Retained crossings when every unselected visit is good (the empty row) -/

/-- **The retained crossings of a carrier are carried to those of its copy** when every visit of an
unselected crossing is a good mark (no reversed partner is a corner). -/
theorem GT_geoCarrierCrossings_eq_of_good (W : GT_Wall hP hP' hs T S)
    (hgood : ∀ v : Visit P, v.1 ∉ S → GT_Good T S (Sum.inr v)) (q : GeoComponent hP S) :
    geoCarrierCrossings hP' (transportSupport hs S) (GT_carrierEquiv W q) =
      (geoCarrierCrossings hP S q).map (crossingTransport hs).toEmbedding := by
  classical
  ext x'
  obtain ⟨x, rfl⟩ := (crossingTransport hs).surjective x'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, mem_geoCarrierCrossings, mem_geoCarrierCrossings,
    mem_transportSupport_iff]
  constructor
  · rintro ⟨hxS, hall⟩
    refine ⟨hxS, fun v hv => ?_⟩
    have := hall (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, GT_owner_transport W (hgood v (hv ▸ hxS))] at this
    exact (GT_carrierEquiv W).injective this
  · rintro ⟨hxS, hall⟩
    refine ⟨hxS, fun w hw => ?_⟩
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective w
    rw [visitTransport_crossing] at hw
    have hvx : v.1 = x := (crossingTransport hs).injective hw
    rw [← markTransport_visit, GT_owner_transport W (hgood v (hvx ▸ hxS)), hall v hvx]

/-! ### Pieces under a relabelling of the retained crossings (the endpoint rows) -/

/-- **Relabelling data**: a bijection `φ` of the crossings agreeing with the edge-pair transport on
`S`, carrying the retained crossings of every carrier to those of its copy, carrying `U(S)` and the
residual interlacement. (For the endpoint rows `φ` is the transport composed with the exchange of
the two unselected triangle crossings; for a triangle-free support it is the transport itself.) -/
structure GT_Relabel (W : GT_Wall hP hP' hs T S) (φ : Crossing P ≃ Crossing P') : Prop where
  phi_S : ∀ c ∈ S, φ c = crossingTransport hs c
  retained : ∀ q : GeoComponent hP S,
    geoCarrierCrossings hP' (transportSupport hs S) (GT_carrierEquiv W q) =
      (geoCarrierCrossings hP S q).map φ.toEmbedding
  mem_U : ∀ y : Crossing P, φ y ∈ CV.U hP' (transportSupport hs S) ↔ y ∈ CV.U hP S
  adj : ∀ y ∈ CV.U hP S, ∀ z ∈ CV.U hP S,
    (GeometricInterlaces hP' (φ y) (φ z) ↔ GeometricInterlaces hP y z)

variable {W : GT_Wall hP hP' hs T S} {φ : Crossing P ≃ Crossing P'}

/-- The residual graphs are isomorphic along `φ`. -/
noncomputable def GT_residualIso (R : GT_Relabel W φ) :
    CV.residualGraph hP S ≃g CV.residualGraph hP' (transportSupport hs S) where
  toEquiv := Equiv.subtypeEquiv φ (fun y => (R.mem_U y).symm)
  map_rel_iff' := by
    intro a b
    show GeometricInterlaces hP' (φ a.1) (φ b.1) ↔ GeometricInterlaces hP a.1 b.1
    exact R.adj a.1 a.2 b.1 b.2

theorem GT_residualIso_apply_val (R : GT_Relabel W φ) (a : ↑(CV.U hP S)) :
    ((GT_residualIso R) a).1 = φ a.1 := rfl

/-- The pieces of `S` correspond to the pieces of the transported support along `φ`. -/
noncomputable def GT_pieceEquiv (R : GT_Relabel W φ) :
    CV.Piece hP S ≃ CV.Piece hP' (transportSupport hs S) :=
  (GT_residualIso R).connectedComponentEquiv

theorem GT_pieceEquiv_pieceOf (R : GT_Relabel W φ) (c : Crossing P) (hc : c ∈ CV.U hP S) :
    GT_pieceEquiv R (CV.pieceOf hP S c hc) =
      CV.pieceOf hP' (transportSupport hs S) (φ c) ((R.mem_U c).mpr hc) := by
  unfold GT_pieceEquiv CV.pieceOf
  rw [SimpleGraph.Iso.connectedComponentEquiv_apply, SimpleGraph.ConnectedComponent.map_mk]
  rfl

/-- The labels of a piece are carried along `φ`. -/
theorem GT_pieceLabels_eq (R : GT_Relabel W φ) (H : CV.Piece hP S) :
    CV.pieceLabels hP' (transportSupport hs S) (GT_pieceEquiv R H) =
      (CV.pieceLabels hP S H).map φ.toEmbedding := by
  ext c'
  obtain ⟨c, rfl⟩ := φ.surjective c'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, CV.mem_pieceLabels, CV.mem_pieceLabels]
  constructor
  · rintro ⟨hc', hH⟩
    have hc : c ∈ CV.U hP S := (R.mem_U c).mp hc'
    refine ⟨hc, (GT_pieceEquiv R).injective ?_⟩
    rw [GT_pieceEquiv_pieceOf]
    exact hH
  · rintro ⟨hc, hH⟩
    refine ⟨(R.mem_U c).mpr hc, ?_⟩
    rw [← GT_pieceEquiv_pieceOf R c hc, hH]

theorem GT_pieceWrithe_eq (R : GT_Relabel W φ) (H : CV.Piece hP S) :
    CV.pieceWrithe hP' (transportSupport hs S) (GT_pieceEquiv R H) = CV.pieceWrithe hP S H := by
  unfold CV.pieceWrithe
  rw [GT_pieceLabels_eq, Finset.card_map]

/-- A piece is assigned to a carrier iff its labels are among the carrier's retained crossings. -/
theorem GT_mem_piecesOn_iff_subset (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) (H : CV.Piece hP S) :
    H ∈ CV.piecesOn hP S q ↔ CV.pieceLabels hP S H ⊆ geoCarrierCrossings hP S q := by
  rw [CV.mem_piecesOn]
  constructor
  · intro h c hc
    rw [mem_geoCarrierCrossings]
    exact ⟨((CV.mem_U_iff hP S c).mp (CV.pieceLabels_subset hP S H hc)).1, h c hc⟩
  · intro h c hc v hv
    exact ((mem_geoCarrierCrossings hP S q c).mp (h hc)).2 v hv

/-- The pieces assigned to a carrier are carried onto the pieces assigned to its copy. -/
theorem GT_piecesOn_eq (R : GT_Relabel W φ) (q : GeoComponent hP S) :
    CV.piecesOn hP' (transportSupport hs S) (GT_carrierEquiv W q) =
      (CV.piecesOn hP S q).map (GT_pieceEquiv R).toEmbedding := by
  ext H'
  obtain ⟨H, rfl⟩ := (GT_pieceEquiv R).surjective H'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, GT_mem_piecesOn_iff_subset,
    GT_mem_piecesOn_iff_subset, GT_pieceLabels_eq, R.retained]
  exact Finset.map_subset_map

theorem GT_card_geoCarrierCrossings_eq (R : GT_Relabel W φ) (q : GeoComponent hP S) :
    (geoCarrierCrossings hP' (transportSupport hs S) (GT_carrierEquiv W q)).card =
      (geoCarrierCrossings hP S q).card := by
  rw [R.retained, Finset.card_map]

/-! ### `P_{S,L}` is the HOMFLY polynomial of the positive lift (CV:cor:groupedknot (B), both cases) -/

/-- **`P_{S,L} = P(D(W))`** on every carrier: cor:groupedknot (B) `grouped_polynomial` when the carrier
bears a piece, and its parenthetical `no_piece` (`P_{S,L} = 1 = P(○)`) otherwise. -/
theorem GT_groupedPoly_eq_homfly (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    CV.groupedPoly hn hG hS q = homfly (CV.carrierDiagram hn hG hS q) := by
  by_cases hne : (CV.piecesOn hG.crossingGeometry S q).Nonempty
  · exact ((CV.groupedknot hn hG hS q).grouped_polynomial hne).1.symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    obtain ⟨h1, -, -, h4⟩ := (CV.groupedknot hn hG hS q).no_piece hne
    rw [h1, h4]

/-! ### The generalized record isomorphism of two lifts (EXT_homfly_wall with an arbitrary visit
bijection) -/

/-- **Two carriers whose retained visits correspond through any bijection `ψ` compatible with the
twin pairing, carrying the cyclic key order and the divide signs, have positive lifts with the same
HOMFLY polynomial**: `ψ` lifted through the parent-visit maps is a record isomorphism (CV:def:record
(a)–(d), `recordIsoOfData`) and CV:ax:gausscode (`gausscode_polynomial`) applies. `EXT_homfly_wall` is
the case `ψ = visitTransport`. -/
theorem GT_homfly_wall_gen (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
    (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
    (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
    (ψ : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q} ≃
      {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q'})
    (htwin : ∀ (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q),
      (ψ ⟨visitTwin v, by rw [visitTwin_crossing]; exact hv⟩).1 = visitTwin (ψ ⟨v, hv⟩).1)
    (hcyc : ∀ u v w : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q},
      cycBetween (geometricVisitKey hG.cg u.1) (geometricVisitKey hG.cg v.1) (geometricVisitKey hG.cg w.1) →
      cycBetween (geometricVisitKey hG'.cg (ψ u).1) (geometricVisitKey hG'.cg (ψ v).1)
        (geometricVisitKey hG'.cg (ψ w).1))
    (hdet : ∀ v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q},
      (0 < det (edge P v.1.2.val) (edge P (visitTwin v.1).2.val) ↔
        0 < det (edge P' (ψ v).1.2.val) (edge P' (visitTwin (ψ v).1).2.val))) :
    homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q) := by
  let Φ : (geoPositiveLift hn hG hT q).Γ.Visit ≃ (geoPositiveLift hn hG' hT' q').Γ.Visit :=
    (CV.liftVisitEquiv hn hG hT q).trans (ψ.trans (CV.liftVisitEquiv hn hG' hT' q').symm)
  have hΦ : ∀ v, CV.liftVisit hn hG' hT' q' (Φ v) = (ψ (CV.liftVisitEquiv hn hG hT q v)).1 := by
    intro v
    show CV.liftVisit hn hG' hT' q'
      ((CV.liftVisitEquiv hn hG' hT' q').symm (ψ (CV.liftVisitEquiv hn hG hT q v))) = _
    rw [CV.liftVisit_symm]
  have hval : ∀ v, (CV.liftVisitEquiv hn hG hT q v).1 = CV.liftVisit hn hG hT q v := fun v => rfl
  have hdata : CV.IsRecordIsoData (geoPositiveLift hn hG hT q) (geoPositiveLift hn hG' hT' q') Φ :=
    { cyclic_order := fun v w u hb => by
        rw [CV.visitBetween_iff_key, hΦ, hΦ, hΦ]
        rw [CV.visitBetween_iff_key] at hb
        exact hcyc _ _ _ (by simpa only [hval] using hb)
      double_points :=
        (CV.carriesDoublePoints_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG' hT' q').record) Φ).2 fun v => by
          apply CV.liftVisit_injective hn hG' hT' q'
          change CV.liftVisit hn hG' hT' q' (Φ ((geoPositiveLift hn hG hT q).twin v)) =
            CV.liftVisit hn hG' hT' q' ((geoPositiveLift hn hG' hT' q').twin (Φ v))
          rw [hΦ, CV.liftVisit_twin, hΦ]
          have h := htwin (CV.liftVisit hn hG hT q v) (CV.liftVisit_mem hn hG hT q v)
          have hL : CV.liftVisitEquiv hn hG hT q ((geoPositiveLift hn hG hT q).twin v) =
              ⟨visitTwin (CV.liftVisit hn hG hT q v), by
                rw [visitTwin_crossing]; exact CV.liftVisit_mem hn hG hT q v⟩ :=
            Subtype.ext (CV.liftVisit_twin hn hG hT q v)
          rw [hL, h]
          rfl
      over_under :=
        (CV.carriesOverUnder_iff (ρ := (geoPositiveLift hn hG hT q).record)
          (ρ' := (geoPositiveLift hn hG' hT' q').record) Φ).2 fun v => by
          change (geoPositiveLift hn hG' hT' q').overBit (Φ v) = (geoPositiveLift hn hG hT q).overBit v
          rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hΦ]
          exact (hdet (CV.liftVisitEquiv hn hG hT q v)).symm
      signs := fun v => by
        change (geoPositiveLift hn hG' hT' q').sign (Φ v).1 = (geoPositiveLift hn hG hT q).sign v.1
        rw [geoPositiveLift_sign, geoPositiveLift_sign] }
  exact (CV.gausscode_polynomial _ _ (geoPositiveLift_componentCount hn hG hT q)
    (geoPositiveLift_componentCount hn hG' hT' q')
    (CV.recordIsoOfData (geoPositiveLift_componentCount hn hG hT q)
      (geoPositiveLift_componentCount hn hG' hT' q') Φ hdata)).symm

end GT

section GT

open SM.Carrier SM.Link

/-! ### Real-number cyclic-order lemmas for the relabelled record isomorphism -/

theorem GT_cyc_gt_gt {a x y : ℝ} (hx : a < x) (hy : a < y) : cycBetween a x y ↔ x < y := by
  unfold cycBetween
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> first | exact h | (exfalso; linarith)
  · intro h; exact Or.inl ⟨hx, h⟩

theorem GT_cyc_gt_lt {a x y : ℝ} (hx : a < x) (hy : y < a) : cycBetween a x y := by
  unfold cycBetween
  exact Or.inr (Or.inr ⟨hy, hx⟩)

theorem GT_cyc_lt_gt {a x y : ℝ} (hx : x < a) (hy : a < y) : ¬ cycBetween a x y := by
  unfold cycBetween
  rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨h, _⟩) <;> linarith

theorem GT_cyc_lt_lt {a x y : ℝ} (hx : x < a) (hy : y < a) : cycBetween a x y ↔ x < y := by
  unfold cycBetween
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, h⟩) <;> first | exact h | (exfalso; linarith)
  · intro h; exact Or.inr (Or.inl ⟨h, hy⟩)

/-- **Cyclic betweenness read from a base point `a`**: for `a` distinct from `u, v, s`, the cyclic order
of `(u, v, s)` is the cyclic closure of the linear order "first after `a`" (`cycBetween a · ·`). -/
theorem GT_cyc_base {a u v s : ℝ} (hau : a ≠ u) (hav : a ≠ v) (has : a ≠ s) :
    cycBetween u v s ↔
      (cycBetween a u v ∧ cycBetween a v s) ∨ (cycBetween a v s ∧ cycBetween a s u) ∨
      (cycBetween a s u ∧ cycBetween a u v) := by
  rcases lt_or_gt_of_ne hau with h1 | h1 <;> rcases lt_or_gt_of_ne hav with h2 | h2 <;>
    rcases lt_or_gt_of_ne has with h3 | h3
  · rw [GT_cyc_gt_gt h1 h2, GT_cyc_gt_gt h2 h3, GT_cyc_gt_gt h3 h1]; rfl
  · have hq : ¬ v < s := by intro h; linarith
    have hr : s < u := by linarith
    rw [iff_true_intro (GT_cyc_gt_lt h2 h3), iff_false_intro (GT_cyc_lt_gt h3 h1), GT_cyc_gt_gt h1 h2]
    unfold cycBetween; tauto
  · have hp : ¬ u < v := by intro h; linarith
    have hq : v < s := by linarith
    rw [iff_true_intro (GT_cyc_gt_lt h1 h2), iff_false_intro (GT_cyc_lt_gt h2 h3), GT_cyc_gt_gt h3 h1]
    unfold cycBetween; tauto
  · have hp : ¬ u < v := by intro h; linarith
    have hr : s < u := by linarith
    rw [iff_true_intro (GT_cyc_gt_lt h1 h2), iff_false_intro (GT_cyc_lt_gt h3 h1), GT_cyc_lt_lt h2 h3]
    unfold cycBetween; tauto
  · have hp : u < v := by linarith
    have hr : ¬ s < u := by intro h; linarith
    rw [iff_false_intro (GT_cyc_lt_gt h1 h2), iff_true_intro (GT_cyc_gt_lt h3 h1), GT_cyc_gt_gt h2 h3]
    unfold cycBetween; tauto
  · have hp : u < v := by linarith
    have hq : ¬ v < s := by intro h; linarith
    rw [iff_false_intro (GT_cyc_lt_gt h1 h2), iff_true_intro (GT_cyc_gt_lt h2 h3), GT_cyc_lt_lt h3 h1]
    unfold cycBetween; tauto
  · have hq : v < s := by linarith
    have hr : ¬ s < u := by intro h; linarith
    rw [iff_false_intro (GT_cyc_lt_gt h2 h3), iff_true_intro (GT_cyc_gt_lt h3 h1), GT_cyc_lt_lt h1 h2]
    unfold cycBetween; tauto
  · rw [GT_cyc_lt_lt h1 h2, GT_cyc_lt_lt h2 h3, GT_cyc_lt_lt h3 h1]; rfl

/-- Four points: if `u` and `w` lie in the arc from `a` to `b` and `w` comes before `u` from `a`,
then `u` lies in the arc from `w` to `b`. -/
theorem GT_cyc_arc_step {a u w b : ℝ} (h1 : cycBetween a u b) (h2 : cycBetween a w b)
    (h3 : cycBetween a w u) : cycBetween w u b := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h3 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | (exfalso; linarith)
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

theorem GT_cyc_rotate {a b c : ℝ} : cycBetween a b c ↔ cycBetween b c a := by
  unfold cycBetween; tauto

/-- Totality of "first after `a`" on points distinct from `a` and from each other. -/
theorem GT_cyc_total {a u v : ℝ} (hau : a ≠ u) (hav : a ≠ v) (huv : u ≠ v) :
    cycBetween a u v ∨ cycBetween a v u :=
  cycBetween_or_of_ne hau huv hav

/-- **Carriage of the cyclic order by a bijection that carries the base-point order on all pairs not
involving one element `p`, while `p` either keeps its position or moves from last to first (or from
first to last)**: the cyclic order of every triple is carried. -/
theorem GT_cyc_carried {ι : Type*} (k₁ k₂ : ι → ℝ) (a₁ a₂ : ℝ)
    (hk₁ : Function.Injective k₁) (hk₂ : Function.Injective k₂)
    (ha₁ : ∀ u, a₁ ≠ k₁ u) (ha₂ : ∀ u, a₂ ≠ k₂ u) (p : ι)
    (hrest : ∀ u v, u ≠ p → v ≠ p → (cycBetween a₁ (k₁ u) (k₁ v) ↔ cycBetween a₂ (k₂ u) (k₂ v)))
    (hp : (∀ u, u ≠ p → (cycBetween a₁ (k₁ u) (k₁ p) ↔ cycBetween a₂ (k₂ u) (k₂ p))) ∨
          (∀ u, u ≠ p → cycBetween a₁ (k₁ u) (k₁ p) ∧ cycBetween a₂ (k₂ p) (k₂ u)) ∨
          (∀ u, u ≠ p → cycBetween a₁ (k₁ p) (k₁ u) ∧ cycBetween a₂ (k₂ u) (k₂ p))) :
    ∀ u v s, cycBetween (k₁ u) (k₁ v) (k₁ s) ↔ cycBetween (k₂ u) (k₂ v) (k₂ s) := by
  -- the relations `r₁ u v = cycBetween a₁ (k₁ u) (k₁ v)`, `r₂` likewise, are asymmetric and total
  have asym₁ : ∀ u v, cycBetween a₁ (k₁ u) (k₁ v) → ¬ cycBetween a₁ (k₁ v) (k₁ u) := by
    intro u v h h'
    exact cycBetween_asymm' h (GT_cyc_rotate.mp h')
  have asym₂ : ∀ u v, cycBetween a₂ (k₂ u) (k₂ v) → ¬ cycBetween a₂ (k₂ v) (k₂ u) := by
    intro u v h h'
    exact cycBetween_asymm' h (GT_cyc_rotate.mp h')
  have irr₁ : ∀ u, ¬ cycBetween a₁ (k₁ u) (k₁ u) := fun u => not_cycBetween_self_mid _ _
  have irr₂ : ∀ u, ¬ cycBetween a₂ (k₂ u) (k₂ u) := fun u => not_cycBetween_self_mid _ _
  have tot₁ : ∀ u v, u ≠ v → cycBetween a₁ (k₁ u) (k₁ v) ∨ cycBetween a₁ (k₁ v) (k₁ u) :=
    fun u v huv => GT_cyc_total (ha₁ u) (ha₁ v) (hk₁.ne huv)
  have tot₂ : ∀ u v, u ≠ v → cycBetween a₂ (k₂ u) (k₂ v) ∨ cycBetween a₂ (k₂ v) (k₂ u) :=
    fun u v huv => GT_cyc_total (ha₂ u) (ha₂ v) (hk₂.ne huv)
  -- the core: triples with `p` in first position
  have core : ∀ v s, v ≠ p → s ≠ p → v ≠ s →
      (cycBetween (k₁ p) (k₁ v) (k₁ s) ↔ cycBetween (k₂ p) (k₂ v) (k₂ s)) := by
    intro v s hv hs hvs
    rw [GT_cyc_base (ha₁ p) (ha₁ v) (ha₁ s), GT_cyc_base (ha₂ p) (ha₂ v) (ha₂ s)]
    have hvs' := hrest v s hv hs
    rcases hp with h | h | h
    · -- `p` keeps its position: every atom is carried
      have hpv : cycBetween a₁ (k₁ p) (k₁ v) ↔ cycBetween a₂ (k₂ p) (k₂ v) := by
        rcases tot₁ v p hv with h1 | h1 <;> rcases tot₂ v p hv with h2 | h2
        · exact ⟨fun h' => absurd h1 (asym₁ _ _ h'), fun h' => absurd h2 (asym₂ _ _ h')⟩
        · exact absurd ((h v hv).mp h1) (asym₂ _ _ h2)
        · exact absurd ((h v hv).mpr h2) (asym₁ _ _ h1)
        · exact ⟨fun _ => h2, fun _ => h1⟩
      rw [hpv, hvs', h s hs]
    · -- `p` moves from last to first
      have h1 := h v hv
      have h2 := h s hs
      rw [iff_false_intro (asym₁ _ _ h1.1), iff_true_intro h2.1, iff_true_intro h1.2,
        iff_false_intro (asym₂ _ _ h2.2)]
      simp only [false_and, and_true, true_and, and_false, false_or, or_false]
      exact hvs'
    · -- `p` moves from first to last
      have h1 := h v hv
      have h2 := h s hs
      rw [iff_true_intro h1.1, iff_false_intro (asym₁ _ _ h2.1), iff_false_intro (asym₂ _ _ h1.2),
        iff_true_intro h2.2]
      simp only [false_and, and_true, true_and, and_false, false_or, or_false]
      exact hvs'
  have core' : ∀ u v s, u ≠ p → v ≠ p → s ≠ p →
      (cycBetween (k₁ u) (k₁ v) (k₁ s) ↔ cycBetween (k₂ u) (k₂ v) (k₂ s)) := by
    intro u v s hu hv hs
    rw [GT_cyc_base (ha₁ u) (ha₁ v) (ha₁ s), GT_cyc_base (ha₂ u) (ha₂ v) (ha₂ s),
      hrest u v hu hv, hrest v s hv hs, hrest s u hs hu]
  intro u v s
  by_cases hu : u = p
  · subst hu
    by_cases hv : v = u
    · subst hv
      exact iff_of_false (not_cycBetween_self_left _ _) (not_cycBetween_self_left _ _)
    by_cases hs : s = u
    · subst hs
      exact iff_of_false (not_cycBetween_self_right _ _) (not_cycBetween_self_right _ _)
    by_cases hvs : v = s
    · subst hvs
      exact iff_of_false (not_cycBetween_self_mid _ _) (not_cycBetween_self_mid _ _)
    exact core v s hv hs hvs
  by_cases hv : v = p
  · subst hv
    by_cases hs : s = v
    · subst hs
      exact iff_of_false (not_cycBetween_self_mid _ _) (not_cycBetween_self_mid _ _)
    by_cases hus : u = s
    · subst hus
      exact iff_of_false (not_cycBetween_self_right _ _) (not_cycBetween_self_right _ _)
    rw [GT_cyc_rotate, GT_cyc_rotate (a := k₂ u)]
    exact core s u hs hu (Ne.symm hus)
  by_cases hs : s = p
  · subst hs
    by_cases huv : u = v
    · subst huv
      exact iff_of_false (not_cycBetween_self_left _ _) (not_cycBetween_self_left _ _)
    rw [← GT_cyc_rotate, ← GT_cyc_rotate (a := k₂ s)]
    exact core u v hu hv huv
  exact core' u v s hu hv hs

end GT

section GT

open SM.Carrier SM.Link

variable {P : LabelledTuple n}

/-! ### One polygon: adjacent visits, arcs and the carriers of a selected crossing -/

omit [NeZero n] in
/-- The key of a visit as a mark is its visit key. -/
theorem GT_markKey_visit (hP : CrossingGeometry P) (v : Visit P) :
    geoMarkKey hP (Sum.inr v) = geometricVisitKey hP v := rfl

omit [NeZero n] in
theorem GT_traversalBetween_iff (hP : CrossingGeometry P) (v u w : Visit P) :
    traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP u)
        (geometricVisitPosition hP w) ↔
      cycBetween (geometricVisitKey hP v) (geometricVisitKey hP u) (geometricVisitKey hP w) :=
  Iff.rfl

omit [NeZero n] in
/-- Of the two arcs cut by two adjacent visits, the one containing a crossing visit is the nonempty
one; so the other arc carries no crossing visit. -/
theorem GT_adj_empty (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w)
    (z : Visit P) (hz : cycBetween (geometricVisitKey hP w) (geometricVisitKey hP z) (geometricVisitKey hP v)) :
    ∀ u : Visit P, ¬ cycBetween (geometricVisitKey hP v) (geometricVisitKey hP u) (geometricVisitKey hP w) := by
  rcases hadj.2 with h | h
  · exact h
  · exact absurd hz (h z)

omit [NeZero n] in
theorem GT_adj_empty' (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w)
    (z : Visit P) (hz : cycBetween (geometricVisitKey hP v) (geometricVisitKey hP z) (geometricVisitKey hP w)) :
    ∀ u : Visit P, ¬ cycBetween (geometricVisitKey hP w) (geometricVisitKey hP u) (geometricVisitKey hP v) := by
  rcases hadj.2 with h | h
  · exact absurd hz (h z)
  · exact h

/-- Adjacent visits are consecutive marks in one of the two orders. -/
theorem GT_succ_of_adjacent (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w)
    (hedge : v.2.val = w.2.val) :
    geoMarkSuccessor hP (Sum.inr v) = Sum.inr w ∨ geoMarkSuccessor hP (Sum.inr w) = Sum.inr v := by
  rcases hadj.2 with h | h
  · exact Or.inl (SEL_geoMarkSuccessor_eq_of_no_visit_between hP hadj.1 hedge h)
  · exact Or.inr (SEL_geoMarkSuccessor_eq_of_no_visit_between hP (Ne.symm hadj.1) hedge.symm h)

/-- Two adjacent unselected visits lie on the same carrier. -/
theorem GT_owner_eq_of_adjacent (hP : CrossingGeometry P) (S : Finset (Crossing P)) {v w : Visit P}
    (hadj : AdjacentVisits hP v w) (hedge : v.2.val = w.2.val) (hv : v.1 ∉ S) (hw : w.1 ∉ S) :
    geoOwner hP S (Sum.inr v) = geoOwner hP S (Sum.inr w) := by
  rcases GT_succ_of_adjacent hP hadj hedge with h | h
  · rw [← geoOwner_successor hP S (Sum.inr v), geoSmoothingSuccessor_visit_of_not_mem hP S v hv, h]
  · rw [← geoOwner_successor hP S (Sum.inr w), geoSmoothingSuccessor_visit_of_not_mem hP S w hw, h]

/-- Two visits on different edges have different keys, in the order of their edge indices. -/
theorem GT_key_lt_of_edge_val_lt (hP : CrossingGeometry P) {v w : Visit P}
    (h : v.2.val.val < w.2.val.val) : geometricVisitKey hP v < geometricVisitKey hP w := by
  unfold geometricVisitKey
  rw [traversalKey_lt_iff]
  exact Or.inl h

theorem GT_key_ne_of_ne (hP : CrossingGeometry P) {v w : Visit P} (h : v ≠ w) :
    geometricVisitKey hP v ≠ geometricVisitKey hP w :=
  fun h' => h (geometricVisitKey_injective hP h')

theorem GT_markKey_ne_of_ne (hP : CrossingGeometry P) {a b : Mark P} (h : a ≠ b) :
    geoMarkKey hP a ≠ geoMarkKey hP b :=
  fun h' => h (geoMarkKey_injective hP h')

/-- The key of a visit is positive (the vertex `0` alone has key `0`). -/
theorem GT_markKey_visit_pos (hP : CrossingGeometry P) (v : Visit P) :
    0 < geoMarkKey hP (Sum.inr v) := by
  rcases lt_or_eq_of_le (AV_key_nonneg hP (Sum.inr v)) with h | h
  · exact h
  · exfalso
    have : geoMarkKey hP (Sum.inl (0 : ZMod n)) = geoMarkKey hP (Sum.inr v) := by
      rw [AV_key_inl_zero, ← h]
    exact absurd (geoMarkKey_injective hP this) (by simp)

/-- **The arc step**: if a mark `m'` lies in the arc from `x₁` to `x₂` (or is `x₁`), its
traversal successor lies in that arc or is `x₂`. -/
theorem GT_arc_succ (hP : CrossingGeometry P) {x₁ x₂ : Visit P} (hx : x₁ ≠ x₂) (m' : Mark P)
    (hm : cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP m') (geoMarkKey hP (Sum.inr x₂)) ∨
      m' = Sum.inr x₁) :
    cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP (geoMarkSuccessor hP m'))
        (geoMarkKey hP (Sum.inr x₂)) ∨
      geoMarkSuccessor hP m' = Sum.inr x₂ := by
  have hx12 : geoMarkKey hP (Sum.inr x₁) ≠ geoMarkKey hP (Sum.inr x₂) :=
    GT_markKey_ne_of_ne hP (fun h => hx (Sum.inr.inj h))
  have hpos2 := GT_markKey_visit_pos hP x₂
  rcases AV_succ_spec hP m' with ⟨hlt, hbet⟩ | ⟨hwrap, hall⟩
  · -- no wrap: the successor is the next key, nothing strictly between
    by_cases heq : geoMarkKey hP (geoMarkSuccessor hP m') = geoMarkKey hP (Sum.inr x₂)
    · exact Or.inr (geoMarkKey_injective hP heq)
    left
    rcases lt_or_gt_of_ne heq with hlt2 | hgt2
    · -- successor below `x₂`
      rcases hm with hm | rfl
      · unfold cycBetween at hm ⊢
        rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by linarith, hlt2⟩
        · exact Or.inr (Or.inl ⟨hlt2, h2⟩)
        · exact absurd hlt2 (by linarith)
      · unfold cycBetween
        exact Or.inl ⟨hlt, hlt2⟩
    · -- successor above `x₂`: `x₂` is not strictly between, so `m'` is above `x₂` as well
      have hnb := hbet (Sum.inr x₂)
      have h2 : ¬ geoMarkKey hP m' < geoMarkKey hP (Sum.inr x₂) := fun h => hnb ⟨h, hgt2⟩
      rcases hm with hm | rfl
      · unfold cycBetween at hm ⊢
        rcases hm with ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩
        · exact absurd h3 h2
        · exact absurd h1 h2
        · exact Or.inr (Or.inr ⟨h1, by linarith⟩)
      · unfold cycBetween
        rcases lt_or_gt_of_ne hx12 with h | h
        · exact absurd h h2
        · exact Or.inr (Or.inr ⟨h, hlt⟩)
  · -- wrap: `m'` is the last mark, its successor the vertex `0`
    left
    rw [hwrap, AV_key_inl_zero]
    have hle2 := hall (Sum.inr x₂)
    have hle1 := hall (Sum.inr x₁)
    rcases hm with hm | rfl
    · unfold cycBetween at hm ⊢
      rcases hm with ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩
      · exact absurd h3 (not_lt.mpr hle2)
      · exact absurd h1 (not_lt.mpr hle2)
      · exact Or.inr (Or.inl ⟨hpos2, h1⟩)
    · unfold cycBetween
      rcases lt_or_gt_of_ne hx12 with h | h
      · exact absurd h (not_lt.mpr hle2)
      · exact Or.inr (Or.inl ⟨hpos2, h⟩)

/-- For an independent support and a selected visit `x₁` with twin `x₂`, the set
"the arc from `x₁` to `x₂`, together with `x₂`" is closed under the smoothing successor. -/
theorem GT_arc_closed (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x₁ : Visit P} (hx : x₁.1 ∈ S) (m : Mark P)
    (hm : cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP m)
        (geoMarkKey hP (Sum.inr (visitTwin x₁))) ∨ m = Sum.inr (visitTwin x₁)) :
    cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP (geoSmoothingSuccessor hP S m))
        (geoMarkKey hP (Sum.inr (visitTwin x₁))) ∨
      geoSmoothingSuccessor hP S m = Sum.inr (visitTwin x₁) := by
  have hne : x₁ ≠ visitTwin x₁ := (visitTwin_ne x₁).symm
  rw [geoSmoothingSuccessor_apply]
  apply GT_arc_succ hP hne
  rcases hm with hm | rfl
  · -- `m` is in the open arc: its selected image is in the arc as well
    cases m with
    | inl i => exact Or.inl (by simpa using hm)
    | inr v =>
      by_cases hv : v.1 ∈ S
      · rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S v hv]
        -- `v` is a visit of another selected crossing, which does not interlace `x₁.1`
        have hvx : v.1 ≠ x₁.1 := by
          intro h
          rcases visit_eq_or_twin x₁ v h with rfl | rfl
          · exact not_cycBetween_self_left _ _ hm
          · exact not_cycBetween_self_mid _ _ hm
        have hnI : ¬ GeometricInterlaces hP x₁.1 v.1 := hS _ hx _ hv (Ne.symm hvx)
        have hx2 : x₁.2 ≠ (visitTwin x₁).2 := by
          intro h
          exact visitTwin_ne x₁ (Sigma.ext (visitTwin_crossing x₁) (heq_of_eq h.symm))
        have hv2 : v.2 ≠ (visitTwin v).2 := by
          intro h
          exact visitTwin_ne v (Sigma.ext (visitTwin_crossing v) (heq_of_eq h.symm))
        rw [L.interlaces_iff_xor hP (Ne.symm hvx) (x₀ := x₁.2) (x₁ := (visitTwin x₁).2) hx2
          (y₀ := v.2) (y₁ := (visitTwin v).2) hv2] at hnI
        left
        show cycBetween (geometricVisitKey hP x₁) (geometricVisitKey hP (visitTwin v))
          (geometricVisitKey hP (visitTwin x₁))
        have hm' : L.Cyc (geometricVisitKey hP ⟨x₁.1, x₁.2⟩) (geometricVisitKey hP ⟨v.1, v.2⟩)
            (geometricVisitKey hP ⟨x₁.1, (visitTwin x₁).2⟩) := hm
        by_contra hcon
        exact hnI (Or.inl ⟨hm', hcon⟩)
      · rw [selectedMarkPerm_visit, selectedVisitTwin_of_not_mem S v hv]
        exact Or.inl hm
  · -- `m = x₂`: its selected image is `x₁`
    right
    rw [selectedMarkPerm_visit, selectedVisitTwin_of_mem S _ (by rw [visitTwin_crossing]; exact hx),
      visitTwin_involutive]

/-- **The carrier of `x₂` lies in the arc from `x₁` to `x₂`** (plus `x₂` itself): every mark on the
carrier of the selected visit `x₂ = visitTwin x₁` is `x₂` or lies strictly between `x₁` and `x₂`
going forward from `x₁`. -/
theorem GT_owner_arc (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x₁ : Visit P} (hx : x₁.1 ∈ S) (m : Mark P)
    (hm : geoOwner hP S m = geoOwner hP S (Sum.inr (visitTwin x₁))) :
    m = Sum.inr (visitTwin x₁) ∨
      cycBetween (geoMarkKey hP (Sum.inr x₁)) (geoMarkKey hP m) (geoMarkKey hP (Sum.inr (visitTwin x₁))) := by
  have hsc : (geoSmoothingSuccessor hP S).SameCycle (Sum.inr (visitTwin x₁)) m :=
    (geoOwner_eq_iff hP S _ _).mp hm.symm
  obtain ⟨k, -, hk⟩ := hsc.exists_pow_eq'
  rw [← hk]
  clear hk hm
  induction k with
  | zero =>
    rw [pow_zero, Equiv.Perm.one_apply]
    exact Or.inl rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases GT_arc_closed hP hS hx ((geoSmoothingSuccessor hP S ^ k) (Sum.inr (visitTwin x₁)))
      (ih.symm) with h | h
    · exact Or.inr h
    · exact Or.inl h

/-- The two visits of a selected crossing lie on different carriers. -/
theorem GT_owner_twin_ne (hP : CrossingGeometry P) {S : Finset (Crossing P)} (hS : GeoIndependent hP S)
    {x₁ : Visit P} (hx : x₁.1 ∈ S) :
    geoOwner hP S (Sum.inr x₁) ≠ geoOwner hP S (Sum.inr (visitTwin x₁)) := by
  intro h
  rcases GT_owner_arc hP hS hx (Sum.inr x₁) h with h' | h'
  · exact (visitTwin_ne x₁) (Sum.inr.inj h').symm
  · exact not_cycBetween_self_left _ _ h'

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

omit [NeZero n] in
/-- The support of an endpoint row: `Q ∪ {x}` (reducible, so that it is `Q ∪ {x}` to every consumer). -/
abbrev GT_S (Q : Finset (Crossing P)) (x : Crossing P) : Finset (Crossing P) := Q ∪ {x}

omit [NeZero n] in
theorem GT_mem_S_iff (Q : Finset (Crossing P)) (x y : Crossing P) :
    y ∈ GT_S Q x ↔ y ∈ Q ∨ y = x := by
  simp only [GT_S, Finset.mem_union, Finset.mem_singleton]

omit [NeZero n] in
/-- The crossing relabelling of an endpoint row: the edge-pair transport followed by the exchange of
`w'` and `m'` ("the map fixing every outside label and sending `c` to `b`",
R_GENERIC_COMMON_TRANSPORT_PROOF.md §2). -/
noncomputable def GT_φ (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (w m : Crossing P) :
    Crossing P ≃ Crossing P' :=
  (crossingTransport hs).trans (Equiv.swap (crossingTransport hs w) (crossingTransport hs m))

/-! ### The endpoint-row configuration (R_GENERIC_COMMON_TRANSPORT_PROOF.md §2–§3, all six branches)

Row `x` of the full-availability fibre, `x` a member of the selected pair `{x, w}`, `m` the centre of the
path side: side `P` is the two-edge side (edges `x–m`, `w–m`; `x`, `w` independent), side `P'` the
one-edge side. Edge labels: `ℓ₁` shared by `x, m`, `ℓ₂` shared by `x, w`, `ℓ₃` shared by `w, m`. The
structure collects exactly the facts the printed proof cites: the local graph, R-LOC-2 (2)–(4), the
adjacency of the three bundle pairs on both sides, lem:guardconst (turns, signs, a ray), the sharpened
masks ("`w, m` are twins relative to every outside survivor") and the sign identity (4)/(6). -/
structure GT_Endpoint (hP : CrossingGeometry P) (hP' : CrossingGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n) (Q : Finset (Crossing P))
    (x w m : Crossing P) (ℓ₁ ℓ₂ ℓ₃ : ZMod n) : Prop where
  hef : e ≠ f
  heg : e ≠ g
  hfg : f ≠ g
  xT : x.val ∈ triangleSupports e f g
  wT : w.val ∈ triangleSupports e f g
  mT : m.val ∈ triangleSupports e f g
  tri_cases : ∀ y : Crossing P, y.val ∈ triangleSupports e f g → y = x ∨ y = w ∨ y = m
  xw : x ≠ w
  xm : x ≠ m
  wm : w ≠ m
  x1 : ℓ₁ ∈ x.val
  m1 : ℓ₁ ∈ m.val
  x2 : ℓ₂ ∈ x.val
  w2 : ℓ₂ ∈ w.val
  w3 : ℓ₃ ∈ w.val
  m3 : ℓ₃ ∈ m.val
  l12 : ℓ₁ ≠ ℓ₂
  l13 : ℓ₁ ≠ ℓ₃
  l23 : ℓ₂ ≠ ℓ₃
  Q_ind : Q ∈ CV.Ind hP
  Q_out : ∀ q ∈ Q, q.val ∉ triangleSupports e f g
  Q_avail : ∀ q ∈ Q, ∀ y : Crossing P, y.val ∈ triangleSupports e f g → ¬ GeometricInterlaces hP q y
  hxw : ¬ GeometricInterlaces hP x w
  hxm : GeometricInterlaces hP x m
  hwm : GeometricInterlaces hP w m
  gauss : ExactTriangleVisitOrders P P' e f g hs
  toggle : ∀ y z : Crossing P, ¬ (y.val ∈ triangleSupports e f g ∧ z.val ∈ triangleSupports e f g) →
    (GeometricInterlaces hP' (crossingTransport hs y) (crossingTransport hs z) ↔
      GeometricInterlaces hP y z)
  compl : ∀ y z : Crossing P, y.val ∈ triangleSupports e f g → z.val ∈ triangleSupports e f g →
    y ≠ z →
    (GeometricInterlaces hP' (crossingTransport hs y) (crossingTransport hs z) ↔
      ¬ GeometricInterlaces hP y z)
  adj1 : AdjacentVisits hP (visitOn x ℓ₁ x1) (visitOn m ℓ₁ m1)
  adj2 : AdjacentVisits hP (visitOn x ℓ₂ x2) (visitOn w ℓ₂ w2)
  adj3 : AdjacentVisits hP (visitOn w ℓ₃ w3) (visitOn m ℓ₃ m3)
  adj1' : AdjacentVisits hP' (visitTransport hs (visitOn x ℓ₁ x1)) (visitTransport hs (visitOn m ℓ₁ m1))
  adj2' : AdjacentVisits hP' (visitTransport hs (visitOn x ℓ₂ x2)) (visitTransport hs (visitOn w ℓ₂ w2))
  adj3' : AdjacentVisits hP' (visitTransport hs (visitOn w ℓ₃ w3)) (visitTransport hs (visitOn m ℓ₃ m3))
  turn_eq : ∀ i, turn P' i = turn P i
  sign_eq : ∀ i j, IsCrossing P {i, j} → crossingSign P' i j = crossingSign P i j
  ray : ∃ r : Plane, ∀ h : ZMod n, det r (edge P h) ≠ 0 ∧
    SignType.sign (det r (edge P' h)) = SignType.sign (det r (edge P h))
  twins : ∀ y ∈ CV.U hP (GT_S Q x), y.val ∉ triangleSupports e f g →
    (GeometricInterlaces hP y w ↔ GeometricInterlaces hP y m)
  sgn : crossingSign P ℓ₂ ℓ₃ = crossingSign P ℓ₁ ℓ₃

/-- For a crossing of `U(S)`, all visits are on the carrier iff one of them is. -/
theorem GT_forall_visit_owner_iff {hP : CrossingGeometry P} {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hP) {c : Crossing P} (hc : c ∈ CV.U hP S) (v₀ : Visit P) (hv₀ : v₀.1 = c)
    (q : GeoComponent hP S) :
    (∀ v : Visit P, v.1 = c → geoOwner hP S (Sum.inr v) = q) ↔ geoOwner hP S (Sum.inr v₀) = q := by
  constructor
  · intro h; exact h v₀ hv₀
  · intro h v hv
    rw [CV.owner_eq_of_mem_U hP hS hc v v₀ hv hv₀]
    exact h

theorem GT_retained_of_not_mem_U {hP : CrossingGeometry P} {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) {c : Crossing P} (hc : c ∉ CV.U hP S) (q : GeoComponent hP S) :
    c ∉ geoCarrierCrossings hP S q := by
  intro h
  apply hc
  have := geoCarrierCrossings_subset_U hP hS q h
  rw [mem_geoSupportUnselected_iff] at this
  exact (CV.mem_U_iff hP S c).mpr this

namespace GT_Endpoint

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

local notation "𝑇" => triangleCrossings P e f g
local notation "𝑆" => GT_S Q x
local notation "𝑆'" => transportSupport hs (GT_S Q x)

variable (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
include D

/-! #### Names: the six visits -/

/-- `x₁`, the visit of `x` on the edge `ℓ₁` shared with `m`. -/
def x₁ : Visit P := visitOn x ℓ₁ D.x1
/-- `x₂`, the visit of `x` on the edge `ℓ₂` shared with `w`. -/
def x₂ : Visit P := visitOn x ℓ₂ D.x2
/-- `w₂`, the visit of `w` on `ℓ₂`. -/
def w₂ : Visit P := visitOn w ℓ₂ D.w2
/-- `w₃`, the visit of `w` on `ℓ₃`. -/
def w₃ : Visit P := visitOn w ℓ₃ D.w3
/-- `m₁`, the visit of `m` on `ℓ₁`. -/
def m₁ : Visit P := visitOn m ℓ₁ D.m1
/-- `m₃`, the visit of `m` on `ℓ₃`. -/
def m₃ : Visit P := visitOn m ℓ₃ D.m3

theorem x₁_fst : D.x₁.1 = x := rfl
theorem x₂_fst : D.x₂.1 = x := rfl
theorem w₂_fst : D.w₂.1 = w := rfl
theorem w₃_fst : D.w₃.1 = w := rfl
theorem m₁_fst : D.m₁.1 = m := rfl
theorem m₃_fst : D.m₃.1 = m := rfl
theorem x₁_edge : D.x₁.2.val = ℓ₁ := rfl
theorem x₂_edge : D.x₂.2.val = ℓ₂ := rfl
theorem w₂_edge : D.w₂.2.val = ℓ₂ := rfl
theorem w₃_edge : D.w₃.2.val = ℓ₃ := rfl
theorem m₁_edge : D.m₁.2.val = ℓ₁ := rfl
theorem m₃_edge : D.m₃.2.val = ℓ₃ := rfl

theorem twin_x₁ : visitTwin D.x₁ = D.x₂ := SEL_visitTwin_visitOn D.x2 D.x1 D.l12.symm
theorem twin_x₂ : visitTwin D.x₂ = D.x₁ := SEL_visitTwin_visitOn D.x1 D.x2 D.l12
theorem twin_w₂ : visitTwin D.w₂ = D.w₃ := SEL_visitTwin_visitOn D.w3 D.w2 D.l23.symm
theorem twin_w₃ : visitTwin D.w₃ = D.w₂ := SEL_visitTwin_visitOn D.w2 D.w3 D.l23
theorem twin_m₁ : visitTwin D.m₁ = D.m₃ := SEL_visitTwin_visitOn D.m3 D.m1 D.l13.symm
theorem twin_m₃ : visitTwin D.m₃ = D.m₁ := SEL_visitTwin_visitOn D.m1 D.m3 D.l13

/-- The support of `x`: exactly `{ℓ₁, ℓ₂}`. -/
theorem xval : x.val = {ℓ₁, ℓ₂} := by
  have h2 := crossing_card_two x
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact D.x1
    · exact D.x2
  · rw [h2, Finset.card_pair D.l12]

theorem wval : w.val = {ℓ₂, ℓ₃} := by
  have h2 := crossing_card_two w
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact D.w2
    · exact D.w3
  · rw [h2, Finset.card_pair D.l23]

theorem mval : m.val = {ℓ₁, ℓ₃} := by
  have h2 := crossing_card_two m
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact D.m1
    · exact D.m3
  · rw [h2, Finset.card_pair D.l13]

theorem l3_not_mem_x : ℓ₃ ∉ x.val := by
  rw [D.xval]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.l13.symm, D.l23.symm⟩

theorem l1_not_mem_w : ℓ₁ ∉ w.val := by
  rw [D.wval]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.l12, D.l13⟩

theorem l2_not_mem_m : ℓ₂ ∉ m.val := by
  rw [D.mval]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.l12.symm, D.l23⟩

/-! #### The triangle and the support -/

theorem x_mem_T : x ∈ 𝑇 := (F1.mem_triangleCrossings e f g x).mpr D.xT
theorem w_mem_T : w ∈ 𝑇 := (F1.mem_triangleCrossings e f g w).mpr D.wT
theorem m_mem_T : m ∈ 𝑇 := (F1.mem_triangleCrossings e f g m).mpr D.mT

omit [NeZero n] D in
theorem x_mem_S : x ∈ 𝑆 := (GT_mem_S_iff Q x x).mpr (Or.inr rfl)

theorem not_mem_Q_of_mem_T {y : Crossing P} (hy : y.val ∈ triangleSupports e f g) : y ∉ Q :=
  fun h => D.Q_out y h hy

theorem w_not_mem_S : w ∉ 𝑆 := by
  rw [GT_mem_S_iff]
  rintro (h | h)
  · exact D.not_mem_Q_of_mem_T D.wT h
  · exact D.xw h.symm

theorem m_not_mem_S : m ∉ 𝑆 := by
  rw [GT_mem_S_iff]
  rintro (h | h)
  · exact D.not_mem_Q_of_mem_T D.mT h
  · exact D.xm h.symm

/-- The only triangle crossing in `S` is `x`. -/
theorem eq_x_of_mem_S_T {y : Crossing P} (hyS : y ∈ 𝑆) (hyT : y.val ∈ triangleSupports e f g) :
    y = x := by
  rcases (GT_mem_S_iff Q x y).mp hyS with h | h
  · exact absurd h (D.not_mem_Q_of_mem_T hyT)
  · exact h

theorem S_ind : 𝑆 ∈ CV.Ind hP := by
  rw [CV.mem_Ind_iff]
  intro a ha b hb hab
  rcases (GT_mem_S_iff Q x a).mp ha with ha | hax <;>
    rcases (GT_mem_S_iff Q x b).mp hb with hb | hbx
  · exact ((CV.mem_Ind_iff hP Q).mp D.Q_ind) a ha b hb hab
  · subst b; exact D.Q_avail a ha _ D.xT
  · subst a; exact fun h => D.Q_avail b hb _ D.xT (geometricInterlaces_symm hP h)
  · subst a; exact absurd hbx.symm hab

theorem S_geoIndep : GeoIndependent hP 𝑆 := CV.geoIndependent_of_mem_Ind hP D.S_ind

/-! #### `U(S)` on both sides -/

theorem w_mem_U : w ∈ CV.U hP 𝑆 := by
  rw [CV.mem_U_iff]
  refine ⟨D.w_not_mem_S, fun s hs => ?_⟩
  rcases (GT_mem_S_iff Q x s).mp hs with h | hsx
  · exact fun h' => D.Q_avail s h w D.wT (geometricInterlaces_symm hP h')
  · subst s; exact fun h' => D.hxw (geometricInterlaces_symm hP h')

theorem m_not_mem_U : m ∉ CV.U hP 𝑆 := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  exact h x x_mem_S (geometricInterlaces_symm hP D.hxm)

omit D in
theorem x_not_mem_U : x ∉ CV.U hP 𝑆 := fun h => ((CV.mem_U_iff hP _ x).mp h).1 x_mem_S

/-- A crossing of `U(S)` is `w` or an outside crossing. -/
theorem mem_U_cases {y : Crossing P} (hy : y ∈ CV.U hP 𝑆) :
    y = w ∨ y.val ∉ triangleSupports e f g := by
  by_cases hyT : y.val ∈ triangleSupports e f g
  · rcases D.tri_cases y hyT with rfl | rfl | rfl
    · exact absurd hy x_not_mem_U
    · exact Or.inl rfl
    · exact absurd hy D.m_not_mem_U
  · exact Or.inr hyT

omit [NeZero n] D in
theorem mem_S'_iff (y : Crossing P) : crossingTransport hs y ∈ 𝑆' ↔ y ∈ 𝑆 :=
  mem_transportSupport_iff hs _ y

theorem S'_ind : GeoIndependent hP' 𝑆' := by
  intro a' ha' b' hb' hab
  obtain ⟨a, rfl⟩ := (crossingTransport hs).surjective a'
  obtain ⟨b, rfl⟩ := (crossingTransport hs).surjective b'
  rw [mem_S'_iff] at ha' hb'
  have hab' : a ≠ b := fun h => hab (h ▸ rfl)
  have hnT : ¬ (a.val ∈ triangleSupports e f g ∧ b.val ∈ triangleSupports e f g) := by
    rintro ⟨haT, hbT⟩
    exact hab' ((D.eq_x_of_mem_S_T ha' haT).trans (D.eq_x_of_mem_S_T hb' hbT).symm)
  rw [D.toggle a b hnT]
  exact D.S_geoIndep a ha' b hb' hab'

theorem S'_mem_Ind : 𝑆' ∈ CV.Ind hP' := (CV.mem_Ind_iff_geoIndependent _ _).mpr D.S'_ind

theorem m'_mem_U : crossingTransport hs m ∈ CV.U hP' 𝑆' := by
  rw [CV.mem_U_iff]
  refine ⟨fun h => D.m_not_mem_S ((mem_S'_iff m).mp h), fun s' hs' => ?_⟩
  obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
  rw [mem_S'_iff] at hs'
  rcases (GT_mem_S_iff Q x s).mp hs' with h | hsx
  · rw [D.toggle m s (fun h' => D.Q_out s h h'.2)]
    exact fun h' => D.Q_avail s h m D.mT (geometricInterlaces_symm hP h')
  · subst s
    rw [D.compl m x D.mT D.xT D.xm.symm]
    exact fun h' => h' (geometricInterlaces_symm hP D.hxm)

theorem w'_not_mem_U : crossingTransport hs w ∉ CV.U hP' 𝑆' := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  apply h (crossingTransport hs x) ((mem_S'_iff x).mpr x_mem_S)
  rw [D.compl w x D.wT D.xT D.xw.symm]
  exact fun h' => D.hxw (geometricInterlaces_symm hP h')

omit D in
theorem x'_not_mem_U : crossingTransport hs x ∉ CV.U hP' 𝑆' :=
  fun h => ((CV.mem_U_iff hP' _ _).mp h).1 ((mem_S'_iff x).mpr x_mem_S)

/-- Outside crossings: membership in `U` is carried. -/
theorem mem_U_iff_of_outside {y : Crossing P} (hy : y.val ∉ triangleSupports e f g) :
    crossingTransport hs y ∈ CV.U hP' 𝑆' ↔ y ∈ CV.U hP 𝑆 := by
  rw [CV.mem_U_iff, CV.mem_U_iff, mem_S'_iff]
  apply and_congr Iff.rfl
  constructor
  · intro h s hsS
    rw [← D.toggle y s (fun h' => hy h'.1)]
    exact h _ ((mem_S'_iff s).mpr hsS)
  · intro h s' hs'
    obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
    rw [D.toggle y s (fun h' => hy h'.1)]
    exact h s ((mem_S'_iff s).mp hs')

/-! #### The wall data and the good marks -/

theorem wall : GT_Wall hP hP' hs 𝑇 𝑆 where
  indep := D.S_geoIndep
  indep' := D.S'_ind
  key_lt v w hvw := AV_key_lt_of_gauss hP hP' hs D.hef D.heg D.hfg D.gauss v w hvw
  corners_apart v w hrev := by
    rintro ⟨hvS, hwS⟩
    have h1 := D.eq_x_of_mem_S_T hvS ((F1.mem_triangleCrossings e f g v.1).mp hrev.1)
    have h2 := D.eq_x_of_mem_S_T hwS ((F1.mem_triangleCrossings e f g w.1).mp hrev.2.1)
    exact hrev.2.2.1 (h1.trans h2.symm)
  turn_eq := D.turn_eq
  sign_eq := D.sign_eq
  ray := D.ray

/-- Every visit not on the edges `ℓ₁`, `ℓ₂` shared with `x` is good; in particular the visits of
outside crossings and the `ℓ₃`-visits `w₃`, `m₃`. -/
theorem good_of_edge {v : Visit P} (hv : v.2.val ∉ x.val) : GT_Good 𝑇 𝑆 (Sum.inr v) := by
  intro v' hv' u hrev hu
  obtain rfl := Sum.inr.inj hv'
  have huS : u.1 ∈ 𝑆 := hu
  have hux : u.1 = x := D.eq_x_of_mem_S_T huS ((F1.mem_triangleCrossings e f g u.1).mp hrev.2.1)
  apply hv
  rw [hrev.2.2.2, ← hux]
  exact u.2.property

omit D in
theorem good_of_outside {v : Visit P} (hv : v.1.val ∉ triangleSupports e f g) :
    GT_Good 𝑇 𝑆 (Sum.inr v) :=
  GT_good_of_not_mem _ _ (fun h => hv ((F1.mem_triangleCrossings e f g v.1).mp h))

theorem good_w₃ : GT_Good 𝑇 𝑆 (Sum.inr D.w₃) := D.good_of_edge (v := D.w₃) D.l3_not_mem_x
theorem good_m₃ : GT_Good 𝑇 𝑆 (Sum.inr D.m₃) := D.good_of_edge (v := D.m₃) D.l3_not_mem_x

theorem x₁_corner : IsTrueCorner 𝑆 (Sum.inr D.x₁) := x_mem_S
theorem x₂_corner : IsTrueCorner 𝑆 (Sum.inr D.x₂) := x_mem_S

/-! #### The carriers of the local visits -/

/-- Both visits of `w` lie on one carrier of `S` (`w ∈ U(S)`). -/
theorem owner_w₂_eq_w₃ : geoOwner hP 𝑆 (Sum.inr D.w₂) = geoOwner hP 𝑆 (Sum.inr D.w₃) :=
  CV.owner_eq_of_mem_U hP D.S_ind D.w_mem_U D.w₂ D.w₃ rfl rfl

/-- Both visits of `m'` lie on one carrier of `S'` (`m' ∈ U(S')`). -/
theorem owner'_m₁_eq_m₃ :
    geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₁)) =
      geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₃)) :=
  CV.owner_eq_of_mem_U hP' D.S'_mem_Ind D.m'_mem_U _ _ rfl rfl

/-- On the one-edge side the `ℓ₃`-visits of `w'` and `m'` are adjacent unselected visits, hence on one
carrier. -/
theorem owner'_w₃_eq_m₃ :
    geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.w₃)) =
      geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₃)) :=
  GT_owner_eq_of_adjacent hP' _ D.adj3' rfl
    (fun h => D.w_not_mem_S ((mem_S'_iff w).mp h))
    (fun h => D.m_not_mem_S ((mem_S'_iff m).mp h))

theorem owner_w₃_eq_m₃ :
    geoOwner hP 𝑆 (Sum.inr D.w₃) = geoOwner hP 𝑆 (Sum.inr D.m₃) :=
  GT_owner_eq_of_adjacent hP _ D.adj3 rfl D.w_not_mem_S D.m_not_mem_S

/-- The carrier bijection of the endpoint row. -/
noncomputable abbrev β : GeoComponent hP 𝑆 ≃ GeoComponent hP' 𝑆' := GT_carrierEquiv D.wall

/-- **The visit of `m'` on `ℓ₃` lies on the copy of the carrier of `w₃`**: `m₃'` and `w₃'` are
adjacent unselected visits on the one-edge side, and `w₃` is a good mark. -/
theorem owner'_m₃ :
    geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₃)) = D.β (geoOwner hP 𝑆 (Sum.inr D.w₃)) := by
  rw [← D.owner'_w₃_eq_m₃, ← markTransport_visit]
  exact GT_owner_transport D.wall D.good_w₃

theorem owner'_m₁ :
    geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.m₁)) = D.β (geoOwner hP 𝑆 (Sum.inr D.w₃)) := by
  rw [D.owner'_m₁_eq_m₃, D.owner'_m₃]

/-! #### The relabelling `φ = swap(w', m') ∘ τ` -/

omit [NeZero n] D in
theorem φ_apply (y : Crossing P) :
    GT_φ hs w m y = Equiv.swap (crossingTransport hs w) (crossingTransport hs m) (crossingTransport hs y) := rfl

omit [NeZero n] D in
theorem φ_w : GT_φ hs w m w = crossingTransport hs m := by
  rw [φ_apply]; exact Equiv.swap_apply_left _ _

omit [NeZero n] D in
theorem φ_m : GT_φ hs w m m = crossingTransport hs w := by
  rw [φ_apply]; exact Equiv.swap_apply_right _ _

omit [NeZero n] D in
theorem φ_of_ne {y : Crossing P} (hyw : y ≠ w) (hym : y ≠ m) : GT_φ hs w m y = crossingTransport hs y := by
  rw [φ_apply]
  exact Equiv.swap_apply_of_ne_of_ne ((crossingTransport hs).injective.ne hyw)
    ((crossingTransport hs).injective.ne hym)

theorem φ_of_mem_S {y : Crossing P} (hy : y ∈ 𝑆) : GT_φ hs w m y = crossingTransport hs y :=
  φ_of_ne (fun h => D.w_not_mem_S (h ▸ hy)) (fun h => D.m_not_mem_S (h ▸ hy))

theorem φ_of_outside {y : Crossing P} (hy : y.val ∉ triangleSupports e f g) :
    GT_φ hs w m y = crossingTransport hs y :=
  φ_of_ne (fun h => hy (h ▸ D.wT)) (fun h => hy (h ▸ D.mT))

/-- A crossing not among `x, w, m` is outside. -/
theorem outside_of_ne {y : Crossing P} (hyx : y ≠ x) (hyw : y ≠ w) (hym : y ≠ m) :
    y.val ∉ triangleSupports e f g := by
  intro h
  rcases D.tri_cases y h with h | h | h
  · exact hyx h
  · exact hyw h
  · exact hym h

/-- **The retained crossings of a carrier are carried to those of its copy along `φ`**: outside
crossings by the ownership transport of their (good) visits, `w ↦ m'` through the `ℓ₃`-pair. -/
theorem retained (q : GeoComponent hP 𝑆) :
    geoCarrierCrossings hP' 𝑆' (D.β q) = (geoCarrierCrossings hP 𝑆 q).map (GT_φ hs w m).toEmbedding := by
  classical
  ext y'
  obtain ⟨y, rfl⟩ := (GT_φ hs w m).surjective y'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hyw : y = w
  · subst hyw
    rw [φ_w, mem_geoCarrierCrossings, mem_geoCarrierCrossings,
      GT_forall_visit_owner_iff D.S'_mem_Ind D.m'_mem_U (visitTransport hs D.m₃) rfl,
      GT_forall_visit_owner_iff D.S_ind D.w_mem_U D.w₃ rfl, D.owner'_m₃]
    refine and_congr ?_ (GT_carrierEquiv D.wall).injective.eq_iff
    exact iff_of_true (fun h => D.m_not_mem_S ((mem_S'_iff m).mp h)) D.w_not_mem_S
  by_cases hym : y = m
  · subst hym
    rw [φ_m]
    exact iff_of_false (GT_retained_of_not_mem_U D.S'_ind D.w'_not_mem_U _)
      (GT_retained_of_not_mem_U D.S_geoIndep D.m_not_mem_U _)
  by_cases hyx : y = x
  · subst hyx
    rw [φ_of_ne hyw hym]
    exact iff_of_false (GT_retained_of_not_mem_U D.S'_ind x'_not_mem_U _)
      (GT_retained_of_not_mem_U D.S_geoIndep x_not_mem_U _)
  have hyT : y.val ∉ triangleSupports e f g := D.outside_of_ne hyx hyw hym
  rw [φ_of_ne hyw hym, mem_geoCarrierCrossings, mem_geoCarrierCrossings, mem_S'_iff]
  apply and_congr Iff.rfl
  constructor
  · intro hall v hv
    have := hall (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, GT_owner_transport D.wall (good_of_outside (hv ▸ hyT))] at this
    exact (GT_carrierEquiv D.wall).injective this
  · intro hall v' hv'
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective v'
    rw [visitTransport_crossing] at hv'
    have hv : v.1 = y := (crossingTransport hs).injective hv'
    rw [← markTransport_visit, GT_owner_transport D.wall (good_of_outside (hv ▸ hyT)), hall v hv]

/-- `U(S)` is carried along `φ`. -/
theorem mem_U_iff (y : Crossing P) : GT_φ hs w m y ∈ CV.U hP' 𝑆' ↔ y ∈ CV.U hP 𝑆 := by
  by_cases hyw : y = w
  · subst hyw; rw [φ_w]; exact iff_of_true D.m'_mem_U D.w_mem_U
  by_cases hym : y = m
  · subst hym; rw [φ_m]; exact iff_of_false D.w'_not_mem_U D.m_not_mem_U
  by_cases hyx : y = x
  · subst hyx; rw [φ_of_ne hyw hym]; exact iff_of_false x'_not_mem_U x_not_mem_U
  rw [φ_of_ne hyw hym]
  exact D.mem_U_iff_of_outside (D.outside_of_ne hyx hyw hym)

/-- Residual interlacement is carried along `φ` ("`b` and `c` are twins relative to every outside
vertex that survives `Q ∪ {a}`"). -/
theorem adj (y : Crossing P) (hy : y ∈ CV.U hP 𝑆) (z : Crossing P) (hz : z ∈ CV.U hP 𝑆) :
    GeometricInterlaces hP' (GT_φ hs w m y) (GT_φ hs w m z) ↔ GeometricInterlaces hP y z := by
  rcases D.mem_U_cases hy with rfl | hyT <;> rcases D.mem_U_cases hz with rfl | hzT
  · rw [φ_w]
    exact iff_of_false (geometricInterlaces_irrefl hP' _) (geometricInterlaces_irrefl hP _)
  · rw [φ_w, D.φ_of_outside hzT, CV.geometricInterlaces_comm hP' _ _, CV.geometricInterlaces_comm hP _ _,
      D.toggle z m (fun h => hzT h.1)]
    exact (D.twins z hz hzT).symm
  · rw [φ_w, D.φ_of_outside hyT, D.toggle y m (fun h => hyT h.1)]
    exact (D.twins y hy hyT).symm
  · rw [D.φ_of_outside hyT, D.φ_of_outside hzT]
    exact D.toggle y z (fun h => hyT h.1)

/-- The relabelling data of the endpoint row. -/
theorem relabel : GT_Relabel D.wall (GT_φ hs w m) where
  phi_S _ hc := D.φ_of_mem_S hc
  retained := D.retained
  mem_U := D.mem_U_iff
  adj := D.adj

end GT_Endpoint

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

/-! ### Keys of visits: different edges compare by edge index; betweenness on one edge -/

theorem GT_key_lt_iff_of_edge_ne (hP : CrossingGeometry P) {v w : Visit P} (h : v.2.val ≠ w.2.val) :
    geometricVisitKey hP v < geometricVisitKey hP w ↔ v.2.val.val < w.2.val.val := by
  unfold geometricVisitKey
  rw [traversalKey_lt_iff]
  constructor
  · rintro (h1 | ⟨h1, -⟩)
    · exact h1
    · exact absurd h1 h
  · exact fun h1 => Or.inl h1

/-- A visit whose key lies strictly between the keys of two visits of one edge is on that edge. -/
theorem GT_edge_of_between (hP : CrossingGeometry P) {v u w : Visit P} (hvw : v.2.val = w.2.val)
    (h1 : geometricVisitKey hP v < geometricVisitKey hP u) (h2 : geometricVisitKey hP u < geometricVisitKey hP w) :
    u.2.val = v.2.val := by
  by_contra hne
  have h1' := (GT_key_lt_iff_of_edge_ne hP (Ne.symm hne)).mp h1
  have h2' := (GT_key_lt_iff_of_edge_ne hP (fun h => hne (h.trans hvw.symm))).mp h2
  rw [← hvw] at h2'
  omega

/-- **Adjacent same-edge visits are indistinguishable from any other visit's position**: if `v, w` are
adjacent visits on one edge and some crossing visit `z` lies on another edge, then no visit `y ≠ v, w`
lies strictly between them, so `key y < key v ↔ key y < key w`. -/
theorem GT_adj_lt_iff (hP : CrossingGeometry P) {v w : Visit P} (hadj : AdjacentVisits hP v w)
    (hedge : v.2.val = w.2.val) (z : Visit P) (hz : z.2.val ≠ v.2.val) (y : Visit P) (hyv : y ≠ v)
    (hyw : y ≠ w) :
    (geometricVisitKey hP y < geometricVisitKey hP v ↔ geometricVisitKey hP y < geometricVisitKey hP w) ∧
    (geometricVisitKey hP v < geometricVisitKey hP y ↔ geometricVisitKey hP w < geometricVisitKey hP y) := by
  have hkyv := GT_key_ne_of_ne hP hyv
  have hkyw := GT_key_ne_of_ne hP hyw
  have hkvw := GT_key_ne_of_ne hP hadj.1
  -- the arc between `v` and `w` (in the linear order) contains no visit: the other arc contains `z`
  have hzout : ∀ a b : Visit P, a.2.val = b.2.val → geometricVisitKey hP a < geometricVisitKey hP b →
      z.2.val ≠ a.2.val → cycBetween (geometricVisitKey hP b) (geometricVisitKey hP z) (geometricVisitKey hP a) := by
    intro a b hab hlt hza
    have hza' : z ≠ a := fun h => hza (congrArg (fun v : Visit P => v.2.val) h)
    have hzb' : z ≠ b := fun h => hza ((congrArg (fun v : Visit P => v.2.val) h).trans hab.symm)
    rcases lt_or_gt_of_ne (GT_key_ne_of_ne hP hza') with h | h
    · -- `z` below `a`
      exact Or.inr (Or.inl ⟨h, hlt⟩)
    · -- `z` above `a`: not between `a` and `b` (else on their edge), so above `b`
      have hzb : geometricVisitKey hP b < geometricVisitKey hP z := by
        rcases lt_or_gt_of_ne (GT_key_ne_of_ne hP hzb') with h' | h'
        · exact absurd (GT_edge_of_between hP hab h h') hza
        · exact h'
      exact Or.inr (Or.inr ⟨hlt, hzb⟩)
  have hnot : ∀ a b : Visit P, AdjacentVisits hP a b → a.2.val = b.2.val →
      geometricVisitKey hP a < geometricVisitKey hP b → z.2.val ≠ a.2.val →
      ¬ (geometricVisitKey hP a < geometricVisitKey hP y ∧ geometricVisitKey hP y < geometricVisitKey hP b) := by
    intro a b hab hedge' hlt hza ⟨h1, h2⟩
    exact GT_adj_empty hP hab z (hzout a b hedge' hlt hza) y (Or.inl ⟨h1, h2⟩)
  rcases lt_or_gt_of_ne hkvw with hvw | hwv
  · have hn := hnot v w hadj hedge hvw hz
    constructor
    · constructor
      · intro h; linarith
      · intro h
        rcases lt_or_gt_of_ne hkyv with h' | h'
        · exact h'
        · exact absurd ⟨h', h⟩ hn
    · constructor
      · intro h
        rcases lt_or_gt_of_ne hkyw with h' | h'
        · exact absurd ⟨h, h'⟩ hn
        · exact h'
      · intro h; linarith
  · have hn := hnot w v ⟨Ne.symm hadj.1, hadj.2.symm⟩ hedge.symm hwv (hedge ▸ hz)
    constructor
    · constructor
      · intro h
        rcases lt_or_gt_of_ne hkyw with h' | h'
        · exact h'
        · exact absurd ⟨h', h⟩ hn
      · intro h; linarith
    · constructor
      · intro h; linarith
      · intro h
        rcases lt_or_gt_of_ne hkyv with h' | h'
        · exact absurd ⟨h, h'⟩ hn
        · exact h'

omit [NeZero n] in
theorem GT_cyc_congr_of_lt {a b c a' b' c' : ℝ} (h1 : a < b ↔ a' < b') (h2 : b < c ↔ b' < c')
    (h3 : c < a ↔ c' < a') : cycBetween a b c ↔ cycBetween a' b' c' := by
  unfold cycBetween
  rw [h1, h2, h3]

omit [NeZero n] in
theorem GT_det_pos_iff_of_sign {a b : ℝ} (h : SignType.sign b = SignType.sign a) : 0 < a ↔ 0 < b := by
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

namespace GT_Endpoint

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

local notation "𝑇" => triangleCrossings P e f g
local notation "𝑆" => GT_S Q x
local notation "𝑆'" => transportSupport hs (GT_S Q x)

variable (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
include D

/-! #### The visit relabelling `ψ₀ = swap(τw₂, τm₁) ∘ swap(τw₃, τm₃) ∘ τ` -/

/-- The visit relabelling of the endpoint row (`w₂ ↦ m₁'`, `w₃ ↦ m₃'`, the other visits transported). -/
noncomputable def ψ₀ : Visit P ≃ Visit P' :=
  (visitTransport hs).trans
    ((Equiv.swap (visitTransport hs D.w₃) (visitTransport hs D.m₃)).trans
      (Equiv.swap (visitTransport hs D.w₂) (visitTransport hs D.m₁)))

theorem ψ₀_apply (v : Visit P) :
    D.ψ₀ v = Equiv.swap (visitTransport hs D.w₂) (visitTransport hs D.m₁)
      (Equiv.swap (visitTransport hs D.w₃) (visitTransport hs D.m₃) (visitTransport hs v)) := rfl

theorem w₂_ne_w₃ : D.w₂ ≠ D.w₃ := fun h => D.l23 (congrArg (fun v : Visit P => v.2.val) h)
theorem m₁_ne_m₃ : D.m₁ ≠ D.m₃ := fun h => D.l13 (congrArg (fun v : Visit P => v.2.val) h)
theorem w₂_ne_m₁ : D.w₂ ≠ D.m₁ := fun h => D.wm (congrArg Sigma.fst h)
theorem w₂_ne_m₃ : D.w₂ ≠ D.m₃ := fun h => D.wm (congrArg Sigma.fst h)
theorem w₃_ne_m₁ : D.w₃ ≠ D.m₁ := fun h => D.wm (congrArg Sigma.fst h)
theorem w₃_ne_m₃ : D.w₃ ≠ D.m₃ := fun h => D.wm (congrArg Sigma.fst h)
theorem x₁_ne_x₂ : D.x₁ ≠ D.x₂ := fun h => D.l12 (congrArg (fun v : Visit P => v.2.val) h)

theorem ψ₀_w₂ : D.ψ₀ D.w₂ = visitTransport hs D.m₁ := by
  rw [ψ₀_apply, Equiv.swap_apply_of_ne_of_ne ((visitTransport hs).injective.ne D.w₂_ne_w₃)
    ((visitTransport hs).injective.ne D.w₂_ne_m₃), Equiv.swap_apply_left]

theorem ψ₀_w₃ : D.ψ₀ D.w₃ = visitTransport hs D.m₃ := by
  rw [ψ₀_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne
    ((visitTransport hs).injective.ne D.w₂_ne_m₃.symm) ((visitTransport hs).injective.ne D.m₁_ne_m₃.symm)]

theorem ψ₀_m₁ : D.ψ₀ D.m₁ = visitTransport hs D.w₂ := by
  rw [ψ₀_apply, Equiv.swap_apply_of_ne_of_ne ((visitTransport hs).injective.ne D.w₃_ne_m₁.symm)
    ((visitTransport hs).injective.ne D.m₁_ne_m₃), Equiv.swap_apply_right]

theorem ψ₀_m₃ : D.ψ₀ D.m₃ = visitTransport hs D.w₃ := by
  rw [ψ₀_apply, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne
    ((visitTransport hs).injective.ne D.w₂_ne_w₃.symm) ((visitTransport hs).injective.ne D.w₃_ne_m₁)]

theorem ψ₀_of_ne {v : Visit P} (hvw : v.1 ≠ w) (hvm : v.1 ≠ m) : D.ψ₀ v = visitTransport hs v := by
  have h1 : v ≠ D.w₂ := fun h => hvw (congrArg Sigma.fst h)
  have h2 : v ≠ D.w₃ := fun h => hvw (congrArg Sigma.fst h)
  have h3 : v ≠ D.m₁ := fun h => hvm (congrArg Sigma.fst h)
  have h4 : v ≠ D.m₃ := fun h => hvm (congrArg Sigma.fst h)
  rw [ψ₀_apply, Equiv.swap_apply_of_ne_of_ne ((visitTransport hs).injective.ne h2)
    ((visitTransport hs).injective.ne h4), Equiv.swap_apply_of_ne_of_ne
    ((visitTransport hs).injective.ne h1) ((visitTransport hs).injective.ne h3)]

/-- The visits of `w` are `w₂`, `w₃`. -/
theorem eq_w₂_or_w₃ {v : Visit P} (hv : v.1 = w) : v = D.w₂ ∨ v = D.w₃ := by
  rcases visit_eq_or_twin D.w₂ v hv with h | h
  · exact Or.inl h
  · rw [D.twin_w₂] at h; exact Or.inr h

theorem eq_m₁_or_m₃ {v : Visit P} (hv : v.1 = m) : v = D.m₁ ∨ v = D.m₃ := by
  rcases visit_eq_or_twin D.m₁ v hv with h | h
  · exact Or.inl h
  · rw [D.twin_m₁] at h; exact Or.inr h

/-- `ψ₀` lies over the crossing relabelling `φ`. -/
theorem ψ₀_fst (v : Visit P) : (D.ψ₀ v).1 = GT_φ hs w m v.1 := by
  by_cases hvw : v.1 = w
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · rw [D.ψ₀_w₂, visitTransport_crossing, w₂_fst, φ_w]; rfl
    · rw [D.ψ₀_w₃, visitTransport_crossing, w₃_fst, φ_w]; rfl
  by_cases hvm : v.1 = m
  · rcases D.eq_m₁_or_m₃ hvm with rfl | rfl
    · rw [D.ψ₀_m₁, visitTransport_crossing, m₁_fst, φ_m]; rfl
    · rw [D.ψ₀_m₃, visitTransport_crossing, m₃_fst, φ_m]; rfl
  rw [D.ψ₀_of_ne hvw hvm, visitTransport_crossing, φ_of_ne hvw hvm]

/-- `ψ₀` commutes with the twin pairing. -/
theorem ψ₀_twin (v : Visit P) : D.ψ₀ (visitTwin v) = visitTwin (D.ψ₀ v) := by
  by_cases hvw : v.1 = w
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · rw [D.twin_w₂, D.ψ₀_w₃, D.ψ₀_w₂, ← visitTransport_visitTwin, D.twin_m₁]
    · rw [D.twin_w₃, D.ψ₀_w₂, D.ψ₀_w₃, ← visitTransport_visitTwin, D.twin_m₃]
  by_cases hvm : v.1 = m
  · rcases D.eq_m₁_or_m₃ hvm with rfl | rfl
    · rw [D.twin_m₁, D.ψ₀_m₃, D.ψ₀_m₁, ← visitTransport_visitTwin, D.twin_w₂]
    · rw [D.twin_m₃, D.ψ₀_m₁, D.ψ₀_m₃, ← visitTransport_visitTwin, D.twin_w₃]
  have htw : (visitTwin v).1 = v.1 := visitTwin_crossing v
  rw [D.ψ₀_of_ne hvw hvm, D.ψ₀_of_ne (htw ▸ hvw) (htw ▸ hvm), visitTransport_visitTwin]

/-- The divide signs are carried by `ψ₀` (outside visits by `sign_eq`; `w₂ ↦ m₁'`, `w₃ ↦ m₃'` by the
sign identity `sgn`, R_GENERIC_COMMON_TRANSPORT_PROOF.md (4)/(6)). -/
theorem ψ₀_det (v : Visit P) (hvm : v.1 ≠ m) :
    (0 < det (edge P v.2.val) (edge P (visitTwin v).2.val) ↔
      0 < det (edge P' (D.ψ₀ v).2.val) (edge P' (visitTwin (D.ψ₀ v)).2.val)) := by
  have hsign : ∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j)) := by
    intro i j hij
    exact GT_det_pos_iff_of_sign (D.sign_eq i j hij)
  have hm : IsCrossing P {ℓ₁, ℓ₃} := by rw [← D.mval]; exact m.property
  by_cases hvw : v.1 = w
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · rw [D.twin_w₂, D.ψ₀_w₂, ← visitTransport_visitTwin, D.twin_m₁, visitTransport_edge,
        visitTransport_edge, w₂_edge, w₃_edge, m₁_edge, m₃_edge, ← hsign ℓ₁ ℓ₃ hm]
      exact GT_det_pos_iff_of_sign D.sgn.symm
    · rw [D.twin_w₃, D.ψ₀_w₃, ← visitTransport_visitTwin, D.twin_m₃, visitTransport_edge,
        visitTransport_edge, w₂_edge, w₃_edge, m₁_edge, m₃_edge, ← hsign ℓ₃ ℓ₁ (by rwa [Finset.pair_comm])]
      have h' : crossingSign P ℓ₃ ℓ₂ = crossingSign P ℓ₃ ℓ₁ := by
        rw [crossingSign_swap P ℓ₂ ℓ₃, crossingSign_swap P ℓ₁ ℓ₃, D.sgn]
      exact GT_det_pos_iff_of_sign h'.symm
  · rw [D.ψ₀_of_ne hvw hvm, ← visitTransport_visitTwin, visitTransport_edge, visitTransport_edge]
    apply hsign
    rw [← visit_crossing_val_eq_pair v]
    exact v.1.property

/-! #### Key comparisons with the `ℓ₃`-visits and with the `x`-visits -/

theorem adj1_v : AdjacentVisits hP D.x₁ D.m₁ := D.adj1
theorem adj2_v : AdjacentVisits hP D.x₂ D.w₂ := D.adj2
theorem adj3_v : AdjacentVisits hP D.w₃ D.m₃ := D.adj3
theorem adj1'_v : AdjacentVisits hP' (visitTransport hs D.x₁) (visitTransport hs D.m₁) := D.adj1'
theorem adj2'_v : AdjacentVisits hP' (visitTransport hs D.x₂) (visitTransport hs D.w₂) := D.adj2'
theorem adj3'_v : AdjacentVisits hP' (visitTransport hs D.w₃) (visitTransport hs D.m₃) := D.adj3'

/-- For a visit `y` on another edge than `ℓ₃`, or an outside visit, its key order relative to `w₃`
is carried to the key order of `τy` relative to `m₃'` (`w₃, m₃` are adjacent on `ℓ₃`, `x₁` on another
edge). -/
theorem key_lt_w₃_iff (y : Visit P) (hy : y.1 ≠ w) (hym : y.1 ≠ m) (hyx : y.2.val ≠ ℓ₃ ∨ y.1.val ∉ triangleSupports e f g) :
    (geometricVisitKey hP y < geometricVisitKey hP D.w₃ ↔
        geometricVisitKey hP' (visitTransport hs y) < geometricVisitKey hP' (visitTransport hs D.m₃)) ∧
    (geometricVisitKey hP D.w₃ < geometricVisitKey hP y ↔
        geometricVisitKey hP' (visitTransport hs D.m₃) < geometricVisitKey hP' (visitTransport hs y)) := by
  have hyw3 : y ≠ D.w₃ := fun h => hy (congrArg Sigma.fst h)
  have hym3 : y ≠ D.m₃ := fun h => hym (congrArg Sigma.fst h)
  -- the order of `y` and `m₃` is carried (not a reversed pair: `y ∉ T`, or different edges)
  have hcarry : ∀ v : Visit P, v.2.val ≠ ℓ₃ ∨ v.1.val ∉ triangleSupports e f g →
      (geometricVisitKey hP v < geometricVisitKey hP D.m₃ ↔
        geometricVisitKey hP' (visitTransport hs v) < geometricVisitKey hP' (visitTransport hs D.m₃)) ∧
      (geometricVisitKey hP D.m₃ < geometricVisitKey hP v ↔
        geometricVisitKey hP' (visitTransport hs D.m₃) < geometricVisitKey hP' (visitTransport hs v)) := by
    intro v hv
    have hnr : ¬ GT_Rev 𝑇 v D.m₃ := by
      rcases hv with hv | hv
      · exact GT_not_rev_of_edge_ne hv
      · exact GT_not_rev_of_not_mem_left (fun h => hv ((F1.mem_triangleCrossings e f g v.1).mp h))
    exact ⟨D.wall.key_lt v D.m₃ hnr, D.wall.key_lt D.m₃ v (fun h => hnr h.symm)⟩
  by_cases hy3 : y.2.val = ℓ₃
  · -- `y` on `ℓ₃`, outside: not between the adjacent `w₃`, `m₃`
    have hlt := GT_adj_lt_iff hP D.adj3_v rfl D.x₁ D.l13 y hyw3 hym3
    rw [hlt.1, hlt.2]
    exact hcarry y (Or.inr (hyx.resolve_left (fun h => h hy3)))
  · -- different edges: the key order is the edge order, on both sides
    have h1 := GT_key_lt_iff_of_edge_ne hP (v := y) (w := D.w₃) hy3
    have h2 := GT_key_lt_iff_of_edge_ne hP' (v := visitTransport hs y) (w := visitTransport hs D.m₃)
      (by rw [visitTransport_edge, visitTransport_edge]; exact hy3)
    have h3 := GT_key_lt_iff_of_edge_ne hP (v := D.w₃) (w := y) (Ne.symm hy3)
    have h4 := GT_key_lt_iff_of_edge_ne hP' (v := visitTransport hs D.m₃) (w := visitTransport hs y)
      (by rw [visitTransport_edge, visitTransport_edge]; exact Ne.symm hy3)
    rw [h1, h2, h3, h4, visitTransport_edge, visitTransport_edge]
    exact ⟨Iff.rfl, Iff.rfl⟩

end GT_Endpoint

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

namespace GT_Endpoint

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

local notation "𝑇" => triangleCrossings P e f g
local notation "𝑆" => GT_S Q x
local notation "𝑆'" => transportSupport hs (GT_S Q x)

variable (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
include D

/-! #### The carrier of `w` and the arcs cut by the two visits of `x` -/

/-- The carrier of `S` bearing `w` (the "`BC`"-type carrier of §2). -/
noncomputable abbrev qw : GeoComponent hP 𝑆 := geoOwner hP 𝑆 (Sum.inr D.w₃)

theorem owner_w₂ : geoOwner hP 𝑆 (Sum.inr D.w₂) = D.qw := D.owner_w₂_eq_w₃

/-- `w₂` is adjacent to `x₂`, so the carrier of `w` is the carrier of `x₂` or that of `x₁`. -/
theorem qw_eq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂) ∨ D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁) := by
  rcases GT_succ_of_adjacent hP D.adj2_v rfl with h | h
  · right
    rw [← D.owner_w₂, ← geoOwner_successor hP _ (Sum.inr D.x₁),
      geoSmoothingSuccessor_visit_of_mem hP (GT_S Q x) D.x₁ x_mem_S, D.twin_x₁, h]
  · left
    rw [← D.owner_w₂, ← geoOwner_successor hP _ (Sum.inr D.w₂),
      geoSmoothingSuccessor_visit_of_not_mem hP (GT_S Q x) D.w₂ D.w_not_mem_S, h]

theorem mem_arc_of_owner_x₂ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂)) {u : Mark P}
    (hu : geoOwner hP 𝑆 u = D.qw) (hne : u ≠ Sum.inr D.x₂) :
    cycBetween (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP u) (geoMarkKey hP (Sum.inr D.x₂)) := by
  have h := GT_owner_arc hP D.S_geoIndep (x₁ := D.x₁) x_mem_S u (by rw [hu, hq, D.twin_x₁])
  rw [D.twin_x₁] at h
  exact h.resolve_left hne

theorem mem_arc_of_owner_x₁ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁)) {u : Mark P}
    (hu : geoOwner hP 𝑆 u = D.qw) (hne : u ≠ Sum.inr D.x₁) :
    cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP u) (geoMarkKey hP (Sum.inr D.x₁)) := by
  have h := GT_owner_arc hP D.S_geoIndep (x₁ := D.x₂) x_mem_S u (by rw [hu, hq, D.twin_x₂])
  rw [D.twin_x₂] at h
  exact h.resolve_left hne

theorem x'_mem_S' : (visitTransport hs D.x₁).1 ∈ 𝑆' := (mem_S'_iff x).mpr x_mem_S

theorem twin_τx₁ : visitTwin (visitTransport hs D.x₁) = visitTransport hs D.x₂ := by
  rw [← visitTransport_visitTwin, D.twin_x₁]
theorem twin_τx₂ : visitTwin (visitTransport hs D.x₂) = visitTransport hs D.x₁ := by
  rw [← visitTransport_visitTwin, D.twin_x₂]

theorem β_qw_of_x₂ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂)) :
    D.β D.qw = geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.x₂)) := by
  rw [hq, ← markTransport_visit, GT_owner_transport_corner D.wall D.x₂_corner]

theorem β_qw_of_x₁ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁)) :
    D.β D.qw = geoOwner hP' 𝑆' (Sum.inr (visitTransport hs D.x₁)) := by
  rw [hq, ← markTransport_visit, GT_owner_transport_corner D.wall D.x₁_corner]

theorem mem_arc'_of_owner_x₂ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂)) {u' : Mark P'}
    (hu : geoOwner hP' 𝑆' u' = D.β D.qw) (hne : u' ≠ Sum.inr (visitTransport hs D.x₂)) :
    cycBetween (geoMarkKey hP' (Sum.inr (visitTransport hs D.x₁))) (geoMarkKey hP' u')
      (geoMarkKey hP' (Sum.inr (visitTransport hs D.x₂))) := by
  have h := GT_owner_arc hP' D.S'_ind (x₁ := visitTransport hs D.x₁) D.x'_mem_S' u'
    (by rw [hu, D.β_qw_of_x₂ hq, D.twin_τx₁])
  rw [D.twin_τx₁] at h
  exact h.resolve_left hne

theorem mem_arc'_of_owner_x₁ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁)) {u' : Mark P'}
    (hu : geoOwner hP' 𝑆' u' = D.β D.qw) (hne : u' ≠ Sum.inr (visitTransport hs D.x₁)) :
    cycBetween (geoMarkKey hP' (Sum.inr (visitTransport hs D.x₂))) (geoMarkKey hP' u')
      (geoMarkKey hP' (Sum.inr (visitTransport hs D.x₁))) := by
  have h := GT_owner_arc hP' D.S'_ind (x₁ := visitTransport hs D.x₂)
    ((mem_S'_iff x).mpr x_mem_S) u' (by rw [hu, D.β_qw_of_x₁ hq, D.twin_τx₂])
  rw [D.twin_τx₂] at h
  exact h.resolve_left hne

/-! #### The visits of the piece of `w` -/

/-- A visit of a crossing of `U(S)` other than `m`: its carrier's copy carries the relabelled visit. -/
theorem owner'_ψ₀ {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) :
    geoOwner hP' 𝑆' (Sum.inr (D.ψ₀ v)) = D.β (geoOwner hP 𝑆 (Sum.inr v)) := by
  rcases D.mem_U_cases hv with hvw | hvT
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · rw [D.ψ₀_w₂, D.owner'_m₁, D.owner_w₂]
    · rw [D.ψ₀_w₃, D.owner'_m₃]
  · have hvw : v.1 ≠ w := fun h => hvT (h ▸ D.wT)
    have hvm : v.1 ≠ m := fun h => hvT (h ▸ D.mT)
    rw [D.ψ₀_of_ne hvw hvm, ← markTransport_visit]
    exact GT_owner_transport D.wall (good_of_outside hvT)

/-- Key orders are carried by `ψ₀` on the visits of `U(S) ∪ {x}` other than `w₂` (the visits of
outside crossings, the two visits of `x`, and `w₃ ↦ m₃'`). -/
theorem key_lt_ψ₀ (y z : Visit P) (hy : y.1 ≠ m ∧ (y.1 ≠ w ∨ y = D.w₃))
    (hz : z.1 ≠ m ∧ (z.1 ≠ w ∨ z = D.w₃)) :
    geometricVisitKey hP y < geometricVisitKey hP z ↔
      geometricVisitKey hP' (D.ψ₀ y) < geometricVisitKey hP' (D.ψ₀ z) := by
  -- a visit of a triangle crossing other than `w, m` is a visit of `x`, hence not on `ℓ₃`
  have hx3 : ∀ v : Visit P, v.1 ≠ w → v.1 ≠ m → v.2.val ≠ ℓ₃ ∨ v.1.val ∉ triangleSupports e f g := by
    intro v hvw hvm
    by_cases hvT : v.1.val ∈ triangleSupports e f g
    · left
      rcases D.tri_cases v.1 hvT with hvx | hvx | hvx
      · intro h3
        apply D.l3_not_mem_x
        rw [← h3, ← hvx]
        exact v.2.property
      · exact absurd hvx hvw
      · exact absurd hvx hvm
    · exact Or.inr hvT
  rcases hy.2 with hyw | rfl <;> rcases hz.2 with hzw | rfl
  · -- neither is `w₃`: transported visits, not a reversed pair
    rw [D.ψ₀_of_ne hyw hy.1, D.ψ₀_of_ne hzw hz.1]
    apply D.wall.key_lt
    rintro ⟨hyT, hzT, hne, -⟩
    have hyx := D.tri_cases y.1 ((F1.mem_triangleCrossings e f g y.1).mp hyT)
    have hzx := D.tri_cases z.1 ((F1.mem_triangleCrossings e f g z.1).mp hzT)
    rcases hyx with hyx | hyx | hyx <;> rcases hzx with hzx | hzx | hzx <;>
      first | exact hne (hyx.trans hzx.symm) | exact absurd hyx hyw | exact absurd hyx hy.1 |
        exact absurd hzx hzw | exact absurd hzx hz.1
  · rw [D.ψ₀_of_ne hyw hy.1, D.ψ₀_w₃]
    exact (D.key_lt_w₃_iff y hyw hy.1 (hx3 y hyw hy.1)).1
  · rw [D.ψ₀_of_ne hzw hz.1, D.ψ₀_w₃]
    exact (D.key_lt_w₃_iff z hzw hz.1 (hx3 z hzw hz.1)).2
  · exact iff_of_false (lt_irrefl _) (lt_irrefl _)

theorem x₁_not_mem_U_visit : D.x₁.1 ∉ CV.U hP 𝑆 := x_not_mem_U
theorem x₁_ne_of_mem_U {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) : D.x₁ ≠ v :=
  fun h => x_not_mem_U (h ▸ hv)
theorem x₂_ne_of_mem_U {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) : D.x₂ ≠ v :=
  fun h => x_not_mem_U (h ▸ hv)
theorem τx₁_ne_ψ₀_of_mem_U {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) : visitTransport hs D.x₁ ≠ D.ψ₀ v := by
  intro h
  have h1 := congrArg Sigma.fst h
  rw [D.ψ₀_fst, visitTransport_crossing] at h1
  have : GT_φ hs w m v.1 ∈ CV.U hP' 𝑆' := (D.mem_U_iff v.1).mpr hv
  rw [← h1] at this
  exact x'_not_mem_U this
theorem τx₂_ne_ψ₀_of_mem_U {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) : visitTransport hs D.x₂ ≠ D.ψ₀ v := by
  intro h
  have h1 := congrArg Sigma.fst h
  rw [D.ψ₀_fst, visitTransport_crossing] at h1
  have : GT_φ hs w m v.1 ∈ CV.U hP' 𝑆' := (D.mem_U_iff v.1).mpr hv
  rw [← h1] at this
  exact x'_not_mem_U this

/-- `ψ₀ v = m₁'` only for `v = w₂`. -/
theorem ψ₀_ne_τm₁ {v : Visit P} (hv : v.1 ∈ CV.U hP 𝑆) (hvw₂ : v ≠ D.w₂) :
    D.ψ₀ v ≠ visitTransport hs D.m₁ := by
  intro h
  have h1 := congrArg Sigma.fst h
  rw [D.ψ₀_fst, visitTransport_crossing, m₁_fst] at h1
  rcases D.mem_U_cases hv with hvw | hvT
  · rcases D.eq_w₂_or_w₃ hvw with rfl | rfl
    · exact hvw₂ rfl
    · rw [D.ψ₀_w₃] at h
      exact D.m₁_ne_m₃ ((visitTransport hs).injective h).symm
  · rw [D.φ_of_outside hvT] at h1
    exact hvT (((crossingTransport hs).injective h1) ▸ D.mT)

/-- **The rotation clause, case `qw = owner x₂`**: from `x₁`, every visit of the piece comes before
`w₂` (the last visit before `x₂`), and on the other side `m₁'` (the first after `x₁'`) comes before
every relabelled visit. -/
theorem rot_of_owner_x₂ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₂)) {u : Visit P}
    (hu : u.1 ∈ CV.U hP 𝑆) (hqu : geoOwner hP 𝑆 (Sum.inr u) = D.qw) (huw : u ≠ D.w₂) :
    cycBetween (geometricVisitKey hP D.x₁) (geometricVisitKey hP u) (geometricVisitKey hP D.w₂) ∧
    cycBetween (geometricVisitKey hP' (visitTransport hs D.x₁))
      (geometricVisitKey hP' (visitTransport hs D.m₁)) (geometricVisitKey hP' (D.ψ₀ u)) := by
  have hne2 : u ≠ D.x₂ := (D.x₂_ne_of_mem_U hu).symm
  have hw2ne : D.w₂ ≠ D.x₂ := fun h => D.xw (congrArg Sigma.fst h).symm
  have hu_arc := D.mem_arc_of_owner_x₂ hq (u := Sum.inr u) hqu (fun h => hne2 (Sum.inr.inj h))
  have hw_arc := D.mem_arc_of_owner_x₂ hq (u := Sum.inr D.w₂) D.owner_w₂ (fun h => hw2ne (Sum.inr.inj h))
  constructor
  · -- the arc from `w₂` to `x₂` is empty: `x₁` lies in the other arc
    have hempty : ∀ v : Visit P, ¬ cycBetween (geometricVisitKey hP D.w₂) (geometricVisitKey hP v)
        (geometricVisitKey hP D.x₂) :=
      GT_adj_empty' hP D.adj2_v D.x₁ (GT_cyc_rotate.mp (GT_cyc_rotate.mp hw_arc))
    rcases GT_cyc_total (GT_key_ne_of_ne hP (D.x₁_ne_of_mem_U hu))
      (GT_key_ne_of_ne hP (v := D.x₁) (w := D.w₂) (fun h => D.xw (congrArg Sigma.fst h)))
      (GT_key_ne_of_ne hP huw) with h | h
    · exact h
    · exact absurd (GT_cyc_arc_step hu_arc hw_arc h) (hempty u)
  · -- on the other side: the arc from `x₁'` to `m₁'` is empty
    have hu'_arc := D.mem_arc'_of_owner_x₂ hq (u' := Sum.inr (D.ψ₀ u))
      (by rw [D.owner'_ψ₀ hu, hqu]) (fun h => D.τx₂_ne_ψ₀_of_mem_U hu (Sum.inr.inj h).symm)
    have hm'_arc := D.mem_arc'_of_owner_x₂ hq (u' := Sum.inr (visitTransport hs D.m₁))
      (by rw [D.owner'_m₁])
      (fun h => D.xm (congrArg Sigma.fst ((visitTransport hs).injective (Sum.inr.inj h))).symm)
    have hempty : ∀ v : Visit P', ¬ cycBetween (geometricVisitKey hP' (visitTransport hs D.x₁))
        (geometricVisitKey hP' v) (geometricVisitKey hP' (visitTransport hs D.m₁)) :=
      GT_adj_empty hP' D.adj1'_v (visitTransport hs D.x₂) (GT_cyc_rotate.mp hm'_arc)
    rcases GT_cyc_total (GT_key_ne_of_ne hP' ((visitTransport hs).injective.ne
        (fun h : D.x₁ = D.m₁ => D.xm (congrArg Sigma.fst h))))
      (GT_key_ne_of_ne hP' (D.τx₁_ne_ψ₀_of_mem_U hu))
      (GT_key_ne_of_ne hP' (D.ψ₀_ne_τm₁ hu huw).symm) with h | h
    · exact h
    · exact absurd h (hempty _)

/-- **The rotation clause, case `qw = owner x₁`**: from `x₂`, `w₂` (the first visit after `x₂`) comes
before every visit of the piece, and on the other side every relabelled visit comes before `m₁'` (the
last before `x₁'`). -/
theorem rot_of_owner_x₁ (hq : D.qw = geoOwner hP 𝑆 (Sum.inr D.x₁)) {u : Visit P}
    (hu : u.1 ∈ CV.U hP 𝑆) (hqu : geoOwner hP 𝑆 (Sum.inr u) = D.qw) (huw : u ≠ D.w₂) :
    cycBetween (geometricVisitKey hP D.x₂) (geometricVisitKey hP D.w₂) (geometricVisitKey hP u) ∧
    cycBetween (geometricVisitKey hP' (visitTransport hs D.x₂)) (geometricVisitKey hP' (D.ψ₀ u))
      (geometricVisitKey hP' (visitTransport hs D.m₁)) := by
  have hne1 : u ≠ D.x₁ := (D.x₁_ne_of_mem_U hu).symm
  have hw1ne : D.w₂ ≠ D.x₁ := fun h => D.xw (congrArg Sigma.fst h).symm
  have hu_arc := D.mem_arc_of_owner_x₁ hq (u := Sum.inr u) hqu (fun h => hne1 (Sum.inr.inj h))
  have hw_arc := D.mem_arc_of_owner_x₁ hq (u := Sum.inr D.w₂) D.owner_w₂ (fun h => hw1ne (Sum.inr.inj h))
  constructor
  · -- the arc from `x₂` to `w₂` is empty: `x₁` lies in the other arc
    have hempty : ∀ v : Visit P, ¬ cycBetween (geometricVisitKey hP D.x₂) (geometricVisitKey hP v)
        (geometricVisitKey hP D.w₂) :=
      GT_adj_empty hP D.adj2_v D.x₁ (GT_cyc_rotate.mp hw_arc)
    rcases GT_cyc_total (GT_key_ne_of_ne hP (D.x₂_ne_of_mem_U hu))
      (GT_key_ne_of_ne hP (v := D.x₂) (w := D.w₂) (fun h => D.xw (congrArg Sigma.fst h)))
      (GT_key_ne_of_ne hP huw) with h | h
    · exact absurd h (hempty u)
    · exact h
  · -- on the other side: the arc from `m₁'` to `x₁'` is empty
    have hu'_arc := D.mem_arc'_of_owner_x₁ hq (u' := Sum.inr (D.ψ₀ u))
      (by rw [D.owner'_ψ₀ hu, hqu]) (fun h => D.τx₁_ne_ψ₀_of_mem_U hu (Sum.inr.inj h).symm)
    have hm'_arc := D.mem_arc'_of_owner_x₁ hq (u' := Sum.inr (visitTransport hs D.m₁))
      (by rw [D.owner'_m₁])
      (fun h => D.xm (congrArg Sigma.fst ((visitTransport hs).injective (Sum.inr.inj h))).symm)
    have hempty : ∀ v : Visit P', ¬ cycBetween (geometricVisitKey hP' (visitTransport hs D.m₁))
        (geometricVisitKey hP' v) (geometricVisitKey hP' (visitTransport hs D.x₁)) :=
      GT_adj_empty' hP' D.adj1'_v (visitTransport hs D.x₂)
        (GT_cyc_rotate.mp (GT_cyc_rotate.mp hm'_arc))
    rcases GT_cyc_total (GT_key_ne_of_ne hP' (D.τx₂_ne_ψ₀_of_mem_U hu))
      (GT_key_ne_of_ne hP' ((visitTransport hs).injective.ne
        (fun h : D.x₂ = D.m₁ => D.xm (congrArg Sigma.fst h))))
      (GT_key_ne_of_ne hP' (D.ψ₀_ne_τm₁ hu huw)) with h | h
    · exact h
    · exact absurd (GT_cyc_arc_step hu'_arc hm'_arc h) (hempty _)

end GT_Endpoint

end GT

section GT

open SM.Carrier SM.Link

variable {P P' : LabelledTuple n}

/-! ### The X₁ objects of the endpoint row across the wall (`CV.Generic` binders) -/

section GTEndpointX1

variable {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
variable (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)

/-- The piece polynomials of the pieces not containing `w` are carried (their labels are outside and
transported; `EXT_pieceHomfly_wall`). -/
theorem GT_endpoint_pieceHomfly_out (H : CV.Piece hG.crossingGeometry (GT_S Q x))
    (hw : w ∉ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H) :
    CV.pieceHomfly hn (hG'.diagrammatic hn) D.S'_mem_Ind (GT_pieceEquiv D.relabel H) =
      CV.pieceHomfly hn (hG.diagrammatic hn) D.S_ind H := by
  have hout : ∀ c ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H, c.val ∉ triangleSupports e f g := by
    intro c hc
    rcases D.mem_U_cases (CV.pieceLabels_subset _ _ H hc) with rfl | h
    · exact absurd hc hw
    · exact h
  refine EXT_pieceHomfly_wall hn hG hG' hs D.S_ind D.S'_mem_Ind ?_ ?_ H (GT_pieceEquiv D.relabel H)
    hout ?_
  · intro v w hv hw
    exact D.wall.key_lt v w (GT_not_rev_of_not_mem_left
      (fun h => hv ((F1.mem_triangleCrossings e f g v.1).mp h)))
  · intro i j hij
    exact GT_det_pos_iff_of_sign (D.sign_eq i j hij)
  · rw [GT_pieceLabels_eq D.relabel H]
    ext c'
    simp only [Finset.mem_map, Equiv.coe_toEmbedding]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, by rw [D.φ_of_outside (hout c hc)]⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c, hc, by rw [D.φ_of_outside (hout c hc)]⟩

/-- The visits of the piece of `w` lie on the carrier of `w`. -/
theorem GT_endpoint_owner_of_mem_piece (H : CV.Piece hG.crossingGeometry (GT_S Q x))
    (hw : w ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H) {v : Visit P}
    (hv : v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H) :
    geoOwner hG.crossingGeometry (GT_S Q x) (Sum.inr v) = D.qw := by
  obtain ⟨hc, hH⟩ := (CV.mem_pieceLabels _ _ H v.1).mp hv
  obtain ⟨hw', hHw⟩ := (CV.mem_pieceLabels _ _ H w).mp hw
  exact CV.owner_eq_of_same_piece _ D.S_ind hc hw' (hH.trans hHw.symm) v D.w₃ rfl rfl

/-- **The piece polynomial of the piece of `w` is carried**: the relabelled record isomorphism
(`GT_homfly_wall_gen` with `ψ₀`), its cyclic-order clause from `GT_cyc_carried` (the arc of the
carrier of `w`, `w₂` moving from last to first or from first to last). -/
theorem GT_endpoint_pieceHomfly_w (H : CV.Piece hG.crossingGeometry (GT_S Q x))
    (hw : w ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H) :
    CV.pieceHomfly hn (hG'.diagrammatic hn) D.S'_mem_Ind (GT_pieceEquiv D.relabel H) =
      CV.pieceHomfly hn (hG.diagrammatic hn) D.S_ind H := by
  unfold CV.pieceHomfly CV.pieceDiagram
  have hret := CV.pieceCarrier_geoCarrierCrossings (hG.diagrammatic hn) D.S_ind H
  have hret' := CV.pieceCarrier_geoCarrierCrossings (hG'.diagrammatic hn) D.S'_mem_Ind
    (GT_pieceEquiv D.relabel H)
  have hlab' := GT_pieceLabels_eq D.relabel H
  -- membership of a visit in the retained set of the piece carrier
  have hmem : ∀ v : Visit P,
      v.1 ∈ geoCarrierCrossings hG.crossingGeometry _ (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H) ↔
      v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H := fun v => by rw [hret]
  have hmem' : ∀ v : Visit P,
      (D.ψ₀ v).1 ∈ geoCarrierCrossings hG'.crossingGeometry _
        (CV.pieceCarrier (hG'.diagrammatic hn) D.S'_mem_Ind (GT_pieceEquiv D.relabel H)) ↔
      v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H := fun v => by
    rw [hret', hlab', D.ψ₀_fst, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  let ψ : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
      (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)} ≃
      {v' : Visit P' // v'.1 ∈ geoCarrierCrossings hG'.crossingGeometry _
        (CV.pieceCarrier (hG'.diagrammatic hn) D.S'_mem_Ind (GT_pieceEquiv D.relabel H))} :=
    Equiv.subtypeEquiv D.ψ₀ (fun v => (hmem v).trans (hmem' v).symm)
  have hU : ∀ v : Visit P, v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H →
      v.1 ∈ CV.U hG.crossingGeometry (GT_S Q x) := fun v hv => CV.pieceLabels_subset _ _ H hv
  refine GT_homfly_wall_gen hn _ _ _ _ _ _ ψ ?_ ?_ ?_
  · intro v hv
    exact D.ψ₀_twin v
  · -- the cyclic order
    intro u v s hcyc
    have hw₂ : D.w₂.1 ∈ geoCarrierCrossings hG.crossingGeometry _
        (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H) := (hmem D.w₂).mpr hw
    have key := GT_cyc_carried (ι := {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
        (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)})
      (fun v => geometricVisitKey hG.crossingGeometry v.1)
      (fun v => geometricVisitKey hG'.crossingGeometry (D.ψ₀ v.1))
    -- the two cases of the carrier of `w`
    have hgood : ∀ v : Visit P, v.1 ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H → v ≠ D.w₂ →
        v.1 ≠ m ∧ (v.1 ≠ w ∨ v = D.w₃) := by
      intro v hv hvw
      have hvU := hU v hv
      refine ⟨fun h => D.m_not_mem_U (h ▸ hvU), ?_⟩
      by_cases h : v.1 = w
      · rcases D.eq_w₂_or_w₃ h with rfl | rfl
        · exact absurd rfl hvw
        · exact Or.inr rfl
      · exact Or.inl h
    have hinj₁ : Function.Injective (fun v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
        (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)} => geometricVisitKey hG.crossingGeometry v.1) :=
      fun a b h => Subtype.ext (geometricVisitKey_injective _ h)
    have hinj₂ : Function.Injective (fun v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
        (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)} =>
          geometricVisitKey hG'.crossingGeometry (D.ψ₀ v.1)) :=
      fun a b h => Subtype.ext (D.ψ₀.injective (geometricVisitKey_injective _ h))
    have hrest : ∀ (a : Visit P), a.1 ≠ m → (a.1 ≠ w ∨ a = D.w₃) →
        ∀ (u v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry _
          (CV.pieceCarrier (hG.diagrammatic hn) D.S_ind H)}), u ≠ ⟨D.w₂, hw₂⟩ → v ≠ ⟨D.w₂, hw₂⟩ →
        (cycBetween (geometricVisitKey hG.crossingGeometry a) (geometricVisitKey hG.crossingGeometry u.1)
            (geometricVisitKey hG.crossingGeometry v.1) ↔
          cycBetween (geometricVisitKey hG'.crossingGeometry (D.ψ₀ a))
            (geometricVisitKey hG'.crossingGeometry (D.ψ₀ u.1))
            (geometricVisitKey hG'.crossingGeometry (D.ψ₀ v.1))) := by
      intro a ham haw u v hu hv
      have hu' := hgood u.1 ((hmem u.1).mp u.2) (fun h => hu (Subtype.ext h))
      have hv' := hgood v.1 ((hmem v.1).mp v.2) (fun h => hv (Subtype.ext h))
      exact GT_cyc_congr_of_lt (D.key_lt_ψ₀ a u.1 ⟨ham, haw⟩ hu') (D.key_lt_ψ₀ u.1 v.1 hu' hv')
        (D.key_lt_ψ₀ v.1 a hv' ⟨ham, haw⟩)
    rcases D.qw_eq with hq | hq
    · -- `qw = owner x₂`: base point `x₁`, `w₂` last ↦ `m₁'` first
      have hx₁ : D.x₁.1 ≠ m ∧ (D.x₁.1 ≠ w ∨ D.x₁ = D.w₃) := ⟨D.xm, Or.inl D.xw⟩
      refine (key (geometricVisitKey hG.crossingGeometry D.x₁)
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs D.x₁)) hinj₁ hinj₂ ?_ ?_ ⟨D.w₂, hw₂⟩
        ?_ ?_ u v s).mp hcyc
      · intro u
        exact GT_key_ne_of_ne _ (D.x₁_ne_of_mem_U (hU u.1 ((hmem u.1).mp u.2)))
      · intro u
        exact GT_key_ne_of_ne _ (D.τx₁_ne_ψ₀_of_mem_U (hU u.1 ((hmem u.1).mp u.2)))
      · intro u v hu hv
        have := hrest D.x₁ hx₁.1 hx₁.2 u v hu hv
        rwa [D.ψ₀_of_ne D.xw D.xm] at this
      · right; left
        intro u hu
        have hu' := D.rot_of_owner_x₂ hq (hU u.1 ((hmem u.1).mp u.2))
          (GT_endpoint_owner_of_mem_piece hG hG' D H hw ((hmem u.1).mp u.2))
          (fun h => hu (Subtype.ext h))
        refine ⟨hu'.1, ?_⟩
        show cycBetween (geometricVisitKey hG'.crossingGeometry (visitTransport hs D.x₁))
          (geometricVisitKey hG'.crossingGeometry (D.ψ₀ D.w₂)) (geometricVisitKey hG'.crossingGeometry (D.ψ₀ u.1))
        rw [D.ψ₀_w₂]
        exact hu'.2
    · -- `qw = owner x₁`: base point `x₂`, `w₂` first ↦ `m₁'` last
      have hx₂ : D.x₂.1 ≠ m ∧ (D.x₂.1 ≠ w ∨ D.x₂ = D.w₃) := ⟨D.xm, Or.inl D.xw⟩
      refine (key (geometricVisitKey hG.crossingGeometry D.x₂)
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs D.x₂)) hinj₁ hinj₂ ?_ ?_ ⟨D.w₂, hw₂⟩
        ?_ ?_ u v s).mp hcyc
      · intro u
        exact GT_key_ne_of_ne _ (D.x₂_ne_of_mem_U (hU u.1 ((hmem u.1).mp u.2)))
      · intro u
        exact GT_key_ne_of_ne _ (D.τx₂_ne_ψ₀_of_mem_U (hU u.1 ((hmem u.1).mp u.2)))
      · intro u v hu hv
        have := hrest D.x₂ hx₂.1 hx₂.2 u v hu hv
        rwa [D.ψ₀_of_ne D.xw D.xm] at this
      · right; right
        intro u hu
        have hu' := D.rot_of_owner_x₁ hq (hU u.1 ((hmem u.1).mp u.2))
          (GT_endpoint_owner_of_mem_piece hG hG' D H hw ((hmem u.1).mp u.2))
          (fun h => hu (Subtype.ext h))
        refine ⟨hu'.1, ?_⟩
        show cycBetween (geometricVisitKey hG'.crossingGeometry (visitTransport hs D.x₂))
          (geometricVisitKey hG'.crossingGeometry (D.ψ₀ u.1)) (geometricVisitKey hG'.crossingGeometry (D.ψ₀ D.w₂))
        rw [D.ψ₀_w₂]
        exact hu'.2
  · -- the divide signs
    intro v
    exact D.ψ₀_det v.1 (fun h => D.m_not_mem_U (h ▸ hU v.1 ((hmem v.1).mp v.2)))

/-- `P_{S,L}` is carried across the wall for the endpoint row. -/
theorem GT_endpoint_groupedPoly_eq (q : GeoComponent hG.crossingGeometry (GT_S Q x)) :
    CV.groupedPoly hn hG' D.S'_mem_Ind (D.β q) = CV.groupedPoly hn hG D.S_ind q := by
  unfold CV.groupedPoly
  rw [GT_piecesOn_eq D.relabel q, Finset.prod_map]
  refine Finset.prod_congr rfl fun H _ => ?_
  by_cases hw : w ∈ CV.pieceLabels hG.crossingGeometry (GT_S Q x) H
  · exact GT_endpoint_pieceHomfly_w hn hG hG' D H hw
  · exact GT_endpoint_pieceHomfly_out hn hG hG' D H hw

theorem GT_endpoint_groupedWrithe_eq (q : GeoComponent hG.crossingGeometry (GT_S Q x)) :
    CV.groupedWrithe hG' (D.β q) = CV.groupedWrithe hG q := by
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG' D.S'_mem_Ind,
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG D.S_ind, GT_card_geoCarrierCrossings_eq D.relabel q]

theorem GT_endpoint_Omega1_eq (q : GeoComponent hG.crossingGeometry (GT_S Q x)) :
    CV.Omega1 hn hG' D.S'_mem_Ind (D.β q) = CV.Omega1 hn hG D.S_ind q := by
  unfold CV.Omega1 CV.slot
  rw [GT_endpoint_groupedWrithe_eq hG hG' D q, GT_carrierR_eq hn hG hG' D.wall D.S_ind D.S'_mem_Ind q,
    GT_endpoint_groupedPoly_eq hn hG hG' D q]

/-- **The summand transport of an endpoint row.** -/
theorem GT_endpoint_summandTransport : SummandTransport hn hG hG' D.S_ind D.S'_mem_Ind :=
  ⟨GT_wind_eq hn hG hG' D.wall, D.β, fun q =>
    ⟨GT_weight_eq hn hG hG' D.wall q, GT_carrierR_eq hn hG hG' D.wall D.S_ind D.S'_mem_Ind q,
      GT_endpoint_groupedWrithe_eq hG hG' D q, GT_endpoint_groupedPoly_eq hn hG hG' D q,
      GT_endpoint_Omega1_eq hn hG hG' D q⟩⟩

include D in
/-- **`T_P(x) = T_E(x)`**: the row term of the endpoint row is carried across the wall
(R_GENERIC_COMMON_TRANSPORT_PROOF.md §2–§3, on the abstract configuration). -/
theorem GT_endpoint_rowTerm_eq :
    rowTerm hn hG (Q ∪ {x}) = rowTerm hn hG' (transportSupport hs (Q ∪ {x})) :=
  AV_rowTerm_eq_of_summandTransport hn hG hG' D.S_ind D.S'_mem_Ind
    (GT_endpoint_summandTransport hn hG hG' D)

end GTEndpointX1

end GT

section GT

open SM.Carrier SM.Link

/-! ### The endpoint configuration from the event data (rows 164, 172-table, the sign radius) -/

section GTEvent

variable {P : LabelledTuple n}

omit [NeZero n] in
theorem GT_adjacent_symm {hP : CrossingGeometry P} {v w : Visit P} (h : AdjacentVisits hP v w) :
    AdjacentVisits hP w v :=
  ⟨Ne.symm h.1, h.2.symm⟩

omit [NeZero n] in
/-- A crossing containing two distinct labels is carried by exactly that pair. -/
theorem GT_val_eq_pair {y : Crossing P} {i j : ZMod n} (hi : i ∈ y.val) (hj : j ∈ y.val) (hij : i ≠ j) :
    y.val = {i, j} := by
  have h2 := crossing_card_two y
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact hi
    · exact hj
  · exact le_of_eq (by rw [h2, Finset.card_pair hij])

omit [NeZero n] in
theorem GT_isCrossing_of_mem {y : Crossing P} {i j : ZMod n} (hi : i ∈ y.val) (hj : j ∈ y.val)
    (hij : i ≠ j) : IsCrossing P {i, j} := by
  rw [← GT_val_eq_pair hi hj hij]; exact y.property

omit [NeZero n] in
theorem GT_S_eq_insert {Q : Finset (Crossing P)} {x : Crossing P} : GT_S Q x = insert x Q := by
  rw [Finset.insert_eq, Finset.union_comm]

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **Adjacency of any two triangle crossings on their common edge** (R-LOC-2 (2), all three pairs,
either order). -/
theorem GT_adjacent_of_shared (hL : LocalizationData E e f g δ) (hef : e ≠ f) (heg : e ≠ g)
    (hfg : f ≠ g) (t : E.Parameter) (ht : Punctured E δ t) {y z : Crossing (E.curve t)}
    (hy : y.val ∈ triangleSupports e f g) (hz : z.val ∈ triangleSupports e f g) (hyz : y ≠ z)
    {ℓ : ZMod n} (hℓy : ℓ ∈ y.val) (hℓz : ℓ ∈ z.val) :
    AdjacentVisits (geomAt E t ht.1) (visitOn y ℓ hℓy) (visitOn z ℓ hℓz) := by
  obtain ⟨hef', heg', hfg'⟩ := hL.triangle_crossings t ht
  obtain ⟨h1, h2, h3⟩ := hL.adjacent t ht hef' heg' hfg'
  have hy' := (P1.mem_triangleCrossings_iff hef' heg' hfg' y).mp
    ((F1.mem_triangleCrossings e f g y).mpr hy)
  have hz' := (P1.mem_triangleCrossings_iff hef' heg' hfg' z).mp
    ((F1.mem_triangleCrossings e f g z).mpr hz)
  have hmem : ∀ {i j k : ZMod n} (_ : k ∈ ({i, j} : Finset (ZMod n))), k = i ∨ k = j := by
    intro i j k hk
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hk
  rcases hy' with rfl | rfl | rfl <;> rcases hz' with rfl | rfl | rfl
  · exact absurd rfl hyz
  · -- `x_ef`, `x_eg`: shared edge `e`
    rcases hmem hℓy with h | h
    · subst h; exact h1
    · exfalso
      rcases hmem (h ▸ hℓz : f ∈ ({e, g} : Finset (ZMod n))) with h' | h'
      · exact hef h'.symm
      · exact hfg h'
  · -- `x_ef`, `x_fg`: shared edge `f`
    rcases hmem hℓy with h | h
    · exfalso
      rcases hmem (h ▸ hℓz : e ∈ ({f, g} : Finset (ZMod n))) with h' | h'
      · exact hef h'
      · exact heg h'
    · subst h; exact h2
  · -- `x_eg`, `x_ef`: shared edge `e`
    rcases hmem hℓy with h | h
    · subst h; exact GT_adjacent_symm h1
    · exfalso
      rcases hmem (h ▸ hℓz : g ∈ ({e, f} : Finset (ZMod n))) with h' | h'
      · exact heg h'.symm
      · exact hfg h'.symm
  · exact absurd rfl hyz
  · -- `x_eg`, `x_fg`: shared edge `g`
    rcases hmem hℓy with h | h
    · exfalso
      rcases hmem (h ▸ hℓz : e ∈ ({f, g} : Finset (ZMod n))) with h' | h'
      · exact hef h'
      · exact heg h'
    · subst h; exact h3
  · -- `x_fg`, `x_ef`: shared edge `f`
    rcases hmem hℓy with h | h
    · subst h; exact GT_adjacent_symm h2
    · exfalso
      rcases hmem (h ▸ hℓz : g ∈ ({e, f} : Finset (ZMod n))) with h' | h'
      · exact heg h'.symm
      · exact hfg h'.symm
  · -- `x_fg`, `x_eg`: shared edge `g`
    rcases hmem hℓy with h | h
    · exfalso
      rcases hmem (h ▸ hℓz : f ∈ ({e, g} : Finset (ZMod n))) with h' | h'
      · exact hef h'.symm
      · exact hfg h'
    · subst h; exact GT_adjacent_symm h3
  · exact absurd rfl hyz

/-- The three triangle crossings. -/
theorem GT_tri_cases (t : E.Parameter) (hef : IsCrossing (E.curve t) {e, f})
    (heg : IsCrossing (E.curve t) {e, g}) (hfg : IsCrossing (E.curve t) {f, g})
    (y : Crossing (E.curve t)) (hy : y.val ∈ triangleSupports e f g) :
    y = xPair hef ∨ y = xPair heg ∨ y = xPair hfg :=
  (P1.mem_triangleCrossings_iff hef heg hfg y).mp ((F1.mem_triangleCrossings e f g y).mpr hy)

/-- **The twin masks** (R-PAR sharpened by full availability, `GenericTableData.mask_sharpening`): after
selecting the triangle crossing `x`, every outside survivor interlaces both other triangle crossings or
neither. -/
theorem GT_twins_of_mask (hG : GenericTableData E e f g δ) (t : E.Parameter) (ht : Punctured E δ t)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {x w m : Crossing (E.curve t)} (hx : x.val ∈ triangleSupports e f g)
    (hw : w.val ∈ triangleSupports e f g) (hm : m.val ∈ triangleSupports e f g)
    (hxw : x ≠ w) (hxm : x ≠ m) :
    ∀ y ∈ CV.U (geomAt E t ht.1) (GT_S Q x), y.val ∉ triangleSupports e f g →
      (GeometricInterlaces (geomAt E t ht.1) y w ↔ GeometricInterlaces (geomAt E t ht.1) y m) := by
  intro y hy hyT
  rw [GT_S_eq_insert] at hy
  obtain ⟨ha, hc, hb, -⟩ := hG.mask_sharpening t ht hef heg hfg Q hQ hfull
  have hint : ∀ z : Crossing (E.curve t), z.val ∈ triangleSupports e f g →
      (GeometricInterlaces (geomAt E t ht.1) y z ↔ z ∈ interlacedTriangle (geomAt E t ht.1) e f g y) := by
    intro z hz
    rw [G2.mem_interlacedTriangle_iff]
    exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  rw [hint w hw, hint m hm]
  have hw' := GT_tri_cases t hef heg hfg w hw
  have hm' := GT_tri_cases t hef heg hfg m hm
  rcases GT_tri_cases t hef heg hfg x hx with rfl | rfl | rfl
  · rcases ha y hy hyT with hM | hM
    · rw [hM]; simp
    · rw [hM]
      refine iff_of_true ?_ ?_
      · rcases hw' with h | h | h
        · exact absurd h.symm hxw
        · rw [h]; simp
        · rw [h]; simp
      · rcases hm' with h | h | h
        · exact absurd h.symm hxm
        · rw [h]; simp
        · rw [h]; simp
  · rcases hb y hy hyT with hM | hM
    · rw [hM]; simp
    · rw [hM]
      refine iff_of_true ?_ ?_
      · rcases hw' with h | h | h
        · rw [h]; simp
        · exact absurd h.symm hxw
        · rw [h]; simp
      · rcases hm' with h | h | h
        · rw [h]; simp
        · exact absurd h.symm hxm
        · rw [h]; simp
  · rcases hc y hy hyT with hM | hM
    · rw [hM]; simp
    · rw [hM]
      refine iff_of_true ?_ ?_
      · rcases hw' with h | h | h
        · rw [h]; simp
        · rw [h]; simp
        · exact absurd h.symm hxw
      · rcases hm' with h | h | h
        · rw [h]; simp
        · rw [h]; simp
        · exact absurd h.symm hxm

/-- The triangle is carried across the wall. -/
theorem GT_triangleCrossings_map {t t' : E.Parameter}
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s) :
    (triangleCrossings (E.curve t) e f g).map (crossingTransport hs).toEmbedding =
      triangleCrossings (E.curve t') e f g := by
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply, F1.mem_triangleCrossings, F1.mem_triangleCrossings]
  rfl

/-- An outside independent support is one on the far side as well (R-LOC-2 (4) off `T`). -/
theorem GT_outsideSupports_transport (hL : LocalizationData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) :
    transportSupport hs Q ∈ outsideSupports (geomAt E t' ht'.1) e f g := by
  obtain ⟨hQi, hQd⟩ := (F1.mem_outsideSupports _ e f g Q).mp hQ
  rw [F1.mem_outsideSupports]
  refine ⟨?_, ?_⟩
  · rw [CV.mem_Ind_iff]
    intro a' ha' b' hb' hab
    obtain ⟨a, rfl⟩ := (crossingTransport hs).surjective a'
    obtain ⟨b, rfl⟩ := (crossingTransport hs).surjective b'
    rw [mem_transportSupport_iff] at ha' hb'
    have hab' : a ≠ b := fun h => hab (h ▸ rfl)
    have hnT : ¬ (a ≠ b ∧ a.val ∈ triangleSupports e f g ∧ b.val ∈ triangleSupports e f g) := by
      rintro ⟨-, haT, -⟩
      exact Finset.disjoint_left.mp hQd ha' ((F1.mem_triangleCrossings e f g a).mpr haT)
    rw [hL.interlace_toggle t t' ht ht' hop hs a b, L.xor_iff_of_not_right hnT]
    exact ((CV.mem_Ind_iff _ Q).mp hQi) a ha' b hb' hab'
  · rw [Finset.disjoint_left]
    intro a' ha' haT
    obtain ⟨a, rfl⟩ := (crossingTransport hs).surjective a'
    rw [mem_transportSupport_iff] at ha'
    exact Finset.disjoint_left.mp hQd ha' ((F1.mem_triangleCrossings e f g a).mpr
      ((F1.mem_triangleCrossings e f g (crossingTransport hs a)).mp haT))

/-- Full availability is carried across the wall (`F1.avail_same`). -/
theorem GT_fullAvail_transport (hL : LocalizationData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    FullAvail (geomAt E t' ht'.1) e f g (transportSupport hs Q) := by
  unfold FullAvail at hfull ⊢
  rw [show transportSupport hs Q = Q.map (crossingTransport hs).toEmbedding from rfl,
    F1.avail_same hL t t' ht ht' hop hs Q hQ, hfull, GT_triangleCrossings_map]

/-- **The endpoint configuration from the event data**: the wall clauses of R-LOC-2 (row 164), the
adjacency of the three bundle pairs on both sides, the twin masks (row 172-table), the turns, signs
and ray (the sign radius), for a triangle crossing `x` with the two others `w` (the other member of
the selected pair) and `m` (the centre of the path side `t`). -/
theorem GT_endpointData (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hIxw : ¬ GeometricInterlaces (geomAt E t ht.1) x w) (hIxm : GeometricInterlaces (geomAt E t ht.1) x m)
    (hIwm : GeometricInterlaces (geomAt E t ht.1) w m)
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    GT_Endpoint (geomAt E t ht.1) (geomAt E t' ht'.1) hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃ := by
  obtain ⟨hQi, hQd⟩ := (F1.mem_outsideSupports _ e f g Q).mp hQ
  obtain ⟨hef', heg', hfg'⟩ := hL.triangle_crossings t ht
  exact {
    hef := hef, heg := heg, hfg := hfg
    xT := hx, wT := hw, mT := hm
    tri_cases := fun y hy => GT_tri_cases t hef' heg' hfg' y hy |>.imp id (fun h => h) |> fun h => by
      -- `y ∈ {x_ef, x_eg, x_fg} = {x, w, m}` (the three are distinct triangle crossings)
      rcases GT_tri_cases t hef' heg' hfg' x hx with hx' | hx' | hx' <;>
      rcases GT_tri_cases t hef' heg' hfg' w hw with hw' | hw' | hw' <;>
      rcases GT_tri_cases t hef' heg' hfg' m hm with hm' | hm' | hm' <;>
      first
      | exact absurd (hx'.trans hw'.symm) hxw
      | exact absurd (hx'.trans hm'.symm) hxm
      | exact absurd (hw'.trans hm'.symm) hwm
      | (rcases h with h | h | h <;> first
          | exact Or.inl (h.trans hx'.symm)
          | exact Or.inr (Or.inl (h.trans hw'.symm))
          | exact Or.inr (Or.inr (h.trans hm'.symm)))
    xw := hxw, xm := hxm, wm := hwm
    x1 := x1, m1 := m1, x2 := x2, w2 := w2, w3 := w3, m3 := m3
    l12 := l12, l13 := l13, l23 := l23
    Q_ind := hQi
    Q_out := fun q hq hqT => Finset.disjoint_left.mp hQd hq ((F1.mem_triangleCrossings e f g q).mpr hqT)
    Q_avail := fun q hq y hy => by
      have hyA : y ∈ avail (geomAt E t ht.1) e f g Q := by
        rw [hfull]; exact (F1.mem_triangleCrossings e f g y).mpr hy
      exact ((F1.mem_avail _ e f g Q y).mp hyA).2 q hq
    hxw := hIxw, hxm := hIxm, hwm := hIwm
    gauss := hL.gauss_words t t' ht ht' hop hs
    toggle := fun y z hyz => by
      rw [hL.interlace_toggle t t' ht ht' hop hs y z, L.xor_iff_of_not_right (fun h => hyz ⟨h.2.1, h.2.2⟩)]
    compl := fun y z hy hz hyz => hL.complement_on_triangle t t' ht ht' hop hs y z hy hz hyz
    adj1 := GT_adjacent_of_shared hL hef heg hfg t ht hx hm hxm x1 m1
    adj2 := GT_adjacent_of_shared hL hef heg hfg t ht hx hw hxw x2 w2
    adj3 := GT_adjacent_of_shared hL hef heg hfg t ht hw hm hwm w3 m3
    adj1' := GT_adjacent_of_shared hL hef heg hfg t' ht' (y := crossingTransport hs x)
      (z := crossingTransport hs m) hx hm ((crossingTransport hs).injective.ne hxm) x1 m1
    adj2' := GT_adjacent_of_shared hL hef heg hfg t' ht' (y := crossingTransport hs x)
      (z := crossingTransport hs w) hx hw ((crossingTransport hs).injective.ne hxw) x2 w2
    adj3' := GT_adjacent_of_shared hL hef heg hfg t' ht' (y := crossingTransport hs w)
      (z := crossingTransport hs m) hw hm ((crossingTransport hs).injective.ne hwm) w3 m3
    turn_eq := hR.turn_eq t t' ht ht'
    sign_eq := hR.sign_eq t t' ht ht'
    ray := by
      obtain ⟨r, hr⟩ := hR.ray
      refine ⟨r, fun h => ⟨(hr t ht h).1, ?_⟩⟩
      rw [(hr t' ht' h).2, (hr t ht h).2]
    twins := GT_twins_of_mask hG t ht hef' heg' hfg' hQ hfull hx hw hm hxw hxm
    sgn := hsgn }

/-- **The endpoint transport, `t` the two-edge side.** -/
theorem GT_endpoint_transport_path (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hIxw : ¬ GeometricInterlaces (geomAt E t ht.1) x w) (hIxm : GeometricInterlaces (geomAt E t ht.1) x m)
    (hIwm : GeometricInterlaces (geomAt E t ht.1) w m)
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {x}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {x})) :=
  GT_endpoint_rowTerm_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1)
    (GT_endpointData hL hG hR hef heg hfg ht ht' hop hs hQ hfull x w m ℓ₁ ℓ₂ ℓ₃ hx hw hm hxw hxm hwm
      x1 m1 x2 w2 w3 m3 l12 l13 l23 hIxw hIxm hIwm hsgn)

omit [NeZero n] in
theorem GT_transportSupport_S {P Q' : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q' s)
    (Q : Finset (Crossing P)) (x : Crossing P) :
    transportSupport hs (Q ∪ {x}) = transportSupport hs Q ∪ {crossingTransport hs x} := by
  rw [AV_transportSupport_union]
  rfl

/-- **The endpoint transport, `t` the one-edge side**: apply the two-edge case to the pair `(t', t)`. -/
theorem GT_endpoint_transport_edge (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hIxw : GeometricInterlaces (geomAt E t ht.1) x w) (hIxm : ¬ GeometricInterlaces (geomAt E t ht.1) x m)
    (hIwm : ¬ GeometricInterlaces (geomAt E t ht.1) w m)
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {x}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {x})) := by
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
  have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
  have hsgn' : crossingSign (E.curve t') ℓ₂ ℓ₃ = crossingSign (E.curve t') ℓ₁ ℓ₃ := by
    rw [hR.sign_eq t t' ht ht' ℓ₂ ℓ₃ (GT_isCrossing_of_mem w2 w3 l23),
      hR.sign_eq t t' ht ht' ℓ₁ ℓ₃ (GT_isCrossing_of_mem m1 m3 l13), hsgn]
  have h := GT_endpoint_transport_path hn hL hG hR hef heg hfg ht' ht hop' hs' hQ' hfull'
    (crossingTransport hs x) (crossingTransport hs w) (crossingTransport hs m) ℓ₁ ℓ₂ ℓ₃ hx hw hm
    ((crossingTransport hs).injective.ne hxw) ((crossingTransport hs).injective.ne hxm)
    ((crossingTransport hs).injective.ne hwm) x1 m1 x2 w2 w3 m3 l12 l13 l23
    (by rw [hL.complement_on_triangle t t' ht ht' hop hs x w hx hw hxw]; exact fun h => h hIxw)
    (by rw [hL.complement_on_triangle t t' ht ht' hop hs x m hx hm hxm]; exact hIxm)
    (by rw [hL.complement_on_triangle t t' ht ht' hop hs w m hw hm hwm]; exact hIwm) hsgn'
  rw [← GT_transportSupport_S hs Q x, EXT_transportSupport_symm hs (Q ∪ {x})] at h
  exact h.symm

/-- **The endpoint transport** for a row `x` of the selected pair `{x, w}`, `m` the third crossing: the
local graph at `t` is the path with centre `m` or the single edge `x–w`. -/
theorem GT_endpoint_transport (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (x w m : Crossing (E.curve t)) (ℓ₁ ℓ₂ ℓ₃ : ZMod n)
    (hx : x.val ∈ triangleSupports e f g) (hw : w.val ∈ triangleSupports e f g)
    (hm : m.val ∈ triangleSupports e f g) (hxw : x ≠ w) (hxm : x ≠ m) (hwm : w ≠ m)
    (x1 : ℓ₁ ∈ x.val) (m1 : ℓ₁ ∈ m.val) (x2 : ℓ₂ ∈ x.val) (w2 : ℓ₂ ∈ w.val) (w3 : ℓ₃ ∈ w.val)
    (m3 : ℓ₃ ∈ m.val) (l12 : ℓ₁ ≠ ℓ₂) (l13 : ℓ₁ ≠ ℓ₃) (l23 : ℓ₂ ≠ ℓ₃)
    (hloc : (¬ GeometricInterlaces (geomAt E t ht.1) x w ∧ GeometricInterlaces (geomAt E t ht.1) x m ∧
        GeometricInterlaces (geomAt E t ht.1) w m) ∨
      (GeometricInterlaces (geomAt E t ht.1) x w ∧ ¬ GeometricInterlaces (geomAt E t ht.1) x m ∧
        ¬ GeometricInterlaces (geomAt E t ht.1) w m))
    (hsgn : crossingSign (E.curve t) ℓ₂ ℓ₃ = crossingSign (E.curve t) ℓ₁ ℓ₃) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {x}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {x})) := by
  rcases hloc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact GT_endpoint_transport_path hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull x w m ℓ₁ ℓ₂ ℓ₃
      hx hw hm hxw hxm hwm x1 m1 x2 w2 w3 m3 l12 l13 l23 h1 h2 h3 hsgn
  · exact GT_endpoint_transport_edge hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull x w m ℓ₁ ℓ₂ ℓ₃
      hx hw hm hxw hxm hwm x1 m1 x2 w2 w3 m3 l12 l13 l23 h1 h2 h3 hsgn

end GTEvent

end GT

section GT

open SM.Carrier SM.Link

/-! ### The six endpoint rows: the two fields `endpoint_rows_canonical`, `endpoint_rows_relabelled` -/

section GTFields

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- Nonalternating, `s_a = −s_b` (pair `ab` selected) forces `s_b = s_c`. -/
theorem GT_signs_of_selectedAB : ∀ sa sb sc : SignType, sa ≠ 0 → sb ≠ 0 → sc ≠ 0 →
    ¬ IsAlternating sa sb sc → SelectedAB sa sb → sb = sc := by
  intro sa sb sc
  cases sa <;> cases sb <;> cases sc <;> decide

/-- Nonalternating, `s_b = −s_c` (pair `bc` selected) forces `s_a = s_b`. -/
theorem GT_signs_of_selectedBC : ∀ sa sb sc : SignType, sa ≠ 0 → sb ≠ 0 → sc ≠ 0 →
    ¬ IsAlternating sa sb sc → SelectedBC sb sc → sa = sb := by
  intro sa sb sc
  cases sa <;> cases sb <;> cases sc <;> decide

omit [NeZero n] in
theorem GT_mem_pair_l {i j : ZMod n} : i ∈ ({i, j} : Finset (ZMod n)) := mem_pair_left i j
omit [NeZero n] in
theorem GT_mem_pair_r {i j : ZMod n} : j ∈ ({i, j} : Finset (ZMod n)) := mem_pair_right i j

omit [NeZero n] in
theorem GT_tri_ef {e f g : ZMod n} : ({e, f} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  simp [triangleSupports]
omit [NeZero n] in
theorem GT_tri_eg {e f g : ZMod n} : ({e, g} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  simp [triangleSupports]
omit [NeZero n] in
theorem GT_tri_fg {e f g : ZMod n} : ({f, g} : Finset (ZMod n)) ∈ triangleSupports e f g := by
  simp [triangleSupports]

omit [NeZero n] in
/-- In the generic orbit not all three local edges are present. -/
theorem GT_not_all_edges {P : LabelledTuple n} (hP : CrossingGeometry P)
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hgen : ¬ ExtremeLocal hP hef heg hfg) (hAB : EdgeAB hP hef heg) (hBC : EdgeBC hP heg hfg) :
    ¬ EdgeAC hP hef hfg :=
  fun hAC => hgen (Or.inl ⟨hAB, hAC, hBC⟩)

omit [NeZero n] in
theorem GT_not_all_edges' {P : LabelledTuple n} (hP : CrossingGeometry P)
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hgen : ¬ ExtremeLocal hP hef heg hfg) (hAC : EdgeAC hP hef hfg) (hBC : EdgeBC hP heg hfg) :
    ¬ EdgeAB hP hef heg :=
  fun hAB => hgen (Or.inl ⟨hAB, hAC, hBC⟩)

omit [NeZero n] in
theorem GT_not_all_edges'' {P : LabelledTuple n} (hP : CrossingGeometry P)
    {hef : IsCrossing P {e, f}} {heg : IsCrossing P {e, g}} {hfg : IsCrossing P {f, g}}
    (hgen : ¬ ExtremeLocal hP hef heg hfg) (hAB : EdgeAB hP hef heg) (hAC : EdgeAC hP hef hfg) :
    ¬ EdgeBC hP heg hfg :=
  fun hBC => hgen (Or.inl ⟨hAB, hAC, hBC⟩)

/-- **Row `a` in the branch `ac`** (`x = a`, `w = c`, `m = b`; `ℓ₁ = e`, `ℓ₂ = f`, `ℓ₃ = g`). -/
theorem GT_row_a_of_AC (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAC (geomAt E t ht.1) hef' hfg') ∨
      (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg'))
    (hsbc : strandSign (E.curve t) e g = strandSign (E.curve t) f g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hef') (xPair hfg') (xPair heg') e f g GT_tri_ef GT_tri_fg GT_tri_eg
    (P1.xPair_ef_ne_fg hef' heg' hfg') (P1.xPair_ef_ne_eg hef' heg' hfg')
    (P1.xPair_eg_ne_fg hef' heg' hfg').symm
    GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r hef heg hfg ?_ ?_
  · rcases hloc with ⟨hAB, hBC, hAC⟩ | ⟨hAC, hAB, hBC⟩
    · exact Or.inl ⟨hAC, hAB, geometricInterlaces_symm _ hBC⟩
    · exact Or.inr ⟨hAC, hAB, fun h => hBC (geometricInterlaces_symm _ h)⟩
  · exact hsbc.symm

/-- **Row `c` in the branch `ac`** (`x = c`, `w = a`, `m = b`; `ℓ₁ = g`, `ℓ₂ = f`, `ℓ₃ = e`). -/
theorem GT_row_c_of_AC (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAC (geomAt E t ht.1) hef' hfg') ∨
      (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg'))
    (hsab : strandSign (E.curve t) e f = strandSign (E.curve t) e g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hfg') (xPair hef') (xPair heg') g f e GT_tri_fg GT_tri_ef GT_tri_eg
    (P1.xPair_ef_ne_fg hef' heg' hfg').symm (P1.xPair_eg_ne_fg hef' heg' hfg').symm
    (P1.xPair_ef_ne_eg hef' heg' hfg')
    GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l
    hfg.symm heg.symm hef.symm ?_ ?_
  · rcases hloc with ⟨hAB, hBC, hAC⟩ | ⟨hAC, hAB, hBC⟩
    · exact Or.inl ⟨fun h => hAC (geometricInterlaces_symm _ h), geometricInterlaces_symm _ hBC, hAB⟩
    · exact Or.inr ⟨geometricInterlaces_symm _ hAC, fun h => hBC (geometricInterlaces_symm _ h), hAB⟩
  · -- `crossingSign f e = crossingSign g e ⟸ s_a = s_b`
    show crossingSign (E.curve t) f e = crossingSign (E.curve t) g e
    rw [crossingSign_swap (E.curve t) e f, crossingSign_swap (E.curve t) e g]
    exact congrArg Neg.neg hsab

/-- **Row `a` in the branch `ab`** (`x = a`, `w = b`, `m = c`; `ℓ₁ = f`, `ℓ₂ = e`, `ℓ₃ = g`). -/
theorem GT_row_a_of_AB (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAB (geomAt E t ht.1) hef' heg') ∨
      (EdgeAB (geomAt E t ht.1) hef' heg' ∧ ¬ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg'))
    (hsbc : strandSign (E.curve t) e g = strandSign (E.curve t) f g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hef') (xPair heg') (xPair hfg') f e g GT_tri_ef GT_tri_eg GT_tri_fg
    (P1.xPair_ef_ne_eg hef' heg' hfg') (P1.xPair_ef_ne_fg hef' heg' hfg')
    (P1.xPair_eg_ne_fg hef' heg' hfg')
    GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r
    hef.symm hfg heg ?_ ?_
  · rcases hloc with ⟨hAC, hBC, hAB⟩ | ⟨hAB, hAC, hBC⟩
    · exact Or.inl ⟨hAB, hAC, hBC⟩
    · exact Or.inr ⟨hAB, hAC, hBC⟩
  · exact hsbc

/-- **Row `b` in the branch `ab`** (`x = b`, `w = a`, `m = c`; `ℓ₁ = g`, `ℓ₂ = e`, `ℓ₃ = f`). -/
theorem GT_row_b_of_AB (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAB (geomAt E t ht.1) hef' heg') ∨
      (EdgeAB (geomAt E t ht.1) hef' heg' ∧ ¬ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg'))
    (hsab : strandSign (E.curve t) e f = -strandSign (E.curve t) e g)
    (hsbc : strandSign (E.curve t) e g = strandSign (E.curve t) f g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair heg') (xPair hef') (xPair hfg') g e f GT_tri_eg GT_tri_ef GT_tri_fg
    (P1.xPair_ef_ne_eg hef' heg' hfg').symm (P1.xPair_eg_ne_fg hef' heg' hfg')
    (P1.xPair_ef_ne_fg hef' heg' hfg')
    GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_l
    heg.symm hfg.symm hef ?_ ?_
  · rcases hloc with ⟨hAC, hBC, hAB⟩ | ⟨hAB, hAC, hBC⟩
    · exact Or.inl ⟨fun h => hAB (geometricInterlaces_symm _ h), hBC, hAC⟩
    · exact Or.inr ⟨geometricInterlaces_symm _ hAB, hBC, hAC⟩
  · -- `crossingSign e f = crossingSign g f ⟸ s_a = −s_c`
    show crossingSign (E.curve t) e f = crossingSign (E.curve t) g f
    rw [crossingSign_swap (E.curve t) f g]
    show strandSign (E.curve t) e f = -strandSign (E.curve t) f g
    rw [← hsbc]; exact hsab

/-- **Row `b` in the branch `bc`** (`x = b`, `w = c`, `m = a`; `ℓ₁ = e`, `ℓ₂ = g`, `ℓ₃ = f`). -/
theorem GT_row_b_of_BC (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg') ∨
      (EdgeBC (geomAt E t ht.1) heg' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeAC (geomAt E t ht.1) hef' hfg'))
    (hsab : strandSign (E.curve t) e f = strandSign (E.curve t) e g)
    (hsbc : strandSign (E.curve t) e g = -strandSign (E.curve t) f g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair heg') (xPair hfg') (xPair hef') e g f GT_tri_eg GT_tri_fg GT_tri_ef
    (P1.xPair_eg_ne_fg hef' heg' hfg') (P1.xPair_ef_ne_eg hef' heg' hfg').symm
    (P1.xPair_ef_ne_fg hef' heg' hfg').symm
    GT_mem_pair_l GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_r
    heg hef hfg.symm ?_ ?_
  · rcases hloc with ⟨hAB, hAC, hBC⟩ | ⟨hBC, hAB, hAC⟩
    · exact Or.inl ⟨hBC, geometricInterlaces_symm _ hAB, geometricInterlaces_symm _ hAC⟩
    · exact Or.inr ⟨hBC, fun h => hAB (geometricInterlaces_symm _ h),
        fun h => hAC (geometricInterlaces_symm _ h)⟩
  · -- `crossingSign g f = crossingSign e f ⟸ s_a = −s_c`
    show crossingSign (E.curve t) g f = crossingSign (E.curve t) e f
    rw [crossingSign_swap (E.curve t) f g]
    show -strandSign (E.curve t) f g = strandSign (E.curve t) e f
    rw [hsab, hsbc]

/-- **Row `c` in the branch `bc`** (`x = c`, `w = b`, `m = a`; `ℓ₁ = f`, `ℓ₂ = g`, `ℓ₃ = e`). -/
theorem GT_row_c_of_BC (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hG : GenericTableData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g})
    (hloc : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg') ∨
      (EdgeBC (geomAt E t ht.1) heg' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeAC (geomAt E t ht.1) hef' hfg'))
    (hsab : strandSign (E.curve t) e f = strandSign (E.curve t) e g)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'})) := by
  refine GT_endpoint_transport hn hL hG hR hef heg hfg ht ht' hop hs hQ hfull
    (xPair hfg') (xPair heg') (xPair hef') f g e GT_tri_fg GT_tri_eg GT_tri_ef
    (P1.xPair_eg_ne_fg hef' heg' hfg').symm (P1.xPair_ef_ne_fg hef' heg' hfg').symm
    (P1.xPair_ef_ne_eg hef' heg' hfg').symm
    GT_mem_pair_l GT_mem_pair_r GT_mem_pair_r GT_mem_pair_r GT_mem_pair_l GT_mem_pair_l
    hfg hef.symm heg.symm ?_ ?_
  · rcases hloc with ⟨hAB, hAC, hBC⟩ | ⟨hBC, hAB, hAC⟩
    · exact Or.inl ⟨fun h => hBC (geometricInterlaces_symm _ h), geometricInterlaces_symm _ hAC,
        geometricInterlaces_symm _ hAB⟩
    · exact Or.inr ⟨geometricInterlaces_symm _ hBC, fun h => hAC (geometricInterlaces_symm _ h),
        fun h => hAB (geometricInterlaces_symm _ h)⟩
  · -- `crossingSign g e = crossingSign f e ⟸ s_a = s_b`
    show crossingSign (E.curve t) g e = crossingSign (E.curve t) f e
    rw [crossingSign_swap (E.curve t) e g, crossingSign_swap (E.curve t) e f]
    exact congrArg Neg.neg hsab.symm

/-- **Field `endpoint_rows_canonical` of `GenericTransportData`** (R_GENERIC_COMMON_TRANSPORT_PROOF.md
(2), `T_P(a) = T_E(a)`, `T_P(c) = T_E(c)` in the canonical branch `s_a = s_b = s_c`). -/
theorem GT_173_endpoint_rows_canonical (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'})) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen hsab hsbc Q hQ hfull
  have hsel : SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g) :=
    hsab.trans hsbc
  have hloc := ((hG.selected_is_graph_selected t ht hef' heg' hfg' hgen).1).mp hsel
  have hloc' : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
      ¬ EdgeAC (geomAt E t ht.1) hef' hfg') ∨
      (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg') := by
    rcases hloc with ⟨hAB, hBC⟩ | h
    · exact Or.inl ⟨hAB, hBC, GT_not_all_edges _ hgen hAB hBC⟩
    · exact Or.inr h
  exact ⟨GT_row_a_of_AC hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsbc hQ hfull,
    GT_row_c_of_AC hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsab hQ hfull⟩

/-- **Field `endpoint_rows_relabelled` of `GenericTransportData`** ("Every generic branch can be put in
this form by relabelling …"): the endpoint rows of the branches `ab` (rows `a, b`) and `bc` (rows `b, c`). -/
theorem GT_173_endpoint_rows_relabelled (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hG : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    (SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef'})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'}))) ∧
    (SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g) →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg'})) ∧
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg'}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg'}))) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen Q hQ hfull
  obtain ⟨h1, h2, h3, -⟩ := hG.nonzero t ht
  have hna := (hG.generic_iff_nonalternating t ht hef' heg' hfg').mp hgen
  have hz1 : strandSign (E.curve t) e f ≠ 0 := sign_ne_zero.mpr h1
  have hz2 : strandSign (E.curve t) e g ≠ 0 := sign_ne_zero.mpr h2
  have hz3 : strandSign (E.curve t) f g ≠ 0 := sign_ne_zero.mpr h3
  have hsel := hG.selected_is_graph_selected t ht hef' heg' hfg' hgen
  constructor
  · intro hAB
    have hsbc := GT_signs_of_selectedAB _ _ _ hz1 hz2 hz3 hna hAB
    have hloc := (hsel.2.1).mp hAB
    have hloc' : (EdgeAC (geomAt E t ht.1) hef' hfg' ∧ EdgeBC (geomAt E t ht.1) heg' hfg' ∧
        ¬ EdgeAB (geomAt E t ht.1) hef' heg') ∨
        (EdgeAB (geomAt E t ht.1) hef' heg' ∧ ¬ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
          ¬ EdgeBC (geomAt E t ht.1) heg' hfg') := by
      rcases hloc with ⟨hAC, hBC⟩ | h
      · exact Or.inl ⟨hAC, hBC, GT_not_all_edges' _ hgen hAC hBC⟩
      · exact Or.inr h
    exact ⟨GT_row_a_of_AB hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsbc hQ hfull,
      GT_row_b_of_AB hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hAB hsbc hQ hfull⟩
  · intro hBC
    have hsab := GT_signs_of_selectedBC _ _ _ hz1 hz2 hz3 hna hBC
    have hloc := (hsel.2.2).mp hBC
    have hloc' : (EdgeAB (geomAt E t ht.1) hef' heg' ∧ EdgeAC (geomAt E t ht.1) hef' hfg' ∧
        ¬ EdgeBC (geomAt E t ht.1) heg' hfg') ∨
        (EdgeBC (geomAt E t ht.1) heg' hfg' ∧ ¬ EdgeAB (geomAt E t ht.1) hef' heg' ∧
          ¬ EdgeAC (geomAt E t ht.1) hef' hfg') := by
      rcases hloc with ⟨hAB, hAC⟩ | h
      · exact Or.inl ⟨hAB, hAC, GT_not_all_edges'' _ hgen hAB hAC⟩
      · exact Or.inr h
    exact ⟨GT_row_b_of_BC hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsab hBC hQ hfull,
      GT_row_c_of_BC hn hL hG hR hef heg hfg ht ht' hop hs hef' heg' hfg' hloc' hsab hQ hfull⟩

end GTFields

end GT

section GT

open SM.Carrier SM.Link

/-! ### The empty row (R_GENERIC_COMMON_TRANSPORT_PROOF.md §1) and the missing fact G11

§1 transports the empty row carrier by carrier. Every carrier of `Q` has a copy across the wall
(`GT_carrierEquiv`, all marks are good since no triangle visit is a corner), with the same corner list,
turns, rotation and retained crossings; by cor:groupedknot (B) the grouped polynomial `P_{Q,L}` of every
carrier is the HOMFLY polynomial of its positive lift (`GT_groupedPoly_eq_homfly`). For a
triangle-disjoint carrier the two lifts are record-isomorphic (`EXT_homfly_wall`). For the one
distinguished carrier bearing the three local crossings the two lifts differ by the printed
"ordinary oriented Reidemeister III move" — the fact **G11** below, which the accepted library does not
provide: `SM.homfly_reidemeister_III` needs a geometric disc-local `SM.Link.RIII` site, and no
`RIIIData` is constructed anywhere in `work/lean`; the record-level replacement of CV:ax:gausscode
(`CV.gausscode_polynomial`) covers record *isomorphisms* only. `GT_G11` states exactly the polynomial
consequence the printed proof invokes ("Apply the corresponding ordinary oriented Reidemeister III
move to `D_P` … `ax:homfly` gives `P(D') = P(D_P)` … `ax:gausscode` identifies their oriented
links"), in the form in which the empty row consumes it. -/

/-- **G11 — HOMFLY invariance of the grouped diagram across the RIII wall.** Two carriers on the two
sides of a simple RIII wall in the generic orbit (`¬ IsAlternating`: the divide over-order of the
three local strands is transitive), with corresponding retained crossings, both retaining the three
triangle crossings, whose six triangle visits are exchanged pairwise on their edges
(`ExactTriangleVisitOrders`) and whose divide signs are carried, have positive lifts with the same
HOMFLY polynomial. This is an actual Reidemeister III move between the two lifts followed by a record
isomorphism; it is NOT provable from the accepted library (see the section docstring). -/
def GT_G11 : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) {P P' : LabelledTuple n}
    (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s) (e f g : ZMod n),
    e ≠ f → e ≠ g → f ≠ g →
    ExactTriangleVisitOrders P P' e f g hs →
    (∀ i j : ZMod n, IsCrossing P {i, j} →
      (0 < det (edge P i) (edge P j) ↔ 0 < det (edge P' i) (edge P' j))) →
    ¬ IsAlternating (strandSign P e f) (strandSign P e g) (strandSign P f g) →
    ∀ {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
      (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
      (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T'),
      geoCarrierCrossings hG'.cg T' q' =
        (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding →
      triangleCrossings P e f g ⊆ geoCarrierCrossings hG.cg T q →
      homfly (geoPositiveLift hn hG' hT' q') = homfly (geoPositiveLift hn hG hT q)

section GTEmpty

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

omit [NeZero n] in
/-- Two distinct triangle crossings share a label. -/
theorem GT_shared_label {P : LabelledTuple n} {y z : Crossing P} (hy : y.val ∈ triangleSupports e f g) (hz : z.val ∈ triangleSupports e f g)
    (hyz : y ≠ z) : ∃ ℓ : ZMod n, ℓ ∈ y.val ∧ ℓ ∈ z.val := by
  have hmem : ∀ {s : Finset (ZMod n)}, s ∈ triangleSupports e f g → s = {e, f} ∨ s = {e, g} ∨ s = {f, g} := by
    intro s hs
    simpa [triangleSupports] using hs
  have hne : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases hmem hy with h1 | h1 | h1 <;> rcases hmem hz with h2 | h2 | h2 <;>
    first
    | exact absurd (h1.trans h2.symm) hne
    | exact ⟨e, by rw [h1]; exact mem_pair_left _ _, by rw [h2]; exact mem_pair_left _ _⟩
    | exact ⟨f, by rw [h1]; exact mem_pair_right _ _, by rw [h2]; exact mem_pair_left _ _⟩
    | exact ⟨g, by rw [h1]; exact mem_pair_right _ _, by rw [h2]; exact mem_pair_right _ _⟩
    | exact ⟨f, by rw [h1]; exact mem_pair_left _ _, by rw [h2]; exact mem_pair_right _ _⟩

/-- The wall data of the empty row `S = Q` (no triangle crossing is selected). -/
theorem GT_empty_wall (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f)
    (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t') (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) :
    GT_Wall (geomAt E t ht.1) (geomAt E t' ht'.1) hs (triangleCrossings (E.curve t) e f g) Q where
  indep := CV.geoIndependent_of_mem_Ind _ ((F1.mem_outsideSupports _ e f g Q).mp hQ).1
  indep' := CV.geoIndependent_of_mem_Ind _
    ((F1.mem_outsideSupports _ e f g _).mp (GT_outsideSupports_transport hL ht ht' hop hs hQ)).1
  key_lt v w hvw := AV_key_lt_of_gauss _ _ hs hef heg hfg (hL.gauss_words t t' ht ht' hop hs) v w hvw
  corners_apart v w hrev := by
    rintro ⟨hvQ, -⟩
    exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hvQ hrev.1
  turn_eq := hR.turn_eq t t' ht ht'
  sign_eq := hR.sign_eq t t' ht ht'
  ray := by
    obtain ⟨r, hr⟩ := hR.ray
    refine ⟨r, fun h => ⟨(hr t ht h).1, ?_⟩⟩
    rw [(hr t' ht' h).2, (hr t ht h).2]

/-- In the empty row every visit of an unselected crossing is good (no triangle visit is a corner). -/
theorem GT_empty_good {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (v : Visit (E.curve t)) (_ : v.1 ∉ Q) :
    GT_Good (triangleCrossings (E.curve t) e f g) Q (Sum.inr v) := by
  intro v' hv' w hrev hw
  have hwQ : w.1 ∈ Q := hw
  exact Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hwQ hrev.2.1

/-- At full availability the three triangle crossings are undominated by `Q`. -/
theorem GT_empty_tri_mem_U {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    {y : Crossing (E.curve t)} (hy : y.val ∈ triangleSupports e f g) : y ∈ CV.U (geomAt E t ht.1) Q := by
  have hyA : y ∈ avail (geomAt E t ht.1) e f g Q := by
    rw [hfull]; exact (F1.mem_triangleCrossings e f g y).mpr hy
  rw [CV.mem_U_iff]
  refine ⟨fun h => Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 h
    ((F1.mem_triangleCrossings e f g y).mpr hy), fun q hq h => ?_⟩
  exact ((F1.mem_avail _ e f g Q y).mp hyA).2 q hq (geometricInterlaces_symm _ h)

/-- **A carrier of the empty row owning one triangle visit retains all three triangle crossings**:
the two visits of an undominated crossing lie on one carrier, and the adjacent unselected visits of
two triangle crossings on their shared edge lie on one carrier. -/
theorem GT_empty_tri_subset (hL : LocalizationData E e f g δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t : E.Parameter} (ht : Punctured E δ t) {Q : Finset (Crossing (E.curve t))}
    (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g) (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (q : GeoComponent (geomAt E t ht.1) Q) {v : Visit (E.curve t)}
    (hv : v.1.val ∈ triangleSupports e f g) (hvq : geoOwner (geomAt E t ht.1) Q (Sum.inr v) = q) :
    triangleCrossings (E.curve t) e f g ⊆ geoCarrierCrossings (geomAt E t ht.1) Q q := by
  have hQi := ((F1.mem_outsideSupports _ e f g Q).mp hQ).1
  have hall : ∀ {y : Crossing (E.curve t)}, y.val ∈ triangleSupports e f g →
      ∀ u : Visit (E.curve t), u.1 = y → geoOwner (geomAt E t ht.1) Q (Sum.inr u) = q →
      y ∈ geoCarrierCrossings (geomAt E t ht.1) Q q := by
    intro y hy u hu huq
    rw [mem_geoCarrierCrossings]
    refine ⟨((CV.mem_U_iff _ Q y).mp (GT_empty_tri_mem_U ht hQ hfull hy)).1, fun u' hu' => ?_⟩
    rw [CV.owner_eq_of_mem_U _ hQi (GT_empty_tri_mem_U ht hQ hfull hy) u' u hu' hu]
    exact huq
  intro z hz
  have hzT := (F1.mem_triangleCrossings e f g z).mp hz
  by_cases hzv : z = v.1
  · exact hall hzT v hzv.symm hvq
  · obtain ⟨ℓ, hℓv, hℓz⟩ := GT_shared_label hv hzT (Ne.symm hzv)
    have hadj := GT_adjacent_of_shared hL hef heg hfg t ht hv hzT (Ne.symm hzv) hℓv hℓz
    have hzQ : z ∉ Q := ((CV.mem_U_iff _ Q z).mp (GT_empty_tri_mem_U ht hQ hfull hzT)).1
    have hvQ : v.1 ∉ Q := ((CV.mem_U_iff _ Q v.1).mp (GT_empty_tri_mem_U ht hQ hfull hv)).1
    have h1 := GT_owner_eq_of_adjacent _ Q hadj rfl hvQ hzQ
    have h2 : geoOwner (geomAt E t ht.1) Q (Sum.inr (visitOn v.1 ℓ hℓv)) = q := by
      rw [CV.owner_eq_of_mem_U _ hQi (GT_empty_tri_mem_U ht hQ hfull hv) (visitOn v.1 ℓ hℓv) v rfl rfl]
      exact hvq
    exact hall hzT (visitOn z ℓ hℓz) rfl (h1.symm.trans h2)

/-- **The grouped polynomial of every carrier of the empty row is carried**: triangle-disjoint carriers
by the record isomorphism `EXT_homfly_wall`, the distinguished carrier by G11. -/
theorem GT_empty_groupedPoly_eq (hG11 : GT_G11) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hgen : ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q)
    (hQi : Q ∈ CV.Ind (geomAt E t ht.1)) (hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1))
    (q : GeoComponent (geomAt E t ht.1) Q) :
    CV.groupedPoly hn (genericAt E t' ht'.1) hQi' (GT_carrierEquiv (GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ) q) =
      CV.groupedPoly hn (genericAt E t ht.1) hQi q := by
  set W := GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ
  have hX := GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q
  have hdet : ∀ i j : ZMod n, IsCrossing (E.curve t) {i, j} →
      (0 < det (edge (E.curve t) i) (edge (E.curve t) j) ↔
        0 < det (edge (E.curve t') i) (edge (E.curve t') j)) :=
    fun i j hij => GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' i j hij)
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  by_cases htri : ∃ v : Visit (E.curve t), v.1.val ∈ triangleSupports e f g ∧
      geoOwner (geomAt E t ht.1) Q (Sum.inr v) = q
  · -- the distinguished carrier: G11
    obtain ⟨v, hv, hvq⟩ := htri
    exact hG11 n hn (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
      (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hs e f g hef heg hfg
      (hL.gauss_words t t' ht ht' hop hs) hdet
      ((hGT.generic_iff_nonalternating t ht hef' heg' hfg').mp hgen) _ _ q _ hX
      (GT_empty_tri_subset hL hef heg hfg ht hQ hfull q hv hvq)
  · -- a triangle-disjoint carrier: the record isomorphism
    have htri' : ∀ v : Visit (E.curve t), v.1.val ∈ triangleSupports e f g →
        geoOwner (geomAt E t ht.1) Q (Sum.inr v) ≠ q := fun v hv hq => htri ⟨v, hv, hq⟩
    refine EXT_homfly_wall hn _ _ hs _ _ q _ hX ?_ ?_
    · intro v w hv hw
      have hvT : v.1.val ∉ triangleSupports e f g := fun h =>
        htri' v h (((mem_geoCarrierCrossings _ Q q v.1).mp hv).2 v rfl)
      exact W.key_lt v w (GT_not_rev_of_not_mem_left
        (fun h => hvT ((F1.mem_triangleCrossings e f g v.1).mp h)))
    · intro v _
      exact hdet _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property)

/-- **Field `empty_row` of `GenericTransportData`, modulo G11** (R_GENERIC_COMMON_TRANSPORT_PROOF.md
§1: "`T_P(empty) = T_E(empty)`"). -/
theorem GT_173_empty_row (hG11 : GT_G11) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef' heg' hfg' →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) Q = rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) := by
  intro t t' ht ht' hop hs hef' heg' hfg' hgen Q hQ hfull
  have W := GT_empty_wall hL hR hef heg hfg ht ht' hop hs hQ
  have hQi : Q ∈ CV.Ind (geomAt E t ht.1) := ((F1.mem_outsideSupports _ e f g Q).mp hQ).1
  have hQi' : transportSupport hs Q ∈ CV.Ind (geomAt E t' ht'.1) :=
    ((F1.mem_outsideSupports _ e f g _).mp (GT_outsideSupports_transport hL ht ht' hop hs hQ)).1
  refine AV_rowTerm_eq_of_summandTransport hn (genericAt E t ht.1) (genericAt E t' ht'.1) hQi hQi'
    ⟨GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W, GT_carrierEquiv W, fun q =>
      ⟨GT_weight_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W q,
        GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hQi hQi' q, ?_, ?_, ?_⟩⟩
  · rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q, Finset.card_map]
  · exact GT_empty_groupedPoly_eq hG11 hn hL hGT hR hef heg hfg ht ht' hop hs hef' heg' hfg' hgen hQ hfull
      hQi hQi' q
  · unfold CV.Omega1 CV.slot
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hQi,
      GT_geoCarrierCrossings_eq_of_good W (GT_empty_good ht hQ) q, Finset.card_map,
      GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hQi hQi' q,
      GT_empty_groupedPoly_eq hG11 hn hL hGT hR hef heg hfg ht ht' hop hs hef' heg' hfg' hgen hQ hfull hQi hQi' q]

end GTEmpty

/-! ### The bundle and the row, modulo G11 -/

/-- **`GenericTransportData` from the accepted rows 164, 172-table, the sign radius, and G11.** -/
theorem GT_genericTransportData (hG11 : GT_G11) (hn : 3 ≤ n) {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : GenericTransportData hn E e f g δ where
  canonical_branch := PRE_173_canonical_branch hGT
  empty_row := GT_173_empty_row hG11 hn hL hGT hR hef heg hfg
  endpoint_rows_canonical := GT_173_endpoint_rows_canonical hn hL hGT hR hef heg hfg
  endpoint_rows_relabelled := GT_173_endpoint_rows_relabelled hn hL hGT hR hef heg hfg

/-- **Row 173, R:generic_transport, modulo G11**: the row theorem with the radius
`min δ_L (min δ_G δ_R)` of the accepted `localization`, `generic_table` and the sign radius. -/
theorem GT_generic_transport_of_G11 (hG11 : GT_G11) (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ := by
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δG δR), lt_min hδL (lt_min hδG hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δG δR)) hL
  have hGT' := SEL_genericTableData_mono ((min_le_right δL (min δG δR)).trans (min_le_left δG δR)) hGT
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δG δR)).trans (min_le_right δG δR)) hR
  exact GT_genericTransportData hG11 hn hL' hGT' hR' hef heg hfg

end GT

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

/-! ### Unit A2 — the assembly of the fibre identities (4) from rows 170, 172–177

`A2_fibre_identities` below is the clause `CvTheoremData.fibre_identities` proved from the bundles of
rows 170 (`AvailabilityZeroOneData`), 172 (`GenericSelectorData`), 173 (`GenericTransportData`),
174 (`GenericSelectedData`), 175 (`ExtremePairZeroData`), 176 (`ExtremeTransportData`), 177
(`ExtremeSelectedData`) together with the accepted cores 164 (`LocalizationData`), 171
(`FibrePartitionData`) and 172-table (`GenericTableData`), all at one radius `δ` (NOTES_FINAL.md §11,
unit U-A2). Row 168 (`ExteriorData`) is consumed inside the proofs of rows 173/174/176/177 and does
not enter the assembly itself.

Shape of the argument (R_ASSEMBLY_SPEC.md (4), the availability paragraph): by
`FibrePartitionData.avail_card` the availability of an outside support `Q` is `0`, `1` or `3`. At
`0`/`1` the identity is `AvailabilityZeroOneData.fibre_identity`. At `3` (`𝓐(Q) = T`, full
availability) `Φ(Q) = Σ_{J ⊆ T} T(Q ∪ J)` with absent rows `0` (`A2_fibreTerm_eq_eight`), the eight
rows are matched against the eight rows of the far side (`transportSupport hs (Q ∪ J)`), and the
match is: generic orbit — `∅` (173 `empty_row`), the two singletons of the selected pair (173
`endpoint_rows_*`), the centre and the selected pair (174 `couple_*`, with the pair absent on the
one-edge side), the two nonselected pairs (172 `row_zero`, both sides), `T` (absent on both sides,
the local graph having an edge); extreme orbit — the three singletons (176 `transport_x/y/z`), the
three pairs (175 `pair_absent_on_complete`/`pair_row_zero`, both sides), `∅` and `T` (177 `couple`,
with `T` absent on the `K3` side). -/

section A2

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

omit [NeZero n] in
/-- The sum over the eight subsets of a three-element set `{a, b, c}`. -/
theorem A2_sum_powerset_three {α : Type*} [DecidableEq α] {M : Type*} [AddCommMonoid M]
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (F : Finset α → M) :
    ∑ J ∈ ({a, b, c} : Finset α).powerset, F J =
      F ∅ + F {a} + F {b} + F {c} + F {a, b} + F {a, c} + F {b, c} + F {a, b, c} := by
  have h1 : ∀ G : Finset α → M, ∑ J ∈ ({c} : Finset α).powerset, G J = G ∅ + G {c} := by
    intro G
    have hc : ({c} : Finset α) = insert c ∅ := Finset.insert_empty.symm
    rw [hc, Finset.sum_powerset_insert (Finset.notMem_empty c),
      Finset.powerset_empty, Finset.sum_singleton, Finset.sum_singleton]
  have h2 : ∀ G : Finset α → M,
      ∑ J ∈ ({b, c} : Finset α).powerset, G J = G ∅ + G {c} + G {b} + G {b, c} := by
    intro G
    have hb : b ∉ ({c} : Finset α) := by simp [hbc]
    rw [Finset.sum_powerset_insert hb, h1, h1, Finset.insert_empty]
    abel
  have ha : a ∉ ({b, c} : Finset α) := by simp [hab, hac]
  rw [Finset.sum_powerset_insert ha, h2, h2, Finset.insert_empty]
  abel

/-- `T = {x_ef, x_eg, x_fg}` as a finset. -/
theorem A2_triangleCrossings_eq {P : LabelledTuple n} (hef : IsCrossing P {e, f})
    (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    triangleCrossings P e f g = {xPair hef, xPair heg, xPair hfg} := by
  ext x
  rw [P1.mem_triangleCrossings_iff hef heg hfg]
  simp only [Finset.mem_insert, Finset.mem_singleton]

omit [NeZero n] in
/-- The transport of a triangle crossing is the triangle crossing of the same edge pair. -/
theorem A2_crossingTransport_xPair {P Q : LabelledTuple n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) {i j : ZMod n} (h : IsCrossing P {i, j}) :
    crossingTransport hs (xPair h) = xPair ((hs _).mp h) := rfl

/-- The triangle is carried onto the triangle by the carrying edge pairs. -/
theorem A2_transportSupport_triangleCrossings {P Q : LabelledTuple n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (e f g : ZMod n) :
    transportSupport hs (triangleCrossings P e f g) = triangleCrossings Q e f g := by
  ext x'
  rw [transportSupport, Finset.mem_map_equiv, F1.mem_triangleCrossings, F1.mem_triangleCrossings]
  exact Iff.rfl

omit [NeZero n] in
theorem A2_transportSupport_union {P Q : LabelledTuple n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (S J : Finset (Crossing P)) :
    transportSupport hs (S ∪ J) = transportSupport hs S ∪ transportSupport hs J :=
  Finset.map_union S J

omit [NeZero n] in
/-- `transportSupport hs (Q ∪ {x_{ij}}) = transportSupport hs Q ∪ {x_{ij}}`. -/
theorem A2_transport_union_one {P Q : LabelledTuple n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (S : Finset (Crossing P)) {i j : ZMod n}
    (h : IsCrossing P {i, j}) :
    transportSupport hs (S ∪ {xPair h}) = transportSupport hs S ∪ {xPair ((hs _).mp h)} := by
  show (S ∪ {xPair h}).map (crossingTransport hs).toEmbedding =
    S.map (crossingTransport hs).toEmbedding ∪ {xPair ((hs _).mp h)}
  rw [Finset.map_union, Finset.map_singleton]
  rfl

omit [NeZero n] in
/-- `transportSupport hs (Q ∪ {x, y}) = transportSupport hs Q ∪ {x, y}` on the triangle. -/
theorem A2_transport_union_two {P Q : LabelledTuple n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (S : Finset (Crossing P)) {i j k l : ZMod n}
    (h1 : IsCrossing P {i, j}) (h2 : IsCrossing P {k, l}) :
    transportSupport hs (S ∪ {xPair h1, xPair h2}) =
      transportSupport hs S ∪ {xPair ((hs _).mp h1), xPair ((hs _).mp h2)} := by
  show (S ∪ {xPair h1, xPair h2}).map (crossingTransport hs).toEmbedding =
    S.map (crossingTransport hs).toEmbedding ∪ {xPair ((hs _).mp h1), xPair ((hs _).mp h2)}
  rw [Finset.map_union, Finset.map_insert, Finset.map_singleton]
  rfl

/-- `transportSupport hs (Q ∪ T) = transportSupport hs Q ∪ T'`. -/
theorem A2_transport_union_triangle {P Q : LabelledTuple n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (S : Finset (Crossing P))
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    transportSupport hs (S ∪ {xPair hef, xPair heg, xPair hfg}) =
      transportSupport hs S ∪ triangleCrossings Q e f g := by
  rw [A2_transportSupport_union, ← A2_triangleCrossings_eq hef heg hfg,
    A2_transportSupport_triangleCrossings]

omit [NeZero n] in
/-- Reading a support across the wall and back is the identity (the other direction of
`transportSupport_transportSupport_symm`; `hs'` is any proof of the reversed constancy). -/
theorem A2_transport_back {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (hs' : ∀ s, IsCrossing Q s ↔ IsCrossing P s) (S : Finset (Crossing P)) :
    transportSupport hs' (transportSupport hs S) = S :=
  transportSupport_transportSupport_symm hs' S

omit [NeZero n] in
/-- The powerset of a transported support is the transported powerset. -/
theorem A2_powerset_transport {P Q : LabelledTuple n} (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (S : Finset (Crossing P)) :
    (transportSupport hs S).powerset = S.powerset.map (supportEmb hs) := by
  ext J'
  rw [Finset.mem_powerset, Finset.mem_map]
  constructor
  · intro hJ'
    refine ⟨transportSupport (fun s => (hs s).symm) J', ?_, ?_⟩
    · rw [Finset.mem_powerset]
      calc transportSupport (fun s => (hs s).symm) J'
          ⊆ transportSupport (fun s => (hs s).symm) (transportSupport hs S) :=
            Finset.map_subset_map.mpr hJ'
        _ = S := A2_transport_back hs _ S
    · rw [supportEmb_apply]
      exact transportSupport_transportSupport_symm hs J'
  · rintro ⟨J, hJ, rfl⟩
    rw [supportEmb_apply]
    exact Finset.map_subset_map.mpr (Finset.mem_powerset.mp hJ)


/-! #### Event-level helpers: the local graph across the wall, dead rows, full availability -/

/-- R-LOC-2 corollary at the three local edges: each edge of `G[T]` toggles across the wall
(`LocalizationData.complement_on_triangle` at the three pairs). -/
theorem A2_edge_transport (hL : LocalizationData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) :
    (EdgeAB (geomAt E t' ht'.1) ((hs _).mp hef) ((hs _).mp heg) ↔
        ¬ EdgeAB (geomAt E t ht.1) hef heg) ∧
    (EdgeAC (geomAt E t' ht'.1) ((hs _).mp hef) ((hs _).mp hfg) ↔
        ¬ EdgeAC (geomAt E t ht.1) hef hfg) ∧
    (EdgeBC (geomAt E t' ht'.1) ((hs _).mp heg) ((hs _).mp hfg) ↔
        ¬ EdgeBC (geomAt E t ht.1) heg hfg) := by
  have hT : ∀ {i j : ZMod n} (h : IsCrossing (E.curve t) {i, j}),
      ({i, j} : Finset (ZMod n)) ∈ triangleSupports e f g → (xPair h).val ∈ triangleSupports e f g :=
    fun h hm => hm
  refine ⟨?_, ?_, ?_⟩
  · exact hL.complement_on_triangle t t' ht ht' hop hs (xPair hef) (xPair heg)
      (hT hef ((P1.mem_triangleSupports _).mpr (Or.inl rfl)))
      (hT heg ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))))
      (P1.xPair_ef_ne_eg hef heg hfg)
  · exact hL.complement_on_triangle t t' ht ht' hop hs (xPair hef) (xPair hfg)
      (hT hef ((P1.mem_triangleSupports _).mpr (Or.inl rfl)))
      (hT hfg ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))))
      (P1.xPair_ef_ne_fg hef heg hfg)
  · exact hL.complement_on_triangle t t' ht ht' hop hs (xPair heg) (xPair hfg)
      (hT heg ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))))
      (hT hfg ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))))
      (P1.xPair_eg_ne_fg hef heg hfg)

/-- The orbit is the same on the two sides: extreme at `t'` iff extreme at `t` (the complement of
`K3` is empty and conversely). -/
theorem A2_extremeLocal_transport (hL : LocalizationData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hef' : IsCrossing (E.curve t') {e, f}) (heg' : IsCrossing (E.curve t') {e, g})
    (hfg' : IsCrossing (E.curve t') {f, g}) :
    ExtremeLocal (geomAt E t' ht'.1) hef' heg' hfg' ↔ ExtremeLocal (geomAt E t ht.1) hef heg hfg := by
  obtain ⟨hAB, hAC, hBC⟩ := A2_edge_transport hL ht ht' hop hs hef heg hfg
  unfold ExtremeLocal
  rw [hAB, hAC, hBC]
  tauto

/-- The `K3` side faces the empty side (`ExtremeTransportData.graphs_complementary`, here from
row 164). -/
theorem A2_completeLocal_transport (hL : LocalizationData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    (hef' : IsCrossing (E.curve t') {e, f}) (heg' : IsCrossing (E.curve t') {e, g})
    (hfg' : IsCrossing (E.curve t') {f, g}) :
    (CompleteLocal (geomAt E t' ht'.1) hef' heg' hfg' ↔ EmptyLocal (geomAt E t ht.1) hef heg hfg) ∧
    (EmptyLocal (geomAt E t' ht'.1) hef' heg' hfg' ↔ CompleteLocal (geomAt E t ht.1) hef heg hfg) := by
  obtain ⟨hAB, hAC, hBC⟩ := A2_edge_transport hL ht ht' hop hs hef heg hfg
  unfold CompleteLocal EmptyLocal
  rw [hAB, hAC, hBC]
  tauto

/-- A row whose support contains two interlacing crossings is absent, hence `0`. -/
theorem A2_rowTerm_eq_zero_of_interlaces (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CV.Generic P)
    {S : Finset (Crossing P)} {x y : Crossing P} (hx : x ∈ S) (hy : y ∈ S) (hxy : x ≠ y)
    (h : GeometricInterlaces hG.crossingGeometry x y) : rowTerm hn hG S = 0 := by
  apply rowTerm_of_not_mem_Ind
  intro hS
  exact ((CV.mem_Ind_iff _ S).mp hS) x hx y hy hxy h

/-- In the generic orbit the local graph has an edge, so the row `Q ∪ T` is absent on both
sides: `T(Q ∪ T) = 0`. -/
theorem A2_rowTerm_triangle_eq_zero_of_generic (hn : 3 ≤ n) {P : LabelledTuple n}
    (hG : CV.Generic P) (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g})
    (hfg : IsCrossing P {f, g}) (hgen : ¬ ExtremeLocal hG.crossingGeometry hef heg hfg)
    (Q : Finset (Crossing P)) :
    rowTerm hn hG (Q ∪ {xPair hef, xPair heg, xPair hfg}) = 0 := by
  by_cases hAB : EdgeAB hG.crossingGeometry hef heg
  · exact A2_rowTerm_eq_zero_of_interlaces hn hG (by simp) (by simp)
      (P1.xPair_ef_ne_eg hef heg hfg) hAB
  by_cases hAC : EdgeAC hG.crossingGeometry hef hfg
  · exact A2_rowTerm_eq_zero_of_interlaces hn hG (by simp) (by simp)
      (P1.xPair_ef_ne_fg hef heg hfg) hAC
  by_cases hBC : EdgeBC hG.crossingGeometry heg hfg
  · exact A2_rowTerm_eq_zero_of_interlaces hn hG (by simp) (by simp)
      (P1.xPair_eg_ne_fg hef heg hfg) hBC
  exact absurd (Or.inr ⟨hAB, hAC, hBC⟩) hgen

/-- Availability `3` is full availability (`𝓐(Q) ⊆ T`, `|T| = 3`). -/
theorem A2_fullAvail_of_card_three (hL : LocalizationData E e f g δ) {t : E.Parameter}
    (ht : Punctured E δ t) (Q : Finset (Crossing (E.curve t)))
    (h3 : (avail (geomAt E t ht.1) e f g Q).card = 3) : FullAvail (geomAt E t ht.1) e f g Q := by
  obtain ⟨hef, heg, hfg⟩ := hL.triangle_crossings t ht
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    exact (F1.mem_triangleCrossings e f g x).mpr ((F1.mem_avail _ e f g Q x).mp hx).1
  · rw [h3, P1.triangleCrossings_card hef heg hfg]

/-- Full availability is carried across the wall (`FibrePartitionData.avail_same`). -/
theorem A2_fullAvail_transport (hF : FibrePartitionData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    FullAvail (geomAt E t' ht'.1) e f g (transportSupport hs Q) := by
  have hfull' : avail (geomAt E t ht.1) e f g Q = triangleCrossings (E.curve t) e f g := hfull
  show avail (geomAt E t' ht'.1) e f g (Q.map (crossingTransport hs).toEmbedding) = _
  rw [hF.avail_same t t' ht ht' hop hs Q hQ, hfull']
  exact A2_transportSupport_triangleCrossings hs e f g

/-- "`Φ(Q) = Σ_{J ⊆ T} T(Q ∪ J)`" at full availability, absent rows contributing `0`
(`localFibre Q ⊆ 𝒫(T)` and a `J ⊆ T` outside the fibre is dependent, so `Q ∪ J` is absent). -/
theorem A2_fibreTerm_eq_sum_powerset (hn : 3 ≤ n) {t : E.Parameter} (ht : t.val ≠ 0)
    {Q : Finset (Crossing (E.curve t))} (hfull : FullAvail (geomAt E t ht) e f g Q) :
    fibreTerm hn E e f g t ht Q =
      ∑ J ∈ (triangleCrossings (E.curve t) e f g).powerset,
        rowTerm hn (genericAt E t ht) (Q ∪ J) := by
  have hfull' : avail (geomAt E t ht) e f g Q = triangleCrossings (E.curve t) e f g := hfull
  unfold fibreTerm fibreSum
  apply Finset.sum_subset
  · intro J hJ
    rw [F1.mem_localFibre] at hJ
    rw [Finset.mem_powerset, ← hfull']
    exact hJ.2
  · intro J hJ hJn
    apply rowTerm_of_not_mem_Ind
    intro hQJ
    apply hJn
    rw [F1.mem_localFibre]
    refine ⟨?_, ?_⟩
    · rw [CV.mem_Ind_iff] at hQJ ⊢
      intro x hx y hy hxy
      exact hQJ x (Finset.mem_union_right _ hx) y (Finset.mem_union_right _ hy) hxy
    · rw [hfull']
      exact Finset.mem_powerset.mp hJ

/-- The far fibre sum over `Q` read on side `t'`, indexed by the subsets of the near triangle:
`Φ_{t'}(Q') = Σ_{J ⊆ T} T_{t'}(transport (Q ∪ J))`. -/
theorem A2_fibreTerm_far_eq_sum_powerset (hn : 3 ≤ n) (hF : FibrePartitionData E e f g δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) =
      ∑ J ∈ (triangleCrossings (E.curve t) e f g).powerset,
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ J)) := by
  rw [A2_fibreTerm_eq_sum_powerset hn ht'.1 (A2_fullAvail_transport hF ht ht' hop hs hQ hfull),
    ← A2_transportSupport_triangleCrossings hs e f g, A2_powerset_transport, Finset.sum_map]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [supportEmb_apply, A2_transportSupport_union]

/-- **The eight rows of a full-availability fibre** on one side:
`Φ(Q) = T(∅) + T(a) + T(b) + T(c) + T(ab) + T(ac) + T(bc) + T(abc)` (each `T(J) = rowTerm (Q ∪ J)`,
absent rows `0`). -/
theorem A2_fibreTerm_eq_eight (hn : 3 ≤ n) {t : E.Parameter} (ht : t.val ≠ 0)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    {Q : Finset (Crossing (E.curve t))} (hfull : FullAvail (geomAt E t ht) e f g Q) :
    fibreTerm hn E e f g t ht Q =
      rowTerm hn (genericAt E t ht) Q +
      rowTerm hn (genericAt E t ht) (Q ∪ {xPair hef}) +
      rowTerm hn (genericAt E t ht) (Q ∪ {xPair heg}) +
      rowTerm hn (genericAt E t ht) (Q ∪ {xPair hfg}) +
      rowTerm hn (genericAt E t ht) (Q ∪ {xPair hef, xPair heg}) +
      rowTerm hn (genericAt E t ht) (Q ∪ {xPair hef, xPair hfg}) +
      rowTerm hn (genericAt E t ht) (Q ∪ {xPair heg, xPair hfg}) +
      rowTerm hn (genericAt E t ht) (Q ∪ {xPair hef, xPair heg, xPair hfg}) := by
  rw [A2_fibreTerm_eq_sum_powerset hn ht hfull, A2_triangleCrossings_eq hef heg hfg,
    A2_sum_powerset_three (P1.xPair_ef_ne_eg hef heg hfg) (P1.xPair_ef_ne_fg hef heg hfg)
      (P1.xPair_eg_ne_fg hef heg hfg), Finset.union_empty]

/-- **The eight rows of the far fibre**, indexed by the near triangle. -/
theorem A2_fibreTerm_far_eq_eight (hn : 3 ≤ n) (hF : FibrePartitionData E e f g δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g})
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q) +
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef})) +
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg})) +
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg})) +
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef, xPair heg})) +
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef, xPair hfg})) +
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair heg, xPair hfg})) +
      rowTerm hn (genericAt E t' ht'.1)
        (transportSupport hs (Q ∪ {xPair hef, xPair heg, xPair hfg})) := by
  rw [A2_fibreTerm_far_eq_sum_powerset hn hF ht ht' hop hs hQ hfull,
    A2_triangleCrossings_eq hef heg hfg,
    A2_sum_powerset_three (P1.xPair_ef_ne_eg hef heg hfg) (P1.xPair_ef_ne_fg hef heg hfg)
      (P1.xPair_eg_ne_fg hef heg hfg), Finset.union_empty]

/-! #### The extreme orbit: rows 175, 176, 177 -/

/-- In the extreme orbit every pair row is `0` on either side: absent on the `K3` side
(`pair_absent_on_complete`), present but zero on the empty side (`pair_row_zero`). -/
theorem A2_extreme_pair_rows_zero (hn : 3 ≤ n) (hPZ : ExtremePairZeroData hn E e f g δ)
    {t : E.Parameter} (ht : Punctured E δ t)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hext : ExtremeLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair heg}) = 0 ∧
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair hfg}) = 0 ∧
    rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg, xPair hfg}) = 0 := by
  have hpair : ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g →
      J.card = 2 → rowTerm hn (genericAt E t ht.1) (Q ∪ J) = 0 := by
    intro J hJ hJ2
    rcases (extremeLocal_iff _ hef heg hfg).mp hext with hcomp | hempty
    · exact rowTerm_of_not_mem_Ind _ _
        (hPZ.pair_absent_on_complete t ht hef heg hfg hcomp Q hQ hfull J hJ hJ2)
    · exact hPZ.pair_row_zero t ht hef heg hfg hempty Q hQ hfull J hJ hJ2
  have hsub : ∀ x y : Crossing (E.curve t), x ∈ triangleCrossings (E.curve t) e f g →
      y ∈ triangleCrossings (E.curve t) e f g → ({x, y} : Finset _) ⊆ triangleCrossings (E.curve t) e f g := by
    intro x y hx hy z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have ha : xPair hef ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inl rfl)
  have hb : xPair heg ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inl rfl))
  have hc : xPair hfg ∈ triangleCrossings (E.curve t) e f g :=
    (P1.mem_triangleCrossings_iff hef heg hfg _).mpr (Or.inr (Or.inr rfl))
  exact ⟨hpair _ (hsub _ _ ha hb) (Finset.card_pair (P1.xPair_ef_ne_eg hef heg hfg)),
    hpair _ (hsub _ _ ha hc) (Finset.card_pair (P1.xPair_ef_ne_fg hef heg hfg)),
    hpair _ (hsub _ _ hb hc) (Finset.card_pair (P1.xPair_eg_ne_fg hef heg hfg))⟩

/-- **The fibre identity in the extreme orbit at full availability**: singletons by row 176, pairs
`0` on both sides by row 175, `∅`/`T` by the couple of row 177 (`T` absent on the `K3` side). -/
theorem A2_fibre_identity_extreme (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hF : FibrePartitionData E e f g δ) (hPZ : ExtremePairZeroData hn E e f g δ)
    (hET : ExtremeTransportData hn E e f g δ) (hES : ExtremeSelectedData hn E e f g δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hext : ExtremeLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  -- the far side's data
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hQ' := mem_outsideSupports_transport hF ht ht' hop hs hQ
  have hfull' := A2_fullAvail_transport hF ht ht' hop hs hQ hfull
  have hext' : ExtremeLocal (geomAt E t' ht'.1) hef' heg' hfg' :=
    (A2_extremeLocal_transport hL ht ht' hop hs hef heg hfg hef' heg' hfg').mpr hext
  rw [A2_fibreTerm_eq_eight hn ht.1 hef heg hfg hfull,
    A2_fibreTerm_far_eq_eight hn hF ht ht' hop hs hef heg hfg hQ hfull]
  -- singletons (row 176)
  have ha := hET.transport_x t t' ht ht' hop hs hef heg hfg hext Q hQ hfull
  have hb := hET.transport_y t t' ht ht' hop hs hef heg hfg hext Q hQ hfull
  have hc := hET.transport_z t t' ht ht' hop hs hef heg hfg hext Q hQ hfull
  -- pairs (row 175), both sides
  obtain ⟨hab, hac, hbc⟩ := A2_extreme_pair_rows_zero hn hPZ ht hef heg hfg hext hQ hfull
  obtain ⟨hab', hac', hbc'⟩ := A2_extreme_pair_rows_zero hn hPZ ht' hef' heg' hfg' hext' hQ' hfull'
  rw [← A2_transport_union_two hs Q hef heg] at hab'
  rw [← A2_transport_union_two hs Q hef hfg] at hac'
  rw [← A2_transport_union_two hs Q heg hfg] at hbc'
  -- `∅` and `T` (row 177), by which side is `K3`
  rcases (extremeLocal_iff _ hef heg hfg).mp hext with hcomp | hempty
  · -- `t` is the `K3` side: `T_t(∅) − T_t'(∅) = T_t'(T)`, `T_t(T) = 0`
    have hcouple := hES.couple t t' ht ht' hop hs hef heg hfg hcomp Q hQ hfull
    have hT : rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair heg, xPair hfg}) = 0 := by
      apply rowTerm_of_not_mem_Ind
      rw [← A2_triangleCrossings_eq hef heg hfg]
      exact hES.full_absent_on_complete t ht hef heg hfg hcomp Q
    rw [← A2_transport_union_triangle hs Q hef heg hfg] at hcouple
    linarith
  · -- `t'` is the `K3` side: the couple read from `t'`, `T_t'(T) = 0`
    have hcomp' : CompleteLocal (geomAt E t' ht'.1) hef' heg' hfg' :=
      (A2_completeLocal_transport hL ht ht' hop hs hef heg hfg hef' heg' hfg').1.mpr hempty
    have hcouple := hES.couple t' t ht' ht hop.symm hs' hef' heg' hfg' hcomp' _ hQ' hfull'
    rw [A2_transport_back hs hs' Q, A2_triangleCrossings_eq hef heg hfg] at hcouple
    have hT' : rowTerm hn (genericAt E t' ht'.1)
        (transportSupport hs (Q ∪ {xPair hef, xPair heg, xPair hfg})) = 0 := by
      apply rowTerm_of_not_mem_Ind
      rw [A2_transport_union_triangle hs Q hef heg hfg]
      exact hES.full_absent_on_complete t' ht' hef' heg' hfg' hcomp' _
    linarith

/-! #### The generic orbit: rows 172, 173, 174 (canonical branch `ac` and the relabelled `ab`, `bc`) -/

/-- **The fibre identity in the generic orbit, selected pair `ac`** (canonical branch, centre `b`):
`∅` by `empty_row`, `a`/`c` by `endpoint_rows_canonical`, `ab`/`bc` dead on both sides (`row_zero`),
`T` absent on both sides, `b`/`ac` by `couple_canonical` read from the two-edge side, the pair `ac`
being absent on the one-edge side. -/
theorem A2_fibre_identity_generic_ac (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hF : FibrePartitionData E e f g δ) (hG : GenericTableData E e f g δ)
    (hSel : GenericSelectorData hn E e f g δ) (hGT : GenericTransportData hn E e f g δ)
    (hGS : GenericSelectedData hn E e f g δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hgen : ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg)
    (hsel : SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g))
    (hnAB : ¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g))
    (hnBC : ¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g))
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hQ' := mem_outsideSupports_transport hF ht ht' hop hs hQ
  have hfull' := A2_fullAvail_transport hF ht ht' hop hs hQ hfull
  have hgen' : ¬ ExtremeLocal (geomAt E t' ht'.1) hef' heg' hfg' := fun h =>
    hgen ((A2_extremeLocal_transport hL ht ht' hop hs hef heg hfg hef' heg' hfg').mp h)
  have hsg := (hG.chamber_change t t' ht ht' hop).2.1
  obtain ⟨hAB, hAC, hBC⟩ := A2_edge_transport hL ht ht' hop hs hef heg hfg
  have hnAB' : ¬ SelectedAB (strandSign (E.curve t') e f) (strandSign (E.curve t') e g) := by
    rw [hsg.1, hsg.2.1]; exact hnAB
  have hnBC' : ¬ SelectedBC (strandSign (E.curve t') e g) (strandSign (E.curve t') f g) := by
    rw [hsg.2.1, hsg.2.2]; exact hnBC
  rw [A2_fibreTerm_eq_eight hn ht.1 hef heg hfg hfull,
    A2_fibreTerm_far_eq_eight hn hF ht ht' hop hs hef heg hfg hQ hfull]
  -- `∅` (173) and `T` (absent on both sides)
  have h0 := hGT.empty_row t t' ht ht' hop hs hef heg hfg hgen Q hQ hfull
  have habc := A2_rowTerm_triangle_eq_zero_of_generic hn (genericAt E t ht.1) hef heg hfg hgen Q
  have habc' : rowTerm hn (genericAt E t' ht'.1)
      (transportSupport hs (Q ∪ {xPair hef, xPair heg, xPair hfg})) = 0 := by
    rw [A2_transport_union_triangle hs Q hef heg hfg, A2_triangleCrossings_eq hef' heg' hfg']
    exact A2_rowTerm_triangle_eq_zero_of_generic hn (genericAt E t' ht'.1) hef' heg' hfg' hgen' _
  -- the endpoints `a`, `c` (173) in the canonical branch `s_a = s_b = s_c`
  have hcan := (hGT.canonical_branch t ht hef heg hfg hgen).mp hsel
  obtain ⟨ha, hc⟩ :=
    hGT.endpoint_rows_canonical t t' ht ht' hop hs hef heg hfg hgen hcan.1 hcan.2 Q hQ hfull
  -- the nonselected pairs `ab`, `bc` (172), both sides
  have hab := (hSel.row_zero t ht hef heg hfg hgen Q hQ hfull).1 hnAB
  have hbc := (hSel.row_zero t ht hef heg hfg hgen Q hQ hfull).2.2 hnBC
  have hab' := (hSel.row_zero t' ht' hef' heg' hfg' hgen' _ hQ' hfull').1 hnAB'
  have hbc' := (hSel.row_zero t' ht' hef' heg' hfg' hgen' _ hQ' hfull').2.2 hnBC'
  rw [← A2_transport_union_two hs Q hef heg] at hab'
  rw [← A2_transport_union_two hs Q heg hfg] at hbc'
  -- the couple `b` / `ac` (174), read from the two-edge side
  rcases (hG.selected_is_graph_selected t ht hef heg hfg hgen).1.mp hsel with
    ⟨hAB2, hBC2⟩ | ⟨hAC2, hnAB2, hnBC2⟩
  · have hcouple :=
      hGS.couple_canonical t t' ht ht' hop hs hef heg hfg hgen hcan.1 hcan.2 hAB2 hBC2 Q hQ hfull
    have hnAC2 : ¬ EdgeAC (geomAt E t ht.1) hef hfg := fun h => hgen (Or.inl ⟨hAB2, h, hBC2⟩)
    have hac' : rowTerm hn (genericAt E t' ht'.1)
        (transportSupport hs (Q ∪ {xPair hef, xPair hfg})) = 0 := by
      rw [A2_transport_union_two hs Q hef hfg]
      exact A2_rowTerm_eq_zero_of_interlaces hn _ (by simp) (by simp)
        (P1.xPair_ef_ne_fg hef' heg' hfg') (hAC.mpr hnAC2)
    linarith
  · have hAB' := hAB.mpr hnAB2
    have hBC' := hBC.mpr hnBC2
    have hcan' : strandSign (E.curve t') e f = strandSign (E.curve t') e g ∧
        strandSign (E.curve t') e g = strandSign (E.curve t') f g := by
      rw [hsg.1, hsg.2.1, hsg.2.2]; exact hcan
    have hcouple := hGS.couple_canonical t' t ht' ht hop.symm hs' hef' heg' hfg' hgen' hcan'.1 hcan'.2
      hAB' hBC' _ hQ' hfull'
    rw [← A2_transport_union_one hs Q heg, A2_transport_back hs hs',
      ← A2_transport_union_two hs Q hef hfg] at hcouple
    have hac : rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair hfg}) = 0 :=
      A2_rowTerm_eq_zero_of_interlaces hn _ (by simp) (by simp) (P1.xPair_ef_ne_fg hef heg hfg) hAC2
    linarith

/-- **The fibre identity in the generic orbit, selected pair `ab`** (relabelled branch, centre `c`,
two-edge side `ac, bc`). -/
theorem A2_fibre_identity_generic_ab (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hF : FibrePartitionData E e f g δ) (hG : GenericTableData E e f g δ)
    (hSel : GenericSelectorData hn E e f g δ) (hGT : GenericTransportData hn E e f g δ)
    (hGS : GenericSelectedData hn E e f g δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hgen : ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg)
    (hsel : SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g))
    (hnAC : ¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g))
    (hnBC : ¬ SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g))
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hQ' := mem_outsideSupports_transport hF ht ht' hop hs hQ
  have hfull' := A2_fullAvail_transport hF ht ht' hop hs hQ hfull
  have hgen' : ¬ ExtremeLocal (geomAt E t' ht'.1) hef' heg' hfg' := fun h =>
    hgen ((A2_extremeLocal_transport hL ht ht' hop hs hef heg hfg hef' heg' hfg').mp h)
  have hsg := (hG.chamber_change t t' ht ht' hop).2.1
  obtain ⟨hAB, hAC, hBC⟩ := A2_edge_transport hL ht ht' hop hs hef heg hfg
  have hnAC' : ¬ SelectedAC (strandSign (E.curve t') e f) (strandSign (E.curve t') f g) := by
    rw [hsg.1, hsg.2.2]; exact hnAC
  have hnBC' : ¬ SelectedBC (strandSign (E.curve t') e g) (strandSign (E.curve t') f g) := by
    rw [hsg.2.1, hsg.2.2]; exact hnBC
  rw [A2_fibreTerm_eq_eight hn ht.1 hef heg hfg hfull,
    A2_fibreTerm_far_eq_eight hn hF ht ht' hop hs hef heg hfg hQ hfull]
  have h0 := hGT.empty_row t t' ht ht' hop hs hef heg hfg hgen Q hQ hfull
  have habc := A2_rowTerm_triangle_eq_zero_of_generic hn (genericAt E t ht.1) hef heg hfg hgen Q
  have habc' : rowTerm hn (genericAt E t' ht'.1)
      (transportSupport hs (Q ∪ {xPair hef, xPair heg, xPair hfg})) = 0 := by
    rw [A2_transport_union_triangle hs Q hef heg hfg, A2_triangleCrossings_eq hef' heg' hfg']
    exact A2_rowTerm_triangle_eq_zero_of_generic hn (genericAt E t' ht'.1) hef' heg' hfg' hgen' _
  -- the endpoints `a`, `b`
  obtain ⟨ha, hb⟩ :=
    (hGT.endpoint_rows_relabelled t t' ht ht' hop hs hef heg hfg hgen Q hQ hfull).1 hsel
  -- the nonselected pairs `ac`, `bc`, both sides
  have hac := (hSel.row_zero t ht hef heg hfg hgen Q hQ hfull).2.1 hnAC
  have hbc := (hSel.row_zero t ht hef heg hfg hgen Q hQ hfull).2.2 hnBC
  have hac' := (hSel.row_zero t' ht' hef' heg' hfg' hgen' _ hQ' hfull').2.1 hnAC'
  have hbc' := (hSel.row_zero t' ht' hef' heg' hfg' hgen' _ hQ' hfull').2.2 hnBC'
  rw [← A2_transport_union_two hs Q hef hfg] at hac'
  rw [← A2_transport_union_two hs Q heg hfg] at hbc'
  -- the couple `c` / `ab`
  rcases (hG.selected_is_graph_selected t ht hef heg hfg hgen).2.1.mp hsel with
    ⟨hAC2, hBC2⟩ | ⟨hAB2, hnAC2, hnBC2⟩
  · have hcouple :=
      (hGS.couple_relabelled t t' ht ht' hop hs hef heg hfg hgen Q hQ hfull).1 hsel hAC2 hBC2
    have hnAB2 : ¬ EdgeAB (geomAt E t ht.1) hef heg := fun h => hgen (Or.inl ⟨h, hAC2, hBC2⟩)
    have hab' : rowTerm hn (genericAt E t' ht'.1)
        (transportSupport hs (Q ∪ {xPair hef, xPair heg})) = 0 := by
      rw [A2_transport_union_two hs Q hef heg]
      exact A2_rowTerm_eq_zero_of_interlaces hn _ (by simp) (by simp)
        (P1.xPair_ef_ne_eg hef' heg' hfg') (hAB.mpr hnAB2)
    linarith
  · have hAC' := hAC.mpr hnAC2
    have hBC' := hBC.mpr hnBC2
    have hsel' : SelectedAB (strandSign (E.curve t') e f) (strandSign (E.curve t') e g) := by
      rw [hsg.1, hsg.2.1]; exact hsel
    have hcouple := (hGS.couple_relabelled t' t ht' ht hop.symm hs' hef' heg' hfg' hgen' _ hQ'
      hfull').1 hsel' hAC' hBC'
    rw [← A2_transport_union_one hs Q hfg, A2_transport_back hs hs',
      ← A2_transport_union_two hs Q hef heg] at hcouple
    have hab : rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef, xPair heg}) = 0 :=
      A2_rowTerm_eq_zero_of_interlaces hn _ (by simp) (by simp) (P1.xPair_ef_ne_eg hef heg hfg) hAB2
    linarith

/-- **The fibre identity in the generic orbit, selected pair `bc`** (relabelled branch, centre `a`,
two-edge side `ab, ac`). -/
theorem A2_fibre_identity_generic_bc (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hF : FibrePartitionData E e f g δ) (hG : GenericTableData E e f g δ)
    (hSel : GenericSelectorData hn E e f g δ) (hGT : GenericTransportData hn E e f g δ)
    (hGS : GenericSelectedData hn E e f g δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hgen : ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg)
    (hsel : SelectedBC (strandSign (E.curve t) e g) (strandSign (E.curve t) f g))
    (hnAB : ¬ SelectedAB (strandSign (E.curve t) e f) (strandSign (E.curve t) e g))
    (hnAC : ¬ SelectedAC (strandSign (E.curve t) e f) (strandSign (E.curve t) f g))
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  have hef' : IsCrossing (E.curve t') {e, f} := (hs _).mp hef
  have heg' : IsCrossing (E.curve t') {e, g} := (hs _).mp heg
  have hfg' : IsCrossing (E.curve t') {f, g} := (hs _).mp hfg
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hQ' := mem_outsideSupports_transport hF ht ht' hop hs hQ
  have hfull' := A2_fullAvail_transport hF ht ht' hop hs hQ hfull
  have hgen' : ¬ ExtremeLocal (geomAt E t' ht'.1) hef' heg' hfg' := fun h =>
    hgen ((A2_extremeLocal_transport hL ht ht' hop hs hef heg hfg hef' heg' hfg').mp h)
  have hsg := (hG.chamber_change t t' ht ht' hop).2.1
  obtain ⟨hAB, hAC, hBC⟩ := A2_edge_transport hL ht ht' hop hs hef heg hfg
  have hnAB' : ¬ SelectedAB (strandSign (E.curve t') e f) (strandSign (E.curve t') e g) := by
    rw [hsg.1, hsg.2.1]; exact hnAB
  have hnAC' : ¬ SelectedAC (strandSign (E.curve t') e f) (strandSign (E.curve t') f g) := by
    rw [hsg.1, hsg.2.2]; exact hnAC
  rw [A2_fibreTerm_eq_eight hn ht.1 hef heg hfg hfull,
    A2_fibreTerm_far_eq_eight hn hF ht ht' hop hs hef heg hfg hQ hfull]
  have h0 := hGT.empty_row t t' ht ht' hop hs hef heg hfg hgen Q hQ hfull
  have habc := A2_rowTerm_triangle_eq_zero_of_generic hn (genericAt E t ht.1) hef heg hfg hgen Q
  have habc' : rowTerm hn (genericAt E t' ht'.1)
      (transportSupport hs (Q ∪ {xPair hef, xPair heg, xPair hfg})) = 0 := by
    rw [A2_transport_union_triangle hs Q hef heg hfg, A2_triangleCrossings_eq hef' heg' hfg']
    exact A2_rowTerm_triangle_eq_zero_of_generic hn (genericAt E t' ht'.1) hef' heg' hfg' hgen' _
  -- the endpoints `b`, `c`
  obtain ⟨hb, hc⟩ :=
    (hGT.endpoint_rows_relabelled t t' ht ht' hop hs hef heg hfg hgen Q hQ hfull).2 hsel
  -- the nonselected pairs `ab`, `ac`, both sides
  have hab := (hSel.row_zero t ht hef heg hfg hgen Q hQ hfull).1 hnAB
  have hac := (hSel.row_zero t ht hef heg hfg hgen Q hQ hfull).2.1 hnAC
  have hab' := (hSel.row_zero t' ht' hef' heg' hfg' hgen' _ hQ' hfull').1 hnAB'
  have hac' := (hSel.row_zero t' ht' hef' heg' hfg' hgen' _ hQ' hfull').2.1 hnAC'
  rw [← A2_transport_union_two hs Q hef heg] at hab'
  rw [← A2_transport_union_two hs Q hef hfg] at hac'
  -- the couple `a` / `bc`
  rcases (hG.selected_is_graph_selected t ht hef heg hfg hgen).2.2.mp hsel with
    ⟨hAB2, hAC2⟩ | ⟨hBC2, hnAB2, hnAC2⟩
  · have hcouple :=
      (hGS.couple_relabelled t t' ht ht' hop hs hef heg hfg hgen Q hQ hfull).2 hsel hAB2 hAC2
    have hnBC2 : ¬ EdgeBC (geomAt E t ht.1) heg hfg := fun h => hgen (Or.inl ⟨hAB2, hAC2, h⟩)
    have hbc' : rowTerm hn (genericAt E t' ht'.1)
        (transportSupport hs (Q ∪ {xPair heg, xPair hfg})) = 0 := by
      rw [A2_transport_union_two hs Q heg hfg]
      exact A2_rowTerm_eq_zero_of_interlaces hn _ (by simp) (by simp)
        (P1.xPair_eg_ne_fg hef' heg' hfg') (hBC.mpr hnBC2)
    linarith
  · have hAB' := hAB.mpr hnAB2
    have hAC' := hAC.mpr hnAC2
    have hsel' : SelectedBC (strandSign (E.curve t') e g) (strandSign (E.curve t') f g) := by
      rw [hsg.2.1, hsg.2.2]; exact hsel
    have hcouple := (hGS.couple_relabelled t' t ht' ht hop.symm hs' hef' heg' hfg' hgen' _ hQ'
      hfull').2 hsel' hAB' hAC'
    rw [← A2_transport_union_one hs Q hef, A2_transport_back hs hs',
      ← A2_transport_union_two hs Q heg hfg] at hcouple
    have hbc : rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair heg, xPair hfg}) = 0 :=
      A2_rowTerm_eq_zero_of_interlaces hn _ (by simp) (by simp) (P1.xPair_eg_ne_fg hef heg hfg) hBC2
    linarith

/-- **The fibre identity in the generic orbit at full availability**: by the selected pair
(`GenericSelectorData.selected_pair_unique`). -/
theorem A2_fibre_identity_generic (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hF : FibrePartitionData E e f g δ) (hG : GenericTableData E e f g δ)
    (hSel : GenericSelectorData hn E e f g δ) (hGT : GenericTransportData hn E e f g δ)
    (hGS : GenericSelectedData hn E e f g δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
    (hfg : IsCrossing (E.curve t) {f, g}) (hgen : ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  rcases hSel.selected_pair_unique t ht hef heg hfg hgen with
    ⟨hAB, hnAC, hnBC⟩ | ⟨hnAB, hAC, hnBC⟩ | ⟨hnAB, hnAC, hBC⟩
  · exact A2_fibre_identity_generic_ab hn hL hF hG hSel hGT hGS ht ht' hop hs hef heg hfg hgen
      hAB hnAC hnBC hQ hfull
  · exact A2_fibre_identity_generic_ac hn hL hF hG hSel hGT hGS ht ht' hop hs hef heg hfg hgen
      hAC hnAB hnBC hQ hfull
  · exact A2_fibre_identity_generic_bc hn hL hF hG hSel hGT hGS ht ht' hop hs hef heg hfg hgen
      hBC hnAB hnAC hQ hfull

/-! #### The assembly -/

/-- **The fibre identity at full availability** (availability `3`), by orbit. -/
theorem A2_fibre_identity_full (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hF : FibrePartitionData E e f g δ) (hG : GenericTableData E e f g δ)
    (hSel : GenericSelectorData hn E e f g δ) (hGT : GenericTransportData hn E e f g δ)
    (hGS : GenericSelectedData hn E e f g δ) (hPZ : ExtremePairZeroData hn E e f g δ)
    (hET : ExtremeTransportData hn E e f g δ) (hES : ExtremeSelectedData hn E e f g δ)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) :
    fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  obtain ⟨hef, heg, hfg⟩ := hL.triangle_crossings t ht
  by_cases hext : ExtremeLocal (geomAt E t ht.1) hef heg hfg
  · exact A2_fibre_identity_extreme hn hL hF hPZ hET hES ht ht' hop hs hef heg hfg hext hQ hfull
  · exact A2_fibre_identity_generic hn hL hF hG hSel hGT hGS ht ht' hop hs hef heg hfg hext hQ hfull

/-- **The fibre identities (4), `Φ_+(Q) = Φ_-(Q)` for every outside independent `Q`** — the clause
`CvTheoremData.fibre_identities`, assembled from the bundles of rows 170, 172–177 and the accepted
cores 164, 171, 172-table at one radius: availability `0`/`1` by row 170 (`fibre_identity`),
availability `3` = full availability (`A2_fullAvail_of_card_three`) by the eight-row match
(`A2_fibre_identity_full`); `FibrePartitionData.avail_card` excludes `2`. -/
theorem A2_fibre_identities (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hF : FibrePartitionData E e f g δ) (hG : GenericTableData E e f g δ)
    (hAv : AvailabilityZeroOneData hn E e f g δ) (hSel : GenericSelectorData hn E e f g δ)
    (hGT : GenericTransportData hn E e f g δ) (hGS : GenericSelectedData hn E e f g δ)
    (hPZ : ExtremePairZeroData hn E e f g δ) (hET : ExtremeTransportData hn E e f g δ)
    (hES : ExtremeSelectedData hn E e f g δ) :
    ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      fibreTerm hn E e f g t ht.1 Q = fibreTerm hn E e f g t' ht'.1 (transportSupport hs Q) := by
  intro t t' ht ht' hop hs Q hQ
  rcases hF.avail_card t ht Q hQ with h3 | h1 | h0
  · exact A2_fibre_identity_full hn hL hF hG hSel hGT hGS hPZ hET hES ht ht' hop hs hQ
      (A2_fullAvail_of_card_three hL ht Q h3)
  · exact hAv.fibre_identity t t' ht ht' hop hs Q hQ (Or.inr h1)
  · exact hAv.fibre_identity t t' ht ht' hop hs Q hQ (Or.inl h0)

/-- **The bundle of row 178 at one radius** from the accepted cores and the bundles of rows 170,
172–177 (`CvTheoremData.of_fibre_identities` at `A2_fibre_identities`). -/
theorem A2_cvTheoremData (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hF : FibrePartitionData E e f g δ) (hG : GenericTableData E e f g δ)
    (hAv : AvailabilityZeroOneData hn E e f g δ) (hSel : GenericSelectorData hn E e f g δ)
    (hGT : GenericTransportData hn E e f g δ) (hGS : GenericSelectedData hn E e f g δ)
    (hPZ : ExtremePairZeroData hn E e f g δ) (hET : ExtremeTransportData hn E e f g δ)
    (hES : ExtremeSelectedData hn E e f g δ) : CvTheoremData hn E e f g δ :=
  CvTheoremData.of_fibre_identities hn hL hF
    (A2_fibre_identities hn hL hF hG hAv hSel hGT hGS hPZ hET hES)

/-! #### Radius restriction of the bundles (for the common radius of the assembly) -/

/-- `FibrePartitionData` restricts to a smaller punctured radius. -/
theorem A2_fibrePartitionData_mono {δ' : ℝ} (h : δ' ≤ δ) (hF : FibrePartitionData E e f g δ) :
    FibrePartitionData E e f g δ' where
  graph_on_W_same t t' ht ht' :=
    hF.graph_on_W_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  W_to_T_same t t' ht ht' := hF.W_to_T_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  avail_same t t' ht ht' := hF.avail_same t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  decompose t ht := hF.decompose t (F1.punctured_mono h ht)
  compose t ht := hF.compose t (F1.punctured_mono h ht)
  bijection t ht := hF.bijection t (F1.punctured_mono h ht)
  state_sum_partition t ht := hF.state_sum_partition t (F1.punctured_mono h ht)
  avail_card t ht := hF.avail_card t (F1.punctured_mono h ht)

/-- `GenericTableData` restricts to a smaller punctured radius. -/
theorem A2_genericTableData_mono {δ' : ℝ} (h : δ' ≤ δ) (hG : GenericTableData E e f g δ) :
    GenericTableData E e f g δ' where
  nonzero t ht := hG.nonzero t (F1.punctured_mono h ht)
  cramer t ht := hG.cramer t (F1.punctured_mono h ht)
  sign_vector t ht := hG.sign_vector t (F1.punctured_mono h ht)
  edges_iff t ht := hG.edges_iff t (F1.punctured_mono h ht)
  chamber_change t t' ht ht' :=
    hG.chamber_change t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  extreme_iff_orders t ht := hG.extreme_iff_orders t (F1.punctured_mono h ht)
  extreme_iff_alternating t ht := hG.extreme_iff_alternating t (F1.punctured_mono h ht)
  generic_iff_nonalternating t ht := hG.generic_iff_nonalternating t (F1.punctured_mono h ht)
  branch_count := hG.branch_count
  selected_unique := hG.selected_unique
  selected_is_graph_selected t ht := hG.selected_is_graph_selected t (F1.punctured_mono h ht)
  local_word t ht := hG.local_word t (F1.punctured_mono h ht)
  canonical_words t ht := hG.canonical_words t (F1.punctured_mono h ht)
  local_supports t ht := hG.local_supports t (F1.punctured_mono h ht)
  local_undominated t ht := hG.local_undominated t (F1.punctured_mono h ht)
  mask_sharpening t ht := hG.mask_sharpening t (F1.punctured_mono h ht)
  skeleton_table := hG.skeleton_table
  successor_table := hG.successor_table
  residual_table := hG.residual_table

/-- `AvailabilityZeroOneData` restricts to a smaller punctured radius. -/
theorem A2_availabilityZeroOneData_mono (hn : 3 ≤ n) {δ' : ℝ} (h : δ' ≤ δ)
    (hA : AvailabilityZeroOneData hn E e f g δ) : AvailabilityZeroOneData hn E e f g δ' where
  fibre_zero t ht := hA.fibre_zero t (F1.punctured_mono h ht)
  fibre_one t ht := hA.fibre_one t (F1.punctured_mono h ht)
  fibre_correspond t t' ht ht' :=
    hA.fibre_correspond t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  summand_transport t t' ht ht' :=
    hA.summand_transport t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  summands_agree t t' ht ht' :=
    hA.summands_agree t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  fibre_identity t t' ht ht' :=
    hA.fibre_identity t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')

/-- `GenericSelectorData` restricts to a smaller punctured radius. -/
theorem A2_genericSelectorData_mono (hn : 3 ≤ n) {δ' : ℝ} (h : δ' ≤ δ)
    (hS : GenericSelectorData hn E e f g δ) : GenericSelectorData hn E e f g δ' where
  selected_pair_unique t ht := hS.selected_pair_unique t (F1.punctured_mono h ht)
  corner_signs_opposite t ht := hS.corner_signs_opposite t (F1.punctured_mono h ht)
  mixed_carrier t ht := hS.mixed_carrier t (F1.punctured_mono h ht)
  selector_zero t ht := hS.selector_zero t (F1.punctured_mono h ht)
  row_zero t ht := hS.row_zero t (F1.punctured_mono h ht)

/-- `GenericTransportData` restricts to a smaller punctured radius. -/
theorem A2_genericTransportData_mono (hn : 3 ≤ n) {δ' : ℝ} (h : δ' ≤ δ)
    (hT : GenericTransportData hn E e f g δ) : GenericTransportData hn E e f g δ' where
  canonical_branch t ht := hT.canonical_branch t (F1.punctured_mono h ht)
  empty_row t t' ht ht' := hT.empty_row t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  endpoint_rows_canonical t t' ht ht' :=
    hT.endpoint_rows_canonical t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  endpoint_rows_relabelled t t' ht ht' :=
    hT.endpoint_rows_relabelled t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')

/-- `GenericSelectedData` restricts to a smaller punctured radius. -/
theorem A2_genericSelectedData_mono (hn : 3 ≤ n) {δ' : ℝ} (h : δ' ≤ δ)
    (hS : GenericSelectedData hn E e f g δ) : GenericSelectedData hn E e f g δ' where
  couple_canonical t t' ht ht' :=
    hS.couple_canonical t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  couple_relabelled t t' ht ht' :=
    hS.couple_relabelled t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')

/-- `ExtremePairZeroData` restricts to a smaller punctured radius. -/
theorem A2_extremePairZeroData_mono (hn : 3 ≤ n) {δ' : ℝ} (h : δ' ≤ δ)
    (hP : ExtremePairZeroData hn E e f g δ) : ExtremePairZeroData hn E e f g δ' where
  pair_absent_on_complete t ht := hP.pair_absent_on_complete t (F1.punctured_mono h ht)
  pair_present_on_empty t ht := hP.pair_present_on_empty t (F1.punctured_mono h ht)
  third_singleton_piece t ht := hP.third_singleton_piece t (F1.punctured_mono h ht)
  pair_row_zero t ht := hP.pair_row_zero t (F1.punctured_mono h ht)

/-- `ExtremeTransportData` restricts to a smaller punctured radius. -/
theorem A2_extremeTransportData_mono (hn : 3 ≤ n) {δ' : ℝ} (h : δ' ≤ δ)
    (hT : ExtremeTransportData hn E e f g δ) : ExtremeTransportData hn E e f g δ' where
  singleton_rows_present t ht := hT.singleton_rows_present t (F1.punctured_mono h ht)
  graphs_complementary t t' ht ht' :=
    hT.graphs_complementary t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  sign_branch t ht := hT.sign_branch t (F1.punctured_mono h ht)
  transport_x t t' ht ht' := hT.transport_x t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  transport_y t t' ht ht' := hT.transport_y t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')
  transport_z t t' ht ht' := hT.transport_z t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')

/-- `ExtremeSelectedData` restricts to a smaller punctured radius. -/
theorem A2_extremeSelectedData_mono (hn : 3 ≤ n) {δ' : ℝ} (h : δ' ≤ δ)
    (hS : ExtremeSelectedData hn E e f g δ) : ExtremeSelectedData hn E e f g δ' where
  full_present_on_empty t ht := hS.full_present_on_empty t (F1.punctured_mono h ht)
  full_absent_on_complete t ht := hS.full_absent_on_complete t (F1.punctured_mono h ht)
  couple t t' ht ht' := hS.couple t t' (F1.punctured_mono h ht) (F1.punctured_mono h ht')

/-- **The existential of row 178 from the existentials of rows 164, 171, 172-table, 170, 172–177**
(each "on some punctured neighbourhood"): the common radius is the minimum of the ten radii. -/
theorem A2_cvTheoremData_of_rows (hn : 3 ≤ n)
    (h164 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ LocalizationData E e f g δ)
    (h171 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ FibrePartitionData E e f g δ)
    (h172t : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTableData E e f g δ)
    (h170 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AvailabilityZeroOneData hn E e f g δ)
    (h172 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectorData hn E e f g δ)
    (h173 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ)
    (h174 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ)
    (h175 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ)
    (h176 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ)
    (h177 : ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ CvTheoremData hn E e f g δ := by
  obtain ⟨δ1, hp1, hr1, hL⟩ := h164
  obtain ⟨δ2, hp2, -, hF⟩ := h171
  obtain ⟨δ3, hp3, -, hG⟩ := h172t
  obtain ⟨δ4, hp4, -, hAv⟩ := h170
  obtain ⟨δ5, hp5, -, hSel⟩ := h172
  obtain ⟨δ6, hp6, -, hGT⟩ := h173
  obtain ⟨δ7, hp7, -, hGS⟩ := h174
  obtain ⟨δ8, hp8, -, hPZ⟩ := h175
  obtain ⟨δ9, hp9, -, hET⟩ := h176
  obtain ⟨δ10, hp10, -, hES⟩ := h177
  set δ := min δ1 (min δ2 (min δ3 (min δ4 (min δ5 (min δ6 (min δ7 (min δ8 (min δ9 δ10))))))))
    with hδ
  have hδ1 : δ ≤ δ1 := by simp only [hδ, min_le_iff, le_refl, true_or]
  have hδ2 : δ ≤ δ2 := by simp only [hδ, min_le_iff, le_refl, true_or, or_true]
  have hδ3 : δ ≤ δ3 := by simp only [hδ, min_le_iff, le_refl, true_or, or_true]
  have hδ4 : δ ≤ δ4 := by simp only [hδ, min_le_iff, le_refl, true_or, or_true]
  have hδ5 : δ ≤ δ5 := by simp only [hδ, min_le_iff, le_refl, true_or, or_true]
  have hδ6 : δ ≤ δ6 := by simp only [hδ, min_le_iff, le_refl, true_or, or_true]
  have hδ7 : δ ≤ δ7 := by simp only [hδ, min_le_iff, le_refl, true_or, or_true]
  have hδ8 : δ ≤ δ8 := by simp only [hδ, min_le_iff, le_refl, true_or, or_true]
  have hδ9 : δ ≤ δ9 := by simp only [hδ, min_le_iff, le_refl, true_or, or_true]
  have hδ10 : δ ≤ δ10 := by simp only [hδ, min_le_iff, le_refl, or_true]
  refine ⟨δ, ?_, hδ1.trans hr1, ?_⟩
  · simp only [hδ, lt_min_iff]
    exact ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10⟩
  · exact A2_cvTheoremData hn (F1.localizationData_mono hδ1 hL) (A2_fibrePartitionData_mono hδ2 hF)
      (A2_genericTableData_mono hδ3 hG) (A2_availabilityZeroOneData_mono hn hδ4 hAv)
      (A2_genericSelectorData_mono hn hδ5 hSel) (A2_genericTransportData_mono hn hδ6 hGT)
      (A2_genericSelectedData_mono hn hδ7 hGS) (A2_extremePairZeroData_mono hn hδ8 hPZ)
      (A2_extremeTransportData_mono hn hδ9 hET) (A2_extremeSelectedData_mono hn hδ10 hES)

end A2

/-- **`CvRNear` from the seven row theorems 170, 172–177** (each in its fixed row shape, so that the
assembler writes `A2_cvRNear_of_rows availability_zero_one generic_selector generic_transport
generic_selected extreme_pair_zero extreme_transport extreme_selected` once those rows are proved;
the accepted cores `localization`, `fibre_partition`, `generic_table` are consumed directly). This is
the `cv_R_near` of DECISION_FINAL.md R6; `RProof.cv_R` is then
`hyp_R_of_near_of_chamberinv (A2_cvRNear_of_rows …) chamberinv_ii` (unit U-CV). -/
theorem A2_cvRNear_of_rows
    (h170 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AvailabilityZeroOneData hn E e f g δ)
    (h172 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectorData hn E e f g δ)
    (h173 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData hn E e f g δ)
    (h174 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData hn E e f g δ)
    (h175 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData hn E e f g δ)
    (h176 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ)
    (h177 : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData hn E e f g δ) :
    CvRNear := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  exact A2_cvTheoremData_of_rows hn (localization E e f g h3 h4e h4f h4g hE)
    (fibre_partition E e f g h3 h4e h4f h4g hE) (generic_table E e f g h3 h4e h4f h4g hE)
    (h170 n hn E e f g h3 h4e h4f h4g hE) (h172 n hn E e f g h3 h4e h4f h4g hE)
    (h173 n hn E e f g h3 h4e h4f h4g hE) (h174 n hn E e f g h3 h4e h4f h4g hE)
    (h175 n hn E e f g h3 h4e h4f h4g hE) (h176 n hn E e f g h3 h4e h4f h4g hE)
    (h177 n hn E e f g h3 h4e h4f h4g hE)


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
