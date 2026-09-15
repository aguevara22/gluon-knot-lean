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
