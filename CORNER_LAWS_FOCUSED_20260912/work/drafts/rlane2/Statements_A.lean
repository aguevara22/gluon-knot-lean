import RProof.Cores
import CV.X1
import CV.ChamberInvII
import CV.SelectorA

/-! # R lane, part 2 — statements of the nine remaining obligation rows (TAG A, spec-first)

Draft written 2026-09-14 by a Claude Code architect subagent of the pod executor for the R-lane
statement panel (work/drafts/rlane2/). Companion notes: `NOTES_A.md` (clause map with source
citations, readings, dependencies, provable-now verdicts, unit split, risks). Checked with
`cd work/lean && lake env lean ../drafts/rlane2/Statements_A.lean`: the only `sorry`s are the nine
row theorems; every auxiliary is proved or a definition.

Rows (blueprint/ORDER.md 170–186; fixed names, work/lean/axiom-policy.json `targets`):
`R:exterior → RProof.exterior`, `R:availability_0_1 → RProof.availability_zero_one`,
`R:generic_selector → RProof.generic_selector`, `R:generic_transport → RProof.generic_transport`,
`R:generic_selected → RProof.generic_selected`, `R:extreme_pair_zero → RProof.extreme_pair_zero`,
`R:extreme_transport → RProof.extreme_transport`, `R:extreme_selected → RProof.extreme_selected`,
`R:cv_theorem → RProof.cv_R` (of type `CV.hyp_R`, CV:ax:R, DECISION_FINAL.md R6).

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
  `CV.pieceLabels`; the carriers `SM.GeoCarrier.GeoComponent`, `geoOwner` (def:flat-carriers).
* The total summand `CV.X1Summand hn hG S` (CV/ChamberInvII.lean): `wind(S) ∏_L Ω₁(S,L)` when
  `S ∈ Ind(G_P)` and `0` otherwise — literally the RA texts' "complete X₁ term of `Q ∪ J` on side
  `ν`, with an absent row read as zero" (`T_ν(J)`); `CV.X1_eq_sum_X1Summand`.
* Transport across the wall: `SM.crossingTransport hs` (support-preserving, `rfl`) and
  `SM.transportSupport hs Q = Q.map (crossingTransport hs).toEmbedding` (def:flat-carriers), the
  form of the accepted `FibrePartitionData.avail_same`.

## Notation map (RA text → Lean)

| RA text | Lean |
|---|---|
| `T_ν(J)`, "the complete X1 term of `Q ∪ J` on side `ν`, absent rows being zero" | `rowTerm hn (genericAt E t ht.1) (Q ∪ J)` (= `CV.X1Summand`) |
| `F_±(S)` "the complete summand of CV def:X1 at `S`" | `rowTerm hn (genericAt E t ht.1) S` |
| `Φ_±(Q)` | `fibreSum (geomAt E t ht.1) e f g (rowTerm hn (genericAt E t ht.1)) Q` |
| `X_1(P_±)` | `CV.X1 hn (E.curve t) (genericAt E t ht.1)` |
| "full-availability fiber", "full availability" | `FullAvail (geomAt E t ht.1) e f g Q` (`avail … Q = triangleCrossings …`) |
| "the side where `Q ∪ J` is present" / "absent" | `Q ∪ J ∈ CV.Ind …` / `∉` |
| `Q`, `S = Q ∪ A`, `S` read on the other side | `Q ∈ outsideSupports …`, `Q ∪ A`, `transportSupport hs (Q ∪ A)` |
| "a carrier `L` of `S`", `wt(L)`, `Ω₁(S,L)`, `R(L)` | `q : GeoComponent hP S`, `CV.weight hP S q`, `CV.Omega1 hn hG hS q`, `CV.carrierR hn hG hS q` |
| "triangle-disjoint carrier" | `TriangleDisjoint hP S e f g q` |
| `C_{Q,σ}(A)`, `ρ_σ(A)`, `τ_σ(A)` | `exteriorFactor hn hG hS e f g`, `touchingFactor …`, `rowTerm hn hG (Q ∪ A)` |
| `K3` side / empty-graph side (`H` / `L`) | `CompleteLocal hP hef heg hfg` / `EmptyLocal hP hef heg hfg` |
| two-edge side `P` (edges `ab, bc`, centre `b`) / one-edge side `E` | `EdgeAB ∧ EdgeBC` / `EdgeAC ∧ ¬EdgeAB ∧ ¬EdgeBC` |
| `a = x_ef = x`, `b = x_eg = y`, `c = x_fg = z`; `u1, u2, u3 = e, f, g` | `xPair hef`, `xPair heg`, `xPair hfg` |
| "one carrier contains the entire arc and both of its endpoint smoothing corners" | `MixedSharedStrandCarrier` |
| CV ax:R, "sides" = point values at every `tp > 0`, `tm < 0` (R6) | `CV.hyp_R` |
| "on a punctured neighbourhood" form of ax:R (`cv_R_near`, R6) | `CVRNear hn E e f g` |

## Fixed labels

The RA files relabel the strands so that the printed words hold; here the labels are the fixed ones
of the accepted `generic_table`: `a = x_ef`, `b = x_eg`, `c = x_fg`, strands `u1 = e`, `u2 = f`,
`u3 = g`, signs `s_a = strandSign e f`, `s_b = strandSign e g`, `s_c = strandSign f g`. Where a text
states its result in relabelled canonical words ("every generic branch can be put in this form by
relabelling"), the bundle carries the canonical-branch clause (the selected pair `ac`, `s_a = s_b =
s_c`) AND the two relabelled instances (selected pair `ab`, `bc`), so that every branch of the event
is covered without narrowing (decision F2(A)). -/

namespace CV

open SM

/-- **CV:ax:R (`CV.hyp_R`)**, the printed statement (d10_axioms.tex:18–24) in the shape fixed by the
CV-DOM decision (work/drafts/cvdom/DECISION_FINAL.md R6): "`X_1(P_+) = X_1(P_-)` across every simple
Reidemeister III event, i.e. every event whose zero set is the forced bundle `Z = {G3_{e,f,g},
G4_{e;f,g}, G4_{f;e,g}, G4_{g;e,f}}` for three pairwise remote edges with `1 ≤ e < f < g ≤ n`,
concurrent at `t = 0` at a point interior to all three, the event being transversal in the sense of
Definition def:event." The sides are the two chambers of the event (def:event), rendered as `X₁` at
every positive and every negative parameter (equal to the chamber values by prop:chamberinv (ii)).
This is the declaration of the row CV:ax:R (fixed name); it is stated here because the R lane's
final theorem `RProof.cv_R` has this type, and is to be moved to the CV row module by the
assembler. -/
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
(`1 ≤ rep e < rep f < rep g ≤ n`), so the row theorems keep the shape of the accepted cores and
supply `hn` to `CV.X1` themselves. -/
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
theorem extremeLocal_iff (hP : CrossingGeometry P) {e f g : ZMod n}
    (hef : IsCrossing P {e, f}) (heg : IsCrossing P {e, g}) (hfg : IsCrossing P {f, g}) :
    ExtremeLocal hP hef heg hfg ↔ CompleteLocal hP hef heg hfg ∨ EmptyLocal hP hef heg hfg :=
  Iff.rfl

end RowTerm

/-! ### The X₁ specialisation of R_ASSEMBLY_SPEC.md (3) (the "X₁ flag" of NOTES_FINAL.md §3, now closed)

"The finite bijection just established partitions the exact state sum, so
`X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)` (3)": `FibrePartitionData.state_sum_partition` at the summand
`F := F_±` = `rowTerm`, with def:X1 unfolded by `X1_eq_sum_rowTerm`. PROVED. -/
theorem X1_eq_sum_fibreSum {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hF : FibrePartitionData E e f g δ) (hn : 3 ≤ n) (t : E.Parameter) (ht : Punctured E δ t) :
    CV.X1 hn (E.curve t) (genericAt E t ht.1) =
      ∑ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
        fibreSum (geomAt E t ht.1) e f g (rowTerm hn (genericAt E t ht.1)) Q := by
  rw [X1_eq_sum_rowTerm]
  exact hF.state_sum_partition t ht (rowTerm hn (genericAt E t ht.1))

/-! ## Row 170 — R:exterior (R_ATTACHMENT_WARRANTS.md, "R-EXTERIOR-1 — the triangle-disjoint factor")

Printed statement: "Let `P_-` and `P_+` be the generic sides of a simple transversal RIII event, and
let `T` be the three crossings identified by their carrying edge pairs as in R-LOC-2. Fix an outside
independent set `Q`, disjoint from `T`. On either side `sigma`, let `A` be any subset of `T` for
which `S = Q union A` is independent. A carrier of `S` is *triangle-disjoint* when it contains none of
the six traversal visits belonging to `T`, including a selected triangle crossing's smoothing-site
visits. Define `C_{Q,sigma}(A) = product over triangle-disjoint carriers L of wt_sigma(L) *
Omega_{1,sigma}(S,L)`. Then `C_{Q,sigma}(A)` is independent of `A`, and its common value is the same
for `sigma=-` and `sigma=+`. Write that single value as `C_Q`; it may be zero. Consequently every
full-availability row factors exactly as `tau_sigma(A) = C_Q * rho_sigma(A)`, where `rho_sigma(A)` is
the product over the triangle-touching carriers." -/

section Exterior

variable {P : LabelledTuple n}

/-- "A carrier of `S` is *triangle-disjoint* when it contains none of the six traversal visits
belonging to `T`, including a selected triangle crossing's smoothing-site visits": no visit of a
triangle crossing is owned by the carrier (`geoOwner`, SM conv:selected-visits at selected visits). -/
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
independent on the side in question; across the wall `Q` is read through `transportSupport hs`. -/
structure ExteriorData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Then `C_{Q,sigma}(A)` is independent of `A`" (on either side `σ`). -/
  independent_of_A : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
    ∀ A A' : Finset (Crossing (E.curve t)),
      A ⊆ triangleCrossings (E.curve t) e f g → A' ⊆ triangleCrossings (E.curve t) e f g →
      ∀ (hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1)) (hA' : Q ∪ A' ∈ CV.Ind (geomAt E t ht.1)),
        exteriorFactor hn (genericAt E t ht.1) hA e f g =
          exteriorFactor hn (genericAt E t ht.1) hA' e f g
  /-- "and its common value is the same for `sigma=-` and `sigma=+`. Write that single value as `C_Q`;
  it may be zero." -/
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
  rho_sigma(A)`, where `rho_sigma(A)` is the product over the triangle-touching carriers": one integer
  `C_Q` serves every row `A` on both sides. -/
  factorization : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∃ C : ℤ,
      (∀ A : Finset (Crossing (E.curve t)), A ⊆ triangleCrossings (E.curve t) e f g →
        ∀ hA : Q ∪ A ∈ CV.Ind (geomAt E t ht.1),
          rowTerm hn (genericAt E t ht.1) (Q ∪ A) = C * touchingFactor hn (genericAt E t ht.1) hA e f g) ∧
      (∀ A' : Finset (Crossing (E.curve t')), A' ⊆ triangleCrossings (E.curve t') e f g →
        ∀ hA' : transportSupport hs Q ∪ A' ∈ CV.Ind (geomAt E t' ht'.1),
          rowTerm hn (genericAt E t' ht'.1) (transportSupport hs Q ∪ A') =
            C * touchingFactor hn (genericAt E t' ht'.1) hA' e f g)

/-- **Row 170, R:exterior** (R-EXTERIOR-1). -/
theorem exterior (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExteriorData (three_le_of_h3 h3) E e f g δ := by
  sorry

/-! ## Row 176 — R:availability_0_1 (R_ASSEMBLY_SPEC.md, the paragraph after (4); OPEN_WORK.md item 2)

Specified text: "The local proof task, for each such `Q`, is `Φ_+(Q) = Φ_-(Q)` (4). At availability
zero or one the local supports themselves correspond, but that does **not** prove their summands
agree. Prove the required carrier/record, selector, rotation and coefficient transport. These cases
cannot be omitted because the four core proofs assume full availability." OPEN_WORK.md item 2:
"Prove the fibre identities for availability 0 and 1. The supplied core proofs assume full
availability and do not by themselves cover these cases." -/

/-- **The availability-0/1 fibre identities**, clause by clause, for `Q ∈ Ind(G[W])` with
`|𝓐(Q)| ∈ {0, 1}` (`FibrePartitionData.avail_card` excludes `2`; `3` is full availability, rows
172–177), across the wall (`Q` read on the far side through `transportSupport hs`). -/
structure AvailabilityData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "At availability zero or one the local supports themselves correspond": `J ∈ Ind(G_±[𝓐(Q)])`
  on one side iff its transport is in the local fibre of the transported `Q` on the other. -/
  local_supports_correspond : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J : Finset (Crossing (E.curve t)),
        J ∈ localFibre (geomAt E t ht.1) e f g Q ↔
          transportSupport hs J ∈ localFibre (geomAt E t' ht'.1) e f g (transportSupport hs Q)
  /-- "but that does **not** prove their summands agree. Prove the required carrier/record, selector,
  rotation and coefficient transport": for every local support `J` of the fibre, the carriers of
  `Q ∪ J` on the two sides correspond bijectively (carrier transport) with equal weights `wt(L)`
  (selector transport), equal `R(L)` (rotation transport) and equal factors `Ω₁(S,L)` (coefficient
  transport; the record transport of the pieces is what makes the piece polynomials, hence `Ω₁`,
  agree). -/
  carrier_transport : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
      ∀ (hS : Q ∪ J ∈ CV.Ind (geomAt E t ht.1))
        (hS' : transportSupport hs (Q ∪ J) ∈ CV.Ind (geomAt E t' ht'.1)),
      ∃ φ : GeoComponent (geomAt E t ht.1) (Q ∪ J) ≃
          GeoComponent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ J)),
        ∀ q,
          CV.weight (geomAt E t ht.1) (Q ∪ J) q =
              CV.weight (geomAt E t' ht'.1) (transportSupport hs (Q ∪ J)) (φ q) ∧
          CV.carrierR hn (genericAt E t ht.1) hS q = CV.carrierR hn (genericAt E t' ht'.1) hS' (φ q) ∧
          CV.Omega1 hn (genericAt E t ht.1) hS q = CV.Omega1 hn (genericAt E t' ht'.1) hS' (φ q)
  /-- … so that the summands agree: `F_+(Q ∪ J) = F_-(Q ∪ J)` for every `J` of the fibre. -/
  summands_agree : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      ∀ J ∈ localFibre (geomAt E t ht.1) e f g Q,
        rowTerm hn (genericAt E t ht.1) (Q ∪ J) =
          rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ J))
  /-- "The local proof task, for each such `Q`, is `Φ_+(Q) = Φ_-(Q)` (4)" (OPEN_WORK.md item 2 "the
  fibre identities for availability 0 and 1"). -/
  fibre_identity : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      (avail (geomAt E t ht.1) e f g Q).card = 0 ∨ (avail (geomAt E t ht.1) e f g Q).card = 1 →
      fibreSum (geomAt E t ht.1) e f g (rowTerm hn (genericAt E t ht.1)) Q =
        fibreSum (geomAt E t' ht'.1) e f g (rowTerm hn (genericAt E t' ht'.1)) (transportSupport hs Q)

/-- **Row 176, R:availability_0_1**. -/
theorem availability_zero_one (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ AvailabilityData (three_le_of_h3 h3) E e f g δ := by
  sorry

/-! ## Row 177 — R:generic_selector (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md)

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
(CV:def:wind). -/
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
  selected-conditions (4) holds (the event-level instance of `GenericTableData.selected_unique`;
  which pair it is on the graph is `selected_is_graph_selected`). -/
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

/-- **Row 177, R:generic_selector** (R_GENERIC_NONSELECTED_SELECTOR_PROOF.md). -/
theorem generic_selector (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectorData (three_le_of_h3 h3) E e f g δ := by
  sorry

/-! ## Row 178 — R:generic_transport (R_GENERIC_COMMON_TRANSPORT_PROOF.md, "Statement and canonical
branch")

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
`bc` (endpoints `b, c`). -/
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
  /-- (2) "`T_P(a) = T_E(a)`", canonical branch (1). -/
  endpoint_a : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hef}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hef}))
  /-- (2) "`T_P(c) = T_E(c)`", canonical branch (1). -/
  endpoint_c : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ¬ ExtremeLocal (geomAt E t ht.1) hef heg hfg →
    strandSign (E.curve t) e f = strandSign (E.curve t) e g →
    strandSign (E.curve t) e g = strandSign (E.curve t) f g →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      rowTerm hn (genericAt E t ht.1) (Q ∪ {xPair hfg}) =
        rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {xPair hfg}))
  /-- "Every generic branch can be put in this form by relabelling the strands … The same relabelling
  carries the crossings": the two endpoint rows of the other four generic branches — selected pair
  `ab` (endpoints `a, b`) and selected pair `bc` (endpoints `b, c`). -/
  relabelled_branches : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
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

/-- **Row 178, R:generic_transport** (R_GENERIC_COMMON_TRANSPORT_PROOF.md). -/
theorem generic_transport (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericTransportData (three_le_of_h3 h3) E e f g δ := by
  sorry

/-! ## Row 182 — R:generic_selected (R_GENERIC_SELECTED_COUPLE_PROOF.md, Statement)

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
centre `a`). `t` is the two-edge side `P`, `t'` the one-edge side `E`. -/
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

/-- **Row 182, R:generic_selected** (R_GENERIC_SELECTED_COUPLE_PROOF.md). -/
theorem generic_selected (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ GenericSelectedData (three_le_of_h3 h3) E e f g δ := by
  sorry

/-! ## Row 183 — R:extreme_pair_zero (R_EXTREME_PAIR_ZERO_PROOF.md)

Printed statement: "Fix the two nearby generic chamber-side representatives of a simple RIII wall in
the extreme graph orbit `K3 <-> empty`, and fix a full-availability fiber. Each local pair support is
absent on the `K3` side and present on the empty-graph side. Its complete X1 term on the latter
generic polygon is zero, for arbitrary outside support and exterior geometry."
Proof, paragraphs 2–3: "The support `S` is independent. … The remaining crossing `z` is undominated by
`S` … It is a singleton component there." -/

/-- **Every extreme one-sided pair row is zero**, clause by clause, on each side (the side is named by
its local graph). -/
structure ExtremePairZeroData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Each local pair support is absent on the `K3` side and present on the empty-graph side." -/
  pair_absent_present : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
      (CompleteLocal (geomAt E t ht.1) hef heg hfg → Q ∪ J ∉ CV.Ind (geomAt E t ht.1)) ∧
      (EmptyLocal (geomAt E t ht.1) hef heg hfg → Q ∪ J ∈ CV.Ind (geomAt E t ht.1))
  /-- "The remaining crossing `z` is undominated by `S` … It is a singleton component there. … Hence
  `{z}` is a singleton residual piece" (the hypothesis under which thm:s7universal (D)(i),
  CV:singleton_D_i, is read). -/
  remaining_singleton_piece : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    EmptyLocal (geomAt E t ht.1) hef heg hfg →
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
    ∀ J : Finset (Crossing (E.curve t)), J ⊆ triangleCrossings (E.curve t) e f g → J.card = 2 →
    ∀ z ∈ triangleCrossings (E.curve t) e f g \ J,
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

/-- **Row 183, R:extreme_pair_zero** (R_EXTREME_PAIR_ZERO_PROOF.md). -/
theorem extreme_pair_zero (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremePairZeroData (three_le_of_h3 h3) E e f g δ := by
  sorry

/-! ## Row 175 — R:extreme_transport (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md, "Statement and
canonical data")

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
`z = c = x_fg`. -/

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

/-- **Row 175, R:extreme_transport** (R_EXTREME_SINGLETON_TRANSPORT_PROOF.md). -/
theorem extreme_transport (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData (three_le_of_h3 h3) E e f g δ := by
  sorry

/-! ## Row 174 — R:extreme_selected (R_EXTREME_SELECTED_COUPLE_PROOF.md, Statement)

Printed statement: "Fix a full-availability fiber at a simple RIII wall in the extreme graph orbit.
Let `H` denote the side whose local graph is `K3`, let `L` denote the side whose local graph is empty,
and fix the outside support `Q`. … Full availability is a hypothesis of the statement, not merely
scene-setting: it says every member of `T={x,y,z}` is nonadjacent to `Q`, and therefore makes `Q union
T` an independent support on `L`. On `H`, `T` is not independent because its induced graph is `K3`.
… Write `T_nu(J)` for the complete X1 term of `Q union J` on side `nu`, with an absent row read as
zero. Then `T_H(empty) - T_L(empty) = T_L(xyz)` (2). Since `xyz` is absent on the `K3` side, (2) is
exactly the extreme selected empty/full complementary-couple identity. Equation (2), whose sides are
named by their graphs, is independent of coorientation … Thus the extreme orbit is precisely
`s_x = s_z = -s_y =: sigma` (1a)." -/

/-- **The extreme selected empty/full couple**, clause by clause; `t` is the `K3` side `H`, `t'` the
empty side `L` (sides named by their graphs). -/
structure ExtremeSelectedData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- "Full availability … makes `Q union T` an independent support on `L`. On `H`, `T` is not
  independent because its induced graph is `K3`" ("`xyz` is absent on the `K3` side"). -/
  full_row_present_absent : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g, FullAvail (geomAt E t ht.1) e f g Q →
      (EmptyLocal (geomAt E t ht.1) hef heg hfg →
        Q ∪ triangleCrossings (E.curve t) e f g ∈ CV.Ind (geomAt E t ht.1)) ∧
      (CompleteLocal (geomAt E t ht.1) hef heg hfg →
        Q ∪ triangleCrossings (E.curve t) e f g ∉ CV.Ind (geomAt E t ht.1))
  /-- (1a) "Thus the extreme orbit is precisely `s_x = s_z = -s_y =: sigma`." -/
  extreme_signs : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    ∀ (hef : IsCrossing (E.curve t) {e, f}) (heg : IsCrossing (E.curve t) {e, g})
      (hfg : IsCrossing (E.curve t) {f, g}),
    ExtremeLocal (geomAt E t ht.1) hef heg hfg ↔
      (strandSign (E.curve t) e f = strandSign (E.curve t) f g ∧
        strandSign (E.curve t) e g = -strandSign (E.curve t) e f)
  /-- (2) "`T_H(empty) - T_L(empty) = T_L(xyz)`". -/
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

/-- **Row 174, R:extreme_selected** (R_EXTREME_SELECTED_COUPLE_PROOF.md). -/
theorem extreme_selected (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeSelectedData (three_le_of_h3 h3) E e f g δ := by
  sorry

/-! ## Row 185 — R:cv_theorem (R_ASSEMBLY_SPEC.md, last paragraph; OPEN_WORK.md item 4; CV ax:R)

Specified text: "Finally sum the proved identities (4) over the same finite outside-support set in
(3). Equality is preserved by finite summation, giving exactly CV ax:R. Review that all source
event-domain clauses survived the localization and assembly. Apply the independently proved bridge
afterwards." OPEN_WORK.md item 4: "Sum all fibre identities to prove CV ax:R on its entire printed
simple/transversal forced-bundle domain." Shape (DECISION_FINAL.md R6): `RProof.cv_R : CV.hyp_R`; the
R lane's intermediate is the punctured-neighbourhood form `cv_R_near`, and `cv_R = cv_R_near +
prop:chamberinv (ii)` (each side of the event lies in one CV chamber, `CV.Event.sideChamber`). -/

/-- The "punctured neighbourhood" form of CV ax:R delivered by the fibre-sum assembly (R6's
`cv_R_near`): `X₁` agrees at every pair of opposite-side parameters within some radius `δ`. -/
def CVRNear (hn : 3 ≤ n) (E : CV.Event n) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧
    ∀ (tp tm : E.Parameter) (hp : 0 < tp.val) (hm : tm.val < 0), tp.val < δ → -δ < tm.val →
      CV.X1 hn (E.curve tp) (E.generic_punctured tp hp.ne') =
        CV.X1 hn (E.curve tm) (E.generic_punctured tm hm.ne)

/-- **The assembly of CV ax:R**, clause by clause, for the event `E` and the radius `δ`. -/
structure CVTheoremData (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ) : Prop where
  /-- (3) at the summand `F_±`: "`X_1(P_±) = Σ_{Q ∈ Ind(G[W])} Φ_±(Q)`" (the "same finite
  outside-support set"). -/
  state_sum : ∀ t : E.Parameter, ∀ ht : Punctured E δ t,
    CV.X1 hn (E.curve t) (genericAt E t ht.1) =
      ∑ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
        fibreSum (geomAt E t ht.1) e f g (rowTerm hn (genericAt E t ht.1)) Q
  /-- "the proved identities (4)": `Φ_+(Q) = Φ_-(Q)` for every outside independent `Q` (availability
  `0, 1` by row 176; availability `3` by rows 170, 177, 178, 182 in the generic orbit and 170, 175,
  183, 174 in the extreme orbit). -/
  fibre_identities : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
    ∀ hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s,
    ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      fibreSum (geomAt E t ht.1) e f g (rowTerm hn (genericAt E t ht.1)) Q =
        fibreSum (geomAt E t' ht'.1) e f g (rowTerm hn (genericAt E t' ht'.1)) (transportSupport hs Q)
  /-- "Finally sum the proved identities (4) over the same finite outside-support set in (3). Equality
  is preserved by finite summation": `X₁` agrees on the two punctured sides within `δ`. -/
  near : ∀ t t' : E.Parameter, ∀ ht : Punctured E δ t, ∀ ht' : Punctured E δ t',
    OppositeSides E t t' →
      CV.X1 hn (E.curve t) (genericAt E t ht.1) = CV.X1 hn (E.curve t') (genericAt E t' ht'.1)
  /-- "giving exactly CV ax:R": `X_1(P_+) = X_1(P_-)` on the two chambers of the event, i.e. at every
  positive and every negative parameter (R6; from `near` and prop:chamberinv (ii)). -/
  sides : ∀ (tp tm : E.Parameter) (hp : 0 < tp.val) (hm : tm.val < 0),
    CV.X1 hn (E.curve tp) (E.generic_punctured tp hp.ne') =
      CV.X1 hn (E.curve tm) (E.generic_punctured tm hm.ne)

/-- The `near` clause is R6's `cv_R_near`. PROVED. -/
theorem CVTheoremData.cvRNear {hn : 3 ≤ n} {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ E.radius) (h : CVTheoremData hn E e f g δ) : CVRNear hn E := by
  refine ⟨δ, hδ, hδr, fun tp tm hp hm hpδ hmδ => ?_⟩
  have htp : Punctured E δ tp := ⟨hp.ne', by rw [abs_of_pos hp]; exact hpδ⟩
  have htm : Punctured E δ tm := ⟨hm.ne, by rw [abs_of_neg hm]; linarith⟩
  exact h.near tp tm htp htm (mul_neg_of_pos_of_neg hp hm)

/-- **R6, the relation `cv_R = cv_R_near + chamberinv(ii)`**, PROVED: given the chamber constancy of
`X₁` (CV:prop:chamberinv (ii), "`X₁` is constant on each chamber", here an explicit hypothesis —
`CV.X1_eq_of_mem_chamber_of_pieceHomfly` reduces it to `PieceHomflyTransported`), the punctured
form gives the all-sides form: each side image `E.curve (Ioo 0 radius)` lies in the side chamber
`E.sideChamber true` (`CV.Event.curve_mem_sideChamber_pos`), so `X₁` at any `tp > 0` equals `X₁` at a
`tp₀ ∈ (0, δ)`, likewise on the negative side, and `cv_R_near` joins the two. -/
theorem sides_of_near (hn : 3 ≤ n) (E : CV.Event n)
    (hchamber : ∀ (P Q : LabelledTuple n) (hP : CV.Generic P) (hQ : CV.Generic Q),
      Q ∈ CV.chamber P → CV.X1 hn P hP = CV.X1 hn Q hQ)
    (hnear : CVRNear hn E) :
    ∀ (tp tm : E.Parameter) (hp : 0 < tp.val) (hm : tm.val < 0),
      CV.X1 hn (E.curve tp) (E.generic_punctured tp hp.ne') =
        CV.X1 hn (E.curve tm) (E.generic_punctured tm hm.ne) := by
  obtain ⟨δ, hδ, hδr, hn'⟩ := hnear
  intro tp tm hp hm
  have hr := E.radius_pos
  let tp₀ : E.Parameter := ⟨δ / 2, by constructor <;> linarith⟩
  let tm₀ : E.Parameter := ⟨-(δ / 2), by constructor <;> linarith⟩
  have hp₀ : 0 < tp₀.val := by show 0 < δ / 2; linarith
  have hm₀ : tm₀.val < 0 := by show -(δ / 2) < 0; linarith
  have h1 : CV.X1 hn (E.curve tp) (E.generic_punctured tp hp.ne') =
      CV.X1 hn (E.curve tp₀) (E.generic_punctured tp₀ hp₀.ne') := by
    apply hchamber
    have hA := E.curve_mem_sideChamber_pos tp hp
    have hB := E.curve_mem_sideChamber_pos tp₀ hp₀
    unfold CV.Event.sideChamber at hA hB
    rw [← CV.chamber_eq_of_mem hA] at hB
    exact hB
  have h2 : CV.X1 hn (E.curve tm₀) (E.generic_punctured tm₀ hm₀.ne) =
      CV.X1 hn (E.curve tm) (E.generic_punctured tm hm.ne) := by
    apply hchamber
    have hA := E.curve_mem_sideChamber_neg tm hm
    have hB := E.curve_mem_sideChamber_neg tm₀ hm₀
    unfold CV.Event.sideChamber at hA hB
    rw [← CV.chamber_eq_of_mem hB] at hA
    exact hA
  have h3 := hn' tp₀ tm₀ hp₀ hm₀ (by show δ / 2 < δ; linarith) (by show -δ < -(δ / 2); linarith)
  exact h1.trans (h3.trans h2)

/-- `CV.hyp_R` follows from the assembly bundle at every simple RIII event (its `sides` field).
PROVED. -/
theorem hyp_R_of_data
    (h : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
      (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
      (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
      (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
      (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f),
      E.IsSimpleRIII e f g h3 h4e h4f h4g →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ CVTheoremData hn E e f g δ) :
    CV.hyp_R := by
  intro n _ hn E e f g h3 h4e h4f h4g hE tp tm hp hm
  obtain ⟨δ, -, -, hD⟩ := h n hn E e f g h3 h4e h4f h4g hE
  exact hD.sides tp tm hp hm

/-- **Row 185, R:cv_theorem** — CV ax:R as a theorem (`CV.hyp_R`, fixed name `RProof.cv_R`,
work/lean/axiom-policy.json; consumed by `Bridge.sm_R` at the event `Bridge.eventOfTriple hn g h`). -/
theorem cv_R : CV.hyp_R := by
  sorry


/-! ### The finite summation of the fibre identities (R_ASSEMBLY_SPEC.md, last paragraph), PROVED -/

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
`Ind(G[W])` at `t` under the support transport. -/
theorem outsideSupports_transport (hF : FibrePartitionData E e f g δ) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s) :
    (outsideSupports (geomAt E t ht.1) e f g).map
        (Finset.mapEmbedding (crossingTransport hs).toEmbedding).toEmbedding =
      outsideSupports (geomAt E t' ht'.1) e f g := by
  ext Q'
  rw [Finset.mem_map]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    rw [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
    exact mem_outsideSupports_transport hF ht ht' hop hs hQ
  · intro hQ'
    refine ⟨transportSupport (fun s => (hs s).symm) Q',
      mem_outsideSupports_transport hF ht' ht hop.symm (fun s => (hs s).symm) hQ', ?_⟩
    rw [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
    exact transportSupport_transportSupport_symm hs Q'

/-- **"Finally sum the proved identities (4) over the same finite outside-support set in (3).
Equality is preserved by finite summation"**: from (3) on both sides (`X1_eq_sum_fibreSum`) and
the fibre identities (4) at one pair of opposite parameters, `X₁` agrees there. PROVED — the
`near` clause of `CVTheoremData` follows from its `fibre_identities` clause and `fibre_partition`. -/
theorem near_of_fibre_identities (hF : FibrePartitionData E e f g δ) (hn : 3 ≤ n)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t')
    (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hfib : ∀ Q ∈ outsideSupports (geomAt E t ht.1) e f g,
      fibreSum (geomAt E t ht.1) e f g (rowTerm hn (genericAt E t ht.1)) Q =
        fibreSum (geomAt E t' ht'.1) e f g (rowTerm hn (genericAt E t' ht'.1)) (transportSupport hs Q)) :
    CV.X1 hn (E.curve t) (genericAt E t ht.1) = CV.X1 hn (E.curve t') (genericAt E t' ht'.1) := by
  rw [X1_eq_sum_fibreSum hF hn t ht, X1_eq_sum_fibreSum hF hn t' ht',
    ← outsideSupports_transport hF ht ht' hop hs, Finset.sum_map]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply]
  exact hfib Q hQ

end Assembly

end RProof

