import CV.Events
import SM.GeoCarrierGeometry

/-! # CV/Carriers.lean (part) — CV-side bridges of the hypothesis tiers (CV-DOM unit U0)

Written 2026-09-14 by a Claude Code prover subagent of the pod executor, for the CV-DOM decision
(work/drafts/cvdom/DECISION_FINAL.md §3 rulings R1/R2, §5 unit U0). Draft home
work/drafts/cvdom/U0/; intended home: the head of work/lean/CV/Carriers.lean (the row module of
CV:def:smoothing / lem:carriers / lem:carrierword), after `import SM.GeoCarrierGeometry`.

Contents. (a) The CV binders land in the SM tiers: `CarrierGeometry.ofDiagrammatic`
(CV "diagrammatic" ⇒ tier 1, via the accepted `CV.Diagrammatic.crossingGeometry`, CV/Setup.lean:1566,
and the last clause of `CV.Diagrammatic`), `CarrierGeometry.ofCV` (CV "generic" ⇒ tier 1, via the
accepted `CV.Generic.weakGeneric`, CV/Setup.lean:1135, fidelity fact F1) and
`carrierGeometry_iff_diagrammatic (hn)` (tier 1 IS CV "diagrammatic" for n ≥ 3, via the accepted
`CV.diagrammatic_iff`, CV/Setup.lean:1630, fidelity fact F3). (b) Ruling R2: the CV row binder
`hS : S ∈ CV.Ind hP` (accepted CV:def:interlace, CV/Events.lean:165) is the geo-lane hypothesis
`GeoIndependent hP S` (accepted def:flat-carriers, SM/FlatCarriersDefs.lean:457):
`CV.mem_Ind_iff_geoIndependent`; and the unfolded memberships `CV.mem_N_iff`, `CV.mem_U_iff` of the
accepted `CV.N` / `CV.U` (re-exports of `CV.mem_N` / `CV.mem_U`, CV/Events.lean:194, 199), the forms
U2a's neighbour-separation lemmas are stated in.

Checked (draft) with the SM module compiled to an olean under a temporary root that shadows the
whole `SM` package (Lean resolves a module from the first search root containing the package
directory `SM/`): `cd work/lean; LIB=$PWD/.lake/build/lib/lean; mkdir -p /tmp/u0/src/SM /tmp/u0/olean/SM
/tmp/u0/olean2/SM; cp ../drafts/cvdom/U0/GeoCarrierGeometry.lean /tmp/u0/src/SM/; lake env lean -R
/tmp/u0/src -o /tmp/u0/olean/SM/GeoCarrierGeometry.olean /tmp/u0/src/SM/GeoCarrierGeometry.lean; for f in
$LIB/SM/*; do ln -sf "$f" /tmp/u0/olean2/SM/; done; cp /tmp/u0/olean/SM/GeoCarrierGeometry.olean
/tmp/u0/olean2/SM/; lake env bash -c 'LEAN_PATH="/tmp/u0/olean2:$LEAN_PATH" lean
../drafts/cvdom/U0/CVCarrierBridges.lean'`. Once SM/GeoCarrierGeometry.lean is in work/lean the plain
`lake env lean` check applies. -/

namespace SM

variable {n : ℕ} {P : LabelledTuple n}

/-- CV "diagrammatic" (CV:def:diagrammatic, d1_setup.tex:316–320) ⇒ tier 1: the printed binder of
CV:def:smoothing, lem:carriers, lem:carrierword, def:pieces, def:piecediagram, lem:piececurve. -/
theorem CarrierGeometry.ofDiagrammatic (hD : CV.Diagrammatic P) : CarrierGeometry P :=
  ⟨hD.crossingGeometry, hD.2.2.2.2⟩

/-- CV "generic" (CV:def:generic) ⇒ tier 1 (through tier 2, `CV.Generic.weakGeneric`): the printed
binder of CV:def:wind, def:X1, selector_A, prop:chamberinv(ii). -/
theorem CarrierGeometry.ofCV [NeZero n] (hG : CV.Generic P) : CarrierGeometry P :=
  CarrierGeometry.ofWeak hG.weakGeneric

/-- Tier 1 is exactly CV "diagrammatic" (`n ≥ 3`; fidelity fact F3, `CV.diagrammatic_iff`). -/
theorem carrierGeometry_iff_diagrammatic (hn : 3 ≤ n) :
    CarrierGeometry P ↔ CV.Diagrammatic P := by
  have : NeZero n := ⟨by omega⟩
  rw [CV.diagrammatic_iff hn P]
  exact ⟨fun h => ⟨h.cg, h.vertex_off⟩, fun h => ⟨h.1, h.2⟩⟩

end SM

namespace CV

open SM SM.GeoCarrier

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- Ruling R2: the CV row binder `S ∈ Ind(G_P)` (accepted CV:def:interlace) is the geo lane's
`GeoIndependent hP S` (accepted def:flat-carriers). Definitional: both unfold to
`∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ GeometricInterlaces hP x y`. -/
theorem mem_Ind_iff_geoIndependent (hP : CrossingGeometry P) (S : Finset (Crossing P)) :
    S ∈ Ind hP ↔ GeoIndependent hP S :=
  mem_Ind_iff hP S

/-- Re-export of the accepted `CV.mem_N`: `N_{G_P}(S)` is the set of crossings interlaced with some
element of `S`. -/
theorem mem_N_iff (hP : CrossingGeometry P) (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ N hP S ↔ ∃ x ∈ S, GeometricInterlaces hP y x :=
  mem_N hP S y

/-- Re-export of the accepted `CV.mem_U`, fully unfolded: `U(S)` is the set of crossings neither in
`S` nor interlaced with any element of `S`. -/
theorem mem_U_iff (hP : CrossingGeometry P) (S : Finset (Crossing P)) (y : Crossing P) :
    y ∈ U hP S ↔ y ∉ S ∧ ∀ x ∈ S, ¬ GeometricInterlaces hP y x := by
  rw [mem_U, mem_N]
  simp only [not_exists, not_and]

end CV
