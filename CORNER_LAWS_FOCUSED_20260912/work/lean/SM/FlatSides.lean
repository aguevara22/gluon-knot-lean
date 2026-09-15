import SM.FlatFusionData
import SM.FlatSpatial
import SM.DeletionChamber

/-! Complete flat-side geometry on one common interval. The source's actual
turn-sign change is retained. The parent size is n+1 with n>=3, covering every
source size N>=4; the child is the actual induced cyclic deletion. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

/-- All spatial, sign, record and deletion conclusions of original flat-sides,
with actual geometric records at the nongeneric centre. -/
def FlatSidesData (hn : 3 ≤ n) (g : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) : Prop :=
  Function.Injective g.center ∧ (∀ i, edge g.center i ≠ 0) ∧ Regular g.center ∧
  (∀ i, turn g.center i = 0 ↔ i = j) ∧
  (∃ r : ℝ, 0 < r ∧ edge g.center j = r • edge g.center (j - 1)) ∧
  FlatFusionData hn hz hb hc ∧
  ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧
    (∀ t : g.SideParameter, t.val < δ →
      (turn (g.sideTuple true t).val j : ℝ) * (turn (g.sideTuple false t).val j : ℝ) < 0) ∧
    ∀ t : g.Parameter, |t.val| < δ →
      (∀ a b c : ZMod (n + 1), a ≠ b → b ≠ c → a ≠ c →
        ({a, b, c} : Finset _) ≠ turnSupport j →
        chi (g.curve t) a b c = chi g.center a b c ∧ chi (g.curve t) a b c ≠ 0) ∧
      CrossingGeometry (g.curve t) ∧
      Function.Injective (@crossingPoint (n + 1) (g.curve t)) ∧
      (∀ c : Crossing (g.curve t), ∀ k, crossingPoint c ≠ g.curve t k) ∧
      CrossingParameterOrderAgrees g.center (g.curve t) ∧
      GeometricRecordsAgree (flat_crossingGeometry (by omega) hz hb hc)
        (flat_germ_crossingGeometry (by omega) g hz hb hc t) ∧
      ∃ ht : Generic (deleteVertex (g.curve t) j),
        (⟨deleteVertex (g.curve t) j, ht⟩ : GenericTuple n) ∈
          labelledChamber ⟨deleteVertex g.center j, generic_deleteVertex hn hz hb hc⟩ ∧
        polygonProjection ⟨deleteVertex (g.curve t) j, ht⟩ ∈
          chamber (polygonProjection
            ⟨deleteVertex g.center j, generic_deleteVertex hn hz hb hc⟩)

/-- Full original lem:flat-sides. No central Generic/G1, derivative or supplied
crossing/deletion data are premises. One radius covers zero and both sides. -/
theorem flat_sides (hn : 3 ≤ n) (g : WallGerm (n + 1)) {j : ZMod (n + 1)}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅)
    (hsc : g.SignChanges (fun P => (turn P j : ℝ))) : FlatSidesData hn g j hz hb hc := by
  have hcenter := flat_center_geometry (by omega) hz hb
  refine ⟨hcenter.1, hcenter.2.1, hcenter.2.2.1, hcenter.2.2.2.1,
    hcenter.2.2.2.2.1, flat_fusion_data hn hz hb hc, ?_⟩
  obtain ⟨_, _, _, _, _, δl, hδl, hδlr, hlocal⟩ :=
    flat_germ_local_data (by omega) g hz hb hc
  obtain ⟨δd, hδd, _, hdel⟩ := flat_deletion_chamber hn g hz hb hc
  obtain ⟨δs, hδs, _, hsign⟩ := hsc
  have horder := g.continuous_curve.continuousAt.eventually
    (geometric_parameter_order_persists (flat_crossingGeometry (by omega) hz hb hc))
  obtain ⟨δo, hδo, _, horders⟩ := (g.eventually_center_iff_radius _).mp horder
  let δ := min δl (min δd (min δs δo))
  have hδl' : δ ≤ δl := min_le_left _ _
  have hδd' : δ ≤ δd := (min_le_right _ _).trans (min_le_left _ _)
  have hδs' : δ ≤ δs :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδo' : δ ≤ δo :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨δ, lt_min hδl (lt_min hδd (lt_min hδs hδo)), hδl'.trans hδlr, ?_, ?_⟩
  · intro t ht
    exact hsign t (lt_of_lt_of_le ht hδs')
  · intro t ht
    have hl := hlocal t (lt_of_lt_of_le ht hδl')
    have hs := flat_germ_spatial_data (by omega) g hz hb hc t
    exact ⟨hl.1, hs.1, hs.2.1, hs.2.2,
      horders t (lt_of_lt_of_le ht hδo'), hl.2, hdel t (lt_of_lt_of_le ht hδd')⟩

theorem flat_parent_size (N : ℕ) (hN : 4 ≤ N) : ∃ n : ℕ, 3 ≤ n ∧ N = n + 1 :=
  ⟨N - 1, by omega, by omega⟩

/-- The same full result for every raw continuous curve from the source.
The nongeneric-centre condition is derived by pointZeroCurveGerm. -/
theorem flat_sides_curve (hn : 3 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (F : Set.Ioo (-ε) ε → LabelledTuple (n + 1)) (hF : Continuous F)
    (hgen : ∀ t, t.val ≠ 0 → Generic (F t)) (j : ZMod (n + 1))
    (hz : pointZeroTriples (F ⟨0, by constructor <;> linarith⟩) = {turnSupport j})
    (hb : StrictBetween (F ⟨0, by constructor <;> linarith⟩ (j - 1))
      (F ⟨0, by constructor <;> linarith⟩ j) (F ⟨0, by constructor <;> linarith⟩ (j + 1)))
    (hc : concurrenceTriples (F ⟨0, by constructor <;> linarith⟩) = ∅)
    (hsc : (pointZeroCurveGerm hε F hF hgen (turnSupport j) hz).SignChanges
      (fun P => (turn P j : ℝ))) :
    FlatSidesData hn (pointZeroCurveGerm hε F hF hgen (turnSupport j) hz) j hz hb hc :=
  flat_sides hn (pointZeroCurveGerm hε F hF hgen (turnSupport j) hz) hz hb hc hsc

end SM
