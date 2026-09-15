import SM.FlatCrossingGeometry
import SM.GeometricRecords
import SM.FiniteChiStability
import SM.GermNeighborhood

/-! Central geometry and local crossing records of a flat germ. This is a
PARTIAL aggregate for source lem:flat-sides: the deletion/fusion bijection and
deletion-chamber clause are not established here and the source row stays open. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n]

/-- A raw continuous curve with a single actual point-zero support is an
actual wall germ. The centre condition is derived, not an extra premise. -/
def pointZeroCurveGerm {ε : ℝ} (hε : 0 < ε)
    (F : Set.Ioo (-ε) ε → LabelledTuple n) (hF : Continuous F)
    (hgen : ∀ t, t.val ≠ 0 → Generic (F t)) (s : Finset (ZMod n))
    (hz : pointZeroTriples (F ⟨0, by constructor <;> linarith⟩) = {s}) : WallGerm n where
  radius := ε
  radius_pos := hε
  curve := F
  continuous_curve := hF
  generic_punctured := hgen
  nongeneric_center := by
    intro hg
    have he := (pointZeroTriples_empty_iff _).mpr hg.1
    rw [hz] at he
    simp at he

theorem pointZeroCurveGerm_curve {ε : ℝ} (hε : 0 < ε)
    (F : Set.Ioo (-ε) ε → LabelledTuple n) (hF : Continuous F)
    (hgen : ∀ t, t.val ≠ 0 → Generic (F t)) (s : Finset (ZMod n))
    (hz : pointZeroTriples (F ⟨0, by constructor <;> linarith⟩) = {s}) :
    (pointZeroCurveGerm hε F hF hgen s hz).curve = F := rfl

theorem flat_germ_crossingGeometry (hn : 4 ≤ n) (g : WallGerm n) {j : ZMod n}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) (t : g.Parameter) : CrossingGeometry (g.curve t) := by
  by_cases ht : t.val = 0
  · have he : t = g.zeroParameter := Subtype.ext ht
    subst t
    exact flat_crossingGeometry hn hz hb hc
  · exact generic_crossingGeometry (by omega) (g.generic_punctured t ht)

theorem flat_germ_local_data (hn : 4 ≤ n) (g : WallGerm n) {j : ZMod n}
    (hz : g.pointZeros = {turnSupport j})
    (hb : StrictBetween (g.center (j - 1)) (g.center j) (g.center (j + 1)))
    (hc : g.concurrences = ∅) :
    Function.Injective g.center ∧ (∀ i, edge g.center i ≠ 0) ∧ Regular g.center ∧
    (∀ i, turn g.center i = 0 ↔ i = j) ∧
    (∃ r : ℝ, 0 < r ∧ r < 1 ∧
      edge g.center (j - 1) = r • (g.center (j + 1) - g.center (j - 1)) ∧
      edge g.center j = (1 - r) • (g.center (j + 1) - g.center (j - 1))) ∧
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t : g.Parameter, |t.val| < δ →
      (∀ a b c : ZMod n, a ≠ b → b ≠ c → a ≠ c →
        ({a, b, c} : Finset _) ≠ turnSupport j →
          chi (g.curve t) a b c = chi g.center a b c ∧ chi (g.curve t) a b c ≠ 0) ∧
      GeometricRecordsAgree (flat_crossingGeometry hn hz hb hc)
        (flat_germ_crossingGeometry hn g hz hb hc t) := by
  have hgeo := flat_center_geometry hn hz hb
  refine ⟨hgeo.1, hgeo.2.1, hgeo.2.2.1, hgeo.2.2.2.1, flat_fusion hb, ?_⟩
  have hchi := g.continuous_curve.continuousAt.eventually (singlePointTriple_chi_persists hz)
  have hrecords := g.continuous_curve.continuousAt.eventually
    (geometric_records_persist (flat_crossingGeometry hn hz hb hc))
  apply (g.eventually_center_iff_radius _).mp
  filter_upwards [hchi, hrecords] with t hchiT hrecordsT
  exact ⟨hchiT, hrecordsT (flat_germ_crossingGeometry hn g hz hb hc t)⟩

end SM
