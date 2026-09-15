import SM.GeometricTransport
import SM.GeometricOrderStability
import SM.GeometricInterlacement

/-! Equality of independently sorted complete geometric Gauss records under
canonical support transport. This includes their local persistence. -/

namespace SM

open Filter Topology

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n}

theorem geometricGaussList_sorted (hP : CrossingGeometry P) :
    (geometricGaussList hP).Pairwise (fun v w => geometricVisitKey hP v ≤ geometricVisitKey hP w) := by
  classical
  letI := geometricVisitLinearOrder hP
  exact Finset.pairwise_sort _ _

theorem geometricGaussList_transport_perm (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) :
    ((geometricGaussList hP).map (visitTransport hs)).Perm (geometricGaussList hQ) := by
  let e := visitTransport hs
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.map e.injective (geometricGaussList_nodup hP))
    (geometricGaussList_nodup hQ)).mpr
  intro w
  constructor
  · intro _
    exact mem_geometricGaussList hQ w
  · intro _
    obtain ⟨v, rfl⟩ := e.surjective w
    exact List.mem_map.mpr ⟨v, mem_geometricGaussList hP v, rfl⟩

theorem geometricGaussList_transport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q) :
    (geometricGaussList hP).map (visitTransport hs) = geometricGaussList hQ := by
  apply List.Perm.eq_of_pairwise
    (fun x y _ _ hxy hyx => geometricVisitKey_injective hQ (le_antisymm hxy hyx))
    _ (geometricGaussList_sorted hQ) (geometricGaussList_transport_perm hP hQ hs)
  apply List.pairwise_map.mpr
  apply (geometricGaussList_sorted hP).imp
  intro v w h
  exact (geometric_visitKey_le_transport hP hQ hs ho v w).mp h

theorem geometricGaussWord_transport (hP : CrossingGeometry P) (hQ : CrossingGeometry Q)
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s) (ho : CrossingParameterOrderAgrees P Q) :
    (geometricGaussWord hP).map (crossingTransport hs) = geometricGaussWord hQ := by
  have hl := congrArg (List.map Sigma.fst) (geometricGaussList_transport hP hQ hs ho)
  have he : ((geometricGaussList hP).map Sigma.fst).map (crossingTransport hs) =
      (geometricGaussList hQ).map Sigma.fst := by
    simpa only [List.map_map, Function.comp_def, visitTransport_crossing] using hl
  exact congrArg (fun l : List (Crossing Q) => (l : Cycle (Crossing Q))) he

def GeometricRecordsAgree (hP : CrossingGeometry P) (hQ : CrossingGeometry Q) : Prop :=
  ∃ hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s,
    (geometricGaussList hP).map (visitTransport hs) = geometricGaussList hQ ∧
    (geometricGaussWord hP).map (crossingTransport hs) = geometricGaussWord hQ ∧
    (∀ x y, GeometricInterlaces hP x y ↔
      GeometricInterlaces hQ (crossingTransport hs x) (crossingTransport hs y)) ∧
    ∀ i j, IsCrossing P {i, j} → crossingSign Q i j = crossingSign P i j

theorem geometric_records_persist (hP : CrossingGeometry P) :
    ∀ᶠ Q in 𝓝 P, ∀ hQ : CrossingGeometry Q, GeometricRecordsAgree hP hQ := by
  filter_upwards [crossing_support_persists_of_geometry hP,
    geometric_parameter_order_persists hP, geometric_crossing_signs_persist hP]
    with Q hs ho hsign
  intro hQ
  let hc : ∀ s, IsCrossing P s ↔ IsCrossing Q s := fun s => (hs s).symm
  exact ⟨hc, geometricGaussList_transport hP hQ hc ho,
    geometricGaussWord_transport hP hQ hc ho,
    geometric_interlaces_transport hP hQ hc ho, hsign⟩

end SM
