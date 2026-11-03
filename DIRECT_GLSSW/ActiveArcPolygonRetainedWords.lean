import ActiveArcChildReducedPairing

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open PermutationOrbits DaughterFirstReturn
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (p : Fin n → PlanarPoint ℝ) (hG2 : cyclicNoTripleIntersections p)
variable (S : Finset (PolygonCrossing p))

/-- Delete actual unselected polygon visits from the incoming orbit. -/
theorem polygonRetained_orbit_filter
    (x : {x : PolygonEvent p // retainedCorner p S x}) :
    letI := polygonEventOrder p hG2
    (orbitWord (smoothingIncomingPermutation p hG2 S) x.val).filter
      (fun y => decide (retainedCorner p S y))=
      (orbitWord (orderedCyclicSuccessor {x : PolygonEvent p // retainedCorner p S x} *
        polygonRetainedPairing p S) x).map Subtype.val := by
  letI := polygonEventOrder p hG2
  exact RetainedOrbitDeletion.orbitWord_filter_restrict (PolygonEvent p)
    (retainedCorner p S) (smoothingPairing p S) (polygonRetainedPairing p S)
    (pairing_fixes_noncorner p S) (fun _ => rfl) x

/-- Pairing identifies the actual incoming event convention with the actual
outgoing-dart daughter point word. It preserves points and retained labels. -/
theorem polygon_daughterPointList_eq_incoming
    (x : PolygonEvent p) :
    daughterPointList p hG2 S (smoothingPairing p S x)=
      ((orbitWord (smoothingIncomingPermutation p hG2 S) x).filter
        (fun y => decide (retainedCorner p S y))).map (polygonEventPoint p) := by
  have ho := orbitWord_map_injective
    (smoothingIncomingPermutation p hG2 S) (smoothingDartPermutation p hG2 S)
    (smoothingPairing p S) (smoothingPairing p S).injective
    (smoothingPermutation_intertwine p hG2 S) x
  rw [DaughterPointListFilter.daughterPointList_eq_filtered_orbitWord_map,ho,
    ← DaughterPointListFilter.map_filter_comp,List.map_map]
  simp_rw [pairing_preserves_retained]
  apply List.map_congr_left
  intro y _
  exact smoothingPairing_point p S y

theorem polygonRetained_pointWord
    (x : {x : PolygonEvent p // retainedCorner p S x}) :
    letI := polygonEventOrder p hG2
    daughterPointList p hG2 S (smoothingPairing p S x.val)=
      (orbitWord (orderedCyclicSuccessor {x : PolygonEvent p // retainedCorner p S x} *
        polygonRetainedPairing p S) x).map (fun y => polygonEventPoint p y.val) := by
  letI := polygonEventOrder p hG2
  rw [polygon_daughterPointList_eq_incoming,polygonRetained_orbit_filter,List.map_map]
  rfl

/-- Actual incoming component membership is exactly that of its reduced
retained carrier, without polygon G1 or auxiliary assumptions. -/
theorem polygonRetained_sameCycle_iff
    (x y : {x : PolygonEvent p // retainedCorner p S x}) :
    letI := polygonEventOrder p hG2
    (smoothingIncomingPermutation p hG2 S).SameCycle x.val y.val ↔
      (orderedCyclicSuccessor {x : PolygonEvent p // retainedCorner p S x} *
        polygonRetainedPairing p S).SameCycle x y := by
  letI := polygonEventOrder p hG2
  have hd := polygonRetained_orbit_filter p hG2 S x
  constructor
  · intro hh
    have hm : y.val∈(orbitWord (smoothingIncomingPermutation p hG2 S) x.val).filter
        (fun z => decide (retainedCorner p S z)) :=
      List.mem_filter.mpr ⟨(mem_orbitWord_iff _ _ _).mpr hh,by simp only [y.property,decide_true]⟩
    rw [hd] at hm
    obtain ⟨z,hz,he⟩ := List.mem_map.mp hm
    have he' : z=y := Subtype.ext he
    rw [he'] at hz
    exact (mem_orbitWord_iff _ _ _).mp hz
  · intro hh
    have hm : y.val∈(orbitWord (orderedCyclicSuccessor {x : PolygonEvent p // retainedCorner p S x} *
        polygonRetainedPairing p S) x).map Subtype.val :=
      List.mem_map.mpr ⟨y,(mem_orbitWord_iff _ _ _).mpr hh,rfl⟩
    rw [← hd] at hm
    exact (mem_orbitWord_iff _ _ _).mp (List.mem_filter.mp hm).1

end DirectGLSSW.ActiveArc.CompatibleWords
