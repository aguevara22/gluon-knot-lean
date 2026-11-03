import DirectGLSSW.DaughterFirstReturn

set_option autoImplicit false

namespace DirectGLSSW.DaughterPointListFilter

noncomputable section

open DirectGLSSW
open DirectGLSSW.DaughterFirstReturn
open DirectGLSSW.PermutationOrbits

local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ} (q : Fin n → PlanarPoint K)
variable (hG2 : cyclicNoTripleIntersections q)
variable (S : Finset (PolygonCrossing q))

theorem map_filter_comp {α β : Type*} (f : α → β) (p : β → Bool)
    (l : List α) :
    (l.filter fun a => p (f a)).map f = (l.map f).filter p := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : p (f a) = true <;> simp [List.filter, h, ih]

omit [IsStrictOrderedRing K] in
theorem cornerCoordinateList_eq_filter (root : PolygonEvent q) :
    List.ofFn (fun i : Fin (Fintype.card (CornerCoord q hG2 S root)) =>
      (cornerEnumeration q hG2 S root i).val) =
      (List.ofFn (fun i : OrbitCoord q hG2 S root => i)).filter
        (fun i => decide (retainedCorner q S (orbitEventAt q hG2 S root i))) := by
  classical
  let e := cornerEnumeration q hG2 S root
  have hs₁ :
      (List.ofFn (fun i : Fin (Fintype.card (CornerCoord q hG2 S root)) => (e i).val)).Sorted (· < ·) := by
    apply List.sorted_lt_ofFn_iff.mpr
    intro i j hij
    change (e i).val < (e j).val
    exact e.strictMono hij
  have hs₂ :
      ((List.ofFn (fun i : OrbitCoord q hG2 S root => i)).filter
        (fun i => decide (retainedCorner q S (orbitEventAt q hG2 S root i)))).Sorted (· < ·) := by
    exact (List.sorted_lt_ofFn_iff.mpr strictMono_id).filter _
  apply List.Sorted.eq_of_mem_iff hs₁ hs₂
  intro i
  constructor
  · intro hi
    rcases List.mem_ofFn.mp hi with ⟨j, hj⟩
    have hret : retainedCorner q S (orbitEventAt q hG2 S root (e j).val) := (e j).property
    rw [hj] at hret
    exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, by simpa using hret⟩
  · intro hi
    rcases List.mem_filter.mp hi with ⟨_, hret⟩
    have hret' : retainedCorner q S (orbitEventAt q hG2 S root i) := by simpa using hret
    let c : CornerCoord q hG2 S root := ⟨i, hret'⟩
    refine List.mem_ofFn.mpr ⟨e.symm c, ?_⟩
    simp [e, c]

omit [IsStrictOrderedRing K] in
theorem daughterEventList_eq_filtered_orbitWord
    (root : PolygonEvent q) :
    List.ofFn (fun i : Fin (Fintype.card (CornerCoord q hG2 S root)) =>
      orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val) =
      (orbitWord (smoothingDartPermutation q hG2 S) root).filter
        (fun x => decide (retainedCorner q S x)) := by
  classical
  have hcoords := cornerCoordinateList_eq_filter q hG2 S root
  have hmapped := congrArg
    (List.map (orbitEventAt q hG2 S root)) hcoords
  have hword :
      orbitWord (smoothingDartPermutation q hG2 S) root =
        List.ofFn (orbitEventAt q hG2 S root) := by
    rfl
  calc
    List.ofFn (fun i : Fin (Fintype.card (CornerCoord q hG2 S root)) =>
        orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val) =
        (orbitWord (smoothingDartPermutation q hG2 S) root).filter
          (fun x => decide (retainedCorner q S x)) := by
          rw [hword]
          simpa [List.map_ofFn] using hmapped.trans
            (map_filter_comp (orbitEventAt q hG2 S root)
              (fun x => decide (retainedCorner q S x))
              (List.ofFn fun i : OrbitCoord q hG2 S root => i))

omit [IsStrictOrderedRing K] in
theorem daughterPointList_eq_filtered_orbitWord_map
    (root : PolygonEvent q) :
    daughterPointList q hG2 S root =
      ((orbitWord (smoothingDartPermutation q hG2 S) root).filter
        (fun x => decide (retainedCorner q S x))).map (polygonEventPoint q) := by
  have h := congrArg (List.map (polygonEventPoint q))
    (daughterEventList_eq_filtered_orbitWord q hG2 S root)
  simpa [daughterPointList, daughterVertex] using h






end

end DirectGLSSW.DaughterPointListFilter
