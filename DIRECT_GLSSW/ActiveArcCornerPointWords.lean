import ActiveArcCornerEventInsertion
import ActiveArcSingletonWords
import DirectGLSSW.DaughterPointListFilter

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open Primitive RetainedWords PermutationOrbits
attribute [local instance] Classical.propDecidable
variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)

theorem firstEdgeFreeCrossingEquiv_mem_support
    (T : Support (suffix q) (regular_suffix q hR)) (d : Crossing (suffix q)) :
    firstEdgeFreeCrossingEquiv q hfree d ∈ (firstEdgeFreeSupportEquiv q hfree hR T).val ↔
      d∈T.val := by
  constructor
  · intro h
    obtain ⟨e,he,heq⟩ := Finset.mem_map.mp h
    have hi := (firstEdgeFreeCrossingEquiv q hfree).injective heq
    simpa [hi] using he
  · intro h
    exact Finset.mem_map.mpr ⟨d,h,rfl⟩

theorem suffixEventIntoOriginal_retained
    (T : Support (suffix q) (regular_suffix q hR)) (x : Event (suffix q)) :
    retained q (firstEdgeFreeSupportEquiv q hfree hR T).val
      (suffixEventIntoOriginal q hfree x) ↔ retained (suffix q) T.val x := by
  cases x with
  | inl i => simp [retained,suffixEventIntoOriginal]
  | inr v =>
    rcases v with ⟨d,side⟩
    simpa [retained,suffixEventIntoOriginal] using
      firstEdgeFreeCrossingEquiv_mem_support q hR hfree T d

include hR in
theorem suffixEventIntoOriginal_point (x : Event (suffix q)) :
    eventPoint q (suffixEventIntoOriginal q hfree x)=eventPoint (suffix q) x := by
  cases x with
  | inl i => rfl
  | inr v => exact firstEdgeFreeCrossingEquiv_point q hfree hR v.1

/-- The literal original open smoothing word inserts just the removed initial vertex. -/
theorem corner_openPointWord (T : Support (suffix q) (regular_suffix q hR)) :
    List.ofFn (OpenVertex q hR (firstEdgeFreeSupportEquiv q hfree hR T)) =
      q 0 :: List.ofFn (OpenVertex (suffix q) (regular_suffix q hR) T) := by
  change List.ofFn (RetainedWords.vertex q hR (firstEdgeFreeSupportEquiv q hfree hR T).val
    (start q)) = q 0 :: List.ofFn (RetainedWords.vertex (suffix q) (regular_suffix q hR)
      T.val (start (suffix q)))
  rw [SingletonWords.retainedWord_eq_filtered (a:=1) (b:=b) q hR,
      SingletonWords.retainedWord_eq_filtered (a:=b) (b:=0) (suffix q) (regular_suffix q hR),
      corner_openEventWord q hR hfree T]
  have hret (x : Event (suffix q)) :
      decide (retained q (firstEdgeFreeSupportEquiv q hfree hR T).val
        (suffixEventIntoOriginal q hfree x)) = decide (retained (suffix q) T.val x) := by
    have he := suffixEventIntoOriginal_retained q hR hfree T x
    by_cases hp : retained (suffix q) T.val x
    · have ht := he.mpr hp
      simp only [hp,ht,decide_true]
    · have ht : ¬ retained q (firstEdgeFreeSupportEquiv q hfree hR T).val
          (suffixEventIntoOriginal q hfree x) := fun hh => hp (he.mp hh)
      simp only [hp,ht,decide_false]
  have hstart : decide (retained q (firstEdgeFreeSupportEquiv q hfree hR T).val
      (start q))=true := decide_eq_true (endpoints_retained _ _).1
  simp only [List.filter_cons,hstart,ite_true,List.map_cons]
  congr 1
  change List.map (eventPoint q)
    ((List.map (suffixEventIntoOriginal q hfree)
      (orbitWord (incoming (suffix q) (regular_suffix q hR).noTriple T.val) (start (suffix q)))).filter
        (fun x => decide (retained q (firstEdgeFreeSupportEquiv q hfree hR T).val x))) = _
  rw [← DaughterPointListFilter.map_filter_comp]
  simp only [hret,List.map_map]
  apply List.map_congr_left
  intro x hx
  exact suffixEventIntoOriginal_point q hR hfree x

theorem corner_openCount (T : Support (suffix q) (regular_suffix q hR)) :
    openCount q hR (firstEdgeFreeSupportEquiv q hfree hR T).val =
      openCount (suffix q) (regular_suffix q hR) T.val+1 := by
  have hh := congrArg List.length (corner_openPointWord q hR hfree T)
  simpa only [List.length_ofFn,List.length_cons] using hh

theorem corner_openVertex_shift (T : Support (suffix q) (regular_suffix q hR))
    (k : ℕ) (hk : k<openCount (suffix q) (regular_suffix q hR) T.val)
    (hkt : k+1<openCount q hR (firstEdgeFreeSupportEquiv q hfree hR T).val) :
    OpenVertex q hR (firstEdgeFreeSupportEquiv q hfree hR T) ⟨k+1,hkt⟩ =
      OpenVertex (suffix q) (regular_suffix q hR) T ⟨k,hk⟩ := by
  have he := congrArg (fun l : List (PlanarPoint ℝ) => l[k+1]?)
    (corner_openPointWord q hR hfree T)
  simpa [List.getElem?_ofFn,hkt,hk] using he

theorem corner_rootedWord_zero (T : Support (suffix q) (regular_suffix q hR)) :
    rootedPolygonWord (OpenVertex q hR (firstEdgeFreeSupportEquiv q hfree hR T))
      (openLast q hR (firstEdgeFreeSupportEquiv q hfree hR T).val) 0=q 0 := by
  have hz : 0<openCount q hR (firstEdgeFreeSupportEquiv q hfree hR T).val := by
    have hh := open_count_ge_two q hR (firstEdgeFreeSupportEquiv q hfree hR T).val
    omega
  exact (openCurrent_word q hR (firstEdgeFreeSupportEquiv q hfree hR T) 0 hz).trans
    (open_vertex_first q hR (firstEdgeFreeSupportEquiv q hfree hR T).val)

theorem corner_rootedWord_shift (T : Support (suffix q) (regular_suffix q hR))
    (k : ℕ) (hk : k<openCount (suffix q) (regular_suffix q hR) T.val) :
    rootedPolygonWord (OpenVertex q hR (firstEdgeFreeSupportEquiv q hfree hR T))
      (openLast q hR (firstEdgeFreeSupportEquiv q hfree hR T).val) (k+1) =
    rootedPolygonWord (OpenVertex (suffix q) (regular_suffix q hR) T)
      (openLast (suffix q) (regular_suffix q hR) T.val) k := by
  have hkt : k+1<openCount q hR (firstEdgeFreeSupportEquiv q hfree hR T).val := by
    rw [corner_openCount q hR hfree T]
    omega
  exact (openCurrent_word q hR (firstEdgeFreeSupportEquiv q hfree hR T) (k+1) hkt).trans
    ((corner_openVertex_shift q hR hfree T k hk hkt).trans
      (openCurrent_word (suffix q) (regular_suffix q hR) T k hk).symm)

end DirectGLSSW.ActiveArc.Split
