import ActiveArcPhysicalWords
import ActiveArcGammaM

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.RetainedWords
open DirectGLSSW ActiveArc PhysicalSegments PermutationOrbits
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

/-- The first literal retained side lies on the first physical edge, with positive parameter. -/
theorem open_vertex_second_firstEdge (S : Finset (Crossing q)) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
      vertex q hR S (start q) ⟨1,lt_of_lt_of_le (by decide : 1 < 2) (open_count_ge_two q hR S)⟩ =
        affinePoint (q 0) (q 1) s := by
  let i := openFirst q hR S
  let c := enumeration q hR S (start q) i
  have hx : eventAt q hR S (start q) c.val = start q := open_cornerEvent_first q hR S
  have hnt : eventAt q hR S (start q) c.val ≠ terminal q := by
    rw [hx]; exact start_ne_terminal q
  have hf := corner_firstReturn q hR S (start q) c
  have hb := firstReturn_prefix_bounded q hR S _ hnt _ hf.2.2 _ hf.1 le_rfl
  rw [hf.2.1] at hb
  obtain ⟨s,hs,hs1,hpoint,_⟩ := bounded_event_physical_spec q hR
    (pairing q S (eventAt q hR S (start q) c.val))
    (eventAt q hR S (start q) (nextCorner q hR S (start q) c).val)
    (pairing_ne_terminal q S _ hnt) hb.1 hb.2
  have he := enumeration_cyclic q hR S (start q) i
  have hi : cyclicSuccessor i = ⟨1,lt_of_lt_of_le (by decide : 1 < 2) (open_count_ge_two q hR S)⟩ := by
    apply Fin.ext
    simp only [cyclicSuccessor,cyclicVertexIndex,i,openFirst,Nat.add_zero]
    exact Nat.mod_eq_of_lt (by have := open_count_ge_two q hR S; omega)
  rw [hi] at he
  rw [← he] at hpoint
  simp only [physicalEdge,hx] at hpoint
  rw [hx] at hs
  refine ⟨s,?_,hs1,?_⟩
  · simpa [pairing,pairingMap,start,parameter] using hs
  · simpa [vertex,cornerEvent,physicalEdge,pairing,pairingMap,start,edgeTag] using hpoint

end DirectGLSSW.ActiveArc.RetainedWords

namespace DirectGLSSW.ActiveArc.Primitive
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)

/-- Literal index zero is the original open endpoint. -/
theorem openVertex_zero (S : Support q hR) :
    OpenVertex q hR S ⟨0,lt_of_lt_of_le (by decide : 0 < 2) (RetainedWords.open_count_ge_two q hR S.val)⟩ = q 0 :=
  RetainedWords.open_vertex_first q hR S.val

/-- The first literal retained open side has a strictly positive first-edge scale. -/
theorem openVertex_one_firstEdge (S : Support q hR) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧
      OpenVertex q hR S ⟨1,lt_of_lt_of_le (by decide : 1 < 2) (RetainedWords.open_count_ge_two q hR S.val)⟩ =
        affinePoint (q 0) (q 1) s :=
  RetainedWords.open_vertex_second_firstEdge q hR S.val

end DirectGLSSW.ActiveArc.Primitive
