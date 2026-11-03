import OpenCurrentBoundaryPolygon
import OpenCurrentWordCongruence

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW

/-- A literal child/parent splice fixes its finite length and both indexed
factors. The parent's initial point is the common cut point. -/
theorem ofFn_splice_coordinates {α : Type*} {l m t : ℕ}
    (W : ℕ → α) (Q : Fin m → α) (P : Fin t → α)
    (hm : 0<m) (ht : 0<t)
    (hzero : P ⟨0,ht⟩=Q ⟨0,hm⟩)
    (hw : List.ofFn (fun i : Fin l => W i.val) =
      List.ofFn Q ++ (List.ofFn P).tail) :
    l=m+t-1 ∧ (∀ i : Fin m, W i.val=Q i) ∧
      (∀ i : Fin t, (if i.val=0 then W 0 else W (m-1+i.val))=P i) := by
  have hlen := congrArg List.length hw
  simp only [List.length_ofFn,List.length_append,List.length_tail] at hlen
  have hl : l=m+t-1 := by omega
  have hprefix (i : Fin m) : W i.val=Q i := by
    have hi : i.val<l := by omega
    have he := congrArg (fun L : List α => L[i.val]?) hw
    dsimp only at he
    rw [List.getElem?_append_left (by simpa using i.isLt)] at he
    simpa only [List.getElem?_ofFn,dif_pos hi,dif_pos i.isLt,Option.some.injEq] using he
  refine ⟨hl,hprefix,?_⟩
  intro i
  by_cases hz : i.val=0
  · have hi0 : i=⟨0,ht⟩ := Fin.ext hz
    subst i
    simpa only [ite_true] using (hprefix ⟨0,hm⟩).trans hzero.symm
  · have hpos : 0 < i.val := Nat.pos_of_ne_zero hz
    have hi : m-1+i.val<l := by omega
    have he := congrArg (fun L : List α => L[m-1+i.val]?) hw
    dsimp only at he
    rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega)] at he
    simp only [List.getElem?_tail,List.length_ofFn] at he
    have heq : m-1+i.val-m+1=i.val := by omega
    rw [heq] at he
    simpa only [if_neg hz,List.getElem?_ofFn,dif_pos hi,dif_pos i.isLt,
      Option.some.injEq] using he

/-- The reindexed parent current in boundary transport equals the current
of the literal finite parent word supplied by the proved splice. -/
theorem boundary_parent_current_of_splice {l m t : ℕ}
    (W : ℕ → PlanarPoint ℝ) (Q : Fin m → PlanarPoint ℝ)
    (P : Fin t → PlanarPoint ℝ) (hm : 0<m) (ht : 2≤t)
    (hzero : P ⟨0,by omega⟩=Q ⟨0,hm⟩)
    (hw : List.ofFn (fun i : Fin l => W i.val) =
      List.ofFn Q ++ (List.ofFn P).tail) :
    OpenMarkedCurrent.entry
      (polygonSignArray (fun i => if i=0 then W 0 else W (m-1+i)))
        0 ((l-1)-(m-1)) =
      OpenMarkedCurrent.entry
        (polygonSignArray (rootedPolygonWord P ⟨t-1,by omega⟩)) 0 (t-1) := by
  obtain ⟨hl,hQ,hP⟩ := ofFn_splice_coordinates W Q P hm (by omega) hzero hw
  have hcount : (l-1)-(m-1)=t-1 := by omega
  rw [hcount]
  apply openMarkedCurrent_entry_congr_of_word_eq _ _ (by omega)
  intro i hi
  have hit : i<t := by omega
  have hmod : (t-1+1+i)%t=i := by
    rw [show t-1+1=t by omega,Nat.add_comm t i,Nat.add_mod_right,Nat.mod_eq_of_lt hit]
  simpa only [rootedPolygonWord,cyclicVertexIndex,hmod] using hP ⟨i,hit⟩



end DirectGLSSW
