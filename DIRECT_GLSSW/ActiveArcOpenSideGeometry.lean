import ActiveArcOutgoingCarrier
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc PhysicalSegments RetainedWords
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (S : Finset (Crossing q))

/-- The first retained outgoing carrier is the first genuine physical edge. -/
theorem openSideCarrier_zero :
    openSideCarrier q hR S ⟨0,by have := open_count_ge_two q hR S; omega⟩ = 0 := by
  apply Fin.ext
  change edgeTag q (pairing q S (cornerEvent q hR S (start q) (openFirst q hR S))) = 0
  rw [open_cornerEvent_first]
  rfl

/-- The chosen carrier, not merely some edge, carries both endpoints of the retained side. -/
theorem openSideCarrier_physical (i : Fin (openCount q hR S - 1)) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ 1 ∧
      vertex q hR S (start q) ⟨i.val,by change i.val < openCount q hR S; have := i.isLt; omega⟩ =
        affinePoint (q (openSideCarrier q hR S i).castSucc) (q (openSideCarrier q hR S i).succ) a ∧
      vertex q hR S (start q) ⟨i.val+1,by change i.val+1 < openCount q hR S; have := i.isLt; omega⟩ =
        affinePoint (q (openSideCarrier q hR S i).castSucc) (q (openSideCarrier q hR S i).succ) b := by
  let j : Fin (openCount q hR S) := ⟨i.val,by have := i.isLt; omega⟩
  have hj : j.val+1 < openCount q hR S := by dsimp [j]; have := i.isLt; omega
  let c := enumeration q hR S (start q) j
  have hx := open_nonlast_ne_terminal q hR S j hj
  obtain ⟨a,b,ha,hab,hb,hpoint,hnext,_⟩ := retained_side_physical q hR S (start q) c hx
  have hs : cyclicSuccessor j=⟨i.val+1,hj⟩ := by
    apply Fin.ext
    simp only [cyclicSuccessor,cyclicVertexIndex,Nat.add_zero]
    exact Nat.mod_eq_of_lt hj
  have he := enumeration_cyclic q hR S (start q) j
  rw [hs] at he
  have hev : eventAt q hR S (start q) (nextCorner q hR S (start q) c).val =
      cornerEvent q hR S (start q) ⟨i.val+1,hj⟩ := by rw [← he]; rfl
  rw [hev] at hnext
  exact ⟨a,b,ha,hab,hb,hpoint,hnext⟩

end DirectGLSSW.ActiveArc.OpenCarrier
