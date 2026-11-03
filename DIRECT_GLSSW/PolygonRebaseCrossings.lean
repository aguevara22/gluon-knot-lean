import PolygonRebaseGeometry

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.PolygonRebase
open HOMFLY.PolygonDrawingBridge
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))

include hρ in
theorem edgeInterior_relabel (e : Fin n) (x : PlanarPoint ℝ) :
    edgeInterior (q ∘ ρ) e x ↔ edgeInterior q (ρ e) x := by
  simp only [edgeInterior,Function.comp_apply,hρ]

def crossingMap (c : PolygonCrossing (q ∘ ρ)) : PolygonCrossing q := by
  let a := ρ c.val.1
  let b := ρ c.val.2
  have hab : a ≠ b := ρ.injective.ne (crossing_edges_ne _ c)
  let x := crossingPoint (q ∘ ρ) c
  have hx := crossingPoint_mem_left (q ∘ ρ) c
  have hy := crossingPoint_mem_right (q ∘ ρ) c
  have hx' : edgeInterior q a x := (edgeInterior_relabel q ρ hρ _ _).mp hx
  have hy' : edgeInterior q b x := (edgeInterior_relabel q ρ hρ _ _).mp hy
  exact if h : a < b then ⟨(a,b),h,⟨x,hx',hy'⟩⟩
    else ⟨(b,a),lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab),⟨x,hy',hx'⟩⟩

theorem crossingMap_carriers (c : PolygonCrossing (q ∘ ρ)) :
    ((crossingMap q ρ hρ c).val = (ρ c.val.1,ρ c.val.2)) ∨
      ((crossingMap q ρ hρ c).val = (ρ c.val.2,ρ c.val.1)) := by
  by_cases h : ρ c.val.1 < ρ c.val.2
  · exact Or.inl (by simp [crossingMap,h])
  · exact Or.inr (by simp [crossingMap,h])

theorem crossingMap_injective : Function.Injective (crossingMap q ρ hρ) := by
  intro c d he
  have hv := congrArg Subtype.val he
  rcases crossingMap_carriers q ρ hρ c with hc | hc <;>
    rcases crossingMap_carriers q ρ hρ d with hd | hd <;> rw [hc,hd] at hv
  · exact Subtype.ext (Prod.ext (ρ.injective (congrArg Prod.fst hv))
      (ρ.injective (congrArg Prod.snd hv)))
  · have ha := ρ.injective (congrArg Prod.fst hv)
    have hb := ρ.injective (congrArg Prod.snd hv)
    have hlt := c.property.1
    rw [ha,hb] at hlt
    exact (not_lt_of_ge (le_of_lt d.property.1) hlt).elim
  · have ha := ρ.injective (congrArg Prod.fst hv)
    have hb := ρ.injective (congrArg Prod.snd hv)
    have hlt := c.property.1
    rw [hb,ha] at hlt
    exact (not_lt_of_ge (le_of_lt d.property.1) hlt).elim
  · exact Subtype.ext (Prod.ext (ρ.injective (congrArg Prod.snd hv))
      (ρ.injective (congrArg Prod.fst hv)))

theorem crossingMap_surjective : Function.Surjective (crossingMap q ρ hρ) := by
  intro d
  let a := ρ.symm d.val.1
  let b := ρ.symm d.val.2
  have hab : a ≠ b := ρ.symm.injective.ne (crossing_edges_ne _ d)
  obtain ⟨x,hx,hy⟩ := d.property.2
  have hx' : edgeInterior (q ∘ ρ) a x :=
    (edgeInterior_relabel q ρ hρ a x).mpr (by simpa only [a,Equiv.apply_symm_apply] using hx)
  have hy' : edgeInterior (q ∘ ρ) b x :=
    (edgeInterior_relabel q ρ hρ b x).mpr (by simpa only [b,Equiv.apply_symm_apply] using hy)
  let c : PolygonCrossing (q ∘ ρ) := if h : a < b then
    ⟨(a,b),h,⟨x,hx',hy'⟩⟩ else
    ⟨(b,a),lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hab),⟨x,hy',hx'⟩⟩
  refine ⟨c,Subtype.ext ?_⟩
  rcases crossingMap_carriers q ρ hρ c with h | h
  · by_cases hh : a < b
    · simpa only [c,dif_pos hh,a,b,Equiv.apply_symm_apply] using h
    · have hr : (crossingMap q ρ hρ c).val = (d.val.2,d.val.1) := by
        simpa only [c,dif_neg hh,a,b,Equiv.apply_symm_apply] using h
      have hl := (crossingMap q ρ hρ c).property.1
      rw [hr] at hl
      exact (not_lt_of_ge (le_of_lt d.property.1) hl).elim
  · by_cases hh : a < b
    · have hr : (crossingMap q ρ hρ c).val = (d.val.2,d.val.1) := by
        simpa only [c,dif_pos hh,a,b,Equiv.apply_symm_apply] using h
      have hl := (crossingMap q ρ hρ c).property.1
      rw [hr] at hl
      exact (not_lt_of_ge (le_of_lt d.property.1) hl).elim
    · simpa only [c,dif_neg hh,a,b,Equiv.apply_symm_apply] using h

def crossingEquiv : PolygonCrossing (q ∘ ρ) ≃ PolygonCrossing q :=
  Equiv.ofBijective (crossingMap q ρ hρ)
    ⟨crossingMap_injective q ρ hρ,crossingMap_surjective q ρ hρ⟩

theorem positiveDiagram_crossingCount (hq : CyclicGeneric q) :
    (positivePolygonEventDiagram (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq)).nCrossing =
      (positivePolygonEventDiagram q hq).nCrossing :=
  Fintype.card_congr (crossingEquiv q ρ hρ)

end DirectGLSSW.PolygonRebase
