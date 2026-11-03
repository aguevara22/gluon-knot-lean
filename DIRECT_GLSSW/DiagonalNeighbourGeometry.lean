import HoleStarNeighbourConverse

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
attribute [local instance] Classical.propDecidable

/-- An actual cut between adjacent endpoints is one of those endpoints. -/
theorem secantAxisAdjacent_cut_eq_left {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b u : ℝ) (h : secantAxisAdjacent T C a u)
    (hb : b ∈ secantAxisCuts T C) (hab : a≤b) (hbu : b<u) : a=b := by
  rcases eq_or_lt_of_le hab with he | hlt
  · exact he
  · exact False.elim (h.2.2.2 b hb hlt hbu)

theorem secantAxisAdjacent_cut_eq_right {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (b u v : ℝ) (h : secantAxisAdjacent T C b v)
    (hu : u ∈ secantAxisCuts T C) (hbu : b<u) (huv : u≤v) : u=v := by
  rcases eq_or_lt_of_le huv with he | hlt
  · exact he
  · exact False.elim (h.2.2.2 u hu hbu hlt)

/-- The literal diagonal-removal branch in each possible neighbouring cell. -/
def rectangleDiagonalNeighbour {D : PLLinkDiagram} {T : BasedTraversal D}
    {C : diagramComponent D} (e : RetainedRectangleSide T C) : Prop :=
  if e.2=0 then ∃ l, secantAxisAdjacent T C l e.1.val.2.1 ∧ l≤e.1.val.1.2
  else if e.2=1 then ∃ w, secantAxisAdjacent T C e.1.val.1.2 w ∧ e.1.val.2.1≤w
  else if e.2=2 then ∃ w, secantAxisAdjacent T C e.1.val.2.2 w ∧ e.1.val.2.2≤e.1.val.1.2
  else ∃ l, secantAxisAdjacent T C l e.1.val.1.1 ∧ e.1.val.2.1≤e.1.val.1.1

/-- The diagonal staircase consists exactly of bottom/right sides with one
intervening actual axis cell. This is a geometric classification, not the
still-open principal-turn sum identity. -/
theorem rectangleDiagonalNeighbour_exact {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (e : RetainedRectangleSide T C) :
    rectangleDiagonalNeighbour e ↔ (e.2=0 ∨ e.2=1) ∧
      secantAxisAdjacent T C e.1.val.1.2 e.1.val.2.1 := by
  have hc := retainedRectangle_axis_cells e.1
  have horder := (Finset.mem_filter.mp e.1.property).2.1
  rcases e with ⟨r,s⟩
  fin_cases s
  · simp [rectangleDiagonalNeighbour]
    constructor
    · rintro ⟨l,hl,hle⟩
      have he := secantAxisAdjacent_cut_eq_left T C l r.val.1.2 r.val.2.1 hl hc.1.2.1 hle horder
      simpa only [he] using hl
    · intro h
      exact ⟨r.val.1.2,h,le_rfl⟩
  · simp [rectangleDiagonalNeighbour]
    constructor
    · rintro ⟨w,hw,hle⟩
      have he := secantAxisAdjacent_cut_eq_right T C r.val.1.2 r.val.2.1 w hw hc.2.1 horder hle
      simpa only [←he] using hw
    · intro h
      exact ⟨r.val.2.1,h,le_rfl⟩
  · change (∃ w, secantAxisAdjacent T C r.val.2.2 w ∧ r.val.2.2≤r.val.1.2) ↔
      ((2 : Fin 4)=0 ∨ (2 : Fin 4)=1) ∧ secantAxisAdjacent T C r.val.1.2 r.val.2.1
    constructor
    · rintro ⟨w,hw,hle⟩
      exfalso
      linarith [hc.2.2.2.1]
    · rintro ⟨h,_⟩
      exact False.elim ((by decide : ¬((2 : Fin 4)=0 ∨ (2 : Fin 4)=1)) h)
  · change (∃ l, secantAxisAdjacent T C l r.val.1.1 ∧ r.val.2.1≤r.val.1.1) ↔
      ((3 : Fin 4)=0 ∨ (3 : Fin 4)=1) ∧ secantAxisAdjacent T C r.val.1.2 r.val.2.1
    constructor
    · rintro ⟨l,hl,hle⟩
      exfalso
      linarith [hc.1.2.2.1]
    · rintro ⟨h,_⟩
      exact False.elim ((by decide : ¬((3 : Fin 4)=0 ∨ (3 : Fin 4)=1)) h)

end
end DirectGLSSW.HOMFLY.PrincipalTurning



