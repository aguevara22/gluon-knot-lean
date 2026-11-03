import HOMFLYEmptyTriangleMove
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

private theorem unique_of_filter_card_one {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p]
    (h : (Finset.univ.filter p).card = 1) : ∃! x, p x := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h
  refine ⟨x, ?_, ?_⟩
  · have := Finset.mem_singleton_self x
    rw [← hx] at this
    exact (Finset.mem_filter.mp this).2
  · intro y hy
    have : y ∈ Finset.univ.filter p := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
    rw [hx] at this
    exact Finset.mem_singleton.mp this

namespace EmptyTriangleSite
variable {D : PLLinkDiagram} (S : EmptyTriangleSite D)

theorem target_middle_iff (e : Fin D.nArc) :
    D.arcTarget e = D.arcTarget S.left ↔ e = S.left := by
  obtain ⟨x, hx, hu⟩ := unique_of_filter_card_one _
    (D.regular_degree_one _ S.regular_middle).1
  constructor
  · intro he
    exact (hu e he).trans (hu S.left rfl).symm
  · rintro rfl; rfl

theorem source_middle_iff (e : Fin D.nArc) :
    D.arcSource e = D.arcTarget S.left ↔ e = S.right := by
  obtain ⟨x, hx, hu⟩ := unique_of_filter_card_one _
    (D.regular_degree_one _ S.regular_middle).2
  constructor
  · intro he
    exact (hu e he).trans (hu S.right S.joint.symm).symm
  · rintro rfl; exact S.joint.symm

theorem incoming_ne_left (c : Fin D.nCrossing) (i : Fin 2) :
    D.incoming c i ≠ S.left := by
  intro h
  apply S.regular_middle c
  rw [← D.incoming_target c i, h]

theorem incoming_ne_right (c : Fin D.nCrossing) (i : Fin 2) :
    D.incoming c i ≠ S.right := by
  intro h
  apply S.regular_end c
  rw [← D.incoming_target c i, h]

theorem outgoing_ne_left (c : Fin D.nCrossing) (i : Fin 2) :
    D.outgoing c i ≠ S.left := by
  intro h
  apply S.regular_start c
  rw [← D.outgoing_source c i, h]

theorem outgoing_ne_right (c : Fin D.nCrossing) (i : Fin 2) :
    D.outgoing c i ≠ S.right := by
  intro h
  apply S.regular_middle c
  rw [← D.outgoing_source c i, h, ← S.joint]

abbrev ContractVertex := {v : Fin D.nVertex // v ≠ D.arcTarget S.left}
abbrev ContractArc := {e : Fin D.nArc // e ≠ S.left}

def contractVertexEquiv : S.ContractVertex ≃ Fin (Fintype.card S.ContractVertex) :=
  Fintype.equivFin _
def contractArcEquiv : S.ContractArc ≃ Fin (Fintype.card S.ContractArc) :=
  Fintype.equivFin _

def contractMap (e : Fin D.nArc) : S.ContractArc :=
  if h : e = S.left then ⟨S.right, S.distinct.symm⟩ else ⟨e, h⟩

@[simp] theorem contractMap_left : (S.contractMap S.left).val = S.right := by
  simp [contractMap]
@[simp] theorem contractMap_of_ne (e : Fin D.nArc) (h : e ≠ S.left) :
    (S.contractMap e).val = e := by simp [contractMap, h]

theorem contractMap_surjective : Function.Surjective S.contractMap := by
  intro e
  refine ⟨e.val, ?_⟩
  apply Subtype.ext
  exact S.contractMap_of_ne _ e.property

theorem contractMap_fibers (e f : Fin D.nArc) :
    S.contractMap e = S.contractMap f ↔
      e = f ∨ (e = S.left ∧ f = S.right) ∨ (e = S.right ∧ f = S.left) := by
  by_cases he : e = S.left <;> by_cases hf : f = S.left
  · subst e; subst f; simp
  · subst e
    simp only [← Subtype.val_inj, S.contractMap_left, S.contractMap_of_ne f hf]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨True.intro, h.symm⟩)
    · rintro (h | ⟨_, h⟩ | ⟨h, _⟩)
      · exact False.elim (hf h.symm)
      · exact h.symm
      · exact False.elim (S.distinct h)
  · subst f
    simp only [← Subtype.val_inj, S.contractMap_left, S.contractMap_of_ne e he]
    constructor
    · intro h; exact Or.inr (Or.inr ⟨h, True.intro⟩)
    · rintro (h | ⟨h, _⟩ | ⟨h, _⟩)
      · exact False.elim (he h)
      · exact False.elim (he h)
      · exact h
  · simp only [← Subtype.val_inj, S.contractMap_of_ne e he, S.contractMap_of_ne f hf]
    exact ⟨Or.inl, fun h => h.elim id (fun h => h.elim (fun h => False.elim (he h.1)) (fun h => False.elim (hf h.2)))⟩

def contractSource (e : S.ContractArc) : S.ContractVertex :=
  ⟨if e.val = S.right then D.arcSource S.left else D.arcSource e.val, by
    split_ifs with h
    · exact D.arc_endpoints_distinct S.left
    · exact fun he => h ((S.source_middle_iff e.val).mp he)⟩

def contractTarget (e : S.ContractArc) : S.ContractVertex :=
  ⟨D.arcTarget e.val, fun h => e.property ((S.target_middle_iff e.val).mp h)⟩

def contractCrossing (c : Fin D.nCrossing) : S.ContractVertex :=
  ⟨D.crossingVertex c, S.regular_middle c⟩

def contractPerm : Equiv.Perm S.ContractArc := by
  classical
  let q : Equiv.Perm (Fin D.nArc) := Equiv.swap S.left S.right * D.continuation
  have hq : q S.left = S.left := by simp [q, S.consecutive]
  exact q.subtypePerm (fun e => by
    constructor
    · intro he h
      apply he
      exact q.injective (h.trans hq.symm)
    · intro he h
      apply he
      simpa only [h] using hq)

theorem contractPerm_val (e : S.ContractArc) :
    (S.contractPerm e).val = (S.contractMap (D.continuation e.val)).val := by
  have hp : D.continuation e.val ≠ S.right := by
    intro h
    exact e.property (D.continuation.injective (h.trans S.consecutive.symm))
  change Equiv.swap S.left S.right (D.continuation e.val) = _
  by_cases h : D.continuation e.val = S.left
  · simp [h, contractMap]
  · simp [Equiv.swap_apply_def, h, hp, contractMap]

theorem contract_continuation_incidence (e : S.ContractArc) :
    S.contractTarget e = S.contractSource (S.contractPerm e) := by
  apply Subtype.ext
  change D.arcTarget e.val = if (S.contractPerm e).val = S.right then _ else _
  rw [S.contractPerm_val]
  by_cases h : D.continuation e.val = S.left
  · simp only [h, S.contractMap_left, if_pos rfl]
    exact (D.continuation_incidence e.val).trans (congrArg D.arcSource h)
  · have hp : D.continuation e.val ≠ S.right := by
      intro he
      exact e.property (D.continuation.injective (he.trans S.consecutive.symm))
    rw [S.contractMap_of_ne _ h, if_neg hp]
    exact D.continuation_incidence e.val

end EmptyTriangleSite
end
end DirectGLSSW.HOMFLY



