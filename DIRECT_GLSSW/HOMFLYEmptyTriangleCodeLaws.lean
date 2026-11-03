import HOMFLYEmptyTriangleGeometry

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY
noncomputable section

theorem filter_card_one_iff_unique {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = 1 ↔ ∃! x, p x := by
  rw [Finset.card_eq_one]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · have hm := Finset.mem_singleton_self x
      rw [← hx] at hm
      exact (Finset.mem_filter.mp hm).2
    · intro y hy
      have hm : y ∈ Finset.univ.filter p := by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hy
      rw [hx] at hm
      exact Finset.mem_singleton.mp hm
  · rintro ⟨x, hx, hu⟩
    refine ⟨x, ?_⟩
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hy => hu y hy, fun hy => hy ▸ hx⟩

namespace EmptyTriangleSite
variable {D : PLLinkDiagram} (S : EmptyTriangleSite D)

def contractSourceLift (e : S.ContractArc) : Fin D.nArc :=
  Equiv.swap S.left S.right e.val

theorem contractSource_val (e : S.ContractArc) :
    (S.contractSource e).val = D.arcSource (S.contractSourceLift e) := by
  dsimp [contractSource, contractSourceLift]
  by_cases h : e.val = S.right
  · simp [h]
  · simp [Equiv.swap_apply_def, e.property, h]

theorem contractMap_sourceLift (e : S.ContractArc) :
    S.contractMap (S.contractSourceLift e) = e := by
  apply Subtype.ext
  by_cases h : e.val = S.right
  · simp [contractSourceLift, h, contractMap]
  · have hl : S.contractSourceLift e = e.val := by
      simp [contractSourceLift, Equiv.swap_apply_def, e.property, h]
    rw [hl, S.contractMap_of_ne _ e.property]

theorem contractSource_map (e : Fin D.nArc) (h : e ≠ S.right) :
    (S.contractSource (S.contractMap e)).val = D.arcSource e := by
  by_cases hl : e = S.left
  · subst e
    simp [contractSource, contractMap, S.distinct.symm]
  · simp [contractSource, contractMap, hl, h]

def contractIncoming (c : Fin D.nCrossing) (i : Fin 2) : S.ContractArc :=
  ⟨D.incoming c i, S.incoming_ne_left c i⟩
def contractOutgoing (c : Fin D.nCrossing) (i : Fin 2) : S.ContractArc :=
  ⟨D.outgoing c i, S.outgoing_ne_left c i⟩

theorem contract_incoming_target (c : Fin D.nCrossing) (i : Fin 2) :
    S.contractTarget (S.contractIncoming c i) = S.contractCrossing c := by
  apply Subtype.ext
  exact D.incoming_target c i

theorem contract_outgoing_source (c : Fin D.nCrossing) (i : Fin 2) :
    S.contractSource (S.contractOutgoing c i) = S.contractCrossing c := by
  apply Subtype.ext
  dsimp [contractSource, contractOutgoing, contractCrossing]
  rw [if_neg (S.outgoing_ne_right c i)]
  exact D.outgoing_source c i

theorem contract_continuation_crossing (c : Fin D.nCrossing) (i : Fin 2) :
    S.contractPerm (S.contractIncoming c i) = S.contractOutgoing c (D.through c i) := by
  apply Subtype.ext
  rw [S.contractPerm_val]
  change (S.contractMap (D.continuation (D.incoming c i))).val = _
  rw [D.continuation_crossing, S.contractMap_of_ne _ (S.outgoing_ne_left _ _)]
  rfl

theorem contract_crossing_incidence (c : Fin D.nCrossing) (e : S.ContractArc) :
    (S.contractSource e = S.contractCrossing c ∨ S.contractTarget e = S.contractCrossing c) ↔
      (e = S.contractIncoming c 0 ∨ e = S.contractIncoming c 1 ∨
       e = S.contractOutgoing c 0 ∨ e = S.contractOutgoing c 1) := by
  simp only [← Subtype.val_inj]
  change ((if e.val = S.right then D.arcSource S.left else D.arcSource e.val) = D.crossingVertex c ∨
      D.arcTarget e.val = D.crossingVertex c) ↔
      (e.val = D.incoming c 0 ∨ e.val = D.incoming c 1 ∨
       e.val = D.outgoing c 0 ∨ e.val = D.outgoing c 1)
  by_cases h : e.val = S.right
  · simp only [h, if_pos rfl]
    simp only [(S.regular_start c).symm, (S.regular_end c).symm,
      (S.incoming_ne_right c 0).symm, (S.incoming_ne_right c 1).symm,
      (S.outgoing_ne_right c 0).symm, (S.outgoing_ne_right c 1).symm, or_self, ite_true, or_false]
  · rw [if_neg h]
    exact D.crossing_incidence_complete c e.val

theorem contract_regular_unique (v : S.ContractVertex)
    (hv : ∀ c, S.contractCrossing c ≠ v) :
    (∃! e : S.ContractArc, S.contractTarget e = v) ∧
    (∃! e : S.ContractArc, S.contractSource e = v) := by
  classical
  have hreg : ∀ c, D.crossingVertex c ≠ v.val := by
    intro c h
    exact hv c (Subtype.ext h)
  have hold := D.regular_degree_one v.val hreg
  have hin : ∃! e, D.arcTarget e = v.val := (filter_card_one_iff_unique _).mp hold.1
  have hout : ∃! e, D.arcSource e = v.val := (filter_card_one_iff_unique _).mp hold.2
  constructor
  · obtain ⟨e, he, hu⟩ := hin
    have hn : e ≠ S.left := by
      intro h; subst e; exact v.property he.symm
    refine ⟨⟨e, hn⟩, Subtype.ext he, ?_⟩
    intro f hf
    exact Subtype.ext (hu f.val (congrArg Subtype.val hf))
  · obtain ⟨e, he, hu⟩ := hout
    have hn : e ≠ S.right := by
      intro h; subst e
      exact v.property (he.symm.trans S.joint.symm)
    refine ⟨S.contractMap e, Subtype.ext ((S.contractSource_map e hn).trans he), ?_⟩
    intro f hf
    have heq : S.contractSourceLift f = e := hu _
      ((S.contractSource_val f).symm.trans (congrArg Subtype.val hf))
    rw [← heq, S.contractMap_sourceLift]

theorem contract_endpoints_distinct (e : S.ContractArc) :
    S.contractSource e ≠ S.contractTarget e := by
  intro h
  have hh := congrArg (fun v : S.ContractVertex => D.vertexPoint v.val) h
  change D.vertexPoint (S.contractSource e).val = D.vertexPoint (S.contractTarget e).val at hh
  by_cases he : e.val = S.right
  · have ha : D.vertexPoint (S.contractSource e).val = S.patch.a := by
      simp [contractSource, he, S.start_eq]
    have hc : D.vertexPoint (S.contractTarget e).val = S.patch.c := by
      simp [contractTarget, he, S.end_eq]
    rw [ha, hc] at hh
    exact S.chord_endpoints_ne hh
  · have hv := congrArg Subtype.val h
    change (if e.val = S.right then _ else _) = D.arcTarget e.val at hv
    rw [if_neg he] at hv
    exact D.arc_endpoints_distinct e.val hv

end EmptyTriangleSite
end
end DirectGLSSW.HOMFLY




