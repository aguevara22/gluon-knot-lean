import DirectGLSSW.HOMFLY.PLDiagrams
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace DirectGLSSW.HOMFLY

open DirectGLSSW

structure BasedTraversal (D : PLLinkDiagram) where
  componentIndex : diagramComponent D ≃ Fin (diagramComponentCount D)
  baseArc : ∀ C : diagramComponent D,
    {e : Fin D.nArc // PermutationOrbits.componentOf D.continuation e = C}

noncomputable def chooseBasedTraversal (D : PLLinkDiagram) : BasedTraversal D := by
  classical
  letI : Fintype (diagramComponent D) :=
    PermutationOrbits.componentFintype D.continuation
  refine ⟨Fintype.equivFin (diagramComponent D), ?_⟩
  intro C
  exact Classical.choice (PermutationOrbits.fibreNonempty D.continuation C)

noncomputable def visitPosition {D : PLLinkDiagram} (T : BasedTraversal D)
    (e : Fin D.nArc) : ℕ := by
  classical
  let C := PermutationOrbits.componentOf D.continuation e
  let base := T.baseArc C
  exact ((PermutationOrbits.orbitEnumeration D.continuation base.val).symm
    ⟨e, (show PermutationOrbits.componentOf D.continuation e = C from rfl).trans
      base.property.symm⟩).val

noncomputable def visitRank {D : PLLinkDiagram} (T : BasedTraversal D)
    (e : Fin D.nArc) : Fin (diagramComponentCount D) × ℕ := by
  classical
  exact (T.componentIndex (PermutationOrbits.componentOf D.continuation e),
    visitPosition T e)

def rankBefore {n : ℕ} (x y : Fin n × ℕ) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

noncomputable def firstVisitedBranch {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) : Fin 2 := by
  classical
  exact if rankBefore (visitRank T (D.incoming c 0))
      (visitRank T (D.incoming c 1)) then 0 else 1

def badAt {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) : Prop :=
  firstVisitedBranch T c ≠ D.overBranch c

noncomputable def badCrossings {D : PLLinkDiagram} (T : BasedTraversal D) :
    Finset (Fin D.nCrossing) :=
  by classical exact Finset.univ.filter (badAt T)

def switchTraversal {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) : BasedTraversal (switchCrossing D c) where
  componentIndex := T.componentIndex
  baseArc := T.baseArc

@[simp] theorem visitPosition_reconstruct {D : PLLinkDiagram}
    (T : BasedTraversal D) (e : Fin D.nArc) :
    (D.continuation ^ visitPosition T e)
      (T.baseArc (PermutationOrbits.componentOf D.continuation e)).val = e := by
  classical
  let C := PermutationOrbits.componentOf D.continuation e
  let base := T.baseArc C
  let q := PermutationOrbits.orbitEnumeration D.continuation base.val
  have he : PermutationOrbits.componentOf D.continuation e =
      PermutationOrbits.componentOf D.continuation base.val := by
    calc
      PermutationOrbits.componentOf D.continuation e = C := rfl
      _ = PermutationOrbits.componentOf D.continuation base.val := base.property.symm
  let y : PermutationOrbits.Fibre D.continuation
      (PermutationOrbits.componentOf D.continuation base.val) := ⟨e, he⟩
  have hy : (q (q.symm y)).val = e := congrArg Subtype.val (q.apply_symm_apply y)
  have hy' : (PermutationOrbits.orbitEnumeration D.continuation base.val
      (q.symm y)).val = e := by simpa [q] using hy
  change (D.continuation ^ (q.symm y).val) base.val = e
  simpa only [q, PermutationOrbits.orbitEnumeration_apply_val] using hy'

theorem visitRank_injective {D : PLLinkDiagram} (T : BasedTraversal D) :
    Function.Injective (visitRank T) := by
  intro e f h
  have hcomp : PermutationOrbits.componentOf D.continuation e =
      PermutationOrbits.componentOf D.continuation f :=
    T.componentIndex.injective (congrArg Prod.fst h)
  have hpos : visitPosition T e = visitPosition T f := congrArg Prod.snd h
  have hbase := congrArg (fun C : diagramComponent D =>
    (⟨C, T.baseArc C⟩ : Σ C, {a : Fin D.nArc //
      PermutationOrbits.componentOf D.continuation a = C})) hcomp
  have hbaseval : (T.baseArc (PermutationOrbits.componentOf D.continuation e)).val =
      (T.baseArc (PermutationOrbits.componentOf D.continuation f)).val :=
    congrArg (fun z => z.2.val) hbase
  have he := visitPosition_reconstruct T e
  have hf := visitPosition_reconstruct T f
  rw [hpos.symm, hbaseval.symm] at hf
  exact he.symm.trans hf

theorem rankBefore_asymm {n : ℕ} {x y : Fin n × ℕ} :
    rankBefore x y → ¬ rankBefore y x := by
  intro h h'
  unfold rankBefore at *
  rcases h with h | ⟨hxy, hlt⟩ <;> rcases h' with h' | ⟨hyx, hlt'⟩ <;> omega

theorem rankBefore_total_of_ne {n : ℕ} {x y : Fin n × ℕ} (h : x ≠ y) :
    rankBefore x y ∨ rankBefore y x := by
  unfold rankBefore
  by_cases h₁ : x.1 < y.1
  · exact Or.inl (Or.inl h₁)
  · by_cases h₂ : y.1 < x.1
    · exact Or.inr (Or.inl h₂)
    · have heq : x.1 = y.1 := by omega
      have h₂ne : x.2 ≠ y.2 := by
        intro h₂
        exact h (Prod.ext heq h₂)
      by_cases hlt : x.2 < y.2
      · exact Or.inl (Or.inr ⟨heq, hlt⟩)
      · right
        right
        exact ⟨heq.symm, by omega⟩

 theorem firstVisitedBranch_is_first {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) :
    rankBefore (visitRank T (D.incoming c (firstVisitedBranch T c)))
      (visitRank T (D.incoming c (otherBranch (firstVisitedBranch T c)))) := by
  classical
  let x := visitRank T (D.incoming c 0)
  let y := visitRank T (D.incoming c 1)
  have hxy : x ≠ y := by
    intro h
    have : D.incoming c 0 = D.incoming c 1 := visitRank_injective T h
    exact D.four_ports_distinct c |>.1 this
  by_cases h : rankBefore x y
  · simpa [firstVisitedBranch, x, y, h] using h
  · have hyx : rankBefore y x := (rankBefore_total_of_ne hxy).resolve_left h
    simpa [firstVisitedBranch, x, y, h, otherBranch_zero, otherBranch_one] using hyx

@[simp] theorem visitRank_switch {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (e : Fin D.nArc) :
    visitRank (switchTraversal T c) e = visitRank T e := by
  rfl

@[simp] theorem switch_crossing_count {D : PLLinkDiagram}
    (c : Fin D.nCrossing) : (switchCrossing D c).nCrossing = D.nCrossing := by
  rfl

@[simp] theorem firstVisitedBranch_switch {D : PLLinkDiagram}
    (T : BasedTraversal D) (c d : Fin D.nCrossing) :
    firstVisitedBranch (switchTraversal T c) d = firstVisitedBranch T d := by
  rfl

theorem neq_otherBranch_iff (x y : Fin 2) :
    x ≠ otherBranch y ↔ ¬ x ≠ y := by
  fin_cases x <;> fin_cases y <;> simp

theorem firstBranch_bad_toggle {D : PLLinkDiagram}
    (T : BasedTraversal D) (c : Fin D.nCrossing) :
    (firstVisitedBranch T c ≠ (switchCrossing D c).overBranch c) ↔
      ¬ badAt T c := by
  simp only [switchCrossing, Function.update_self, badAt]
  exact neq_otherBranch_iff _ _

theorem badAt_switch_toggle {D : PLLinkDiagram}
    (T : BasedTraversal D) (c : Fin D.nCrossing) :
    badAt (switchTraversal T c) c ↔ ¬ badAt T c := by
  simp only [badAt, firstVisitedBranch_switch, switchCrossing, Function.update_self]
  exact neq_otherBranch_iff _ _

theorem badAt_switch_same {D : PLLinkDiagram}
    (T : BasedTraversal D) (c d : Fin D.nCrossing) (h : d ≠ c) :
    badAt (switchTraversal T c) d ↔ badAt T d := by
  simp only [badAt, firstVisitedBranch_switch, switchCrossing,
    Function.update_of_ne h]

theorem badCrossings_switch_erase {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (hc : c ∈ badCrossings T) :
    badCrossings (switchTraversal T c) = (badCrossings T).erase c := by
  classical
  have hc' : badAt T c := by
    simpa [badCrossings] using hc
  ext d
  simp only [badCrossings, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase]
  by_cases h : d = c
  · subst d
    simp [badAt_switch_toggle, hc']
  · simp [h, badAt_switch_same T c d h]

theorem badCrossings_switch_card {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (hc : c ∈ badCrossings T) :
    (badCrossings (switchTraversal T c)).card + 1 = (badCrossings T).card := by
  rw [badCrossings_switch_erase T c hc]
  exact Finset.card_erase_add_one hc

theorem badCrossings_eq_empty_iff_firstVisited_over {D : PLLinkDiagram}
    (T : BasedTraversal D) :
    badCrossings T = ∅ ↔ ∀ c, firstVisitedBranch T c = D.overBranch c := by
  classical
  constructor
  · intro h c
    by_contra hn
    have hc : c ∈ badCrossings T := by simp [badCrossings, badAt, hn]
    rw [h] at hc
    exact Finset.not_mem_empty c hc
  · intro h
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro c hc
    have := (Finset.mem_filter.mp hc).2
    exact this (h c)

theorem triangleUnknot_badCrossings_eq_empty (T : BasedTraversal triangleUnknot) :
    badCrossings T = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro c hc
  exact Fin.elim0 c

theorem triangleUnknot_chooseBasedTraversal_badCrossings_eq_empty :
    badCrossings (chooseBasedTraversal triangleUnknot) = ∅ := by
  exact triangleUnknot_badCrossings_eq_empty _

theorem emptyDiagram_badCrossings_vacuous :
    ∀ c : Fin emptyDiagram.nCrossing, False := by
  intro c
  exact Fin.elim0 c

end DirectGLSSW.HOMFLY




































