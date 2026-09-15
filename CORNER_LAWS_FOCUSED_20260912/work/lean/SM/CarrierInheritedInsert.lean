import SM.GaussWord
import SM.SortedCyclicGap
import Mathlib.Tactic
import SM.GaussCyclicGap
import Mathlib.GroupTheory.Perm.Cycle.Basic
import SM.CrossingPair
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.List.Cycle
import Mathlib.Data.List.Nodup
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Data.Set.Function
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import SM.InterlaceSupports
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import SM.CarrierMarks
import SM.CarrierSuccessor
import SM.CarrierVisitTwin
import SM.CarrierSmoothing
import SM.CarrierSingleSwitch
import SM.CarrierOrbitRefinement
import SM.CycleFiltering
import SM.CarrierFilteredCycles
import SM.CarrierCycleList
import SM.CarrierSplitList
import SM.CarrierSingleSupport
import SM.CarrierInheritedOrder
import SM.CarrierCurrentCycle
import SM.CarrierAmbientTransport
import SM.CarrierUnchangedComponent
import SM.CarrierInsertOrbits
import SM.CarrierComponentFibers
import SM.CarrierFiberCard
import SM.CarrierSameArc
import SM.CarrierSortedArcLists
import SM.CarrierMarkedArcLists
import SM.CarrierPendingPairs

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/CarrierInheritedInsert.body.lean (prototype CarrierComponentCount, kernel session 35180, receipt
CarrierComponentCount-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM.Carrier

noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/-- If an actual new-owner block lies in one old-owner block, its inherited
cycle is obtained by filtering that old inherited cycle. The absorption is
proved on the full original marked circle before restricting to the old block. -/
theorem componentCycle_filter_of_owner_imp (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T U : Finset (Crossing P))
    (q : Component hn hP T) (r : Component hn hP U)
    (hsub : ∀ m : Mark P, owner hn hP U m = r → owner hn hP T m = q) :
    componentCycle hn hP U r =
      (componentCycle hn hP T q).filter (fun m => decide (owner hn hP U m = r)) := by
  unfold componentCycle
  rw [Cycle.filter_filter]
  apply congrArg (fun p : Mark P → Bool => (markCycle hn hP).filter p)
  funext m
  by_cases hm : owner hn hP U m = r
  · simp only [hm, hsub m hm, decide_true, Bool.and_self]
  · simp only [hm, decide_false, Bool.false_and]

/-- The affected new inherited cycles are the literal two owner-filtered child
lists, using the same actual original rotation as the insertion orbit data.
Full-circle filter absorption justifies the restriction to the old component. -/
theorem componentCycle_insert_child_cycles (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v))) :
    ∃ (k : ℕ) (A B : List (Mark P)),
      (markList hn hP).rotate k = Sum.inr v :: (A ++ Sum.inr (visitTwin v) :: B) ∧
      let q := owner hn hP T (Sum.inr v)
      let AL := A.filter (fun m => decide (owner hn hP T m = q))
      let BL := B.filter (fun m => decide (owner hn hP T m = q))
      componentCycle hn hP T q =
        (Sum.inr v :: (AL ++ Sum.inr (visitTwin v) :: BL) : Cycle (Mark P)) ∧
      componentCycle hn hP (insert v.1 T)
          (owner hn hP (insert v.1 T) (Sum.inr v)) =
        (Sum.inr v :: BL : Cycle (Mark P)) ∧
      componentCycle hn hP (insert v.1 T)
          (owner hn hP (insert v.1 T) (Sum.inr (visitTwin v))) =
        (Sum.inr (visitTwin v) :: AL : Cycle (Mark P)) ∧
      (∀ m : Mark P, owner hn hP (insert v.1 T) m =
          owner hn hP (insert v.1 T) (Sum.inr v) ↔ m ∈ Sum.inr v :: BL) ∧
      (∀ m : Mark P, owner hn hP (insert v.1 T) m =
          owner hn hP (insert v.1 T) (Sum.inr (visitTwin v)) ↔
          m ∈ Sum.inr (visitTwin v) :: AL) ∧
      (∀ m : Mark P, m ∈ Sum.inr v :: BL →
        smoothingSuccessor hn hP (insert v.1 T) m = (Sum.inr v :: BL).formPerm m) ∧
      (∀ m : Mark P, m ∈ Sum.inr (visitTwin v) :: AL →
        smoothingSuccessor hn hP (insert v.1 T) m =
          (Sum.inr (visitTwin v) :: AL).formPerm m) := by
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  let q := owner hn hP T a
  obtain ⟨k, A, B, hrot, hL, hR, hd, hownerL, hownerR, hstepL, hstepR⟩ :=
    smoothingSuccessor_insert_child_data hn hP T hI v hv hc
  let AL := A.filter (fun m => decide (owner hn hP T m = q))
  let BL := B.filter (fun m => decide (owner hn hP T m = q))
  have hparent : componentCycle hn hP T q = (a :: (AL ++ b :: BL) : Cycle (Mark P)) :=
    componentCycle_eq_filtered_splitList hn hP T q k a b A B hrot rfl hc.symm
  have hN := componentCycle_list_nodup hn hP T q (a :: (AL ++ b :: BL)) hparent
  have hsubL (m : Mark P)
      (hm : owner hn hP (insert v.1 T) m = owner hn hP (insert v.1 T) a) :
      owner hn hP T m = q := by
    rcases List.mem_cons.mp ((hownerL m).mp hm) with hm | hm
    · subst m
      rfl
    · exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hsubR (m : Mark P)
      (hm : owner hn hP (insert v.1 T) m = owner hn hP (insert v.1 T) b) :
      owner hn hP T m = q := by
    rcases List.mem_cons.mp ((hownerR m).mp hm) with hm | hm
    · subst m
      exact hc.symm
    · exact of_decide_eq_true (List.mem_filter.mp hm).2
  have hpL : (fun m => decide (owner hn hP (insert v.1 T) m =
      owner hn hP (insert v.1 T) a)) = (fun m => decide (m ∈ a :: BL)) := by
    funext m
    exact decide_eq_decide.mpr (hownerL m)
  have hpR : (fun m => decide (owner hn hP (insert v.1 T) m =
      owner hn hP (insert v.1 T) b)) = (fun m => decide (m ∈ b :: AL)) := by
    funext m
    exact decide_eq_decide.mpr (hownerR m)
  have hcL : componentCycle hn hP (insert v.1 T) (owner hn hP (insert v.1 T) a) =
      (a :: BL : Cycle (Mark P)) := by
    rw [componentCycle_filter_of_owner_imp hn hP T (insert v.1 T) q
      (owner hn hP (insert v.1 T) a) hsubL, hparent, Cycle.filter_coe, hpL]
    refine congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_left a b AL BL hN))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  have hcR : componentCycle hn hP (insert v.1 T) (owner hn hP (insert v.1 T) b) =
      (b :: AL : Cycle (Mark P)) := by
    rw [componentCycle_filter_of_owner_imp hn hP T (insert v.1 T) q
      (owner hn hP (insert v.1 T) b) hsubR, hparent, Cycle.filter_coe, hpR]
    refine (congrArg (fun l : List (Mark P) => (l : Cycle (Mark P)))
      (Eq.trans ?_ (filter_splitList_right a b AL BL hN))).trans
      (Cycle.coe_eq_coe.mpr (List.isRotated_concat b AL))
    apply List.filter_congr
    intro m _
    exact decide_eq_decide.mpr Iff.rfl
  exact ⟨k, A, B, hrot, hparent, hcL, hcR, hownerL, hownerR, hstepL, hstepR⟩

/-- A proved inherited-cycle representative transports the complete formPerm
through its Nodup subtype, without a dependent rewrite or an order assumption. -/
theorem componentCycle_formPerm_eq_of_list (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (q : Component hn hP T)
    (L : List (Mark P)) (hL : componentCycle hn hP T q = (L : Cycle (Mark P))) :
    (componentCycle hn hP T q).formPerm (componentCycle_nodup hn hP T q) = L.formPerm := by
  have hN := componentCycle_list_nodup hn hP T q L hL
  have he : (⟨componentCycle hn hP T q, componentCycle_nodup hn hP T q⟩ :
      {s : Cycle (Mark P) // s.Nodup}) = ⟨(L : Cycle (Mark P)), hN⟩ := Subtype.ext hL
  have hp := congrArg
    (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
  change (componentCycle hn hP T q).formPerm (componentCycle_nodup hn hP T q) =
    (L : Cycle (Mark P)).formPerm hN at hp
  exact hp.trans (Cycle.formPerm_coe L hN)

/-- Inserting a fresh actual crossing whose incoming marks currently share an
owner preserves the inherited-order invariant. The affected cycles are derived
by full-circle filtering, and every other old owner's cycle and action agree.
No independence premise or supplied component correspondence is used. -/
theorem inheritsMarkOrder_insert (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (T : Finset (Crossing P)) (hI : InheritsMarkOrder hn hP T)
    (v : Visit P) (hv : v.1 ∉ T)
    (hc : owner hn hP T (Sum.inr v) = owner hn hP T (Sum.inr (visitTwin v))) :
    InheritsMarkOrder hn hP (insert v.1 T) := by
  rw [inheritsMarkOrder_iff_formPerm]
  intro r z hz
  have hr := (mem_componentCycle hn hP (insert v.1 T) r z).mp hz
  subst r
  let a : Mark P := Sum.inr v
  let b : Mark P := Sum.inr (visitTwin v)
  let q := owner hn hP T a
  by_cases hqz : owner hn hP T z = q
  · obtain ⟨k, A, B, hrot, hparent, hcL, hcR, hownerL, hownerR, hstepL, hstepR⟩ :=
      componentCycle_insert_child_cycles hn hP T hI v hv hc
    let AL := A.filter (fun m => decide (owner hn hP T m = q))
    let BL := B.filter (fun m => decide (owner hn hP T m = q))
    have hzP : z ∈ a :: (AL ++ b :: BL) :=
      (componentCycle_list_mem_iff hn hP T q (a :: (AL ++ b :: BL)) hparent z).mpr hqz
    have hzchild : z ∈ a :: BL ∨ z ∈ b :: AL := by
      rcases List.mem_cons.mp hzP with he | hzP
      · exact Or.inl (List.mem_cons.mpr (Or.inl he))
      · rcases List.mem_append.mp hzP with hzA | hzB
        · exact Or.inr (List.mem_cons_of_mem b hzA)
        · rcases List.mem_cons.mp hzB with he | hzB
          · exact Or.inr (List.mem_cons.mpr (Or.inl he))
          · exact Or.inl (List.mem_cons_of_mem a hzB)
    rcases hzchild with hzL | hzR
    · have hcz : componentCycle hn hP (insert v.1 T) (owner hn hP (insert v.1 T) z) =
          (a :: BL : Cycle (Mark P)) := by
        rw [(hownerL z).mpr hzL]
        exact hcL
      rw [componentCycle_formPerm_eq_of_list hn hP (insert v.1 T)
        (owner hn hP (insert v.1 T) z) (a :: BL) hcz]
      exact (hstepL z hzL).symm
    · have hcz : componentCycle hn hP (insert v.1 T) (owner hn hP (insert v.1 T) z) =
          (b :: AL : Cycle (Mark P)) := by
        rw [(hownerR z).mpr hzR]
        exact hcR
      rw [componentCycle_formPerm_eq_of_list hn hP (insert v.1 T)
        (owner hn hP (insert v.1 T) z) (b :: AL) hcz]
      exact (hstepR z hzR).symm
  · have hcz := componentCycle_insert_unaffected hn hP T v hv hc
      (owner hn hP T z) hqz z rfl
    have he : (⟨componentCycle hn hP (insert v.1 T) (owner hn hP (insert v.1 T) z),
        componentCycle_nodup hn hP (insert v.1 T) (owner hn hP (insert v.1 T) z)⟩ :
        {s : Cycle (Mark P) // s.Nodup}) =
        ⟨componentCycle hn hP T (owner hn hP T z),
          componentCycle_nodup hn hP T (owner hn hP T z)⟩ := Subtype.ext hcz
    have hp := congrArg
      (fun s : {s : Cycle (Mark P) // s.Nodup} => s.val.formPerm s.property) he
    change (componentCycle hn hP (insert v.1 T) (owner hn hP (insert v.1 T) z)).formPerm
        (componentCycle_nodup hn hP (insert v.1 T) (owner hn hP (insert v.1 T) z)) =
      (componentCycle hn hP T (owner hn hP T z)).formPerm
        (componentCycle_nodup hn hP T (owner hn hP T z)) at hp
    rw [hp]
    have ho := (inheritsMarkOrder_iff_formPerm hn hP T).mp hI (owner hn hP T z) z
      (mem_componentCycle_owner hn hP T z)
    exact ho.trans ((smoothingSuccessor_insert_eqOn_owner hn hP T v hv hc
      (owner hn hP T z) hqz) rfl).symm

end
end SM.Carrier
