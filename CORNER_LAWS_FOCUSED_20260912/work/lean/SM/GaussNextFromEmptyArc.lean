import Mathlib.Data.List.Nodup
import SM.CrossingTransport
import SM.FiniteChiStability
import Mathlib.Topology.Order.LeftRightNhds
import SM.WeakTopology
import SM.WallSegmentStability
import SM.CuspParameters
import Mathlib.Data.Fin.Tuple.Basic
import SM.SinglePointTriple
import SM.CriticalSourceResponse
import Mathlib.Tactic
import SM.SegmentStability
import SM.G1Consequences
import SM.CrossingCriterion
import SM.ContinuousGeometry
import Mathlib.Topology.Instances.Sign
import SM.GenericTopology
import SM.CyclicChambers
import SM.PairVisits
import SM.Traversal
import SM.GaussCyclicGap
import Mathlib.Tactic.NormNum
import SM.BoundaryTripleSupports
import SM.CanonicalTripleSigns
import SM.SoftInsertionIndices
import SM.SoftInsertionSuccessors
import SM.SoftInsertionTuple
import SM.SoftParentEdges
import SM.SoftInheritedParameters
import SM.SoftParentPairStability
import SM.SoftLocalDeterminants
import SM.SoftFamilyG1
import SM.SoftFamilyLocalCrossing
import SM.SoftEdgeAvoidance
import SM.SoftCrossingClassification
import SM.SoftFamilyG2
import SM.SoftCrossingTransport
import SM.SoftParentOrder
import SM.SoftVisitOrder
import SM.SoftGaussLists
import SM.CycleFiltering
import SM.SoftGaussDeletion
import SM.SoftNewbornParameters
import SM.SoftNewbornVisitWindows
import SM.SoftParentArc
import SM.SoftNewbornVisits

/-! Ported verbatim from the previous executor's kernel-checked candidate
work/checks/GaussNextFromEmptyArc.body.lean (prototype SoftFamilyAssembly, kernel session 44274, receipt
SoftFamilyAssembly-prototype-result.json; axioms propext, Classical.choice, Quot.sound only). -/

namespace SM

/-- An empty oriented gap between distinct members of a finite linear order
identifies the actual sorted-list successor, including the last/first cut.
There is no lower bound of three on the number of members. -/
theorem sorted_next_of_no_cyclic_between {α : Type*} [LinearOrder α]
    (s : Finset α) {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hgap : ∀ x ∈ s,
      ¬ ((a < x ∧ x < b) ∨ (x < b ∧ b < a) ∨ (b < a ∧ a < x))) :
    s.sort.next a ((Finset.mem_sort _).mpr ha) = b := by
  let e := s.orderIsoOfFin rfl
  let ia := e.symm ⟨a, ha⟩
  let ib := e.symm ⟨b, hb⟩
  have hcoe {i j : Fin s.card} (h : i < j) : (e i).val < (e j).val :=
    Subtype.coe_lt_coe.mpr (e.strictMono h)
  have hsize : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hne : ia.val ≠ ib.val := by
    intro he
    apply hab
    have hv := congrArg (fun k : Fin s.card => (e k).val) (Fin.ext he : ia = ib)
    simpa only [ia, ib, e.apply_symm_apply] using hv
  have haN := ia.isLt
  have hbN := ib.isLt
  have hindex : ib.val = (ia.val + 1) % s.card := by
    by_cases hcut : ia.val + 1 < s.card
    · let j : Fin s.card := ⟨ia.val + 1, hcut⟩
      have haj : a < (e j).val := by
        have h : ia < j := by change ia.val < ia.val + 1; omega
        simpa only [ia, e.apply_symm_apply] using hcoe h
      have hnone := hgap (e j).val (e j).property
      have hnotBack : ¬ ib.val < ia.val := by
        intro h
        have hba : b < a := by
          simpa only [ia, ib, e.apply_symm_apply] using
            hcoe (show ib < ia from h)
        exact hnone (Or.inr (Or.inr ⟨hba, haj⟩))
      have hnotGap : ¬ j.val < ib.val := by
        intro h
        have hjb : (e j).val < b := by
          simpa only [ib, e.apply_symm_apply] using
            hcoe (show j < ib from h)
        exact hnone (Or.inl ⟨haj, hjb⟩)
      have hj : j.val = ia.val + 1 := rfl
      rw [Nat.mod_eq_of_lt hcut]
      omega
    · have hlast : ia.val + 1 = s.card := by omega
      let j : Fin s.card := ⟨0, hsize⟩
      have hnone := hgap (e j).val (e j).property
      have hnotPos : ¬ 0 < ib.val := by
        intro h
        have hjb : (e j).val < b := by
          simpa only [ib, e.apply_symm_apply] using
            hcoe (show j < ib from h)
        have hba : b < a := by
          have hi : ib < ia := by change ib.val < ia.val; omega
          simpa only [ia, ib, e.apply_symm_apply] using hcoe hi
        exact hnone (Or.inr (Or.inl ⟨hjb, hba⟩))
      rw [hlast, Nat.mod_self]
      omega
  let nextIndex : Fin s.card := ⟨(ia.val + 1) % s.card, Nat.mod_lt _ hsize⟩
  have hvalue : s.sort.next a ((Finset.mem_sort _).mpr ha) = (e nextIndex).val := by
    rw [List.next_eq_getElem]
    simp only [e, Finset.coe_orderIsoOfFin_apply, Finset.orderEmbOfFin_apply, Finset.length_sort]
    rfl
  have hi : nextIndex = ib := Fin.ext hindex.symm
  rw [hvalue, hi]
  simp only [ib, e.apply_symm_apply]

attribute [local instance] Classical.propDecidable

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- With distinct endpoints, no actual visit in the oriented traversal arc
forces adjacency in the complete cyclic Gauss sequence. Numerical wrap and
two-visit cycles are handled by the same finite sorted-order argument. -/
theorem gauss_next_of_no_visit_between (hn : 3 ≤ n) (hP : Generic P) {v w : Visit P}
    (hvw : v ≠ w)
    (hgap : ∀ u : Visit P,
      ¬ traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 u)
        (visitPosition hn hP.1 w)) :
    nextGaussVisit hn hP v = w := by
  classical
  let d : DecidableEq (Visit P) := inferInstance
  letI := visitLinearOrder hn hP
  have hs := sorted_next_of_no_cyclic_between (Finset.univ : Finset (Visit P))
    (Finset.mem_univ v) (Finset.mem_univ w) hvw (fun u _ => hgap u)
  rw [nextGaussVisit_eq_list_next]
  change @List.next (Visit P) d (Finset.univ : Finset (Visit P)).sort v
    ((Finset.mem_sort _).mpr (Finset.mem_univ v)) = w
  have hd : d = (fun a b : Visit P => LinearOrder.toDecidableEq a b) :=
    Subsingleton.elim _ _
  rw [hd]
  exact hs

theorem gauss_next_iff_no_visit_between (hn : 3 ≤ n) (hP : Generic P) {v w : Visit P}
    (hvw : v ≠ w) :
    nextGaussVisit hn hP v = w ↔
      ∀ u : Visit P,
        ¬ traversalBetween (visitPosition hn hP.1 v) (visitPosition hn hP.1 u)
          (visitPosition hn hP.1 w) :=
  ⟨fun h => gauss_next_no_visit_between hn hP h,
    gauss_next_of_no_visit_between hn hP hvw⟩

end SM
