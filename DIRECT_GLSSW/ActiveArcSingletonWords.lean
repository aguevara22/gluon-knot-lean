import ActiveArcClosedChildGeometry
import ActiveArcGammaM
import DirectGLSSW.OrbitWordPrerequisite
import DirectGLSSW.DaughterRootRotation
import DirectGLSSW.DaughterRootAmplitude

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.SingletonWords
open DirectGLSSW PermutationOrbits FiniteCycleOrder Nonalternation
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q)

abbrev leftRank := actualEndpoint q hR (c,false)
abbrev rightRank := actualEndpoint q hR (c,true)

theorem rank_lt : leftRank q hR c < rightRank q hR c := by
  letI := eventOrder q hR.noTriple
  apply (eventOrderIso q hR).symm.strictMono
  exact (event_lt_iff q hR.noTriple _ _).mpr (Or.inl c.property.1)

theorem split_intertwines (i : Fin (Fintype.card (Event q))) :
    eventEnumeration q hR (splitPerm (leftRank q hR c) (rightRank q hR c) i)=
      incoming q hR.noTriple {c} (eventEnumeration q hR i) := by
  change eventEnumeration q hR (cyclicSuccessorPerm _
    (ChordNonalternation.chordSwap (actualEndpoint q hR) c i))=_
  rw [successor_intertwines,singleton_intertwines]
  rfl

def intervalEvents : Fin ((rightRank q hR c).val-(leftRank q hR c).val) → Event q :=
  fun i => eventEnumeration q hR (intervalOrderIso _ _ (rank_lt q hR c) i).val

def complementEvents : Fin (Fintype.card (Event q)-
    ((rightRank q hR c).val-(leftRank q hR c).val)) → Event q :=
  fun i => eventEnumeration q hR (complementOrderIso _ _ (rank_lt q hR c) i).val

theorem intervalEvents_injective : Function.Injective (intervalEvents q hR c) := by
  intro i j h
  apply (intervalOrderIso _ _ (rank_lt q hR c)).injective
  apply Subtype.ext
  exact (eventEnumeration q hR).injective h

theorem complementEvents_injective : Function.Injective (complementEvents q hR c) := by
  intro i j h
  apply (complementOrderIso _ _ (rank_lt q hR c)).injective
  apply Subtype.ext
  exact (eventEnumeration q hR).injective h

theorem intervalEvents_step (i : Fin ((rightRank q hR c).val-(leftRank q hR c).val)) :
    incoming q hR.noTriple {c} (intervalEvents q hR c i)=
      intervalEvents q hR c (cyclicSuccessor i) := by
  unfold intervalEvents
  rw [← split_intertwines]
  exact congrArg (eventEnumeration q hR)
    (congrArg Subtype.val (intervalOrderIso_successor _ _ (rank_lt q hR c) i))

theorem complementEvents_step (i : Fin (Fintype.card (Event q)-
    ((rightRank q hR c).val-(leftRank q hR c).val))) :
    incoming q hR.noTriple {c} (complementEvents q hR c i)=
      complementEvents q hR c (cyclicSuccessor i) := by
  unfold complementEvents
  rw [← split_intertwines]
  exact congrArg (eventEnumeration q hR)
    (congrArg Subtype.val (complementOrderIso_successor _ _ (rank_lt q hR c) i))

def eventZero : Fin (Fintype.card (Event q)) :=
  ⟨0,Fintype.card_pos_iff.mpr ⟨start q⟩⟩

theorem eventEnumeration_zero : eventEnumeration q hR (eventZero q)=start q := by
  letI := eventOrder q hR.noTriple
  apply le_antisymm
  · have h : eventZero q ≤ (eventOrderIso q hR).symm (start q) :=
      Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
    simpa only [OrderIso.apply_symm_apply] using (eventOrderIso q hR).monotone h
  · exact start_le q hR.noTriple _

theorem complementEvents_zero : complementEvents q hR c
    ⟨0,(daughterLengths_pos _ _ (rank_lt q hR c)).2⟩=start q := by
  unfold complementEvents
  have he : (complementOrderIso (leftRank q hR c) (rightRank q hR c)
    (rank_lt q hR c) ⟨0,(daughterLengths_pos _ _ (rank_lt q hR c)).2⟩).val=eventZero q := by
    apply Fin.ext
    simp [complementOrderIso,eventZero]
  rw [he,eventEnumeration_zero]

theorem interval_orbitWord :
    orbitWord (incoming q hR.noTriple {c})
      (intervalEvents q hR c ⟨0,(daughterLengths_pos _ _ (rank_lt q hR c)).1⟩)=
        List.ofFn (intervalEvents q hR c) :=
  orbitWord_eq_of_injective_cyclicSuccessor _ (daughterLengths_pos _ _ (rank_lt q hR c)).1
    _ (intervalEvents_injective q hR c) (intervalEvents_step q hR c)

theorem open_orbitWord : orbitWord (incoming q hR.noTriple {c}) (start q)=
    List.ofFn (complementEvents q hR c) := by
  have hh := orbitWord_eq_of_injective_cyclicSuccessor (incoming q hR.noTriple {c})
    (daughterLengths_pos _ _ (rank_lt q hR c)).2 _
    (complementEvents_injective q hR c) (complementEvents_step q hR c)
  rw [complementEvents_zero] at hh
  exact hh

theorem intervalEvents_mem (x : Event q) :
    x ∈ List.ofFn (intervalEvents q hR c) ↔
      (eventEnumeration q hR).symm x ∈ intervalSide (leftRank q hR c) (rightRank q hR c) := by
  constructor
  · intro hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simp only [intervalEvents,Equiv.symm_apply_apply]
    exact (intervalOrderIso _ _ (rank_lt q hR c) i).property
  · intro hx
    let z : intervalSide (leftRank q hR c) (rightRank q hR c) :=
      ⟨(eventEnumeration q hR).symm x,hx⟩
    refine List.mem_ofFn.mpr ⟨(intervalOrderIso _ _ (rank_lt q hR c)).symm z,?_⟩
    simp [intervalEvents,z]

theorem complementEvents_mem (x : Event q) :
    x ∈ List.ofFn (complementEvents q hR c) ↔
      (eventEnumeration q hR).symm x ∈ complementSide (leftRank q hR c) (rightRank q hR c) := by
  constructor
  · intro hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    simp only [complementEvents,Equiv.symm_apply_apply]
    exact (complementOrderIso _ _ (rank_lt q hR c) i).property
  · intro hx
    let z : complementSide (leftRank q hR c) (rightRank q hR c) :=
      ⟨(eventEnumeration q hR).symm x,hx⟩
    refine List.mem_ofFn.mpr ⟨(complementOrderIso _ _ (rank_lt q hR c)).symm z,?_⟩
    simp [complementEvents,z]

theorem intervalEvents_sorted : letI := eventOrder q hR.noTriple;
    (List.ofFn (intervalEvents q hR c)).Sorted (· < ·) := by
  letI := eventOrder q hR.noTriple
  apply List.sorted_lt_ofFn_iff.mpr
  intro i j hij
  exact (eventOrderIso q hR).strictMono ((intervalOrderIso _ _ (rank_lt q hR c)).strictMono hij)

theorem complementEvents_sorted : letI := eventOrder q hR.noTriple;
    (List.ofFn (complementEvents q hR c)).Sorted (· < ·) := by
  letI := eventOrder q hR.noTriple
  apply List.sorted_lt_ofFn_iff.mpr
  intro i j hij
  exact (eventOrderIso q hR).strictMono ((complementOrderIso _ _ (rank_lt q hR c)).strictMono hij)

theorem rank_interval_iff (x : Event q) :
    (eventEnumeration q hR).symm x ∈ intervalSide (leftRank q hR c) (rightRank q hR c) ↔
      ((eventOrder q hR.noTriple).lt (Sum.inr (c,false)) x ∧
        (eventOrder q hR.noTriple).le x (Sum.inr (c,true))) := by
  letI := eventOrder q hR.noTriple
  change ((eventOrderIso q hR).symm (Sum.inr (c,false)) < (eventOrderIso q hR).symm x ∧
    (eventOrderIso q hR).symm x ≤ (eventOrderIso q hR).symm (Sum.inr (c,true))) ↔ _
  simp only [OrderIso.lt_iff_lt,OrderIso.le_iff_le]

theorem retainedEvents_eq_filtered (S : Finset (Crossing q)) (root : Event q) :
    List.ofFn (RetainedWords.cornerEvent q hR S root)=
      (orbitWord (incoming q hR.noTriple S) root).filter
        (fun z => decide (retained q S z)) := by
  let E := RetainedWords.enumeration q hR S root
  have hcoords :
      List.ofFn (fun i : Fin (Fintype.card (RetainedWords.Corner q hR S root)) => (E i).val)=
        (List.ofFn (fun i : RetainedWords.Coord q hR S root => i)).filter
          (fun i => decide (retained q S (RetainedWords.eventAt q hR S root i))) := by
    have hs₁ : (List.ofFn (fun i : Fin (Fintype.card (RetainedWords.Corner q hR S root)) => (E i).val)).Sorted (· < ·) :=
      List.sorted_lt_ofFn_iff.mpr E.strictMono
    have hs₂ : ((List.ofFn (fun i : RetainedWords.Coord q hR S root => i)).filter
        (fun i => decide (retained q S (RetainedWords.eventAt q hR S root i)))).Sorted (· < ·) :=
      (List.sorted_lt_ofFn_iff.mpr strictMono_id).filter _
    apply List.Sorted.eq_of_mem_iff hs₁ hs₂
    intro i
    constructor
    · intro hi
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hi
      have hret := (E j).property
      rw [hj] at hret
      exact List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨i,rfl⟩,by simpa using hret⟩
    · intro hi
      obtain ⟨_,hret⟩ := List.mem_filter.mp hi
      have hret' : retained q S (RetainedWords.eventAt q hR S root i) := by simpa using hret
      let v : RetainedWords.Corner q hR S root := ⟨i,hret'⟩
      exact List.mem_ofFn.mpr ⟨E.symm v,by simp [v]⟩
  have hmapped := congrArg (List.map (RetainedWords.eventAt q hR S root)) hcoords
  have hevents : List.ofFn (RetainedWords.cornerEvent q hR S root)=
      (orbitWord (incoming q hR.noTriple S) root).filter (fun z => decide (retained q S z)) := by
    change List.ofFn (fun i => RetainedWords.eventAt q hR S root (E i).val)=
      (List.ofFn (RetainedWords.eventAt q hR S root)).filter (fun z => decide (retained q S z))
    simpa only [List.map_ofFn,Function.comp_def] using hmapped.trans
      (DaughterPointListFilter.map_filter_comp (RetainedWords.eventAt q hR S root)
        (fun z => decide (retained q S z)) (List.ofFn fun i : RetainedWords.Coord q hR S root => i))
  exact hevents

theorem retainedWord_eq_filtered (S : Finset (Crossing q)) (root : Event q) :
    List.ofFn (RetainedWords.vertex q hR S root)=
      ((orbitWord (incoming q hR.noTriple S) root).filter
        (fun z => decide (retained q S z))).map (eventPoint q) := by
  have hpoints := congrArg (List.map (eventPoint q)) (retainedEvents_eq_filtered q hR S root)
  simpa [RetainedWords.vertex,List.map_ofFn] using hpoints

theorem filtered_head (S : Finset (Crossing q)) (root : Event q) (hr : retained q S root) :
    ((orbitWord (incoming q hR.noTriple S) root).filter
      (fun z => decide (retained q S z))).head?=some root := by
  rw [← retainedEvents_eq_filtered]
  have hp := RetainedWords.cornerCount_pos q hR S root hr
  simp only [List.head?_eq_getElem?,List.getElem?_ofFn,dif_pos hp]
  exact congrArg some (RetainedWords.cornerEvent_zero q hR S root hr)

theorem nodup_rotated_eq_of_head {α : Type*} {l r : List α}
    (hl : l.Nodup) (hrot : l ~r r) (hh : l.head?=r.head?) : l=r := by
  obtain ⟨n,hn⟩:=hrot
  cases l with
  | nil => simpa using hn
  | cons v vs =>
    have hp : 0<(v::vs).length := by simp
    have hm : n%(v::vs).length<(v::vs).length := Nat.mod_lt _ hp
    rw [← hn] at hh
    have hh0 : (v::vs)[n%(v::vs).length]?=(v::vs)[0]? := by
      simpa only [List.head?_eq_getElem?,List.getElem?_rotate hp,Nat.zero_add] using hh.symm
    have he : (v::vs)[n%(v::vs).length]=(v::vs)[0] := by
      apply Option.some.inj
      simpa only [List.getElem?_eq_getElem hm,List.getElem?_eq_getElem hp] using hh0
    have hn0 : n%(v::vs).length=0 := hl.getElem_inj_iff.mp he
    rw [← List.rotate_mod,hn0,List.rotate_zero] at hn
    exact hn

variable (hfirst : c.val.1=0) (hcut : c.val.2.val=a)

def closedSortedEvents (i : Fin (a+1)) : Event q :=
  if hi : i.val<a then Sum.inl ⟨i.val+1,by clear hfirst hcut;omega⟩ else Sum.inr (c,true)

/-- The initial anchor and the selected left visit are both retained. -/
def tinyParentEvents (i : Fin (b+3)) : Event q :=
  if i.val=0 then start q else if i.val=1 then Sum.inr (c,false)
    else Sum.inl ⟨a+i.val-1,by clear hfirst hcut;have := i.isLt;omega⟩

include hfirst hcut in
theorem anchor_interval_iff (i : Fin (a+b+2)) :
    (eventEnumeration q hR).symm (Sum.inl i) ∈
      intervalSide (leftRank q hR c) (rightRank q hR c) ↔ (0 < i.val ∧ i.val ≤ a) := by
  letI := eventOrder q hR.noTriple
  rw [rank_interval_iff]
  simp only [← not_lt]
  rw [event_lt_iff,event_lt_iff]
  have hl := (leftParameter_spec q c).1
  have hr := (rightParameter_spec q c).1
  change ((c.val.1.val < i.val ∨ c.val.1.val=i.val ∧ leftParameter q c < (0:ℝ)) ∧
    ¬ (c.val.2.val < i.val ∨ c.val.2.val=i.val ∧ rightParameter q c < (0:ℝ))) ↔ _
  rw [hfirst]
  simp [hcut,not_lt_of_ge (le_of_lt hl),not_lt_of_ge (le_of_lt hr)]

theorem left_not_interval : (eventEnumeration q hR).symm (Sum.inr (c,false)) ∉
    intervalSide (leftRank q hR c) (rightRank q hR c) := by
  change ¬ ((leftRank q hR c).val<(leftRank q hR c).val ∧ _)
  simp

theorem right_in_interval : (eventEnumeration q hR).symm (Sum.inr (c,true)) ∈
    intervalSide (leftRank q hR c) (rightRank q hR c) := by
  exact ⟨rank_lt q hR c,le_rfl⟩

include hcut in
theorem closedSortedEvents_sorted : letI := eventOrder q hR.noTriple;
    (List.ofFn (closedSortedEvents q c)).Sorted (· < ·) := by
  letI := eventOrder q hR.noTriple
  apply List.sorted_lt_ofFn_iff.mpr
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val<j.val := hij
  unfold closedSortedEvents
  split_ifs with hiA hjA
  · exact (event_lt_iff q hR.noTriple _ _).mpr (Or.inl (by simpa [edgeTag] using hij'))
  · apply (event_lt_iff q hR.noTriple _ _).mpr
    have hr := (rightParameter_spec q c).1
    change i.val+1<c.val.2.val ∨ i.val+1=c.val.2.val ∧ (0:ℝ)<rightParameter q c
    rw [hcut]
    rcases lt_or_eq_of_le (show i.val+1≤a by omega) with hh|hh
    · exact Or.inl hh
    · exact Or.inr ⟨hh,hr⟩
  · omega
  · omega

include hfirst hcut in
theorem tinyParentEvents_sorted : letI := eventOrder q hR.noTriple;
    (List.ofFn (tinyParentEvents q c)).Sorted (· < ·) := by
  letI := eventOrder q hR.noTriple
  apply List.sorted_lt_ofFn_iff.mpr
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hij' : i.val<j.val := hij
  have ha := Split.cut_positive q c hcut
  have hl := (leftParameter_spec q c).1
  unfold tinyParentEvents
  split_ifs <;> apply (event_lt_iff q hR.noTriple _ _).mpr <;>
    simp [edgeTag,parameter,visitEdge,visitParameter,start,hfirst,hl] <;> omega

include hfirst hcut in
theorem closedSortedEvents_mem (x : Event q) :
    x ∈ List.ofFn (closedSortedEvents q c) ↔
      (eventEnumeration q hR).symm x ∈ intervalSide (leftRank q hR c) (rightRank q hR c) ∧ retained q {c} x := by
  cases x with
  | inl k =>
    rw [anchor_interval_iff q hR c hfirst hcut]
    simp only [retained,true_and,and_true]
    constructor
    · intro hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hx
      by_cases hia : i.val<a
      · simp only [closedSortedEvents,dif_pos hia] at hi
        have hk := congrArg Fin.val (Sum.inl.inj hi)
        dsimp at hk
        omega
      · simp only [closedSortedEvents,dif_neg hia] at hi
        cases hi
    · intro hk
      let i : Fin (a+1) := ⟨k.val-1,by omega⟩
      refine List.mem_ofFn.mpr ⟨i,?_⟩
      have hia : i.val<a := by dsimp [i];omega
      simp only [closedSortedEvents,dif_pos hia]
      congr 1
      apply Fin.ext
      dsimp [i]
      omega
  | inr v =>
    rcases v with ⟨d,z⟩
    constructor
    · intro hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hx
      by_cases hia : i.val<a
      · simp only [closedSortedEvents,dif_pos hia] at hi
        cases hi
      · simp only [closedSortedEvents,dif_neg hia] at hi
        have hv:=Sum.inr.inj hi
        cases hv
        exact ⟨right_in_interval q hR c,by simp [retained]⟩
    · intro hx
      have hd : d=c := by simpa [retained] using hx.2
      subst d
      cases z with
      | false => exact (left_not_interval q hR c hx.1).elim
      | true => exact List.mem_ofFn.mpr ⟨⟨a,by omega⟩,by simp [closedSortedEvents]⟩

include hfirst hcut in
theorem tinyParentEvents_mem (x : Event q) :
    x ∈ List.ofFn (tinyParentEvents q c) ↔
      (eventEnumeration q hR).symm x ∈ complementSide (leftRank q hR c) (rightRank q hR c) ∧ retained q {c} x := by
  cases x with
  | inl k =>
    change _ ↔ (¬ (eventEnumeration q hR).symm (Sum.inl k) ∈ intervalSide _ _) ∧ True
    rw [anchor_interval_iff q hR c hfirst hcut]
    simp only [and_true]
    constructor
    · intro hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hx
      by_cases hi0 : i.val=0
      · simp only [tinyParentEvents,if_pos hi0] at hi
        have hk:=congrArg Fin.val (Sum.inl.inj hi)
        change 0=k.val at hk
        omega
      · by_cases hi1 : i.val=1
        · simp only [tinyParentEvents,if_neg hi0,if_pos hi1] at hi
          cases hi
        · simp only [tinyParentEvents,if_neg hi0,if_neg hi1] at hi
          have hk:=congrArg Fin.val (Sum.inl.inj hi)
          dsimp at hk
          omega
    · intro hk
      by_cases hk0 : k.val=0
      · refine List.mem_ofFn.mpr ⟨⟨0,by omega⟩,?_⟩
        simp only [tinyParentEvents,Fin.val_zero,if_pos rfl]
        apply congrArg Sum.inl
        apply Fin.ext
        exact hk0.symm
      · have hka : a<k.val := by omega
        let i : Fin (b+3) := ⟨k.val-a+1,by have:=k.isLt;omega⟩
        have hi0 : i.val≠0 := by dsimp [i];omega
        have hi1 : i.val≠1 := by dsimp [i];omega
        refine List.mem_ofFn.mpr ⟨i,?_⟩
        simp only [tinyParentEvents,if_neg hi0,if_neg hi1]
        congr 1
        apply Fin.ext
        dsimp [i]
        omega
  | inr v =>
    rcases v with ⟨d,z⟩
    constructor
    · intro hx
      obtain ⟨i,hi⟩:=List.mem_ofFn.mp hx
      by_cases hi0 : i.val=0
      · simp only [tinyParentEvents,if_pos hi0] at hi
        cases hi
      · by_cases hi1 : i.val=1
        · simp only [tinyParentEvents,if_neg hi0,if_pos hi1] at hi
          have hv:=Sum.inr.inj hi
          cases hv
          exact ⟨left_not_interval q hR c,by simp [retained]⟩
        · simp only [tinyParentEvents,if_neg hi0,if_neg hi1] at hi
          cases hi
    · intro hx
      have hd : d=c := by simpa [retained] using hx.2
      subst d
      cases z with
      | false => exact List.mem_ofFn.mpr ⟨⟨1,by omega⟩,by simp [tinyParentEvents]⟩
      | true => exact (hx.1 (right_in_interval q hR c)).elim

include hfirst hcut in
theorem interval_filtered :
    (List.ofFn (intervalEvents q hR c)).filter (fun z => decide (retained q {c} z))=
      List.ofFn (closedSortedEvents q c) := by
  letI := eventOrder q hR.noTriple
  apply List.Sorted.eq_of_mem_iff ((intervalEvents_sorted q hR c).filter _) (closedSortedEvents_sorted q hR c hcut)
  intro x
  rw [List.mem_filter,intervalEvents_mem,closedSortedEvents_mem q hR c hfirst hcut]
  simp

include hfirst hcut in
theorem open_filtered :
    (orbitWord (incoming q hR.noTriple {c}) (start q)).filter (fun z => decide (retained q {c} z))=
      List.ofFn (tinyParentEvents q c) := by
  rw [open_orbitWord]
  letI := eventOrder q hR.noTriple
  apply List.Sorted.eq_of_mem_iff ((complementEvents_sorted q hR c).filter _) (tinyParentEvents_sorted q hR c hfirst hcut)
  intro x
  rw [List.mem_filter,complementEvents_mem,tinyParentEvents_mem q hR c hfirst hcut]
  simp

include hfirst hcut in
/-- The actual distinguished retained word keeps the tiny initial edge pc. -/
theorem singleton_open_retainedWord :
    List.ofFn (RetainedWords.vertex q hR {c} (start q))=
      List.ofFn (fun i : Fin (b+3) => eventPoint q (tinyParentEvents q c i)) := by
  rw [retainedWord_eq_filtered,open_filtered q hR c hfirst hcut,List.map_ofFn]
  rfl

def closedChildEvents : List (Event q) :=
  Sum.inr (c,true) :: List.ofFn (fun i : Fin a =>
    (Sum.inl ⟨i.val+1,by clear hfirst hcut;have := i.isLt;omega⟩ : Event q))

theorem closedSortedEvents_eq_concat : List.ofFn (closedSortedEvents q c)=
    (List.ofFn (fun i : Fin a => (Sum.inl ⟨i.val+1,by clear hfirst hcut;have := i.isLt;omega⟩ : Event q))).concat
      (Sum.inr (c,true)) := by
  rw [List.ofFn_succ']
  have hlast : closedSortedEvents q c (Fin.last a)=Sum.inr (c,true) := by simp [closedSortedEvents]
  rw [hlast]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [closedSortedEvents,i.isLt]

include hfirst hcut in
theorem singleton_closed_filtered :
    (orbitWord (incoming q hR.noTriple {c}) (Sum.inr (c,true))).filter
      (fun z => decide (retained q {c} z))=closedChildEvents q c := by
  let r := intervalEvents q hR c ⟨0,(daughterLengths_pos _ _ (rank_lt q hR c)).1⟩
  have hcycle : (incoming q hR.noTriple {c}).SameCycle r (Sum.inr (c,true)) := by
    apply (mem_orbitWord_iff _ _ _).mp
    rw [interval_orbitWord]
    exact (intervalEvents_mem q hR c _).mpr (right_in_interval q hR c)
  have hrot := DaughterRootRotation.orbitWord_isRotated_of_sameCycle
    (incoming q hR.noTriple {c}) (Sum.inr (c,true)) r hcycle.symm
  have hfilter := DaughterRootRotation.listIsRotated_filter hrot (fun z => decide (retained q {c} z))
  rw [interval_orbitWord,interval_filtered q hR c hfirst hcut,closedSortedEvents_eq_concat] at hfilter
  have hlastrot :
      (List.ofFn (fun i : Fin a => (Sum.inl ⟨i.val+1,by clear hfirst hcut;have := i.isLt;omega⟩ : Event q))).concat
        (Sum.inr (c,true)) ~r closedChildEvents q c := by
    simp only [List.concat_eq_append,closedChildEvents]
    exact List.isRotated_concat _ _
  apply nodup_rotated_eq_of_head ((orbitWord_nodup _ _).filter _) (hfilter.trans hlastrot)
  rw [filtered_head q hR {c} (Sum.inr (c,true)) (by simp [retained])]
  rfl

include hfirst hcut in
/-- Exact actual closed retained word, rooted at the incoming right visit. -/
theorem singleton_closed_retainedWord :
    List.ofFn (RetainedWords.vertex q hR {c} (Sum.inr (c,true)))=
      List.ofFn (Split.child q hR c hfirst hcut) := by
  rw [retainedWord_eq_filtered,singleton_closed_filtered q hR c hfirst hcut]
  rw [closedChildEvents,List.map_cons,List.map_ofFn,List.ofFn_succ]
  congr 1

/-- Source-facing literal word is restricted to the original regular domain. -/
def tinyParent (_hR : Regular q) (c0 : Crossing q) (i : Fin (b+3)) : PlanarPoint ℝ :=
  if i.val=0 then q ⟨0,by clear hfirst hcut;omega⟩ else if i.val=1 then crossingPoint q c0
    else q ⟨a+i.val-1,by clear hfirst hcut;have := i.isLt;omega⟩

theorem tinyParent_events : (fun i : Fin (b+3) => eventPoint q (tinyParentEvents q c i))=
    tinyParent q hR c := by
  funext i
  unfold tinyParentEvents tinyParent
  split_ifs <;> rfl

include hfirst hcut in
/-- Literal open daughter (p,c,q[a+1],...,q[a+b+1]); p=q[0]. -/
theorem singleton_open_word :
    List.ofFn (RetainedWords.vertex q hR {c} (start q))=List.ofFn (tinyParent q hR c) := by
  rw [singleton_open_retainedWord q hR c hfirst hcut,tinyParent_events]

theorem tinyParent_zero : tinyParent q hR c ⟨0,by clear hfirst hcut;omega⟩=q ⟨0,by clear hfirst hcut;omega⟩ := by
  simp [tinyParent]

theorem tinyParent_one : tinyParent q hR c ⟨1,by clear hfirst hcut;omega⟩=crossingPoint q c := by
  simp [tinyParent]

theorem tinyParent_later (i : Fin (b+3)) (hi : 2 ≤ i.val) :
    tinyParent q hR c i=q ⟨a+i.val-1,by clear hfirst hcut;have:=i.isLt;omega⟩ := by
  simp [tinyParent,show i.val≠0 by omega,show i.val≠1 by omega]

theorem singleton_right_component_ne_open :
    componentOf (incoming q hR.noTriple {c}) (Sum.inr (c,true))≠openComponent q hR.noTriple {c} := by
  intro he
  have hc : (incoming q hR.noTriple {c}).SameCycle (start q) (Sum.inr (c,true)) :=
    (componentOf_eq_iff _ _ _).mp he.symm
  have hm := (mem_orbitWord_iff _ _ _).mpr hc
  rw [open_orbitWord] at hm
  exact ((complementEvents_mem q hR c _).mp hm) (right_in_interval q hR c)

theorem retainedWord_isRotated_of_sameCycle (S : Finset (Crossing q)) (x y : Event q)
    (hxy : (incoming q hR.noTriple S).SameCycle x y) :
    List.ofFn (RetainedWords.vertex q hR S x) ~r List.ofFn (RetainedWords.vertex q hR S y) := by
  rw [retainedWord_eq_filtered,retainedWord_eq_filtered]
  exact (DaughterRootRotation.listIsRotated_filter
    (DaughterRootRotation.orbitWord_isRotated_of_sameCycle _ x y hxy)
    (fun z => decide (retained q S z))).map (eventPoint q)

include hfirst hcut in
/-- The actual least retained closed root gives the same cyclic child word. -/
theorem singleton_closedRoot_word :
    List.ofFn (RetainedWords.vertex q hR {c}
      (closedRoot q hR.noTriple {c}
        (componentOf (incoming q hR.noTriple {c}) (Sum.inr (c,true)))
        (singleton_right_component_ne_open q hR c))) ~r
      List.ofFn (Split.child q hR c hfirst hcut) := by
  have hs := (closedRoot_spec q hR.noTriple {c}
    (componentOf (incoming q hR.noTriple {c}) (Sum.inr (c,true)))
    (singleton_right_component_ne_open q hR c)).1
  have hc := (componentOf_eq_iff _ _ _).mp hs
  have hr := retainedWord_isRotated_of_sameCycle q hR {c} _ _ hc
  rw [singleton_closed_retainedWord q hR c hfirst hcut] at hr
  exact hr

def singletonSupport : Nonalternation.Support q hR := ⟨{c},by
  intro d hd e he hne
  have hd' : d=c := Finset.mem_singleton.mp hd
  have he' : e=c := Finset.mem_singleton.mp he
  exact (hne (hd'.trans he'.symm)).elim⟩

include hfirst hcut in
/-- Source auxiliary genericity transfers from the actual singleton closed orbit.
No genericity of the literal daughter is assumed from Regular. -/
theorem child_cyclicGeneric_of_closedAuxiliary (hAux : Primitive.ClosedAuxiliary q hR) :
    CyclicGeneric (Split.child q hR c hfirst hcut) := by
  have hg := hAux (singletonSupport q hR c)
    (componentOf (incoming q hR.noTriple {c}) (Sum.inr (c,true)))
    (singleton_right_component_ne_open q hR c)
  exact DaughterRootAmplitude.cyclicGeneric_ofFn_isRotated
    (singleton_closedRoot_word q hR c hfirst hcut) hg

end DirectGLSSW.ActiveArc.SingletonWords
