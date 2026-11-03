import CarrierTriplePairProperness

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.EventCarrierPairClassification

variable {α : Type*} [DecidableEq α] {m : ℕ}
variable (f : Fin (m+2) → α) (r : α)

/-- The actual event-word incidence pattern: a root chord from the first
carrier to r, followed by consecutive pairs of an open carrier chain. -/
def eventPair (i : Fin (m+2)) : Finset α :=
  if i.val=0 then {f 0,r} else {f ⟨i.val-1,by have := i.isLt;omega⟩,f i}

private theorem mem_pair_pos (i : Fin (m+2)) (hi : 0 < i.val) (x : α) :
    x∈eventPair f r i ↔ x=f ⟨i.val-1,by have := i.isLt;omega⟩ ∨ x=f i := by
  simp only [eventPair,if_neg (Nat.ne_of_gt hi),Finset.mem_insert,Finset.mem_singleton]

/-- Every event pair has two distinct carrier labels. -/
theorem eventPair_card (hf : Function.Injective f) (hr0 : r≠f 0)
    (i : Fin (m+2)) : (eventPair f r i).card=2 := by
  by_cases hi : i.val=0
  · simp [eventPair,hi,Ne.symm hr0]
  · have hp : 0 < i.val := Nat.pos_of_ne_zero hi
    have he : f ⟨i.val-1,by have := i.isLt;omega⟩≠f i := by
      intro hh
      have hv := congrArg Fin.val (hf hh)
      dsimp at hv
      omega
    simp [eventPair,hi,he]

private theorem root_pair_ne_positive (hf : Function.Injective f)
    (hr0 : r≠f 0) (hr1 : r≠f 1)
    (j : Fin (m+2)) (hj : 0 < j.val) : eventPair f r 0≠eventPair f r j := by
  intro he
  have ha : f 0∈eventPair f r j := by rw [←he];simp [eventPair]
  have hb : r∈eventPair f r j := by rw [←he];simp [eventPair]
  rcases (mem_pair_pos f r j hj _).mp ha with ha|ha
  · have hv := congrArg Fin.val (hf ha)
    have hj1 : j=1 := by apply Fin.ext;dsimp at hv ⊢;omega
    rcases (mem_pair_pos f r j hj _).mp hb with hb|hb
    · apply hr0
      have hpred : (⟨j.val-1,by have := j.isLt;omega⟩ : Fin (m+2))=0 := Fin.ext hv.symm
      simpa only [hpred] using hb
    · exact hr1 (hb.trans (congrArg f hj1))
  · have hv := congrArg Fin.val (hf ha)
    dsimp at hv
    omega

/-- Excluding the first adjacent pair prevents the moved root from repeating
a retained intersection pair; all event pairs are then distinct. -/
theorem eventPair_injective (hf : Function.Injective f) (hr0 : r≠f 0) (hr1 : r≠f 1) :
    Function.Injective (eventPair f r) := by
  intro i j he
  by_cases hi : i.val=0
  · have hi0 : i=0 := Fin.ext hi
    by_cases hj : j.val=0
    · exact hi0.trans (Fin.ext hj).symm
    · exact False.elim (root_pair_ne_positive f r hf hr0 hr1 j (Nat.pos_of_ne_zero hj)
        (hi0 ▸ he))
  · by_cases hj : j.val=0
    · have hj0 : j=0 := Fin.ext hj
      exact False.elim (root_pair_ne_positive f r hf hr0 hr1 i (Nat.pos_of_ne_zero hi)
        (hj0 ▸ he.symm))
    · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
      have hjp : 0 < j.val := Nat.pos_of_ne_zero hj
      have hs : f i∈eventPair f r j := by
        rw [←he]
        exact (mem_pair_pos f r i hip _).mpr (Or.inr rfl)
      have hp : f ⟨i.val-1,by have := i.isLt;omega⟩∈eventPair f r j := by
        rw [←he]
        exact (mem_pair_pos f r i hip _).mpr (Or.inl rfl)
      rcases (mem_pair_pos f r j hjp _).mp hs with hs|hs
      · have hv := congrArg Fin.val (hf hs)
        rcases (mem_pair_pos f r j hjp _).mp hp with hp|hp
        all_goals
          have hw := congrArg Fin.val (hf hp)
          apply Fin.ext
          dsimp at hv hw ⊢
          omega
      · exact hf hs

/-- The only shared-carrier triple is the moved root and the two retained
vertices adjacent to its crossed carrier. No determinant statement is assumed. -/
theorem eventPair_common_iff (hf : Function.Injective f)
    (i j k : Fin (m+2)) (hij : i.val < j.val) (hjk : j.val < k.val) :
    (∃ x : α, x∈eventPair f r i ∧ x∈eventPair f r j ∧ x∈eventPair f r k) ↔
      i.val=0 ∧ k.val=j.val+1 ∧ f j=r := by
  have hj : 0 < j.val := by omega
  have hk : 0 < k.val := by omega
  constructor
  · rintro ⟨x,hxi,hxj,hxk⟩
    have hz : i.val=0 := by
      by_contra hi
      have hi' : 0 < i.val := Nat.pos_of_ne_zero hi
      rcases (mem_pair_pos f r i hi' x).mp hxi with ha|ha
      all_goals
        rcases (mem_pair_pos f r j hj x).mp hxj with hb|hb
        all_goals
          rcases (mem_pair_pos f r k hk x).mp hxk with hc|hc
          all_goals
            have hab := congrArg Fin.val (hf (ha.symm.trans hb))
            have hac := congrArg Fin.val (hf (ha.symm.trans hc))
            try dsimp at hab hac
            omega
    have hi0 : i=0 := Fin.ext hz
    have hxr : x=r := by
      rw [hi0] at hxi
      change x∈({f 0,r} : Finset α) at hxi
      rcases Finset.mem_insert.mp hxi with hh|hh
      · subst x
        rcases (mem_pair_pos f r j hj _).mp hxj with ha|ha
        all_goals
          rcases (mem_pair_pos f r k hk _).mp hxk with hb|hb
          all_goals
            have hva := congrArg Fin.val (hf ha)
            have hvb := congrArg Fin.val (hf hb)
            dsimp at hva hvb
            omega
      · exact Finset.mem_singleton.mp hh
    subst x
    rcases (mem_pair_pos f r j hj r).mp hxj with ha|ha
    all_goals
      rcases (mem_pair_pos f r k hk r).mp hxk with hb|hb
      all_goals
        have hv := congrArg Fin.val (hf (ha.symm.trans hb))
        try dsimp at hv
        first | exact ⟨hz,by omega,ha.symm⟩ | omega
  · rintro ⟨hi,hkj,hr⟩
    refine ⟨r,?_,?_,?_⟩
    · simp [eventPair,hi]
    · exact (mem_pair_pos f r j hj r).mpr (Or.inr hr.symm)
    · apply (mem_pair_pos f r k hk r).mpr
      left
      have hp : (⟨k.val-1,by have := k.isLt;omega⟩ : Fin (m+2))=j := by
        apply Fin.ext
        dsimp
        omega
      rw [hp]
      exact hr.symm





end DirectGLSSW.EventCarrierPairClassification
