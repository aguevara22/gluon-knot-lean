import DirectGLSSW.FirstCut
import DirectGLSSW.CutRepresentation
import DirectGLSSW.OrderedCapEvents

set_option autoImplicit false

namespace DirectGLSSW.FiniteSupportCuts
open OrderedCapEvents

noncomputable section

def indexEmbedding {α : Type*} {a b : ℕ} (E : α ≃ ↥(Finset.Ioo a b)) : α ↪ ℕ :=
  ⟨fun x => (E x).val, fun _ _ h => E.injective (Subtype.ext h)⟩

def supportCutMap {α : Type*} {a b : ℕ} (E : α ≃ ↥(Finset.Ioo a b))
    (T : Finset α) : IntervalCutSet a b :=
  ⟨T.map (indexEmbedding E), Finset.mem_powerset.mpr (by
    intro k hk
    rcases Finset.mem_map.mp hk with ⟨x, _, rfl⟩
    exact (E x).property)⟩

theorem supportCutMap_bijective {α : Type*} {a b : ℕ}
    (E : α ≃ ↥(Finset.Ioo a b)) : Function.Bijective (supportCutMap E) := by
  classical
  constructor
  · intro S T h
    exact Finset.map_injective (indexEmbedding E) (congrArg Subtype.val h)
  · intro S
    let g : ↥S.val → α := fun x =>
      E.symm ⟨x.val, Finset.mem_powerset.mp S.property x.property⟩
    refine ⟨S.val.attach.image g, Subtype.ext ?_⟩
    change (S.val.attach.image g).map (indexEmbedding E) = S.val
    ext k
    constructor
    · intro hk
      rcases Finset.mem_map.mp hk with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hx with ⟨y, _, rfl⟩
      simpa [indexEmbedding, g] using y.property
    · intro hk
      refine Finset.mem_map.mpr ⟨g ⟨k,hk⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨k,hk⟩, Finset.mem_attach _ _, rfl⟩
      · simp [indexEmbedding,g]

def allSupportCutsEquiv {α : Type*} {a b : ℕ}
    (E : α ≃ ↥(Finset.Ioo a b)) : Finset α ≃ IntervalCutSet a b :=
  Equiv.ofBijective (supportCutMap E) (supportCutMap_bijective E)

theorem allSupportCutsEquiv_card {α : Type*} {a b : ℕ}
    (E : α ≃ ↥(Finset.Ioo a b)) (T : Finset α) :
    (allSupportCutsEquiv E T).val.card = T.card := by
  exact Finset.card_map (indexEmbedding E)

def nonemptyCutFlatten (a b : ℕ) :
    {S : IntervalCutSet a b // S.val.Nonempty} ≃ NonemptyIntervalCuts a b where
  toFun S := ⟨S.val.val, Finset.mem_erase.mpr ⟨S.property.ne_empty,S.val.property⟩⟩
  invFun S := ⟨⟨S.val,(Finset.mem_erase.mp S.property).2⟩,
    Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp S.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

def nonemptySupportCutsEquiv {α : Type*} {a b : ℕ}
    (E : α ≃ ↥(Finset.Ioo a b)) :
    {T : Finset α // T.Nonempty} ≃ NonemptyIntervalCuts a b :=
  ((allSupportCutsEquiv E).subtypeEquiv (p := fun T => T.Nonempty)
    (q := fun S => S.val.Nonempty) (by
      intro T
      change T.Nonempty ↔ (T.map (indexEmbedding E)).Nonempty
      exact Finset.map_nonempty.symm)).trans (nonemptyCutFlatten a b)

theorem nonemptySupportCutsEquiv_card {α : Type*} {a b : ℕ}
    (E : α ≃ ↥(Finset.Ioo a b)) (T : {T : Finset α // T.Nonempty}) :
    (nonemptySupportCutsEquiv E T).val.card = T.val.card := by
  exact Finset.card_map (indexEmbedding E)

/-- Strict monotonicity of actual event times identifies the open time interval
with the open interval of natural event ranks, including the empty case. -/
def interiorEventRanksEquiv (Q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (u v : EventIndex Q n) (a b : ℝ)
    (hu : eventTime Q n u = a) (hv : eventTime Q n v = b) :
    {c : EventIndex Q n // a < eventTime Q n c ∧ eventTime Q n c < b} ≃
      ↥(Finset.Ioo u.val v.val) where
  toFun c := ⟨c.val.val, Finset.mem_Ioo.mpr (by
    have huc : u < c.val := (eventTime_strictMono Q n).lt_iff_lt.mp (by
      rw [hu]; exact c.property.1)
    have hcv : c.val < v := (eventTime_strictMono Q n).lt_iff_lt.mp (by
      rw [hv]; exact c.property.2)
    exact ⟨huc,hcv⟩)⟩
  invFun k := ⟨⟨k.val, lt_trans (Finset.mem_Ioo.mp k.property).2 v.isLt⟩, by
    constructor
    · rw [← hu]
      exact (eventTime_strictMono Q n) (Finset.mem_Ioo.mp k.property).1
    · rw [← hv]
      exact (eventTime_strictMono Q n) (Finset.mem_Ioo.mp k.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl





end
end DirectGLSSW.FiniteSupportCuts
