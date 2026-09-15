import SM.GaussWord

/-! Faithful alphabet embeddings for cyclic words. These maps retain the
rotation quotient and all repeated letters; injective letter maps are proved
injective on whole cyclic words, including the empty word. -/

namespace SM

theorem cycle_map_map {α β γ : Type*} (s : Cycle α) (f : α → β) (g : β → γ) :
    (s.map f).map g = s.map (g ∘ f) := by
  induction s using Quotient.inductionOn' with
  | _ l =>
    change (((l.map f).map g : List γ) : Cycle γ) = ((l.map (g ∘ f) : List γ) : Cycle γ)
    rw [List.map_map]

theorem cycle_map_id {α : Type*} (s : Cycle α) : s.map id = s := by
  induction s using Quotient.inductionOn' with
  | _ l =>
    change ((l.map id : List α) : Cycle α) = (l : Cycle α)
    rw [List.map_id]

theorem cycle_map_injective {α β : Type*} (f : α → β) (hf : Function.Injective f) :
    Function.Injective (Cycle.map f) := by
  intro s t
  refine Quotient.inductionOn₂' s t ?_
  intro l m he
  obtain ⟨k, hk⟩ := Cycle.coe_eq_coe.mp he
  apply Cycle.coe_eq_coe.mpr
  refine ⟨k, ?_⟩
  apply hf.list_map
  simpa only [List.map_rotate] using hk

theorem cycle_map_length {α β : Type*} (s : Cycle α) (f : α → β) :
    (s.map f).length = s.length := by
  induction s using Quotient.inductionOn' with
  | _ l =>
    change (l.map f).length = l.length
    exact List.length_map f

end SM
