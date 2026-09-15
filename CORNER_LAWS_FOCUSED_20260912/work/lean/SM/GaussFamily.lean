import SM.GaussFamilyOrder

/-! Constancy of independently constructed geometric Gauss lists and words
under canonical crossing/visit transport in continuous generic families. -/

namespace SM

variable {n : ℕ} {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]

theorem generic_family_gaussList_perm (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) :
    ((gaussList hn (F s).property).map
      (visitTransport (generic_family_crossing_constant hn hF s t))).Perm
      (gaussList hn (F t).property) := by
  let e := visitTransport (generic_family_crossing_constant hn hF s t)
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.map e.injective (gaussList_nodup hn (F s).property))
    (gaussList_nodup hn (F t).property)).mpr
  intro w
  constructor
  · intro _
    exact mem_gaussList hn _ w
  · intro _
    obtain ⟨v, rfl⟩ := e.surjective w
    exact List.mem_map.mpr ⟨v, mem_gaussList hn _ v, rfl⟩

theorem generic_family_gaussList (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) :
    (gaussList hn (F s).property).map
      (visitTransport (generic_family_crossing_constant hn hF s t)) =
      gaussList hn (F t).property := by
  apply List.Perm.eq_of_pairwise
    (fun x y _ _ hxy hyx => visitKey_injective hn (F t).property (le_antisymm hxy hyx))
    _ (gaussList_sorted hn (F t).property) (generic_family_gaussList_perm hn hF s t)
  apply List.pairwise_map.mpr
  apply (gaussList_sorted hn (F s).property).imp
  intro v w h
  exact (generic_family_visitKey_le hn hF s t v w).mp h

theorem generic_family_gaussCycle (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) :
    (gaussCycle hn (F s).property).map
      (visitTransport (generic_family_crossing_constant hn hF s t)) =
      gaussCycle hn (F t).property := by
  exact congrArg (fun l : List (Visit (F t).val) => (l : Cycle (Visit (F t).val)))
    (generic_family_gaussList hn hF s t)

theorem generic_family_gaussWord (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) :
    (gaussWord hn (F s).property).map
      (crossingTransport (generic_family_crossing_constant hn hF s t)) =
      gaussWord hn (F t).property := by
  have hl := congrArg (List.map Sigma.fst) (generic_family_gaussList hn hF s t)
  have he : ((gaussList hn (F s).property).map Sigma.fst).map
      (crossingTransport (generic_family_crossing_constant hn hF s t)) =
      (gaussList hn (F t).property).map Sigma.fst := by
    simpa only [List.map_map, Function.comp_def, visitTransport_crossing] using hl
  exact congrArg (fun l : List (Crossing (F t).val) => (l : Cycle (Crossing (F t).val))) he

end SM
