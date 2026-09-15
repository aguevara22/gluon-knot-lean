import SM.SortedCut
import SM.VisitRelabel

/-! The independently constructed Gauss words of cyclically relabelled
polygons agree after the actual crossing/visit bijections. -/

namespace SM

variable {n : ℕ}

theorem gaussList_shift_perm (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : ZMod n) :
    ((gaussList hn hP).map (visitShift a)).Perm
      (gaussList hn ((generic_shift a P).mpr hP)) := by
  have hb := visitShift_bijective a P
  apply (List.perm_ext_iff_of_nodup
    (List.Nodup.map hb.1 (gaussList_nodup hn hP))
    (gaussList_nodup hn ((generic_shift a P).mpr hP))).mpr
  intro w
  constructor
  · intro _
    exact mem_gaussList hn _ w
  · intro _
    obtain ⟨v, rfl⟩ := hb.2 w
    exact List.mem_map.mpr ⟨v, mem_gaussList hn hP v, rfl⟩

theorem gaussList_shift_rotation (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : ZMod n) :
    ((gaussList hn hP).map (visitShift a)).IsRotated
      (gaussList hn ((generic_shift a P).mpr hP)) := by
  haveI : NeZero n := ⟨by omega⟩
  apply sorted_map_cut_rotation _ _ (visitShift a) (visitKey hn hP.1)
    (visitKey hn ((generic_shift a P).mpr hP).1) n a.val
    (visitKey_injective hn hP) (visitKey_injective hn ((generic_shift a P).mpr hP))
    (gaussList_sorted hn hP) (gaussList_sorted hn ((generic_shift a P).mpr hP))
    (gaussList_shift_perm hn hP a)
  · intro v _
    exact ⟨traversalKey_nonneg (visitPosition hn hP.1 v),
      traversalKey_lt_size (visitPosition hn hP.1 v)⟩
  · intro v _
    exact visitKey_shift hn hP.1 a v

theorem gaussCycle_shift (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : ZMod n) :
    (gaussCycle hn hP).map (visitShiftEquiv a P) =
      gaussCycle hn ((generic_shift a P).mpr hP) :=
  Cycle.coe_eq_coe.mpr (gaussList_shift_rotation hn hP a)

theorem gaussWord_shift (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    (a : ZMod n) :
    (gaussWord hn hP).map (crossingShiftEquiv a P) =
      gaussWord hn ((generic_shift a P).mpr hP) := by
  have hr := (gaussList_shift_rotation hn hP a).map Sigma.fst
  apply Cycle.coe_eq_coe.mpr
  simpa only [List.map_map, Function.comp_def, visitShift_crossing] using hr

end SM
