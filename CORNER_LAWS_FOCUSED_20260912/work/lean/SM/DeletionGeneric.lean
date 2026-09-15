import SM.DeletionInteriors

/-! The actual deletion at a flat centre is Generic. A child triple concurrence
would lift to a parent triple concurrence; the missing middle vertex cannot
belong to any unchanged child edge. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple (n + 1)} {j : ZMod (n + 1)}

theorem g2_deleteVertex (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : G2 (deleteVertex P j) := by
  rintro ⟨a, b, c, x, hab, hbc, hac, ha, hb', hc'⟩
  have hxm : x ≠ P j := by
    intro he
    by_cases hal : a = -1
    · have hbl : b ≠ -1 := fun he' => hab (hal.trans he'.symm)
      exact deleted_middle_not_on_unchanged hn hz hb hbl (he ▸ hb')
    · exact deleted_middle_not_on_unchanged hn hz hb hal (he ▸ ha)
  obtain ⟨ka, hka, hxa⟩ := deleted_interior_lift hb ha hxm
  obtain ⟨kb, hkb, hxb⟩ := deleted_interior_lift hb hb' hxm
  obtain ⟨kc, hkc, hxc⟩ := deleted_interior_lift hb hc' hxm
  apply flat_center_g2 (by omega) hz hb hc
  refine ⟨ka, kb, kc, x, ?_, ?_, ?_, hxa, hxb, hxc⟩
  · exact fun he => hab (deletionEdgeLift_injective (he ▸ hka) hkb)
  · exact fun he => hbc (deletionEdgeLift_injective (he ▸ hkb) hkc)
  · exact fun he => hac (deletionEdgeLift_injective (he ▸ hka) hkc)

theorem generic_deleteVertex (hn : 3 ≤ n)
    (hz : pointZeroTriples P = {turnSupport j})
    (hb : StrictBetween (P (j - 1)) (P j) (P (j + 1)))
    (hc : concurrenceTriples P = ∅) : Generic (deleteVertex P j) :=
  ⟨g1_deleteVertex hz, g2_deleteVertex hn hz hb hc⟩

end SM
