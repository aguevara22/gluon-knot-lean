import SM.WallCenterKinds

/-! Central supports distinguish the turn/contact/cut/triple classes.
Within a common support, actual segment geometry separates F/K and V/E. -/

namespace SM

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

theorem singleton_zero_not_empty {S : Finset (ZMod n)}
    (h : pointZeroTriples P = {S}) (he : pointZeroTriples P = ∅) : False :=
  Finset.singleton_ne_empty S (h.symm.trans he)

theorem turn_contact_zero_incompatible (hn : 3 ≤ n) {j M a : ZMod n}
    (hT : pointZeroTriples P = {turnSupport j}) (hs : ContactSeparated M a)
    (hC : pointZeroTriples P = {contactSupport M a}) : False :=
  contactSupport_ne_turnSupport hn hs j (Finset.singleton_inj.mp (hC.symm.trans hT))

theorem turn_cut_zero_incompatible {j : ZMod n} {S : Finset (ZMod n)}
    (hT : pointZeroTriples P = {turnSupport j}) (hs : NoConsecutive S)
    (hC : pointZeroTriples P = {S}) : False :=
  noConsecutive_ne_turnSupport hs j (Finset.singleton_inj.mp (hC.symm.trans hT))

theorem contact_cut_zero_incompatible {M a : ZMod n} {S : Finset (ZMod n)}
    (hC : pointZeroTriples P = {contactSupport M a}) (hs : NoConsecutive S)
    (hS : pointZeroTriples P = {S}) : False := by
  have he : S = contactSupport M a := Finset.singleton_inj.mp (hS.symm.trans hC)
  exact hs a (by rw [he]; simp [contactSupport]) (by rw [he]; simp [contactSupport])

theorem flat_cusp_center_incompatible {j k : ZMod n}
    (hF : FlatCenterAt P j) (hK : CuspCenterAt P k) : False := by
  have he : j = k := turnSupport_injective hF.1 (Finset.singleton_inj.mp (hF.2.1.symm.trans hK.2.1))
  subst k
  obtain ⟨_, t, ht0, ht1, ht⟩ := hF.2.2.2
  exact hK.2.2.2 ⟨t, ht0.le, ht1.le, ht⟩

theorem contactSupport_marks_unique (hn : 3 ≤ n) {M a N b : ZMod n}
    (hM : ContactSeparated M a) (hN : ContactSeparated N b)
    (he : contactSupport M a = contactSupport N b) : M = N ∧ a = b := by
  have hh := contactSupport_vertex_edge hn hN hM.2.1 hM.2.2.1 he
  exact ⟨hh.2, hh.1⟩

theorem vertex_extension_center_incompatible (hn : 3 ≤ n) {M a N b : ZMod n}
    (hV : VertexCenterAt P M a) (hE : ExtensionCenterAt P N b) : False := by
  have he := contactSupport_marks_unique hn hV.1 hE.1
    (Finset.singleton_inj.mp (hV.2.1.symm.trans hE.2.1))
  rcases he with ⟨rfl, rfl⟩
  exact hE.2.2.2.2 (edgeInterior_subset_edgeSegment P _ hV.2.2.2)

end SM
