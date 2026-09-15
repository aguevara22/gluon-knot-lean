import SM.ContactOrder
import SM.ContactVisitWindows

/-! The actual persistent visits, transported by unchanged crossing supports
and edge labels. Their actual same-edge parameters retain every comparison. -/

namespace SM

variable {n : ℕ} [NeZero n] {P Q : LabelledTuple n} {M a : ZMod n}

abbrev PersistentContactVisit (P : LabelledTuple n) (M a : ZMod n) :=
  {v : Visit P // ¬ ContactAffected M a v.1.val}

def contactVisitTransport
    (h : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s)) :
    PersistentContactVisit P M a ≃ PersistentContactVisit Q M a where
  toFun v := ⟨⟨⟨v.val.1.val, (h _ v.property).mpr v.val.1.property⟩, v.val.2⟩, v.property⟩
  invFun v := ⟨⟨⟨v.val.1.val, (h _ v.property).mp v.val.1.property⟩, v.val.2⟩, v.property⟩
  left_inv v := by rcases v with ⟨⟨⟨s, hs⟩, i⟩, hnot⟩; rfl
  right_inv v := by rcases v with ⟨⟨⟨s, hs⟩, i⟩, hnot⟩; rfl

theorem contactVisitTransport_support
    (h : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : PersistentContactVisit P M a) :
    (contactVisitTransport h v).val.1.val = v.val.1.val := rfl

theorem contactVisitTransport_edge
    (h : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v : PersistentContactVisit P M a) :
    (contactVisitTransport h v).val.2.val = v.val.2.val := rfl

theorem contact_visitParameter_eq_of_support_pair (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (v : Visit P)
    (hnot : ¬ ContactAffected M a v.1.val) (j : ZMod n)
    (hs : v.1.val = {v.2.val, j}) :
    visitParameter v = edgeParameter P v.2.val j := by
  rcases v with ⟨⟨s, hc⟩, ⟨i, hi⟩⟩
  change s = {i, j} at hs
  subst s
  exact contact_crossingParameter_eq_edgeParameter hn hsep hz hc hnot

theorem contact_persistent_visit_order (hn : 3 ≤ n) (hsep : ContactSeparated M a)
    (hz : pointZeroTriples P = {contactSupport M a}) (hQ : G1 Q)
    (horder : ContactOrderAgrees P Q M a)
    (hs : ∀ s, ¬ ContactAffected M a s → (IsCrossing Q s ↔ IsCrossing P s))
    (v w : PersistentContactVisit P M a) (he : v.val.2.val = w.val.2.val) :
    visitParameter (contactVisitTransport hs v).val < visitParameter (contactVisitTransport hs w).val ↔
      visitParameter v.val < visitParameter w.val := by
  obtain ⟨j, _, hv⟩ := crossing_support_partner v.val.1 v.val.2.val v.val.2.property
  obtain ⟨k, _, hw⟩ := crossing_support_partner w.val.1 w.val.2.val w.val.2.property
  have hij : IsCrossing P {v.val.2.val, j} := by simpa only [hv] using v.val.1.property
  have hnij : ¬ ContactAffected M a {v.val.2.val, j} := by simpa only [hv] using v.property
  have hik : IsCrossing P {v.val.2.val, k} := by simpa only [hw, he] using w.val.1.property
  have hnik : ¬ ContactAffected M a {v.val.2.val, k} := by simpa only [hw, he] using w.property
  rw [visitParameter_eq_of_support_pair hn hQ (contactVisitTransport hs v).val j hv,
    visitParameter_eq_of_support_pair hn hQ (contactVisitTransport hs w).val k hw,
    contact_visitParameter_eq_of_support_pair hn hsep hz v.val v.property j hv,
    contact_visitParameter_eq_of_support_pair hn hsep hz w.val w.property k hw,
    contactVisitTransport_edge, contactVisitTransport_edge, ← he]
  exact horder _ j k hij hnij hik hnik

end SM
