import SM.WallCenterSeparation

/-! Exhaustive pairwise separation of all six source central wall kinds.
The classification is about already simple germs, not arbitrary singularities. -/

namespace SM

variable {n : ℕ} [NeZero n]

theorem wallCenterKind_unique (hn : 3 ≤ n) {P : LabelledTuple n} {a b : WallKind}
    (h : WallCenterKind P a) (h' : WallCenterKind P b) : a = b := by
  cases h with
  | flat jL hf =>
    cases h' with
    | flat jR hg => rfl
    | cusp jR hg => exact False.elim (flat_cusp_center_incompatible hf hg)
    | vertex MR aR hg => exact False.elim (turn_contact_zero_incompatible hn hf.2.1 hg.1 hg.2.1)
    | triple eR fR kR hg => exact False.elim (singleton_zero_not_empty hf.2.1 hg.1)
    | extension MR aR hg => exact False.elim (turn_contact_zero_incompatible hn hf.2.1 hg.1 hg.2.1)
    | cut iR jR kR hg => exact False.elim (turn_cut_zero_incompatible hf.2.1 hg.1 hg.2.1)
  | cusp jL hf =>
    cases h' with
    | flat jR hg => exact False.elim (flat_cusp_center_incompatible hg hf)
    | cusp jR hg => rfl
    | vertex MR aR hg => exact False.elim (turn_contact_zero_incompatible hn hf.2.1 hg.1 hg.2.1)
    | triple eR fR kR hg => exact False.elim (singleton_zero_not_empty hf.2.1 hg.1)
    | extension MR aR hg => exact False.elim (turn_contact_zero_incompatible hn hf.2.1 hg.1 hg.2.1)
    | cut iR jR kR hg => exact False.elim (turn_cut_zero_incompatible hf.2.1 hg.1 hg.2.1)
  | vertex ML aL hf =>
    cases h' with
    | flat jR hg => exact False.elim (turn_contact_zero_incompatible hn hg.2.1 hf.1 hf.2.1)
    | cusp jR hg => exact False.elim (turn_contact_zero_incompatible hn hg.2.1 hf.1 hf.2.1)
    | vertex MR aR hg => rfl
    | triple eR fR kR hg => exact False.elim (singleton_zero_not_empty hf.2.1 hg.1)
    | extension MR aR hg => exact False.elim (vertex_extension_center_incompatible hn hf hg)
    | cut iR jR kR hg => exact False.elim (contact_cut_zero_incompatible hf.2.1 hg.1 hg.2.1)
  | triple eL fL kL hf =>
    cases h' with
    | flat jR hg => exact False.elim (singleton_zero_not_empty hg.2.1 hf.1)
    | cusp jR hg => exact False.elim (singleton_zero_not_empty hg.2.1 hf.1)
    | vertex MR aR hg => exact False.elim (singleton_zero_not_empty hg.2.1 hf.1)
    | triple eR fR kR hg => rfl
    | extension MR aR hg => exact False.elim (singleton_zero_not_empty hg.2.1 hf.1)
    | cut iR jR kR hg => exact False.elim (singleton_zero_not_empty hg.2.1 hf.1)
  | extension ML aL hf =>
    cases h' with
    | flat jR hg => exact False.elim (turn_contact_zero_incompatible hn hg.2.1 hf.1 hf.2.1)
    | cusp jR hg => exact False.elim (turn_contact_zero_incompatible hn hg.2.1 hf.1 hf.2.1)
    | vertex MR aR hg => exact False.elim (vertex_extension_center_incompatible hn hg hf)
    | triple eR fR kR hg => exact False.elim (singleton_zero_not_empty hf.2.1 hg.1)
    | extension MR aR hg => rfl
    | cut iR jR kR hg => exact False.elim (contact_cut_zero_incompatible hf.2.1 hg.1 hg.2.1)
  | cut iL jL kL hf =>
    cases h' with
    | flat jR hg => exact False.elim (turn_cut_zero_incompatible hg.2.1 hf.1 hf.2.1)
    | cusp jR hg => exact False.elim (turn_cut_zero_incompatible hg.2.1 hf.1 hf.2.1)
    | vertex MR aR hg => exact False.elim (contact_cut_zero_incompatible hg.2.1 hf.1 hf.2.1)
    | triple eR fR kR hg => exact False.elim (singleton_zero_not_empty hf.2.1 hg.1)
    | extension MR aR hg => exact False.elim (contact_cut_zero_incompatible hg.2.1 hf.1 hf.2.1)
    | cut iR jR kR hg => rfl

namespace WallGerm

theorem wallKinds_mutually_exclusive (hn : 3 ≤ n) (g : WallGerm n) {a b : WallKind}
    (ha : g.HasWallKind a) (hb : g.HasWallKind b) : a = b :=
  wallCenterKind_unique hn (hasWallKind_center ha) (hasWallKind_center hb)

theorem wallKind_determined_by_center (hn : 3 ≤ n) {g g' : WallGerm n}
    (he : g.center = g'.center) {a b : WallKind} (ha : g.HasWallKind a) (hb : g'.HasWallKind b) :
    a = b := by
  have hc := hasWallKind_center ha
  rw [he] at hc
  exact wallCenterKind_unique hn hc (hasWallKind_center hb)

theorem simple_has_unique_kind (hn : 3 ≤ n) (g : WallGerm n) (h : g.Simple) :
    ∃! kind : WallKind, g.HasWallKind kind := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk, fun l hl => g.wallKinds_mutually_exclusive hn hl hk⟩

end WallGerm
end SM

