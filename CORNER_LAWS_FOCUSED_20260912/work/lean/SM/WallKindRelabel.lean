import SM.CuspEmptyRelabel
import SM.UnorderedWallTriples
import SM.SilentCenter

namespace SM.WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

theorem hasWallKind_relabel (r : ZMod n) (kind : WallKind) :
    (g.relabel r).HasWallKind kind ↔ g.HasWallKind kind := by
  cases kind with
  | flat =>
    constructor
    · rintro ⟨j, h⟩
      exact ⟨j + r, (g.flatAt_relabel r (j + r)).mp (by simpa only [add_sub_cancel_right] using h)⟩
    · rintro ⟨j, h⟩
      exact ⟨j - r, (g.flatAt_relabel r j).mpr h⟩
  | cusp =>
    constructor
    · rintro ⟨j, h⟩
      exact ⟨j + r, (g.cuspAt_relabel r (j + r)).mp (by simpa only [add_sub_cancel_right] using h)⟩
    · rintro ⟨j, h⟩
      exact ⟨j - r, (g.cuspAt_relabel r j).mpr h⟩
  | vertex =>
    constructor
    · rintro ⟨M, a, h⟩
      exact ⟨M + r, a + r, (g.vertexEdgeAt_relabel r (M + r) (a + r)).mp
        (by simpa only [add_sub_cancel_right] using h)⟩
    · rintro ⟨M, a, h⟩
      exact ⟨M - r, a - r, (g.vertexEdgeAt_relabel r M a).mpr h⟩
  | triple =>
    constructor
    · rintro ⟨e, f, k, h⟩
      exact ⟨e + r, f + r, k + r, (g.tripleAt_relabel r (e + r) (f + r) (k + r)).mp
        (by simpa only [add_sub_cancel_right] using h)⟩
    · rintro ⟨e, f, k, h⟩
      exact ⟨e - r, f - r, k - r, (g.tripleAt_relabel r e f k).mpr h⟩
  | extension =>
    constructor
    · rintro ⟨M, a, h⟩
      exact ⟨M + r, a + r, (g.extensionAt_relabel r (M + r) (a + r)).mp
        (by simpa only [add_sub_cancel_right] using h)⟩
    · rintro ⟨M, a, h⟩
      exact ⟨M - r, a - r, (g.extensionAt_relabel r M a).mpr h⟩
  | cut =>
    constructor
    · rintro ⟨i, j, k, h⟩
      exact ⟨i + r, j + r, k + r, (g.pureCutAt_relabel r (i + r) (j + r) (k + r)).mp
        (by simpa only [add_sub_cancel_right] using h)⟩
    · rintro ⟨i, j, k, h⟩
      exact ⟨i - r, j - r, k - r, (g.pureCutAt_relabel r i j k).mpr h⟩

theorem simple_relabel (r : ZMod n) : (g.relabel r).Simple ↔ g.Simple := by
  simp only [Simple, g.hasWallKind_relabel]

theorem silent_relabel (r : ZMod n) : (g.relabel r).Silent ↔ g.Silent := by
  change ((g.relabel r).HasWallKind .extension ∨ (g.relabel r).HasWallKind .cut) ↔
    (g.HasWallKind .extension ∨ g.HasWallKind .cut)
  simp only [g.hasWallKind_relabel]

end SM.WallGerm
