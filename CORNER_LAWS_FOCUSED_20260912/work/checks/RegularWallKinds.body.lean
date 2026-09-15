namespace SM

/- The two vertex branches remain separate in the six source alternatives. -/
inductive RegularWallKind where
  | flat | bigon | sliding | triple | extension | cut
  deriving DecidableEq

def RegularWallKind.toWallKind : RegularWallKind → WallKind
  | .flat => .flat
  | .bigon => .vertex
  | .sliding => .vertex
  | .triple => .triple
  | .extension => .extension
  | .cut => .cut

namespace WallGerm

variable {n : ℕ} [NeZero n] (g : WallGerm n)

def HasRegularWallKind : RegularWallKind → Prop
  | .flat => ∃ j, g.FlatAt j
  | .bigon => ∃ M a, g.BigonAt M a
  | .sliding => ∃ M a, g.SlidingAt M a
  | .triple => ∃ e f k, g.TripleAt e f k
  | .extension => ∃ M a, g.ExtensionAt M a
  | .cut => ∃ i j k, g.PureCutAt i j k

theorem hasRegularWallKind_underlying {kind : RegularWallKind} (h : g.HasRegularWallKind kind) :
    g.HasWallKind kind.toWallKind := by
  cases kind with
  | flat => exact h
  | bigon => obtain ⟨M, a, h⟩ := h; exact ⟨M, a, h.1⟩
  | sliding => obtain ⟨M, a, h⟩ := h; exact ⟨M, a, h.1⟩
  | triple => exact h
  | extension => exact h
  | cut => exact h

theorem bigon_sliding_marks_incompatible (hn : 3 ≤ n)
    (hb : g.HasRegularWallKind .bigon) (hs : g.HasRegularWallKind .sliding) : False := by
  obtain ⟨M, a, hb⟩ := hb
  obtain ⟨N, b, hs⟩ := hs
  have he := contactSupport_marks_unique hn hb.1.1 hs.1.1
    (Finset.singleton_inj.mp (hb.1.2.1.symm.trans hs.1.2.1))
  rcases he with ⟨rfl, rfl⟩
  exact hs.2 hb.2

theorem regularWallKind_unique (hn : 3 ≤ n) {a b : RegularWallKind}
    (ha : g.HasRegularWallKind a) (hb : g.HasRegularWallKind b) : a = b := by
  have he := g.wallKinds_mutually_exclusive hn
    (g.hasRegularWallKind_underlying ha) (g.hasRegularWallKind_underlying hb)
  cases a <;> cases b <;> simp only [RegularWallKind.toWallKind] at he <;>
    try cases he <;> try rfl
  · exact (g.bigon_sliding_marks_incompatible hn ha hb).elim
  · exact (g.bigon_sliding_marks_incompatible hn hb ha).elim

theorem exists_regularWallKind_of_simple (h : g.Simple) (hno : ∀ j, ¬ g.CuspAt j) :
    ∃ kind : RegularWallKind, g.HasRegularWallKind kind := by
  obtain ⟨kind, h⟩ := h
  cases kind with
  | flat => exact ⟨.flat, h⟩
  | cusp => obtain ⟨j, h⟩ := h; exact (hno j h).elim
  | vertex =>
    obtain ⟨M, a, h⟩ := h
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact ⟨.bigon, M, a, hb⟩
    · exact ⟨.sliding, M, a, hs⟩
  | triple => exact ⟨.triple, h⟩
  | extension => exact ⟨.extension, h⟩
  | cut => exact ⟨.cut, h⟩

theorem existsUnique_regularWallKind_of_simple (hn : 3 ≤ n) (h : g.Simple)
    (hno : ∀ j, ¬ g.CuspAt j) : ∃! kind : RegularWallKind, g.HasRegularWallKind kind := by
  obtain ⟨kind, hk⟩ := g.exists_regularWallKind_of_simple h hno
  exact ⟨kind, hk, fun other ho => g.regularWallKind_unique hn ho hk⟩

end WallGerm

namespace CurveCubeSubdivision.TimedEventCertificate

variable {n : ℕ} [NeZero n] {γ : unitInterval → LabelledTuple n} {δ : ℝ}
    {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}

theorem simple (E : TimedEventCertificate A hn t) : E.germ.Simple := by
  cases he : E.control with
  | inl v => exact (E.point_wall_cases v he).2.1
  | inr v =>
    obtain ⟨e, f, k, _, ht⟩ := E.triple_wall v he
    exact ⟨.triple, e, f, k, ht⟩

theorem regular_kind_unique (E : TimedEventCertificate A hn t) :
    (∃! kind : RegularWallKind, E.germ.HasRegularWallKind kind) ∧ ∀ j, ¬ E.germ.CuspAt j := by
  have hreg : Regular E.germ.center := by rw [E.germ_center]; exact A.regular t
  have hno := E.germ.not_cuspAt_of_regular hreg
  exact ⟨E.germ.existsUnique_regularWallKind_of_simple hn E.simple hno, hno⟩

end CurveCubeSubdivision.TimedEventCertificate

end SM
