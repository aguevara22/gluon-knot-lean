import SM.GlobalEventCertificate
import SM.ZeroTriples

/-! Development: a unique actual named control zero determines the actual
unordered point/concurrence zero sets. An inactive concurrence zero is only
classified when the tuple is genuinely nongeneric. -/

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ} [NeZero n]

theorem vertex_control_zero_iff (P : LabelledTuple n) (v : VertexControlName n) :
    eval (scalarCoordinates P) (namedControlPolynomial (.inl v)) = 0 ↔
      PointZeroTriple P v.val := by
  let r := vertexRepresentative v
  change eval (scalarCoordinates P) (areaPolynomial r.first r.second r.third) = 0 ↔ _
  rw [eval_areaPolynomial]
  have hs := (congrArg (PointZeroTriple P) r.support_eq).to_iff
  exact sign_eq_zero_iff.symm.trans
    ((pointZeroTriple_iff r.first_ne_second r.second_ne_third r.first_ne_third).symm.trans hs.symm)

theorem edge_control_zero_of_concurrence (P : LabelledTuple n) (e : EdgeControlName n)
    (h : ConcurrenceTriple P e.val) :
    eval (scalarCoordinates P) (namedControlPolynomial (.inr e)) = 0 := by
  let r := edgeRepresentative e
  change eval (scalarCoordinates P) (concurrencePolynomial r.first r.second r.third) = 0
  rw [eval_concurrencePolynomial]
  obtain ⟨x, hx⟩ := h.2.2
  apply concurrenceDet_eq_zero_of_closedTriple P r.first r.second r.third
  refine ⟨x, ?_, ?_, ?_⟩
  all_goals apply edgeInterior_subset_edgeSegment
  · exact hx _ (Eq.mpr (congrArg (fun s : Finset (ZMod n) => r.first ∈ s) r.support_eq) (by simp))
  · exact hx _ (Eq.mpr (congrArg (fun s : Finset (ZMod n) => r.second ∈ s) r.support_eq) (by simp))
  · exact hx _ (Eq.mpr (congrArg (fun s : Finset (ZMod n) => r.third ∈ s) r.support_eq) (by simp))

theorem pointZeroTriples_eq_singleton_of_unique_vertex_control
    (P : LabelledTuple n) (v : VertexControlName n)
    (hz : eval (scalarCoordinates P) (namedControlPolynomial (.inl v)) = 0)
    (hother : ∀ u : VertexControlName n, u ≠ v →
      eval (scalarCoordinates P) (namedControlPolynomial (.inl u)) ≠ 0) :
    pointZeroTriples P = {v.val} := by
  classical
  apply Finset.ext
  intro s
  rw [mem_pointZeroTriples, Finset.mem_singleton]
  constructor
  · intro hs
    let u : VertexControlName n := ⟨s, hs.1⟩
    have hroot := (vertex_control_zero_iff P u).mpr hs
    have he : u = v := by
      by_contra he
      exact hother u he hroot
    exact congrArg Subtype.val he
  · rintro rfl
    exact (vertex_control_zero_iff P v).mp hz

theorem pointZeroTriples_empty_of_vertex_controls_nonzero (P : LabelledTuple n)
    (h : ∀ v : VertexControlName n,
      eval (scalarCoordinates P) (namedControlPolynomial (.inl v)) ≠ 0) :
    pointZeroTriples P = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hp := (mem_pointZeroTriples P s).mp hs
  exact h ⟨s, hp.1⟩ ((vertex_control_zero_iff P ⟨s, hp.1⟩).mpr hp)

theorem concurrenceTriples_empty_of_edge_controls_nonzero (P : LabelledTuple n)
    (h : ∀ e : EdgeControlName n,
      eval (scalarCoordinates P) (namedControlPolynomial (.inr e)) ≠ 0) :
    concurrenceTriples P = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hp := (mem_concurrenceTriples P s).mp hs
  exact h ⟨s, hp.1, hp.2.1⟩
    (edge_control_zero_of_concurrence P ⟨s, hp.1, hp.2.1⟩ hp)

theorem concurrenceTriples_nonempty_of_g1_nongeneric (hn : 3 ≤ n)
    (P : LabelledTuple n) (h1 : G1 P) (hng : ¬ Generic P) :
    (concurrenceTriples P).Nonempty := by
  classical
  letI : Fact (1 < n) := ⟨by omega⟩
  have h2 : ¬ G2 P := fun h2 => hng ⟨h1, h2⟩
  obtain ⟨i, j, k, x, hij, hjk, hik, hi, hj, hk⟩ := not_not.mp h2
  have hrij := g1_common_interiors_remote hn h1 hij hi hj
  have hrik := g1_common_interiors_remote hn h1 hik hi hk
  have hrjk := g1_common_interiors_remote hn h1 hjk hj hk
  exact ⟨{i, j, k}, (mem_concurrenceTriples P _).mpr
    ((concurrenceTriple_iff hrij hrjk hrik).mpr ⟨x, hi, hj, hk⟩)⟩

theorem concurrenceTriples_eq_singleton_of_unique_active_control
    (hn : 3 ≤ n) (P : LabelledTuple n) (e : EdgeControlName n)
    (h1 : G1 P) (hng : ¬ Generic P)
    (hother : ∀ f : EdgeControlName n, f ≠ e →
      eval (scalarCoordinates P) (namedControlPolynomial (.inr f)) ≠ 0) :
    concurrenceTriples P = {e.val} := by
  classical
  have hsub : ∀ s ∈ concurrenceTriples P, s = e.val := by
    intro s hs
    have hp := (mem_concurrenceTriples P s).mp hs
    let f : EdgeControlName n := ⟨s, hp.1, hp.2.1⟩
    have hz := edge_control_zero_of_concurrence P f hp
    have he : f = e := by
      by_contra he
      exact hother f he hz
    exact congrArg Subtype.val he
  obtain ⟨s, hs⟩ := concurrenceTriples_nonempty_of_g1_nongeneric hn P h1 hng
  have he : e.val ∈ concurrenceTriples P := (hsub s hs) ▸ hs
  apply Finset.ext
  intro u
  rw [Finset.mem_singleton]
  exact ⟨hsub u, fun hu => hu.symm ▸ he⟩

/-- Transparent actual zero-set dictionary; no root or genericity assumption is
hidden in this predicate. -/
def ControlCenterSets (P : LabelledTuple n) (name : PolynomialControlName n) : Prop :=
  match name with
  | .inl v => pointZeroTriples P = {v.val} ∧ concurrenceTriples P = ∅
  | .inr e => pointZeroTriples P = ∅ ∧ concurrenceTriples P = {e.val}

theorem unique_named_control_center_sets (hn : 3 ≤ n) (P : LabelledTuple n)
    (name : PolynomialControlName n)
    (hz : eval (scalarCoordinates P) (namedControlPolynomial name) = 0)
    (hother : ∀ other, other ≠ name →
      eval (scalarCoordinates P) (namedControlPolynomial other) ≠ 0)
    (hng : ¬ Generic P) : ControlCenterSets P name := by
  cases name with
  | inl v =>
    refine ⟨pointZeroTriples_eq_singleton_of_unique_vertex_control P v hz ?_,
      concurrenceTriples_empty_of_edge_controls_nonzero P ?_⟩
    · intro u hne
      exact hother (.inl u) (fun he => hne (Sum.inl.inj he))
    · intro e
      exact hother (.inr e) (by simp)
  | inr e =>
    have hp := pointZeroTriples_empty_of_vertex_controls_nonzero P
      (fun v => hother (.inl v) (by simp))
    refine ⟨hp, concurrenceTriples_eq_singleton_of_unique_active_control hn P e
      ((pointZeroTriples_empty_iff P).mp hp) hng ?_⟩
    intro f hne
    exact hother (.inr f) (fun he => hne (Sum.inr.inj he))

namespace CurveCubeSubdivision.TimedEventCertificate

variable {γ : unitInterval → LabelledTuple n} {δ : ℝ}
    {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}

theorem center_sets (E : TimedEventCertificate A hn t) (hng : ¬ Generic (A.path t)) :
    match E.control with
    | .inl v => pointZeroTriples E.germ.center = {v.val} ∧ concurrenceTriples E.germ.center = ∅
    | .inr e => pointZeroTriples E.germ.center = ∅ ∧ concurrenceTriples E.germ.center = {e.val} := by
  have hz : eval (scalarCoordinates E.germ.center) (namedControlPolynomial E.control) = 0 := by
    rw [E.germ_center]
    exact E.root
  have hc : ¬ Generic E.germ.center := by rwa [E.germ_center]
  exact unique_named_control_center_sets hn E.germ.center E.control hz E.other_controls hc

end CurveCubeSubdivision.TimedEventCertificate

end

end SM

#print axioms SM.vertex_control_zero_iff
#print axioms SM.edge_control_zero_of_concurrence
#print axioms SM.unique_named_control_center_sets
#print axioms SM.CurveCubeSubdivision.TimedEventCertificate.center_sets
