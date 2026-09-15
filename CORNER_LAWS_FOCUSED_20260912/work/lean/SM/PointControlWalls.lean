import SM.PointControlGeometry
import SM.UnorderedWallTriples
import SM.ContactLegs
import Mathlib.Data.Sign.Basic

namespace SM

open MvPolynomial

noncomputable section

variable {n : ℕ} [NeZero n]

theorem real_sign_product_neg {a b : ℝ} (h : a * b < 0) :
    (SignType.sign a : ℝ) * (SignType.sign b : ℝ) < 0 := by
  rw [← SignType.coe_mul, ← sign_mul, sign_eq_neg_one_iff.mpr h]
  norm_num

namespace WallGerm

variable (g : WallGerm n)

theorem signChanges_real_sign {φ : LabelledTuple n → ℝ} (h : g.SignChanges φ) :
    g.SignChanges (fun P => (SignType.sign (φ P) : ℝ)) := by
  obtain ⟨δ, hδ, hδr, hδφ⟩ := h
  exact ⟨δ, hδ, hδr, fun t ht => real_sign_product_neg (hδφ t ht)⟩

theorem vertex_control_signChanges_chi (v : VertexControlName n)
    (h : g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inl v))))
    (i j k : ZMod n) (hs : ({i, j, k} : Finset (ZMod n)) = v.val) :
    g.SignChanges (fun P => (chi P i j k : ℝ)) := by
  have hcard : ({i, j, k} : Finset (ZMod n)).card = 3 := by rw [hs]; exact v.property
  obtain ⟨hij, hik, hjk⟩ := Finset.card_triple_eq_three_iff.mp hcard
  let r := vertexRepresentative v
  have harea : g.SignChanges (fun P => det (P j - P i) (P k - P i)) := by
    rcases triple_value_eq_or_neg areaPolynomial areaPolynomial_cyclic areaPolynomial_swap_last
      r.first r.second r.third i j k hij hik hjk (hs.trans r.support_eq) with hF | hF
    · have he : (fun P : LabelledTuple n => det (P j - P i) (P k - P i)) =
          (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inl v))) := by
        funext P
        rw [← eval_areaPolynomial, hF]
        rfl
      rw [he]
      exact h
    · have he : (fun P : LabelledTuple n => det (P j - P i) (P k - P i)) =
          (fun P => -eval (scalarCoordinates P) (namedControlPolynomial (.inl v))) := by
        funext P
        rw [← eval_areaPolynomial, hF, map_neg]
        rfl
      rw [he]
      exact (g.signChanges_neg _).mpr h
  exact g.signChanges_real_sign harea

/-- The five point-control branches in the source wall dictionary. -/
def PointWallCases : Prop :=
  (∃ j, g.FlatAt j) ∨ (∃ M a, g.BigonAt M a) ∨ (∃ M a, g.SlidingAt M a) ∨
    (∃ M a, g.ExtensionAt M a) ∨ (∃ i j k, g.PureCutAt i j k)

theorem point_control_wall_cases (hn : 3 ≤ n) (hreg : Regular g.center)
    (v : VertexControlName n) (hz : g.pointZeros = {v.val}) (hc : g.concurrences = ∅)
    (h : g.SignChanges (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inl v)))) :
    g.PointWallCases := by
  rcases regular_single_point_center_cases hn hreg hz hc with hF | hV | hE | hC
  · obtain ⟨j, hf⟩ := hF
    have hs : ({j - 1, j, j + 1} : Finset (ZMod n)) = v.val :=
      Finset.singleton_inj.mp (hf.2.1.symm.trans hz)
    have hχ := g.vertex_control_signChanges_chi v h (j - 1) j (j + 1) hs
    exact Or.inl ⟨j, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2, hχ⟩
  · obtain ⟨M, a, hv⟩ := hV
    have hs : ({a, a + 1, M} : Finset (ZMod n)) = v.val :=
      Finset.singleton_inj.mp (hv.2.1.symm.trans hz)
    have hχ := g.vertex_control_signChanges_chi v h a (a + 1) M hs
    have hV' : g.VertexEdgeAt M a := ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hχ⟩
    rcases g.vertexEdge_bigon_or_sliding hV' with hB | hS
    · exact Or.inr (Or.inl ⟨M, a, hB⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨M, a, hS⟩))
  · obtain ⟨M, a, he⟩ := hE
    have hs : ({a, a + 1, M} : Finset (ZMod n)) = v.val :=
      Finset.singleton_inj.mp (he.2.1.symm.trans hz)
    have hχ := g.vertex_control_signChanges_chi v h a (a + 1) M hs
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨M, a, he.1, he.2.1, he.2.2.1, he.2.2.2.1, he.2.2.2.2, hχ⟩)))
  · obtain ⟨i, j, k, hc'⟩ := hC
    have hs : ({i, j, k} : Finset (ZMod n)) = v.val :=
      Finset.singleton_inj.mp (hc'.2.1.symm.trans hz)
    have hχ := g.vertex_control_signChanges_chi v h i j k hs
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, j, k, hc'.1, hc'.2.1, hc'.2.2, hχ⟩)))

theorem pointWallCases_simple (h : g.PointWallCases) : g.Simple := by
  rcases h with ⟨j, hf⟩ | ⟨M, a, hb⟩ | ⟨M, a, hs⟩ | ⟨M, a, he⟩ | ⟨i, j, k, hc⟩
  · exact ⟨.flat, j, hf⟩
  · exact ⟨.vertex, M, a, hb.1⟩
  · exact ⟨.vertex, M, a, hs.1⟩
  · exact ⟨.extension, M, a, he⟩
  · exact ⟨.cut, i, j, k, hc⟩

theorem vertexEdgeAt_heights_nonzero (hn : 3 ≤ n) {M a : ZMod n} (h : g.VertexEdgeAt M a) :
    chi g.center a (a + 1) (M - 1) ≠ 0 ∧ chi g.center a (a + 1) (M + 1) ≠ 0 := by
  exact ⟨contactNeighbour_chi_nonzero hn h.1 h.2.1 false,
    contactNeighbour_chi_nonzero hn h.1 h.2.1 true⟩

end WallGerm

namespace CurveCubeSubdivision.TimedEventCertificate

variable {γ : unitInterval → LabelledTuple n} {δ : ℝ}
    {d : CurveCubeSubdivision γ δ} {W : d.InternalWaypoint × ScalarCoordinate n → ℝ}
    {A : d.CubeCoordinateApproximation W} {hn : 3 ≤ n} {t : unitInterval}

theorem point_wall_cases (E : TimedEventCertificate A hn t)
    (v : VertexControlName n) (he : E.control = .inl v) :
    E.germ.PointWallCases ∧ E.germ.Simple ∧ ∀ j, ¬ E.germ.CuspAt j := by
  have hng : ¬ Generic (A.path t) := by
    rw [← E.germ_center]
    exact E.germ.center_not_generic
  have hsets := E.center_sets hng
  simp only [he] at hsets
  have hreg : Regular E.germ.center := by rw [E.germ_center]; exact A.regular t
  have hs : E.germ.SignChanges
      (fun P => eval (scalarCoordinates P) (namedControlPolynomial (.inl v))) := by
    simpa only [he] using E.signChanges
  have hw := E.germ.point_control_wall_cases hn hreg v hsets.1 hsets.2 hs
  exact ⟨hw, E.germ.pointWallCases_simple hw, E.germ.not_cuspAt_of_regular hreg⟩

end CurveCubeSubdivision.TimedEventCertificate

end

end SM
