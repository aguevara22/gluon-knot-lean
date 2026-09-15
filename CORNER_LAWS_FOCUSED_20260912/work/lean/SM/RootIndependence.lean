import Mathlib.Topology.LocallyConstant.Basic
import SM.TreeChamber
import SM.FlatLawTree
import SM.VertexEdgeLawTree
import SM.TripleSilentLawsTree
import SM.SoftTheoremTree
import SM.SoftRotationLaw
import SM.ReversalShiftLaw
import SM.StarGenericLaw
import SM.SmallValuesLemma
import SM.MycyclicTheorem
import SM.RelativeGeneralPosition
import SM.Children
import SM.Anchors
import SM.FibreExistence
import SM.GenericCurveChamber
import SM.GermTreeEquality
import SM.TransportLemma

/-! Source thm:root-indep-proof (reference/SM/sm-6-comparison.tex:53, frame SM15): root independence of the tree coefficient.
Main declaration: `SM.root_independence`. Proof planned and drafted 2026-09-13 by a Claude Code scout subagent of the pod executor
(work/reports/root-indep-plan-20260913.md, Appendix A), made unconditional on the accepted lem:transport by a second subagent,
checked with `lake env lean` (sorry-free, standard axioms) and ported verbatim from work/drafts/RootIndependence.lean (only this
header added and the #print line removed). Every helper is prefixed `ri_`. -/

open Filter Topology

/-!
# Root independence of the tree coefficients (thm:root-indep-proof)

`reference/SM/sm-6-comparison.tex`, lines 53–104: for every generic polygon `P` and any two of
its edges `g, h`, `A_g(P) = A_h(P)`. Strong induction on the arity; the base `n = 3` is
lem:A-small-values (i), the step transports `Δ_gh = A_g − A_h` along the path of
lem:transport (`SM.transport_lemma`) to a target with `Δ_gh = 0`, using the wall laws
thm:A-S3, thm:A-S7, thm:A-R3E and the chi-congruence behind prop:A-chamber.
All helpers are prefixed `ri_`; the only unprefixed declaration is `SM.root_independence`.
-/

namespace SM

/-! ### (C0) locally constant off a finite set -/
theorem ri_eq_of_locallyConstant_off_finite {X Y : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [T1Space X] [Nonempty Y]
    (f : X → Y) (S : Set X) (hS : S.Finite)
    (hoff : ∀ x ∉ S, ∀ᶠ y in 𝓝 x, f y = f x)
    (hon : ∀ x ∈ S, ∃ c, ∀ᶠ y in 𝓝[≠] x, f y = c)
    {a b : X} (ha : a ∉ S) (hb : b ∉ S) : f a = f b := by
  classical
  choose! c hc using hon
  let F : X → Y := fun x => if x ∈ S then c x else f x
  have hF : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · have h1 : ∀ᶠ y in 𝓝 x, y ≠ x → f y = c x := eventually_nhdsWithin_iff.mp (hc x hx)
      have h2 : ∀ᶠ y in 𝓝 x, y ∉ S \ {x} :=
        (hS.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
      filter_upwards [h1, h2] with y hy1 hy2
      by_cases hyx : y = x
      · rw [hyx]
      · have hyS : y ∉ S := fun hyS => hy2 ⟨hyS, hyx⟩
        simp only [F, hyS, hx, ↓reduceIte]
        exact hy1 hyx
    · have h1 := hoff x hx
      have h2 : ∀ᶠ y in 𝓝 x, y ∉ S := hS.isClosed.isOpen_compl.mem_nhds hx
      filter_upwards [h1, h2] with y hy1 hy2
      simp only [F, hy2, hx, ↓reduceIte]
      exact hy1
  have := hF.apply_eq_of_preconnectedSpace a b
  simpa [F, ha, hb] using this

/-! ### (A) eventual constancy of chi and of A_g at a generic point of a continuous family -/
theorem ri_chi_eventually_eq_of_G1 {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X]
    {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X} (hx : G1 (γ x)) :
    ∀ᶠ y in 𝓝 x, ∀ i j k : ZMod n, chi (γ y) i j k = chi (γ x) i j k := by
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => ?_
  by_cases hij : i = j
  · subst hij; simp
  by_cases hjk : j = k
  · subst hjk; simp
  by_cases hik : i = k
  · subst hik; simp
  have hne := g1_area_ne_zero hx hij hjk hik
  have hc : ContinuousAt (fun y => chi (γ y) i j k) x :=
    (continuousAt_sign_of_ne_zero hne).comp
      (f := fun y => det (γ y j - γ y i) (γ y k - γ y i))
      ((continuous_area i j k).comp hγ).continuousAt
  have hopen : IsOpen ({chi (γ x) i j k} : Set SignType) := isOpen_discrete _
  exact (hc.eventually_mem (hopen.mem_nhds rfl)).mono fun y hy => hy

theorem ri_treeCoefficient_eventually_eq_of_generic {n : ℕ} [NeZero n] (hn : 3 ≤ n) {X : Type*}
    [TopologicalSpace X] {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X}
    (hx : Generic (γ x)) (g : ZMod n) :
    ∀ᶠ y in 𝓝 x, ∃ hy : Generic (γ y),
      treeCoefficient (γ y) hy.1 g hn = treeCoefficient (γ x) hx.1 g hn := by
  have h1 : ∀ᶠ y in 𝓝 x, Generic (γ y) := hγ.continuousAt.eventually (generic_persists hn hx)
  filter_upwards [h1, ri_chi_eventually_eq_of_G1 hγ hx.1] with y hy hchi
  exact ⟨hy, treeCoefficient_eq_of_chi hy.1 hx.1 hchi g hn⟩

/-! ### Δ_gh as a total function -/
open Classical in
noncomputable def ri_deltaAt {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n)
    (P : LabelledTuple n) : ℤ :=
  if hP : Generic P then treeCoefficient P hP.1 g hn - treeCoefficient P hP.1 h hn else 0

theorem ri_deltaAt_of_generic {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n)
    {P : LabelledTuple n} (hP : Generic P) :
    ri_deltaAt hn g h P = treeCoefficient P hP.1 g hn - treeCoefficient P hP.1 h hn := by
  simp [ri_deltaAt, hP]

theorem ri_deltaAt_eventually_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n) {X : Type*}
    [TopologicalSpace X] {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X}
    (hx : Generic (γ x)) :
    ∀ᶠ y in 𝓝 x, ri_deltaAt hn g h (γ y) = ri_deltaAt hn g h (γ x) := by
  filter_upwards [ri_treeCoefficient_eventually_eq_of_generic hn hγ hx g,
    ri_treeCoefficient_eventually_eq_of_generic hn hγ hx h] with y hyg hyh
  obtain ⟨hy, hg⟩ := hyg
  obtain ⟨_, hh⟩ := hyh
  rw [ri_deltaAt_of_generic hn g h hy, ri_deltaAt_of_generic hn g h hx, hg, hh]

/-! ### side-parameter transport helpers -/
theorem WallGerm.ri_sideTuple_true_val {n : ℕ} (w : WallGerm n) (s : w.Parameter) (hs : 0 < s.val) :
    (w.sideTuple true ⟨s.val, hs, s.property.2⟩).val = w.curve s := rfl

theorem WallGerm.ri_sideTuple_false_val {n : ℕ} (w : WallGerm n) (s : w.Parameter) (hs : s.val < 0) :
    (w.sideTuple false ⟨-s.val, by linarith, by linarith [s.property.1]⟩).val = w.curve s := by
  show w.curve (w.sideTime false _) = w.curve s
  congr 1
  apply Subtype.ext
  simp [WallGerm.sideTime]

/-! ### (C) constancy of Δ along a path with finitely many zero-jump walls -/
theorem ri_deltaAt_const_along_path {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n)
    (path : unitInterval → LabelledTuple n) (hcont : Continuous path)
    (hfin : {t : unitInterval | ¬ Generic (path t)}.Finite)
    (hwall : ∀ t, ¬ Generic (path t) → ∃ w : WallGerm n,
        (∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Set.Icc (0 : ℝ) 1,
          w.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
        ∀ s₁ s₂ : w.Parameter, s₁.val < 0 → 0 < s₂.val →
          ri_deltaAt hn g h (w.curve s₂) = ri_deltaAt hn g h (w.curve s₁))
    (h0 : Generic (path 0)) (h1 : Generic (path 1)) :
    ri_deltaAt hn g h (path 0) = ri_deltaAt hn g h (path 1) := by
  refine ri_eq_of_locallyConstant_off_finite (fun t => ri_deltaAt hn g h (path t))
    {t : unitInterval | ¬ Generic (path t)} hfin ?_ ?_ (by simpa using h0) (by simpa using h1)
  · intro t ht
    have hgen : Generic (path t) := by simpa using ht
    exact ri_deltaAt_eventually_eq hn g h hcont hgen
  · intro t ht
    obtain ⟨w, hcurve, hjump⟩ := hwall t ht
    let sPlus : w.Parameter := ⟨w.radius / 2, by constructor <;> linarith [w.radius_pos]⟩
    let sMinus : w.Parameter := ⟨-(w.radius / 2), by constructor <;> linarith [w.radius_pos]⟩
    have hPlus : 0 < sPlus.val := by show 0 < w.radius / 2; linarith [w.radius_pos]
    have hMinus : sMinus.val < 0 := by show -(w.radius / 2) < 0; linarith [w.radius_pos]
    refine ⟨ri_deltaAt hn g h (w.curve sPlus), ?_⟩
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨w.radius, w.radius_pos, fun u hu hne => ?_⟩
    have hd : |(u : ℝ) - (t : ℝ)| < w.radius := by
      rw [Subtype.dist_eq, Real.dist_eq] at hu; exact hu
    let s : w.Parameter := ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hd⟩
    have hs0 : s.val ≠ 0 := sub_ne_zero.mpr (fun he => hne (Subtype.ext he))
    obtain ⟨hs, he⟩ := hcurve s
    have htu : (⟨(t : ℝ) + s.val, hs⟩ : unitInterval) = u := by
      apply Subtype.ext; show (t : ℝ) + ((u : ℝ) - (t : ℝ)) = u; ring
    rw [htu] at he
    show ri_deltaAt hn g h (path u) = ri_deltaAt hn g h (w.curve sPlus)
    rw [← he]
    rcases lt_or_gt_of_ne hs0 with hneg | hpos
    · rw [hjump s sPlus hneg hPlus]
    · rw [hjump sMinus s hMinus hpos, hjump sMinus sPlus hMinus hPlus]

/-! ### (D2) rotation invariance and the star K_r -/
theorem ri_det_rotationMap (θ : ℝ) (u v : Plane) :
    det (rotationMap θ u) (rotationMap θ v) = det u v := by
  simp only [rotationMap_apply, det]
  linear_combination (u.1 * v.2 - u.2 * v.1) * Real.cos_sq_add_sin_sq θ

theorem ri_chi_rotationMap (θ : ℝ) {n : ℕ} (P : LabelledTuple n) (i j k : ZMod n) :
    chi (rotationMap θ ∘ P) i j k = chi P i j k := by
  simp only [chi, Function.comp, ← map_sub, ri_det_rotationMap]

theorem ri_g1_rotationMap {n : ℕ} (θ : ℝ) {P : LabelledTuple n} (hP : G1 P) :
    G1 (rotationMap θ ∘ P) := by
  intro i j k hij hjk hik
  rw [ri_chi_rotationMap]
  exact hP i j k hij hjk hik

theorem ri_treeCoefficient_rotationMap {n : ℕ} [NeZero n] (θ : ℝ) (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (rotationMap θ ∘ P) (ri_g1_rotationMap θ hP) g hn = treeCoefficient P hP g hn :=
  treeCoefficient_eq_of_chi _ _ (fun i j k => ri_chi_rotationMap θ P i j k) g hn

theorem ri_star_treeCoefficient_succ {r : ℕ} (hr : 1 ≤ r) (hK : G1 (star r)) (g : ZMod (2 * r + 1)) :
    treeCoefficient (star r) hK (g + 1) (by omega) = treeCoefficient (star r) hK g (by omega) := by
  have h1 := treeCoefficient_shift_one (star r) hK g (by omega)
  rw [← h1]
  have hrot := (star_generic_law hr).1.2.1.1
  rw [treeCoefficient_congr_tuple _ _ _ (ri_g1_rotationMap (starAngle r) hK) hrot g (by omega),
    ri_treeCoefficient_rotationMap]

theorem ri_star_treeCoefficient_const {r : ℕ} (hr : 1 ≤ r) (hK : G1 (star r)) (g h : ZMod (2 * r + 1)) :
    treeCoefficient (star r) hK g (by omega) = treeCoefficient (star r) hK h (by omega) := by
  have key : ∀ k : ℕ, treeCoefficient (star r) hK (k : ZMod (2 * r + 1)) (by omega) =
      treeCoefficient (star r) hK 0 (by omega) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, ri_star_treeCoefficient_succ hr hK, ih]
  rw [← ZMod.natCast_zmod_val g, ← ZMod.natCast_zmod_val h, key g.val, key h.val]

theorem ri_starNeg_treeCoefficient_const {r : ℕ} (hr : 1 ≤ r) (hK : G1 (star r))
    (g h : ZMod (2 * r + 1)) :
    treeCoefficient (starNeg r) (g1_reversal_forward hK) g (by omega) =
      treeCoefficient (starNeg r) (g1_reversal_forward hK) h (by omega) := by
  have hg := treeCoefficient_reversal (star r) hK (1 - g) (by omega)
  have hh := treeCoefficient_reversal (star r) hK (1 - h) (by omega)
  simp only [sub_sub_cancel] at hg hh
  show treeCoefficient (reversal (star r)) _ g _ = treeCoefficient (reversal (star r)) _ h _
  rw [hg, hh, ri_star_treeCoefficient_const hr hK (1 - g) (1 - h)]

/-! ### (B-F) flat wall: Δ has zero jump given the IH at the deletion -/
theorem ri_flat_wall_deltaAt_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hf : w.FlatAt j) (hQ : Generic (deleteVertex w.center j))
    (IH : ∀ a b : ZMod n, treeCoefficient (deleteVertex w.center j) hQ.1 a hn =
      treeCoefficient (deleteVertex w.center j) hQ.1 b hn)
    (g h : ZMod (n + 1)) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    ri_deltaAt (by omega) g h (w.curve s₂) = ri_deltaAt (by omega) g h (w.curve s₁) := by
  have hlaw := (w.flat_law_treeCoefficient j hf).2.2
  obtain ⟨b, ⟨hR, hL⟩, -⟩ := w.flat_named_sides hf
  have hg2 := w.generic_punctured s₂ h₂.ne'
  have hg1 := w.generic_punctured s₁ h₁.ne
  rw [ri_deltaAt_of_generic _ g h hg2, ri_deltaAt_of_generic _ g h hg1]
  have hIH := IH (deletionRoot j g) (deletionRoot j h)
  cases b with
  | true =>
    have hL' : w.FlatLeftSide j false := hL
    have ht2 : turn (w.curve s₂) j = -1 := by
      have := hR ⟨s₂.val, h₂, s₂.property.2⟩
      rwa [w.ri_sideTuple_true_val s₂ h₂] at this
    have ht1 : turn (w.curve s₁) j = 1 := by
      have := hL' ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
      rwa [w.ri_sideTuple_false_val s₁ h₁] at this
    have eg := hlaw g s₂ s₁ h₂.ne' h₁.ne ht2 ht1
    have eh := hlaw h s₂ s₁ h₂.ne' h₁.ne ht2 ht1
    linarith
  | false =>
    have hL' : w.FlatLeftSide j true := hL
    have ht1 : turn (w.curve s₁) j = -1 := by
      have := hR ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
      rwa [w.ri_sideTuple_false_val s₁ h₁] at this
    have ht2 : turn (w.curve s₂) j = 1 := by
      have := hL' ⟨s₂.val, h₂, s₂.property.2⟩
      rwa [w.ri_sideTuple_true_val s₂ h₂] at this
    have eg := hlaw g s₁ s₂ h₁.ne h₂.ne' ht1 ht2
    have eh := hlaw h s₁ s₂ h₁.ne h₂.ne' ht1 ht2
    linarith

/-! ### (B-V) vertex–edge wall -/
theorem ri_vertexEdge_wall_deltaAt_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n)
    (hc : w.VertexEdgeAt M a)
    (IH1 : ∀ x y : ZMod (firstHalfSize M a),
      treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1) x
          (contactHalfSizes_bounds hn hc.1).1.1 =
        treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1) y
          (contactHalfSizes_bounds hn hc.1).1.1)
    (IH2 : ∀ x y : ZMod (secondHalfSize M a),
      treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1) x
          (contactHalfSizes_bounds hn hc.1).2.1 =
        treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1) y
          (contactHalfSizes_bounds hn hc.1).2.1)
    (g h : ZMod n) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    ri_deltaAt hn g h (w.curve s₂) = ri_deltaAt hn g h (w.curve s₁) := by
  have hlaw := (w.vertex_edge_law_treeCoefficient M a hn hc).2.2.2.2
  let t : w.SideParameter := ⟨s₂.val, h₂, s₂.property.2⟩
  let s : w.SideParameter := ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
  have hg2 := w.generic_punctured s₂ h₂.ne'
  have hg1 := w.generic_punctured s₁ h₁.ne
  have e2 : (w.sideTuple true t).val = w.curve s₂ := w.ri_sideTuple_true_val s₂ h₂
  have e1 : (w.sideTuple false s).val = w.curve s₁ := w.ri_sideTuple_false_val s₁ h₁
  have eg := hlaw g s t
  have eh := hlaw h s t
  rw [IH1 (halfRoots M a g).1 (halfRoots M a h).1, IH2 (halfRoots M a g).2 (halfRoots M a h).2] at eg
  have a2g := treeCoefficient_congr_tuple _ _ (w.sideTuple true t).property.1 hg2.1 e2 g hn
  have a1g := treeCoefficient_congr_tuple _ _ (w.sideTuple false s).property.1 hg1.1 e1 g hn
  have a2h := treeCoefficient_congr_tuple _ _ (w.sideTuple true t).property.1 hg2.1 e2 h hn
  have a1h := treeCoefficient_congr_tuple _ _ (w.sideTuple false s).property.1 hg1.1 e1 h hn
  rw [ri_deltaAt_of_generic hn g h hg2, ri_deltaAt_of_generic hn g h hg1]
  linarith

/-! ### (B-TEC) triple / extension / cut walls -/
theorem ri_silent_wall_deltaAt_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n)
    (hw : (∃ e f k, w.TripleAt e f k) ∨ (∃ M a, w.ExtensionAt M a) ∨ (∃ i j k, w.PureCutAt i j k))
    (g h : ZMod n) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    ri_deltaAt hn g h (w.curve s₂) = ri_deltaAt hn g h (w.curve s₁) := by
  let t : w.SideParameter := ⟨s₂.val, h₂, s₂.property.2⟩
  let s : w.SideParameter := ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
  have hg2 := w.generic_punctured s₂ h₂.ne'
  have hg1 := w.generic_punctured s₁ h₁.ne
  have e2 : (w.sideTuple true t).val = w.curve s₂ := w.ri_sideTuple_true_val s₂ h₂
  have e1 : (w.sideTuple false s).val = w.curve s₁ := w.ri_sideTuple_false_val s₁ h₁
  have key : ∀ x : ZMod n,
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 x hn =
        treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 x hn := by
    obtain ⟨T, E, C⟩ := WallGerm.triple_and_silent_laws_treeCoefficient (n := n) hn
    rcases hw with ⟨e, f, k, hT⟩ | ⟨M, a, hE⟩ | ⟨i, j, k, hC⟩
    · exact fun x => (T w e f k hT x s t).2.2
    · exact fun x => E w M a hE x s t
    · exact fun x => C w i j k hC x s t
  have a2g := treeCoefficient_congr_tuple _ _ (w.sideTuple true t).property.1 hg2.1 e2 g hn
  have a1g := treeCoefficient_congr_tuple _ _ (w.sideTuple false s).property.1 hg1.1 e1 g hn
  have a2h := treeCoefficient_congr_tuple _ _ (w.sideTuple true t).property.1 hg2.1 e2 h hn
  have a1h := treeCoefficient_congr_tuple _ _ (w.sideTuple false s).property.1 hg1.1 e1 h hn
  have kg := key g
  have kh := key h
  rw [ri_deltaAt_of_generic hn g h hg2, ri_deltaAt_of_generic hn g h hg1]
  linarith

/-! ### (D1) zero-anchor target with the soft edge avoiding g and h -/
theorem ri_softOldIndex_diag_injective {n : ℕ} [NeZero n] :
    Function.Injective (fun j : ZMod n => softOldIndex j j) := by
  intro j j' h
  simp only [softOldIndex_at_attachment] at h
  have h' := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by have := (canonicalPosition j).isLt; omega),
    Nat.mod_eq_of_lt (by have := (canonicalPosition j').isLt; omega)] at h'
  exact canonicalPosition_injective (Fin.ext (by omega))

theorem ri_exists_softEdge_avoiding {m : ℕ} [NeZero m] (hm : 3 ≤ m) (g h : ZMod (m + 1)) :
    ∃ j : ZMod m, softOldIndex j j ≠ g ∧ softOldIndex j j ≠ h := by
  classical
  by_contra hcon
  push Not at hcon
  have hmaps : ∀ j : ZMod m, softOldIndex j j ∈ ({g, h} : Finset (ZMod (m + 1))) := by
    intro j
    by_cases hg : softOldIndex j j = g
    · simp [hg]
    · simp [hcon j hg]
  have hcard := Finset.card_le_card_of_injOn (fun j : ZMod m => softOldIndex j j)
    (s := Finset.univ) (t := {g, h}) (fun j _ => hmaps j) (ri_softOldIndex_diag_injective.injOn)
  have h2 : ({g, h} : Finset (ZMod (m + 1))).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ZMod.card] at hcard
  omega

theorem ri_exists_zero_target {m : ℕ} [NeZero m] (hm : 3 ≤ m) {r : ℤ} (hZ : Admissible (m : ℤ) r)
    (g h : ZMod (m + 1)) :
    ∃ Z : LabelledTuple (m + 1), ∃ hZg : Generic Z, rotationNumber Z = (r : ℝ) ∧
      treeCoefficient Z hZg.1 g (by omega) = 0 ∧ treeCoefficient Z hZg.1 h (by omega) = 0 := by
  obtain ⟨P, hP, hr⟩ := exists_generic_of_admissible hZ
  obtain ⟨j, hjg, hjh⟩ := ri_exists_softEdge_avoiding hm g h
  obtain ⟨q, hq, hmixed⟩ := anchor_mixed_sector_nonempty hm hP j
  obtain ⟨⟨ε₀, hε₀, hrot⟩, -⟩ := soft_rotation_law hm hP j q hq
  obtain ⟨ε₁, hε₁, hle, hsoft⟩ :=
    SoftDuplication.soft_theorem_treeCoefficient hm hP j q hq ε₀ hε₀
  have hε : 0 < ε₁ / 2 := by positivity
  have hε' : ε₁ / 2 < ε₁ := by linarith
  obtain ⟨hQ, hroots⟩ := hsoft (ε₁ / 2) hε hε'
  refine ⟨softInsertion P j q (ε₁ / 2), hQ, ?_, ?_, ?_⟩
  · rw [(hrot (ε₁ / 2) hε (by linarith)).2.1 (Or.inr hmixed), hr]
  · obtain ⟨g', ⟨-, -, -, hzero, -⟩, -⟩ := hroots g (Ne.symm hjg)
    exact hzero hmixed
  · obtain ⟨h', ⟨-, -, -, hzero, -⟩, -⟩ := hroots h (Ne.symm hjh)
    exact hzero hmixed

/-! ### (D3) bow-tie target -/
theorem ri_bowTie_deltaAt_zero (g h k : ZMod 4) :
    ri_deltaAt (by norm_num) g h (shift k bowTie) = 0 := by
  have hgen : Generic (shift k bowTie) := (generic_shift k bowTie).mpr bowTie_generic
  rw [ri_deltaAt_of_generic _ g h hgen, A_small_values_ii k g, A_small_values_ii k h]
  simp

/-- The induction hypothesis: root independence at every arity below `N`. -/
def ri_RootIndepBelow (N : ℕ) : Prop :=
  ∀ k < N, ∀ [NeZero k] (hk : 3 ≤ k) (Q : LabelledTuple k) (hQ : Generic Q) (a b : ZMod k),
    treeCoefficient Q hQ.1 a hk = treeCoefficient Q hQ.1 b hk

/-! ### (C') Δ is transported from P to the target along the path of `SM.transport_lemma` -/
theorem ri_deltaAt_eq_target_of_transport {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (IH : ri_RootIndepBelow (m + 1)) {r : ℤ} {P Z : LabelledTuple (m + 1)}
    (hP : Generic P) (hZ : Generic Z) (hrP : rotationNumber P = r) (hrZ : rotationNumber Z = r)
    (g h : ZMod (m + 1)) :
    ∃ k : ZMod (m + 1), ((((m + 1 : ℕ) : ℤ), r) ≠ (4, 0) → k = 0) ∧
      ri_deltaAt (by omega) g h P = ri_deltaAt (by omega) g h (shift k Z) := by
  obtain ⟨k, hk, path, hcont, h0, h1, -, -, hfin, hwall⟩ :=
    transport_lemma (by omega) hP hZ hrP hrZ
  refine ⟨k, hk, ?_⟩
  rw [← h0, ← h1]
  apply ri_deltaAt_const_along_path (by omega) g h path hcont hfin _ (h0 ▸ hP) (h1 ▸ (generic_shift k Z).mpr hZ)
  intro t ht
  obtain ⟨w, hcenter, hcurve, -, halt⟩ := hwall t ht
  refine ⟨w, hcurve, ?_⟩
  intro s₁ s₂ h₁ h₂
  rcases halt with ⟨j, hf, hdel⟩ | ⟨M, a, hc, hfst, hsnd, hlt1, hlt2⟩ | hT | hE | hC
  · have hQ : Generic (deleteVertex w.center j) := by rw [hcenter]; exact hdel
    exact ri_flat_wall_deltaAt_eq hm w j hf hQ (IH m (by omega) hm _ hQ) g h s₁ s₂ h₁ h₂
  · have hfst' : Generic (firstHalf w.center M a) := by rw [hcenter]; exact hfst
    have hsnd' : Generic (secondHalf w.center M a) := by rw [hcenter]; exact hsnd
    have hb := contactHalfSizes_bounds (by omega : 3 ≤ m + 1) hc.1
    exact ri_vertexEdge_wall_deltaAt_eq (by omega) w M a hc
      (fun x y => IH _ hlt1 hb.1.1 _ hfst' x y) (fun x y => IH _ hlt2 hb.2.1 _ hsnd' x y)
      g h s₁ s₂ h₁ h₂
  · exact ri_silent_wall_deltaAt_eq (by omega) w (Or.inl hT) g h s₁ s₂ h₁ h₂
  · exact ri_silent_wall_deltaAt_eq (by omega) w (Or.inr (Or.inl hE)) g h s₁ s₂ h₁ h₂
  · exact ri_silent_wall_deltaAt_eq (by omega) w (Or.inr (Or.inr hC)) g h s₁ s₂ h₁ h₂


/-! ### (E) the strong induction wrapper -/
abbrev ri_RootIndepAt (n : ℕ) : Prop :=
  ∀ [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (g h : ZMod n),
    treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn

theorem ri_rootIndepBelow_of_forall {N : ℕ} (H : ∀ k < N, ri_RootIndepAt k) : ri_RootIndepBelow N :=
  fun k hk _ hk3 Q hQ a b => H k hk hk3 Q hQ a b

/-- Strong induction on the arity: root independence at every arity. -/
theorem ri_root_independence_all : ∀ n : ℕ, ri_RootIndepAt n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro _ hn P hP g h
  by_cases h3 : n = 3
  · subst h3
    obtain ⟨τ, -, -, hτ⟩ := A_small_values_lemma.1 P hP.1
    rw [hτ g, hτ h]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 3 ≤ m := by omega
    have : NeZero m := ⟨by omega⟩
    obtain ⟨r, hr⟩ := rotationNumber_integer (generic_regular hn hP)
    have hadm : Admissible ((m + 1 : ℕ) : ℤ) r := generic_rotation_admissible hn hP r hr
    have hIH : ri_RootIndepBelow (m + 1) := ri_rootIndepBelow_of_forall IH
    suffices hΔ : ri_deltaAt hn g h P = 0 by
      rw [ri_deltaAt_of_generic hn g h hP] at hΔ
      exact sub_eq_zero.mp hΔ
    obtain ⟨hcases, -, hex2, hex3⟩ :=
      anchor_cases_exhaustive ((m + 1 : ℕ) : ℤ) r hadm (by push_cast; omega)
    rcases hcases with hZ | ⟨hL, hr2⟩ | h40
    · -- (Z): zero anchor target
      have hcast : (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) := by push_cast; ring
      rw [hcast] at hZ
      obtain ⟨Z, hZg, hrZ, hg0, hh0⟩ := ri_exists_zero_target hm hZ g h
      obtain ⟨k, hk, hΔ⟩ :=
        ri_deltaAt_eq_target_of_transport hm hIH hP hZg hr hrZ g h
      have hk0 : k = 0 := hk (fun h40 => hex2 ⟨by rwa [hcast], h40⟩)
      rw [hΔ, hk0, shift_zero, ri_deltaAt_of_generic hn g h hZg, hg0, hh0, sub_zero]
    · -- (L): star target K_r
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr2
      have hmN : ((m + 1 : ℕ) : ℤ) = 2 * |r| + 1 := by
        rcases hL.2 with ⟨-, h⟩ | h
        · exact h
        · exact absurd (congrArg Prod.snd h) hr0
      have hne40 : (((m + 1 : ℕ) : ℤ), r) ≠ (4, 0) := fun h40 => hex3 ⟨⟨hL, hr2⟩, h40⟩
      push_cast at hmN
      rcases lt_or_gt_of_ne hr0 with hneg | hpos
      · rw [abs_of_neg hneg] at hmN
        obtain ⟨r', hm2, hrr⟩ : ∃ r' : ℕ, m = 2 * r' ∧ (r' : ℤ) = -r :=
          ⟨(-r).toNat, by omega, Int.toNat_of_nonneg (by omega)⟩
        subst hm2
        have hr1 : 1 ≤ r' := by omega
        have hK : G1 (star r') := (star_generic_law hr1).1.2.2.2.1.1
        have hZg : Generic (starNeg r') := (star_generic_law hr1).1.2.2.2.2.1
        have hrZ : rotationNumber (starNeg r') = (r : ℝ) := by
          rw [(star_generic_law hr1).1.2.2.2.2.2.2]
          have : (r : ℝ) = -((r' : ℤ) : ℝ) := by rw [hrr]; push_cast; ring
          rw [this]; simp
        obtain ⟨k, hk, hΔ⟩ :=
          ri_deltaAt_eq_target_of_transport hm hIH hP hZg hr hrZ g h
        rw [hΔ, hk hne40, shift_zero, ri_deltaAt_of_generic hn g h hZg]
        exact sub_eq_zero.mpr (ri_starNeg_treeCoefficient_const hr1 hK g h)
      · rw [abs_of_pos hpos] at hmN
        obtain ⟨r', hm2, hrr⟩ : ∃ r' : ℕ, m = 2 * r' ∧ (r' : ℤ) = r :=
          ⟨r.toNat, by omega, Int.toNat_of_nonneg hpos.le⟩
        subst hm2
        have hr1 : 1 ≤ r' := by omega
        have hZg : Generic (star r') := (star_generic_law hr1).1.2.2.2.1
        have hrZ : rotationNumber (star r') = (r : ℝ) := by
          rw [(star_generic_law hr1).1.2.1.2.2.2.2, ← hrr]; simp
        obtain ⟨k, hk, hΔ⟩ :=
          ri_deltaAt_eq_target_of_transport hm hIH hP hZg hr hrZ g h
        rw [hΔ, hk hne40, shift_zero, ri_deltaAt_of_generic hn g h hZg]
        exact sub_eq_zero.mpr (ri_star_treeCoefficient_const hr1 hZg.1 g h)
    · -- (4, 0): bow-tie target
      have h1 := congrArg Prod.fst h40
      have h2 := congrArg Prod.snd h40
      simp only at h1 h2
      have hm3 : m = 3 := by omega
      subst hm3
      subst h2
      have hrZ : rotationNumber bowTie = ((0 : ℤ) : ℝ) := by rw [bowTie_rotation]; simp
      obtain ⟨k, -, hΔ⟩ :=
        ri_deltaAt_eq_target_of_transport hm hIH hP bowTie_generic hr hrZ g h
      rw [hΔ]
      exact ri_bowTie_deltaAt_zero g h k

/-- **thm:root-indep-proof** (`reference/SM/sm-6-comparison.tex`, lines 53–104): for every
generic polygon `P` with `n ≥ 3` vertices and any two edge labels `g, h`, the tree coefficients
agree, `A_g(P) = A_h(P)`. Strong induction on `n`: base `n = 3` by lem:A-small-values (i)
(`A_small_values_lemma`); step by transporting `Δ_gh = A_g − A_h` along the path of
lem:transport (`SM.transport_lemma`) — locally constant off the finitely many walls by the
chi-congruence of prop:A-chamber, zero jump at F/V walls by thm:A-S3 / thm:A-S7 with the
induction hypothesis at the deletion / halves, zero jump at T/E/C walls by thm:A-R3E — to a
target where `Δ_gh = 0` (soft zero anchor, star `K_r`, or bow-tie). -/
theorem root_independence (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (g h : ZMod n) :
    treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn :=
  ri_root_independence_all n hn P hP g h

end SM

