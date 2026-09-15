import SM.TransverseFront
import SM.Rounding
import SM.FrontRecordBridge
import SM.FrontGeomModel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Row 89 ce:rounding — skeleton (architect B): statement verbatim, construction, chain, row

§1-§3 are the statement text of Statements_B.lean, byte for byte.  §4 is the construction of the
printed proof (sm-3:3063-3169) as explicit definitions on `L : SpatialLink c` with
`hL : L.CuspedProjection`: the per-cusp chart package (`CuspChart`: A, δ, the arc `[a, b]` = the
subarc `|u| ≤ s` of the exact chart, the clean neighbourhood `U = rectU` = the chart preimage of the
rectangle `[−s², s²] × [−s³, s³]`), the cutoff `φ = u·ρ(u)` (`ρ` a Mathlib `ContDiffBump`, `ρ = 1` on
`|u| ≤ s/4`, `ρ = 0` for `|u| ≥ s/2`) periodized to `Φ`, the displacement
`Δ = (A λ ε Φ, 0, A y₀ λ ε Φ)` (ce:physical-displacement) with `ε = s/2`, the family map `famMap`,
the slices and the family; §5 the chain of leaf lemmas (all `sorry`, units N, P, F, I, G of
PLAN_B.md §5); §6 the glue (proved) and the witness `roundingFamily`; §7 the constant family for a
cuspless `L`; §8 the row `SM.ce_rounding` PROVED from the chain.  Nothing here is to be ported
without the row's own statement review. -/

namespace SM

open Link SmoothFront Filter Topology
open scoped ContDiff

noncomputable section
open Classical

/-! ## 1. The spatial vocabulary (memo §3, verbatim; = Statements_B.lean §1) -/

structure SpatialLink (c : ℕ) where
  T : Fin c → ℝ → Space
  smooth : ∀ i, ContDiff ℝ ∞ (T i)
  periodic : ∀ i, Function.Periodic (T i) 1
  embedded : ∀ (i j : Fin c) (s t : ℝ), T i s = T j t → i = j ∧ SameT s t
  regular : ∀ i t, deriv (T i) t ≠ 0

namespace SpatialLink

variable {c : ℕ} (L : SpatialLink c)

theorem ext' {L L' : SpatialLink c} (h : L.T = L'.T) : L = L' := by
  cases L; cases L'; cases h; rfl

def projLoop (i : Fin c) : SmoothLoop where
  γ := xzOf (L.T i)
  smooth := ((L.smooth i).fst).prodMk ((L.smooth i).snd.snd)
  periodic := fun t => by
    show xzOf (L.T i) (t + 1) = xzOf (L.T i) t
    simp only [xzOf, xOf, zOf, L.periodic i t]

@[simp] theorem projLoop_γ (i : Fin c) : (L.projLoop i).γ = xzOf (L.T i) := rfl

def height (p : Fin c × ℝ) : ℝ := yOf (L.T p.1) p.2

def IsCusp (i : Fin c) (t : ℝ) : Prop := deriv (xzOf (L.T i)) t = 0

def cuspSet : Set (Fin c × ℝ) := {p | p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ L.IsCusp p.1 p.2}

def ExactCuspGerm (i : Fin c) (t₀ : ℝ) : Prop :=
  ∃ (A δ : ℝ), A ≠ 0 ∧ 0 < δ ∧
    (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), deriv (yOf (L.T i)) t ≠ 0) ∧
    ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ),
      L.T i t = ((L.T i t₀).1 + A * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2,
        yOf (L.T i) t,
        (L.T i t₀).2.2 + A * yOf (L.T i) t₀ * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 2
          + (2 * A / 3) * (yOf (L.T i) t - yOf (L.T i) t₀) ^ 3)

structure CuspedProjection : Prop where
  cusps_finite : L.cuspSet.Finite
  exact_germ : ∀ p ∈ L.cuspSet, L.ExactCuspGerm p.1 p.2
  doubles_finite : (occSetOf L.projLoop).Finite
  transverse : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    det (deriv (xzOf (L.T p.1)) p.2) (deriv (xzOf (L.T q.1)) q.2) ≠ 0
  no_triple : ∀ p q r : Fin c × ℝ, IsDoubleOf L.projLoop p q → IsDoubleOf L.projLoop q r →
    IsDoubleOf L.projLoop p r → False
  heights_distinct : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q → L.height p ≠ L.height q

theorem CuspedProjection.not_isCusp_of_isDouble (h : L.CuspedProjection) {p q : Fin c × ℝ}
    (hpq : IsDoubleOf L.projLoop p q) : ¬ L.IsCusp p.1 p.2 := by
  intro hc
  apply h.transverse p q hpq
  unfold IsCusp at hc
  rw [hc]
  simp [det]

structure RegularGenericProjection : Prop where
  regular : ∀ i t, deriv (xzOf (L.T i)) t ≠ 0
  doubles_finite : (occSetOf L.projLoop).Finite
  transverse : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    det (deriv (xzOf (L.T p.1)) p.2) (deriv (xzOf (L.T q.1)) q.2) ≠ 0
  no_triple : ∀ p q r : Fin c × ℝ, IsDoubleOf L.projLoop p q → IsDoubleOf L.projLoop q r →
    IsDoubleOf L.projLoop p r → False
  heights_distinct : ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q → L.height p ≠ L.height q

structure CleanCuspSmoothing (G : Fin c → SmoothLoop) where
  U : L.cuspSet → Set Plane
  a : L.cuspSet → ℝ
  b : L.cuspSet → ℝ
  disc : ∀ k, IsDisc (U k)
  center : ∀ k, xzOf (L.T k.1.1) k.1.2 ∈ interior (U k)
  disjoint : ∀ k k', k ≠ k' → Disjoint (U k) (U k')
  a_lt : ∀ k, a k < k.1.2
  lt_b : ∀ k, k.1.2 < b k
  len : ∀ k, b k - a k < 1
  clean : ∀ k (q : Fin c × ℝ), xzOf (L.T q.1) q.2 ∈ U k →
    q.1 = k.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ Set.Icc (a k) (b k)
  arc_in : ∀ k, ∀ t ∈ Set.Icc (a k) (b k), xzOf (L.T k.1.1) t ∈ U k
  arc_simple : ∀ k, ∀ t ∈ Set.Icc (a k) (b k), ∀ q : Fin c × ℝ, ¬ SameParam (k.1.1, t) q →
    xzOf (L.T q.1) q.2 ≠ xzOf (L.T k.1.1) t
  agree : ∀ (i : Fin c) (t : ℝ),
    (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (a k) (b k)) →
    (G i).γ t = xzOf (L.T i) t
  inside : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), (G k.1.1).γ t ∈ U k
  regular : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), deriv (G k.1.1).γ t ≠ 0
  simple : ∀ k, Set.InjOn (G k.1.1).γ (Set.Ioo (a k) (b k))
  no_crossing : ∀ k, ∀ t ∈ Set.Ioo (a k) (b k), ∀ q : Fin c × ℝ, ¬ SameParam (k.1.1, t) q →
    (G q.1).γ q.2 ≠ (G k.1.1).γ t

end SpatialLink

/-! ## 2. Families (= Statements_B.lean §2) -/

structure SpatialFamily (c : ℕ) where
  G : ℝ → SpatialLink c
  joint_smooth : ∀ i, ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (G p.1).T i p.2)
    (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)

/-! ## 3. Row 89: the witness structure and the bundle (= Statements_B.lean §3) -/

structure CuspRoundingFamily {c : ℕ} (L : SpatialLink c) where
  fam : SpatialFamily c
  start : fam.G 0 = L
  U : L.cuspSet → Set Plane
  a : L.cuspSet → ℝ
  b : L.cuspSet → ℝ
  a_lt : ∀ k, a k < k.1.2
  lt_b : ∀ k, k.1.2 < b k
  len : ∀ k, b k - a k < 1
  intervals_disjoint : ∀ k k', k ≠ k' → k.1.1 = k'.1.1 →
    ∀ t ∈ Set.Ioo (a k) (b k), ∀ n : ℤ, t + n ∉ Set.Ioo (a k') (b k')
  fixed_outside : ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ (i : Fin c) (t : ℝ),
    (∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (a k) (b k)) →
    (fam.G lam).T i t = L.T i t
  generic : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, (fam.G lam).RegularGenericProjection
  clean : ∀ lam ∈ Set.Ioc (0 : ℝ) 1,
    ∃ cs : L.CleanCuspSmoothing (fam.G lam).projLoop, cs.U = U ∧ cs.a = a ∧ cs.b = b
  creates_no_crossing : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, ∀ p q : Fin c × ℝ,
    IsDoubleOf (fam.G lam).projLoop p q → IsDoubleOf L.projLoop p q
  retains_crossings : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, ∀ p q : Fin c × ℝ,
    IsDoubleOf L.projLoop p q → IsDoubleOf (fam.G lam).projLoop p q
  same_data : ∀ lam ∈ Set.Ioc (0 : ℝ) 1, ∀ p q : Fin c × ℝ, IsDoubleOf L.projLoop p q →
    crossSignOf (fam.G lam).projLoop p q = crossSignOf L.projLoop p q ∧
    ((fam.G lam).height p < (fam.G lam).height q ↔ L.height p < L.height q)

namespace CuspRoundingFamily

variable {c : ℕ} {L : SpatialLink c} (R : CuspRoundingFamily L)

theorem a_lt_b (k : L.cuspSet) : R.a k < R.b k := (R.a_lt k).trans (R.lt_b k)

theorem isDoubleOf_iff {lam : ℝ} (h : lam ∈ Set.Ioc (0 : ℝ) 1) (p q : Fin c × ℝ) :
    IsDoubleOf (R.fam.G lam).projLoop p q ↔ IsDoubleOf L.projLoop p q :=
  ⟨R.creates_no_crossing lam h p q, R.retains_crossings lam h p q⟩

theorem same_circles (lam : ℝ) (i : Fin c) : Function.Periodic ((R.fam.G lam).T i) 1 :=
  (R.fam.G lam).periodic i

end CuspRoundingFamily

structure CeRoundingData : Prop where
  exists_family : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    Nonempty (CuspRoundingFamily L)
  const_of_no_cusps : ∀ {c : ℕ} (L : SpatialLink c), 0 < c → L.CuspedProjection →
    L.cuspSet = ∅ → ∃ R : CuspRoundingFamily L, ∀ lam : ℝ, R.fam.G lam = L

/-! ## 4. The construction (printed proof sm-3:3063-3169) -/

namespace CeRounding

variable {c : ℕ} (L : SpatialLink c)

/-! ### 4.1 Per-cusp chart data (the first paragraph of the proof, sm-3:3064-3094) -/

/-- the cusp point in the page -/
def cuspPt (k : L.cuspSet) : Plane := xzOf (L.T k.1.1) k.1.2
/-- `x₀`, `y₀`, `z₀` of the cusp -/
def x₀ (k : L.cuspSet) : ℝ := (L.T k.1.1 k.1.2).1
def y₀ (k : L.cuspSet) : ℝ := yOf (L.T k.1.1) k.1.2
def z₀ (k : L.cuspSet) : ℝ := (L.T k.1.1 k.1.2).2.2
/-- the germ coordinate `u = y − y₀` -/
def uOf (k : L.cuspSet) (t : ℝ) : ℝ := yOf (L.T k.1.1) t - y₀ L k
/-- the exact germ point (ce:exact-germ) at parameter `t`, with the printed constant `A` -/
def germPt (k : L.cuspSet) (A t : ℝ) : Space :=
  (x₀ L k + A * uOf L k t ^ 2, yOf (L.T k.1.1) t,
    z₀ L k + A * y₀ L k * uOf L k t ^ 2 + (2 * A / 3) * uOf L k t ^ 3)
/-- the positive affine page chart (ce:positive-chart): `X = (x − x₀)/A`,
`Z = 3(z − z₀ − y₀(x − x₀))/(2A)`; it sends the germ to `(u², u³)` -/
def chartX (k : L.cuspSet) (A : ℝ) (q : Plane) : ℝ := (q.1 - x₀ L k) / A
def chartZ (k : L.cuspSet) (A : ℝ) (q : Plane) : ℝ :=
  3 * (q.2 - z₀ L k - y₀ L k * (q.1 - x₀ L k)) / (2 * A)
/-- the clean neighbourhood: the chart preimage of the closed rectangle `[−s², s²] × [−s³, s³]`
(a compact convex set with the cusp point interior — the accepted `IsDisc`); on the exact chart arc
`(u², u³)` it cuts out exactly the subarc `|u| ≤ s` -/
def rectU (k : L.cuspSet) (A s : ℝ) : Set Plane :=
  {q | |chartX L k A q| ≤ s ^ 2 ∧ |chartZ L k A q| ≤ s ^ 3}

/-- The chart package at one cusp: the germ constants, the arc half-width `s` (in `u`), the arc
parameter interval `[a, b]` (the subarc `|u| ≤ s`, inside the germ interval, shorter than `1/4`),
injectivity of `u`, and cleanness of `rectU` ("a sufficiently small open page neighbourhood V meets
only the exact-chart arc", sm-3:3079-3083). -/
structure CuspChart (k : L.cuspSet) where
  A : ℝ
  δ : ℝ
  s : ℝ
  a : ℝ
  b : ℝ
  A_ne : A ≠ 0
  δ_pos : 0 < δ
  s_pos : 0 < s
  s_lt_one : s < 1
  /-- `u` is a coordinate on the germ interval -/
  coord : ∀ t ∈ Set.Ioo (k.1.2 - δ) (k.1.2 + δ), deriv (yOf (L.T k.1.1)) t ≠ 0
  /-- the exact germ on it -/
  germ : ∀ t ∈ Set.Ioo (k.1.2 - δ) (k.1.2 + δ), L.T k.1.1 t = germPt L k A t
  a_mem : k.1.2 - δ < a
  a_lt : a < k.1.2
  lt_b : k.1.2 < b
  b_mem : b < k.1.2 + δ
  len : b - a < 1 / 4
  u_injOn : Set.InjOn (uOf L k) (Set.Ioo (k.1.2 - δ) (k.1.2 + δ))
  u_a : |uOf L k a| = s
  u_b : |uOf L k b| = s
  u_lt : ∀ t ∈ Set.Ioo a b, |uOf L k t| < s
  u_gt : ∀ t ∈ Set.Ioo (k.1.2 - δ) (k.1.2 + δ), t ∉ Set.Icc a b → s < |uOf L k t|
  /-- clean: every point of `L`'s projection in the rectangle lies on the closed arc (mod 1) -/
  clean : ∀ q : Fin c × ℝ, xzOf (L.T q.1) q.2 ∈ rectU L k A s →
    q.1 = k.1.1 ∧ ∃ n : ℤ, q.2 + n ∈ Set.Icc a b

variable (hL : L.CuspedProjection)

include hL in
/-- **Leaf N0.** distinct cusps have distinct page images (two cusps meeting would be a coincidence
at a cusp, excluded by transversality) and there are finitely many: a separation radius -/
theorem exists_sep : ∃ r : ℝ, 0 < r ∧
    ∀ k k' : L.cuspSet, k ≠ k' → 2 * r < dist (cuspPt L k) (cuspPt L k') := by
  sorry

/-- **Leaf N1.** a smooth function with nonvanishing derivative on an open interval is strictly
monotone or strictly antitone there (Darboux) -/
theorem strictMono_or_strictAnti_of_deriv_ne_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {l r : ℝ}
    (h : ∀ t ∈ Set.Ioo l r, deriv f t ≠ 0) :
    StrictMonoOn f (Set.Ioo l r) ∨ StrictAntiOn f (Set.Ioo l r) := by
  sorry

include hL in
/-- **Leaf N2.** "The cusp image is absent from the compact image of the complement of that
interval's interior … Its distance from that complement is positive." -/
theorem remote_far (k : L.cuspSet) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ q : Fin c × ℝ,
      (q.1 = k.1.1 → ∀ n : ℤ, q.2 + n ∉ Set.Ioo (k.1.2 - δ) (k.1.2 + δ)) →
      r₀ ≤ dist (xzOf (L.T q.1) q.2) (cuspPt L k) := by
  sorry

/-- **Leaf N3.** the rectangle shrinks to the cusp point: `rectU ⊆ closedBall (cuspPt) (C s²)` -/
theorem rectU_subset_closedBall (k : L.cuspSet) {A s : ℝ} (hA : A ≠ 0) (hs : 0 < s)
    (hs1 : s ≤ 1) :
    rectU L k A s ⊆ Metric.closedBall (cuspPt L k) (|A| * (|y₀ L k| + 2) * s ^ 2) := by
  sorry

/-- **Leaf N4.** the chart sends the exact germ to `(u², u³)` -/
theorem chart_germ (k : L.cuspSet) {A : ℝ} (hA : A ≠ 0) (t : ℝ) :
    chartX L k A (xzOf (germPt L k A) t) = uOf L k t ^ 2 ∧
    chartZ L k A (xzOf (germPt L k A) t) = uOf L k t ^ 3 := by
  sorry

include hL in
/-- **Leaf N5.** the chart package exists at every cusp, with the rectangle inside any prescribed
ball about the cusp point ("Make these choices at each of the finitely many cusps") -/
theorem exists_cuspChart (k : L.cuspSet) (r : ℝ) (hr : 0 < r) :
    ∃ P : CuspChart L k, rectU L k P.A P.s ⊆ Metric.closedBall (cuspPt L k) r := by
  sorry

/-- the separation radius -/
def sep : ℝ := Classical.choose (exists_sep L hL)

theorem sep_pos : 0 < sep L hL := (Classical.choose_spec (exists_sep L hL)).1

theorem sep_spec (k k' : L.cuspSet) (h : k ≠ k') :
    2 * sep L hL < dist (cuspPt L k) (cuspPt L k') :=
  (Classical.choose_spec (exists_sep L hL)).2 k k' h

/-- the chosen chart package at the cusp `k` -/
def chart (k : L.cuspSet) : CuspChart L k :=
  Classical.choose (exists_cuspChart L hL k (sep L hL) (sep_pos L hL))

theorem chart_small (k : L.cuspSet) :
    rectU L k (chart L hL k).A (chart L hL k).s ⊆ Metric.closedBall (cuspPt L k) (sep L hL) :=
  Classical.choose_spec (exists_cuspChart L hL k (sep L hL) (sep_pos L hL))

/-- the clean neighbourhood, the arc ends and the constants at the cusp `k` -/
def Uk (k : L.cuspSet) : Set Plane := rectU L k (chart L hL k).A (chart L hL k).s
def aK (k : L.cuspSet) : ℝ := (chart L hL k).a
def bK (k : L.cuspSet) : ℝ := (chart L hL k).b
def sK (k : L.cuspSet) : ℝ := (chart L hL k).s
def AK (k : L.cuspSet) : ℝ := (chart L hL k).A
def δK (k : L.cuspSet) : ℝ := (chart L hL k).δ

theorem sK_pos (k : L.cuspSet) : 0 < sK L hL k := (chart L hL k).s_pos

/-! ### 4.2 The cutoff (sm-3:3084-3094) and the rounding formula (sm-3:3096-3103) -/

/-- "a smooth real cutoff equal to one near zero, with support strictly inside (−b, b)": Mathlib's
bump, `= 1` on `|u| ≤ s/4`, `= 0` for `|u| ≥ s/2` -/
def bump (k : L.cuspSet) : ContDiffBump (0 : ℝ) where
  rIn := sK L hL k / 4
  rOut := sK L hL k / 2
  rIn_pos := by have := sK_pos L hL k; linarith
  rIn_lt_rOut := by have := sK_pos L hL k; linarith

/-- `u ρ(u)` as a function of the parameter on the germ interval, `0` elsewhere -/
def φ (k : L.cuspSet) (t : ℝ) : ℝ :=
  if t ∈ Set.Ioo (k.1.2 - δK L hL k) (k.1.2 + δK L hL k) then
    uOf L k t * bump L hL k (uOf L k t) else 0

/-- the periodization of `φ` (the parameter reduced to the window of length 1 about the cusp) -/
def Φ (k : L.cuspSet) (t : ℝ) : ℝ := φ L hL k (t - round (t - k.1.2))

/-- the amplitude `ε` (ce:support-clearance, here explicit: `ε = s/2`) -/
def ε (k : L.cuspSet) : ℝ := sK L hL k / 2

/-- the physical displacement (ce:physical-displacement):
`Δx = A λ ε u ρ(u)`, `Δy = 0`, `Δz = A y₀ λ ε u ρ(u)` -/
def disp (k : L.cuspSet) (lam t : ℝ) : Space :=
  (AK L hL k * lam * ε L hL k * Φ L hL k t, 0, AK L hL k * y₀ L k * lam * ε L hL k * Φ L hL k t)

/-- the finitely many cusps, as a `Finset` -/
def cuspFinset : Finset (Fin c × ℝ) := hL.cusps_finite.toFinset

/-- the displacement indexed by raw parameters (zero off the cusp set) -/
def dispRaw (p : Fin c × ℝ) (lam t : ℝ) : Space :=
  if hp : p ∈ L.cuspSet then disp L hL ⟨p, hp⟩ lam t else 0

/-- **The complete rounding family** (sm-3:3096-3103): `L` plus the displacements of the cusps of the
component, for every real time `λ` -/
def famMap (lam : ℝ) (i : Fin c) (t : ℝ) : Space :=
  L.T i t + ∑ p ∈ (cuspFinset L hL).filter (fun p => p.1 = i), dispRaw L hL p lam t

/-! ## 5. The chain of leaves -/

theorem xzOf_add_int (i : Fin c) (n : ℤ) (t : ℝ) : xzOf (L.T i) (t + n) = xzOf (L.T i) t :=
  (L.projLoop i).eq_add_int n t

theorem xzOf_eq_of_eq {f g : ℝ → Space} {t : ℝ} (h : f t = g t) : xzOf f t = xzOf g t := by
  simp only [xzOf, xOf, zOf, h]

theorem aK_def (k : L.cuspSet) : aK L hL k = (chart L hL k).a := rfl
theorem bK_def (k : L.cuspSet) : bK L hL k = (chart L hL k).b := rfl
theorem sK_def (k : L.cuspSet) : sK L hL k = (chart L hL k).s := rfl
theorem δK_def (k : L.cuspSet) : δK L hL k = (chart L hL k).δ := rfl
theorem AK_def (k : L.cuspSet) : AK L hL k = (chart L hL k).A := rfl
theorem Uk_def (k : L.cuspSet) : Uk L hL k = rectU L k (chart L hL k).A (chart L hL k).s := rfl

theorem uOf_cusp (k : L.cuspSet) : uOf L k k.1.2 = 0 := by
  unfold uOf y₀; ring

theorem continuous_uOf (k : L.cuspSet) : Continuous (uOf L k) := by
  unfold uOf
  exact ((continuous_fst.comp continuous_snd).comp (L.smooth k.1.1).continuous).sub continuous_const

/-! ### Unit P — the cutoff and its periodization -/

/-- **Leaf P1.** `φ` is `C^∞` (it vanishes outside the compact arc `[a, b]` inside the open germ
interval, on which it is a product of smooth functions) -/
theorem φ_contDiff (k : L.cuspSet) : ContDiff ℝ ∞ (φ L hL k) := by
  sorry

/-- **Leaf P2.** `φ` vanishes off the open arc -/
theorem φ_eq_zero_of_notMem (k : L.cuspSet) {t : ℝ} (ht : t ∉ Set.Ioo (aK L hL k) (bK L hL k)) :
    φ L hL k t = 0 := by
  unfold φ
  split_ifs with hmem
  · have hs : sK L hL k ≤ |uOf L k t| := by
      by_cases hIcc : t ∈ Set.Icc (aK L hL k) (bK L hL k)
      · rcases eq_or_lt_of_le hIcc.1 with h1 | h1
        · rw [← h1, aK_def, sK_def]; exact (chart L hL k).u_a.symm.le
        · rcases eq_or_lt_of_le hIcc.2 with h2 | h2
          · rw [h2, bK_def, sK_def]; exact (chart L hL k).u_b.symm.le
          · exact absurd ⟨h1, h2⟩ ht
      · rw [sK_def]; exact ((chart L hL k).u_gt t hmem hIcc).le
    have hb : bump L hL k (uOf L k t) = 0 := by
      apply ContDiffBump.zero_of_le_dist
      rw [Real.dist_eq, sub_zero]
      show sK L hL k / 2 ≤ |uOf L k t|
      linarith [sK_pos L hL k]
    rw [hb, mul_zero]
  · rfl

/-- **Leaf P3.** near the cusp parameter `φ = u` (the cutoff is `1` there) -/
theorem φ_eventuallyEq_u (k : L.cuspSet) : φ L hL k =ᶠ[𝓝 k.1.2] uOf L k := by
  have hδ := (chart L hL k).δ_pos
  have h1 : ∀ᶠ t in 𝓝 k.1.2, t ∈ Set.Ioo (k.1.2 - δK L hL k) (k.1.2 + δK L hL k) :=
    Ioo_mem_nhds (by rw [δK_def]; linarith) (by rw [δK_def]; linarith)
  have hpos : 0 < sK L hL k / 4 := by have := sK_pos L hL k; linarith
  have h2 : ∀ᶠ t in 𝓝 k.1.2, uOf L k t ∈ Metric.closedBall (uOf L k k.1.2) (sK L hL k / 4) :=
    (continuous_uOf L k).continuousAt.eventually_mem (Metric.closedBall_mem_nhds _ hpos)
  filter_upwards [h1, h2] with t ht1 ht2
  unfold φ
  split_ifs
  have hb : bump L hL k (uOf L k t) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    rw [uOf_cusp] at ht2
    exact ht2
  rw [hb, mul_one]

/-- **Leaf P4.** `Φ` is 1-periodic -/
theorem Φ_periodic (k : L.cuspSet) : Function.Periodic (Φ L hL k) 1 := by
  intro t
  unfold Φ
  have h : round (t + 1 - k.1.2) = round (t - k.1.2) + 1 := by
    have := round_add_intCast (t - k.1.2) 1
    rw [Int.cast_one] at this
    rw [← this]; congr 1; ring
  rw [h]; congr 1; push_cast; ring

/-- **Leaf P5.** `Φ` is `C^∞` -/
theorem Φ_contDiff (k : L.cuspSet) : ContDiff ℝ ∞ (Φ L hL k) := by
  sorry

/-- **Leaf P6.** `Φ = φ` on the window `|t − t₀| < 1/2` -/
theorem Φ_eq_φ (k : L.cuspSet) {t : ℝ} (ht : |t - k.1.2| < 1 / 2) : Φ L hL k t = φ L hL k t := by
  unfold Φ
  have h : round (t - k.1.2) = 0 := by
    rw [round_eq_zero_iff]
    rw [abs_lt] at ht
    exact ⟨ht.1.le, ht.2⟩
  rw [h]; simp

/-- **Leaf P7.** `Φ` vanishes at every parameter whose orbit avoids the open arc -/
theorem Φ_eq_zero_of_notMem (k : L.cuspSet) {t : ℝ}
    (ht : ∀ n : ℤ, t + n ∉ Set.Ioo (aK L hL k) (bK L hL k)) : Φ L hL k t = 0 := by
  unfold Φ
  apply φ_eq_zero_of_notMem
  have := ht (-(round (t - k.1.2)))
  push_cast at this
  rwa [← sub_eq_add_neg] at this

/-! ### Unit F — the family map -/

/-- **Leaf F1.** every slice is `C^∞` -/
theorem dispRaw_contDiff (p : Fin c × ℝ) (lam : ℝ) :
    ContDiff ℝ ∞ (fun t => dispRaw L hL p lam t) := by
  unfold dispRaw
  split_ifs with hpc
  · unfold disp
    exact (contDiff_const.mul (Φ_contDiff L hL ⟨p, hpc⟩)).prodMk
      (contDiff_const.prodMk (contDiff_const.mul (Φ_contDiff L hL ⟨p, hpc⟩)))
  · exact contDiff_const

theorem famMap_smooth (lam : ℝ) (i : Fin c) : ContDiff ℝ ∞ (famMap L hL lam i) := by
  unfold famMap
  exact (L.smooth i).add (ContDiff.sum fun p _ => dispRaw_contDiff L hL p lam)

/-- **Leaf F2.** every slice is 1-periodic -/
theorem famMap_periodic (lam : ℝ) (i : Fin c) : Function.Periodic (famMap L hL lam i) 1 := by
  intro t
  unfold famMap
  rw [L.periodic i t]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  unfold dispRaw
  split_ifs with hpc
  · unfold disp; rw [Φ_periodic L hL ⟨p, hpc⟩ t]
  · rfl

/-- **Leaf F3.** "a jointly smooth family on all parameter circles and the closed λ interval" (in
fact on all of `ℝ × ℝ`) -/
theorem dispRaw_joint_contDiff (p : Fin c × ℝ) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => dispRaw L hL p q.1 q.2) := by
  unfold dispRaw
  split_ifs with hpc
  · unfold disp
    have hΦ : ContDiff ℝ ∞ (fun q : ℝ × ℝ => Φ L hL ⟨p, hpc⟩ q.2) :=
      (Φ_contDiff L hL ⟨p, hpc⟩).comp contDiff_snd
    exact (((contDiff_const.mul contDiff_fst).mul contDiff_const).mul hΦ).prodMk
      (contDiff_const.prodMk (((contDiff_const.mul contDiff_fst).mul contDiff_const).mul hΦ))
  · exact contDiff_const

theorem famMap_joint_smooth (i : Fin c) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => famMap L hL p.1 i p.2) := by
  unfold famMap
  exact ((L.smooth i).comp contDiff_snd).add
    (ContDiff.sum fun p _ => dispRaw_joint_contDiff L hL p)

/-- **Leaf F4.** `L_0 = L` -/
theorem famMap_zero : famMap L hL 0 = L.T := by
  funext i t
  unfold famMap
  rw [Finset.sum_eq_zero, add_zero]
  intro p _
  unfold dispRaw
  split_ifs
  · unfold disp; simp
  · rfl

/-- **Leaf F5.** `Δy = 0`: the heights never change -/
theorem dispRaw_y (p : Fin c × ℝ) (lam t : ℝ) : (dispRaw L hL p lam t).2.1 = 0 := by
  unfold dispRaw
  split_ifs <;> rfl

theorem yOf_famMap (lam : ℝ) (i : Fin c) : yOf (famMap L hL lam i) = yOf (L.T i) := by
  funext t
  unfold yOf famMap
  rw [Prod.snd_add, Prod.fst_add]
  have h : (∑ p ∈ (cuspFinset L hL).filter (fun p => p.1 = i), dispRaw L hL p lam t).2.1 =
      ∑ p ∈ (cuspFinset L hL).filter (fun p => p.1 = i), (dispRaw L hL p lam t).2.1 :=
    map_sum ((AddMonoidHom.fst ℝ ℝ).comp (AddMonoidHom.snd ℝ (ℝ × ℝ))) _ _
  rw [h, Finset.sum_eq_zero (fun p _ => dispRaw_y L hL p lam t), add_zero]

/-- **Leaf F6.** "fixed outside disjoint cusp parameter intervals" -/
theorem famMap_eq_of_outside (lam : ℝ) (i : Fin c) (t : ℝ)
    (h : ∀ k : L.cuspSet, k.1.1 = i → ∀ n : ℤ, t + n ∉ Set.Ioo (aK L hL k) (bK L hL k)) :
    famMap L hL lam i t = L.T i t := by
  unfold famMap
  rw [Finset.sum_eq_zero, add_zero]
  intro p hp
  rw [Finset.mem_filter] at hp
  unfold dispRaw
  split_ifs with hpc
  · have hΦ : Φ L hL ⟨p, hpc⟩ t = 0 := Φ_eq_zero_of_notMem L hL ⟨p, hpc⟩ (h ⟨p, hpc⟩ hp.2)
    unfold disp; rw [hΦ]; simp
  · rfl

/-- **Leaf F7.** on the arc of the cusp `k` only that cusp's displacement acts -/
theorem famMap_on_arc (lam : ℝ) (k : L.cuspSet) {t : ℝ} (ht : t ∈ Set.Ioo (aK L hL k) (bK L hL k)) :
    famMap L hL lam k.1.1 t = L.T k.1.1 t + disp L hL k lam t := by
  sorry

/-- **Leaf F10.** the clean neighbourhoods are discs (compact, convex, nonempty interior) -/
theorem Uk_isDisc (k : L.cuspSet) : IsDisc (Uk L hL k) := by
  sorry

/-- **Leaf F11.** about their cusp points -/
theorem cuspPt_mem_interior_Uk (k : L.cuspSet) : cuspPt L k ∈ interior (Uk L hL k) := by
  sorry

/-- **Leaf F12.** the closed arc lies in its neighbourhood -/
theorem arc_in (k : L.cuspSet) {t : ℝ} (ht : t ∈ Set.Icc (aK L hL k) (bK L hL k)) :
    xzOf (L.T k.1.1) t ∈ Uk L hL k := by
  rw [aK_def, bK_def] at ht
  have hmem : t ∈ Set.Ioo (k.1.2 - (chart L hL k).δ) (k.1.2 + (chart L hL k).δ) :=
    ⟨by linarith [(chart L hL k).a_mem, ht.1], by linarith [(chart L hL k).b_mem, ht.2]⟩
  have hu : |uOf L k t| ≤ (chart L hL k).s := by
    rcases eq_or_lt_of_le ht.1 with h1 | h1
    · rw [← h1]; exact (chart L hL k).u_a.le
    · rcases eq_or_lt_of_le ht.2 with h2 | h2
      · rw [h2]; exact (chart L hL k).u_b.le
      · exact ((chart L hL k).u_lt t ⟨h1, h2⟩).le
  have he : xzOf (L.T k.1.1) t = xzOf (germPt L k (chart L hL k).A) t :=
    xzOf_eq_of_eq ((chart L hL k).germ t hmem)
  obtain ⟨hX, hZ⟩ := chart_germ L k (chart L hL k).A_ne t
  rw [Uk_def]
  show |chartX L k (chart L hL k).A (xzOf (L.T k.1.1) t)| ≤ (chart L hL k).s ^ 2 ∧
    |chartZ L k (chart L hL k).A (xzOf (L.T k.1.1) t)| ≤ (chart L hL k).s ^ 3
  rw [he, hX, hZ, abs_pow, abs_pow]
  exact ⟨pow_le_pow_left₀ (abs_nonneg _) hu 2, pow_le_pow_left₀ (abs_nonneg _) hu 3⟩

/-- **Leaf F13.** the closed arc carries no double point of `L` (cleanness and the injectivity of
`Z = u³` on the chart, ce:cubic-difference) -/
theorem arc_simple (k : L.cuspSet) {t : ℝ} (ht : t ∈ Set.Icc (aK L hL k) (bK L hL k))
    (q : Fin c × ℝ) (hq : ¬ SameParam (k.1.1, t) q) :
    xzOf (L.T q.1) q.2 ≠ xzOf (L.T k.1.1) t := by
  sorry

/-! ### Unit I — the slices: embedded, regular, no new coincidence -/

/-- **Leaf I1.** "Spatial immersion holds for every λ because dy/du = 1 in each modified chart and
the rest of L is unchanged" -/
theorem famMap_regular (lam : ℝ) (i : Fin c) (t : ℝ) : deriv (famMap L hL lam i) t ≠ 0 := by
  sorry

/-- **Leaf I2.** "Spatial injectivity follows for the whole family" (`λ ∈ [0,1]`) -/
theorem famMap_embedded {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (i j : Fin c) (s t : ℝ)
    (h : famMap L hL lam i s = famMap L hL lam j t) : i = j ∧ SameT s t := by
  sorry

/-- **Leaf I3.** "the two projected derivatives are never simultaneously zero for λ > 0" -/
theorem proj_regular {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) (i : Fin c) (t : ℝ) :
    deriv (xzOf (famMap L hL lam i)) t ≠ 0 := by
  sorry

/-- **Leaf I4.** "a moved point cannot meet a remote parameter … different modifications cannot
meet each other … these facts exclude every new projected crossing": a projected coincidence of
the slice is a projected coincidence of `L` -/
theorem proj_eq_of_proj_eq {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (p q : Fin c × ℝ)
    (hpq : ¬ SameParam p q)
    (h : xzOf (famMap L hL lam p.1) p.2 = xzOf (famMap L hL lam q.1) q.2) :
    xzOf (L.T p.1) p.2 = xzOf (L.T q.1) q.2 := by
  sorry

/-- **Leaf I5.** "All old double points are outside the chosen supports. Their exact branches …
remain unchanged": the germ of the slice at a branch of an original double point is `L`'s -/
theorem famMap_eventuallyEq_of_double (lam : ℝ) {p q : Fin c × ℝ} (h : IsDoubleOf L.projLoop p q) :
    famMap L hL lam p.1 =ᶠ[𝓝 p.2] L.T p.1 := by
  sorry

/-- **Leaf I6.** the moved arc stays inside its clean neighbourhood (`|X_λ| ≤ s²/4 + s²/4 < s²`,
`|Z_λ| = |u|³ < s³`) -/
theorem famMap_inside {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (k : L.cuspSet) {t : ℝ}
    (ht : t ∈ Set.Ioo (aK L hL k) (bK L hL k)) : xzOf (famMap L hL lam k.1.1) t ∈ Uk L hL k := by
  sorry

/-- **Leaf I7.** the moved arc is simple (`Z_λ = u³` throughout the chart, ce:cubic-difference) -/
theorem famMap_injOn_arc {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (k : L.cuspSet) :
    Set.InjOn (xzOf (famMap L hL lam k.1.1)) (Set.Ioo (aK L hL k) (bK L hL k)) := by
  sorry

/-! ## 6. Glue (proved) and the witness -/

/-- **F9 (proved).** the clean neighbourhoods are pairwise disjoint (each lies in the closed
`sep`-ball about its cusp point; the cusp points are more than `2·sep` apart) -/
theorem Uk_disjoint (k k' : L.cuspSet) (h : k ≠ k') : Disjoint (Uk L hL k) (Uk L hL k') :=
  (Metric.closedBall_disjoint_closedBall (by have := sep_spec L hL k k' h; linarith)).mono
    (chart_small L hL k) (chart_small L hL k')

/-- **F8 (proved).** "disjoint cusp parameter intervals" on the circle -/
theorem arcs_disjoint (k k' : L.cuspSet) (hne : k ≠ k') (hi : k.1.1 = k'.1.1) {t : ℝ}
    (ht : t ∈ Set.Ioo (aK L hL k) (bK L hL k)) (n : ℤ) :
    t + n ∉ Set.Ioo (aK L hL k') (bK L hL k') := by
  intro hn
  have h1 : xzOf (L.T k.1.1) t ∈ Uk L hL k := arc_in L hL k (Set.Ioo_subset_Icc_self ht)
  have h2 : xzOf (L.T k.1.1) t ∈ Uk L hL k' := by
    have := arc_in L hL k' (Set.Ioo_subset_Icc_self hn)
    rw [← hi, xzOf_add_int] at this
    exact this
  exact Set.disjoint_left.mp (Uk_disjoint L hL k k' hne) h1 h2

/-- the time clamped to `[0,1]` (the values of the family outside `[0,1]` carry no claim) -/
def clamp (lam : ℝ) : ℝ := max 0 (min 1 lam)

theorem clamp_mem (lam : ℝ) : clamp lam ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clamp_eq_of_mem {lam : ℝ} (h : lam ∈ Set.Icc (0 : ℝ) 1) : clamp lam = lam := by
  unfold clamp
  rw [min_eq_right h.2, max_eq_right h.1]

/-- the slice `L_λ` -/
def slice (lam : ℝ) : SpatialLink c where
  T := famMap L hL (clamp lam)
  smooth := famMap_smooth L hL (clamp lam)
  periodic := famMap_periodic L hL (clamp lam)
  embedded := famMap_embedded L hL (clamp_mem lam)
  regular := famMap_regular L hL (clamp lam)

theorem slice_T {lam : ℝ} (h : lam ∈ Set.Icc (0 : ℝ) 1) : (slice L hL lam).T = famMap L hL lam := by
  simp only [slice, clamp_eq_of_mem h]

/-- the family `L_λ` -/
def family : SpatialFamily c where
  G := slice L hL
  joint_smooth := fun i =>
    (famMap_joint_smooth L hL i).contDiffOn.congr fun p hp => by
      show (slice L hL p.1).T i p.2 = famMap L hL p.1 i p.2
      rw [slice_T L hL hp.1]

theorem family_G (lam : ℝ) : (family L hL).G lam = slice L hL lam := rfl

theorem slice_zero : slice L hL 0 = L :=
  SpatialLink.ext' (by rw [slice_T L hL ⟨le_rfl, zero_le_one⟩]; exact famMap_zero L hL)

/-- the projection of a slice at a branch of an original double point is `L`'s, with `L`'s germ -/
theorem xzOf_famMap_eventuallyEq_of_double (lam : ℝ) {p q : Fin c × ℝ}
    (h : IsDoubleOf L.projLoop p q) : xzOf (famMap L hL lam p.1) =ᶠ[𝓝 p.2] xzOf (L.T p.1) :=
  (famMap_eventuallyEq_of_double L hL lam h).fun_comp (fun v : Space => (v.1, v.2.2))

theorem xzOf_famMap_eq_of_double (lam : ℝ) {p q : Fin c × ℝ} (h : IsDoubleOf L.projLoop p q) :
    xzOf (famMap L hL lam p.1) p.2 = xzOf (L.T p.1) p.2 :=
  (xzOf_famMap_eventuallyEq_of_double L hL lam h).eq_of_nhds

theorem deriv_xzOf_famMap_eq_of_double (lam : ℝ) {p q : Fin c × ℝ}
    (h : IsDoubleOf L.projLoop p q) :
    deriv (xzOf (famMap L hL lam p.1)) p.2 = deriv (xzOf (L.T p.1)) p.2 :=
  (xzOf_famMap_eventuallyEq_of_double L hL lam h).deriv_eq

/-- the same double points ("creates no crossing, and retains every original crossing") -/
theorem isDoubleOf_slice_iff {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (p q : Fin c × ℝ) :
    IsDoubleOf (slice L hL lam).projLoop p q ↔ IsDoubleOf L.projLoop p q := by
  constructor
  · rintro ⟨hns, he⟩
    refine ⟨hns, ?_⟩
    simp only [SpatialLink.projLoop_γ, slice_T L hL hlam] at he
    exact proj_eq_of_proj_eq L hL hlam p q hns he
  · intro h
    refine ⟨h.1, ?_⟩
    simp only [SpatialLink.projLoop_γ, slice_T L hL hlam]
    rw [xzOf_famMap_eq_of_double L hL lam h, xzOf_famMap_eq_of_double L hL lam h.symm]
    exact h.2

theorem occSetOf_slice_eq {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) :
    occSetOf (slice L hL lam).projLoop = occSetOf L.projLoop := by
  ext p
  simp only [mem_occSetOf]
  constructor
  · rintro ⟨hp, q, hq, hne, he⟩
    have hd : IsDoubleOf (slice L hL lam).projLoop p q :=
      ⟨fun hs => hne (SameParam.eq_of_mem_Ico hp hq hs), he⟩
    exact ⟨hp, q, hq, hne, ((isDoubleOf_slice_iff L hL hlam p q).mp hd).2⟩
  · rintro ⟨hp, q, hq, hne, he⟩
    have hd : IsDoubleOf L.projLoop p q := ⟨fun hs => hne (SameParam.eq_of_mem_Ico hp hq hs), he⟩
    exact ⟨hp, q, hq, hne, ((isDoubleOf_slice_iff L hL hlam p q).mpr hd).2⟩

theorem height_slice {lam : ℝ} (hlam : lam ∈ Set.Icc (0 : ℝ) 1) (p : Fin c × ℝ) :
    (slice L hL lam).height p = L.height p := by
  simp only [SpatialLink.height, slice_T L hL hlam, yOf_famMap]

/-- **G1 (proved from the leaves).** "For positive λ the result is therefore precisely a finite
regular generic diagram" -/
theorem slice_generic {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    (slice L hL lam).RegularGenericProjection := by
  have hlam' : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam.1.le, hlam.2⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i t
    rw [slice_T L hL hlam']
    exact proj_regular L hL hlam i t
  · rw [occSetOf_slice_eq L hL hlam']
    exact hL.doubles_finite
  · intro p q hpq
    have h := (isDoubleOf_slice_iff L hL hlam' p q).mp hpq
    rw [slice_T L hL hlam', deriv_xzOf_famMap_eq_of_double L hL lam h,
      deriv_xzOf_famMap_eq_of_double L hL lam h.symm]
    exact hL.transverse p q h
  · intro p q r hpq hqr hpr
    exact hL.no_triple p q r ((isDoubleOf_slice_iff L hL hlam' p q).mp hpq)
      ((isDoubleOf_slice_iff L hL hlam' q r).mp hqr) ((isDoubleOf_slice_iff L hL hlam' p r).mp hpr)
  · intro p q hpq
    rw [height_slice L hL hlam', height_slice L hL hlam']
    exact hL.heights_distinct p q ((isDoubleOf_slice_iff L hL hlam' p q).mp hpq)

/-- **G2 (proved from the leaves).** "It is exactly a clean cusp smoothing" -/
def sliceClean {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) :
    L.CleanCuspSmoothing (slice L hL lam).projLoop where
  U := Uk L hL
  a := aK L hL
  b := bK L hL
  disc := Uk_isDisc L hL
  center := cuspPt_mem_interior_Uk L hL
  disjoint := Uk_disjoint L hL
  a_lt := fun k => (chart L hL k).a_lt
  lt_b := fun k => (chart L hL k).lt_b
  len := fun k => by have := (chart L hL k).len; show bK L hL k - aK L hL k < 1; unfold bK aK; linarith
  clean := fun k q hq => (chart L hL k).clean q hq
  arc_in := fun k t ht => arc_in L hL k ht
  arc_simple := fun k t ht q hq => arc_simple L hL k ht q hq
  agree := fun i t h => by
    simp only [SpatialLink.projLoop_γ, slice_T L hL ⟨hlam.1.le, hlam.2⟩]
    exact xzOf_eq_of_eq (famMap_eq_of_outside L hL lam i t h)
  inside := fun k t ht => by
    simp only [SpatialLink.projLoop_γ, slice_T L hL ⟨hlam.1.le, hlam.2⟩]
    exact famMap_inside L hL ⟨hlam.1.le, hlam.2⟩ k ht
  regular := fun k t _ => by
    simp only [SpatialLink.projLoop_γ, slice_T L hL ⟨hlam.1.le, hlam.2⟩]
    exact proj_regular L hL hlam k.1.1 t
  simple := fun k => by
    simp only [SpatialLink.projLoop_γ, slice_T L hL ⟨hlam.1.le, hlam.2⟩]
    exact famMap_injOn_arc L hL ⟨hlam.1.le, hlam.2⟩ k
  no_crossing := fun k t ht q hq he => by
    simp only [SpatialLink.projLoop_γ, slice_T L hL ⟨hlam.1.le, hlam.2⟩] at he
    exact arc_simple L hL k (Set.Ioo_subset_Icc_self ht) q hq
      (proj_eq_of_proj_eq L hL ⟨hlam.1.le, hlam.2⟩ q (k.1.1, t) (fun h => hq h.symm) he)

/-- **G3 (proved from the leaves).** "transversality, crossing signs and O/U choices persist" -/
theorem slice_same_data {lam : ℝ} (hlam : lam ∈ Set.Ioc (0 : ℝ) 1) (p q : Fin c × ℝ)
    (h : IsDoubleOf L.projLoop p q) :
    crossSignOf (slice L hL lam).projLoop p q = crossSignOf L.projLoop p q ∧
    ((slice L hL lam).height p < (slice L hL lam).height q ↔ L.height p < L.height q) := by
  have hlam' : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam.1.le, hlam.2⟩
  constructor
  · have e1 : deriv ((slice L hL lam).projLoop p.1).γ p.2 = deriv (L.projLoop p.1).γ p.2 := by
      show deriv (xzOf ((slice L hL lam).T p.1)) p.2 = deriv (xzOf (L.T p.1)) p.2
      rw [slice_T L hL hlam']
      exact deriv_xzOf_famMap_eq_of_double L hL lam h
    have e2 : deriv ((slice L hL lam).projLoop q.1).γ q.2 = deriv (L.projLoop q.1).γ q.2 := by
      show deriv (xzOf ((slice L hL lam).T q.1)) q.2 = deriv (xzOf (L.T q.1)) q.2
      rw [slice_T L hL hlam']
      exact deriv_xzOf_famMap_eq_of_double L hL lam h.symm
    unfold crossSignOf
    rw [e1, e2]
  · rw [height_slice L hL hlam', height_slice L hL hlam']

/-- **The witness** of ce:rounding for a cusped projection, assembled from the chain. -/
def roundingFamily : CuspRoundingFamily L where
  fam := family L hL
  start := slice_zero L hL
  U := Uk L hL
  a := aK L hL
  b := bK L hL
  a_lt := fun k => (chart L hL k).a_lt
  lt_b := fun k => (chart L hL k).lt_b
  len := fun k => by have := (chart L hL k).len; show bK L hL k - aK L hL k < 1; unfold bK aK; linarith
  intervals_disjoint := fun k k' hne hi t ht n => arcs_disjoint L hL k k' hne hi ht n
  fixed_outside := fun lam hlam i t h => by
    rw [family_G, slice_T L hL hlam]
    exact famMap_eq_of_outside L hL lam i t h
  generic := fun lam hlam => slice_generic L hL hlam
  clean := fun lam hlam => ⟨sliceClean L hL hlam, rfl, rfl, rfl⟩
  creates_no_crossing := fun lam hlam p q hpq =>
    (isDoubleOf_slice_iff L hL ⟨hlam.1.le, hlam.2⟩ p q).mp hpq
  retains_crossings := fun lam hlam p q hpq =>
    (isDoubleOf_slice_iff L hL ⟨hlam.1.le, hlam.2⟩ p q).mpr hpq
  same_data := fun lam hlam p q h => slice_same_data L hL hlam p q h

/-! ## 7. "With no cusps take the constant family." -/

section NoCusps

variable (h0 : L.cuspSet = ∅)

include h0 in
theorem noCusp (k : L.cuspSet) : False := by
  obtain ⟨p, hp⟩ := k
  rw [h0] at hp
  exact hp

include h0 in
/-- **Leaf Z1.** a cuspless cusped projection is regular everywhere (every parameter reduces to
the fundamental period, where no cusp exists) -/
theorem regular_of_no_cusps : ∀ (i : Fin c) (t : ℝ), deriv (xzOf (L.T i)) t ≠ 0 := by
  intro i t h
  have hmem : (i, Int.fract t) ∈ L.cuspSet := by
    refine ⟨⟨Int.fract_nonneg t, Int.fract_lt_one t⟩, ?_⟩
    show deriv (xzOf (L.T i)) (Int.fract t) = 0
    have e : Int.fract t = t + ((-⌊t⌋ : ℤ) : ℝ) := by rw [← Int.self_sub_floor]; push_cast; ring
    rw [e, ← SpatialLink.projLoop_γ, (L.projLoop i).deriv_eq_add_int, SpatialLink.projLoop_γ]
    exact h
  rw [h0] at hmem
  exact hmem

/-- the constant family is a rounding family of a cuspless `L` (proved) -/
def constFamily : CuspRoundingFamily L where
  fam :=
    { G := fun _ => L
      joint_smooth := fun i =>
        ((L.smooth i).comp contDiff_snd).contDiffOn }
  start := rfl
  U := fun k => (noCusp L h0 k).elim
  a := fun k => (noCusp L h0 k).elim
  b := fun k => (noCusp L h0 k).elim
  a_lt := fun k => (noCusp L h0 k).elim
  lt_b := fun k => (noCusp L h0 k).elim
  len := fun k => (noCusp L h0 k).elim
  intervals_disjoint := fun k => (noCusp L h0 k).elim
  fixed_outside := fun _ _ _ _ _ => rfl
  generic := fun _ _ =>
    ⟨regular_of_no_cusps L h0, hL.doubles_finite, hL.transverse, hL.no_triple,
      hL.heights_distinct⟩
  clean := fun _ _ =>
    ⟨{ U := fun k => (noCusp L h0 k).elim
       a := fun k => (noCusp L h0 k).elim
       b := fun k => (noCusp L h0 k).elim
       disc := fun k => (noCusp L h0 k).elim
       center := fun k => (noCusp L h0 k).elim
       disjoint := fun k => (noCusp L h0 k).elim
       a_lt := fun k => (noCusp L h0 k).elim
       lt_b := fun k => (noCusp L h0 k).elim
       len := fun k => (noCusp L h0 k).elim
       clean := fun k => (noCusp L h0 k).elim
       arc_in := fun k => (noCusp L h0 k).elim
       arc_simple := fun k => (noCusp L h0 k).elim
       agree := fun _ _ _ => rfl
       inside := fun k => (noCusp L h0 k).elim
       regular := fun k => (noCusp L h0 k).elim
       simple := fun k => (noCusp L h0 k).elim
       no_crossing := fun k => (noCusp L h0 k).elim }, rfl, rfl, rfl⟩
  creates_no_crossing := fun _ _ _ _ h => h
  retains_crossings := fun _ _ _ _ h => h
  same_data := fun _ _ _ _ _ => ⟨rfl, Iff.rfl⟩

theorem constFamily_G (lam : ℝ) : (constFamily L hL h0).fam.G lam = L := rfl

end NoCusps

end CeRounding

/-! ## 8. The row -/

/-- **Lemma ce:rounding (sm-3:3029-3062)**, assembled from the chain of §5-§7. -/
theorem ce_rounding : CeRoundingData where
  exists_family := fun L _ hL => ⟨CeRounding.roundingFamily L hL⟩
  const_of_no_cusps := fun L _ hL h0 =>
    ⟨CeRounding.constFamily L hL h0, fun lam => CeRounding.constFamily_G L hL h0 lam⟩

end

end SM
