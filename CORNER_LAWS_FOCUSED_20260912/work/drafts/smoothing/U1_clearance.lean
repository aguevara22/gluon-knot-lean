import SM.LinkDiagramRecord
import SM.LinkMoves
import SM.LinkRecordExtras
import SM.LinkDiagramExtras
import SM.LinkRecordExtension

/-! # Skeleton FINAL — the oriented smoothing `exists_smoothing` / `smoothing_record`
(Chapter-3 representation layer; lane sm-3:1084-1103).  Plan of record 2026-09-13
(work/drafts/smoothing/PLAN_FINAL.md): tag A's splice-model construction with the following
grafts from tag B — the reusable generic-shadow lemmas (§0'), the `[0,1)`-clamp `clampIco`
(fixing A's `origPt`, which clamped at `1/2`), the explicit no-wrap law `cut_val` of the splice
model, and B's record-bridge architecture (a global "smoothed coordinate" `key` on the occurrences
of `D`, the general first-return lemma `firstReturn_no_between`, and the successor law derived once
at the model level from a per-component rotated monotone coordinate, `succ_of_coord`).

Construction (design note, "cut both strands at parameter distance ε before and after the crossing
point, join crosswise"): with `s = D.overStrand x = ⟨i, a⟩`, `t = D.underStrand x = ⟨j, b⟩`,
`p = crossingPoint x`, `τs, τt ∈ (0,1)` the crossing parameters and `es = edge P_i a`,
`et = edge P_j b`, the four new corner points are
`s⁻ = p − ε es`, `s⁺ = p + ε es`, `t⁻ = p − ε et`, `t⁺ = p + ε et`; the smoothing arcs are the
segments `s⁻ → t⁺` and `t⁻ → s⁺`.  Every strand of the smoothed shadow is of one of seven *kinds*
(`StrandKind`): an unchanged old strand, one of the four cut pieces `[tail s, s⁻]`, `[s⁺, head s]`,
`[tail t, t⁻]`, `[t⁺, head t]`, or one of the two arcs.  All geometry (genericity, cleanness of the
disc, the arcs inside the disc, the outside match, the crossing correspondence) is proved once for an
abstract *splice model* (`SpliceModel`: a shadow with a kind map satisfying six index laws); the two
concrete shadows — `mixedShadow` (two components joined into one of `k_i + k_j + 4` vertices) and
`selfShadow` (one component of `k` vertices split into two of `d + 2` and `k − d + 2` vertices) —
are given explicit vertex tuples by `ZMod.val` index arithmetic and are shown to be splice models.

Status: definitions are real; every lemma of the chain is `sorry`; the two goal theorems at the end
are proved from the chain.  Plan: work/drafts/smoothing/PLAN_A.md. -/

namespace SM.Link

open SM

noncomputable section

/-- The first strand of a crossing (the chosen witness of `IsCrossing`). -/
def Shadow.Crossing.fst {Γ : Shadow} (y : Γ.Crossing) : Γ.Strand := Classical.choose y.2

theorem Shadow.Crossing.fst_mem {Γ : Shadow} (y : Γ.Crossing) : y.fst ∈ y.val := by
  obtain ⟨t, hy, -, -⟩ := Classical.choose_spec y.2
  exact (Finset.ext_iff.mp hy _).mpr (Finset.mem_insert_self _ _)

/-- The second strand of a crossing. -/
def Shadow.Crossing.snd {Γ : Shadow} (y : Γ.Crossing) : Γ.Strand := Γ.other y y.fst_mem

theorem Shadow.Crossing.snd_mem {Γ : Shadow} (y : Γ.Crossing) : y.snd ∈ y.val :=
  Γ.other_mem y y.fst_mem

theorem Shadow.Crossing.val_eq {Γ : Shadow} (y : Γ.Crossing) : y.val = {y.fst, y.snd} :=
  Γ.eq_pair_other y y.fst_mem

/-! ## 0'. Reusable lemmas on generic shadows and on the plane (graft from tag B, §0)

Small facts about any generic shadow, stated once here so that the smoothing lane can cite them;
they belong in LinkDiagramExtras when the lane lands. -/

namespace Shadow

variable (Γ : Shadow)

/-- The plane point at an arbitrary real edge parameter of a strand (extends `eval`). -/
def edgePt (s : Γ.Strand) (t : ℝ) : Plane := edgePoint (Γ.comp s.1).P s.2 t

theorem edgePt_zero (s : Γ.Strand) : Γ.edgePt s 0 = Γ.tail s := by
  unfold edgePt tail; rw [edgePoint_zero]

theorem edgePt_one (s : Γ.Strand) : Γ.edgePt s 1 = Γ.head s := by
  unfold edgePt head; rw [edgePoint_one]

theorem edgePt_eq (s : Γ.Strand) (t : ℝ) : Γ.edgePt s t = Γ.tail s + t • Γ.dir s := rfl

theorem mem_seg_iff (s : Γ.Strand) (q : Plane) :
    q ∈ Γ.seg s ↔ ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ q = Γ.edgePt s t := Iff.rfl

theorem mem_interior_iff (s : Γ.Strand) (q : Plane) :
    q ∈ Γ.interior s ↔ ∃ t, 0 < t ∧ t < 1 ∧ q = Γ.edgePt s t := Iff.rfl

/-- Distances along an edge scale with the edge vector. -/
theorem dist_edgePt (s : Γ.Strand) (t t' : ℝ) :
    dist (Γ.edgePt s t) (Γ.edgePt s t') = |t - t'| * ‖Γ.dir s‖ := by
  rw [edgePt_eq, edgePt_eq, dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul, norm_smul,
    Real.norm_eq_abs]

/-- The closed edge segment is the image of `[0,1]` under the affine parametrisation. -/
theorem seg_eq_image (s : Γ.Strand) :
    Γ.seg s = (fun t : ℝ => Γ.tail s + t • Γ.dir s) '' Set.Icc 0 1 := by
  ext q
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, ⟨h0, h1⟩, rfl⟩
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩
    exact ⟨t, h0, h1, rfl⟩

theorem isCompact_seg' (s : Γ.Strand) : IsCompact (Γ.seg s) := by
  rw [seg_eq_image]
  exact isCompact_Icc.image (by fun_prop)

/-- Closed edge segments are closed (compact) sets: continuous image of `[0,1]`. -/
theorem isClosed_seg (s : Γ.Strand) : IsClosed (Γ.seg s) := by
  exact (Γ.isCompact_seg' s).isClosed

theorem isCompact_seg (s : Γ.Strand) : IsCompact (Γ.seg s) := by
  exact Γ.isCompact_seg' s

/-- Two consecutive edges of a generic shadow meet only at their common vertex (independent
directions meet once; positively collinear consecutive edges only touch). -/
theorem Generic.seg_inter_succ {Γ : Shadow} (hΓ : Γ.Generic) (u : Γ.Strand) :
    Γ.seg u ∩ Γ.seg ⟨u.1, u.2 + 1⟩ = {Γ.head u} := by
  obtain ⟨i, a⟩ := u
  have hreg : RegularPair (Γ.dir ⟨i, a⟩) (Γ.dir ⟨i, a + 1⟩) := by
    have h := hΓ.regular i (a + 1)
    rw [add_sub_cancel_right] at h
    exact h
  have hne : Γ.dir ⟨i, a⟩ ≠ 0 := hreg.1
  have hne' : Γ.dir ⟨i, a + 1⟩ ≠ 0 := hreg.2.1
  have h3 : Γ.head ⟨i, a⟩ = Γ.tail ⟨i, a⟩ + Γ.dir ⟨i, a⟩ := by
    show (Γ.comp i).P (a + 1) = (Γ.comp i).P a + ((Γ.comp i).P (a + 1) - (Γ.comp i).P a)
    abel
  ext q
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨α, hα0, hα1, hqα⟩, ⟨β, hβ0, hβ1, hqβ⟩⟩
    have h1 : q = Γ.tail ⟨i, a⟩ + α • Γ.dir ⟨i, a⟩ := hqα
    have h2 : q = Γ.head ⟨i, a⟩ + β • Γ.dir ⟨i, a + 1⟩ := hqβ
    have hkey : (α - 1) • Γ.dir ⟨i, a⟩ = β • Γ.dir ⟨i, a + 1⟩ := by
      rw [sub_smul, one_smul, sub_eq_iff_eq_add]
      calc α • Γ.dir ⟨i, a⟩ = q - Γ.tail ⟨i, a⟩ := by rw [h1]; abel
        _ = β • Γ.dir ⟨i, a + 1⟩ + Γ.dir ⟨i, a⟩ := by rw [h2, h3]; abel
    have hα : α = 1 := by
      by_cases hd : det (Γ.dir ⟨i, a⟩) (Γ.dir ⟨i, a + 1⟩) = 0
      · obtain ⟨c, hc⟩ : ∃ c : ℝ, Γ.dir ⟨i, a + 1⟩ = c • Γ.dir ⟨i, a⟩ :=
          ⟨_, scalar_of_det_zero hne hd⟩
        have hcpos : 0 < c := by
          rcases lt_trichotomy c 0 with h | h | h
          · exact absurd ⟨c, h, hc⟩ hreg.2.2
          · exact absurd (by rw [hc, h, zero_smul]) hne'
          · exact h
        rw [hc, smul_smul] at hkey
        have h4 := smul_left_injective ℝ hne hkey
        have h5 : 0 ≤ β * c := mul_nonneg hβ0 hcpos.le
        linarith
      · have h4 := independent_of_det_ne_zero hd (α - 1) (-β)
          (by rw [neg_smul, hkey, add_neg_cancel])
        linarith [h4.1]
    subst hα
    rw [h1, one_smul, ← h3]
  · rintro rfl
    exact ⟨Γ.head_mem_seg _, by rw [Γ.head_eq_tail_succ]; exact Γ.tail_mem_seg _⟩

/-- The double point is not a vertex (helper stated before `crossingPoint_not_mem_seg`, which uses
it for the two boundary cases; `Generic.crossingPoint_ne_tail` below is this lemma). -/
theorem Generic.crossingPoint_ne_tail' {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)
    (s : Γ.Strand) : Γ.crossingPoint x ≠ Γ.tail s := by
  intro h
  by_cases hs : s ∈ x.val
  · obtain ⟨τ, h0, h1, hτ⟩ := hΓ.crossingPoint_mem_interior x hs
    have h2 : Γ.edgePt s τ = Γ.edgePt s 0 := by
      rw [Γ.edgePt_zero, ← h]; exact hτ.symm
    exact h0.ne' (edgePoint_injective (Γ.edge_ne_zero hΓ s) h2)
  · obtain ⟨s₀, s₁, hx, hna, -⟩ := x.2
    have hs₀ : s₀ ∈ x.val := by rw [hx]; simp
    obtain ⟨l, m⟩ := s
    apply hΓ.tail_off ⟨l, m⟩ s₀ ?_ (by rw [← h]; exact Γ.crossingPoint_mem x hs₀)
    rintro ⟨l', a, b, hlm, hs₀', hinc⟩
    rw [Sigma.mk.inj_iff] at hlm
    obtain ⟨rfl, ha⟩ := hlm
    obtain rfl := eq_of_heq ha
    subst hs₀'
    rcases hinc with rfl | rfl
    · obtain ⟨τ, h0, h1, hτ⟩ := hΓ.crossingPoint_mem_interior x hs₀
      have h2 : Γ.edgePt ⟨l, m - 1⟩ τ = Γ.edgePt ⟨l, m - 1⟩ 1 := by
        rw [Γ.edgePt_one]
        refine hτ.symm.trans ?_
        rw [h]
        show Γ.tail ⟨l, m⟩ = Γ.tail ⟨l, m - 1 + 1⟩
        rw [sub_add_cancel]
      exact h1.ne (edgePoint_injective (Γ.edge_ne_zero hΓ _) h2)
    · exact hs hs₀

/-- The double point of `x` lies on no edge other than the two edges of `x` (a non-adjacent third
edge through it would give a second crossing with the same point, `crossingPoint_injective`; an
adjacent one a vertex on an edge of `x`, `tail_off`, or a triple point, `no_triple`). -/
theorem Generic.crossingPoint_not_mem_seg {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)
    {t : Γ.Strand} (ht : t ∉ x.val) : Γ.crossingPoint x ∉ Γ.seg t := by
  rintro ⟨θ, h0, h1, hθ⟩
  rcases h0.lt_or_eq with h0 | h0
  · rcases h1.lt_or_eq with h1 | h1
    · obtain ⟨s, s', hx, hna, -⟩ := x.2
      have hs : s ∈ x.val := by rw [hx]; simp
      have hs' : s' ∈ x.val := by rw [hx]; simp
      exact hΓ.no_triple ⟨s, s', t, Γ.ne_of_not_adjacent hna, fun h => ht (h ▸ hs'),
        fun h => ht (h ▸ hs), Γ.crossingPoint x,
        ⟨hΓ.crossingPoint_mem_interior x hs, hΓ.crossingPoint_mem_interior x hs'⟩,
        ⟨θ, h0, h1, hθ⟩⟩
    · subst h1
      obtain ⟨l, m⟩ := t
      exact hΓ.crossingPoint_ne_tail' x ⟨l, m + 1⟩ (by rw [hθ]; exact edgePoint_one _ _)
  · subst h0
    exact hΓ.crossingPoint_ne_tail' x t (by rw [hθ]; exact edgePoint_zero _ _)

/-- The double point is not a vertex. -/
theorem Generic.crossingPoint_ne_tail {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)
    (s : Γ.Strand) : Γ.crossingPoint x ≠ Γ.tail s := by
  exact hΓ.crossingPoint_ne_tail' x s

/-- The two edges of a crossing meet exactly in the double point. -/
theorem Generic.seg_inter_seg_eq {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s t : Γ.Strand}
    (hs : s ∈ x.val) (ht : t ∈ x.val) (hst : s ≠ t) :
    Γ.seg s ∩ Γ.seg t = {Γ.crossingPoint x} := by
  ext q
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hqs, hqt⟩
    apply hΓ.common_point_unique x
    intro u hu
    rcases (Γ.mem_iff_eq_or_other x hs u).mp hu with rfl | rfl
    · exact hqs
    · rwa [← Γ.eq_other_of_mem_of_ne x hs ht hst.symm]
  · rintro rfl
    exact ⟨Γ.crossingPoint_mem x hs, Γ.crossingPoint_mem x ht⟩

/-- The edge parameter of a point of an edge is unique (nonzero edge vector). -/
theorem Generic.edgePt_injective {Γ : Shadow} (hΓ : Γ.Generic) (s : Γ.Strand) :
    Function.Injective (Γ.edgePt s) := by
  exact edgePoint_injective (Γ.edge_ne_zero hΓ s)

/-! Index bookkeeping on strands `⟨i, a ± 1⟩` (used throughout the smoothing lane). -/

theorem mk_add_one_ne (s : Γ.Strand) : (⟨s.1, s.2 + 1⟩ : Γ.Strand) ≠ s := by
  obtain ⟨i, a⟩ := s
  intro h
  rw [Sigma.mk.inj_iff] at h
  exact next_ne_self a (eq_of_heq h.2)

theorem mk_sub_one_ne (s : Γ.Strand) : (⟨s.1, s.2 - 1⟩ : Γ.Strand) ≠ s := by
  obtain ⟨i, a⟩ := s
  intro h
  rw [Sigma.mk.inj_iff] at h
  exact prev_ne_self a (eq_of_heq h.2)

theorem mk_add_one_inj {s t : Γ.Strand} (h : (⟨s.1, s.2 + 1⟩ : Γ.Strand) = ⟨t.1, t.2 + 1⟩) :
    s = t := by
  obtain ⟨i, a⟩ := s
  obtain ⟨j, b⟩ := t
  rw [Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  have h' : a + 1 = b + 1 := eq_of_heq h
  rw [add_right_cancel h']

theorem mk_sub_one_inj {s t : Γ.Strand} (h : (⟨s.1, s.2 - 1⟩ : Γ.Strand) = ⟨t.1, t.2 - 1⟩) :
    s = t := by
  obtain ⟨i, a⟩ := s
  obtain ⟨j, b⟩ := t
  rw [Sigma.mk.inj_iff] at h
  obtain ⟨rfl, h⟩ := h
  have h' : a - 1 = b - 1 := eq_of_heq h
  rw [sub_left_inj.mp h']

theorem mk_add_one_sub_one (s : Γ.Strand) : (⟨s.1, s.2 + 1 - 1⟩ : Γ.Strand) = s := by
  obtain ⟨i, a⟩ := s
  simp

theorem mk_sub_one_add_one (s : Γ.Strand) : (⟨s.1, s.2 - 1 + 1⟩ : Γ.Strand) = s := by
  obtain ⟨i, a⟩ := s
  simp

theorem mk_add_one_eq_iff {s t : Γ.Strand} :
    (⟨s.1, s.2 + 1⟩ : Γ.Strand) = t ↔ s = ⟨t.1, t.2 - 1⟩ := by
  constructor
  · rintro rfl
    exact (Γ.mk_add_one_sub_one s).symm
  · rintro rfl
    exact Γ.mk_sub_one_add_one t

theorem mk_sub_one_eq_iff {s t : Γ.Strand} :
    (⟨s.1, s.2 - 1⟩ : Γ.Strand) = t ↔ s = ⟨t.1, t.2 + 1⟩ := by
  constructor
  · rintro rfl
    exact (Γ.mk_sub_one_add_one s).symm
  · rintro rfl
    exact Γ.mk_add_one_sub_one t

theorem adjacent_mk_add_one (s : Γ.Strand) : Γ.Adjacent s ⟨s.1, s.2 + 1⟩ := by
  obtain ⟨i, a⟩ := s
  exact (Γ.adjacent_mk_iff i a (a + 1)).mpr (Or.inr (Or.inr (by ring)))

theorem adjacent_mk_sub_one (s : Γ.Strand) : Γ.Adjacent s ⟨s.1, s.2 - 1⟩ := by
  obtain ⟨i, a⟩ := s
  exact (Γ.adjacent_mk_iff i a (a - 1)).mpr (Or.inl (by ring))

theorem head_eq_tail_add_dir (s : Γ.Strand) : Γ.head s = Γ.tail s + Γ.dir s := by
  obtain ⟨i, a⟩ := s
  show (Γ.comp i).P (a + 1) = (Γ.comp i).P a + ((Γ.comp i).P (a + 1) - (Γ.comp i).P a)
  abel

theorem head_eq_tail_mk_add_one (s : Γ.Strand) : Γ.head s = Γ.tail ⟨s.1, s.2 + 1⟩ := rfl

theorem tail_mem_seg_pred (s : Γ.Strand) : Γ.tail s ∈ Γ.seg ⟨s.1, s.2 - 1⟩ := by
  have h : Γ.tail s = Γ.head ⟨s.1, s.2 - 1⟩ := by
    rw [Γ.head_eq_tail_mk_add_one]
    exact congrArg Γ.tail (Γ.mk_sub_one_add_one s).symm
  rw [h]
  exact Γ.head_mem_seg _

theorem head_mem_seg_succ (s : Γ.Strand) : Γ.head s ∈ Γ.seg ⟨s.1, s.2 + 1⟩ := by
  rw [Γ.head_eq_tail_mk_add_one]
  exact Γ.tail_mem_seg _

end Shadow

/-- The labels of two non-adjacent edges of a `k`-gon differ by at least `2` in both cyclic
directions. -/
theorem two_le_val_sub_of_not_adjacent {k : ℕ} [NeZero k] {a b : ZMod k} (h : ¬ adjacent a b) :
    2 ≤ (b - a).val ∧ (b - a).val + 2 ≤ k := by
  simp only [adjacent, not_or] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hlt := ZMod.val_lt (b - a)
  have hne0 : (b - a).val ≠ 0 := fun h0 => h2 ((ZMod.val_eq_zero _).mp h0)
  have hne1 : (b - a).val ≠ 1 := by
    intro h1'
    apply h3
    have hc := ZMod.natCast_zmod_val (b - a)
    rw [h1', Nat.cast_one] at hc
    exact hc.symm
  have hnek : (b - a).val + 1 ≠ k := by
    intro hk
    apply h1
    have hc := ZMod.natCast_zmod_val (b - a)
    have hk' : (((b - a).val : ℕ) : ZMod k) + 1 = 0 := by
      rw [← Nat.cast_one, ← Nat.cast_add, hk, ZMod.natCast_self]
    rw [← hc]
    exact eq_neg_of_add_eq_zero_left hk'
  omega

/-- Coordinates in a basis `(u, v)` with `det u v ≠ 0` are unique (the form of
`intersection_parameters_unique` used for all geometry inside the disc). -/
theorem coords_unique {u v : Plane} (hd : det u v ≠ 0) {α β α' β' : ℝ}
    (h : α • u + β • v = α' • u + β' • v) : α = α' ∧ β = β' := by
  have h0 : (α - α') • u + (β - β') • v = 0 := by
    have h' : α • u + β • v - (α' • u + β' • v) = 0 := sub_eq_zero.mpr h
    rw [← h']
    simp only [sub_smul]
    abel
  obtain ⟨h1, h2⟩ := independent_of_det_ne_zero hd _ _ h0
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

/-- A positive rescaling keeps a regular pair regular. -/
theorem regularPair_smul_pos {u v : Plane} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (h : RegularPair u v) : RegularPair (l • u) (m • v) := by
  obtain ⟨hu, hv, hneg⟩ := h
  refine ⟨smul_ne_zero hl.ne' hu, smul_ne_zero hm.ne' hv, ?_⟩
  rintro ⟨r, hr, hrv⟩
  apply hneg
  refine ⟨r * l / m, div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hr hl) hm, ?_⟩
  have hv' : v = m⁻¹ • (m • v) := by rw [smul_smul, inv_mul_cancel₀ hm.ne', one_smul]
  rw [hv', hrv, smul_smul, smul_smul]
  congr 1
  field_simp

/-- Two independent vectors form a regular pair. -/
theorem regularPair_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) : RegularPair u v := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl; apply hd; simp [det]
  · rintro rfl; apply hd; simp [det]
  · rintro ⟨r, -, rfl⟩; exact hd (det_smul_self u r)

/-- The corners at the cut points: `(l•u, u+v)` and `(u+v, l•v)` are regular when `det u v ≠ 0`. -/
theorem regularPair_add_right_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) {l : ℝ} (hl : 0 < l) :
    RegularPair (l • u) (u + v) := by
  have hu : u ≠ 0 := by rintro rfl; apply hd; simp [det]
  have hd' : det u (u + v) ≠ 0 := by
    rw [det_add_right]
    have huu : det u u = 0 := by unfold det; ring
    rwa [huu, zero_add]
  refine ⟨smul_ne_zero hl.ne' hu, ?_, ?_⟩
  · intro h; apply hd'; rw [h]; simp [det]
  · rintro ⟨r, -, h⟩; apply hd'; rw [h, smul_smul, det_smul_self]

theorem regularPair_add_left_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) {l : ℝ} (hl : 0 < l) :
    RegularPair (u + v) (l • v) := by
  have hv : v ≠ 0 := by rintro rfl; apply hd; simp [det]
  have hd' : det (u + v) (l • v) ≠ 0 := by
    have : det (u + v) (l • v) = l * det u v := by
      simp only [det, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this]; exact mul_ne_zero hl.ne' hd
  refine ⟨?_, smul_ne_zero hl.ne' hv, ?_⟩
  · intro h; apply hd'; rw [h]; simp [det]
  · rintro ⟨r, -, h⟩; apply hd'; rw [h, det_smul_self]

/-- The traversal coordinate of an occurrence, unfolded: edge label plus crossing parameter. -/
theorem Diagram.visitCoord_eq (D : Diagram) (v : D.Γ.Visit) :
    D.visitCoord v = (v.2.val.2.val : ℝ) + D.crossingParam v.1 v.2.2 := rfl

/-- Clamp a real number into `[0, 1)` (identity on `[0,1)`, junk `0` outside; every use in this
file is on a parameter already in `[0,1)`). -/
def clampIco (t : ℝ) : Set.Ico (0 : ℝ) 1 :=
  if ht : 0 ≤ t ∧ t < 1 then ⟨t, ht⟩ else ⟨0, ⟨le_rfl, zero_lt_one⟩⟩

theorem clampIco_val_of_mem {t : ℝ} (ht : 0 ≤ t ∧ t < 1) : (clampIco t).val = t := by
  simp [clampIco, ht]

theorem clampIco_val_of_mem' (t : Set.Ico (0 : ℝ) 1) : clampIco t.val = t := by
  apply Subtype.ext; exact clampIco_val_of_mem t.2

/-- **The first return of a cyclic-successor permutation is the cyclic successor within `p`**
(graft from tag B, L5.4b).  If `κ` is injective on each cycle of `f` and no element of the cycle
lies strictly between `κ v` and `κ (f v)`, then no `p`-element of the cycle lies strictly between
`κ v` and the key of the first return of `v` to `p`.  Proof: induction on the return time; the
points `f v, …, f^(n-1) v` are exactly the cycle elements strictly between `κ v` and `κ (f^n v)`
(arcs concatenate, `cycBetween` is a case bash with `linarith`), and none of them is in `p`. -/
theorem firstReturn_no_between {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop)
    [DecidablePred p] (κ : α → ℝ)
    (hκ : ∀ v u, f.SameCycle u v → κ u = κ v → u = v)
    (hf : ∀ v u, f.SameCycle u v → ¬ cycBetween (κ v) (κ u) (κ (f v)))
    (v : {m // p m}) (u : α) (hu : f.SameCycle u v.1) (hp : p u) :
    ¬ cycBetween (κ v.1) (κ u) (κ (firstReturn f p v).1) := by
  sorry

namespace Smoothing

variable (D : Diagram) (x : D.Γ.Crossing)

/-! ## 0. The crossing data -/

/-- The over strand `s = ⟨i, a⟩` of the smoothed crossing. -/
abbrev sS : D.Γ.Strand := D.overStrand x

/-- The under strand `t = ⟨j, b⟩` of the smoothed crossing. -/
abbrev tS : D.Γ.Strand := D.underStrand x

/-- The double point `p`. -/
abbrev pt : Plane := D.Γ.crossingPoint x

/-- The edge parameter of `p` on `s`. -/
abbrev τs : ℝ := D.crossingParam x (D.over_mem x)

/-- The edge parameter of `p` on `t`. -/
abbrev τt : ℝ := D.crossingParam x (D.under_mem x)

/-- The direction of `s`. -/
abbrev es : Plane := D.Γ.dir (sS D x)

/-- The direction of `t`. -/
abbrev et : Plane := D.Γ.dir (tS D x)

theorem sS_ne_tS : sS D x ≠ tS D x := D.over_ne_under x

theorem not_adjacent_sS_tS : ¬ D.Γ.Adjacent (sS D x) (tS D x) := D.not_adjacent_over_under x

theorem det_es_et_ne_zero : det (es D x) (et D x) ≠ 0 := D.det_over_under_ne_zero x

theorem es_ne_zero : es D x ≠ 0 := D.Γ.edge_ne_zero D.generic _

theorem et_ne_zero : et D x ≠ 0 := D.Γ.edge_ne_zero D.generic _

theorem τs_pos : 0 < τs D x := D.crossingParam_pos x _
theorem τs_lt_one : τs D x < 1 := D.crossingParam_lt_one x _
theorem τt_pos : 0 < τt D x := D.crossingParam_pos x _
theorem τt_lt_one : τt D x < 1 := D.crossingParam_lt_one x _

theorem pt_eq_s : pt D x = D.Γ.tail (sS D x) + τs D x • es D x :=
  (D.crossingParam_spec x (D.over_mem x)).2.2

theorem pt_eq_t : pt D x = D.Γ.tail (tS D x) + τt D x • et D x :=
  (D.crossingParam_spec x (D.under_mem x)).2.2

/-! ## 1. The clearance radius `r₁`

`r₁` is the least distance from `p` to a closed edge segment of a strand other than `s`, `t`.  It is
positive because (`crossingPoint_not_mem_seg_other`) no third strand passes through `p`: a
non-adjacent third strand through `p` would give a second crossing with the same double point
(`Generic.crossingPoint_injective`), an adjacent one would put a vertex on `s` or `t` (`tail_off`)
or a triple point (`no_triple`). -/

/-- The strands other than `s` and `t`. -/
def others : Finset D.Γ.Strand :=
  Finset.univ.filter (fun e => e ≠ sS D x ∧ e ≠ tS D x)

theorem mem_others (e : D.Γ.Strand) : e ∈ others D x ↔ e ≠ sS D x ∧ e ≠ tS D x := by
  simp [others]

/-- The strand preceding `s` on its component is neither `s` nor `t`. -/
theorem others_nonempty : (others D x).Nonempty := by
  refine ⟨⟨(sS D x).1, (sS D x).2 - 1⟩, (mem_others D x _).mpr ⟨D.Γ.mk_sub_one_ne _, ?_⟩⟩
  intro h
  apply not_adjacent_sS_tS D x
  rw [← h]
  exact D.Γ.adjacent_mk_sub_one _

/-- **Key clearance lemma**: no strand other than `s`, `t` passes through the double point. -/
theorem crossingPoint_not_mem_seg_other (e : D.Γ.Strand) (hs : e ≠ sS D x) (ht : e ≠ tS D x) :
    pt D x ∉ D.Γ.seg e := by
  refine D.generic.crossingPoint_not_mem_seg x (fun h => ?_)
  rcases (D.mem_iff x e).mp h with h' | h'
  · exact hs h'
  · exact ht h'

/-- The clearance radius: the least distance from `p` to a strand other than `s`, `t`. -/
def r₁ : ℝ :=
  (others D x).inf' (others_nonempty D x) (fun e => Metric.infDist (pt D x) (D.Γ.seg e))

theorem r₁_pos : 0 < r₁ D x := by
  unfold r₁
  rw [Finset.lt_inf'_iff]
  intro e he
  rw [mem_others] at he
  exact ((D.Γ.isClosed_seg e).notMem_iff_infDist_pos ⟨_, D.Γ.tail_mem_seg e⟩).mp
    (crossingPoint_not_mem_seg_other D x e he.1 he.2)

theorem r₁_le_dist {e : D.Γ.Strand} (hs : e ≠ sS D x) (ht : e ≠ tS D x) {q : Plane}
    (hq : q ∈ D.Γ.seg e) : r₁ D x ≤ dist (pt D x) q := by
  exact (Finset.inf'_le _ ((mem_others D x e).mpr ⟨hs, ht⟩)).trans
    (Metric.infDist_le_dist_of_mem hq)

/-- Every vertex of `D` lies on a strand other than `s`, `t` (a vertex of `s` lies on `s ∓ 1`),
hence at distance `≥ r₁` from `p`. -/
theorem r₁_le_dist_tail (e : D.Γ.Strand) : r₁ D x ≤ dist (pt D x) (D.Γ.tail e) := by
  by_cases hs : e = sS D x
  · subst hs
    refine r₁_le_dist D x (e := ⟨(sS D x).1, (sS D x).2 - 1⟩) (D.Γ.mk_sub_one_ne _) ?_
      (D.Γ.tail_mem_seg_pred _)
    intro h
    apply not_adjacent_sS_tS D x
    rw [← h]
    exact D.Γ.adjacent_mk_sub_one _
  · by_cases ht : e = tS D x
    · subst ht
      refine r₁_le_dist D x (e := ⟨(tS D x).1, (tS D x).2 - 1⟩) ?_ (D.Γ.mk_sub_one_ne _)
        (D.Γ.tail_mem_seg_pred _)
      intro h
      apply not_adjacent_sS_tS D x
      rw [← h]
      exact (D.Γ.adjacent_mk_sub_one _).symm
    · exact r₁_le_dist D x hs ht (D.Γ.tail_mem_seg e)

/-- Every other crossing point is at distance `≥ r₁` from `p` (one of its strands is not `s`,`t`). -/
theorem r₁_le_dist_crossingPoint {y : D.Γ.Crossing} (hy : y ≠ x) :
    r₁ D x ≤ dist (pt D x) (D.Γ.crossingPoint y) := by
  obtain ⟨e, he, hes, het⟩ : ∃ e ∈ y.val, e ≠ sS D x ∧ e ≠ tS D x := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hy
    apply Subtype.ext
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rw [D.mem_iff]
      by_cases h : e = sS D x
      · exact Or.inl h
      · exact Or.inr (hcon e he h)
    · rw [D.Γ.crossing_card_two, D.Γ.crossing_card_two]
  exact r₁_le_dist D x hes het (D.Γ.crossingPoint_mem y he)

theorem r₁_le_τs_mul : r₁ D x ≤ τs D x * ‖es D x‖ := by
  have h := r₁_le_dist D x (e := ⟨(sS D x).1, (sS D x).2 - 1⟩) (D.Γ.mk_sub_one_ne _)
    (fun h => not_adjacent_sS_tS D x (by rw [← h]; exact D.Γ.adjacent_mk_sub_one _))
    (D.Γ.tail_mem_seg_pred _)
  rwa [← D.Γ.edgePt_zero, show pt D x = D.Γ.edgePt (sS D x) (τs D x) from pt_eq_s D x,
    D.Γ.dist_edgePt, sub_zero, abs_of_pos (τs_pos D x)] at h
theorem r₁_le_one_sub_τs_mul : r₁ D x ≤ (1 - τs D x) * ‖es D x‖ := by
  have h := r₁_le_dist D x (e := ⟨(sS D x).1, (sS D x).2 + 1⟩) (D.Γ.mk_add_one_ne _)
    (fun h => not_adjacent_sS_tS D x (by rw [← h]; exact D.Γ.adjacent_mk_add_one _))
    (D.Γ.head_mem_seg_succ _)
  rwa [← D.Γ.edgePt_one, show pt D x = D.Γ.edgePt (sS D x) (τs D x) from pt_eq_s D x,
    D.Γ.dist_edgePt, abs_sub_comm, abs_of_pos (sub_pos.mpr (τs_lt_one D x))] at h
theorem r₁_le_τt_mul : r₁ D x ≤ τt D x * ‖et D x‖ := by
  have h := r₁_le_dist D x (e := ⟨(tS D x).1, (tS D x).2 - 1⟩)
    (fun h => not_adjacent_sS_tS D x (by rw [← h]; exact (D.Γ.adjacent_mk_sub_one _).symm))
    (D.Γ.mk_sub_one_ne _) (D.Γ.tail_mem_seg_pred _)
  rwa [← D.Γ.edgePt_zero, show pt D x = D.Γ.edgePt (tS D x) (τt D x) from pt_eq_t D x,
    D.Γ.dist_edgePt, sub_zero, abs_of_pos (τt_pos D x)] at h
theorem r₁_le_one_sub_τt_mul : r₁ D x ≤ (1 - τt D x) * ‖et D x‖ := by
  have h := r₁_le_dist D x (e := ⟨(tS D x).1, (tS D x).2 + 1⟩)
    (fun h => not_adjacent_sS_tS D x (by rw [← h]; exact (D.Γ.adjacent_mk_add_one _).symm))
    (D.Γ.mk_add_one_ne _) (D.Γ.head_mem_seg_succ _)
  rwa [← D.Γ.edgePt_one, show pt D x = D.Γ.edgePt (tS D x) (τt D x) from pt_eq_t D x,
    D.Γ.dist_edgePt, abs_sub_comm, abs_of_pos (sub_pos.mpr (τt_lt_one D x))] at h

/-! ## 2. Admissible cut parameters `ε` -/

/-- The constraints on the cut parameter: the cut points stay inside the open edges and inside the
clearance ball. -/
structure SmallEps (ε : ℝ) : Prop where
  pos : 0 < ε
  lt_τs : ε < τs D x
  lt_one_sub_τs : ε < 1 - τs D x
  lt_τt : ε < τt D x
  lt_one_sub_τt : ε < 1 - τt D x
  mul_es_lt : ε * ‖es D x‖ < r₁ D x
  mul_et_lt : ε * ‖et D x‖ < r₁ D x

/-- An explicit admissible cut parameter: half the minimum of the six bounds. -/
def eps : ℝ :=
  min (min (min (τs D x) (1 - τs D x)) (min (τt D x) (1 - τt D x)))
    (min (r₁ D x / ‖es D x‖) (r₁ D x / ‖et D x‖)) / 2

theorem eps_small : SmallEps D x (eps D x) := by
  have hes : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
  have het : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
  have hr := r₁_pos D x
  have h1 := τs_pos D x
  have h2 := sub_pos.mpr (τs_lt_one D x)
  have h3 := τt_pos D x
  have h4 := sub_pos.mpr (τt_lt_one D x)
  have hA : 0 < r₁ D x / ‖es D x‖ := div_pos hr hes
  have hB : 0 < r₁ D x / ‖et D x‖ := div_pos hr het
  obtain ⟨hpos, hm1, hm2, hm3, hm4, hm5, hm6⟩ : 0 < eps D x ∧ eps D x ≤ τs D x / 2 ∧
      eps D x ≤ (1 - τs D x) / 2 ∧ eps D x ≤ τt D x / 2 ∧ eps D x ≤ (1 - τt D x) / 2 ∧
      eps D x ≤ r₁ D x / ‖es D x‖ / 2 ∧ eps D x ≤ r₁ D x / ‖et D x‖ / 2 := by
    unfold eps
    refine ⟨by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · gcongr
      simp only [min_le_iff, le_refl, true_or, or_true]
  refine ⟨hpos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · linarith
  · rw [← lt_div_iff₀ hes]; linarith
  · rw [← lt_div_iff₀ het]; linarith

/-- No other occurrence on `s` lies within parameter distance `ε` of the double point (its crossing
point is at distance `≥ r₁ > ε‖es‖` from `p`, `r₁_le_dist_crossingPoint`); the analogue of tag B's
`Small.ε_vis_o`.  Used to place the passage of every other crossing on the right cut piece. -/
theorem crossingParam_far_s {ε : ℝ} (hε : SmallEps D x ε) (w : D.Γ.Visit) (hw : w.2.val = sS D x)
    (hne : w.1 ≠ x) : ε < |D.crossingParam w.1 w.2.2 - τs D x| := by
  have hes : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
  have h1 := r₁_le_dist_crossingPoint D x hne
  have h2 : D.Γ.crossingPoint w.1 = D.Γ.edgePt (sS D x) (D.crossingParam w.1 w.2.2) := by
    rw [← hw]
    exact (D.crossingParam_spec w.1 w.2.2).2.2
  rw [h2, show pt D x = D.Γ.edgePt (sS D x) (τs D x) from pt_eq_s D x, D.Γ.dist_edgePt] at h1
  have h3 : r₁ D x ≤ |τs D x - D.crossingParam w.1 w.2.2| * ‖es D x‖ := h1
  have h4 := hε.mul_es_lt
  rw [abs_sub_comm]
  by_contra hcon
  push Not at hcon
  have h5 : |τs D x - D.crossingParam w.1 w.2.2| * ‖es D x‖ ≤ ε * ‖es D x‖ :=
    mul_le_mul_of_nonneg_right hcon hes.le
  linarith

theorem crossingParam_far_t {ε : ℝ} (hε : SmallEps D x ε) (w : D.Γ.Visit) (hw : w.2.val = tS D x)
    (hne : w.1 ≠ x) : ε < |D.crossingParam w.1 w.2.2 - τt D x| := by
  have het : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
  have h1 := r₁_le_dist_crossingPoint D x hne
  have h2 : D.Γ.crossingPoint w.1 = D.Γ.edgePt (tS D x) (D.crossingParam w.1 w.2.2) := by
    rw [← hw]
    exact (D.crossingParam_spec w.1 w.2.2).2.2
  rw [h2, show pt D x = D.Γ.edgePt (tS D x) (τt D x) from pt_eq_t D x, D.Γ.dist_edgePt] at h1
  have h3 : r₁ D x ≤ |τt D x - D.crossingParam w.1 w.2.2| * ‖et D x‖ := h1
  have h4 := hε.mul_et_lt
  rw [abs_sub_comm]
  by_contra hcon
  push Not at hcon
  have h5 : |τt D x - D.crossingParam w.1 w.2.2| * ‖et D x‖ ≤ ε * ‖et D x‖ :=
    mul_le_mul_of_nonneg_right hcon het.le
  linarith

/-! ## 3. The four new corner points and the smoothing arcs -/

variable (ε : ℝ)

/-- `s⁻ = p − ε es`: the cut point on `s` before the crossing. -/
def sMinus : Plane := pt D x - ε • es D x
/-- `s⁺ = p + ε es`. -/
def sPlus : Plane := pt D x + ε • es D x
/-- `t⁻ = p − ε et`. -/
def tMinus : Plane := pt D x - ε • et D x
/-- `t⁺ = p + ε et`. -/
def tPlus : Plane := pt D x + ε • et D x

theorem sMinus_eq_edgePoint : sMinus D x ε = edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (τs D x - ε) := by
  unfold sMinus
  rw [pt_eq_s, add_sub_assoc, ← sub_smul]
  rfl
theorem sPlus_eq_edgePoint : sPlus D x ε = edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (τs D x + ε) := by
  unfold sPlus
  rw [pt_eq_s, add_assoc, ← add_smul]
  rfl
theorem tMinus_eq_edgePoint : tMinus D x ε = edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (τt D x - ε) := by
  unfold tMinus
  rw [pt_eq_t, add_sub_assoc, ← sub_smul]
  rfl
theorem tPlus_eq_edgePoint : tPlus D x ε = edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (τt D x + ε) := by
  unfold tPlus
  rw [pt_eq_t, add_assoc, ← add_smul]
  rfl

/-- Distance of the cut points from `p`. -/
theorem dist_sMinus : dist (sMinus D x ε) (pt D x) = |ε| * ‖es D x‖ := by
  rw [sMinus, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]

/-! ## 4. Strand kinds and the abstract splice model

The seven kinds of strands of a smoothed shadow.  `kindTail`, `kindDir` give the tail vertex and
the direction of a kind; `kindPred` is the kind of the preceding strand on the same component
(the reconnection is visible here: the successor of `cutStartS` is `arcST`, whose successor is
`cutEndT`).  `kindOrig` is the strand of `D` a kind is a piece of (arcs are assigned `s`; never
used for arcs). -/

inductive StrandKind (D : Diagram) (x : D.Γ.Crossing)
  | old (e : D.Γ.Strand)
  | cutStartS | cutEndS | cutStartT | cutEndT
  | arcST | arcTS
  deriving DecidableEq

namespace StrandKind

variable {D x}

/-- Tail vertex of a kind. -/
def tail (ε : ℝ) : StrandKind D x → Plane
  | old e => D.Γ.tail e
  | cutStartS => D.Γ.tail (sS D x)
  | cutEndS => sPlus D x ε
  | cutStartT => D.Γ.tail (tS D x)
  | cutEndT => tPlus D x ε
  | arcST => sMinus D x ε
  | arcTS => tMinus D x ε

/-- Direction of a kind. -/
def dir (ε : ℝ) : StrandKind D x → Plane
  | old e => D.Γ.dir e
  | cutStartS => (τs D x - ε) • es D x
  | cutEndS => (1 - τs D x - ε) • es D x
  | cutStartT => (τt D x - ε) • et D x
  | cutEndT => (1 - τt D x - ε) • et D x
  | arcST => ε • (es D x + et D x)
  | arcTS => ε • (es D x + et D x)

/-- Head vertex of a kind. -/
def head (ε : ℝ) (κ : StrandKind D x) : Plane := κ.tail ε + κ.dir ε

/-- Closed segment of a kind. -/
def seg (ε : ℝ) (κ : StrandKind D x) : Set Plane :=
  {q | ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ q = κ.tail ε + θ • κ.dir ε}

/-- Open segment of a kind. -/
def interior (ε : ℝ) (κ : StrandKind D x) : Set Plane :=
  {q | ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ q = κ.tail ε + θ • κ.dir ε}

/-- The strand of `D` a kind is a piece of. -/
def orig : StrandKind D x → D.Γ.Strand
  | old e => e
  | cutStartS => sS D x
  | cutEndS => sS D x
  | cutStartT => tS D x
  | cutEndT => tS D x
  | arcST => sS D x
  | arcTS => tS D x

/-- The kind of the strand preceding a strand of the given kind on its component. -/
def pred : StrandKind D x → StrandKind D x
  | old e =>
      if e = ⟨(sS D x).1, (sS D x).2 + 1⟩ then cutEndS
      else if e = ⟨(tS D x).1, (tS D x).2 + 1⟩ then cutEndT
      else old ⟨e.1, e.2 - 1⟩
  | cutStartS => old ⟨(sS D x).1, (sS D x).2 - 1⟩
  | cutEndS => arcTS
  | cutStartT => old ⟨(tS D x).1, (tS D x).2 - 1⟩
  | cutEndT => arcST
  | arcST => cutStartS
  | arcTS => cutStartT

/-- The kind of the strand following a strand of the given kind on its component. -/
def succ : StrandKind D x → StrandKind D x
  | old e =>
      if e = ⟨(sS D x).1, (sS D x).2 - 1⟩ then cutStartS
      else if e = ⟨(tS D x).1, (tS D x).2 - 1⟩ then cutStartT
      else old ⟨e.1, e.2 + 1⟩
  | cutStartS => arcST
  | cutEndS => old ⟨(sS D x).1, (sS D x).2 + 1⟩
  | cutStartT => arcTS
  | cutEndT => old ⟨(tS D x).1, (tS D x).2 + 1⟩
  | arcST => cutEndT
  | arcTS => cutEndS

/-- The kinds that occur in a smoothed shadow: everything except the two erased strands. -/
def Occurs (κ : StrandKind D x) : Prop := κ ≠ old (sS D x) ∧ κ ≠ old (tS D x)

theorem occurs_cutStartS : (cutStartS : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_cutEndS : (cutEndS : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_cutStartT : (cutStartT : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_cutEndT : (cutEndT : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_arcST : (arcST : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_arcTS : (arcTS : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_old {e : D.Γ.Strand} (hs : e ≠ sS D x) (ht : e ≠ tS D x) : (old e : StrandKind D x).Occurs :=
  ⟨fun h => hs (StrandKind.old.inj h), fun h => ht (StrandKind.old.inj h)⟩

/-- The kind of the crossing parameter: the parameter on the original strand of a point at
parameter `θ` of a kind (identity on old strands, affine rescaling on the cut pieces). -/
def origParam (ε : ℝ) : StrandKind D x → ℝ → ℝ
  | old _ => fun θ => θ
  | cutStartS => fun θ => θ * (τs D x - ε)
  | cutEndS => fun θ => τs D x + ε + θ * (1 - τs D x - ε)
  | cutStartT => fun θ => θ * (τt D x - ε)
  | cutEndT => fun θ => τt D x + ε + θ * (1 - τt D x - ε)
  | arcST => fun _ => τs D x
  | arcTS => fun _ => τt D x

/-- The inverse rescaling: the parameter on the cut piece of a point at parameter `θ` of the
original strand. -/
def liftParam (ε : ℝ) : StrandKind D x → ℝ → ℝ
  | old _ => fun θ => θ
  | cutStartS => fun θ => θ / (τs D x - ε)
  | cutEndS => fun θ => (θ - τs D x - ε) / (1 - τs D x - ε)
  | cutStartT => fun θ => θ / (τt D x - ε)
  | cutEndT => fun θ => (θ - τt D x - ε) / (1 - τt D x - ε)
  | arcST => fun θ => θ
  | arcTS => fun θ => θ

/-- Adjacency of kinds: same kind, or successor/predecessor. -/
def Adj (κ κ' : StrandKind D x) : Prop := κ' = κ ∨ κ' = κ.succ ∨ κ' = κ.pred

/-- The tail vertex of a kind is an endpoint of another kind: the kind itself or its predecessor. -/
def Incident (κ κ' : StrandKind D x) : Prop := κ' = κ ∨ κ' = κ.pred

theorem pred_succ (κ : StrandKind D x) (hκ : κ.Occurs) : κ.succ.pred = κ := by
  obtain ⟨hs, ht⟩ := hκ
  cases κ with
  | old e =>
    have hes : e ≠ sS D x := fun h => hs (congrArg old h)
    have het : e ≠ tS D x := fun h => ht (congrArg old h)
    simp only [succ]
    split_ifs with h1 h2
    · subst h1; rfl
    · subst h2; rfl
    · have hns : (⟨e.1, e.2 + 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩ :=
        fun h => hes (D.Γ.mk_add_one_inj h)
      have hnt : (⟨e.1, e.2 + 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ :=
        fun h => het (D.Γ.mk_add_one_inj h)
      simp only [pred, hns, hnt, ↓reduceIte]
      rw [D.Γ.mk_add_one_sub_one]
  | cutStartS => rfl
  | cutEndS => simp [succ, pred]
  | cutStartT => rfl
  | cutEndT =>
    have h : (⟨(tS D x).1, (tS D x).2 + 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩ :=
      fun h => sS_ne_tS D x (D.Γ.mk_add_one_inj h).symm
    simp [succ, pred, h]
  | arcST => rfl
  | arcTS => rfl

theorem succ_pred (κ : StrandKind D x) (hκ : κ.Occurs) : κ.pred.succ = κ := by
  obtain ⟨hs, ht⟩ := hκ
  cases κ with
  | old e =>
    have hes : e ≠ sS D x := fun h => hs (congrArg old h)
    have het : e ≠ tS D x := fun h => ht (congrArg old h)
    simp only [pred]
    split_ifs with h1 h2
    · subst h1; rfl
    · subst h2; rfl
    · have hns : (⟨e.1, e.2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 - 1⟩ :=
        fun h => hes (D.Γ.mk_sub_one_inj h)
      have hnt : (⟨e.1, e.2 - 1⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 - 1⟩ :=
        fun h => het (D.Γ.mk_sub_one_inj h)
      simp only [succ, hns, hnt, ↓reduceIte]
      rw [D.Γ.mk_sub_one_add_one]
  | cutStartS => simp [succ, pred]
  | cutEndS => rfl
  | cutStartT =>
    have h : (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 - 1⟩ :=
      fun h => sS_ne_tS D x (D.Γ.mk_sub_one_inj h).symm
    simp [succ, pred, h]
  | cutEndT => rfl
  | arcST => rfl
  | arcTS => rfl

theorem succ_occurs (κ : StrandKind D x) (hκ : κ.Occurs) : κ.succ.Occurs := by
  obtain ⟨hs, ht⟩ := hκ
  cases κ with
  | old e =>
    simp only [succ]
    split_ifs with h1 h2
    · exact occurs_cutStartS
    · exact occurs_cutStartT
    · refine occurs_old ?_ ?_
      · intro h; exact h1 (D.Γ.mk_add_one_eq_iff.mp h)
      · intro h; exact h2 (D.Γ.mk_add_one_eq_iff.mp h)
  | cutStartS => exact occurs_arcST
  | cutEndS =>
    show (old ⟨(sS D x).1, (sS D x).2 + 1⟩ : StrandKind D x).Occurs
    refine occurs_old (D.Γ.mk_add_one_ne _) ?_
    intro h
    apply not_adjacent_sS_tS D x
    rw [← h]
    exact D.Γ.adjacent_mk_add_one _
  | cutStartT => exact occurs_arcTS
  | cutEndT =>
    show (old ⟨(tS D x).1, (tS D x).2 + 1⟩ : StrandKind D x).Occurs
    refine occurs_old ?_ (D.Γ.mk_add_one_ne _)
    intro h
    apply not_adjacent_sS_tS D x
    rw [← h]
    exact (D.Γ.adjacent_mk_add_one _).symm
  | arcST => exact occurs_cutEndT
  | arcTS => exact occurs_cutEndS

theorem pred_occurs (κ : StrandKind D x) (hκ : κ.Occurs) : κ.pred.Occurs := by
  obtain ⟨hs, ht⟩ := hκ
  cases κ with
  | old e =>
    simp only [pred]
    split_ifs with h1 h2
    · exact occurs_cutEndS
    · exact occurs_cutEndT
    · refine occurs_old ?_ ?_
      · intro h; exact h1 (D.Γ.mk_sub_one_eq_iff.mp h)
      · intro h; exact h2 (D.Γ.mk_sub_one_eq_iff.mp h)
  | cutStartS =>
    show (old ⟨(sS D x).1, (sS D x).2 - 1⟩ : StrandKind D x).Occurs
    refine occurs_old (D.Γ.mk_sub_one_ne _) ?_
    intro h
    apply not_adjacent_sS_tS D x
    rw [← h]
    exact D.Γ.adjacent_mk_sub_one _
  | cutEndS => exact occurs_arcTS
  | cutStartT =>
    show (old ⟨(tS D x).1, (tS D x).2 - 1⟩ : StrandKind D x).Occurs
    refine occurs_old ?_ (D.Γ.mk_sub_one_ne _)
    intro h
    apply not_adjacent_sS_tS D x
    rw [← h]
    exact (D.Γ.adjacent_mk_sub_one _).symm
  | cutEndT => exact occurs_arcST
  | arcST => exact occurs_cutStartS
  | arcTS => exact occurs_cutStartT

/-- Consecutive kinds fit: the head of a kind is the tail of its successor. -/
theorem head_eq_tail_succ (ε : ℝ) (κ : StrandKind D x) (hκ : κ.Occurs) :
    κ.head ε = κ.succ.tail ε := by
  cases κ with
  | old e =>
    simp only [head, succ]
    split_ifs with h1 h2
    · subst h1
      simp only [tail, dir]
      rw [← D.Γ.head_eq_tail_add_dir, D.Γ.head_eq_tail_mk_add_one]
      exact congrArg D.Γ.tail (D.Γ.mk_sub_one_add_one (sS D x))
    · subst h2
      simp only [tail, dir]
      rw [← D.Γ.head_eq_tail_add_dir, D.Γ.head_eq_tail_mk_add_one]
      exact congrArg D.Γ.tail (D.Γ.mk_sub_one_add_one (tS D x))
    · simp only [tail, dir]
      rw [← D.Γ.head_eq_tail_add_dir, D.Γ.head_eq_tail_mk_add_one]
  | cutStartS =>
    simp only [head, succ, tail, dir, sMinus]
    rw [pt_eq_s, sub_smul, add_sub_assoc]
  | cutEndS =>
    simp only [head, succ, tail, dir, sPlus]
    rw [pt_eq_s, ← D.Γ.head_eq_tail_mk_add_one, D.Γ.head_eq_tail_add_dir]
    simp only [sub_smul, one_smul]
    abel
  | cutStartT =>
    simp only [head, succ, tail, dir, tMinus]
    rw [pt_eq_t, sub_smul, add_sub_assoc]
  | cutEndT =>
    simp only [head, succ, tail, dir, tPlus]
    rw [pt_eq_t, ← D.Γ.head_eq_tail_mk_add_one, D.Γ.head_eq_tail_add_dir]
    simp only [sub_smul, one_smul]
    abel
  | arcST =>
    simp only [head, succ, tail, dir, sMinus, tPlus, smul_add]
    abel
  | arcTS =>
    simp only [head, succ, tail, dir, tMinus, sPlus, smul_add]
    abel

/-- Every point of a kind lies on its original strand at the rescaled parameter (cut pieces and
old strands). -/
theorem tail_add_smul_dir (ε : ℝ) (κ : StrandKind D x) (hκ : κ ≠ arcST) (hκ' : κ ≠ arcTS) (θ : ℝ) :
    κ.tail ε + θ • κ.dir ε = edgePoint (D.Γ.comp κ.orig.1).P κ.orig.2 (κ.origParam ε θ) := by
  cases κ with
  | old e => rfl
  | cutStartS =>
    simp only [tail, dir, orig, origParam, smul_smul]
    rfl
  | cutEndS =>
    simp only [tail, dir, orig, origParam, sPlus]
    rw [pt_eq_s]
    show _ = D.Γ.tail (sS D x) + (τs D x + ε + θ * (1 - τs D x - ε)) • es D x
    simp only [add_smul, smul_smul]
    abel
  | cutStartT =>
    simp only [tail, dir, orig, origParam, smul_smul]
    rfl
  | cutEndT =>
    simp only [tail, dir, orig, origParam, tPlus]
    rw [pt_eq_t]
    show _ = D.Γ.tail (tS D x) + (τt D x + ε + θ * (1 - τt D x - ε)) • et D x
    simp only [add_smul, smul_smul]
    abel
  | arcST => exact absurd rfl hκ
  | arcTS => exact absurd rfl hκ'

theorem seg_subset_seg_orig (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)
    (hκ' : κ ≠ arcTS) : κ.seg ε ⊆ D.Γ.seg κ.orig := by
  rintro q ⟨θ, h0, h1, rfl⟩
  rw [tail_add_smul_dir ε κ hκ hκ' θ]
  refine ⟨κ.origParam ε θ, ?_, ?_, rfl⟩
  · cases κ with
    | old e => exact h0
    | cutStartS => exact mul_nonneg h0 (sub_pos.mpr hε.lt_τs).le
    | cutEndS =>
      have h2 := mul_nonneg h0 (sub_pos.mpr hε.lt_one_sub_τs).le
      show 0 ≤ τs D x + ε + θ * (1 - τs D x - ε)
      linarith [τs_pos D x, hε.pos]
    | cutStartT => exact mul_nonneg h0 (sub_pos.mpr hε.lt_τt).le
    | cutEndT =>
      have h2 := mul_nonneg h0 (sub_pos.mpr hε.lt_one_sub_τt).le
      show 0 ≤ τt D x + ε + θ * (1 - τt D x - ε)
      linarith [τt_pos D x, hε.pos]
    | arcST => exact absurd rfl hκ
    | arcTS => exact absurd rfl hκ'
  · cases κ with
    | old e => exact h1
    | cutStartS =>
      show θ * (τs D x - ε) ≤ 1
      have h2 := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τs).le h1
      linarith [τs_lt_one D x, hε.pos]
    | cutEndS =>
      show τs D x + ε + θ * (1 - τs D x - ε) ≤ 1
      have h2 := mul_le_of_le_one_left (sub_pos.mpr hε.lt_one_sub_τs).le h1
      linarith
    | cutStartT =>
      show θ * (τt D x - ε) ≤ 1
      have h2 := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τt).le h1
      linarith [τt_lt_one D x, hε.pos]
    | cutEndT =>
      show τt D x + ε + θ * (1 - τt D x - ε) ≤ 1
      have h2 := mul_le_of_le_one_left (sub_pos.mpr hε.lt_one_sub_τt).le h1
      linarith
    | arcST => exact absurd rfl hκ
    | arcTS => exact absurd rfl hκ'

theorem seg_old (ε : ℝ) (e : D.Γ.Strand) : (old e : StrandKind D x).seg ε = D.Γ.seg e := by
  rfl

theorem interior_old (ε : ℝ) (e : D.Γ.Strand) :
    (old e : StrandKind D x).interior ε = D.Γ.interior e := by
  rfl

/-- The arcs lie in the *closed* ball of radius `ε · max(‖es‖, ‖et‖)` about `p` (the provable
form of `seg_arc_subset_ball` below; see the note there). -/
theorem seg_arc_subset_closedBall (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x)
    (hκ : κ = arcST ∨ κ = arcTS) :
    κ.seg ε ⊆ Metric.closedBall (pt D x) (max (ε * ‖es D x‖) (ε * ‖et D x‖)) := by
  rintro q ⟨θ, h0, h1, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hε0 := hε.pos
  have h1' : 0 ≤ 1 - θ := sub_nonneg.mpr h1
  rcases hκ with rfl | rfl
  · have hq : (arcST : StrandKind D x).tail ε + θ • (arcST : StrandKind D x).dir ε - pt D x
        = ((θ - 1) * ε) • es D x + (θ * ε) • et D x := by
      simp only [tail, dir, sMinus, smul_add, smul_smul, sub_mul, one_mul, sub_smul]
      abel
    rw [hq]
    calc ‖((θ - 1) * ε) • es D x + (θ * ε) • et D x‖
        ≤ ‖((θ - 1) * ε) • es D x‖ + ‖(θ * ε) • et D x‖ := norm_add_le _ _
      _ = (1 - θ) * (ε * ‖es D x‖) + θ * (ε * ‖et D x‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_pos hε0, abs_of_nonneg h0, abs_sub_comm, abs_of_nonneg h1']
          ring
      _ ≤ (1 - θ) * max (ε * ‖es D x‖) (ε * ‖et D x‖) + θ * max (ε * ‖es D x‖) (ε * ‖et D x‖) :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h1')
            (mul_le_mul_of_nonneg_left (le_max_right _ _) h0)
      _ = max (ε * ‖es D x‖) (ε * ‖et D x‖) := by ring
  · have hq : (arcTS : StrandKind D x).tail ε + θ • (arcTS : StrandKind D x).dir ε - pt D x
        = (θ * ε) • es D x + ((θ - 1) * ε) • et D x := by
      simp only [tail, dir, tMinus, smul_add, smul_smul, sub_mul, one_mul, sub_smul]
      abel
    rw [hq]
    calc ‖(θ * ε) • es D x + ((θ - 1) * ε) • et D x‖
        ≤ ‖(θ * ε) • es D x‖ + ‖((θ - 1) * ε) • et D x‖ := norm_add_le _ _
      _ = θ * (ε * ‖es D x‖) + (1 - θ) * (ε * ‖et D x‖) := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
            abs_of_pos hε0, abs_of_nonneg h0, abs_sub_comm, abs_of_nonneg h1']
          ring
      _ ≤ θ * max (ε * ‖es D x‖) (ε * ‖et D x‖) + (1 - θ) * max (ε * ‖es D x‖) (ε * ‖et D x‖) :=
          add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0)
            (mul_le_mul_of_nonneg_left (le_max_right _ _) h1')
      _ = max (ε * ‖es D x‖) (ε * ‖et D x‖) := by ring

/-- The arcs lie in the open ball of radius `ε · max(‖es‖, ‖et‖) < r₁` about `p`.

**FALSE as stated (U1 prover, 2026-09-13; statement left unchanged per PLAN_FINAL §5 convention).**
The norm on `Plane = ℝ × ℝ` is the sup norm, and a convex combination can reach the maximum:
take `es = (1, 0)`, `et = (-1, 1/2)` (transverse, `det = 1/2`, `‖es‖ = ‖et‖ = 1`).  Then
`arcST` is the segment from `p - (ε, 0)` to `p + (-ε, ε/2)`, i.e. `q(θ) = p + (-ε, θ ε / 2)`, and
`dist (q θ) p = max ε (θ ε / 2) = ε = max (ε‖es‖) (ε‖et‖)` for every `θ ∈ [0,1]`: the whole arc
lies on the *sphere*, not in the open ball.  The provable form is `seg_arc_subset_closedBall`
above; downstream users should compose it with `closedBall p (max …) ⊆ ball p r`, which holds
because `arc_lt_discRadius` leaves strict room (`max … < discRadius`). -/
theorem seg_arc_subset_ball (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x)
    (hκ : κ = arcST ∨ κ = arcTS) :
    κ.seg ε ⊆ Metric.ball (pt D x) (max (ε * ‖es D x‖) (ε * ‖et D x‖)) := by
  sorry

/-- The cut points are inside the clearance ball, so the cut pieces reach the ball's boundary. -/
theorem dist_cut_lt (ε : ℝ) (hε : SmallEps D x ε) :
    dist (sMinus D x ε) (pt D x) < r₁ D x ∧ dist (sPlus D x ε) (pt D x) < r₁ D x ∧
      dist (tMinus D x ε) (pt D x) < r₁ D x ∧ dist (tPlus D x ε) (pt D x) < r₁ D x := by
  have hε0 := hε.pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [dist_sMinus, abs_of_pos hε0]; exact hε.mul_es_lt
  · rw [sPlus, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
    exact hε.mul_es_lt
  · rw [tMinus, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos hε0]
    exact hε.mul_et_lt
  · rw [tPlus, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε0]
    exact hε.mul_et_lt

end StrandKind

/-- **The abstract splice model.**  A shadow `Γ₀` together with a kind map on its strands that is a
bijection onto the occurring kinds and respects tails, directions and the cyclic predecessor.  All
geometric statements about the smoothing are proved for an arbitrary splice model; the concrete
shadows `mixedShadow` / `selfShadow` are shown to be models by index arithmetic. -/
structure SpliceModel (ε : ℝ) (Γ₀ : Shadow) where
  /-- the kind of every strand -/
  kind : Γ₀.Strand → StrandKind D x
  kind_injective : Function.Injective kind
  /-- every occurring kind is realised -/
  kind_surj : ∀ κ : StrandKind D x, κ.Occurs → ∃ u, kind u = κ
  /-- the erased strands do not occur -/
  kind_occurs : ∀ u, (kind u).Occurs
  /-- the predecessor law (encodes the reconnection and all adjacency) -/
  kind_pred : ∀ u : Γ₀.Strand, kind ⟨u.1, u.2 - 1⟩ = (kind u).pred
  tail_eq : ∀ u, Γ₀.tail u = (kind u).tail ε
  dir_eq : ∀ u, Γ₀.dir u = (kind u).dir ε
  /-- the no-wrap law: a cut-start piece, the arc after it and the cut-end piece after that occupy
  three consecutive labels `m, m+1, m+2` without passing label `0` (so the smoothing arcs of `D₀`
  need no wrap-around case, `traversalBetween_span_two`).  Not derivable from the other laws;
  trivial index arithmetic in both concrete models. -/
  cut_val : ∀ u : Γ₀.Strand, (kind u = StrandKind.cutStartS ∨ kind u = StrandKind.cutStartT) →
    u.2.val + 2 < (Γ₀.comp u.1).k

namespace SpliceModel

variable {D x ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)

/-- The strand of a given occurring kind. -/
def strandOf (κ : StrandKind D x) (hκ : κ.Occurs) : Γ₀.Strand :=
  Classical.choose (M.kind_surj κ hκ)

@[simp] theorem kind_strandOf (κ : StrandKind D x) (hκ : κ.Occurs) : M.kind (M.strandOf κ hκ) = κ :=
  Classical.choose_spec (M.kind_surj κ hκ)

theorem strandOf_kind (u : Γ₀.Strand) : M.strandOf (M.kind u) (M.kind_occurs u) = u :=
  M.kind_injective (M.kind_strandOf _ _)

/-- The original strand of `D` a strand of `Γ₀` is a piece of. -/
def orig (u : Γ₀.Strand) : D.Γ.Strand := (M.kind u).orig

theorem kind_succ (u : Γ₀.Strand) : M.kind ⟨u.1, u.2 + 1⟩ = (M.kind u).succ := by
  have h : M.kind ⟨u.1, u.2 + 1 - 1⟩ = (M.kind ⟨u.1, u.2 + 1⟩).pred := M.kind_pred ⟨u.1, u.2 + 1⟩
  rw [Γ₀.mk_add_one_sub_one] at h
  rw [h, StrandKind.succ_pred _ (M.kind_occurs _)]

theorem seg_eq (u : Γ₀.Strand) : Γ₀.seg u = (M.kind u).seg ε := by
  have h : ∀ t : ℝ, edgePoint (Γ₀.comp u.1).P u.2 t = (M.kind u).tail ε + t • (M.kind u).dir ε := by
    intro t
    rw [← M.tail_eq, ← M.dir_eq]
    rfl
  ext q
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, h t⟩
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, (h t).symm⟩

theorem interior_eq (u : Γ₀.Strand) : Γ₀.interior u = (M.kind u).interior ε := by
  have h : ∀ t : ℝ, edgePoint (Γ₀.comp u.1).P u.2 t = (M.kind u).tail ε + t • (M.kind u).dir ε := by
    intro t
    rw [← M.tail_eq, ← M.dir_eq]
    rfl
  ext q
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, h t⟩
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, (h t).symm⟩

theorem head_eq (u : Γ₀.Strand) : Γ₀.head u = (M.kind u).head ε := by
  rw [Γ₀.head_eq_tail_add_dir, M.tail_eq, M.dir_eq]
  rfl

/-- Adjacency in `Γ₀` is adjacency of kinds. -/
theorem adjacent_iff (u u' : Γ₀.Strand) : Γ₀.Adjacent u u' ↔ (M.kind u).Adj (M.kind u') := by
  constructor
  · rintro ⟨i, a, b, rfl, rfl, hab⟩
    rcases hab with h | h | h
    · have hb : b = a - 1 := by linear_combination h
      subst hb
      exact Or.inr (Or.inr (M.kind_pred ⟨i, a⟩))
    · rw [sub_eq_zero] at h
      subst h
      exact Or.inl rfl
    · have hb : b = a + 1 := by linear_combination h
      subst hb
      exact Or.inr (Or.inl (M.kind_succ ⟨i, a⟩))
  · rintro (h | h | h)
    · rw [M.kind_injective h]
      exact Shadow.Adjacent.refl Γ₀ u
    · rw [M.kind_injective (h.trans (M.kind_succ u).symm)]
      exact Γ₀.adjacent_mk_add_one u
    · rw [M.kind_injective (h.trans (M.kind_pred u).symm)]
      exact Γ₀.adjacent_mk_sub_one u

theorem incidentTail_iff (u u' : Γ₀.Strand) :
    Γ₀.IncidentTail u u' ↔ (M.kind u).Incident (M.kind u') := by
  constructor
  · rintro ⟨i, a, b, rfl, rfl, hab⟩
    rcases hab with rfl | rfl
    · exact Or.inr (M.kind_pred ⟨i, a⟩)
    · exact Or.inl rfl
  · rintro (h | h)
    · rw [M.kind_injective h]
      obtain ⟨i, a⟩ := u
      exact (Γ₀.incidentTail_mk_iff i a a).mpr (Or.inr rfl)
    · rw [M.kind_injective (h.trans (M.kind_pred u).symm)]
      obtain ⟨i, a⟩ := u
      exact (Γ₀.incidentTail_mk_iff i a (a - 1)).mpr (Or.inl rfl)

/-- Adjacency of old strands is inherited. -/
theorem adjacent_old_iff (e e' : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x)
    (he' : e' ≠ sS D x ∧ e' ≠ tS D x) :
    (StrandKind.old e : StrandKind D x).Adj (StrandKind.old e') ↔ D.Γ.Adjacent e e' := by
  constructor
  · rintro (h | h | h)
    · rw [StrandKind.old.inj h]
      exact Shadow.Adjacent.refl D.Γ e
    · -- `split_ifs` closes the two cut branches (`old e' = cutStartS/T` is a constructor clash)
      simp only [StrandKind.succ] at h
      split_ifs at h with h1 h2
      rw [StrandKind.old.inj h]
      exact D.Γ.adjacent_mk_add_one e
    · simp only [StrandKind.pred] at h
      split_ifs at h with h1 h2
      rw [StrandKind.old.inj h]
      exact D.Γ.adjacent_mk_sub_one e
  · rintro ⟨i, a, b, rfl, rfl, hab⟩
    rcases hab with h | h | h
    · have hb : b = a - 1 := by linear_combination h
      subst hb
      refine Or.inr (Or.inr ?_)
      have hA : (⟨i, a⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 + 1⟩ :=
        fun h' => he'.1 (D.Γ.mk_add_one_eq_iff.mp h'.symm).symm
      have hB : (⟨i, a⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ :=
        fun h' => he'.2 (D.Γ.mk_add_one_eq_iff.mp h'.symm).symm
      simp only [StrandKind.pred, hA, hB, ↓reduceIte]
    · rw [sub_eq_zero] at h
      subst h
      exact Or.inl rfl
    · have hb : b = a + 1 := by linear_combination h
      subst hb
      refine Or.inr (Or.inl ?_)
      have hA : (⟨i, a⟩ : D.Γ.Strand) ≠ ⟨(sS D x).1, (sS D x).2 - 1⟩ :=
        fun h' => he'.1 (D.Γ.mk_sub_one_eq_iff.mp h'.symm).symm
      have hB : (⟨i, a⟩ : D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 - 1⟩ :=
        fun h' => he'.2 (D.Γ.mk_sub_one_eq_iff.mp h'.symm).symm
      simp only [StrandKind.succ, hA, hB, ↓reduceIte]

/-- The evaluation of a traversal point of `Γ₀`, through its kind. -/
theorem eval_eq (q : Γ₀.Pt) :
    Γ₀.eval q = (M.kind ⟨q.1, q.2.1⟩).tail ε + q.2.2.val • (M.kind ⟨q.1, q.2.1⟩).dir ε := by
  rw [← M.tail_eq, ← M.dir_eq]
  rfl

end SpliceModel

/-! ## 5. The disc and the trace of `D` inside it

The disc is `U = closedBall p r` with `r = discRadius`, strictly between `ε · max(‖es‖,‖et‖)` (so
the cut points and both arcs are inside the open ball) and `r₁` (so no other strand, vertex or
crossing point of `D` meets the closed ball). -/

/-- The disc radius: the midpoint between the arc radius and the clearance radius. -/
def discRadius : ℝ := (max (ε * ‖es D x‖) (ε * ‖et D x‖) + r₁ D x) / 2

/-- The smoothing disc `U` (a closed ball of the sup metric of `ℝ × ℝ`, an axis-parallel square). -/
def disc : Set Plane := Metric.closedBall (pt D x) (discRadius D x ε)

theorem discRadius_pos (hε : SmallEps D x ε) : 0 < discRadius D x ε := by
  sorry

theorem discRadius_lt_r₁ (hε : SmallEps D x ε) : discRadius D x ε < r₁ D x := by
  sorry

theorem arc_lt_discRadius (hε : SmallEps D x ε) :
    max (ε * ‖es D x‖) (ε * ‖et D x‖) < discRadius D x ε := by
  sorry

theorem isDisc_disc (hε : SmallEps D x ε) : IsDisc (disc D x ε) :=
  isDisc_closedBall _ (discRadius_pos D x ε hε)

theorem interior_disc (hε : SmallEps D x ε) :
    interior (disc D x ε) = Metric.ball (pt D x) (discRadius D x ε) :=
  interior_closedBall _ (discRadius_pos D x ε hε).ne'

theorem frontier_disc (hε : SmallEps D x ε) :
    frontier (disc D x ε) = Metric.sphere (pt D x) (discRadius D x ε) :=
  frontier_closedBall _ (discRadius_pos D x ε hε).ne'

/-- The trace of `D` inside the closed disc lies on `s ∪ t`. -/
theorem mem_seg_of_mem_disc (hε : SmallEps D x ε) {e : D.Γ.Strand} {q : Plane} (hq : q ∈ D.Γ.seg e)
    (hU : q ∈ disc D x ε) : e = sS D x ∨ e = tS D x := by
  sorry

/-- No crossing point of `D` other than `p` lies in the closed disc. -/
theorem crossingPoint_ne_not_mem_disc (hε : SmallEps D x ε) {y : D.Γ.Crossing} (hy : y ≠ x) :
    D.Γ.crossingPoint y ∉ disc D x ε := by
  sorry

/-- No vertex of `D` lies in the closed disc. -/
theorem tail_not_mem_disc (hε : SmallEps D x ε) (e : D.Γ.Strand) : D.Γ.tail e ∉ disc D x ε := by
  sorry

/-- The frontier parameters of `s` and `t`: the entering and exiting parameters of the two strands
through the square `U` are `τ ∓ r/‖e‖`. -/
def θsIn : ℝ := τs D x - discRadius D x ε / ‖es D x‖
def θsOut : ℝ := τs D x + discRadius D x ε / ‖es D x‖
def θtIn : ℝ := τt D x - discRadius D x ε / ‖et D x‖
def θtOut : ℝ := τt D x + discRadius D x ε / ‖et D x‖

theorem θsIn_pos (hε : SmallEps D x ε) : 0 < θsIn D x ε := by
  sorry
theorem θsOut_lt_one (hε : SmallEps D x ε) : θsOut D x ε < 1 := by
  sorry
theorem θtIn_pos (hε : SmallEps D x ε) : 0 < θtIn D x ε := by
  sorry
theorem θtOut_lt_one (hε : SmallEps D x ε) : θtOut D x ε < 1 := by
  sorry
theorem θsIn_lt_θsOut (hε : SmallEps D x ε) : θsIn D x ε < θsOut D x ε := by
  sorry
theorem θtIn_lt_θtOut (hε : SmallEps D x ε) : θtIn D x ε < θtOut D x ε := by
  sorry

/-- The cut parameters lie strictly inside the frontier parameters:
`θsIn < τs − ε < τs + ε < θsOut` (the cut points are inside the open disc). -/
theorem θsIn_lt_cut (hε : SmallEps D x ε) : θsIn D x ε < τs D x - ε ∧ τs D x + ε < θsOut D x ε := by
  sorry
theorem θtIn_lt_cut (hε : SmallEps D x ε) : θtIn D x ε < τt D x - ε ∧ τt D x + ε < θtOut D x ε := by
  sorry

/-- A point of `s` is in the closed (open) disc iff its parameter lies in `[θsIn, θsOut]`
(`(θsIn, θsOut)`). -/
theorem edgePoint_s_mem_disc_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 θ ∈ disc D x ε ↔
      θsIn D x ε ≤ θ ∧ θ ≤ θsOut D x ε := by
  sorry

theorem edgePoint_s_mem_ball_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 θ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔
      θsIn D x ε < θ ∧ θ < θsOut D x ε := by
  sorry

theorem edgePoint_t_mem_disc_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 θ ∈ disc D x ε ↔
      θtIn D x ε ≤ θ ∧ θ ≤ θtOut D x ε := by
  sorry

theorem edgePoint_t_mem_ball_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 θ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔
      θtIn D x ε < θ ∧ θ < θtOut D x ε := by
  sorry

/-- The frontier parameters on the cut pieces of `Γ₀` (rescaled frontier parameters of `D`). -/
def θ₀sIn : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutStartS (θsIn D x ε)
def θ₀sOut : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutEndS (θsOut D x ε)
def θ₀tIn : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutStartT (θtIn D x ε)
def θ₀tOut : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutEndT (θtOut D x ε)

theorem θ₀_mem (hε : SmallEps D x ε) : θ₀sIn D x ε ∈ Set.Ico (0:ℝ) 1 ∧ θ₀sOut D x ε ∈ Set.Ico (0:ℝ) 1 ∧
    θ₀tIn D x ε ∈ Set.Ico (0:ℝ) 1 ∧ θ₀tOut D x ε ∈ Set.Ico (0:ℝ) 1 := by
  sorry

/-- Traversal betweenness on one edge: the points strictly between two points of the same edge in
the cyclic order are the points of that edge with parameter strictly between (accepted
`traversalBetween`, key form). -/
theorem traversalBetween_same_edge {n : ℕ} [NeZero n] (a : ZMod n) (θ₁ θ₂ : Set.Ico (0:ℝ) 1)
    (h : θ₁.val < θ₂.val) (r : TraversalPoint n) :
    traversalBetween (a, θ₁) r (a, θ₂) ↔ r.1 = a ∧ θ₁.val < r.2.val ∧ r.2.val < θ₂.val := by
  sorry

/-- Traversal betweenness across two consecutive edges `m`, `m+2` (used for the smoothing arcs of
`D₀`: start on the cut piece, through the arc, stop on the next cut piece; no wrap). -/
theorem traversalBetween_span_two {n : ℕ} [NeZero n] (m : ZMod n) (hm : m.val + 2 < n)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint n) :
    traversalBetween (m, θ₁) r (m + 2, θ₂) ↔
      (r.1 = m ∧ θ₁.val < r.2.val) ∨ r.1 = m + 1 ∨ (r.1 = m + 2 ∧ r.2.val < θ₂.val) := by
  sorry

section DiscD

variable {ε} (hε : SmallEps D x ε)
include hε

theorem clean_D : Clean (disc D x ε) D := by
  sorry

theorem center_mem : pt D x ∈ interior (disc D x ε) := by
  sorry

/-- The arc of `D` through the over occurrence: on `s`, from parameter `θsIn` to `θsOut`. -/
def arcS : D.Γ.Arc :=
  ⟨(sS D x).1,
    ((sS D x).2, ⟨θsIn D x ε, (θsIn_pos D x ε hε).le,
      (θsIn_lt_θsOut D x ε hε).trans (θsOut_lt_one D x ε hε)⟩),
    ((sS D x).2, ⟨θsOut D x ε, ((θsIn_pos D x ε hε).trans (θsIn_lt_θsOut D x ε hε)).le,
      θsOut_lt_one D x ε hε⟩)⟩

/-- The arc of `D` through the under occurrence: on `t`, from `θtIn` to `θtOut`. -/
def arcT : D.Γ.Arc :=
  ⟨(tS D x).1,
    ((tS D x).2, ⟨θtIn D x ε, (θtIn_pos D x ε hε).le,
      (θtIn_lt_θtOut D x ε hε).trans (θtOut_lt_one D x ε hε)⟩),
    ((tS D x).2, ⟨θtOut D x ε, ((θtIn_pos D x ε hε).trans (θtIn_lt_θtOut D x ε hε)).le,
      θtOut_lt_one D x ε hε⟩)⟩

theorem arcS_ne_arcT : arcS D x hε ≠ arcT D x hε := by
  sorry

theorem arcCover_D : D.Γ.ArcCover (disc D x ε) {arcS D x hε, arcT D x hε} := by
  sorry

theorem overOn_arcS : D.OverOn (arcS D x hε) x := by
  sorry

theorem underOn_arcT : D.UnderOn (arcT D x hε) x := by
  sorry

theorem inner_iff_D (y : D.Γ.Crossing) : D.Γ.crossingPoint y ∈ interior (disc D x ε) ↔ y = x := by
  sorry

end DiscD

/-! ## 6. Model-level geometry

Everything in this section is stated for an arbitrary splice model `M : SpliceModel D x ε Γ₀` with
`hε : SmallEps D x ε`. -/

section Model

variable {ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
include M hε

/-! ### 6a. Genericity of the spliced shadow -/

omit M in
/-- Non-adjacent kinds that are not both old have disjoint segments, except an old strand meeting a
cut piece at a crossing of `D` (cut pieces of one strand are disjoint; cut pieces of `s` and `t`
are disjoint since their only common point `p` is cut away; arcs are disjoint from each other and
from the cut pieces they are not adjacent to, by independence of `es`, `et`; arcs are disjoint from
old strands by the clearance radius). -/
theorem kind_disjoint (κ κ' : StrandKind D x) (hκ : ¬ ∃ e, κ = StrandKind.old e)
    (hadj : ¬ κ.Adj κ') (hold : ∀ e, κ' = StrandKind.old e → False) :
    Disjoint (κ.seg ε) (κ'.seg ε) := by
  sorry

omit M in
/-- A cut piece meets an old strand `e ≠ s, t` only if `e` is non-adjacent to the original strand
(so the meeting is a crossing of `D`); adjacent old strands `s ∓ 1` meet only the piece they touch,
at the common vertex. -/
theorem cut_inter_old (κ : StrandKind D x) (hκ : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS)
    (hκo : ¬ ∃ e, κ = StrandKind.old e) (e : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x)
    (hmeet : (κ.seg ε ∩ D.Γ.seg e).Nonempty) (hadj : ¬ κ.Adj (StrandKind.old e)) :
    ¬ D.Γ.Adjacent κ.orig e := by
  sorry

/-- Every component of `Γ₀` is a regular polygon: old corners are inherited, the corners at the
cut points are positively collinear, the corners at the arc ends are transverse
(`det es et ≠ 0`). -/
theorem regular (i : Fin Γ₀.c) : Regular (Γ₀.comp i).P := by
  sorry

theorem tail_off (u u' : Γ₀.Strand) (h : ¬ Γ₀.IncidentTail u u') : Γ₀.tail u ∉ Γ₀.seg u' := by
  sorry

theorem transverse (u u' : Γ₀.Strand) (h : ¬ Γ₀.Adjacent u u')
    (hmeet : (Γ₀.seg u ∩ Γ₀.seg u').Nonempty) : det (Γ₀.dir u) (Γ₀.dir u') ≠ 0 := by
  sorry

theorem no_triple : ¬ ∃ u u' u'' : Γ₀.Strand, u ≠ u' ∧ u' ≠ u'' ∧ u ≠ u'' ∧
    (Γ₀.interior u ∩ Γ₀.interior u' ∩ Γ₀.interior u'').Nonempty := by
  sorry

/-- **Genericity of the spliced shadow.** -/
theorem generic : Γ₀.Generic where
  regular := regular D x M hε
  tail_off := tail_off D x M hε
  transverse := transverse D x M hε
  no_triple := no_triple D x M hε

/-! ### 6b. Crossings of the spliced shadow -/

/-- A crossing of `Γ₀` consists of two strands whose original strands form a crossing of `D`
other than `x` (cut pieces meet nothing but old strands; arcs meet nothing). -/
theorem isCrossing_orig {u u' : Γ₀.Strand} (h : Γ₀.IsCrossing {u, u'}) :
    D.Γ.IsCrossing {M.orig u, M.orig u'} ∧ ({M.orig u, M.orig u'} : Finset D.Γ.Strand) ≠ x.val := by
  sorry

/-- The crossing of `D` under a crossing of `Γ₀`. -/
def origCrossing (y : Γ₀.Crossing) : D.Γ.Crossing :=
  ⟨{M.orig y.fst, M.orig y.snd}, (isCrossing_orig D x M hε (y.val_eq ▸ y.2)).1⟩

theorem origCrossing_ne (y : Γ₀.Crossing) : origCrossing D x M hε y ≠ x := by
  sorry

theorem orig_mem_origCrossing {y : Γ₀.Crossing} {u : Γ₀.Strand} (hu : u ∈ y.val) :
    M.orig u ∈ (origCrossing D x M hε y).val := by
  sorry

theorem origCrossing_injective : Function.Injective (origCrossing D x M hε) := by
  sorry

/-- The crossing point of `Γ₀` at `y` is the crossing point of `D` at `origCrossing y`. -/
theorem crossingPoint_origCrossing (y : Γ₀.Crossing) :
    Γ₀.crossingPoint y = D.Γ.crossingPoint (origCrossing D x M hε y) := by
  sorry

omit hε in
/-- The strand of `Γ₀` carrying the passage of the strand `e ∈ y` of `D` through the crossing
`y ≠ x`: the old strand, or the cut piece of `s` (`t`) containing the crossing point. -/
def liftStrand (y : D.Γ.Crossing) (e : D.Γ.Strand) (he : e ∈ y.val) : Γ₀.Strand :=
  if hs : e = sS D x then
    (if D.crossingParam y he < τs D x then M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS
     else M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS)
  else if ht : e = tS D x then
    (if D.crossingParam y he < τt D x then M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT
     else M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT)
  else M.strandOf (StrandKind.old e) (StrandKind.occurs_old hs ht)

omit hε in
theorem orig_liftStrand (y : D.Γ.Crossing) (e : D.Γ.Strand) (he : e ∈ y.val) :
    M.orig (liftStrand D x M y e he) = e := by
  sorry

/-- Every crossing of `D` other than `x` lifts to a crossing of `Γ₀`. -/
theorem isCrossing_lift {y : D.Γ.Crossing} (hy : y ≠ x) :
    Γ₀.IsCrossing {liftStrand D x M y y.fst y.fst_mem, liftStrand D x M y y.snd y.snd_mem} := by
  sorry

/-- The lift of a crossing `y ≠ x`. -/
def liftCrossing (y : D.Γ.Crossing) (hy : y ≠ x) : Γ₀.Crossing :=
  ⟨_, isCrossing_lift D x M hε hy⟩

theorem origCrossing_liftCrossing (y : D.Γ.Crossing) (hy : y ≠ x) :
    origCrossing D x M hε (liftCrossing D x M hε y hy) = y := by
  sorry

theorem liftCrossing_origCrossing (y : Γ₀.Crossing) :
    liftCrossing D x M hε (origCrossing D x M hε y) (origCrossing_ne D x M hε y) = y := by
  sorry

/-- The crossings of `Γ₀` are the crossings of `D` other than `x`. -/
def crossingEquiv : Γ₀.Crossing ≃ {y : D.Γ.Crossing // y ≠ x} where
  toFun y := ⟨origCrossing D x M hε y, origCrossing_ne D x M hε y⟩
  invFun y := liftCrossing D x M hε y.1 y.2
  left_inv y := liftCrossing_origCrossing D x M hε y
  right_inv y := Subtype.ext (origCrossing_liftCrossing D x M hε y.1 y.2)

/-- The strands of a crossing of `Γ₀` lie over distinct strands of the original crossing. -/
theorem orig_injOn_crossing (y : Γ₀.Crossing) {u u' : Γ₀.Strand} (hu : u ∈ y.val) (hu' : u' ∈ y.val)
    (h : M.orig u = M.orig u') : u = u' := by
  sorry

/-! ### 6c. The smoothed diagram: over data pulled back through `orig` -/

/-- The over strand of the smoothed diagram at `y`: the strand of `y` lying over the over strand of
`D` at the original crossing. -/
def overStrand₀ (y : Γ₀.Crossing) : Γ₀.Strand :=
  if M.orig y.fst = D.overStrand (origCrossing D x M hε y) then y.fst else y.snd

theorem overStrand₀_mem (y : Γ₀.Crossing) : overStrand₀ D x M hε y ∈ y.val := by
  unfold overStrand₀
  split_ifs
  · exact y.fst_mem
  · exact y.snd_mem

theorem orig_overStrand₀ (y : Γ₀.Crossing) :
    M.orig (overStrand₀ D x M hε y) = D.overStrand (origCrossing D x M hε y) := by
  sorry

/-- **The smoothed diagram** on a splice model. -/
def toDiagram : Diagram where
  Γ := Γ₀
  generic := generic D x M hε
  overStrand := overStrand₀ D x M hε
  over_mem := overStrand₀_mem D x M hε

@[simp] theorem toDiagram_Γ : (toDiagram D x M hε).Γ = Γ₀ := rfl

theorem toDiagram_underStrand_orig (y : Γ₀.Crossing) :
    M.orig ((toDiagram D x M hε).underStrand y) = D.underStrand (origCrossing D x M hε y) := by
  sorry

/-- Signs are inherited (directions of cut pieces are positive multiples of the originals). -/
theorem toDiagram_sign (y : Γ₀.Crossing) :
    (toDiagram D x M hε).sign y = D.sign (origCrossing D x M hε y) := by
  sorry

/-- The crossing parameter of a strand of `Γ₀` through `y` is the rescaled parameter of `D`. -/
theorem crossingParam_toDiagram (y : Γ₀.Crossing) {u : Γ₀.Strand} (hu : u ∈ y.val) :
    (toDiagram D x M hε).crossingParam y hu =
      (M.kind u).liftParam ε (D.crossingParam (origCrossing D x M hε y)
        (orig_mem_origCrossing D x M hε hu)) := by
  sorry

/-! ### 6d. Cleanness of `D₀` and its two arcs inside the disc -/

/-- No crossing point of `Γ₀` lies in the closed disc. -/
theorem crossingPoint_not_mem_disc (y : Γ₀.Crossing) : Γ₀.crossingPoint y ∉ disc D x ε := by
  rw [crossingPoint_origCrossing D x M hε y]
  exact crossingPoint_ne_not_mem_disc D x ε hε (origCrossing_ne D x M hε y)

theorem no_inner_toDiagram (y : Γ₀.Crossing) : Γ₀.crossingPoint y ∉ interior (disc D x ε) :=
  fun h => crossingPoint_not_mem_disc D x M hε y (interior_subset h)

theorem clean_toDiagram : Clean (disc D x ε) (toDiagram D x M hε) := by
  sorry

theorem localFrame : LocalFrame (disc D x ε) D (toDiagram D x M hε) where
  disc := isDisc_disc D x ε hε
  clean := clean_D D x hε
  clean' := clean_toDiagram D x M hε

/-- The smoothing arc `a₀` of `D₀`: from the frontier point on `[tail s, s⁻]`, along `s⁻ → t⁺`, to
the frontier point on `[t⁺, head t]` (two strands later on the same component). -/
def arcST₀ : Γ₀.Arc :=
  ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
    ((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2, ⟨θ₀sIn D x ε, (θ₀_mem D x ε hε).1⟩),
    ((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2, ⟨θ₀tOut D x ε, (θ₀_mem D x ε hε).2.2.2⟩)⟩

/-- The smoothing arc `b₀` of `D₀`: from the frontier point on `[tail t, t⁻]`, along `t⁻ → s⁺`, to
the frontier point on `[s⁺, head s]`. -/
def arcTS₀ : Γ₀.Arc :=
  ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
    ((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2, ⟨θ₀tIn D x ε, (θ₀_mem D x ε hε).2.2.1⟩),
    ((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2, ⟨θ₀sOut D x ε, (θ₀_mem D x ε hε).2.1⟩)⟩

omit hε in
/-- The strand two steps after `cutStartS` is `cutEndT` (through `arcST`), on the same component
(from `kind_pred`/`kind_succ`). -/
theorem strandOf_cutEndT_eq :
    M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT =
      ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
        (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ := by
  sorry

omit hε in
theorem strandOf_cutEndS_eq :
    M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS =
      ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ := by
  sorry

omit hε in
/-- The no-wrap law at the two cut-start strands (feeds `traversalBetween_span_two`). -/
theorem strandOf_cutStartS_val :
    (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2.val + 2 <
      (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k :=
  M.cut_val _ (Or.inl (M.kind_strandOf _ _))

omit hε in
theorem strandOf_cutStartT_val :
    (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2.val + 2 <
      (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k :=
  M.cut_val _ (Or.inr (M.kind_strandOf _ _))

theorem arcST₀_ne_arcTS₀ : arcST₀ D x M hε ≠ arcTS₀ D x M hε := by
  sorry

theorem arcCover_toDiagram : Γ₀.ArcCover (disc D x ε) {arcST₀ D x M hε, arcTS₀ D x M hε} := by
  sorry

theorem arcST₀_start : Γ₀.eval (arcST₀ D x M hε).startPt = D.Γ.eval (arcS D x hε).startPt := by
  sorry
theorem arcST₀_stop : Γ₀.eval (arcST₀ D x M hε).stopPt = D.Γ.eval (arcT D x hε).stopPt := by
  sorry
theorem arcTS₀_start : Γ₀.eval (arcTS₀ D x M hε).startPt = D.Γ.eval (arcT D x hε).startPt := by
  sorry
theorem arcTS₀_stop : Γ₀.eval (arcTS₀ D x M hε).stopPt = D.Γ.eval (arcS D x hε).stopPt := by
  sorry

/-! ### 6e. The outside match -/

omit hε in
/-- The traversal point of `D` under a traversal point of `Γ₀`: the original strand at the
rescaled parameter (clamped into `[0,1)`; the clamp only acts on the arcs, which never occur
outside the disc). -/
def origPt (q : Γ₀.Pt) : D.Γ.Pt :=
  ⟨(M.orig ⟨q.1, q.2.1⟩).1, ((M.orig ⟨q.1, q.2.1⟩).2,
    clampIco ((M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val))⟩

omit hε in
theorem origPt_fst (q : Γ₀.Pt) : (origPt D x M q).1 = (M.orig ⟨q.1, q.2.1⟩).1 := rfl

omit hε in
theorem origPt_edge (q : Γ₀.Pt) : (origPt D x M q).2.1 = (M.orig ⟨q.1, q.2.1⟩).2 := rfl

/-- The rescaled parameter of a non-arc kind lies in `[0,1)` (so the clamp is inactive); arcs have
the constant parameter `τ ∈ (0,1)`. -/
theorem origParam_mem (κ : StrandKind D x) (θ : Set.Ico (0:ℝ) 1) :
    κ.origParam ε θ.val ∈ Set.Ico (0:ℝ) 1 := by
  sorry

theorem origPt_param (q : Γ₀.Pt) :
    (origPt D x M q).2.2.val = (M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val :=
  clampIco_val_of_mem (origParam_mem D x M hε _ _)

/-- Outside the open disc, `origPt` traces the same point. -/
theorem eval_origPt (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    D.Γ.eval (origPt D x M q) = Γ₀.eval q := by
  sorry

theorem origPt_outside (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    D.Γ.eval (origPt D x M q) ∉ interior (disc D x ε) := by
  rw [eval_origPt D x M hε q hq]; exact hq

/-- `origPt` is a bijection from the outside traversal points of `Γ₀` onto those of `D`. -/
theorem origPt_bijective :
    Function.Bijective (fun q : Γ₀.Outside (disc D x ε) =>
      (⟨origPt D x M q.1, origPt_outside D x M hε q.1 q.2⟩ : D.Γ.Outside (disc D x ε))) := by
  sorry

/-- The outside correspondence `φ`. -/
def outsideEquiv : D.Γ.Outside (disc D x ε) ≃ Γ₀.Outside (disc D x ε) :=
  (Equiv.ofBijective _ (origPt_bijective D x M hε)).symm

theorem outsideEquiv_eval (q : D.Γ.Outside (disc D x ε)) :
    Γ₀.eval (outsideEquiv D x M hε q).1 = D.Γ.eval q.1 := by
  sorry

theorem outsideEquiv_dir_pos (q : D.Γ.Outside (disc D x ε)) (hq : D.Γ.eval q.1 ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧
      Γ₀.dir (Γ₀.strandOf (outsideEquiv D x M hε q).1) = l • D.Γ.dir (D.Γ.strandOf q.1) := by
  sorry

theorem outsideEquiv_dir_pos_before (q : D.Γ.Outside (disc D x ε))
    (hq : D.Γ.eval q.1 ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧ Γ₀.dir (Γ₀.strandBefore (outsideEquiv D x M hε q).1) =
      l • D.Γ.dir (D.Γ.strandBefore q.1) := by
  sorry

/-- The outer crossings of `D` are the crossings other than `x`; all crossings of `D₀` are outer. -/
def outerEquiv : D.OuterCrossing (disc D x ε) ≃ (toDiagram D x M hε).OuterCrossing (disc D x ε) :=
  ((Equiv.subtypeEquivRight (fun y => by
      show D.Γ.crossingPoint y ∉ interior (disc D x ε) ↔ y ≠ x
      rw [inner_iff_D D x hε])).trans (crossingEquiv D x M hε).symm).trans
    (Equiv.subtypeUnivEquiv (no_inner_toDiagram D x M hε)).symm

theorem outsideEquiv_outerOverPt (y : D.OuterCrossing (disc D x ε)) :
    outsideEquiv D x M hε (D.outerOverPt y) =
      (toDiagram D x M hε).outerOverPt (outerEquiv D x M hε y) := by
  sorry

theorem outsideEquiv_outerUnderPt (y : D.OuterCrossing (disc D x ε)) :
    outsideEquiv D x M hε (D.outerUnderPt y) =
      (toDiagram D x M hε).outerUnderPt (outerEquiv D x M hε y) := by
  sorry

/-- The outside match of `D` and its smoothing. -/
def outsideMatch : OutsideMatch (disc D x ε) D (toDiagram D x M hε) where
  φ := outsideEquiv D x M hε
  eval_eq := outsideEquiv_eval D x M hε
  dir_pos := outsideEquiv_dir_pos D x M hε
  dir_pos_before := outsideEquiv_dir_pos_before D x M hε
  ψ := outerEquiv D x M hε
  over_eq := outsideEquiv_outerOverPt D x M hε
  under_eq := outsideEquiv_outerUnderPt D x M hε

/-! ### 6f. The smoothing data -/

/-- **The oriented smoothing data** of a splice model. -/
def orientedSmoothingData : OrientedSmoothingData (disc D x ε) D x (toDiagram D x M hε) where
  frame := localFrame D x M hε
  center := center_mem D x hε
  out := outsideMatch D x M hε
  a := arcS D x hε
  b := arcT D x hε
  ab := arcS_ne_arcT D x hε
  cover := arcCover_D D x hε
  over_on_a := overOn_arcS D x hε
  under_on_b := underOn_arcT D x hε
  inner_iff := inner_iff_D D x hε
  a₀ := arcST₀ D x M hε
  b₀ := arcTS₀ D x M hε
  ab₀ := arcST₀_ne_arcTS₀ D x M hε
  cover₀ := arcCover_toDiagram D x M hε
  no_inner₀ := no_inner_toDiagram D x M hε
  a₀_start := arcST₀_start D x M hε
  a₀_stop := arcST₀_stop D x M hε
  b₀_start := arcTS₀_start D x M hε
  b₀_stop := arcTS₀_stop D x M hε

theorem isOrientedSmoothing_toDiagram : IsOrientedSmoothing D x (toDiagram D x M hε) :=
  ⟨disc D x ε, ⟨orientedSmoothingData D x M hε⟩⟩

end Model

/-! ## 7. The concrete shadows

Both shadows list the new component(s) first (index `0`, and `1` in the self case, via
`Fin.cases`, which reduces definitionally on `0` and `Fin.succ`), then the untouched components of
`D` in increasing order (`Finset.orderEmbOfFin`).  Vertex tuples are given by `ZMod.val` case
analysis; old vertices are addressed as `P (a + 1 + m)` so that no cast between `ZMod` sizes is
needed. -/

/-- `k_i`, the vertex count of the component of `s`. -/
abbrev kI : ℕ := (D.Γ.comp (sS D x).1).k
/-- `k_j`, the vertex count of the component of `t`. -/
abbrev kJ : ℕ := (D.Γ.comp (tS D x).1).k
/-- The vertex tuple of the component of `s`. -/
abbrev Pi : LabelledTuple (kI D x) := (D.Γ.comp (sS D x).1).P
/-- The vertex tuple of the component of `t`. -/
abbrev Pj : LabelledTuple (kJ D x) := (D.Γ.comp (tS D x).1).P
/-- The edge label `a` of `s`. -/
abbrev aS : ZMod (kI D x) := (sS D x).2
/-- The edge label `b` of `t`. -/
abbrev bT : ZMod (kJ D x) := (tS D x).2

/-! ### 7a. The mixed case: `i ≠ j`, two components joined into one

Vertices of the merged component, `N = k_i + k_j + 4`:
`Q m = P_i (a+1+m)` for `m < k_i` (so `Q (k_i−1) = P_i a`), `Q k_i = s⁻`, `Q (k_i+1) = t⁺`,
`Q (k_i+2+m) = P_j (b+1+m)` for `m < k_j` (so `Q (k_i+1+k_j) = P_j b`), `Q (k_i+2+k_j) = t⁻`,
`Q (k_i+3+k_j) = s⁺`, and `Q N = Q 0 = P_i (a+1)`.
Edges: `0 … k_i−2` old `⟨i, a+1+m⟩`; `k_i−1` = `[P_i a, s⁻]` (cutStartS); `k_i` = arcST;
`k_i+1` = `[t⁺, P_j (b+1)]` (cutEndT); `k_i+2 … k_i+k_j` old `⟨j, b+1+m⟩`; `k_i+1+k_j` = cutStartT;
`k_i+2+k_j` = arcTS; `k_i+3+k_j` = `[s⁺, P_i (a+1)]` (cutEndS). -/

/-- The vertex tuple of the merged component. -/
def mergedTuple : LabelledTuple (kI D x + kJ D x + 4) := fun m =>
  if m.val < kI D x then Pi D x (aS D x + 1 + (m.val : ZMod (kI D x)))
  else if m.val = kI D x then sMinus D x ε
  else if m.val = kI D x + 1 then tPlus D x ε
  else if m.val < kI D x + 2 + kJ D x then
    Pj D x (bT D x + 1 + ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x)))
  else if m.val = kI D x + 2 + kJ D x then tMinus D x ε
  else sPlus D x ε

/-- The merged component (`k_i + k_j + 4 ≥ 10` vertices). -/
def mergedComp : PolyComp := ⟨kI D x + kJ D x + 4, by omega, mergedTuple D x ε⟩

/-- The components of `D` other than those of `s` and `t`. -/
def othersM : Finset (Fin D.Γ.c) := (Finset.univ.erase (sS D x).1).erase (tS D x).1

theorem card_othersM (h : (sS D x).1 ≠ (tS D x).1) : (othersM D x).card + 2 = D.Γ.c := by
  sorry

/-- The mixed smoothed shadow: the merged component first, then the untouched components. -/
def mixedShadow : Shadow where
  c := (othersM D x).card + 1
  hc := Nat.succ_pos _
  comp := Fin.cases (mergedComp D x ε) (fun l => D.Γ.comp ((othersM D x).orderEmbOfFin rfl l))

@[simp] theorem mixedShadow_comp_zero :
    (mixedShadow D x ε).comp (0 : Fin ((othersM D x).card + 1)) = mergedComp D x ε := rfl

@[simp] theorem mixedShadow_comp_succ (l : Fin (othersM D x).card) :
    (mixedShadow D x ε).comp l.succ = D.Γ.comp ((othersM D x).orderEmbOfFin rfl l) := rfl

/-- The kind of the edge with index `m` (as a natural number) of the merged component. -/
def mergedKindIdx (m : ℕ) : StrandKind D x :=
  if m < kI D x - 1 then StrandKind.old ⟨(sS D x).1, aS D x + 1 + (m : ZMod (kI D x))⟩
  else if m = kI D x - 1 then StrandKind.cutStartS
  else if m = kI D x then StrandKind.arcST
  else if m = kI D x + 1 then StrandKind.cutEndT
  else if m < kI D x + 1 + kJ D x then
    StrandKind.old ⟨(tS D x).1, bT D x + 1 + ((m - (kI D x + 2) : ℕ) : ZMod (kJ D x))⟩
  else if m = kI D x + 1 + kJ D x then StrandKind.cutStartT
  else if m = kI D x + 2 + kJ D x then StrandKind.arcTS
  else StrandKind.cutEndS

/-- The kind map of the mixed shadow. -/
def mixedKind (u : (mixedShadow D x ε).Strand) : StrandKind D x :=
  Fin.cases (motive := fun l => ZMod ((mixedShadow D x ε).comp l).k → StrandKind D x)
    (fun m => mergedKindIdx D x m.val)
    (fun l m => StrandKind.old ⟨(othersM D x).orderEmbOfFin rfl l, (m.val : ZMod _)⟩) u.1 u.2

/-- The mixed shadow is a splice model (index arithmetic on `ZMod.val`). -/
def mixedModel (h : (sS D x).1 ≠ (tS D x).1) : SpliceModel D x ε (mixedShadow D x ε) where
  kind := mixedKind D x ε
  kind_injective := by
    sorry
  kind_surj := by
    sorry
  kind_occurs := by
    sorry
  kind_pred := by
    sorry
  tail_eq := by
    sorry
  dir_eq := by
    sorry
  cut_val := by
    sorry

/-! ### 7b. The self case: `i = j`, one component split into two

With `d = (b − a).val ∈ [2, k−2]` (non-adjacency), component `A` (`d + 2` vertices):
`Q_A m = P (a+1+m)` for `m < d` (so `Q_A (d−1) = P b`), `Q_A d = t⁻`, `Q_A (d+1) = s⁺`; edges
`0 … d−2` old `⟨i, a+1+m⟩`, `d−1` cutStartT, `d` arcTS, `d+1` cutEndS.  Component `B`
(`k − d + 2` vertices): `Q_B m = P (b+1+m)` for `m < k−d` (so `Q_B (k−d−1) = P a`),
`Q_B (k−d) = s⁻`, `Q_B (k−d+1) = t⁺`; edges `0 … k−d−2` old `⟨i, b+1+m⟩`, `k−d−1` cutStartS,
`k−d` arcST, `k−d+1` cutEndT.  `A` carries the occurrences met after `x` and before `τx`, `B` the
others (`A ↦ ⟦τx⟧`, `B ↦ ⟦x⟧` in `Record.SmoothComps`). -/

/-- The edge label of `t` transported to the component of `s` (by its value; meaningful when
`i = j`). -/
abbrev bS : ZMod (kI D x) := ((tS D x).2.val : ZMod (kI D x))

/-- `d = (b − a).val`: the number of edges from `a` to `b` going forward. -/
def dd : ℕ := (bS D x - aS D x).val

theorem two_le_dd (h : (sS D x).1 = (tS D x).1) : 2 ≤ dd D x := by
  sorry

theorem dd_add_two_le (h : (sS D x).1 = (tS D x).1) : dd D x + 2 ≤ kI D x := by
  sorry

/-- The vertex tuple of component `A`. -/
def tupleA : LabelledTuple (dd D x + 2) := fun m =>
  if m.val < dd D x then Pi D x (aS D x + 1 + (m.val : ZMod (kI D x)))
  else if m.val = dd D x then tMinus D x ε
  else sPlus D x ε

/-- The vertex tuple of component `B`. -/
def tupleB : LabelledTuple (kI D x - dd D x + 2) := fun m =>
  if m.val < kI D x - dd D x then Pi D x (bS D x + 1 + (m.val : ZMod (kI D x)))
  else if m.val = kI D x - dd D x then sMinus D x ε
  else tPlus D x ε

def compA (h : (sS D x).1 = (tS D x).1) : PolyComp :=
  ⟨dd D x + 2, by have := two_le_dd D x h; omega, tupleA D x ε⟩

def compB (h : (sS D x).1 = (tS D x).1) : PolyComp :=
  ⟨kI D x - dd D x + 2, by have := dd_add_two_le D x h; omega, tupleB D x ε⟩

/-- The components of `D` other than that of `s` (`= t`). -/
def othersS : Finset (Fin D.Γ.c) := Finset.univ.erase (sS D x).1

theorem card_othersS : (othersS D x).card + 1 = D.Γ.c := by
  sorry

/-- The self smoothed shadow: `A`, then `B`, then the untouched components. -/
def selfShadow (h : (sS D x).1 = (tS D x).1) : Shadow where
  c := (othersS D x).card + 2
  hc := by omega
  comp := Fin.cases (compA D x ε h)
    (Fin.cases (compB D x ε h) (fun l => D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)))

@[simp] theorem selfShadow_comp_zero (h : (sS D x).1 = (tS D x).1) :
    (selfShadow D x ε h).comp (0 : Fin ((othersS D x).card + 2)) = compA D x ε h := rfl

@[simp] theorem selfShadow_comp_one (h : (sS D x).1 = (tS D x).1) :
    (selfShadow D x ε h).comp (1 : Fin ((othersS D x).card + 2)) = compB D x ε h := rfl

@[simp] theorem selfShadow_comp_succ_succ (h : (sS D x).1 = (tS D x).1) (l : Fin (othersS D x).card) :
    (selfShadow D x ε h).comp l.succ.succ = D.Γ.comp ((othersS D x).orderEmbOfFin rfl l) := rfl

/-- The kind of the edge with index `m` of component `A`. -/
def kindIdxA (m : ℕ) : StrandKind D x :=
  if m < dd D x - 1 then StrandKind.old ⟨(sS D x).1, aS D x + 1 + (m : ZMod (kI D x))⟩
  else if m = dd D x - 1 then StrandKind.cutStartT
  else if m = dd D x then StrandKind.arcTS
  else StrandKind.cutEndS

/-- The kind of the edge with index `m` of component `B`. -/
def kindIdxB (m : ℕ) : StrandKind D x :=
  if m < kI D x - dd D x - 1 then StrandKind.old ⟨(sS D x).1, bS D x + 1 + (m : ZMod (kI D x))⟩
  else if m = kI D x - dd D x - 1 then StrandKind.cutStartS
  else if m = kI D x - dd D x then StrandKind.arcST
  else StrandKind.cutEndT

/-- The kind map of the self shadow. -/
def selfKind (h : (sS D x).1 = (tS D x).1) (u : (selfShadow D x ε h).Strand) : StrandKind D x :=
  Fin.cases (motive := fun l => ZMod ((selfShadow D x ε h).comp l).k → StrandKind D x)
    (fun m => kindIdxA D x m.val)
    (Fin.cases (motive := fun l => ZMod ((selfShadow D x ε h).comp l.succ).k → StrandKind D x)
      (fun m => kindIdxB D x m.val)
      (fun l m => StrandKind.old ⟨(othersS D x).orderEmbOfFin rfl l, (m.val : ZMod _)⟩)) u.1 u.2

/-- The self shadow is a splice model. -/
def selfModel (h : (sS D x).1 = (tS D x).1) : SpliceModel D x ε (selfShadow D x ε h) where
  kind := selfKind D x ε h
  kind_injective := by
    sorry
  kind_surj := by
    sorry
  kind_occurs := by
    sorry
  kind_pred := by
    sorry
  tail_eq := by
    sorry
  dir_eq := by
    sorry
  cut_val := by
    sorry

/-! ### 7c. The smoothed diagram -/

/-- **The smoothed diagram** `D₀` of `D` at `x` with cut parameter `ε`. -/
def smoothDiagram (hε : SmallEps D x ε) : Diagram :=
  if h : (sS D x).1 = (tS D x).1 then toDiagram D x (selfModel D x ε h) hε
  else toDiagram D x (mixedModel D x ε h) hε

theorem isOrientedSmoothing_smoothDiagram (hε : SmallEps D x ε) :
    IsOrientedSmoothing D x (smoothDiagram D x ε hε) := by
  unfold smoothDiagram
  split_ifs with h
  · exact isOrientedSmoothing_toDiagram D x (selfModel D x ε h) hε
  · exact isOrientedSmoothing_toDiagram D x (mixedModel D x ε h) hε

/-- Component count by construction: `c + 1` (self) or `c − 1` (mixed). -/
theorem smoothDiagram_componentCount (hε : SmallEps D x ε) :
    (smoothDiagram D x ε hε).componentCount =
      if (sS D x).1 = (tS D x).1 then D.componentCount + 1 else D.componentCount - 1 := by
  unfold smoothDiagram
  split_ifs with h
  · show (othersS D x).card + 2 = D.Γ.c + 1
    have := card_othersS D x; omega
  · show (othersM D x).card + 1 = D.Γ.c - 1
    have := card_othersM D x h; omega

/-! ## 8. The record bridge

For a splice model, the occurrences of `D₀` are the occurrences of `D` at crossings other than `x`
(`origVisit`); pairing, bits and signs transport strand-wise; the components of `D₀` are the
`Record.SmoothComps` of `D.record` at the over occurrence (a bijective classification `cls`,
explicit per case); and the successor of `D₀` is the first return of the reconnected successor
(`Record.smoothSucc`).  The successor law is proved **once**, at the model level
(`succ_of_coord`), from three ingredients grafted from tag B:
* the *smoothed coordinate* `key` on the occurrences of `D` (forward distance from `xv` on the
  circle of `s`, `k_i +` forward distance from `τ xv` on the circle of `t`, plain coordinate
  elsewhere), on whose retained values the reconnected successor is the cyclic successor
  (`reconnect_no_between`, stated for `rkey = key ∘ swap(xv, τxv)` so that the two erased
  occurrences sit at their cyclic positions);
* the general first-return lemma `firstReturn_no_between` (§0');
* per concrete model, the statement that the traversal coordinate of `D₀`, rotated on each
  component so that the cut-end piece comes first (`mixedBase`, `selfBase`), is a strictly
  increasing function of `key ∘ origVisit` (`mixed_key_lt_iff`, `self_key_lt_iff`).
Then `cycNext_unique_on` in `D₀` identifies `D₀.nextVisit` with `smoothSucc`, exactly as in
`Diagram.restrictVisit_nextVisit` (LinkDiagramRecord 1344-1452). -/

/-! ### 8-pre. The smoothed coordinate of `D`'s occurrences -/

/-- The over occurrence of `x`, the erased occurrence of `Record.smooth`. -/
abbrev xv : D.Γ.Visit := D.overVisit x

/-- `τ xv` is the under occurrence (by `rfl`). -/
theorem record_pair_xv : D.record.pair (xv D x) = D.underVisit x := rfl

/-- The reconnected successor `s₁ = s ∘ swap(xv, τ xv)`, unfolded (by `rfl`). -/
theorem reconnect_xv_apply (v : D.Γ.Visit) :
    D.record.reconnect (xv D x) v = D.nextVisit (Equiv.swap (xv D x) (D.underVisit x) v) := rfl

/-- The smoothed coordinate of an occurrence of `D` (tag B's `smB_off`): on the circle of `s` the
forward distance from the over occurrence, on the circle of `t` (mixed case) `k_i +` the forward
distance from the under occurrence, and the plain traversal coordinate elsewhere.  In the self
case (`i = j`) the first branch applies to both words. -/
def key (v : D.Γ.Visit) : ℝ :=
  if D.compOf v = (sS D x).1 then
    Diagram.cyclicOffset (kI D x) (D.visitCoord (xv D x)) (D.visitCoord v)
  else if D.compOf v = (tS D x).1 then
    (kI D x : ℝ) + Diagram.cyclicOffset (kJ D x) (D.visitCoord (D.underVisit x)) (D.visitCoord v)
  else D.visitCoord v

/-- The reconnect coordinate: `key` with the two erased occurrences exchanged.  `s₁` sends the last
retained occurrence before `xv` to `xv` itself, whose cyclic position on the merged/split cycle is
that of `τ xv` (and vice versa); the swap puts them there. -/
def rkey (v : D.Γ.Visit) : ℝ := key D x (Equiv.swap (xv D x) (D.underVisit x) v)

theorem rkey_of_smoothKeep (v : D.Γ.Visit) (hv : D.record.SmoothKeep (xv D x) v) :
    rkey D x v = key D x v := by
  sorry

/-- `key` is injective on each `s₁`-cycle (on the circle of `s`: `cyclicOffset` is a bijection of
`[0,k_i)`; mixed case: the shift `k_i` separates the two circles; elsewhere `visitCoord_injOn`). -/
theorem rkey_injOn (v u : D.Γ.Visit) (hu : (D.record.reconnect (xv D x)).SameCycle u v)
    (he : rkey D x u = rkey D x v) : u = v := by
  sorry

/-- **`s₁` is the cyclic successor for `rkey` on each of its cycles.**  Away from `xv, τ xv`:
`s₁ v = succ v` and `nextVisit_no_between` transported by the rotation (`rexPL_rot_eq_cyclicOffset`,
`rexB_cycBetween_rot`), the other circle (mixed case) being shifted out of the way; at `xv`:
`s₁ xv = succ (τ xv)`, `rkey xv = key (τ xv)` and the retained occurrences after `τ xv` have larger
keys; at `τ xv`: symmetric. -/
theorem reconnect_no_between (v u : D.Γ.Visit)
    (hu : (D.record.reconnect (xv D x)).SameCycle u v) :
    ¬ cycBetween (rkey D x v) (rkey D x u) (rkey D x (D.record.reconnect (xv D x) v)) := by
  sorry

/-- No retained occurrence of the cycle lies strictly between a retained `v` and its smoothed
successor (`firstReturn_no_between` applied to `s₁`, `SmoothKeep`, `rkey`). -/
theorem smoothSucc_no_between (v : D.Γ.Visit) (hv : D.record.SmoothKeep (xv D x) v) (u : D.Γ.Visit)
    (hu : (D.record.reconnect (xv D x)).SameCycle u v) (hu' : D.record.SmoothKeep (xv D x) u) :
    ¬ cycBetween (key D x v) (key D x u)
      (key D x ((D.record.smooth (xv D x)).succ ⟨v, hv⟩).1) := by
  have h := firstReturn_no_between (D.record.reconnect (xv D x)) (D.record.SmoothKeep (xv D x))
    (rkey D x) (rkey_injOn D x) (reconnect_no_between D x) ⟨v, hv⟩ u hu hu'
  rw [rkey_of_smoothKeep D x v hv, rkey_of_smoothKeep D x u hu'] at h
  have h3 : rkey D x ((firstReturn (D.record.reconnect (xv D x)) (D.record.SmoothKeep (xv D x))
      ⟨v, hv⟩).1) = key D x ((D.record.smooth (xv D x)).succ ⟨v, hv⟩).1 :=
    rkey_of_smoothKeep D x _ ((D.record.smooth (xv D x)).succ ⟨v, hv⟩).2
  rw [h3] at h
  exact h

/-- Self case: the `s₁`-cycle of `τ xv` consists of `τ xv` and the occurrences of the circle met
strictly after `xv` and strictly before `τ xv` (the word `A` of `(x A y B)`).  Proof: the set on the
right is `s₁`-closed (`nextVisit_no_between` and cyclic trichotomy), contains `τ xv`, and its
complement in the circle is `s₁`-closed and contains `xv`; `reconnect_sameCycle_or` finishes. -/
theorem self_sameCycle_pair_iff (h : (sS D x).1 = (tS D x).1) (w : D.Γ.Visit)
    (hw : D.compOf w = (sS D x).1) :
    (D.record.reconnect (xv D x)).SameCycle w (D.underVisit x) ↔
      w = D.underVisit x ∨
        cycBetween (D.visitCoord (xv D x)) (D.visitCoord w) (D.visitCoord (D.underVisit x)) := by
  sorry

/-- Untouched circles: the `s₁`-cycles are the old circles. -/
theorem sameCycle_of_comp_ne (v w : D.Γ.Visit) (hv : D.compOf v ≠ (sS D x).1)
    (hv' : D.compOf v ≠ (tS D x).1) :
    (D.record.reconnect (xv D x)).SameCycle v w ↔ D.compOf v = D.compOf w := by
  sorry

/-- A rotated strictly monotone coordinate on each component transports the oriented cyclic order
of a diagram (`rexB_cycBetween_rot`, then `cycBetween` is three strict inequalities). -/
theorem visitBetween_iff_of_rot_lt_iff (D₀ : Diagram) (κ : D₀.Γ.Visit → ℝ) (c₀ : Fin D₀.Γ.c → ℝ)
    (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((D₀.Γ.comp l).k : ℝ))
    (hlt : ∀ v w, D₀.compOf v = D₀.compOf w →
      (rexB_rot ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) (c₀ (D₀.compOf v)) (D₀.visitCoord v) <
        rexB_rot ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) (c₀ (D₀.compOf v)) (D₀.visitCoord w) ↔ κ v < κ w))
    (v u w : D₀.Γ.Visit) (hu : D₀.compOf u = D₀.compOf v) (hw : D₀.compOf w = D₀.compOf v) :
    D₀.VisitBetween v u w ↔ cycBetween (κ v) (κ u) (κ w) := by
  sorry

section RecordBridge

variable {ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
include M hε

/-- The occurrence of `D` under an occurrence of `Γ₀`. -/
def origVisit (v : Γ₀.Visit) : D.Γ.Visit :=
  ⟨origCrossing D x M hε v.1, ⟨M.orig v.2.val, orig_mem_origCrossing D x M hε v.2.2⟩⟩

theorem origVisit_fst (v : Γ₀.Visit) : (origVisit D x M hε v).1 = origCrossing D x M hε v.1 := rfl

theorem origVisit_injective : Function.Injective (origVisit D x M hε) := by
  sorry

/-- Occurrences of `Γ₀` sit at crossings other than `x`: they are retained by `Record.smooth`. -/
theorem smoothKeep_origVisit (v : Γ₀.Visit) : D.record.SmoothKeep (xv D x) (origVisit D x M hε v) := by
  sorry

theorem exists_origVisit (w : D.Γ.Visit) (hw : D.record.SmoothKeep (xv D x) w) :
    ∃ v, origVisit D x M hε v = w := by
  sorry

/-- The occurrences of `D₀` are the retained occurrences of `D`. -/
def visitEquiv : Γ₀.Visit ≃ {w : D.Γ.Visit // D.record.SmoothKeep (xv D x) w} :=
  Equiv.ofBijective (fun v => ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    ⟨fun v w h => origVisit_injective D x M hε (congrArg Subtype.val h),
     fun w => by
      obtain ⟨v, hv⟩ := exists_origVisit D x M hε w.1 w.2
      exact ⟨v, Subtype.ext hv⟩⟩

theorem twin_origVisit (v : Γ₀.Visit) :
    D.twin (origVisit D x M hε v) = origVisit D x M hε ((toDiagram D x M hε).twin v) := by
  sorry

theorem overBit_origVisit (v : Γ₀.Visit) :
    (toDiagram D x M hε).overBit v = D.overBit (origVisit D x M hε v) := by
  sorry

theorem sign_origVisit (v : Γ₀.Visit) :
    (toDiagram D x M hε).sign v.1 = D.sign (origVisit D x M hε v).1 :=
  toDiagram_sign D x M hε v.1

/-- The traversal coordinate of an occurrence of `D₀` under `origVisit`: the original parameter is
the rescaled one (`crossingParam_toDiagram`), so `visitCoord (origVisit v) = label(orig).val +
origParam (param₀ v)`. -/
theorem visitCoord_origVisit (v : Γ₀.Visit) :
    D.visitCoord (origVisit D x M hε v) =
      ((M.orig v.2.val).2.val : ℝ) +
        (M.kind v.2.val).origParam ε ((toDiagram D x M hε).crossingParam v.1 v.2.2) := by
  sorry

/-- **Assembly of the record isomorphism** from a component classification `cls` and the
successor law. -/
def recordIsoOfCls (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)
    (hcls : Function.Bijective cls)
    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =
      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    (hsucc : ∀ v : Γ₀.Visit, origVisit D x M hε ((toDiagram D x M hε).nextVisit v) =
      ((D.record.smooth (xv D x)).succ ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩).1) :
    RecordIso (toDiagram D x M hε).record (D.record.smooth (xv D x)) where
  e := Equiv.ofBijective cls hcls
  Φ := visitEquiv D x M hε
  comp_eq v := (hcls_visit v).symm
  succ_eq v := Subtype.ext (hsucc v)
  pair_eq v := Subtype.ext (twin_origVisit D x M hε v).symm
  bit_eq v := (overBit_origVisit D x M hε v).symm
  sgn_eq v := (sign_origVisit D x M hε v).symm

/-- Same component of `D₀` iff same `s₁`-cycle of the original occurrences (from an injective
classification compatible with `origVisit`, via `Record.smooth_comp_eq_iff`). -/
theorem compOf_eq_iff_of_cls (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)
    (hcls : Function.Injective cls)
    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =
      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    (v w : Γ₀.Visit) :
    (toDiagram D x M hε).compOf v = (toDiagram D x M hε).compOf w ↔
      (D.record.reconnect (xv D x)).SameCycle (origVisit D x M hε v) (origVisit D x M hε w) := by
  sorry

/-- **The successor law from a rotated monotone coordinate** (the one proof of the successor law,
shared by both cases; template `Diagram.restrictVisit_nextVisit`).  If, on every component of `D₀`,
the traversal coordinate rotated by `c₀` is a strictly increasing function of `key ∘ origVisit`,
then the successor of `D₀` is the smoothed successor.  Proof: if `v` is alone on its component both
sides are `v` (`nextVisit_eq_self`, first return to the only retained element of the cycle);
otherwise `cycNext_unique_on` in `D₀` with `p := same component as v`, `k := D₀.visitCoord`,
candidates `D₀.nextVisit v` (`nextVisit_no_between`, `nextVisit_ne_self`) and the `origVisit`-preimage
of `smoothSucc (origVisit v)` (same component by `compOf_eq_iff_of_cls` + `Record.succ_comp`; no
occurrence between by `smoothSucc_no_between` transported through `visitBetween_iff_of_rot_lt_iff`). -/
theorem succ_of_coord (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)
    (hcls : Function.Injective cls)
    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =
      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    (c₀ : Fin Γ₀.c → ℝ) (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((Γ₀.comp l).k : ℝ))
    (hlt : ∀ v w : Γ₀.Visit, (toDiagram D x M hε).compOf v = (toDiagram D x M hε).compOf w →
      (rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord v) <
        rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord w) ↔
        key D x (origVisit D x M hε v) < key D x (origVisit D x M hε w)))
    (v : Γ₀.Visit) :
    origVisit D x M hε ((toDiagram D x M hε).nextVisit v) =
      ((D.record.smooth (xv D x)).succ ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩).1 := by
  sorry

/-- The record isomorphism from a classification and a rotated monotone coordinate. -/
def recordIsoOfCoord (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)
    (hcls : Function.Bijective cls)
    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =
      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    (c₀ : Fin Γ₀.c → ℝ) (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((Γ₀.comp l).k : ℝ))
    (hlt : ∀ v w : Γ₀.Visit, (toDiagram D x M hε).compOf v = (toDiagram D x M hε).compOf w →
      (rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord v) <
        rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord w) ↔
        key D x (origVisit D x M hε v) < key D x (origVisit D x M hε w))) :
    RecordIso (toDiagram D x M hε).record (D.record.smooth (xv D x)) :=
  recordIsoOfCls D x M hε cls hcls hcls_visit
    (succ_of_coord D x M hε cls hcls.1 hcls_visit c₀ hc₀ hlt)

end RecordBridge

/-! ### 8a. Component classification and rotated coordinate, per case -/

/-- The `SmoothComps` class of an untouched component `i₀` of `D`: the reconnect-cycle of any of
its occurrences, or the crossing-free circle `i₀`. -/
def oldCls (i₀ : Fin D.Γ.c) : (D.record.smooth (xv D x)).comps :=
  if h : ∃ w : D.Γ.Visit, D.compOf w = i₀ then Sum.inl (Quotient.mk _ (Classical.choose h))
  else Sum.inr ⟨i₀, fun w hw => h ⟨w, hw⟩⟩

/-- On an untouched component `i₀ ∉ {i, j}` the class of every occurrence is `oldCls i₀`. -/
theorem oldCls_eq (i₀ : Fin D.Γ.c) (hi : i₀ ≠ (sS D x).1) (hj : i₀ ≠ (tS D x).1) (w : D.Γ.Visit)
    (hw : D.compOf w = i₀) : oldCls D x i₀ = Sum.inl (Quotient.mk _ w) := by
  sorry

section MixedRecord

/-- The class map of the mixed case: the merged component is the reconnect-cycle of `x`
(`= ⟦τx⟧`, `Record.reconnect_sameCycle_pair_of_mixed`). -/
def mixedCls : Fin ((othersM D x).card + 1) → (D.record.smooth (xv D x)).comps :=
  Fin.cases (Sum.inl (Quotient.mk _ (xv D x)))
    (fun l => oldCls D x ((othersM D x).orderEmbOfFin rfl l))

/-- The rotation base of the mixed shadow: on the merged component the cut-end piece `[s⁺, P_i(a+1)]`
sits at the last label `N − 1` and is where the smoothed order starts; untouched components are not
rotated. -/
def mixedBase : Fin ((othersM D x).card + 1) → ℝ :=
  Fin.cases ((kI D x + kJ D x + 3 : ℕ) : ℝ) (fun _ => 0)

variable {ε} (hε : SmallEps D x ε) (h : (sS D x).1 ≠ (tS D x).1)

omit hε in
theorem mixedBase_mem (l : Fin ((othersM D x).card + 1)) :
    0 ≤ mixedBase D x l ∧ mixedBase D x l < (((mixedShadow D x ε).comp l).k : ℝ) := by
  sorry

include h in
theorem mixedCls_bijective : Function.Bijective (mixedCls D x) := by
  sorry

theorem mixedCls_visit (v : (mixedShadow D x ε).Visit) :
    mixedCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp
      ⟨origVisit D x (mixedModel D x ε h) hε v, smoothKeep_origVisit D x (mixedModel D x ε h) hε v⟩ := by
  sorry

/-- The smoothed coordinate on the merged component, block by block (`m = v.2.val.2.val` the label,
`θ = param₀`): old `i`-edges `m < k_i − 1 ↦ m + 1 + θ − τs`; `cutStartS ↦ k_i − τs + θ(τs − ε)`;
`cutEndT ↦ k_i + ε + θ(1 − τt − ε)`; old `j`-edges `↦ m − 1 + θ − τt`; `cutStartT ↦ k_i + k_j − τt +
θ(τt − ε)`; `cutEndS ↦ ε + θ(1 − τs − ε)`.  Each block is affine with positive slope, the blocks are
increasing in label order except the last, which is the smallest: hence the rotation by `N − 1`. -/
theorem mixed_key_lt_iff (v w : (mixedShadow D x ε).Visit)
    (hc : (toDiagram D x (mixedModel D x ε h) hε).compOf v =
      (toDiagram D x (mixedModel D x ε h) hε).compOf w) :
    (rexB_rot (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) (mixedBase D x v.2.val.1)
        ((toDiagram D x (mixedModel D x ε h) hε).visitCoord v) <
      rexB_rot (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) (mixedBase D x v.2.val.1)
        ((toDiagram D x (mixedModel D x ε h) hε).visitCoord w) ↔
      key D x (origVisit D x (mixedModel D x ε h) hε v) <
        key D x (origVisit D x (mixedModel D x ε h) hε w)) := by
  sorry

/-- The record bridge, mixed case. -/
def mixedRecordIso :
    RecordIso (toDiagram D x (mixedModel D x ε h) hε).record (D.record.smooth (xv D x)) :=
  recordIsoOfCoord D x (mixedModel D x ε h) hε (mixedCls D x) (mixedCls_bijective D x h)
    (mixedCls_visit D x hε h) (mixedBase D x) (mixedBase_mem D x) (mixed_key_lt_iff D x hε h)

end MixedRecord

section SelfRecord

/-- The class map of the self case: `A ↦ ⟦τx⟧` (occurrences after `x`, before `τx`),
`B ↦ ⟦x⟧`. -/
def selfCls : Fin ((othersS D x).card + 2) → (D.record.smooth (xv D x)).comps :=
  Fin.cases (Sum.inl (Quotient.mk _ (D.record.pair (xv D x))))
    (Fin.cases (Sum.inl (Quotient.mk _ (xv D x)))
      (fun l => oldCls D x ((othersS D x).orderEmbOfFin rfl l)))

/-- The rotation bases of the self shadow: on `A` the cut-end piece `[s⁺, P(a+1)]` sits at label
`d + 1`, on `B` the cut-end piece `[t⁺, P(b+1)]` at label `k − d + 1`. -/
def selfBase : Fin ((othersS D x).card + 2) → ℝ :=
  Fin.cases ((dd D x + 1 : ℕ) : ℝ) (Fin.cases ((kI D x - dd D x + 1 : ℕ) : ℝ) (fun _ => 0))

variable {ε} (hε : SmallEps D x ε) (h : (sS D x).1 = (tS D x).1)

omit hε in
theorem selfBase_mem (l : Fin ((othersS D x).card + 2)) :
    0 ≤ selfBase D x l ∧ selfBase D x l < (((selfShadow D x ε h).comp l).k : ℝ) := by
  sorry

include h in
theorem selfCls_bijective : Function.Bijective (selfCls D x) := by
  sorry

/-- `A`'s occurrences are on the `s₁`-cycle of `τ xv` and `B`'s on that of `xv`
(`self_sameCycle_pair_iff`, `reconnect_sameCycle_or`, `smooth_comps_ne_of_self`). -/
theorem selfCls_visit (v : (selfShadow D x ε h).Visit) :
    selfCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp
      ⟨origVisit D x (selfModel D x ε h) hε v, smoothKeep_origVisit D x (selfModel D x ε h) hε v⟩ := by
  sorry

/-- The smoothed coordinate on `A` (labels `m`): old edges `m < d − 1 ↦ m + 1 + θ − τs`;
`cutStartT ↦ d − τs + θ(τt − ε)`; `cutEndS ↦ ε + θ(1 − τs − ε)` (smallest block, rotation by `d + 1`);
on `B`: old edges `↦ m + d + 1 + θ − τs`; `cutStartS ↦ k − τs + θ(τs − ε)`; `cutEndT ↦ d − τs + τt +
ε + θ(1 − τt − ε)` (smallest block, rotation by `k − d + 1`). -/
theorem self_key_lt_iff (v w : (selfShadow D x ε h).Visit)
    (hc : (toDiagram D x (selfModel D x ε h) hε).compOf v =
      (toDiagram D x (selfModel D x ε h) hε).compOf w) :
    (rexB_rot (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) (selfBase D x v.2.val.1)
        ((toDiagram D x (selfModel D x ε h) hε).visitCoord v) <
      rexB_rot (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) (selfBase D x v.2.val.1)
        ((toDiagram D x (selfModel D x ε h) hε).visitCoord w) ↔
      key D x (origVisit D x (selfModel D x ε h) hε v) <
        key D x (origVisit D x (selfModel D x ε h) hε w)) := by
  sorry

/-- The record bridge, self case. -/
def selfRecordIso :
    RecordIso (toDiagram D x (selfModel D x ε h) hε).record (D.record.smooth (xv D x)) :=
  recordIsoOfCoord D x (selfModel D x ε h) hε (selfCls D x) (selfCls_bijective D x h)
    (selfCls_visit D x hε h) (selfBase D x) (selfBase_mem D x h) (self_key_lt_iff D x hε h)

end SelfRecord

/-- **The record bridge for the construction.** -/
theorem smoothDiagram_record (hε : SmallEps D x ε) :
    Nonempty (RecordIso (smoothDiagram D x ε hε).record (D.record.smooth (D.overVisit x))) := by
  unfold smoothDiagram
  split_ifs with h
  · exact ⟨selfRecordIso D x hε h⟩
  · exact ⟨mixedRecordIso D x hε h⟩

end Smoothing

/-! ## 9. The goal theorems (namespace `SM.Link`) -/

open Smoothing

/-- **exists_smoothing** (design file, section skein_and_moves; sm-3:1084-1103): every crossing of
every diagram admits an oriented smoothing — the ε-reconnection `smoothDiagram`. -/
theorem exists_smoothing (D : Diagram) (x : D.Γ.Crossing) : ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ :=
  ⟨smoothDiagram D x (eps D x) (eps_small D x), isOrientedSmoothing_smoothDiagram D x _ (eps_small D x)⟩

/-- **smoothing_record, constructive form**: the smoothing produced by `exists_smoothing` has the
record `D.record.smooth (overVisit x)` (sm-3:1090-1103, the cycle rewriting
`(x A y B) ↦ (x B), (y A)` / `(x A), (y B) ↦ (x B y A)`).  This is the form the (N, b) inductions
of rp:record-polynomial and lp:core consume: it yields `c(D₀) = c ± 1 ≥ 1`
(`Record.componentCount_smooth`) and `N(D₀) = N − 1` (`IsOrientedSmoothing.card_crossing`). -/
theorem exists_smoothing_record (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) :=
  ⟨smoothDiagram D x (eps D x) (eps_small D x), isOrientedSmoothing_smoothDiagram D x _ (eps_small D x),
    smoothDiagram_record D x (eps D x) (eps_small D x)⟩

/-- The same for the under occurrence, or any occurrence `v` of `x` (`Record.smoothPairIso`). -/
theorem exists_smoothing_record_visit (D : Diagram) (x : D.Γ.Crossing) (v : D.Γ.Visit) (hv : v.1 = x) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧ Nonempty (RecordIso D₀.record (D.record.smooth v)) := by
  obtain ⟨D₀, hD₀, ⟨ι⟩⟩ := exists_smoothing_record D x
  refine ⟨D₀, hD₀, ?_⟩
  have h := D.visit_eq_over_or_under v
  rw [hv] at h
  rcases h with rfl | rfl
  · exact ⟨ι⟩
  · exact ⟨ι.trans (D.record.smoothPairIso (D.overVisit x)).symm⟩

/-- The `SmoothingRecordClause` of LinkMoves holds for the constructed smoothing. -/
theorem smoothingRecordClause_smoothDiagram (D : Diagram) (x : D.Γ.Crossing) :
    SmoothingRecordClause Diagram.record (fun _ v => v) D x (smoothDiagram D x (eps D x) (eps_small D x)) :=
  smoothDiagram_record D x (eps D x) (eps_small D x)

open scoped Classical in
/-- Consumers' counts: the constructed smoothing has `c ± 1` components and `N − 1` crossings. -/
theorem exists_smoothing_counts (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) ∧
      D₀.componentCount = (if D.record.IsSelfCrossing (D.overVisit x) then D.componentCount + 1
        else D.componentCount - 1) ∧
      1 ≤ D₀.componentCount ∧
      Fintype.card D₀.Γ.Crossing + 1 = Fintype.card D.Γ.Crossing := by
  obtain ⟨D₀, hD₀, ⟨ι⟩⟩ := exists_smoothing_record D x
  refine ⟨D₀, hD₀, ⟨ι⟩, ?_, D₀.componentCount_pos, hD₀.card_crossing⟩
  rw [← D₀.record_componentCount, ι.componentCount_eq, D.record.componentCount_smooth,
    D.record_componentCount]

end

end SM.Link
