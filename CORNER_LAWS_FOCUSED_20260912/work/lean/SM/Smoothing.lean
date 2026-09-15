import SM.LinkDiagramRecord
import SM.LinkMoves
import SM.LinkRecordExtras
import SM.LinkDiagramExtras
import SM.LinkRecordExtension

/-! Ported verbatim 2026-09-13 from work/drafts/smoothing/Smoothing_Assembled.lean (assembler subagent of the pod executor merging the eight sorry-free prover units U1-U5, U6a-c of work/drafts/smoothing/ into the judge-merged Skeleton_FINAL.lean; ASSEMBLY_REPORT.md records the de-duplications and the replacement of the false lemma `seg_arc_subset_ball` by `seg_arc_subset_closedBall`; checked with `lake env lean`, no sorry, standard axioms); only this header added and `#print axioms` lines removed. Library module (no row): the geometric smoothing existence `exists_smoothing : ∀ D x, ∃ D₀, IsOrientedSmoothing D x D₀`, the constructive record bridge `exists_smoothing_record` / `exists_smoothing_record_visit` (D₀ with RecordIso D₀.record (D.record.smooth v)) and `exists_smoothing_counts` — the gate for lp:core, rp:record-polynomial, lp:split-circle, lc:presentations and the mp:* rows. Design: work/drafts/smoothing/PLAN_FINAL.md. -/


/-! # Smoothing (assembled) — the oriented smoothing `exists_smoothing` / `smoothing_record`
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

Status (assembled 2026-09-13 from Skeleton_FINAL.lean and the eight prover units U1, U2, U3, U4, U5,
U6a, U6b, U6c; see ASSEMBLY_REPORT.md): every lemma of the chain is proved, nothing is left unproved; the goal
theorems at the end are proved from the chain.  The skeleton's `seg_arc_subset_ball` was false as
stated and is replaced by `seg_arc_subset_closedBall` (PLAN_FINAL.md §5 addendum).
Plan: work/drafts/smoothing/PLAN_FINAL.md. -/

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

/-! U4 helpers (general): `det` under rescaling, traversal points `⟨e.1, (e.2, θ)⟩` built from a
strand and a parameter, and congruence of `crossingParam`. -/

theorem det_smul_smul (a b : Plane) (l m : ℝ) : det (l • a) (m • b) = (l * m) * det a b := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem Shadow.mk_eq_mk_iff {Γ : Shadow} (e e' : Γ.Strand) (θ θ' : Set.Ico (0:ℝ) 1) :
    (⟨e.1, (e.2, θ)⟩ : Γ.Pt) = ⟨e'.1, (e'.2, θ')⟩ ↔ e = e' ∧ θ = θ' := by
  obtain ⟨i, m⟩ := e
  obtain ⟨i', m'⟩ := e'
  constructor
  · intro h
    rw [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h2⟩ := h
    have h3 := eq_of_heq h2
    rw [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, rfl⟩
    rw [Sigma.mk.inj_iff] at h1
    obtain ⟨rfl, h2⟩ := h1
    rw [eq_of_heq h2]

theorem mem_sphere_of_mem_closedBall_not_mem_ball {c q : Plane} {r : ℝ}
    (h1 : q ∈ Metric.closedBall c r) (h2 : q ∉ Metric.ball c r) : q ∈ Metric.sphere c r :=
  Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp h1)
    (not_lt.mp (fun h => h2 (Metric.mem_ball.mpr h))))

theorem Diagram.crossingParam_congr (D : Diagram) {y y' : D.Γ.Crossing} {s s' : D.Γ.Strand}
    (hy : y = y') (hs : s = s') (h : s ∈ y.val) (h' : s' ∈ y'.val) :
    D.crossingParam y h = D.crossingParam y' h' := by
  subst hy; subst hs; rfl

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

/-! ### Cyclic-order toolbox for the record bridge (unit U6a) -/

theorem cycBetween_add_left (c x y z : ℝ) :
    cycBetween (c + x) (c + y) (c + z) ↔ cycBetween x y z := by
  unfold cycBetween; simp only [add_lt_add_iff_left]

theorem cycBetween_or_of_ne {a b c : ℝ} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cycBetween a b c ∨ cycBetween a c b := by
  unfold cycBetween
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3 <;>
    first
    | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

theorem cycBetween_asymm' {a b c : ℝ} (h : cycBetween a b c) : ¬ cycBetween c b a := by
  unfold cycBetween at *
  rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rcases h with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem not_cycBetween_of_of {a b c d : ℝ} (h1 : cycBetween a c d) (h2 : cycBetween c b d) :
    ¬ cycBetween a d b := by
  unfold cycBetween at *
  rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

theorem cyclicOffset_injOn (k : ℕ) {a x y : ℝ} (ha : 0 ≤ a ∧ a < k) (hx : 0 ≤ x ∧ x < k)
    (hy : 0 ≤ y ∧ y < k) (h : Diagram.cyclicOffset k a x = Diagram.cyclicOffset k a y) : x = y := by
  have := ha.1; have := ha.2; have := hx.1; have := hx.2; have := hy.1; have := hy.2
  unfold Diagram.cyclicOffset at h
  split_ifs at h <;> linarith

namespace Diagram

variable (D : Diagram)

theorem compOf_swap (p q w : D.Γ.Visit) (hc : D.compOf q = D.compOf p) (hw : D.compOf w = D.compOf p) :
    D.compOf (Equiv.swap p q w) = D.compOf p := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · exact hc
  · rfl
  · exact hw

/-- One step of `succ ∘ swap p q` keeps the word strictly between `p` and `q` (plus `q`) closed. -/
theorem swap_step_closed (p q : D.Γ.Visit) (hpq : p ≠ q) (hc : D.compOf q = D.compOf p)
    (w : D.Γ.Visit) (hw : D.compOf w = D.compOf p)
    (hW : w = q ∨ cycBetween (D.visitCoord p) (D.visitCoord w) (D.visitCoord q)) :
    D.nextVisit (Equiv.swap p q w) = q ∨
      cycBetween (D.visitCoord p) (D.visitCoord (D.nextVisit (Equiv.swap p q w))) (D.visitCoord q) := by
  have hne : ∀ z z' : D.Γ.Visit, D.compOf z = D.compOf z' → z ≠ z' → D.visitCoord z ≠ D.visitCoord z' :=
    fun z z' hzz' hne h => hne (D.visitCoord_injOn hzz' h)
  rcases hW with rfl | hW
  · rw [Equiv.swap_apply_right]
    by_cases hn : D.nextVisit p = w
    · exact Or.inl hn
    · right
      have hnb := D.nextVisit_no_between p w hc
      have hnp : D.nextVisit p ≠ p := D.nextVisit_ne_self p w hc hpq.symm
      have hcn : D.compOf (D.nextVisit p) = D.compOf p := D.compOf_nextVisit p
      exact (cycBetween_or_of_ne (hne p w hc.symm hpq) (hne w _ (hc.trans hcn.symm) (Ne.symm hn))
        (hne p _ hcn.symm hnp.symm)).resolve_left hnb
  · have hwp : w ≠ p := fun h => by rw [h] at hW; exact not_cycBetween_self_left _ _ hW
    have hwq : w ≠ q := fun h => by rw [h] at hW; exact not_cycBetween_self_mid _ _ hW
    rw [Equiv.swap_apply_of_ne_of_ne hwp hwq]
    by_cases hn : D.nextVisit w = q
    · exact Or.inl hn
    · right
      have hnb := D.nextVisit_no_between w q (hc.trans hw.symm)
      have hnw : D.nextVisit w ≠ w := D.nextVisit_ne_self w q (hc.trans hw.symm) (Ne.symm hwq)
      have hcn : D.compOf (D.nextVisit w) = D.compOf p := (D.compOf_nextVisit w).trans hw
      have h2 : cycBetween (D.visitCoord w) (D.visitCoord (D.nextVisit w)) (D.visitCoord q) :=
        (cycBetween_or_of_ne (hne w q (hw.trans hc.symm) hwq) (hne q _ (hc.trans hcn.symm) (Ne.symm hn))
          (hne w _ (hw.trans hcn.symm) hnw.symm)).resolve_left hnb
      -- hW : cycBetween p w q, h2 : cycBetween w n q ⊢ cycBetween p n q
      unfold cycBetween at hW h2 ⊢
      rcases hW with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
        first
        | exact Or.inl ⟨by linarith, by linarith⟩
        | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
        | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

/-- Iterating `succ ∘ swap p q` from `q` stays in the word strictly between `p` and `q` (plus `q`). -/
theorem swap_pow_closed (p q : D.Γ.Visit) (hpq : p ≠ q) (hc : D.compOf q = D.compOf p) (n : ℕ) :
    D.compOf (((D.visitSucc * Equiv.swap p q) ^ n) q) = D.compOf p ∧
      ((((D.visitSucc * Equiv.swap p q) ^ n) q = q) ∨
        cycBetween (D.visitCoord p) (D.visitCoord (((D.visitSucc * Equiv.swap p q) ^ n) q))
          (D.visitCoord q)) := by
  induction n with
  | zero => exact ⟨by rw [pow_zero, Equiv.Perm.one_apply]; exact hc, Or.inl (by rw [pow_zero, Equiv.Perm.one_apply])⟩
  | succ n ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, visitSucc_apply]
    refine ⟨?_, D.swap_step_closed p q hpq hc _ ih.1 ih.2⟩
    rw [D.compOf_nextVisit, D.compOf_swap p q _ hc ih.1]

end Diagram

/-- The step of the first-return induction: `b` between `a` and `d`, and neither `a` nor `b`
between `c` and `d` (so `d` comes before both going forward from `c`): then `b` is between `a`
and `c`. -/
theorem cycBetween_step {a b c d : ℝ} (h1 : cycBetween a b d) (h2 : cycBetween c d b)
    (h3 : cycBetween c d a) : cycBetween a b c := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h3 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)

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
  have hne : ∀ w z, f.SameCycle w z → w ≠ z → κ w ≠ κ z :=
    fun w z hs hwz h => hwz (hκ z w hs h)
  have claim : ∀ j : ℕ, cycBetween (κ v.1) (κ u) (κ ((f ^ j) v.1)) →
      ∃ i, 0 < i ∧ i < j ∧ (f ^ i) v.1 = u := by
    intro j
    induction j with
    | zero =>
      intro h
      rw [pow_zero, Equiv.Perm.one_apply] at h
      exact absurd h (not_cycBetween_self_right _ _)
    | succ j ih =>
      intro h
      have hfw : (f ^ (j + 1)) v.1 = f ((f ^ j) v.1) := by
        rw [pow_succ', Equiv.Perm.mul_apply]
      rw [hfw] at h
      have hwv : f.SameCycle ((f ^ j) v.1) v.1 :=
        Equiv.Perm.sameCycle_pow_left.mpr (Equiv.Perm.SameCycle.refl f v.1)
      have huw : f.SameCycle u ((f ^ j) v.1) := hu.trans hwv.symm
      by_cases huw' : u = (f ^ j) v.1
      · refine ⟨j, ?_, by omega, huw'.symm⟩
        rcases Nat.eq_zero_or_pos j with hj | hj
        · exfalso
          rw [hj, pow_zero, Equiv.Perm.one_apply] at huw'
          rw [huw'] at h
          exact not_cycBetween_self_left _ _ h
        · exact hj
      · by_cases hwv' : (f ^ j) v.1 = v.1
        · exfalso
          rw [hwv'] at h
          exact hf v.1 u hu h
        · have hfw_ne_v : f ((f ^ j) v.1) ≠ v.1 := fun heq => by
            rw [heq] at h; exact not_cycBetween_self_right _ _ h
          by_cases hfw_w : f ((f ^ j) v.1) = (f ^ j) v.1
          · rw [hfw_w] at h
            obtain ⟨i, hi0, hij, hi⟩ := ih h
            exact ⟨i, hi0, by omega, hi⟩
          · have hu_fw : u ≠ f ((f ^ j) v.1) := fun heq => by
              rw [← heq] at h; exact not_cycBetween_self_mid _ _ h
            have hfw_cycle : f.SameCycle (f ((f ^ j) v.1)) ((f ^ j) v.1) :=
              Equiv.Perm.sameCycle_apply_left.mpr (Equiv.Perm.SameCycle.refl f _)
            have n1 : ¬ cycBetween (κ ((f ^ j) v.1)) (κ u) (κ (f ((f ^ j) v.1))) :=
              hf _ u huw
            have n2 : ¬ cycBetween (κ ((f ^ j) v.1)) (κ v.1) (κ (f ((f ^ j) v.1))) :=
              hf _ v.1 hwv.symm
            have p1 : cycBetween (κ ((f ^ j) v.1)) (κ (f ((f ^ j) v.1))) (κ u) :=
              (cycBetween_or_of_ne (hne _ u huw.symm (Ne.symm huw'))
                (hne u _ (huw.trans hfw_cycle.symm) hu_fw)
                (hne _ _ hfw_cycle.symm (Ne.symm hfw_w))).resolve_left n1
            have p2 : cycBetween (κ ((f ^ j) v.1)) (κ (f ((f ^ j) v.1))) (κ v.1) :=
              (cycBetween_or_of_ne (hne _ v.1 hwv hwv')
                (hne v.1 _ (hwv.symm.trans hfw_cycle.symm) hfw_ne_v.symm)
                (hne _ _ hfw_cycle.symm (Ne.symm hfw_w))).resolve_left n2
            obtain ⟨i, hi0, hij, hi⟩ := ih (cycBetween_step h p1 p2)
            exact ⟨i, hi0, by omega, hi⟩
  intro h
  rw [firstReturn_apply] at h
  obtain ⟨i, hi0, hin, hi⟩ := claim _ h
  exact returnTime_min f p v.1 v.2 hi0 hin (by rw [hi]; exact hp)

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
form of the skeleton's `seg_arc_subset_ball`, which is false as stated; see the note below). -/
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

/-! The skeleton's `seg_arc_subset_ball` (open ball of radius `ε · max(‖es‖, ‖et‖)`) is FALSE as
stated — `Plane = ℝ × ℝ` carries the sup norm, so an arc can lie on that sphere (counterexample
`es = (1, 0)`, `et = (-1, 1/2)`; PLAN_FINAL.md §5 addendum).  It is not part of the assembled module;
every former use composes `seg_arc_subset_closedBall` with
`Metric.closedBall_subset_ball (arc_lt_discRadius …)` (strict room: `max … < discRadius`). -/

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

/-! U4 helpers: kind-level parameter arithmetic (`origParam`/`liftParam` are inverse affine maps
on the non-arc kinds; directions of non-arc kinds are positive multiples of the original
directions; two non-arc kinds over the same strand with a common rescaled parameter coincide). -/

theorem liftParam_origParam (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)
    (hκ' : κ ≠ arcTS) (θ : ℝ) : κ.liftParam ε (κ.origParam ε θ) = θ := by
  have h1 : τs D x - ε ≠ 0 := by linarith [hε.lt_τs]
  have h2 : 1 - τs D x - ε ≠ 0 := by linarith [hε.lt_one_sub_τs]
  have h3 : τt D x - ε ≠ 0 := by linarith [hε.lt_τt]
  have h4 : 1 - τt D x - ε ≠ 0 := by linarith [hε.lt_one_sub_τt]
  cases κ with
  | old e => rfl
  | cutStartS => simp only [liftParam, origParam]; rw [div_eq_iff h1]
  | cutEndS => simp only [liftParam, origParam]; rw [div_eq_iff h2]; ring
  | cutStartT => simp only [liftParam, origParam]; rw [div_eq_iff h3]
  | cutEndT => simp only [liftParam, origParam]; rw [div_eq_iff h4]; ring
  | arcST => exact absurd rfl hκ
  | arcTS => exact absurd rfl hκ'

theorem origParam_liftParam (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)
    (hκ' : κ ≠ arcTS) (θ : ℝ) : κ.origParam ε (κ.liftParam ε θ) = θ := by
  have h1 : τs D x - ε ≠ 0 := by linarith [hε.lt_τs]
  have h2 : 1 - τs D x - ε ≠ 0 := by linarith [hε.lt_one_sub_τs]
  have h3 : τt D x - ε ≠ 0 := by linarith [hε.lt_τt]
  have h4 : 1 - τt D x - ε ≠ 0 := by linarith [hε.lt_one_sub_τt]
  cases κ with
  | old e => rfl
  | cutStartS => simp only [liftParam, origParam]; exact div_mul_cancel₀ θ h1
  | cutEndS => simp only [liftParam, origParam]; rw [div_mul_cancel₀ _ h2]; ring
  | cutStartT => simp only [liftParam, origParam]; exact div_mul_cancel₀ θ h3
  | cutEndT => simp only [liftParam, origParam]; rw [div_mul_cancel₀ _ h4]; ring
  | arcST => exact absurd rfl hκ
  | arcTS => exact absurd rfl hκ'

theorem dir_eq_smul_orig (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)
    (hκ' : κ ≠ arcTS) : ∃ l : ℝ, 0 < l ∧ κ.dir ε = l • D.Γ.dir κ.orig := by
  cases κ with
  | old e => exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  | cutStartS => exact ⟨τs D x - ε, sub_pos.mpr hε.lt_τs, rfl⟩
  | cutEndS => exact ⟨1 - τs D x - ε, by linarith [hε.lt_one_sub_τs], rfl⟩
  | cutStartT => exact ⟨τt D x - ε, sub_pos.mpr hε.lt_τt, rfl⟩
  | cutEndT => exact ⟨1 - τt D x - ε, by linarith [hε.lt_one_sub_τt], rfl⟩
  | arcST => exact absurd rfl hκ
  | arcTS => exact absurd rfl hκ'

theorem origParam_mem_Ico (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ < 1) : κ.origParam ε θ ∈ Set.Ico (0:ℝ) 1 := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt
  have := hε.lt_one_sub_τt
  have := τs_pos D x; have := τs_lt_one D x; have := τt_pos D x; have := τt_lt_one D x
  cases κ <;> simp only [origParam, Set.mem_Ico]
  · exact ⟨h0, h1⟩
  · exact ⟨mul_nonneg h0 (by linarith), by nlinarith⟩
  · exact ⟨by nlinarith, by nlinarith⟩
  · exact ⟨mul_nonneg h0 (by linarith), by nlinarith⟩
  · exact ⟨by nlinarith, by nlinarith⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

theorem origParam_zero (ε : ℝ) (κ : StrandKind D x) (h1 : κ ≠ cutEndS) (h2 : κ ≠ cutEndT)
    (h3 : κ ≠ arcST) (h4 : κ ≠ arcTS) : κ.origParam ε 0 = 0 := by
  cases κ with
  | old e => rfl
  | cutStartS => exact zero_mul _
  | cutStartT => exact zero_mul _
  | cutEndS => exact absurd rfl h1
  | cutEndT => exact absurd rfl h2
  | arcST => exact absurd rfl h3
  | arcTS => exact absurd rfl h4

theorem origParam_ne_zero (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (h3 : κ ≠ arcST)
    (h4 : κ ≠ arcTS) {θ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≠ 0) : κ.origParam ε θ ≠ 0 := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt
  have := hε.lt_one_sub_τt
  have hθ' : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ)
  cases κ with
  | old e => exact hθ
  | cutStartS => exact (mul_pos hθ' (by linarith)).ne'
  | cutEndS => exact (add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg h0 (by linarith))).ne'
  | cutStartT => exact (mul_pos hθ' (by linarith)).ne'
  | cutEndT => exact (add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg h0 (by linarith))).ne'
  | arcST => exact absurd rfl h3
  | arcTS => exact absurd rfl h4

/-- The direction of the predecessor of a kind whose tail is an old vertex is a positive multiple
of the direction of the preceding strand of `D`. -/
theorem dir_pred_eq_smul (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x)
    (h1 : κ ≠ cutEndS) (h2 : κ ≠ cutEndT) (h3 : κ ≠ arcST) (h4 : κ ≠ arcTS) :
    ∃ l : ℝ, 0 < l ∧ κ.pred.dir ε = l • D.Γ.dir ⟨κ.orig.1, κ.orig.2 - 1⟩ := by
  cases κ with
  | old e =>
    simp only [pred, orig]
    split_ifs with hs ht
    · subst hs
      refine ⟨1 - τs D x - ε, by linarith [hε.lt_one_sub_τs], ?_⟩
      show (1 - τs D x - ε) • es D x = (1 - τs D x - ε) • D.Γ.dir ⟨(sS D x).1, (sS D x).2 + 1 - 1⟩
      rw [add_sub_cancel_right]
      try rfl
    · subst ht
      refine ⟨1 - τt D x - ε, by linarith [hε.lt_one_sub_τt], ?_⟩
      show (1 - τt D x - ε) • et D x = (1 - τt D x - ε) • D.Γ.dir ⟨(tS D x).1, (tS D x).2 + 1 - 1⟩
      rw [add_sub_cancel_right]
      try rfl
    · exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  | cutStartS => exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  | cutStartT => exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  | cutEndS => exact absurd rfl h1
  | cutEndT => exact absurd rfl h2
  | arcST => exact absurd rfl h3
  | arcTS => exact absurd rfl h4

theorem eq_of_orig_eq_of_origParam_eq (ε : ℝ) (hε : SmallEps D x ε) {κ κ' : StrandKind D x}
    (hκ : κ ≠ arcST ∧ κ ≠ arcTS) (hκ' : κ' ≠ arcST ∧ κ' ≠ arcTS) (ho : κ.Occurs) (ho' : κ'.Occurs)
    (horig : κ.orig = κ'.orig) {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (h0' : 0 ≤ θ') (h1' : θ' < 1)
    (hp : κ.origParam ε θ = κ'.origParam ε θ') : κ = κ' := by
  have hst := sS_ne_tS D x
  have hε1 := hε.pos; have hε2 := hε.lt_τs; have hε3 := hε.lt_one_sub_τs
  have hε4 := hε.lt_τt; have hε5 := hε.lt_one_sub_τt
  have m1 := mul_pos (sub_pos.mpr h1) (sub_pos.mpr hε2)
  have m2 := mul_pos (sub_pos.mpr h1') (sub_pos.mpr hε2)
  have m3 := mul_pos (sub_pos.mpr h1) (sub_pos.mpr hε4)
  have m4 := mul_pos (sub_pos.mpr h1') (sub_pos.mpr hε4)
  have m5 := mul_nonneg h0 (sub_pos.mpr hε3).le
  have m6 := mul_nonneg h0' (sub_pos.mpr hε3).le
  have m7 := mul_nonneg h0 (sub_pos.mpr hε5).le
  have m8 := mul_nonneg h0' (sub_pos.mpr hε5).le
  cases κ <;> cases κ' <;>
    try simp only [orig, origParam, Occurs, ne_eq, old.injEq] at horig hp ho ho' ⊢
  all_goals first
  | rfl
  | exact horig
  | exact absurd horig hst
  | exact absurd horig.symm hst
  | exact absurd horig ho.1
  | exact absurd horig ho.2
  | exact absurd horig.symm ho'.1
  | exact absurd horig.symm ho'.2
  | exact absurd rfl hκ.1
  | exact absurd rfl hκ.2
  | exact absurd rfl hκ'.1
  | exact absurd rfl hκ'.2
  | nlinarith

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
  unfold discRadius
  have h1 : 0 ≤ ε * ‖es D x‖ := mul_nonneg hε.pos.le (norm_nonneg _)
  have h2 := r₁_pos D x
  have h3 : ε * ‖es D x‖ ≤ max (ε * ‖es D x‖) (ε * ‖et D x‖) := le_max_left _ _
  linarith

theorem discRadius_lt_r₁ (hε : SmallEps D x ε) : discRadius D x ε < r₁ D x := by
  unfold discRadius
  have := max_lt hε.mul_es_lt hε.mul_et_lt
  linarith

theorem arc_lt_discRadius (hε : SmallEps D x ε) :
    max (ε * ‖es D x‖) (ε * ‖et D x‖) < discRadius D x ε := by
  unfold discRadius
  have := max_lt hε.mul_es_lt hε.mul_et_lt
  linarith

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
  by_contra h
  have h' := not_or.mp h
  have h1 := r₁_le_dist D x h'.1 h'.2 hq
  have h2 : dist (pt D x) q ≤ discRadius D x ε := by
    rw [dist_comm]; exact Metric.mem_closedBall.mp hU
  have h3 := discRadius_lt_r₁ D x ε hε
  linarith

/-- No crossing point of `D` other than `p` lies in the closed disc. -/
theorem crossingPoint_ne_not_mem_disc (hε : SmallEps D x ε) {y : D.Γ.Crossing} (hy : y ≠ x) :
    D.Γ.crossingPoint y ∉ disc D x ε := by
  intro hU
  have h1 := r₁_le_dist_crossingPoint D x hy
  have h2 : dist (pt D x) (D.Γ.crossingPoint y) ≤ discRadius D x ε := by
    rw [dist_comm]; exact Metric.mem_closedBall.mp hU
  have h3 := discRadius_lt_r₁ D x ε hε
  linarith

/-- No vertex of `D` lies in the closed disc. -/
theorem tail_not_mem_disc (hε : SmallEps D x ε) (e : D.Γ.Strand) : D.Γ.tail e ∉ disc D x ε := by
  intro hU
  have h1 := r₁_le_dist_tail D x e
  have h2 : dist (pt D x) (D.Γ.tail e) ≤ discRadius D x ε := by
    rw [dist_comm]; exact Metric.mem_closedBall.mp hU
  have h3 := discRadius_lt_r₁ D x ε hε
  linarith

/-! ### U2 helpers: one strand through the disc (general in the strand `e` and its parameter `τ`
at `p`; instantiated for `s` and `t` below). -/

/-- (U2 helper) Distance from a point of a strand `e` through `p` to `p`. -/
theorem dist_edgePt_pt {e : D.Γ.Strand} {τ : ℝ} (hp : pt D x = D.Γ.edgePt e τ) (θ : ℝ) :
    dist (D.Γ.edgePt e θ) (pt D x) = |θ - τ| * ‖D.Γ.dir e‖ := by
  rw [hp]; exact D.Γ.dist_edgePt e θ τ

/-- (U2 helper) Every strand of a generic shadow has a nonzero direction. -/
theorem norm_dir_pos (e : D.Γ.Strand) : 0 < ‖D.Γ.dir e‖ :=
  norm_pos_iff.mpr (D.Γ.edge_ne_zero D.generic e)

/-- (U2 helper) A point of a strand through `p` lies in the closed ball about `p` iff its
parameter is within `ρ / ‖dir e‖` of the parameter of `p`. -/
theorem edgePt_mem_closedBall_iff {e : D.Γ.Strand} {τ : ℝ} (hp : pt D x = D.Γ.edgePt e τ)
    (ρ θ : ℝ) :
    D.Γ.edgePt e θ ∈ Metric.closedBall (pt D x) ρ ↔
      τ - ρ / ‖D.Γ.dir e‖ ≤ θ ∧ θ ≤ τ + ρ / ‖D.Γ.dir e‖ := by
  have he := norm_dir_pos D e
  rw [Metric.mem_closedBall, dist_edgePt_pt D x hp θ, ← le_div_iff₀ he, abs_sub_le_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem edgePt_mem_ball_iff {e : D.Γ.Strand} {τ : ℝ} (hp : pt D x = D.Γ.edgePt e τ) (ρ θ : ℝ) :
    D.Γ.edgePt e θ ∈ Metric.ball (pt D x) ρ ↔
      τ - ρ / ‖D.Γ.dir e‖ < θ ∧ θ < τ + ρ / ‖D.Γ.dir e‖ := by
  have he := norm_dir_pos D e
  rw [Metric.mem_ball, dist_edgePt_pt D x hp θ, ← lt_div_iff₀ he, abs_sub_lt_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem edgePt_mem_sphere {e : D.Γ.Strand} {τ : ℝ} (hp : pt D x = D.Γ.edgePt e τ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (θ : ℝ) (hθ : θ = τ - ρ / ‖D.Γ.dir e‖ ∨ θ = τ + ρ / ‖D.Γ.dir e‖) :
    D.Γ.edgePt e θ ∈ Metric.sphere (pt D x) ρ := by
  have he := norm_dir_pos D e
  rw [Metric.mem_sphere, dist_edgePt_pt D x hp θ]
  rcases hθ with rfl | rfl
  · rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (div_nonneg hρ he.le),
      div_mul_cancel₀ _ he.ne']
  · rw [add_sub_cancel_left, abs_of_nonneg (div_nonneg hρ he.le), div_mul_cancel₀ _ he.ne']

/-- The frontier parameters of `s` and `t`: the entering and exiting parameters of the two strands
through the square `U` are `τ ∓ r/‖e‖`. -/
def θsIn : ℝ := τs D x - discRadius D x ε / ‖es D x‖
def θsOut : ℝ := τs D x + discRadius D x ε / ‖es D x‖
def θtIn : ℝ := τt D x - discRadius D x ε / ‖et D x‖
def θtOut : ℝ := τt D x + discRadius D x ε / ‖et D x‖

theorem θsIn_pos (hε : SmallEps D x ε) : 0 < θsIn D x ε := by
  unfold θsIn
  have hes : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
  have h : discRadius D x ε / ‖es D x‖ < τs D x := by
    rw [div_lt_iff₀ hes]
    linarith [discRadius_lt_r₁ D x ε hε, r₁_le_τs_mul D x]
  linarith
theorem θsOut_lt_one (hε : SmallEps D x ε) : θsOut D x ε < 1 := by
  unfold θsOut
  have hes : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
  have h : discRadius D x ε / ‖es D x‖ < 1 - τs D x := by
    rw [div_lt_iff₀ hes]
    linarith [discRadius_lt_r₁ D x ε hε, r₁_le_one_sub_τs_mul D x]
  linarith
theorem θtIn_pos (hε : SmallEps D x ε) : 0 < θtIn D x ε := by
  unfold θtIn
  have het : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
  have h : discRadius D x ε / ‖et D x‖ < τt D x := by
    rw [div_lt_iff₀ het]
    linarith [discRadius_lt_r₁ D x ε hε, r₁_le_τt_mul D x]
  linarith
theorem θtOut_lt_one (hε : SmallEps D x ε) : θtOut D x ε < 1 := by
  unfold θtOut
  have het : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
  have h : discRadius D x ε / ‖et D x‖ < 1 - τt D x := by
    rw [div_lt_iff₀ het]
    linarith [discRadius_lt_r₁ D x ε hε, r₁_le_one_sub_τt_mul D x]
  linarith
theorem θsIn_lt_θsOut (hε : SmallEps D x ε) : θsIn D x ε < θsOut D x ε := by
  unfold θsIn θsOut
  have hes : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
  have := div_pos (discRadius_pos D x ε hε) hes
  linarith
theorem θtIn_lt_θtOut (hε : SmallEps D x ε) : θtIn D x ε < θtOut D x ε := by
  unfold θtIn θtOut
  have het : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
  have := div_pos (discRadius_pos D x ε hε) het
  linarith

/-- The cut parameters lie strictly inside the frontier parameters:
`θsIn < τs − ε < τs + ε < θsOut` (the cut points are inside the open disc). -/
theorem θsIn_lt_cut (hε : SmallEps D x ε) : θsIn D x ε < τs D x - ε ∧ τs D x + ε < θsOut D x ε := by
  unfold θsIn θsOut
  have hes : 0 < ‖es D x‖ := norm_pos_iff.mpr (es_ne_zero D x)
  have h : ε < discRadius D x ε / ‖es D x‖ := by
    rw [lt_div_iff₀ hes]
    exact (le_max_left _ _).trans_lt (arc_lt_discRadius D x ε hε)
  constructor <;> linarith
theorem θtIn_lt_cut (hε : SmallEps D x ε) : θtIn D x ε < τt D x - ε ∧ τt D x + ε < θtOut D x ε := by
  unfold θtIn θtOut
  have het : 0 < ‖et D x‖ := norm_pos_iff.mpr (et_ne_zero D x)
  have h : ε < discRadius D x ε / ‖et D x‖ := by
    rw [lt_div_iff₀ het]
    exact (le_max_right _ _).trans_lt (arc_lt_discRadius D x ε hε)
  constructor <;> linarith

/-- A point of `s` is in the closed (open) disc iff its parameter lies in `[θsIn, θsOut]`
(`(θsIn, θsOut)`). -/
theorem edgePoint_s_mem_disc_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 θ ∈ disc D x ε ↔
      θsIn D x ε ≤ θ ∧ θ ≤ θsOut D x ε := by
  have hp : pt D x = D.Γ.edgePt (sS D x) (τs D x) := pt_eq_s D x
  exact edgePt_mem_closedBall_iff D x hp (discRadius D x ε) θ

theorem edgePoint_s_mem_ball_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 θ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔
      θsIn D x ε < θ ∧ θ < θsOut D x ε := by
  have hp : pt D x = D.Γ.edgePt (sS D x) (τs D x) := pt_eq_s D x
  exact edgePt_mem_ball_iff D x hp (discRadius D x ε) θ

theorem edgePoint_t_mem_disc_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 θ ∈ disc D x ε ↔
      θtIn D x ε ≤ θ ∧ θ ≤ θtOut D x ε := by
  have hp : pt D x = D.Γ.edgePt (tS D x) (τt D x) := pt_eq_t D x
  exact edgePt_mem_closedBall_iff D x hp (discRadius D x ε) θ

theorem edgePoint_t_mem_ball_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 θ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔
      θtIn D x ε < θ ∧ θ < θtOut D x ε := by
  have hp : pt D x = D.Γ.edgePt (tS D x) (τt D x) := pt_eq_t D x
  exact edgePt_mem_ball_iff D x hp (discRadius D x ε) θ

/-- The frontier parameters on the cut pieces of `Γ₀` (rescaled frontier parameters of `D`). -/
def θ₀sIn : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutStartS (θsIn D x ε)
def θ₀sOut : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutEndS (θsOut D x ε)
def θ₀tIn : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutStartT (θtIn D x ε)
def θ₀tOut : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutEndT (θtOut D x ε)

theorem θ₀_mem (hε : SmallEps D x ε) : θ₀sIn D x ε ∈ Set.Ico (0:ℝ) 1 ∧ θ₀sOut D x ε ∈ Set.Ico (0:ℝ) 1 ∧
    θ₀tIn D x ε ∈ Set.Ico (0:ℝ) 1 ∧ θ₀tOut D x ε ∈ Set.Ico (0:ℝ) 1 := by
  have hs1 := θsIn_pos D x ε hε
  have hs2 := θsOut_lt_one D x ε hε
  have hs3 := θsIn_lt_cut D x ε hε
  have ht1 := θtIn_pos D x ε hε
  have ht2 := θtOut_lt_one D x ε hε
  have ht3 := θtIn_lt_cut D x ε hε
  have hs4 : 0 < τs D x - ε := by linarith [hε.lt_τs]
  have hs5 : 0 < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
  have ht4 : 0 < τt D x - ε := by linarith [hε.lt_τt]
  have ht5 : 0 < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · show 0 ≤ θsIn D x ε / (τs D x - ε)
    exact div_nonneg hs1.le hs4.le
  · show θsIn D x ε / (τs D x - ε) < 1
    rw [div_lt_one hs4]; exact hs3.1
  · show 0 ≤ (θsOut D x ε - τs D x - ε) / (1 - τs D x - ε)
    exact div_nonneg (by linarith [hs3.2]) hs5.le
  · show (θsOut D x ε - τs D x - ε) / (1 - τs D x - ε) < 1
    rw [div_lt_one hs5]; linarith
  · show 0 ≤ θtIn D x ε / (τt D x - ε)
    exact div_nonneg ht1.le ht4.le
  · show θtIn D x ε / (τt D x - ε) < 1
    rw [div_lt_one ht4]; exact ht3.1
  · show 0 ≤ (θtOut D x ε - τt D x - ε) / (1 - τt D x - ε)
    exact div_nonneg (by linarith [ht3.2]) ht5.le
  · show (θtOut D x ε - τt D x - ε) / (1 - τt D x - ε) < 1
    rw [div_lt_one ht5]; linarith

/-- Traversal betweenness on one edge: the points strictly between two points of the same edge in
the cyclic order are the points of that edge with parameter strictly between (accepted
`traversalBetween`, key form). -/
theorem traversalBetween_same_edge {n : ℕ} [NeZero n] (a : ZMod n) (θ₁ θ₂ : Set.Ico (0:ℝ) 1)
    (h : θ₁.val < θ₂.val) (r : TraversalPoint n) :
    traversalBetween (a, θ₁) r (a, θ₂) ↔ r.1 = a ∧ θ₁.val < r.2.val ∧ r.2.val < θ₂.val := by
  obtain ⟨b, θ⟩ := r
  have hθ1 := θ₁.2.1
  have hθ1' := θ₁.2.2
  have hθ2 := θ₂.2.1
  have hθ2' := θ₂.2.2
  have hθ := θ.2.1
  have hθ' := θ.2.2
  simp only [traversalBetween, traversalKey]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have h3 : b.val < a.val + 1 := by
        have : (b.val : ℝ) < a.val + 1 := by linarith
        exact_mod_cast this
      have h4 : a.val < b.val + 1 := by
        have : (a.val : ℝ) < b.val + 1 := by linarith
        exact_mod_cast this
      have hb : b.val = a.val := by omega
      have hab : b = a := ZMod.val_injective n hb
      subst hab
      exact ⟨rfl, by linarith, by linarith⟩
    · exfalso; linarith
    · exfalso; linarith
  · rintro ⟨rfl, h1, h2⟩
    exact Or.inl ⟨by linarith, by linarith⟩

/-- Traversal betweenness across two consecutive edges `m`, `m+2` (used for the smoothing arcs of
`D₀`: start on the cut piece, through the arc, stop on the next cut piece; no wrap). -/
theorem traversalBetween_span_two {n : ℕ} [NeZero n] (m : ZMod n) (hm : m.val + 2 < n)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint n) :
    traversalBetween (m, θ₁) r (m + 2, θ₂) ↔
      (r.1 = m ∧ θ₁.val < r.2.val) ∨ r.1 = m + 1 ∨ (r.1 = m + 2 ∧ r.2.val < θ₂.val) := by
  have h1 : (m + 1).val = m.val + 1 := by
    have : m + 1 = ((m.val + 1 : ℕ) : ZMod n) := by
      rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have h2 : (m + 2).val = m.val + 2 := by
    have : m + 2 = ((m.val + 2 : ℕ) : ZMod n) := by
      rw [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨b, θ⟩ := r
  have hθ1 := θ₁.2.1
  have hθ1' := θ₁.2.2
  have hθ2 := θ₂.2.1
  have hθ2' := θ₂.2.2
  have hθ := θ.2.1
  have hθ' := θ.2.2
  simp only [traversalBetween, traversalKey, h2]
  push_cast
  constructor
  · rintro (⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩)
    · have h5 : m.val < b.val + 1 := by
        have : (m.val : ℝ) < b.val + 1 := by linarith
        exact_mod_cast this
      have h6 : b.val < m.val + 3 := by
        have : (b.val : ℝ) < m.val + 3 := by linarith
        exact_mod_cast this
      rcases (by omega : b.val = m.val ∨ b.val = m.val + 1 ∨ b.val = m.val + 2) with hb | hb | hb
      · have hab : b = m := ZMod.val_injective n hb
        subst hab
        exact Or.inl ⟨rfl, by linarith⟩
      · exact Or.inr (Or.inl (ZMod.val_injective n (hb.trans h1.symm)))
      · have hab : b = m + 2 := ZMod.val_injective n (hb.trans h2.symm)
        subst hab
        refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        rw [h2] at h4
        push_cast at h4
        linarith
    · exfalso; linarith
    · exfalso; linarith
  · rintro (⟨rfl, h3⟩ | rfl | ⟨rfl, h3⟩)
    · exact Or.inl ⟨by linarith, by linarith⟩
    · rw [h1]; push_cast
      exact Or.inl ⟨by linarith, by linarith⟩
    · rw [h2]; push_cast
      exact Or.inl ⟨by linarith, by linarith⟩

/-! ### U2 helpers: traversal points, their strands, and arcs lying on one edge -/

/-- (U2 helper) `eval` as `edgePt` of the carrying strand. -/
theorem eval_eq_edgePt {Γ : Shadow} (q : Γ.Pt) : Γ.eval q = Γ.edgePt ⟨q.1, q.2.1⟩ q.2.2.val := rfl

/-- (U2 helper) `eval q` lies on the closed segment of the strand of `q`. -/
theorem eval_mem_seg {Γ : Shadow} (q : Γ.Pt) : Γ.eval q ∈ Γ.seg ⟨q.1, q.2.1⟩ :=
  ⟨q.2.2.val, q.2.2.2.1, q.2.2.2.2.le, rfl⟩

/-- (U2 helper) A traversal point is its strand together with its parameter. -/
theorem Pt_eq_mk_strand {Γ : Shadow} (q : Γ.Pt) (e : Γ.Strand)
    (h : (⟨q.1, q.2.1⟩ : Γ.Strand) = e) : q = ⟨e.1, (e.2, q.2.2)⟩ := by
  obtain ⟨l, m, θ⟩ := q
  subst h
  rfl

/-- (U2 helper) Traversal points with the same strand and the same parameter are equal. -/
theorem Pt_ext {Γ : Shadow} {q q' : Γ.Pt} (hst : (⟨q.1, q.2.1⟩ : Γ.Strand) = ⟨q'.1, q'.2.1⟩)
    (hθ : q.2.2.val = q'.2.2.val) : q = q' := by
  obtain ⟨l, m, θ⟩ := q
  obtain ⟨l', m', θ'⟩ := q'
  simp only [Sigma.mk.inj_iff] at hst
  obtain ⟨rfl, hm⟩ := hst
  have hm' : m = m' := eq_of_heq hm
  subst hm'
  have hθ' : θ = θ' := Subtype.ext hθ
  subst hθ'
  rfl

/-- (U2 helper) Inner points of an arc whose two ends lie on one edge `m`. -/
theorem arc_inner_iff_of_same_edge {Γ : Shadow} (a : Γ.Arc) (m : ZMod (Γ.comp a.i).k)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (hstart : a.start = (m, θ₁)) (hstop : a.stop = (m, θ₂))
    (h : θ₁.val < θ₂.val) (q : Γ.Pt) :
    a.Inner q ↔ (⟨q.1, q.2.1⟩ : Γ.Strand) = ⟨a.i, m⟩ ∧ θ₁.val < q.2.2.val ∧ q.2.2.val < θ₂.val := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    rw [hstart, hstop, traversalBetween_same_edge _ _ _ h] at hr
    obtain ⟨hr1, hr2, hr3⟩ := hr
    refine ⟨?_, hr2, hr3⟩
    show (⟨a.i, r.1⟩ : Γ.Strand) = ⟨a.i, m⟩
    rw [hr1]
  · rintro ⟨hq, h1, h2⟩
    obtain ⟨θ, rfl⟩ : ∃ θ : Set.Ico (0:ℝ) 1, q = ⟨a.i, (m, θ)⟩ := ⟨q.2.2, Pt_eq_mk_strand q _ hq⟩
    refine ⟨(m, θ), ?_, rfl⟩
    rw [hstart, hstop, traversalBetween_same_edge _ _ _ h]
    exact ⟨rfl, h1, h2⟩

/-- (U2 helper) Points of the closed arc whose two ends lie on one edge `m`. -/
theorem arc_mem_iff_of_same_edge {Γ : Shadow} (a : Γ.Arc) (m : ZMod (Γ.comp a.i).k)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (hstart : a.start = (m, θ₁)) (hstop : a.stop = (m, θ₂))
    (h : θ₁.val < θ₂.val) (q : Γ.Pt) :
    a.Mem q ↔ (⟨q.1, q.2.1⟩ : Γ.Strand) = ⟨a.i, m⟩ ∧ θ₁.val ≤ q.2.2.val ∧ q.2.2.val ≤ θ₂.val := by
  have hs1 : a.start.2.val = θ₁.val := by rw [hstart]
  have hs2 : a.stop.2.val = θ₂.val := by rw [hstop]
  unfold Shadow.Arc.Mem
  rw [arc_inner_iff_of_same_edge a m θ₁ θ₂ hstart hstop h q]
  constructor
  · rintro (rfl | rfl | ⟨hq, h1, h2⟩)
    · refine ⟨?_, hs1.symm.le, ?_⟩
      · show (⟨a.i, a.start.1⟩ : Γ.Strand) = ⟨a.i, m⟩
        rw [hstart]
      · show a.start.2.val ≤ θ₂.val
        rw [hs1]; exact h.le
    · refine ⟨?_, ?_, hs2.le⟩
      · show (⟨a.i, a.stop.1⟩ : Γ.Strand) = ⟨a.i, m⟩
        rw [hstop]
      · show θ₁.val ≤ a.stop.2.val
        rw [hs2]; exact h.le
    · exact ⟨hq, h1.le, h2.le⟩
  · rintro ⟨hq, h1, h2⟩
    obtain ⟨θ, rfl⟩ : ∃ θ : Set.Ico (0:ℝ) 1, q = ⟨a.i, (m, θ)⟩ := ⟨q.2.2, Pt_eq_mk_strand q _ hq⟩
    change θ₁.val ≤ θ.val at h1
    change θ.val ≤ θ₂.val at h2
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · exact Or.inr (Or.inr ⟨rfl, h1, h2⟩)
      · refine Or.inr (Or.inl ?_)
        show (⟨a.i, (m, θ)⟩ : Γ.Pt) = ⟨a.i, a.stop⟩
        rw [hstop, Subtype.ext h2]
    · refine Or.inl ?_
      show (⟨a.i, (m, θ)⟩ : Γ.Pt) = ⟨a.i, a.start⟩
      rw [hstart, Subtype.ext h1]

/-- (U2 helper) The points of an arc of a closed region `U` evaluate into `U`. -/
theorem isArc_eval_mem_of_mem {Γ : Shadow} {U : Set Plane} {a : Γ.Arc} (h : Γ.IsArc U a)
    (hU : IsClosed U) {q : Γ.Pt} (hq : a.Mem q) : Γ.eval q ∈ U := by
  rcases hq with rfl | rfl | hq
  · exact hU.frontier_subset h.start_frontier
  · exact hU.frontier_subset h.stop_frontier
  · exact interior_subset (h.inner_interior _ hq)

section DiscD

variable {ε} (hε : SmallEps D x ε)
include hε

theorem clean_D : Clean (disc D x ε) D := by
  refine ⟨?_, ?_⟩
  · intro q hq q' hq' heq
    have hq1 : D.Γ.eval q ∈ Metric.sphere (pt D x) (discRadius D x ε) := by
      rw [← frontier_disc D x ε hε]; exact hq
    have hq1' : D.Γ.eval q' ∈ Metric.sphere (pt D x) (discRadius D x ε) := by
      rw [← frontier_disc D x ε hε]; exact hq'
    have hU : D.Γ.eval q ∈ disc D x ε := Metric.sphere_subset_closedBall hq1
    have hU' : D.Γ.eval q' ∈ disc D x ε := Metric.sphere_subset_closedBall hq1'
    have hs := mem_seg_of_mem_disc D x ε hε (eval_mem_seg q) hU
    have hs' := mem_seg_of_mem_disc D x ε hε (eval_mem_seg q') hU'
    -- on the same strand: the parameters agree (`edgePt_injective`)
    have same : ∀ e : D.Γ.Strand, (⟨q.1, q.2.1⟩ : D.Γ.Strand) = e →
        (⟨q'.1, q'.2.1⟩ : D.Γ.Strand) = e → q = q' := by
      intro e he he'
      refine Pt_ext (he.trans he'.symm) ?_
      rw [eval_eq_edgePt, eval_eq_edgePt, he, he'] at heq
      exact D.generic.edgePt_injective e heq
    -- on `s` and `t`: the common point is `p`, which is not on the sphere
    have cross : ∀ e e' : D.Γ.Strand, e ∈ x.val → e' ∈ x.val → e ≠ e' →
        (⟨q.1, q.2.1⟩ : D.Γ.Strand) = e → (⟨q'.1, q'.2.1⟩ : D.Γ.Strand) = e' → False := by
      intro e e' he he' hee' hqe hqe'
      have h1 : D.Γ.eval q ∈ D.Γ.seg e := by rw [← hqe]; exact eval_mem_seg q
      have h2 : D.Γ.eval q ∈ D.Γ.seg e' := by rw [heq, ← hqe']; exact eval_mem_seg q'
      have h3 : D.Γ.eval q ∈ D.Γ.seg e ∩ D.Γ.seg e' := ⟨h1, h2⟩
      rw [D.generic.seg_inter_seg_eq x he he' hee', Set.mem_singleton_iff] at h3
      have h4 : dist (D.Γ.eval q) (pt D x) = discRadius D x ε := Metric.mem_sphere.mp hq1
      rw [h3] at h4
      change dist (pt D x) (pt D x) = discRadius D x ε at h4
      rw [dist_self] at h4
      exact (discRadius_pos D x ε hε).ne h4
    rcases hs with hs | hs <;> rcases hs' with hs' | hs'
    · exact same _ hs hs'
    · exact (cross _ _ (D.over_mem x) (D.under_mem x) (sS_ne_tS D x) hs hs').elim
    · exact (cross _ _ (D.under_mem x) (D.over_mem x) (sS_ne_tS D x).symm hs hs').elim
    · exact same _ hs hs'
  · intro i
    refine ⟨(0, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
    have h0 : D.Γ.eval ⟨i, (0, ⟨0, le_rfl, zero_lt_one⟩)⟩ = D.Γ.tail ⟨i, 0⟩ :=
      D.Γ.edgePt_zero ⟨i, 0⟩
    rw [h0]
    exact tail_not_mem_disc D x ε hε _

theorem center_mem : pt D x ∈ interior (disc D x ε) := by
  rw [interior_disc D x ε hε]
  exact Metric.mem_ball_self (discRadius_pos D x ε hε)

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

/-- (U2 helper) Points of `arcS`: on `s` with parameter in `[θsIn, θsOut]`. -/
theorem mem_arcS_iff (q : D.Γ.Pt) :
    (arcS D x hε).Mem q ↔ (⟨q.1, q.2.1⟩ : D.Γ.Strand) = sS D x ∧
      θsIn D x ε ≤ q.2.2.val ∧ q.2.2.val ≤ θsOut D x ε :=
  arc_mem_iff_of_same_edge (arcS D x hε) (sS D x).2 _ _ rfl rfl (θsIn_lt_θsOut D x ε hε) q

/-- (U2 helper) Points of `arcT`: on `t` with parameter in `[θtIn, θtOut]`. -/
theorem mem_arcT_iff (q : D.Γ.Pt) :
    (arcT D x hε).Mem q ↔ (⟨q.1, q.2.1⟩ : D.Γ.Strand) = tS D x ∧
      θtIn D x ε ≤ q.2.2.val ∧ q.2.2.val ≤ θtOut D x ε :=
  arc_mem_iff_of_same_edge (arcT D x hε) (tS D x).2 _ _ rfl rfl (θtIn_lt_θtOut D x ε hε) q

/-- (U2 helper) Inner points of `arcS`. -/
theorem inner_arcS_iff (q : D.Γ.Pt) :
    (arcS D x hε).Inner q ↔ (⟨q.1, q.2.1⟩ : D.Γ.Strand) = sS D x ∧
      θsIn D x ε < q.2.2.val ∧ q.2.2.val < θsOut D x ε :=
  arc_inner_iff_of_same_edge (arcS D x hε) (sS D x).2 _ _ rfl rfl (θsIn_lt_θsOut D x ε hε) q

/-- (U2 helper) Inner points of `arcT`. -/
theorem inner_arcT_iff (q : D.Γ.Pt) :
    (arcT D x hε).Inner q ↔ (⟨q.1, q.2.1⟩ : D.Γ.Strand) = tS D x ∧
      θtIn D x ε < q.2.2.val ∧ q.2.2.val < θtOut D x ε :=
  arc_inner_iff_of_same_edge (arcT D x hε) (tS D x).2 _ _ rfl rfl (θtIn_lt_θtOut D x ε hε) q

/-- (U2 helper) `arcS` is an arc of the disc. -/
theorem isArc_arcS : D.Γ.IsArc (disc D x ε) (arcS D x hε) := by
  have hp : pt D x = D.Γ.edgePt (sS D x) (τs D x) := pt_eq_s D x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun r : TraversalPoint (D.Γ.comp (arcS D x hε).i).k => r.2.val) h
    exact (θsIn_lt_θsOut D x ε hε).ne this
  · rw [frontier_disc D x ε hε]
    exact edgePt_mem_sphere D x hp (discRadius_pos D x ε hε).le (θsIn D x ε) (Or.inl rfl)
  · rw [frontier_disc D x ε hε]
    exact edgePt_mem_sphere D x hp (discRadius_pos D x ε hε).le (θsOut D x ε) (Or.inr rfl)
  · intro q hq
    rw [inner_arcS_iff D x hε] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    rw [interior_disc D x ε hε, eval_eq_edgePt, hq1]
    exact (edgePt_mem_ball_iff D x hp _ _).mpr ⟨hq2, hq3⟩

/-- (U2 helper) `arcT` is an arc of the disc. -/
theorem isArc_arcT : D.Γ.IsArc (disc D x ε) (arcT D x hε) := by
  have hp : pt D x = D.Γ.edgePt (tS D x) (τt D x) := pt_eq_t D x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun r : TraversalPoint (D.Γ.comp (arcT D x hε).i).k => r.2.val) h
    exact (θtIn_lt_θtOut D x ε hε).ne this
  · rw [frontier_disc D x ε hε]
    exact edgePt_mem_sphere D x hp (discRadius_pos D x ε hε).le (θtIn D x ε) (Or.inl rfl)
  · rw [frontier_disc D x ε hε]
    exact edgePt_mem_sphere D x hp (discRadius_pos D x ε hε).le (θtOut D x ε) (Or.inr rfl)
  · intro q hq
    rw [inner_arcT_iff D x hε] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    rw [interior_disc D x ε hε, eval_eq_edgePt, hq1]
    exact (edgePt_mem_ball_iff D x hp _ _).mpr ⟨hq2, hq3⟩

theorem arcS_ne_arcT : arcS D x hε ≠ arcT D x hε := by
  intro h
  have h1 := (mem_arcS_iff D x hε _).mp (Shadow.Arc.startPt_mem (arcS D x hε))
  have h2 : (arcT D x hε).Mem (arcS D x hε).startPt := by
    rw [← h]; exact Shadow.Arc.startPt_mem _
  have h3 := (mem_arcT_iff D x hε _).mp h2
  exact sS_ne_tS D x (h1.1.symm.trans h3.1)

theorem arcCover_D : D.Γ.ArcCover (disc D x ε) {arcS D x hε, arcT D x hε} := by
  have hclosed : IsClosed (disc D x ε) := Metric.isClosed_closedBall
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact isArc_arcS D x hε
    · exact isArc_arcT D x hε
  · intro q
    constructor
    · intro hq
      rcases mem_seg_of_mem_disc D x ε hε (eval_mem_seg q) hq with hs | hs
      · refine ⟨arcS D x hε, by simp, ?_⟩
        rw [mem_arcS_iff D x hε]
        refine ⟨hs, ?_⟩
        rw [eval_eq_edgePt, hs] at hq
        exact (edgePoint_s_mem_disc_iff D x ε hε _).mp hq
      · refine ⟨arcT D x hε, by simp, ?_⟩
        rw [mem_arcT_iff D x hε]
        refine ⟨hs, ?_⟩
        rw [eval_eq_edgePt, hs] at hq
        exact (edgePoint_t_mem_disc_iff D x ε hε _).mp hq
    · rintro ⟨a, ha, hq⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact isArc_eval_mem_of_mem (isArc_arcS D x hε) hclosed hq
      · exact isArc_eval_mem_of_mem (isArc_arcT D x hε) hclosed hq
  · intro a ha b hb hab q hqa hqb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    have key : ∀ q, (arcS D x hε).Mem q → (arcT D x hε).Mem q → False := fun q h1 h2 =>
      sS_ne_tS D x (((mem_arcS_iff D x hε q).mp h1).1.symm.trans
        ((mem_arcT_iff D x hε q).mp h2).1)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab rfl
    · exact key q hqa hqb
    · exact key q hqb hqa
    · exact hab rfl

theorem overOn_arcS : D.OverOn (arcS D x hε) x := by
  unfold Diagram.OverOn
  rw [mem_arcS_iff D x hε]
  have h := θsIn_lt_cut D x ε hε
  have h0 := hε.pos
  refine ⟨rfl, ?_, ?_⟩
  · show θsIn D x ε ≤ τs D x
    linarith [h.1]
  · show τs D x ≤ θsOut D x ε
    linarith [h.2]

theorem underOn_arcT : D.UnderOn (arcT D x hε) x := by
  unfold Diagram.UnderOn
  rw [mem_arcT_iff D x hε]
  have h := θtIn_lt_cut D x ε hε
  have h0 := hε.pos
  refine ⟨rfl, ?_, ?_⟩
  · show θtIn D x ε ≤ τt D x
    linarith [h.1]
  · show τt D x ≤ θtOut D x ε
    linarith [h.2]

theorem inner_iff_D (y : D.Γ.Crossing) : D.Γ.crossingPoint y ∈ interior (disc D x ε) ↔ y = x := by
  constructor
  · intro h
    by_contra hy
    exact crossingPoint_ne_not_mem_disc D x ε hε hy (interior_subset h)
  · intro h
    rw [h]
    exact center_mem D x hε

end DiscD

/-! ## 6. Model-level geometry

Everything in this section is stated for an arbitrary splice model `M : SpliceModel D x ε Γ₀` with
`hε : SmallEps D x ε`. -/

section Model

variable {ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
include M hε

/-! ### 6a. Genericity of the spliced shadow -/

/-! #### U3 helpers: coordinates of the six new kinds in the basis `(es, et)` about `p` -/

omit M hε in
theorem u3_cutStartS_pt (θ : ℝ) :
    (StrandKind.cutStartS : StrandKind D x).tail ε + θ • (StrandKind.cutStartS : StrandKind D x).dir ε =
      pt D x + (θ * (τs D x - ε) - τs D x) • es D x + (0:ℝ) • et D x := by
  simp only [StrandKind.tail, StrandKind.dir]
  rw [pt_eq_s D x]
  module

omit M hε in
theorem u3_cutEndS_pt (θ : ℝ) :
    (StrandKind.cutEndS : StrandKind D x).tail ε + θ • (StrandKind.cutEndS : StrandKind D x).dir ε =
      pt D x + (ε + θ * (1 - τs D x - ε)) • es D x + (0:ℝ) • et D x := by
  simp only [StrandKind.tail, StrandKind.dir, sPlus]
  module

omit M hε in
theorem u3_cutStartT_pt (θ : ℝ) :
    (StrandKind.cutStartT : StrandKind D x).tail ε + θ • (StrandKind.cutStartT : StrandKind D x).dir ε =
      pt D x + (0:ℝ) • es D x + (θ * (τt D x - ε) - τt D x) • et D x := by
  simp only [StrandKind.tail, StrandKind.dir]
  rw [pt_eq_t D x]
  module

omit M hε in
theorem u3_cutEndT_pt (θ : ℝ) :
    (StrandKind.cutEndT : StrandKind D x).tail ε + θ • (StrandKind.cutEndT : StrandKind D x).dir ε =
      pt D x + (0:ℝ) • es D x + (ε + θ * (1 - τt D x - ε)) • et D x := by
  simp only [StrandKind.tail, StrandKind.dir, tPlus]
  module

omit M hε in
theorem u3_arcST_pt (θ : ℝ) :
    (StrandKind.arcST : StrandKind D x).tail ε + θ • (StrandKind.arcST : StrandKind D x).dir ε =
      pt D x + ((θ - 1) * ε) • es D x + (θ * ε) • et D x := by
  simp only [StrandKind.tail, StrandKind.dir, sMinus]
  module

omit M hε in
theorem u3_arcTS_pt (θ : ℝ) :
    (StrandKind.arcTS : StrandKind D x).tail ε + θ • (StrandKind.arcTS : StrandKind D x).dir ε =
      pt D x + (θ * ε) • es D x + ((θ - 1) * ε) • et D x := by
  simp only [StrandKind.tail, StrandKind.dir, tMinus]
  module

omit M hε in
/-- Coordinates about `p` in the basis `(es, et)` are unique. -/
theorem u3_coords_eq {α β α' β' : ℝ}
    (h : pt D x + α • es D x + β • et D x = pt D x + α' • es D x + β' • et D x) : α = α' ∧ β = β' := by
  apply coords_unique (det_es_et_ne_zero D x)
  rw [add_assoc, add_assoc] at h
  exact add_left_cancel h

omit M hε in
theorem u3_tail_mem_seg (κ : StrandKind D x) : κ.tail ε ∈ κ.seg ε :=
  ⟨0, le_rfl, zero_le_one, by rw [zero_smul, add_zero]⟩

omit M hε in
theorem u3_interior_subset_seg (κ : StrandKind D x) : κ.interior ε ⊆ κ.seg ε :=
  fun _ ⟨θ, h0, h1, hq⟩ => ⟨θ, h0.le, h1.le, hq⟩

/-! #### U3 helpers: the eleven non-adjacent pairs of new kinds have disjoint segments -/

omit M in
theorem u3_disj_SS : Disjoint ((StrandKind.cutStartS : StrandKind D x).seg ε)
    ((StrandKind.cutEndS : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨θ', h0', h1', h⟩
  rw [u3_cutStartS_pt, u3_cutEndS_pt] at h
  obtain ⟨h₁, -⟩ := u3_coords_eq D x h
  have e1 : θ * (τs D x - ε) ≤ τs D x - ε := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τs).le h1
  have e2 : 0 ≤ θ' * (1 - τs D x - ε) := mul_nonneg h0' (by linarith [hε.lt_one_sub_τs])
  linarith [hε.pos]

omit M in
theorem u3_disj_TT : Disjoint ((StrandKind.cutStartT : StrandKind D x).seg ε)
    ((StrandKind.cutEndT : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨θ', h0', h1', h⟩
  rw [u3_cutStartT_pt, u3_cutEndT_pt] at h
  obtain ⟨-, h₂⟩ := u3_coords_eq D x h
  have e1 : θ * (τt D x - ε) ≤ τt D x - ε := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τt).le h1
  have e2 : 0 ≤ θ' * (1 - τt D x - ε) := mul_nonneg h0' (by linarith [hε.lt_one_sub_τt])
  linarith [hε.pos]

omit M in
theorem u3_disj_cutStartS_cutStartT : Disjoint ((StrandKind.cutStartS : StrandKind D x).seg ε)
    ((StrandKind.cutStartT : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨θ', h0', h1', h⟩
  rw [u3_cutStartS_pt, u3_cutStartT_pt] at h
  obtain ⟨h₁, -⟩ := u3_coords_eq D x h
  have e1 : θ * (τs D x - ε) ≤ τs D x - ε := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τs).le h1
  linarith [hε.pos]

omit M in
theorem u3_disj_cutStartS_cutEndT : Disjoint ((StrandKind.cutStartS : StrandKind D x).seg ε)
    ((StrandKind.cutEndT : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨θ', h0', h1', h⟩
  rw [u3_cutStartS_pt, u3_cutEndT_pt] at h
  obtain ⟨h₁, -⟩ := u3_coords_eq D x h
  have e1 : θ * (τs D x - ε) ≤ τs D x - ε := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τs).le h1
  linarith [hε.pos]

omit M in
theorem u3_disj_cutEndS_cutStartT : Disjoint ((StrandKind.cutEndS : StrandKind D x).seg ε)
    ((StrandKind.cutStartT : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨θ', h0', h1', h⟩
  rw [u3_cutEndS_pt, u3_cutStartT_pt] at h
  obtain ⟨h₁, -⟩ := u3_coords_eq D x h
  have e2 : 0 ≤ θ * (1 - τs D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τs])
  linarith [hε.pos]

omit M in
theorem u3_disj_cutEndS_cutEndT : Disjoint ((StrandKind.cutEndS : StrandKind D x).seg ε)
    ((StrandKind.cutEndT : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨θ', h0', h1', h⟩
  rw [u3_cutEndS_pt, u3_cutEndT_pt] at h
  obtain ⟨h₁, -⟩ := u3_coords_eq D x h
  have e2 : 0 ≤ θ * (1 - τs D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τs])
  linarith [hε.pos]

omit M in
theorem u3_disj_cutStartS_arcTS : Disjoint ((StrandKind.cutStartS : StrandKind D x).seg ε)
    ((StrandKind.arcTS : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨μ, h0', h1', h⟩
  rw [u3_cutStartS_pt, u3_arcTS_pt] at h
  obtain ⟨h₁, h₂⟩ := u3_coords_eq D x h
  have hμ : μ = 1 := by
    have := (mul_eq_zero.mp h₂.symm).resolve_right hε.pos.ne'
    linarith
  subst hμ
  have e1 : θ * (τs D x - ε) ≤ τs D x - ε := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τs).le h1
  linarith [hε.pos]

omit M in
theorem u3_disj_cutEndS_arcST : Disjoint ((StrandKind.cutEndS : StrandKind D x).seg ε)
    ((StrandKind.arcST : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨μ, h0', h1', h⟩
  rw [u3_cutEndS_pt, u3_arcST_pt] at h
  obtain ⟨h₁, h₂⟩ := u3_coords_eq D x h
  have hμ : μ = 0 := (mul_eq_zero.mp h₂.symm).resolve_right hε.pos.ne'
  subst hμ
  have e2 : 0 ≤ θ * (1 - τs D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τs])
  linarith [hε.pos]

omit M in
theorem u3_disj_cutStartT_arcST : Disjoint ((StrandKind.cutStartT : StrandKind D x).seg ε)
    ((StrandKind.arcST : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨μ, h0', h1', h⟩
  rw [u3_cutStartT_pt, u3_arcST_pt] at h
  obtain ⟨h₁, h₂⟩ := u3_coords_eq D x h
  have hμ : μ = 1 := by
    have := (mul_eq_zero.mp h₁.symm).resolve_right hε.pos.ne'
    linarith
  subst hμ
  have e1 : θ * (τt D x - ε) ≤ τt D x - ε := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τt).le h1
  linarith [hε.pos]

omit M in
theorem u3_disj_cutEndT_arcTS : Disjoint ((StrandKind.cutEndT : StrandKind D x).seg ε)
    ((StrandKind.arcTS : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, rfl⟩ ⟨μ, h0', h1', h⟩
  rw [u3_cutEndT_pt, u3_arcTS_pt] at h
  obtain ⟨h₁, h₂⟩ := u3_coords_eq D x h
  have hμ : μ = 0 := (mul_eq_zero.mp h₁.symm).resolve_right hε.pos.ne'
  subst hμ
  have e2 : 0 ≤ θ * (1 - τt D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τt])
  linarith [hε.pos]

omit M in
theorem u3_disj_arcST_arcTS : Disjoint ((StrandKind.arcST : StrandKind D x).seg ε)
    ((StrandKind.arcTS : StrandKind D x).seg ε) := by
  rw [Set.disjoint_left]
  rintro q ⟨μ, h0, h1, rfl⟩ ⟨ν, h0', h1', h⟩
  rw [u3_arcST_pt, u3_arcTS_pt] at h
  obtain ⟨h₁, h₂⟩ := u3_coords_eq D x h
  have : ε = 0 := by linarith
  exact hε.pos.ne' this

omit M in
/-- Non-adjacent kinds that are not both old have disjoint segments, except an old strand meeting a
cut piece at a crossing of `D` (cut pieces of one strand are disjoint; cut pieces of `s` and `t`
are disjoint since their only common point `p` is cut away; arcs are disjoint from each other and
from the cut pieces they are not adjacent to, by independence of `es`, `et`; arcs are disjoint from
old strands by the clearance radius). -/
theorem kind_disjoint (κ κ' : StrandKind D x) (hκ : ¬ ∃ e, κ = StrandKind.old e)
    (hadj : ¬ κ.Adj κ') (hold : ∀ e, κ' = StrandKind.old e → False) :
    Disjoint (κ.seg ε) (κ'.seg ε) := by
  cases κ <;> cases κ' <;> first
    | exact (hκ ⟨_, rfl⟩).elim
    | exact (hold _ rfl).elim
    | (exfalso; apply hadj; simp [StrandKind.Adj, StrandKind.succ, StrandKind.pred]; done)
    | exact u3_disj_SS D x hε
    | exact (u3_disj_SS D x hε).symm
    | exact u3_disj_TT D x hε
    | exact (u3_disj_TT D x hε).symm
    | exact u3_disj_cutStartS_cutStartT D x hε
    | exact (u3_disj_cutStartS_cutStartT D x hε).symm
    | exact u3_disj_cutStartS_cutEndT D x hε
    | exact (u3_disj_cutStartS_cutEndT D x hε).symm
    | exact u3_disj_cutEndS_cutStartT D x hε
    | exact (u3_disj_cutEndS_cutStartT D x hε).symm
    | exact u3_disj_cutEndS_cutEndT D x hε
    | exact (u3_disj_cutEndS_cutEndT D x hε).symm
    | exact u3_disj_cutStartS_arcTS D x hε
    | exact (u3_disj_cutStartS_arcTS D x hε).symm
    | exact u3_disj_cutEndS_arcST D x hε
    | exact (u3_disj_cutEndS_arcST D x hε).symm
    | exact u3_disj_cutStartT_arcST D x hε
    | exact (u3_disj_cutStartT_arcST D x hε).symm
    | exact u3_disj_cutEndT_arcTS D x hε
    | exact (u3_disj_cutEndT_arcTS D x hε).symm
    | exact u3_disj_arcST_arcTS D x hε
    | exact (u3_disj_arcST_arcTS D x hε).symm

/-! #### U3 helpers: index bookkeeping on strands of `D` -/

omit M hε in
theorem u3_occurs_old_iff {e : D.Γ.Strand} :
    (StrandKind.old e : StrandKind D x).Occurs ↔ e ≠ sS D x ∧ e ≠ tS D x := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by rw [h]), fun h => h2 (by rw [h])⟩
  · rintro ⟨h1, h2⟩
    exact StrandKind.occurs_old h1 h2

omit M hε in
theorem u3_strand_pred_eq (u v : D.Γ.Strand) (h : u = ⟨v.1, v.2 + 1⟩) : (⟨u.1, u.2 - 1⟩ : D.Γ.Strand) = v := by
  subst h; simp

omit M hε in
theorem u3_strand_succ_eq (u v : D.Γ.Strand) (h : u = ⟨v.1, v.2 - 1⟩) : (⟨u.1, u.2 + 1⟩ : D.Γ.Strand) = v := by
  subst h; simp

omit M hε in
theorem u3_succ_ne_succ_of_ne (u v : D.Γ.Strand) (h : u ≠ v) :
    (⟨u.1, u.2 + 1⟩ : D.Γ.Strand) ≠ ⟨v.1, v.2 + 1⟩ := fun heq => by
  have := u3_strand_pred_eq D _ _ heq
  simp only [add_sub_cancel_right, Sigma.eta] at this
  exact h this

omit M hε in
theorem u3_adjacent_of_eq_pred (e f : D.Γ.Strand) (h : e = ⟨f.1, f.2 - 1⟩) : D.Γ.Adjacent e f := by
  subst h
  exact ⟨f.1, f.2 - 1, f.2, rfl, rfl, Or.inr (Or.inr (by ring))⟩

omit M hε in
theorem u3_adjacent_of_eq_succ (e f : D.Γ.Strand) (h : e = ⟨f.1, f.2 + 1⟩) : D.Γ.Adjacent e f := by
  subst h
  exact ⟨f.1, f.2 + 1, f.2, rfl, rfl, Or.inl (by ring)⟩

omit M hε in
/-- A vertex of `D` on an edge of `D` is one of its two endpoints (`tail_off`). -/
theorem u3_eq_or_eq_succ_of_tail_mem_seg (e f : D.Γ.Strand) (hm : D.Γ.tail e ∈ D.Γ.seg f) :
    e = f ∨ e = ⟨f.1, f.2 + 1⟩ := by
  by_contra hne
  rw [not_or] at hne
  refine D.generic.tail_off e f ?_ hm
  rintro ⟨i, a, b, rfl, rfl, hab⟩
  rcases hab with rfl | rfl
  · exact hne.2 (by simp)
  · exact hne.1 rfl

/-! #### U3 helpers: the cut pieces avoid the adjacent old strand they do not touch -/

omit M in
theorem u3_cutEndS_disj_pred :
    Disjoint ((StrandKind.cutEndS : StrandKind D x).seg ε) (D.Γ.seg ⟨(sS D x).1, (sS D x).2 - 1⟩) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, hq⟩ hqe
  have hq' : q ∈ D.Γ.seg (sS D x) :=
    StrandKind.seg_subset_seg_orig ε hε StrandKind.cutEndS (by simp) (by simp) ⟨θ, h0, h1, hq⟩
  have hmem : q ∈ D.Γ.seg ⟨(sS D x).1, (sS D x).2 - 1⟩ ∩
      D.Γ.seg ⟨(sS D x).1, (sS D x).2 - 1 + 1⟩ := ⟨hqe, by rw [sub_add_cancel]; exact hq'⟩
  rw [D.generic.seg_inter_succ, Set.mem_singleton_iff] at hmem
  have hhead : D.Γ.head ⟨(sS D x).1, (sS D x).2 - 1⟩ = D.Γ.edgePt (sS D x) 0 := by
    rw [D.Γ.edgePt_zero]
    show (D.Γ.comp (sS D x).1).P ((sS D x).2 - 1 + 1) = (D.Γ.comp (sS D x).1).P (sS D x).2
    rw [sub_add_cancel]
  rw [hhead, hq, StrandKind.tail_add_smul_dir ε StrandKind.cutEndS (by simp) (by simp)] at hmem
  have h := D.generic.edgePt_injective (sS D x) hmem
  simp only [StrandKind.origParam] at h
  have : 0 ≤ θ * (1 - τs D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τs])
  linarith [τs_pos D x, hε.pos]

omit M in
theorem u3_cutEndT_disj_pred :
    Disjoint ((StrandKind.cutEndT : StrandKind D x).seg ε) (D.Γ.seg ⟨(tS D x).1, (tS D x).2 - 1⟩) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, hq⟩ hqe
  have hq' : q ∈ D.Γ.seg (tS D x) :=
    StrandKind.seg_subset_seg_orig ε hε StrandKind.cutEndT (by simp) (by simp) ⟨θ, h0, h1, hq⟩
  have hmem : q ∈ D.Γ.seg ⟨(tS D x).1, (tS D x).2 - 1⟩ ∩
      D.Γ.seg ⟨(tS D x).1, (tS D x).2 - 1 + 1⟩ := ⟨hqe, by rw [sub_add_cancel]; exact hq'⟩
  rw [D.generic.seg_inter_succ, Set.mem_singleton_iff] at hmem
  have hhead : D.Γ.head ⟨(tS D x).1, (tS D x).2 - 1⟩ = D.Γ.edgePt (tS D x) 0 := by
    rw [D.Γ.edgePt_zero]
    show (D.Γ.comp (tS D x).1).P ((tS D x).2 - 1 + 1) = (D.Γ.comp (tS D x).1).P (tS D x).2
    rw [sub_add_cancel]
  rw [hhead, hq, StrandKind.tail_add_smul_dir ε StrandKind.cutEndT (by simp) (by simp)] at hmem
  have h := D.generic.edgePt_injective (tS D x) hmem
  simp only [StrandKind.origParam] at h
  have : 0 ≤ θ * (1 - τt D x - ε) := mul_nonneg h0 (by linarith [hε.lt_one_sub_τt])
  linarith [τt_pos D x, hε.pos]

omit M in
theorem u3_cutStartS_disj_succ :
    Disjoint ((StrandKind.cutStartS : StrandKind D x).seg ε) (D.Γ.seg ⟨(sS D x).1, (sS D x).2 + 1⟩) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, hq⟩ hqe
  have hq' : q ∈ D.Γ.seg (sS D x) :=
    StrandKind.seg_subset_seg_orig ε hε StrandKind.cutStartS (by simp) (by simp) ⟨θ, h0, h1, hq⟩
  have hmem : q ∈ D.Γ.seg (sS D x) ∩ D.Γ.seg ⟨(sS D x).1, (sS D x).2 + 1⟩ := ⟨hq', hqe⟩
  rw [D.generic.seg_inter_succ, Set.mem_singleton_iff, ← D.Γ.edgePt_one, hq,
    StrandKind.tail_add_smul_dir ε StrandKind.cutStartS (by simp) (by simp)] at hmem
  have h := D.generic.edgePt_injective (sS D x) hmem
  simp only [StrandKind.origParam] at h
  have := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τs).le h1
  linarith [τs_lt_one D x, hε.pos]

omit M in
theorem u3_cutStartT_disj_succ :
    Disjoint ((StrandKind.cutStartT : StrandKind D x).seg ε) (D.Γ.seg ⟨(tS D x).1, (tS D x).2 + 1⟩) := by
  rw [Set.disjoint_left]
  rintro q ⟨θ, h0, h1, hq⟩ hqe
  have hq' : q ∈ D.Γ.seg (tS D x) :=
    StrandKind.seg_subset_seg_orig ε hε StrandKind.cutStartT (by simp) (by simp) ⟨θ, h0, h1, hq⟩
  have hmem : q ∈ D.Γ.seg (tS D x) ∩ D.Γ.seg ⟨(tS D x).1, (tS D x).2 + 1⟩ := ⟨hq', hqe⟩
  rw [D.generic.seg_inter_succ, Set.mem_singleton_iff, ← D.Γ.edgePt_one, hq,
    StrandKind.tail_add_smul_dir ε StrandKind.cutStartT (by simp) (by simp)] at hmem
  have h := D.generic.edgePt_injective (tS D x) hmem
  simp only [StrandKind.origParam] at h
  have := mul_le_of_le_one_left (sub_pos.mpr hε.lt_τt).le h1
  linarith [τt_lt_one D x, hε.pos]

omit M in
/-- A cut piece meets an old strand `e ≠ s, t` only if `e` is non-adjacent to the original strand
(so the meeting is a crossing of `D`); adjacent old strands `s ∓ 1` meet only the piece they touch,
at the common vertex. -/
theorem cut_inter_old (κ : StrandKind D x) (hκ : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS)
    (hκo : ¬ ∃ e, κ = StrandKind.old e) (e : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x)
    (hmeet : (κ.seg ε ∩ D.Γ.seg e).Nonempty) (hadj : ¬ κ.Adj (StrandKind.old e)) :
    ¬ D.Γ.Adjacent κ.orig e := by
  intro hA
  obtain ⟨i, a, b, ho, hev, hab⟩ := hA
  obtain ⟨q, hq, hqe⟩ := hmeet
  unfold StrandKind.Adj at hadj
  rcases hab with h1 | h1 | h1
  · have hb : b = a - 1 := by linear_combination h1
    subst hb
    have he' : e = ⟨κ.orig.1, κ.orig.2 - 1⟩ := by rw [hev, ho]
    rw [he'] at hqe
    cases κ with
    | old e' => exact hκo ⟨_, rfl⟩
    | cutStartS => exact hadj (Or.inr (Or.inr (by rw [he']; rfl)))
    | cutEndS => exact Set.disjoint_left.mp (u3_cutEndS_disj_pred D x hε) hq hqe
    | cutStartT => exact hadj (Or.inr (Or.inr (by rw [he']; rfl)))
    | cutEndT => exact Set.disjoint_left.mp (u3_cutEndT_disj_pred D x hε) hq hqe
    | arcST => exact hκ.1 rfl
    | arcTS => exact hκ.2 rfl
  · have hb : b = a := sub_eq_zero.mp h1
    subst hb
    have he' : e = κ.orig := by rw [hev, ho]
    cases κ with
    | old e' => exact hκo ⟨_, rfl⟩
    | cutStartS => exact he.1 he'
    | cutEndS => exact he.1 he'
    | cutStartT => exact he.2 he'
    | cutEndT => exact he.2 he'
    | arcST => exact hκ.1 rfl
    | arcTS => exact hκ.2 rfl
  · have hb : b = a + 1 := by linear_combination h1
    subst hb
    have he' : e = ⟨κ.orig.1, κ.orig.2 + 1⟩ := by rw [hev, ho]
    rw [he'] at hqe
    cases κ with
    | old e' => exact hκo ⟨_, rfl⟩
    | cutStartS => exact Set.disjoint_left.mp (u3_cutStartS_disj_succ D x hε) hq hqe
    | cutEndS => exact hadj (Or.inr (Or.inl (by rw [he']; rfl)))
    | cutStartT => exact Set.disjoint_left.mp (u3_cutStartT_disj_succ D x hε) hq hqe
    | cutEndT => exact hadj (Or.inr (Or.inl (by rw [he']; rfl)))
    | arcST => exact hκ.1 rfl
    | arcTS => exact hκ.2 rfl

omit M in
/-- The corner between the predecessor kind and a kind is regular. -/
theorem u3_regularPair_pred_dir (κ : StrandKind D x) (hκ : κ.Occurs) :
    RegularPair (κ.pred.dir ε) (κ.dir ε) := by
  have hdet := det_es_et_ne_zero D x
  have hdet' : det (et D x) (es D x) ≠ 0 := by rw [det_swap]; exact neg_ne_zero.mpr hdet
  have h1 : (0:ℝ) < τs D x - ε := sub_pos.mpr hε.lt_τs
  have h2 : (0:ℝ) < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
  have h3 : (0:ℝ) < τt D x - ε := sub_pos.mpr hε.lt_τt
  have h4 : (0:ℝ) < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
  cases κ with
  | old e =>
    simp only [StrandKind.pred]
    split_ifs with hs ht
    · subst hs
      simp only [StrandKind.dir]
      have h := D.generic.regular (sS D x).1 ((sS D x).2 + 1)
      rw [add_sub_cancel_right] at h
      have h' := regularPair_smul_pos h2 one_pos h
      rw [one_smul] at h'
      exact h'
    · subst ht
      simp only [StrandKind.dir]
      have h := D.generic.regular (tS D x).1 ((tS D x).2 + 1)
      rw [add_sub_cancel_right] at h
      have h' := regularPair_smul_pos h4 one_pos h
      rw [one_smul] at h'
      exact h'
    · simp only [StrandKind.dir]
      exact D.generic.regular e.1 e.2
  | cutStartS =>
    simp only [StrandKind.pred, StrandKind.dir]
    have h' := regularPair_smul_pos one_pos h1 (D.generic.regular (sS D x).1 (sS D x).2)
    rw [one_smul] at h'
    exact h'
  | cutEndS =>
    simp only [StrandKind.pred, StrandKind.dir]
    have h' := regularPair_smul_pos hε.pos one_pos (regularPair_add_left_of_det_ne_zero hdet' h2)
    rw [one_smul, add_comm] at h'
    exact h'
  | cutStartT =>
    simp only [StrandKind.pred, StrandKind.dir]
    have h' := regularPair_smul_pos one_pos h3 (D.generic.regular (tS D x).1 (tS D x).2)
    rw [one_smul] at h'
    exact h'
  | cutEndT =>
    simp only [StrandKind.pred, StrandKind.dir]
    have h' := regularPair_smul_pos hε.pos one_pos (regularPair_add_left_of_det_ne_zero hdet h4)
    rw [one_smul] at h'
    exact h'
  | arcST =>
    simp only [StrandKind.pred, StrandKind.dir]
    have h' := regularPair_smul_pos one_pos hε.pos (regularPair_add_right_of_det_ne_zero hdet h1)
    rw [one_smul] at h'
    exact h'
  | arcTS =>
    simp only [StrandKind.pred, StrandKind.dir]
    have h' := regularPair_smul_pos one_pos hε.pos (regularPair_add_right_of_det_ne_zero hdet' h3)
    rw [one_smul, add_comm] at h'
    exact h'

/-- Every component of `Γ₀` is a regular polygon: old corners are inherited, the corners at the
cut points are positively collinear, the corners at the arc ends are transverse
(`det es et ≠ 0`). -/
theorem regular (i : Fin Γ₀.c) : Regular (Γ₀.comp i).P := by
  intro m
  have h := u3_regularPair_pred_dir D x hε (M.kind ⟨i, m⟩) (M.kind_occurs _)
  rw [← M.kind_pred ⟨i, m⟩, ← M.dir_eq, ← M.dir_eq] at h
  exact h

/-! #### U3 helpers: vertices and cut points against the pieces they do not touch -/

omit M in
/-- No vertex of `D` lies on a smoothing arc (the arcs lie inside the clearance ball). -/
theorem u3_tail_not_mem_arc (e : D.Γ.Strand) (κ : StrandKind D x)
    (hκ : κ = StrandKind.arcST ∨ κ = StrandKind.arcTS) : D.Γ.tail e ∉ κ.seg ε := by
  intro hm
  have h1 := StrandKind.seg_arc_subset_closedBall ε hε κ hκ hm
  rw [Metric.mem_closedBall] at h1
  have h2 := r₁_le_dist_tail D x e
  rw [dist_comm] at h2
  have h3 : max (ε * ‖es D x‖) (ε * ‖et D x‖) < r₁ D x := max_lt hε.mul_es_lt hε.mul_et_lt
  linarith

omit M in
/-- No cut point lies on an old strand `e ≠ s, t`. -/
theorem u3_cutpt_not_mem_old (κ : StrandKind D x)
    (hκ : κ = StrandKind.cutEndS ∨ κ = StrandKind.cutEndT ∨ κ = StrandKind.arcST ∨ κ = StrandKind.arcTS)
    (e : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x) : κ.tail ε ∉ D.Γ.seg e := by
  intro hm
  have h1 := r₁_le_dist D x he.1 he.2 hm
  rw [dist_comm] at h1
  obtain ⟨c1, c2, c3, c4⟩ := StrandKind.dist_cut_lt ε hε
  rcases hκ with rfl | rfl | rfl | rfl <;> simp only [StrandKind.tail] at h1 <;> linarith

omit M in
theorem u3_sMinus_not_mem_cutEndT :
    (StrandKind.arcST : StrandKind D x).tail ε ∉ (StrandKind.cutEndT : StrandKind D x).seg ε := by
  rintro ⟨θ, h0, h1, h⟩
  have e0 : (StrandKind.arcST : StrandKind D x).tail ε =
      (StrandKind.arcST : StrandKind D x).tail ε + (0:ℝ) • (StrandKind.arcST : StrandKind D x).dir ε := by
    rw [zero_smul, add_zero]
  rw [e0, u3_arcST_pt, u3_cutEndT_pt] at h
  obtain ⟨h₁, -⟩ := u3_coords_eq D x h
  linarith [hε.pos]

omit M in
theorem u3_tMinus_not_mem_cutEndS :
    (StrandKind.arcTS : StrandKind D x).tail ε ∉ (StrandKind.cutEndS : StrandKind D x).seg ε := by
  rintro ⟨θ, h0, h1, h⟩
  have e0 : (StrandKind.arcTS : StrandKind D x).tail ε =
      (StrandKind.arcTS : StrandKind D x).tail ε + (0:ℝ) • (StrandKind.arcTS : StrandKind D x).dir ε := by
    rw [zero_smul, add_zero]
  rw [e0, u3_arcTS_pt, u3_cutEndS_pt] at h
  obtain ⟨-, h₂⟩ := u3_coords_eq D x h
  linarith [hε.pos]

omit M hε in
theorem u3_not_tail_s_mem_seg_t : D.Γ.tail (sS D x) ∉ D.Γ.seg (tS D x) := by
  intro hm
  rcases u3_eq_or_eq_succ_of_tail_mem_seg D (sS D x) (tS D x) hm with h | h
  · exact sS_ne_tS D x h
  · exact not_adjacent_sS_tS D x (u3_adjacent_of_eq_succ D _ _ h)

omit M hε in
theorem u3_not_tail_t_mem_seg_s : D.Γ.tail (tS D x) ∉ D.Γ.seg (sS D x) := by
  intro hm
  rcases u3_eq_or_eq_succ_of_tail_mem_seg D (tS D x) (sS D x) hm with h | h
  · exact sS_ne_tS D x h.symm
  · exact not_adjacent_sS_tS D x (u3_adjacent_of_eq_succ D _ _ h).symm

omit M hε in
/-- Incidence of old strands is inherited by their kinds. -/
theorem u3_incident_old_of_incidentTail (e e' : D.Γ.Strand) (he' : e' ≠ sS D x ∧ e' ≠ tS D x)
    (hi : D.Γ.IncidentTail e e') :
    (StrandKind.old e : StrandKind D x).Incident (StrandKind.old e') := by
  obtain ⟨i, a, b, rfl, rfl, hab⟩ := hi
  rcases hab with rfl | rfl
  · right
    simp only [StrandKind.pred]
    split_ifs with hs ht
    · exact absurd (u3_strand_pred_eq D _ _ hs) he'.1
    · exact absurd (u3_strand_pred_eq D _ _ ht) he'.2
    · rfl
  · left; rfl

omit M in
/-- The kind-level form of `tail_off`. -/
theorem u3_kind_tail_off (κ κ' : StrandKind D x) (hκ : κ.Occurs) (hκ' : κ'.Occurs)
    (h : ¬ κ.Incident κ') : κ.tail ε ∉ κ'.seg ε := by
  have h1 : (0:ℝ) < τs D x - ε := sub_pos.mpr hε.lt_τs
  have h3 : (0:ℝ) < τt D x - ε := sub_pos.mpr hε.lt_τt
  unfold StrandKind.Incident at h
  cases κ with
  | old e =>
    have he := (u3_occurs_old_iff D x).mp hκ
    cases κ' with
    | old e' =>
      rw [StrandKind.seg_old]
      exact D.generic.tail_off e e' fun hi =>
        h (u3_incident_old_of_incidentTail D x e e' ((u3_occurs_old_iff D x).mp hκ') hi)
    | cutStartS =>
      intro hm
      have hm' : D.Γ.tail e ∈ D.Γ.seg (sS D x) :=
        StrandKind.seg_subset_seg_orig ε hε StrandKind.cutStartS (by simp) (by simp) hm
      rcases u3_eq_or_eq_succ_of_tail_mem_seg D e (sS D x) hm' with rfl | rfl
      · exact he.1 rfl
      · obtain ⟨θ, -, hθ1, hθ⟩ := hm
        rw [StrandKind.tail_add_smul_dir ε StrandKind.cutStartS (by simp) (by simp)] at hθ
        have h2 := D.generic.edgePt_injective (sS D x)
          (show D.Γ.edgePt (sS D x) 1 = D.Γ.edgePt (sS D x) (θ * (τs D x - ε)) from
            (D.Γ.edgePt_one _).trans hθ)
        have := mul_le_of_le_one_left h1.le hθ1
        linarith [hε.lt_τs, τs_lt_one D x, hε.pos]
    | cutEndS =>
      intro hm
      have hm' : D.Γ.tail e ∈ D.Γ.seg (sS D x) :=
        StrandKind.seg_subset_seg_orig ε hε StrandKind.cutEndS (by simp) (by simp) hm
      rcases u3_eq_or_eq_succ_of_tail_mem_seg D e (sS D x) hm' with rfl | rfl
      · exact he.1 rfl
      · exact h (Or.inr (by simp [StrandKind.pred]))
    | cutStartT =>
      intro hm
      have hm' : D.Γ.tail e ∈ D.Γ.seg (tS D x) :=
        StrandKind.seg_subset_seg_orig ε hε StrandKind.cutStartT (by simp) (by simp) hm
      rcases u3_eq_or_eq_succ_of_tail_mem_seg D e (tS D x) hm' with rfl | rfl
      · exact he.2 rfl
      · obtain ⟨θ, -, hθ1, hθ⟩ := hm
        rw [StrandKind.tail_add_smul_dir ε StrandKind.cutStartT (by simp) (by simp)] at hθ
        have h2 := D.generic.edgePt_injective (tS D x)
          (show D.Γ.edgePt (tS D x) 1 = D.Γ.edgePt (tS D x) (θ * (τt D x - ε)) from
            (D.Γ.edgePt_one _).trans hθ)
        have := mul_le_of_le_one_left h3.le hθ1
        linarith [hε.lt_τt, τt_lt_one D x, hε.pos]
    | cutEndT =>
      intro hm
      have hm' : D.Γ.tail e ∈ D.Γ.seg (tS D x) :=
        StrandKind.seg_subset_seg_orig ε hε StrandKind.cutEndT (by simp) (by simp) hm
      rcases u3_eq_or_eq_succ_of_tail_mem_seg D e (tS D x) hm' with rfl | rfl
      · exact he.2 rfl
      · refine h (Or.inr ?_)
        simp only [StrandKind.pred]
        split_ifs with h1
        · exact absurd h1 (u3_succ_ne_succ_of_ne D _ _ (sS_ne_tS D x).symm)
        · rfl
    | arcST => exact u3_tail_not_mem_arc D x hε e _ (Or.inl rfl)
    | arcTS => exact u3_tail_not_mem_arc D x hε e _ (Or.inr rfl)
  | cutStartS =>
    cases κ' with
    | old e' =>
      have he' := (u3_occurs_old_iff D x).mp hκ'
      intro hm
      rw [StrandKind.seg_old] at hm
      rcases u3_eq_or_eq_succ_of_tail_mem_seg D (sS D x) e' hm with h' | h'
      · exact he'.1 h'.symm
      · exact h (Or.inr (by simp only [StrandKind.pred]; rw [u3_strand_pred_eq D _ _ h']))
    | cutStartS => exact (h (Or.inl rfl)).elim
    | cutEndS =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_SS D x hε) (u3_tail_mem_seg D x _) hm
    | cutStartT =>
      exact fun hm => u3_not_tail_s_mem_seg_t D x
        (StrandKind.seg_subset_seg_orig ε hε StrandKind.cutStartT (by simp) (by simp) hm)
    | cutEndT =>
      exact fun hm => u3_not_tail_s_mem_seg_t D x
        (StrandKind.seg_subset_seg_orig ε hε StrandKind.cutEndT (by simp) (by simp) hm)
    | arcST => exact u3_tail_not_mem_arc D x hε (sS D x) _ (Or.inl rfl)
    | arcTS => exact u3_tail_not_mem_arc D x hε (sS D x) _ (Or.inr rfl)
  | cutStartT =>
    cases κ' with
    | old e' =>
      have he' := (u3_occurs_old_iff D x).mp hκ'
      intro hm
      rw [StrandKind.seg_old] at hm
      rcases u3_eq_or_eq_succ_of_tail_mem_seg D (tS D x) e' hm with h' | h'
      · exact he'.2 h'.symm
      · exact h (Or.inr (by simp only [StrandKind.pred]; rw [u3_strand_pred_eq D _ _ h']))
    | cutStartS =>
      exact fun hm => u3_not_tail_t_mem_seg_s D x
        (StrandKind.seg_subset_seg_orig ε hε StrandKind.cutStartS (by simp) (by simp) hm)
    | cutEndS =>
      exact fun hm => u3_not_tail_t_mem_seg_s D x
        (StrandKind.seg_subset_seg_orig ε hε StrandKind.cutEndS (by simp) (by simp) hm)
    | cutStartT => exact (h (Or.inl rfl)).elim
    | cutEndT =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_TT D x hε) (u3_tail_mem_seg D x _) hm
    | arcST => exact u3_tail_not_mem_arc D x hε (tS D x) _ (Or.inl rfl)
    | arcTS => exact u3_tail_not_mem_arc D x hε (tS D x) _ (Or.inr rfl)
  | cutEndS =>
    cases κ' with
    | old e' => exact u3_cutpt_not_mem_old D x hε _ (by simp) e' ((u3_occurs_old_iff D x).mp hκ')
    | cutStartS =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_SS D x hε).symm (u3_tail_mem_seg D x _) hm
    | cutEndS => exact (h (Or.inl rfl)).elim
    | cutStartT =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutEndS_cutStartT D x hε) (u3_tail_mem_seg D x _) hm
    | cutEndT =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutEndS_cutEndT D x hε) (u3_tail_mem_seg D x _) hm
    | arcST =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutEndS_arcST D x hε) (u3_tail_mem_seg D x _) hm
    | arcTS => exact (h (Or.inr rfl)).elim
  | cutEndT =>
    cases κ' with
    | old e' => exact u3_cutpt_not_mem_old D x hε _ (by simp) e' ((u3_occurs_old_iff D x).mp hκ')
    | cutStartS =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutStartS_cutEndT D x hε).symm (u3_tail_mem_seg D x _) hm
    | cutEndS =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutEndS_cutEndT D x hε).symm (u3_tail_mem_seg D x _) hm
    | cutStartT =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_TT D x hε).symm (u3_tail_mem_seg D x _) hm
    | cutEndT => exact (h (Or.inl rfl)).elim
    | arcST => exact (h (Or.inr rfl)).elim
    | arcTS =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutEndT_arcTS D x hε) (u3_tail_mem_seg D x _) hm
  | arcST =>
    cases κ' with
    | old e' => exact u3_cutpt_not_mem_old D x hε _ (by simp) e' ((u3_occurs_old_iff D x).mp hκ')
    | cutStartS => exact (h (Or.inr rfl)).elim
    | cutEndS =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutEndS_arcST D x hε).symm (u3_tail_mem_seg D x _) hm
    | cutStartT =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutStartT_arcST D x hε).symm (u3_tail_mem_seg D x _) hm
    | cutEndT => exact u3_sMinus_not_mem_cutEndT D x hε
    | arcST => exact (h (Or.inl rfl)).elim
    | arcTS =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_arcST_arcTS D x hε) (u3_tail_mem_seg D x _) hm
  | arcTS =>
    cases κ' with
    | old e' => exact u3_cutpt_not_mem_old D x hε _ (by simp) e' ((u3_occurs_old_iff D x).mp hκ')
    | cutStartS =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutStartS_arcTS D x hε).symm (u3_tail_mem_seg D x _) hm
    | cutEndS => exact u3_tMinus_not_mem_cutEndS D x hε
    | cutStartT => exact (h (Or.inr rfl)).elim
    | cutEndT =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_cutEndT_arcTS D x hε).symm (u3_tail_mem_seg D x _) hm
    | arcST =>
      exact fun hm => Set.disjoint_left.mp (u3_disj_arcST_arcTS D x hε).symm (u3_tail_mem_seg D x _) hm
    | arcTS => exact (h (Or.inl rfl)).elim

theorem tail_off (u u' : Γ₀.Strand) (h : ¬ Γ₀.IncidentTail u u') : Γ₀.tail u ∉ Γ₀.seg u' := by
  rw [M.incidentTail_iff] at h
  rw [M.tail_eq, M.seg_eq]
  exact u3_kind_tail_off D x hε _ _ (M.kind_occurs u) (M.kind_occurs u') h

/-! #### U3 helpers: classification of a meeting non-adjacent pair -/

omit M hε in
/-- Adjacency of occurring kinds is symmetric. -/
theorem u3_adj_symm {κ κ' : StrandKind D x} (hκ : κ.Occurs) (h : κ.Adj κ') : κ'.Adj κ := by
  rcases h with rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (StrandKind.pred_succ κ hκ).symm)
  · exact Or.inr (Or.inl (StrandKind.succ_pred κ hκ).symm)

omit M in
/-- The arcs are disjoint from every old strand `e ≠ s, t` (clearance radius). -/
theorem u3_arc_disjoint_old (κ : StrandKind D x) (hκ : κ = StrandKind.arcST ∨ κ = StrandKind.arcTS)
    (e : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x) : Disjoint (κ.seg ε) (D.Γ.seg e) := by
  rw [Set.disjoint_left]
  intro q hq hq'
  have h1 := StrandKind.seg_arc_subset_closedBall ε hε κ hκ hq
  rw [Metric.mem_closedBall] at h1
  have h2 := r₁_le_dist D x he.1 he.2 hq'
  rw [dist_comm] at h2
  have h3 : max (ε * ‖es D x‖) (ε * ‖et D x‖) < r₁ D x := max_lt hε.mul_es_lt hε.mul_et_lt
  linarith

omit M in
/-- Two non-adjacent occurring kinds whose segments meet: neither is an arc, one of them is old,
and their original strands form a non-adjacent meeting pair of `D`. -/
theorem u3_meet_classify (κ κ' : StrandKind D x) (hκ : κ.Occurs) (hκ' : κ'.Occurs)
    (hadj : ¬ κ.Adj κ') (hmeet : (κ.seg ε ∩ κ'.seg ε).Nonempty) :
    (κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS) ∧ (κ' ≠ StrandKind.arcST ∧ κ' ≠ StrandKind.arcTS) ∧
      ((∃ e, κ = StrandKind.old e) ∨ (∃ e, κ' = StrandKind.old e)) ∧
      ¬ D.Γ.Adjacent κ.orig κ'.orig ∧ (D.Γ.seg κ.orig ∩ D.Γ.seg κ'.orig).Nonempty := by
  obtain ⟨q, hq, hq'⟩ := hmeet
  by_cases ho : ∃ e, κ = StrandKind.old e
  · obtain ⟨e, rfl⟩ := ho
    have he := (u3_occurs_old_iff D x).mp hκ
    rw [StrandKind.seg_old] at hq
    by_cases ho' : ∃ e', κ' = StrandKind.old e'
    · obtain ⟨e', rfl⟩ := ho'
      have he' := (u3_occurs_old_iff D x).mp hκ'
      rw [StrandKind.seg_old] at hq'
      refine ⟨by simp, by simp, Or.inl ⟨e, rfl⟩, ?_, ⟨q, hq, hq'⟩⟩
      exact (SpliceModel.adjacent_old_iff e e' he he').not.mp hadj
    · have hna' : κ' ≠ StrandKind.arcST ∧ κ' ≠ StrandKind.arcTS := by
        constructor <;> rintro rfl <;>
          exact Set.disjoint_left.mp (u3_arc_disjoint_old D x hε _ (by simp) e he) hq' hq
      refine ⟨by simp, hna', Or.inl ⟨e, rfl⟩, ?_, ⟨q, hq, StrandKind.seg_subset_seg_orig ε hε κ' hna'.1 hna'.2 hq'⟩⟩
      have := cut_inter_old D x hε κ' hna' ho' e he ⟨q, hq', hq⟩ (fun h => hadj (u3_adj_symm D x hκ' h))
      exact fun h => this h.symm
  · by_cases ho' : ∃ e', κ' = StrandKind.old e'
    · obtain ⟨e', rfl⟩ := ho'
      have he' := (u3_occurs_old_iff D x).mp hκ'
      rw [StrandKind.seg_old] at hq'
      have hna : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS := by
        constructor <;> rintro rfl <;>
          exact Set.disjoint_left.mp (u3_arc_disjoint_old D x hε _ (by simp) e' he') hq hq'
      refine ⟨hna, by simp, Or.inr ⟨e', rfl⟩, ?_, ⟨q, StrandKind.seg_subset_seg_orig ε hε κ hna.1 hna.2 hq, hq'⟩⟩
      exact cut_inter_old D x hε κ hna ho e' he' ⟨q, hq, hq'⟩ hadj
    · exact absurd hq' (Set.disjoint_left.mp (kind_disjoint D x hε κ κ' ho hadj (fun e h => ho' ⟨e, h⟩)) hq)

omit M in
/-- The direction of a non-arc kind is a positive multiple of the direction of its original strand. -/
theorem u3_dir_eq_smul_dir_orig (κ : StrandKind D x) (hκ : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS) :
    ∃ l : ℝ, 0 < l ∧ κ.dir ε = l • D.Γ.dir κ.orig := by
  cases κ with
  | old e => exact ⟨1, one_pos, (one_smul _ _).symm⟩
  | cutStartS => exact ⟨τs D x - ε, sub_pos.mpr hε.lt_τs, rfl⟩
  | cutEndS => exact ⟨1 - τs D x - ε, by linarith [hε.lt_one_sub_τs], rfl⟩
  | cutStartT => exact ⟨τt D x - ε, sub_pos.mpr hε.lt_τt, rfl⟩
  | cutEndT => exact ⟨1 - τt D x - ε, by linarith [hε.lt_one_sub_τt], rfl⟩
  | arcST => exact absurd rfl hκ.1
  | arcTS => exact absurd rfl hκ.2

omit M hε in
theorem u3_det_smul_smul (l l' : ℝ) (a b : Plane) : det (l • a) (l' • b) = (l * l') * det a b := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem transverse (u u' : Γ₀.Strand) (h : ¬ Γ₀.Adjacent u u')
    (hmeet : (Γ₀.seg u ∩ Γ₀.seg u').Nonempty) : det (Γ₀.dir u) (Γ₀.dir u') ≠ 0 := by
  rw [M.adjacent_iff] at h
  rw [M.seg_eq, M.seg_eq] at hmeet
  rw [M.dir_eq, M.dir_eq]
  obtain ⟨hna, hna', -, hadj, hmeet'⟩ :=
    u3_meet_classify D x hε _ _ (M.kind_occurs u) (M.kind_occurs u') h hmeet
  obtain ⟨l, hl, hd⟩ := u3_dir_eq_smul_dir_orig D x hε _ hna
  obtain ⟨l', hl', hd'⟩ := u3_dir_eq_smul_dir_orig D x hε _ hna'
  rw [hd, hd', u3_det_smul_smul]
  exact mul_ne_zero (mul_ne_zero hl.ne' hl'.ne') (D.generic.transverse _ _ hadj hmeet')

/-! #### U3 helpers: interiors, and the arcs against everything else -/

omit M in
/-- The open segment of a non-arc kind lies in the open segment of its original strand. -/
theorem u3_interior_subset_interior_orig (κ : StrandKind D x)
    (hκ : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS) : κ.interior ε ⊆ D.Γ.interior κ.orig := by
  have h1 : (0:ℝ) < τs D x - ε := sub_pos.mpr hε.lt_τs
  have h2 : (0:ℝ) < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
  have h3 : (0:ℝ) < τt D x - ε := sub_pos.mpr hε.lt_τt
  have h4 : (0:ℝ) < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
  have hτs := τs_pos D x
  have hτt := τt_pos D x
  have hτs' := τs_lt_one D x
  have hτt' := τt_lt_one D x
  have hpos := hε.pos
  rintro q ⟨θ, h0, hθ1, rfl⟩
  rw [StrandKind.tail_add_smul_dir ε κ hκ.1 hκ.2]
  refine ⟨κ.origParam ε θ, ?_, ?_, rfl⟩ <;> cases κ <;> simp only [StrandKind.origParam] <;> first
    | exact absurd rfl hκ.1
    | exact absurd rfl hκ.2
    | exact h0
    | exact hθ1
    | exact mul_pos h0 h1
    | exact mul_pos h0 h3
    | nlinarith

omit M in
/-- Two distinct non-arc occurring kinds with a common point lie over distinct strands of `D`. -/
theorem u3_orig_ne_of_seg_meet (κ κ' : StrandKind D x) (hκ : κ.Occurs) (hκ' : κ'.Occurs)
    (na : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS) (na' : κ' ≠ StrandKind.arcST ∧ κ' ≠ StrandKind.arcTS)
    (hne : κ ≠ κ') {q : Plane} (hq : q ∈ κ.seg ε) (hq' : q ∈ κ'.seg ε) : κ.orig ≠ κ'.orig := by
  have hd : ∀ κ κ' : StrandKind D x, (¬ ∃ e, κ = StrandKind.old e) → ¬ κ.Adj κ' →
      (∀ e, κ' = StrandKind.old e → False) → q ∈ κ.seg ε → q ∈ κ'.seg ε → False :=
    fun κ κ' h1 h2 h3 hq hq' => Set.disjoint_left.mp (kind_disjoint D x hε κ κ' h1 h2 h3) hq hq'
  cases κ <;> cases κ' <;> simp only [StrandKind.orig] <;> first
    | exact (hne rfl).elim
    | exact (na.1 rfl).elim
    | exact (na.2 rfl).elim
    | exact (na'.1 rfl).elim
    | exact (na'.2 rfl).elim
    | exact fun h => hne (congrArg _ h)
    | exact ((u3_occurs_old_iff D x).mp hκ).1
    | exact ((u3_occurs_old_iff D x).mp hκ).2
    | exact ((u3_occurs_old_iff D x).mp hκ').1.symm
    | exact ((u3_occurs_old_iff D x).mp hκ').2.symm
    | exact sS_ne_tS D x
    | exact (sS_ne_tS D x).symm
    | exact (hd _ _ (by simp) (by simp [StrandKind.Adj, StrandKind.succ, StrandKind.pred]) (by simp) hq hq').elim

omit M in
theorem u3_arcST_interior_cutStartS {q : Plane} (hq : q ∈ (StrandKind.arcST : StrandKind D x).interior ε)
    (hq' : q ∈ (StrandKind.cutStartS : StrandKind D x).seg ε) : False := by
  obtain ⟨μ, h0, h1, rfl⟩ := hq
  obtain ⟨θ, -, -, h⟩ := hq'
  rw [u3_arcST_pt, u3_cutStartS_pt] at h
  obtain ⟨-, h₂⟩ := u3_coords_eq D x h
  exact (mul_pos h0 hε.pos).ne' h₂

omit M in
theorem u3_arcST_interior_cutEndT {q : Plane} (hq : q ∈ (StrandKind.arcST : StrandKind D x).interior ε)
    (hq' : q ∈ (StrandKind.cutEndT : StrandKind D x).seg ε) : False := by
  obtain ⟨μ, h0, h1, rfl⟩ := hq
  obtain ⟨θ, -, -, h⟩ := hq'
  rw [u3_arcST_pt, u3_cutEndT_pt] at h
  obtain ⟨h₁, -⟩ := u3_coords_eq D x h
  exact (mul_neg_of_neg_of_pos (by linarith) hε.pos).ne h₁

omit M in
theorem u3_arcTS_interior_cutStartT {q : Plane} (hq : q ∈ (StrandKind.arcTS : StrandKind D x).interior ε)
    (hq' : q ∈ (StrandKind.cutStartT : StrandKind D x).seg ε) : False := by
  obtain ⟨μ, h0, h1, rfl⟩ := hq
  obtain ⟨θ, -, -, h⟩ := hq'
  rw [u3_arcTS_pt, u3_cutStartT_pt] at h
  obtain ⟨h₁, -⟩ := u3_coords_eq D x h
  exact (mul_pos h0 hε.pos).ne' h₁

omit M in
theorem u3_arcTS_interior_cutEndS {q : Plane} (hq : q ∈ (StrandKind.arcTS : StrandKind D x).interior ε)
    (hq' : q ∈ (StrandKind.cutEndS : StrandKind D x).seg ε) : False := by
  obtain ⟨μ, h0, h1, rfl⟩ := hq
  obtain ⟨θ, -, -, h⟩ := hq'
  rw [u3_arcTS_pt, u3_cutEndS_pt] at h
  obtain ⟨-, h₂⟩ := u3_coords_eq D x h
  exact (mul_neg_of_neg_of_pos (by linarith) hε.pos).ne h₂

omit M in
/-- An interior point of an arc lies on no other occurring kind. -/
theorem u3_arc_interior_not_mem (κ : StrandKind D x) (ha : κ = StrandKind.arcST ∨ κ = StrandKind.arcTS)
    (κ' : StrandKind D x) (hκ' : κ'.Occurs) (hne : κ ≠ κ') {q : Plane}
    (hq : q ∈ κ.interior ε) (hq' : q ∈ κ'.seg ε) : False := by
  have hd : ∀ κ κ' : StrandKind D x, (¬ ∃ e, κ = StrandKind.old e) → ¬ κ.Adj κ' →
      (∀ e, κ' = StrandKind.old e → False) → q ∈ κ.seg ε → q ∈ κ'.seg ε → False :=
    fun κ κ' h1 h2 h3 hq hq' => Set.disjoint_left.mp (kind_disjoint D x hε κ κ' h1 h2 h3) hq hq'
  rcases ha with rfl | rfl <;> cases κ' <;> first
    | exact (hne rfl).elim
    | exact Set.disjoint_left.mp (u3_arc_disjoint_old D x hε _ (by simp) _ ((u3_occurs_old_iff D x).mp hκ'))
        (u3_interior_subset_seg D x _ hq) (by rwa [StrandKind.seg_old] at hq')
    | exact u3_arcST_interior_cutStartS D x hε hq hq'
    | exact u3_arcST_interior_cutEndT D x hε hq hq'
    | exact u3_arcTS_interior_cutStartT D x hε hq hq'
    | exact u3_arcTS_interior_cutEndS D x hε hq hq'
    | exact hd _ _ (by simp) (by simp [StrandKind.Adj, StrandKind.succ, StrandKind.pred]) (by simp) (u3_interior_subset_seg D x _ hq) hq'

omit M in
/-- The kind-level form of `no_triple`. -/
theorem u3_kind_no_triple (κ κ' κ'' : StrandKind D x) (hκ : κ.Occurs) (hκ' : κ'.Occurs)
    (hκ'' : κ''.Occurs) (k1 : κ ≠ κ') (k2 : κ' ≠ κ'') (k3 : κ ≠ κ'') {q : Plane}
    (hq : q ∈ κ.interior ε) (hq' : q ∈ κ'.interior ε) (hq'' : q ∈ κ''.interior ε) : False := by
  by_cases a1 : κ = StrandKind.arcST ∨ κ = StrandKind.arcTS
  · exact u3_arc_interior_not_mem D x hε κ a1 κ' hκ' k1 hq (u3_interior_subset_seg D x _ hq')
  by_cases a2 : κ' = StrandKind.arcST ∨ κ' = StrandKind.arcTS
  · exact u3_arc_interior_not_mem D x hε κ' a2 κ hκ k1.symm hq' (u3_interior_subset_seg D x _ hq)
  by_cases a3 : κ'' = StrandKind.arcST ∨ κ'' = StrandKind.arcTS
  · exact u3_arc_interior_not_mem D x hε κ'' a3 κ hκ k3.symm hq'' (u3_interior_subset_seg D x _ hq)
  rw [not_or] at a1 a2 a3
  apply D.generic.no_triple
  refine ⟨κ.orig, κ'.orig, κ''.orig,
    u3_orig_ne_of_seg_meet D x hε κ κ' hκ hκ' a1 a2 k1 (u3_interior_subset_seg D x _ hq) (u3_interior_subset_seg D x _ hq'),
    u3_orig_ne_of_seg_meet D x hε κ' κ'' hκ' hκ'' a2 a3 k2 (u3_interior_subset_seg D x _ hq') (u3_interior_subset_seg D x _ hq''),
    u3_orig_ne_of_seg_meet D x hε κ κ'' hκ hκ'' a1 a3 k3 (u3_interior_subset_seg D x _ hq) (u3_interior_subset_seg D x _ hq''),
    q, ⟨u3_interior_subset_interior_orig D x hε κ a1 hq, u3_interior_subset_interior_orig D x hε κ' a2 hq'⟩,
    u3_interior_subset_interior_orig D x hε κ'' a3 hq''⟩

theorem no_triple : ¬ ∃ u u' u'' : Γ₀.Strand, u ≠ u' ∧ u' ≠ u'' ∧ u ≠ u'' ∧
    (Γ₀.interior u ∩ Γ₀.interior u' ∩ Γ₀.interior u'').Nonempty := by
  rintro ⟨u, u', u'', h1, h2, h3, q, ⟨hq, hq'⟩, hq''⟩
  rw [M.interior_eq] at hq hq' hq''
  exact u3_kind_no_triple D x hε _ _ _ (M.kind_occurs u) (M.kind_occurs u') (M.kind_occurs u'')
    (fun h => h1 (M.kind_injective h)) (fun h => h2 (M.kind_injective h))
    (fun h => h3 (M.kind_injective h)) hq hq' hq''

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
  have hne : u ≠ u' := by
    rintro rfl
    obtain ⟨s, t, hx, hna, -⟩ := h
    have hs : s ∈ ({u, u} : Finset Γ₀.Strand) := by rw [hx]; simp
    have ht : t ∈ ({u, u} : Finset Γ₀.Strand) := by rw [hx]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, or_self] at hs ht
    subst hs; subst ht
    exact hna (Shadow.Adjacent.refl Γ₀ _)
  obtain ⟨hna, hmeet⟩ := Γ₀.crossing_pair_spec ⟨{u, u'}, h⟩ (by simp) (by simp) hne
  rw [M.adjacent_iff] at hna
  rw [M.seg_eq, M.seg_eq] at hmeet
  obtain ⟨-, -, hold, hadj, hmeet'⟩ :=
    u3_meet_classify D x hε _ _ (M.kind_occurs u) (M.kind_occurs u') hna hmeet
  refine ⟨D.Γ.isCrossing_pair hadj hmeet', ?_⟩
  intro hx
  rw [D.val_eq_pair x] at hx
  rcases hold with ⟨e, he⟩ | ⟨e, he⟩
  · have hm : M.orig u ∈ ({M.orig u, M.orig u'} : Finset D.Γ.Strand) := by simp
    rw [hx] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hocc := (u3_occurs_old_iff D x).mp (he ▸ M.kind_occurs u)
    have horig : M.orig u = e := by unfold SpliceModel.orig; rw [he]; rfl
    rw [horig] at hm
    rcases hm with hm | hm
    · exact hocc.1 hm
    · exact hocc.2 hm
  · have hm : M.orig u' ∈ ({M.orig u, M.orig u'} : Finset D.Γ.Strand) := by simp
    rw [hx] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    have hocc := (u3_occurs_old_iff D x).mp (he ▸ M.kind_occurs u')
    have horig : M.orig u' = e := by unfold SpliceModel.orig; rw [he]; rfl
    rw [horig] at hm
    rcases hm with hm | hm
    · exact hocc.1 hm
    · exact hocc.2 hm

/-- The crossing of `D` under a crossing of `Γ₀`. -/
def origCrossing (y : Γ₀.Crossing) : D.Γ.Crossing :=
  ⟨{M.orig y.fst, M.orig y.snd}, (isCrossing_orig D x M hε (y.val_eq ▸ y.2)).1⟩

theorem origCrossing_ne (y : Γ₀.Crossing) : origCrossing D x M hε y ≠ x := by
  exact fun h => (isCrossing_orig D x M hε (y.val_eq ▸ y.2)).2 (congrArg Subtype.val h)

theorem orig_mem_origCrossing {y : Γ₀.Crossing} {u : Γ₀.Strand} (hu : u ∈ y.val) :
    M.orig u ∈ (origCrossing D x M hε y).val := by
  show M.orig u ∈ ({M.orig y.fst, M.orig y.snd} : Finset D.Γ.Strand)
  rw [y.val_eq] at hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl <;> simp

/-! #### U3 helpers: the strands of a crossing of `Γ₀` are not arcs, and are determined by their
original strands and the crossing point -/

/-- No arc carries a crossing of `Γ₀`. -/
theorem u3_kind_ne_arc_of_mem (y : Γ₀.Crossing) {u : Γ₀.Strand} (hu : u ∈ y.val) :
    M.kind u ≠ StrandKind.arcST ∧ M.kind u ≠ StrandKind.arcTS := by
  obtain ⟨hna, hmeet⟩ := Γ₀.crossing_pair_spec y hu (Γ₀.other_mem y hu) (Γ₀.other_ne y hu).symm
  rw [M.adjacent_iff] at hna
  rw [M.seg_eq, M.seg_eq] at hmeet
  exact (u3_meet_classify D x hε _ _ (M.kind_occurs _) (M.kind_occurs _) hna hmeet).1

/-- The crossing point of `Γ₀` at `y` is the crossing point of `D` at `origCrossing y`
(stated before `origCrossing_injective`, which uses it). -/
theorem u3_crossingPoint_origCrossing (y : Γ₀.Crossing) :
    Γ₀.crossingPoint y = D.Γ.crossingPoint (origCrossing D x M hε y) := by
  apply D.generic.common_point_unique
  intro f hf
  have hf' : f ∈ ({M.orig y.fst, M.orig y.snd} : Finset D.Γ.Strand) := hf
  simp only [Finset.mem_insert, Finset.mem_singleton] at hf'
  have key : ∀ u ∈ y.val, Γ₀.crossingPoint y ∈ D.Γ.seg (M.orig u) := fun u hu =>
    StrandKind.seg_subset_seg_orig ε hε _ (u3_kind_ne_arc_of_mem D x M hε y hu).1
      (u3_kind_ne_arc_of_mem D x M hε y hu).2 (by rw [← M.seg_eq]; exact Γ₀.crossingPoint_mem y hu)
  rcases hf' with rfl | rfl
  · exact key _ y.fst_mem
  · exact key _ y.snd_mem

/-- Two strands of crossings of `Γ₀` with the same crossing point and the same original strand
coincide (the two cut pieces of one strand are disjoint). -/
theorem u3_eq_of_orig_eq_of_mem {y y' : Γ₀.Crossing} (hpt : Γ₀.crossingPoint y = Γ₀.crossingPoint y')
    {u u' : Γ₀.Strand} (hu : u ∈ y.val) (hu' : u' ∈ y'.val) (h : M.orig u = M.orig u') : u = u' := by
  by_contra hne
  have hk : M.kind u ≠ M.kind u' := fun hk => hne (M.kind_injective hk)
  have hp : Γ₀.crossingPoint y ∈ (M.kind u).seg ε := by
    rw [← M.seg_eq]; exact Γ₀.crossingPoint_mem y hu
  have hp' : Γ₀.crossingPoint y ∈ (M.kind u').seg ε := by
    rw [hpt, ← M.seg_eq]; exact Γ₀.crossingPoint_mem y' hu'
  exact u3_orig_ne_of_seg_meet D x hε _ _ (M.kind_occurs u) (M.kind_occurs u')
    (u3_kind_ne_arc_of_mem D x M hε y hu) (u3_kind_ne_arc_of_mem D x M hε y' hu') hk hp hp' h

theorem origCrossing_injective : Function.Injective (origCrossing D x M hε) := by
  intro y y' h
  have hpt : Γ₀.crossingPoint y = Γ₀.crossingPoint y' := by
    rw [u3_crossingPoint_origCrossing D x M hε y, u3_crossingPoint_origCrossing D x M hε y', h]
  have key : ∀ (y y' : Γ₀.Crossing), origCrossing D x M hε y = origCrossing D x M hε y' →
      Γ₀.crossingPoint y = Γ₀.crossingPoint y' → y.val ⊆ y'.val := by
    intro y y' h hpt u hu
    have h1 : M.orig u ∈ (origCrossing D x M hε y').val := h ▸ orig_mem_origCrossing D x M hε hu
    have h2 : M.orig u ∈ ({M.orig y'.fst, M.orig y'.snd} : Finset D.Γ.Strand) := h1
    simp only [Finset.mem_insert, Finset.mem_singleton] at h2
    rcases h2 with h2 | h2
    · rw [u3_eq_of_orig_eq_of_mem D x M hε hpt hu y'.fst_mem h2]; exact y'.fst_mem
    · rw [u3_eq_of_orig_eq_of_mem D x M hε hpt hu y'.snd_mem h2]; exact y'.snd_mem
  exact Subtype.ext (Finset.Subset.antisymm (key y y' h hpt) (key y' y h.symm hpt.symm))

/-- The crossing point of `Γ₀` at `y` is the crossing point of `D` at `origCrossing y`. -/
theorem crossingPoint_origCrossing (y : Γ₀.Crossing) :
    Γ₀.crossingPoint y = D.Γ.crossingPoint (origCrossing D x M hε y) := by
  exact u3_crossingPoint_origCrossing D x M hε y

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
  unfold liftStrand SpliceModel.orig
  split_ifs with hs hlt ht hlt' <;> simp only [SpliceModel.kind_strandOf, StrandKind.orig] <;>
    first | exact hs.symm | exact ht.symm

omit hε in
theorem u3_kind_liftStrand_ne_arc (y : D.Γ.Crossing) (e : D.Γ.Strand) (he : e ∈ y.val) :
    M.kind (liftStrand D x M y e he) ≠ StrandKind.arcST ∧
      M.kind (liftStrand D x M y e he) ≠ StrandKind.arcTS := by
  unfold liftStrand
  split_ifs <;> simp

/-- The crossing point of `y ≠ x` lies on the lift of each strand of `y`. -/
theorem u3_crossingPoint_mem_seg_liftStrand {y : D.Γ.Crossing} (hy : y ≠ x) (e : D.Γ.Strand)
    (he : e ∈ y.val) : D.Γ.crossingPoint y ∈ Γ₀.seg (liftStrand D x M y e he) := by
  rw [M.seg_eq]
  have hspec := D.crossingParam_spec y he
  have hpos := hε.pos
  unfold liftStrand
  split_ifs with hs hlt ht hlt'
  · subst hs
    rw [M.kind_strandOf]
    have hfar : ε < |D.crossingParam y he - τs D x| := crossingParam_far_s D x hε ⟨y, ⟨_, he⟩⟩ rfl hy
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt)] at hfar
    have h1 : (0:ℝ) < τs D x - ε := sub_pos.mpr hε.lt_τs
    refine ⟨D.crossingParam y he / (τs D x - ε), div_nonneg hspec.1 h1.le,
      (div_le_one h1).mpr (by linarith), ?_⟩
    rw [StrandKind.tail_add_smul_dir ε StrandKind.cutStartS (by simp) (by simp)]
    simp only [StrandKind.origParam, StrandKind.orig]
    rw [div_mul_cancel₀ _ h1.ne']
    exact hspec.2.2
  · subst hs
    rw [M.kind_strandOf]
    have hfar : ε < |D.crossingParam y he - τs D x| := crossingParam_far_s D x hε ⟨y, ⟨_, he⟩⟩ rfl hy
    rw [abs_of_nonneg (by linarith)] at hfar
    have h2 : (0:ℝ) < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
    refine ⟨(D.crossingParam y he - τs D x - ε) / (1 - τs D x - ε), div_nonneg (by linarith) h2.le,
      (div_le_one h2).mpr (by linarith [hspec.2.1]), ?_⟩
    rw [StrandKind.tail_add_smul_dir ε StrandKind.cutEndS (by simp) (by simp)]
    simp only [StrandKind.origParam, StrandKind.orig]
    rw [div_mul_cancel₀ _ h2.ne']
    have hτ : τs D x + ε + (D.crossingParam y he - τs D x - ε) = D.crossingParam y he := by ring
    rw [hτ]
    exact hspec.2.2
  · subst ht
    rw [M.kind_strandOf]
    have hfar : ε < |D.crossingParam y he - τt D x| := crossingParam_far_t D x hε ⟨y, ⟨_, he⟩⟩ rfl hy
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt')] at hfar
    have h1 : (0:ℝ) < τt D x - ε := sub_pos.mpr hε.lt_τt
    refine ⟨D.crossingParam y he / (τt D x - ε), div_nonneg hspec.1 h1.le,
      (div_le_one h1).mpr (by linarith), ?_⟩
    rw [StrandKind.tail_add_smul_dir ε StrandKind.cutStartT (by simp) (by simp)]
    simp only [StrandKind.origParam, StrandKind.orig]
    rw [div_mul_cancel₀ _ h1.ne']
    exact hspec.2.2
  · subst ht
    rw [M.kind_strandOf]
    have hfar : ε < |D.crossingParam y he - τt D x| := crossingParam_far_t D x hε ⟨y, ⟨_, he⟩⟩ rfl hy
    rw [abs_of_nonneg (by linarith)] at hfar
    have h2 : (0:ℝ) < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
    refine ⟨(D.crossingParam y he - τt D x - ε) / (1 - τt D x - ε), div_nonneg (by linarith) h2.le,
      (div_le_one h2).mpr (by linarith [hspec.2.1]), ?_⟩
    rw [StrandKind.tail_add_smul_dir ε StrandKind.cutEndT (by simp) (by simp)]
    simp only [StrandKind.origParam, StrandKind.orig]
    rw [div_mul_cancel₀ _ h2.ne']
    have hτ : τt D x + ε + (D.crossingParam y he - τt D x - ε) = D.crossingParam y he := by ring
    rw [hτ]
    exact hspec.2.2
  · rw [M.kind_strandOf, StrandKind.seg_old]
    exact D.Γ.crossingPoint_mem y he

omit M hε in
/-- An old strand adjacent (as a kind) to a cut piece is adjacent in `D` to its original strand. -/
theorem u3_adj_old_cut (e : D.Γ.Strand) (κ' : StrandKind D x)
    (hc : κ' = StrandKind.cutStartS ∨ κ' = StrandKind.cutEndS ∨ κ' = StrandKind.cutStartT ∨
      κ' = StrandKind.cutEndT)
    (h : (StrandKind.old e : StrandKind D x).Adj κ') : D.Γ.Adjacent e κ'.orig := by
  unfold StrandKind.Adj at h
  simp only [StrandKind.succ, StrandKind.pred] at h
  rcases hc with rfl | rfl | rfl | rfl <;> simp only [StrandKind.orig] <;>
    split_ifs at h <;> simp at h <;>
    first
    | exact u3_adjacent_of_eq_pred D _ _ (by assumption)
    | exact u3_adjacent_of_eq_succ D _ _ (by assumption)

omit M hε in
theorem u3_adj_cut_old (κ : StrandKind D x)
    (hc : κ = StrandKind.cutStartS ∨ κ = StrandKind.cutEndS ∨ κ = StrandKind.cutStartT ∨
      κ = StrandKind.cutEndT)
    (e : D.Γ.Strand) (h : κ.Adj (StrandKind.old e)) : D.Γ.Adjacent κ.orig e := by
  unfold StrandKind.Adj at h
  rcases hc with rfl | rfl | rfl | rfl <;> simp only [StrandKind.orig] <;>
    simp [StrandKind.succ, StrandKind.pred] at h <;>
    first
    | exact (u3_adjacent_of_eq_pred D _ _ h).symm
    | exact (u3_adjacent_of_eq_succ D _ _ h).symm

omit M hε in
/-- Non-arc kinds over non-adjacent strands of `D` are non-adjacent kinds. -/
theorem u3_not_adj_of_not_adjacent_orig (κ κ' : StrandKind D x) (hκ : κ.Occurs) (hκ' : κ'.Occurs)
    (na : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS) (na' : κ' ≠ StrandKind.arcST ∧ κ' ≠ StrandKind.arcTS)
    (h : ¬ D.Γ.Adjacent κ.orig κ'.orig) : ¬ κ.Adj κ' := by
  cases κ <;> cases κ' <;> first
    | exact (na.1 rfl).elim
    | exact (na.2 rfl).elim
    | exact (na'.1 rfl).elim
    | exact (na'.2 rfl).elim
    | exact (h (Shadow.Adjacent.refl D.Γ _)).elim
    | exact (SpliceModel.adjacent_old_iff _ _ ((u3_occurs_old_iff D x).mp hκ) ((u3_occurs_old_iff D x).mp hκ')).not.mpr h
    | exact fun hadj => h (u3_adj_old_cut D x _ _ (by simp) hadj)
    | exact fun hadj => h (u3_adj_cut_old D x _ (by simp) _ hadj)
    | simp [StrandKind.Adj, StrandKind.succ, StrandKind.pred]

/-- Every crossing of `D` other than `x` lifts to a crossing of `Γ₀`. -/
theorem isCrossing_lift {y : D.Γ.Crossing} (hy : y ≠ x) :
    Γ₀.IsCrossing {liftStrand D x M y y.fst y.fst_mem, liftStrand D x M y y.snd y.snd_mem} := by
  have hne : y.fst ≠ y.snd := (D.Γ.other_ne y y.fst_mem).symm
  have hna := (D.Γ.crossing_pair_spec y y.fst_mem y.snd_mem hne).1
  refine Γ₀.isCrossing_pair ?_ ⟨D.Γ.crossingPoint y, u3_crossingPoint_mem_seg_liftStrand D x M hε hy _ _,
    u3_crossingPoint_mem_seg_liftStrand D x M hε hy _ _⟩
  rw [M.adjacent_iff]
  apply u3_not_adj_of_not_adjacent_orig D x _ _ (M.kind_occurs _) (M.kind_occurs _)
    (u3_kind_liftStrand_ne_arc D x M y _ _) (u3_kind_liftStrand_ne_arc D x M y _ _)
  show ¬ D.Γ.Adjacent (M.orig _) (M.orig _)
  rw [orig_liftStrand, orig_liftStrand]
  exact hna

/-- The lift of a crossing `y ≠ x`. -/
def liftCrossing (y : D.Γ.Crossing) (hy : y ≠ x) : Γ₀.Crossing :=
  ⟨_, isCrossing_lift D x M hε hy⟩

theorem origCrossing_liftCrossing (y : D.Γ.Crossing) (hy : y ≠ x) :
    origCrossing D x M hε (liftCrossing D x M hε y hy) = y := by
  apply Subtype.ext
  show ({M.orig (liftCrossing D x M hε y hy).fst, M.orig (liftCrossing D x M hε y hy).snd} :
    Finset D.Γ.Strand) = y.val
  have h1 : (liftCrossing D x M hε y hy).fst ∈
      ({liftStrand D x M y y.fst y.fst_mem, liftStrand D x M y y.snd y.snd_mem} : Finset Γ₀.Strand) :=
    (liftCrossing D x M hε y hy).fst_mem
  have h2 : (liftCrossing D x M hε y hy).snd ∈
      ({liftStrand D x M y y.fst y.fst_mem, liftStrand D x M y y.snd y.snd_mem} : Finset Γ₀.Strand) :=
    (liftCrossing D x M hε y hy).snd_mem
  have hne : (liftCrossing D x M hε y hy).snd ≠ (liftCrossing D x M hε y hy).fst :=
    Γ₀.other_ne _ (liftCrossing D x M hε y hy).fst_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rw [y.val_eq]
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h2.trans h1.symm) hne
  · rw [h1, h2, orig_liftStrand, orig_liftStrand]
  · rw [h1, h2, orig_liftStrand, orig_liftStrand, Finset.pair_comm]
  · exact absurd (h2.trans h1.symm) hne

theorem liftCrossing_origCrossing (y : Γ₀.Crossing) :
    liftCrossing D x M hε (origCrossing D x M hε y) (origCrossing_ne D x M hε y) = y := by
  apply Subtype.ext
  have hz : (origCrossing D x M hε y).val = {M.orig y.fst, M.orig y.snd} := rfl
  have hpt : Γ₀.crossingPoint (liftCrossing D x M hε (origCrossing D x M hε y) (origCrossing_ne D x M hε y)) =
      Γ₀.crossingPoint y := by
    rw [u3_crossingPoint_origCrossing D x M hε
      (liftCrossing D x M hε (origCrossing D x M hε y) (origCrossing_ne D x M hε y)),
      u3_crossingPoint_origCrossing D x M hε y, origCrossing_liftCrossing]
  have key : ∀ (e : D.Γ.Strand) (he : e ∈ (origCrossing D x M hε y).val),
      liftStrand D x M (origCrossing D x M hε y) e he ∈ y.val := by
    intro e he
    have hmemL : liftStrand D x M (origCrossing D x M hε y) e he ∈
        (liftCrossing D x M hε (origCrossing D x M hε y) (origCrossing_ne D x M hε y)).val := by
      have he' := he
      rw [(origCrossing D x M hε y).val_eq] at he'
      simp only [Finset.mem_insert, Finset.mem_singleton] at he'
      rcases he' with rfl | rfl
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have he' := he
    rw [hz] at he'
    simp only [Finset.mem_insert, Finset.mem_singleton] at he'
    rcases he' with he' | he'
    · rw [u3_eq_of_orig_eq_of_mem D x M hε hpt hmemL y.fst_mem ((orig_liftStrand D x M _ e he).trans he')]
      exact y.fst_mem
    · rw [u3_eq_of_orig_eq_of_mem D x M hε hpt hmemL y.snd_mem ((orig_liftStrand D x M _ e he).trans he')]
      exact y.snd_mem
  refine Finset.eq_of_subset_of_card_le ?_ (by rw [Γ₀.crossing_card_two, Γ₀.crossing_card_two])
  intro w hw
  have hw' : w ∈ ({liftStrand D x M (origCrossing D x M hε y) _ (origCrossing D x M hε y).fst_mem,
      liftStrand D x M (origCrossing D x M hε y) _ (origCrossing D x M hε y).snd_mem} : Finset Γ₀.Strand) := hw
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw'
  rcases hw' with rfl | rfl
  · exact key _ _
  · exact key _ _

/-- The crossings of `Γ₀` are the crossings of `D` other than `x`. -/
def crossingEquiv : Γ₀.Crossing ≃ {y : D.Γ.Crossing // y ≠ x} where
  toFun y := ⟨origCrossing D x M hε y, origCrossing_ne D x M hε y⟩
  invFun y := liftCrossing D x M hε y.1 y.2
  left_inv y := liftCrossing_origCrossing D x M hε y
  right_inv y := Subtype.ext (origCrossing_liftCrossing D x M hε y.1 y.2)

/-- The strands of a crossing of `Γ₀` lie over distinct strands of the original crossing. -/
theorem orig_injOn_crossing (y : Γ₀.Crossing) {u u' : Γ₀.Strand} (hu : u ∈ y.val) (hu' : u' ∈ y.val)
    (h : M.orig u = M.orig u') : u = u' := by
  exact u3_eq_of_orig_eq_of_mem D x M hε rfl hu hu' h

/-! U4 helpers at the model level: evaluation of `⟨u.1, (u.2, θ)⟩` through the kind of `u`; arcs
evaluate into the open disc, so strands through outside points and through crossings are not
arcs; the pair (original strand, rescaled parameter) determines an outside traversal point. -/

omit hε in
theorem eval_mk' (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ = (M.kind u).tail ε + θ.val • (M.kind u).dir ε :=
  M.eval_eq ⟨u.1, (u.2, θ)⟩

omit hε in
theorem eval_eq_edgePt_orig (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) (h1 : M.kind u ≠ StrandKind.arcST)
    (h2 : M.kind u ≠ StrandKind.arcTS) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ = D.Γ.edgePt (M.orig u) ((M.kind u).origParam ε θ.val) := by
  rw [eval_mk' D x M u θ, StrandKind.tail_add_smul_dir ε _ h1 h2]; rfl

theorem eval_arc_mem_ball (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1)
    (h : M.kind u = StrandKind.arcST ∨ M.kind u = StrandKind.arcTS) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) := by
  have hmem : Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ (M.kind u).seg ε :=
    ⟨θ.val, θ.2.1, θ.2.2.le, eval_mk' D x M u θ⟩
  exact Metric.closedBall_subset_ball (arc_lt_discRadius D x ε hε)
    (StrandKind.seg_arc_subset_closedBall ε hε _ h hmem)

theorem kind_ne_arc_of_not_mem_ball (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1)
    (h : Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∉ Metric.ball (pt D x) (discRadius D x ε)) :
    M.kind u ≠ StrandKind.arcST ∧ M.kind u ≠ StrandKind.arcTS :=
  ⟨fun h' => h (eval_arc_mem_ball D x M hε u θ (Or.inl h')),
   fun h' => h (eval_arc_mem_ball D x M hε u θ (Or.inr h'))⟩

theorem kind_ne_arc_of_not_mem_interior (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    M.kind ⟨q.1, q.2.1⟩ ≠ StrandKind.arcST ∧ M.kind ⟨q.1, q.2.1⟩ ≠ StrandKind.arcTS := by
  rw [interior_disc D x ε hε] at hq
  exact kind_ne_arc_of_not_mem_ball D x M hε ⟨q.1, q.2.1⟩ q.2.2 hq

theorem kind_ne_arc_of_mem (y : Γ₀.Crossing) {u : Γ₀.Strand} (hu : u ∈ y.val) :
    M.kind u ≠ StrandKind.arcST ∧ M.kind u ≠ StrandKind.arcTS := by
  have hmem : Γ₀.crossingPoint y ∈ (M.kind u).seg ε := by
    rw [← M.seg_eq]; exact Γ₀.crossingPoint_mem y hu
  have hnot : Γ₀.crossingPoint y ∉ disc D x ε := by
    rw [crossingPoint_origCrossing D x M hε y]
    exact crossingPoint_ne_not_mem_disc D x ε hε (origCrossing_ne D x M hε y)
  have key : ¬ (M.kind u = StrandKind.arcST ∨ M.kind u = StrandKind.arcTS) := fun h =>
    hnot (Metric.ball_subset_closedBall (Metric.closedBall_subset_ball (arc_lt_discRadius D x ε hε)
      (StrandKind.seg_arc_subset_closedBall ε hε _ h hmem)))
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem eq_of_orig_eq (u u' : Γ₀.Strand) (θ θ' : Set.Ico (0:ℝ) 1)
    (hκ : M.kind u ≠ StrandKind.arcST ∧ M.kind u ≠ StrandKind.arcTS)
    (hκ' : M.kind u' ≠ StrandKind.arcST ∧ M.kind u' ≠ StrandKind.arcTS)
    (horig : M.orig u = M.orig u')
    (hp : (M.kind u).origParam ε θ.val = (M.kind u').origParam ε θ'.val) : u = u' ∧ θ = θ' := by
  have hk : M.kind u = M.kind u' :=
    StrandKind.eq_of_orig_eq_of_origParam_eq ε hε hκ hκ' (M.kind_occurs u) (M.kind_occurs u')
      horig θ.2.1 θ.2.2 θ'.2.1 θ'.2.2 hp
  have hu : u = u' := M.kind_injective hk
  subst hu
  refine ⟨rfl, Subtype.ext ?_⟩
  have := congrArg ((M.kind u).liftParam ε) hp
  rwa [StrandKind.liftParam_origParam ε hε _ hκ.1 hκ.2,
    StrandKind.liftParam_origParam ε hε _ hκ.1 hκ.2] at this

/-- The traversal point of `D` under a traversal point of `Γ₀` outside the open disc: the original
strand at the rescaled parameter (the body of `origPt` before the clamp). -/
theorem exists_pt_of_not_mem_ball (q : Γ₀.Pt)
    (hq : Γ₀.eval q ∉ Metric.ball (pt D x) (discRadius D x ε)) :
    ∃ p : D.Γ.Pt, D.Γ.eval p = Γ₀.eval q ∧ (⟨p.1, p.2.1⟩ : D.Γ.Strand) = M.orig ⟨q.1, q.2.1⟩ ∧
      p.2.2.val = (M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val := by
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_not_mem_ball D x M hε ⟨q.1, q.2.1⟩ q.2.2 hq
  exact ⟨⟨(M.orig ⟨q.1, q.2.1⟩).1, ((M.orig ⟨q.1, q.2.1⟩).2,
    ⟨(M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val,
      StrandKind.origParam_mem_Ico ε hε _ q.2.2.2.1 q.2.2.2.2⟩)⟩,
    (eval_eq_edgePt_orig D x M ⟨q.1, q.2.1⟩ q.2.2 h1 h2).symm, rfl, rfl⟩

omit hε in
/-- Every component of `Γ₀` has a strand whose tail is a vertex of `D` (at most two predecessor
steps from any strand). -/
theorem exists_tail_old (i : Fin Γ₀.c) :
    ∃ (m : ZMod (Γ₀.comp i).k) (e : D.Γ.Strand), Γ₀.tail ⟨i, m⟩ = D.Γ.tail e := by
  have key : ∀ m : ZMod (Γ₀.comp i).k,
      ((∃ e, M.kind ⟨i, m⟩ = StrandKind.old e) ∨ M.kind ⟨i, m⟩ = StrandKind.cutStartS ∨
        M.kind ⟨i, m⟩ = StrandKind.cutStartT) → ∃ e, Γ₀.tail ⟨i, m⟩ = D.Γ.tail e := by
    intro m h
    rw [M.tail_eq]
    rcases h with ⟨e, he⟩ | he | he <;> rw [he]
    · exact ⟨e, rfl⟩
    · exact ⟨sS D x, rfl⟩
    · exact ⟨tS D x, rfl⟩
  have hp1 := M.kind_pred ⟨i, 0⟩
  have hp2 := M.kind_pred ⟨i, 0 - 1⟩
  dsimp only at hp1 hp2
  rcases hk : M.kind ⟨i, 0⟩ with e | _ | _ | _ | _ | _ | _
  · exact ⟨0, key 0 (Or.inl ⟨e, hk⟩)⟩
  · exact ⟨0, key 0 (Or.inr (Or.inl hk))⟩
  · rw [hk] at hp1; rw [hp1] at hp2
    exact ⟨0 - 1 - 1, key _ (Or.inr (Or.inr hp2))⟩
  · exact ⟨0, key 0 (Or.inr (Or.inr hk))⟩
  · rw [hk] at hp1; rw [hp1] at hp2
    exact ⟨0 - 1 - 1, key _ (Or.inr (Or.inl hp2))⟩
  · rw [hk] at hp1
    exact ⟨0 - 1, key _ (Or.inr (Or.inl hp1))⟩
  · rw [hk] at hp1
    exact ⟨0 - 1, key _ (Or.inr (Or.inr hp1))⟩

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
  unfold overStrand₀
  split_ifs with h
  · exact h
  · have h1 : M.orig y.fst = D.underStrand (origCrossing D x M hε y) :=
      D.eq_under_of_mem_of_ne _ (orig_mem_origCrossing D x M hε y.fst_mem) h
    apply D.eq_over_of_mem_of_ne _ (orig_mem_origCrossing D x M hε y.snd_mem)
    intro h2
    exact Γ₀.other_ne y y.fst_mem
      (orig_injOn_crossing D x M hε y y.snd_mem y.fst_mem (h2.trans h1.symm))

/-- **The smoothed diagram** on a splice model. -/
def toDiagram : Diagram where
  Γ := Γ₀
  generic := generic D x M hε
  overStrand := overStrand₀ D x M hε
  over_mem := overStrand₀_mem D x M hε

@[simp] theorem toDiagram_Γ : (toDiagram D x M hε).Γ = Γ₀ := rfl

theorem toDiagram_underStrand_orig (y : Γ₀.Crossing) :
    M.orig ((toDiagram D x M hε).underStrand y) = D.underStrand (origCrossing D x M hε y) := by
  have hmem : (toDiagram D x M hε).underStrand y ∈ y.val := (toDiagram D x M hε).under_mem y
  have hne : (toDiagram D x M hε).underStrand y ≠ overStrand₀ D x M hε y :=
    (toDiagram D x M hε).under_ne_over y
  apply D.eq_under_of_mem_of_ne _ (orig_mem_origCrossing D x M hε hmem)
  intro h
  exact hne (orig_injOn_crossing D x M hε y hmem (overStrand₀_mem D x M hε y)
    (h.trans (orig_overStrand₀ D x M hε y).symm))

/-- Signs are inherited (directions of cut pieces are positive multiples of the originals). -/
theorem toDiagram_sign (y : Γ₀.Crossing) :
    (toDiagram D x M hε).sign y = D.sign (origCrossing D x M hε y) := by
  have key : ∀ u u' : Γ₀.Strand, u ∈ y.val → u' ∈ y.val →
      M.orig u = D.overStrand (origCrossing D x M hε y) →
      M.orig u' = D.underStrand (origCrossing D x M hε y) →
      SignType.sign (det (Γ₀.dir u) (Γ₀.dir u')) = D.sign (origCrossing D x M hε y) := by
    intro u u' hu hu' ho ho'
    obtain ⟨l, hl, hdl⟩ := StrandKind.dir_eq_smul_orig ε hε (M.kind u)
      (kind_ne_arc_of_mem D x M hε y hu).1 (kind_ne_arc_of_mem D x M hε y hu).2
    obtain ⟨m, hm, hdm⟩ := StrandKind.dir_eq_smul_orig ε hε (M.kind u')
      (kind_ne_arc_of_mem D x M hε y hu').1 (kind_ne_arc_of_mem D x M hε y hu').2
    unfold Diagram.sign
    rw [M.dir_eq u, M.dir_eq u', hdl, hdm, det_smul_smul, sign_mul, sign_pos (mul_pos hl hm),
      one_mul, ← ho, ← ho']
    rfl
  exact key _ _ (overStrand₀_mem D x M hε y) ((toDiagram D x M hε).under_mem y)
    (orig_overStrand₀ D x M hε y) (toDiagram_underStrand_orig D x M hε y)

/-- The crossing parameter of a strand of `Γ₀` through `y` is the rescaled parameter of `D`. -/
theorem crossingParam_toDiagram (y : Γ₀.Crossing) {u : Γ₀.Strand} (hu : u ∈ y.val) :
    (toDiagram D x M hε).crossingParam y hu =
      (M.kind u).liftParam ε (D.crossingParam (origCrossing D x M hε y)
        (orig_mem_origCrossing D x M hε hu)) := by
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_mem D x M hε y hu
  have hs : Γ₀.crossingPoint y =
      edgePoint (Γ₀.comp u.1).P u.2 ((toDiagram D x M hε).crossingParam y hu) :=
    ((toDiagram D x M hε).crossingParam_spec y hu).2.2
  have hD := D.crossingParam_spec (origCrossing D x M hε y) (orig_mem_origCrossing D x M hε hu)
  have key : D.Γ.edgePt (M.orig u)
      ((M.kind u).origParam ε ((toDiagram D x M hε).crossingParam y hu)) =
      D.Γ.edgePt (M.orig u) (D.crossingParam (origCrossing D x M hε y)
        (orig_mem_origCrossing D x M hε hu)) := by
    show edgePoint (D.Γ.comp (M.kind u).orig.1).P (M.kind u).orig.2 _ =
      edgePoint (D.Γ.comp (M.orig u).1).P (M.orig u).2 _
    rw [← StrandKind.tail_add_smul_dir ε _ h1 h2, ← M.tail_eq, ← M.dir_eq, ← hD.2.2,
      ← crossingPoint_origCrossing D x M hε y, hs]
    rfl
  have := D.generic.edgePt_injective _ key
  rw [← this, StrandKind.liftParam_origParam ε hε _ h1 h2]

/-! ### 6d. Cleanness of `D₀` and its two arcs inside the disc -/

/-- No crossing point of `Γ₀` lies in the closed disc. -/
theorem crossingPoint_not_mem_disc (y : Γ₀.Crossing) : Γ₀.crossingPoint y ∉ disc D x ε := by
  rw [crossingPoint_origCrossing D x M hε y]
  exact crossingPoint_ne_not_mem_disc D x ε hε (origCrossing_ne D x M hε y)

theorem no_inner_toDiagram (y : Γ₀.Crossing) : Γ₀.crossingPoint y ∉ interior (disc D x ε) :=
  fun h => crossingPoint_not_mem_disc D x M hε y (interior_subset h)

/-- U4 helper: injectivity of `Γ₀.eval` on the frontier of the disc (through `clean_D` and the
injectivity of the pair (original strand, rescaled parameter)). -/
theorem frontier_injOn_toDiagram :
    Set.InjOn Γ₀.eval {p | Γ₀.eval p ∈ frontier (disc D x ε)} := by
    intro q hq q' hq' heq
    simp only [Set.mem_setOf_eq, frontier_disc D x ε hε] at hq hq'
    have hnb : Γ₀.eval q ∉ Metric.ball (pt D x) (discRadius D x ε) := fun h =>
      (Metric.mem_ball.mp h).ne (Metric.mem_sphere.mp hq)
    have hnb' : Γ₀.eval q' ∉ Metric.ball (pt D x) (discRadius D x ε) := fun h =>
      (Metric.mem_ball.mp h).ne (Metric.mem_sphere.mp hq')
    obtain ⟨p, hp1, hp2, hp3⟩ := exists_pt_of_not_mem_ball D x M hε q hnb
    obtain ⟨p', hp1', hp2', hp3'⟩ := exists_pt_of_not_mem_ball D x M hε q' hnb'
    have hpp : p = p' := (clean_D D x hε).frontier_injOn
      (by show D.Γ.eval p ∈ frontier (disc D x ε); rw [hp1, frontier_disc D x ε hε]; exact hq)
      (by show D.Γ.eval p' ∈ frontier (disc D x ε); rw [hp1', frontier_disc D x ε hε]; exact hq')
      (by rw [hp1, hp1']; exact heq)
    subst hpp
    obtain ⟨hu, hθ⟩ := eq_of_orig_eq D x M hε ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2
      (kind_ne_arc_of_not_mem_ball D x M hε ⟨q.1, q.2.1⟩ q.2.2 hnb)
      (kind_ne_arc_of_not_mem_ball D x M hε ⟨q'.1, q'.2.1⟩ q'.2.2 hnb') (hp2.symm.trans hp2')
      (hp3.symm.trans hp3')
    exact (Shadow.mk_eq_mk_iff ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2).mpr ⟨hu, hθ⟩

/-- U4 helper: every component of `Γ₀` leaves the disc (at a vertex of `D`). -/
theorem exists_eval_not_mem_disc (i : Fin Γ₀.c) :
    ∃ p : TraversalPoint (Γ₀.comp i).k, Γ₀.eval ⟨i, p⟩ ∉ disc D x ε := by
  obtain ⟨m, e, he⟩ := exists_tail_old D x M i
  refine ⟨(m, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
  have h0 : Γ₀.eval ⟨i, (m, ⟨0, le_rfl, zero_lt_one⟩)⟩ = Γ₀.tail ⟨i, m⟩ := by
    show edgePoint (Γ₀.comp i).P m (0:ℝ) = (Γ₀.comp i).P m
    simp [edgePoint]
  rw [h0, he]
  exact tail_not_mem_disc D x ε hε e

theorem clean_toDiagram : Clean (disc D x ε) (toDiagram D x M hε) where
  frontier_injOn := frontier_injOn_toDiagram D x M hε
  exits := exists_eval_not_mem_disc D x M hε

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
  apply M.kind_injective
  rw [M.kind_strandOf]
  have h1 := M.kind_succ (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS)
  have h2 := M.kind_succ ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
    (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 1⟩
  rw [M.kind_strandOf] at h1
  dsimp only at h2
  rw [h1] at h2
  rw [← one_add_one_eq_two, ← add_assoc]
  exact h2.symm

omit hε in
theorem strandOf_cutEndS_eq :
    M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS =
      ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ := by
  apply M.kind_injective
  rw [M.kind_strandOf]
  have h1 := M.kind_succ (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT)
  have h2 := M.kind_succ ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
    (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 1⟩
  rw [M.kind_strandOf] at h1
  dsimp only at h2
  rw [h1] at h2
  rw [← one_add_one_eq_two, ← add_assoc]
  exact h2.symm

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

/-! U4 helpers for the two smoothing arcs of `D₀`: the kinds of the three strands of each arc,
per-kind membership of `⟨u.1, (u.2, θ)⟩` in the disc / open disc, and the classification of the
points of `arcST₀` / `arcTS₀` by kind and parameter. -/

omit hε in
theorem kind_cutStartS_add_one :
    M.kind ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
      (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 1⟩ = StrandKind.arcST := by
  rw [M.kind_succ, M.kind_strandOf]; rfl

omit hε in
theorem kind_cutStartS_add_two :
    M.kind ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
      (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ = StrandKind.cutEndT := by
  rw [← strandOf_cutEndT_eq D x M, M.kind_strandOf]

omit hε in
theorem kind_cutStartT_add_one :
    M.kind ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
      (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 1⟩ = StrandKind.arcTS := by
  rw [M.kind_succ, M.kind_strandOf]; rfl

omit hε in
theorem kind_cutStartT_add_two :
    M.kind ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
      (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ = StrandKind.cutEndS := by
  rw [← strandOf_cutEndS_eq D x M, M.kind_strandOf]

omit hε in
theorem eq_strandOf_of_kind {u : Γ₀.Strand} {κ : StrandKind D x} (hκ : κ.Occurs)
    (h : M.kind u = κ) : u = M.strandOf κ hκ :=
  M.kind_injective (by rw [h, M.kind_strandOf])

theorem eval_old_not_mem_disc (u : Γ₀.Strand) (e : D.Γ.Strand) (hu : M.kind u = StrandKind.old e)
    (θ : Set.Ico (0:ℝ) 1) : Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∉ disc D x ε := by
  intro hmem
  have hseg : Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ D.Γ.seg e := by
    rw [← StrandKind.seg_old ε e, ← hu]
    exact ⟨θ.val, θ.2.1, θ.2.2.le, eval_mk' D x M u θ⟩
  have hocc := M.kind_occurs u
  rw [hu] at hocc
  rcases mem_seg_of_mem_disc D x ε hε hseg hmem with h | h
  · exact hocc.1 (by rw [h])
  · exact hocc.2 (by rw [h])

theorem eval_cutStartS_mem_disc_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutStartS)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔ θ₀sIn D x ε ≤ θ.val := by
  rw [eval_eq_edgePt_orig D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (θ.val * (τs D x - ε)) ∈ _ ↔ _
  rw [edgePoint_s_mem_disc_iff D x ε hε]
  unfold θ₀sIn
  simp only [StrandKind.liftParam]
  have hpos : 0 < τs D x - ε := sub_pos.mpr hε.lt_τs
  have h2 := (θsIn_lt_cut D x ε hε).2
  have h3 := mul_lt_mul_of_pos_right θ.2.2 hpos
  have h4 := hε.pos
  constructor
  · rintro ⟨h1, -⟩; exact (div_le_iff₀ hpos).mpr h1
  · intro h; exact ⟨(div_le_iff₀ hpos).mp h, by linarith⟩

theorem eval_cutStartS_mem_ball_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutStartS)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔ θ₀sIn D x ε < θ.val := by
  rw [eval_eq_edgePt_orig D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (θ.val * (τs D x - ε)) ∈ _ ↔ _
  rw [edgePoint_s_mem_ball_iff D x ε hε]
  unfold θ₀sIn
  simp only [StrandKind.liftParam]
  have hpos : 0 < τs D x - ε := sub_pos.mpr hε.lt_τs
  have h2 := (θsIn_lt_cut D x ε hε).2
  have h3 := mul_lt_mul_of_pos_right θ.2.2 hpos
  have h4 := hε.pos
  constructor
  · rintro ⟨h1, -⟩; exact (div_lt_iff₀ hpos).mpr h1
  · intro h; exact ⟨(div_lt_iff₀ hpos).mp h, by linarith⟩

theorem eval_cutStartT_mem_disc_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutStartT)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔ θ₀tIn D x ε ≤ θ.val := by
  rw [eval_eq_edgePt_orig D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (θ.val * (τt D x - ε)) ∈ _ ↔ _
  rw [edgePoint_t_mem_disc_iff D x ε hε]
  unfold θ₀tIn
  simp only [StrandKind.liftParam]
  have hpos : 0 < τt D x - ε := sub_pos.mpr hε.lt_τt
  have h2 := (θtIn_lt_cut D x ε hε).2
  have h3 := mul_lt_mul_of_pos_right θ.2.2 hpos
  have h4 := hε.pos
  constructor
  · rintro ⟨h1, -⟩; exact (div_le_iff₀ hpos).mpr h1
  · intro h; exact ⟨(div_le_iff₀ hpos).mp h, by linarith⟩

theorem eval_cutStartT_mem_ball_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutStartT)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔ θ₀tIn D x ε < θ.val := by
  rw [eval_eq_edgePt_orig D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (θ.val * (τt D x - ε)) ∈ _ ↔ _
  rw [edgePoint_t_mem_ball_iff D x ε hε]
  unfold θ₀tIn
  simp only [StrandKind.liftParam]
  have hpos : 0 < τt D x - ε := sub_pos.mpr hε.lt_τt
  have h2 := (θtIn_lt_cut D x ε hε).2
  have h3 := mul_lt_mul_of_pos_right θ.2.2 hpos
  have h4 := hε.pos
  constructor
  · rintro ⟨h1, -⟩; exact (div_lt_iff₀ hpos).mpr h1
  · intro h; exact ⟨(div_lt_iff₀ hpos).mp h, by linarith⟩

theorem eval_cutEndT_mem_disc_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutEndT)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔ θ.val ≤ θ₀tOut D x ε := by
  rw [eval_eq_edgePt_orig D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2
    (τt D x + ε + θ.val * (1 - τt D x - ε)) ∈ _ ↔ _
  rw [edgePoint_t_mem_disc_iff D x ε hε]
  unfold θ₀tOut
  simp only [StrandKind.liftParam]
  have hpos : 0 < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
  have h2 := (θtIn_lt_cut D x ε hε).1
  have h3 := mul_nonneg θ.2.1 hpos.le
  have h4 := hε.pos
  constructor
  · rintro ⟨-, h1⟩; rw [le_div_iff₀ hpos]; linarith
  · intro h; rw [le_div_iff₀ hpos] at h; exact ⟨by linarith, by linarith⟩

theorem eval_cutEndT_mem_ball_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutEndT)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔ θ.val < θ₀tOut D x ε := by
  rw [eval_eq_edgePt_orig D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2
    (τt D x + ε + θ.val * (1 - τt D x - ε)) ∈ _ ↔ _
  rw [edgePoint_t_mem_ball_iff D x ε hε]
  unfold θ₀tOut
  simp only [StrandKind.liftParam]
  have hpos : 0 < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
  have h2 := (θtIn_lt_cut D x ε hε).1
  have h3 := mul_nonneg θ.2.1 hpos.le
  have h4 := hε.pos
  constructor
  · rintro ⟨-, h1⟩; rw [lt_div_iff₀ hpos]; linarith
  · intro h; rw [lt_div_iff₀ hpos] at h; exact ⟨by linarith, by linarith⟩

theorem eval_cutEndS_mem_disc_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutEndS)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔ θ.val ≤ θ₀sOut D x ε := by
  rw [eval_eq_edgePt_orig D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2
    (τs D x + ε + θ.val * (1 - τs D x - ε)) ∈ _ ↔ _
  rw [edgePoint_s_mem_disc_iff D x ε hε]
  unfold θ₀sOut
  simp only [StrandKind.liftParam]
  have hpos : 0 < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
  have h2 := (θsIn_lt_cut D x ε hε).1
  have h3 := mul_nonneg θ.2.1 hpos.le
  have h4 := hε.pos
  constructor
  · rintro ⟨-, h1⟩; rw [le_div_iff₀ hpos]; linarith
  · intro h; rw [le_div_iff₀ hpos] at h; exact ⟨by linarith, by linarith⟩

theorem eval_cutEndS_mem_ball_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutEndS)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔ θ.val < θ₀sOut D x ε := by
  rw [eval_eq_edgePt_orig D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2
    (τs D x + ε + θ.val * (1 - τs D x - ε)) ∈ _ ↔ _
  rw [edgePoint_s_mem_ball_iff D x ε hε]
  unfold θ₀sOut
  simp only [StrandKind.liftParam]
  have hpos : 0 < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
  have h2 := (θsIn_lt_cut D x ε hε).1
  have h3 := mul_nonneg θ.2.1 hpos.le
  have h4 := hε.pos
  constructor
  · rintro ⟨-, h1⟩; rw [lt_div_iff₀ hpos]; linarith
  · intro h; rw [lt_div_iff₀ hpos] at h; exact ⟨by linarith, by linarith⟩

theorem inner_arcST₀_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    (arcST₀ D x M hε).Inner ⟨u.1, (u.2, θ)⟩ ↔
      (M.kind u = StrandKind.cutStartS ∧ θ₀sIn D x ε < θ.val) ∨ M.kind u = StrandKind.arcST ∨
        (M.kind u = StrandKind.cutEndT ∧ θ.val < θ₀tOut D x ε) := by
  have hval := strandOf_cutStartS_val D x M
  constructor
  · rintro ⟨r, hb, hp⟩
    obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
      ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1, r.1⟩ θ r.2).mp hp
    rcases (traversalBetween_span_two _ hval _ _ r).mp hb with ⟨hr, hlt⟩ | hr | ⟨hr, hlt⟩
    · left
      rw [hr] at hu
      refine ⟨?_, by subst hθ; exact hlt⟩
      rw [hu]; exact M.kind_strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS
    · right; left
      rw [hr] at hu
      rw [hu]; exact kind_cutStartS_add_one D x M
    · right; right
      rw [hr] at hu
      refine ⟨?_, by subst hθ; exact hlt⟩
      rw [hu]; exact kind_cutStartS_add_two D x M
  · rintro (⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩)
    · have hu := eq_strandOf_of_kind D x M StrandKind.occurs_cutStartS hk
      subst hu
      exact ⟨((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2, θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inl ⟨rfl, hlt⟩), rfl⟩
    · have hu : u = ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
          (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 1⟩ :=
        M.kind_injective (by rw [hk, kind_cutStartS_add_one D x M])
      subst hu
      exact ⟨(((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 1 :
          ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k), θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inr (Or.inl rfl)), rfl⟩
    · have hu : u = ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
          (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ :=
        M.kind_injective (by rw [hk, kind_cutStartS_add_two D x M])
      subst hu
      exact ⟨(((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2 :
          ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k), θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inr (Or.inr ⟨rfl, hlt⟩)), rfl⟩

theorem mem_arcST₀_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    (arcST₀ D x M hε).Mem ⟨u.1, (u.2, θ)⟩ ↔
      (M.kind u = StrandKind.cutStartS ∧ θ₀sIn D x ε ≤ θ.val) ∨ M.kind u = StrandKind.arcST ∨
        (M.kind u = StrandKind.cutEndT ∧ θ.val ≤ θ₀tOut D x ε) := by
  constructor
  · rintro (h | h | h)
    · obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
        (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS) θ
        ⟨θ₀sIn D x ε, (θ₀_mem D x ε hε).1⟩).mp h
      left
      refine ⟨?_, by subst hθ; exact le_rfl⟩
      rw [hu]; exact M.kind_strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS
    · obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
        ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
          (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ θ
        ⟨θ₀tOut D x ε, (θ₀_mem D x ε hε).2.2.2⟩).mp h
      right; right
      refine ⟨?_, by subst hθ; exact le_rfl⟩
      rw [hu]; exact kind_cutStartS_add_two D x M
    · rcases (inner_arcST₀_iff D x M hε u θ).mp h with ⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩
      · exact Or.inl ⟨hk, hlt.le⟩
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr ⟨hk, hlt.le⟩)
  · rintro (⟨hk, hle⟩ | hk | ⟨hk, hle⟩)
    · rcases hle.lt_or_eq with hlt | heq
      · exact ((inner_arcST₀_iff D x M hε u θ).mpr (Or.inl ⟨hk, hlt⟩)).mem
      · left
        exact (Shadow.mk_eq_mk_iff u (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS)
          θ ⟨θ₀sIn D x ε, (θ₀_mem D x ε hε).1⟩).mpr
          ⟨eq_strandOf_of_kind D x M _ hk, Subtype.ext heq.symm⟩
    · exact ((inner_arcST₀_iff D x M hε u θ).mpr (Or.inr (Or.inl hk))).mem
    · rcases hle.lt_or_eq with hlt | heq
      · exact ((inner_arcST₀_iff D x M hε u θ).mpr (Or.inr (Or.inr ⟨hk, hlt⟩))).mem
      · right; left
        exact (Shadow.mk_eq_mk_iff u
          ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
            (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ θ
          ⟨θ₀tOut D x ε, (θ₀_mem D x ε hε).2.2.2⟩).mpr
          ⟨M.kind_injective (by rw [hk, kind_cutStartS_add_two D x M]), Subtype.ext heq⟩

theorem eval_arcST₀_startPt : Γ₀.eval (arcST₀ D x M hε).startPt =
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (θsIn D x ε) := by
  have h := eval_eq_edgePt_orig D x M (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS)
    ⟨θ₀sIn D x ε, (θ₀_mem D x ε hε).1⟩ (by rw [M.kind_strandOf]; nofun)
    (by rw [M.kind_strandOf]; nofun)
  rw [SpliceModel.orig, M.kind_strandOf] at h
  dsimp only at h
  have h2 : StrandKind.origParam ε StrandKind.cutStartS (θ₀sIn D x ε) = θsIn D x ε :=
    StrandKind.origParam_liftParam ε hε _ (by nofun) (by nofun) _
  rw [h2] at h
  exact h

theorem eval_arcST₀_stopPt : Γ₀.eval (arcST₀ D x M hε).stopPt =
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (θtOut D x ε) := by
  have h := eval_eq_edgePt_orig D x M (M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT)
    ⟨θ₀tOut D x ε, (θ₀_mem D x ε hε).2.2.2⟩ (by rw [M.kind_strandOf]; nofun)
    (by rw [M.kind_strandOf]; nofun)
  rw [SpliceModel.orig, M.kind_strandOf, strandOf_cutEndT_eq D x M] at h
  dsimp only at h
  have h2 : StrandKind.origParam ε StrandKind.cutEndT (θ₀tOut D x ε) = θtOut D x ε :=
    StrandKind.origParam_liftParam ε hε _ (by nofun) (by nofun) _
  rw [h2] at h
  exact h

theorem isArc_arcST₀ : Γ₀.IsArc (disc D x ε) (arcST₀ D x M hε) where
  start_ne_stop := by
    intro h
    have h1 : (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 =
        (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2 := congrArg Prod.fst h
    have h2 := left_eq_add.mp h1
    have hv := strandOf_cutStartS_val D x M
    have h3 : (2 : ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartS
        StrandKind.occurs_cutStartS).1).k).val = 2 := by
      rw [ZMod.val_two_eq_two_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [h2, ZMod.val_zero] at h3
    exact absurd h3 (by norm_num)
  start_frontier := by
    rw [frontier_disc D x ε hε, eval_arcST₀_startPt D x M hε]
    exact mem_sphere_of_mem_closedBall_not_mem_ball
      ((edgePoint_s_mem_disc_iff D x ε hε _).mpr ⟨le_rfl, (θsIn_lt_θsOut D x ε hε).le⟩)
      (fun h => lt_irrefl _ ((edgePoint_s_mem_ball_iff D x ε hε _).mp h).1)
  stop_frontier := by
    rw [frontier_disc D x ε hε, eval_arcST₀_stopPt D x M hε]
    exact mem_sphere_of_mem_closedBall_not_mem_ball
      ((edgePoint_t_mem_disc_iff D x ε hε _).mpr ⟨(θtIn_lt_θtOut D x ε hε).le, le_rfl⟩)
      (fun h => lt_irrefl _ ((edgePoint_t_mem_ball_iff D x ε hε _).mp h).2)
  inner_interior := by
    intro p hp
    rw [interior_disc D x ε hε]
    rcases (inner_arcST₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hp with ⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩
    · exact (eval_cutStartS_mem_ball_iff D x M hε _ hk _).mpr hlt
    · exact eval_arc_mem_ball D x M hε _ _ (Or.inl hk)
    · exact (eval_cutEndT_mem_ball_iff D x M hε _ hk _).mpr hlt

theorem inner_arcTS₀_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    (arcTS₀ D x M hε).Inner ⟨u.1, (u.2, θ)⟩ ↔
      (M.kind u = StrandKind.cutStartT ∧ θ₀tIn D x ε < θ.val) ∨ M.kind u = StrandKind.arcTS ∨
        (M.kind u = StrandKind.cutEndS ∧ θ.val < θ₀sOut D x ε) := by
  have hval := strandOf_cutStartT_val D x M
  constructor
  · rintro ⟨r, hb, hp⟩
    obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
      ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1, r.1⟩ θ r.2).mp hp
    rcases (traversalBetween_span_two _ hval _ _ r).mp hb with ⟨hr, hlt⟩ | hr | ⟨hr, hlt⟩
    · left
      rw [hr] at hu
      refine ⟨?_, by subst hθ; exact hlt⟩
      rw [hu]; exact M.kind_strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT
    · right; left
      rw [hr] at hu
      rw [hu]; exact kind_cutStartT_add_one D x M
    · right; right
      rw [hr] at hu
      refine ⟨?_, by subst hθ; exact hlt⟩
      rw [hu]; exact kind_cutStartT_add_two D x M
  · rintro (⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩)
    · have hu := eq_strandOf_of_kind D x M StrandKind.occurs_cutStartT hk
      subst hu
      exact ⟨((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2, θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inl ⟨rfl, hlt⟩), rfl⟩
    · have hu : u = ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
          (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 1⟩ :=
        M.kind_injective (by rw [hk, kind_cutStartT_add_one D x M])
      subst hu
      exact ⟨(((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 1 :
          ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k), θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inr (Or.inl rfl)), rfl⟩
    · have hu : u = ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
          (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ :=
        M.kind_injective (by rw [hk, kind_cutStartT_add_two D x M])
      subst hu
      exact ⟨(((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2 :
          ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k), θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inr (Or.inr ⟨rfl, hlt⟩)), rfl⟩

theorem mem_arcTS₀_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    (arcTS₀ D x M hε).Mem ⟨u.1, (u.2, θ)⟩ ↔
      (M.kind u = StrandKind.cutStartT ∧ θ₀tIn D x ε ≤ θ.val) ∨ M.kind u = StrandKind.arcTS ∨
        (M.kind u = StrandKind.cutEndS ∧ θ.val ≤ θ₀sOut D x ε) := by
  constructor
  · rintro (h | h | h)
    · obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT) θ
        ⟨θ₀tIn D x ε, (θ₀_mem D x ε hε).2.2.1⟩).mp h
      left
      refine ⟨?_, by subst hθ; exact le_rfl⟩
      rw [hu]; exact M.kind_strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT
    · obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
        ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
          (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ θ
        ⟨θ₀sOut D x ε, (θ₀_mem D x ε hε).2.1⟩).mp h
      right; right
      refine ⟨?_, by subst hθ; exact le_rfl⟩
      rw [hu]; exact kind_cutStartT_add_two D x M
    · rcases (inner_arcTS₀_iff D x M hε u θ).mp h with ⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩
      · exact Or.inl ⟨hk, hlt.le⟩
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr ⟨hk, hlt.le⟩)
  · rintro (⟨hk, hle⟩ | hk | ⟨hk, hle⟩)
    · rcases hle.lt_or_eq with hlt | heq
      · exact ((inner_arcTS₀_iff D x M hε u θ).mpr (Or.inl ⟨hk, hlt⟩)).mem
      · left
        exact (Shadow.mk_eq_mk_iff u (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT)
          θ ⟨θ₀tIn D x ε, (θ₀_mem D x ε hε).2.2.1⟩).mpr
          ⟨eq_strandOf_of_kind D x M _ hk, Subtype.ext heq.symm⟩
    · exact ((inner_arcTS₀_iff D x M hε u θ).mpr (Or.inr (Or.inl hk))).mem
    · rcases hle.lt_or_eq with hlt | heq
      · exact ((inner_arcTS₀_iff D x M hε u θ).mpr (Or.inr (Or.inr ⟨hk, hlt⟩))).mem
      · right; left
        exact (Shadow.mk_eq_mk_iff u
          ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
            (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ θ
          ⟨θ₀sOut D x ε, (θ₀_mem D x ε hε).2.1⟩).mpr
          ⟨M.kind_injective (by rw [hk, kind_cutStartT_add_two D x M]), Subtype.ext heq⟩

theorem eval_arcTS₀_startPt : Γ₀.eval (arcTS₀ D x M hε).startPt =
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (θtIn D x ε) := by
  have h := eval_eq_edgePt_orig D x M (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT)
    ⟨θ₀tIn D x ε, (θ₀_mem D x ε hε).2.2.1⟩ (by rw [M.kind_strandOf]; nofun)
    (by rw [M.kind_strandOf]; nofun)
  rw [SpliceModel.orig, M.kind_strandOf] at h
  dsimp only at h
  have h2 : StrandKind.origParam ε StrandKind.cutStartT (θ₀tIn D x ε) = θtIn D x ε :=
    StrandKind.origParam_liftParam ε hε _ (by nofun) (by nofun) _
  rw [h2] at h
  exact h

theorem eval_arcTS₀_stopPt : Γ₀.eval (arcTS₀ D x M hε).stopPt =
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (θsOut D x ε) := by
  have h := eval_eq_edgePt_orig D x M (M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS)
    ⟨θ₀sOut D x ε, (θ₀_mem D x ε hε).2.1⟩ (by rw [M.kind_strandOf]; nofun)
    (by rw [M.kind_strandOf]; nofun)
  rw [SpliceModel.orig, M.kind_strandOf, strandOf_cutEndS_eq D x M] at h
  dsimp only at h
  have h2 : StrandKind.origParam ε StrandKind.cutEndS (θ₀sOut D x ε) = θsOut D x ε :=
    StrandKind.origParam_liftParam ε hε _ (by nofun) (by nofun) _
  rw [h2] at h
  exact h

theorem isArc_arcTS₀ : Γ₀.IsArc (disc D x ε) (arcTS₀ D x M hε) where
  start_ne_stop := by
    intro h
    have h1 : (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 =
        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2 := congrArg Prod.fst h
    have h2 := left_eq_add.mp h1
    have hv := strandOf_cutStartT_val D x M
    have h3 : (2 : ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartT
        StrandKind.occurs_cutStartT).1).k).val = 2 := by
      rw [ZMod.val_two_eq_two_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [h2, ZMod.val_zero] at h3
    exact absurd h3 (by norm_num)
  start_frontier := by
    rw [frontier_disc D x ε hε, eval_arcTS₀_startPt D x M hε]
    exact mem_sphere_of_mem_closedBall_not_mem_ball
      ((edgePoint_t_mem_disc_iff D x ε hε _).mpr ⟨le_rfl, (θtIn_lt_θtOut D x ε hε).le⟩)
      (fun h => lt_irrefl _ ((edgePoint_t_mem_ball_iff D x ε hε _).mp h).1)
  stop_frontier := by
    rw [frontier_disc D x ε hε, eval_arcTS₀_stopPt D x M hε]
    exact mem_sphere_of_mem_closedBall_not_mem_ball
      ((edgePoint_s_mem_disc_iff D x ε hε _).mpr ⟨(θsIn_lt_θsOut D x ε hε).le, le_rfl⟩)
      (fun h => lt_irrefl _ ((edgePoint_s_mem_ball_iff D x ε hε _).mp h).2)
  inner_interior := by
    intro p hp
    rw [interior_disc D x ε hε]
    rcases (inner_arcTS₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hp with ⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩
    · exact (eval_cutStartT_mem_ball_iff D x M hε _ hk _).mpr hlt
    · exact eval_arc_mem_ball D x M hε _ _ (Or.inr hk)
    · exact (eval_cutEndS_mem_ball_iff D x M hε _ hk _).mpr hlt

theorem eval_mem_disc_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔
      (arcST₀ D x M hε).Mem ⟨u.1, (u.2, θ)⟩ ∨ (arcTS₀ D x M hε).Mem ⟨u.1, (u.2, θ)⟩ := by
  rw [mem_arcST₀_iff D x M hε, mem_arcTS₀_iff D x M hε]
  rcases hk : M.kind u with e | _ | _ | _ | _ | _ | _
  · exact iff_of_false (eval_old_not_mem_disc D x M hε u e hk θ) (by simp)
  · rw [eval_cutStartS_mem_disc_iff D x M hε u hk θ]; simp
  · rw [eval_cutEndS_mem_disc_iff D x M hε u hk θ]; simp
  · rw [eval_cutStartT_mem_disc_iff D x M hε u hk θ]; simp
  · rw [eval_cutEndT_mem_disc_iff D x M hε u hk θ]; simp
  · exact iff_of_true (Metric.ball_subset_closedBall (eval_arc_mem_ball D x M hε u θ (Or.inl hk)))
      (by simp)
  · exact iff_of_true (Metric.ball_subset_closedBall (eval_arc_mem_ball D x M hε u θ (Or.inr hk)))
      (by simp)

theorem arcST₀_ne_arcTS₀ : arcST₀ D x M hε ≠ arcTS₀ D x M hε := by
  intro h
  have h1 : M.kind (Γ₀.strandOf (arcST₀ D x M hε).startPt) =
      M.kind (Γ₀.strandOf (arcTS₀ D x M hε).startPt) := by rw [h]
  have h2 : M.kind (Γ₀.strandOf (arcST₀ D x M hε).startPt) = StrandKind.cutStartS :=
    M.kind_strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS
  have h3 : M.kind (Γ₀.strandOf (arcTS₀ D x M hε).startPt) = StrandKind.cutStartT :=
    M.kind_strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT
  rw [h2, h3] at h1
  cases h1

theorem arcCover_toDiagram : Γ₀.ArcCover (disc D x ε) {arcST₀ D x M hε, arcTS₀ D x M hε} where
  isArc := by
    intro a ha
    rcases ha with rfl | rfl
    · exact isArc_arcST₀ D x M hε
    · exact isArc_arcTS₀ D x M hε
  mem_iff := by
    intro p
    have key := eval_mem_disc_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2
    constructor
    · intro h
      rcases key.mp h with h' | h'
      · exact ⟨_, Or.inl rfl, h'⟩
      · exact ⟨_, Or.inr rfl, h'⟩
    · rintro ⟨a, ha, hm⟩
      rcases ha with rfl | rfl
      · exact key.mpr (Or.inl hm)
      · exact key.mpr (Or.inr hm)
  disjoint := by
    intro a ha b hb hab p hpa hpb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab rfl
    · have h1 := (mem_arcST₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hpa
      have h2 := (mem_arcTS₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hpb
      rcases h1 with ⟨h1, -⟩ | h1 | ⟨h1, -⟩ <;> rcases h2 with ⟨h2, -⟩ | h2 | ⟨h2, -⟩ <;>
        rw [h1] at h2 <;> cases h2
    · have h1 := (mem_arcTS₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hpa
      have h2 := (mem_arcST₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hpb
      rcases h1 with ⟨h1, -⟩ | h1 | ⟨h1, -⟩ <;> rcases h2 with ⟨h2, -⟩ | h2 | ⟨h2, -⟩ <;>
        rw [h1] at h2 <;> cases h2
    · exact hab rfl

theorem arcST₀_start : Γ₀.eval (arcST₀ D x M hε).startPt = D.Γ.eval (arcS D x hε).startPt :=
  eval_arcST₀_startPt D x M hε
theorem arcST₀_stop : Γ₀.eval (arcST₀ D x M hε).stopPt = D.Γ.eval (arcT D x hε).stopPt :=
  eval_arcST₀_stopPt D x M hε
theorem arcTS₀_start : Γ₀.eval (arcTS₀ D x M hε).startPt = D.Γ.eval (arcT D x hε).startPt :=
  eval_arcTS₀_startPt D x M hε
theorem arcTS₀_stop : Γ₀.eval (arcTS₀ D x M hε).stopPt = D.Γ.eval (arcS D x hε).stopPt :=
  eval_arcTS₀_stopPt D x M hε

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
    κ.origParam ε θ.val ∈ Set.Ico (0:ℝ) 1 :=
  StrandKind.origParam_mem_Ico ε hε κ θ.2.1 θ.2.2

theorem origPt_param (q : Γ₀.Pt) :
    (origPt D x M q).2.2.val = (M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val :=
  clampIco_val_of_mem (origParam_mem D x M hε _ _)

/-- Outside the open disc, `origPt` traces the same point. -/
theorem eval_origPt (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    D.Γ.eval (origPt D x M q) = Γ₀.eval q := by
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_not_mem_interior D x M hε q hq
  have h : Γ₀.eval q =
      D.Γ.edgePt (M.orig ⟨q.1, q.2.1⟩) ((M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val) :=
    eval_eq_edgePt_orig D x M ⟨q.1, q.2.1⟩ q.2.2 h1 h2
  show D.Γ.edgePt (M.orig ⟨q.1, q.2.1⟩) (origPt D x M q).2.2.val = Γ₀.eval q
  rw [origPt_param D x M hε q]
  exact h.symm

theorem origPt_outside (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    D.Γ.eval (origPt D x M q) ∉ interior (disc D x ε) := by
  rw [eval_origPt D x M hε q hq]; exact hq

/-- U4 helper: a point of `D` on the original strand of a non-arc kind, at a parameter whose lift
is in `[0,1)`, is `origPt` of the corresponding point of `Γ₀`. -/
theorem exists_lift (κ : StrandKind D x) (hκo : κ.Occurs) (h1 : κ ≠ StrandKind.arcST)
    (h2 : κ ≠ StrandKind.arcTS) (e : D.Γ.Strand) (he : κ.orig = e) (θD : Set.Ico (0:ℝ) 1)
    (hl : 0 ≤ κ.liftParam ε θD.val ∧ κ.liftParam ε θD.val < 1) :
    ∃ q : Γ₀.Pt, origPt D x M q = ⟨e.1, (e.2, θD)⟩ ∧
      Γ₀.eval q = D.Γ.eval ⟨e.1, (e.2, θD)⟩ := by
  subst he
  refine ⟨⟨(M.strandOf κ hκo).1, ((M.strandOf κ hκo).2, ⟨κ.liftParam ε θD.val, hl⟩)⟩, ?_, ?_⟩
  · show (⟨(M.orig (M.strandOf κ hκo)).1, ((M.orig (M.strandOf κ hκo)).2,
      clampIco ((M.kind (M.strandOf κ hκo)).origParam ε (κ.liftParam ε θD.val)))⟩ : D.Γ.Pt) = _
    rw [SpliceModel.orig, M.kind_strandOf, StrandKind.origParam_liftParam ε hε κ h1 h2,
      clampIco_val_of_mem' θD]
  · rw [eval_eq_edgePt_orig D x M _ _ (by rw [M.kind_strandOf]; exact h1)
      (by rw [M.kind_strandOf]; exact h2), SpliceModel.orig, M.kind_strandOf]
    dsimp only
    rw [StrandKind.origParam_liftParam ε hε κ h1 h2]
    rfl

/-- U4 helper: surjectivity of `origPt` onto the outside points of `D`. -/
theorem exists_origPt_eq (p : D.Γ.Pt) (hp : D.Γ.eval p ∉ interior (disc D x ε)) :
    ∃ q : Γ₀.Pt, origPt D x M q = p ∧ Γ₀.eval q = D.Γ.eval p := by
  rw [interior_disc D x ε hε] at hp
  have hIn := θsIn_lt_cut D x ε hε
  have htIn := θtIn_lt_cut D x ε hε
  by_cases hs : (⟨p.1, p.2.1⟩ : D.Γ.Strand) = sS D x
  · have hp' : edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 p.2.2.val ∉
        Metric.ball (pt D x) (discRadius D x ε) := by
      rw [← hs]; exact hp
    rw [edgePoint_s_mem_ball_iff D x ε hε, not_and_or, not_lt, not_lt] at hp'
    have hpos1 : 0 < τs D x - ε := sub_pos.mpr hε.lt_τs
    have hpos2 : 0 < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
    rcases hp' with h | h
    · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε StrandKind.cutStartS
        StrandKind.occurs_cutStartS (by nofun) (by nofun) _ hs.symm p.2.2
        ⟨div_nonneg p.2.2.2.1 hpos1.le, (div_lt_one hpos1).mpr (by linarith)⟩
      exact ⟨q, hq1, hq2⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε StrandKind.cutEndS
        StrandKind.occurs_cutEndS (by nofun) (by nofun) _ hs.symm p.2.2
        ⟨div_nonneg (by linarith) hpos2.le, (div_lt_one hpos2).mpr (by linarith [p.2.2.2.2])⟩
      exact ⟨q, hq1, hq2⟩
  · by_cases ht : (⟨p.1, p.2.1⟩ : D.Γ.Strand) = tS D x
    · have hp' : edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 p.2.2.val ∉
          Metric.ball (pt D x) (discRadius D x ε) := by
        rw [← ht]; exact hp
      rw [edgePoint_t_mem_ball_iff D x ε hε, not_and_or, not_lt, not_lt] at hp'
      have hpos1 : 0 < τt D x - ε := sub_pos.mpr hε.lt_τt
      have hpos2 : 0 < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
      rcases hp' with h | h
      · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε StrandKind.cutStartT
          StrandKind.occurs_cutStartT (by nofun) (by nofun) _ ht.symm p.2.2
          ⟨div_nonneg p.2.2.2.1 hpos1.le, (div_lt_one hpos1).mpr (by linarith)⟩
        exact ⟨q, hq1, hq2⟩
      · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε StrandKind.cutEndT
          StrandKind.occurs_cutEndT (by nofun) (by nofun) _ ht.symm p.2.2
          ⟨div_nonneg (by linarith) hpos2.le, (div_lt_one hpos2).mpr (by linarith [p.2.2.2.2])⟩
        exact ⟨q, hq1, hq2⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε (StrandKind.old ⟨p.1, p.2.1⟩)
        (StrandKind.occurs_old hs ht) (by nofun) (by nofun) _ rfl p.2.2 ⟨p.2.2.2.1, p.2.2.2.2⟩
      exact ⟨q, hq1, hq2⟩

/-- `origPt` is a bijection from the outside traversal points of `Γ₀` onto those of `D`. -/
theorem origPt_bijective :
    Function.Bijective (fun q : Γ₀.Outside (disc D x ε) =>
      (⟨origPt D x M q.1, origPt_outside D x M hε q.1 q.2⟩ : D.Γ.Outside (disc D x ε))) := by
  constructor
  · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
    have h' : origPt D x M q = origPt D x M q' := congrArg Subtype.val h
    obtain ⟨horig, hcl⟩ :=
      (Shadow.mk_eq_mk_iff (M.orig ⟨q.1, q.2.1⟩) (M.orig ⟨q'.1, q'.2.1⟩) _ _).mp h'
    have hp : (M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val =
        (M.kind ⟨q'.1, q'.2.1⟩).origParam ε q'.2.2.val := by
      rw [← origPt_param D x M hε q, ← origPt_param D x M hε q']
      exact congrArg Subtype.val hcl
    obtain ⟨hu, hθ⟩ := eq_of_orig_eq D x M hε ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2
      (kind_ne_arc_of_not_mem_interior D x M hε q hq)
      (kind_ne_arc_of_not_mem_interior D x M hε q' hq') horig hp
    exact Subtype.ext ((Shadow.mk_eq_mk_iff ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2).mpr ⟨hu, hθ⟩)
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq1, hq2⟩ := exists_origPt_eq D x M hε p hp
    exact ⟨⟨q, by rw [hq2]; exact hp⟩, Subtype.ext hq1⟩

/-- The outside correspondence `φ`. -/
def outsideEquiv : D.Γ.Outside (disc D x ε) ≃ Γ₀.Outside (disc D x ε) :=
  (Equiv.ofBijective _ (origPt_bijective D x M hε)).symm

/-- U4 helper: `origPt` inverts `outsideEquiv` (`Equiv.ofBijective_apply_symm_apply`). -/
theorem origPt_outsideEquiv (q : D.Γ.Outside (disc D x ε)) :
    origPt D x M (outsideEquiv D x M hε q).1 = q.1 :=
  congrArg Subtype.val (Equiv.ofBijective_apply_symm_apply _ (origPt_bijective D x M hε) q)

theorem outsideEquiv_eval (q : D.Γ.Outside (disc D x ε)) :
    Γ₀.eval (outsideEquiv D x M hε q).1 = D.Γ.eval q.1 := by
  rw [← eval_origPt D x M hε _ (outsideEquiv D x M hε q).2, origPt_outsideEquiv D x M hε q]

theorem outsideEquiv_dir_pos (q : D.Γ.Outside (disc D x ε)) (hq : D.Γ.eval q.1 ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧
      Γ₀.dir (Γ₀.strandOf (outsideEquiv D x M hε q).1) = l • D.Γ.dir (D.Γ.strandOf q.1) := by
  have hφ := origPt_outsideEquiv D x M hε q
  have hout := (outsideEquiv D x M hε q).2
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_not_mem_interior D x M hε _ hout
  obtain ⟨l, hl, hdir⟩ := StrandKind.dir_eq_smul_orig ε hε _ h1 h2
  refine ⟨l, hl, ?_⟩
  rw [← hφ]
  show Γ₀.dir ⟨(outsideEquiv D x M hε q).1.1, (outsideEquiv D x M hε q).1.2.1⟩ =
    l • D.Γ.dir (M.orig ⟨(outsideEquiv D x M hε q).1.1, (outsideEquiv D x M hε q).1.2.1⟩)
  rw [M.dir_eq]
  exact hdir

/-- U4 helper: the arriving direction at a point of `Γ₀` strictly outside the disc is a positive
multiple of the arriving direction at its `origPt`. -/
theorem dir_strandBefore_origPt (q : Γ₀.Pt) (hout : Γ₀.eval q ∉ interior (disc D x ε))
    (hq : Γ₀.eval q ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧ Γ₀.dir (Γ₀.strandBefore q) =
      l • D.Γ.dir (D.Γ.strandBefore (origPt D x M q)) := by
  obtain ⟨i, m, θ⟩ := q
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_not_mem_interior D x M hε ⟨i, (m, θ)⟩ hout
  dsimp only at h1 h2
  have hparam : (origPt D x M ⟨i, (m, θ)⟩).2.2.val = (M.kind ⟨i, m⟩).origParam ε θ.val :=
    origPt_param D x M hε ⟨i, (m, θ)⟩
  have hev := eval_eq_edgePt_orig D x M ⟨i, m⟩ θ h1 h2
  dsimp only at hev
  by_cases hθ : θ.val = 0
  · have hne1 : M.kind ⟨i, m⟩ ≠ StrandKind.cutEndS := by
      intro hk
      apply hq
      rw [SpliceModel.orig, hk] at hev
      rw [hev, hθ]
      show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (τs D x + ε + 0 * (1 - τs D x - ε)) ∈ _
      rw [edgePoint_s_mem_disc_iff D x ε hε, zero_mul, add_zero]
      have := θsIn_lt_cut D x ε hε
      have := hε.pos
      exact ⟨by linarith, by linarith⟩
    have hne2 : M.kind ⟨i, m⟩ ≠ StrandKind.cutEndT := by
      intro hk
      apply hq
      rw [SpliceModel.orig, hk] at hev
      rw [hev, hθ]
      show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (τt D x + ε + 0 * (1 - τt D x - ε)) ∈ _
      rw [edgePoint_t_mem_disc_iff D x ε hε, zero_mul, add_zero]
      have := θtIn_lt_cut D x ε hε
      have := hε.pos
      exact ⟨by linarith, by linarith⟩
    have hz : (origPt D x M ⟨i, (m, θ)⟩).2.2.val = 0 := by
      rw [hparam, hθ]; exact StrandKind.origParam_zero ε _ hne1 hne2 h1 h2
    rw [Γ₀.strandBefore_of_zero _ hθ, D.Γ.strandBefore_of_zero _ hz]
    dsimp only
    obtain ⟨l, hl, hd⟩ := StrandKind.dir_pred_eq_smul ε hε (M.kind ⟨i, m⟩) hne1 hne2 h1 h2
    refine ⟨l, hl, ?_⟩
    have hp := M.kind_pred ⟨i, m⟩
    dsimp only at hp
    rw [M.dir_eq, hp]
    exact hd
  · have hz : (origPt D x M ⟨i, (m, θ)⟩).2.2.val ≠ 0 := by
      rw [hparam]; exact StrandKind.origParam_ne_zero ε hε _ h1 h2 θ.2.1 hθ
    rw [Γ₀.strandBefore_of_ne_zero _ hθ, D.Γ.strandBefore_of_ne_zero _ hz]
    obtain ⟨l, hl, hd⟩ := StrandKind.dir_eq_smul_orig ε hε (M.kind ⟨i, m⟩) h1 h2
    refine ⟨l, hl, ?_⟩
    show Γ₀.dir ⟨i, m⟩ = l • D.Γ.dir (M.orig ⟨i, m⟩)
    rw [M.dir_eq]
    exact hd

theorem outsideEquiv_dir_pos_before (q : D.Γ.Outside (disc D x ε))
    (hq : D.Γ.eval q.1 ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧ Γ₀.dir (Γ₀.strandBefore (outsideEquiv D x M hε q).1) =
      l • D.Γ.dir (D.Γ.strandBefore q.1) := by
  have hφ := origPt_outsideEquiv D x M hε q
  have hout := (outsideEquiv D x M hε q).2
  rw [← hφ] at hq ⊢
  rw [eval_origPt D x M hε _ hout] at hq
  exact dir_strandBefore_origPt D x M hε _ hout hq

/-- The outer crossings of `D` are the crossings other than `x`; all crossings of `D₀` are outer. -/
def outerEquiv : D.OuterCrossing (disc D x ε) ≃ (toDiagram D x M hε).OuterCrossing (disc D x ε) :=
  ((Equiv.subtypeEquivRight (fun y => by
      show D.Γ.crossingPoint y ∉ interior (disc D x ε) ↔ y ≠ x
      rw [inner_iff_D D x hε])).trans (crossingEquiv D x M hε).symm).trans
    (Equiv.subtypeUnivEquiv (no_inner_toDiagram D x M hε)).symm

theorem outsideEquiv_outerOverPt (y : D.OuterCrossing (disc D x ε)) :
    outsideEquiv D x M hε (D.outerOverPt y) =
      (toDiagram D x M hε).outerOverPt (outerEquiv D x M hε y) := by
  have hy : y.1 ≠ x := fun h => y.2 ((inner_iff_D D x hε y.1).mpr h)
  have horig : origCrossing D x M hε (outerEquiv D x M hε y).1 = y.1 :=
    origCrossing_liftCrossing D x M hε y.1 hy
  have hmem := overStrand₀_mem D x M hε (outerEquiv D x M hε y).1
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_mem D x M hε _ hmem
  have hs : M.orig (overStrand₀ D x M hε (outerEquiv D x M hε y).1) = D.overStrand y.1 := by
    rw [orig_overStrand₀ D x M hε (outerEquiv D x M hε y).1, horig]
  unfold outsideEquiv
  refine (Equiv.symm_apply_eq _).mpr ?_
  apply Subtype.ext
  show D.visitPt (D.overVisit y.1) = origPt D x M
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).overVisit (outerEquiv D x M hε y).1))
  refine (Shadow.mk_eq_mk_iff (D.overStrand y.1)
    (M.orig (overStrand₀ D x M hε (outerEquiv D x M hε y).1)) _ _).mpr ⟨hs.symm, Subtype.ext ?_⟩
  show D.crossingParam y.1 (D.over_mem y.1) = (origPt D x M
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).overVisit (outerEquiv D x M hε y).1))).2.2.val
  rw [origPt_param D x M hε
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).overVisit (outerEquiv D x M hε y).1))]
  show D.crossingParam y.1 (D.over_mem y.1) =
    (M.kind (overStrand₀ D x M hε (outerEquiv D x M hε y).1)).origParam ε
      ((toDiagram D x M hε).crossingParam (outerEquiv D x M hε y).1 hmem)
  rw [crossingParam_toDiagram D x M hε (outerEquiv D x M hε y).1 hmem,
    StrandKind.origParam_liftParam ε hε _ h1 h2]
  exact D.crossingParam_congr horig.symm hs.symm _ _

theorem outsideEquiv_outerUnderPt (y : D.OuterCrossing (disc D x ε)) :
    outsideEquiv D x M hε (D.outerUnderPt y) =
      (toDiagram D x M hε).outerUnderPt (outerEquiv D x M hε y) := by
  have hy : y.1 ≠ x := fun h => y.2 ((inner_iff_D D x hε y.1).mpr h)
  have horig : origCrossing D x M hε (outerEquiv D x M hε y).1 = y.1 :=
    origCrossing_liftCrossing D x M hε y.1 hy
  have hmem : (toDiagram D x M hε).underStrand (outerEquiv D x M hε y).1 ∈
      (outerEquiv D x M hε y).1.val := (toDiagram D x M hε).under_mem _
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_mem D x M hε _ hmem
  have hs : M.orig ((toDiagram D x M hε).underStrand (outerEquiv D x M hε y).1) =
      D.underStrand y.1 := by
    rw [toDiagram_underStrand_orig D x M hε (outerEquiv D x M hε y).1, horig]
  unfold outsideEquiv
  refine (Equiv.symm_apply_eq _).mpr ?_
  apply Subtype.ext
  show D.visitPt (D.underVisit y.1) = origPt D x M
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).underVisit (outerEquiv D x M hε y).1))
  refine (Shadow.mk_eq_mk_iff (D.underStrand y.1)
    (M.orig ((toDiagram D x M hε).underStrand (outerEquiv D x M hε y).1)) _ _).mpr
    ⟨hs.symm, Subtype.ext ?_⟩
  show D.crossingParam y.1 (D.under_mem y.1) = (origPt D x M
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).underVisit (outerEquiv D x M hε y).1))).2.2.val
  rw [origPt_param D x M hε
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).underVisit (outerEquiv D x M hε y).1))]
  show D.crossingParam y.1 (D.under_mem y.1) =
    (M.kind ((toDiagram D x M hε).underStrand (outerEquiv D x M hε y).1)).origParam ε
      ((toDiagram D x M hε).crossingParam (outerEquiv D x M hε y).1 hmem)
  rw [crossingParam_toDiagram D x M hε (outerEquiv D x M hε y).1 hmem,
    StrandKind.origParam_liftParam ε hε _ h1 h2]
  exact D.crossingParam_congr horig.symm hs.symm _ _

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

/-! ### 7-pre. A small `ZMod.val` toolbox for the index arithmetic of the concrete models
(U5-concrete-models).  Everything here is elementary; the lemmas are phrased so that every use in
§7a/§7b is a `rw` followed by `omega`, `ring` or `module`. -/

theorem three_le_kI : 3 ≤ kI D x := (D.Γ.comp (sS D x).1).hk
theorem three_le_kJ : 3 ≤ kJ D x := (D.Γ.comp (tS D x).1).hk

theorem zval_one_of_two_le {n : ℕ} (hn : 2 ≤ n) : (1 : ZMod n).val = 1 := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]

theorem zval_add_one_of_lt {n : ℕ} [NeZero n] (m : ZMod n) (h : m.val + 1 < n) :
    (m + 1).val = m.val + 1 := by
  have h1 : (1 : ZMod n).val = 1 := zval_one_of_two_le (by omega)
  rw [ZMod.val_add_of_lt (by rw [h1]; exact h), h1]

theorem zval_add_one_of_eq {n : ℕ} [NeZero n] (m : ZMod n) (h : m.val + 1 = n) : (m + 1).val = 0 := by
  rw [ZMod.val_eq_zero]
  have : ((m.val + 1 : ℕ) : ZMod n) = 0 := by rw [h, ZMod.natCast_self]
  rwa [Nat.cast_succ, ZMod.natCast_zmod_val] at this

theorem zval_sub_one_of_pos {n : ℕ} [NeZero n] (m : ZMod n) (h : 0 < m.val) :
    (m - 1).val = m.val - 1 := by
  have hn : 2 ≤ n := by have := ZMod.val_lt m; omega
  have h1 : (1 : ZMod n).val = 1 := zval_one_of_two_le hn
  rw [ZMod.val_sub (by rw [h1]; exact h), h1]

/-- `(n - c : ℕ)` cast to `ZMod n` is `-c`. -/
theorem zcast_sub_self {n c : ℕ} (hc : c ≤ n) : ((n - c : ℕ) : ZMod n) = -(c : ZMod n) := by
  rw [Nat.cast_sub hc, ZMod.natCast_self, zero_sub]

theorem zval_sub_one_of_zero {n : ℕ} [NeZero n] (m : ZMod n) (h : m.val = 0) : (m - 1).val = n - 1 := by
  rw [ZMod.val_eq_zero] at h
  subst h
  have hn : 0 < n := NeZero.pos n
  rw [zero_sub, ← Nat.cast_one, ← zcast_sub_self (by omega), ZMod.val_natCast_of_lt (by omega)]

theorem zcast_pred {n v : ℕ} (hv : 0 < v) : ((v - 1 : ℕ) : ZMod n) = (v : ZMod n) - 1 := by
  rw [Nat.cast_sub hv, Nat.cast_one]

theorem nat_eq_of_zcast_eq {n v v' : ℕ} (hv : v < n) (hv' : v' < n) (h : (v : ZMod n) = v') : v = v' := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hv, ZMod.val_natCast_of_lt hv'] at this

theorem zcast_ne_zero_of_lt {n v : ℕ} (h0 : 0 < v) (hv : v < n) : (v : ZMod n) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

/-- A strand with first component `i` is `⟨i, its label transported by value⟩`. -/
theorem Strand_eq_mk_val {Γ : Shadow} {e : Γ.Strand} {i : Fin Γ.c} (hi : i = e.1) :
    e = ⟨i, (e.2.val : ZMod (Γ.comp i).k)⟩ := by
  obtain ⟨l, c⟩ := e
  dsimp only at hi
  subst hi
  simp

theorem Strand_mk_eq_mk_iff {Γ : Shadow} {i : Fin Γ.c} {c c' : ZMod (Γ.comp i).k} :
    (⟨i, c⟩ : Γ.Strand) = ⟨i, c'⟩ ↔ c = c' := by
  simp

theorem Strand_mk_ne_mk_of_ne {Γ : Shadow} {i j : Fin Γ.c} {c : ZMod (Γ.comp i).k}
    {c' : ZMod (Γ.comp j).k} (h : i ≠ j) : (⟨i, c⟩ : Γ.Strand) ≠ ⟨j, c'⟩ :=
  fun heq => h (congrArg Sigma.fst heq)

/-- The vertex identities used to place the cut points: `P_i (a + 1 + (k_i − 1)) = P_i a`. -/
theorem Pi_a_wrap : Pi D x (aS D x + 1 + ((kI D x - 1 : ℕ) : ZMod (kI D x))) = D.Γ.tail (sS D x) := by
  have := three_le_kI D x
  rw [zcast_sub_self (by omega), Nat.cast_one, add_neg_cancel_right]; rfl

theorem Pj_b_wrap : Pj D x (bT D x + 1 + ((kJ D x - 1 : ℕ) : ZMod (kJ D x))) = D.Γ.tail (tS D x) := by
  have := three_le_kJ D x
  rw [zcast_sub_self (by omega), Nat.cast_one, add_neg_cancel_right]; rfl

theorem tail_sS : D.Γ.tail (sS D x) = Pi D x (aS D x) := rfl
theorem tail_tS : D.Γ.tail (tS D x) = Pj D x (bT D x) := rfl
theorem es_eq : es D x = Pi D x (aS D x + 1) - Pi D x (aS D x) := rfl
theorem et_eq : et D x = Pj D x (bT D x + 1) - Pj D x (bT D x) := rfl

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
  have hj : (tS D x).1 ∈ Finset.univ.erase (sS D x).1 := by
    rw [Finset.mem_erase]; exact ⟨Ne.symm h, Finset.mem_univ _⟩
  have h1 : 0 < (Finset.univ.erase (sS D x).1).card := Finset.card_pos.mpr ⟨_, hj⟩
  unfold othersM
  rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin] at *
  omega

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

/-! #### Index arithmetic for the mixed shadow (U5) -/

/-- Case analysis on the strands of the mixed shadow: the merged component, or an untouched one. -/
theorem mixedShadow_strand_cases {P : (mixedShadow D x ε).Strand → Prop}
    (h0 : ∀ m : ZMod (kI D x + kJ D x + 4), P ⟨(0 : Fin ((othersM D x).card + 1)), m⟩)
    (hs : ∀ (l : Fin (othersM D x).card)
      (m : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k), P ⟨l.succ, m⟩)
    (u : (mixedShadow D x ε).Strand) : P u := by
  obtain ⟨l, m⟩ := u
  induction l using Fin.cases with
  | zero => exact h0 m
  | succ l => exact hs l m

theorem mixedKind_zero (m : ZMod (kI D x + kJ D x + 4)) :
    mixedKind D x ε ⟨(0 : Fin ((othersM D x).card + 1)), m⟩ = mergedKindIdx D x m.val := rfl

theorem mixedKind_succ (l : Fin (othersM D x).card)
    (m : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k) :
    mixedKind D x ε ⟨l.succ, m⟩ =
      StrandKind.old ⟨(othersM D x).orderEmbOfFin rfl l, (m.val : ZMod _)⟩ := rfl

theorem mixedShadow_tail_zero (m : ZMod (kI D x + kJ D x + 4)) :
    (mixedShadow D x ε).tail ⟨(0 : Fin ((othersM D x).card + 1)), m⟩ = mergedTuple D x ε m := rfl

theorem mixedShadow_dir_zero (m : ZMod (kI D x + kJ D x + 4)) :
    (mixedShadow D x ε).dir ⟨(0 : Fin ((othersM D x).card + 1)), m⟩ =
      mergedTuple D x ε (m + 1) - mergedTuple D x ε m := rfl

theorem mixedShadow_tail_succ (l : Fin (othersM D x).card)
    (m : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k) :
    (mixedShadow D x ε).tail ⟨l.succ, m⟩ = D.Γ.tail ⟨(othersM D x).orderEmbOfFin rfl l, m⟩ := rfl

theorem mixedShadow_dir_succ (l : Fin (othersM D x).card)
    (m : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k) :
    (mixedShadow D x ε).dir ⟨l.succ, m⟩ = D.Γ.dir ⟨(othersM D x).orderEmbOfFin rfl l, m⟩ := rfl

theorem mixedShadow_comp_succ_k (l : Fin (othersM D x).card) :
    ((mixedShadow D x ε).comp l.succ).k = (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k := rfl

/-- The untouched components are neither `i` nor `j`. -/
theorem orderEmbOfFin_othersM_ne (l : Fin (othersM D x).card) :
    (othersM D x).orderEmbOfFin rfl l ≠ (sS D x).1 ∧ (othersM D x).orderEmbOfFin rfl l ≠ (tS D x).1 := by
  have := Finset.orderEmbOfFin_mem (othersM D x) rfl l
  simp only [othersM, Finset.mem_erase, Finset.mem_univ, and_true] at this
  exact ⟨this.2, this.1⟩

/-- The eight blocks of labels of the merged component. -/
theorem merged_block (v : ℕ) (hv : v < kI D x + kJ D x + 4) :
    v < kI D x - 1 ∨ v = kI D x - 1 ∨ v = kI D x ∨ v = kI D x + 1 ∨
    (kI D x + 2 ≤ v ∧ v < kI D x + 1 + kJ D x) ∨ v = kI D x + 1 + kJ D x ∨
    v = kI D x + 2 + kJ D x ∨ v = kI D x + 3 + kJ D x := by
  omega

theorem mergedKindIdx_of_lt {v : ℕ} (hv : v < kI D x - 1) :
    mergedKindIdx D x v = StrandKind.old ⟨(sS D x).1, aS D x + 1 + (v : ZMod (kI D x))⟩ := by
  unfold mergedKindIdx; split_ifs; rfl

theorem mergedKindIdx_eq_cutStartS {v : ℕ} (hv : v = kI D x - 1) :
    mergedKindIdx D x v = StrandKind.cutStartS := by
  have := three_le_kI D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_arcST {v : ℕ} (hv : v = kI D x) : mergedKindIdx D x v = StrandKind.arcST := by
  have := three_le_kI D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_cutEndT {v : ℕ} (hv : v = kI D x + 1) :
    mergedKindIdx D x v = StrandKind.cutEndT := by
  have := three_le_kI D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_of_j {v : ℕ} (h1 : kI D x + 2 ≤ v) (h2 : v < kI D x + 1 + kJ D x) :
    mergedKindIdx D x v =
      StrandKind.old ⟨(tS D x).1, bT D x + 1 + ((v - (kI D x + 2) : ℕ) : ZMod (kJ D x))⟩ := by
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_cutStartT {v : ℕ} (hv : v = kI D x + 1 + kJ D x) :
    mergedKindIdx D x v = StrandKind.cutStartT := by
  have := three_le_kJ D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_arcTS {v : ℕ} (hv : v = kI D x + 2 + kJ D x) :
    mergedKindIdx D x v = StrandKind.arcTS := by
  have := three_le_kJ D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_cutEndS {v : ℕ} (hv : v = kI D x + 3 + kJ D x) :
    mergedKindIdx D x v = StrandKind.cutEndS := by
  have := three_le_kJ D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedTuple_of_lt (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val < kI D x) :
    mergedTuple D x ε m = Pi D x (aS D x + 1 + (m.val : ZMod (kI D x))) := by
  unfold mergedTuple; split_ifs; rfl

theorem mergedTuple_eq_sMinus (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val = kI D x) :
    mergedTuple D x ε m = sMinus D x ε := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

theorem mergedTuple_eq_tPlus (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val = kI D x + 1) :
    mergedTuple D x ε m = tPlus D x ε := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

theorem mergedTuple_of_j (m : ZMod (kI D x + kJ D x + 4)) (h1 : kI D x + 2 ≤ m.val)
    (h2 : m.val < kI D x + 2 + kJ D x) :
    mergedTuple D x ε m = Pj D x (bT D x + 1 + ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x))) := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

theorem mergedTuple_eq_tMinus (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val = kI D x + 2 + kJ D x) :
    mergedTuple D x ε m = tMinus D x ε := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

theorem mergedTuple_eq_sPlus (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val = kI D x + 3 + kJ D x) :
    mergedTuple D x ε m = sPlus D x ε := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

/-- An old kind of the merged component lies on the component of `s` or of `t`. -/
theorem mergedKindIdx_old_fst {v : ℕ} (hv : v < kI D x + kJ D x + 4) (e : D.Γ.Strand)
    (he : mergedKindIdx D x v = StrandKind.old e) : e.1 = (sS D x).1 ∨ e.1 = (tS D x).1 := by
  rcases merged_block D x v hv with h1 | h1 | h1 | h1 | ⟨h1, h1'⟩ | h1 | h1 | h1
  · rw [mergedKindIdx_of_lt D x h1] at he; exact Or.inl (congrArg Sigma.fst (StrandKind.old.inj he)).symm
  · rw [mergedKindIdx_eq_cutStartS D x h1] at he; cases he
  · rw [mergedKindIdx_eq_arcST D x h1] at he; cases he
  · rw [mergedKindIdx_eq_cutEndT D x h1] at he; cases he
  · rw [mergedKindIdx_of_j D x h1 h1'] at he; exact Or.inr (congrArg Sigma.fst (StrandKind.old.inj he)).symm
  · rw [mergedKindIdx_eq_cutStartT D x h1] at he; cases he
  · rw [mergedKindIdx_eq_arcTS D x h1] at he; cases he
  · rw [mergedKindIdx_eq_cutEndS D x h1] at he; cases he

/-- The label of an old strand `a + 1 + v` of a `n`-gon, recovered from its value. -/
theorem zmod_code_eq {n : ℕ} [NeZero n] (a : ZMod n) {v : ℕ} (hv : v < n) :
    ((a + 1 + (v : ZMod n)).val + (n - 1) - a.val) % n = v := by
  have hn := NeZero.pos n
  have ha := ZMod.val_lt a
  have h1 : a.val ≤ (a + 1 + (v : ZMod n)).val + (n - 1) := by omega
  have h2 : (((a + 1 + (v : ZMod n)).val + (n - 1) - a.val : ℕ) : ZMod n) = (v : ZMod n) := by
    rw [Nat.cast_sub h1, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      zcast_sub_self (by omega), Nat.cast_one]
    ring
  have := congrArg ZMod.val h2
  rwa [ZMod.val_natCast, ZMod.val_natCast_of_lt hv] at this

/-- A left inverse of `mergedKindIdx` on the labels of the merged component. -/
def mergedCode : StrandKind D x → ℕ
  | .old e =>
      if e.1 = (sS D x).1 then (e.2.val + (kI D x - 1) - (aS D x).val) % kI D x
      else kI D x + 2 + (e.2.val + (kJ D x - 1) - (bT D x).val) % kJ D x
  | .cutStartS => kI D x - 1
  | .arcST => kI D x
  | .cutEndT => kI D x + 1
  | .cutStartT => kI D x + 1 + kJ D x
  | .arcTS => kI D x + 2 + kJ D x
  | .cutEndS => kI D x + 3 + kJ D x

theorem mergedCode_mergedKindIdx (h : (sS D x).1 ≠ (tS D x).1) {v : ℕ}
    (hv : v < kI D x + kJ D x + 4) : mergedCode D x (mergedKindIdx D x v) = v := by
  have hk := three_le_kI D x
  have hk' := three_le_kJ D x
  rcases merged_block D x v hv with h1 | h1 | h1 | h1 | ⟨h1, h1'⟩ | h1 | h1 | h1
  · rw [mergedKindIdx_of_lt D x h1]
    simp only [mergedCode, ↓reduceIte]
    exact zmod_code_eq (aS D x) (by omega)
  · rw [mergedKindIdx_eq_cutStartS D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_eq_arcST D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_eq_cutEndT D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_of_j D x h1 h1']
    simp only [mergedCode]
    rw [ite_eq_right (Ne.symm h), zmod_code_eq (bT D x) (by omega)]
    omega
  · rw [mergedKindIdx_eq_cutStartT D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_eq_arcTS D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_eq_cutEndS D x h1]; simp only [mergedCode]; omega

/-- The kind map of the merged component is injective on its labels. -/
theorem mergedKindIdx_inj (h : (sS D x).1 ≠ (tS D x).1) {v v' : ℕ} (hv : v < kI D x + kJ D x + 4)
    (hv' : v' < kI D x + kJ D x + 4) (heq : mergedKindIdx D x v = mergedKindIdx D x v') : v = v' := by
  have := congrArg (mergedCode D x) heq
  rwa [mergedCode_mergedKindIdx D x h hv, mergedCode_mergedKindIdx D x h hv'] at this

/-- The mixed shadow is a splice model (index arithmetic on `ZMod.val`). -/
def mixedModel (h : (sS D x).1 ≠ (tS D x).1) : SpliceModel D x ε (mixedShadow D x ε) where
  kind := mixedKind D x ε
  kind_injective := by
    show ∀ u u' : (mixedShadow D x ε).Strand, mixedKind D x ε u = mixedKind D x ε u' → u = u'
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      refine mixedShadow_strand_cases D x ε ?_ ?_
      · intro m' heq
        rw [mixedKind_zero, mixedKind_zero] at heq
        rw [ZMod.val_injective _ (mergedKindIdx_inj D x h (ZMod.val_lt m) (ZMod.val_lt m') heq)]
      · intro l' m' heq
        exfalso
        rw [mixedKind_zero, mixedKind_succ] at heq
        rcases mergedKindIdx_old_fst D x (ZMod.val_lt m) _ heq with h1 | h1
        · exact (orderEmbOfFin_othersM_ne D x l').1 h1
        · exact (orderEmbOfFin_othersM_ne D x l').2 h1
    · intro l m
      refine mixedShadow_strand_cases D x ε ?_ ?_
      · intro m' heq
        exfalso
        rw [mixedKind_zero, mixedKind_succ] at heq
        rcases mergedKindIdx_old_fst D x (ZMod.val_lt m') _ heq.symm with h1 | h1
        · exact (orderEmbOfFin_othersM_ne D x l).1 h1
        · exact (orderEmbOfFin_othersM_ne D x l).2 h1
      · intro l' m' heq
        rw [mixedKind_succ, mixedKind_succ] at heq
        have h1 := StrandKind.old.inj heq
        rw [Sigma.mk.inj_iff] at h1
        obtain ⟨h1, h2⟩ := h1
        have hl : l = l' := ((othersM D x).orderEmbOfFin rfl).injective h1
        subst hl
        have h3 := eq_of_heq h2
        simp only [ZMod.natCast_zmod_val] at h3
        rw [h3]
  kind_surj := by
    intro κ hκ
    have hk := three_le_kI D x
    have hk' := three_le_kJ D x
    cases κ with
    | old e =>
      obtain ⟨hs, ht⟩ := hκ
      have hs' : e ≠ sS D x := fun h' => hs (by rw [h'])
      have ht' : e ≠ tS D x := fun h' => ht (by rw [h'])
      obtain ⟨l₀, c⟩ := e
      by_cases hi : l₀ = (sS D x).1
      · subst hi
        have hca : c ≠ aS D x := fun h' => hs' (Sigma.ext rfl (heq_of_eq h'))
        obtain ⟨v, hv⟩ : ∃ v, v = (c - aS D x - 1).val := ⟨_, rfl⟩
        have hv1 : v < kI D x := by rw [hv]; exact ZMod.val_lt _
        have hv2 : v ≠ kI D x - 1 := by
          intro h2
          apply hca
          have h3 : ((c - aS D x - 1).val : ZMod (kI D x)) = c - aS D x - 1 := ZMod.natCast_zmod_val _
          rw [← hv, h2, zcast_sub_self (by omega), Nat.cast_one] at h3
          linear_combination -h3
        refine ⟨⟨(0 : Fin ((othersM D x).card + 1)), (v : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
        rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega), mergedKindIdx_of_lt D x (by omega)]
        simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        rw [hv, ZMod.natCast_zmod_val]; ring
      · by_cases hj : l₀ = (tS D x).1
        · subst hj
          have hcb : c ≠ bT D x := fun h' => ht' (Sigma.ext rfl (heq_of_eq h'))
          obtain ⟨w, hw⟩ : ∃ w, w = (c - bT D x - 1).val := ⟨_, rfl⟩
          have hw1 : w < kJ D x := by rw [hw]; exact ZMod.val_lt _
          have hw2 : w ≠ kJ D x - 1 := by
            intro h2
            apply hcb
            have h3 : ((c - bT D x - 1).val : ZMod (kJ D x)) = c - bT D x - 1 := ZMod.natCast_zmod_val _
            rw [← hw, h2, zcast_sub_self (by omega), Nat.cast_one] at h3
            linear_combination -h3
          refine ⟨⟨(0 : Fin ((othersM D x).card + 1)),
            ((kI D x + 2 + w : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
          rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega),
            mergedKindIdx_of_j D x (by omega) (by omega)]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          have : kI D x + 2 + w - (kI D x + 2) = w := by omega
          rw [this, hw, ZMod.natCast_zmod_val]; ring
        · have hmem : l₀ ∈ othersM D x := by
            simp only [othersM, Finset.mem_erase, Finset.mem_univ, and_true]
            exact ⟨hj, hi⟩
          have hrange : l₀ ∈ Set.range ((othersM D x).orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]; exact hmem
          obtain ⟨l, hl⟩ := hrange
          subst hl
          exact ⟨⟨l.succ, c⟩, by rw [mixedKind_succ, ZMod.natCast_zmod_val]⟩
    | cutStartS =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)), ((kI D x - 1 : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_cutStartS D x rfl
    | cutEndS =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)),
        ((kI D x + 3 + kJ D x : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_cutEndS D x rfl
    | cutStartT =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)),
        ((kI D x + 1 + kJ D x : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_cutStartT D x rfl
    | cutEndT =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)), ((kI D x + 1 : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_cutEndT D x rfl
    | arcST =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)), ((kI D x : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_arcST D x rfl
    | arcTS =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)),
        ((kI D x + 2 + kJ D x : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_arcTS D x rfl
  kind_occurs := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      rw [mixedKind_zero]
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · rw [mergedKindIdx_of_lt D x hv]
        refine StrandKind.occurs_old ?_ (Strand_mk_ne_mk_of_ne h)
        intro heq
        have heq2 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) =
            ⟨(sS D x).1, (sS D x).2⟩ := heq
        have heq' := Strand_mk_eq_mk_iff.mp heq2
        have h2 : ((m.val + 1 : ℕ) : ZMod (kI D x)) = 0 := by
          push_cast; linear_combination heq'
        exact zcast_ne_zero_of_lt (by omega) (by omega) h2
      · rw [mergedKindIdx_eq_cutStartS D x hv]; exact StrandKind.occurs_cutStartS
      · rw [mergedKindIdx_eq_arcST D x hv]; exact StrandKind.occurs_arcST
      · rw [mergedKindIdx_eq_cutEndT D x hv]; exact StrandKind.occurs_cutEndT
      · rw [mergedKindIdx_of_j D x hv hv']
        refine StrandKind.occurs_old (Strand_mk_ne_mk_of_ne (Ne.symm h)) ?_
        intro heq
        have heq2 : (⟨(tS D x).1, bT D x + 1 + ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x))⟩ :
            D.Γ.Strand) = ⟨(tS D x).1, (tS D x).2⟩ := heq
        have heq' := Strand_mk_eq_mk_iff.mp heq2
        have h2 : ((m.val - (kI D x + 2) + 1 : ℕ) : ZMod (kJ D x)) = 0 := by
          push_cast; linear_combination heq'
        exact zcast_ne_zero_of_lt (by omega) (by omega) h2
      · rw [mergedKindIdx_eq_cutStartT D x hv]; exact StrandKind.occurs_cutStartT
      · rw [mergedKindIdx_eq_arcTS D x hv]; exact StrandKind.occurs_arcTS
      · rw [mergedKindIdx_eq_cutEndS D x hv]; exact StrandKind.occurs_cutEndS
    · intro l m
      rw [mixedKind_succ]
      exact StrandKind.occurs_old (Strand_mk_ne_mk_of_ne (orderEmbOfFin_othersM_ne D x l).1)
        (Strand_mk_ne_mk_of_ne (orderEmbOfFin_othersM_ne D x l).2)
  kind_pred := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      show mixedKind D x ε ⟨(0 : Fin ((othersM D x).card + 1)), (m - 1 : ZMod (kI D x + kJ D x + 4))⟩ =
        (mixedKind D x ε ⟨(0 : Fin ((othersM D x).card + 1)), m⟩).pred
      rw [mixedKind_zero, mixedKind_zero]
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · -- old strands of the component of `s`
        rw [mergedKindIdx_of_lt D x hv]
        rcases Nat.eq_zero_or_pos m.val with h0 | h0
        · rw [zval_sub_one_of_zero m h0, mergedKindIdx_eq_cutEndS D x (by omega), h0, Nat.cast_zero,
            add_zero]
          simp only [StrandKind.pred, ↓reduceIte]
        · rw [zval_sub_one_of_pos m h0, mergedKindIdx_of_lt D x (by omega)]
          simp only [StrandKind.pred]
          have hne1 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
              ⟨(sS D x).1, (sS D x).2 + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : (m.val : ZMod (kI D x)) = 0 := by linear_combination heq'
            exact zcast_ne_zero_of_lt h0 (by omega) h2
          rw [ite_eq_right hne1, ite_eq_right (Strand_mk_ne_mk_of_ne h)]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          rw [zcast_pred h0]; ring
      · -- cutStartS at `k_i − 1`: predecessor `old ⟨i, a − 1⟩` at `k_i − 2`
        rw [mergedKindIdx_eq_cutStartS D x hv, zval_sub_one_of_pos m (by omega), hv,
          mergedKindIdx_of_lt D x (by omega)]
        simp only [StrandKind.pred, StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        have : kI D x - 1 - 1 = kI D x - 2 := by omega
        rw [this, zcast_sub_self (by omega)]
        push_cast; ring
      · rw [mergedKindIdx_eq_arcST D x hv, zval_sub_one_of_pos m (by omega),
          mergedKindIdx_eq_cutStartS D x (by omega)]; rfl
      · rw [mergedKindIdx_eq_cutEndT D x hv, zval_sub_one_of_pos m (by omega),
          mergedKindIdx_eq_arcST D x (by omega)]; rfl
      · -- old strands of the component of `t`
        rw [mergedKindIdx_of_j D x hv hv']
        rcases Nat.lt_or_ge (kI D x + 2) m.val with h0 | h0
        · rw [zval_sub_one_of_pos m (by omega), mergedKindIdx_of_j D x (by omega) (by omega)]
          simp only [StrandKind.pred]
          have hne2 : (⟨(tS D x).1, bT D x + 1 + ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x))⟩ :
              D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x)) = 0 := by linear_combination heq'
            exact zcast_ne_zero_of_lt (by omega) (by omega) h2
          rw [ite_eq_right (Strand_mk_ne_mk_of_ne (Ne.symm h)), ite_eq_right hne2]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          have : m.val - 1 - (kI D x + 2) = m.val - (kI D x + 2) - 1 := by omega
          rw [this, zcast_pred (by omega)]; ring
        · have hv2 : m.val = kI D x + 2 := by omega
          rw [zval_sub_one_of_pos m (by omega), mergedKindIdx_eq_cutEndT D x (by omega), hv2]
          have : kI D x + 2 - (kI D x + 2) = 0 := by omega
          rw [this, Nat.cast_zero, add_zero]
          simp only [StrandKind.pred, ↓reduceIte]
          rw [ite_eq_right (Strand_mk_ne_mk_of_ne (Ne.symm h))]
      · -- cutStartT at `k_i + 1 + k_j`: predecessor `old ⟨j, b − 1⟩`
        rw [mergedKindIdx_eq_cutStartT D x hv, zval_sub_one_of_pos m (by omega), hv,
          mergedKindIdx_of_j D x (by omega) (by omega)]
        simp only [StrandKind.pred, StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        have : kI D x + 1 + kJ D x - 1 - (kI D x + 2) = kJ D x - 2 := by omega
        rw [this, zcast_sub_self (by omega)]
        push_cast; ring
      · rw [mergedKindIdx_eq_arcTS D x hv, zval_sub_one_of_pos m (by omega),
          mergedKindIdx_eq_cutStartT D x (by omega)]; rfl
      · rw [mergedKindIdx_eq_cutEndS D x hv, zval_sub_one_of_pos m (by omega),
          mergedKindIdx_eq_arcTS D x (by omega)]; rfl
    · intro l m
      show mixedKind D x ε ⟨l.succ, (m - 1 : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k)⟩ =
        (mixedKind D x ε ⟨l.succ, m⟩).pred
      rw [mixedKind_succ, mixedKind_succ]
      simp only [StrandKind.pred, ZMod.natCast_zmod_val]
      rw [ite_eq_right (Strand_mk_ne_mk_of_ne (orderEmbOfFin_othersM_ne D x l).1),
        ite_eq_right (Strand_mk_ne_mk_of_ne (orderEmbOfFin_othersM_ne D x l).2)]
  tail_eq := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      rw [mixedShadow_tail_zero, mixedKind_zero]
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · rw [mergedKindIdx_of_lt D x hv, mergedTuple_of_lt D x ε m (by omega)]; rfl
      · rw [mergedKindIdx_eq_cutStartS D x hv, mergedTuple_of_lt D x ε m (by omega), hv, Pi_a_wrap]; rfl
      · rw [mergedKindIdx_eq_arcST D x hv, mergedTuple_eq_sMinus D x ε m hv]; rfl
      · rw [mergedKindIdx_eq_cutEndT D x hv, mergedTuple_eq_tPlus D x ε m hv]; rfl
      · rw [mergedKindIdx_of_j D x hv hv', mergedTuple_of_j D x ε m hv (by omega)]; rfl
      · rw [mergedKindIdx_eq_cutStartT D x hv, mergedTuple_of_j D x ε m (by omega) (by omega), hv]
        have : kI D x + 1 + kJ D x - (kI D x + 2) = kJ D x - 1 := by omega
        rw [this, Pj_b_wrap]; rfl
      · rw [mergedKindIdx_eq_arcTS D x hv, mergedTuple_eq_tMinus D x ε m hv]; rfl
      · rw [mergedKindIdx_eq_cutEndS D x hv, mergedTuple_eq_sPlus D x ε m hv]; rfl
    · intro l m
      rw [mixedShadow_tail_succ, mixedKind_succ]
      simp only [StrandKind.tail, ZMod.natCast_zmod_val]
  dir_eq := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      rw [mixedShadow_dir_zero, mixedKind_zero]
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_of_lt D x hv, mergedTuple_of_lt D x ε (m + 1) (by omega),
          mergedTuple_of_lt D x ε m (by omega), h1, Nat.cast_succ]
        simp only [StrandKind.dir, Shadow.dir_mk, edge, add_assoc]
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_cutStartS D x hv, mergedTuple_eq_sMinus D x ε (m + 1) (by omega),
          mergedTuple_of_lt D x ε m (by omega), hv, Pi_a_wrap]
        simp only [StrandKind.dir, sMinus]
        rw [pt_eq_s]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_arcST D x hv, mergedTuple_eq_tPlus D x ε (m + 1) (by omega),
          mergedTuple_eq_sMinus D x ε m hv]
        simp only [StrandKind.dir, sMinus, tPlus]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_cutEndT D x hv, mergedTuple_of_j D x ε (m + 1) (by omega) (by omega),
          mergedTuple_eq_tPlus D x ε m hv, h1, hv]
        have : kI D x + 1 + 1 - (kI D x + 2) = 0 := by omega
        rw [this, Nat.cast_zero, add_zero]
        simp only [StrandKind.dir, tPlus]
        rw [pt_eq_t, tail_tS, et_eq]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_of_j D x hv hv', mergedTuple_of_j D x ε (m + 1) (by omega) (by omega),
          mergedTuple_of_j D x ε m hv (by omega), h1]
        have : m.val + 1 - (kI D x + 2) = m.val - (kI D x + 2) + 1 := by omega
        rw [this, Nat.cast_succ]
        simp only [StrandKind.dir, Shadow.dir_mk, edge, add_assoc]
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_cutStartT D x hv, mergedTuple_eq_tMinus D x ε (m + 1) (by omega),
          mergedTuple_of_j D x ε m (by omega) (by omega), hv]
        have : kI D x + 1 + kJ D x - (kI D x + 2) = kJ D x - 1 := by omega
        rw [this, Pj_b_wrap]
        simp only [StrandKind.dir, tMinus]
        rw [pt_eq_t]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_arcTS D x hv, mergedTuple_eq_sPlus D x ε (m + 1) (by omega),
          mergedTuple_eq_tMinus D x ε m hv]
        simp only [StrandKind.dir, sPlus, tMinus]; module
      · have h1 := zval_add_one_of_eq m (by omega)
        rw [mergedKindIdx_eq_cutEndS D x hv, mergedTuple_of_lt D x ε (m + 1) (by omega),
          mergedTuple_eq_sPlus D x ε m hv, h1, Nat.cast_zero, add_zero]
        simp only [StrandKind.dir, sPlus]
        rw [pt_eq_s, tail_sS, es_eq]; module
    · intro l m
      rw [mixedShadow_dir_succ, mixedKind_succ]
      simp only [StrandKind.dir, ZMod.natCast_zmod_val]
  cut_val := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m hm
      rw [mixedKind_zero] at hm
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      show m.val + 2 < kI D x + kJ D x + 4
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · rw [mergedKindIdx_eq_arcTS D x hv] at hm; rcases hm with hm | hm <;> cases hm
      · rw [mergedKindIdx_eq_cutEndS D x hv] at hm; rcases hm with hm | hm <;> cases hm
    · intro l m hm
      rw [mixedKind_succ] at hm
      rcases hm with hm | hm <;> cases hm

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

/-- In the self case the under strand is `⟨i, bS⟩`: `t` transported to the component of `s`. -/
theorem tS_eq_self (h : (sS D x).1 = (tS D x).1) : tS D x = ⟨(sS D x).1, bS D x⟩ :=
  Strand_eq_mk_val h

theorem tail_tS_self (h : (sS D x).1 = (tS D x).1) : D.Γ.tail (tS D x) = Pi D x (bS D x) :=
  congrArg D.Γ.tail (tS_eq_self D x h)

theorem et_self (h : (sS D x).1 = (tS D x).1) :
    et D x = Pi D x (bS D x + 1) - Pi D x (bS D x) :=
  congrArg D.Γ.dir (tS_eq_self D x h)

theorem pt_eq_t_self (h : (sS D x).1 = (tS D x).1) :
    pt D x = Pi D x (bS D x) + τt D x • et D x := by
  rw [pt_eq_t, tail_tS_self D x h]

theorem tS_succ_self (h : (sS D x).1 = (tS D x).1) :
    (⟨(tS D x).1, (tS D x).2 + 1⟩ : D.Γ.Strand) = ⟨(sS D x).1, bS D x + 1⟩ :=
  congrArg (fun e : D.Γ.Strand => (⟨e.1, e.2 + 1⟩ : D.Γ.Strand)) (tS_eq_self D x h)

theorem tS_pred_self (h : (sS D x).1 = (tS D x).1) :
    (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) = ⟨(sS D x).1, bS D x - 1⟩ :=
  congrArg (fun e : D.Γ.Strand => (⟨e.1, e.2 - 1⟩ : D.Γ.Strand)) (tS_eq_self D x h)

theorem not_adjacent_aS_bS (h : (sS D x).1 = (tS D x).1) : ¬ adjacent (aS D x) (bS D x) := by
  intro had
  apply not_adjacent_sS_tS D x
  rw [tS_eq_self D x h]
  exact ⟨(sS D x).1, aS D x, bS D x, rfl, rfl, had⟩

theorem two_le_dd (h : (sS D x).1 = (tS D x).1) : 2 ≤ dd D x :=
  (two_le_val_sub_of_not_adjacent (not_adjacent_aS_bS D x h)).1

theorem dd_add_two_le (h : (sS D x).1 = (tS D x).1) : dd D x + 2 ≤ kI D x :=
  (two_le_val_sub_of_not_adjacent (not_adjacent_aS_bS D x h)).2

theorem dd_cast : (dd D x : ZMod (kI D x)) = bS D x - aS D x := ZMod.natCast_zmod_val _

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
  unfold othersS
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have := D.Γ.hc
  omega

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

/-! #### Index arithmetic for the self shadow (U5) -/

/-- Case analysis on the strands of the self shadow: `A`, `B`, or an untouched component. -/
theorem selfShadow_strand_cases (h : (sS D x).1 = (tS D x).1) {P : (selfShadow D x ε h).Strand → Prop}
    (h0 : ∀ m : ZMod (dd D x + 2), P ⟨(0 : Fin ((othersS D x).card + 2)), m⟩)
    (h1 : ∀ m : ZMod (kI D x - dd D x + 2), P ⟨(1 : Fin ((othersS D x).card + 2)), m⟩)
    (hs : ∀ (l : Fin (othersS D x).card)
      (m : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k), P ⟨l.succ.succ, m⟩)
    (u : (selfShadow D x ε h).Strand) : P u := by
  obtain ⟨l, m⟩ := u
  induction l using Fin.cases with
  | zero => exact h0 m
  | succ l =>
    induction l using Fin.cases with
    | zero => exact h1 m
    | succ l => exact hs l m

theorem selfKind_zero (h : (sS D x).1 = (tS D x).1) (m : ZMod (dd D x + 2)) :
    selfKind D x ε h ⟨(0 : Fin ((othersS D x).card + 2)), m⟩ = kindIdxA D x m.val := rfl

theorem selfKind_one (h : (sS D x).1 = (tS D x).1) (m : ZMod (kI D x - dd D x + 2)) :
    selfKind D x ε h ⟨(1 : Fin ((othersS D x).card + 2)), m⟩ = kindIdxB D x m.val := rfl

theorem selfKind_succ_succ (h : (sS D x).1 = (tS D x).1) (l : Fin (othersS D x).card)
    (m : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k) :
    selfKind D x ε h ⟨l.succ.succ, m⟩ =
      StrandKind.old ⟨(othersS D x).orderEmbOfFin rfl l, (m.val : ZMod _)⟩ := rfl

theorem selfShadow_tail_zero (h : (sS D x).1 = (tS D x).1) (m : ZMod (dd D x + 2)) :
    (selfShadow D x ε h).tail ⟨(0 : Fin ((othersS D x).card + 2)), m⟩ = tupleA D x ε m := rfl

theorem selfShadow_dir_zero (h : (sS D x).1 = (tS D x).1) (m : ZMod (dd D x + 2)) :
    (selfShadow D x ε h).dir ⟨(0 : Fin ((othersS D x).card + 2)), m⟩ =
      tupleA D x ε (m + 1) - tupleA D x ε m := rfl

theorem selfShadow_tail_one (h : (sS D x).1 = (tS D x).1) (m : ZMod (kI D x - dd D x + 2)) :
    (selfShadow D x ε h).tail ⟨(1 : Fin ((othersS D x).card + 2)), m⟩ = tupleB D x ε m := rfl

theorem selfShadow_dir_one (h : (sS D x).1 = (tS D x).1) (m : ZMod (kI D x - dd D x + 2)) :
    (selfShadow D x ε h).dir ⟨(1 : Fin ((othersS D x).card + 2)), m⟩ =
      tupleB D x ε (m + 1) - tupleB D x ε m := rfl

theorem selfShadow_tail_succ_succ (h : (sS D x).1 = (tS D x).1) (l : Fin (othersS D x).card)
    (m : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k) :
    (selfShadow D x ε h).tail ⟨l.succ.succ, m⟩ = D.Γ.tail ⟨(othersS D x).orderEmbOfFin rfl l, m⟩ := rfl

theorem selfShadow_dir_succ_succ (h : (sS D x).1 = (tS D x).1) (l : Fin (othersS D x).card)
    (m : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k) :
    (selfShadow D x ε h).dir ⟨l.succ.succ, m⟩ = D.Γ.dir ⟨(othersS D x).orderEmbOfFin rfl l, m⟩ := rfl

/-- The untouched components are not the component of `s` (`= t`). -/
theorem orderEmbOfFin_othersS_ne (l : Fin (othersS D x).card) :
    (othersS D x).orderEmbOfFin rfl l ≠ (sS D x).1 := by
  have := Finset.orderEmbOfFin_mem (othersS D x) rfl l
  simp only [othersS, Finset.mem_erase, Finset.mem_univ, and_true] at this
  exact this

/-- The four blocks of labels of `A` and of `B`. -/
theorem blockA (v : ℕ) (hv : v < dd D x + 2) :
    v < dd D x - 1 ∨ v = dd D x - 1 ∨ v = dd D x ∨ v = dd D x + 1 := by omega

theorem blockB (v : ℕ) (hv : v < kI D x - dd D x + 2) :
    v < kI D x - dd D x - 1 ∨ v = kI D x - dd D x - 1 ∨ v = kI D x - dd D x ∨
      v = kI D x - dd D x + 1 := by omega

theorem kindIdxA_of_lt {v : ℕ} (hv : v < dd D x - 1) :
    kindIdxA D x v = StrandKind.old ⟨(sS D x).1, aS D x + 1 + (v : ZMod (kI D x))⟩ := by
  unfold kindIdxA; split_ifs; rfl

theorem kindIdxA_eq_cutStartT {v : ℕ} (hv : v = dd D x - 1) : kindIdxA D x v = StrandKind.cutStartT := by
  unfold kindIdxA; split_ifs <;> first | rfl | omega

theorem kindIdxA_eq_arcTS (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v = dd D x) :
    kindIdxA D x v = StrandKind.arcTS := by
  have := two_le_dd D x h
  unfold kindIdxA; split_ifs <;> first | rfl | omega

theorem kindIdxA_eq_cutEndS {v : ℕ} (hv : v = dd D x + 1) : kindIdxA D x v = StrandKind.cutEndS := by
  unfold kindIdxA; split_ifs <;> first | rfl | omega

theorem kindIdxB_of_lt {v : ℕ} (hv : v < kI D x - dd D x - 1) :
    kindIdxB D x v = StrandKind.old ⟨(sS D x).1, bS D x + 1 + (v : ZMod (kI D x))⟩ := by
  unfold kindIdxB; split_ifs; rfl

theorem kindIdxB_eq_cutStartS {v : ℕ} (hv : v = kI D x - dd D x - 1) :
    kindIdxB D x v = StrandKind.cutStartS := by
  unfold kindIdxB; split_ifs <;> first | rfl | omega

theorem kindIdxB_eq_arcST (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v = kI D x - dd D x) :
    kindIdxB D x v = StrandKind.arcST := by
  have := dd_add_two_le D x h
  unfold kindIdxB; split_ifs <;> first | rfl | omega

theorem kindIdxB_eq_cutEndT {v : ℕ} (hv : v = kI D x - dd D x + 1) :
    kindIdxB D x v = StrandKind.cutEndT := by
  unfold kindIdxB; split_ifs <;> first | rfl | omega

theorem tupleA_of_lt (m : ZMod (dd D x + 2)) (hv : m.val < dd D x) :
    tupleA D x ε m = Pi D x (aS D x + 1 + (m.val : ZMod (kI D x))) := by
  unfold tupleA; split_ifs; rfl

theorem tupleA_eq_tMinus (m : ZMod (dd D x + 2)) (hv : m.val = dd D x) :
    tupleA D x ε m = tMinus D x ε := by
  unfold tupleA; split_ifs <;> first | rfl | omega

theorem tupleA_eq_sPlus (m : ZMod (dd D x + 2)) (hv : m.val = dd D x + 1) :
    tupleA D x ε m = sPlus D x ε := by
  unfold tupleA; split_ifs <;> first | rfl | omega

theorem tupleB_of_lt (m : ZMod (kI D x - dd D x + 2)) (hv : m.val < kI D x - dd D x) :
    tupleB D x ε m = Pi D x (bS D x + 1 + (m.val : ZMod (kI D x))) := by
  unfold tupleB; split_ifs; rfl

theorem tupleB_eq_sMinus (m : ZMod (kI D x - dd D x + 2)) (hv : m.val = kI D x - dd D x) :
    tupleB D x ε m = sMinus D x ε := by
  unfold tupleB; split_ifs <;> first | rfl | omega

theorem tupleB_eq_tPlus (m : ZMod (kI D x - dd D x + 2)) (hv : m.val = kI D x - dd D x + 1) :
    tupleB D x ε m = tPlus D x ε := by
  unfold tupleB; split_ifs <;> first | rfl | omega

/-- `P (a + 1 + (d − 1)) = P b`: the last old vertex of `A` is the tail of `t`. -/
theorem Pi_bS_wrap (h : (sS D x).1 = (tS D x).1) :
    Pi D x (aS D x + 1 + ((dd D x - 1 : ℕ) : ZMod (kI D x))) = Pi D x (bS D x) := by
  have := two_le_dd D x h
  congr 1
  rw [zcast_pred (by omega), dd_cast]; ring

/-- `P (b + 1 + (k − d − 1)) = P a`: the last old vertex of `B` is the tail of `s`. -/
theorem Pi_aS_wrapB (h : (sS D x).1 = (tS D x).1) :
    Pi D x (bS D x + 1 + ((kI D x - dd D x - 1 : ℕ) : ZMod (kI D x))) = Pi D x (aS D x) := by
  have := dd_add_two_le D x h
  congr 1
  have e : kI D x - dd D x - 1 = kI D x - (dd D x + 1) := by omega
  rw [e, zcast_sub_self (by omega)]
  push_cast
  rw [dd_cast]; ring

/-- An old kind of `A` or `B` lies on the component of `s`. -/
theorem kindIdxA_old_fst (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v < dd D x + 2) (e : D.Γ.Strand)
    (he : kindIdxA D x v = StrandKind.old e) : e.1 = (sS D x).1 := by
  rcases blockA D x v hv with h1 | h1 | h1 | h1
  · rw [kindIdxA_of_lt D x h1] at he; exact (congrArg Sigma.fst (StrandKind.old.inj he)).symm
  · rw [kindIdxA_eq_cutStartT D x h1] at he; cases he
  · rw [kindIdxA_eq_arcTS D x h h1] at he; cases he
  · rw [kindIdxA_eq_cutEndS D x h1] at he; cases he

theorem kindIdxB_old_fst (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v < kI D x - dd D x + 2)
    (e : D.Γ.Strand) (he : kindIdxB D x v = StrandKind.old e) : e.1 = (sS D x).1 := by
  rcases blockB D x v hv with h1 | h1 | h1 | h1
  · rw [kindIdxB_of_lt D x h1] at he; exact (congrArg Sigma.fst (StrandKind.old.inj he)).symm
  · rw [kindIdxB_eq_cutStartS D x h1] at he; cases he
  · rw [kindIdxB_eq_arcST D x h h1] at he; cases he
  · rw [kindIdxB_eq_cutEndT D x h1] at he; cases he

/-- A left inverse of the two kind maps `kindIdxA`, `kindIdxB`: component (`0` = `A`, `1` = `B`)
and label. -/
def selfCode : StrandKind D x → ℕ × ℕ
  | .old e =>
      if e.1 = (sS D x).1 then
        if (e.2.val + (kI D x - 1) - (aS D x).val) % kI D x < dd D x - 1 then
          (0, (e.2.val + (kI D x - 1) - (aS D x).val) % kI D x)
        else (1, (e.2.val + (kI D x - 1) - (aS D x).val) % kI D x - dd D x)
      else (2, 0)
  | .cutStartT => (0, dd D x - 1)
  | .arcTS => (0, dd D x)
  | .cutEndS => (0, dd D x + 1)
  | .cutStartS => (1, kI D x - dd D x - 1)
  | .arcST => (1, kI D x - dd D x)
  | .cutEndT => (1, kI D x - dd D x + 1)

theorem selfCode_kindIdxA (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v < dd D x + 2) :
    selfCode D x (kindIdxA D x v) = (0, v) := by
  have hd := two_le_dd D x h
  have hd' := dd_add_two_le D x h
  rcases blockA D x v hv with h1 | h1 | h1 | h1
  · rw [kindIdxA_of_lt D x h1]
    simp only [selfCode, ↓reduceIte]
    rw [zmod_code_eq (aS D x) (by omega), ite_eq_left h1]
  · rw [kindIdxA_eq_cutStartT D x h1]; simp only [selfCode]; rw [h1]
  · rw [kindIdxA_eq_arcTS D x h h1]; simp only [selfCode]; rw [h1]
  · rw [kindIdxA_eq_cutEndS D x h1]; simp only [selfCode]; rw [h1]

theorem selfCode_kindIdxB (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v < kI D x - dd D x + 2) :
    selfCode D x (kindIdxB D x v) = (1, v) := by
  have hd := two_le_dd D x h
  have hd' := dd_add_two_le D x h
  rcases blockB D x v hv with h1 | h1 | h1 | h1
  · rw [kindIdxB_of_lt D x h1]
    simp only [selfCode, ↓reduceIte]
    have e : bS D x + 1 + (v : ZMod (kI D x)) = aS D x + 1 + ((dd D x + v : ℕ) : ZMod (kI D x)) := by
      push_cast; rw [dd_cast]; ring
    rw [e, zmod_code_eq (aS D x) (by omega), ite_eq_right (by omega)]
    congr 1; omega
  · rw [kindIdxB_eq_cutStartS D x h1]; simp only [selfCode]; rw [h1]
  · rw [kindIdxB_eq_arcST D x h h1]; simp only [selfCode]; rw [h1]
  · rw [kindIdxB_eq_cutEndT D x h1]; simp only [selfCode]; rw [h1]

theorem kindIdxA_inj (h : (sS D x).1 = (tS D x).1) {v v' : ℕ} (hv : v < dd D x + 2)
    (hv' : v' < dd D x + 2) (heq : kindIdxA D x v = kindIdxA D x v') : v = v' := by
  have := congrArg (selfCode D x) heq
  rw [selfCode_kindIdxA D x h hv, selfCode_kindIdxA D x h hv'] at this
  exact (Prod.mk.inj this).2

theorem kindIdxB_inj (h : (sS D x).1 = (tS D x).1) {v v' : ℕ} (hv : v < kI D x - dd D x + 2)
    (hv' : v' < kI D x - dd D x + 2) (heq : kindIdxB D x v = kindIdxB D x v') : v = v' := by
  have := congrArg (selfCode D x) heq
  rw [selfCode_kindIdxB D x h hv, selfCode_kindIdxB D x h hv'] at this
  exact (Prod.mk.inj this).2

theorem kindIdxA_ne_kindIdxB (h : (sS D x).1 = (tS D x).1) {v v' : ℕ} (hv : v < dd D x + 2)
    (hv' : v' < kI D x - dd D x + 2) : kindIdxA D x v ≠ kindIdxB D x v' := by
  intro heq
  have := congrArg (selfCode D x) heq
  rw [selfCode_kindIdxA D x h hv, selfCode_kindIdxB D x h hv'] at this
  exact absurd (Prod.mk.inj this).1 (by decide)

/-- The self shadow is a splice model. -/
def selfModel (h : (sS D x).1 = (tS D x).1) : SpliceModel D x ε (selfShadow D x ε h) where
  kind := selfKind D x ε h
  kind_injective := by
    show ∀ u u' : (selfShadow D x ε h).Strand, selfKind D x ε h u = selfKind D x ε h u' → u = u'
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
      · intro m' heq
        rw [selfKind_zero, selfKind_zero] at heq
        rw [ZMod.val_injective _ (kindIdxA_inj D x h (ZMod.val_lt m) (ZMod.val_lt m') heq)]
      · intro m' heq
        rw [selfKind_zero, selfKind_one] at heq
        exact absurd heq (kindIdxA_ne_kindIdxB D x h (ZMod.val_lt m) (ZMod.val_lt m'))
      · intro l' m' heq
        rw [selfKind_zero, selfKind_succ_succ] at heq
        exact absurd (kindIdxA_old_fst D x h (ZMod.val_lt m) _ heq) (orderEmbOfFin_othersS_ne D x l')
    · intro m
      refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
      · intro m' heq
        rw [selfKind_one, selfKind_zero] at heq
        exact absurd heq.symm (kindIdxA_ne_kindIdxB D x h (ZMod.val_lt m') (ZMod.val_lt m))
      · intro m' heq
        rw [selfKind_one, selfKind_one] at heq
        rw [ZMod.val_injective _ (kindIdxB_inj D x h (ZMod.val_lt m) (ZMod.val_lt m') heq)]
      · intro l' m' heq
        rw [selfKind_one, selfKind_succ_succ] at heq
        exact absurd (kindIdxB_old_fst D x h (ZMod.val_lt m) _ heq) (orderEmbOfFin_othersS_ne D x l')
    · intro l m
      refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
      · intro m' heq
        rw [selfKind_succ_succ, selfKind_zero] at heq
        exact absurd (kindIdxA_old_fst D x h (ZMod.val_lt m') _ heq.symm) (orderEmbOfFin_othersS_ne D x l)
      · intro m' heq
        rw [selfKind_succ_succ, selfKind_one] at heq
        exact absurd (kindIdxB_old_fst D x h (ZMod.val_lt m') _ heq.symm) (orderEmbOfFin_othersS_ne D x l)
      · intro l' m' heq
        rw [selfKind_succ_succ, selfKind_succ_succ] at heq
        have h1 := StrandKind.old.inj heq
        rw [Sigma.mk.inj_iff] at h1
        obtain ⟨h1, h2⟩ := h1
        have hl : l = l' := ((othersS D x).orderEmbOfFin rfl).injective h1
        subst hl
        have h3 := eq_of_heq h2
        simp only [ZMod.natCast_zmod_val] at h3
        rw [h3]
  kind_surj := by
    intro κ hκ
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    cases κ with
    | old e =>
      obtain ⟨hs, ht⟩ := hκ
      have hs' : e ≠ sS D x := fun h' => hs (by rw [h'])
      have ht' : e ≠ tS D x := fun h' => ht (by rw [h'])
      rw [tS_eq_self D x h] at ht'
      obtain ⟨l₀, c⟩ := e
      by_cases hi : l₀ = (sS D x).1
      · subst hi
        have hca : c ≠ aS D x := fun h' => hs' (Sigma.ext rfl (heq_of_eq h'))
        have hcb : c ≠ bS D x := fun h' => ht' (Sigma.ext rfl (heq_of_eq h'))
        obtain ⟨w, hw⟩ : ∃ w, w = (c - aS D x).val := ⟨_, rfl⟩
        have hw1 : w < kI D x := by rw [hw]; exact ZMod.val_lt _
        have hwc : (w : ZMod (kI D x)) = c - aS D x := by rw [hw, ZMod.natCast_zmod_val]
        have hw0 : w ≠ 0 := by
          intro h0
          apply hca
          rw [h0, Nat.cast_zero] at hwc
          linear_combination -hwc
        have hwd : w ≠ dd D x := by
          intro h0
          apply hcb
          rw [h0, dd_cast] at hwc
          linear_combination -hwc
        rcases Nat.lt_or_gt_of_ne hwd with hlt | hgt
        · refine ⟨⟨(0 : Fin ((othersS D x).card + 2)), ((w - 1 : ℕ) : ZMod (dd D x + 2))⟩, ?_⟩
          rw [selfKind_zero, ZMod.val_natCast_of_lt (by omega), kindIdxA_of_lt D x (by omega)]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          rw [zcast_pred (by omega), hwc]; ring
        · refine ⟨⟨(1 : Fin ((othersS D x).card + 2)),
            ((w - dd D x - 1 : ℕ) : ZMod (kI D x - dd D x + 2))⟩, ?_⟩
          rw [selfKind_one, ZMod.val_natCast_of_lt (by omega), kindIdxB_of_lt D x (by omega)]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          have e : w - dd D x - 1 = w - (dd D x + 1) := by omega
          rw [e, Nat.cast_sub (by omega)]
          push_cast
          rw [hwc, dd_cast]; ring
      · have hmem : l₀ ∈ othersS D x := by
          simp only [othersS, Finset.mem_erase, Finset.mem_univ, and_true]
          exact hi
        have hrange : l₀ ∈ Set.range ((othersS D x).orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hmem
        obtain ⟨l, hl⟩ := hrange
        subst hl
        exact ⟨⟨l.succ.succ, c⟩, by rw [selfKind_succ_succ, ZMod.natCast_zmod_val]⟩
    | cutStartS =>
      refine ⟨⟨(1 : Fin ((othersS D x).card + 2)),
        ((kI D x - dd D x - 1 : ℕ) : ZMod (kI D x - dd D x + 2))⟩, ?_⟩
      rw [selfKind_one, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxB_eq_cutStartS D x rfl
    | cutEndS =>
      refine ⟨⟨(0 : Fin ((othersS D x).card + 2)), ((dd D x + 1 : ℕ) : ZMod (dd D x + 2))⟩, ?_⟩
      rw [selfKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxA_eq_cutEndS D x rfl
    | cutStartT =>
      refine ⟨⟨(0 : Fin ((othersS D x).card + 2)), ((dd D x - 1 : ℕ) : ZMod (dd D x + 2))⟩, ?_⟩
      rw [selfKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxA_eq_cutStartT D x rfl
    | cutEndT =>
      refine ⟨⟨(1 : Fin ((othersS D x).card + 2)),
        ((kI D x - dd D x + 1 : ℕ) : ZMod (kI D x - dd D x + 2))⟩, ?_⟩
      rw [selfKind_one, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxB_eq_cutEndT D x rfl
    | arcST =>
      refine ⟨⟨(1 : Fin ((othersS D x).card + 2)),
        ((kI D x - dd D x : ℕ) : ZMod (kI D x - dd D x + 2))⟩, ?_⟩
      rw [selfKind_one, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxB_eq_arcST D x h rfl
    | arcTS =>
      refine ⟨⟨(0 : Fin ((othersS D x).card + 2)), ((dd D x : ℕ) : ZMod (dd D x + 2))⟩, ?_⟩
      rw [selfKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxA_eq_arcTS D x h rfl
  kind_occurs := by
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      rw [selfKind_zero]
      have hmv := ZMod.val_lt m
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxA_of_lt D x hv]
        refine StrandKind.occurs_old ?_ ?_
        · intro heq
          have heq2 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) =
              ⟨(sS D x).1, (sS D x).2⟩ := heq
          have heq' := Strand_mk_eq_mk_iff.mp heq2
          have h2 : ((m.val + 1 : ℕ) : ZMod (kI D x)) = 0 := by
            push_cast; linear_combination heq'
          exact zcast_ne_zero_of_lt (by omega) (by omega) h2
        · intro heq
          rw [tS_eq_self D x h] at heq
          have heq' := Strand_mk_eq_mk_iff.mp heq
          have h2 : ((m.val + 1 : ℕ) : ZMod (kI D x)) = (dd D x : ZMod (kI D x)) := by
            push_cast; rw [dd_cast]; linear_combination heq'
          have := nat_eq_of_zcast_eq (by omega) (by omega) h2
          omega
      · rw [kindIdxA_eq_cutStartT D x hv]; exact StrandKind.occurs_cutStartT
      · rw [kindIdxA_eq_arcTS D x h hv]; exact StrandKind.occurs_arcTS
      · rw [kindIdxA_eq_cutEndS D x hv]; exact StrandKind.occurs_cutEndS
    · intro m
      rw [selfKind_one]
      have hmv := ZMod.val_lt m
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxB_of_lt D x hv]
        refine StrandKind.occurs_old ?_ ?_
        · intro heq
          have heq2 : (⟨(sS D x).1, bS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) =
              ⟨(sS D x).1, (sS D x).2⟩ := heq
          have heq' := Strand_mk_eq_mk_iff.mp heq2
          have h2 : ((m.val + 1 + dd D x : ℕ) : ZMod (kI D x)) = 0 := by
            push_cast; rw [dd_cast]; linear_combination heq'
          exact zcast_ne_zero_of_lt (by omega) (by omega) h2
        · intro heq
          rw [tS_eq_self D x h] at heq
          have heq' := Strand_mk_eq_mk_iff.mp heq
          have h2 : ((m.val + 1 : ℕ) : ZMod (kI D x)) = 0 := by
            push_cast; linear_combination heq'
          exact zcast_ne_zero_of_lt (by omega) (by omega) h2
      · rw [kindIdxB_eq_cutStartS D x hv]; exact StrandKind.occurs_cutStartS
      · rw [kindIdxB_eq_arcST D x h hv]; exact StrandKind.occurs_arcST
      · rw [kindIdxB_eq_cutEndT D x hv]; exact StrandKind.occurs_cutEndT
    · intro l m
      rw [selfKind_succ_succ]
      have hne := orderEmbOfFin_othersS_ne D x l
      exact StrandKind.occurs_old (Strand_mk_ne_mk_of_ne hne)
        (Strand_mk_ne_mk_of_ne (fun heq => hne (heq.trans h.symm)))
  kind_pred := by
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      show selfKind D x ε h ⟨(0 : Fin ((othersS D x).card + 2)), (m - 1 : ZMod (dd D x + 2))⟩ =
        (selfKind D x ε h ⟨(0 : Fin ((othersS D x).card + 2)), m⟩).pred
      rw [selfKind_zero, selfKind_zero]
      have hmv := ZMod.val_lt m
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxA_of_lt D x hv]
        rcases Nat.eq_zero_or_pos m.val with h0 | h0
        · rw [zval_sub_one_of_zero m h0, kindIdxA_eq_cutEndS D x (by omega), h0, Nat.cast_zero,
            add_zero]
          simp only [StrandKind.pred, ↓reduceIte]
        · rw [zval_sub_one_of_pos m h0, kindIdxA_of_lt D x (by omega)]
          simp only [StrandKind.pred]
          have hne1 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
              ⟨(sS D x).1, (sS D x).2 + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : (m.val : ZMod (kI D x)) = 0 := by linear_combination heq'
            exact zcast_ne_zero_of_lt h0 (by omega) h2
          have hne2 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
              ⟨(sS D x).1, bS D x + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : (m.val : ZMod (kI D x)) = (dd D x : ZMod (kI D x)) := by
              rw [dd_cast]; linear_combination heq'
            have := nat_eq_of_zcast_eq (by omega) (by omega) h2
            omega
          rw [ite_eq_right hne1, tS_succ_self D x h, ite_eq_right hne2]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          rw [zcast_pred h0]; ring
      · -- cutStartT at `d − 1`: predecessor `old ⟨i, b − 1⟩` at `d − 2`
        rw [kindIdxA_eq_cutStartT D x hv, zval_sub_one_of_pos m (by omega), hv,
          kindIdxA_of_lt D x (by omega)]
        simp only [StrandKind.pred]
        rw [tS_pred_self D x h]
        simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        have e : dd D x - 1 - 1 = dd D x - 2 := by omega
        rw [e, Nat.cast_sub (by omega)]
        push_cast
        rw [dd_cast]; ring
      · rw [kindIdxA_eq_arcTS D x h hv, zval_sub_one_of_pos m (by omega),
          kindIdxA_eq_cutStartT D x (by omega)]; rfl
      · rw [kindIdxA_eq_cutEndS D x hv, zval_sub_one_of_pos m (by omega),
          kindIdxA_eq_arcTS D x h (by omega)]; rfl
    · intro m
      show selfKind D x ε h ⟨(1 : Fin ((othersS D x).card + 2)), (m - 1 : ZMod (kI D x - dd D x + 2))⟩ =
        (selfKind D x ε h ⟨(1 : Fin ((othersS D x).card + 2)), m⟩).pred
      rw [selfKind_one, selfKind_one]
      have hmv := ZMod.val_lt m
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxB_of_lt D x hv]
        have hne1 : (⟨(sS D x).1, bS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
            ⟨(sS D x).1, (sS D x).2 + 1⟩ := by
          intro heq
          have heq' := Strand_mk_eq_mk_iff.mp heq
          have h2 : ((m.val + dd D x : ℕ) : ZMod (kI D x)) = 0 := by
            push_cast; rw [dd_cast]; linear_combination heq'
          exact zcast_ne_zero_of_lt (by omega) (by omega) h2
        rcases Nat.eq_zero_or_pos m.val with h0 | h0
        · rw [zval_sub_one_of_zero m h0, kindIdxB_eq_cutEndT D x (by omega)]
          rw [h0, Nat.cast_zero, add_zero] at hne1 ⊢
          simp only [StrandKind.pred]
          rw [ite_eq_right hne1, tS_succ_self D x h, ite_eq_left rfl]
        · rw [zval_sub_one_of_pos m h0, kindIdxB_of_lt D x (by omega)]
          simp only [StrandKind.pred]
          have hne2 : (⟨(sS D x).1, bS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
              ⟨(sS D x).1, bS D x + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : (m.val : ZMod (kI D x)) = 0 := by linear_combination heq'
            exact zcast_ne_zero_of_lt h0 (by omega) h2
          rw [ite_eq_right hne1, tS_succ_self D x h, ite_eq_right hne2]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          rw [zcast_pred h0]; ring
      · -- cutStartS at `k − d − 1`: predecessor `old ⟨i, a − 1⟩` at `k − d − 2`
        rw [kindIdxB_eq_cutStartS D x hv, zval_sub_one_of_pos m (by omega), hv,
          kindIdxB_of_lt D x (by omega)]
        simp only [StrandKind.pred, StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        have e : kI D x - dd D x - 1 - 1 = kI D x - (dd D x + 2) := by omega
        rw [e, zcast_sub_self (by omega)]
        push_cast
        rw [dd_cast]; ring
      · rw [kindIdxB_eq_arcST D x h hv, zval_sub_one_of_pos m (by omega),
          kindIdxB_eq_cutStartS D x (by omega)]; rfl
      · rw [kindIdxB_eq_cutEndT D x hv, zval_sub_one_of_pos m (by omega),
          kindIdxB_eq_arcST D x h (by omega)]; rfl
    · intro l m
      show selfKind D x ε h ⟨l.succ.succ, (m - 1 : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k)⟩ =
        (selfKind D x ε h ⟨l.succ.succ, m⟩).pred
      rw [selfKind_succ_succ, selfKind_succ_succ]
      simp only [StrandKind.pred, ZMod.natCast_zmod_val]
      have hne := orderEmbOfFin_othersS_ne D x l
      rw [ite_eq_right (Strand_mk_ne_mk_of_ne hne),
        ite_eq_right (Strand_mk_ne_mk_of_ne (fun heq => hne (heq.trans h.symm)))]
  tail_eq := by
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      rw [selfShadow_tail_zero, selfKind_zero]
      have hmv := ZMod.val_lt m
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxA_of_lt D x hv, tupleA_of_lt D x ε m (by omega)]; rfl
      · rw [kindIdxA_eq_cutStartT D x hv, tupleA_of_lt D x ε m (by omega), hv, Pi_bS_wrap D x h]
        exact (tail_tS_self D x h).symm
      · rw [kindIdxA_eq_arcTS D x h hv, tupleA_eq_tMinus D x ε m hv]; rfl
      · rw [kindIdxA_eq_cutEndS D x hv, tupleA_eq_sPlus D x ε m hv]; rfl
    · intro m
      rw [selfShadow_tail_one, selfKind_one]
      have hmv := ZMod.val_lt m
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxB_of_lt D x hv, tupleB_of_lt D x ε m (by omega)]; rfl
      · rw [kindIdxB_eq_cutStartS D x hv, tupleB_of_lt D x ε m (by omega), hv, Pi_aS_wrapB D x h]; rfl
      · rw [kindIdxB_eq_arcST D x h hv, tupleB_eq_sMinus D x ε m hv]; rfl
      · rw [kindIdxB_eq_cutEndT D x hv, tupleB_eq_tPlus D x ε m hv]; rfl
    · intro l m
      rw [selfShadow_tail_succ_succ, selfKind_succ_succ]
      simp only [StrandKind.tail, ZMod.natCast_zmod_val]
  dir_eq := by
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      rw [selfShadow_dir_zero, selfKind_zero]
      have hmv := ZMod.val_lt m
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxA_of_lt D x hv, tupleA_of_lt D x ε (m + 1) (by omega),
          tupleA_of_lt D x ε m (by omega), h1, Nat.cast_succ]
        simp only [StrandKind.dir, Shadow.dir_mk, edge, add_assoc]
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxA_eq_cutStartT D x hv, tupleA_eq_tMinus D x ε (m + 1) (by omega),
          tupleA_of_lt D x ε m (by omega), hv, Pi_bS_wrap D x h]
        simp only [StrandKind.dir, tMinus]
        rw [pt_eq_t_self D x h]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxA_eq_arcTS D x h hv, tupleA_eq_sPlus D x ε (m + 1) (by omega),
          tupleA_eq_tMinus D x ε m hv]
        simp only [StrandKind.dir, sPlus, tMinus]; module
      · have h1 := zval_add_one_of_eq m (by omega)
        rw [kindIdxA_eq_cutEndS D x hv, tupleA_of_lt D x ε (m + 1) (by omega),
          tupleA_eq_sPlus D x ε m hv, h1, Nat.cast_zero, add_zero]
        simp only [StrandKind.dir, sPlus]
        rw [pt_eq_s, tail_sS, es_eq]; module
    · intro m
      rw [selfShadow_dir_one, selfKind_one]
      have hmv := ZMod.val_lt m
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxB_of_lt D x hv, tupleB_of_lt D x ε (m + 1) (by omega),
          tupleB_of_lt D x ε m (by omega), h1, Nat.cast_succ]
        simp only [StrandKind.dir, Shadow.dir_mk, edge, add_assoc]
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxB_eq_cutStartS D x hv, tupleB_eq_sMinus D x ε (m + 1) (by omega),
          tupleB_of_lt D x ε m (by omega), hv, Pi_aS_wrapB D x h]
        simp only [StrandKind.dir, sMinus]
        rw [pt_eq_s, tail_sS]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxB_eq_arcST D x h hv, tupleB_eq_tPlus D x ε (m + 1) (by omega),
          tupleB_eq_sMinus D x ε m hv]
        simp only [StrandKind.dir, sMinus, tPlus]; module
      · have h1 := zval_add_one_of_eq m (by omega)
        rw [kindIdxB_eq_cutEndT D x hv, tupleB_of_lt D x ε (m + 1) (by omega),
          tupleB_eq_tPlus D x ε m hv, h1, Nat.cast_zero, add_zero]
        simp only [StrandKind.dir, tPlus]
        rw [pt_eq_t_self D x h, et_self D x h]; module
    · intro l m
      rw [selfShadow_dir_succ_succ, selfKind_succ_succ]
      simp only [StrandKind.dir, ZMod.natCast_zmod_val]
  cut_val := by
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m hm
      rw [selfKind_zero] at hm
      have hmv := ZMod.val_lt m
      show m.val + 2 < dd D x + 2
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · omega
      · omega
      · rw [kindIdxA_eq_arcTS D x h hv] at hm; rcases hm with hm | hm <;> cases hm
      · rw [kindIdxA_eq_cutEndS D x hv] at hm; rcases hm with hm | hm <;> cases hm
    · intro m hm
      rw [selfKind_one] at hm
      have hmv := ZMod.val_lt m
      show m.val + 2 < kI D x - dd D x + 2
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · omega
      · omega
      · rw [kindIdxB_eq_arcST D x h hv] at hm; rcases hm with hm | hm <;> cases hm
      · rw [kindIdxB_eq_cutEndT D x hv] at hm; rcases hm with hm | hm <;> cases hm
    · intro l m hm
      rw [selfKind_succ_succ] at hm
      rcases hm with hm | hm <;> cases hm

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

/-! #### Helpers for the cyclic-order core (unit U6a): the `key` blocks, the swap, the untouched
circles and the self-case classification (stated early, under primed names, because
`reconnect_no_between` precedes `self_sameCycle_pair_iff` / `sameCycle_of_comp_ne` in the chain). -/

theorem compOf_xv : D.compOf (xv D x) = (sS D x).1 := rfl
theorem compOf_underVisit' : D.compOf (D.underVisit x) = (tS D x).1 := rfl
theorem xv_ne_underVisit : xv D x ≠ D.underVisit x := D.overVisit_ne_underVisit x

theorem reconnect_eq_mul_swap :
    D.record.reconnect (xv D x) = D.visitSucc * Equiv.swap (xv D x) (D.underVisit x) := rfl

theorem coord_bounds_i (w : D.Γ.Visit) (hw : D.compOf w = (sS D x).1) :
    0 ≤ D.visitCoord w ∧ D.visitCoord w < (kI D x : ℝ) := by
  refine ⟨D.visitCoord_nonneg w, ?_⟩
  have := D.visitCoord_lt w
  rw [hw] at this
  exact this

theorem coord_bounds_j (w : D.Γ.Visit) (hw : D.compOf w = (tS D x).1) :
    0 ≤ D.visitCoord w ∧ D.visitCoord w < (kJ D x : ℝ) := by
  refine ⟨D.visitCoord_nonneg w, ?_⟩
  have := D.visitCoord_lt w
  rw [hw] at this
  exact this

theorem key_of_i (w : D.Γ.Visit) (hw : D.compOf w = (sS D x).1) :
    key D x w = Diagram.cyclicOffset (kI D x) (D.visitCoord (xv D x)) (D.visitCoord w) := by
  unfold key; rw [ite_eq_left hw]

theorem key_of_j (w : D.Γ.Visit) (hw : D.compOf w = (tS D x).1) (hij : (sS D x).1 ≠ (tS D x).1) :
    key D x w = (kI D x : ℝ) +
      Diagram.cyclicOffset (kJ D x) (D.visitCoord (D.underVisit x)) (D.visitCoord w) := by
  unfold key; rw [ite_eq_right (by rw [hw]; exact hij.symm), ite_eq_left hw]

theorem key_of_ne (w : D.Γ.Visit) (hw : D.compOf w ≠ (sS D x).1) (hw' : D.compOf w ≠ (tS D x).1) :
    key D x w = D.visitCoord w := by
  unfold key; rw [ite_eq_right hw, ite_eq_right hw']

theorem key_xv : key D x (xv D x) = 0 := by
  rw [key_of_i D x (xv D x) rfl, Diagram.cyclicOffset_self]

theorem key_underVisit_of_mixed (hij : (sS D x).1 ≠ (tS D x).1) :
    key D x (D.underVisit x) = (kI D x : ℝ) := by
  rw [key_of_j D x (D.underVisit x) rfl hij, Diagram.cyclicOffset_self, add_zero]

theorem key_nonneg_i (w : D.Γ.Visit) (hw : D.compOf w = (sS D x).1) : 0 ≤ key D x w := by
  rw [key_of_i D x w hw]
  exact Diagram.cyclicOffset_nonneg (coord_bounds_i D x (xv D x) rfl).2 (coord_bounds_i D x w hw).1

theorem key_lt_i (w : D.Γ.Visit) (hw : D.compOf w = (sS D x).1) : key D x w < (kI D x : ℝ) := by
  rw [key_of_i D x w hw]
  exact Diagram.cyclicOffset_lt (coord_bounds_i D x (xv D x) rfl).1 (coord_bounds_i D x w hw).2

theorem kI_le_key_j (w : D.Γ.Visit) (hw : D.compOf w = (tS D x).1) (hij : (sS D x).1 ≠ (tS D x).1) :
    (kI D x : ℝ) ≤ key D x w := by
  rw [key_of_j D x w hw hij]
  linarith [Diagram.cyclicOffset_nonneg (coord_bounds_j D x (D.underVisit x) rfl).2 (coord_bounds_j D x w hw).1]

theorem key_injOn_i (w₁ w₂ : D.Γ.Visit) (h₁ : D.compOf w₁ = (sS D x).1) (h₂ : D.compOf w₂ = (sS D x).1)
    (he : key D x w₁ = key D x w₂) : w₁ = w₂ := by
  rw [key_of_i D x w₁ h₁, key_of_i D x w₂ h₂] at he
  exact D.visitCoord_injOn (h₁.trans h₂.symm)
    (cyclicOffset_injOn _ (coord_bounds_i D x (xv D x) rfl) (coord_bounds_i D x w₁ h₁) (coord_bounds_i D x w₂ h₂) he)

theorem key_injOn_j (w₁ w₂ : D.Γ.Visit) (h₁ : D.compOf w₁ = (tS D x).1) (h₂ : D.compOf w₂ = (tS D x).1)
    (hij : (sS D x).1 ≠ (tS D x).1) (he : key D x w₁ = key D x w₂) : w₁ = w₂ := by
  rw [key_of_j D x w₁ h₁ hij, key_of_j D x w₂ h₂ hij] at he
  exact D.visitCoord_injOn (h₁.trans h₂.symm)
    (cyclicOffset_injOn _ (coord_bounds_j D x (D.underVisit x) rfl) (coord_bounds_j D x w₁ h₁) (coord_bounds_j D x w₂ h₂)
      (add_left_cancel he))

theorem key_cycBetween_i (w₁ w₂ w₃ : D.Γ.Visit) (h₁ : D.compOf w₁ = (sS D x).1)
    (h₂ : D.compOf w₂ = (sS D x).1) (h₃ : D.compOf w₃ = (sS D x).1) :
    cycBetween (key D x w₁) (key D x w₂) (key D x w₃) ↔
      cycBetween (D.visitCoord w₁) (D.visitCoord w₂) (D.visitCoord w₃) := by
  rw [key_of_i D x w₁ h₁, key_of_i D x w₂ h₂, key_of_i D x w₃ h₃]
  simp only [← rexPL_rot_eq_cyclicOffset]
  exact rexB_cycBetween_rot _ _ _ _ _ (coord_bounds_i D x (xv D x) rfl) (coord_bounds_i D x w₁ h₁)
    (coord_bounds_i D x w₂ h₂) (coord_bounds_i D x w₃ h₃)

theorem key_cycBetween_j (w₁ w₂ w₃ : D.Γ.Visit) (h₁ : D.compOf w₁ = (tS D x).1)
    (h₂ : D.compOf w₂ = (tS D x).1) (h₃ : D.compOf w₃ = (tS D x).1) (hij : (sS D x).1 ≠ (tS D x).1) :
    cycBetween (key D x w₁) (key D x w₂) (key D x w₃) ↔
      cycBetween (D.visitCoord w₁) (D.visitCoord w₂) (D.visitCoord w₃) := by
  rw [key_of_j D x w₁ h₁ hij, key_of_j D x w₂ h₂ hij, key_of_j D x w₃ h₃ hij, cycBetween_add_left]
  simp only [← rexPL_rot_eq_cyclicOffset]
  exact rexB_cycBetween_rot _ _ _ _ _ (coord_bounds_j D x (D.underVisit x) rfl) (coord_bounds_j D x w₁ h₁)
    (coord_bounds_j D x w₂ h₂) (coord_bounds_j D x w₃ h₃)

/-- The old successor is the cyclic successor for `key` on every circle. -/
theorem key_nextVisit_no_between (w u : D.Γ.Visit) (hu : D.compOf u = D.compOf w) :
    ¬ cycBetween (key D x w) (key D x u) (key D x (D.nextVisit w)) := by
  by_cases hi : D.compOf w = (sS D x).1
  · rw [key_cycBetween_i D x _ _ _ hi (hu.trans hi) ((D.compOf_nextVisit w).trans hi)]
    exact D.nextVisit_no_between w u hu
  · by_cases hj : D.compOf w = (tS D x).1
    · have hij : (sS D x).1 ≠ (tS D x).1 := fun e => hi (hj.trans e.symm)
      rw [key_cycBetween_j D x _ _ _ hj (hu.trans hj) ((D.compOf_nextVisit w).trans hj) hij]
      exact D.nextVisit_no_between w u hu
    · rw [key_of_ne D x w hi hj, key_of_ne D x u (hu ▸ hi) (hu ▸ hj),
        key_of_ne D x _ ((D.compOf_nextVisit w) ▸ hi) ((D.compOf_nextVisit w) ▸ hj)]
      exact D.nextVisit_no_between w u hu

theorem swap_of_comp_ne (w : D.Γ.Visit) (hw : D.compOf w ≠ (sS D x).1) (hw' : D.compOf w ≠ (tS D x).1) :
    Equiv.swap (xv D x) (D.underVisit x) w = w :=
  Equiv.swap_apply_of_ne_of_ne (fun e => hw (by rw [e]; rfl)) (fun e => hw' (by rw [e]; rfl))

theorem swap_xv_cases (w : D.Γ.Visit) :
    (w ≠ xv D x ∧ w ≠ D.underVisit x ∧ Equiv.swap (xv D x) (D.underVisit x) w = w) ∨
    (w = xv D x ∧ Equiv.swap (xv D x) (D.underVisit x) w = D.underVisit x) ∨
    (w = D.underVisit x ∧ Equiv.swap (xv D x) (D.underVisit x) w = xv D x) := by
  by_cases h1 : w = xv D x
  · exact Or.inr (Or.inl ⟨h1, by rw [h1, Equiv.swap_apply_left]⟩)
  by_cases h2 : w = D.underVisit x
  · exact Or.inr (Or.inr ⟨h2, by rw [h2, Equiv.swap_apply_right]⟩)
  exact Or.inl ⟨h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2⟩

theorem compOf_swap_i_or_j (w : D.Γ.Visit) (hw : D.compOf w = (sS D x).1 ∨ D.compOf w = (tS D x).1) :
    D.compOf (Equiv.swap (xv D x) (D.underVisit x) w) = (sS D x).1 ∨
      D.compOf (Equiv.swap (xv D x) (D.underVisit x) w) = (tS D x).1 := by
  rcases swap_xv_cases D x w with ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · rw [h]; exact hw
  · rw [h]; exact Or.inr rfl
  · rw [h]; exact Or.inl rfl

/-- Untouched circles: the `s₁`-cycles are the old circles (proof of `sameCycle_of_comp_ne`). -/
theorem sameCycle_of_comp_ne' (v w : D.Γ.Visit) (hv : D.compOf v ≠ (sS D x).1)
    (hv' : D.compOf v ≠ (tS D x).1) :
    (D.record.reconnect (xv D x)).SameCycle v w ↔ D.compOf v = D.compOf w := by
  have hne : ∀ z, D.compOf z = D.compOf v → D.record.reconnect (xv D x) z = D.nextVisit z := by
    intro z hz
    rw [reconnect_xv_apply, swap_of_comp_ne D x z (hz ▸ hv) (hz ▸ hv')]
  constructor
  · intro hs
    obtain ⟨n, hn⟩ := hs.exists_nat_pow_eq
    have key : ∀ n, D.compOf (((D.record.reconnect (xv D x)) ^ n) v) = D.compOf v := by
      intro n
      induction n with
      | zero => rw [pow_zero, Equiv.Perm.one_apply]
      | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hne _ ih, D.compOf_nextVisit, ih]
    rw [← hn, key]
  · intro hc
    exact Record.sameCycle_of_eqOn_orbit D.visitSucc _ v w (D.visitSucc_sameCycle hc)
      (fun z hz => hne z ((D.record.sameCycle_iff_comp_eq v z).mp hz).symm)

theorem sameCycle_comp_i_or_j (v u : D.Γ.Visit) (hu : (D.record.reconnect (xv D x)).SameCycle u v)
    (hv : D.compOf v = (sS D x).1 ∨ D.compOf v = (tS D x).1) :
    D.compOf u = (sS D x).1 ∨ D.compOf u = (tS D x).1 := by
  by_contra h
  have h := not_or.mp h
  have := (sameCycle_of_comp_ne' D x u v h.1 h.2).mp hu
  rcases hv with hv | hv
  · exact h.1 (this.trans hv)
  · exact h.2 (this.trans hv)

/-- Self case: the `s₁`-cycle of `τ xv` (proof of `self_sameCycle_pair_iff`). -/
theorem self_sameCycle_pair_iff' (h : (sS D x).1 = (tS D x).1) (w : D.Γ.Visit)
    (hw : D.compOf w = (sS D x).1) :
    (D.record.reconnect (xv D x)).SameCycle w (D.underVisit x) ↔
      w = D.underVisit x ∨
        cycBetween (D.visitCoord (xv D x)) (D.visitCoord w) (D.visitCoord (D.underVisit x)) := by
  have hpq : xv D x ≠ D.underVisit x := xv_ne_underVisit D x
  have hc : D.compOf (D.underVisit x) = D.compOf (xv D x) := h.symm
  constructor
  · intro hsc
    obtain ⟨n, hn⟩ := hsc.symm.exists_nat_pow_eq
    rw [reconnect_eq_mul_swap] at hn
    have := (D.swap_pow_closed (xv D x) (D.underVisit x) hpq hc n).2
    rw [hn] at this
    exact this
  · intro hW
    rcases Record.reconnect_sameCycle_or D.record (xv D x) w hw with h1 | h1
    · exfalso
      obtain ⟨n, hn⟩ := h1.symm.exists_nat_pow_eq
      rw [reconnect_eq_mul_swap, Equiv.swap_comm] at hn
      have hW' := (D.swap_pow_closed (D.underVisit x) (xv D x) hpq.symm hc.symm n).2
      rw [hn] at hW'
      rcases hW with hW | hW <;> rcases hW' with hW' | hW'
      · exact hpq (hW'.symm.trans hW)
      · rw [hW] at hW'; exact not_cycBetween_self_left _ _ hW'
      · rw [hW'] at hW; exact not_cycBetween_self_left _ _ hW
      · exact cycBetween_asymm' hW hW'
    · exact h1


/-- `reconnect_no_between`, self case: everything lives on the circle of `s`. -/
theorem no_between_self (h : (sS D x).1 = (tS D x).1) (v u : D.Γ.Visit)
    (hu : (D.record.reconnect (xv D x)).SameCycle u v) (hv : D.compOf v = (sS D x).1) :
    ¬ cycBetween (key D x (Equiv.swap (xv D x) (D.underVisit x) v))
      (key D x (Equiv.swap (xv D x) (D.underVisit x) u))
      (key D x (Equiv.swap (xv D x) (D.underVisit x)
        (D.nextVisit (Equiv.swap (xv D x) (D.underVisit x) v)))) := by
  have hself : D.record.IsSelfCrossing (xv D x) := h
  have hnot : ¬ (D.record.reconnect (xv D x)).SameCycle (xv D x) (D.underVisit x) :=
    Record.not_reconnect_sameCycle_pair_of_self D.record (xv D x) hself
  have hcu : D.compOf u = (sS D x).1 :=
    ((D.record.sameCycle_iff_comp_eq u v).mp
      (Record.reconnect_sameCycle_refines_of_self D.record (xv D x) hself hu)).trans hv
  have hcτ : D.compOf (D.underVisit x) = (sS D x).1 := h.symm
  have hcx : D.compOf (xv D x) = (sS D x).1 := rfl
  have hcS : ∀ w, D.compOf w = (sS D x).1 →
      D.compOf (Equiv.swap (xv D x) (D.underVisit x) w) = (sS D x).1 := by
    intro w hw
    rcases swap_xv_cases D x w with ⟨-, -, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact hw
    · exact hcτ
    · exact hcx
  have hne : ∀ w₁ w₂, D.compOf w₁ = (sS D x).1 → D.compOf w₂ = (sS D x).1 → w₁ ≠ w₂ →
      key D x w₁ ≠ key D x w₂ :=
    fun w₁ w₂ h₁ h₂ hne he => hne (key_injOn_i D x w₁ w₂ h₁ h₂ he)
  rcases swap_xv_cases D x v with ⟨hv1, hv2, ev⟩ | ⟨rfl, ev⟩ | ⟨rfl, ev⟩
  · -- `v ∉ {xv, τxv}`
    rw [ev]
    rcases swap_xv_cases D x (D.nextVisit v) with ⟨hn1, hn2, en⟩ | ⟨hn, en⟩ | ⟨hn, en⟩
    · rw [en]
      exact key_nextVisit_no_between D x v _ ((hcS u hcu).trans hv.symm)
    · -- `succ v = xv`: `v` lies on the cycle of `xv`
      rw [en]
      have hvx : (D.record.reconnect (xv D x)).SameCycle v (xv D x) :=
        ⟨1, by rw [zpow_one, reconnect_xv_apply, ev, hn]⟩
      rcases swap_xv_cases D x u with ⟨hu1, hu2, eu⟩ | ⟨rfl, eu⟩ | ⟨rfl, eu⟩
      · rw [eu]
        have hux : (D.record.reconnect (xv D x)).SameCycle u (xv D x) := hu.trans hvx
        have hnu : ¬ (D.record.reconnect (xv D x)).SameCycle u (D.underVisit x) :=
          fun hc => hnot (hux.symm.trans hc)
        rw [self_sameCycle_pair_iff' D x h u hcu, not_or,
          ← key_cycBetween_i D x _ _ _ hcx hcu hcτ] at hnu
        have A := key_nextVisit_no_between D x v u (hcu.trans hv.symm)
        rw [hn] at A
        by_cases huv : u = v
        · rw [huv]; exact not_cycBetween_self_left _ _
        have p1 : cycBetween (key D x v) (key D x (xv D x)) (key D x u) :=
          (cycBetween_or_of_ne (hne v u hv hcu (Ne.symm huv)) (hne u _ hcu hcx hu1)
            (hne v _ hv hcx hv1)).resolve_left A
        have p2 : cycBetween (key D x (xv D x)) (key D x (D.underVisit x)) (key D x u) :=
          (cycBetween_or_of_ne (hne _ u hcx hcu (Ne.symm hu1)) (hne u _ hcu hcτ hu2)
            (hne _ _ hcx hcτ (xv_ne_underVisit D x))).resolve_left hnu.2
        exact not_cycBetween_of_of p1 p2
      · rw [eu]; exact not_cycBetween_self_mid _ _
      · exfalso; exact hnot (hu.trans hvx).symm
    · -- `succ v = τxv`: `v` lies on the cycle of `τxv`
      rw [en]
      have hvτ : (D.record.reconnect (xv D x)).SameCycle v (D.underVisit x) :=
        ⟨1, by rw [zpow_one, reconnect_xv_apply, ev, hn]⟩
      rcases swap_xv_cases D x u with ⟨hu1, hu2, eu⟩ | ⟨rfl, eu⟩ | ⟨rfl, eu⟩
      · rw [eu]
        have huτ := hu.trans hvτ
        rw [self_sameCycle_pair_iff' D x h u hcu] at huτ
        rw [self_sameCycle_pair_iff' D x h v hv] at hvτ
        have hu' := huτ.resolve_left hu2
        have hv' := hvτ.resolve_left hv2
        rw [← key_cycBetween_i D x _ _ _ hcx hcu hcτ, key_xv] at hu'
        rw [← key_cycBetween_i D x _ _ _ hcx hv hcτ, key_xv] at hv'
        have A := key_nextVisit_no_between D x v u (hcu.trans hv.symm)
        rw [hn] at A
        rw [key_xv]
        have hβ : 0 ≤ key D x (D.underVisit x) := key_nonneg_i D x _ hcτ
        rw [rexB_cycBetween_zero _ _ hβ] at hu' hv'
        intro hc
        apply A
        unfold cycBetween at hc ⊢
        rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith [hu'.1]
        · linarith [hu'.1]
        · exact Or.inl ⟨h2, hu'.2⟩
      · exfalso; exact hnot (hu.trans hvτ)
      · rw [eu]; exact not_cycBetween_self_mid _ _
  · -- `v = xv`, `swap v = τxv`
    rw [ev]
    have hn0 : D.nextVisit (D.underVisit x) ≠ D.underVisit x :=
      D.nextVisit_ne_self (D.underVisit x) (xv D x) h (xv_ne_underVisit D x)
    rcases swap_xv_cases D x (D.nextVisit (D.underVisit x)) with ⟨hn1, hn2, en⟩ | ⟨hn, en⟩ | ⟨hn, en⟩
    · rw [en]
      rcases swap_xv_cases D x u with ⟨hu1, hu2, eu⟩ | ⟨rfl, eu⟩ | ⟨rfl, eu⟩
      · rw [eu]; exact key_nextVisit_no_between D x _ u (hcu.trans hcτ.symm)
      · rw [eu]; exact not_cycBetween_self_left _ _
      · exfalso; exact hnot hu.symm
    · rw [en]; exact not_cycBetween_self_right _ _
    · exact absurd hn hn0
  · -- `v = τxv`, `swap v = xv`
    rw [ev]
    have hn0 : D.nextVisit (xv D x) ≠ xv D x :=
      D.nextVisit_ne_self (xv D x) (D.underVisit x) h.symm (xv_ne_underVisit D x).symm
    rcases swap_xv_cases D x (D.nextVisit (xv D x)) with ⟨hn1, hn2, en⟩ | ⟨hn, en⟩ | ⟨hn, en⟩
    · rw [en]
      rcases swap_xv_cases D x u with ⟨hu1, hu2, eu⟩ | ⟨rfl, eu⟩ | ⟨rfl, eu⟩
      · rw [eu]; exact key_nextVisit_no_between D x _ u (hcu.trans hcx.symm)
      · exfalso; exact hnot hu
      · rw [eu]; exact not_cycBetween_self_left _ _
    · exact absurd hn hn0
    · rw [en]; exact not_cycBetween_self_right _ _

/-- `reconnect_no_between`, mixed case: the circles of `s` and `t` are distinct and `key` places
the circle of `t` in the block `[k_i, k_i + k_j)`. -/
theorem no_between_mixed (hij : (sS D x).1 ≠ (tS D x).1) (v u : D.Γ.Visit)
    (hu : (D.record.reconnect (xv D x)).SameCycle u v)
    (hv : D.compOf v = (sS D x).1 ∨ D.compOf v = (tS D x).1) :
    ¬ cycBetween (key D x (Equiv.swap (xv D x) (D.underVisit x) v))
      (key D x (Equiv.swap (xv D x) (D.underVisit x) u))
      (key D x (Equiv.swap (xv D x) (D.underVisit x)
        (D.nextVisit (Equiv.swap (xv D x) (D.underVisit x) v)))) := by
  have hcx : D.compOf (xv D x) = (sS D x).1 := rfl
  have hcτ : D.compOf (D.underVisit x) = (tS D x).1 := rfl
  have hkI : (0 : ℝ) ≤ (kI D x : ℝ) := Nat.cast_nonneg _
  have hsu := compOf_swap_i_or_j D x u (sameCycle_comp_i_or_j D x v u hu hv)
  set su := Equiv.swap (xv D x) (D.underVisit x) u with hsu_def
  have hsu_i : D.compOf su = (sS D x).1 → 0 ≤ key D x su ∧ key D x su < (kI D x : ℝ) :=
    fun h => ⟨key_nonneg_i D x su h, key_lt_i D x su h⟩
  have hsu_j : D.compOf su = (tS D x).1 → (kI D x : ℝ) ≤ key D x su :=
    fun h => kI_le_key_j D x su h hij
  have hkx := key_xv D x
  have hkτ := key_underVisit_of_mixed D x hij
  rcases swap_xv_cases D x v with ⟨hv1, hv2, ev⟩ | ⟨rfl, ev⟩ | ⟨rfl, ev⟩
  · rw [ev]
    rcases hv with hvi | hvj
    · -- `v` on the circle of `s`
      have hkv := key_nonneg_i D x v hvi
      have hkv' := key_lt_i D x v hvi
      have hkv0 : (0 : ℝ) < key D x v :=
        lt_of_le_of_ne hkv (fun e => hv1 (key_injOn_i D x v _ hvi hcx (e.symm.trans hkx.symm)))
      have hcn : D.compOf (D.nextVisit v) = (sS D x).1 := (D.compOf_nextVisit v).trans hvi
      rcases swap_xv_cases D x (D.nextVisit v) with ⟨hn1, hn2, en⟩ | ⟨hn, en⟩ | ⟨hn, en⟩
      · rw [en]
        have hkn := key_nonneg_i D x _ hcn
        have hkn' := key_lt_i D x _ hcn
        have hkn0 : (0 : ℝ) < key D x (D.nextVisit v) :=
          lt_of_le_of_ne hkn (fun e => hn1 (key_injOn_i D x _ _ hcn hcx (e.symm.trans hkx.symm)))
        rcases hsu with hs | hs
        · exact key_nextVisit_no_between D x v su (hs.trans hvi.symm)
        · have hks := hsu_j hs
          have B := key_nextVisit_no_between D x v (xv D x) (hcx.trans hvi.symm)
          rw [hkx] at B
          intro hc
          unfold cycBetween at hc B
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · linarith
          · exact B (Or.inr (Or.inl ⟨hkn0, h1⟩))
      · rw [en, hkτ]
        rcases hsu with hs | hs
        · have A := key_nextVisit_no_between D x v su (hs.trans hvi.symm)
          rw [hn, hkx] at A
          obtain ⟨hs1, hs2⟩ := hsu_i hs
          intro hc
          unfold cycBetween at hc A
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact A (Or.inr (Or.inr ⟨hkv0, h1⟩))
          · linarith
          · linarith
        · have := hsu_j hs
          intro hc
          unfold cycBetween at hc
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      · exfalso
        exact hij (hcn.symm.trans (by rw [hn]; rfl))
    · -- `v` on the circle of `t`
      have hkv := kI_le_key_j D x v hvj hij
      have hkvk : (kI D x : ℝ) < key D x v :=
        lt_of_le_of_ne hkv (fun e => hv2 (key_injOn_j D x v _ hvj hcτ hij (e.symm.trans hkτ.symm)))
      have hcn : D.compOf (D.nextVisit v) = (tS D x).1 := (D.compOf_nextVisit v).trans hvj
      rcases swap_xv_cases D x (D.nextVisit v) with ⟨hn1, hn2, en⟩ | ⟨hn, en⟩ | ⟨hn, en⟩
      · rw [en]
        have hkn := kI_le_key_j D x _ hcn hij
        have hkn0 : (kI D x : ℝ) < key D x (D.nextVisit v) :=
          lt_of_le_of_ne hkn (fun e => hn2 (key_injOn_j D x _ _ hcn hcτ hij (e.symm.trans hkτ.symm)))
        rcases hsu with hs | hs
        · obtain ⟨hs1, hs2⟩ := hsu_i hs
          have B := key_nextVisit_no_between D x v (D.underVisit x) (hcτ.trans hvj.symm)
          rw [hkτ] at B
          intro hc
          unfold cycBetween at hc B
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · exact B (Or.inr (Or.inl ⟨hkn0, h2⟩))
          · linarith
        · exact key_nextVisit_no_between D x v su (hs.trans hvj.symm)
      · exfalso
        exact hij ((congrArg D.compOf hn).symm.trans hcn)
      · rw [en, hkx]
        rcases hsu with hs | hs
        · obtain ⟨hs1, hs2⟩ := hsu_i hs
          intro hc
          unfold cycBetween at hc
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
        · have A := key_nextVisit_no_between D x v su (hs.trans hvj.symm)
          rw [hn, hkτ] at A
          have := hsu_j hs
          intro hc
          unfold cycBetween at hc A
          rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
          · linarith
          · linarith
          · exact A (Or.inr (Or.inr ⟨hkvk, h2⟩))
  · -- `v = xv`, `swap v = τxv`
    rw [ev, hkτ]
    have hcn : D.compOf (D.nextVisit (D.underVisit x)) = (tS D x).1 :=
      (D.compOf_nextVisit _).trans hcτ
    rcases swap_xv_cases D x (D.nextVisit (D.underVisit x)) with ⟨hn1, hn2, en⟩ | ⟨hn, en⟩ | ⟨hn, en⟩
    · rw [en]
      have hkn := kI_le_key_j D x _ hcn hij
      rcases hsu with hs | hs
      · obtain ⟨hs1, hs2⟩ := hsu_i hs
        intro hc
        unfold cycBetween at hc
        rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      · have A := key_nextVisit_no_between D x (D.underVisit x) su (hs.trans hcτ.symm)
        rw [hkτ] at A
        exact A
    · exfalso
      exact hij ((congrArg D.compOf hn).symm.trans hcn)
    · rw [en, hkx]
      have halone := (D.nextVisit_eq_self_iff (D.underVisit x)).mp hn
      rcases hsu with hs | hs
      · obtain ⟨hs1, hs2⟩ := hsu_i hs
        intro hc
        unfold cycBetween at hc
        rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
      · have hsu_eq : su = D.underVisit x := halone su (hs.trans hcτ.symm)
        rw [hsu_eq, hkτ]
        exact not_cycBetween_self_left _ _
  · -- `v = τxv`, `swap v = xv`
    rw [ev, hkx]
    have hcn : D.compOf (D.nextVisit (xv D x)) = (sS D x).1 := (D.compOf_nextVisit _).trans hcx
    rcases swap_xv_cases D x (D.nextVisit (xv D x)) with ⟨hn1, hn2, en⟩ | ⟨hn, en⟩ | ⟨hn, en⟩
    · rw [en]
      have hkn := key_lt_i D x _ hcn
      have hkn0 := key_nonneg_i D x _ hcn
      rcases hsu with hs | hs
      · have A := key_nextVisit_no_between D x (xv D x) su (hs.trans hcx.symm)
        rw [hkx] at A
        exact A
      · have := hsu_j hs
        intro hc
        unfold cycBetween at hc
        rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    · rw [en, hkτ]
      have halone := (D.nextVisit_eq_self_iff (xv D x)).mp hn
      rcases hsu with hs | hs
      · have hsu_eq : su = xv D x := halone su (hs.trans hcx.symm)
        rw [hsu_eq, hkx]
        exact not_cycBetween_self_left _ _
      · have := hsu_j hs
        intro hc
        unfold cycBetween at hc
        rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    · exfalso
      exact hij ((congrArg D.compOf hn).symm.trans hcn).symm

theorem rkey_of_smoothKeep (v : D.Γ.Visit) (hv : D.record.SmoothKeep (xv D x) v) :
    rkey D x v = key D x v := by
  rw [Record.smoothKeep_iff] at hv
  have h2 : v ≠ D.underVisit x := hv.2
  unfold rkey
  rw [Equiv.swap_apply_of_ne_of_ne hv.1 h2]

/-- `key` is injective on each `s₁`-cycle (on the circle of `s`: `cyclicOffset` is a bijection of
`[0,k_i)`; mixed case: the shift `k_i` separates the two circles; elsewhere `visitCoord_injOn`). -/
theorem rkey_injOn (v u : D.Γ.Visit) (hu : (D.record.reconnect (xv D x)).SameCycle u v)
    (he : rkey D x u = rkey D x v) : u = v := by
  unfold rkey at he
  by_cases hv : D.compOf v = (sS D x).1 ∨ D.compOf v = (tS D x).1
  · have hsu := compOf_swap_i_or_j D x u (sameCycle_comp_i_or_j D x v u hu hv)
    have hsv := compOf_swap_i_or_j D x v hv
    apply (Equiv.swap (xv D x) (D.underVisit x)).injective
    by_cases hij : (sS D x).1 = (tS D x).1
    · have h1 : D.compOf (Equiv.swap (xv D x) (D.underVisit x) u) = (sS D x).1 := by
        rcases hsu with h | h
        · exact h
        · exact h.trans hij.symm
      have h2 : D.compOf (Equiv.swap (xv D x) (D.underVisit x) v) = (sS D x).1 := by
        rcases hsv with h | h
        · exact h
        · exact h.trans hij.symm
      exact key_injOn_i D x _ _ h1 h2 he
    · rcases hsu with h1 | h1 <;> rcases hsv with h2 | h2
      · exact key_injOn_i D x _ _ h1 h2 he
      · exfalso
        have := key_lt_i D x _ h1
        have := kI_le_key_j D x _ h2 hij
        linarith
      · exfalso
        have := kI_le_key_j D x _ h1 hij
        have := key_lt_i D x _ h2
        linarith
      · exact key_injOn_j D x _ _ h1 h2 hij he
  · have hv' := not_or.mp hv
    have hcu : D.compOf v = D.compOf u := (sameCycle_of_comp_ne' D x v u hv'.1 hv'.2).mp hu.symm
    rw [swap_of_comp_ne D x v hv'.1 hv'.2,
      swap_of_comp_ne D x u (fun e => hv'.1 (hcu.trans e)) (fun e => hv'.2 (hcu.trans e)),
      key_of_ne D x v hv'.1 hv'.2,
      key_of_ne D x u (fun e => hv'.1 (hcu.trans e)) (fun e => hv'.2 (hcu.trans e))] at he
    exact D.visitCoord_injOn hcu.symm he

/-- **`s₁` is the cyclic successor for `rkey` on each of its cycles.**  Away from `xv, τ xv`:
`s₁ v = succ v` and `nextVisit_no_between` transported by the rotation (`rexPL_rot_eq_cyclicOffset`,
`rexB_cycBetween_rot`), the other circle (mixed case) being shifted out of the way; at `xv`:
`s₁ xv = succ (τ xv)`, `rkey xv = key (τ xv)` and the retained occurrences after `τ xv` have larger
keys; at `τ xv`: symmetric. -/
theorem reconnect_no_between (v u : D.Γ.Visit)
    (hu : (D.record.reconnect (xv D x)).SameCycle u v) :
    ¬ cycBetween (rkey D x v) (rkey D x u) (rkey D x (D.record.reconnect (xv D x) v)) := by
  unfold rkey
  rw [reconnect_xv_apply]
  by_cases hv : D.compOf v = (sS D x).1 ∨ D.compOf v = (tS D x).1
  · by_cases hij : (sS D x).1 = (tS D x).1
    · have hv' : D.compOf v = (sS D x).1 := by
        rcases hv with hv | hv
        · exact hv
        · exact hv.trans hij.symm
      exact no_between_self D x hij v u hu hv'
    · exact no_between_mixed D x hij v u hu hv
  · have hv' := not_or.mp hv
    have hcu : D.compOf v = D.compOf u := (sameCycle_of_comp_ne' D x v u hv'.1 hv'.2).mp hu.symm
    rw [swap_of_comp_ne D x v hv'.1 hv'.2,
      swap_of_comp_ne D x u (fun e => hv'.1 (hcu.trans e)) (fun e => hv'.2 (hcu.trans e)),
      swap_of_comp_ne D x (D.nextVisit v) (fun e => hv'.1 ((D.compOf_nextVisit v).symm.trans e))
        (fun e => hv'.2 ((D.compOf_nextVisit v).symm.trans e))]
    exact key_nextVisit_no_between D x v u hcu.symm

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
        cycBetween (D.visitCoord (xv D x)) (D.visitCoord w) (D.visitCoord (D.underVisit x)) :=
  self_sameCycle_pair_iff' D x h w hw

/-- Untouched circles: the `s₁`-cycles are the old circles. -/
theorem sameCycle_of_comp_ne (v w : D.Γ.Visit) (hv : D.compOf v ≠ (sS D x).1)
    (hv' : D.compOf v ≠ (tS D x).1) :
    (D.record.reconnect (xv D x)).SameCycle v w ↔ D.compOf v = D.compOf w :=
  sameCycle_of_comp_ne' D x v w hv hv'

/-- A rotated strictly monotone coordinate on each component transports the oriented cyclic order
of a diagram (`rexB_cycBetween_rot`, then `cycBetween` is three strict inequalities). -/
theorem visitBetween_iff_of_rot_lt_iff (D₀ : Diagram) (κ : D₀.Γ.Visit → ℝ) (c₀ : Fin D₀.Γ.c → ℝ)
    (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((D₀.Γ.comp l).k : ℝ))
    (hlt : ∀ v w, D₀.compOf v = D₀.compOf w →
      (rexB_rot ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) (c₀ (D₀.compOf v)) (D₀.visitCoord v) <
        rexB_rot ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) (c₀ (D₀.compOf v)) (D₀.visitCoord w) ↔ κ v < κ w))
    (v u w : D₀.Γ.Visit) (hu : D₀.compOf u = D₀.compOf v) (hw : D₀.compOf w = D₀.compOf v) :
    D₀.VisitBetween v u w ↔ cycBetween (κ v) (κ u) (κ w) := by
  have hb : ∀ z : D₀.Γ.Visit, D₀.compOf z = D₀.compOf v →
      0 ≤ D₀.visitCoord z ∧ D₀.visitCoord z < ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) := by
    intro z hz
    refine ⟨D₀.visitCoord_nonneg z, ?_⟩
    have := D₀.visitCoord_lt z
    rw [hz] at this
    exact this
  unfold Diagram.VisitBetween
  rw [← rexB_cycBetween_rot _ (c₀ (D₀.compOf v)) _ _ _ (hc₀ _) (hb v rfl) (hb u hu) (hb w hw)]
  have e1 := hlt v u hu.symm
  have e2 := hlt u w (hu.trans hw.symm)
  have e3 := hlt w v hw
  rw [hu] at e2
  rw [hw] at e3
  unfold cycBetween
  rw [e1, e2, e3]

section RecordBridge

variable {ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
include M hε

/-- The occurrence of `D` under an occurrence of `Γ₀`. -/
def origVisit (v : Γ₀.Visit) : D.Γ.Visit :=
  ⟨origCrossing D x M hε v.1, ⟨M.orig v.2.val, orig_mem_origCrossing D x M hε v.2.2⟩⟩

theorem origVisit_fst (v : Γ₀.Visit) : (origVisit D x M hε v).1 = origCrossing D x M hε v.1 := rfl

theorem origVisit_injective : Function.Injective (origVisit D x M hε) := by
  intro v w h
  obtain ⟨y, u, hu⟩ := v
  obtain ⟨y', u', hu'⟩ := w
  have h1 : origCrossing D x M hε y = origCrossing D x M hε y' := congrArg Sigma.fst h
  have hyy := origCrossing_injective D x M hε h1
  subst hyy
  have h2 : M.orig u = M.orig u' := congrArg (fun z : D.Γ.Visit => z.2.val) h
  have huu := orig_injOn_crossing D x M hε y hu hu' h2
  subst huu
  rfl

/-- Occurrences of `Γ₀` sit at crossings other than `x`: they are retained by `Record.smooth`. -/
theorem smoothKeep_origVisit (v : Γ₀.Visit) : D.record.SmoothKeep (xv D x) (origVisit D x M hε v) := by
  rw [Record.smoothKeep_iff, record_pair_xv]
  have hne : (origVisit D x M hε v).1 ≠ x := origCrossing_ne D x M hε v.1
  exact ⟨fun h => hne (congrArg Sigma.fst h), fun h => hne (congrArg Sigma.fst h)⟩

theorem exists_origVisit (w : D.Γ.Visit) (hw : D.record.SmoothKeep (xv D x) w) :
    ∃ v, origVisit D x M hε v = w := by
  rw [Record.smoothKeep_iff, record_pair_xv] at hw
  have hne : w.1 ≠ x := by
    intro h
    rcases D.visit_eq_over_or_under w with h' | h'
    · exact hw.1 (h'.trans (congrArg D.overVisit h))
    · exact hw.2 (h'.trans (congrArg D.underVisit h))
  obtain ⟨y, s, hs⟩ := w
  have hy : y ≠ x := hne
  have hmem : liftStrand D x M y s hs ∈ (liftCrossing D x M hε y hy).val := by
    have hs' : s ∈ ({y.fst, y.snd} : Finset D.Γ.Strand) := by rw [← y.val_eq]; exact hs
    rcases Finset.mem_insert.mp hs' with rfl | hs''
    · exact Finset.mem_insert_self _ _
    · rw [Finset.mem_singleton] at hs''
      subst hs''
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  refine ⟨⟨liftCrossing D x M hε y hy, ⟨liftStrand D x M y s hs, hmem⟩⟩, ?_⟩
  have key : ∀ (y' : D.Γ.Crossing) (_ : y' = y) (s' : D.Γ.Strand) (hs' : s' ∈ y'.val)
      (_ : s' = s), (⟨y', ⟨s', hs'⟩⟩ : D.Γ.Visit) = ⟨y, ⟨s, hs⟩⟩ := by
    rintro y' rfl s' hs' rfl; rfl
  exact key _ (origCrossing_liftCrossing D x M hε y hy) _ _ (orig_liftStrand D x M y s hs)

/-- The occurrences of `D₀` are the retained occurrences of `D`. -/
def visitEquiv : Γ₀.Visit ≃ {w : D.Γ.Visit // D.record.SmoothKeep (xv D x) w} :=
  Equiv.ofBijective (fun v => ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    ⟨fun v w h => origVisit_injective D x M hε (congrArg Subtype.val h),
     fun w => by
      obtain ⟨v, hv⟩ := exists_origVisit D x M hε w.1 w.2
      exact ⟨v, Subtype.ext hv⟩⟩

theorem twin_origVisit (v : Γ₀.Visit) :
    D.twin (origVisit D x M hε v) = origVisit D x M hε ((toDiagram D x M hε).twin v) := by
  have hmem : M.orig (Γ₀.other v.1 v.2.2) ∈ (origCrossing D x M hε v.1).val :=
    orig_mem_origCrossing D x M hε (Γ₀.other_mem v.1 v.2.2)
  have hne : M.orig (Γ₀.other v.1 v.2.2) ≠ M.orig v.2.val := fun h =>
    Γ₀.other_ne v.1 v.2.2 (orig_injOn_crossing D x M hε v.1 (Γ₀.other_mem v.1 v.2.2) v.2.2 h)
  have h := D.Γ.eq_other_of_mem_of_ne (origCrossing D x M hε v.1)
    (orig_mem_origCrossing D x M hε v.2.2) hmem hne
  exact congrArg (fun t : {s // s ∈ (origCrossing D x M hε v.1).val} =>
      (⟨origCrossing D x M hε v.1, t⟩ : D.Γ.Visit)) (Subtype.ext h.symm)

theorem overBit_origVisit (v : Γ₀.Visit) :
    (toDiagram D x M hε).overBit v = D.overBit (origVisit D x M hε v) := by
  have hov := orig_overStrand₀ D x M hε v.1
  by_cases h : v.2.val = overStrand₀ D x M hε v.1
  · have e1 : (toDiagram D x M hε).overBit v = true := decide_eq_true h
    have e2 : D.overBit (origVisit D x M hε v) = true := by
      apply decide_eq_true
      show M.orig v.2.val = D.overStrand (origCrossing D x M hε v.1)
      rw [h]; exact hov
    rw [e1, e2]
  · have e1 : (toDiagram D x M hε).overBit v = false := decide_eq_false h
    have e2 : D.overBit (origVisit D x M hε v) = false := by
      apply decide_eq_false
      intro heq
      exact h (orig_injOn_crossing D x M hε v.1 v.2.2 (overStrand₀_mem D x M hε v.1)
        (heq.trans hov.symm))
    rw [e1, e2]

theorem sign_origVisit (v : Γ₀.Visit) :
    (toDiagram D x M hε).sign v.1 = D.sign (origVisit D x M hε v).1 :=
  toDiagram_sign D x M hε v.1

-- (U6b's `kind_ne_arc_of_mem` was an exact duplicate of U4's, declared above in section `Model`.)

omit M in
/-- `origParam ∘ liftParam = id` on the non-arc kinds (the affine rescalings are inverse to each
other; the denominators `τ ∓ ε`, `1 − τ − ε` are positive by `SmallEps`). -/
theorem origParam_liftParam (κ : StrandKind D x) (hκ : κ ≠ StrandKind.arcST)
    (hκ' : κ ≠ StrandKind.arcTS) (θ : ℝ) : κ.origParam ε (κ.liftParam ε θ) = θ := by
  have h1 : τs D x - ε ≠ 0 := (sub_pos.mpr hε.lt_τs).ne'
  have h2 : 1 - τs D x - ε ≠ 0 := (sub_pos.mpr hε.lt_one_sub_τs).ne'
  have h3 : τt D x - ε ≠ 0 := (sub_pos.mpr hε.lt_τt).ne'
  have h4 : 1 - τt D x - ε ≠ 0 := (sub_pos.mpr hε.lt_one_sub_τt).ne'
  cases κ with
  | old e => rfl
  | cutStartS =>
    simp only [StrandKind.origParam, StrandKind.liftParam]
    rw [div_mul_cancel₀ _ h1]
  | cutEndS =>
    simp only [StrandKind.origParam, StrandKind.liftParam]
    rw [div_mul_cancel₀ _ h2]; ring
  | cutStartT =>
    simp only [StrandKind.origParam, StrandKind.liftParam]
    rw [div_mul_cancel₀ _ h3]
  | cutEndT =>
    simp only [StrandKind.origParam, StrandKind.liftParam]
    rw [div_mul_cancel₀ _ h4]; ring
  | arcST => exact absurd rfl hκ
  | arcTS => exact absurd rfl hκ'

/-- The traversal coordinate of an occurrence of `D₀` under `origVisit`: the original parameter is
the rescaled one (`crossingParam_toDiagram`), so `visitCoord (origVisit v) = label(orig).val +
origParam (param₀ v)`. -/
theorem visitCoord_origVisit (v : Γ₀.Visit) :
    D.visitCoord (origVisit D x M hε v) =
      ((M.orig v.2.val).2.val : ℝ) +
        (M.kind v.2.val).origParam ε ((toDiagram D x M hε).crossingParam v.1 v.2.2) := by
  rw [D.visitCoord_eq, crossingParam_toDiagram D x M hε v.1 v.2.2]
  have hna := kind_ne_arc_of_mem D x M hε v.1 v.2.2
  rw [origParam_liftParam D x hε _ hna.1 hna.2]
  rfl

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
  have e := Record.smooth_comp_eq_iff D.record (xv D x)
    ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩
    ⟨origVisit D x M hε w, smoothKeep_origVisit D x M hε w⟩
  rw [← hcls_visit v, ← hcls_visit w, hcls.eq_iff] at e
  exact e

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
  have hcomp := compOf_eq_iff_of_cls D x M hε cls hcls hcls_visit
  -- the smoothed successor lies on the `s₁`-cycle of `origVisit v` and is retained
  have hsc : (D.record.reconnect (xv D x)).SameCycle (origVisit D x M hε v)
      ((D.record.smooth (xv D x)).succ
        ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩).1 :=
    sameCycle_firstReturn_apply (D.record.reconnect (xv D x)) (D.record.SmoothKeep (xv D x))
      ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩
  obtain ⟨v', hv'⟩ := exists_origVisit D x M hε
    ((D.record.smooth (xv D x)).succ ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩).1
    ((D.record.smooth (xv D x)).succ ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩).2
  rw [← hv'] at hsc ⊢
  have hcv' : (toDiagram D x M hε).compOf v' = (toDiagram D x M hε).compOf v :=
    (hcomp v' v).mpr hsc.symm
  by_cases hsingle : ∀ u : Γ₀.Visit,
      (toDiagram D x M hε).compOf u = (toDiagram D x M hε).compOf v → u = v
  · rw [(toDiagram D x M hε).nextVisit_eq_self v hsingle, hsingle v' hcv']
  · push Not at hsingle
    obtain ⟨u, hu, hne⟩ := hsingle
    -- the smoothed successor is not `origVisit v` itself: a fixed point of the first return would
    -- make its cycle a singleton, but `origVisit u` is on it
    have hv'ne : v' ≠ v := by
      intro heq
      have hfix : (D.record.smooth (xv D x)).succ
          ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩ =
          ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩ := by
        apply Subtype.ext
        rw [← hv', heq]
      have hsame : (D.record.reconnect (xv D x)).SameCycle (origVisit D x M hε v)
          (origVisit D x M hε u) := (hcomp v u).mp hu.symm
      have hsame' : ((D.record.smooth (xv D x)).succ).SameCycle
          ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩
          ⟨origVisit D x M hε u, smoothKeep_origVisit D x M hε u⟩ :=
        firstReturn_sameCycle_of_sameCycle (D.record.reconnect (xv D x))
          (D.record.SmoothKeep (xv D x)) hsame
      have h := hsame'.eq_of_left hfix
      exact hne (origVisit_injective D x M hε (congrArg Subtype.val h)).symm
    -- no occurrence of the component lies strictly between `v` and `v'`
    have hbetw : ∀ u' : Γ₀.Visit,
        (toDiagram D x M hε).compOf u' = (toDiagram D x M hε).compOf v →
        ¬ cycBetween ((toDiagram D x M hε).visitCoord v) ((toDiagram D x M hε).visitCoord u')
          ((toDiagram D x M hε).visitCoord v') := by
      intro u' hu' hb
      have hiff := visitBetween_iff_of_rot_lt_iff (toDiagram D x M hε)
        (fun z => key D x (origVisit D x M hε z)) c₀ hc₀ hlt v u' v' hu' hcv'
      have hb' : (toDiagram D x M hε).VisitBetween v u' v' := hb
      have h2 : cycBetween (key D x (origVisit D x M hε v)) (key D x (origVisit D x M hε u'))
          (key D x (origVisit D x M hε v')) := hiff.mp hb'
      rw [hv'] at h2
      exact smoothSucc_no_between D x _ (smoothKeep_origVisit D x M hε v) _
        ((hcomp u' v).mp hu') (smoothKeep_origVisit D x M hε u') h2
    have hnv : (toDiagram D x M hε).nextVisit v = v' :=
      cycNext_unique_on
        (p := fun u' : Γ₀.Visit => (toDiagram D x M hε).compOf u' = (toDiagram D x M hε).compOf v)
        (k := (toDiagram D x M hε).visitCoord)
        (fun a b ha hb h => (toDiagram D x M hε).visitCoord_injOn (ha.trans hb.symm) h)
        rfl ((toDiagram D x M hε).compOf_nextVisit v) hcv'
        ((toDiagram D x M hε).nextVisit_ne_self v u hu hne) hv'ne
        (fun u' hu' => (toDiagram D x M hε).nextVisit_no_between v u' hu') hbetw
    rw [hnv]

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
  have h : ∃ w : D.Γ.Visit, D.compOf w = i₀ := ⟨w, hw⟩
  have hc := Classical.choose_spec h
  -- the `dite_eq_left` branch, stated in term mode (`rw` fails at instance transparency here)
  have e : oldCls D x i₀ = Sum.inl (Quotient.mk _ (Classical.choose h)) := dite_eq_left h
  refine e.trans (congrArg Sum.inl (Quotient.sound ?_))
  exact (sameCycle_of_comp_ne D x _ w (by rw [hc]; exact hi) (by rw [hc]; exact hj)).mpr
    (hc.trans hw.symm)

/-! ### 8a-pre. Helpers for the per-case classification and rotated coordinate (sub-lane 6c)

The smoothed coordinate `key` evaluated block by block, the arithmetic of `cyclicOffset` on the
labels `(a + n).val`, and a generic "block monotonicity" lemma turning a piecewise-affine
description of `key ∘ origVisit` in the rotated coordinate into the `lt_iff` the record bridge
needs. -/

theorem oldCls_of_exists (i₀ : Fin D.Γ.c) (hex : ∃ w : D.Γ.Visit, D.compOf w = i₀) :
    oldCls D x i₀ = Sum.inl (Quotient.mk _ (Classical.choose hex)) := by
  unfold oldCls; exact dite_eq_left hex

theorem oldCls_eq_inr (i₀ : Fin D.Γ.c) (hex : ¬ ∃ w : D.Γ.Visit, D.compOf w = i₀) :
    oldCls D x i₀ = Sum.inr ⟨i₀, fun w hw => hex ⟨w, hw⟩⟩ := by
  unfold oldCls; exact dite_eq_right hex

/-- Injectivity of `Sum.inl ∘ Quotient.mk` into the smoothed components, stated at the unfolded type
(the `Record.smooth` transparency caveat of PLAN_FINAL §6). -/
theorem inl_mk_eq_iff (a b : D.Γ.Visit) :
    (Sum.inl (Quotient.mk _ a) : (D.record.smooth (xv D x)).comps) = Sum.inl (Quotient.mk _ b) ↔
      (D.record.reconnect (xv D x)).SameCycle a b := by
  constructor
  · intro hab
    have hab' : (Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid (D.record.reconnect (xv D x))) a) :
        Quotient (Equiv.Perm.SameCycle.setoid (D.record.reconnect (xv D x))) ⊕ D.record.FreeComp) =
        Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid (D.record.reconnect (xv D x))) b) := hab
    exact Quotient.exact (Sum.inl.inj hab')
  · intro hab
    exact congrArg Sum.inl (Quotient.sound hab)

theorem inl_ne_inr (a : D.Γ.Visit) (c : D.record.FreeComp) :
    (Sum.inl (Quotient.mk _ a) : (D.record.smooth (xv D x)).comps) ≠ Sum.inr c := by
  intro hac
  have hac' : (Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid (D.record.reconnect (xv D x))) a) :
      Quotient (Equiv.Perm.SameCycle.setoid (D.record.reconnect (xv D x))) ⊕ D.record.FreeComp) =
      Sum.inr c := hac
  exact Sum.inl_ne_inr hac'

/-- `oldCls i₀ = ⟦w⟧` forces `w` to lie on `i₀` (untouched component). -/
theorem oldCls_eq_inl_imp (i₀ : Fin D.Γ.c) (hi : i₀ ≠ (sS D x).1) (hj : i₀ ≠ (tS D x).1)
    (w : D.Γ.Visit) (hw : oldCls D x i₀ = Sum.inl (Quotient.mk _ w)) : D.compOf w = i₀ := by
  by_cases hex : ∃ w : D.Γ.Visit, D.compOf w = i₀
  · rw [oldCls_of_exists D x i₀ hex] at hw
    have hsc := (inl_mk_eq_iff D x _ _).mp hw
    have hc := Classical.choose_spec hex
    rw [← hc]
    exact ((sameCycle_of_comp_ne D x _ _ (by rw [hc]; exact hi) (by rw [hc]; exact hj)).mp hsc).symm
  · rw [oldCls_eq_inr D x i₀ hex] at hw
    exact (inl_ne_inr D x _ _ hw.symm).elim

/-- `oldCls` is injective on the untouched components. -/
theorem oldCls_injOn (i₀ i₁ : Fin D.Γ.c) (hi₀ : i₀ ≠ (sS D x).1) (hj₀ : i₀ ≠ (tS D x).1)
    (hi₁ : i₁ ≠ (sS D x).1) (hj₁ : i₁ ≠ (tS D x).1) (heq : oldCls D x i₀ = oldCls D x i₁) :
    i₀ = i₁ := by
  by_cases hex : ∃ w : D.Γ.Visit, D.compOf w = i₀
  · obtain ⟨w, hw⟩ := hex
    rw [oldCls_eq D x i₀ hi₀ hj₀ w hw] at heq
    exact hw.symm.trans (oldCls_eq_inl_imp D x i₁ hi₁ hj₁ w heq.symm)
  · by_cases hex' : ∃ w : D.Γ.Visit, D.compOf w = i₁
    · obtain ⟨w, hw⟩ := hex'
      rw [oldCls_eq D x i₁ hi₁ hj₁ w hw] at heq
      exact absurd (oldCls_eq_inl_imp D x i₀ hi₀ hj₀ w heq) (fun hc => hex ⟨w, hc⟩)
    · rw [oldCls_eq_inr D x i₀ hex, oldCls_eq_inr D x i₁ hex'] at heq
      exact congrArg Subtype.val (Sum.inr.inj heq)

theorem mem_othersM {c : Fin D.Γ.c} : c ∈ othersM D x ↔ c ≠ (tS D x).1 ∧ c ≠ (sS D x).1 := by
  simp [othersM]

theorem mem_othersS {c : Fin D.Γ.c} : c ∈ othersS D x ↔ c ≠ (sS D x).1 := by
  simp [othersS]

-- (U6c's `orderEmbOfFin_othersM_ne` / `orderEmbOfFin_othersS_ne` were exact duplicates of U5's, above.)

theorem othersM_exists_emb {c : Fin D.Γ.c} (hc : c ∈ othersM D x) :
    ∃ l, (othersM D x).orderEmbOfFin rfl l = c := by
  have : c ∈ Set.range ⇑((othersM D x).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hc
  exact Set.mem_range.mp this

theorem othersS_exists_emb {c : Fin D.Γ.c} (hc : c ∈ othersS D x) :
    ∃ l, (othersS D x).orderEmbOfFin rfl l = c := by
  have : c ∈ Set.range ⇑((othersS D x).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hc
  exact Set.mem_range.mp this

/-- The coordinates of the two erased occurrences: edge label plus crossing parameter. -/
theorem visitCoord_xv : D.visitCoord (xv D x) = ((aS D x).val : ℝ) + τs D x := rfl

theorem visitCoord_underVisit : D.visitCoord (D.underVisit x) = ((bT D x).val : ℝ) + τt D x := rfl

theorem key_of_comp_s (w : D.Γ.Visit) (hw : D.compOf w = (sS D x).1) :
    key D x w = Diagram.cyclicOffset (kI D x) (D.visitCoord (xv D x)) (D.visitCoord w) := by
  unfold key; rw [ite_eq_left hw]

theorem key_of_comp_t (w : D.Γ.Visit) (hw : D.compOf w = (tS D x).1) (h : (sS D x).1 ≠ (tS D x).1) :
    key D x w = (kI D x : ℝ) +
      Diagram.cyclicOffset (kJ D x) (D.visitCoord (D.underVisit x)) (D.visitCoord w) := by
  unfold key
  rw [ite_eq_right (fun h' => h (h'.symm.trans hw)), ite_eq_left hw]

theorem key_of_comp_other (w : D.Γ.Visit) (h1 : D.compOf w ≠ (sS D x).1)
    (h2 : D.compOf w ≠ (tS D x).1) : key D x w = D.visitCoord w := by
  unfold key; rw [ite_eq_right h1, ite_eq_right h2]

/-- Forward cyclic distance from `a.val + τ` to `(a + n).val + φ` on the circle of length `k`
(`1 ≤ n < k`, `τ ∈ (0,1)`, `φ ∈ [0,1)`): the label difference `n` plus `φ − τ`, whether or not
the label `a + n` wraps past `0`. -/
theorem cyclicOffset_val_add {k : ℕ} [NeZero k] (a : ZMod k) (n : ℕ) (hn1 : 1 ≤ n) (hnk : n < k)
    {τ φ : ℝ} (hτ : 0 < τ ∧ τ < 1) (hφ : 0 ≤ φ ∧ φ < 1) :
    Diagram.cyclicOffset k ((a.val : ℝ) + τ) (((a + (n : ZMod k)).val : ℝ) + φ) = n + φ - τ := by
  have hav := ZMod.val_lt a
  rw [ZMod.val_add, ZMod.val_cast_of_lt hnk]
  by_cases hlt : a.val + n < k
  · rw [Nat.mod_eq_of_lt hlt, Diagram.cyclicOffset_of_le]
    · push_cast; ring
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      push_cast; linarith
  · have hge : k ≤ a.val + n := not_lt.mp hlt
    have hlt2 : a.val + n - k < k := by omega
    have hmod : (a.val + n) % k = a.val + n - k := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt2]
    rw [hmod, Diagram.cyclicOffset_of_lt]
    · rw [Nat.cast_sub hge]; push_cast; ring
    · rw [Nat.cast_sub hge]
      have : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
      push_cast; linarith

theorem rexB_rot_of_lt {k c r : ℝ} (h : r < c) : rexB_rot k c r = r - c + k := by
  unfold rexB_rot; rw [ite_eq_left h]

theorem rexB_rot_of_le {k c r : ℝ} (h : c ≤ r) : rexB_rot k c r = r - c := by
  unfold rexB_rot; rw [ite_eq_right (not_lt.mpr h)]

/-- **Block monotonicity.**  If a coordinate `r` ranges over blocks `[lo i, hi i)` listed in
increasing order, and on block `i` a second coordinate is `F i r` with `F i` strictly increasing on
the block and with values in `[flo i, fhi i)`, these also increasing, then two points compare the
same way in both coordinates. -/
theorem lt_iff_of_blocks (n : ℕ) (lo hi flo fhi : ℕ → ℝ) (F : ℕ → ℝ → ℝ)
    (hlohi : ∀ i, i < n → lo i ≤ hi i ∧ flo i ≤ fhi i)
    (hchain : ∀ i, i + 1 < n → hi i ≤ lo (i + 1) ∧ fhi i ≤ flo (i + 1))
    (hmono : ∀ i, i < n → ∀ r r', lo i ≤ r → r < hi i → lo i ≤ r' → r' < hi i →
      (r < r' ↔ F i r < F i r'))
    (hrange : ∀ i, i < n → ∀ r, lo i ≤ r → r < hi i → flo i ≤ F i r ∧ F i r < fhi i)
    {i j : ℕ} (hi' : i < n) (hj : j < n) {r r' : ℝ}
    (hr : lo i ≤ r ∧ r < hi i) (hr' : lo j ≤ r' ∧ r' < hi j) :
    r < r' ↔ F i r < F j r' := by
  have key : ∀ i j, i < j → j < n → hi i ≤ lo j ∧ fhi i ≤ flo j := by
    intro i j hij hjn
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hij' | rfl
      · have h1 := ih hij' (by omega)
        have h2 := hlohi j (by omega)
        have h3 := hchain j hjn
        exact ⟨h1.1.trans (h2.1.trans h3.1), h1.2.trans (h2.2.trans h3.2)⟩
      · exact hchain i hjn
  rcases lt_trichotomy i j with hij | rfl | hji
  · obtain ⟨h1, h2⟩ := key i j hij hj
    have hF := hrange i hi' r hr.1 hr.2
    have hF' := hrange j hj r' hr'.1 hr'.2
    exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · exact hmono i hi' r r' hr.1 hr.2 hr'.1 hr'.2
  · obtain ⟨h1, h2⟩ := key j i hji hi'
    have hF := hrange i hi' r hr.1 hr.2
    have hF' := hrange j hj r' hr'.1 hr'.2
    exact ⟨fun h => absurd h (by linarith), fun h => absurd h (by linarith)⟩

/-- `b = a + d` on the circle of `s` (self case: `d = (bS − a).val`). -/
theorem bS_eq : bS D x = aS D x + (dd D x : ZMod (kI D x)) := by
  unfold dd; rw [ZMod.natCast_zmod_val]; ring

theorem kJ_eq (h : (sS D x).1 = (tS D x).1) : kJ D x = kI D x := by
  unfold kJ kI; rw [h]

theorem bT_val_lt_kI (h : (sS D x).1 = (tS D x).1) : (bT D x).val < kI D x :=
  calc (bT D x).val < kJ D x := ZMod.val_lt _
    _ = kI D x := kJ_eq D x h

theorem val_aS_add_dd (h : (sS D x).1 = (tS D x).1) :
    (aS D x + (dd D x : ZMod (kI D x))).val = (bT D x).val := by
  rw [← bS_eq]
  exact ZMod.val_cast_of_lt (bT_val_lt_kI D x h)

/-- The forward distance from the over to the under occurrence on the circle of `s` (self case). -/
theorem cyclicOffset_xv_underVisit (h : (sS D x).1 = (tS D x).1) :
    Diagram.cyclicOffset (kI D x) (D.visitCoord (xv D x)) (D.visitCoord (D.underVisit x)) =
      (dd D x : ℝ) + τt D x - τs D x := by
  rw [visitCoord_xv, visitCoord_underVisit, ← val_aS_add_dd D x h]
  exact cyclicOffset_val_add _ _ (by have := two_le_dd D x h; omega)
    (by have := dd_add_two_le D x h; omega) ⟨τs_pos D x, τs_lt_one D x⟩
    ⟨(τt_pos D x).le, τt_lt_one D x⟩

/-- Self case: an occurrence `w` of the circle of `s` lies strictly between `xv` and `τ xv` iff its
forward distance from `xv` is strictly between `0` and that of `τ xv`. -/
theorem cycBetween_xv_iff (h : (sS D x).1 = (tS D x).1) (w : D.Γ.Visit)
    (hw : D.compOf w = (sS D x).1) :
    cycBetween (D.visitCoord (xv D x)) (D.visitCoord w) (D.visitCoord (D.underVisit x)) ↔
      0 < Diagram.cyclicOffset (kI D x) (D.visitCoord (xv D x)) (D.visitCoord w) ∧
        Diagram.cyclicOffset (kI D x) (D.visitCoord (xv D x)) (D.visitCoord w) <
          (dd D x : ℝ) + τt D x - τs D x := by
  have hxv : 0 ≤ D.visitCoord (xv D x) ∧ D.visitCoord (xv D x) < (kI D x : ℝ) :=
    ⟨D.visitCoord_nonneg _, D.visitCoord_lt (xv D x)⟩
  have hw' : 0 ≤ D.visitCoord w ∧ D.visitCoord w < (kI D x : ℝ) := by
    refine ⟨D.visitCoord_nonneg _, ?_⟩
    have := D.visitCoord_lt w
    rw [hw] at this
    exact this
  have hτ : 0 ≤ D.visitCoord (D.underVisit x) ∧ D.visitCoord (D.underVisit x) < (kI D x : ℝ) := by
    refine ⟨D.visitCoord_nonneg _, ?_⟩
    have := D.visitCoord_lt (D.underVisit x)
    rw [D.compOf_underVisit, ← h] at this
    exact this
  rw [← rexB_cycBetween_rot (kI D x : ℝ) (D.visitCoord (xv D x)) _ _ _ hxv hxv hw' hτ, rexB_rot_self,
    rexPL_rot_eq_cyclicOffset, rexPL_rot_eq_cyclicOffset,
    rexB_cycBetween_zero _ _ (Diagram.cyclicOffset_nonneg hxv.2 hτ.1), cyclicOffset_xv_underVisit D x h]

section KeyHelpers

variable {ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
include M hε

theorem compOf_origVisit (v : Γ₀.Visit) : D.compOf (origVisit D x M hε v) = (M.orig v.2.val).1 := rfl

theorem visitCoord_toDiagram (v : Γ₀.Visit) :
    (toDiagram D x M hε).visitCoord v =
      (v.2.val.2.val : ℝ) + (toDiagram D x M hε).crossingParam v.1 v.2.2 := rfl

/-- Occurrences of `Γ₀` never lie on an arc: an arc occurrence would have the coordinate of the
erased occurrence `xv` (resp. `τ xv`) on the same circle, contradicting `smoothKeep_origVisit`. -/
theorem kind_visit_ne_arcST (v : Γ₀.Visit) : M.kind v.2.val ≠ StrandKind.arcST := by
  intro ha
  have hk := visitCoord_origVisit D x M hε v
  have hsk := (D.record.smoothKeep_iff (xv D x) _).mp (smoothKeep_origVisit D x M hε v)
  apply hsk.1
  apply D.visitCoord_injOn
  · show (M.orig v.2.val).1 = (sS D x).1
    unfold SpliceModel.orig; rw [ha]; rfl
  · rw [hk, visitCoord_xv]; unfold SpliceModel.orig; rw [ha]; rfl

theorem kind_visit_ne_arcTS (v : Γ₀.Visit) : M.kind v.2.val ≠ StrandKind.arcTS := by
  intro ha
  have hk := visitCoord_origVisit D x M hε v
  have hsk := (D.record.smoothKeep_iff (xv D x) _).mp (smoothKeep_origVisit D x M hε v)
  have hsk2 : origVisit D x M hε v ≠ D.underVisit x := hsk.2
  apply hsk2
  apply D.visitCoord_injOn
  · show (M.orig v.2.val).1 = (tS D x).1
    unfold SpliceModel.orig; rw [ha]; rfl
  · rw [hk, visitCoord_underVisit]; unfold SpliceModel.orig; rw [ha]; rfl

/-- `key ∘ origVisit` on an old edge `⟨i, a + 1 + n⟩` of the circle of `s`. -/
theorem key_origVisit_old_s (v : Γ₀.Visit) (n : ℕ) (hnk : n + 1 < kI D x)
    (hk : M.kind v.2.val = StrandKind.old ⟨(sS D x).1, aS D x + 1 + (n : ZMod (kI D x))⟩) :
    key D x (origVisit D x M hε v) =
      (n : ℝ) + 1 + (toDiagram D x M hε).crossingParam v.1 v.2.2 - τs D x := by
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v.1 v.2.2
  have hθ1 := (toDiagram D x M hε).crossingParam_lt_one v.1 v.2.2
  have horig : M.orig v.2.val = ⟨(sS D x).1, aS D x + ((n + 1 : ℕ) : ZMod (kI D x))⟩ := by
    unfold SpliceModel.orig; rw [hk]
    exact congrArg (fun z : ZMod (kI D x) => (⟨(sS D x).1, z⟩ : D.Γ.Strand)) (by push_cast; ring)
  rw [key_of_comp_s D x _ (by rw [compOf_origVisit, horig]), visitCoord_origVisit, visitCoord_xv,
    horig, hk]
  show Diagram.cyclicOffset (kI D x) (((aS D x).val : ℝ) + τs D x)
    (((aS D x + ((n + 1 : ℕ) : ZMod (kI D x))).val : ℝ) + (toDiagram D x M hε).crossingParam v.1 v.2.2) = _
  rw [cyclicOffset_val_add _ (n + 1) (by omega) hnk ⟨τs_pos D x, τs_lt_one D x⟩ ⟨hθ0.le, hθ1⟩]
  push_cast; ring

theorem key_origVisit_cutStartS (v : Γ₀.Visit) (hk : M.kind v.2.val = StrandKind.cutStartS) :
    key D x (origVisit D x M hε v) =
      (kI D x : ℝ) - τs D x + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (τs D x - ε) := by
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v.1 v.2.2
  have hθ1 := (toDiagram D x M hε).crossingParam_lt_one v.1 v.2.2
  have horig : M.orig v.2.val = sS D x := by unfold SpliceModel.orig; rw [hk]; rfl
  rw [key_of_comp_s D x _ (by rw [compOf_origVisit, horig]), visitCoord_origVisit, visitCoord_xv,
    horig, hk]
  show Diagram.cyclicOffset (kI D x) (((aS D x).val : ℝ) + τs D x)
    (((aS D x).val : ℝ) + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (τs D x - ε)) = _
  rw [Diagram.cyclicOffset_of_lt]
  · ring
  · nlinarith [hε.pos, hε.lt_τs]

theorem key_origVisit_cutEndS (v : Γ₀.Visit) (hk : M.kind v.2.val = StrandKind.cutEndS) :
    key D x (origVisit D x M hε v) =
      ε + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (1 - τs D x - ε) := by
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v.1 v.2.2
  have hθ1 := (toDiagram D x M hε).crossingParam_lt_one v.1 v.2.2
  have horig : M.orig v.2.val = sS D x := by unfold SpliceModel.orig; rw [hk]; rfl
  rw [key_of_comp_s D x _ (by rw [compOf_origVisit, horig]), visitCoord_origVisit, visitCoord_xv,
    horig, hk]
  show Diagram.cyclicOffset (kI D x) (((aS D x).val : ℝ) + τs D x)
    (((aS D x).val : ℝ) + (τs D x + ε + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (1 - τs D x - ε))) = _
  rw [Diagram.cyclicOffset_of_le]
  · ring
  · nlinarith [hε.pos, hε.lt_one_sub_τs]

theorem key_origVisit_cutEndT_mixed (h : (sS D x).1 ≠ (tS D x).1) (v : Γ₀.Visit)
    (hk : M.kind v.2.val = StrandKind.cutEndT) :
    key D x (origVisit D x M hε v) =
      (kI D x : ℝ) + ε + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (1 - τt D x - ε) := by
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v.1 v.2.2
  have hθ1 := (toDiagram D x M hε).crossingParam_lt_one v.1 v.2.2
  have horig : M.orig v.2.val = tS D x := by unfold SpliceModel.orig; rw [hk]; rfl
  rw [key_of_comp_t D x _ (by rw [compOf_origVisit, horig]) h, visitCoord_origVisit,
    visitCoord_underVisit, horig, hk]
  show (kI D x : ℝ) + Diagram.cyclicOffset (kJ D x) (((bT D x).val : ℝ) + τt D x)
    (((bT D x).val : ℝ) + (τt D x + ε + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (1 - τt D x - ε))) = _
  rw [Diagram.cyclicOffset_of_le]
  · ring
  · nlinarith [hε.pos, hε.lt_one_sub_τt]

theorem key_origVisit_cutStartT_mixed (h : (sS D x).1 ≠ (tS D x).1) (v : Γ₀.Visit)
    (hk : M.kind v.2.val = StrandKind.cutStartT) :
    key D x (origVisit D x M hε v) =
      (kI D x : ℝ) + kJ D x - τt D x + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (τt D x - ε) := by
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v.1 v.2.2
  have hθ1 := (toDiagram D x M hε).crossingParam_lt_one v.1 v.2.2
  have horig : M.orig v.2.val = tS D x := by unfold SpliceModel.orig; rw [hk]; rfl
  rw [key_of_comp_t D x _ (by rw [compOf_origVisit, horig]) h, visitCoord_origVisit,
    visitCoord_underVisit, horig, hk]
  show (kI D x : ℝ) + Diagram.cyclicOffset (kJ D x) (((bT D x).val : ℝ) + τt D x)
    (((bT D x).val : ℝ) + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (τt D x - ε)) = _
  rw [Diagram.cyclicOffset_of_lt]
  · ring
  · nlinarith [hε.pos, hε.lt_τt]

/-- `key ∘ origVisit` on an old edge `⟨j, b + 1 + n⟩` of the circle of `t` (mixed case). -/
theorem key_origVisit_old_t_mixed (h : (sS D x).1 ≠ (tS D x).1) (v : Γ₀.Visit) (n : ℕ)
    (hnk : n + 1 < kJ D x)
    (hk : M.kind v.2.val = StrandKind.old ⟨(tS D x).1, bT D x + 1 + (n : ZMod (kJ D x))⟩) :
    key D x (origVisit D x M hε v) =
      (kI D x : ℝ) + ((n : ℝ) + 1) + (toDiagram D x M hε).crossingParam v.1 v.2.2 - τt D x := by
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v.1 v.2.2
  have hθ1 := (toDiagram D x M hε).crossingParam_lt_one v.1 v.2.2
  have horig : M.orig v.2.val = ⟨(tS D x).1, bT D x + ((n + 1 : ℕ) : ZMod (kJ D x))⟩ := by
    unfold SpliceModel.orig; rw [hk]
    exact congrArg (fun z : ZMod (kJ D x) => (⟨(tS D x).1, z⟩ : D.Γ.Strand)) (by push_cast; ring)
  rw [key_of_comp_t D x _ (by rw [compOf_origVisit, horig]) h, visitCoord_origVisit,
    visitCoord_underVisit, horig, hk]
  show (kI D x : ℝ) + Diagram.cyclicOffset (kJ D x) (((bT D x).val : ℝ) + τt D x)
    (((bT D x + ((n + 1 : ℕ) : ZMod (kJ D x))).val : ℝ) + (toDiagram D x M hε).crossingParam v.1 v.2.2) = _
  rw [cyclicOffset_val_add _ (n + 1) (by omega) hnk ⟨τt_pos D x, τt_lt_one D x⟩ ⟨hθ0.le, hθ1⟩]
  push_cast; ring

theorem key_origVisit_cutStartT_self (h : (sS D x).1 = (tS D x).1) (v : Γ₀.Visit)
    (hk : M.kind v.2.val = StrandKind.cutStartT) :
    key D x (origVisit D x M hε v) =
      (dd D x : ℝ) - τs D x + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (τt D x - ε) := by
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v.1 v.2.2
  have hθ1 := (toDiagram D x M hε).crossingParam_lt_one v.1 v.2.2
  have horig : M.orig v.2.val = tS D x := by unfold SpliceModel.orig; rw [hk]; rfl
  rw [key_of_comp_s D x _ (by rw [compOf_origVisit, horig]; exact h.symm), visitCoord_origVisit,
    visitCoord_xv, horig, hk]
  show Diagram.cyclicOffset (kI D x) (((aS D x).val : ℝ) + τs D x)
    (((bT D x).val : ℝ) + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (τt D x - ε)) = _
  rw [← val_aS_add_dd D x h,
    cyclicOffset_val_add _ _ (by have := two_le_dd D x h; omega) (by have := dd_add_two_le D x h; omega)
      ⟨τs_pos D x, τs_lt_one D x⟩ ⟨by nlinarith [hε.pos, hε.lt_τt],
        by nlinarith [hε.pos, hε.lt_τt, τt_lt_one D x, hθ0, hθ1]⟩]
  ring

theorem key_origVisit_cutEndT_self (h : (sS D x).1 = (tS D x).1) (v : Γ₀.Visit)
    (hk : M.kind v.2.val = StrandKind.cutEndT) :
    key D x (origVisit D x M hε v) =
      (dd D x : ℝ) - τs D x + τt D x + ε +
        (toDiagram D x M hε).crossingParam v.1 v.2.2 * (1 - τt D x - ε) := by
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v.1 v.2.2
  have hθ1 := (toDiagram D x M hε).crossingParam_lt_one v.1 v.2.2
  have horig : M.orig v.2.val = tS D x := by unfold SpliceModel.orig; rw [hk]; rfl
  rw [key_of_comp_s D x _ (by rw [compOf_origVisit, horig]; exact h.symm), visitCoord_origVisit,
    visitCoord_xv, horig, hk]
  show Diagram.cyclicOffset (kI D x) (((aS D x).val : ℝ) + τs D x)
    (((bT D x).val : ℝ) + (τt D x + ε + (toDiagram D x M hε).crossingParam v.1 v.2.2 * (1 - τt D x - ε))) = _
  rw [← val_aS_add_dd D x h,
    cyclicOffset_val_add _ _ (by have := two_le_dd D x h; omega) (by have := dd_add_two_le D x h; omega)
      ⟨τs_pos D x, τs_lt_one D x⟩
      ⟨by nlinarith [hε.pos, hε.lt_one_sub_τt, τt_pos D x],
        by nlinarith [hε.pos, hε.lt_one_sub_τt, hθ0, hθ1]⟩]
  ring

/-- On an untouched component the smoothed coordinate is the plain traversal coordinate of the
same label and parameter. -/
theorem key_origVisit_old_other (v : Γ₀.Visit) (i₀ : Fin D.Γ.c) (hi : i₀ ≠ (sS D x).1)
    (hj : i₀ ≠ (tS D x).1) (m : ℕ) (hm : m < (D.Γ.comp i₀).k)
    (hk : M.kind v.2.val = StrandKind.old ⟨i₀, (m : ZMod (D.Γ.comp i₀).k)⟩) :
    key D x (origVisit D x M hε v) = (m : ℝ) + (toDiagram D x M hε).crossingParam v.1 v.2.2 := by
  have horig : M.orig v.2.val = ⟨i₀, (m : ZMod (D.Γ.comp i₀).k)⟩ := by
    unfold SpliceModel.orig; rw [hk]; rfl
  rw [key_of_comp_other D x _ (by rw [compOf_origVisit, horig]; exact hi)
    (by rw [compOf_origVisit, horig]; exact hj), visitCoord_origVisit, horig, hk]
  show (((m : ZMod (D.Γ.comp i₀).k)).val : ℝ) + (toDiagram D x M hε).crossingParam v.1 v.2.2 = _
  rw [ZMod.val_cast_of_lt hm]

end KeyHelpers

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

/-- Block data of the rotated coordinate on the merged component (docstring of `mixed_key_lt_iff`),
in rotated-label order: cutEndS, old `i`-edges, cutStartS, cutEndT, old `j`-edges, cutStartT.
Lower and upper bounds of the rotated coordinate on each block. -/
def mixedLo : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => kI D x
  | 3 => kI D x + 2
  | 4 => kI D x + 3
  | 5 => kI D x + kJ D x + 2
  | _ + 6 => 0

def mixedHi : ℕ → ℝ
  | 0 => 1
  | 1 => kI D x
  | 2 => kI D x + 1
  | 3 => kI D x + 3
  | 4 => kI D x + kJ D x + 2
  | 5 => kI D x + kJ D x + 3
  | _ + 6 => 0

/-- Lower and upper bounds of `key` on each block. -/
def mixedFlo : ℕ → ℝ
  | 0 => ε
  | 1 => 1 - τs D x
  | 2 => kI D x - τs D x
  | 3 => kI D x + ε
  | 4 => kI D x + 1 - τt D x
  | 5 => kI D x + kJ D x - τt D x
  | _ + 6 => 0

def mixedFhi : ℕ → ℝ
  | 0 => 1 - τs D x
  | 1 => kI D x - τs D x
  | 2 => kI D x - ε
  | 3 => kI D x + 1 - τt D x
  | 4 => kI D x + kJ D x - τt D x
  | 5 => kI D x + kJ D x - ε
  | _ + 6 => 0

/-- `key` as an affine function of the rotated coordinate on each block. -/
def mixedF : ℕ → ℝ → ℝ
  | 0, r => ε + r * (1 - τs D x - ε)
  | 1, r => r - τs D x
  | 2, r => kI D x - τs D x + (r - kI D x) * (τs D x - ε)
  | 3, r => kI D x + ε + (r - kI D x - 2) * (1 - τt D x - ε)
  | 4, r => r - 2 - τt D x
  | 5, r => kI D x + kJ D x - τt D x + (r - kI D x - kJ D x - 2) * (τt D x - ε)
  | _ + 6, _ => 0

variable {ε} (hε : SmallEps D x ε) (h : (sS D x).1 ≠ (tS D x).1)

omit hε in
theorem mixedBase_mem (l : Fin ((othersM D x).card + 1)) :
    0 ≤ mixedBase D x l ∧ mixedBase D x l < (((mixedShadow D x ε).comp l).k : ℝ) := by
  rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', rfl⟩
  · show (0 : ℝ) ≤ ((kI D x + kJ D x + 3 : ℕ) : ℝ) ∧
      ((kI D x + kJ D x + 3 : ℕ) : ℝ) < ((kI D x + kJ D x + 4 : ℕ) : ℝ)
    exact ⟨by positivity, by exact_mod_cast (by omega : kI D x + kJ D x + 3 < kI D x + kJ D x + 4)⟩
  · show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < ((D.Γ.comp ((othersM D x).orderEmbOfFin rfl l')).k : ℝ)
    refine ⟨le_rfl, ?_⟩
    have := (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l')).hk
    exact_mod_cast (by omega : 0 < (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l')).k)

include h in
theorem mixedCls_bijective : Function.Bijective (mixedCls D x) := by
  have hmixed : ¬ D.record.IsSelfCrossing (xv D x) := h
  constructor
  · intro l l' hll'
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l₀, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ l' with rfl | ⟨l₀', rfl⟩
    · rfl
    · exfalso
      have := oldCls_eq_inl_imp D x _ (orderEmbOfFin_othersM_ne D x l₀').1
        (orderEmbOfFin_othersM_ne D x l₀').2 (xv D x) hll'.symm
      exact (orderEmbOfFin_othersM_ne D x l₀').1 this.symm
    · exfalso
      have := oldCls_eq_inl_imp D x _ (orderEmbOfFin_othersM_ne D x l₀).1
        (orderEmbOfFin_othersM_ne D x l₀).2 (xv D x) hll'
      exact (orderEmbOfFin_othersM_ne D x l₀).1 this.symm
    · have := oldCls_injOn D x _ _ (orderEmbOfFin_othersM_ne D x l₀).1
        (orderEmbOfFin_othersM_ne D x l₀).2 (orderEmbOfFin_othersM_ne D x l₀').1
        (orderEmbOfFin_othersM_ne D x l₀').2 hll'
      rw [((othersM D x).orderEmbOfFin rfl).injective this]
  · intro c
    rcases c with q | ⟨c, hc⟩
    · induction q using Quotient.inductionOn with
      | h w =>
        by_cases hw : D.compOf w = (sS D x).1 ∨ D.compOf w = (tS D x).1
        · refine ⟨0, ?_⟩
          show Sum.inl (Quotient.mk _ (xv D x)) = Sum.inl (Quotient.mk _ w)
          apply congrArg Sum.inl
          apply Quotient.sound
          exact (D.record.reconnect_sameCycle_of_mixed (xv D x) hmixed w hw).symm
        · obtain ⟨hw1, hw2⟩ := not_or.mp hw
          obtain ⟨l, hl⟩ := othersM_exists_emb D x ((mem_othersM D x).mpr ⟨hw2, hw1⟩)
          refine ⟨l.succ, ?_⟩
          show oldCls D x ((othersM D x).orderEmbOfFin rfl l) = Sum.inl (Quotient.mk _ w)
          exact oldCls_eq D x _ (hl ▸ hw1) (hl ▸ hw2) w hl.symm
    · have hc1 : c ≠ (sS D x).1 := fun e => hc (xv D x) e.symm
      have hc2 : c ≠ (tS D x).1 := fun e => hc (D.underVisit x) e.symm
      obtain ⟨l, hl⟩ := othersM_exists_emb D x ((mem_othersM D x).mpr ⟨hc2, hc1⟩)
      refine ⟨l.succ, ?_⟩
      show oldCls D x ((othersM D x).orderEmbOfFin rfl l) = Sum.inr ⟨c, hc⟩
      subst hl
      exact oldCls_eq_inr D x _ (fun ⟨w, hw⟩ => hc w hw)

theorem mixedCls_visit (v : (mixedShadow D x ε).Visit) :
    mixedCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp
      ⟨origVisit D x (mixedModel D x ε h) hε v, smoothKeep_origVisit D x (mixedModel D x ε h) hε v⟩ := by
  have hmixed : ¬ D.record.IsSelfCrossing (xv D x) := h
  obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
  rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l₀, rfl⟩
  · show Sum.inl (Quotient.mk _ (xv D x)) =
      Sum.inl (Quotient.mk _ (origVisit D x (mixedModel D x ε h) hε
        ⟨y, ⟨⟨(0 : Fin ((othersM D x).card + 1)), m⟩, hm⟩⟩))
    apply congrArg Sum.inl
    apply Quotient.sound
    refine (D.record.reconnect_sameCycle_of_mixed (xv D x) hmixed _ ?_).symm
    show ((mergedKindIdx D x m.val).orig).1 = (sS D x).1 ∨ ((mergedKindIdx D x m.val).orig).1 = (tS D x).1
    unfold mergedKindIdx
    split_ifs <;> simp [StrandKind.orig]
  · show oldCls D x ((othersM D x).orderEmbOfFin rfl l₀) = _
    exact oldCls_eq D x _ (orderEmbOfFin_othersM_ne D x l₀).1 (orderEmbOfFin_othersM_ne D x l₀).2 _ rfl

include hε in
theorem mixed_blocks_lohi : ∀ i, i < 6 → mixedLo D x i ≤ mixedHi D x i ∧ mixedFlo D x ε i ≤ mixedFhi D x ε i := by
  have hkI : (3 : ℝ) ≤ kI D x := by exact_mod_cast (D.Γ.comp (sS D x).1).hk
  have hkJ : (3 : ℝ) ≤ kJ D x := by exact_mod_cast (D.Γ.comp (tS D x).1).hk
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi
  interval_cases i <;> simp only [mixedLo, mixedHi, mixedFlo, mixedFhi] <;> constructor <;> linarith

include hε in
theorem mixed_blocks_chain : ∀ i, i + 1 < 6 →
    mixedHi D x i ≤ mixedLo D x (i + 1) ∧ mixedFhi D x ε i ≤ mixedFlo D x ε (i + 1) := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi
  have hi' : i < 5 := by omega
  interval_cases i <;> simp only [mixedLo, mixedHi, mixedFlo, mixedFhi] <;> constructor <;> linarith

include hε in
theorem mixed_blocks_mono : ∀ i, i < 6 → ∀ r r', mixedLo D x i ≤ r → r < mixedHi D x i →
    mixedLo D x i ≤ r' → r' < mixedHi D x i → (r < r' ↔ mixedF D x ε i r < mixedF D x ε i r') := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi r r' _ _ _ _
  interval_cases i <;> simp only [mixedF] <;> constructor <;> intro hh <;> nlinarith

include hε in
theorem mixed_blocks_range : ∀ i, i < 6 → ∀ r, mixedLo D x i ≤ r → r < mixedHi D x i →
    mixedFlo D x ε i ≤ mixedF D x ε i r ∧ mixedF D x ε i r < mixedFhi D x ε i := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi r hr1 hr2
  interval_cases i <;> simp only [mixedLo, mixedHi, mixedFlo, mixedFhi, mixedF] at hr1 hr2 ⊢ <;>
    constructor <;> nlinarith

include hε h in
/-- Every occurrence of the merged component lies in one of the six blocks, where `key ∘ origVisit`
is the corresponding affine function of the rotated coordinate. -/
theorem mixed_block (v : (mixedShadow D x ε).Visit) (hv : v.2.val.1 = (0 : Fin ((othersM D x).card + 1))) :
    ∃ i, i < 6 ∧
      (mixedLo D x i ≤ rexB_rot (kI D x + kJ D x + 4) (kI D x + kJ D x + 3)
          ((toDiagram D x (mixedModel D x ε h) hε).visitCoord v) ∧
        rexB_rot (kI D x + kJ D x + 4) (kI D x + kJ D x + 3)
          ((toDiagram D x (mixedModel D x ε h) hε).visitCoord v) < mixedHi D x i) ∧
      key D x (origVisit D x (mixedModel D x ε h) hε v) =
        mixedF D x ε i (rexB_rot (kI D x + kJ D x + 4) (kI D x + kJ D x + 3)
          ((toDiagram D x (mixedModel D x ε h) hε).visitCoord v)) := by
  obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
  change l = (0 : Fin ((othersM D x).card + 1)) at hv
  subst hv
  set M := mixedModel D x ε h with hM
  set v0 : (mixedShadow D x ε).Visit := ⟨y, ⟨⟨(0 : Fin ((othersM D x).card + 1)), m⟩, hm⟩⟩ with hv0
  set θ := (toDiagram D x M hε).crossingParam v0.1 v0.2.2 with hθ
  have hθ0 : 0 < θ := (toDiagram D x M hε).crossingParam_pos v0.1 v0.2.2
  have hθ1 : θ < 1 := (toDiagram D x M hε).crossingParam_lt_one v0.1 v0.2.2
  have hcoord : (toDiagram D x M hε).visitCoord v0 = (m.val : ℝ) + θ := rfl
  have hmlt : m.val < kI D x + kJ D x + 4 := ZMod.val_lt m
  have hk : M.kind v0.2.val = mergedKindIdx D x m.val := rfl
  have hkI0 : 3 ≤ kI D x := (D.Γ.comp (sS D x).1).hk
  have hkJ0 : 3 ≤ kJ D x := (D.Γ.comp (tS D x).1).hk
  have hkI : (3 : ℝ) ≤ kI D x := by exact_mod_cast hkI0
  have hkJ : (3 : ℝ) ≤ kJ D x := by exact_mod_cast hkJ0
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  have := τs_pos D x; have := τs_lt_one D x; have := τt_pos D x; have := τt_lt_one D x
  rw [hcoord]
  have hrot1 : m.val ≤ kI D x + kJ D x + 2 →
      rexB_rot (kI D x + kJ D x + 4) (kI D x + kJ D x + 3) ((m.val : ℝ) + θ) = (m.val : ℝ) + θ + 1 := by
    intro hle
    have : (m.val : ℝ) ≤ kI D x + kJ D x + 2 := by exact_mod_cast hle
    rw [rexB_rot_of_lt (by linarith)]; ring
  unfold mergedKindIdx at hk
  split_ifs at hk with h1 h2 h3 h4 h5 h6 h7
  · -- old `i`-edge
    have hm1 : m.val + 1 < kI D x := by omega
    have hm2 : (m.val : ℝ) + 2 ≤ kI D x := by exact_mod_cast (by omega : m.val + 2 ≤ kI D x)
    refine ⟨1, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [mixedLo, mixedHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_old_s D x M hε v0 m.val hm1 hk]; simp only [mixedF]; ring
  · -- cutStartS
    have hm1 : (m.val : ℝ) + 1 = kI D x := by exact_mod_cast (by omega : m.val + 1 = kI D x)
    refine ⟨2, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [mixedLo, mixedHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_cutStartS D x M hε v0 hk]; simp only [mixedF]
      rw [← hm1]; ring
  · exact absurd hk (kind_visit_ne_arcST D x M hε v0)
  · -- cutEndT
    have hm1 : (m.val : ℝ) = kI D x + 1 := by exact_mod_cast h4
    refine ⟨3, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [mixedLo, mixedHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_cutEndT_mixed D x M hε h v0 hk]; simp only [mixedF]
      rw [hm1]; ring
  · -- old `j`-edge
    have hge : kI D x + 2 ≤ m.val := by omega
    have hn : m.val - (kI D x + 2) + 1 < kJ D x := by omega
    have hcast : ((m.val - (kI D x + 2) : ℕ) : ℝ) = m.val - kI D x - 2 := by
      rw [Nat.cast_sub hge]; push_cast; ring
    have hge' : (kI D x : ℝ) + 2 ≤ m.val := by exact_mod_cast hge
    have hlt' : (m.val : ℝ) ≤ kI D x + kJ D x := by exact_mod_cast (by omega : m.val ≤ kI D x + kJ D x)
    refine ⟨4, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [mixedLo, mixedHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_old_t_mixed D x M hε h v0 _ hn hk, hcast]
      simp only [mixedF]; ring
  · -- cutStartT
    have hm1 : (m.val : ℝ) = kI D x + 1 + kJ D x := by exact_mod_cast h6
    refine ⟨5, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [mixedLo, mixedHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_cutStartT_mixed D x M hε h v0 hk]; simp only [mixedF]
      rw [hm1]; ring
  · exact absurd hk (kind_visit_ne_arcTS D x M hε v0)
  · -- cutEndS at the last label `N − 1`
    have hm1 : (m.val : ℝ) = kI D x + kJ D x + 3 := by
      exact_mod_cast (by omega : m.val = kI D x + kJ D x + 3)
    have hrot : rexB_rot (kI D x + kJ D x + 4) (kI D x + kJ D x + 3) ((m.val : ℝ) + θ) = θ := by
      rw [rexB_rot_of_le (by linarith)]; linarith
    refine ⟨0, by norm_num, ?_, ?_⟩
    · rw [hrot]; simp only [mixedLo, mixedHi]; constructor <;> linarith
    · rw [hrot, key_origVisit_cutEndS D x M hε v0 hk]; simp only [mixedF]; rfl

include hε h in
/-- On an untouched component the rotated coordinate (base `0`) is `key ∘ origVisit` itself. -/
theorem mixed_rot_eq_key (v : (mixedShadow D x ε).Visit) (l₀ : Fin (othersM D x).card)
    (hv : v.2.val.1 = l₀.succ) :
    rexB_rot (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) 0
        ((toDiagram D x (mixedModel D x ε h) hε).visitCoord v) =
      key D x (origVisit D x (mixedModel D x ε h) hε v) := by
  obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
  change l = l₀.succ at hv
  subst hv
  set M := mixedModel D x ε h with hM
  set v0 : (mixedShadow D x ε).Visit := ⟨y, ⟨⟨l₀.succ, m⟩, hm⟩⟩ with hv0
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v0.1 v0.2.2
  have hcoord : (toDiagram D x M hε).visitCoord v0 =
      (m.val : ℝ) + (toDiagram D x M hε).crossingParam v0.1 v0.2.2 := rfl
  have hk : M.kind v0.2.val =
      StrandKind.old ⟨(othersM D x).orderEmbOfFin rfl l₀, (m.val : ZMod _)⟩ := rfl
  have hkey := key_origVisit_old_other D x M hε v0 _ (orderEmbOfFin_othersM_ne D x l₀).1
    (orderEmbOfFin_othersM_ne D x l₀).2 m.val (ZMod.val_lt m) hk
  rw [hkey, hcoord, rexB_rot_of_le (by positivity)]
  ring

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
  change v.2.val.1 = w.2.val.1 at hc
  rcases Fin.eq_zero_or_eq_succ v.2.val.1 with hv | ⟨l₀, hv⟩
  · have hw : w.2.val.1 = (0 : Fin ((othersM D x).card + 1)) := by rw [← hc]; exact hv
    obtain ⟨i, hi, hr, hk⟩ := mixed_block D x hε h v hv
    obtain ⟨j, hj, hr', hk'⟩ := mixed_block D x hε h w hw
    have hN : (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) = kI D x + kJ D x + 4 := by
      rw [hv]; show ((kI D x + kJ D x + 4 : ℕ) : ℝ) = _; push_cast; ring
    have hb : mixedBase D x v.2.val.1 = kI D x + kJ D x + 3 := by
      rw [hv]; show ((kI D x + kJ D x + 3 : ℕ) : ℝ) = _; push_cast; ring
    rw [hN, hb, hk, hk']
    exact lt_iff_of_blocks 6 _ _ _ _ _ (mixed_blocks_lohi D x hε) (mixed_blocks_chain D x hε)
      (mixed_blocks_mono D x hε) (mixed_blocks_range D x hε) hi hj hr hr'
  · have hw : w.2.val.1 = l₀.succ := by rw [← hc]; exact hv
    have hb : mixedBase D x v.2.val.1 = 0 := by rw [hv]; rfl
    have hN : (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) = (((mixedShadow D x ε).comp w.2.val.1).k : ℝ) := by
      rw [hc]
    rw [hb, mixed_rot_eq_key D x hε h v l₀ hv, hN, mixed_rot_eq_key D x hε h w l₀ hw]

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

/-- Block data of the rotated coordinate on component `A` (docstring of `self_key_lt_iff`), in
rotated-label order: cutEndS, old edges, cutStartT. -/
def selfALo : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => dd D x
  | _ + 3 => 0

def selfAHi : ℕ → ℝ
  | 0 => 1
  | 1 => dd D x
  | 2 => dd D x + 1
  | _ + 3 => 0

def selfAFlo : ℕ → ℝ
  | 0 => ε
  | 1 => 1 - τs D x
  | 2 => dd D x - τs D x
  | _ + 3 => 0

def selfAFhi : ℕ → ℝ
  | 0 => 1 - τs D x
  | 1 => dd D x - τs D x
  | 2 => dd D x - τs D x + τt D x - ε
  | _ + 3 => 0

def selfAF : ℕ → ℝ → ℝ
  | 0, r => ε + r * (1 - τs D x - ε)
  | 1, r => r - τs D x
  | 2, r => dd D x - τs D x + (r - dd D x) * (τt D x - ε)
  | _ + 3, _ => 0

/-- Block data on component `B`, in rotated-label order: cutEndT, old edges, cutStartS. -/
def selfBLo : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => kI D x - dd D x
  | _ + 3 => 0

def selfBHi : ℕ → ℝ
  | 0 => 1
  | 1 => kI D x - dd D x
  | 2 => kI D x - dd D x + 1
  | _ + 3 => 0

def selfBFlo : ℕ → ℝ
  | 0 => dd D x - τs D x + τt D x + ε
  | 1 => dd D x + 1 - τs D x
  | 2 => kI D x - τs D x
  | _ + 3 => 0

def selfBFhi : ℕ → ℝ
  | 0 => dd D x + 1 - τs D x
  | 1 => kI D x - τs D x
  | 2 => kI D x - ε
  | _ + 3 => 0

def selfBF : ℕ → ℝ → ℝ
  | 0, r => dd D x - τs D x + τt D x + ε + r * (1 - τt D x - ε)
  | 1, r => r + dd D x - τs D x
  | 2, r => kI D x - τs D x + (r - (kI D x - dd D x)) * (τs D x - ε)
  | _ + 3, _ => 0

variable {ε} (hε : SmallEps D x ε) (h : (sS D x).1 = (tS D x).1)

omit hε in
theorem selfBase_mem (l : Fin ((othersS D x).card + 2)) :
    0 ≤ selfBase D x l ∧ selfBase D x l < (((selfShadow D x ε h).comp l).k : ℝ) := by
  rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l₁, rfl⟩
  · show (0 : ℝ) ≤ ((dd D x + 1 : ℕ) : ℝ) ∧ ((dd D x + 1 : ℕ) : ℝ) < ((dd D x + 2 : ℕ) : ℝ)
    exact ⟨by positivity, by exact_mod_cast (by omega : dd D x + 1 < dd D x + 2)⟩
  · rcases Fin.eq_zero_or_eq_succ l₁ with rfl | ⟨l₀, rfl⟩
    · show (0 : ℝ) ≤ ((kI D x - dd D x + 1 : ℕ) : ℝ) ∧
        ((kI D x - dd D x + 1 : ℕ) : ℝ) < ((kI D x - dd D x + 2 : ℕ) : ℝ)
      exact ⟨by positivity, by exact_mod_cast (by omega : kI D x - dd D x + 1 < kI D x - dd D x + 2)⟩
    · show (0 : ℝ) ≤ 0 ∧ (0 : ℝ) < ((D.Γ.comp ((othersS D x).orderEmbOfFin rfl l₀)).k : ℝ)
      refine ⟨le_rfl, ?_⟩
      have := (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l₀)).hk
      exact_mod_cast (by omega : 0 < (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l₀)).k)

include h in
theorem selfCls_bijective : Function.Bijective (selfCls D x) := by
  have hself : D.record.IsSelfCrossing (xv D x) := h
  have hne := D.record.smooth_comps_ne_of_self (xv D x) hself
  have hemb : ∀ l : Fin (othersS D x).card,
      (othersS D x).orderEmbOfFin rfl l ≠ (sS D x).1 ∧ (othersS D x).orderEmbOfFin rfl l ≠ (tS D x).1 :=
    fun l => ⟨orderEmbOfFin_othersS_ne D x l, fun e => orderEmbOfFin_othersS_ne D x l (e.trans h.symm)⟩
  constructor
  · intro l l' hll'
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l₁, rfl⟩ <;>
      rcases Fin.eq_zero_or_eq_succ l' with rfl | ⟨l₁', rfl⟩
    · rfl
    · rcases Fin.eq_zero_or_eq_succ l₁' with rfl | ⟨l₀', rfl⟩
      · exact absurd hll' hne.symm
      · exfalso
        have := oldCls_eq_inl_imp D x _ (hemb l₀').1 (hemb l₀').2 (D.underVisit x) hll'.symm
        exact (hemb l₀').2 this.symm
    · rcases Fin.eq_zero_or_eq_succ l₁ with rfl | ⟨l₀, rfl⟩
      · exact absurd hll' hne
      · exfalso
        have := oldCls_eq_inl_imp D x _ (hemb l₀).1 (hemb l₀).2 (D.underVisit x) hll'
        exact (hemb l₀).2 this.symm
    · rcases Fin.eq_zero_or_eq_succ l₁ with rfl | ⟨l₀, rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ l₁' with rfl | ⟨l₀', rfl⟩
      · rfl
      · exfalso
        have := oldCls_eq_inl_imp D x _ (hemb l₀').1 (hemb l₀').2 (xv D x) hll'.symm
        exact (hemb l₀').1 this.symm
      · exfalso
        have := oldCls_eq_inl_imp D x _ (hemb l₀).1 (hemb l₀).2 (xv D x) hll'
        exact (hemb l₀).1 this.symm
      · have := oldCls_injOn D x _ _ (hemb l₀).1 (hemb l₀).2 (hemb l₀').1 (hemb l₀').2 hll'
        rw [((othersS D x).orderEmbOfFin rfl).injective this]
  · intro c
    rcases c with q | ⟨c, hc⟩
    · induction q using Quotient.inductionOn with
      | h w =>
        by_cases hw : D.compOf w = (sS D x).1
        · rcases D.record.reconnect_sameCycle_or (xv D x) w hw with h1 | h1
          · refine ⟨1, ?_⟩
            show Sum.inl (Quotient.mk _ (xv D x)) = Sum.inl (Quotient.mk _ w)
            apply congrArg Sum.inl
            apply Quotient.sound
            exact h1.symm
          · refine ⟨0, ?_⟩
            show Sum.inl (Quotient.mk _ (D.underVisit x)) = Sum.inl (Quotient.mk _ w)
            apply congrArg Sum.inl
            apply Quotient.sound
            exact h1.symm
        · obtain ⟨l, hl⟩ := othersS_exists_emb D x ((mem_othersS D x).mpr hw)
          refine ⟨l.succ.succ, ?_⟩
          show oldCls D x ((othersS D x).orderEmbOfFin rfl l) = Sum.inl (Quotient.mk _ w)
          exact oldCls_eq D x _ (hl ▸ hw) (hl ▸ fun e => hw (e.trans h.symm)) w hl.symm
    · have hc1 : c ≠ (sS D x).1 := fun e => hc (xv D x) e.symm
      obtain ⟨l, hl⟩ := othersS_exists_emb D x ((mem_othersS D x).mpr hc1)
      refine ⟨l.succ.succ, ?_⟩
      show oldCls D x ((othersS D x).orderEmbOfFin rfl l) = Sum.inr ⟨c, hc⟩
      subst hl
      exact oldCls_eq_inr D x _ (fun ⟨w, hw⟩ => hc w hw)

include hε h in
theorem selfA_blocks_lohi : ∀ i, i < 3 → selfALo D x i ≤ selfAHi D x i ∧ selfAFlo D x ε i ≤ selfAFhi D x ε i := by
  have hd : (2 : ℝ) ≤ dd D x := by exact_mod_cast two_le_dd D x h
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi
  interval_cases i <;> simp only [selfALo, selfAHi, selfAFlo, selfAFhi] <;> constructor <;> linarith

include hε h in
theorem selfA_blocks_chain : ∀ i, i + 1 < 3 →
    selfAHi D x i ≤ selfALo D x (i + 1) ∧ selfAFhi D x ε i ≤ selfAFlo D x ε (i + 1) := by
  have hd : (2 : ℝ) ≤ dd D x := by exact_mod_cast two_le_dd D x h
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi
  have hi' : i < 2 := by omega
  interval_cases i <;> simp only [selfALo, selfAHi, selfAFlo, selfAFhi] <;> constructor <;> linarith

include hε in
theorem selfA_blocks_mono : ∀ i, i < 3 → ∀ r r', selfALo D x i ≤ r → r < selfAHi D x i →
    selfALo D x i ≤ r' → r' < selfAHi D x i → (r < r' ↔ selfAF D x ε i r < selfAF D x ε i r') := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi r r' _ _ _ _
  interval_cases i <;> simp only [selfAF] <;> constructor <;> intro hh <;> nlinarith

include hε in
theorem selfA_blocks_range : ∀ i, i < 3 → ∀ r, selfALo D x i ≤ r → r < selfAHi D x i →
    selfAFlo D x ε i ≤ selfAF D x ε i r ∧ selfAF D x ε i r < selfAFhi D x ε i := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi r hr1 hr2
  interval_cases i <;> simp only [selfALo, selfAHi, selfAFlo, selfAFhi, selfAF] at hr1 hr2 ⊢ <;>
    constructor <;> nlinarith

include hε h in
theorem selfB_blocks_lohi : ∀ i, i < 3 → selfBLo D x i ≤ selfBHi D x i ∧ selfBFlo D x ε i ≤ selfBFhi D x ε i := by
  have hd : (2 : ℝ) ≤ dd D x := by exact_mod_cast two_le_dd D x h
  have hdk : (dd D x : ℝ) + 2 ≤ kI D x := by exact_mod_cast dd_add_two_le D x h
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi
  interval_cases i <;> simp only [selfBLo, selfBHi, selfBFlo, selfBFhi] <;> constructor <;> linarith

include hε h in
theorem selfB_blocks_chain : ∀ i, i + 1 < 3 →
    selfBHi D x i ≤ selfBLo D x (i + 1) ∧ selfBFhi D x ε i ≤ selfBFlo D x ε (i + 1) := by
  have hd : (2 : ℝ) ≤ dd D x := by exact_mod_cast two_le_dd D x h
  have hdk : (dd D x : ℝ) + 2 ≤ kI D x := by exact_mod_cast dd_add_two_le D x h
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi
  have hi' : i < 2 := by omega
  interval_cases i <;> simp only [selfBLo, selfBHi, selfBFlo, selfBFhi] <;> constructor <;> linarith

include hε in
theorem selfB_blocks_mono : ∀ i, i < 3 → ∀ r r', selfBLo D x i ≤ r → r < selfBHi D x i →
    selfBLo D x i ≤ r' → r' < selfBHi D x i → (r < r' ↔ selfBF D x ε i r < selfBF D x ε i r') := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi r r' _ _ _ _
  interval_cases i <;> simp only [selfBF] <;> constructor <;> intro hh <;> nlinarith

include hε in
theorem selfB_blocks_range : ∀ i, i < 3 → ∀ r, selfBLo D x i ≤ r → r < selfBHi D x i →
    selfBFlo D x ε i ≤ selfBF D x ε i r ∧ selfBF D x ε i r < selfBFhi D x ε i := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  intro i hi r hr1 hr2
  interval_cases i <;> simp only [selfBLo, selfBHi, selfBFlo, selfBFhi, selfBF] at hr1 hr2 ⊢ <;>
    constructor <;> nlinarith

include hε h in
/-- Every occurrence of component `A` lies in one of its three blocks. -/
theorem selfA_block (v : (selfShadow D x ε h).Visit) (hv : v.2.val.1 = (0 : Fin ((othersS D x).card + 2))) :
    ∃ i, i < 3 ∧
      (selfALo D x i ≤ rexB_rot (dd D x + 2) (dd D x + 1)
          ((toDiagram D x (selfModel D x ε h) hε).visitCoord v) ∧
        rexB_rot (dd D x + 2) (dd D x + 1)
          ((toDiagram D x (selfModel D x ε h) hε).visitCoord v) < selfAHi D x i) ∧
      key D x (origVisit D x (selfModel D x ε h) hε v) =
        selfAF D x ε i (rexB_rot (dd D x + 2) (dd D x + 1)
          ((toDiagram D x (selfModel D x ε h) hε).visitCoord v)) := by
  obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
  change l = (0 : Fin ((othersS D x).card + 2)) at hv
  subst hv
  set M := selfModel D x ε h with hM
  set v0 : (selfShadow D x ε h).Visit := ⟨y, ⟨⟨(0 : Fin ((othersS D x).card + 2)), m⟩, hm⟩⟩ with hv0
  set θ := (toDiagram D x M hε).crossingParam v0.1 v0.2.2 with hθ
  have hθ0 : 0 < θ := (toDiagram D x M hε).crossingParam_pos v0.1 v0.2.2
  have hθ1 : θ < 1 := (toDiagram D x M hε).crossingParam_lt_one v0.1 v0.2.2
  have hcoord : (toDiagram D x M hε).visitCoord v0 = (m.val : ℝ) + θ := rfl
  have hmlt : m.val < dd D x + 2 := ZMod.val_lt m
  have hk : M.kind v0.2.val = kindIdxA D x m.val := rfl
  have hd2 := two_le_dd D x h
  have hdk := dd_add_two_le D x h
  have hd : (2 : ℝ) ≤ dd D x := by exact_mod_cast hd2
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  have := τs_pos D x; have := τs_lt_one D x; have := τt_pos D x; have := τt_lt_one D x
  rw [hcoord]
  have hrot1 : m.val ≤ dd D x →
      rexB_rot (dd D x + 2) (dd D x + 1) ((m.val : ℝ) + θ) = (m.val : ℝ) + θ + 1 := by
    intro hle
    have : (m.val : ℝ) ≤ dd D x := by exact_mod_cast hle
    rw [rexB_rot_of_lt (by linarith)]; ring
  unfold kindIdxA at hk
  split_ifs at hk with h1 h2 h3
  · -- old edge
    have hm1 : m.val + 1 < kI D x := by omega
    have hm2 : (m.val : ℝ) + 2 ≤ dd D x := by exact_mod_cast (by omega : m.val + 2 ≤ dd D x)
    refine ⟨1, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [selfALo, selfAHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_old_s D x M hε v0 m.val hm1 hk]; simp only [selfAF]; ring
  · -- cutStartT
    have hm1 : (m.val : ℝ) + 1 = dd D x := by exact_mod_cast (by omega : m.val + 1 = dd D x)
    refine ⟨2, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [selfALo, selfAHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_cutStartT_self D x M hε h v0 hk]; simp only [selfAF]
      rw [← hm1]; ring
  · exact absurd hk (kind_visit_ne_arcTS D x M hε v0)
  · -- cutEndS at the last label `d + 1`
    have hm1 : (m.val : ℝ) = dd D x + 1 := by exact_mod_cast (by omega : m.val = dd D x + 1)
    have hrot : rexB_rot (dd D x + 2) (dd D x + 1) ((m.val : ℝ) + θ) = θ := by
      rw [rexB_rot_of_le (by linarith)]; linarith
    refine ⟨0, by norm_num, ?_, ?_⟩
    · rw [hrot]; simp only [selfALo, selfAHi]; constructor <;> linarith
    · rw [hrot, key_origVisit_cutEndS D x M hε v0 hk]; simp only [selfAF]; rfl

include hε h in
/-- Every occurrence of component `B` lies in one of its three blocks. -/
theorem selfB_block (v : (selfShadow D x ε h).Visit) (hv : v.2.val.1 = (1 : Fin ((othersS D x).card + 2))) :
    ∃ i, i < 3 ∧
      (selfBLo D x i ≤ rexB_rot (kI D x - dd D x + 2) (kI D x - dd D x + 1)
          ((toDiagram D x (selfModel D x ε h) hε).visitCoord v) ∧
        rexB_rot (kI D x - dd D x + 2) (kI D x - dd D x + 1)
          ((toDiagram D x (selfModel D x ε h) hε).visitCoord v) < selfBHi D x i) ∧
      key D x (origVisit D x (selfModel D x ε h) hε v) =
        selfBF D x ε i (rexB_rot (kI D x - dd D x + 2) (kI D x - dd D x + 1)
          ((toDiagram D x (selfModel D x ε h) hε).visitCoord v)) := by
  obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
  change l = (1 : Fin ((othersS D x).card + 2)) at hv
  subst hv
  set M := selfModel D x ε h with hM
  set v0 : (selfShadow D x ε h).Visit := ⟨y, ⟨⟨(1 : Fin ((othersS D x).card + 2)), m⟩, hm⟩⟩ with hv0
  set θ := (toDiagram D x M hε).crossingParam v0.1 v0.2.2 with hθ
  have hθ0 : 0 < θ := (toDiagram D x M hε).crossingParam_pos v0.1 v0.2.2
  have hθ1 : θ < 1 := (toDiagram D x M hε).crossingParam_lt_one v0.1 v0.2.2
  have hcoord : (toDiagram D x M hε).visitCoord v0 = (m.val : ℝ) + θ := rfl
  have hmlt : m.val < kI D x - dd D x + 2 := ZMod.val_lt m
  have hk : M.kind v0.2.val = kindIdxB D x m.val := rfl
  have hd2 := two_le_dd D x h
  have hdk := dd_add_two_le D x h
  have hd : (2 : ℝ) ≤ dd D x := by exact_mod_cast hd2
  have hdk' : (dd D x : ℝ) + 2 ≤ kI D x := by exact_mod_cast hdk
  have hsub : ((kI D x - dd D x : ℕ) : ℝ) = kI D x - dd D x := by
    rw [Nat.cast_sub (by omega)]
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  have := τs_pos D x; have := τs_lt_one D x; have := τt_pos D x; have := τt_lt_one D x
  rw [hcoord]
  have hrot1 : m.val ≤ kI D x - dd D x →
      rexB_rot (kI D x - dd D x + 2) (kI D x - dd D x + 1) ((m.val : ℝ) + θ) = (m.val : ℝ) + θ + 1 := by
    intro hle
    have : (m.val : ℝ) ≤ ((kI D x - dd D x : ℕ) : ℝ) := by exact_mod_cast hle
    rw [hsub] at this
    rw [rexB_rot_of_lt (by linarith)]; ring
  unfold kindIdxB at hk
  split_ifs at hk with h1 h2 h3
  · -- old edge `⟨i, b + 1 + m⟩ = ⟨i, a + 1 + (d + m)⟩`
    have hk' : M.kind v0.2.val =
        StrandKind.old ⟨(sS D x).1, aS D x + 1 + ((dd D x + m.val : ℕ) : ZMod (kI D x))⟩ := by
      rw [hk]
      exact congrArg (fun z : ZMod (kI D x) => StrandKind.old (⟨(sS D x).1, z⟩ : D.Γ.Strand))
        (by rw [bS_eq]; push_cast; ring)
    have hm1 : dd D x + m.val + 1 < kI D x := by omega
    have hm2 : (m.val : ℝ) + 2 ≤ ((kI D x - dd D x : ℕ) : ℝ) := by
      exact_mod_cast (by omega : m.val + 2 ≤ kI D x - dd D x)
    rw [hsub] at hm2
    refine ⟨1, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [selfBLo, selfBHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_old_s D x M hε v0 (dd D x + m.val) hm1 hk']
      simp only [selfBF]; push_cast; ring
  · -- cutStartS
    have hm1 : (m.val : ℝ) + 1 = ((kI D x - dd D x : ℕ) : ℝ) := by
      exact_mod_cast (by omega : m.val + 1 = kI D x - dd D x)
    rw [hsub] at hm1
    refine ⟨2, by norm_num, ?_, ?_⟩
    · rw [hrot1 (by omega)]; simp only [selfBLo, selfBHi]; constructor <;> linarith
    · rw [hrot1 (by omega), key_origVisit_cutStartS D x M hε v0 hk]; simp only [selfBF]
      rw [← hm1]; ring
  · exact absurd hk (kind_visit_ne_arcST D x M hε v0)
  · -- cutEndT at the last label `k − d + 1`
    have hm1 : (m.val : ℝ) = ((kI D x - dd D x : ℕ) : ℝ) + 1 := by
      exact_mod_cast (by omega : m.val = kI D x - dd D x + 1)
    rw [hsub] at hm1
    have hrot : rexB_rot (kI D x - dd D x + 2) (kI D x - dd D x + 1) ((m.val : ℝ) + θ) = θ := by
      rw [rexB_rot_of_le (by linarith)]; linarith
    refine ⟨0, by norm_num, ?_, ?_⟩
    · rw [hrot]; simp only [selfBLo, selfBHi]; constructor <;> linarith
    · rw [hrot, key_origVisit_cutEndT_self D x M hε h v0 hk]; simp only [selfBF]; rfl

include hε h in
/-- On an untouched component the rotated coordinate (base `0`) is `key ∘ origVisit` itself. -/
theorem self_rot_eq_key (v : (selfShadow D x ε h).Visit) (l₀ : Fin (othersS D x).card)
    (hv : v.2.val.1 = l₀.succ.succ) :
    rexB_rot (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) 0
        ((toDiagram D x (selfModel D x ε h) hε).visitCoord v) =
      key D x (origVisit D x (selfModel D x ε h) hε v) := by
  obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
  change l = l₀.succ.succ at hv
  subst hv
  set M := selfModel D x ε h with hM
  set v0 : (selfShadow D x ε h).Visit := ⟨y, ⟨⟨l₀.succ.succ, m⟩, hm⟩⟩ with hv0
  have hθ0 := (toDiagram D x M hε).crossingParam_pos v0.1 v0.2.2
  have hcoord : (toDiagram D x M hε).visitCoord v0 =
      (m.val : ℝ) + (toDiagram D x M hε).crossingParam v0.1 v0.2.2 := rfl
  have hk : M.kind v0.2.val =
      StrandKind.old ⟨(othersS D x).orderEmbOfFin rfl l₀, (m.val : ZMod _)⟩ := rfl
  have hkey := key_origVisit_old_other D x M hε v0 _ (orderEmbOfFin_othersS_ne D x l₀)
    (fun e => orderEmbOfFin_othersS_ne D x l₀ (e.trans h.symm)) m.val (ZMod.val_lt m) hk
  rw [hkey, hcoord, rexB_rot_of_le (by positivity)]
  ring

/-- The component of `D` carrying an occurrence of `A` or `B` is the circle of `s`. -/
theorem compOf_origVisit_selfA (v : (selfShadow D x ε h).Visit)
    (hv : v.2.val.1 = (0 : Fin ((othersS D x).card + 2))) :
    D.compOf (origVisit D x (selfModel D x ε h) hε v) = (sS D x).1 := by
  obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
  change l = (0 : Fin ((othersS D x).card + 2)) at hv
  subst hv
  show ((kindIdxA D x m.val).orig).1 = (sS D x).1
  unfold kindIdxA
  split_ifs <;> first | rfl | exact h.symm

theorem compOf_origVisit_selfB (v : (selfShadow D x ε h).Visit)
    (hv : v.2.val.1 = (1 : Fin ((othersS D x).card + 2))) :
    D.compOf (origVisit D x (selfModel D x ε h) hε v) = (sS D x).1 := by
  obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
  change l = (1 : Fin ((othersS D x).card + 2)) at hv
  subst hv
  show ((kindIdxB D x m.val).orig).1 = (sS D x).1
  unfold kindIdxB
  split_ifs <;> first | rfl | exact h.symm

/-- `A`'s occurrences are on the `s₁`-cycle of `τ xv` and `B`'s on that of `xv`
(`self_sameCycle_pair_iff`, `reconnect_sameCycle_or`, `smooth_comps_ne_of_self`). -/
theorem selfCls_visit (v : (selfShadow D x ε h).Visit) :
    selfCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp
      ⟨origVisit D x (selfModel D x ε h) hε v, smoothKeep_origVisit D x (selfModel D x ε h) hε v⟩ := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt; have := hε.lt_one_sub_τt
  have hd : (2 : ℝ) ≤ dd D x := by exact_mod_cast two_le_dd D x h
  have hdk' : (dd D x : ℝ) + 2 ≤ kI D x := by exact_mod_cast dd_add_two_le D x h
  have := τs_pos D x; have := τs_lt_one D x; have := τt_pos D x; have := τt_lt_one D x
  rcases Fin.eq_zero_or_eq_succ v.2.val.1 with hv | ⟨l₁, hv⟩
  · -- component `A`: the class of `τ xv`
    have hcomp := compOf_origVisit_selfA D x hε h v hv
    have hcls : selfCls D x v.2.val.1 = Sum.inl (Quotient.mk _ (D.underVisit x)) := by rw [hv]; rfl
    rw [hcls]
    show Sum.inl (Quotient.mk _ (D.underVisit x)) =
      Sum.inl (Quotient.mk _ (origVisit D x (selfModel D x ε h) hε v))
    apply congrArg Sum.inl
    apply Quotient.sound
    refine ((self_sameCycle_pair_iff D x h _ hcomp).mpr (Or.inr ?_)).symm
    rw [cycBetween_xv_iff D x h _ hcomp, ← key_of_comp_s D x _ hcomp]
    obtain ⟨i, hi, hr, hk⟩ := selfA_block D x hε h v hv
    have hrange := selfA_blocks_range D x hε i hi _ hr.1 hr.2
    rw [hk]
    interval_cases i <;> simp only [selfAFlo, selfAFhi] at hrange <;> constructor <;> linarith
  · rcases Fin.eq_zero_or_eq_succ l₁ with rfl | ⟨l₀, rfl⟩
    · -- component `B`: the class of `xv`
      rw [Fin.succ_zero_eq_one] at hv
      have hcomp := compOf_origVisit_selfB D x hε h v hv
      have hcls : selfCls D x v.2.val.1 = Sum.inl (Quotient.mk _ (xv D x)) := by rw [hv]; rfl
      rw [hcls]
      show Sum.inl (Quotient.mk _ (xv D x)) =
        Sum.inl (Quotient.mk _ (origVisit D x (selfModel D x ε h) hε v))
      apply congrArg Sum.inl
      apply Quotient.sound
      rcases D.record.reconnect_sameCycle_or (xv D x) _ hcomp with h1 | h1
      · exact h1.symm
      · exfalso
        rw [record_pair_xv, self_sameCycle_pair_iff D x h _ hcomp] at h1
        rcases h1 with h1 | h1
        · exact ((D.record.smoothKeep_iff (xv D x) _).mp
            (smoothKeep_origVisit D x (selfModel D x ε h) hε v)).2 h1
        · rw [cycBetween_xv_iff D x h _ hcomp, ← key_of_comp_s D x _ hcomp] at h1
          obtain ⟨i, hi, hr, hk⟩ := selfB_block D x hε h v hv
          have hrange := selfB_blocks_range D x hε i hi _ hr.1 hr.2
          rw [hk] at h1
          interval_cases i <;> simp only [selfBFlo, selfBFhi] at hrange <;> linarith [h1.2]
    · -- untouched component
      have hcls : selfCls D x v.2.val.1 = oldCls D x ((othersS D x).orderEmbOfFin rfl l₀) := by
        rw [hv]; rfl
      rw [hcls]
      refine oldCls_eq D x _ (orderEmbOfFin_othersS_ne D x l₀)
        (fun e => orderEmbOfFin_othersS_ne D x l₀ (e.trans h.symm)) _ ?_
      obtain ⟨y, ⟨⟨l, m⟩, hm⟩⟩ := v
      change l = l₀.succ.succ at hv
      subst hv
      rfl

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
  change v.2.val.1 = w.2.val.1 at hc
  have hdk : dd D x ≤ kI D x := by have := dd_add_two_le D x h; omega
  rcases Fin.eq_zero_or_eq_succ v.2.val.1 with hv | ⟨l₁, hv⟩
  · -- component `A`
    have hw : w.2.val.1 = (0 : Fin ((othersS D x).card + 2)) := by rw [← hc]; exact hv
    obtain ⟨i, hi, hr, hk⟩ := selfA_block D x hε h v hv
    obtain ⟨j, hj, hr', hk'⟩ := selfA_block D x hε h w hw
    have hN : (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) = dd D x + 2 := by
      rw [hv]; show ((dd D x + 2 : ℕ) : ℝ) = _; push_cast; ring
    have hb : selfBase D x v.2.val.1 = dd D x + 1 := by
      rw [hv]; show ((dd D x + 1 : ℕ) : ℝ) = _; push_cast; ring
    rw [hN, hb, hk, hk']
    exact lt_iff_of_blocks 3 _ _ _ _ _ (selfA_blocks_lohi D x hε h) (selfA_blocks_chain D x hε h)
      (selfA_blocks_mono D x hε) (selfA_blocks_range D x hε) hi hj hr hr'
  · rcases Fin.eq_zero_or_eq_succ l₁ with rfl | ⟨l₀, rfl⟩
    · -- component `B`
      rw [Fin.succ_zero_eq_one] at hv
      have hw : w.2.val.1 = (1 : Fin ((othersS D x).card + 2)) := by rw [← hc]; exact hv
      obtain ⟨i, hi, hr, hk⟩ := selfB_block D x hε h v hv
      obtain ⟨j, hj, hr', hk'⟩ := selfB_block D x hε h w hw
      have hN : (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) = kI D x - dd D x + 2 := by
        rw [hv]; show ((kI D x - dd D x + 2 : ℕ) : ℝ) = _
        rw [Nat.cast_add, Nat.cast_sub hdk]; push_cast; ring
      have hb : selfBase D x v.2.val.1 = kI D x - dd D x + 1 := by
        rw [hv]; show ((kI D x - dd D x + 1 : ℕ) : ℝ) = _
        rw [Nat.cast_add, Nat.cast_sub hdk]; push_cast; ring
      rw [hN, hb, hk, hk']
      exact lt_iff_of_blocks 3 _ _ _ _ _ (selfB_blocks_lohi D x hε h) (selfB_blocks_chain D x hε h)
        (selfB_blocks_mono D x hε) (selfB_blocks_range D x hε) hi hj hr hr'
    · -- untouched component
      have hw : w.2.val.1 = l₀.succ.succ := by rw [← hc]; exact hv
      have hb : selfBase D x v.2.val.1 = 0 := by rw [hv]; rfl
      have hN : (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) =
          (((selfShadow D x ε h).comp w.2.val.1).k : ℝ) := by rw [hc]
      rw [hb, self_rot_eq_key D x hε h v l₀ hv, hN, self_rot_eq_key D x hε h w l₀ hw]

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
