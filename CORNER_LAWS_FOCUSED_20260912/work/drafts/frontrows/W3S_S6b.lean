import SM.FrontRealizeGeometry
import SM.FrontRealizeBase
import SM.FrontRealizeDeform
import SM.FrontInterfaces
import SM.FrontWordsBase
import SM.FrontGeomModel
import SM.PolynomialBlock
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-! # Front certificate rows 76-83 — PROOF SKELETON (FINAL, judge 2026-09-14)

work/drafts/frontrows/Skeleton_FINAL.lean.  The definitions and the eight bundles are copied verbatim from
Statements_FINAL.lean; the eight row theorems are ASSEMBLED at the end from the named LEAVES of section
"Leaves" (26 placeholders, none a row); all glue is proved.  Plan and unit split: PLAN_FINAL.md (units U1-U8).

Leaf groups (PLAN_FINAL.md §5):
* **L-deg** (U1): Laurent-degree arithmetic on `R` — `delta_ne_zero`, `degAZ_delta`, the two skein degree
  bounds (displays ng:skein-plus/minus, ng:degree-plus/minus).
* **L-cnt** (U1): the count changes `ΔD`, `Δw` of each pattern on the realization, through the accepted letter
  tracing (`realize_downCount`, `realize_writhe`) — displays ng:type-I-counts, ng:zigzag-counts,
  ng:crossed-cusp-counts, ng:circle-counts and the (t,u) table.
* **L-rec** (U3, on the record core U2): named-record isomorphisms for the moves that are NOT Reidemeister moves
  of the ordinary diagram — commutation, zigzag deletion, circle deletion (`Record.addFree`), the cusp-skein
  site (switch record + smoothing record + sign), and the uniqueness of the compatible smoothing.
* **L-geo** (U5, U6 on the geometry core U4): the disc-local moves — type III directly between the two standard
  realizations (`RIIIData` in a band disc hugging the three strands), types I, II and the crossed cusp through
  a vertex-moved diagram `D` (same shadow structure as `realize W`, the active strand's interior vertices moved
  inside a convex disc hugging the active strands; `RI`/`RII` there) whose named record is that of `realize W'`.
  NOT through the full-height block rectangle `BlockSetup.U`: `ArcCover` (LinkMoves.lean:208) forbids
  spectator strands inside the move disc (PLAN_FINAL.md §3 F1).
* **L-PL** (U7): the planarity fact `D = c` for an arbitrary PL union of standard circles (row 81 sentence 2).
* **L-smooth** (U8): the smooth clauses of row 76 (nonsingular deformation; representation).

Every leaf below is a TRUE statement about the accepted objects (audited in PLAN_FINAL.md §4); no leaf fixes a
move disc.  Checked with `cd work/lean && lake env lean`. -/

namespace SM

open SM.FrontWord SM.Link
open scoped ContDiff

/-! ## Statements (verbatim from Statements_FINAL.lean) -/

structure SmoothFront.NonsingularDeformation (F F' : SmoothFront) where
  path : ℝ → SmoothFront
  start : path 0 = F
  stop : path 1 = F'
  c_eq : ∀ t, (path t).c = F.c
  smooth : ∀ i : Fin F.c, ContDiffOn ℝ ∞
    (fun p : ℝ × ℝ => ((path p.1).comp (Fin.cast (c_eq p.1).symm i)).γ p.2) (Set.Icc 0 1 ×ˢ Set.univ)

structure NgCommutationClauses : Prop where
  comm_D : ∀ W W' : OWord, IsComm W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  comm_w : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).writhe = (realize W').writhe
  comm_d : ∀ W W' : OWord, IsComm W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  comm_B : ∀ W W' : OWord, IsComm W.letters W'.letters → (realize W).defect = (realize W').defect
  deform_D : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.downCount = F'.downCount
  deform_w : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') → F.writhe = F'.writhe
  deform_d : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → degAZ (P S) = degAZ (P S')
  deform_B : ∀ F F' : SmoothFront, Nonempty (F.NonsingularDeformation F') →
    ∀ S S' : Diagram, F.IsRounding S → F'.IsRounding S' → F.defect S = F'.defect S'
  represent : ∀ F : SmoothFront, ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record)

structure NgFrontIClauses : Prop where
  typeI_B : ∀ W W' : OWord, IsTypeI W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgFrontIIClauses : Prop where
  typeII_D : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  typeII_w : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  typeII_d : ∀ W W' : OWord, IsTypeII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  typeII_B : ∀ W W' : OWord, IsTypeII W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgFrontIIIClauses : Prop where
  typeIII_D : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    (realize W).downCount = (realize W').downCount
  typeIII_w : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).writhe = (realize W').writhe
  typeIII_d : ∀ W W' : OWord, IsTypeIII W.letters W'.letters →
    degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram)
  typeIII_B : ∀ W W' : OWord, IsTypeIII W.letters W'.letters → (realize W).defect = (realize W').defect

structure NgDeletionsClauses : Prop where
  zigzag_s : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').sCount + 2 = (realize W).sCount
  zigzag_B : ∀ W W' : OWord, IsZigzagDeletion W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect
  crossedCusp_s : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').sCount + 1 = (realize W).sCount
  crossedCusp_B : ∀ W W' : OWord, IsCrossedCuspShortcut W.letters W'.letters →
    (realize W').defect ≤ (realize W).defect

structure NgCircleClauses : Prop where
  circleDeletion_B : ∀ W W' : OWord, IsCircleDeletion W.letters W'.letters →
    (realize W).defect = (realize W').defect
  single_B : ∀ F : PLFront, F.IsStandardCircles → F.Γ.c = 1 → F.defect = 0
  union_B : ∀ F : PLFront, F.IsStandardCircles → F.defect = 0

structure NgCuspSkeinClauses : Prop where
  earlier_branch : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    min (realize A').defect (realize C).defect ≤ (realize A).defect
  unique_smoothing : ∀ A A' C C' : OWord, IsCuspSkein A.letters A'.letters C.letters →
    IsCuspSkein A.letters A'.letters C'.letters → C.letters = C'.letters
  smoothing_s : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    (realize C).sCount + 1 = (realize A).sCount
  principal_s : ∀ A A' C : OWord, IsCuspSkein A.letters A'.letters C.letters →
    (realize A').sCount = (realize A).sCount

structure NgLocalFrontBoundClauses : Prop where
  front_inequality : ∀ (F : SmoothFront) (S : Diagram), F.IsRounding S →
    F.writhe - (F.downCount : ℤ) ≤ -degAZ (P S) - 1

/-! ### Nonemptiness helpers (the `s` clauses read `realize_sCount`, which needs a nonempty word) -/

namespace FrontWord

theorem IsZigzagDeletion.source_ne_nil {W W' : Word} (h : IsZigzagDeletion W W') : W ≠ [] := by
  obtain ⟨X, Y, m, d, -, hpat, -⟩ := h
  rcases hpat with rfl | rfl <;> simp

theorem IsCrossedCuspShortcut.ne_nil {W W' : Word} (h : IsCrossedCuspShortcut W W') : W ≠ [] ∧ W' ≠ [] := by
  obtain ⟨X, Y, i, -, hpat⟩ := h
  rcases hpat with ⟨d, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem IsCuspSkeinStep.ne_nil {A A' C : Word} (h : IsCuspSkeinStep A A' C) : A ≠ [] ∧ A' ≠ [] ∧ C ≠ [] := by
  obtain ⟨X, Y, m, d, a, P, L, -, -, -, rfl, rfl, hC⟩ := h
  rcases hC with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp

theorem IsCuspSkein.ne_nil {A A' C : Word} (h : IsCuspSkein A A' C) : A ≠ [] ∧ A' ≠ [] ∧ C ≠ [] := by
  rcases h with h | h
  · exact h.ne_nil
  · obtain ⟨h1, h2, h3⟩ := h.ne_nil; exact ⟨h2, h1, h3⟩

end FrontWord

namespace FrontRows

/-! ## Leaves -/

section Leaves

/-! ### L-deg (unit U1) — Laurent-degree arithmetic (def:adeg, `SM/LinkLaurentRing.lean`) -/

/-- LEAF: `δ = (a − a⁻¹) z⁻¹ ≠ 0` (units and the domain `R`). -/
theorem u1_aInv_ne_zero : R.aInv ≠ 0 := (R.aUnit⁻¹).ne_zero
theorem u1_zInv_ne_zero : R.zInv ≠ 0 := (R.zUnit⁻¹).ne_zero

theorem u1_coeffAt_aInv (d k : ℤ) : coeffAt d k R.aInv = if ((-1 : ℤ), (0 : ℤ)) = (d, k) then 1 else 0 :=
  coeffAt_single ..

theorem u1_coeffAt_a_sub_aInv_one : coeffAt 1 0 (R.a - R.aInv) = 1 := by
  rw [coeffAt_sub, coeffAt_a, u1_coeffAt_aInv]
  simp

theorem u1_a_sub_aInv_ne_zero : R.a - R.aInv ≠ 0 := by
  intro h
  have := u1_coeffAt_a_sub_aInv_one
  rw [h, coeffAt_zero] at this
  exact absurd this (by decide)

theorem delta_ne_zero : R.delta ≠ 0 :=
  mul_ne_zero u1_a_sub_aInv_ne_zero u1_zInv_ne_zero

/-- LEAF (ng:circle, sm-3:2060-2061 "The leading a coefficient of δ is z⁻¹, in degree one"): `deg_a δ = 1`. -/
theorem u1_degAZ_of_degA {f : R} {d : ℤ} (h : degA f = (d : WithBot ℤ)) : degAZ f = d := by
  rw [degAZ, h, WithBot.unbotD_coe]

theorem u1_degAZ_a : degAZ R.a = 1 := u1_degAZ_of_degA (by rw [degA_a, WithBot.coe_one])
theorem u1_degAZ_aInv : degAZ R.aInv = -1 := u1_degAZ_of_degA degA_aInv
theorem u1_degAZ_z : degAZ R.z = 0 := u1_degAZ_of_degA (by rw [degA_z, WithBot.coe_zero])
theorem u1_degAZ_zInv : degAZ R.zInv = 0 := u1_degAZ_of_degA (degA_single 0 (-1) one_ne_zero)

theorem u1_degAZ_a_sub_aInv : degAZ (R.a - R.aInv) = 1 := by
  apply degAZ_eq_of_spec
  · exact ⟨0, by rw [u1_coeffAt_a_sub_aInv_one]; decide⟩
  · intro d k h
    rw [coeffAt_sub, coeffAt_a, u1_coeffAt_aInv] at h
    by_contra hlt
    rw [not_le] at hlt
    have h1 : ¬ ((1 : ℤ), (0 : ℤ)) = (d, k) := by
      intro e; rw [Prod.mk.injEq] at e; omega
    have h2 : ¬ ((-1 : ℤ), (0 : ℤ)) = (d, k) := by
      intro e; rw [Prod.mk.injEq] at e; omega
    simp [h1, h2] at h

theorem degAZ_delta : degAZ R.delta = 1 := by
  rw [R.delta, degAZ_mul u1_a_sub_aInv_ne_zero u1_zInv_ne_zero, u1_degAZ_a_sub_aInv, u1_degAZ_zInv]
  rfl

/-- LEAF (display ng:skein-plus solved for degrees, sm-3:2137-2146 "The degree of a nonzero sum is at most
the maximum of the summand degrees.  Multiplication by a^k shifts degree by k, and multiplication by z
does not change it"): from `f = a⁻² g + a⁻¹ z h`, `deg_a f ≤ max (deg_a g − 2) (deg_a h − 1)`
(`degA_add_le`, `degAZ_mul`, `degA_aInv`, `degA_z`). -/
theorem u1_degAZ_le_max_of_degA_le {f : R} {x y : ℤ} (hf : f ≠ 0)
    (h : degA f ≤ max (x : WithBot ℤ) (y : WithBot ℤ)) : degAZ f ≤ max x y := by
  rw [degA_eq_degAZ hf] at h
  rcases le_max_iff.1 h with h | h
  · exact le_max_of_le_left (WithBot.coe_le_coe.1 h)
  · exact le_max_of_le_right (WithBot.coe_le_coe.1 h)

theorem degAZ_le_of_eq_pos {f g h : R} (hg : g ≠ 0) (hh : h ≠ 0)
    (e : f = R.aInv * R.aInv * g + R.aInv * R.z * h) (hf : f ≠ 0) :
    degAZ f ≤ max (degAZ g - 2) (degAZ h - 1) := by
  have hg' : R.aInv * R.aInv * g ≠ 0 := mul_ne_zero (mul_ne_zero u1_aInv_ne_zero u1_aInv_ne_zero) hg
  have hh' : R.aInv * R.z * h ≠ 0 := mul_ne_zero (mul_ne_zero u1_aInv_ne_zero R.z_ne_zero) hh
  have h1 : degAZ (R.aInv * R.aInv * g) = degAZ g - 2 := by
    rw [degAZ_mul (mul_ne_zero u1_aInv_ne_zero u1_aInv_ne_zero) hg, degAZ_mul u1_aInv_ne_zero u1_aInv_ne_zero,
      u1_degAZ_aInv]; ring
  have h2 : degAZ (R.aInv * R.z * h) = degAZ h - 1 := by
    rw [degAZ_mul (mul_ne_zero u1_aInv_ne_zero R.z_ne_zero) hh, degAZ_mul u1_aInv_ne_zero R.z_ne_zero,
      u1_degAZ_aInv, u1_degAZ_z]; ring
  have hle := degA_add_le (R.aInv * R.aInv * g) (R.aInv * R.z * h)
  rw [← e, degA_eq_degAZ hg', degA_eq_degAZ hh', h1, h2] at hle
  exact u1_degAZ_le_max_of_degA_le hf hle

/-- LEAF (display ng:skein-minus solved for degrees, sm-3:2140-2148): from `f = a² g − a z h`,
`deg_a f ≤ max (deg_a g + 2) (deg_a h + 1)`. -/
theorem degAZ_le_of_eq_neg {f g h : R} (hg : g ≠ 0) (hh : h ≠ 0)
    (e : f = R.a * R.a * g - R.a * R.z * h) (hf : f ≠ 0) :
    degAZ f ≤ max (degAZ g + 2) (degAZ h + 1) := by
  have hg' : R.a * R.a * g ≠ 0 := mul_ne_zero (mul_ne_zero R.a_ne_zero R.a_ne_zero) hg
  have hh' : R.a * R.z * h ≠ 0 := mul_ne_zero (mul_ne_zero R.a_ne_zero R.z_ne_zero) hh
  have h1 : degAZ (R.a * R.a * g) = degAZ g + 2 := by
    rw [degAZ_mul (mul_ne_zero R.a_ne_zero R.a_ne_zero) hg, degAZ_mul R.a_ne_zero R.a_ne_zero, u1_degAZ_a]; ring
  have h2 : degAZ (R.a * R.z * h) = degAZ h + 1 := by
    rw [degAZ_mul (mul_ne_zero R.a_ne_zero R.z_ne_zero) hh, degAZ_mul R.a_ne_zero R.z_ne_zero,
      u1_degAZ_a, u1_degAZ_z]; ring
  have hle := degA_sub_le (R.a * R.a * g) (R.a * R.z * h)
  rw [← e, degA_eq_degAZ hg', degA_eq_degAZ hh', h1, h2] at hle
  exact u1_degAZ_le_max_of_degA_le hf hle

/-! ### L-cnt (unit U1) — the count changes on the realization, through the accepted letter tracing
(`realize_downCount`, `realize_writhe` = β1's `downCountFrom`/`writheFrom` over `X ++ P ++ Y` at the typed
cut before the factor; the printed displays are the factor's own contribution) -/

/-! ### U1 infrastructure — letter tracing of `D` and `w` on the word layer: `downCountFrom` /
`writheFrom` over appends (the run of the prefix fixes the cut before the factor), the bit values of the letters
at a decomposed cut (`downBit`, `signBit` read only the window of `arity` strands at the letter's position), and
the local value of every printed pattern on the symbolic cut — the displays ng:type-I-counts, ng:zigzag-counts,
ng:crossed-cusp-counts, ng:circle-counts, the (t,u) table, and the two disjoint-gadget commutations. -/
section U1Infra

open SM.FrontWord.Letter SM.FrontWord.Word

theorem u1_downCountFrom_nil (c : Cuts) : Word.downCountFrom [] c = 0 := rfl
theorem u1_writheFrom_nil (c : Cuts) : Word.writheFrom [] c = 0 := rfl

theorem u1_downCountFrom_cons {a : Letter} {V : Word} {c c' : Cuts} (h : a.step c = some c') :
    Word.downCountFrom (a :: V) c = a.downBit c + V.downCountFrom c' := by
  simp only [Word.downCountFrom, h]

theorem u1_writheFrom_cons {a : Letter} {V : Word} {c c' : Cuts} (h : a.step c = some c') :
    Word.writheFrom (a :: V) c = a.signBit c + V.writheFrom c' := by
  simp only [Word.writheFrom, h]

theorem u1_downCountFrom_append {V W : Word} {c c' : Cuts} (h : Word.run V c = some c') :
    (V ++ W).downCountFrom c = V.downCountFrom c + W.downCountFrom c' := by
  induction V generalizing c with
  | nil =>
    simp only [run_nil, Option.some.injEq] at h
    subst h
    simp [u1_downCountFrom_nil]
  | cons a V ih =>
    rw [run_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, h1, h2⟩ := h
    rw [List.cons_append, u1_downCountFrom_cons h1, u1_downCountFrom_cons h1, ih h2, add_assoc]

theorem u1_writheFrom_append {V W : Word} {c c' : Cuts} (h : Word.run V c = some c') :
    (V ++ W).writheFrom c = V.writheFrom c + W.writheFrom c' := by
  induction V generalizing c with
  | nil =>
    simp only [run_nil, Option.some.injEq] at h
    subst h
    simp [u1_writheFrom_nil]
  | cons a V ih =>
    rw [run_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, h1, h2⟩ := h
    rw [List.cons_append, u1_writheFrom_cons h1, u1_writheFrom_cons h1, ih h2, add_assoc]

theorem u1_run_append_some {X P : Word} {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀)
    (hP : Word.run P c₀ = some c₁) : Word.run (X ++ P) [] = some c₁ := by
  rw [run_append, hX]; exact hP

theorem u1_downCountFrom_append₃ (X P Y : Word) {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀)
    (hP : Word.run P c₀ = some c₁) :
    (X ++ P ++ Y).downCountFrom [] = X.downCountFrom [] + P.downCountFrom c₀ + Y.downCountFrom c₁ := by
  rw [u1_downCountFrom_append (u1_run_append_some hX hP), u1_downCountFrom_append hX]

theorem u1_writheFrom_append₃ (X P Y : Word) {c₀ c₁ : Cuts} (hX : Word.run X [] = some c₀)
    (hP : Word.run P c₀ = some c₁) :
    (X ++ P ++ Y).writheFrom [] = X.writheFrom [] + P.writheFrom c₀ + Y.writheFrom c₁ := by
  rw [u1_writheFrom_append (u1_run_append_some hX hP), u1_writheFrom_append hX]

/-! bit values -/

theorem u1_downBit_l (m : ℕ) (d : Bool) (c : Cuts) : (Letter.l m d).downBit c = if d then 0 else 1 := rfl
theorem u1_downBit_σ (m : ℕ) (c : Cuts) : (Letter.σ m).downBit c = 0 := rfl
theorem u1_signBit_l (m : ℕ) (d : Bool) (c : Cuts) : (Letter.l m d).signBit c = 0 := rfl
theorem u1_signBit_r (m : ℕ) (c : Cuts) : (Letter.r m).signBit c = 0 := rfl

theorem u1_downBit_r {m : ℕ} {A L : Cuts} (b : Bool) (hA : A.length = m - 1) :
    (Letter.r m).downBit (A ++ b :: L) = if b then 1 else 0 := by
  simp only [downBit]
  rw [List.drop_left' hA]
  cases b <;> rfl

theorem u1_signBit_σ {m : ℕ} {A L : Cuts} (a b : Bool) (hA : A.length = m - 1) :
    (Letter.σ m).signBit (A ++ a :: b :: L) = if a = b then 1 else -1 := by
  simp only [signBit]
  rw [List.drop_left' hA]

/-- the down bit of a letter reads only its window of `arity` strands at its position -/
theorem u1_downBit_window {ℓ : Letter} {n : ℕ} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1)
    (hA' : A'.length = n - 1) (hw : w.length = ℓ.arity) :
    (ℓ.reindex n).downBit (A' ++ (w ++ R')) = ℓ.downBit (A ++ (w ++ R)) := by
  cases ℓ with
  | l m d => rfl
  | σ m => rfl
  | r m =>
    simp only [downBit, reindex, idx] at hA hA' ⊢
    rw [List.drop_left' hA, List.drop_left' hA']
    obtain ⟨p, q, rfl⟩ : ∃ p q, w = [p, q] := by
      match w, hw with
      | [p, q], _ => exact ⟨p, q, rfl⟩
    cases p <;> rfl

theorem u1_signBit_window {ℓ : Letter} {n : ℕ} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1)
    (hA' : A'.length = n - 1) (hw : w.length = ℓ.arity) :
    (ℓ.reindex n).signBit (A' ++ (w ++ R')) = ℓ.signBit (A ++ (w ++ R)) := by
  cases ℓ with
  | l m d => rfl
  | r m => rfl
  | σ m =>
    simp only [signBit, reindex, idx] at hA hA' ⊢
    rw [List.drop_left' hA, List.drop_left' hA']
    obtain ⟨p, q, rfl⟩ : ∃ p q, w = [p, q] := by
      match w, hw with
      | [p, q], _ => exact ⟨p, q, rfl⟩
    rfl


/-! drop helpers -/

theorem u1_drop_eq₁ {A L : Cuts} {x : Bool} {k : ℕ} (hA : A.length + 1 = k) : (A ++ x :: L).drop k = L := by
  rw [List.append_cons]
  exact List.drop_left' (by rw [List.length_append, List.length_singleton]; exact hA)

theorem u1_downBit_r_drop {m : ℕ} {c L : Cuts} {b : Bool} (h : c.drop (m - 1) = b :: L) :
    (Letter.r m).downBit c = if b then 1 else 0 := by
  simp only [downBit]
  rw [h]
  cases b <;> rfl

theorem u1_signBit_σ_drop {m : ℕ} {c L : Cuts} {a b : Bool} (h : c.drop (m - 1) = a :: b :: L) :
    (Letter.σ m).signBit c = if a = b then 1 else -1 := by
  simp only [signBit]
  rw [h]

theorem u1_downBit_window' {ℓ : Letter} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1)
    (hA' : A'.length = ℓ.idx - 1) (hw : w.length = ℓ.arity) :
    ℓ.downBit (A' ++ (w ++ R')) = ℓ.downBit (A ++ (w ++ R)) := by
  have := u1_downBit_window (n := ℓ.idx) (R := R) (R' := R') hA hA' hw
  rwa [reindex_self] at this

theorem u1_signBit_window' {ℓ : Letter} {A A' w R R' : Cuts} (hA : A.length = ℓ.idx - 1)
    (hA' : A'.length = ℓ.idx - 1) (hw : w.length = ℓ.arity) :
    ℓ.signBit (A' ++ (w ++ R')) = ℓ.signBit (A ++ (w ++ R)) := by
  have := u1_signBit_window (n := ℓ.idx) (R := R) (R' := R') hA hA' hw
  rwa [reindex_self] at this

/-! ### Type I -/

theorem u1_typeI_left_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.l m d, .σ (m - 1), .r m] c = some c') :
    Word.downCountFrom [.l m d, .σ (m - 1), .r m] c = 1 ∧
      Word.writheFrom [.l m d, .σ (m - 1), .r m] c = 1 := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', a, rfl, hA'⟩ := exists_split_last A (m - 2) (by omega)
  have h2' : (Letter.σ (m - 1)).step (A' ++ [a] ++ d :: (!d) :: L) = some (A' ++ d :: a :: (!d) :: L) := by
    rw [List.append_assoc, List.singleton_append]
    exact step_of_prefix (ℓ := .σ (m - 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have had : a = d := by
    have h3' := h3
    rw [show A' ++ d :: a :: (!d) :: L = (A' ++ [d]) ++ a :: (!d) :: L by simp,
      step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons] at h3'
    split_ifs at h3' with had
    · exact Bool.not_eq_not.mp had
    · simp at h3'
  have hdrop : (A' ++ d :: a :: (!d) :: L).drop (m - 1) = a :: (!d) :: L := u1_drop_eq₁ (by omega)
  have hdrop1 : (A' ++ [a] ++ d :: (!d) :: L).drop (m - 1 - 1) = a :: d :: (!d) :: L := by
    rw [List.append_assoc]; exact List.drop_left' (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3, u1_downCountFrom_nil,
      u1_downBit_l, u1_downBit_σ, u1_downBit_r_drop hdrop, had]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3, u1_writheFrom_nil,
      u1_signBit_l, u1_signBit_r, u1_signBit_σ_drop hdrop1, had]
    simp

theorem u1_typeI_right_local {m : ℕ} {d : Bool} {c c' : Cuts} (_hm : 1 ≤ m)
    (h : Word.run [.l m d, .σ (m + 1), .r m] c = some c') :
    Word.downCountFrom [.l m d, .σ (m + 1), .r m] c = 1 ∧
      Word.writheFrom [.l m d, .σ (m + 1), .r m] c = 1 := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨b, L₀, rfl⟩ : ∃ b L₀, L = b :: L₀ :=
    exists_cons_of_σ_succ (m := m) (A := A ++ [d]) (by idxomega)
      (by rw [show (A ++ [d]) ++ (!d) :: L = A ++ d :: (!d) :: L by simp]; exact h2)
  have h2' : (Letter.σ (m + 1)).step (A ++ d :: (!d) :: b :: L₀) = some (A ++ d :: b :: (!d) :: L₀) := by
    rw [show A ++ d :: (!d) :: b :: L₀ = (A ++ [d]) ++ (!d) :: b :: L₀ by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have hbd : b = !d := by
    have h3' := h3
    rw [step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons] at h3'
    split_ifs at h3' with hdb
    · exact Bool.eq_not.mpr (Ne.symm hdb)
    · simp at h3'
  have hdrop : (A ++ d :: b :: (!d) :: L₀).drop (m - 1) = d :: b :: (!d) :: L₀ := List.drop_left' hA
  have hdrop1 : (A ++ d :: (!d) :: b :: L₀).drop (m + 1 - 1) = (!d) :: b :: L₀ := u1_drop_eq₁ (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3, u1_downCountFrom_nil,
      u1_downBit_l, u1_downBit_σ, u1_downBit_r_drop hdrop]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3, u1_writheFrom_nil,
      u1_signBit_l, u1_signBit_r, u1_signBit_σ_drop hdrop1, hbd]
    simp

/-! ### Zigzag, circle, crossed cusp -/

theorem u1_zigzag_below_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l m d, .r (m + 1)] c = some c') :
    Word.downCountFrom [.l m d, .r (m + 1)] c = (if d then 0 else 2) ∧
      Word.writheFrom [.l m d, .r (m + 1)] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  have hdrop : (A ++ d :: (!d) :: L).drop (m + 1 - 1) = (!d) :: L := u1_drop_eq₁ (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_l,
      u1_downBit_r_drop hdrop]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_l, u1_signBit_r]
    simp

theorem u1_zigzag_above_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l (m + 1) d, .r m] c = some c') :
    Word.downCountFrom [.l (m + 1) d, .r m] c = (if d then 0 else 2) ∧
      Word.writheFrom [.l (m + 1) d, .r m] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', b, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  have hbd : b = !d := by
    have h2' := h2
    rw [List.append_assoc, List.singleton_append, step_prefix (ℓ := .r m) (by idxomega) (by idxomega),
      act_r_cons] at h2'
    split_ifs at h2' with hbd
    · exact Bool.eq_not.mpr hbd
    · simp at h2'
  have hdrop : (A' ++ [b] ++ d :: (!d) :: L).drop (m - 1) = b :: d :: (!d) :: L := by
    rw [List.append_assoc]; exact List.drop_left' hA'
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_l,
      u1_downBit_r_drop hdrop, hbd]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_l, u1_signBit_r]
    simp

theorem u1_circle_local {m : ℕ} {d : Bool} {c c' : Cuts} (_hm : 1 ≤ m)
    (h : Word.run [.l m d, .r m] c = some c') :
    Word.downCountFrom [.l m d, .r m] c = 1 ∧ Word.writheFrom [.l m d, .r m] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  have hdrop : (A ++ d :: (!d) :: L).drop (m - 1) = d :: (!d) :: L := List.drop_left' hA
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_l,
      u1_downBit_r_drop hdrop]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_l, u1_signBit_r]
    simp

theorem u1_crossedCusp_l_local {i : ℕ} {d : Bool} {c c' : Cuts} (hi : 1 ≤ i)
    (h : Word.run [.l i d, .σ i] c = some c') :
    (Word.downCountFrom [.l i (!d)] c + 1 = Word.downCountFrom [.l i d, .σ i] c ∨
      Word.downCountFrom [.l i (!d)] c = Word.downCountFrom [.l i d, .σ i] c + 1) ∧
    Word.writheFrom [.l i d, .σ i] c = -1 ∧ Word.writheFrom [.l i (!d)] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  have h1' : (Letter.l i (!d)).step (A ++ L) = some (A ++ (!d) :: (!!d) :: L) :=
    step_of_prefix (ℓ := .l i (!d)) (by idxomega) (by idxomega) (act_l _ _ _)
  have hdrop : (A ++ d :: (!d) :: L).drop (i - 1) = d :: (!d) :: L := List.drop_left' hA
  refine ⟨?_, ?_, ?_⟩
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_l,
      u1_downBit_σ, u1_downCountFrom_cons h1', u1_downCountFrom_nil, u1_downBit_l]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_l,
      u1_signBit_σ_drop hdrop]
    cases d <;> simp
  · rw [u1_writheFrom_cons h1', u1_writheFrom_nil, u1_signBit_l]; simp

theorem u1_crossedCusp_r_local {i : ℕ} {c c' : Cuts} (hi : 1 ≤ i)
    (h : Word.run [.σ i, .r i] c = some c') :
    (Word.downCountFrom [.r i] c + 1 = Word.downCountFrom [.σ i, .r i] c ∨
      Word.downCountFrom [.r i] c = Word.downCountFrom [.σ i, .r i] c + 1) ∧
    Word.writheFrom [.σ i, .r i] c = -1 ∧ Word.writheFrom [.r i] c = 0 := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨p, q, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  have hpq : p ≠ q := by
    have h2' := h2
    rw [step_prefix (ℓ := .r i) (by idxomega) (by idxomega), act_r_cons] at h2'
    split_ifs at h2' with hqp
    · exact Ne.symm hqp
    · simp at h2'
  have h1' : (Letter.r i).step (A ++ p :: q :: L₀) = some (A ++ L₀) := by
    rw [step_prefix (ℓ := .r i) (by idxomega) (by idxomega), act_r_cons, ite_eq_left hpq]; rfl
  have hdrop : (A ++ p :: q :: L₀).drop (i - 1) = p :: q :: L₀ := List.drop_left' hA
  have hdrop1 : (A ++ q :: p :: L₀).drop (i - 1) = q :: p :: L₀ := List.drop_left' hA
  refine ⟨?_, ?_, ?_⟩
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2, u1_downCountFrom_nil, u1_downBit_σ,
      u1_downBit_r_drop hdrop1, u1_downCountFrom_cons h1', u1_downCountFrom_nil, u1_downBit_r_drop hdrop]
    cases p <;> cases q <;> simp_all
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2, u1_writheFrom_nil, u1_signBit_r,
      u1_signBit_σ_drop hdrop]
    simp [hpq]
  · rw [u1_writheFrom_cons h1', u1_writheFrom_nil, u1_signBit_r]; simp


/-! ### Type II -/

theorem u1_typeII_l_left_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.l (m - 1) d, .σ m, .σ (m - 1)] c = some c') :
    Word.downCountFrom [.l (m - 1) d, .σ m, .σ (m - 1)] c = Word.downCountFrom [.l m d] c ∧
      Word.writheFrom [.l (m - 1) d, .σ m, .σ (m - 1)] c = Word.writheFrom [.l m d] c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨b, L₀, rfl⟩ : ∃ b L₀, L = b :: L₀ := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact exists_cons_of_σ_succ (m := m') (A := A ++ [d]) (by idxomega)
      (by rw [show (A ++ [d]) ++ (!d) :: L = A ++ d :: (!d) :: L by simp]; exact h2)
  have h2' : (Letter.σ m).step (A ++ d :: (!d) :: b :: L₀) = some (A ++ d :: b :: (!d) :: L₀) := by
    rw [show A ++ d :: (!d) :: b :: L₀ = (A ++ [d]) ++ (!d) :: b :: L₀ by simp,
      step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have h3' : (Letter.σ (m - 1)).step (A ++ d :: b :: (!d) :: L₀) = some (A ++ b :: d :: (!d) :: L₀) :=
    step_of_prefix (ℓ := .σ (m - 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have hP' : (Letter.l m d).step (A ++ b :: L₀) = some (A ++ b :: d :: (!d) :: L₀) := by
    rw [show A ++ b :: L₀ = (A ++ [b]) ++ L₀ by simp,
      step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)]
    simp
  have hdrop1 : (A ++ d :: (!d) :: b :: L₀).drop (m - 1) = (!d) :: b :: L₀ := u1_drop_eq₁ (by omega)
  have hdrop2 : (A ++ d :: b :: (!d) :: L₀).drop (m - 1 - 1) = d :: b :: (!d) :: L₀ := List.drop_left' hA
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3', u1_downCountFrom_nil,
      u1_downCountFrom_cons hP', u1_downCountFrom_nil]
    simp only [u1_downBit_l, u1_downBit_σ, add_zero]
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3', u1_writheFrom_nil,
      u1_writheFrom_cons hP', u1_writheFrom_nil, u1_signBit_σ_drop hdrop1, u1_signBit_σ_drop hdrop2]
    simp only [u1_signBit_l]
    cases d <;> cases b <;> simp

theorem u1_typeII_l_right_local {m : ℕ} {d : Bool} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.l (m + 1) d, .σ m, .σ (m + 1)] c = some c') :
    Word.downCountFrom [.l (m + 1) d, .σ m, .σ (m + 1)] c = Word.downCountFrom [.l m d] c ∧
      Word.writheFrom [.l (m + 1) d, .σ m, .σ (m + 1)] c = Word.writheFrom [.l m d] c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  simp only [act_l, Option.some.injEq, idx] at hL hA
  subst hL
  obtain ⟨A', b, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  have h2' : (Letter.σ m).step (A' ++ [b] ++ d :: (!d) :: L) = some (A' ++ d :: b :: (!d) :: L) := by
    rw [List.append_assoc, List.singleton_append]
    exact step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have h3' : (Letter.σ (m + 1)).step (A' ++ d :: b :: (!d) :: L) = some (A' ++ d :: (!d) :: b :: L) := by
    rw [show A' ++ d :: b :: (!d) :: L = (A' ++ [d]) ++ b :: (!d) :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have hP' : (Letter.l m d).step (A' ++ [b] ++ L) = some (A' ++ d :: (!d) :: b :: L) := by
    rw [List.append_assoc, List.singleton_append]
    exact step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)
  have hdrop1 : (A' ++ [b] ++ d :: (!d) :: L).drop (m - 1) = b :: d :: (!d) :: L := by
    rw [List.append_assoc]; exact List.drop_left' hA'
  have hdrop2 : (A' ++ d :: b :: (!d) :: L).drop (m + 1 - 1) = b :: (!d) :: L := u1_drop_eq₁ (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3', u1_downCountFrom_nil,
      u1_downCountFrom_cons hP', u1_downCountFrom_nil]
    simp only [u1_downBit_l, u1_downBit_σ, add_zero]
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3', u1_writheFrom_nil,
      u1_writheFrom_cons hP', u1_writheFrom_nil, u1_signBit_σ_drop hdrop1, u1_signBit_σ_drop hdrop2]
    simp only [u1_signBit_l]
    cases d <;> cases b <;> simp

theorem u1_typeII_r_left_local {m : ℕ} {c c' : Cuts} (hm : 2 ≤ m)
    (h : Word.run [.σ (m - 1), .σ m, .r (m - 1)] c = some c') :
    Word.downCountFrom [.σ (m - 1), .σ m, .r (m - 1)] c = Word.downCountFrom [.r m] c ∧
      Word.writheFrom [.σ (m - 1), .σ m, .r (m - 1)] c = Word.writheFrom [.r m] c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨p, q, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  obtain ⟨r, L₁, rfl⟩ : ∃ r L₁, L₀ = r :: L₁ := by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    exact exists_cons_of_σ_succ (m := m') (A := A ++ [q]) (by idxomega)
      (by rw [show (A ++ [q]) ++ p :: L₀ = A ++ q :: p :: L₀ by simp]; exact h2)
  have h2' : (Letter.σ m).step (A ++ q :: p :: r :: L₁) = some (A ++ q :: r :: p :: L₁) := by
    rw [show A ++ q :: p :: r :: L₁ = (A ++ [q]) ++ p :: r :: L₁ by simp,
      step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have hqr : q ≠ r := by
    have h3' := h3
    rw [step_prefix (ℓ := .r (m - 1)) (by idxomega) (by idxomega), act_r_cons] at h3'
    split_ifs at h3' with hqr
    · exact hqr
    · simp at h3'
  have hP' : (Letter.r m).step (A ++ p :: q :: r :: L₁) = some (A ++ p :: L₁) := by
    rw [show A ++ p :: q :: r :: L₁ = (A ++ [p]) ++ q :: r :: L₁ by simp,
      step_prefix (ℓ := .r m) (by idxomega) (by idxomega), act_r_cons, ite_eq_left hqr]
    simp
  have hdrop0 : (A ++ p :: q :: r :: L₁).drop (m - 1 - 1) = p :: q :: r :: L₁ := List.drop_left' hA
  have hdrop1 : (A ++ q :: p :: r :: L₁).drop (m - 1) = p :: r :: L₁ := u1_drop_eq₁ (by omega)
  have hdrop2 : (A ++ q :: r :: p :: L₁).drop (m - 1 - 1) = q :: r :: p :: L₁ := List.drop_left' hA
  have hdropP : (A ++ p :: q :: r :: L₁).drop (m - 1) = q :: r :: L₁ := u1_drop_eq₁ (by omega)
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3, u1_downCountFrom_nil,
      u1_downCountFrom_cons hP', u1_downCountFrom_nil, u1_downBit_r_drop hdrop2, u1_downBit_r_drop hdropP]
    simp only [u1_downBit_σ, add_zero, zero_add]
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3, u1_writheFrom_nil,
      u1_writheFrom_cons hP', u1_writheFrom_nil, u1_signBit_σ_drop hdrop0, u1_signBit_σ_drop hdrop1]
    simp only [u1_signBit_r]
    cases p <;> cases q <;> cases r <;> simp_all

theorem u1_typeII_r_right_local {m : ℕ} {c c' : Cuts} (hm : 1 ≤ m)
    (h : Word.run [.σ (m + 1), .σ m, .r (m + 1)] c = some c') :
    Word.downCountFrom [.σ (m + 1), .σ m, .r (m + 1)] c = Word.downCountFrom [.r m] c ∧
      Word.writheFrom [.σ (m + 1), .σ m, .r (m + 1)] c = Word.writheFrom [.r m] c := by
  rw [run_three_iff] at h
  obtain ⟨c₁, h1, c₂, h2, h3⟩ := h
  obtain ⟨A, L, L', -, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨q, r, L₀, rfl, rfl⟩ := act_σ_eq_some_iff.1 hL
  simp only [idx] at hA
  obtain ⟨A', p, rfl, hA'⟩ := exists_split_last A (m - 1) (by omega)
  have h2' : (Letter.σ m).step (A' ++ [p] ++ r :: q :: L₀) = some (A' ++ r :: p :: q :: L₀) := by
    rw [List.append_assoc, List.singleton_append]
    exact step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  rw [h2'] at h2
  obtain rfl := Option.some.inj h2
  have hpq : p ≠ q := by
    have h3' := h3
    rw [show A' ++ r :: p :: q :: L₀ = (A' ++ [r]) ++ p :: q :: L₀ by simp,
      step_prefix (ℓ := .r (m + 1)) (by idxomega) (by idxomega), act_r_cons] at h3'
    split_ifs at h3' with hpq
    · exact hpq
    · simp at h3'
  have hP' : (Letter.r m).step (A' ++ [p] ++ q :: r :: L₀) = some (A' ++ r :: L₀) := by
    rw [List.append_assoc, List.singleton_append, step_prefix (ℓ := .r m) (by idxomega) (by idxomega),
      act_r_cons, ite_eq_left hpq]
    simp
  have hdrop0 : (A' ++ [p] ++ q :: r :: L₀).drop (m + 1 - 1) = q :: r :: L₀ :=
    List.drop_left' (by rw [List.length_append, List.length_singleton]; omega)
  have hdrop1 : (A' ++ [p] ++ r :: q :: L₀).drop (m - 1) = p :: r :: q :: L₀ := by
    rw [List.append_assoc]; exact List.drop_left' hA'
  have hdrop2 : (A' ++ r :: p :: q :: L₀).drop (m + 1 - 1) = p :: q :: L₀ := u1_drop_eq₁ (by omega)
  have hdropP : (A' ++ [p] ++ q :: r :: L₀).drop (m - 1) = p :: q :: r :: L₀ := by
    rw [List.append_assoc]; exact List.drop_left' hA'
  constructor
  · rw [u1_downCountFrom_cons h1, u1_downCountFrom_cons h2', u1_downCountFrom_cons h3, u1_downCountFrom_nil,
      u1_downCountFrom_cons hP', u1_downCountFrom_nil, u1_downBit_r_drop hdrop2, u1_downBit_r_drop hdropP]
    simp only [u1_downBit_σ, add_zero, zero_add]
  · rw [u1_writheFrom_cons h1, u1_writheFrom_cons h2', u1_writheFrom_cons h3, u1_writheFrom_nil,
      u1_writheFrom_cons hP', u1_writheFrom_nil, u1_signBit_σ_drop hdrop0, u1_signBit_σ_drop hdrop1]
    simp only [u1_signBit_r]
    cases p <;> cases q <;> cases r <;> simp_all

/-! ### Type III -/

theorem u1_typeIII_local {m : ℕ} {A L : Cuts} {p q r : Bool} (hm : 1 ≤ m) (hA : A.length = m - 1) :
    Word.downCountFrom [.σ (m + 1), .σ m, .σ (m + 1)] (A ++ p :: q :: r :: L) = 0 ∧
    Word.downCountFrom [.σ m, .σ (m + 1), .σ m] (A ++ p :: q :: r :: L) = 0 ∧
    Word.writheFrom [.σ (m + 1), .σ m, .σ (m + 1)] (A ++ p :: q :: r :: L) =
      Word.writheFrom [.σ m, .σ (m + 1), .σ m] (A ++ p :: q :: r :: L) := by
  have s1 : (Letter.σ (m + 1)).step (A ++ p :: q :: r :: L) = some (A ++ p :: r :: q :: L) := by
    rw [show A ++ p :: q :: r :: L = (A ++ [p]) ++ q :: r :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have s2 : (Letter.σ m).step (A ++ p :: r :: q :: L) = some (A ++ r :: p :: q :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have s3 : (Letter.σ (m + 1)).step (A ++ r :: p :: q :: L) = some (A ++ r :: q :: p :: L) := by
    rw [show A ++ r :: p :: q :: L = (A ++ [r]) ++ p :: q :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have t1 : (Letter.σ m).step (A ++ p :: q :: r :: L) = some (A ++ q :: p :: r :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have t2 : (Letter.σ (m + 1)).step (A ++ q :: p :: r :: L) = some (A ++ q :: r :: p :: L) := by
    rw [show A ++ q :: p :: r :: L = (A ++ [q]) ++ p :: r :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have t3 : (Letter.σ m).step (A ++ q :: r :: p :: L) = some (A ++ r :: q :: p :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have d1 : (A ++ p :: q :: r :: L).drop (m + 1 - 1) = q :: r :: L := u1_drop_eq₁ (by omega)
  have d2 : (A ++ p :: r :: q :: L).drop (m - 1) = p :: r :: q :: L := List.drop_left' hA
  have d3 : (A ++ r :: p :: q :: L).drop (m + 1 - 1) = p :: q :: L := u1_drop_eq₁ (by omega)
  have e1 : (A ++ p :: q :: r :: L).drop (m - 1) = p :: q :: r :: L := List.drop_left' hA
  have e2 : (A ++ q :: p :: r :: L).drop (m + 1 - 1) = p :: r :: L := u1_drop_eq₁ (by omega)
  have e3 : (A ++ q :: r :: p :: L).drop (m - 1) = q :: r :: p :: L := List.drop_left' hA
  refine ⟨?_, ?_, ?_⟩
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_cons s2, u1_downCountFrom_cons s3, u1_downCountFrom_nil]
    simp only [u1_downBit_σ, add_zero]
  · rw [u1_downCountFrom_cons t1, u1_downCountFrom_cons t2, u1_downCountFrom_cons t3, u1_downCountFrom_nil]
    simp only [u1_downBit_σ, add_zero]
  · rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_cons s3, u1_writheFrom_nil,
      u1_writheFrom_cons t1, u1_writheFrom_cons t2, u1_writheFrom_cons t3, u1_writheFrom_nil,
      u1_signBit_σ_drop d1, u1_signBit_σ_drop d2, u1_signBit_σ_drop d3,
      u1_signBit_σ_drop e1, u1_signBit_σ_drop e2, u1_signBit_σ_drop e3]
    ring

/-! ### Cusp skein -/

theorem u1_skein_local {m : ℕ} {d a : Bool} {P L : Cuts} (hm : 1 ≤ m) (hP : P.length = m - 1) :
    Word.downCountFrom [.l (m + 1) d, .σ m] (P ++ a :: L) = (if d then 0 else 1) ∧
    Word.downCountFrom [.l m d, .σ (m + 1)] (P ++ a :: L) = (if d then 0 else 1) ∧
    Word.downCountFrom [.l m d] (P ++ a :: L) = (if d then 0 else 1) ∧
    Word.downCountFrom [.l (m + 1) d] (P ++ a :: L) = (if d then 0 else 1) ∧
    Word.writheFrom [.l (m + 1) d, .σ m] (P ++ a :: L) + Word.writheFrom [.l m d, .σ (m + 1)] (P ++ a :: L) = 0 ∧
    Word.writheFrom [.l m d] (P ++ a :: L) = 0 ∧ Word.writheFrom [.l (m + 1) d] (P ++ a :: L) = 0 := by
  have s1 : (Letter.l (m + 1) d).step (P ++ a :: L) = some (P ++ a :: d :: (!d) :: L) := by
    rw [show P ++ a :: L = (P ++ [a]) ++ L by simp,
      step_of_prefix (ℓ := .l (m + 1) d) (by idxomega) (by idxomega) (act_l _ _ _)]
    simp
  have s2 : (Letter.σ m).step (P ++ a :: d :: (!d) :: L) = some (P ++ d :: a :: (!d) :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have t1 : (Letter.l m d).step (P ++ a :: L) = some (P ++ d :: (!d) :: a :: L) :=
    step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (act_l _ _ _)
  have t2 : (Letter.σ (m + 1)).step (P ++ d :: (!d) :: a :: L) = some (P ++ d :: a :: (!d) :: L) := by
    rw [show P ++ d :: (!d) :: a :: L = (P ++ [d]) ++ (!d) :: a :: L by simp,
      step_of_prefix (ℓ := .σ (m + 1)) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)]
    simp
  have d1 : (P ++ a :: d :: (!d) :: L).drop (m - 1) = a :: d :: (!d) :: L := List.drop_left' hP
  have d2 : (P ++ d :: (!d) :: a :: L).drop (m + 1 - 1) = (!d) :: a :: L := u1_drop_eq₁ (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_cons s2, u1_downCountFrom_nil]
    simp only [u1_downBit_l, u1_downBit_σ, add_zero]
  · rw [u1_downCountFrom_cons t1, u1_downCountFrom_cons t2, u1_downCountFrom_nil]
    simp only [u1_downBit_l, u1_downBit_σ, add_zero]
  · rw [u1_downCountFrom_cons t1, u1_downCountFrom_nil]
    simp only [u1_downBit_l, add_zero]
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_nil]
    simp only [u1_downBit_l, add_zero]
  · rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_nil, u1_writheFrom_cons t1,
      u1_writheFrom_cons t2, u1_writheFrom_nil, u1_signBit_σ_drop d1, u1_signBit_σ_drop d2]
    simp only [u1_signBit_l]
    cases a <;> cases d <;> simp
  · rw [u1_writheFrom_cons t1, u1_writheFrom_nil]
    simp only [u1_signBit_l, add_zero]
  · rw [u1_writheFrom_cons s1, u1_writheFrom_nil]
    simp only [u1_signBit_l, add_zero]

/-! ### Commutations -/

theorem u1_comm_above_local {a b : Letter} {c c' : Cuts} (hab : b.idx + b.arity ≤ a.idx)
    (h : Word.run [a, b] c = some c') :
    Word.downCountFrom [a, b] c = Word.downCountFrom [b, a.reindex (a.idx + b.coarity - b.arity)] c ∧
    Word.writheFrom [a, b] c = Word.writheFrom [b, a.reindex (a.idx + b.coarity - b.arity)] c := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', ha1, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨B, M, M', hb1, hB, hc₁, hM, rfl⟩ := step_eq_some_iff.1 h2
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := act_window hM
  obtain ⟨A₁, H, rfl, hA₁⟩ := exists_split A (b.idx - 1 + b.arity) (by omega)
  have hlen : A₁.length = (B ++ w).length := by simp only [List.length_append]; omega
  rw [List.append_assoc, ← List.append_assoc B w R] at hc₁
  obtain ⟨rfl, hR⟩ := List.append_inj hc₁ hlen
  subst hR
  obtain ⟨v, v', S, rfl, hv, hv', hv'len, rfl⟩ := act_window hL
  have s1 : a.step (B ++ w ++ H ++ (v ++ S)) = some (B ++ (w ++ (H ++ (v' ++ S)))) := by
    rw [h1]; simp only [List.append_assoc]
  have s2 : b.step (B ++ (w ++ (H ++ (v' ++ S)))) = some (B ++ (w' ++ (H ++ (v' ++ S)))) :=
    step_of_prefix hb1 hB (by rw [act_append hw, hw']; rfl)
  have s1' : b.step (B ++ w ++ H ++ (v ++ S)) = some (B ++ w' ++ H ++ (v ++ S)) := by
    rw [show B ++ w ++ H ++ (v ++ S) = B ++ (w ++ (H ++ (v ++ S))) by simp only [List.append_assoc],
      step_of_prefix hb1 hB (L' := w' ++ (H ++ (v ++ S))) (by rw [act_append hw, hw']; rfl)]
    simp only [List.append_assoc]
  have s2' : (a.reindex (a.idx + b.coarity - b.arity)).step (B ++ w' ++ H ++ (v ++ S)) =
      some (B ++ w' ++ H ++ (v' ++ S)) :=
    step_of_prefix (ℓ := a.reindex _) (A := B ++ w' ++ H) (by lenomega) (by lenomega)
      (by rw [act_reindex]; exact hL)
  have e1 : (a.reindex (a.idx + b.coarity - b.arity)).downBit (B ++ w' ++ H ++ (v ++ S)) =
      a.downBit (B ++ w ++ H ++ (v ++ S)) := u1_downBit_window hA (by lenomega) hv
  have e2 : b.downBit (B ++ (w ++ (H ++ (v' ++ S)))) = b.downBit (B ++ w ++ H ++ (v ++ S)) := by
    rw [show B ++ w ++ H ++ (v ++ S) = B ++ (w ++ (H ++ (v ++ S))) by simp only [List.append_assoc]]
    exact u1_downBit_window' hB hB hw
  have f1 : (a.reindex (a.idx + b.coarity - b.arity)).signBit (B ++ w' ++ H ++ (v ++ S)) =
      a.signBit (B ++ w ++ H ++ (v ++ S)) := u1_signBit_window hA (by lenomega) hv
  have f2 : b.signBit (B ++ (w ++ (H ++ (v' ++ S)))) = b.signBit (B ++ w ++ H ++ (v ++ S)) := by
    rw [show B ++ w ++ H ++ (v ++ S) = B ++ (w ++ (H ++ (v ++ S))) by simp only [List.append_assoc]]
    exact u1_signBit_window' hB hB hw
  constructor
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_cons s2, u1_downCountFrom_nil,
      u1_downCountFrom_cons s1', u1_downCountFrom_cons s2', u1_downCountFrom_nil, e1, e2]
    ring
  · rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_nil,
      u1_writheFrom_cons s1', u1_writheFrom_cons s2', u1_writheFrom_nil, f1, f2]
    ring

theorem u1_comm_below_local {a b : Letter} {c c' : Cuts} (hab : a.idx + a.coarity ≤ b.idx)
    (h : Word.run [a, b] c = some c') :
    Word.downCountFrom [a, b] c = Word.downCountFrom [b.reindex (b.idx + a.arity - a.coarity), a] c ∧
    Word.writheFrom [a, b] c = Word.writheFrom [b.reindex (b.idx + a.arity - a.coarity), a] c := by
  rw [run_two_iff] at h
  obtain ⟨c₁, h1, h2⟩ := h
  obtain ⟨A, L, L', ha1, hA, rfl, hL, rfl⟩ := step_eq_some_iff.1 h1
  obtain ⟨w, w', R, rfl, hw, hw', hw'len, rfl⟩ := act_window hL
  obtain ⟨B, M, M', hb1, hB, hc₁, hM, rfl⟩ := step_eq_some_iff.1 h2
  obtain ⟨B₁, H, rfl, hB₁⟩ := exists_split B (a.idx - 1 + a.coarity) (by omega)
  have hlen : (A ++ w').length = B₁.length := by simp only [List.length_append]; omega
  rw [← List.append_assoc, List.append_assoc B₁ H M] at hc₁
  obtain ⟨hB₁eq, hR⟩ := List.append_inj hc₁ hlen
  subst hB₁eq
  subst hR
  obtain ⟨u, u', T, rfl, hu, hu', hu'len, rfl⟩ := act_window hM
  have s1 : a.step (A ++ (w ++ (H ++ (u ++ T)))) = some (A ++ w' ++ H ++ (u ++ T)) := by
    rw [h1]; simp only [List.append_assoc]
  have s2 : b.step (A ++ w' ++ H ++ (u ++ T)) = some (A ++ w' ++ H ++ (u' ++ T)) :=
    step_of_prefix hb1 hB hM
  have s1' : (b.reindex (b.idx + a.arity - a.coarity)).step (A ++ (w ++ (H ++ (u ++ T)))) =
      some (A ++ w ++ H ++ (u' ++ T)) := by
    rw [show A ++ (w ++ (H ++ (u ++ T))) = A ++ w ++ H ++ (u ++ T) by simp only [List.append_assoc]]
    exact step_of_prefix (ℓ := b.reindex _) (A := A ++ w ++ H) (by lenomega) (by lenomega)
      (by rw [act_reindex]; exact hM)
  have s2' : a.step (A ++ w ++ H ++ (u' ++ T)) = some (A ++ w' ++ H ++ (u' ++ T)) := by
    rw [show A ++ w ++ H ++ (u' ++ T) = A ++ (w ++ (H ++ (u' ++ T))) by simp only [List.append_assoc],
      step_of_prefix ha1 hA (L' := w' ++ (H ++ (u' ++ T))) (by rw [act_append hw, hw']; rfl)]
    simp only [List.append_assoc]
  have e1 : a.downBit (A ++ w ++ H ++ (u' ++ T)) = a.downBit (A ++ (w ++ (H ++ (u ++ T)))) := by
    rw [show A ++ w ++ H ++ (u' ++ T) = A ++ (w ++ (H ++ (u' ++ T))) by simp only [List.append_assoc]]
    exact u1_downBit_window' hA hA hw
  have e2 : (b.reindex (b.idx + a.arity - a.coarity)).downBit (A ++ (w ++ (H ++ (u ++ T)))) =
      b.downBit (A ++ w' ++ H ++ (u ++ T)) := by
    rw [show A ++ (w ++ (H ++ (u ++ T))) = A ++ w ++ H ++ (u ++ T) by simp only [List.append_assoc]]
    exact u1_downBit_window hB (by lenomega) hu
  have f1 : a.signBit (A ++ w ++ H ++ (u' ++ T)) = a.signBit (A ++ (w ++ (H ++ (u ++ T)))) := by
    rw [show A ++ w ++ H ++ (u' ++ T) = A ++ (w ++ (H ++ (u' ++ T))) by simp only [List.append_assoc]]
    exact u1_signBit_window' hA hA hw
  have f2 : (b.reindex (b.idx + a.arity - a.coarity)).signBit (A ++ (w ++ (H ++ (u ++ T)))) =
      b.signBit (A ++ w' ++ H ++ (u ++ T)) := by
    rw [show A ++ (w ++ (H ++ (u ++ T))) = A ++ w ++ H ++ (u ++ T) by simp only [List.append_assoc]]
    exact u1_signBit_window hB (by lenomega) hu
  constructor
  · rw [u1_downCountFrom_cons s1, u1_downCountFrom_cons s2, u1_downCountFrom_nil,
      u1_downCountFrom_cons s1', u1_downCountFrom_cons s2', u1_downCountFrom_nil, e1, e2]
    ring
  · rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_nil,
      u1_writheFrom_cons s1', u1_writheFrom_cons s2', u1_writheFrom_nil, f1, f2]
    ring

theorem u1_commStep_counts {V V' : Word} (h : IsCommStep V V') (hV : V.Closed) :
    V.downCountFrom [] = V'.downCountFrom [] ∧ V.writheFrom [] = V'.writheFrom [] := by
  obtain ⟨X, Y, a, b, rfl, hpat⟩ := h
  obtain ⟨c₀, c₁, hX, hP, -⟩ := hV.exists_run
  rcases hpat with ⟨hab, rfl⟩ | ⟨hab, rfl⟩
  · have hP' := run_comm_above hab hP
    obtain ⟨hD, hw⟩ := u1_comm_above_local hab hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_downCountFrom_append₃ X _ Y hX hP',
      u1_writheFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩
  · have hP' := run_comm_below hab hP
    obtain ⟨hD, hw⟩ := u1_comm_below_local hab hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_downCountFrom_append₃ X _ Y hX hP',
      u1_writheFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩

/-! ### the type-I target is never empty -/

theorem u1_typeI_target_ne_nil {W X Y : Word} {m : ℕ} {d : Bool}
    (hpat : (2 ≤ m ∧ W = X ++ [.l m d, .σ (m - 1), .r m] ++ Y) ∨
      (1 ≤ m ∧ W = X ++ [.l m d, .σ (m + 1), .r m] ++ Y))
    (hW : W.Closed) : X ++ Y ≠ [] := by
  intro hXY
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hXY
  rcases hpat with ⟨hm, rfl⟩ | ⟨hm, rfl⟩
  · simp only [List.nil_append, List.append_nil] at hW
    obtain ⟨c₁, h1, -⟩ := run_three_iff.1 hW
    obtain ⟨A, L, L', -, hA, hAL, -, -⟩ := step_eq_some_iff.1 h1
    have hA0 : A = [] := (List.append_eq_nil_iff.1 hAL.symm).1
    simp only [idx] at hA
    rw [hA0] at hA
    simp at hA; omega
  · simp only [List.nil_append, List.append_nil] at hW
    obtain ⟨c₁, h1, -⟩ := run_three_iff.1 hW
    obtain ⟨A, L, L', -, hA, hAL, -, -⟩ := step_eq_some_iff.1 h1
    have hA0 : A = [] := (List.append_eq_nil_iff.1 hAL.symm).1
    simp only [idx] at hA
    rw [hA0] at hA
    have : m = 1 := by simp at hA; omega
    subst this
    cases d <;> exact absurd hW (by decide)

end U1Infra

/-- LEAF (ng:commutation, sm-3:1929-1933 "The cusp directions and crossing signs are unchanged, so D and w
are unchanged as well"). -/
theorem comm_counts {W W' : OWord} (h : IsComm W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := by
  have hne : W.letters ≠ [] := by
    rcases h with ⟨X, Y, a, b, hW, -⟩ | ⟨X, Y, a, b, -, hpat⟩
    · rw [hW]; simp
    · rcases hpat with ⟨-, hW⟩ | ⟨-, hW⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by
    rcases h with ⟨X, Y, a, b, -, hpat⟩ | ⟨X, Y, a, b, hW', -⟩
    · rcases hpat with ⟨-, hW'⟩ | ⟨-, hW'⟩ <;> rw [hW'] <;> simp
    · rw [hW']; simp
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rcases h with h | h
  · exact u1_commStep_counts h W.closed
  · obtain ⟨hD, hw⟩ := u1_commStep_counts h W'.closed
    exact ⟨hD.symm, hw.symm⟩

/-- LEAF (display ng:type-I-counts, sm-3:1964-1966, deletion direction: the curl carries exactly one downward
cusp — "Exactly one of the two cusps is downward and one is upward" — and one positive crossing — "Its
crossing is also positive"). -/
theorem typeI_counts {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount + 1 ∧ (realize W).writhe = (realize W').writhe + 1 := by
  obtain ⟨X, Y, m, d, hpat, hW'⟩ := h
  have hcl := W.closed
  have hne : W.letters ≠ [] := by rcases hpat with ⟨-, hW⟩ | ⟨-, hW⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by rw [hW']; exact u1_typeI_target_ne_nil hpat hcl
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rw [hW']
  rcases hpat with ⟨hm, hW⟩ | ⟨hm, hW⟩
  · rw [hW] at hcl ⊢
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain rfl := run_typeI_left hm hP
    obtain ⟨hD, hw⟩ := u1_typeI_left_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
    constructor <;> omega
  · rw [hW] at hcl ⊢
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain rfl := run_typeI_right hm hP
    obtain ⟨hD, hw⟩ := u1_typeI_right_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
    constructor <;> omega

/-- LEAF (ng:front-II, sm-3:1979-1987 "Their signs are opposite ... The same upper and lower cusp arms remain
after deletion.  Thus Δw = ΔD = 0"). -/
theorem typeII_counts {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := by
  obtain ⟨X, Y, m, hpat⟩ := h
  have hcl := W.closed
  have hne : W.letters ≠ [] := by
    rcases hpat with ⟨d, -, hW, -⟩ | ⟨d, -, hW, -⟩ | ⟨-, hW, -⟩ | ⟨-, hW, -⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by
    rcases hpat with ⟨d, -, -, hW'⟩ | ⟨d, -, -, hW'⟩ | ⟨-, -, hW'⟩ | ⟨-, -, hW'⟩ <;> rw [hW'] <;> simp
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rcases hpat with ⟨d, hm, hW, hW'⟩ | ⟨d, hm, hW, hW'⟩ | ⟨hm, hW, hW'⟩ | ⟨hm, hW, hW'⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_typeII_l_left hm hP
    obtain ⟨hD, hw⟩ := u1_typeII_l_left_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_typeII_l_right hm hP
    obtain ⟨hD, hw⟩ := u1_typeII_l_right_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_typeII_r_left hm hP
    obtain ⟨hD, hw⟩ := u1_typeII_r_left_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_typeII_r_right hm hP
    obtain ⟨hD, hw⟩ := u1_typeII_r_right_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hD, hw]
    exact ⟨rfl, rfl⟩

/-- LEAF (ng:front-III, sm-3:1997-2001 "Each physical pair crosses on both sides with the same over/under bit
and transported arrows" — no cusp letter, signs preserved). -/
theorem typeIII_counts {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    (realize W).downCount = (realize W').downCount ∧ (realize W).writhe = (realize W').writhe := by
  obtain ⟨X, Y, m, hm, hpat⟩ := h
  have hcl := W.closed
  have hne : W.letters ≠ [] := by rcases hpat with ⟨hW, -⟩ | ⟨hW, -⟩ <;> rw [hW] <;> simp
  have hne' : W'.letters ≠ [] := by rcases hpat with ⟨-, hW'⟩ | ⟨-, hW'⟩ <;> rw [hW'] <;> simp
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rcases hpat with ⟨hW, hW'⟩ | ⟨hW, hW'⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain ⟨A, p, q, r, L, hA, rfl, rfl⟩ := run_typeIII_aux hm hP
    obtain ⟨hD₁, hD₂, hw⟩ := u1_typeIII_local (L := L) (p := p) (q := q) (r := r) hm hA
    rw [u1_downCountFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).1,
      u1_downCountFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).2,
      u1_writheFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).1,
      u1_writheFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).2, hD₁, hD₂, hw]
    exact ⟨rfl, rfl⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain ⟨A, p, q, r, L, hA, rfl, rfl⟩ := run_typeIII_aux' hm hP
    obtain ⟨hD₁, hD₂, hw⟩ := u1_typeIII_local (L := L) (p := p) (q := q) (r := r) hm hA
    rw [u1_downCountFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).1,
      u1_downCountFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).2,
      u1_writheFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).1,
      u1_writheFrom_append₃ X _ Y hX (run_typeIII_of_split hm hA).2, hD₁, hD₂, hw]
    exact ⟨rfl, rfl⟩

/-- LEAF (display ng:zigzag-counts, sm-3:2020-2022: `Δw = 0`, `ΔD ∈ {0, −2}` — "Their directions are both
downward or both upward"). -/
theorem zigzag_counts {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    (realize W).writhe = (realize W').writhe ∧
    ((realize W).downCount = (realize W').downCount ∨ (realize W).downCount = (realize W').downCount + 2) := by
  have hne : W.letters ≠ [] := h.source_ne_nil
  have hne' : W'.letters ≠ [] := IsZigzagDeletion.ne_nil h W.closed
  have hcl := W.closed
  obtain ⟨X, Y, m, d, hm, hpat, hW'⟩ := h
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rw [hW']
  rcases hpat with hW | hW
  · rw [hW] at hcl; rw [hW]
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain rfl := run_zigzag_below hm hP
    obtain ⟨hD, hw⟩ := u1_zigzag_below_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
    refine ⟨by omega, ?_⟩
    split_ifs <;> omega
  · rw [hW] at hcl; rw [hW]
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    obtain rfl := run_zigzag_above hm hP
    obtain ⟨hD, hw⟩ := u1_zigzag_above_local hm hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
    refine ⟨by omega, ?_⟩
    split_ifs <;> omega

/-- LEAF (display ng:crossed-cusp-counts, sm-3:2030-2036 "the old crossing has sign −1.  Deletion raises w by
one and flips the cusp direction ... If the old cusp was downward, ΔD = −1; otherwise ΔD = 1"). -/
theorem crossedCusp_counts {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    (realize W').writhe = (realize W).writhe + 1 ∧
    ((realize W').downCount + 1 = (realize W).downCount ∨ (realize W').downCount = (realize W).downCount + 1) := by
  obtain ⟨hne, hne'⟩ := h.ne_nil
  have hcl := W.closed
  obtain ⟨X, Y, i, hi, hpat⟩ := h
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rcases hpat with ⟨d, hW, hW'⟩ | ⟨hW, hW'⟩
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_crossedCusp_l hi hP
    obtain ⟨hD, hw, hw'⟩ := u1_crossedCusp_l_local hi hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hw, hw']
    refine ⟨by omega, ?_⟩
    rcases hD with hD | hD
    · left; omega
    · right; omega
  · rw [hW] at hcl; rw [hW, hW']
    obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
    have hP' := run_crossedCusp_r hi hP
    obtain ⟨hD, hw, hw'⟩ := u1_crossedCusp_r_local hi hP
    rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
      u1_downCountFrom_append₃ X _ Y hX hP', u1_writheFrom_append₃ X _ Y hX hP', hw, hw']
    refine ⟨by omega, ?_⟩
    rcases hD with hD | hD
    · left; omega
    · right; omega

/-- LEAF (display ng:circle-counts, sm-3:2064-2068: `D_before = D_after + 1`, "The writhe is unchanged"). -/
theorem circleDeletion_counts {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    (realize W).writhe = (realize W').writhe ∧ (realize W).downCount = (realize W').downCount + 1 := by
  have hcl := W.closed
  obtain ⟨X, Y, m, d, hm, hW, hW', hXY⟩ := h
  have hne : W.letters ≠ [] := by rw [hW]; simp
  have hne' : W'.letters ≠ [] := by rw [hW']; exact hXY
  rw [realize_downCount W hne, realize_downCount W' hne', realize_writhe W hne, realize_writhe W' hne']
  unfold OWord.downCountSyn OWord.writheSyn
  rw [hW] at hcl; rw [hW, hW']
  obtain ⟨c₀, c₁, hX, hP, -⟩ := hcl.exists_run
  obtain rfl := run_circle hm hP
  obtain ⟨hD, hw⟩ := u1_circle_local hm hP
  rw [u1_downCountFrom_append₃ X _ Y hX hP, u1_writheFrom_append₃ X _ Y hX hP,
    u1_downCountFrom_append hX, u1_writheFrom_append hX, hD, hw]
  constructor <;> omega

/-- LEAF (the (t,u) table sm-3:2107-2126 "the same downward-cusp count in all three diagrams", and
sm-3:2129-2131 "Their writhes are w₀+1, w₀−1, w₀": the two principal branches carry opposite signs at the
one crossing, so `w_A + w_{A'} = 2 w_C`; which is which is fixed by the sign of the site, `skein_site`). -/
theorem skein_counts {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    (realize A).downCount = (realize C).downCount ∧ (realize A').downCount = (realize C).downCount ∧
    (realize A).writhe + (realize A').writhe = 2 * (realize C).writhe := by
  obtain ⟨hA, hA', hC⟩ := h.ne_nil
  rw [realize_downCount A hA, realize_downCount A' hA', realize_downCount C hC, realize_writhe A hA,
    realize_writhe A' hA', realize_writhe C hC]
  unfold OWord.downCountSyn OWord.writheSyn
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, hAe, hA'e, hCe⟩ := h
  rw [hAe, hA'e]
  rw [u1_downCountFrom_append₃ X _ Y hX (run_skein_A hm hP), u1_writheFrom_append₃ X _ Y hX (run_skein_A hm hP),
    u1_downCountFrom_append₃ X _ Y hX (run_skein_A' hm hP), u1_writheFrom_append₃ X _ Y hX (run_skein_A' hm hP)]
  obtain ⟨l1, l2, l3, l4, w12, w3, w4⟩ := u1_skein_local (d := d) (a := a) (L := L) hm hP
  rcases hCe with ⟨rfl, hCe⟩ | ⟨rfl, hCe⟩
  · rw [hCe, u1_downCountFrom_append₃ X _ Y hX (run_skein_Ctop hm hP),
      u1_writheFrom_append₃ X _ Y hX (run_skein_Ctop hm hP), l1, l2, l3, w3]
    refine ⟨rfl, rfl, ?_⟩
    omega
  · rw [hCe, u1_downCountFrom_append₃ X _ Y hX (run_skein_Cbottom hm hP),
      u1_writheFrom_append₃ X _ Y hX (run_skein_Cbottom hm hP), l1, l2, l4, w4]
    refine ⟨rfl, rfl, ?_⟩
    omega

/-! ### U2 infrastructure — the record core (unit U2; PLAN_FINAL.md §4 "L-rec", §5 "U2 record core")

The abstract named record of a closed word restricted to an *active set* of `σ` slots, `U2.slotRecord`,
and the isomorphisms that connect it to the records of the realization (`U2.realizeRecordIso`,
`U2.realizeAtRecordIso`) and of any diagram on the strands of the realization with the crossings of a
set of `σ` columns (`U2.diagramRecordIso`, for the vertex-moved diagrams of U6); the exterior
correspondence of two words agreeing outside a block (`U2.φE`, β2's `shiftIdx`/`extSlot`/`next_ext`),
reduced by the block-passage hypothesis `U2.Passage` to a conjugation of first returns
(`U2.conj_of_passage`, `U2.extRecordIso`, `U2.extRecordIsoAddFree`); a constructor for full slot
bijections (`U2.slotRecordIsoOfSlotEquiv`, commutation and skein switch); and the composed isomorphisms
`U2.vertexMovedRecordIso'`, `U2.realize_recordIso_of_ext`, `U2.realize_recordIso_addFree_of_ext`.
Consumers: U3 (`comm_recordIso`, `zigzag_recordIso`, `circle_recordIso_addFree`, `skein_site`) and U6
(`typeII_move`, `typeI_move`, `crossedCusp_move`).  Report: work/drafts/frontrows/U_U2_REPORT.md. -/

namespace U2

open SM.FrontRealize SM.FrontWord.Letter Equiv

/-! #### A. First-return lemmas (pure permutation theory, extending `SM.Link` §A) -/

section FirstReturnExtra

variable {α β : Type*} [Fintype α] [Fintype β] (f : Perm α) (g : Perm β)

/-- The first return to a subset factors through the first return to a superset: the `p`-return of `a`
along `f` is the `p`-return of `a` along the first-return permutation of the superset `E ⊇ p`
(strengthened `firstReturn_pow_of_pow`: the intermediate `E`-returns sit at intermediate times). -/
theorem firstReturn_pow_of_pow_strong (E : α → Prop) [DecidablePred E] (n : ℕ) :
    ∀ (m : {m // E m}), E ((f ^ n) m.1) →
      ∃ i : ℕ, ((firstReturn f E ^ i) m).1 = (f ^ n) m.1 ∧ (0 < n → 0 < i) ∧
        ∀ j, 0 < j → j < i → ∃ t, 0 < t ∧ t < n ∧ ((firstReturn f E ^ j) m).1 = (f ^ t) m.1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro m hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · exact ⟨0, by simp, fun h => absurd h (lt_irrefl 0), fun j hj hj' => absurd hj' (by omega)⟩
    set k := returnTime f E m.1 m.2 with hk
    have hkpos : 0 < k := returnTime_pos f E m.1 m.2
    rcases lt_trichotomy n k with hlt | heq | hgt
    · exact absurd hn (returnTime_min f E m.1 m.2 hpos hlt)
    · refine ⟨1, by rw [pow_one, firstReturn_apply, ← hk, heq], fun _ => Nat.one_pos, ?_⟩
      intro j hj hj'; omega
    · have hsplit : (f ^ n) m.1 = (f ^ (n - k)) (firstReturn f E m).1 := by
        rw [firstReturn_apply, ← hk, ← Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hgt.le]
      obtain ⟨i, hi, hipos, hmid⟩ := ih (n - k) (by omega) (firstReturn f E m) (hsplit ▸ hn)
      refine ⟨i + 1, by rw [pow_succ, Perm.mul_apply, hi, hsplit], fun _ => Nat.succ_pos _, ?_⟩
      intro j hj hj'
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj1 : j = 1 := by omega
        subst hj1
        exact ⟨k, hkpos, hgt, by rw [pow_one, firstReturn_apply, ← hk]⟩
      · obtain ⟨t, ht0, htn, ht⟩ := hmid (j - 1) (by omega) (by omega)
        refine ⟨t + k, by omega, by omega, ?_⟩
        have e : (firstReturn f E ^ j) m = (firstReturn f E ^ (j - 1)) (firstReturn f E m) := by
          rw [← Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel (by omega)]
        rw [e, ht, firstReturn_apply, ← hk, ← Perm.mul_apply, ← pow_add]

/-- The first return to `p ⊆ E` along `f` is the first return to `p` along the first-return permutation
of `E`. -/
theorem firstReturn_factor (E : α → Prop) [DecidablePred E] (p : α → Prop) [DecidablePred p]
    (hpE : ∀ a, p a → E a) (a : {a // p a}) :
    (firstReturn f p a).1 =
      (firstReturn (firstReturn f E) (fun b => p b.1) ⟨⟨a.1, hpE _ a.2⟩, a.2⟩).1.1 := by
  set r := returnTime f p a.1 a.2 with hr
  have hrpos : 0 < r := returnTime_pos f p a.1 a.2
  have hrp : p ((f ^ r) a.1) := returnTime_spec f p a.1 a.2
  set b : {m // E m} := ⟨a.1, hpE _ a.2⟩ with hb
  obtain ⟨i, hi, hipos, hmid⟩ := firstReturn_pow_of_pow_strong f E r b (hpE _ hrp)
  have hi0 : 0 < i := hipos hrpos
  have hret : returnTime (firstReturn f E) (fun b => p b.1) b a.2 = i := by
    rw [returnTime_eq_iff]
    refine ⟨⟨hi0, ?_⟩, ?_⟩
    · show p ((firstReturn f E ^ i) b).1
      rw [hi]; exact hrp
    · intro j hj ⟨hj0, hjp⟩
      obtain ⟨t, ht0, htr, ht⟩ := hmid j hj0 hj
      have : p ((f ^ t) a.1) := by
        have hjp' : p ((firstReturn f E ^ j) b).1 := hjp
        rwa [ht] at hjp'
      exact returnTime_min f p a.1 a.2 ht0 htr this
  show (f ^ r) a.1 = ((firstReturn f E ^ returnTime (firstReturn f E) (fun b => p b.1) b a.2) b).1
  rw [hret, hi]

/-- A bijection conjugating `f` to `g` and carrying `p` to `q` conjugates the first returns. -/
theorem firstReturn_conj (p : α → Prop) (q : β → Prop) [DecidablePred p] [DecidablePred q]
    (φ : α ≃ β) (hφ : ∀ a, φ (f a) = g (φ a)) (hpq : ∀ a, q (φ a) ↔ p a) (a : {a // p a}) :
    (firstReturn g q ⟨φ a.1, (hpq _).2 a.2⟩).1 = φ (firstReturn f p a).1 := by
  have hpow : ∀ n (x : α), φ ((f ^ n) x) = (g ^ n) (φ x) := by
    intro n; induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [pow_succ', Perm.mul_apply, hφ, ih, pow_succ', Perm.mul_apply]
  set r := returnTime f p a.1 a.2 with hr
  have hret : returnTime g q (φ a.1) ((hpq _).2 a.2) = r := by
    rw [returnTime_eq_iff]
    refine ⟨⟨returnTime_pos f p a.1 a.2, ?_⟩, ?_⟩
    · rw [← hpow, hpq]; exact returnTime_spec f p a.1 a.2
    · intro j hj ⟨hj0, hjq⟩
      rw [← hpow, hpq] at hjq
      exact returnTime_min f p a.1 a.2 hj0 hj hjq
  show (g ^ returnTime g q (φ a.1) _) (φ a.1) = φ ((f ^ r) a.1)
  rw [hret, hpow]

/-- The first return of `f` to `E` is characterised by a path: `m` steps to an `E`-point, none before. -/
theorem firstReturn_eq_of_path (E : α → Prop) [DecidablePred E] (a : {a // E a}) {m : ℕ} (hm : 0 < m)
    (hE : E ((f ^ m) a.1)) (hmin : ∀ i, 0 < i → i < m → ¬ E ((f ^ i) a.1)) :
    (firstReturn f E a).1 = (f ^ m) a.1 := by
  have : returnTime f E a.1 a.2 = m :=
    (returnTime_eq_iff f E a.1 a.2).mpr ⟨⟨hm, hE⟩, fun j hj hj' => hmin j hj'.1 hj hj'.2⟩
  rw [firstReturn_apply, this]

/-- The return time is at most any positive period of the point. -/
theorem returnTime_le_of_pow_eq (E : α → Prop) [DecidablePred E] (a : α) (ha : E a) {k : ℕ} (hk : 0 < k)
    (h : (f ^ k) a = a) : returnTime f E a ha ≤ k :=
  Nat.find_min' (exists_return f E a ha) ⟨hk, by rw [h]; exact ha⟩

end FirstReturnExtra

/-! #### F. Conjugate first returns: transport of cycles (generic) -/

section ConjExtra

variable {α β : Type*} [Fintype α] [Fintype β] (f : Perm α) (g : Perm β)

omit [Fintype α] [Fintype β] in
theorem pow_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (n : ℕ) (x : α) :
    φ ((f ^ n) x) = (g ^ n) (φ x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Perm.mul_apply, hφ, ih, pow_succ', Perm.mul_apply]

omit [Fintype β] in
theorem sameCycle_of_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) {x y : α} (h : f.SameCycle x y) :
    g.SameCycle (φ x) (φ y) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, ← pow_conj f g hφ, hn]⟩

omit [Fintype α] [Fintype β] in
theorem conj_symm {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (b : β) : φ.symm (g b) = f (φ.symm b) := by
  apply φ.injective
  rw [Equiv.apply_symm_apply, hφ, Equiv.apply_symm_apply]

theorem sameCycle_iff_of_conj {φ : α ≃ β} (hφ : ∀ a, φ (f a) = g (φ a)) (x y : α) :
    g.SameCycle (φ x) (φ y) ↔ f.SameCycle x y := by
  refine ⟨fun h => ?_, sameCycle_of_conj f g hφ⟩
  have := sameCycle_of_conj g f (conj_symm f g hφ) h
  simpa using this

variable (E : α → Prop) (E' : β → Prop) [DecidablePred E] [DecidablePred E'] (φ : {a // E a} ≃ {b // E' b})

/-- Conjugate first returns: `E`-points lie on one `f`-cycle iff their images lie on one `g`-cycle. -/
theorem sameCycle_φ_iff (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a)) (a b : {a // E a}) :
    g.SameCycle (φ a).1 (φ b).1 ↔ f.SameCycle a.1 b.1 := by
  rw [← firstReturn_sameCycle_iff g E', ← firstReturn_sameCycle_iff f E]
  exact sameCycle_iff_of_conj (firstReturn f E) (firstReturn g E') (fun a => (conj a).symm) a b

theorem conj_symm' (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a)) (b : {b // E' b}) :
    firstReturn f E (φ.symm b) = φ.symm (firstReturn g E' b) :=
  (conj_symm (firstReturn f E) (firstReturn g E') (fun a => (conj a).symm) b).symm

/-- The first return to `p ⊆ E` is carried by a bijection conjugating the first returns to `E`, `E'`
(`firstReturn_factor` on both sides, then `firstReturn_conj`). -/
theorem firstReturn_conj_of_factor (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (p : α → Prop) (p' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpE : ∀ a, p a → E a) (hp'E' : ∀ b, p' b → E' b) (hpq : ∀ a : {a // E a}, p' (φ a).1 ↔ p a.1)
    (a : {a // p a}) :
    (firstReturn g p' ⟨(φ ⟨a.1, hpE _ a.2⟩).1, (hpq _).2 a.2⟩).1 =
      (φ ⟨(firstReturn f p a).1, hpE _ (firstReturn f p a).2⟩).1 := by
  have h1 := firstReturn_factor g E' p' hp'E' ⟨(φ ⟨a.1, hpE _ a.2⟩).1, (hpq _).2 a.2⟩
  have h2 := firstReturn_factor f E p hpE a
  have h3 := firstReturn_conj (firstReturn f E) (firstReturn g E') (fun a => p a.1) (fun b => p' b.1) φ
    (fun a => (conj a).symm) hpq ⟨⟨a.1, hpE _ a.2⟩, a.2⟩
  rw [h1]
  refine (congrArg Subtype.val h3).trans ?_
  exact congrArg (fun x => (φ x).1) (Subtype.ext h2.symm)

omit [Fintype α] [Fintype β] in
theorem sameCycle_pow (n : ℕ) (a : α) : f.SameCycle a ((f ^ n) a) := ⟨(n : ℤ), by rw [zpow_natCast]⟩

omit [Fintype α] [Fintype β] [DecidablePred E] in
/-- An `E`-point on the cycle of `a`. -/
noncomputable def repE (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) : {a // E a} :=
  ⟨(f ^ Classical.choose (hE a)) a, Classical.choose_spec (hE a)⟩

omit [Fintype α] [Fintype β] [DecidablePred E] in
theorem repE_sameCycle (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) : f.SameCycle a (repE f E hE a).1 :=
  sameCycle_pow f _ a

/-- The map of cycles induced by `φ`. -/
noncomputable def cycleMap (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) :
    Quotient (Perm.SameCycle.setoid f) → Quotient (Perm.SameCycle.setoid g) :=
  Quotient.lift (fun a => Quotient.mk (Perm.SameCycle.setoid g) (φ (repE f E hE a)).1) (by
    intro a b hab
    apply Quotient.sound
    have h : f.SameCycle (repE f E hE a).1 (repE f E hE b).1 :=
      (repE_sameCycle f E hE a).symm.trans ((show f.SameCycle a b from hab).trans (repE_sameCycle f E hE b))
    exact (sameCycle_φ_iff f g E E' φ conj _ _).2 h)

theorem cycleMap_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : {a // E a}) :
    cycleMap f g E E' φ conj hE (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ a).1 := by
  apply Quotient.sound
  exact (sameCycle_φ_iff f g E E' φ conj _ _).2 (repE_sameCycle f E hE a.1).symm

theorem cycleMap_mk' (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (a : α) :
    cycleMap f g E E' φ conj hE (Quotient.mk (Perm.SameCycle.setoid f) a) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ (repE f E hE a)).1 := rfl

/-- Conjugate first returns, every cycle meeting `E` resp. `E'`: the cycle sets correspond. -/
noncomputable def cycleEquiv (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) :
    Quotient (Perm.SameCycle.setoid f) ≃ Quotient (Perm.SameCycle.setoid g) where
  toFun := cycleMap f g E E' φ conj hE
  invFun := cycleMap g f E' E φ.symm (conj_symm' f g E E' φ conj) hE'
  left_inv o := by
    induction o using Quotient.inductionOn with
    | h a =>
      have h1 : Quotient.mk (Perm.SameCycle.setoid f) a =
          Quotient.mk (Perm.SameCycle.setoid f) (repE f E hE a).1 :=
        Quotient.sound (repE_sameCycle f E hE a)
      rw [h1, cycleMap_mk, cycleMap_mk, Equiv.symm_apply_apply]
  right_inv o := by
    induction o using Quotient.inductionOn with
    | h b =>
      have h1 : Quotient.mk (Perm.SameCycle.setoid g) b =
          Quotient.mk (Perm.SameCycle.setoid g) (repE g E' hE' b).1 :=
        Quotient.sound (repE_sameCycle g E' hE' b)
      rw [h1, cycleMap_mk, cycleMap_mk, Equiv.apply_symm_apply]

theorem cycleEquiv_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE : ∀ a : α, ∃ n : ℕ, E ((f ^ n) a)) (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (a : {a // E a}) :
    cycleEquiv f g E E' φ conj hE hE' (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      Quotient.mk (Perm.SameCycle.setoid g) (φ a).1 :=
  cycleMap_mk f g E E' φ conj hE a

open Classical in
/-- The cycles of `f` when every `g`-cycle meets `E'` and exactly one `f`-cycle `c₀` misses `E`: the
`g`-cycles plus one (`Record.addFree`, the circle deletion). -/
noncomputable def cycleEquivOption (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (c₀ : Quotient (Perm.SameCycle.setoid f))
    (hc₀ : ∀ a : α, (¬ ∃ n : ℕ, E ((f ^ n) a)) ↔ Quotient.mk (Perm.SameCycle.setoid f) a = c₀) :
    Quotient (Perm.SameCycle.setoid f) ≃ Option (Quotient (Perm.SameCycle.setoid g)) where
  toFun := Quotient.lift (fun a => if h : ∃ n : ℕ, E ((f ^ n) a) then
      some (Quotient.mk (Perm.SameCycle.setoid g)
        (φ ⟨(f ^ Classical.choose h) a, Classical.choose_spec h⟩).1) else none) (by
    intro a b hab
    have hab' : f.SameCycle a b := hab
    have hiff : (∃ n : ℕ, E ((f ^ n) a)) ↔ ∃ n : ℕ, E ((f ^ n) b) := by
      constructor
      · rintro ⟨n, hn⟩
        obtain ⟨m, hm⟩ := hab'.symm.exists_nat_pow_eq
        exact ⟨n + m, by rw [pow_add, Perm.mul_apply, hm]; exact hn⟩
      · rintro ⟨n, hn⟩
        obtain ⟨m, hm⟩ := hab'.exists_nat_pow_eq
        exact ⟨n + m, by rw [pow_add, Perm.mul_apply, hm]; exact hn⟩
    by_cases h : ∃ n : ℕ, E ((f ^ n) a)
    · have h' : ∃ n : ℕ, E ((f ^ n) b) := hiff.1 h
      simp only [h, h', ↓reduceDIte, Option.some.injEq]
      apply Quotient.sound
      apply (sameCycle_φ_iff f g E E' φ conj _ _).2
      show f.SameCycle ((f ^ Classical.choose h) a) ((f ^ Classical.choose h') b)
      exact (sameCycle_pow f (Classical.choose h) a).symm.trans
        (hab'.trans (sameCycle_pow f (Classical.choose h') b))
    · have h' : ¬ ∃ n : ℕ, E ((f ^ n) b) := fun hb => h (hiff.2 hb)
      simp only [h, h', ↓reduceDIte])
  invFun o := match o with
    | none => c₀
    | some o' => cycleMap g f E' E φ.symm (conj_symm' f g E E' φ conj) hE' o'
  left_inv o := by
    induction o using Quotient.inductionOn with
    | h a =>
      by_cases h : ∃ n : ℕ, E ((f ^ n) a)
      · simp only [Quotient.lift_mk, h, ↓reduceDIte]
        show cycleMap g f E' E φ.symm _ hE' (Quotient.mk _ (φ ⟨(f ^ Classical.choose h) a, _⟩).1) = _
        rw [cycleMap_mk, Equiv.symm_apply_apply]
        apply Quotient.sound
        exact (sameCycle_pow f (Classical.choose h) a).symm
      · simp only [Quotient.lift_mk, h, ↓reduceDIte]
        exact ((hc₀ a).1 h).symm
  right_inv o := by
    cases o with
    | none =>
      induction c₀ using Quotient.inductionOn with
      | h a₀ =>
        have : ¬ ∃ n : ℕ, E ((f ^ n) a₀) := (hc₀ a₀).2 rfl
        simp only [Quotient.lift_mk, this, ↓reduceDIte]
    | some o' =>
      induction o' using Quotient.inductionOn with
      | h b =>
        dsimp only
        rw [cycleMap_mk']
        set a : {a // E a} := φ.symm (repE g E' hE' b) with ha
        have h : ∃ n : ℕ, E ((f ^ n) a.1) := ⟨0, by simpa using a.2⟩
        simp only [Quotient.lift_mk, h, ↓reduceDIte, Option.some.injEq]
        apply Quotient.sound
        have h1 : f.SameCycle ((f ^ Classical.choose h) a.1) a.1 := (sameCycle_pow f (Classical.choose h) a.1).symm
        have h2 := (sameCycle_φ_iff f g E E' φ conj ⟨_, Classical.choose_spec h⟩ a).2 h1
        have h3 : (φ a).1 = (repE g E' hE' b).1 := by rw [ha, Equiv.apply_symm_apply]
        have h4 : g.SameCycle (φ a).1 b := by rw [h3]; exact (repE_sameCycle g E' hE' b).symm
        exact h2.trans h4

theorem cycleEquivOption_mk (conj : ∀ a, firstReturn g E' (φ a) = φ (firstReturn f E a))
    (hE' : ∀ b : β, ∃ n : ℕ, E' ((g ^ n) b)) (c₀ : Quotient (Perm.SameCycle.setoid f))
    (hc₀ : ∀ a : α, (¬ ∃ n : ℕ, E ((f ^ n) a)) ↔ Quotient.mk (Perm.SameCycle.setoid f) a = c₀)
    (a : {a // E a}) :
    cycleEquivOption f g E E' φ conj hE' c₀ hc₀ (Quotient.mk (Perm.SameCycle.setoid f) a.1) =
      some (Quotient.mk (Perm.SameCycle.setoid g) (φ a).1) := by
  have h : ∃ n : ℕ, E ((f ^ n) a.1) := ⟨0, by simpa using a.2⟩
  simp only [cycleEquivOption, Equiv.coe_fn_mk, Quotient.lift_mk, h, ↓reduceDIte, Option.some.injEq]
  apply Quotient.sound
  apply (sameCycle_φ_iff f g E E' φ conj _ _).2
  exact (sameCycle_pow f (Classical.choose h) a.1).symm


end ConjExtra


/-! #### B. The `σ` slots of a closed word: over bit, twin, sign -/

section SigmaSlots

variable {W : Word}

/-- A crossing letter is `σ` of its own index. -/
theorem letterAt_σ_of_isCrossing {k : ℕ} (h : (letterAt W k).isCrossing = true) :
    letterAt W k = .σ (letterAt W k).idx := by
  cases hℓ : letterAt W k with
  | l m d => rw [hℓ] at h; simp [isCrossing] at h
  | r m => rw [hℓ] at h; simp [isCrossing] at h
  | σ m => rfl

/-- The over bit of a slot: its piece is a descending pass (`pass p q` with `p < q`; the printed rule
"the branch with smaller dz/dx is over", `overStrand_crossingOf`). -/
def isDesc (u : Slot W) : Bool :=
  match shapeOf u with
  | .pass p q => decide (p < q)
  | _ => false

/-- A `σ` slot: the letter of its column is a crossing and its piece is one of the two crossing strands
(`pass m (m+1)` or `pass (m+1) m`).  These are exactly `σSlotA`/`σSlotB` (`isσSlot_iff`). -/
def IsσSlot (u : Slot W) : Prop :=
  (letterAt W (colOf u)).isCrossing = true ∧
    (shapeOf u = .pass (letterAt W (colOf u)).idx ((letterAt W (colOf u)).idx + 1) ∨
     shapeOf u = .pass ((letterAt W (colOf u)).idx + 1) (letterAt W (colOf u)).idx)

instance : DecidablePred (IsσSlot (W := W)) := fun u => by unfold IsσSlot; infer_instance

/-- The sign of the crossing letter of column `k` (the printed rule: positive iff the two bits agree,
`sign_crossingOf`). -/
def σsgnCol (W : Word) (k : ℕ) : SignType :=
  if bit W k (letterAt W k).idx = bit W k ((letterAt W k).idx + 1) then 1 else -1

/-- The sign carried by a `σ` slot: that of its column. -/
def σsgn (u : Slot W) : SignType := σsgnCol W (colOf u)

theorem σsgnCol_ne_zero (k : ℕ) : σsgnCol W k ≠ 0 := by
  unfold σsgnCol; split_ifs <;> decide

theorem σsgn_ne_zero (u : Slot W) : σsgn u ≠ 0 := σsgnCol_ne_zero _

theorem coe_σsgnCol (k : ℕ) :
    ((σsgnCol W k : SignType) : ℤ) =
      if bit W k (letterAt W k).idx = bit W k ((letterAt W k).idx + 1) then 1 else -1 := by
  unfold σsgnCol; split_ifs <;> rfl

variable (hW : W.Closed)
include hW

theorem isσSlot_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    IsσSlot (σSlotA hW hk hℓ) := by
  obtain ⟨hc, hs, -⟩ := σSlotA_spec hW hk hℓ
  refine ⟨?_, Or.inl ?_⟩
  · rw [hc, hℓ]; rfl
  · rw [hc, hℓ, hs]; rfl

theorem isσSlot_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    IsσSlot (σSlotB hW hk hℓ) := by
  obtain ⟨hc, hs, -⟩ := σSlotB_spec hW hk hℓ
  refine ⟨?_, Or.inr ?_⟩
  · rw [hc, hℓ]; rfl
  · rw [hc, hℓ, hs]; rfl

theorem isDesc_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    isDesc (σSlotA hW hk hℓ) = true := by
  unfold isDesc; rw [(σSlotA_spec hW hk hℓ).2.1]; simp

theorem isDesc_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    isDesc (σSlotB hW hk hℓ) = false := by
  unfold isDesc; rw [(σSlotB_spec hW hk hℓ).2.1]; simp

/-- The column of a slot is a real column. -/
theorem colOf_lt (u : Slot W) : colOf u < W.length := (piece_spec .std hW u).1

/-- A `σ` slot is `σSlotA` or `σSlotB` of its column. -/
theorem eq_σSlotA_or_σSlotB {u : Slot W} (hu : IsσSlot u) :
    u = σSlotA hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1) ∨
    u = σSlotB hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1) := by
  obtain ⟨hA1, hA2, -⟩ := σSlotA_spec hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1)
  obtain ⟨hB1, hB2, -⟩ := σSlotB_spec hW (colOf_lt hW u) (letterAt_σ_of_isCrossing hu.1)
  rcases hu.2 with h | h
  · left; exact slot_eq_of_piece_eq hW .std hA1.symm (h.trans hA2.symm)
  · right; exact slot_eq_of_piece_eq hW .std hB1.symm (h.trans hB2.symm)

theorem isσSlot_iff (u : Slot W) :
    IsσSlot u ↔ ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      u = σSlotA hW hk hℓ ∨ u = σSlotB hW hk hℓ := by
  constructor
  · intro hu
    exact ⟨_, _, colOf_lt hW u, letterAt_σ_of_isCrossing hu.1, eq_σSlotA_or_σSlotB hW hu⟩
  · rintro ⟨k, m, hk, hℓ, rfl | rfl⟩
    · exact isσSlot_σSlotA hW hk hℓ
    · exact isσSlot_σSlotB hW hk hℓ

/-- Two `σ` slots of one column with the same over bit coincide. -/
theorem σslot_ext {u v : Slot W} (hu : IsσSlot u) (hv : IsσSlot v) (hc : colOf u = colOf v)
    (hd : isDesc u = isDesc v) : u = v := by
  apply slot_eq_of_piece_eq hW .std hc
  have hu2 := hu.2
  have hv2 := hv.2
  rw [hc] at hu2
  rcases hu2 with h1 | h1 <;> rcases hv2 with h2 | h2 <;> simp [isDesc, h1, h2] at hd ⊢

omit hW in
theorem isDesc_eq_true_iff {u : Slot W} (hu : IsσSlot u) :
    isDesc u = true ↔ shapeOf u = .pass (letterAt W (colOf u)).idx ((letterAt W (colOf u)).idx + 1) := by
  unfold isDesc
  rcases hu.2 with h | h <;> rw [h] <;> simp

/-- The twin of a `σ` slot: the other crossing strand of its column (the identity on other slots). -/
noncomputable def σtwin (u : Slot W) : Slot W :=
  if h : (letterAt W (colOf u)).isCrossing = true then
    if isDesc u then σSlotB hW (colOf_lt hW u) (letterAt_σ_of_isCrossing h)
    else σSlotA hW (colOf_lt hW u) (letterAt_σ_of_isCrossing h)
  else u

theorem σtwin_spec {u : Slot W} (hu : IsσSlot u) :
    colOf (σtwin hW u) = colOf u ∧ IsσSlot (σtwin hW u) ∧ isDesc (σtwin hW u) = !isDesc u := by
  unfold σtwin
  simp only [hu.1, ↓reduceDIte]
  cases hd : isDesc u
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    exact ⟨(σSlotA_spec hW _ _).1, isσSlot_σSlotA hW _ _, isDesc_σSlotA hW _ _⟩
  · simp only [↓reduceIte, Bool.not_true]
    exact ⟨(σSlotB_spec hW _ _).1, isσSlot_σSlotB hW _ _, isDesc_σSlotB hW _ _⟩

theorem colOf_σtwin {u : Slot W} (hu : IsσSlot u) : colOf (σtwin hW u) = colOf u := (σtwin_spec hW hu).1

theorem isσSlot_σtwin {u : Slot W} (hu : IsσSlot u) : IsσSlot (σtwin hW u) := (σtwin_spec hW hu).2.1

theorem isDesc_σtwin {u : Slot W} (hu : IsσSlot u) : isDesc (σtwin hW u) = !isDesc u :=
  (σtwin_spec hW hu).2.2

theorem σtwin_σtwin {u : Slot W} (hu : IsσSlot u) : σtwin hW (σtwin hW u) = u := by
  have h1 := σtwin_spec hW hu
  have h2 := σtwin_spec hW h1.2.1
  apply σslot_ext hW h2.2.1 hu (h2.1.trans h1.1)
  rw [h2.2.2, h1.2.2, Bool.not_not]

theorem σtwin_ne {u : Slot W} (hu : IsσSlot u) : σtwin hW u ≠ u := by
  intro h
  have := isDesc_σtwin hW hu
  rw [h] at this
  cases isDesc u <;> simp at this

theorem σsgn_σtwin {u : Slot W} (hu : IsσSlot u) : σsgn (σtwin hW u) = σsgn u := by
  unfold σsgn; rw [colOf_σtwin hW hu]

theorem σtwin_σSlotA {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    σtwin hW (σSlotA hW hk hℓ) = σSlotB hW hk hℓ := by
  have hA := isσSlot_σSlotA hW hk hℓ
  apply σslot_ext hW (isσSlot_σtwin hW hA) (isσSlot_σSlotB hW hk hℓ)
  · rw [colOf_σtwin hW hA, (σSlotA_spec hW hk hℓ).1, (σSlotB_spec hW hk hℓ).1]
  · rw [isDesc_σtwin hW hA, isDesc_σSlotA hW hk hℓ, isDesc_σSlotB hW hk hℓ]; rfl

theorem σtwin_σSlotB {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    σtwin hW (σSlotB hW hk hℓ) = σSlotA hW hk hℓ := by
  rw [← σtwin_σSlotA hW hk hℓ, σtwin_σtwin hW (isσSlot_σSlotA hW hk hℓ)]

/-- The sign of a `σ` slot is β1's `signBit` of its letter at its cut. -/
theorem coe_σsgn_eq_signBit {u : Slot W} (hu : IsσSlot u) :
    ((σsgn u : SignType) : ℤ) = (letterAt W (colOf u)).signBit (cut W (colOf u)) := by
  unfold σsgn
  rw [coe_σsgnCol]
  have hℓ := letterAt_σ_of_isCrossing hu.1
  conv_rhs => rw [hℓ]
  rw [signBit_σ hW (colOf_lt hW u) hℓ]

/-- The sign of a `σ` slot is the geometric sign of its crossing. -/
theorem coe_σsgn_σSlotA (pl : Placement) (hne : W ≠ []) {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    ((σsgn (σSlotA hW hk hℓ) : SignType) : ℤ) =
      ((realizeAt pl hW hne).diagram.sign (crossingOf pl hW hne hk hℓ) : ℤ) := by
  rw [sign_crossingOf, σsgn, (σSlotA_spec hW hk hℓ).1, coe_σsgnCol, hℓ]; rfl

end SigmaSlots

/-! #### C. The slot record of a closed word restricted to an active set of `σ` slots -/

section SlotRecord

variable {W : Word} (hW : W.Closed)

/-- The component of a slot: the component index of its strand (the `comp` field). -/
noncomputable def slotComp (u : Slot W) : Fin (numComp hW) := ((idxEquiv hW).symm u).1

theorem slotComp_eq_iff (u v : Slot W) :
    slotComp hW u = slotComp hW v ↔ (nextPerm hW).SameCycle u v := by
  have := toSlot_fst_eq_iff hW ((idxEquiv hW).symm u) ((idxEquiv hW).symm v)
  rw [← idxEquiv_apply, ← idxEquiv_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
  exact this

theorem slotComp_idxEquiv (s : Idx hW) : slotComp hW (idxEquiv hW s) = s.1 := by
  show ((idxEquiv hW).symm (idxEquiv hW s)).1 = s.1
  rw [Equiv.symm_apply_apply]

/-- The component of a slot is its orbit, numbered by `Fintype.equivFin`. -/
theorem slotComp_eq_equivFin (u : Slot W) :
    slotComp hW u = Fintype.equivFin (Orbit hW) (orbitOf hW u) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (idxEquiv hW).surjective u
  rw [slotComp_idxEquiv]
  have : orbitOf hW (idxEquiv hW ⟨i, j⟩) = orbitOf hW (rep hW i) := by
    rw [orbitOf_eq_iff]
    exact sameCycle_of_iterate hW (s := idxEquiv hW ⟨i, j⟩) (t := rep hW i) (a := 0) (b := j.val) rfl
  rw [this, orbitOf_rep, Equiv.apply_symm_apply]

/-- An *active set* of slots: `σ` slots, closed under the twin. -/
structure ActiveSet (S : Slot W → Prop) : Prop where
  isσ : ∀ u, S u → IsσSlot u
  twin : ∀ u, S u → S (σtwin hW u)

variable (S : Slot W → Prop) [DecidablePred S] (hS : ActiveSet hW S)

/-- The pairing of the active slots: the twin. -/
noncomputable def slotPair : Perm {u : Slot W // S u} where
  toFun u := ⟨σtwin hW u.1, hS.twin _ u.2⟩
  invFun u := ⟨σtwin hW u.1, hS.twin _ u.2⟩
  left_inv u := Subtype.ext (σtwin_σtwin hW (hS.isσ _ u.2))
  right_inv u := Subtype.ext (σtwin_σtwin hW (hS.isσ _ u.2))

/-- THE ABSTRACT NAMED RECORD of a closed word `W` restricted to the active set `S` of `σ` slots
(def:gauss-record read on the slot cycle of the realization):
* `comps := Fin (numComp hW)` — the components (cycles of `next`), crossing-free ones included;
* `M := {u // S u}` — the active slots (one occurrence per crossing strand);
* `comp` — the component of the slot's strand;
* `succ := firstReturn (nextPerm hW) S` — the next active slot along the slot cycle `next`;
* `pair := σtwin` — the other crossing strand of the column;
* `isOver := isDesc` — the descending strand is over;
* `sgn := σsgn` — positive iff the two bits of the column agree (β1's `signBit`). -/
noncomputable def slotRecord : Record where
  comps := Fin (numComp hW)
  M := {u : Slot W // S u}
  comp u := slotComp hW u.1
  succ := firstReturn (nextPerm hW) S
  pair := slotPair hW S hS
  isOver u := isDesc u.1
  sgn u := σsgn u.1
  succ_comp u := (slotComp_eq_iff hW _ _).2 (sameCycle_firstReturn_apply (nextPerm hW) S u).symm
  succ_cycle _ _ h := firstReturn_sameCycle_of_sameCycle _ _ ((slotComp_eq_iff hW _ _).1 h)
  pair_ne u h := σtwin_ne hW (hS.isσ _ u.2) (congrArg Subtype.val h)
  pair_invol u := Subtype.ext (σtwin_σtwin hW (hS.isσ _ u.2))
  bit_pair u := isDesc_σtwin hW (hS.isσ _ u.2)
  sgn_pair u := σsgn_σtwin hW (hS.isσ _ u.2)
  sgn_ne u := σsgn_ne_zero u.1

@[simp] theorem slotRecord_comps : (slotRecord hW S hS).comps = Fin (numComp hW) := rfl
@[simp] theorem slotRecord_M : (slotRecord hW S hS).M = {u : Slot W // S u} := rfl
theorem slotRecord_comp (u : {u : Slot W // S u}) : (slotRecord hW S hS).comp u = slotComp hW u.1 := rfl
theorem slotRecord_succ : (slotRecord hW S hS).succ = firstReturn (nextPerm hW) S := rfl
theorem slotRecord_succ_val (u : {u : Slot W // S u}) :
    ((slotRecord hW S hS).succ u).1 = ((nextPerm hW) ^ returnTime (nextPerm hW) S u.1 u.2) u.1 := rfl
theorem slotRecord_pair_val (u : {u : Slot W // S u}) :
    ((slotRecord hW S hS).pair u).1 = σtwin hW u.1 := rfl
theorem slotRecord_isOver (u : {u : Slot W // S u}) : (slotRecord hW S hS).isOver u = isDesc u.1 := rfl
theorem slotRecord_sgn (u : {u : Slot W // S u}) : (slotRecord hW S hS).sgn u = σsgn u.1 := rfl

/-- Two pointwise-equivalent active sets give isomorphic slot records. -/
noncomputable def slotRecordCongr (S' : Slot W → Prop) [DecidablePred S'] (hS' : ActiveSet hW S')
    (h : ∀ u, S u ↔ S' u) : RecordIso (slotRecord hW S hS) (slotRecord hW S' hS') where
  e := Equiv.refl _
  Φ := Equiv.subtypeEquivRight h
  comp_eq _ := rfl
  succ_eq u := by
    apply Subtype.ext
    exact (firstReturn_conj (nextPerm hW) (nextPerm hW) S S' (Equiv.refl _) (fun _ => rfl) (fun a => (h a).symm) u).symm
  pair_eq _ := rfl
  bit_eq _ := rfl
  sgn_eq _ := rfl

end SlotRecord

/-! #### D. The record of a diagram on the strands of a realization -/

section DiagramIso

/-- Visits are determined by their crossing and their strand. -/
theorem visit_ext {Γ : Shadow} {v w : Γ.Visit} (h1 : v.1 = w.1) (h2 : v.2.val = w.2.val) : v = w := by
  obtain ⟨x, s, hs⟩ := v
  obtain ⟨y, t, ht⟩ := w
  cases h1
  cases (Subtype.ext h2 : (⟨s, hs⟩ : {s // s ∈ x.val}) = ⟨t, ht⟩)
  rfl

theorem signType_ext_int {a b : SignType} (h : ((a : SignType) : ℤ) = b) : a = b := by
  cases a <;> cases b <;> first | rfl | (exfalso; revert h; decide)

/-- Real cyclic betweenness of integer parts plus fractional parts in `[0,1)` is cyclic betweenness of the
integer parts (distinct integers). -/
theorem cycBetween_nat_add {A B C : ℕ} (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) {α β γ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    cycBetween (A + α) (B + β) (C + γ) ↔ ((A < B ∧ B < C) ∨ (B < C ∧ C < A) ∨ (C < A ∧ A < B)) := by
  have key : ∀ (x y : ℕ) (ξ η : ℝ), x ≠ y → 0 ≤ ξ → ξ < 1 → 0 ≤ η → η < 1 →
      ((x : ℝ) + ξ < y + η ↔ x < y) := by
    intro x y ξ η hxy hξ0 hξ1 hη0 hη1
    rcases lt_or_gt_of_ne hxy with h | h
    · have : (x : ℝ) + 1 ≤ y := by exact_mod_cast h
      exact iff_of_true (by linarith) h
    · have : (y : ℝ) + 1 ≤ x := by exact_mod_cast h
      exact iff_of_false (by linarith) (by omega)
  unfold cycBetween
  rw [key A B α β hAB hα0 hα1 hβ0 hβ1, key B C β γ hBC hβ0 hβ1 hγ0 hγ1, key C A γ α hAC.symm hγ0 hγ1 hα0 hα1]

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])

/-- The active set of an admissible set `K` of columns: the `σ` slots whose column lies in `K`. -/
def colActive (K : ℕ → Prop) (u : Slot W) : Prop := IsσSlot u ∧ K (colOf u)

instance (K : ℕ → Prop) [DecidablePred K] : DecidablePred (colActive (W := W) K) := fun _ => by
  unfold colActive; infer_instance

theorem colActive_activeSet (K : ℕ → Prop) : ActiveSet hW (colActive K) where
  isσ _ hu := hu.1
  twin u hu := ⟨isσSlot_σtwin hW hu.1, by rw [colOf_σtwin hW hu.1]; exact hu.2⟩

theorem colActive_σSlotA {K : ℕ → Prop} {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    colActive K (σSlotA hW hk hℓ) := ⟨isσSlot_σSlotA hW hk hℓ, by rw [(σSlotA_spec hW hk hℓ).1]; exact hK⟩

theorem colActive_σSlotB {K : ℕ → Prop} {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    colActive K (σSlotB hW hk hℓ) := ⟨isσSlot_σSlotB hW hk hℓ, by rw [(σSlotB_spec hW hk hℓ).1]; exact hK⟩

variable (V : (shadowOf pl hW hne).Vertices)

/-- A slot as a strand of the re-vertexed shadow (`Idx hW` is its strand type). -/
noncomputable def stStrand (u : Slot W) : ((shadowOf pl hW hne).withVertices V).Strand := (idxEquiv hW).symm u

@[simp] theorem idxEquiv_stStrand (u : Slot W) : idxEquiv hW (stStrand pl hW hne V u) = u :=
  Equiv.apply_symm_apply _ _

@[simp] theorem stStrand_idxEquiv (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    stStrand pl hW hne V (idxEquiv hW s) = s := Equiv.symm_apply_apply _ _

theorem stStrand_injective : Function.Injective (stStrand pl hW hne V) := (idxEquiv hW).symm.injective

/-- A strand of the re-vertexed shadow as a strand index (the identity, typed). -/
def strIdx (s : ((shadowOf pl hW hne).withVertices V).Strand) : Idx hW := s

theorem idxEquiv_strIdx (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    idxEquiv hW (strIdx pl hW hne V s) = idxEquiv hW s := rfl

theorem strIdx_stStrand (u : Slot W) : strIdx pl hW hne V (stStrand pl hW hne V u) = (idxEquiv hW).symm u := rfl

theorem eq_stStrand_iff (s : ((shadowOf pl hW hne).withVertices V).Strand) (u : Slot W) :
    s = stStrand pl hW hne V u ↔ idxEquiv hW s = u := Equiv.eq_symm_apply _

variable (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
  (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
  (hov : ∀ x, ov x ∈ x.val)

/-- A diagram on the re-vertexed shadow of a realization (the vertex-moved diagrams of the geometric rows;
the realization itself is `V := vertices`). -/
noncomputable abbrev mkDiagram : Diagram := ⟨(shadowOf pl hW hne).withVertices V, hgen, ov, hov⟩

local notation "𝔇" => mkDiagram pl hW hne V hgen ov hov

/-- The crossing pair of the `σ` letter at column `k`, as strands (`Idx hW` is the strand type of every
re-vertexed shadow of the realization). -/
noncomputable abbrev σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    Finset ((shadowOf pl hW hne).withVertices V).Strand :=
  {stStrand pl hW hne V (σSlotA hW hk hℓ), stStrand pl hW hne V (σSlotB hW hk hℓ)}

theorem mem_σpair_A {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    stStrand pl hW hne V (σSlotA hW hk hℓ) ∈ σpair pl hW hne V hk hℓ := Finset.mem_insert_self _ _

theorem mem_σpair_B {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) :
    stStrand pl hW hne V (σSlotB hW hk hℓ) ∈ σpair pl hW hne V hk hℓ :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem mem_σpair_iff {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    (s : ((shadowOf pl hW hne).withVertices V).Strand) :
    s ∈ σpair pl hW hne V hk hℓ ↔ idxEquiv hW s = σSlotA hW hk hℓ ∨ idxEquiv hW s = σSlotB hW hk hℓ := by
  simp only [σpair, Finset.mem_insert, Finset.mem_singleton, eq_stStrand_iff]

theorem colOf_of_mem_σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    {s : ((shadowOf pl hW hne).withVertices V).Strand} (hs : s ∈ σpair pl hW hne V hk hℓ) :
    colOf (idxEquiv hW s) = k := by
  rcases (mem_σpair_iff pl hW hne V hk hℓ s).1 hs with h | h <;> rw [h]
  · exact (σSlotA_spec hW hk hℓ).1
  · exact (σSlotB_spec hW hk hℓ).1

variable (K : ℕ → Prop)

/-- The data making `mkDiagram` a diagram "with the shadow structure of `realize W` and the crossings of
the active columns `K`": its crossings are exactly the `σ` pairs of the columns in `K`, the over strand
of each is the descending strand, and the sign is the printed sign of the letter. -/
structure SlotDiagramData : Prop where
  cross : ∀ x : Finset ((shadowOf pl hW hne).withVertices V).Strand,
    ((shadowOf pl hW hne).withVertices V).IsCrossing x ↔
      ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k ∧ x = σpair pl hW hne V hk hℓ
  overStrand : ∀ (x : ((shadowOf pl hW hne).withVertices V).Crossing) (k m : ℕ) (hk : k < W.length)
    (hℓ : letterAt W k = .σ m), x.val = σpair pl hW hne V hk hℓ → ov x = stStrand pl hW hne V (σSlotA hW hk hℓ)
  sgn : ∀ (x : ((shadowOf pl hW hne).withVertices V).Crossing) (k m : ℕ) (hk : k < W.length)
    (hℓ : letterAt W k = .σ m), x.val = σpair pl hW hne V hk hℓ →
    ((mkDiagram pl hW hne V hgen ov hov).sign x : ℤ) = if bit W k m = bit W k (m + 1) then 1 else -1

variable (data : SlotDiagramData pl hW hne V hgen ov hov K)
include data

/-- The crossing of an active column. -/
noncomputable def σcross {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing :=
  ⟨σpair pl hW hne V hk hℓ, (data.cross _).2 ⟨k, m, hk, hℓ, hK, rfl⟩⟩

theorem σcross_val {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (hK : K k) :
    (σcross pl hW hne V hgen ov hov K data hk hℓ hK).val = σpair pl hW hne V hk hℓ := rfl

/-- The strand of a visit is an active `σ` slot. -/
theorem visit_active (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    colActive K (idxEquiv hW v.2.val) := by
  obtain ⟨k, m, hk, hℓ, hK, hx⟩ := (data.cross v.1.val).1 v.1.2
  have hs : v.2.val ∈ σpair pl hW hne V hk hℓ := hx ▸ v.2.2
  rcases (mem_σpair_iff pl hW hne V hk hℓ _).1 hs with h | h <;> rw [h]
  · exact colActive_σSlotA hW hk hℓ hK
  · exact colActive_σSlotB hW hk hℓ hK

/-- A strand lies in at most one crossing. -/
theorem crossing_eq_of_mem {x y : (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing}
    {s : (mkDiagram pl hW hne V hgen ov hov).Γ.Strand} (hx : s ∈ x.val) (hy : s ∈ y.val) : x = y := by
  obtain ⟨k, m, hk, hℓ, -, ex⟩ := (data.cross x.val).1 x.2
  obtain ⟨k', m', hk', hℓ', -, ey⟩ := (data.cross y.val).1 y.2
  have hkk : k = k' :=
    (colOf_of_mem_σpair pl hW hne V hk hℓ (ex ▸ hx)).symm.trans (colOf_of_mem_σpair pl hW hne V hk' hℓ' (ey ▸ hy))
  subst hkk
  have hmm : m = m' := Letter.σ.inj (hℓ.symm.trans hℓ')
  subst hmm
  exact Subtype.ext (ex.trans ey.symm)

/-- The visit of an active slot. -/
noncomputable def toVisit (u : {u : Slot W // colActive K u}) : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit :=
  ⟨σcross pl hW hne V hgen ov hov K data (colOf_lt hW u.1) (letterAt_σ_of_isCrossing u.2.1.1) u.2.2,
    ⟨stStrand pl hW hne V u.1, by
      rw [σcross_val, mem_σpair_iff, idxEquiv_stStrand]
      exact eq_σSlotA_or_σSlotB hW u.2.1⟩⟩

theorem toVisit_strand (u : {u : Slot W // colActive K u}) :
    (toVisit pl hW hne V hgen ov hov K data u).2.val = stStrand pl hW hne V u.1 := rfl

/-- The visits of the diagram are the active slots. -/
noncomputable def visitEquiv : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit ≃ {u : Slot W // colActive K u} where
  toFun v := ⟨idxEquiv hW v.2.val, visit_active pl hW hne V hgen ov hov K data v⟩
  invFun := toVisit pl hW hne V hgen ov hov K data
  left_inv v := by
    apply visit_ext
    · refine crossing_eq_of_mem pl hW hne V hgen ov hov K data (s := v.2.val) ?_ v.2.2
      have h := (toVisit pl hW hne V hgen ov hov K data
        ⟨idxEquiv hW v.2.val, visit_active pl hW hne V hgen ov hov K data v⟩).2.2
      rwa [toVisit_strand, stStrand_idxEquiv] at h
    · rw [toVisit_strand, stStrand_idxEquiv]
  right_inv u := Subtype.ext (by
    show idxEquiv hW (toVisit pl hW hne V hgen ov hov K data u).2.val = u.1
    rw [toVisit_strand, idxEquiv_stStrand])

theorem visitEquiv_apply_val (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (visitEquiv pl hW hne V hgen ov hov K data v).1 = idxEquiv hW v.2.val := rfl

theorem visitEquiv_symm_apply (u : {u : Slot W // colActive K u}) :
    (visitEquiv pl hW hne V hgen ov hov K data).symm u = toVisit pl hW hne V hgen ov hov K data u := rfl

/-- The other strand of a crossing is the twin slot. -/
theorem slot_other {x : (mkDiagram pl hW hne V hgen ov hov).Γ.Crossing}
    {s : (mkDiagram pl hW hne V hgen ov hov).Γ.Strand} (hs : s ∈ x.val) :
    idxEquiv hW (((shadowOf pl hW hne).withVertices V).other x hs) = σtwin hW (idxEquiv hW s) := by
  obtain ⟨k, m, hk, hℓ, -, ex⟩ := (data.cross x.val).1 x.2
  have hs' : s ∈ σpair pl hW hne V hk hℓ := ex ▸ hs
  have hAB : stStrand pl hW hne V (σSlotA hW hk hℓ) ≠ stStrand pl hW hne V (σSlotB hW hk hℓ) :=
    fun h => σSlotA_ne_σSlotB hW hk hℓ (stStrand_injective pl hW hne V h)
  rcases (mem_σpair_iff pl hW hne V hk hℓ s).1 hs' with h | h
  · have hsA : s = stStrand pl hW hne V (σSlotA hW hk hℓ) := (eq_stStrand_iff pl hW hne V _ _).2 h
    have : stStrand pl hW hne V (σSlotB hW hk hℓ) = ((shadowOf pl hW hne).withVertices V).other x hs :=
      ((shadowOf pl hW hne).withVertices V).eq_other_of_mem_of_ne x hs
        (by rw [ex]; exact mem_σpair_B pl hW hne V hk hℓ) (by rw [hsA]; exact hAB.symm)
    rw [← this, idxEquiv_stStrand, h, σtwin_σSlotA]
  · have hsB : s = stStrand pl hW hne V (σSlotB hW hk hℓ) := (eq_stStrand_iff pl hW hne V _ _).2 h
    have : stStrand pl hW hne V (σSlotA hW hk hℓ) = ((shadowOf pl hW hne).withVertices V).other x hs :=
      ((shadowOf pl hW hne).withVertices V).eq_other_of_mem_of_ne x hs
        (by rw [ex]; exact mem_σpair_A pl hW hne V hk hℓ) (by rw [hsB]; exact hAB)
    rw [← this, idxEquiv_stStrand, h, σtwin_σSlotB]

/-- The over bit of a visit is the descent bit of its slot. -/
theorem overBit_eq (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).overBit v = isDesc (idxEquiv hW v.2.val) := by
  obtain ⟨k, m, hk, hℓ, -, ex⟩ := (data.cross v.1.val).1 v.1.2
  have hs : v.2.val ∈ σpair pl hW hne V hk hℓ := ex ▸ v.2.2
  have hover : (mkDiagram pl hW hne V hgen ov hov).overStrand v.1 = stStrand pl hW hne V (σSlotA hW hk hℓ) :=
    data.overStrand v.1 k m hk hℓ ex
  unfold Diagram.overBit
  rw [hover]
  rcases (mem_σpair_iff pl hW hne V hk hℓ _).1 hs with h | h
  · rw [h, isDesc_σSlotA]
    exact decide_eq_true ((eq_stStrand_iff pl hW hne V _ _).2 h)
  · rw [h, isDesc_σSlotB]
    refine decide_eq_false (fun e => σSlotA_ne_σSlotB hW hk hℓ ?_)
    rw [← h, e, idxEquiv_stStrand]

/-- The sign of a visit is the `σ` sign of its slot. -/
theorem sign_eq (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).sign v.1 = σsgn (idxEquiv hW v.2.val) := by
  obtain ⟨k, m, hk, hℓ, -, ex⟩ := (data.cross v.1.val).1 v.1.2
  have hcol : colOf (idxEquiv hW v.2.val) = k := colOf_of_mem_σpair pl hW hne V hk hℓ (ex ▸ v.2.2)
  apply signType_ext_int
  rw [data.sgn v.1 k m hk hℓ ex, σsgn, hcol, coe_σsgnCol, hℓ]; rfl

/-- Two visits with the same strand coincide (a strand lies in at most one crossing). -/
theorem visit_eq_of_strand_eq {w w' : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit}
    (h : w.2.val = w'.2.val) : w = w' :=
  visit_ext (crossing_eq_of_mem pl hW hne V hgen ov hov K data (h ▸ w.2.2) w'.2.2) h

omit data in
/-- Moving `n` steps along a component is `n` applications of `next`. -/
theorem idxEquiv_add (i : Fin (numComp hW)) (a : ZMod (period hW (rep hW i))) (n : ℕ) :
    idxEquiv hW ⟨i, a + n⟩ = (next hW)^[n] (idxEquiv hW ⟨i, a⟩) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, Nat.cast_succ, ← add_assoc]
    exact toSlot_succ hW i (a + n)

omit data in
theorem nextPerm_pow_apply (n : ℕ) (u : Slot W) : ((nextPerm hW) ^ n) u = (next hW)^[n] u := by
  rw [Equiv.Perm.coe_pow]; rfl

omit data in
/-- The traversal coordinate of a visit: its strand's label plus its crossing parameter. -/
theorem visitCoord_eq (w : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).visitCoord w =
      ((w.2.val.2.val : ℕ) : ℝ) + ((mkDiagram pl hW hne V hgen ov hov).visitPt w).2.2.val := rfl

omit data in
/-- The traversal coordinate of a visit whose strand is `⟨i, b⟩` (as a strand index). -/
theorem visitCoord_eq_of (w : (𝔇).Γ.Visit) {i : Fin (numComp hW)} {b : ZMod (period hW (rep hW i))}
    (h : strIdx pl hW hne V w.2.val = ⟨i, b⟩) :
    (𝔇).visitCoord w = ((b.val : ℕ) : ℝ) + ((𝔇).visitPt w).2.2.val := by
  have e : (w.2.val.2.val : ℕ) = b.val := by
    have := congrArg (fun s : Idx hW => s.2.val) h
    exact this
  rw [visitCoord_eq, e]

omit data in
/-- The component of a visit whose strand is `⟨i, b⟩`. -/
theorem compOf_eq_of (w : (𝔇).Γ.Visit) {i : Fin (numComp hW)} {b : ZMod (period hW (rep hW i))}
    (h : strIdx pl hW hne V w.2.val = ⟨i, b⟩) : (𝔇).compOf w = i := by
  have := congrArg Sigma.fst h
  exact this

/-- THE SUCCESSOR LAW: the forward successor of a visit is the first return of the slot cycle `next` to
the active slots (each strand carries at most one visit, so the traversal order of the visits on a
component is the cyclic order of their strands). -/
theorem nextVisit_eq [DecidablePred K] (v : (mkDiagram pl hW hne V hgen ov hov).Γ.Visit) :
    (mkDiagram pl hW hne V hgen ov hov).nextVisit v =
      toVisit pl hW hne V hgen ov hov K data
        (firstReturn (nextPerm hW) (colActive K) (visitEquiv pl hW hne V hgen ov hov K data v)) := by
  set S : Slot W → Prop := colActive (W := W) K with hSdef
  set u₀ : {u : Slot W // S u} := visitEquiv pl hW hne V hgen ov hov K data v with hu₀
  obtain ⟨i, a, hva⟩ : ∃ (i : Fin (numComp hW)) (a : ZMod (period hW (rep hW i))),
      strIdx pl hW hne V v.2.val = ⟨i, a⟩ := ⟨_, _, rfl⟩
  have hu₀v : u₀.1 = idxEquiv hW ⟨i, a⟩ := by
    show idxEquiv hW (strIdx pl hW hne V v.2.val) = _
    rw [hva]
  set n := returnTime (nextPerm hW) S u₀.1 u₀.2 with hn
  have hn0 : 0 < n := returnTime_pos _ _ _ _
  have hmin : ∀ j, 0 < j → j < n → ¬ S (((nextPerm hW) ^ j) u₀.1) :=
    fun j hj hjn => returnTime_min _ _ _ _ hj hjn
  have hfr : (firstReturn (nextPerm hW) S u₀).1 = ((nextPerm hW) ^ n) u₀.1 := rfl
  have hk3 : 3 ≤ period hW (rep hW i) := three_le_period hW _
  have hkpos : 0 < period hW (rep hW i) := by omega
  have hpow : ∀ j : ℕ, ((nextPerm hW) ^ j) u₀.1 = idxEquiv hW ⟨i, a + j⟩ := by
    intro j; rw [nextPerm_pow_apply, idxEquiv_add, hu₀v]
  have hnk : n ≤ period hW (rep hW i) := by
    apply returnTime_le_of_pow_eq (nextPerm hW) S u₀.1 u₀.2 hkpos
    rw [hpow, hu₀v, ZMod.natCast_self, add_zero]
  set w := toVisit pl hW hne V hgen ov hov K data (firstReturn (nextPerm hW) S u₀) with hw
  have hw2 : strIdx pl hW hne V w.2.val = ⟨i, a + n⟩ := by
    show strIdx pl hW hne V (stStrand pl hW hne V (firstReturn (nextPerm hW) S u₀).1) = _
    rw [strIdx_stStrand, hfr, hpow]
    exact Equiv.symm_apply_apply _ _
  -- every visit of the component sits `j` steps after `v`, at an active slot
  have hcomp : ∀ (b : ZMod (period hW (rep hW i))), ∃ j : ℕ, j < period hW (rep hW i) ∧ b = a + j := by
    intro b
    exact ⟨(b - a).val, ZMod.val_lt _, by rw [ZMod.natCast_zmod_val, add_sub_cancel]⟩
  have hno : ∀ (u' : (𝔇).Γ.Visit) (b : ZMod (period hW (rep hW i))), strIdx pl hW hne V u'.2.val = ⟨i, b⟩ →
      ∀ j : ℕ, b = a + j → 0 < j → j < n → False := by
    intro u' b hub j hb hj hjn
    apply hmin j hj hjn
    rw [hpow, ← hb, ← hub, idxEquiv_strIdx]
    exact visit_active pl hW hne V hgen ov hov K data u'
  have hcast_ne : ∀ j : ℕ, 0 < j → j < period hW (rep hW i) → (j : ZMod (period hW (rep hW i))) ≠ 0 := by
    intro j hj hjk h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hj h) (not_le.2 hjk)
  have hcast_inj : ∀ j j' : ℕ, j < period hW (rep hW i) → j' < period hW (rep hW i) →
      (j : ZMod (period hW (rep hW i))) = j' → j = j' := by
    intro j j' hj hj' h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at this
  have hvisit_eq : ∀ (u' u'' : (𝔇).Γ.Visit) (b : ZMod (period hW (rep hW i))),
      strIdx pl hW hne V u'.2.val = ⟨i, b⟩ → strIdx pl hW hne V u''.2.val = ⟨i, b⟩ → u' = u'' := by
    intro u' u'' b h1 h2
    apply visit_eq_of_strand_eq pl hW hne V hgen ov hov K data
    exact h1.trans h2.symm
  have hcompv : ∀ u' : (𝔇).Γ.Visit, (𝔇).compOf u' = (𝔇).compOf v →
      ∃ b : ZMod (period hW (rep hW i)), strIdx pl hW hne V u'.2.val = ⟨i, b⟩ := by
    intro u' hu'
    obtain ⟨i', b, hub⟩ : ∃ (i' : Fin (numComp hW)) (b : ZMod (period hW (rep hW i'))),
      strIdx pl hW hne V u'.2.val = ⟨i', b⟩ := ⟨_, _, rfl⟩
    have hi' : i = i' := by
      rw [← compOf_eq_of pl hW hne V hgen ov hov u' hub, ← compOf_eq_of pl hW hne V hgen ov hov v hva, hu']
    subst hi'
    exact ⟨b, hub⟩
  rcases lt_or_eq_of_le hnk with hlt | heq
  · -- `n < k`: the candidate differs from `v`; uniqueness of the cyclic successor
    have hwv : w ≠ v := by
      intro h
      have h2 : strIdx pl hW hne V w.2.val = strIdx pl hW hne V v.2.val := by rw [h]
      rw [hw2, hva] at h2
      have h3 : a + (n : ZMod (period hW (rep hW i))) = a := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
      exact hcast_ne n hn0 hlt (add_eq_left.1 h3)
    have hwc : (𝔇).compOf w = (𝔇).compOf v := by
      rw [compOf_eq_of pl hW hne V hgen ov hov w hw2, compOf_eq_of pl hW hne V hgen ov hov v hva]
    apply cycNext_unique_on (p := fun w' => (𝔇).compOf w' = (𝔇).compOf v) (k := (𝔇).visitCoord)
      (fun a b ha hb h => (𝔇).visitCoord_injOn (ha.trans hb.symm) h) rfl ((𝔇).compOf_nextVisit v) hwc
      ((𝔇).nextVisit_ne_self v w hwc hwv) hwv (fun u' hu' => (𝔇).nextVisit_no_between v u' hu')
    intro u' hu'
    obtain ⟨b, hub⟩ := hcompv u' hu'
    obtain ⟨j, hjk, hb⟩ := hcomp b
    rw [hb] at hub
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hvisit_eq u' v _ hub (by rw [hva, Nat.cast_zero, add_zero])]
      exact not_cycBetween_self_left _ _
    rcases lt_trichotomy j n with hjn | hjn | hnj
    · exact (hno u' _ hub j rfl hj0 hjn).elim
    · rw [hvisit_eq u' w _ hub (by rw [hw2, hjn])]
      exact not_cycBetween_self_mid _ _
    · -- `n < j`: the coordinates are in the wrong cyclic order
      rw [visitCoord_eq_of pl hW hne V hgen ov hov v hva, visitCoord_eq_of pl hW hne V hgen ov hov u' hub,
        visitCoord_eq_of pl hW hne V hgen ov hov w hw2]
      have hAB : a.val ≠ (a + (j : ZMod (period hW (rep hW i)))).val := by
        intro h
        have := ZMod.val_injective _ h
        exact hcast_ne j hj0 hjk (add_eq_left.1 this.symm)
      have hBC : (a + (j : ZMod (period hW (rep hW i)))).val ≠ (a + (n : ZMod (period hW (rep hW i)))).val := by
        intro h
        have := hcast_inj j n hjk hlt (add_left_cancel (ZMod.val_injective _ h))
        omega
      have hAC : a.val ≠ (a + (n : ZMod (period hW (rep hW i)))).val := by
        intro h
        have := ZMod.val_injective _ h
        exact hcast_ne n hn0 hlt (add_eq_left.1 this.symm)
      rw [cycBetween_nat_add hAB hBC hAC ((𝔇).visitPt v).2.2.2.1 ((𝔇).visitPt v).2.2.2.2
        ((𝔇).visitPt u').2.2.2.1 ((𝔇).visitPt u').2.2.2.2 ((𝔇).visitPt w).2.2.2.1 ((𝔇).visitPt w).2.2.2.2]
      have hb' : (a + (j : ZMod (period hW (rep hW i)))).val = a.val + j ∨
          (a + (j : ZMod (period hW (rep hW i)))).val + period hW (rep hW i) = a.val + j := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hjk]
        exact add_mod_cases _ _ _ (ZMod.val_lt a) hjk
      have hc' : (a + (n : ZMod (period hW (rep hW i)))).val = a.val + n ∨
          (a + (n : ZMod (period hW (rep hW i)))).val + period hW (rep hW i) = a.val + n := by
        rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
        exact add_mod_cases _ _ _ (ZMod.val_lt a) hlt
      rw [cycIdx_iff (period hW (rep hW i)) j n a.val _ _ hkpos (ZMod.val_lt _) (ZMod.val_lt _) hj0 hn0 hjk hlt
        hb' hc']
      omega
  · -- `n = k`: `v` is the only visit of its component, and the candidate is `v`
    have hwv : w = v := by
      apply hvisit_eq w v _ hw2
      rw [hva, heq, ZMod.natCast_self, add_zero]
    rw [hwv]
    apply (𝔇).nextVisit_eq_self v
    intro u' hu'
    obtain ⟨b, hub⟩ := hcompv u' hu'
    obtain ⟨j, hjk, hb⟩ := hcomp b
    rw [hb] at hub
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact hvisit_eq u' v _ hub (by rw [hva, Nat.cast_zero, add_zero])
    · exact (hno u' _ hub j rfl hj0 (heq ▸ hjk)).elim

/-- THE RECORD OF A DIAGRAM ON THE STRANDS OF A REALIZATION is the slot record of the active columns. -/
noncomputable def diagramRecordIso [DecidablePred K] :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (slotRecord hW (colActive K) (colActive_activeSet hW K)) where
  e := Equiv.refl _
  Φ := visitEquiv pl hW hne V hgen ov hov K data
  comp_eq v := by
    show slotComp hW (idxEquiv hW v.2.val) = v.2.val.1
    exact slotComp_idxEquiv hW _
  succ_eq v := by
    show visitEquiv pl hW hne V hgen ov hov K data ((mkDiagram pl hW hne V hgen ov hov).nextVisit v) = _
    rw [nextVisit_eq pl hW hne V hgen ov hov K data]
    exact (visitEquiv pl hW hne V hgen ov hov K data).apply_symm_apply _
  pair_eq v := by
    apply Subtype.ext
    show idxEquiv hW ((mkDiagram pl hW hne V hgen ov hov).twin v).2.val = σtwin hW (idxEquiv hW v.2.val)
    exact slot_other pl hW hne V hgen ov hov K data v.2.2
  bit_eq v := (overBit_eq pl hW hne V hgen ov hov K data v).symm
  sgn_eq v := (sign_eq pl hW hne V hgen ov hov K data v).symm

end DiagramIso

/-! #### E. The realization itself -/

section Realize

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])

/-- All `σ` slots form an active set. -/
theorem allActive : ActiveSet hW (IsσSlot (W := W)) where
  isσ _ hu := hu
  twin _ hu := isσSlot_σtwin hW hu

/-- The realization is the diagram with all `σ` columns active. -/
theorem realizeAt_data :
    SlotDiagramData pl hW hne (shadowOf pl hW hne).vertices (realizeAt pl hW hne).generic
      (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True) where
  cross x := by
    constructor
    · intro h
      have e := congrArg Subtype.val (eq_crossingOf pl hW hne ⟨x, h⟩)
      rw [crossingOf_val] at e
      exact ⟨_, _, _, _, trivial, e⟩
    · rintro ⟨k, m, hk, hℓ, -, rfl⟩
      exact (crossingOf pl hW hne hk hℓ).2
  overStrand x k m hk hℓ hx := by
    have : x = crossingOf pl hW hne hk hℓ := Subtype.ext hx
    rw [this]
    exact overStrand_crossingOf pl hW hne hk hℓ
  sgn x k m hk hℓ hx := by
    have : x = crossingOf pl hW hne hk hℓ := Subtype.ext hx
    rw [this]
    exact sign_crossingOf pl hW hne hk hℓ

/-- `realizeRecordIso` for `realizeAt`: the named record of the realization is the slot record of all
`σ` slots. -/
noncomputable def realizeAtRecordIso :
    RecordIso (realizeAt pl hW hne).diagram.record (slotRecord hW IsσSlot (allActive hW)) :=
  (diagramRecordIso pl hW hne (shadowOf pl hW hne).vertices (realizeAt pl hW hne).generic
    (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True)
    (realizeAt_data pl hW hne)).trans
    (slotRecordCongr hW _ _ IsσSlot (allActive hW) (fun _ => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩))

end Realize



/-! #### G. The exterior correspondence of `X ++ P ++ Y` and `X ++ P' ++ Y` (β2's `shiftIdx`/`extSlot`/`next_ext`) -/

section Exterior

variable (X P Y P' : Word)

instance instDecidableExtCol (k : ℕ) : Decidable (ExtCol X P k) := by unfold ExtCol; infer_instance
instance instDecidablePredExtCol : DecidablePred (ExtCol X P) := fun k => instDecidableExtCol X P k

/-- A slot whose piece lies in an exterior column. -/
def ExtPiece (u : Slot (X ++ P ++ Y)) : Prop := ExtCol X P (colOf u)

instance : DecidablePred (ExtPiece X P Y) := fun u => by unfold ExtPiece; infer_instance

theorem extPiece_σtwin (hW : (X ++ P ++ Y).Closed) {u : Slot (X ++ P ++ Y)} (hu : IsσSlot u)
    (h : ExtPiece X P Y u) : ExtPiece X P Y (σtwin hW u) := by
  show ExtCol X P (colOf _); rw [colOf_σtwin hW hu]; exact h

theorem shiftIdx_injOn (hP : P ≠ []) {k k' : ℕ} (hk : ExtCol X P k) (hk' : ExtCol X P k')
    (h : shiftIdx X P P' k = shiftIdx X P P' k') : k = k' := by
  have := P_length_pos P hP
  unfold ExtCol at hk hk'
  unfold shiftIdx at h
  split_ifs at h <;> omega

/-- The inverse index shift on exterior columns of `W'`. -/
def unshiftCol (k' : ℕ) : ℕ := if k' < X.length then k' else k' + P.length - P'.length

theorem unshiftCol_spec (hP : P ≠ []) {k' : ℕ} (h : ExtCol X P' k') :
    ExtCol X P (unshiftCol X P P' k') ∧ shiftIdx X P P' (unshiftCol X P P' k') = k' := by
  have := P_length_pos P hP
  unfold ExtCol at h ⊢
  unfold unshiftCol shiftIdx
  split_ifs <;> omega

theorem colOf_mk {V : Word} (k p : ℕ) (hs : IsSlot V (k, p)) :
    colOf (⟨(k, p), hs⟩ : Slot V) = if p = 0 then k else if bit V k p then k else k - 1 := rfl

variable (hP : P ≠ []) (hE : SameEffect X P P') (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE hW

/-- The slot of `W'` corresponding to an exterior-piece slot of `W` (β2's `extSlot`). -/
noncomputable def extF (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    {u' : Slot (X ++ P' ++ Y) // ExtPiece X P' Y u'} :=
  ⟨extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩, by
    show ExtCol X P' (colOf _)
    rw [colOf_ext X P Y P' hP hE hW ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ u.2]
    exact extCol_shift X P P' hP u.2⟩

theorem extF_val (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (extF X P Y P' hP hE hW u).1.1 = extPair X P P' u.1.1 := rfl

theorem extF_eq (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (extF X P Y P' hP hE hW u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ := rfl

theorem extF_injective : Function.Injective (extF X P Y P' hP hE hW) := by
  rintro ⟨⟨⟨k, p⟩, hs⟩, hu⟩ ⟨⟨⟨k', p'⟩, hs'⟩, hv⟩ h
  have h1 : extPair X P P' (k, p) = extPair X P P' (k', p') := congrArg (fun x => x.1.1) h
  simp only [extPair, Prod.mk.injEq] at h1
  obtain ⟨hsh, rfl⟩ := h1
  have hext : IsExtSlot X P (k, p) := isExtSlot_of_extCol X P Y P' hP hE ⟨(k, p), hs⟩ hu
  have hext' : IsExtSlot X P (k', p) := isExtSlot_of_extCol X P Y P' hP hE ⟨(k', p), hs'⟩ hv
  have hu' := hu; have hv' := hv
  unfold ExtPiece at hu' hv'
  rw [colOf_mk] at hu' hv'
  suffices hkk : k = k' by subst hkk; rfl
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte] at hu' hv'
    exact shiftIdx_injOn X P P' hP hu' hv' hsh
  · simp only [hp, ↓reduceIte] at hu' hv'
    unfold IsExtSlot at hext hext'
    simp only [hp, ↓reduceIte] at hext hext'
    have hb : bit (X ++ P ++ Y) k p = bit (X ++ P ++ Y) k' p := by
      rw [bit_ext X P Y P' hP hE hext, bit_ext X P Y P' hP hE hext', hsh]
    cases hbk : bit (X ++ P ++ Y) k p
    · rw [hbk] at hu' hb
      rw [← hb] at hv'
      simp only [Bool.false_eq_true, ↓reduceIte] at hu' hv'
      have hk1 : 1 ≤ k := (cutSlot_pos hW (by
        rcases hs with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · exact absurd h0 hp
        · exact h1) (by
        rcases hs with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · exact absurd h0 hp
        · exact h2)).1
      have hk1' : 1 ≤ k' := (cutSlot_pos hW (by
        rcases hs' with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · exact absurd h0 hp
        · exact h1) (by
        rcases hs' with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · exact absurd h0 hp
        · exact h2)).1
      have e1 := shiftIdx_pred X P P' hP hu' hk1
      have e2 := shiftIdx_pred X P P' hP hv' hk1'
      have := shiftIdx_injOn X P P' hP hu' hv' (by rw [e1, e2, hsh])
      omega
    · rw [hbk] at hu' hb
      rw [← hb] at hv'
      simp only [↓reduceIte] at hu' hv'
      exact shiftIdx_injOn X P P' hP hu' hv' hsh

omit hP hE hW in
theorem length_W' : (X ++ P' ++ Y).length = X.length + P'.length + Y.length := by
  simp only [List.length_append]
omit hP hE hW in
theorem length_W : (X ++ P ++ Y).length = X.length + P.length + Y.length := by
  simp only [List.length_append]

theorem extF_surjective : Function.Surjective (extF X P Y P' hP hE hW) := by
  rintro ⟨⟨⟨j', p⟩, hs'⟩, hu'⟩
  have hu'' := hu'
  unfold ExtPiece at hu''
  rw [colOf_mk] at hu''
  have hPpos := P_length_pos P hP
  have hlen := length_W X P Y
  have hlen' := length_W' X Y P'
  by_cases hp : p = 0
  · subst hp
    simp only [↓reduceIte] at hu''
    obtain ⟨hk, hsh⟩ := unshiftCol_spec X P P' hP hu''
    set k := unshiftCol X P P' j' with hkdef
    have hj' : j' < (X ++ P' ++ Y).length := by
      rcases hs' with ⟨-, h, -⟩ | ⟨h, -, -⟩
      · exact h
      · omega
    have hkW : k < (X ++ P ++ Y).length := by
      unfold unshiftCol at hkdef; unfold ExtCol at hu''; split_ifs at hkdef <;> omega
    have hslot : IsSlot (X ++ P ++ Y) (k, 0) := by
      left
      refine ⟨rfl, hkW, ?_⟩
      rw [letterAt_ext X P Y P' hP hk, hsh]
      rcases hs' with ⟨-, -, h⟩ | ⟨h, -, -⟩
      · exact h
      · omega
    refine ⟨⟨⟨(k, 0), hslot⟩, ?_⟩, ?_⟩
    · show ExtCol X P (colOf _); rw [colOf_mk]; simpa using hk
    · apply Subtype.ext; apply Subtype.ext
      rw [extF_val]; simp only [extPair]; rw [hsh]
  · simp only [hp, ↓reduceIte] at hu''
    have hs'' : 1 ≤ p ∧ p ≤ (cut (X ++ P' ++ Y) j').length ∧ j' ≤ (X ++ P' ++ Y).length := by
      rcases hs' with ⟨h0, -⟩ | h
      · exact absurd h0 hp
      · exact h
    cases hb : bit (X ++ P' ++ Y) j' p
    · -- leftward: the piece is in column `j' - 1`
      rw [hb] at hu''
      simp only [Bool.false_eq_true, ↓reduceIte] at hu''
      have hj1 : 1 ≤ j' := by
        rcases Nat.eq_zero_or_pos j' with rfl | h
        · exfalso
          have := hs''.2.1
          rw [cut_zero] at this
          simp at this
          omega
        · exact h
      obtain ⟨hk, hsh⟩ := unshiftCol_spec X P P' hP hu''
      set k := unshiftCol X P P' (j' - 1) with hkdef
      have hsh1 : shiftIdx X P P' (k + 1) = j' := by rw [shiftIdx_succ X P P' hP hk, hsh]; omega
      have hkW : k + 1 ≤ (X ++ P ++ Y).length := by
        unfold unshiftCol at hkdef; unfold ExtCol at hu''; split_ifs at hkdef <;> omega
      have hcut : cut (X ++ P ++ Y) (k + 1) = cut (X ++ P' ++ Y) j' := by
        rw [cut_ext X P Y P' hP hE hk.extCut_succ, hsh1]
      have hslot : IsSlot (X ++ P ++ Y) (k + 1, p) := by
        right; exact ⟨hs''.1, by rw [hcut]; exact hs''.2.1, hkW⟩
      have hbit : bit (X ++ P ++ Y) (k + 1) p = false := by
        rw [bit_ext X P Y P' hP hE hk.extCut_succ, hsh1, hb]
      refine ⟨⟨⟨(k + 1, p), hslot⟩, ?_⟩, ?_⟩
      · show ExtCol X P (colOf _); rw [colOf_mk]; simp only [hp, ↓reduceIte, hbit, Bool.false_eq_true]
        simpa using hk
      · apply Subtype.ext; apply Subtype.ext
        rw [extF_val]; simp only [extPair]; rw [hsh1]
    · -- rightward: the piece is in column `j'`
      rw [hb] at hu''
      simp only [↓reduceIte] at hu''
      obtain ⟨hk, hsh⟩ := unshiftCol_spec X P P' hP hu''
      set k := unshiftCol X P P' j' with hkdef
      have hkW : k ≤ (X ++ P ++ Y).length := by
        unfold unshiftCol at hkdef; unfold ExtCol at hu''; split_ifs at hkdef <;> omega
      have hcut : cut (X ++ P ++ Y) k = cut (X ++ P' ++ Y) j' := by
        rw [cut_ext X P Y P' hP hE hk.extCut, hsh]
      have hslot : IsSlot (X ++ P ++ Y) (k, p) := by
        right; exact ⟨hs''.1, by rw [hcut]; exact hs''.2.1, hkW⟩
      have hbit : bit (X ++ P ++ Y) k p = true := by
        rw [bit_ext X P Y P' hP hE hk.extCut, hsh, hb]
      refine ⟨⟨⟨(k, p), hslot⟩, ?_⟩, ?_⟩
      · show ExtCol X P (colOf _); rw [colOf_mk]; simp only [hp, ↓reduceIte, hbit]; exact hk
      · apply Subtype.ext; apply Subtype.ext
        rw [extF_val]; simp only [extPair]; rw [hsh]

/-- THE EXTERIOR SLOT CORRESPONDENCE: the exterior-piece slots of the two words are in bijection by the
index shift (`shiftIdx`); `P'` may be empty. -/
noncomputable def φE : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u} ≃ {u' : Slot (X ++ P' ++ Y) // ExtPiece X P' Y u'} :=
  Equiv.ofBijective (extF X P Y P' hP hE hW) ⟨extF_injective X P Y P' hP hE hW, extF_surjective X P Y P' hP hE hW⟩

theorem φE_apply (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    φE X P Y P' hP hE hW u = extF X P Y P' hP hE hW u := rfl

theorem φE_val (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    (φE X P Y P' hP hE hW u).1.1 = extPair X P P' u.1.1 := rfl

theorem colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    colOf (φE X P Y P' hP hE hW u).1 = shiftIdx X P P' (colOf u.1) :=
  colOf_ext X P Y P' hP hE hW ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ u.2

/-- THE BLOCK PASSAGE HYPOTHESIS (verified by the rows on their concrete patterns): from every *entry slot*
`b` of the block of `W` (an exterior slot whose piece lies in the block: cut `|X|` heading right or cut
`|X|+|P|` heading left) the traversal exits the block after `m` steps at the exterior-piece slot `c`, and
in `W'` the slot `b'` corresponding to `b` reaches the slot corresponding to `c` after `m'` block steps
(`m' = 0` allowed: the case `P' = []`). -/
structure Passage : Prop where
  pass : ∀ b : Slot (X ++ P ++ Y), IsExtSlot X P b.1 → ¬ ExtCol X P (colOf b) →
    ∃ (m : ℕ) (c : Slot (X ++ P ++ Y)), (next hW)^[m] b = c ∧ ExtCol X P (colOf c) ∧
      (∀ i < m, ¬ ExtCol X P (colOf ((next hW)^[i] b))) ∧
      ∃ (m' : ℕ) (b' : Slot (X ++ P' ++ Y)), b'.1 = extPair X P P' b.1 ∧
        ((next hW')^[m'] b').1 = extPair X P P' c.1 ∧
        ∀ i < m', ¬ ExtCol X P' (colOf ((next hW')^[i] b'))

/-- The passage hypothesis makes the first returns to the exterior-piece slots conjugate under `φE`. -/
theorem conj_of_passage (hpass : Passage X P Y P' hW hW') (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    firstReturn (nextPerm hW') (ExtPiece X P' Y) (φE X P Y P' hP hE hW u) =
      φE X P Y P' hP hE hW (firstReturn (nextPerm hW) (ExtPiece X P Y) u) := by
  set φ := φE X P Y P' hP hE hW with hφ
  obtain ⟨hnext_ext, hnext_eq⟩ :=
    next_ext X P Y P' hP hE hW hW' ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ u.2
  have hφu : (φ u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ := rfl
  by_cases hE1 : ExtPiece X P Y (next hW u.1)
  · -- one exterior step on both sides
    have h1 : (firstReturn (nextPerm hW) (ExtPiece X P Y) u).1 = next hW u.1 :=
      firstReturn_apply_of_mem _ _ u hE1
    have h2 : next hW' (φ u).1 = (φ ⟨next hW u.1, hE1⟩).1 := by
      apply Subtype.ext
      rw [hφu, hnext_eq]; rfl
    have hE1' : ExtPiece X P' Y (next hW' (φ u).1) := by rw [h2]; exact (φ _).2
    apply Subtype.ext
    rw [firstReturn_apply_of_mem _ _ (φ u) hE1', nextPerm_apply, h2]
    exact congrArg (fun x => (φ x).1) (Subtype.ext h1.symm)
  · -- a block passage
    obtain ⟨m, c, hmc, hc, hint, m', b', hb', hm', hint'⟩ := hpass.pass (next hW u.1) hnext_ext hE1
    have hW1 : (firstReturn (nextPerm hW) (ExtPiece X P Y) u).1 = c := by
      rw [firstReturn_eq_of_path (nextPerm hW) (ExtPiece X P Y) u (m := m + 1) (Nat.succ_pos _) ?_ ?_]
      · rw [nextPerm_pow_apply, Function.iterate_succ_apply, hmc]
      · show ExtCol X P (colOf _)
        rw [nextPerm_pow_apply, Function.iterate_succ_apply, hmc]; exact hc
      · intro i hi him
        show ¬ ExtCol X P (colOf _)
        rw [nextPerm_pow_apply]
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Function.iterate_succ_apply]
        exact hint i' (by omega)
    have hb'' : next hW' (φ u).1 = b' := by
      apply Subtype.ext
      rw [hb', hφu, hnext_eq]
    have hcφ : (φ ⟨c, hc⟩).1 = (next hW')^[m'] b' := by
      apply Subtype.ext
      rw [hm']; rfl
    have hW2 : (firstReturn (nextPerm hW') (ExtPiece X P' Y) (φ u)).1 = (φ ⟨c, hc⟩).1 := by
      rw [firstReturn_eq_of_path (nextPerm hW') (ExtPiece X P' Y) (φ u) (m := m' + 1) (Nat.succ_pos _) ?_ ?_]
      · rw [nextPerm_pow_apply, Function.iterate_succ_apply, hb'', hcφ]
      · show ExtCol X P' (colOf _)
        rw [nextPerm_pow_apply, Function.iterate_succ_apply, hb'', ← hcφ]; exact (φ ⟨c, hc⟩).2
      · intro i hi him
        show ¬ ExtCol X P' (colOf _)
        rw [nextPerm_pow_apply]
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Function.iterate_succ_apply, hb'']
        exact hint' i' (by omega)
    apply Subtype.ext
    rw [hW2]
    exact congrArg (fun x => (φ x).1) (Subtype.ext hW1.symm)

omit hE in
/-- The entry slots of the block, concretely: cut `|X|` heading right, or cut `|X|+|P|` heading left. -/
theorem entry_iff (b : Slot (X ++ P ++ Y)) :
    IsExtSlot X P b.1 ∧ ¬ ExtCol X P (colOf b) ↔
      (∃ p, b.1 = (X.length, p) ∧ p ≠ 0 ∧ bit (X ++ P ++ Y) X.length p = true) ∨
      (∃ p, b.1 = (X.length + P.length, p) ∧ p ≠ 0 ∧ bit (X ++ P ++ Y) (X.length + P.length) p = false) := by
  have hPpos := P_length_pos P hP
  obtain ⟨⟨k, p⟩, hs⟩ := b
  rw [colOf_mk]
  by_cases hp : p = 0
  · subst hp
    simp only [IsExtSlot, ↓reduceIte]
    constructor
    · rintro ⟨h1, h2⟩; exact absurd h1 h2
    · rintro (⟨p', h, hp', -⟩ | ⟨p', h, hp', -⟩) <;> simp only [Prod.mk.injEq] at h <;> exact absurd h.2.symm hp'
  · have hk1 : 1 ≤ k := (cutSlot_pos hW (by
        rcases hs with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · exact absurd h0 hp
        · exact h1) (by
        rcases hs with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · exact absurd h0 hp
        · exact h2)).1
    simp only [IsExtSlot, hp, ↓reduceIte]
    cases hb : bit (X ++ P ++ Y) k p
    · simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro ⟨h1, h2⟩
        have hk : k = X.length + P.length := by unfold ExtCut at h1; unfold ExtCol at h2; omega
        subst hk
        exact Or.inr ⟨p, rfl, hp, hb⟩
      · rintro (⟨p', h, -, hb'⟩ | ⟨p', h, -, -⟩)
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact absurd (hb'.symm.trans hb) (by decide)
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_⟩ <;> (try unfold ExtCut) <;> (try unfold ExtCol) <;> omega
    · simp only [↓reduceIte]
      constructor
      · rintro ⟨h1, h2⟩
        have hk : k = X.length := by unfold ExtCut at h1; unfold ExtCol at h2; omega
        subst hk
        exact Or.inl ⟨p, rfl, hp, hb⟩
      · rintro (⟨p', h, -, -⟩ | ⟨p', h, -, hb'⟩)
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, ?_⟩ <;> (try unfold ExtCut) <;> (try unfold ExtCol) <;> omega
        · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          exact absurd (hb'.symm.trans hb) (by decide)

/-- The piece shape is preserved by the exterior correspondence. -/
theorem shapeOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    shapeOf (φE X P Y P' hP hE hW u).1 = shapeOf u.1 := by
  obtain ⟨⟨⟨k, p⟩, hs⟩, hu⟩ := u
  have hext : IsExtSlot X P (k, p) := isExtSlot_of_extCol X P Y P' hP hE ⟨(k, p), hs⟩ hu
  have hval : (φE X P Y P' hP hE hW ⟨⟨(k, p), hs⟩, hu⟩).1.1 = (shiftIdx X P P' k, p) := rfl
  have hu' := hu
  unfold ExtPiece at hu'
  rw [colOf_mk] at hu'
  unfold shapeOf
  rw [hval]
  simp only
  by_cases hp : p = 0
  · subst hp
    simp only [↓reduceIte] at hu' ⊢
    simp only [← letterAt_ext X P Y P' hP hu', ← bit_ext X P Y P' hP hE hu'.extCut]
  · simp only [hp, ↓reduceIte] at hu' ⊢
    simp only [IsExtSlot, hp, ↓reduceIte] at hext
    rw [← bit_ext X P Y P' hP hE hext p]
    cases hb : bit (X ++ P ++ Y) k p
    · rw [hb] at hu'
      simp only [Bool.false_eq_true, ↓reduceIte] at hu' ⊢
      have hk1 : 1 ≤ k := (cutSlot_pos hW (by
        rcases hs with ⟨h0, -⟩ | ⟨h1, -, -⟩
        · exact absurd h0 hp
        · exact h1) (by
        rcases hs with ⟨h0, -⟩ | ⟨-, h2, -⟩
        · exact absurd h0 hp
        · exact h2)).1
      rw [← shiftIdx_pred X P P' hP hu' hk1, ← letterAt_ext X P Y P' hP hu']
    · rw [hb] at hu'
      simp only [↓reduceIte] at hu' ⊢
      rw [← letterAt_ext X P Y P' hP hu']

theorem letterAt_colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    letterAt (X ++ P' ++ Y) (colOf (φE X P Y P' hP hE hW u).1) = letterAt (X ++ P ++ Y) (colOf u.1) := by
  rw [colOf_φE, ← letterAt_ext X P Y P' hP u.2]

theorem bit_colOf_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) (p : ℕ) :
    bit (X ++ P' ++ Y) (colOf (φE X P Y P' hP hE hW u).1) p = bit (X ++ P ++ Y) (colOf u.1) p := by
  rw [colOf_φE, ← bit_ext X P Y P' hP hE u.2.extCut]

/-- `σ` slots correspond to `σ` slots. -/
theorem isσSlot_φE_iff (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    IsσSlot (φE X P Y P' hP hE hW u).1 ↔ IsσSlot u.1 := by
  unfold IsσSlot
  rw [letterAt_colOf_φE, shapeOf_φE]

theorem isDesc_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    isDesc (φE X P Y P' hP hE hW u).1 = isDesc u.1 := by
  unfold isDesc; rw [shapeOf_φE]

theorem σsgn_φE (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    σsgn (φE X P Y P' hP hE hW u).1 = σsgn u.1 := by
  unfold σsgn σsgnCol
  rw [letterAt_colOf_φE, bit_colOf_φE, bit_colOf_φE]

theorem φE_σtwin (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) (hu : IsσSlot u.1) :
    (φE X P Y P' hP hE hW ⟨σtwin hW u.1, extPiece_σtwin X P Y hW hu u.2⟩).1 = σtwin hW' (φE X P Y P' hP hE hW u).1 := by
  have hu' : IsσSlot (φE X P Y P' hP hE hW u).1 := (isσSlot_φE_iff X P Y P' hP hE hW u).2 hu
  apply σslot_ext hW' ((isσSlot_φE_iff X P Y P' hP hE hW _).2 (isσSlot_σtwin hW hu)) (isσSlot_σtwin hW' hu')
  · rw [colOf_φE, colOf_σtwin hW' hu', colOf_φE]
    show shiftIdx X P P' (colOf (σtwin hW u.1)) = _
    rw [colOf_σtwin hW hu]
  · rw [isDesc_φE, isDesc_σtwin hW' hu', isDesc_φE]
    show isDesc (σtwin hW u.1) = _
    rw [isDesc_σtwin hW hu]

/-- The active sets correspond. -/
theorem colActive_φE_iff (u : {u : Slot (X ++ P ++ Y) // ExtPiece X P Y u}) :
    colActive (ExtCol X P') (φE X P Y P' hP hE hW u).1 ↔ colActive (ExtCol X P) u.1 := by
  constructor
  · rintro ⟨h1, -⟩; exact ⟨(isσSlot_φE_iff X P Y P' hP hE hW u).1 h1, u.2⟩
  · rintro ⟨h1, -⟩; exact ⟨(isσSlot_φE_iff X P Y P' hP hE hW u).2 h1, (φE X P Y P' hP hE hW u).2⟩

/-- The active slots of the two words correspond. -/
noncomputable def extActiveEquiv :
    {u : Slot (X ++ P ++ Y) // colActive (ExtCol X P) u} ≃ {u' : Slot (X ++ P' ++ Y) // colActive (ExtCol X P') u'} where
  toFun u := ⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, (colActive_φE_iff X P Y P' hP hE hW _).2 u.2⟩
  invFun u' := ⟨((φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩).1, by
    have h := (colActive_φE_iff X P Y P' hP hE hW ((φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩)).1
    rw [Equiv.apply_symm_apply] at h
    exact h u'.2⟩
  left_inv u := Subtype.ext (by
    show ((φE X P Y P' hP hE hW).symm ⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, _⟩).1 = u.1
    rw [show (⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, _⟩ : {u' // ExtPiece X P' Y u'}) =
      φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩ from rfl, Equiv.symm_apply_apply])
  right_inv u' := Subtype.ext (by
    show (φE X P Y P' hP hE hW ⟨((φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩).1, _⟩).1 = u'.1
    rw [show (⟨((φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩).1, _⟩ : {u // ExtPiece X P Y u}) =
      (φE X P Y P' hP hE hW).symm ⟨u'.1, u'.2.2⟩ from rfl, Equiv.apply_symm_apply])

theorem extActiveEquiv_val (u : {u : Slot (X ++ P ++ Y) // colActive (ExtCol X P) u}) :
    (extActiveEquiv X P Y P' hP hE hW u).1 = (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 := rfl

/-- THE EXTERIOR RECORD ISOMORPHISM: two words agreeing outside a block, with corresponding block passages
and every component meeting the exterior, have isomorphic slot records on their exterior `σ` slots. -/
noncomputable def extRecordIso (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u')) :
    RecordIso (slotRecord hW (colActive (ExtCol X P)) (colActive_activeSet hW _))
      (slotRecord hW' (colActive (ExtCol X P')) (colActive_activeSet hW' _)) :=
  let φ := φE X P Y P' hP hE hW
  let conj := conj_of_passage X P Y P' hP hE hW hW' hpass
  let hexitP : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y (((nextPerm hW) ^ n) u) := fun u => by
    obtain ⟨n, hn⟩ := hexit u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let hexitP' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y (((nextPerm hW') ^ n) u') := fun u => by
    obtain ⟨n, hn⟩ := hexit' u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let oe : Orbit hW ≃ Orbit hW' :=
    cycleEquiv (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj hexitP hexitP'
  { e := (Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))
    Φ := extActiveEquiv X P Y P' hP hE hW
    comp_eq := fun u => by
      show slotComp hW' (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 =
        ((Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))) (slotComp hW u.1)
      rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      congr 1
      show orbitOf hW' _ = cycleEquiv (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj
        hexitP hexitP' (orbitOf hW u.1)
      exact (cycleEquiv_mk (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj hexitP hexitP'
        ⟨u.1, u.2.2⟩).symm
    succ_eq := fun u => by
      apply Subtype.ext
      show (φE X P Y P' hP hE hW ⟨(firstReturn (nextPerm hW) (colActive (ExtCol X P)) u).1, _⟩).1 =
        (firstReturn (nextPerm hW') (colActive (ExtCol X P')) ⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, _⟩).1
      exact (firstReturn_conj_of_factor (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj
        (colActive (ExtCol X P)) (colActive (ExtCol X P')) (fun _ h => h.2) (fun _ h => h.2)
        (colActive_φE_iff X P Y P' hP hE hW) u).symm
    pair_eq := fun u => by
      apply Subtype.ext
      show (φE X P Y P' hP hE hW ⟨σtwin hW u.1, _⟩).1 = σtwin hW' (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1
      exact φE_σtwin X P Y P' hP hE hW hW' ⟨u.1, u.2.2⟩ u.2.1
    bit_eq := fun u => by
      show isDesc (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 = isDesc u.1
      exact isDesc_φE X P Y P' hP hE hW _
    sgn_eq := fun u => by
      show σsgn (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 = σsgn u.1
      exact σsgn_φE X P Y P' hP hE hW _ }

end Exterior



/-! #### H. Consequences: realizations, full slot bijections, the composed isomorphisms -/

section Consequences

/-- `realizeRecordIso` (PLAN_FINAL §5 "U2"): the named record of `realize W` is the slot record of all `σ`
slots of `W` (nonempty words; the empty word realizes to the standard circle). -/
noncomputable def realizeRecordIso (W : OWord) (h : W.letters ≠ []) :
    RecordIso (realize W).diagram.record (slotRecord W.closed IsσSlot (allActive W.closed)) := by
  rw [realize_eq_realizeAt W h]
  exact realizeAtRecordIso .std W.closed h

/-- Blocks without crossing letters: the exterior `σ` slots are all `σ` slots. -/
theorem colActive_extCol_iff (X P Y : Word)
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (u : Slot (X ++ P ++ Y)) : colActive (ExtCol X P) u ↔ IsσSlot u := by
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    by_contra hc
    unfold ExtCol at hc
    have h1 := h.1
    rw [hnoσ (colOf u) (by omega) (by omega)] at h1
    exact Bool.false_ne_true h1

variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed) (S : Slot W → Prop) (S' : Slot W' → Prop)
  [DecidablePred S] [DecidablePred S'] (hS : ActiveSet hW S) (hS' : ActiveSet hW' S')

/-- The cycle bijection induced by a slot bijection commuting with `next`. -/
noncomputable def orbitEquivOfSlotEquiv (ψ : Slot W ≃ Slot W') (hnext : ∀ u, ψ (next hW u) = next hW' (ψ u)) :
    Orbit hW ≃ Orbit hW' :=
  Quotient.congr ψ (fun a b => (sameCycle_iff_of_conj (nextPerm hW) (nextPerm hW') hnext a b).symm)

/-- A bijection of ALL slots commuting with `next`, carrying the active set onto the active set and
preserving twins, over bits and signs, is a record isomorphism (the commutation, PLAN_FINAL §4 L-rec; the
cusp-skein switch record after `Record.switch`). -/
noncomputable def slotRecordIsoOfSlotEquiv (ψ : Slot W ≃ Slot W') (hnext : ∀ u, ψ (next hW u) = next hW' (ψ u))
    (hact : ∀ u, S' (ψ u) ↔ S u) (htwin : ∀ u, S u → ψ (σtwin hW u) = σtwin hW' (ψ u))
    (hdesc : ∀ u, S u → isDesc (ψ u) = isDesc u) (hsgn : ∀ u, S u → σsgn (ψ u) = σsgn u) :
    RecordIso (slotRecord hW S hS) (slotRecord hW' S' hS') where
  e := (Fintype.equivFin (Orbit hW)).symm.trans
    ((orbitEquivOfSlotEquiv hW hW' ψ hnext).trans (Fintype.equivFin (Orbit hW')))
  Φ := Equiv.subtypeEquiv ψ (fun u => (hact u).symm)
  comp_eq u := by
    show slotComp hW' (ψ u.1) = ((Fintype.equivFin (Orbit hW)).symm.trans
      ((orbitEquivOfSlotEquiv hW hW' ψ hnext).trans (Fintype.equivFin (Orbit hW')))) (slotComp hW u.1)
    rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
    simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
    rfl
  succ_eq u := by
    apply Subtype.ext
    show ψ (firstReturn (nextPerm hW) S u).1 = (firstReturn (nextPerm hW') S' ⟨ψ u.1, (hact u.1).2 u.2⟩).1
    exact (firstReturn_conj (nextPerm hW) (nextPerm hW') S S' ψ hnext hact u).symm
  pair_eq u := Subtype.ext (htwin u.1 u.2)
  bit_eq u := hdesc u.1 u.2
  sgn_eq u := hsgn u.1 u.2

end Consequences

section Composed

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
  (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE

/-- THE RECORD OF THE VERTEX-MOVED DIAGRAM (U6): a diagram on the re-vertexed shadow of `realize (X ++ P ++ Y)`
whose crossings are the exterior `σ` pairs, with corresponding block passages, every component meeting the
exterior, and no crossing letter in `P'`, has the named record of `realize (X ++ P' ++ Y)` (any placement). -/
noncomputable def vertexMovedRecordIso (pl : Placement) (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (V : (shadowOf pl hW hne).Vertices) (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
    (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
    (hov : ∀ x, ov x ∈ x.val) (data : SlotDiagramData pl hW hne V hgen ov hov (ExtCol X P))
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (pl' : Placement) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (realizeAt pl' hW' hne').diagram.record :=
  ((diagramRecordIso pl hW hne V hgen ov hov (ExtCol X P) data).trans
    (extRecordIso X P Y P' hP hE hW hW' hpass hexit hexit')).trans
    ((slotRecordCongr hW' _ _ IsσSlot (allActive hW') (colActive_extCol_iff X P' Y hnoσ)).trans
      (realizeAtRecordIso pl' hW' hne').symm)

/-- The same with the target `realize W'` for a closed oriented word `W'` with letters `X ++ P' ++ Y`. -/
noncomputable def vertexMovedRecordIso' (pl : Placement) (hne : X ++ P ++ Y ≠ [])
    (V : (shadowOf pl hW hne).Vertices) (hgen : ((shadowOf pl hW hne).withVertices V).Generic)
    (ov : ((shadowOf pl hW hne).withVertices V).Crossing → ((shadowOf pl hW hne).withVertices V).Strand)
    (hov : ∀ x, ov x ∈ x.val) (data : SlotDiagramData pl hW hne V hgen ov hov (ExtCol X P))
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W' : OWord) (hW'eq : W'.letters = X ++ P' ++ Y) (hne' : X ++ P' ++ Y ≠ []) :
    RecordIso (mkDiagram pl hW hne V hgen ov hov).record (realize W').diagram.record := by
  obtain ⟨L, hL⟩ := W'
  simp only at hW'eq
  subst hW'eq
  rw [realize_eq_realizeAt ⟨_, hL⟩ hne']
  exact vertexMovedRecordIso X P Y P' hP hE hW hL pl hne hne' V hgen ov hov data hpass hexit hexit' hnoσ .std

/-- TWO REALIZATIONS agreeing outside a block without crossing letters on either side (the zigzag deletion
and, with `P' = []`, every deletion with an empty factor), with corresponding passages and every component
meeting the exterior, have isomorphic named records. -/
noncomputable def realizeAtRecordIsoOfExt (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (pl pl' : Placement) :
    RecordIso (realizeAt pl hW hne).diagram.record (realizeAt pl' hW' hne').diagram.record :=
  (((realizeAtRecordIso pl hW hne).trans
    (slotRecordCongr hW IsσSlot (allActive hW) _ (colActive_activeSet hW _)
      (fun u => (colActive_extCol_iff X P Y hnoσ u).symm))).trans
    (extRecordIso X P Y P' hP hE hW hW' hpass hexit hexit')).trans
    ((slotRecordCongr hW' _ _ IsσSlot (allActive hW') (colActive_extCol_iff X P' Y hnoσ')).trans
      (realizeAtRecordIso pl' hW' hne').symm)

/-- The same for closed oriented words `W`, `W'` with letters `X ++ P ++ Y`, `X ++ P' ++ Y`. -/
theorem realize_recordIso_of_ext (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit : ∀ u : Slot (X ++ P ++ Y), ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W W' : OWord) (hWeq : W.letters = X ++ P ++ Y) (hW'eq : W'.letters = X ++ P' ++ Y) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  obtain ⟨L, hL⟩ := W
  obtain ⟨L', hL'⟩ := W'
  simp only at hWeq hW'eq
  subst hWeq hW'eq
  rw [realize_eq_realizeAt ⟨_, hL⟩ hne, realize_eq_realizeAt ⟨_, hL'⟩ hne']
  exact ⟨realizeAtRecordIsoOfExt X P Y P' hP hE hL hL' hne hne' hpass hexit hexit' hnoσ hnoσ' .std .std⟩

end Composed


/-! #### I. The circle deletion: one interior component on the left (`Record.addFree`) -/

section AddFree

/-- `Record.addFree` is functorial in named record isomorphisms. -/
noncomputable def addFreeCongr {ρ ρ' : Record} (ι : RecordIso ρ ρ') : RecordIso ρ.addFree ρ'.addFree where
  e := Equiv.optionCongr ι.e
  Φ := ι.Φ
  comp_eq v := congrArg some (ι.comp_eq v)
  succ_eq := ι.succ_eq
  pair_eq := ι.pair_eq
  bit_eq := ι.bit_eq
  sgn_eq := ι.sgn_eq

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
  (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)
include hP hE

/-- THE EXTERIOR RECORD ISOMORPHISM WITH ONE FREE CIRCLE (ng:circle, `circle_recordIso_addFree`): as
`extRecordIso`, but exactly one component `c₀` of `W` misses the exterior (the separated circle) — the slot
record of `W` is the slot record of `W'` with one crossing-free circle added. -/
noncomputable def extRecordIsoAddFree (hpass : Passage X P Y P' hW hW')
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (c₀ : Orbit hW)
    (hc₀ : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u = c₀) :
    RecordIso (slotRecord hW (colActive (ExtCol X P)) (colActive_activeSet hW _))
      (slotRecord hW' (colActive (ExtCol X P')) (colActive_activeSet hW' _)).addFree :=
  let φ := φE X P Y P' hP hE hW
  let conj := conj_of_passage X P Y P' hP hE hW hW' hpass
  let hexitP' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y (((nextPerm hW') ^ n) u') := fun u => by
    obtain ⟨n, hn⟩ := hexit' u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let hc₀' : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y (((nextPerm hW) ^ n) u)) ↔
      Quotient.mk (Perm.SameCycle.setoid (nextPerm hW)) u = c₀ := fun u => by
    simp only [nextPerm_pow_apply]; exact hc₀ u
  let oe : Orbit hW ≃ Option (Orbit hW') :=
    cycleEquivOption (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj hexitP' c₀ hc₀'
  { e := (Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Equiv.optionCongr (Fintype.equivFin (Orbit hW'))))
    Φ := extActiveEquiv X P Y P' hP hE hW
    comp_eq := fun u => by
      show some (slotComp hW' (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1) =
        ((Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Equiv.optionCongr (Fintype.equivFin (Orbit hW')))))
          (slotComp hW u.1)
      rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      have h := cycleEquivOption_mk (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj
        hexitP' c₀ hc₀' ⟨u.1, u.2.2⟩
      show _ = Equiv.optionCongr (Fintype.equivFin (Orbit hW')) (oe (orbitOf hW u.1))
      rw [show oe (orbitOf hW u.1) = some (orbitOf hW' (φ ⟨u.1, u.2.2⟩).1) from h, Equiv.optionCongr_apply,
        Option.map_some]
      try rfl
    succ_eq := fun u => by
      apply Subtype.ext
      show (φE X P Y P' hP hE hW ⟨(firstReturn (nextPerm hW) (colActive (ExtCol X P)) u).1, _⟩).1 =
        (firstReturn (nextPerm hW') (colActive (ExtCol X P')) ⟨(φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1, _⟩).1
      exact (firstReturn_conj_of_factor (nextPerm hW) (nextPerm hW') (ExtPiece X P Y) (ExtPiece X P' Y) φ conj
        (colActive (ExtCol X P)) (colActive (ExtCol X P')) (fun _ h => h.2) (fun _ h => h.2)
        (colActive_φE_iff X P Y P' hP hE hW) u).symm
    pair_eq := fun u => by
      apply Subtype.ext
      show (φE X P Y P' hP hE hW ⟨σtwin hW u.1, _⟩).1 = σtwin hW' (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1
      exact φE_σtwin X P Y P' hP hE hW hW' ⟨u.1, u.2.2⟩ u.2.1
    bit_eq := fun u => by
      show isDesc (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 = isDesc u.1
      exact isDesc_φE X P Y P' hP hE hW _
    sgn_eq := fun u => by
      show σsgn (φE X P Y P' hP hE hW ⟨u.1, u.2.2⟩).1 = σsgn u.1
      exact σsgn_φE X P Y P' hP hE hW _ }

/-- The circle deletion on realizations: `W = X ++ P ++ Y` with a separated crossing-free block `P` forming
one component `c₀`, `W' = X ++ P' ++ Y` (`P' = []`), corresponding passages, every component of `W'` meeting
the exterior: the named record of `realize W` is that of `realize W'` with one free circle added. -/
theorem realize_recordIso_addFree_of_ext (hne : X ++ P ++ Y ≠ []) (hne' : X ++ P' ++ Y ≠ [])
    (hpass : Passage X P Y P' hW hW')
    (hexit' : ∀ u' : Slot (X ++ P' ++ Y), ∃ n : ℕ, ExtPiece X P' Y ((next hW')^[n] u'))
    (c₀ : Orbit hW)
    (hc₀ : ∀ u : Slot (X ++ P ++ Y), (¬ ∃ n : ℕ, ExtPiece X P Y ((next hW)^[n] u)) ↔ orbitOf hW u = c₀)
    (hnoσ : ∀ k, X.length ≤ k → k < X.length + P.length → (letterAt (X ++ P ++ Y) k).isCrossing = false)
    (hnoσ' : ∀ k, X.length ≤ k → k < X.length + P'.length → (letterAt (X ++ P' ++ Y) k).isCrossing = false)
    (W W' : OWord) (hWeq : W.letters = X ++ P ++ Y) (hW'eq : W'.letters = X ++ P' ++ Y) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := by
  obtain ⟨L, hL⟩ := W
  obtain ⟨L', hL'⟩ := W'
  simp only at hWeq hW'eq
  subst hWeq hW'eq
  rw [realize_eq_realizeAt ⟨_, hL⟩ hne, realize_eq_realizeAt ⟨_, hL'⟩ hne']
  exact ⟨(((realizeAtRecordIso .std hL hne).trans
    (slotRecordCongr hL IsσSlot (allActive hL) _ (colActive_activeSet hL _)
      (fun u => (colActive_extCol_iff X P Y hnoσ u).symm))).trans
    (extRecordIsoAddFree X P Y P' hP hE hL hL' hpass hexit' c₀ hc₀)).trans
    (addFreeCongr ((slotRecordCongr hL' _ _ IsσSlot (allActive hL') (colActive_extCol_iff X P' Y hnoσ')).trans
      (realizeAtRecordIso .std hL' hne').symm))⟩

end AddFree


end U2

/-! ### U3 infrastructure — the record rows (unit U3; PLAN_FINAL.md §4 "L-rec", §5 "U3 record rows")

Tools for the five L-rec leaves, on the record core U2: (A) the word combinatorics of `skein_unique`; (B) a
record isomorphism of the full `σ`-slot records from conjugate first returns to any active supersets
(`U3.recordIsoOfConj`, the generalisation of `U2.extRecordIso` needed when the block itself carries `σ`
letters — the commutation and the cusp-skein switch), the glue of two subtype bijections
(`U3.glueEquiv`), and conjugation from explicit paths (`U3.conj_of_paths`); (C) the letter-local
successor computations on a block (straight passes, the three letter kinds); (D)-(G) the concrete block
passages of the zigzag, the circle, the commutation and the cusp skein. -/

namespace U3

open SM.FrontRealize SM.FrontWord.Letter Equiv U2

/-! #### A. Word combinatorics for `skein_unique` -/

/-- Two pairs of lists, each pair differing at the end of its common prefix and agreeing on the prefix,
have the same prefix and correspond letter by letter. -/
theorem two_appends_eq {X X₂ Y₁ Y₂ Y₃ Y₄ : Word} {a b a₂ b₂ : Letter} (hab : a ≠ b) (hab₂ : a₂ ≠ b₂)
    (h1 : X ++ a :: Y₁ = X₂ ++ a₂ :: Y₃) (h2 : X ++ b :: Y₂ = X₂ ++ b₂ :: Y₄) :
    X = X₂ ∧ a = a₂ ∧ b = b₂ ∧ Y₁ = Y₃ ∧ Y₂ = Y₄ := by
  induction X generalizing X₂ with
  | nil =>
    cases X₂ with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h1 h2
      exact ⟨rfl, h1.1, h2.1, h1.2, h2.2⟩
    | cons x X₂ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h1 h2
      exact absurd (h1.1.trans h2.1.symm) hab
  | cons x X ih =>
    cases X₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h1 h2
      exact absurd (h1.1.symm.trans h2.1) hab₂
    | cons x₂ X₂ =>
      simp only [List.cons_append, List.cons.injEq] at h1 h2
      obtain ⟨rfl, h1⟩ := h1
      obtain ⟨-, h2⟩ := h2
      obtain ⟨rfl, h3, h4, h5, h6⟩ := ih h1 h2
      exact ⟨rfl, h3, h4, h5, h6⟩

/-- The same principal direction twice: the interchange data agree, so the smoothings agree. -/
theorem skeinStep_unique {A A' C C' : Word} (h : IsCuspSkeinStep A A' C) (h' : IsCuspSkeinStep A A' C') :
    C = C' := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, hA, hA', hC⟩ := h
  obtain ⟨X₂, Y₂, m₂, d₂, a₂, P₂, L₂, hm₂, hX₂, hP₂, hA₂, hA'₂, hC₂⟩ := h'
  have e1 : X ++ (Letter.l (m + 1) d) :: (Letter.σ m :: Y) = X₂ ++ (Letter.l (m₂ + 1) d₂) :: (Letter.σ m₂ :: Y₂) := by
    simpa using hA.symm.trans hA₂
  have e2 : X ++ (Letter.l m d) :: (Letter.σ (m + 1) :: Y) = X₂ ++ (Letter.l m₂ d₂) :: (Letter.σ (m₂ + 1) :: Y₂) := by
    simpa using hA'.symm.trans hA'₂
  have hab : Letter.l (m + 1) d ≠ Letter.l m d := by intro h; injection h with h1; omega
  have hab₂ : Letter.l (m₂ + 1) d₂ ≠ Letter.l m₂ d₂ := by intro h; injection h with h1; omega
  obtain ⟨rfl, hl, -, hY, -⟩ := two_appends_eq hab hab₂ e1 e2
  simp only [Letter.l.injEq, List.cons.injEq, Letter.σ.injEq] at hl hY
  obtain ⟨hmm, rfl⟩ := hl
  obtain ⟨-, rfl⟩ := hY
  have hmm' : m = m₂ := by omega
  subst hmm'
  rw [hX] at hX₂
  have hPP : P ++ a :: L = P₂ ++ a₂ :: L₂ := Option.some.inj hX₂
  obtain ⟨-, hal⟩ := List.append_inj hPP (hP.trans hP₂.symm)
  obtain ⟨rfl, -⟩ := List.cons.inj hal
  rcases hC with ⟨had, rfl⟩ | ⟨had, rfl⟩ <;> rcases hC₂ with ⟨had₂, rfl⟩ | ⟨had₂, rfl⟩
  · rfl
  · exact absurd (had.symm.trans had₂) (by cases d <;> simp)
  · exact absurd (had.symm.trans had₂) (by cases d <;> simp)
  · rfl

/-- The two principal directions cannot both hold for one pair `(A, A')`: the cusp letters would satisfy
`l (m+1) = l m'` and `l m = l (m'+1)`. -/
theorem skeinStep_not_both {A A' C C' : Word} (h : IsCuspSkeinStep A A' C) (h' : IsCuspSkeinStep A' A C') :
    False := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, hA, hA', -⟩ := h
  obtain ⟨X₂, Y₂, m₂, d₂, a₂, P₂, L₂, hm₂, hX₂, hP₂, hA'₂, hA₂, -⟩ := h'
  have e1 : X ++ (Letter.l (m + 1) d) :: (Letter.σ m :: Y) = X₂ ++ (Letter.l m₂ d₂) :: (Letter.σ (m₂ + 1) :: Y₂) := by
    simpa using hA.symm.trans hA₂
  have e2 : X ++ (Letter.l m d) :: (Letter.σ (m + 1) :: Y) = X₂ ++ (Letter.l (m₂ + 1) d₂) :: (Letter.σ m₂ :: Y₂) := by
    simpa using hA'.symm.trans hA'₂
  have hab : Letter.l (m + 1) d ≠ Letter.l m d := by intro h; injection h with h1; omega
  have hab₂ : Letter.l m₂ d₂ ≠ Letter.l (m₂ + 1) d₂ := by intro h; injection h with h1; omega
  obtain ⟨rfl, hl, hl', -, -⟩ := two_appends_eq hab hab₂ e1 e2
  injection hl with hl1 hl2
  injection hl' with hl3 hl4
  omega

/-! #### B. Records from conjugate first returns to active supersets (generic) -/

section Generic

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Glueing two subtype bijections along disjoint predicates. -/
noncomputable def glueEquiv (p q : α → Prop) (p' q' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpq : ∀ a, p a → ¬ q a) (hpq' : ∀ b, p' b → ¬ q' b)
    (φ₁ : {a // p a} ≃ {b // p' b}) (φ₂ : {a // q a} ≃ {b // q' b}) : {a // p a ∨ q a} ≃ {b // p' b ∨ q' b} where
  toFun a := if h : p a.1 then ⟨(φ₁ ⟨a.1, h⟩).1, Or.inl (φ₁ ⟨a.1, h⟩).2⟩
    else ⟨(φ₂ ⟨a.1, a.2.resolve_left h⟩).1, Or.inr (φ₂ ⟨a.1, a.2.resolve_left h⟩).2⟩
  invFun b := if h : p' b.1 then ⟨(φ₁.symm ⟨b.1, h⟩).1, Or.inl (φ₁.symm ⟨b.1, h⟩).2⟩
    else ⟨(φ₂.symm ⟨b.1, b.2.resolve_left h⟩).1, Or.inr (φ₂.symm ⟨b.1, b.2.resolve_left h⟩).2⟩
  left_inv a := by
    apply Subtype.ext
    by_cases h : p a.1
    · simp only [h, ↓reduceDIte, (φ₁ ⟨a.1, h⟩).2]
      rw [show (⟨(φ₁ ⟨a.1, h⟩).1, (φ₁ ⟨a.1, h⟩).2⟩ : {b // p' b}) = φ₁ ⟨a.1, h⟩ from rfl, Equiv.symm_apply_apply]
    · have hq := a.2.resolve_left h
      have h' : ¬ p' (φ₂ ⟨a.1, hq⟩).1 := fun hp' => hpq' _ hp' (φ₂ ⟨a.1, hq⟩).2
      simp only [h, ↓reduceDIte, h']
      rw [show (⟨(φ₂ ⟨a.1, hq⟩).1, _⟩ : {b // q' b}) = φ₂ ⟨a.1, hq⟩ from rfl, Equiv.symm_apply_apply]
  right_inv b := by
    apply Subtype.ext
    by_cases h : p' b.1
    · simp only [h, ↓reduceDIte, (φ₁.symm ⟨b.1, h⟩).2]
      rw [show (⟨(φ₁.symm ⟨b.1, h⟩).1, (φ₁.symm ⟨b.1, h⟩).2⟩ : {a // p a}) = φ₁.symm ⟨b.1, h⟩ from rfl,
        Equiv.apply_symm_apply]
    · have hq := b.2.resolve_left h
      have h' : ¬ p (φ₂.symm ⟨b.1, hq⟩).1 := fun hp => hpq _ hp (φ₂.symm ⟨b.1, hq⟩).2
      simp only [h, ↓reduceDIte, h']
      rw [show (⟨(φ₂.symm ⟨b.1, hq⟩).1, _⟩ : {a // q a}) = φ₂.symm ⟨b.1, hq⟩ from rfl, Equiv.apply_symm_apply]

omit [Fintype α] [Fintype β] in
theorem glueEquiv_val_left (p q : α → Prop) (p' q' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpq : ∀ a, p a → ¬ q a) (hpq' : ∀ b, p' b → ¬ q' b)
    (φ₁ : {a // p a} ≃ {b // p' b}) (φ₂ : {a // q a} ≃ {b // q' b}) (a : {a // p a ∨ q a}) (h : p a.1) :
    (glueEquiv p q p' q' hpq hpq' φ₁ φ₂ a).1 = (φ₁ ⟨a.1, h⟩).1 := by
  simp only [glueEquiv, Equiv.coe_fn_mk, h, ↓reduceDIte]

omit [Fintype α] [Fintype β] in
theorem glueEquiv_val_right (p q : α → Prop) (p' q' : β → Prop) [DecidablePred p] [DecidablePred p']
    (hpq : ∀ a, p a → ¬ q a) (hpq' : ∀ b, p' b → ¬ q' b)
    (φ₁ : {a // p a} ≃ {b // p' b}) (φ₂ : {a // q a} ≃ {b // q' b}) (a : {a // p a ∨ q a}) (h : ¬ p a.1) :
    (glueEquiv p q p' q' hpq hpq' φ₁ φ₂ a).1 = (φ₂ ⟨a.1, a.2.resolve_left h⟩).1 := by
  simp only [glueEquiv, Equiv.coe_fn_mk, h, ↓reduceDIte]

variable (f : Perm α) (g : Perm β) (E : α → Prop) (E' : β → Prop) [DecidablePred E] [DecidablePred E']
  (φ : {a // E a} ≃ {b // E' b})

/-- Conjugation of the first returns from explicit paths on both sides. -/
theorem conj_of_paths
    (h : ∀ u : {a // E a}, ∃ (m m' : ℕ) (_ : 0 < m) (_ : 0 < m') (hE : E ((f ^ m) u.1)),
      (∀ i, 0 < i → i < m → ¬ E ((f ^ i) u.1)) ∧ (∀ i, 0 < i → i < m' → ¬ E' ((g ^ i) (φ u).1)) ∧
      (g ^ m') (φ u).1 = (φ ⟨(f ^ m) u.1, hE⟩).1) :
    ∀ u, firstReturn g E' (φ u) = φ (firstReturn f E u) := by
  intro u
  obtain ⟨m, m', hm, hm', hE, hmin, hmin', heq⟩ := h u
  have h1 : firstReturn f E u = ⟨(f ^ m) u.1, hE⟩ := Subtype.ext (firstReturn_eq_of_path f E u hm hE hmin)
  rw [h1]
  apply Subtype.ext
  have hE' : E' ((g ^ m') (φ u).1) := by rw [heq]; exact (φ _).2
  rw [firstReturn_eq_of_path g E' (φ u) hm' hE' hmin']
  exact heq

end Generic

section RecIso

variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed)
  (E : Slot W → Prop) (E' : Slot W' → Prop) [DecidablePred E] [DecidablePred E']
  (φ : {u // E u} ≃ {u' // E' u'})

/-- `conj_of_paths` for the slot successor, with iterates. -/
theorem conj_of_paths_next
    (h : ∀ u : {u // E u}, ∃ (m m' : ℕ) (_ : 0 < m) (_ : 0 < m') (hE : E ((next hW)^[m] u.1)),
      (∀ i, 0 < i → i < m → ¬ E ((next hW)^[i] u.1)) ∧ (∀ i, 0 < i → i < m' → ¬ E' ((next hW')^[i] (φ u).1)) ∧
      (next hW')^[m'] (φ u).1 = (φ ⟨(next hW)^[m] u.1, hE⟩).1) :
    ∀ u, firstReturn (nextPerm hW') E' (φ u) = φ (firstReturn (nextPerm hW) E u) := by
  apply conj_of_paths
  intro u
  obtain ⟨m, m', hm, hm', hE, hmin, hmin', heq⟩ := h u
  refine ⟨m, m', hm, hm', by rw [nextPerm_pow_apply]; exact hE, ?_, ?_, ?_⟩
  · intro i hi him; rw [nextPerm_pow_apply]; exact hmin i hi him
  · intro i hi him; rw [nextPerm_pow_apply]; exact hmin' i hi him
  · have e1 : (nextPerm hW' ^ m') (φ u).1 = (next hW')^[m'] (φ u).1 := nextPerm_pow_apply hW' m' _
    rw [e1, heq]
    exact congrArg (fun x : {u // E u} => (φ x).1) (Subtype.ext (nextPerm_pow_apply hW m u.1).symm)

/-- THE RECORD ISOMORPHISM FROM CONJUGATE FIRST RETURNS: active supersets `E ⊇ IsσSlot`, `E' ⊇ IsσSlot`
of the two words, conjugate first returns under `φ`, every component meeting `E` resp. `E'`, and `φ`
carrying `σ` slots to `σ` slots with twins, over bits and signs — the full `σ`-slot records are
isomorphic (`U2.extRecordIso` is the case `E = ExtPiece`). -/
noncomputable def recordIsoOfConj
    (conj : ∀ u, firstReturn (nextPerm hW') E' (φ u) = φ (firstReturn (nextPerm hW) E u))
    (hexit : ∀ u : Slot W, ∃ n : ℕ, E ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot W', ∃ n : ℕ, E' ((next hW')^[n] u'))
    (hσE : ∀ u, IsσSlot u → E u) (hσE' : ∀ u', IsσSlot u' → E' u')
    (hσ : ∀ u : {u // E u}, IsσSlot (φ u).1 ↔ IsσSlot u.1)
    (htwin : ∀ (u : {u // E u}) (hu : IsσSlot u.1),
      (φ ⟨σtwin hW u.1, hσE _ (isσSlot_σtwin hW hu)⟩).1 = σtwin hW' (φ u).1)
    (hdesc : ∀ u : {u // E u}, IsσSlot u.1 → isDesc (φ u).1 = isDesc u.1)
    (hsgn : ∀ u : {u // E u}, IsσSlot u.1 → σsgn (φ u).1 = σsgn u.1) :
    RecordIso (slotRecord hW IsσSlot (allActive hW)) (slotRecord hW' IsσSlot (allActive hW')) :=
  let hexitP : ∀ u : Slot W, ∃ n : ℕ, E (((nextPerm hW) ^ n) u) := fun u => by
    obtain ⟨n, hn⟩ := hexit u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let hexitP' : ∀ u' : Slot W', ∃ n : ℕ, E' (((nextPerm hW') ^ n) u') := fun u => by
    obtain ⟨n, hn⟩ := hexit' u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let oe : Orbit hW ≃ Orbit hW' := cycleEquiv (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP'
  { e := (Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))
    Φ := { toFun := fun u => ⟨(φ ⟨u.1, hσE _ u.2⟩).1, (hσ _).2 u.2⟩
           invFun := fun u' => ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, by
             have h := (hσ (φ.symm ⟨u'.1, hσE' _ u'.2⟩)).1
             rw [Equiv.apply_symm_apply] at h
             exact h u'.2⟩
           left_inv := fun u => Subtype.ext (by
             show (φ.symm ⟨(φ ⟨u.1, hσE _ u.2⟩).1, _⟩).1 = u.1
             rw [show (⟨(φ ⟨u.1, hσE _ u.2⟩).1, _⟩ : {u' // E' u'}) = φ ⟨u.1, hσE _ u.2⟩ from rfl,
               Equiv.symm_apply_apply])
           right_inv := fun u' => Subtype.ext (by
             show (φ ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩).1 = u'.1
             rw [show (⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩ : {u // E u}) = φ.symm ⟨u'.1, hσE' _ u'.2⟩ from rfl,
               Equiv.apply_symm_apply]) }
    comp_eq := fun u => by
      show slotComp hW' (φ ⟨u.1, hσE _ u.2⟩).1 =
        ((Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))) (slotComp hW u.1)
      rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      congr 1
      show orbitOf hW' _ = cycleEquiv (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP' (orbitOf hW u.1)
      exact (cycleEquiv_mk (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP' ⟨u.1, hσE _ u.2⟩).symm
    succ_eq := fun u => by
      apply Subtype.ext
      show (φ ⟨(firstReturn (nextPerm hW) IsσSlot u).1, _⟩).1 =
        (firstReturn (nextPerm hW') IsσSlot ⟨(φ ⟨u.1, _⟩).1, _⟩).1
      exact (firstReturn_conj_of_factor (nextPerm hW) (nextPerm hW') E E' φ conj IsσSlot IsσSlot hσE hσE' hσ u).symm
    pair_eq := fun u => by
      apply Subtype.ext
      show (φ ⟨σtwin hW u.1, _⟩).1 = σtwin hW' (φ ⟨u.1, _⟩).1
      exact htwin ⟨u.1, hσE _ u.2⟩ u.2
    bit_eq := fun u => hdesc ⟨u.1, hσE _ u.2⟩ u.2
    sgn_eq := fun u => hsgn ⟨u.1, hσE _ u.2⟩ u.2 }

end RecIso

/-! #### C. Letter-local successor computations on a block -/

section Local

variable {V : Word} (hV : V.Closed)

omit hV in
theorem colOf_val {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) :
    colOf s = if p = 0 then k else if bit V k p then k else k - 1 := by
  obtain ⟨⟨k', p'⟩, hs'⟩ := s
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl⟩ := hs
  rfl

include hV

/-- every slot's column is a real column -/
theorem slot_col_lt {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) : k < V.length := by
  have h := s.2
  rw [hs] at h
  rcases h with ⟨-, hk, -⟩ | ⟨h1, h2, -⟩
  · exact hk
  · exact (cutSlot_pos hV h1 h2).2

theorem cutSlot_facts {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) :
    1 ≤ p ∧ p ≤ (cut V k).length ∧ 0 < k ∧ k < V.length := by
  have h := s.2
  rw [hs] at h
  rcases h with ⟨h0, -, -⟩ | ⟨h1, h2, -⟩
  · exact absurd h0 hp
  · obtain ⟨hk0, hk⟩ := cutSlot_pos hV h1 h2
    exact ⟨h1, h2, hk0, hk⟩

omit hV in
theorem vertex_lt {s : Slot V} {k : ℕ} (hs : s.1 = (k, 0)) : k < V.length := by
  have h := s.2
  rw [hs] at h
  rcases h with ⟨-, hk, -⟩ | ⟨h1, -, -⟩
  · exact hk
  · simp at h1

omit hV in
theorem vertex_not_crossing {s : Slot V} {k : ℕ} (hs : s.1 = (k, 0)) : (letterAt V k).isCrossing = false := by
  have h := s.2
  rw [hs] at h
  rcases h with ⟨-, -, hσ⟩ | ⟨h1, -, -⟩
  · exact hσ
  · simp at h1

theorem letter_idx_pos {k : ℕ} (hk : k < V.length) : 1 ≤ (letterAt V k).idx := by
  obtain ⟨D⟩ := decomp hV k hk
  exact D.hm

/-- bits above a letter are unchanged across its column -/
theorem bit_succ_of_lt {k p : ℕ} (hk : k < V.length) (hp1 : 1 ≤ p) (hp : p < (letterAt V k).idx) :
    bit V (k + 1) p = bit V k p := by
  obtain ⟨D⟩ := decomp hV k hk
  rw [bit_eq, bit_eq]
  exact D.getD_above hp1 hp

/-- bits below a letter are unchanged across its column, shifted by its strand-count change -/
theorem bit_succ_of_ge {k p : ℕ} (hk : k < V.length) (hp : (letterAt V k).idx + (letterAt V k).arity ≤ p) :
    bit V (k + 1) (p + (letterAt V k).coarity - (letterAt V k).arity) = bit V k p := by
  obtain ⟨D⟩ := decomp hV k hk
  rw [bit_eq, bit_eq]
  exact D.getD_below hp

/-- (1) a rightward strand above the letter passes the column -/
theorem next_right_lt {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true)
    (hlt : p < (letterAt V k).idx) :
    (next hV s).1 = (k + 1, p) ∧ bit V (k + 1) p = true := by
  obtain ⟨hp1, -, -, hk⟩ := cutSlot_facts hV hs hp
  refine ⟨?_, ?_⟩
  · rw [next_val, hs, nextPair_right V hp hb (posR_of_lt hlt)]
  · rw [bit_succ_of_lt hV hk hp1 hlt, hb]

/-- (2) a rightward strand below the letter passes the column, shifted -/
theorem next_right_ge {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true)
    (hge : (letterAt V k).idx + (letterAt V k).arity ≤ p) :
    (next hV s).1 = (k + 1, p + (letterAt V k).coarity - (letterAt V k).arity) ∧
      bit V (k + 1) (p + (letterAt V k).coarity - (letterAt V k).arity) = true := by
  obtain ⟨-, -, -, hk⟩ := cutSlot_facts hV hs hp
  refine ⟨?_, ?_⟩
  · rw [next_val, hs, nextPair_right V hp hb (posR_of_ge hge)]
  · rw [bit_succ_of_ge hV hk hge, hb]

/-- (3) a leftward strand above the letter of the previous column passes it -/
theorem next_left_lt {s : Slot V} {k q : ℕ} (hs : s.1 = (k, q)) (hq : q ≠ 0) (hb : bit V k q = false)
    (hlt : q < (letterAt V (k - 1)).idx) :
    (next hV s).1 = (k - 1, q) ∧ bit V (k - 1) q = false := by
  obtain ⟨hq1, -, hk0, hk⟩ := cutSlot_facts hV hs hq
  refine ⟨?_, ?_⟩
  · rw [next_val, hs, nextPair_left V hq hb (posL_of_lt hlt)]
  · have := bit_succ_of_lt hV (k := k - 1) (by omega) hq1 hlt
    rw [Nat.sub_add_cancel hk0] at this
    rw [← this, hb]

/-- (4) a leftward strand below the letter of the previous column passes it, shifted -/
theorem next_left_ge {s : Slot V} {k q : ℕ} (hs : s.1 = (k, q)) (hq : q ≠ 0) (hb : bit V k q = false)
    (hge : (letterAt V (k - 1)).idx + (letterAt V (k - 1)).coarity ≤ q) :
    (next hV s).1 = (k - 1, q + (letterAt V (k - 1)).arity - (letterAt V (k - 1)).coarity) ∧
      bit V (k - 1) (q + (letterAt V (k - 1)).arity - (letterAt V (k - 1)).coarity) = false := by
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hV hs hq
  refine ⟨?_, ?_⟩
  · rw [next_val, hs, nextPair_left V hq hb (posL_of_ge hge)]
  · have := bit_succ_of_ge hV (k := k - 1) (p := q + (letterAt V (k - 1)).arity - (letterAt V (k - 1)).coarity)
      (by omega) (by omega)
    rw [Nat.sub_add_cancel hk0, show q + (letterAt V (k - 1)).arity - (letterAt V (k - 1)).coarity +
      (letterAt V (k - 1)).coarity - (letterAt V (k - 1)).arity = q by omega] at this
    rw [← this, hb]

/-! the crossing letter -/

omit hV in
theorem lt_length_of_letterAt_σ {k j : ℕ} (hℓ : letterAt V k = .σ j) : k < V.length := by
  by_contra h
  rw [not_lt] at h
  unfold letterAt at hℓ
  rw [List.getD_eq_default _ _ h] at hℓ
  cases hℓ

theorem σ_idx_pos {k j : ℕ} (hℓ : letterAt V k = .σ j) : 1 ≤ j :=
  (σ_facts hV (lt_length_of_letterAt_σ hℓ) hℓ).1

theorem next_σ_right_idx {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .σ j) (hs : s.1 = (k, j))
    (hb : bit V k j = true) : (next hV s).1 = (k + 1, j + 1) := by
  have hj := σ_idx_pos hV hℓ
  rw [next_val, hs, nextPair_right V (by omega) hb (by rw [hℓ]; exact posR_σ_idx j)]

theorem next_σ_right_succ {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .σ j) (hs : s.1 = (k, j + 1))
    (hb : bit V k (j + 1) = true) : (next hV s).1 = (k + 1, j) := by
  rw [next_val, hs, nextPair_right V (by omega) hb (by rw [hℓ]; exact posR_σ_idx_succ j)]

theorem next_σ_left_idx {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .σ j) (hs : s.1 = (k + 1, j))
    (hb : bit V (k + 1) j = false) : (next hV s).1 = (k, j + 1) := by
  have hj := σ_idx_pos hV hℓ
  rw [next_val, hs, nextPair_left V (by omega) hb (by rw [Nat.add_sub_cancel, hℓ]; exact posL_σ_idx j)]
  simp

theorem next_σ_left_succ {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .σ j) (hs : s.1 = (k + 1, j + 1))
    (hb : bit V (k + 1) (j + 1) = false) : (next hV s).1 = (k, j) := by
  rw [next_val, hs, nextPair_left V (by omega) hb (by rw [Nat.add_sub_cancel, hℓ]; exact posL_σ_idx_succ j)]
  simp

/-! the left cusp -/

theorem l_bits {k j : ℕ} {d : Bool} (hk : k < V.length) (hℓ : letterAt V k = .l j d) :
    1 ≤ j ∧ bit V (k + 1) j = d ∧ bit V (k + 1) (j + 1) = !d := by
  obtain ⟨D⟩ := decomp hV k hk
  rw [hℓ] at D
  obtain ⟨h1, h2, -⟩ := D.bits_l
  refine ⟨D.hm, ?_, ?_⟩
  · rw [bit_eq]; exact h1
  · rw [bit_succ]; exact h2

theorem next_cusp_l {s : Slot V} {k j : ℕ} {d : Bool} (hℓ : letterAt V k = .l j d) (hs : s.1 = (k, 0)) :
    (next hV s).1 = (k + 1, if d then j else j + 1) := by
  rw [next_val, hs, nextPair_cusp_l V hℓ]

/-- the leftward arm of a left cusp enters its vertex -/
theorem next_arm_l {s : Slot V} {k j q : ℕ} {d : Bool} (hk : k < V.length) (hℓ : letterAt V k = .l j d)
    (hs : s.1 = (k + 1, q)) (hq : q = j ∨ q = j + 1) (hb : bit V (k + 1) q = false) :
    (next hV s).1 = (k, 0) := by
  have hj := (l_bits hV hk hℓ).1
  rw [next_val, hs, nextPair_left_none V (by omega) hb (by
    rw [Nat.add_sub_cancel, hℓ]
    rcases hq with h | h <;> rw [h]
    · exact posL_l_idx _ _
    · exact posL_l_idx_succ _ _)]
  simp

/-! the right cusp -/

theorem r_bits {k j : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .r j) :
    1 ≤ j ∧ bit V k j ≠ bit V k (j + 1) := by
  obtain ⟨D⟩ := decomp hV k hk
  rw [hℓ] at D
  obtain ⟨h1, -⟩ := D.bits_r
  refine ⟨D.hm, ?_⟩
  rw [bit_eq, bit_succ]; exact h1

theorem next_cusp_r {s : Slot V} {k j : ℕ} (hℓ : letterAt V k = .r j) (hs : s.1 = (k, 0)) :
    (next hV s).1 = (k, if bit V k j then j + 1 else j) := by
  rw [next_val, hs, nextPair_cusp_r V hℓ]

/-- the rightward arm of a right cusp enters its vertex -/
theorem next_arm_r {s : Slot V} {k j p : ℕ} (hk : k < V.length) (hℓ : letterAt V k = .r j)
    (hs : s.1 = (k, p)) (hp : p = j ∨ p = j + 1) (hb : bit V k p = true) :
    (next hV s).1 = (k, 0) := by
  have hj := (r_bits hV hk hℓ).1
  rw [next_val, hs, nextPair_right_none V (by omega) hb (by
    rw [hℓ]
    rcases hp with h | h <;> rw [h]
    · exact posR_r_idx _
    · exact posR_r_idx_succ _)]

/-! cuts and letters of a block -/

omit hV in
theorem letterAt_block (X P Y : Word) {i : ℕ} (hi : i < P.length) :
    letterAt (X ++ P ++ Y) (X.length + i) = P.getD i (.l 0 false) := by
  unfold letterAt
  rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
    List.getD_append _ _ _ _ hi]

omit hV in
theorem cut_start (X P Y : Word) {c₀ : Cuts} (hX : Word.run X [] = some c₀) : cut (X ++ P ++ Y) X.length = c₀ := by
  unfold cut
  rw [List.append_assoc, List.take_left' rfl, hX]; rfl

theorem cut_succ_of {k : ℕ} (hk : k < V.length) {ℓ : Letter} {c c' : Cuts} (hℓ : letterAt V k = ℓ)
    (hc : cut V k = c) (hstep : ℓ.step c = some c') : cut V (k + 1) = c' := by
  have := step_cut V hV hk
  rw [hℓ, hc, hstep] at this
  exact (Option.some.inj this).symm

/-- reaching an exterior piece: the recursion -/
theorem reach_of_next {E : Slot V → Prop} {u : Slot V} (h : ∃ n, E ((next hV)^[n] (next hV u))) :
    ∃ n, E ((next hV)^[n] u) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

theorem reach_self {E : Slot V → Prop} {u : Slot V} (h : E u) : ∃ n, E ((next hV)^[n] u) := ⟨0, h⟩

end Local

/-! #### D. Block passages: the generic bookkeeping -/

section Passages

variable {V : Word} (hV : V.Closed)
include hV

omit hV in
theorem block_col_true {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true) :
    colOf s = k := by
  rw [colOf_val hs]; simp [hp, hb]

omit hV in
theorem block_col_false {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = false) :
    colOf s = k - 1 := by
  rw [colOf_val hs]; simp [hp, hb]

omit hV in
theorem block_col_vertex {s : Slot V} {k : ℕ} (hs : s.1 = (k, 0)) : colOf s = k := by
  rw [colOf_val hs]; simp

/-- one more step of a block passage (the current slot is inside the block) -/
theorem passage_step (Ext : ℕ → Prop) {b c : Slot V} (hb : ¬ Ext (colOf b))
    (h : ∃ n, (next hV)^[n] (next hV b) = c ∧ ∀ i < n, ¬ Ext (colOf ((next hV)^[i] (next hV b)))) :
    ∃ n, (next hV)^[n] b = c ∧ ∀ i < n, ¬ Ext (colOf ((next hV)^[i] b)) := by
  obtain ⟨n, hc, hmin⟩ := h
  refine ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hc, ?_⟩
  intro i hi
  cases i with
  | zero => simpa using hb
  | succ i => rw [Function.iterate_succ_apply]; exact hmin i (by omega)

theorem passage_end {Ext : ℕ → Prop} {b : Slot V} :
    ∃ n, (next hV)^[n] b = b ∧ ∀ i < n, ¬ Ext (colOf ((next hV)^[i] b)) :=
  ⟨0, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

end Passages

/-! #### E. The zigzag deletion (ng:deletions, `l_m r_{m+1}` below / `l_{m+1} r_m` above) -/

section Zigzag

variable (X Y : Word) (m : ℕ) (d : Bool)

theorem zb_letters :
    letterAt (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) X.length = .l m d ∧
    letterAt (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) (X.length + 1) = .r (m + 1) := by
  constructor
  · have := letterAt_block X [Letter.l m d, Letter.r (m + 1)] Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X [Letter.l m d, Letter.r (m + 1)] Y (i := 1) (by simp)
    simpa using this

theorem zb_length : (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem bool_eq_of_not_ne {d b : Bool} (h : (!d) ≠ b) : b = d := by cases d <;> cases b <;> simp_all

variable (hW : (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y).Closed)
include hW

/-- the bits of the middle cut at the zigzag: `d`, `!d` (the arms), `d` (the strand below) -/
theorem zb_bits :
    bit (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) (X.length + 1) m = d ∧
    bit (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) (X.length + 1) (m + 1) = !d ∧
    bit (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y) (X.length + 1) (m + 2) = d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := zb_letters X Y m d
  have hk₀ : X.length < (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y).length := by rw [zb_length]; omega
  have hk₁ : X.length + 1 < (X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y).length := by rw [zb_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, h3⟩ := r_bits hW hk₁ hℓ₁
  rw [h2] at h3
  exact ⟨h1, h2, bool_eq_of_not_ne h3⟩

local notation "Vz" => X ++ [Letter.l m d, Letter.r (m + 1)] ++ Y
local notation "Pz" => [Letter.l m d, Letter.r (m + 1)]

omit hW in
theorem zb_extCol (k : ℕ) : ExtCol X Pz k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by
  unfold ExtCol; simp

omit hW in
theorem zb_shift : shiftIdx X Pz [] (X.length + 2) = X.length := by
  unfold shiftIdx; simp

/-! the successor table of the block `l_m r_{m+1}` (columns `|X|`, `|X|+1`) -/

theorem zb_T1 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vz X.length p = true)
    (hpm : p < m) : (next hW s).1 = (X.length + 1, p) ∧ bit Vz (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(zb_letters X Y m d).1]; exact hpm)

theorem zb_T2 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vz X.length p = true)
    (hpm : m ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Vz (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(zb_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(zb_letters X Y m d).1] at this

theorem zb_T3 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vz (X.length + 1) p = true) (hpm : p < m + 1) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vz (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(zb_letters X Y m d).2]; exact hpm)

theorem zb_T4 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vz (X.length + 1) p = true) (hpm : m + 3 ≤ p) :
    (next hW s).1 = (X.length + 2, p - 2) ∧ bit Vz (X.length + 2) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(zb_letters X Y m d).2]; simpa [idx, arity] using hpm)
  rw [(zb_letters X Y m d).2] at this
  simpa [coarity, arity] using this

theorem zb_T5 {s : Slot Vz} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p = m + 1 ∨ p = m + 2)
    (hb : bit Vz (X.length + 1) p = true) : (next hW s).1 = (X.length + 1, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (zb_letters X Y m d).2 hs (by omega) hb

theorem zb_T6 {s : Slot Vz} (hs : s.1 = (X.length + 1, 0)) :
    (next hW s).1 = (X.length + 1, if d then m + 1 else m + 2) := by
  rw [next_cusp_r hW (zb_letters X Y m d).2 hs, (zb_bits X Y m d hW).2.1]
  cases d <;> rfl

theorem zb_T7 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vz (X.length + 1) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length, q) ∧ bit Vz X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (zb_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem zb_T8 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m ∨ q = m + 1)
    (hb : bit Vz (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (zb_letters X Y m d).1 hs hq hb

theorem zb_T9 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vz (X.length + 1) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Vz X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (zb_letters X Y m d).1]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, (zb_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem zb_T10 {s : Slot Vz} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m else m + 1) :=
  next_cusp_l hW (zb_letters X Y m d).1 hs

theorem zb_T11 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vz (X.length + 2) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vz (X.length + 1) q = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e, (zb_letters X Y m d).2]; exact hqm)
  rwa [e] at this

theorem zb_T12 {s : Slot Vz} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vz (X.length + 2) q = false) (hqm : m + 1 ≤ q) :
    (next hW s).1 = (X.length + 1, q + 2) ∧ bit Vz (X.length + 1) (q + 2) = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e, (zb_letters X Y m d).2]; simpa [idx, coarity] using hqm)
  rw [e, (zb_letters X Y m d).2] at this
  simpa [arity, coarity] using this

/-- the traversal from the left-cusp vertex reaches the exterior -/
theorem zb_reach_v0 {u : Slot Vz} (hu : u.1 = (X.length, 0)) :
    ∃ n, ExtPiece X Pz Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3⟩ := zb_bits X Y m d hW
  have hm1 : 1 ≤ m := (l_bits hW (vertex_lt hu) (zb_letters X Y m d).1).1
  have h1 := zb_T10 X Y m d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Vz (X.length + 1) m = true := by rw [B1, hd]
    obtain ⟨h2, hb2⟩ := zb_T3 X Y m d hW h1 (by omega) hb1 (by omega)
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pz (colOf _)
    rw [block_col_true h2 (by omega) hb2, zb_extCol]; omega
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Vz (X.length + 1) (m + 1) = true := by rw [B2, hd]; rfl
    have h2 := zb_T5 X Y m d hW h1 (Or.inl rfl) hb1
    have h3 := zb_T6 X Y m d hW h2
    rw [ite_eq_right (by simp [hd])] at h3
    have hb3 : bit Vz (X.length + 1) (m + 2) = false := by rw [B3, hd]
    obtain ⟨h4, hb4⟩ := zb_T9 X Y m d hW h3 (by omega) hb3 le_rfl
    refine reach_of_next hW (reach_of_next hW (reach_of_next hW (reach_of_next hW (reach_self hW ?_))))
    show ExtCol X Pz (colOf _)
    have hk := (cutSlot_facts hW h4 (by omega)).2.2.1
    rw [block_col_false h4 (by omega) hb4, zb_extCol]; omega

/-- the traversal from the right-cusp vertex reaches the exterior -/
theorem zb_reach_v1 {u : Slot Vz} (hu : u.1 = (X.length + 1, 0)) :
    ∃ n, ExtPiece X Pz Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3⟩ := zb_bits X Y m d hW
  have hm1 : 1 ≤ m := (l_bits hW (by have := vertex_lt hu; omega) (zb_letters X Y m d).1).1
  have h1 := zb_T6 X Y m d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Vz (X.length + 1) (m + 1) = false := by rw [B2, hd]; rfl
    have h2 := zb_T8 X Y m d hW h1 (Or.inr rfl) hb1
    exact reach_of_next hW (reach_of_next hW (zb_reach_v0 X Y m d hW h2))
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Vz (X.length + 1) (m + 2) = false := by rw [B3, hd]
    obtain ⟨h2, hb2⟩ := zb_T9 X Y m d hW h1 (by omega) hb1 le_rfl
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pz (colOf _)
    have hk := (cutSlot_facts hW h2 (by omega)).2.2.1
    rw [block_col_false h2 (by omega) hb2, zb_extCol]; omega

/-- every component of the zigzag word meets the exterior -/
theorem zb_hexit : ∀ u : Slot Vz, ∃ n, ExtPiece X Pz Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨B1, B2, B3⟩ := zb_bits X Y m d hW
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pz (colOf u)
  · exact reach_self hW hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, zb_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact zb_reach_v0 X Y m d hW hu
    · exact zb_reach_v1 X Y m d hW hu
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  have hm1 : 1 ≤ m := (l_bits hW (by rw [zb_length]; omega) (zb_letters X Y m d).1).1
  cases hb : bit Vz k p
  · rw [block_col_false hu hp hb, zb_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := zb_T7 X Y m d hW hu hp hb hpm
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pz (colOf _)
        have := (cutSlot_facts hW h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, zb_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have h1 := zb_T8 X Y m d hW hu (by omega) hb
        exact reach_of_next hW (zb_reach_v0 X Y m d hW h1)
      · obtain ⟨h1, hb1⟩ := zb_T9 X Y m d hW hu hp hb hpm2
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pz (colOf _)
        have := (cutSlot_facts hW h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, zb_extCol]; omega
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := zb_T11 X Y m d hW hu hp hb hpm
        rcases lt_or_ge p m with hpm' | hpm'
        · obtain ⟨h2, hb2⟩ := zb_T7 X Y m d hW h1 hp hb1 hpm'
          refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
          show ExtCol X Pz (colOf _)
          have := (cutSlot_facts hW h2 hp).2.2.1
          rw [block_col_false h2 hp hb2, zb_extCol]; omega
        · have h2 := zb_T8 X Y m d hW h1 (by omega) hb1
          exact reach_of_next hW (reach_of_next hW (zb_reach_v0 X Y m d hW h2))
      · obtain ⟨h1, hb1⟩ := zb_T12 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := zb_T9 X Y m d hW h1 (by omega) hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pz (colOf _)
        have := (cutSlot_facts hW h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, zb_extCol]; omega
  · rw [block_col_true hu hp hb, zb_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := zb_T1 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := zb_T3 X Y m d hW h1 hp hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pz (colOf _)
        rw [block_col_true h2 hp hb2, zb_extCol]; omega
      · obtain ⟨h1, hb1⟩ := zb_T2 X Y m d hW hu hp hb hpm
        rcases Nat.eq_or_lt_of_le hpm with rfl | hpm1
        · have h2 := zb_T5 X Y m d hW h1 (Or.inr rfl) hb1
          exact reach_of_next hW (reach_of_next hW (zb_reach_v1 X Y m d hW h2))
        · obtain ⟨h2, hb2⟩ := zb_T4 X Y m d hW h1 (by omega) hb1 (by omega)
          refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
          show ExtCol X Pz (colOf _)
          rw [block_col_true h2 (by omega) hb2, zb_extCol]; omega
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := zb_T3 X Y m d hW hu hp hb hpm
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pz (colOf _)
        rw [block_col_true h1 hp hb1, zb_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have h1 := zb_T5 X Y m d hW hu (by omega) hb
        exact reach_of_next hW (zb_reach_v1 X Y m d hW h1)
      · obtain ⟨h1, hb1⟩ := zb_T4 X Y m d hW hu hp hb hpm3
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pz (colOf _)
        rw [block_col_true h1 (by omega) hb1, zb_extCol]; omega

theorem zb_sameEffect : SameEffect X Pz [] := by
  have hm1 : 1 ≤ m := (l_bits hW (by rw [zb_length]; omega) (zb_letters X Y m d).1).1
  exact sameEffect_of_replace X Pz Y [] hW (fun c c' h => by obtain rfl := run_zigzag_below hm1 h; rfl)

/-- THE BLOCK PASSAGE of the zigzag `l_m r_{m+1}`: every entering strand exits at its own position. -/
theorem zb_passage (hW' : (X ++ [] ++ Y).Closed) : Passage X Pz Y [] hW hW' := by
  obtain ⟨hℓ₀, hℓ₁⟩ := zb_letters X Y m d
  obtain ⟨B1, B2, B3⟩ := zb_bits X Y m d hW
  have hm1 : 1 ≤ m := (l_bits hW (by rw [zb_length]; omega) hℓ₀).1
  have hP : Pz ≠ [] := by simp
  have hE := zb_sameEffect X Y m d hW
  constructor
  intro b hext hcol
  have side : ∀ {c : Slot Vz}, extPair X Pz [] b.1 = extPair X Pz [] c.1 →
      ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pz [] b.1 ∧
        ((next hW')^[m'] b').1 = extPair X Pz [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) :=
    fun hbc => ⟨0, ⟨_, isSlot_ext X Pz Y [] hP hE b.2 hext⟩, rfl, hbc, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  have shiftL : ∀ p, extPair X Pz [] (X.length, p) = extPair X Pz [] (X.length + 2, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pz [] le_rfl, zb_shift X m d]
  rcases (entry_iff X Pz Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := zb_T1 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := zb_T3 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
        (by rw [block_col_true hb hp hbit, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_true h1 hp hb1, zb_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 hp hb2, zb_extCol]; omega
      · rw [hb, h2]; exact shiftL p
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
    · -- `p = m`: through the zigzag
      obtain ⟨h1, hb1⟩ := zb_T2 X Y m d hW hb hp hbit hpm
      rw [← hpe] at h1 hb1
      have hd : d = true := by rw [B3] at hb1; exact hb1
      have h2 := zb_T5 X Y m d hW h1 (Or.inr rfl) hb1
      have h3 := zb_T6 X Y m d hW h2
      rw [ite_eq_left hd] at h3
      have hb3 : bit Vz (X.length + 1) (m + 1) = false := by rw [B2, hd]; rfl
      have h4 := zb_T8 X Y m d hW h3 (Or.inr rfl) hb3
      have h5 := zb_T10 X Y m d hW h4
      rw [ite_eq_left hd] at h5
      have hb5 : bit Vz (X.length + 1) m = true := by rw [B1, hd]
      obtain ⟨h6, hb6⟩ := zb_T3 X Y m d hW h5 (by omega) hb5 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
        (by rw [block_col_true hb hp hbit, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_true h1 (by omega) hb1, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_vertex h2, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_false h3 (by omega) hb3, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_vertex h4, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_true h5 (by omega) hb5, zb_extCol]; omega) (passage_end hW))))))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h6 (by omega) hb6, zb_extCol]; omega
      · rw [hb, h6, ← hpe]; exact shiftL m
    · obtain ⟨h1, hb1⟩ := zb_T2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := zb_T4 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
        (by rw [block_col_true hb hp hbit, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_true h1 (by omega) hb1, zb_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 (by omega) hb2, zb_extCol]; omega
      · rw [hb, h2, show p + 2 - 2 = p by omega]; exact shiftL p
  · -- from the right at `(|X|+2, p)`
    replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Vz (X.length + 2) p = false := hbit
    rcases lt_or_ge p (m + 1) with hpm | hpm
    · obtain ⟨h1, hb1⟩ := zb_T11 X Y m d hW hb hp hbit hpm
      rcases lt_or_ge p m with hpm' | hpm'
      · obtain ⟨h2, hb2⟩ := zb_T7 X Y m d hW h1 hp hb1 hpm'
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
          (by rw [block_col_false hb hp hbit, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_false h1 hp hb1, zb_extCol]; omega) (passage_end hW))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · have := (cutSlot_facts hW h2 hp).2.2.1
          rw [block_col_false h2 hp hb2, zb_extCol]; omega
        · rw [hb, h2]; exact (shiftL p).symm
      · -- `p = m`: through the zigzag, from the right
        have hpe : p = m := by omega
        rw [hpe] at h1 hb1
        have hd : d = false := by rw [B1] at hb1; exact hb1
        have h2 := zb_T8 X Y m d hW h1 (Or.inl rfl) hb1
        have h3 := zb_T10 X Y m d hW h2
        rw [ite_eq_right (by simp [hd])] at h3
        have hb3 : bit Vz (X.length + 1) (m + 1) = true := by rw [B2, hd]; rfl
        have h4 := zb_T5 X Y m d hW h3 (Or.inl rfl) hb3
        have h5 := zb_T6 X Y m d hW h4
        rw [ite_eq_right (by simp [hd])] at h5
        have hb5 : bit Vz (X.length + 1) (m + 2) = false := by rw [B3, hd]
        obtain ⟨h6, hb6⟩ := zb_T9 X Y m d hW h5 (by omega) hb5 le_rfl
        rw [show m + 2 - 2 = m by omega] at h6 hb6
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
          (by rw [block_col_false hb hp hbit, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_false h1 (by omega) hb1, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_vertex h2, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_true h3 (by omega) hb3, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_vertex h4, zb_extCol]; omega)
          (passage_step hW (ExtCol X Pz) (by rw [block_col_false h5 (by omega) hb5, zb_extCol]; omega) (passage_end hW))))))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · have := (cutSlot_facts hW h6 (by omega)).2.2.1
          rw [block_col_false h6 (by omega) hb6, zb_extCol]; omega
        · rw [hb, h6, hpe]; exact (shiftL m).symm
    · obtain ⟨h1, hb1⟩ := zb_T12 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := zb_T9 X Y m d hW h1 (by omega) hb1 (by omega)
      rw [show p + 2 - 2 = p by omega] at h2 hb2
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pz)
        (by rw [block_col_false hb hp hbit, zb_extCol]; omega)
        (passage_step hW (ExtCol X Pz) (by rw [block_col_false h1 (by omega) hb1, zb_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, zb_extCol]; omega
      · rw [hb, h2]; exact (shiftL p).symm

/-- LEAF `zigzag_recordIso`, the `l_m r_{m+1}` case. -/
theorem zb_recordIso (W W' : OWord) (hWeq : W.letters = Vz) (hW'eq : W'.letters = X ++ Y)
    (hne' : W'.letters ≠ []) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  have hW' : (X ++ [] ++ Y).Closed := by have := W'.closed; rw [hW'eq] at this; simpa using this
  refine realize_recordIso_of_ext X Pz Y [] (by simp) (zb_sameEffect X Y m d hW) hW hW' (by simp)
    (by rw [hW'eq] at hne'; simpa using hne') (zb_passage X Y m d hW hW') (zb_hexit X Y m d hW) ?_ ?_ ?_
    W W' hWeq (by simpa using hW'eq)
  · intro u; exact ⟨0, by show ExtCol X [] (colOf u); unfold ExtCol; simp; omega⟩
  · intro k hk1 hk2
    simp only [List.length_cons, List.length_nil] at hk2
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rw [(zb_letters X Y m d).1]; rfl
    · rw [(zb_letters X Y m d).2]; rfl
  · intro k hk1 hk2; simp at hk2; omega

end Zigzag

section ZigzagAbove

variable (X Y : Word) (m : ℕ) (d : Bool)

local notation "Va" => X ++ [Letter.l (m + 1) d, Letter.r m] ++ Y
local notation "Pa" => [Letter.l (m + 1) d, Letter.r m]

theorem za_letters : letterAt Va X.length = .l (m + 1) d ∧ letterAt Va (X.length + 1) = .r m := by
  constructor
  · have := letterAt_block X Pa Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pa Y (i := 1) (by simp)
    simpa using this

theorem za_length : (X ++ [Letter.l (m + 1) d, Letter.r m] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem za_extCol (k : ℕ) : ExtCol X Pa k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by
  unfold ExtCol; simp

theorem za_shift : shiftIdx X Pa [] (X.length + 2) = X.length := by
  unfold shiftIdx; simp

theorem bool_eq_not_of_ne {b d : Bool} (h : b ≠ d) : b = !d := by cases d <;> cases b <;> simp_all

variable (hW : (X ++ [Letter.l (m + 1) d, Letter.r m] ++ Y).Closed)
include hW

/-- the bits of the middle cut: `!d` (the strand above), `d`, `!d` (the arms) -/
theorem za_bits :
    bit Va (X.length + 1) m = !d ∧ bit Va (X.length + 1) (m + 1) = d ∧ bit Va (X.length + 1) (m + 2) = !d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := za_letters X Y m d
  have hk₀ : X.length < (Va).length := by rw [za_length]; omega
  have hk₁ : X.length + 1 < (Va).length := by rw [za_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hW hk₀ hℓ₀
  obtain ⟨-, h3⟩ := r_bits hW hk₁ hℓ₁
  rw [h1] at h3
  exact ⟨bool_eq_not_of_ne h3, h1, h2⟩

theorem za_m_pos : 1 ≤ m :=
  (r_bits hW (by rw [za_length]; omega) (za_letters X Y m d).2).1

theorem za_T1 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Va X.length p = true)
    (hpm : p < m + 1) : (next hW s).1 = (X.length + 1, p) ∧ bit Va (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(za_letters X Y m d).1]; exact hpm)

theorem za_T2 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Va X.length p = true)
    (hpm : m + 1 ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Va (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(za_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(za_letters X Y m d).1] at this

theorem za_T3 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Va (X.length + 1) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Va (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(za_letters X Y m d).2]; exact hpm)

theorem za_T4 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Va (X.length + 1) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p - 2) ∧ bit Va (X.length + 2) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(za_letters X Y m d).2]; simpa [idx, arity] using hpm)
  rw [(za_letters X Y m d).2] at this
  simpa [coarity, arity] using this

theorem za_T5 {s : Slot Va} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p = m ∨ p = m + 1)
    (hb : bit Va (X.length + 1) p = true) : (next hW s).1 = (X.length + 1, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (za_letters X Y m d).2 hs hp hb

theorem za_T6 {s : Slot Va} (hs : s.1 = (X.length + 1, 0)) :
    (next hW s).1 = (X.length + 1, if d then m else m + 1) := by
  rw [next_cusp_r hW (za_letters X Y m d).2 hs, (za_bits X Y m d hW).1]
  cases d <;> rfl

theorem za_T7 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 1) q = false) (hqm : q < m + 1) :
    (next hW s).1 = (X.length, q) ∧ bit Va X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (za_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem za_T8 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m + 1 ∨ q = m + 2)
    (hb : bit Va (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (za_letters X Y m d).1 hs hq hb

theorem za_T9 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 1) q = false) (hqm : m + 3 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Va X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (za_letters X Y m d).1]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, (za_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem za_T10 {s : Slot Va} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m + 1 else m + 2) :=
  next_cusp_l hW (za_letters X Y m d).1 hs

theorem za_T11 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 2) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Va (X.length + 1) q = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e, (za_letters X Y m d).2]; exact hqm)
  rwa [e] at this

theorem za_T12 {s : Slot Va} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Va (X.length + 2) q = false) (hqm : m ≤ q) :
    (next hW s).1 = (X.length + 1, q + 2) ∧ bit Va (X.length + 1) (q + 2) = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e, (za_letters X Y m d).2]; simpa [idx, coarity] using hqm)
  rw [e, (za_letters X Y m d).2] at this
  simpa [arity, coarity] using this

theorem za_reach_v0 {u : Slot Va} (hu : u.1 = (X.length, 0)) :
    ∃ n, ExtPiece X Pa Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3⟩ := za_bits X Y m d hW
  have hm1 := za_m_pos X Y m d hW
  have h1 := za_T10 X Y m d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Va (X.length + 1) (m + 1) = true := by rw [B2, hd]
    have h2 := za_T5 X Y m d hW h1 (Or.inr rfl) hb1
    have h3 := za_T6 X Y m d hW h2
    rw [ite_eq_left hd] at h3
    have hb3 : bit Va (X.length + 1) m = false := by rw [B1, hd]; rfl
    obtain ⟨h4, hb4⟩ := za_T7 X Y m d hW h3 (by omega) hb3 (by omega)
    refine reach_of_next hW (reach_of_next hW (reach_of_next hW (reach_of_next hW (reach_self hW ?_))))
    show ExtCol X Pa (colOf _)
    have hk := (cutSlot_facts hW h4 (by omega)).2.2.1
    rw [block_col_false h4 (by omega) hb4, za_extCol]; omega
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Va (X.length + 1) (m + 2) = true := by rw [B3, hd]; rfl
    obtain ⟨h2, hb2⟩ := za_T4 X Y m d hW h1 (by omega) hb1 le_rfl
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pa (colOf _)
    rw [block_col_true h2 (by omega) hb2, za_extCol]; omega

theorem za_reach_v1 {u : Slot Va} (hu : u.1 = (X.length + 1, 0)) :
    ∃ n, ExtPiece X Pa Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2, B3⟩ := za_bits X Y m d hW
  have hm1 := za_m_pos X Y m d hW
  have h1 := za_T6 X Y m d hW hu
  rcases Bool.eq_false_or_eq_true d with hd | hd
  · rw [ite_eq_left hd] at h1
    have hb1 : bit Va (X.length + 1) m = false := by rw [B1, hd]; rfl
    obtain ⟨h2, hb2⟩ := za_T7 X Y m d hW h1 (by omega) hb1 (by omega)
    refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
    show ExtCol X Pa (colOf _)
    have hk := (cutSlot_facts hW h2 (by omega)).2.2.1
    rw [block_col_false h2 (by omega) hb2, za_extCol]; omega
  · rw [ite_eq_right (by simp [hd])] at h1
    have hb1 : bit Va (X.length + 1) (m + 1) = false := by rw [B2, hd]
    have h2 := za_T8 X Y m d hW h1 (Or.inl rfl) hb1
    exact reach_of_next hW (reach_of_next hW (za_reach_v0 X Y m d hW h2))

theorem za_hexit : ∀ u : Slot Va, ∃ n, ExtPiece X Pa Y ((next hW)^[n] u) := by
  intro u
  obtain ⟨B1, B2, B3⟩ := za_bits X Y m d hW
  have hm1 := za_m_pos X Y m d hW
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pa (colOf u)
  · exact reach_self hW hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, za_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact za_reach_v0 X Y m d hW hu
    · exact za_reach_v1 X Y m d hW hu
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Va k p
  · rw [block_col_false hu hp hb, za_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := za_T7 X Y m d hW hu hp hb hpm
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pa (colOf _)
        have := (cutSlot_facts hW h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, za_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm2 | hpm2
      · have h1 := za_T8 X Y m d hW hu (by omega) hb
        exact reach_of_next hW (za_reach_v0 X Y m d hW h1)
      · obtain ⟨h1, hb1⟩ := za_T9 X Y m d hW hu hp hb hpm2
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pa (colOf _)
        have := (cutSlot_facts hW h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, za_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := za_T11 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := za_T7 X Y m d hW h1 hp hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pa (colOf _)
        have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, za_extCol]; omega
      · obtain ⟨h1, hb1⟩ := za_T12 X Y m d hW hu hp hb hpm
        rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
        · have h2 := za_T8 X Y m d hW h1 (by omega) hb1
          exact reach_of_next hW (reach_of_next hW (za_reach_v0 X Y m d hW h2))
        · obtain ⟨h2, hb2⟩ := za_T9 X Y m d hW h1 (by omega) hb1 (by omega)
          refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
          show ExtCol X Pa (colOf _)
          have := (cutSlot_facts hW h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2, za_extCol]; omega
  · rw [block_col_true hu hp hb, za_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := za_T1 X Y m d hW hu hp hb hpm
        rcases lt_or_ge p m with hpm' | hpm'
        · obtain ⟨h2, hb2⟩ := za_T3 X Y m d hW h1 hp hb1 hpm'
          refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
          show ExtCol X Pa (colOf _)
          rw [block_col_true h2 hp hb2, za_extCol]; omega
        · have h2 := za_T5 X Y m d hW h1 (by omega) hb1
          exact reach_of_next hW (reach_of_next hW (za_reach_v1 X Y m d hW h2))
      · obtain ⟨h1, hb1⟩ := za_T2 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := za_T4 X Y m d hW h1 (by omega) hb1 (by omega)
        refine reach_of_next hW (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pa (colOf _)
        rw [block_col_true h2 (by omega) hb2, za_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := za_T3 X Y m d hW hu hp hb hpm
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pa (colOf _)
        rw [block_col_true h1 hp hb1, za_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have h1 := za_T5 X Y m d hW hu (by omega) hb
        exact reach_of_next hW (za_reach_v1 X Y m d hW h1)
      · obtain ⟨h1, hb1⟩ := za_T4 X Y m d hW hu hp hb hpm2
        refine reach_of_next hW (reach_self hW ?_)
        show ExtCol X Pa (colOf _)
        rw [block_col_true h1 (by omega) hb1, za_extCol]; omega

theorem za_sameEffect : SameEffect X Pa [] := by
  have hm1 := za_m_pos X Y m d hW
  exact sameEffect_of_replace X Pa Y [] hW (fun c c' h => by obtain rfl := run_zigzag_above hm1 h; rfl)

/-- THE BLOCK PASSAGE of the zigzag `l_{m+1} r_m`. -/
theorem za_passage (hW' : (X ++ [] ++ Y).Closed) : Passage X Pa Y [] hW hW' := by
  obtain ⟨hℓ₀, hℓ₁⟩ := za_letters X Y m d
  obtain ⟨B1, B2, B3⟩ := za_bits X Y m d hW
  have hm1 := za_m_pos X Y m d hW
  have hP : Pa ≠ [] := by simp
  have hE := za_sameEffect X Y m d hW
  constructor
  intro b hext hcol
  have side : ∀ {c : Slot Va}, extPair X Pa [] b.1 = extPair X Pa [] c.1 →
      ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pa [] b.1 ∧
        ((next hW')^[m'] b').1 = extPair X Pa [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) :=
    fun hbc => ⟨0, ⟨_, isSlot_ext X Pa Y [] hP hE b.2 hext⟩, rfl, hbc, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  have shiftL : ∀ p, extPair X Pa [] (X.length, p) = extPair X Pa [] (X.length + 2, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pa [] le_rfl, za_shift X m d]
  rcases (entry_iff X Pa Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · rcases lt_or_ge p (m + 1) with hpm | hpm
    · obtain ⟨h1, hb1⟩ := za_T1 X Y m d hW hb hp hbit hpm
      rcases lt_or_ge p m with hpm' | hpm'
      · obtain ⟨h2, hb2⟩ := za_T3 X Y m d hW h1 hp hb1 hpm'
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
          (by rw [block_col_true hb hp hbit, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_true h1 hp hb1, za_extCol]; omega) (passage_end hW))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · rw [block_col_true h2 hp hb2, za_extCol]; omega
        · rw [hb, h2]; exact shiftL p
      · -- `p = m`: through the zigzag
        have hpe : p = m := by omega
        rw [hpe] at h1 hb1
        have hd : d = false := by rw [B1] at hb1; cases d <;> simp_all
        have h2 := za_T5 X Y m d hW h1 (Or.inl rfl) hb1
        have h3 := za_T6 X Y m d hW h2
        rw [ite_eq_right (by simp [hd])] at h3
        have hb3 : bit Va (X.length + 1) (m + 1) = false := by rw [B2, hd]
        have h4 := za_T8 X Y m d hW h3 (Or.inl rfl) hb3
        have h5 := za_T10 X Y m d hW h4
        rw [ite_eq_right (by simp [hd])] at h5
        have hb5 : bit Va (X.length + 1) (m + 2) = true := by rw [B3, hd]; rfl
        obtain ⟨h6, hb6⟩ := za_T4 X Y m d hW h5 (by omega) hb5 le_rfl
        rw [show m + 2 - 2 = m by omega] at h6 hb6
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
          (by rw [block_col_true hb hp hbit, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_true h1 (by omega) hb1, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_vertex h2, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_false h3 (by omega) hb3, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_vertex h4, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_true h5 (by omega) hb5, za_extCol]; omega)
            (passage_end hW))))))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · rw [block_col_true h6 (by omega) hb6, za_extCol]; omega
        · rw [hb, h6, hpe]; exact shiftL m
    · obtain ⟨h1, hb1⟩ := za_T2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := za_T4 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
        (by rw [block_col_true hb hp hbit, za_extCol]; omega)
        (passage_step hW (ExtCol X Pa) (by rw [block_col_true h1 (by omega) hb1, za_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 (by omega) hb2, za_extCol]; omega
      · rw [hb, h2, show p + 2 - 2 = p by omega]; exact shiftL p
  · replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Va (X.length + 2) p = false := hbit
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := za_T11 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := za_T7 X Y m d hW h1 hp hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
        (by rw [block_col_false hb hp hbit, za_extCol]; omega)
        (passage_step hW (ExtCol X Pa) (by rw [block_col_false h1 hp hb1, za_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, za_extCol]; omega
      · rw [hb, h2]; exact (shiftL p).symm
    · obtain ⟨h1, hb1⟩ := za_T12 X Y m d hW hb hp hbit hpm
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
      · -- `p = m`: through the zigzag, from the right
        rw [← hpe] at h1 hb1
        have hd : d = true := by rw [B3] at hb1; cases d <;> simp_all
        have h2 := za_T8 X Y m d hW h1 (Or.inr rfl) hb1
        have h3 := za_T10 X Y m d hW h2
        rw [ite_eq_left hd] at h3
        have hb3 : bit Va (X.length + 1) (m + 1) = true := by rw [B2, hd]
        have h4 := za_T5 X Y m d hW h3 (Or.inr rfl) hb3
        have h5 := za_T6 X Y m d hW h4
        rw [ite_eq_left hd] at h5
        have hb5 : bit Va (X.length + 1) m = false := by rw [B1, hd]; rfl
        obtain ⟨h6, hb6⟩ := za_T7 X Y m d hW h5 (by omega) hb5 (by omega)
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
          (by rw [block_col_false hb hp hbit, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_false h1 (by omega) hb1, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_vertex h2, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_true h3 (by omega) hb3, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_vertex h4, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_false h5 (by omega) hb5, za_extCol]; omega)
            (passage_end hW))))))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · have := (cutSlot_facts hW h6 (by omega)).2.2.1
          rw [block_col_false h6 (by omega) hb6, za_extCol]; omega
        · rw [hb, h6, ← hpe]; exact (shiftL m).symm
      · obtain ⟨h2, hb2⟩ := za_T9 X Y m d hW h1 (by omega) hb1 (by omega)
        rw [show p + 2 - 2 = p by omega] at h2 hb2
        obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pa)
          (by rw [block_col_false hb hp hbit, za_extCol]; omega)
          (passage_step hW (ExtCol X Pa) (by rw [block_col_false h1 (by omega) hb1, za_extCol]; omega) (passage_end hW))
        refine ⟨n, _, hc, ?_, hmin, side ?_⟩
        · have := (cutSlot_facts hW h2 hp).2.2.1
          rw [block_col_false h2 hp hb2, za_extCol]; omega
        · rw [hb, h2]; exact (shiftL p).symm

/-- LEAF `zigzag_recordIso`, the `l_{m+1} r_m` case. -/
theorem za_recordIso (W W' : OWord) (hWeq : W.letters = Va) (hW'eq : W'.letters = X ++ Y)
    (hne' : W'.letters ≠ []) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  have hW' : (X ++ [] ++ Y).Closed := by have := W'.closed; rw [hW'eq] at this; simpa using this
  refine realize_recordIso_of_ext X Pa Y [] (by simp) (za_sameEffect X Y m d hW) hW hW' (by simp)
    (by rw [hW'eq] at hne'; simpa using hne') (za_passage X Y m d hW hW') (za_hexit X Y m d hW) ?_ ?_ ?_
    W W' hWeq (by simpa using hW'eq)
  · intro u; exact ⟨0, by show ExtCol X [] (colOf u); unfold ExtCol; simp; omega⟩
  · intro k hk1 hk2
    simp only [List.length_cons, List.length_nil] at hk2
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rw [(za_letters X Y m d).1]; rfl
    · rw [(za_letters X Y m d).2]; rfl
  · intro k hk1 hk2; simp at hk2; omega

end ZigzagAbove

/-! #### F. The circle deletion (ng:circle, `l_m r_m` a separated standard circle) -/

section Circle

variable (X Y : Word) (m : ℕ) (d : Bool)

local notation "Vc" => X ++ [Letter.l m d, Letter.r m] ++ Y
local notation "Pc" => [Letter.l m d, Letter.r m]

theorem ci_letters : letterAt Vc X.length = .l m d ∧ letterAt Vc (X.length + 1) = .r m := by
  constructor
  · have := letterAt_block X Pc Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pc Y (i := 1) (by simp)
    simpa using this

theorem ci_length : (X ++ [Letter.l m d, Letter.r m] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem ci_extCol (k : ℕ) : ExtCol X Pc k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by
  unfold ExtCol; simp

theorem ci_shift : shiftIdx X Pc [] (X.length + 2) = X.length := by
  unfold shiftIdx; simp

variable (hW : (X ++ [Letter.l m d, Letter.r m] ++ Y).Closed)
include hW

theorem ci_bits : bit Vc (X.length + 1) m = d ∧ bit Vc (X.length + 1) (m + 1) = !d :=
  (l_bits hW (by rw [ci_length]; omega) (ci_letters X Y m d).1).2

theorem ci_m_pos : 1 ≤ m := (l_bits hW (by rw [ci_length]; omega) (ci_letters X Y m d).1).1

theorem ci_T1 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc X.length p = true)
    (hpm : p < m) : (next hW s).1 = (X.length + 1, p) ∧ bit Vc (X.length + 1) p = true :=
  next_right_lt hW hs hp hb (by rw [(ci_letters X Y m d).1]; exact hpm)

theorem ci_T2 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length, p)) (hp : p ≠ 0) (hb : bit Vc X.length p = true)
    (hpm : m ≤ p) : (next hW s).1 = (X.length + 1, p + 2) ∧ bit Vc (X.length + 1) (p + 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(ci_letters X Y m d).1]; simpa [idx, arity] using hpm)
  rwa [(ci_letters X Y m d).1] at this

theorem ci_T3 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 1) p = true) (hpm : p < m) :
    (next hW s).1 = (X.length + 2, p) ∧ bit Vc (X.length + 2) p = true :=
  next_right_lt hW hs hp hb (by rw [(ci_letters X Y m d).2]; exact hpm)

theorem ci_T4 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p ≠ 0)
    (hb : bit Vc (X.length + 1) p = true) (hpm : m + 2 ≤ p) :
    (next hW s).1 = (X.length + 2, p - 2) ∧ bit Vc (X.length + 2) (p - 2) = true := by
  have := next_right_ge hW hs hp hb (by rw [(ci_letters X Y m d).2]; simpa [idx, arity] using hpm)
  rw [(ci_letters X Y m d).2] at this
  simpa [coarity, arity] using this

theorem ci_T5 {s : Slot Vc} {p : ℕ} (hs : s.1 = (X.length + 1, p)) (hp : p = m ∨ p = m + 1)
    (hb : bit Vc (X.length + 1) p = true) : (next hW s).1 = (X.length + 1, 0) :=
  next_arm_r hW (slot_col_lt hW hs) (ci_letters X Y m d).2 hs hp hb

theorem ci_T6 {s : Slot Vc} (hs : s.1 = (X.length + 1, 0)) :
    (next hW s).1 = (X.length + 1, if d then m + 1 else m) := by
  rw [next_cusp_r hW (ci_letters X Y m d).2 hs, (ci_bits X Y m d hW).1]

theorem ci_T7 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 1) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length, q) ∧ bit Vc X.length q = false := by
  have := next_left_lt hW hs hq hb (by rw [Nat.add_sub_cancel, (ci_letters X Y m d).1]; exact hqm)
  rwa [Nat.add_sub_cancel] at this

theorem ci_T8 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q = m ∨ q = m + 1)
    (hb : bit Vc (X.length + 1) q = false) : (next hW s).1 = (X.length, 0) :=
  next_arm_l hW (by have := slot_col_lt hW hs; omega) (ci_letters X Y m d).1 hs hq hb

theorem ci_T9 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 1, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 1) q = false) (hqm : m + 2 ≤ q) :
    (next hW s).1 = (X.length, q - 2) ∧ bit Vc X.length (q - 2) = false := by
  have := next_left_ge hW hs hq hb (by rw [Nat.add_sub_cancel, (ci_letters X Y m d).1]; simpa [idx, coarity] using hqm)
  rw [Nat.add_sub_cancel, (ci_letters X Y m d).1] at this
  simpa [arity, coarity] using this

theorem ci_T10 {s : Slot Vc} (hs : s.1 = (X.length, 0)) :
    (next hW s).1 = (X.length + 1, if d then m else m + 1) :=
  next_cusp_l hW (ci_letters X Y m d).1 hs

theorem ci_T11 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 2) q = false) (hqm : q < m) :
    (next hW s).1 = (X.length + 1, q) ∧ bit Vc (X.length + 1) q = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_lt hW hs hq hb (by rw [e, (ci_letters X Y m d).2]; exact hqm)
  rwa [e] at this

theorem ci_T12 {s : Slot Vc} {q : ℕ} (hs : s.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hb : bit Vc (X.length + 2) q = false) (hqm : m ≤ q) :
    (next hW s).1 = (X.length + 1, q + 2) ∧ bit Vc (X.length + 1) (q + 2) = false := by
  have e : X.length + 2 - 1 = X.length + 1 := by omega
  have := next_left_ge hW hs hq hb (by rw [e, (ci_letters X Y m d).2]; simpa [idx, coarity] using hqm)
  rw [e, (ci_letters X Y m d).2] at this
  simpa [arity, coarity] using this

/-- the four slots of the separated circle -/
def InCirc (u : Slot Vc) : Prop :=
  u.1 = (X.length, 0) ∨ u.1 = (X.length + 1, if d then m else m + 1) ∨
  u.1 = (X.length + 1, 0) ∨ u.1 = (X.length + 1, if d then m + 1 else m)

omit hW in
theorem ci_bit_arm_true (B1 : bit Vc (X.length + 1) m = d) (B2 : bit Vc (X.length + 1) (m + 1) = !d) :
    bit Vc (X.length + 1) (if d then m else m + 1) = true := by
  cases d <;> simp_all

omit hW in
theorem ci_bit_arm_false (B1 : bit Vc (X.length + 1) m = d) (B2 : bit Vc (X.length + 1) (m + 1) = !d) :
    bit Vc (X.length + 1) (if d then m + 1 else m) = false := by
  cases d <;> simp_all

theorem inCirc_next {u : Slot Vc} (hu : InCirc X Y m d u) : InCirc X Y m d (next hW u) := by
  obtain ⟨B1, B2⟩ := ci_bits X Y m d hW
  have hm1 := ci_m_pos X Y m d hW
  rcases hu with hu | hu | hu | hu
  · exact Or.inr (Or.inl (ci_T10 X Y m d hW hu))
  · exact Or.inr (Or.inr (Or.inl (ci_T5 X Y m d hW hu (by split_ifs <;> simp) (ci_bit_arm_true X Y m d B1 B2))))
  · exact Or.inr (Or.inr (Or.inr (ci_T6 X Y m d hW hu)))
  · exact Or.inl (ci_T8 X Y m d hW hu (by split_ifs <;> simp) (ci_bit_arm_false X Y m d B1 B2))

theorem inCirc_iterate {u : Slot Vc} (hu : InCirc X Y m d u) (n : ℕ) : InCirc X Y m d ((next hW)^[n] u) := by
  induction n with
  | zero => exact hu
  | succ n ih => rw [Function.iterate_succ_apply']; exact inCirc_next X Y m d hW ih

theorem inCirc_not_ext {u : Slot Vc} (hu : InCirc X Y m d u) : ¬ ExtCol X Pc (colOf u) := by
  obtain ⟨B1, B2⟩ := ci_bits X Y m d hW
  have hm1 := ci_m_pos X Y m d hW
  rcases hu with hu | hu | hu | hu
  · rw [block_col_vertex hu, ci_extCol]; omega
  · rw [block_col_true hu (by split_ifs <;> omega) (ci_bit_arm_true X Y m d B1 B2), ci_extCol]; omega
  · rw [block_col_vertex hu, ci_extCol]; omega
  · rw [block_col_false hu (by split_ifs <;> omega) (ci_bit_arm_false X Y m d B1 B2), ci_extCol]; omega

/-- the left-cusp vertex of the circle -/
def circV : Slot Vc :=
  ⟨(X.length, 0), Or.inl ⟨rfl, by rw [ci_length]; omega, by rw [(ci_letters X Y m d).1]; rfl⟩⟩

omit hW in
theorem circV_val : (circV X Y m d).1 = (X.length, 0) := rfl

/-- the circle's slots all lie on the cycle of its vertex -/
theorem inCirc_sameCycle {u : Slot Vc} (hu : InCirc X Y m d u) :
    (nextPerm hW).SameCycle (circV X Y m d) u := by
  obtain ⟨B1, B2⟩ := ci_bits X Y m d hW
  have h1 := ci_T10 X Y m d hW (circV_val X Y m d)
  have h2 := ci_T5 X Y m d hW h1 (by split_ifs <;> simp) (ci_bit_arm_true X Y m d B1 B2)
  have h3 := ci_T6 X Y m d hW h2
  rcases hu with hu | hu | hu | hu
  · exact sameCycle_of_iterate hW (a := 0) (b := 0) (Subtype.ext (hu.symm.trans rfl))
  · exact sameCycle_of_iterate hW (a := 1) (b := 0) (Subtype.ext (h1.trans hu.symm))
  · exact sameCycle_of_iterate hW (a := 2) (b := 0) (Subtype.ext (h2.trans hu.symm))
  · exact sameCycle_of_iterate hW (a := 3) (b := 0) (Subtype.ext (h3.trans hu.symm))

/-- every slot lies on the circle or reaches the exterior -/
theorem ci_reach_or (u : Slot Vc) : InCirc X Y m d u ∨ ∃ n, ExtPiece X Pc Y ((next hW)^[n] u) := by
  obtain ⟨B1, B2⟩ := ci_bits X Y m d hW
  have hm1 := ci_m_pos X Y m d hW
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pc (colOf u)
  · exact Or.inr (reach_self hW hext)
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, ci_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact Or.inl (Or.inl hu)
    · exact Or.inl (Or.inr (Or.inr (Or.inl hu)))
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hW hu hp
  cases hb : bit Vc k p
  · rw [block_col_false hu hp hb, ci_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := ci_T7 X Y m d hW hu hp hb hpm
        refine Or.inr (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, ci_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · left; right; right; right
        rw [hu]
        rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · rw [← hpe] at hb; rw [B1] at hb; rw [hb, ← hpe]; rfl
        · have hpe' : p = m + 1 := by omega
          rw [hpe'] at hb; rw [B2] at hb
          have hd : d = true := by cases d <;> simp_all
          rw [hpe', hd]; rfl
      · obtain ⟨h1, hb1⟩ := ci_T9 X Y m d hW hu hp hb hpm2
        refine Or.inr (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, ci_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := ci_T11 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := ci_T7 X Y m d hW h1 hp hb1 hpm
        refine Or.inr (reach_of_next hW (reach_of_next hW (reach_self hW ?_)))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, ci_extCol]; omega
      · obtain ⟨h1, hb1⟩ := ci_T12 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := ci_T9 X Y m d hW h1 (by omega) hb1 (by omega)
        refine Or.inr (reach_of_next hW (reach_of_next hW (reach_self hW ?_)))
        show ExtCol X Pc (colOf _)
        have := (cutSlot_facts hW h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, ci_extCol]; omega
  · rw [block_col_true hu hp hb, ci_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := ci_T1 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := ci_T3 X Y m d hW h1 hp hb1 hpm
        refine Or.inr (reach_of_next hW (reach_of_next hW (reach_self hW ?_)))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h2 hp hb2, ci_extCol]; omega
      · obtain ⟨h1, hb1⟩ := ci_T2 X Y m d hW hu hp hb hpm
        obtain ⟨h2, hb2⟩ := ci_T4 X Y m d hW h1 (by omega) hb1 (by omega)
        refine Or.inr (reach_of_next hW (reach_of_next hW (reach_self hW ?_)))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h2 (by omega) hb2, ci_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := ci_T3 X Y m d hW hu hp hb hpm
        refine Or.inr (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h1 hp hb1, ci_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · left; right; left
        rw [hu]
        rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · rw [← hpe] at hb; rw [B1] at hb; rw [hb, ← hpe]; rfl
        · have hpe' : p = m + 1 := by omega
          rw [hpe'] at hb; rw [B2] at hb
          have hd : d = false := by cases d <;> simp_all
          rw [hpe', hd]; rfl
      · obtain ⟨h1, hb1⟩ := ci_T4 X Y m d hW hu hp hb hpm2
        refine Or.inr (reach_of_next hW (reach_self hW ?_))
        show ExtCol X Pc (colOf _)
        rw [block_col_true h1 (by omega) hb1, ci_extCol]; omega

/-- exactly the circle misses the exterior -/
theorem ci_hc₀ (u : Slot Vc) :
    (¬ ∃ n, ExtPiece X Pc Y ((next hW)^[n] u)) ↔ orbitOf hW u = orbitOf hW (circV X Y m d) := by
  constructor
  · intro hn
    rcases ci_reach_or X Y m d hW u with hu | hu
    · rw [orbitOf_eq_iff]
      exact (inCirc_sameCycle X Y m d hW hu).symm
    · exact absurd hu hn
  · intro ho
    rw [orbitOf_eq_iff] at ho
    obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW ho.symm
    rintro ⟨j, hj⟩
    have hu : InCirc X Y m d u := by
      rw [← hn]; exact inCirc_iterate X Y m d hW (Or.inl rfl) n
    exact inCirc_not_ext X Y m d hW (inCirc_iterate X Y m d hW hu j) hj

theorem ci_sameEffect : SameEffect X Pc [] := by
  have hm1 := ci_m_pos X Y m d hW
  exact sameEffect_of_replace X Pc Y [] hW (fun c c' h => by obtain rfl := run_circle hm1 h; rfl)

/-- THE BLOCK PASSAGE of the circle block: every entering strand exits at its own position. -/
theorem ci_passage (hW' : (X ++ [] ++ Y).Closed) : Passage X Pc Y [] hW hW' := by
  have hm1 := ci_m_pos X Y m d hW
  have hP : Pc ≠ [] := by simp
  have hE := ci_sameEffect X Y m d hW
  constructor
  intro b hext hcol
  have side : ∀ {c : Slot Vc}, extPair X Pc [] b.1 = extPair X Pc [] c.1 →
      ∃ (m' : ℕ) (b' : Slot (X ++ [] ++ Y)), b'.1 = extPair X Pc [] b.1 ∧
        ((next hW')^[m'] b').1 = extPair X Pc [] c.1 ∧ ∀ i < m', ¬ ExtCol X [] (colOf ((next hW')^[i] b')) :=
    fun hbc => ⟨0, ⟨_, isSlot_ext X Pc Y [] hP hE b.2 hext⟩, rfl, hbc, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  have shiftL : ∀ p, extPair X Pc [] (X.length, p) = extPair X Pc [] (X.length + 2, p) := by
    intro p; simp only [extPair, shiftIdx_of_le X Pc [] le_rfl, ci_shift X m d]
  rcases (entry_iff X Pc Y hP hW b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := ci_T1 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := ci_T3 X Y m d hW h1 hp hb1 hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc)
        (by rw [block_col_true hb hp hbit, ci_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h1 hp hb1, ci_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 hp hb2, ci_extCol]; omega
      · rw [hb, h2]; exact shiftL p
    · obtain ⟨h1, hb1⟩ := ci_T2 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := ci_T4 X Y m d hW h1 (by omega) hb1 (by omega)
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc)
        (by rw [block_col_true hb hp hbit, ci_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_true h1 (by omega) hb1, ci_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · rw [block_col_true h2 (by omega) hb2, ci_extCol]; omega
      · rw [hb, h2, show p + 2 - 2 = p by omega]; exact shiftL p
  · replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Vc (X.length + 2) p = false := hbit
    rcases lt_or_ge p m with hpm | hpm
    · obtain ⟨h1, hb1⟩ := ci_T11 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := ci_T7 X Y m d hW h1 hp hb1 hpm
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc)
        (by rw [block_col_false hb hp hbit, ci_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 hp hb1, ci_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, ci_extCol]; omega
      · rw [hb, h2]; exact (shiftL p).symm
    · obtain ⟨h1, hb1⟩ := ci_T12 X Y m d hW hb hp hbit hpm
      obtain ⟨h2, hb2⟩ := ci_T9 X Y m d hW h1 (by omega) hb1 (by omega)
      rw [show p + 2 - 2 = p by omega] at h2 hb2
      obtain ⟨n, hc, hmin⟩ := passage_step hW (ExtCol X Pc)
        (by rw [block_col_false hb hp hbit, ci_extCol]; omega)
        (passage_step hW (ExtCol X Pc) (by rw [block_col_false h1 (by omega) hb1, ci_extCol]; omega) (passage_end hW))
      refine ⟨n, _, hc, ?_, hmin, side ?_⟩
      · have := (cutSlot_facts hW h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, ci_extCol]; omega
      · rw [hb, h2]; exact (shiftL p).symm

/-- LEAF `circle_recordIso_addFree`. -/
theorem ci_recordIso (W W' : OWord) (hWeq : W.letters = Vc) (hW'eq : W'.letters = X ++ Y)
    (hne' : X ++ Y ≠ []) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := by
  have hW' : (X ++ [] ++ Y).Closed := by have := W'.closed; rw [hW'eq] at this; simpa using this
  refine realize_recordIso_addFree_of_ext X Pc Y [] (by simp) (ci_sameEffect X Y m d hW) hW hW' (by simp)
    (by simpa using hne') (ci_passage X Y m d hW hW') ?_ (orbitOf hW (circV X Y m d)) (ci_hc₀ X Y m d hW)
    ?_ ?_ W W' hWeq (by simpa using hW'eq)
  · intro u; exact ⟨0, by show ExtCol X [] (colOf u); unfold ExtCol; simp; omega⟩
  · intro k hk1 hk2
    simp only [List.length_cons, List.length_nil] at hk2
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rw [(ci_letters X Y m d).1]; rfl
    · rw [(ci_letters X Y m d).2]; rfl
  · intro k hk1 hk2; simp at hk2; omega

end Circle

/-! #### G. Blocks with interior `σ` slots: the extended passage hypothesis and the switch variant -/

/-- one more step of a passage for a slot predicate -/
theorem apassage_step {V : Word} (hV : V.Closed) (Q : Slot V → Prop) {b c : Slot V} (hb : ¬ Q b)
    (h : ∃ n, (next hV)^[n] (next hV b) = c ∧ ∀ i < n, ¬ Q ((next hV)^[i] (next hV b))) :
    ∃ n, (next hV)^[n] b = c ∧ ∀ i < n, ¬ Q ((next hV)^[i] b) := by
  obtain ⟨n, hc, hmin⟩ := h
  refine ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hc, ?_⟩
  intro i hi
  cases i with
  | zero => simpa using hb
  | succ i => rw [Function.iterate_succ_apply]; exact hmin i (by omega)

theorem apassage_end {V : Word} (hV : V.Closed) (Q : Slot V → Prop) {b : Slot V} :
    ∃ n, (next hV)^[n] b = b ∧ ∀ i < n, ¬ Q ((next hV)^[i] b) :=
  ⟨0, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

/-- the positive-length version, for the interior clause -/
theorem apassage_pos {V : Word} (hV : V.Closed) (Q : Slot V → Prop) {u c : Slot V}
    (h : ∃ n, (next hV)^[n] (next hV u) = c ∧ ∀ i < n, ¬ Q ((next hV)^[i] (next hV u))) :
    ∃ (m : ℕ) (_ : 0 < m), (next hV)^[m] u = c ∧ ∀ i, 0 < i → i < m → ¬ Q ((next hV)^[i] u) := by
  obtain ⟨n, hc, hmin⟩ := h
  refine ⟨n + 1, Nat.succ_pos _, by rw [Function.iterate_succ_apply]; exact hc, ?_⟩
  intro i hi him
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [Function.iterate_succ_apply]; exact hmin i' (by omega)


section IntPassage

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
  (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed)

/-- the interior `σ` slots of the block -/
def IntSlot (u : Slot (X ++ P ++ Y)) : Prop := IsσSlot u ∧ ¬ ExtCol X P (colOf u)

instance : DecidablePred (IntSlot X P Y) := fun u => by unfold IntSlot; infer_instance

/-- the active superset: exterior pieces and interior `σ` slots -/
def ActE (u : Slot (X ++ P ++ Y)) : Prop := ExtPiece X P Y u ∨ IntSlot X P Y u

instance : DecidablePred (ActE X P Y) := fun u => by unfold ActE; infer_instance

theorem isσSlot_actE {u : Slot (X ++ P ++ Y)} (hu : IsσSlot u) : ActE X P Y u := by
  by_cases h : ExtCol X P (colOf u)
  · exact Or.inl h
  · exact Or.inr ⟨hu, h⟩

theorem not_actE_of {u : Slot (X ++ P ++ Y)} (h1 : ¬ ExtCol X P (colOf u)) (h2 : ¬ IsσSlot u) :
    ¬ ActE X P Y u := by
  rintro (h | h)
  · exact h1 h
  · exact h2 h.1

variable (φI : {u // IntSlot X P Y u} ≃ {u' // IntSlot X P' Y u'})
include hP hE hW

/-- the glued correspondence of the active supersets -/
noncomputable def φA : {u // ActE X P Y u} ≃ {u' // ActE X P' Y u'} :=
  glueEquiv (ExtPiece X P Y) (IntSlot X P Y) (ExtPiece X P' Y) (IntSlot X P' Y)
    (fun _ h h' => h'.2 h) (fun _ h h' => h'.2 h) (φE X P Y P' hP hE hW) φI

theorem φA_val_ext (u : {u // ActE X P Y u}) (h : ExtPiece X P Y u.1) :
    (φA X P Y P' hP hE hW φI u).1 = (φE X P Y P' hP hE hW ⟨u.1, h⟩).1 :=
  glueEquiv_val_left _ _ _ _ _ _ _ _ u h

theorem φA_val_int (u : {u // ActE X P Y u}) (h : ¬ ExtPiece X P Y u.1) :
    (φA X P Y P' hP hE hW φI u).1 = (φI ⟨u.1, u.2.resolve_left h⟩).1 :=
  glueEquiv_val_right _ _ _ _ _ _ _ _ u h

theorem φA_val_ext' (u : {u // ActE X P Y u}) (h : ExtPiece X P Y u.1) :
    (φA X P Y P' hP hE hW φI u).1.1 = extPair X P P' u.1.1 := by
  rw [φA_val_ext X P Y P' hP hE hW φI u h]; rfl

/-- THE EXTENDED BLOCK PASSAGE HYPOTHESIS: from every entry the traversal reaches an active slot
(exterior piece or interior `σ` slot), with the corresponding path in `W'`; from every interior `σ`
slot likewise. -/
structure IntPassage : Prop where
  entry : ∀ b : Slot (X ++ P ++ Y), IsExtSlot X P b.1 → ¬ ExtCol X P (colOf b) →
    ∃ (m : ℕ) (c : Slot (X ++ P ++ Y)) (hc : ActE X P Y c), (next hW)^[m] b = c ∧
      (∀ i < m, ¬ ActE X P Y ((next hW)^[i] b)) ∧
      ∃ (m' : ℕ) (b' : Slot (X ++ P' ++ Y)), b'.1 = extPair X P P' b.1 ∧
        (next hW')^[m'] b' = (φA X P Y P' hP hE hW φI ⟨c, hc⟩).1 ∧
        ∀ i < m', ¬ ActE X P' Y ((next hW')^[i] b')
  interior : ∀ (u : Slot (X ++ P ++ Y)) (hu : IntSlot X P Y u),
    ∃ (m : ℕ) (_ : 0 < m) (c : Slot (X ++ P ++ Y)) (hc : ActE X P Y c), (next hW)^[m] u = c ∧
      (∀ i, 0 < i → i < m → ¬ ActE X P Y ((next hW)^[i] u)) ∧
      ∃ (m' : ℕ), 0 < m' ∧ (next hW')^[m'] (φI ⟨u, hu⟩).1 = (φA X P Y P' hP hE hW φI ⟨c, hc⟩).1 ∧
        ∀ i, 0 < i → i < m' → ¬ ActE X P' Y ((next hW')^[i] (φI ⟨u, hu⟩).1)

/-- the extended passage makes the first returns to the active supersets conjugate -/
theorem conj_of_intPassage (hpass : IntPassage X P Y P' hP hE hW hW' φI) (u : {u // ActE X P Y u}) :
    firstReturn (nextPerm hW') (ActE X P' Y) (φA X P Y P' hP hE hW φI u) =
      φA X P Y P' hP hE hW φI (firstReturn (nextPerm hW) (ActE X P Y) u) := by
  revert u
  apply conj_of_paths_next
  intro u
  by_cases hext : ExtPiece X P Y u.1
  · obtain ⟨hnext_ext, hnext_eq⟩ :=
      next_ext X P Y P' hP hE hW hW' ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 hext⟩ hext
    have hφu : (φA X P Y P' hP hE hW φI u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 hext⟩ :=
      φA_val_ext X P Y P' hP hE hW φI u hext
    by_cases hE1 : ExtCol X P (colOf (next hW u.1))
    · refine ⟨1, 1, one_pos, one_pos, Or.inl hE1, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
        fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _), ?_⟩
      apply Subtype.ext
      rw [Function.iterate_one, hφu, hnext_eq]
      exact (φA_val_ext' X P Y P' hP hE hW φI ⟨_, Or.inl hE1⟩ hE1).symm
    · obtain ⟨m₀, c, hc, hmc, hmin, m₀', b', hb', hm', hmin'⟩ := hpass.entry (next hW u.1) hnext_ext hE1
      have hb'' : next hW' (φA X P Y P' hP hE hW φI u).1 = b' := Subtype.ext (by rw [hφu, hnext_eq, hb'])
      refine ⟨m₀ + 1, m₀' + 1, Nat.succ_pos _, Nat.succ_pos _, by rw [Function.iterate_succ_apply, hmc]; exact hc, ?_, ?_, ?_⟩
      · intro i hi him
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Function.iterate_succ_apply]; exact hmin i' (by omega)
      · intro i hi him
        obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [Function.iterate_succ_apply, hb'']; exact hmin' i' (by omega)
      · rw [Function.iterate_succ_apply, hb'', hm']
        exact congrArg (fun x : {u // ActE X P Y u} => (φA X P Y P' hP hE hW φI x).1) (Subtype.ext hmc.symm)
  · have hu : IntSlot X P Y u.1 := u.2.resolve_left hext
    obtain ⟨m, hm, c, hc, hmc, hmin, m', hm', heq, hmin'⟩ := hpass.interior u.1 hu
    have hφu : (φA X P Y P' hP hE hW φI u).1 = (φI ⟨u.1, hu⟩).1 := φA_val_int X P Y P' hP hE hW φI u hext
    refine ⟨m, m', hm, hm', by rw [hmc]; exact hc, hmin, ?_, ?_⟩
    · intro i hi him; rw [hφu]; exact hmin' i hi him
    · rw [hφu, heq]
      exact congrArg (fun x : {u // ActE X P Y u} => (φA X P Y P' hP hE hW φI x).1) (Subtype.ext hmc.symm)

end IntPassage

section RecIsoSwitch

variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed)
  (E : Slot W → Prop) (E' : Slot W' → Prop) [DecidablePred E] [DecidablePred E']
  (φ : {u // E u} ≃ {u' // E' u'})

/-- THE RECORD ISOMORPHISM ONTO A SWITCHED RECORD: as `recordIsoOfConj`, but the over bits and signs
are reversed exactly on the slots `S` carried to the switched crossing `{x₀, σtwin x₀}`. -/
noncomputable def recordIsoOfConjSwitch
    (conj : ∀ u, firstReturn (nextPerm hW') E' (φ u) = φ (firstReturn (nextPerm hW) E u))
    (hexit : ∀ u : Slot W, ∃ n : ℕ, E ((next hW)^[n] u))
    (hexit' : ∀ u' : Slot W', ∃ n : ℕ, E' ((next hW')^[n] u'))
    (hσE : ∀ u, IsσSlot u → E u) (hσE' : ∀ u', IsσSlot u' → E' u')
    (hσ : ∀ u : {u // E u}, IsσSlot (φ u).1 ↔ IsσSlot u.1)
    (htwin : ∀ (u : {u // E u}) (hu : IsσSlot u.1),
      (φ ⟨σtwin hW u.1, hσE _ (isσSlot_σtwin hW hu)⟩).1 = σtwin hW' (φ u).1)
    (x₀ : (slotRecord hW' IsσSlot (allActive hW')).M) (S : Slot W → Prop)
    (hS : ∀ u : {u // E u}, IsσSlot u.1 → (((φ u).1 = x₀.1 ∨ (φ u).1 = σtwin hW' x₀.1) ↔ S u.1))
    (hdescS : ∀ u : {u // E u}, IsσSlot u.1 → S u.1 → isDesc (φ u).1 = !isDesc u.1)
    (hdescN : ∀ u : {u // E u}, IsσSlot u.1 → ¬ S u.1 → isDesc (φ u).1 = isDesc u.1)
    (hsgnS : ∀ u : {u // E u}, IsσSlot u.1 → S u.1 → σsgn (φ u).1 = -σsgn u.1)
    (hsgnN : ∀ u : {u // E u}, IsσSlot u.1 → ¬ S u.1 → σsgn (φ u).1 = σsgn u.1) :
    RecordIso (slotRecord hW IsσSlot (allActive hW)) ((slotRecord hW' IsσSlot (allActive hW')).switch x₀) :=
  let hexitP : ∀ u : Slot W, ∃ n : ℕ, E (((nextPerm hW) ^ n) u) := fun u => by
    obtain ⟨n, hn⟩ := hexit u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let hexitP' : ∀ u' : Slot W', ∃ n : ℕ, E' (((nextPerm hW') ^ n) u') := fun u => by
    obtain ⟨n, hn⟩ := hexit' u; exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩
  let oe : Orbit hW ≃ Orbit hW' := cycleEquiv (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP'
  let Φ : (slotRecord hW IsσSlot (allActive hW)).M ≃ (slotRecord hW' IsσSlot (allActive hW')).M :=
    { toFun := fun u => ⟨(φ ⟨u.1, hσE _ u.2⟩).1, (hσ _).2 u.2⟩
      invFun := fun u' => ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, by
        have h := (hσ (φ.symm ⟨u'.1, hσE' _ u'.2⟩)).1
        rw [Equiv.apply_symm_apply] at h
        exact h u'.2⟩
      left_inv := fun u => Subtype.ext (by
        show (φ.symm ⟨(φ ⟨u.1, hσE _ u.2⟩).1, _⟩).1 = u.1
        rw [show (⟨(φ ⟨u.1, hσE _ u.2⟩).1, _⟩ : {u' // E' u'}) = φ ⟨u.1, hσE _ u.2⟩ from rfl,
          Equiv.symm_apply_apply])
      right_inv := fun u' => Subtype.ext (by
        show (φ ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩).1 = u'.1
        rw [show (⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩ : {u // E u}) = φ.symm ⟨u'.1, hσE' _ u'.2⟩ from rfl,
          Equiv.apply_symm_apply]) }
  have hmem : ∀ u : (slotRecord hW IsσSlot (allActive hW)).M,
      Φ u ∈ ({x₀, (slotRecord hW' IsσSlot (allActive hW')).pair x₀} :
        Finset (slotRecord hW' IsσSlot (allActive hW')).M) ↔ S u.1 := by
    intro u
    rw [Finset.mem_insert, Finset.mem_singleton, ← hS ⟨u.1, hσE _ u.2⟩ u.2]
    constructor
    · rintro (h | h)
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr ((congrArg Subtype.val h).trans (slotRecord_pair_val hW' _ _ x₀))
    · rintro (h | h)
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext (h.trans (slotRecord_pair_val hW' _ _ x₀).symm))
  { e := (Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))
    Φ := Φ
    comp_eq := fun u => by
      show slotComp hW' (φ ⟨u.1, hσE _ u.2⟩).1 =
        ((Fintype.equivFin (Orbit hW)).symm.trans (oe.trans (Fintype.equivFin (Orbit hW')))) (slotComp hW u.1)
      rw [slotComp_eq_equivFin, slotComp_eq_equivFin]
      simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
      congr 1
      show orbitOf hW' _ = cycleEquiv (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP' (orbitOf hW u.1)
      exact (cycleEquiv_mk (nextPerm hW) (nextPerm hW') E E' φ conj hexitP hexitP' ⟨u.1, hσE _ u.2⟩).symm
    succ_eq := fun u => by
      apply Subtype.ext
      show (φ ⟨(firstReturn (nextPerm hW) IsσSlot u).1, _⟩).1 =
        (firstReturn (nextPerm hW') IsσSlot ⟨(φ ⟨u.1, _⟩).1, _⟩).1
      exact (firstReturn_conj_of_factor (nextPerm hW) (nextPerm hW') E E' φ conj IsσSlot IsσSlot hσE hσE' hσ u).symm
    pair_eq := fun u => by
      apply Subtype.ext
      show (φ ⟨σtwin hW u.1, _⟩).1 = σtwin hW' (φ ⟨u.1, _⟩).1
      exact htwin ⟨u.1, hσE _ u.2⟩ u.2
    bit_eq := fun u => by
      refine (Record.switch_isOver (slotRecord hW' IsσSlot (allActive hW')) x₀ (Φ u)).trans ?_
      by_cases hs : S u.1
      · rw [ite_eq_left ((hmem u).2 hs)]
        show (!isDesc (φ ⟨u.1, hσE _ u.2⟩).1) = isDesc u.1
        rw [hdescS ⟨u.1, hσE _ u.2⟩ u.2 hs, Bool.not_not]
      · rw [ite_eq_right (fun h => hs ((hmem u).1 h))]
        exact hdescN ⟨u.1, hσE _ u.2⟩ u.2 hs
    sgn_eq := fun u => by
      refine (Record.switch_sgn (slotRecord hW' IsσSlot (allActive hW')) x₀ (Φ u)).trans ?_
      by_cases hs : S u.1
      · rw [ite_eq_left ((hmem u).2 hs)]
        show -σsgn (φ ⟨u.1, hσE _ u.2⟩).1 = σsgn u.1
        rw [hsgnS ⟨u.1, hσE _ u.2⟩ u.2 hs, neg_neg]
      · rw [ite_eq_right (fun h => hs ((hmem u).1 h))]
        exact hsgnN ⟨u.1, hσE _ u.2⟩ u.2 hs }

end RecIsoSwitch

/-! generic pass lemmas with the letter named -/

section PassLetter

variable {V : Word} (hV : V.Closed)
include hV

theorem pass_r_lt {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} {p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0)
    (hb : bit V k p = true) (hlt : p < ℓ.idx) : (next hV s).1 = (k + 1, p) ∧ bit V (k + 1) p = true :=
  next_right_lt hV hs hp hb (by rw [hℓ]; exact hlt)

theorem pass_r_ge {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} {p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0)
    (hb : bit V k p = true) (hge : ℓ.idx + ℓ.arity ≤ p) :
    (next hV s).1 = (k + 1, p + ℓ.coarity - ℓ.arity) ∧ bit V (k + 1) (p + ℓ.coarity - ℓ.arity) = true := by
  have := next_right_ge hV hs hp hb (by rw [hℓ]; exact hge)
  rwa [hℓ] at this

theorem pass_l_lt {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} {q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0)
    (hb : bit V (k + 1) q = false) (hlt : q < ℓ.idx) : (next hV s).1 = (k, q) ∧ bit V k q = false := by
  have := next_left_lt hV hs hq hb (by rw [Nat.add_sub_cancel, hℓ]; exact hlt)
  rwa [Nat.add_sub_cancel] at this

theorem pass_l_ge {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} {q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0)
    (hb : bit V (k + 1) q = false) (hge : ℓ.idx + ℓ.coarity ≤ q) :
    (next hV s).1 = (k, q + ℓ.arity - ℓ.coarity) ∧ bit V k (q + ℓ.arity - ℓ.coarity) = false := by
  have := next_left_ge hV hs hq hb (by rw [Nat.add_sub_cancel, hℓ]; exact hge)
  rwa [Nat.add_sub_cancel, hℓ] at this

omit hV in
/-- a pass slot heading right is not a `σ` slot unless the letter is `σ j` and the position is `j` or `j+1` -/
theorem not_σ_right {s : Slot V} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true)
    (h : ∀ j, letterAt V k = .σ j → p ≠ j ∧ p ≠ j + 1) : ¬ IsσSlot s := by
  intro hσ
  have hcol : colOf s = k := block_col_true hs hp hb
  unfold IsσSlot at hσ
  rw [hcol] at hσ
  obtain ⟨hcr, hsh⟩ := hσ
  obtain ⟨j, hℓ⟩ : ∃ j, letterAt V k = .σ j := ⟨_, letterAt_σ_of_isCrossing hcr⟩
  obtain ⟨h1, h2⟩ := h j hℓ
  have hshape : shapeOf s = .pass p p := by
    unfold shapeOf
    rw [hs]
    simp only [hp, ↓reduceIte, hb, hℓ]
    unfold posR
    simp only [idx, arity, coarity]
    split_ifs with c1 c2
    · rfl
    · omega
    · rw [Nat.add_sub_cancel]
  rw [hℓ, hshape] at hsh
  simp only [idx, Shape.pass.injEq] at hsh
  omega

omit hV in
/-- a pass slot heading left is not a `σ` slot unless the previous letter is `σ j` and the position is `j` or `j+1` -/
theorem not_σ_left {s : Slot V} {k q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0) (hb : bit V (k + 1) q = false)
    (h : ∀ j, letterAt V k = .σ j → q ≠ j ∧ q ≠ j + 1) : ¬ IsσSlot s := by
  intro hσ
  have hcol : colOf s = k := by rw [block_col_false hs hq hb, Nat.add_sub_cancel]
  unfold IsσSlot at hσ
  rw [hcol] at hσ
  obtain ⟨hcr, hsh⟩ := hσ
  obtain ⟨j, hℓ⟩ : ∃ j, letterAt V k = .σ j := ⟨_, letterAt_σ_of_isCrossing hcr⟩
  obtain ⟨h1, h2⟩ := h j hℓ
  have hshape : shapeOf s = .pass q q := by
    unfold shapeOf
    rw [hs]
    simp only [hq, ↓reduceIte, hb, Bool.false_eq_true, Nat.add_sub_cancel, hℓ]
    unfold posL
    simp only [idx, arity, coarity]
    split_ifs with c1 c2
    · rfl
    · omega
    · rw [Nat.add_sub_cancel]
  rw [hℓ, hshape] at hsh
  simp only [idx, Shape.pass.injEq] at hsh
  omega

omit hV in
/-- a cusp vertex is never a `σ` slot -/
theorem not_σ_vertex {s : Slot V} {k : ℕ} (hs : s.1 = (k, 0)) : ¬ IsσSlot s := by
  intro hσ
  have := vertex_not_crossing hs
  unfold IsσSlot at hσ
  rw [block_col_vertex hs] at hσ
  rw [hσ.1] at this
  exact Bool.noConfusion this

end PassLetter

/-! #### H. The cusp-skein interchange (ng:cusp-skein): `A = X l_{m+1} σ_m Y`, `A' = X l_m σ_{m+1} Y` -/

section Skein

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

theorem sk_letters : letterAt Vs X.length = .l (m + 1) d ∧ letterAt Vs (X.length + 1) = .σ m := by
  constructor
  · have := letterAt_block X Ps Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Ps Y (i := 1) (by simp)
    simpa using this

theorem sk'_letters : letterAt Vsp X.length = .l m d ∧ letterAt Vsp (X.length + 1) = .σ (m + 1) := by
  constructor
  · have := letterAt_block X Psp Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Psp Y (i := 1) (by simp)
    simpa using this

theorem sk_length : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem sk'_length : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem sk_extCol (k : ℕ) : ExtCol X Ps k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by unfold ExtCol; simp
theorem sk'_extCol (k : ℕ) : ExtCol X Psp k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by unfold ExtCol; simp

/-- the index shift between the two principal words is the identity on exterior indices -/
theorem sk_shift {k : ℕ} (hk : k ≤ X.length ∨ X.length + 2 ≤ k) : shiftIdx X Psp Ps k = k := by
  unfold shiftIdx
  by_cases h : k ≤ X.length
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have e1 : ([Letter.l m d, Letter.σ (m + 1)] : Word).length = 2 := rfl
    have e2 : ([Letter.l (m + 1) d, Letter.σ m] : Word).length = 2 := rfl
    rw [e1, e2]; omega

theorem sk_extPair {s : ℕ × ℕ} (hs : s.1 ≤ X.length ∨ X.length + 2 ≤ s.1) : extPair X Psp Ps s = s := by
  obtain ⟨k, p⟩ := s; simp only [extPair, sk_shift X m d hs]

theorem sk_Pne : ([Letter.l m d, Letter.σ (m + 1)] : Word) ≠ [] := List.cons_ne_nil _ _

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)

include hX hP in
/-- the through-strand bit at the cut before the factor -/
theorem sk_bit_a : bit Vs X.length m = a ∧ bit Vsp X.length m = a := by
  have h1 : cut Vs X.length = P ++ a :: L := cut_start X Ps Y hX
  have h2 : cut Vsp X.length = P ++ a :: L := cut_start X Psp Y hX
  have e : (P ++ a :: L).getD (m - 1) false = a := by
    rw [← hP, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]; rfl
  constructor
  · rw [bit_eq, h1, e]
  · rw [bit_eq, h2, e]

include hA in
theorem sk_bits (ha : bit Vs X.length m = a) :
    bit Vs (X.length + 1) m = a ∧ bit Vs (X.length + 1) (m + 1) = d ∧ bit Vs (X.length + 1) (m + 2) = !d ∧
    bit Vs (X.length + 2) m = d ∧ bit Vs (X.length + 2) (m + 1) = a ∧ bit Vs (X.length + 2) (m + 2) = !d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have hk₀ : X.length < (Vs).length := by rw [sk_length]; omega
  have hk₁ : X.length + 1 < (Vs).length := by rw [sk_length]; omega
  obtain ⟨-, h1, h2⟩ := l_bits hA hk₀ hℓ₀
  have hm1 : 1 ≤ m := σ_idx_pos hA hℓ₁
  have h0 : bit Vs (X.length + 1) m = a := by
    rw [bit_succ_of_lt hA hk₀ hm1 (by rw [hℓ₀]; exact Nat.lt_succ_self m), ha]
  obtain ⟨-, -, -, h3, h4⟩ := σ_facts hA hk₁ hℓ₁
  have h5 : bit Vs (X.length + 2) (m + 2) = bit Vs (X.length + 1) (m + 2) := by
    have := bit_succ_of_ge hA hk₁ (p := m + 2) (by rw [hℓ₁]; simp [idx, arity])
    rw [hℓ₁] at this; simpa [arity, coarity] using this
  exact ⟨h0, h1, h2, by rw [h4, h1], by rw [h3, h0], by rw [h5, h2]⟩

include hA' in
theorem sk'_bits (ha : bit Vsp X.length m = a) :
    bit Vsp (X.length + 1) m = d ∧ bit Vsp (X.length + 1) (m + 1) = !d ∧ bit Vsp (X.length + 1) (m + 2) = a ∧
    bit Vsp (X.length + 2) m = d ∧ bit Vsp (X.length + 2) (m + 1) = a ∧ bit Vsp (X.length + 2) (m + 2) = !d := by
  obtain ⟨hℓ₀, hℓ₁⟩ := sk'_letters X Y m d
  have hk₀ : X.length < (Vsp).length := by rw [sk'_length]; omega
  have hk₁ : X.length + 1 < (Vsp).length := by rw [sk'_length]; omega
  obtain ⟨hm1, h1, h2⟩ := l_bits hA' hk₀ hℓ₀
  have h0 : bit Vsp (X.length + 1) (m + 2) = a := by
    have := bit_succ_of_ge hA' hk₀ (p := m) (by rw [hℓ₀]; simp [idx, arity])
    rw [hℓ₀] at this; simp only [arity, coarity, Nat.sub_zero] at this
    rw [← ha, ← this]
  obtain ⟨-, -, -, h3, h4⟩ := σ_facts hA' hk₁ hℓ₁
  have h5 : bit Vsp (X.length + 2) m = bit Vsp (X.length + 1) m :=
    bit_succ_of_lt hA' hk₁ hm1 (by rw [hℓ₁]; exact Nat.lt_succ_self m)
  exact ⟨h1, h2, h0, by rw [h5, h1], by rw [h4, h0], by rw [h3, h2]⟩

theorem sk_m_pos (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed) : 1 ≤ m :=
  σ_idx_pos hA (sk_letters X Y m d).2

end Skein

section SkeinSwitch

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)

theorem sk_k₁ : X.length + 1 < (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).length := by rw [sk_length]; omega
theorem sk'_k₁ : X.length + 1 < (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).length := by rw [sk'_length]; omega

/-- the two site slots of `A` -/
noncomputable def siteA : Slot Vs := σSlotA hA (sk_k₁ X Y m d) (sk_letters X Y m d).2
noncomputable def siteB : Slot Vs := σSlotB hA (sk_k₁ X Y m d) (sk_letters X Y m d).2
/-- the two site slots of `A'` -/
noncomputable def siteA' : Slot Vsp := σSlotA hA' (sk'_k₁ X Y m d) (sk'_letters X Y m d).2
noncomputable def siteB' : Slot Vsp := σSlotB hA' (sk'_k₁ X Y m d) (sk'_letters X Y m d).2

include hA in
theorem siteA_val (ha : bit Vs X.length m = a) :
    (siteA X Y m d hA).1 = if a then (X.length + 1, m) else (X.length + 2, m + 1) := by
  have h := (sk_bits X Y m d a hA ha).1
  unfold siteA σSlotA
  rw [h]; cases a <;> rfl

include hA in
theorem siteB_val :
    (siteB X Y m d hA).1 = if d then (X.length + 1, m + 1) else (X.length + 2, m) := by
  have h := (l_bits hA (by rw [sk_length]; omega) (sk_letters X Y m d).1).2.1
  unfold siteB σSlotB
  rw [h]; cases d <;> rfl

include hA' in
theorem siteA'_val :
    (siteA' X Y m d hA').1 = if d then (X.length + 2, m + 2) else (X.length + 1, m + 1) := by
  have h := (l_bits hA' (by rw [sk'_length]; omega) (sk'_letters X Y m d).1).2.2
  unfold siteA' σSlotA
  rw [h]; cases d <;> rfl

include hA' in
theorem siteB'_val (ha : bit Vsp X.length m = a) :
    (siteB' X Y m d hA').1 = if a then (X.length + 1, m + 2) else (X.length + 2, m + 1) := by
  have h := (sk'_bits X Y m d a hA' ha).2.2.1
  unfold siteB' σSlotB
  rw [h]; cases a <;> rfl

omit hA hA' in
theorem σSlotA_congr {W : Word} (hW : W.Closed) {k k' j j' : ℕ} (hk : k < W.length) (hk' : k' < W.length)
    (hℓ : letterAt W k = .σ j) (hℓ' : letterAt W k' = .σ j') (e : k = k') : σSlotA hW hk hℓ = σSlotA hW hk' hℓ' := by
  subst e
  have : j = j' := by rw [hℓ] at hℓ'; exact Letter.σ.inj hℓ'
  subst this
  rfl

omit hA hA' in
theorem σSlotB_congr {W : Word} (hW : W.Closed) {k k' j j' : ℕ} (hk : k < W.length) (hk' : k' < W.length)
    (hℓ : letterAt W k = .σ j) (hℓ' : letterAt W k' = .σ j') (e : k = k') : σSlotB hW hk hℓ = σSlotB hW hk' hℓ' := by
  subst e
  have : j = j' := by rw [hℓ] at hℓ'; exact Letter.σ.inj hℓ'
  subst this
  rfl

include hA in
/-- the interior `σ` slots of `A` are the two site slots -/
theorem sk_int_iff (u : Slot Vs) : IntSlot X Ps Y u ↔ u = siteA X Y m d hA ∨ u = siteB X Y m d hA := by
  constructor
  · rintro ⟨hu, hext⟩
    rw [sk_extCol] at hext
    have hlt := colOf_lt hA u
    rw [sk_length] at hlt
    have hcol : colOf u = X.length + 1 := by
      rcases Nat.lt_or_ge (colOf u) (X.length + 1) with h | h
      · exfalso
        have e : colOf u = X.length := by omega
        have := hu.1
        rw [e, (sk_letters X Y m d).1] at this
        exact Bool.noConfusion this
      · omega
    rcases eq_σSlotA_or_σSlotB hA hu with h | h
    · left; rw [h]; exact σSlotA_congr hA _ _ _ _ hcol
    · right; rw [h]; exact σSlotB_congr hA _ _ _ _ hcol
  · rintro (rfl | rfl)
    · refine ⟨isσSlot_σSlotA hA _ _, ?_⟩
      unfold siteA; rw [(σSlotA_spec hA _ _).1, sk_extCol]; omega
    · refine ⟨isσSlot_σSlotB hA _ _, ?_⟩
      unfold siteB; rw [(σSlotB_spec hA _ _).1, sk_extCol]; omega

include hA' in
theorem sk'_int_iff (u : Slot Vsp) : IntSlot X Psp Y u ↔ u = siteA' X Y m d hA' ∨ u = siteB' X Y m d hA' := by
  constructor
  · rintro ⟨hu, hext⟩
    rw [sk'_extCol] at hext
    have hlt := colOf_lt hA' u
    rw [sk'_length] at hlt
    have hcol : colOf u = X.length + 1 := by
      rcases Nat.lt_or_ge (colOf u) (X.length + 1) with h | h
      · exfalso
        have e : colOf u = X.length := by omega
        have := hu.1
        rw [e, (sk'_letters X Y m d).1] at this
        exact Bool.noConfusion this
      · omega
    rcases eq_σSlotA_or_σSlotB hA' hu with h | h
    · left; rw [h]; exact σSlotA_congr hA' _ _ _ _ hcol
    · right; rw [h]; exact σSlotB_congr hA' _ _ _ _ hcol
  · rintro (rfl | rfl)
    · refine ⟨isσSlot_σSlotA hA' _ _, ?_⟩
      unfold siteA'; rw [(σSlotA_spec hA' _ _).1, sk'_extCol]; omega
    · refine ⟨isσSlot_σSlotB hA' _ _, ?_⟩
      unfold siteB'; rw [(σSlotB_spec hA' _ _).1, sk'_extCol]; omega

include hA in
theorem siteA_int : IntSlot X Ps Y (siteA X Y m d hA) := (sk_int_iff X Y m d hA _).2 (Or.inl rfl)
include hA in
theorem siteB_int : IntSlot X Ps Y (siteB X Y m d hA) := (sk_int_iff X Y m d hA _).2 (Or.inr rfl)
include hA' in
theorem siteA'_int : IntSlot X Psp Y (siteA' X Y m d hA') := (sk'_int_iff X Y m d hA' _).2 (Or.inl rfl)
include hA' in
theorem siteB'_int : IntSlot X Psp Y (siteB' X Y m d hA') := (sk'_int_iff X Y m d hA' _).2 (Or.inr rfl)

include hA in
theorem isDesc_siteA : isDesc (siteA X Y m d hA) = true := isDesc_σSlotA hA _ _
include hA in
theorem isDesc_siteB : isDesc (siteB X Y m d hA) = false := isDesc_σSlotB hA _ _
include hA' in
theorem isDesc_siteA' : isDesc (siteA' X Y m d hA') = true := isDesc_σSlotA hA' _ _
include hA' in
theorem isDesc_siteB' : isDesc (siteB' X Y m d hA') = false := isDesc_σSlotB hA' _ _

include hA in
theorem σtwin_siteA : σtwin hA (siteA X Y m d hA) = siteB X Y m d hA := σtwin_σSlotA hA _ _
include hA in
theorem σtwin_siteB : σtwin hA (siteB X Y m d hA) = siteA X Y m d hA := σtwin_σSlotB hA _ _
include hA' in
theorem σtwin_siteA' : σtwin hA' (siteA' X Y m d hA') = siteB' X Y m d hA' := σtwin_σSlotA hA' _ _
include hA' in
theorem σtwin_siteB' : σtwin hA' (siteB' X Y m d hA') = siteA' X Y m d hA' := σtwin_σSlotB hA' _ _

include hA hA' in
/-- THE INTERIOR SLOT CORRESPONDENCE of the cusp-skein switch: the through-strand slots and the arm slots
correspond (the over bit is reversed). -/
noncomputable def skφI : {u // IntSlot X Psp Y u} ≃ {u' // IntSlot X Ps Y u'} where
  toFun u := if isDesc u.1 then ⟨siteB X Y m d hA, siteB_int X Y m d hA⟩ else ⟨siteA X Y m d hA, siteA_int X Y m d hA⟩
  invFun u := if isDesc u.1 then ⟨siteB' X Y m d hA', siteB'_int X Y m d hA'⟩
    else ⟨siteA' X Y m d hA', siteA'_int X Y m d hA'⟩
  left_inv u := by
    rcases (sk'_int_iff X Y m d hA' u.1).1 u.2 with h | h
    · simp only [h, isDesc_siteA', ↓reduceIte, isDesc_siteB, Bool.false_eq_true]
      exact Subtype.ext h.symm
    · simp only [h, isDesc_siteB', Bool.false_eq_true, ↓reduceIte, isDesc_siteA]
      exact Subtype.ext h.symm
  right_inv u := by
    rcases (sk_int_iff X Y m d hA u.1).1 u.2 with h | h
    · simp only [h, isDesc_siteA, ↓reduceIte, isDesc_siteB', Bool.false_eq_true]
      exact Subtype.ext h.symm
    · simp only [h, isDesc_siteB, Bool.false_eq_true, ↓reduceIte, isDesc_siteA']
      exact Subtype.ext h.symm

include hA hA' in
theorem skφI_siteA' : (skφI X Y m d hA hA' ⟨_, siteA'_int X Y m d hA'⟩).1 = siteB X Y m d hA := by
  simp only [skφI, Equiv.coe_fn_mk, isDesc_siteA', ↓reduceIte]

include hA hA' in
theorem skφI_siteB' : (skφI X Y m d hA hA' ⟨_, siteB'_int X Y m d hA'⟩).1 = siteA X Y m d hA := by
  simp only [skφI, Equiv.coe_fn_mk, isDesc_siteB', Bool.false_eq_true, ↓reduceIte]

include hA hA' in
theorem skφI_val (u : {u // IntSlot X Psp Y u}) :
    (skφI X Y m d hA hA' u).1 = if isDesc u.1 then siteB X Y m d hA else siteA X Y m d hA := by
  simp only [skφI, Equiv.coe_fn_mk]
  split_ifs <;> rfl

include hA hA' in
theorem skφI_desc (u : {u // IntSlot X Psp Y u}) : isDesc (skφI X Y m d hA hA' u).1 = !isDesc u.1 := by
  rw [skφI_val]
  rcases (sk'_int_iff X Y m d hA' u.1).1 u.2 with h | h
  · rw [h, isDesc_siteA']; simp [isDesc_siteB]
  · rw [h, isDesc_siteB']; simp [isDesc_siteA]

include hA hA' in
theorem skφI_twin (u : {u // IntSlot X Psp Y u}) :
    (skφI X Y m d hA hA' ⟨σtwin hA' u.1, ⟨isσSlot_σtwin hA' u.2.1, by rw [colOf_σtwin hA' u.2.1]; exact u.2.2⟩⟩).1 =
      σtwin hA (skφI X Y m d hA hA' u).1 := by
  rw [skφI_val, skφI_val]
  rcases (sk'_int_iff X Y m d hA' u.1).1 u.2 with h | h
  · simp only [h, σtwin_siteA', isDesc_siteB', Bool.false_eq_true, ↓reduceIte, isDesc_siteA', σtwin_siteB]
  · simp only [h, σtwin_siteB', isDesc_siteA', ↓reduceIte, isDesc_siteB', Bool.false_eq_true, σtwin_siteA]

include hA hA' in
theorem skφI_sgn (ha : bit Vs X.length m = a) (ha' : bit Vsp X.length m = a) (u : {u // IntSlot X Psp Y u}) :
    σsgn (skφI X Y m d hA hA' u).1 = -σsgn u.1 := by
  obtain ⟨b1, b2, -, -, -, -⟩ := sk_bits X Y m d a hA ha
  obtain ⟨-, b2', b3', -, -, -⟩ := sk'_bits X Y m d a hA' ha'
  have hcol : colOf (skφI X Y m d hA hA' u).1 = X.length + 1 := by
    rw [skφI_val]; split_ifs
    · exact (σSlotB_spec hA _ _).1
    · exact (σSlotA_spec hA _ _).1
  have hcol' : colOf u.1 = X.length + 1 := by
    rcases (sk'_int_iff X Y m d hA' u.1).1 u.2 with h | h
    · rw [h]; exact (σSlotA_spec hA' _ _).1
    · rw [h]; exact (σSlotB_spec hA' _ _).1
  have b3'' : bit Vsp (X.length + 1) (m + 1 + 1) = a := b3'
  unfold σsgn σsgnCol
  rw [hcol, hcol', (sk_letters X Y m d).2, (sk'_letters X Y m d).2]
  simp only [idx, b1, b2, b2', b3'']
  cases a <;> cases d <;> decide

end SkeinSwitch

section SkeinPassage

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)
include hX hP hm

theorem sk_sameEffect : SameEffect X Psp Ps := by
  unfold SameEffect
  rw [Word.run_append, Word.run_append, hX, Option.bind_some, Option.bind_some, run_skein_A' hm hP, run_skein_A hm hP]

omit hX hP hm in
theorem sk_extPair_of_ext (c : Slot Vsp) (hc : IsExtSlot X Psp c.1) : extPair X Psp Ps c.1 = c.1 := by
  apply sk_extPair
  obtain ⟨⟨k, p⟩, hs⟩ := c
  unfold IsExtSlot at hc
  simp only at hc ⊢
  split_ifs at hc with hp
  · unfold ExtCol at hc; simp at hc; omega
  · unfold ExtCut at hc; simp at hc; omega

/-- the exterior bits of the two principal words agree (cuts `|X|` and `|X|+2`) -/
theorem sk_bits_ext (p : ℕ) : bit Vs X.length p = bit Vsp X.length p ∧ bit Vs (X.length + 2) p = bit Vsp (X.length + 2) p := by
  have hE := sk_sameEffect X m d a hX hP hm
  have h0 := bit_ext X Psp Y Ps (by simp) hE (k := X.length) (Or.inl le_rfl) p
  have h2 := bit_ext X Psp Y Ps (by simp) hE (k := X.length + 2) (Or.inr (by simp)) p
  rw [sk_shift X m d (Or.inl le_rfl)] at h0
  rw [sk_shift X m d (Or.inr le_rfl)] at h2
  exact ⟨h0.symm, h2.symm⟩

include hA hA'

omit hA in
/-- every slot of `A'` reaches the exterior -/
theorem sk'_hexit : ∀ u : Slot Vsp, ∃ n, ExtPiece X Psp Y ((next hA')^[n] u) := by
  obtain ⟨hℓ₀, hℓ₁⟩ := sk'_letters X Y m d
  have ha' := (sk_bit_a X Y m d a hX hP).2
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk'_bits X Y m d a hA' ha'
  have hm1 : 1 ≤ m := hm
  -- the vertex chain
  have hv : ∀ u : Slot Vsp, u.1 = (X.length, 0) → ∃ n, ExtPiece X Psp Y ((next hA')^[n] u) := by
    intro u hu
    have h1 := next_cusp_l hA' hℓ₀ hu
    rcases Bool.eq_false_or_eq_true d with hd | hd
    · rw [ite_eq_left hd] at h1
      have hb1 : bit Vsp (X.length + 1) m = true := by rw [c1, hd]
      obtain ⟨h2, hb2⟩ := pass_r_lt hA' hℓ₁ h1 (by omega) hb1 (by simp [idx])
      refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
      show ExtCol X Psp (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk'_extCol]; omega
    · rw [ite_eq_right (by simp [hd])] at h1
      have hb1 : bit Vsp (X.length + 1) (m + 1) = true := by rw [c2, hd]; rfl
      have h2 := next_σ_right_idx hA' hℓ₁ h1 hb1
      have hb2 : bit Vsp (X.length + 2) (m + 1 + 1) = true := by rw [e3, hd]; rfl
      refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
      show ExtCol X Psp (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk'_extCol]; omega
  intro u
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Psp (colOf u)
  · exact reach_self hA' hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, sk'_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact hv u hu
    · exfalso; have := vertex_not_crossing hu; rw [hℓ₁] at this; exact Bool.noConfusion this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hA' hu hp
  cases hb : bit Vsp k p
  · rw [block_col_false hu hp hb, sk'_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_l_lt hA' hℓ₀ hu hp hb (by simpa [idx] using hpm)
        refine reach_of_next hA' (reach_self hA' ?_)
        show ExtCol X Psp (colOf _)
        have := (cutSlot_facts hA' h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, sk'_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · have h1 := next_arm_l hA' (by omega) hℓ₀ hu (by omega) hb
        exact reach_of_next hA' (hv _ h1)
      · obtain ⟨h1, hb1⟩ := pass_l_ge hA' hℓ₀ hu hp hb (by simpa [idx, coarity] using hpm2)
        simp only [arity, coarity] at h1 hb1
        refine reach_of_next hA' (reach_self hA' ?_)
        show ExtCol X Psp (colOf _)
        have := (cutSlot_facts hA' h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, sk'_extCol]; omega
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_l_lt hA' hℓ₁ hu hp hb (by simpa [idx] using hpm)
        rcases lt_or_ge p m with hpm' | hpm'
        · obtain ⟨h2, hb2⟩ := pass_l_lt hA' hℓ₀ h1 hp hb1 (by simpa [idx] using hpm')
          refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
          show ExtCol X Psp (colOf _)
          have := (cutSlot_facts hA' h2 hp).2.2.1
          rw [block_col_false h2 hp hb2, sk'_extCol]; omega
        · have h2 := next_arm_l hA' (by omega) hℓ₀ h1 (by omega) hb1
          exact reach_of_next hA' (reach_of_next hA' (hv _ h2))
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- `p = m + 1`: the through-strand, heading left
          rw [← hpe] at hu hb
          have h1 := next_σ_left_idx hA' hℓ₁ hu hb
          have hb1 : bit Vsp (X.length + 1) (m + 1 + 1) = false := by rw [c3, ← e2, hb]
          obtain ⟨h2, hb2⟩ := pass_l_ge hA' hℓ₀ h1 (by omega) hb1 (by simp [idx, coarity])
          simp only [arity, coarity] at h2 hb2
          refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
          show ExtCol X Psp (colOf _)
          have := (cutSlot_facts hA' h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2, sk'_extCol]; omega
        · have hpe' : p = m + 1 + 1 := by omega
          rw [hpe'] at hu hb
          have h1 := next_σ_left_succ hA' hℓ₁ hu hb
          have hb1 : bit Vsp (X.length + 1) (m + 1) = false := by rw [c2, ← e3, hb]
          have h2 := next_arm_l hA' (by omega) hℓ₀ h1 (Or.inr rfl) hb1
          exact reach_of_next hA' (reach_of_next hA' (hv _ h2))
      · obtain ⟨h1, hb1⟩ := pass_l_ge hA' hℓ₁ hu hp hb (by simpa [idx, coarity] using hpm3)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        obtain ⟨h2, hb2⟩ := pass_l_ge hA' hℓ₀ h1 hp hb1 (by simp [idx, coarity]; omega)
        simp only [arity, coarity] at h2 hb2
        refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
        show ExtCol X Psp (colOf _)
        have := (cutSlot_facts hA' h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, sk'_extCol]; omega
  · rw [block_col_true hu hp hb, sk'_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_r_lt hA' hℓ₀ hu hp hb (by simpa [idx] using hpm)
        obtain ⟨h2, hb2⟩ := pass_r_lt hA' hℓ₁ h1 hp hb1 (by simp [idx]; omega)
        refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
        show ExtCol X Psp (colOf _)
        rw [block_col_true h2 hp hb2, sk'_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_r_ge hA' hℓ₀ hu hp hb (by simpa [idx, arity] using hpm)
        simp only [arity, coarity, Nat.sub_zero] at h1 hb1
        rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- `p = m`: the through-strand enters the crossing
          rw [← hpe] at h1 hb1
          have h2 := next_σ_right_succ hA' hℓ₁ h1 hb1
          have hb2 : bit Vsp (X.length + 2) (m + 1) = true := by rw [e2, ← c3, hb1]
          refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
          show ExtCol X Psp (colOf _)
          rw [block_col_true h2 (by omega) hb2, sk'_extCol]; omega
        · obtain ⟨h2, hb2⟩ := pass_r_ge hA' hℓ₁ h1 (by omega) hb1 (by simp [idx, arity]; omega)
          simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
          refine reach_of_next hA' (reach_of_next hA' (reach_self hA' ?_))
          show ExtCol X Psp (colOf _)
          rw [block_col_true h2 (by omega) hb2, sk'_extCol]; omega
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_r_lt hA' hℓ₁ hu hp hb (by simpa [idx] using hpm)
        refine reach_of_next hA' (reach_self hA' ?_)
        show ExtCol X Psp (colOf _)
        rw [block_col_true h1 hp hb1, sk'_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · rw [← hpe] at hu hb
          have h1 := next_σ_right_idx hA' hℓ₁ hu hb
          have hb1 : bit Vsp (X.length + 2) (m + 1 + 1) = true := by rw [e3, ← c2, hb]
          refine reach_of_next hA' (reach_self hA' ?_)
          show ExtCol X Psp (colOf _)
          rw [block_col_true h1 (by omega) hb1, sk'_extCol]; omega
        · have hpe' : p = m + 1 + 1 := by omega
          rw [hpe'] at hu hb
          have h1 := next_σ_right_succ hA' hℓ₁ hu hb
          have hb1 : bit Vsp (X.length + 2) (m + 1) = true := by rw [e2, ← c3, hb]
          refine reach_of_next hA' (reach_self hA' ?_)
          show ExtCol X Psp (colOf _)
          rw [block_col_true h1 (by omega) hb1, sk'_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_r_ge hA' hℓ₁ hu hp hb (by simpa [idx, arity] using hpm3)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        refine reach_of_next hA' (reach_self hA' ?_)
        show ExtCol X Psp (colOf _)
        rw [block_col_true h1 hp hb1, sk'_extCol]; omega

omit hA' in
/-- every slot of `A` reaches the exterior -/
theorem sk_hexit : ∀ u : Slot Vs, ∃ n, ExtPiece X Ps Y ((next hA)^[n] u) := by
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk_bits X Y m d a hA ha
  have hm1 : 1 ≤ m := hm
  have hv : ∀ u : Slot Vs, u.1 = (X.length, 0) → ∃ n, ExtPiece X Ps Y ((next hA)^[n] u) := by
    intro u hu
    have h1 := next_cusp_l hA hℓ₀ hu
    rcases Bool.eq_false_or_eq_true d with hd | hd
    · rw [ite_eq_left hd] at h1
      have hb1 : bit Vs (X.length + 1) (m + 1) = true := by rw [c2, hd]
      have h2 := next_σ_right_succ hA hℓ₁ h1 hb1
      have hb2 : bit Vs (X.length + 2) m = true := by rw [e1, hd]
      refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
      show ExtCol X Ps (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
    · rw [ite_eq_right (by simp [hd])] at h1
      have hb1 : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hd]; rfl
      obtain ⟨h2, hb2⟩ := pass_r_ge hA hℓ₁ h1 (by omega) hb1 (by simp [idx, arity])
      simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
      refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
      show ExtCol X Ps (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
  intro u
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Ps (colOf u)
  · exact reach_self hA hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, sk_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact hv u hu
    · exfalso; have := vertex_not_crossing hu; rw [hℓ₁] at this; exact Bool.noConfusion this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hA hu hp
  cases hb : bit Vs k p
  · rw [block_col_false hu hp hb, sk_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_l_lt hA hℓ₀ hu hp hb (by simpa [idx] using hpm)
        refine reach_of_next hA (reach_self hA ?_)
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, sk_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have h1 := next_arm_l hA (by omega) hℓ₀ hu (by omega) hb
        exact reach_of_next hA (hv _ h1)
      · obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₀ hu hp hb (by simpa [idx, coarity] using hpm3)
        simp only [arity, coarity] at h1 hb1
        refine reach_of_next hA (reach_self hA ?_)
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, sk_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_l_lt hA hℓ₁ hu hp hb (by simpa [idx] using hpm)
        obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ h1 hp hb1 (by simp [idx]; omega)
        refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, sk_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- `p = m`: the upper arm heading left
          rw [← hpe] at hu hb
          have h1 := next_σ_left_idx hA hℓ₁ hu hb
          have hb1 : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, ← e1, hb]
          have h2 := next_arm_l hA (by omega) hℓ₀ h1 (Or.inl rfl) hb1
          exact reach_of_next hA (reach_of_next hA (hv _ h2))
        · have hpe' : p = m + 1 := by omega
          rw [hpe'] at hu hb
          have h1 := next_σ_left_succ hA hℓ₁ hu hb
          have hb1 : bit Vs (X.length + 1) m = false := by rw [c1, ← e2, hb]
          obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ h1 (by omega) hb1 (by simp [idx])
          refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
          show ExtCol X Ps (colOf _)
          have := (cutSlot_facts hA h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₁ hu hp hb (by simpa [idx, coarity] using hpm2)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        rcases lt_or_ge p (m + 3) with hpm3 | hpm3
        · have h2 := next_arm_l hA (by omega) hℓ₀ h1 (by omega) hb1
          exact reach_of_next hA (reach_of_next hA (hv _ h2))
        · obtain ⟨h2, hb2⟩ := pass_l_ge hA hℓ₀ h1 hp hb1 (by simpa [idx, coarity] using hpm3)
          simp only [arity, coarity] at h2 hb2
          refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
          show ExtCol X Ps (colOf _)
          have := (cutSlot_facts hA h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
  · rw [block_col_true hu hp hb, sk_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₀ hu hp hb (by simpa [idx] using hpm)
        rcases lt_or_ge p m with hpm' | hpm'
        · obtain ⟨h2, hb2⟩ := pass_r_lt hA hℓ₁ h1 hp hb1 (by simpa [idx] using hpm')
          refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
          show ExtCol X Ps (colOf _)
          rw [block_col_true h2 hp hb2, sk_extCol]; omega
        · have hpe : p = m := by omega
          rw [hpe] at h1 hb1
          have h2 := next_σ_right_idx hA hℓ₁ h1 hb1
          have hb2 : bit Vs (X.length + 2) (m + 1) = true := by rw [e2, ← c1, hb1]
          refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
          show ExtCol X Ps (colOf _)
          rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_r_ge hA hℓ₀ hu hp hb (by simpa [idx, arity] using hpm)
        simp only [arity, coarity, Nat.sub_zero] at h1 hb1
        obtain ⟨h2, hb2⟩ := pass_r_ge hA hℓ₁ h1 (by omega) hb1 (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
        refine reach_of_next hA (reach_of_next hA (reach_self hA ?_))
        show ExtCol X Ps (colOf _)
        rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
    · rcases lt_or_ge p m with hpm | hpm
      · obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₁ hu hp hb (by simpa [idx] using hpm)
        refine reach_of_next hA (reach_self hA ?_)
        show ExtCol X Ps (colOf _)
        rw [block_col_true h1 hp hb1, sk_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · rw [← hpe] at hu hb
          have h1 := next_σ_right_idx hA hℓ₁ hu hb
          have hb1 : bit Vs (X.length + 2) (m + 1) = true := by rw [e2, ← c1, hb]
          refine reach_of_next hA (reach_self hA ?_)
          show ExtCol X Ps (colOf _)
          rw [block_col_true h1 (by omega) hb1, sk_extCol]; omega
        · have hpe' : p = m + 1 := by omega
          rw [hpe'] at hu hb
          have h1 := next_σ_right_succ hA hℓ₁ hu hb
          have hb1 : bit Vs (X.length + 2) m = true := by rw [e1, ← c2, hb]
          refine reach_of_next hA (reach_self hA ?_)
          show ExtCol X Ps (colOf _)
          rw [block_col_true h1 (by omega) hb1, sk_extCol]; omega
      · obtain ⟨h1, hb1⟩ := pass_r_ge hA hℓ₁ hu hp hb (by simpa [idx, arity] using hpm2)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        refine reach_of_next hA (reach_self hA ?_)
        show ExtCol X Ps (colOf _)
        rw [block_col_true h1 hp hb1, sk_extCol]; omega

end SkeinPassage

section SkeinIntPassage

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)

/-! non-active block slots and exterior slots by coordinates -/

omit hA in
theorem sk'_notAct_r {s : Slot Vsp} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit Vsp k p = true)
    (hk : k = X.length ∨ k = X.length + 1) (hσ : k = X.length + 1 → p ≠ m + 1 ∧ p ≠ m + 2) : ¬ ActE X Psp Y s := by
  refine not_actE_of X Psp Y (by rw [block_col_true hs hp hb, sk'_extCol]; omega) ?_
  refine not_σ_right hs hp hb (fun j hj => ?_)
  rcases hk with rfl | rfl
  · rw [(sk'_letters X Y m d).1] at hj; cases hj
  · rw [(sk'_letters X Y m d).2] at hj; injection hj with hj; subst hj; exact hσ rfl

omit hA in
theorem sk'_notAct_l {s : Slot Vsp} {k q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0) (hb : bit Vsp (k + 1) q = false)
    (hk : k = X.length ∨ k = X.length + 1) (hσ : k = X.length + 1 → q ≠ m + 1 ∧ q ≠ m + 2) : ¬ ActE X Psp Y s := by
  refine not_actE_of X Psp Y (by rw [block_col_false hs hq hb, Nat.add_sub_cancel, sk'_extCol]; omega) ?_
  refine not_σ_left hs hq hb (fun j hj => ?_)
  rcases hk with rfl | rfl
  · rw [(sk'_letters X Y m d).1] at hj; cases hj
  · rw [(sk'_letters X Y m d).2] at hj; injection hj with hj; subst hj; exact hσ rfl

omit hA in
theorem sk'_notAct_v {s : Slot Vsp} {k : ℕ} (hs : s.1 = (k, 0)) (hk : k = X.length ∨ k = X.length + 1) :
    ¬ ActE X Psp Y s :=
  not_actE_of X Psp Y (by rw [block_col_vertex hs, sk'_extCol]; omega) (not_σ_vertex hs)

omit hA' in
theorem sk_notAct_r {s : Slot Vs} {k p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit Vs k p = true)
    (hk : k = X.length ∨ k = X.length + 1) (hσ : k = X.length + 1 → p ≠ m ∧ p ≠ m + 1) : ¬ ActE X Ps Y s := by
  refine not_actE_of X Ps Y (by rw [block_col_true hs hp hb, sk_extCol]; omega) ?_
  refine not_σ_right hs hp hb (fun j hj => ?_)
  rcases hk with rfl | rfl
  · rw [(sk_letters X Y m d).1] at hj; cases hj
  · rw [(sk_letters X Y m d).2] at hj; injection hj with hj; subst hj; exact hσ rfl

omit hA' in
theorem sk_notAct_l {s : Slot Vs} {k q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0) (hb : bit Vs (k + 1) q = false)
    (hk : k = X.length ∨ k = X.length + 1) (hσ : k = X.length + 1 → q ≠ m ∧ q ≠ m + 1) : ¬ ActE X Ps Y s := by
  refine not_actE_of X Ps Y (by rw [block_col_false hs hq hb, Nat.add_sub_cancel, sk_extCol]; omega) ?_
  refine not_σ_left hs hq hb (fun j hj => ?_)
  rcases hk with rfl | rfl
  · rw [(sk_letters X Y m d).1] at hj; cases hj
  · rw [(sk_letters X Y m d).2] at hj; injection hj with hj; subst hj; exact hσ rfl

omit hA' in
theorem sk_notAct_v {s : Slot Vs} {k : ℕ} (hs : s.1 = (k, 0)) (hk : k = X.length ∨ k = X.length + 1) :
    ¬ ActE X Ps Y s :=
  not_actE_of X Ps Y (by rw [block_col_vertex hs, sk_extCol]; omega) (not_σ_vertex hs)

omit hA in
theorem sk'_ext_r {s : Slot Vsp} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0) (hb : bit Vsp (X.length + 2) p = true) :
    ExtCol X Psp (colOf s) := by rw [block_col_true hs hp hb, sk'_extCol]; omega

include hA' in
theorem sk'_ext_l {s : Slot Vsp} {q : ℕ} (hs : s.1 = (X.length, q)) (hq : q ≠ 0) (hb : bit Vsp X.length q = false) :
    ExtCol X Psp (colOf s) := by
  have := (cutSlot_facts hA' hs hq).2.2.1
  rw [block_col_false hs hq hb, sk'_extCol]; omega

omit hA' in
theorem sk_ext_r {s : Slot Vs} {p : ℕ} (hs : s.1 = (X.length + 2, p)) (hp : p ≠ 0) (hb : bit Vs (X.length + 2) p = true) :
    ExtCol X Ps (colOf s) := by rw [block_col_true hs hp hb, sk_extCol]; omega

include hA in
theorem sk_ext_l {s : Slot Vs} {q : ℕ} (hs : s.1 = (X.length, q)) (hq : q ≠ 0) (hb : bit Vs X.length q = false) :
    ExtCol X Ps (colOf s) := by
  have := (cutSlot_facts hA hs hq).2.2.1
  rw [block_col_false hs hq hb, sk_extCol]; omega

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
include hX hP hm hA hA'

/-- THE EXTENDED BLOCK PASSAGE of the cusp-skein interchange, from `A'` to `A`. -/
theorem sk_intPassage :
    IntPassage X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' hA (skφI X Y m d hA hA') := by
  have hE := sk_sameEffect X m d a hX hP hm
  have hPne : Psp ≠ [] := sk_Pne m d
  obtain ⟨hℓ₀', hℓ₁'⟩ := sk'_letters X Y m d
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have ha' := (sk_bit_a X Y m d a hX hP).2
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1', c2', c3', e1', e2', e3'⟩ := sk'_bits X Y m d a hA' ha'
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk_bits X Y m d a hA ha
  have hbx := sk_bits_ext X Y m d a hX hP hm
  -- the value of the glued correspondence
  have φext : ∀ (c : Slot Vsp) (hc : ExtCol X Psp (colOf c)),
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨c, Or.inl hc⟩).1.1 = c.1 :=
    fun c hc => (φA_val_ext' X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' _ ⟨c, Or.inl hc⟩ hc).trans
      (sk_extPair_of_ext X Y m d c (isExtSlot_of_extCol X Psp Y Ps hPne hE c hc))
  have φintA : ∀ (hc : ActE X Psp Y (siteA' X Y m d hA')),
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨_, hc⟩).1 =
        siteB X Y m d hA :=
    fun hc => (φA_val_int X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' _ ⟨_, hc⟩
      (siteA'_int X Y m d hA').2).trans (skφI_siteA' X Y m d hA hA')
  have φintB : ∀ (hc : ActE X Psp Y (siteB' X Y m d hA')),
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨_, hc⟩).1 =
        siteA X Y m d hA :=
    fun hc => (φA_val_int X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' _ ⟨_, hc⟩
      (siteB'_int X Y m d hA').2).trans (skφI_siteB' X Y m d hA hA')
  have φcongr : ∀ (c c' : Slot Vsp) (hc : ActE X Psp Y c) (hc' : ActE X Psp Y c'), c = c' →
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨c, hc⟩).1 =
      (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA') ⟨c', hc'⟩).1 := by
    rintro c c' hc hc' rfl; rfl
  have hsA' := siteA'_val X Y m d hA'
  have hsB' := siteB'_val X Y m d a hA' ha'
  have hsA := siteA_val X Y m d a hA ha
  have hsB := siteB_val X Y m d hA
  constructor
  · -- the entries
    intro b hext hcol
    let b' : Slot Vs := ⟨extPair X Psp Ps b.1, isSlot_ext X Psp Y Ps hPne hE b.2 hext⟩
    have hb'v : b'.1 = b.1 := sk_extPair_of_ext X Y m d b hext
    rcases (entry_iff X Psp Y hPne hA' b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
    · -- from the left at `(|X|, p)`
      have hb' : b'.1 = (X.length, p) := hb'v.trans hb
      have hbit' : bit Vs X.length p = true := by rw [(hbx p).1]; exact hbit
      have nb0 : ¬ ActE X Psp Y b := sk'_notAct_r X Y m d hb hp hbit (Or.inl rfl) (by omega)
      have nb0' : ¬ ActE X Ps Y b' := sk_notAct_r X Y m d hb' hp hbit' (Or.inl rfl) (by omega)
      rcases lt_or_ge p m with hpm | hpm
      · -- above the site
        obtain ⟨h1, hb1⟩ := pass_r_lt hA' hℓ₀' hb hp hbit (by simpa [idx] using hpm)
        obtain ⟨h2, hb2⟩ := pass_r_lt hA' hℓ₁' h1 hp hb1 (by simp [idx]; omega)
        obtain ⟨h1', hb1'⟩ := pass_r_lt hA hℓ₀ hb' hp hbit' (by simp [idx]; omega)
        obtain ⟨h2', hb2'⟩ := pass_r_lt hA hℓ₁ h1' hp hb1' (by simpa [idx] using hpm)
        have hcE := sk'_ext_r X Y m d h2 hp hb2
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y) nb0
          (apassage_step hA' _ (sk'_notAct_r X Y m d h1 hp hb1 (Or.inr rfl) (by omega)) (apassage_end hA' _))
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y) nb0'
          (apassage_step hA _ (sk_notAct_r X Y m d h1' hp hb1' (Or.inr rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, _, Or.inl hcE, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
      rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
      · -- `p = m`: the through-strand enters the crossing at once
        rw [← hpe] at hb hb' hbit hbit'
        have hat : a = true := ha'.symm.trans hbit
        obtain ⟨h1, hb1⟩ := pass_r_ge hA' hℓ₀' hb (by omega) hbit (by simp [idx, arity])
        simp only [arity, coarity, Nat.sub_zero] at h1 hb1
        have hcb : next hA' b = siteB' X Y m d hA' := Subtype.ext (by rw [h1, hsB', ite_eq_left hat])
        obtain ⟨h1', hb1'⟩ := pass_r_lt hA hℓ₀ hb' (by omega) hbit' (by simp [idx])
        have hcb' : next hA b' = siteA X Y m d hA := Subtype.ext (by rw [h1', hsA, ite_eq_left hat])
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y) nb0 (apassage_end hA' _)
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y) nb0' (apassage_end hA _)
        have hcA : ActE X Psp Y (next hA' b) := by rw [hcb]; exact Or.inr (siteB'_int X Y m d hA')
        refine ⟨n, _, hcA, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc', hcb']
        exact ((φcongr _ _ hcA (Or.inr (siteB'_int X Y m d hA')) hcb).trans (φintB _)).symm
      · -- below the site
        obtain ⟨h1, hb1⟩ := pass_r_ge hA' hℓ₀' hb hp hbit (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.sub_zero] at h1 hb1
        obtain ⟨h2, hb2⟩ := pass_r_ge hA' hℓ₁' h1 (by omega) hb1 (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
        obtain ⟨h1', hb1'⟩ := pass_r_ge hA hℓ₀ hb' hp hbit' (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.sub_zero] at h1' hb1'
        obtain ⟨h2', hb2'⟩ := pass_r_ge hA hℓ₁ h1' (by omega) hb1' (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h2' hb2'
        have hcE := sk'_ext_r X Y m d h2 (by omega) hb2
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y) nb0
          (apassage_step hA' _ (sk'_notAct_r X Y m d h1 (by omega) hb1 (Or.inr rfl) (by omega)) (apassage_end hA' _))
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y) nb0'
          (apassage_step hA _ (sk_notAct_r X Y m d h1' (by omega) hb1' (Or.inr rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, _, Or.inl hcE, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
    · -- from the right at `(|X|+2, p)`
      replace hb : b.1 = (X.length + 2, p) := hb
      replace hbit : bit Vsp (X.length + 2) p = false := hbit
      have hb' : b'.1 = (X.length + 2, p) := hb'v.trans hb
      have hbit' : bit Vs (X.length + 2) p = false := by rw [(hbx p).2]; exact hbit
      rcases lt_or_ge p m with hpm | hpm
      · -- above the site
        obtain ⟨h1, hb1⟩ := pass_l_lt hA' hℓ₁' hb hp hbit (by simp [idx]; omega)
        obtain ⟨h2, hb2⟩ := pass_l_lt hA' hℓ₀' h1 hp hb1 (by simpa [idx] using hpm)
        obtain ⟨h1', hb1'⟩ := pass_l_lt hA hℓ₁ hb' hp hbit' (by simpa [idx] using hpm)
        obtain ⟨h2', hb2'⟩ := pass_l_lt hA hℓ₀ h1' hp hb1' (by simp [idx]; omega)
        have hcE := sk'_ext_l X Y m d hA' h2 hp hb2
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y)
          (sk'_notAct_l X Y m d hb hp hbit (Or.inr rfl) (by omega))
          (apassage_step hA' _ (sk'_notAct_l X Y m d h1 hp hb1 (Or.inl rfl) (by omega)) (apassage_end hA' _))
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y)
          (sk_notAct_l X Y m d hb' hp hbit' (Or.inr rfl) (by omega))
          (apassage_step hA _ (sk_notAct_l X Y m d h1' hp hb1' (Or.inl rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, _, Or.inl hcE, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · -- the three site positions
        have hp3 : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
        rcases hp3 with hpe | hpe | hpe
        · -- `p = m`: the upper arm heading left; in `A` this is the arm slot at once
          rw [hpe] at hb hb' hbit hbit'
          have hdf : d = false := e1'.symm.trans hbit
          obtain ⟨h1, hb1⟩ := pass_l_lt hA' hℓ₁' hb (by omega) hbit (by simp [idx])
          have h2 := next_arm_l hA' (by rw [sk'_length]; omega) hℓ₀' h1 (Or.inl rfl) hb1
          have h3 := next_cusp_l hA' hℓ₀' h2
          rw [ite_eq_right (by simp [hdf])] at h3
          have hb3 : bit Vsp (X.length + 1) (m + 1) = true := by rw [c2', hdf]; rfl
          have hcb : next hA' (next hA' (next hA' b)) = siteA' X Y m d hA' :=
            Subtype.ext (by rw [h3, hsA', ite_eq_right (by simp [hdf])])
          have hcb' : b' = siteB X Y m d hA := Subtype.ext (by rw [hb', hsB, ite_eq_right (by simp [hdf])])
          obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y)
            (sk'_notAct_l X Y m d hb (by omega) hbit (Or.inr rfl) (by omega))
            (apassage_step hA' _ (sk'_notAct_l X Y m d h1 (by omega) hb1 (Or.inl rfl) (by omega))
            (apassage_step hA' _ (sk'_notAct_v X Y m d h2 (Or.inl rfl)) (apassage_end hA' _)))
          have hcA : ActE X Psp Y (next hA' (next hA' (next hA' b))) := by
            rw [hcb]; exact Or.inr (siteA'_int X Y m d hA')
          refine ⟨n, _, hcA, hc, hmin, 0, b', rfl, ?_, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
          rw [Function.iterate_zero, id, hcb']
          exact ((φcongr _ _ hcA (Or.inr (siteA'_int X Y m d hA')) hcb).trans (φintA _)).symm
        · -- `p = m + 1`: the through-strand heading left is the site slot in both words
          rw [hpe] at hb hb' hbit hbit'
          have haf : a = false := e2'.symm.trans hbit
          have hcb : b = siteB' X Y m d hA' := Subtype.ext (by rw [hb, hsB', ite_eq_right (by simp [haf])])
          have hcb' : b' = siteA X Y m d hA := Subtype.ext (by rw [hb', hsA, ite_eq_right (by simp [haf])])
          have hcA : ActE X Psp Y b := by rw [hcb]; exact Or.inr (siteB'_int X Y m d hA')
          refine ⟨0, b, hcA, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _), 0, b', rfl, ?_,
            fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
          rw [Function.iterate_zero, id, hcb']
          exact ((φcongr _ _ hcA (Or.inr (siteB'_int X Y m d hA')) hcb).trans (φintB _)).symm
        · -- `p = m + 2`: the lower arm heading left is the site slot of `A'`; in `A` it reaches the arm slot
          rw [hpe] at hb hb' hbit hbit'
          have hdt : d = true := by
            have := e3'.symm.trans hbit
            cases d <;> simp_all
          have hcb : b = siteA' X Y m d hA' := Subtype.ext (by rw [hb, hsA', ite_eq_left hdt])
          have hcA : ActE X Psp Y b := by rw [hcb]; exact Or.inr (siteA'_int X Y m d hA')
          obtain ⟨h1', hb1'⟩ := pass_l_ge hA hℓ₁ hb' (by omega) hbit' (by simp [idx, coarity])
          simp only [arity, coarity, Nat.add_sub_cancel] at h1' hb1'
          have h2' := next_arm_l hA (by rw [sk_length]; omega) hℓ₀ h1' (Or.inr rfl) hb1'
          have h3' := next_cusp_l hA hℓ₀ h2'
          rw [ite_eq_left hdt] at h3'
          have hcb' : next hA (next hA (next hA b')) = siteB X Y m d hA :=
            Subtype.ext (by rw [h3', hsB, ite_eq_left hdt])
          obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y)
            (sk_notAct_l X Y m d hb' (by omega) hbit' (Or.inr rfl) (by omega))
            (apassage_step hA _ (sk_notAct_l X Y m d h1' (by omega) hb1' (Or.inl rfl) (by omega))
            (apassage_step hA _ (sk_notAct_v X Y m d h2' (Or.inl rfl)) (apassage_end hA _)))
          refine ⟨0, b, hcA, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _), n', b', rfl, ?_, hmin'⟩
          rw [hc', hcb']
          exact ((φcongr _ _ hcA (Or.inr (siteA'_int X Y m d hA')) hcb).trans (φintA _)).symm
      · -- below the site
        obtain ⟨h1, hb1⟩ := pass_l_ge hA' hℓ₁' hb hp hbit (by simp [idx, coarity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        obtain ⟨h2, hb2⟩ := pass_l_ge hA' hℓ₀' h1 hp hb1 (by simp [idx, coarity]; omega)
        simp only [arity, coarity] at h2 hb2
        obtain ⟨h1', hb1'⟩ := pass_l_ge hA hℓ₁ hb' hp hbit' (by simp [idx, coarity]; omega)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1' hb1'
        obtain ⟨h2', hb2'⟩ := pass_l_ge hA hℓ₀ h1' hp hb1' (by simp [idx, coarity]; omega)
        simp only [arity, coarity] at h2' hb2'
        have hcE := sk'_ext_l X Y m d hA' h2 (by omega) hb2
        obtain ⟨n, hc, hmin⟩ := apassage_step hA' (ActE X Psp Y)
          (sk'_notAct_l X Y m d hb hp hbit (Or.inr rfl) (by omega))
          (apassage_step hA' _ (sk'_notAct_l X Y m d h1 hp hb1 (Or.inl rfl) (by omega)) (apassage_end hA' _))
        obtain ⟨n', hc', hmin'⟩ := apassage_step hA (ActE X Ps Y)
          (sk_notAct_l X Y m d hb' hp hbit' (Or.inr rfl) (by omega))
          (apassage_step hA _ (sk_notAct_l X Y m d h1' hp hb1' (Or.inl rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, _, Or.inl hcE, hc, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  · -- the interior slots
    intro u hu
    rcases (sk'_int_iff X Y m d hA' u).1 hu with rfl | rfl
    · -- the arm slot of `A'` ↦ the arm slot of `A`
      have hφ : (skφI X Y m d hA hA' ⟨_, hu⟩).1 = siteB X Y m d hA := skφI_siteA' X Y m d hA hA'
      rcases Bool.eq_false_or_eq_true d with hdt | hdf
      · -- `d = true`: `(|X|+2, m+2)` leftward, through the cusp, out at `(|X|+2, m)`
        have hu1 : (siteA' X Y m d hA').1 = (X.length + 2, m + 1 + 1) := by rw [hsA', ite_eq_left hdt]
        have hb1 : bit Vsp (X.length + 2) (m + 1 + 1) = false := by rw [e3', hdt]; rfl
        have h1 := next_σ_left_succ hA' hℓ₁' hu1 hb1
        have hb2 : bit Vsp (X.length + 1) (m + 1) = false := by rw [c2', hdt]; rfl
        have h2 := next_arm_l hA' (by rw [sk'_length]; omega) hℓ₀' h1 (Or.inr rfl) hb2
        have h3 := next_cusp_l hA' hℓ₀' h2
        rw [ite_eq_left hdt] at h3
        have hb3 : bit Vsp (X.length + 1) m = true := by rw [c1', hdt]
        obtain ⟨h4, hb4⟩ := pass_r_lt hA' hℓ₁' h3 (by omega) hb3 (by simp [idx])
        have hcE := sk'_ext_r X Y m d h4 (by omega) hb4
        obtain ⟨n, hn, hc, hmin⟩ := apassage_pos hA' (ActE X Psp Y)
          (apassage_step hA' _ (sk'_notAct_l X Y m d h1 (by omega) hb2 (Or.inl rfl) (by omega))
          (apassage_step hA' _ (sk'_notAct_v X Y m d h2 (Or.inl rfl))
          (apassage_step hA' _ (sk'_notAct_r X Y m d h3 (by omega) hb3 (Or.inr rfl) (by omega)) (apassage_end hA' _))))
        have hu1' : (siteB X Y m d hA).1 = (X.length + 1, m + 1) := by rw [hsB, ite_eq_left hdt]
        have hb1' : bit Vs (X.length + 1) (m + 1) = true := by rw [c2, hdt]
        have h1' := next_σ_right_succ hA hℓ₁ hu1' hb1'
        refine ⟨n, hn, _, Or.inl hcE, hc, hmin, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        rw [Function.iterate_one, hφ]; apply Subtype.ext; rw [φext _ hcE, h4, h1']
      · -- `d = false`: `(|X|+1, m+1)` rightward through the crossing, out at `(|X|+2, m+2)`
        have hu1 : (siteA' X Y m d hA').1 = (X.length + 1, m + 1) := by rw [hsA', ite_eq_right (by simp [hdf])]
        have hb1 : bit Vsp (X.length + 1) (m + 1) = true := by rw [c2', hdf]; rfl
        have h1 := next_σ_right_idx hA' hℓ₁' hu1 hb1
        have hb1e : bit Vsp (X.length + 2) (m + 1 + 1) = true := by rw [e3', hdf]; rfl
        have hcE := sk'_ext_r X Y m d h1 (by omega) hb1e
        obtain ⟨n, hn, hc, hmin⟩ := apassage_pos hA' (ActE X Psp Y) (apassage_end hA' _)
        have hu1' : (siteB X Y m d hA).1 = (X.length + 2, m) := by rw [hsB, ite_eq_right (by simp [hdf])]
        have hb1' : bit Vs (X.length + 2) m = false := by rw [e1, hdf]
        have h1' := next_σ_left_idx hA hℓ₁ hu1' hb1'
        have hb2' : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, hdf]
        have h2' := next_arm_l hA (by rw [sk_length]; omega) hℓ₀ h1' (Or.inl rfl) hb2'
        have h3' := next_cusp_l hA hℓ₀ h2'
        rw [ite_eq_right (by simp [hdf])] at h3'
        have hb3' : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hdf]; rfl
        obtain ⟨h4', hb4'⟩ := pass_r_ge hA hℓ₁ h3' (by omega) hb3' (by simp [idx, arity])
        simp only [arity, coarity, Nat.add_sub_cancel] at h4' hb4'
        obtain ⟨n', hn', hc', hmin'⟩ := apassage_pos hA (ActE X Ps Y)
          (apassage_step hA _ (sk_notAct_l X Y m d h1' (by omega) hb2' (Or.inl rfl) (by omega))
          (apassage_step hA _ (sk_notAct_v X Y m d h2' (Or.inl rfl))
          (apassage_step hA _ (sk_notAct_r X Y m d h3' (by omega) hb3' (Or.inr rfl) (by omega)) (apassage_end hA _))))
        refine ⟨n, hn, _, Or.inl hcE, hc, hmin, n', hn', ?_, ?_⟩
        · rw [hφ, hc']; apply Subtype.ext; rw [φext _ hcE, h1, h4']
        · rw [hφ]; exact hmin'
    · -- the through-strand slot of `A'` ↦ the through-strand slot of `A`
      have hφ : (skφI X Y m d hA hA' ⟨_, hu⟩).1 = siteA X Y m d hA := skφI_siteB' X Y m d hA hA'
      rcases Bool.eq_false_or_eq_true a with hat | haf
      · -- `a = true`: `(|X|+1, m+2)` rightward through the crossing, out at `(|X|+2, m+1)`
        have hu1 : (siteB' X Y m d hA').1 = (X.length + 1, m + 1 + 1) := by rw [hsB', ite_eq_left hat]
        have hb1 : bit Vsp (X.length + 1) (m + 1 + 1) = true := by rw [c3', hat]
        have h1 := next_σ_right_succ hA' hℓ₁' hu1 hb1
        have hb1e : bit Vsp (X.length + 2) (m + 1) = true := by rw [e2', hat]
        have hcE := sk'_ext_r X Y m d h1 (by omega) hb1e
        obtain ⟨n, hn, hc, hmin⟩ := apassage_pos hA' (ActE X Psp Y) (apassage_end hA' _)
        have hu1' : (siteA X Y m d hA).1 = (X.length + 1, m) := by rw [hsA, ite_eq_left hat]
        have hb1' : bit Vs (X.length + 1) m = true := by rw [c1, hat]
        have h1' := next_σ_right_idx hA hℓ₁ hu1' hb1'
        refine ⟨n, hn, _, Or.inl hcE, hc, hmin, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        rw [Function.iterate_one, hφ]; apply Subtype.ext; rw [φext _ hcE, h1, h1']
      · -- `a = false`: `(|X|+2, m+1)` leftward through the crossing, out at `(|X|, m)`
        have hu1 : (siteB' X Y m d hA').1 = (X.length + 2, m + 1) := by rw [hsB', ite_eq_right (by simp [haf])]
        have hb1 : bit Vsp (X.length + 2) (m + 1) = false := by rw [e2', haf]
        have h1 := next_σ_left_idx hA' hℓ₁' hu1 hb1
        have hb2 : bit Vsp (X.length + 1) (m + 1 + 1) = false := by rw [c3', haf]
        obtain ⟨h2, hb2e⟩ := pass_l_ge hA' hℓ₀' h1 (by omega) hb2 (by simp [idx, coarity])
        simp only [arity, coarity] at h2 hb2e
        have hcE := sk'_ext_l X Y m d hA' h2 (by omega) hb2e
        obtain ⟨n, hn, hc, hmin⟩ := apassage_pos hA' (ActE X Psp Y)
          (apassage_step hA' _ (sk'_notAct_l X Y m d h1 (by omega) hb2 (Or.inl rfl) (by omega)) (apassage_end hA' _))
        have hu1' : (siteA X Y m d hA).1 = (X.length + 2, m + 1) := by rw [hsA, ite_eq_right (by simp [haf])]
        have hb1' : bit Vs (X.length + 2) (m + 1) = false := by rw [e2, haf]
        have h1' := next_σ_left_succ hA hℓ₁ hu1' hb1'
        have hb2b : bit Vs (X.length + 1) m = false := by rw [c1, haf]
        obtain ⟨h2', hb2c⟩ := pass_l_lt hA hℓ₀ h1' (by omega) hb2b (by simp [idx])
        obtain ⟨n', hn', hc', hmin'⟩ := apassage_pos hA (ActE X Ps Y)
          (apassage_step hA _ (sk_notAct_l X Y m d h1' (by omega) hb2b (Or.inl rfl) (by omega)) (apassage_end hA _))
        refine ⟨n, hn, _, Or.inl hcE, hc, hmin, n', hn', ?_, ?_⟩
        · rw [hφ, hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
          simp only [Prod.mk.injEq, true_and]; omega
        · rw [hφ]; exact hmin'

end SkeinIntPassage

section SkeinSwitchIso

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Vsp" => X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Psp" => [Letter.l m d, Letter.σ (m + 1)]

variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)
  (hA' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y).Closed)
variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)

/-- the site slot of `A` as an occurrence of its abstract record -/
noncomputable def siteX : (slotRecord hA IsσSlot (allActive hA)).M := ⟨siteA X Y m d hA, isσSlot_σSlotA hA _ _⟩

theorem siteX_val : (siteX X Y m d hA).1 = siteA X Y m d hA := rfl

include hX hP hm hA' in
/-- THE SWITCH HALF of the cusp-skein site: the `σ`-slot record of `A'` is the `σ`-slot record of `A`
switched at the site. -/
theorem sk_switchIso :
    Nonempty (RecordIso (slotRecord hA' IsσSlot (allActive hA'))
      ((slotRecord hA IsσSlot (allActive hA)).switch (siteX X Y m d hA))) := by
  have hE := sk_sameEffect X m d a hX hP hm
  have hPne : Psp ≠ [] := sk_Pne m d
  have ha' := (sk_bit_a X Y m d a hX hP).2
  have ha := (sk_bit_a X Y m d a hX hP).1
  refine ⟨recordIsoOfConjSwitch hA' hA (ActE X Psp Y) (ActE X Ps Y)
    (φA X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' (skφI X Y m d hA hA'))
    (conj_of_intPassage X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' hA _
      (sk_intPassage X Y m d a hA hA' hX hP hm))
    (fun u => by obtain ⟨n, hn⟩ := sk'_hexit X Y m d a hX hP hm hA' u; exact ⟨n, Or.inl hn⟩)
    (fun u => by obtain ⟨n, hn⟩ := sk_hexit X Y m d a hX hP hm hA u; exact ⟨n, Or.inl hn⟩)
    (fun _ hu => isσSlot_actE X Psp Y hu) (fun _ hu => isσSlot_actE X Ps Y hu) ?_ ?_ (siteX X Y m d hA)
    (IntSlot X Psp Y) ?_ ?_ ?_ ?_ ?_⟩
  · -- `σ` slots correspond
    intro u
    by_cases hext : ExtPiece X Psp Y u.1
    · rw [φA_val_ext X Psp Y Ps _ _ hA' _ u hext]
      exact isσSlot_φE_iff X Psp Y Ps _ _ hA' ⟨u.1, hext⟩
    · rw [φA_val_int X Psp Y Ps _ _ hA' _ u hext]
      exact iff_of_true (skφI X Y m d hA hA' ⟨u.1, u.2.resolve_left hext⟩).2.1 (u.2.resolve_left hext).1
  · -- twins correspond
    intro u hu
    by_cases hext : ExtPiece X Psp Y u.1
    · have hext2 : ExtPiece X Psp Y (σtwin hA' u.1) := extPiece_σtwin X Psp Y hA' hu hext
      rw [φA_val_ext X Psp Y Ps _ _ hA' _ _ hext2, φA_val_ext X Psp Y Ps _ _ hA' _ u hext]
      exact φE_σtwin X Psp Y Ps _ _ hA' hA ⟨u.1, hext⟩ hu
    · have hint : IntSlot X Psp Y u.1 := u.2.resolve_left hext
      have hext2 : ¬ ExtPiece X Psp Y (σtwin hA' u.1) := by
        show ¬ ExtCol X Psp (colOf _); rw [colOf_σtwin hA' hu]; exact hint.2
      rw [φA_val_int X Psp Y Ps _ _ hA' _ _ hext2, φA_val_int X Psp Y Ps _ _ hA' _ u hext]
      exact skφI_twin X Y m d hA hA' ⟨u.1, hint⟩
  · -- the site
    intro u hu
    constructor
    · intro h
      by_contra hint
      have hext : ExtPiece X Psp Y u.1 := u.2.resolve_right hint
      have hE2 := (φE X Psp Y Ps (sk_Pne m d) (sk_sameEffect X m d a hX hP hm) hA' ⟨u.1, hext⟩).2
      rw [← φA_val_ext X Psp Y Ps _ _ hA' (skφI X Y m d hA hA') u hext] at hE2
      rcases h with h | h
      · rw [h, siteX_val] at hE2; exact (siteA_int X Y m d hA).2 hE2
      · rw [h, siteX_val, σtwin_siteA] at hE2; exact (siteB_int X Y m d hA).2 hE2
    · intro hint
      rw [φA_val_int X Psp Y Ps _ _ hA' _ u (fun h => hint.2 h), skφI_val, siteX_val, σtwin_siteA]
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
  · intro u hu hint
    rw [φA_val_int X Psp Y Ps _ _ hA' _ u (fun h => hint.2 h)]
    exact skφI_desc X Y m d hA hA' ⟨u.1, hint⟩
  · intro u hu hint
    have hext : ExtPiece X Psp Y u.1 := u.2.resolve_right hint
    rw [φA_val_ext X Psp Y Ps _ _ hA' _ u hext]
    exact isDesc_φE X Psp Y Ps _ _ hA' ⟨u.1, hext⟩
  · intro u hu hint
    rw [φA_val_int X Psp Y Ps _ _ hA' _ u (fun h => hint.2 h)]
    exact skφI_sgn X Y m d a hA hA' ha ha' ⟨u.1, hint⟩
  · intro u hu hint
    have hext : ExtPiece X Psp Y u.1 := u.2.resolve_right hint
    rw [φA_val_ext X Psp Y Ps _ _ hA' _ u hext]
    exact σsgn_φE X Psp Y Ps _ _ hA' ⟨u.1, hext⟩

include hX hP in
/-- the sign of the site -/
theorem siteX_sgn :
    (((slotRecord hA IsσSlot (allActive hA)).sgn (siteX X Y m d hA) : SignType) : ℤ) = if a = d then 1 else -1 := by
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1, c2, -, -, -, -⟩ := sk_bits X Y m d a hA ha
  show ((σsgn (siteA X Y m d hA) : SignType) : ℤ) = _
  unfold σsgn
  rw [show colOf (siteA X Y m d hA) = X.length + 1 from (σSlotA_spec hA _ _).1, coe_σsgnCol,
    (sk_letters X Y m d).2]
  simp only [idx, c1, c2]

end SkeinSwitchIso

/-! #### I. The smoothing half: `Record.smooth` of a slot record as a first return of a reconnected slot
permutation, and its transport along record isomorphisms -/

section SmoothGeneric

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- the swap on a subtype has the swapped value -/
theorem swap_subtype_val {S : α → Prop} (a b v : {x // S x}) :
    (Equiv.swap a b v).1 = Equiv.swap a.1 b.1 v.1 := by
  by_cases hva : v = a
  · subst hva; simp
  · by_cases hvb : v = b
    · subst hvb; simp
    · rw [Equiv.swap_apply_of_ne_of_ne hva hvb,
        Equiv.swap_apply_of_ne_of_ne (fun h => hva (Subtype.ext h)) (fun h => hvb (Subtype.ext h))]

/-- the first return of `f ∘ swap` to `S` (with `a, b ∈ S`) is the first return of `f` composed with the swap -/
theorem firstReturn_mul_swap (f : Perm α) (S : α → Prop) [DecidablePred S] (a b : α) (ha : S a) (hb : S b)
    (v : {x // S x}) :
    firstReturn (f * Equiv.swap a b) S v = firstReturn f S (Equiv.swap ⟨a, ha⟩ ⟨b, hb⟩ v) := by
  set w := Equiv.swap (⟨a, ha⟩ : {x // S x}) ⟨b, hb⟩ v with hw
  have hwv : w.1 = Equiv.swap a b v.1 := swap_subtype_val ⟨a, ha⟩ ⟨b, hb⟩ v
  set r := returnTime f S w.1 w.2 with hr
  have hrpos : 0 < r := returnTime_pos f S w.1 w.2
  have hpow : ∀ i, 1 ≤ i → i ≤ r → ((f * Equiv.swap a b) ^ i) v.1 = (f ^ i) w.1 := by
    intro i hi1 hir
    induction i with
    | zero => omega
    | succ i ih =>
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp only [zero_add, pow_one, Perm.mul_apply, hwv]
      · rw [pow_succ', Perm.mul_apply, ih hi (by omega), Perm.mul_apply, pow_succ', Perm.mul_apply]
        congr 1
        have hnot : ¬ S ((f ^ i) w.1) := returnTime_min f S w.1 w.2 hi (by omega)
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hnot (h ▸ ha)) (fun h => hnot (h ▸ hb))
  apply Subtype.ext
  rw [firstReturn_eq_of_path (f * Equiv.swap a b) S v hrpos]
  · rw [hpow r hrpos le_rfl, firstReturn_apply]
  · rw [hpow r hrpos le_rfl]; exact returnTime_spec f S w.1 w.2
  · intro i hi hir
    rw [hpow i hi hir.le]
    exact returnTime_min f S w.1 w.2 hi hir

omit [DecidableEq α] in
/-- first returns to pointwise-equivalent predicates (instances given explicitly) have equal values -/
theorem firstReturn_val_congr (f : Perm α) (p q : α → Prop) (ip : DecidablePred p) (iq : DecidablePred q)
    (hpq : ∀ a, p a ↔ q a) (a : {x // p x}) :
    (@firstReturn α _ f p ip a).1 = (@firstReturn α _ f q iq ⟨a.1, (hpq _).1 a.2⟩).1 := by
  have hr : @returnTime α _ f q iq a.1 ((hpq _).1 a.2) = @returnTime α _ f p ip a.1 a.2 := by
    rw [@returnTime_eq_iff α _ f q iq]
    refine ⟨⟨@returnTime_pos α _ f p ip a.1 a.2, (hpq _).1 (@returnTime_spec α _ f p ip a.1 a.2)⟩, ?_⟩
    intro j hj ⟨hj0, hq⟩
    exact @returnTime_min α _ f p ip a.1 a.2 j hj0 hj ((hpq _).2 hq)
  rw [@firstReturn_apply α _ f p ip a, @firstReturn_apply α _ f q iq _, hr]

end SmoothGeneric

section SmoothCongr

/-- `Record.smooth` is functorial in named record isomorphisms. -/
noncomputable def smoothCongr {ρ ρ' : Record} (ι : RecordIso ρ ρ') (x : ρ.M) :
    RecordIso (ρ.smooth x) (ρ'.smooth (ι.Φ x)) :=
  let hrec : ∀ v, ι.Φ (ρ.reconnect x v) = ρ'.reconnect (ι.Φ x) (ι.Φ v) := fun v => by
    unfold Record.reconnect
    rw [Perm.mul_apply, Perm.mul_apply, ι.succ_eq]
    congr 1
    by_cases hv : v = x
    · subst hv; rw [Equiv.swap_apply_left, Equiv.swap_apply_left]; exact ι.pair_eq _
    · by_cases hv' : v = ρ.pair x
      · subst hv'; rw [Equiv.swap_apply_right, ι.pair_eq, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hv hv', Equiv.swap_apply_of_ne_of_ne (fun h => hv (ι.Φ.injective h))
          (fun h => hv' (ι.Φ.injective (by rw [h, ι.pair_eq])))]
  let hkeep : ∀ v, ρ.SmoothKeep x v ↔ ρ'.SmoothKeep (ι.Φ x) (ι.Φ v) := fun v => by
    unfold Record.SmoothKeep
    rw [not_iff_not, ι.mem_pair_iff]
  { e := Equiv.sumCongr
      (Quotient.congr ι.Φ (fun v w => (sameCycle_iff_of_conj (ρ.reconnect x) (ρ'.reconnect (ι.Φ x)) hrec v w).symm))
      { toFun := fun c => ⟨ι.e c.1, fun v h => c.2 (ι.Φ.symm v) (by
            rw [← ι.e.injective.eq_iff, ← ι.comp_eq, Equiv.apply_symm_apply, h])⟩
        invFun := fun c => ⟨ι.e.symm c.1, fun v h => c.2 (ι.Φ v) (by rw [ι.comp_eq, h, Equiv.apply_symm_apply])⟩
        left_inv := fun c => Subtype.ext (Equiv.symm_apply_apply _ _)
        right_inv := fun c => Subtype.ext (Equiv.apply_symm_apply _ _) }
    Φ := Equiv.subtypeEquiv ι.Φ hkeep
    comp_eq := fun v => by
      show Sum.inl (Quotient.mk _ (ι.Φ v.1)) = Sum.inl (Quotient.congr ι.Φ _ (Quotient.mk _ v.1))
      rfl
    succ_eq := fun v => by
      apply Subtype.ext
      show ι.Φ (firstReturn (ρ.reconnect x) (ρ.SmoothKeep x) v).1 =
        (firstReturn (ρ'.reconnect (ι.Φ x)) (ρ'.SmoothKeep (ι.Φ x)) ⟨ι.Φ v.1, (hkeep v.1).1 v.2⟩).1
      exact (firstReturn_conj (ρ.reconnect x) (ρ'.reconnect (ι.Φ x)) (ρ.SmoothKeep x) (ρ'.SmoothKeep (ι.Φ x))
        ι.Φ hrec (fun v => (hkeep v).symm) v).symm
    pair_eq := fun v => by
      apply Subtype.ext
      show ι.Φ (ρ.pair v.1) = ρ'.pair (ι.Φ v.1)
      exact ι.pair_eq v.1
    bit_eq := fun v => ι.bit_eq v.1
    sgn_eq := fun v => ι.sgn_eq v.1 }

end SmoothCongr

section SmoothIso

variable {W W' : Word} (hW : W.Closed) (hW' : W'.Closed)
  (E : Slot W → Prop) (E' : Slot W' → Prop) [DecidablePred E] [DecidablePred E']
  (φ : {u // E u} ≃ {u' // E' u'}) (x₀ : (slotRecord hW IsσSlot (allActive hW)).M)

/-- the reconnected slot permutation: the traversal with the two site slots exchanged -/
noncomputable def gPerm : Perm (Slot W) := nextPerm hW * Equiv.swap x₀.1 (σtwin hW x₀.1)

omit hW' E E' φ in
theorem gPerm_apply_of_ne {u : Slot W} (h1 : u ≠ x₀.1) (h2 : u ≠ σtwin hW x₀.1) :
    gPerm hW x₀ u = next hW u := by
  unfold gPerm
  rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2, nextPerm_apply]

omit hW' E E' φ in
theorem gPerm_apply_of_not_σ {u : Slot W} (h : ¬ IsσSlot u) : gPerm hW x₀ u = next hW u :=
  gPerm_apply_of_ne hW x₀ (fun e => h (e ▸ x₀.2)) (fun e => h (e ▸ isσSlot_σtwin hW x₀.2))

omit hW' E E' φ in
theorem gPerm_pow_of_not_σ {u : Slot W} (h : ∀ n, ¬ IsσSlot ((next hW)^[n] u)) (n : ℕ) :
    ((gPerm hW x₀) ^ n) u = (next hW)^[n] u := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, ih, Function.iterate_succ_apply']
    exact gPerm_apply_of_not_σ hW x₀ (h n)

omit hW' E E' φ in
/-- the record-level reconnection is the first return of the reconnected slot permutation -/
theorem reconnect_eq :
    (slotRecord hW IsσSlot (allActive hW)).reconnect x₀ =
      (firstReturn (gPerm hW x₀) IsσSlot : Perm (slotRecord hW IsσSlot (allActive hW)).M) := by
  refine Equiv.ext fun v => ?_
  have hpair : (slotRecord hW IsσSlot (allActive hW)).pair x₀ = ⟨σtwin hW x₀.1, isσSlot_σtwin hW x₀.2⟩ :=
    Subtype.ext (slotRecord_pair_val hW _ _ x₀)
  have h := firstReturn_mul_swap (nextPerm hW) IsσSlot x₀.1 (σtwin hW x₀.1) x₀.2 (isσSlot_σtwin hW x₀.2) v
  refine Eq.trans ?_ h.symm
  show (slotRecord hW IsσSlot (allActive hW)).succ
    (Equiv.swap x₀ ((slotRecord hW IsσSlot (allActive hW)).pair x₀) v) = _
  rw [hpair]
  rfl

omit hW' E E' φ in
theorem smoothKeep_iff' (v : (slotRecord hW IsσSlot (allActive hW)).M) :
    (slotRecord hW IsσSlot (allActive hW)).SmoothKeep x₀ v ↔ v.1 ≠ x₀.1 ∧ v.1 ≠ σtwin hW x₀.1 := by
  rw [Record.smoothKeep_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (Subtype.ext h), fun h => h2 (Subtype.ext (h.trans (slotRecord_pair_val hW _ _ x₀).symm))⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (congrArg Subtype.val h),
      fun h => h2 ((congrArg Subtype.val h).trans (slotRecord_pair_val hW _ _ x₀))⟩

/-- the kept σ slots -/
noncomputable def KeptSlot (u : Slot W) : Prop := IsσSlot u ∧ u ≠ x₀.1 ∧ u ≠ σtwin hW x₀.1

noncomputable instance : DecidablePred (KeptSlot hW x₀) := fun u => by unfold KeptSlot; infer_instance


omit hW' E E' φ in
/-- the smoothed successor is the first return of the reconnected slot permutation to the kept slots -/
theorem smooth_succ_val_eq (v : ((slotRecord hW IsσSlot (allActive hW)).smooth x₀).M) :
    (((slotRecord hW IsσSlot (allActive hW)).smooth x₀).succ v).1.1 =
      (firstReturn (gPerm hW x₀) (KeptSlot hW x₀) ⟨v.1.1, v.1.2, ((smoothKeep_iff' hW x₀ v.1).1 v.2)⟩).1 := by
  have e1 : (((slotRecord hW IsσSlot (allActive hW)).smooth x₀).succ v).1 =
      (firstReturn ((slotRecord hW IsσSlot (allActive hW)).reconnect x₀)
        ((slotRecord hW IsσSlot (allActive hW)).SmoothKeep x₀) v).1 := rfl
  rw [reconnect_eq hW x₀] at e1
  have e2 := @firstReturn_val_congr _ _ (firstReturn (gPerm hW x₀) IsσSlot)
    ((slotRecord hW IsσSlot (allActive hW)).SmoothKeep x₀) (fun b => KeptSlot hW x₀ b.1)
    (Record.instDecidablePredMSmoothKeep _ x₀) inferInstance
    (fun b => by rw [smoothKeep_iff' hW x₀ b]; exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩) v
  rw [firstReturn_factor (gPerm hW x₀) IsσSlot (KeptSlot hW x₀) (fun _ h => h.1)]
  exact congrArg Subtype.val (e1.trans e2)

variable (hint : ∀ u, IsσSlot u → u ≠ x₀.1 → u ≠ σtwin hW x₀.1 → E u)
  (hnot₁ : ¬ E x₀.1) (hnot₂ : ¬ E (σtwin hW x₀.1))
  (hσE' : ∀ u', IsσSlot u' → E' u')
  (conj : ∀ u, firstReturn (nextPerm hW') E' (φ u) = φ (firstReturn (gPerm hW x₀) E u))
  (hexit : ∀ u : Slot W, ∃ n : ℕ, E (((gPerm hW x₀) ^ n) u))
  (hexit' : ∀ u' : Slot W', ∃ n : ℕ, E' (((nextPerm hW') ^ n) u'))
  (hσ : ∀ u : {u // E u}, IsσSlot (φ u).1 ↔ IsσSlot u.1)
  (hEtwin : ∀ u, E u → IsσSlot u → E (σtwin hW u))
  (htwin : ∀ (u : {u // E u}) (hu : IsσSlot u.1), (φ ⟨σtwin hW u.1, hEtwin _ u.2 hu⟩).1 = σtwin hW' (φ u).1)
  (hdesc : ∀ u : {u // E u}, IsσSlot u.1 → isDesc (φ u).1 = isDesc u.1)
  (hsgn : ∀ u : {u // E u}, IsσSlot u.1 → σsgn (φ u).1 = σsgn u.1)

include hnot₁ hnot₂ in
omit hW' E' φ [DecidablePred E] in
theorem kept_of_E {u : Slot W} (hu : E u) (hσu : IsσSlot u) : KeptSlot hW x₀ u :=
  ⟨hσu, fun h => hnot₁ (h ▸ hu), fun h => hnot₂ (h ▸ hu)⟩

include hint in
omit hW' E' φ [DecidablePred E] in
theorem E_of_kept {u : Slot W} (hu : KeptSlot hW x₀ u) : E u := hint u hu.1 hu.2.1 hu.2.2

/-- the components of the smoothing are the cycles of the reconnected slot permutation -/
noncomputable def smoothCompsEquiv :
    ((slotRecord hW IsσSlot (allActive hW)).smooth x₀).comps ≃ Quotient (Perm.SameCycle.setoid (gPerm hW x₀)) := by
  let ρ := slotRecord hW IsσSlot (allActive hW)
  let g := gPerm hW x₀
  -- the σ-cycles
  let toG : Quotient (Perm.SameCycle.setoid (ρ.reconnect x₀)) → Quotient (Perm.SameCycle.setoid g) :=
    Quotient.lift (fun v : ρ.M => Quotient.mk _ v.1) (fun v w h => Quotient.sound (by
      have h' : (ρ.reconnect x₀).SameCycle v w := h
      rw [reconnect_eq hW x₀] at h'
      exact (firstReturn_sameCycle_iff g IsσSlot v w).1 h'))
  -- the crossing-free cycles
  have hfree : ∀ (i : Fin (numComp hW)), (∀ v : ρ.M, ρ.comp v ≠ i) → ∀ n, ¬ IsσSlot ((next hW)^[n] (rep hW i)) := by
    intro i hi n hσn
    apply hi ⟨_, hσn⟩
    show slotComp hW ((next hW)^[n] (rep hW i)) = i
    rw [slotComp_eq_equivFin]
    have : orbitOf hW ((next hW)^[n] (rep hW i)) = orbitOf hW (rep hW i) := by
      rw [orbitOf_eq_iff]
      exact sameCycle_of_iterate hW (a := 0) (b := n) rfl
    rw [this, orbitOf_rep, Equiv.apply_symm_apply]
  have hfreeCycle : ∀ (i : Fin (numComp hW)) (hi : ∀ v : ρ.M, ρ.comp v ≠ i) (w : Slot W),
      g.SameCycle (rep hW i) w ↔ (nextPerm hW).SameCycle (rep hW i) w := by
    intro i hi w
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      rw [gPerm_pow_of_not_σ hW x₀ (hfree i hi) n] at hn
      exact sameCycle_of_iterate hW (a := n) (b := 0) hn
    · intro h
      obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW h
      exact ⟨n, by rw [zpow_natCast, gPerm_pow_of_not_σ hW x₀ (hfree i hi) n]; exact hn⟩
  let freeG : ρ.FreeComp → Quotient (Perm.SameCycle.setoid g) := fun c => Quotient.mk _ (rep hW c.1)
  refine Equiv.ofBijective (Sum.elim toG freeG) ⟨?_, ?_⟩
  · -- injective
    rintro (q | c) (q' | c') h
    · induction q using Quotient.inductionOn with
      | h v =>
        induction q' using Quotient.inductionOn with
        | h w =>
          have h' : g.SameCycle v.1 w.1 := Quotient.exact h
          rw [← firstReturn_sameCycle_iff g IsσSlot v w, ← reconnect_eq hW x₀] at h'
          exact congrArg Sum.inl (Quotient.sound h')
    · exfalso
      induction q using Quotient.inductionOn with
      | h v =>
        have h' : g.SameCycle v.1 (rep hW c'.1) := Quotient.exact h
        obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW ((hfreeCycle c'.1 c'.2 v.1).1 h'.symm)
        exact hfree c'.1 c'.2 n (hn ▸ v.2)
    · exfalso
      induction q' using Quotient.inductionOn with
      | h v =>
        have h' : g.SameCycle (rep hW c.1) v.1 := Quotient.exact h
        obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW ((hfreeCycle c.1 c.2 v.1).1 h')
        exact hfree c.1 c.2 n (hn ▸ v.2)
    · have h' : g.SameCycle (rep hW c.1) (rep hW c'.1) := Quotient.exact h
      exact congrArg Sum.inr (Subtype.ext (rep_injective_orbit hW ((hfreeCycle c.1 c.2 _).1 h')))
  · -- surjective
    intro q
    induction q using Quotient.inductionOn with
    | h u =>
      by_cases h : ∃ n, IsσSlot ((g ^ n) u)
      · obtain ⟨n, hn⟩ := h
        refine ⟨Sum.inl (Quotient.mk _ ⟨(g ^ n) u, hn⟩), ?_⟩
        show Quotient.mk _ ((g ^ n) u) = Quotient.mk _ u
        exact Quotient.sound (sameCycle_pow g n u).symm
      · replace h : ∀ n, ¬ IsσSlot ((g ^ n) u) := fun n hn => h ⟨n, hn⟩
        have hpow : ∀ n, (g ^ n) u = (next hW)^[n] u := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih =>
            rw [pow_succ', Perm.mul_apply, Function.iterate_succ_apply', ← ih]
            exact gPerm_apply_of_not_σ hW x₀ (h n)
        have hnoσ : ∀ n, ¬ IsσSlot ((next hW)^[n] u) := fun n => by rw [← hpow n]; exact h n
        have hfreeu : ∀ v : ρ.M, ρ.comp v ≠ slotComp hW u := by
          intro v hv
          have : (nextPerm hW).SameCycle u v.1 := ((slotComp_eq_iff hW _ _).1 hv).symm
          obtain ⟨n, hn⟩ := exists_iterate_of_sameCycle hW this
          exact hnoσ n (hn ▸ v.2)
        refine ⟨Sum.inr ⟨slotComp hW u, hfreeu⟩, ?_⟩
        show Quotient.mk _ (rep hW (slotComp hW u)) = Quotient.mk _ u
        apply Quotient.sound
        apply (hfreeCycle (slotComp hW u) hfreeu u).2
        rw [← orbitOf_eq_iff, orbitOf_rep, slotComp_eq_equivFin, Equiv.symm_apply_apply]

theorem smoothCompsEquiv_inl (v : (slotRecord hW IsσSlot (allActive hW)).M) :
    smoothCompsEquiv hW x₀ (Sum.inl (Quotient.mk _ v)) = Quotient.mk _ v.1 := rfl

include hint hnot₁ hnot₂ hσE' conj hexit hexit' hσ hEtwin htwin hdesc hsgn in
/-- THE RECORD ISOMORPHISM OF THE SMOOTHING: the σ-slot record of `W` smoothed at the site `x₀` is the σ-slot
record of `W'`, given conjugate first returns of the reconnected slot permutation of `W` and the traversal
of `W'` on the active supersets `E`, `E'` (all σ slots of `W` other than the site, all σ slots of `W'`). -/
noncomputable def smoothRecordIso :
    RecordIso ((slotRecord hW IsσSlot (allActive hW)).smooth x₀) (slotRecord hW' IsσSlot (allActive hW')) :=
  let ρ := slotRecord hW IsσSlot (allActive hW)
  let g := gPerm hW x₀
  let oe : Quotient (Perm.SameCycle.setoid g) ≃ Orbit hW' := cycleEquiv g (nextPerm hW') E E' φ conj hexit hexit'
  let keptE : ∀ v : (ρ.smooth x₀).M, E v.1.1 := fun v =>
    E_of_kept hW E x₀ hint ⟨v.1.2, (smoothKeep_iff' hW x₀ v.1).1 v.2⟩
  let Φ : (ρ.smooth x₀).M ≃ (slotRecord hW' IsσSlot (allActive hW')).M :=
    { toFun := fun v => ⟨(φ ⟨v.1.1, keptE v⟩).1, (hσ _).2 v.1.2⟩
      invFun := fun u' =>
        let a := φ.symm ⟨u'.1, hσE' _ u'.2⟩
        have hσa : IsσSlot a.1 := by
          have h := (hσ a).1
          rw [Equiv.apply_symm_apply] at h
          exact h u'.2
        ⟨⟨a.1, hσa⟩, (smoothKeep_iff' hW x₀ ⟨a.1, hσa⟩).2 (kept_of_E hW E x₀ hnot₁ hnot₂ a.2 hσa).2⟩
      left_inv := fun v => Subtype.ext (Subtype.ext (by
        show (φ.symm ⟨(φ ⟨v.1.1, keptE v⟩).1, _⟩).1 = v.1.1
        rw [show (⟨(φ ⟨v.1.1, keptE v⟩).1, _⟩ : {u' // E' u'}) = φ ⟨v.1.1, keptE v⟩ from rfl,
          Equiv.symm_apply_apply]))
      right_inv := fun u' => Subtype.ext (by
        show (φ ⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩).1 = u'.1
        rw [show (⟨(φ.symm ⟨u'.1, hσE' _ u'.2⟩).1, _⟩ : {u // E u}) = φ.symm ⟨u'.1, hσE' _ u'.2⟩ from rfl,
          Equiv.apply_symm_apply]) }
  { e := (smoothCompsEquiv hW x₀).trans (oe.trans (Fintype.equivFin (Orbit hW')))
    Φ := Φ
    comp_eq := fun v => by
      have h1 : (slotRecord hW' IsσSlot (allActive hW')).comp (Φ v) =
          Fintype.equivFin (Orbit hW') (orbitOf hW' (φ ⟨v.1.1, keptE v⟩).1) := slotComp_eq_equivFin hW' _
      have h2 : ((smoothCompsEquiv hW x₀).trans (oe.trans (Fintype.equivFin (Orbit hW')))) ((ρ.smooth x₀).comp v) =
          Fintype.equivFin (Orbit hW') (oe (Quotient.mk _ v.1.1)) := rfl
      have key : orbitOf hW' (φ ⟨v.1.1, keptE v⟩).1 = oe (Quotient.mk _ v.1.1) :=
        (cycleEquiv_mk g (nextPerm hW') E E' φ conj hexit hexit' ⟨v.1.1, keptE v⟩).symm
      exact h1.trans ((congrArg (Fintype.equivFin (Orbit hW')) key).trans h2.symm)
    succ_eq := fun v => by
      apply Subtype.ext
      show (φ ⟨((ρ.smooth x₀).succ v).1.1, _⟩).1 = (firstReturn (nextPerm hW') IsσSlot ⟨(φ ⟨v.1.1, _⟩).1, _⟩).1
      have h1 := firstReturn_conj_of_factor g (nextPerm hW') E E' φ conj (KeptSlot hW x₀) IsσSlot
        (fun _ h => E_of_kept hW E x₀ hint h) hσE' (fun a => ⟨fun h => kept_of_E hW E x₀ hnot₁ hnot₂ a.2 ((hσ a).1 h),
          fun h => (hσ a).2 h.1⟩) ⟨v.1.1, v.1.2, (smoothKeep_iff' hW x₀ v.1).1 v.2⟩
      exact (congrArg (fun x : {u // E u} => (φ x).1) (Subtype.ext (smooth_succ_val_eq hW x₀ v))).trans h1.symm
    pair_eq := fun v => by
      apply Subtype.ext
      show (φ ⟨σtwin hW v.1.1, _⟩).1 = σtwin hW' (φ ⟨v.1.1, keptE v⟩).1
      exact htwin ⟨v.1.1, keptE v⟩ v.1.2
    bit_eq := fun v => hdesc ⟨v.1.1, keptE v⟩ v.1.2
    sgn_eq := fun v => hsgn ⟨v.1.1, keptE v⟩ v.1.2 }

end SmoothIso

section PassageF

variable (X P Y P' : Word) (hP : P ≠ []) (hE : SameEffect X P P')
  (hW : (X ++ P ++ Y).Closed) (hW' : (X ++ P' ++ Y).Closed) (f : Perm (Slot (X ++ P ++ Y)))

/-- the block passage hypothesis for a slot permutation `f` agreeing with the traversal on the exterior -/
structure PassageF : Prop where
  pass : ∀ b : Slot (X ++ P ++ Y), IsExtSlot X P b.1 → ¬ ExtCol X P (colOf b) →
    ∃ (m : ℕ) (c : Slot (X ++ P ++ Y)), (f ^ m) b = c ∧ ExtCol X P (colOf c) ∧
      (∀ i < m, ¬ ExtCol X P (colOf ((f ^ i) b))) ∧
      ∃ (m' : ℕ) (b' : Slot (X ++ P' ++ Y)), b'.1 = extPair X P P' b.1 ∧
        ((next hW')^[m'] b').1 = extPair X P P' c.1 ∧
        ∀ i < m', ¬ ExtCol X P' (colOf ((next hW')^[i] b'))

include hP hE in
/-- the passage makes the first returns to the exterior pieces conjugate (`U2.conj_of_passage` for `f`) -/
theorem conj_of_passageF (hf : ∀ u, ExtPiece X P Y u → f u = next hW u) (hpass : PassageF X P Y P' hW' f)
    (u : {u // ExtPiece X P Y u}) :
    firstReturn (nextPerm hW') (ExtPiece X P' Y) (φE X P Y P' hP hE hW u) =
      φE X P Y P' hP hE hW (firstReturn f (ExtPiece X P Y) u) := by
  revert u
  apply conj_of_paths
  intro u
  obtain ⟨hnext_ext, hnext_eq⟩ :=
    next_ext X P Y P' hP hE hW hW' ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ u.2
  have hfu : f u.1 = next hW u.1 := hf u.1 u.2
  have hφu : (φE X P Y P' hP hE hW u).1 = extSlot X P Y P' hP hE ⟨u.1, isExtSlot_of_extCol X P Y P' hP hE u.1 u.2⟩ := rfl
  by_cases hE1 : ExtPiece X P Y (next hW u.1)
  · refine ⟨1, 1, one_pos, one_pos, by rw [pow_one, hfu]; exact hE1,
      fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
      fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _), ?_⟩
    apply Subtype.ext
    rw [pow_one, nextPerm_apply, hφu, hnext_eq, φE_val]
    exact congrArg (fun x => extPair X P P' x.1) hfu.symm
  · obtain ⟨m, c, hmc, hc, hint, m', b', hb', hm', hint'⟩ := hpass.pass (next hW u.1) hnext_ext hE1
    have hb'' : next hW' (φE X P Y P' hP hE hW u).1 = b' := Subtype.ext (by rw [hφu, hnext_eq, hb'])
    have hfpow : ∀ i, (f ^ (i + 1)) u.1 = (f ^ i) (next hW u.1) := fun i => by
      rw [pow_succ, Perm.mul_apply, hfu]
    refine ⟨m + 1, m' + 1, Nat.succ_pos _, Nat.succ_pos _, by rw [hfpow, hmc]; exact hc, ?_, ?_, ?_⟩
    · intro i hi him
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hfpow]; exact hint i' (by omega)
    · intro i hi him
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [pow_succ, Perm.mul_apply, nextPerm_apply, hb'', nextPerm_pow_apply]; exact hint' i' (by omega)
    · apply Subtype.ext
      rw [pow_succ, Perm.mul_apply, nextPerm_apply, hb'', nextPerm_pow_apply, hm', φE_val]
      exact congrArg (fun x => extPair X P P' x.1) (hmc.symm.trans (hfpow m).symm)

end PassageF

/-! #### J. The cusp-skein smoothing: the reconnected traversal of `A` against the compatible smoothing `C` -/

section CuspColumn

variable (X Y : Word) (j : ℕ) (d : Bool)

local notation "Vc1" => X ++ [Letter.l j d] ++ Y
local notation "Pc1" => [Letter.l j d]

theorem c1_letter : letterAt Vc1 X.length = .l j d := by
  have := letterAt_block X Pc1 Y (i := 0) (by simp)
  simpa using this

theorem c1_length : (X ++ [Letter.l j d] ++ Y).length = X.length + 1 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem c1_extCol (k : ℕ) : ExtCol X Pc1 k ↔ k + 1 ≤ X.length ∨ X.length + 1 ≤ k := by unfold ExtCol; simp

theorem c1_Pne : ([Letter.l j d] : Word) ≠ [] := List.cons_ne_nil _ _

variable (hC : (X ++ [Letter.l j d] ++ Y).Closed)
include hC

theorem c1_j_pos : 1 ≤ j := (l_bits hC (by rw [c1_length]; omega) (c1_letter X Y j d)).1

/-- every `σ` slot of a single-cusp block word is exterior -/
theorem c1_σ_ext {u : Slot Vc1} (hu : IsσSlot u) : ExtPiece X Pc1 Y u := by
  by_contra h
  have hcol : colOf u = X.length := by
    have := colOf_lt hC u
    have h' : ¬ ExtCol X Pc1 (colOf u) := h
    rw [c1_extCol] at h'
    rw [c1_length] at this
    omega
  have := hu.1
  rw [hcol, c1_letter] at this
  exact Bool.noConfusion this

/-- every slot of a single-cusp block word reaches the exterior -/
theorem c1_hexit : ∀ u : Slot Vc1, ∃ n, ExtPiece X Pc1 Y ((next hC)^[n] u) := by
  have hℓ := c1_letter X Y j d
  have hj := c1_j_pos X Y j d hC
  have hk₀ : X.length < (Vc1).length := by rw [c1_length]; omega
  obtain ⟨-, b1, b2⟩ := l_bits hC hk₀ hℓ
  have hv : ∀ u : Slot Vc1, u.1 = (X.length, 0) → ∃ n, ExtPiece X Pc1 Y ((next hC)^[n] u) := by
    intro u hu
    have h1 := next_cusp_l hC hℓ hu
    refine reach_of_next hC (reach_self hC ?_)
    show ExtCol X Pc1 (colOf _)
    rcases Bool.eq_false_or_eq_true d with hd | hd
    · rw [ite_eq_left hd] at h1
      rw [block_col_true h1 (by omega) (by rw [b1, hd]), c1_extCol]; omega
    · rw [ite_eq_right (by simp [hd])] at h1
      rw [block_col_true h1 (by omega) (by rw [b2, hd]; rfl), c1_extCol]; omega
  intro u
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases hext : ExtCol X Pc1 (colOf u)
  · exact reach_self hC hext
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, c1_extCol] at hext
    have : k = X.length := by omega
    subst this
    exact hv u hu
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hC hu hp
  cases hb : bit Vc1 k p
  · rw [block_col_false hu hp hb, c1_extCol] at hext
    have : k = X.length + 1 := by omega
    subst this
    rcases lt_or_ge p j with hpj | hpj
    · obtain ⟨h1, hb1⟩ := pass_l_lt hC hℓ hu hp hb (by simpa [idx] using hpj)
      refine reach_of_next hC (reach_self hC ?_)
      show ExtCol X Pc1 (colOf _)
      have := (cutSlot_facts hC h1 hp).2.2.1
      rw [block_col_false h1 hp hb1, c1_extCol]; omega
    rcases lt_or_ge p (j + 2) with hpj2 | hpj2
    · have h1 := next_arm_l hC hk₀ hℓ hu (by omega) hb
      exact reach_of_next hC (hv _ h1)
    · obtain ⟨h1, hb1⟩ := pass_l_ge hC hℓ hu hp hb (by simpa [idx, coarity] using hpj2)
      simp only [arity, coarity] at h1 hb1
      refine reach_of_next hC (reach_self hC ?_)
      show ExtCol X Pc1 (colOf _)
      have := (cutSlot_facts hC h1 (by omega)).2.2.1
      rw [block_col_false h1 (by omega) hb1, c1_extCol]; omega
  · rw [block_col_true hu hp hb, c1_extCol] at hext
    have : k = X.length := by omega
    subst this
    rcases lt_or_ge p j with hpj | hpj
    · obtain ⟨h1, hb1⟩ := pass_r_lt hC hℓ hu hp hb (by simpa [idx] using hpj)
      refine reach_of_next hC (reach_self hC ?_)
      show ExtCol X Pc1 (colOf _)
      rw [block_col_true h1 hp hb1, c1_extCol]; omega
    · obtain ⟨h1, hb1⟩ := pass_r_ge hC hℓ hu hp hb (by simpa [idx, arity] using hpj)
      simp only [arity, coarity, Nat.sub_zero] at h1 hb1
      refine reach_of_next hC (reach_self hC ?_)
      show ExtCol X Pc1 (colOf _)
      rw [block_col_true h1 (by omega) hb1, c1_extCol]; omega

end CuspColumn

section GPassage

variable {V : Word} (f : Perm (Slot V))

/-- one more step of a block passage for a slot permutation -/
theorem gpassage_step (Ext : ℕ → Prop) {b c : Slot V} (hb : ¬ Ext (colOf b))
    (h : ∃ n, (f ^ n) (f b) = c ∧ ∀ i < n, ¬ Ext (colOf ((f ^ i) (f b)))) :
    ∃ n, (f ^ n) b = c ∧ ∀ i < n, ¬ Ext (colOf ((f ^ i) b)) := by
  obtain ⟨n, hc, hmin⟩ := h
  refine ⟨n + 1, by rw [pow_succ, Perm.mul_apply]; exact hc, ?_⟩
  intro i hi
  cases i with
  | zero => simpa using hb
  | succ i => rw [pow_succ, Perm.mul_apply]; exact hmin i (by omega)

theorem gpassage_end (Ext : ℕ → Prop) {b : Slot V} :
    ∃ n, (f ^ n) b = b ∧ ∀ i < n, ¬ Ext (colOf ((f ^ i) b)) :=
  ⟨0, rfl, fun _ hi => absurd hi (Nat.not_lt_zero _)⟩

end GPassage

section SkeinG

variable (X Y : Word) (m : ℕ) (d a : Bool)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]

variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed)

/-- the reconnected traversal of `A` at its site -/
noncomputable abbrev skG : Perm (Slot Vs) := gPerm hA (siteX X Y m d hA)

theorem skG_siteA : skG X Y m d hA (siteA X Y m d hA) = next hA (siteB X Y m d hA) := by
  unfold skG gPerm
  rw [Perm.mul_apply, siteX_val, Equiv.swap_apply_left, nextPerm_apply, σtwin_siteA]

theorem skG_siteB : skG X Y m d hA (siteB X Y m d hA) = next hA (siteA X Y m d hA) := by
  unfold skG gPerm
  rw [Perm.mul_apply, siteX_val, σtwin_siteA, Equiv.swap_apply_right, nextPerm_apply]

theorem skG_of_not_σ {u : Slot Vs} (h : ¬ IsσSlot u) : skG X Y m d hA u = next hA u :=
  gPerm_apply_of_not_σ hA _ h

theorem skG_of_ext {u : Slot Vs} (h : ExtPiece X Ps Y u) : skG X Y m d hA u = next hA u := by
  refine gPerm_apply_of_ne hA _ (fun e => ?_) (fun e => ?_)
  · rw [siteX_val] at e; exact (siteA_int X Y m d hA).2 (e ▸ h)
  · rw [siteX_val, σtwin_siteA] at e; exact (siteB_int X Y m d hA).2 (e ▸ h)

theorem sk_Pne2 : ([Letter.l (m + 1) d, Letter.σ m] : Word) ≠ [] := List.cons_ne_nil _ _

end SkeinG

section SkeinSmoothPassage

variable (X Y : Word) (m : ℕ) (d a : Bool) (j : ℕ)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Vc" => X ++ [Letter.l j d] ++ Y
local notation "Pc" => [Letter.l j d]

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed) (hC : (X ++ [Letter.l j d] ++ Y).Closed)
variable (hj : (a = !d ∧ j = m) ∨ (a = d ∧ j = m + 1))

include hX hP hm hj in
theorem skc_sameEffect : SameEffect X Ps Pc := by
  unfold SameEffect
  rw [Word.run_append, Word.run_append, hX, Option.bind_some, Option.bind_some, run_skein_A hm hP]
  rcases hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [run_skein_Ctop hm hP]
  · rw [run_skein_Cbottom hm hP]

theorem skc_shift0 : shiftIdx X Ps Pc X.length = X.length := shiftIdx_of_le X Ps Pc le_rfl

theorem skc_shift2 : shiftIdx X Ps Pc (X.length + 2) = X.length + 1 := by
  unfold shiftIdx
  rw [ite_eq_right (by omega)]
  have e1 : ([Letter.l (m + 1) d, Letter.σ m] : Word).length = 2 := rfl
  have e2 : ([Letter.l j d] : Word).length = 1 := rfl
  rw [e1, e2]; omega

theorem skc_extPair0 (p : ℕ) : extPair X Ps Pc (X.length, p) = (X.length, p) := by
  simp only [extPair, skc_shift0]

theorem skc_extPair2 (p : ℕ) : extPair X Ps Pc (X.length + 2, p) = (X.length + 1, p) := by
  simp only [extPair, skc_shift2]

include hX hP hm hj in
/-- the bits of the cut after the smoothing's cusp are those after `A`'s block -/
theorem skc_bits (p : ℕ) : bit Vc (X.length + 1) p = bit Vs (X.length + 2) p := by
  have hE := skc_sameEffect X m d a j hX hP hm hj
  have := bit_ext X Ps Y Pc (sk_Pne2 m d) hE (k := X.length + 2) (Or.inr (by simp)) p
  rw [skc_shift2] at this
  exact this.symm

include hX hP hm hj in
theorem skc_bits0 (p : ℕ) : bit Vc X.length p = bit Vs X.length p := by
  have hE := skc_sameEffect X m d a j hX hP hm hj
  have := bit_ext X Ps Y Pc (sk_Pne2 m d) hE (k := X.length) (Or.inl le_rfl) p
  rw [skc_shift0] at this
  exact this.symm

include hX hP hm hj hA hC in
/-- THE BLOCK PASSAGE OF THE RECONNECTED TRAVERSAL of `A` against the compatible smoothing `C`. -/
theorem skc_passageF : PassageF X Ps Y Pc hC (skG X Y m d hA) := by
  have hE := skc_sameEffect X m d a j hX hP hm hj
  have hPne := sk_Pne2 m d
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have hℓC := c1_letter X Y j d
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk_bits X Y m d a hA ha
  have cb1 : bit Vc (X.length + 1) m = d := by rw [skc_bits X Y m d a j hX hP hm hj, e1]
  have cb2 : bit Vc (X.length + 1) (m + 1) = a := by rw [skc_bits X Y m d a j hX hP hm hj, e2]
  have cb3 : bit Vc (X.length + 1) (m + 2) = !d := by rw [skc_bits X Y m d a j hX hP hm hj, e3]
  have hbx := skc_bits0 X Y m d a j hX hP hm hj
  have hsA := siteA_val X Y m d a hA ha
  have hsB := siteB_val X Y m d hA
  have hjm : j = m ∨ j = m + 1 := by rcases hj with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hk₀C : X.length < (Vc).length := by rw [c1_length]; omega
  have hk₀ : X.length < (Vs).length := by rw [sk_length]; omega
  constructor
  intro b hext hcol
  let b' : Slot Vc := ⟨extPair X Ps Pc b.1, isSlot_ext X Ps Y Pc hPne hE b.2 hext⟩
  have hb'v : b'.1 = extPair X Ps Pc b.1 := rfl
  rcases (entry_iff X Ps Y hPne hA b).1 ⟨hext, hcol⟩ with ⟨p, hb, hp, hbit⟩ | ⟨p, hb, hp, hbit⟩
  · -- from the left at `(|X|, p)`
    have hb' : b'.1 = (X.length, p) := by rw [hb'v, hb, skc_extPair0]
    have hbit' : bit Vc X.length p = true := by rw [hbx]; exact hbit
    have nσb : ¬ IsσSlot b := not_σ_right hb hp hbit (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
    have g0 : (skG X Y m d hA b).1 = (next hA b).1 := by rw [skG_of_not_σ X Y m d hA nσb]
    have nb0 : ¬ ExtCol X Ps (colOf b) := by rw [block_col_true hb hp hbit, sk_extCol]; omega
    have nb0' : ¬ ExtCol X Pc (colOf b') := by rw [block_col_true hb' hp hbit', c1_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · -- above the site
      obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₀ hb hp hbit (by simp [idx]; omega)
      rw [← g0] at h1
      have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_right h1 hp hb1 (fun _ hj' => by
        rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h2, hb2⟩ := pass_r_lt hA hℓ₁ h1 hp hb1 (by simpa [idx] using hpm)
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      obtain ⟨h1', hb1'⟩ := pass_r_lt hC hℓC hb' hp hbit' (by simp [idx]; omega)
      obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps) nb0
        (gpassage_step _ _ (by rw [block_col_true h1 hp hb1, sk_extCol]; omega) (gpassage_end _ _))
      obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
      refine ⟨n, _, hc, by rw [block_col_true h2 hp hb2, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, skc_extPair2]
    rcases Nat.eq_or_lt_of_le hpm with hpe | hpm1
    · -- `p = m`: the through-strand enters the site
      rw [← hpe] at hb hb' hbit hbit'
      have hat : a = true := ha.symm.trans hbit
      have hp0 : m ≠ 0 := by omega
      obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₀ hb hp0 hbit (by simp [idx])
      rw [← g0] at h1
      have hs1 : skG X Y m d hA b = siteA X Y m d hA := Subtype.ext (by rw [h1, hsA, ite_eq_left hat])
      rcases Bool.eq_false_or_eq_true d with hdt | hdf
      · -- `d = true`: `C = X l_{m+1} Y`, the arm exits at `(|X|+2, m)`
        have hjb : j = m + 1 := by
          rcases hj with ⟨h, -⟩ | ⟨-, h⟩
          · rw [hat, hdt] at h; cases h
          · exact h
        have hsB' : (siteB X Y m d hA).1 = (X.length + 1, m + 1) := by rw [hsB, ite_eq_left hdt]
        have hb2 : bit Vs (X.length + 1) (m + 1) = true := by rw [c2, hdt]
        have h2 := next_σ_right_succ hA hℓ₁ hsB' hb2
        have g2 : (skG X Y m d hA (skG X Y m d hA b)).1 = (X.length + 2, m) := by rw [hs1, skG_siteA, h2]
        have hb2e : bit Vs (X.length + 2) m = true := by rw [e1, hdt]
        obtain ⟨h1', hb1'⟩ := pass_r_lt hC hℓC hb' hp0 hbit' (by simp [idx]; omega)
        obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps) nb0
          (gpassage_step _ _ (by rw [block_col_true h1 hp0 hb1, sk_extCol]; omega) (gpassage_end _ _))
        obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
        refine ⟨n, _, hc, by rw [block_col_true g2 hp0 hb2e, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc', h1', g2, skc_extPair2]
      · -- `d = false`: `C = X l_m Y`, the reconnected strand runs through the cusp, exits at `(|X|+2, m+2)`
        have hjt : j = m := by
          rcases hj with ⟨-, h⟩ | ⟨h, -⟩
          · exact h
          · rw [hat, hdf] at h; cases h
        have hsB' : (siteB X Y m d hA).1 = (X.length + 2, m) := by rw [hsB, ite_eq_right (by simp [hdf])]
        have hb2 : bit Vs (X.length + 2) m = false := by rw [e1, hdf]
        have h2 := next_σ_left_idx hA hℓ₁ hsB' hb2
        have g2 : (skG X Y m d hA (skG X Y m d hA b)).1 = (X.length + 1, m + 1) := by rw [hs1, skG_siteA, h2]
        have hb3 : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, hdf]
        have nσ2 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA b)) :=
          not_σ_left g2 (by omega) hb3 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        have h3 := next_arm_l hA hk₀ hℓ₀ g2 (Or.inl rfl) hb3
        rw [← skG_of_not_σ X Y m d hA nσ2] at h3
        have nσ3 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b))) := not_σ_vertex h3
        have h4 := next_cusp_l hA hℓ₀ h3
        rw [ite_eq_right (by simp [hdf]), ← skG_of_not_σ X Y m d hA nσ3] at h4
        have hb4 : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hdf]; rfl
        have nσ4 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)))) :=
          not_σ_right h4 (by omega) hb4 (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
        obtain ⟨h5, hb5⟩ := pass_r_ge hA hℓ₁ h4 (by omega) hb4 (by simp [idx, arity])
        simp only [arity, coarity, Nat.add_sub_cancel] at h5 hb5
        rw [← skG_of_not_σ X Y m d hA nσ4] at h5
        obtain ⟨h1', hb1'⟩ := pass_r_ge hC hℓC hb' hp0 hbit' (by simp [idx, arity]; omega)
        simp only [arity, coarity, Nat.sub_zero] at h1' hb1'
        obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps) nb0
          (gpassage_step _ _ (by rw [block_col_true h1 hp0 hb1, sk_extCol]; omega)
          (gpassage_step _ _ (by rw [block_col_false g2 (by omega) hb3, sk_extCol]; omega)
          (gpassage_step _ _ (by rw [block_col_vertex h3, sk_extCol]; omega)
          (gpassage_step _ _ (by rw [block_col_true h4 (by omega) hb4, sk_extCol]; omega) (gpassage_end _ _)))))
        obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
        refine ⟨n, _, hc, by rw [block_col_true h5 (by omega) hb5, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
        rw [hc', h1', h5, skc_extPair2]
    · -- below the site
      obtain ⟨h1, hb1⟩ := pass_r_ge hA hℓ₀ hb hp hbit (by simp [idx, arity]; omega)
      simp only [arity, coarity, Nat.sub_zero] at h1 hb1
      rw [← g0] at h1
      have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_right h1 (by omega) hb1 (fun _ hj' => by
        rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h2, hb2⟩ := pass_r_ge hA hℓ₁ h1 (by omega) hb1 (by simp [idx, arity]; omega)
      simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      obtain ⟨h1', hb1'⟩ := pass_r_ge hC hℓC hb' hp hbit' (by simp [idx, arity]; omega)
      simp only [arity, coarity, Nat.sub_zero] at h1' hb1'
      obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps) nb0
        (gpassage_step _ _ (by rw [block_col_true h1 (by omega) hb1, sk_extCol]; omega) (gpassage_end _ _))
      obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
      refine ⟨n, _, hc, by rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
      rw [hc', h1', h2, skc_extPair2]
  · -- from the right at `(|X|+2, p)`
    replace hb : b.1 = (X.length + 2, p) := hb
    replace hbit : bit Vs (X.length + 2) p = false := hbit
    have hb' : b'.1 = (X.length + 1, p) := by rw [hb'v, hb, skc_extPair2]
    have hbit' : bit Vc (X.length + 1) p = false := by rw [skc_bits X Y m d a j hX hP hm hj]; exact hbit
    have nb0' : ¬ ExtCol X Pc (colOf b') := by rw [block_col_false hb' hp hbit', c1_extCol]; omega
    rcases lt_or_ge p m with hpm | hpm
    · -- above the site
      have nσb : ¬ IsσSlot b := not_σ_left hb hp hbit (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h1, hb1⟩ := pass_l_lt hA hℓ₁ hb hp hbit (by simpa [idx] using hpm)
      rw [← skG_of_not_σ X Y m d hA nσb] at h1
      have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left h1 hp hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
      obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ h1 hp hb1 (by simp [idx]; omega)
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      obtain ⟨h1', hb1'⟩ := pass_l_lt hC hℓC hb' hp hbit' (by simp [idx]; omega)
      obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
        (by rw [block_col_false hb hp hbit, sk_extCol]; omega)
        (gpassage_step _ _ (by rw [block_col_false h1 hp hb1, sk_extCol]; omega) (gpassage_end _ _))
      obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
      refine ⟨n, _, hc, ?_, hmin, n', b', rfl, ?_, hmin'⟩
      · have := (cutSlot_facts hA h2 hp).2.2.1
        rw [block_col_false h2 hp hb2, sk_extCol]; omega
      · rw [hc', h1', h2, skc_extPair0]
    rcases lt_or_ge p (m + 3) with hpm3 | hpm3
    · have hp3 : p = m ∨ p = m + 1 ∨ p = m + 2 := by omega
      rcases hp3 with hpe | hpe | hpe
      · -- `p = m`: the upper arm heading left is the arm slot; the reconnection follows the through-strand
        rw [hpe] at hb hb' hbit hbit'
        have hdf : d = false := e1.symm.trans hbit
        have hs0 : b = siteB X Y m d hA := Subtype.ext (by rw [hb, hsB, ite_eq_right (by simp [hdf])])
        rcases Bool.eq_false_or_eq_true a with hat | haf
        · -- `a = true`, `C = X l_m Y`: out at `(|X|+2, m+1)`
          have hjt : j = m := by
            rcases hj with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · rw [hat, hdf] at h; cases h
          have hsA' : (siteA X Y m d hA).1 = (X.length + 1, m) := by rw [hsA, ite_eq_left hat]
          have hb1 : bit Vs (X.length + 1) m = true := by rw [c1, hat]
          have h1 := next_σ_right_idx hA hℓ₁ hsA' hb1
          have g1 : (skG X Y m d hA b).1 = (X.length + 2, m + 1) := by rw [hs0, skG_siteB, h1]
          have hb1e : bit Vs (X.length + 2) (m + 1) = true := by rw [e2, hat]
          -- `C`: through the cusp
          have h1' := next_arm_l hC hk₀C hℓC hb' (by omega) hbit'
          have h2' := next_cusp_l hC hℓC h1'
          rw [ite_eq_right (by simp [hdf])] at h2'
          have hb2' : bit Vc (X.length + 1) (j + 1) = true := by
            have h := cb2; rw [← hjt] at h; rw [h, hat]
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega) (gpassage_end _ _)
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0'
            (passage_step hC _ (by rw [block_col_vertex h1', c1_extCol]; omega) (passage_end hC))
          refine ⟨n, _, hc, by rw [block_col_true g1 (by omega) hb1e, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
          rw [hc', h2', g1, skc_extPair2, hjt]
        · -- `a = false`, `C = X l_{m+1} Y`: out at `(|X|, m)`
          have hjb : j = m + 1 := by
            rcases hj with ⟨h, -⟩ | ⟨-, h⟩
            · rw [haf, hdf] at h; cases h
            · exact h
          have hsA' : (siteA X Y m d hA).1 = (X.length + 2, m + 1) := by rw [hsA, ite_eq_right (by simp [haf])]
          have hb1 : bit Vs (X.length + 2) (m + 1) = false := by rw [e2, haf]
          have h1 := next_σ_left_succ hA hℓ₁ hsA' hb1
          have g1 : (skG X Y m d hA b).1 = (X.length + 1, m) := by rw [hs0, skG_siteB, h1]
          have hb1e : bit Vs (X.length + 1) m = false := by rw [c1, haf]
          have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left g1 (by omega) hb1e (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
          obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ g1 (by omega) hb1e (by simp [idx])
          rw [← skG_of_not_σ X Y m d hA nσ1] at h2
          obtain ⟨h1', hb1'⟩ := pass_l_lt hC hℓC hb' (by omega) hbit' (by simp [idx]; omega)
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_false g1 (by omega) hb1e, sk_extCol]; omega) (gpassage_end _ _))
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
          refine ⟨n, _, hc, ?_, hmin, n', b', rfl, ?_, hmin'⟩
          · have := (cutSlot_facts hA h2 (by omega)).2.2.1
            rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
          · rw [hc', h1', h2, skc_extPair0]
      · -- `p = m + 1`: the through-strand heading left is the site slot
        rw [hpe] at hb hb' hbit hbit'
        have haf : a = false := e2.symm.trans hbit
        have hs0 : b = siteA X Y m d hA := Subtype.ext (by rw [hb, hsA, ite_eq_right (by simp [haf])])
        rcases Bool.eq_false_or_eq_true d with hdt | hdf
        · -- `d = true`, `C = X l_m Y`: out at `(|X|+2, m)`
          have hjt : j = m := by
            rcases hj with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · rw [haf, hdt] at h; cases h
          have hsB' : (siteB X Y m d hA).1 = (X.length + 1, m + 1) := by rw [hsB, ite_eq_left hdt]
          have hb1 : bit Vs (X.length + 1) (m + 1) = true := by rw [c2, hdt]
          have h1 := next_σ_right_succ hA hℓ₁ hsB' hb1
          have g1 : (skG X Y m d hA b).1 = (X.length + 2, m) := by rw [hs0, skG_siteA, h1]
          have hb1e : bit Vs (X.length + 2) m = true := by rw [e1, hdt]
          have h1' := next_arm_l hC hk₀C hℓC hb' (by omega) hbit'
          have h2' := next_cusp_l hC hℓC h1'
          rw [ite_eq_left hdt] at h2'
          have hb2' : bit Vc (X.length + 1) j = true := by
            have h := cb1; rw [← hjt] at h; rw [h, hdt]
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega) (gpassage_end _ _)
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0'
            (passage_step hC _ (by rw [block_col_vertex h1', c1_extCol]; omega) (passage_end hC))
          refine ⟨n, _, hc, by rw [block_col_true g1 (by omega) hb1e, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
          rw [hc', h2', g1, skc_extPair2, hjt]
        · -- `d = false`, `C = X l_{m+1} Y`: through the cusp, out at `(|X|+2, m+2)`
          have hjb : j = m + 1 := by
            rcases hj with ⟨h, -⟩ | ⟨-, h⟩
            · rw [haf, hdf] at h; cases h
            · exact h
          have hsB' : (siteB X Y m d hA).1 = (X.length + 2, m) := by rw [hsB, ite_eq_right (by simp [hdf])]
          have hb1 : bit Vs (X.length + 2) m = false := by rw [e1, hdf]
          have h1 := next_σ_left_idx hA hℓ₁ hsB' hb1
          have g1 : (skG X Y m d hA b).1 = (X.length + 1, m + 1) := by rw [hs0, skG_siteA, h1]
          have hb1e : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, hdf]
          have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left g1 (by omega) hb1e (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
          have h2 := next_arm_l hA hk₀ hℓ₀ g1 (Or.inl rfl) hb1e
          rw [← skG_of_not_σ X Y m d hA nσ1] at h2
          have nσ2 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA b)) := not_σ_vertex h2
          have h3 := next_cusp_l hA hℓ₀ h2
          rw [ite_eq_right (by simp [hdf]), ← skG_of_not_σ X Y m d hA nσ2] at h3
          have hb3 : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hdf]; rfl
          have nσ3 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b))) :=
            not_σ_right h3 (by omega) hb3 (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
          obtain ⟨h4, hb4⟩ := pass_r_ge hA hℓ₁ h3 (by omega) hb3 (by simp [idx, arity])
          simp only [arity, coarity, Nat.add_sub_cancel] at h4 hb4
          rw [← skG_of_not_σ X Y m d hA nσ3] at h4
          have h1' := next_arm_l hC hk₀C hℓC hb' (by omega) hbit'
          have h2' := next_cusp_l hC hℓC h1'
          rw [ite_eq_right (by simp [hdf])] at h2'
          have hb2' : bit Vc (X.length + 1) (j + 1) = true := by
            have h := cb3; rw [show m + 2 = j + 1 by omega] at h; rw [h, hdf]; rfl
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_false g1 (by omega) hb1e, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_vertex h2, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_true h3 (by omega) hb3, sk_extCol]; omega) (gpassage_end _ _))))
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0'
            (passage_step hC _ (by rw [block_col_vertex h1', c1_extCol]; omega) (passage_end hC))
          refine ⟨n, _, hc, by rw [block_col_true h4 (by omega) hb4, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
          rw [hc', h2', h4, skc_extPair2, hjb]
      · -- `p = m + 2`: the lower arm heading left, through the cusp to the arm slot, then the reconnection
        rw [hpe] at hb hb' hbit hbit'
        have hdt : d = true := by have := e3.symm.trans hbit; cases d <;> simp_all
        have nσb : ¬ IsσSlot b := not_σ_left hb (by omega) hbit (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
        obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₁ hb (by omega) hbit (by simp [idx, coarity])
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        rw [← skG_of_not_σ X Y m d hA nσb] at h1
        have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left h1 (by omega) hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        have h2 := next_arm_l hA hk₀ hℓ₀ h1 (Or.inr rfl) hb1
        rw [← skG_of_not_σ X Y m d hA nσ1] at h2
        have nσ2 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA b)) := not_σ_vertex h2
        have h3 := next_cusp_l hA hℓ₀ h2
        rw [ite_eq_left hdt, ← skG_of_not_σ X Y m d hA nσ2] at h3
        have hs3 : skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)) = siteB X Y m d hA :=
          Subtype.ext (by rw [h3, hsB, ite_eq_left hdt])
        rcases Bool.eq_false_or_eq_true a with hat | haf
        · -- `a = true`, `C = X l_{m+1} Y`: through the cusp to the arm at `(|X|+1, j)`, out at `(|X|+2, m+1)`
          have hjb : j = m + 1 := by
            rcases hj with ⟨h, -⟩ | ⟨-, h⟩
            · rw [hat, hdt] at h; cases h
            · exact h
          have hsA' : (siteA X Y m d hA).1 = (X.length + 1, m) := by rw [hsA, ite_eq_left hat]
          have hb4 : bit Vs (X.length + 1) m = true := by rw [c1, hat]
          have h4 := next_σ_right_idx hA hℓ₁ hsA' hb4
          have g4 : (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)))).1 = (X.length + 2, m + 1) := by
            rw [hs3, skG_siteB, h4]
          have hb4e : bit Vs (X.length + 2) (m + 1) = true := by rw [e2, hat]
          have h1' := next_arm_l hC hk₀C hℓC hb' (by omega) hbit'
          have h2' := next_cusp_l hC hℓC h1'
          rw [ite_eq_left hdt] at h2'
          have hb2' : bit Vc (X.length + 1) j = true := by
            have h := cb2; rw [← hjb] at h; rw [h, hat]
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_false h1 (by omega) hb1, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_vertex h2, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [hs3]; exact (siteB_int X Y m d hA).2) (gpassage_end _ _))))
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0'
            (passage_step hC _ (by rw [block_col_vertex h1', c1_extCol]; omega) (passage_end hC))
          refine ⟨n, _, hc, by rw [block_col_true g4 (by omega) hb4e, sk_extCol]; omega, hmin, n', b', rfl, ?_, hmin'⟩
          rw [hc', h2', g4, skc_extPair2, hjb]
        · -- `a = false`, `C = X l_m Y`: out at `(|X|, m)`
          have hjt : j = m := by
            rcases hj with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · rw [haf, hdt] at h; cases h
          have hsA' : (siteA X Y m d hA).1 = (X.length + 2, m + 1) := by rw [hsA, ite_eq_right (by simp [haf])]
          have hb4 : bit Vs (X.length + 2) (m + 1) = false := by rw [e2, haf]
          have h4 := next_σ_left_succ hA hℓ₁ hsA' hb4
          have g4 : (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)))).1 = (X.length + 1, m) := by
            rw [hs3, skG_siteB, h4]
          have hb4e : bit Vs (X.length + 1) m = false := by rw [c1, haf]
          have nσ4 : ¬ IsσSlot (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA (skG X Y m d hA b)))) :=
            not_σ_left g4 (by omega) hb4e (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
          obtain ⟨h5, hb5⟩ := pass_l_lt hA hℓ₀ g4 (by omega) hb4e (by simp [idx])
          rw [← skG_of_not_σ X Y m d hA nσ4] at h5
          -- `C`: the arm strand passes below the cusp straight to `(|X|, m)`
          obtain ⟨h1c, hb1c⟩ := pass_l_ge hC hℓC hb' (by omega) hbit' (by simp [idx, coarity]; omega)
          simp only [arity, coarity] at h1c hb1c
          obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
            (by rw [block_col_false hb (by omega) hbit, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_false h1 (by omega) hb1, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [block_col_vertex h2, sk_extCol]; omega)
            (gpassage_step _ _ (by rw [hs3]; exact (siteB_int X Y m d hA).2)
            (gpassage_step _ _ (by rw [block_col_false g4 (by omega) hb4e, sk_extCol]; omega) (gpassage_end _ _)))))
          obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
          refine ⟨n, _, hc, ?_, hmin, n', b', rfl, ?_, hmin'⟩
          · have := (cutSlot_facts hA h5 (by omega)).2.2.1
            rw [block_col_false h5 (by omega) hb5, sk_extCol]; omega
          · rw [hc', h1c, h5, skc_extPair0]
            simp only [Prod.mk.injEq, true_and]; omega
    · -- below the site
      have nσb : ¬ IsσSlot b := not_σ_left hb hp hbit (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₁ hb hp hbit (by simp [idx, coarity]; omega)
      simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
      rw [← skG_of_not_σ X Y m d hA nσb] at h1
      have nσ1 : ¬ IsσSlot (skG X Y m d hA b) := not_σ_left h1 hp hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
      obtain ⟨h2, hb2⟩ := pass_l_ge hA hℓ₀ h1 hp hb1 (by simp [idx, coarity]; omega)
      simp only [arity, coarity] at h2 hb2
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      obtain ⟨h1', hb1'⟩ := pass_l_ge hC hℓC hb' hp hbit' (by simp [idx, coarity]; omega)
      simp only [arity, coarity] at h1' hb1'
      obtain ⟨n, hc, hmin⟩ := gpassage_step (skG X Y m d hA) (ExtCol X Ps)
        (by rw [block_col_false hb hp hbit, sk_extCol]; omega)
        (gpassage_step _ _ (by rw [block_col_false h1 hp hb1, sk_extCol]; omega) (gpassage_end _ _))
      obtain ⟨n', hc', hmin'⟩ := passage_step hC (ExtCol X Pc) nb0' (passage_end hC)
      refine ⟨n, _, hc, ?_, hmin, n', b', rfl, ?_, hmin'⟩
      · have := (cutSlot_facts hA h2 (by omega)).2.2.1
        rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
      · rw [hc', h1', h2, skc_extPair0]

end SkeinSmoothPassage

section SkeinSmoothIso

variable (X Y : Word) (m : ℕ) (d a : Bool) (j : ℕ)

local notation "Vs" => X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y
local notation "Ps" => [Letter.l (m + 1) d, Letter.σ m]
local notation "Vc" => X ++ [Letter.l j d] ++ Y
local notation "Pc" => [Letter.l j d]

variable {P L : Cuts} (hX : Word.run X [] = some (P ++ a :: L)) (hP : P.length = m - 1) (hm : 1 ≤ m)
variable (hA : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y).Closed) (hC : (X ++ [Letter.l j d] ++ Y).Closed)
variable (hj : (a = !d ∧ j = m) ∨ (a = d ∧ j = m + 1))

theorem greach_step {V : Word} {f : Perm (Slot V)} {E : Slot V → Prop} {u : Slot V} (h : ∃ n, E ((f ^ n) (f u))) :
    ∃ n, E ((f ^ n) u) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [pow_succ, Perm.mul_apply]; exact hn⟩

theorem greach_self {V : Word} {f : Perm (Slot V)} {E : Slot V → Prop} {u : Slot V} (h : E u) : ∃ n, E ((f ^ n) u) :=
  ⟨0, h⟩

include hX hP hm hA hC hj in
/-- every slot of `A` reaches the exterior under the reconnected traversal -/
theorem sk_ghexit : ∀ u : Slot Vs, ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) u) := by
  have hpass := skc_passageF X Y m d a j hX hP hm hA hC hj
  obtain ⟨hℓ₀, hℓ₁⟩ := sk_letters X Y m d
  have ha := (sk_bit_a X Y m d a hX hP).1
  obtain ⟨c1, c2, c3, e1, e2, e3⟩ := sk_bits X Y m d a hA ha
  have hsA := siteA_val X Y m d a hA ha
  have hsB := siteB_val X Y m d hA
  have hk₀ : X.length < (Vs).length := by rw [sk_length]; omega
  have hPne := sk_Pne2 m d
  -- from the successor of the through-strand slot
  have R2 : ∀ u : Slot Vs, u = next hA (siteA X Y m d hA) → ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) u) := by
    intro u hu
    rcases Bool.eq_false_or_eq_true a with hat | haf
    · have hs : (siteA X Y m d hA).1 = (X.length + 1, m) := by rw [hsA, ite_eq_left hat]
      have h1 := next_σ_right_idx hA hℓ₁ hs (by rw [c1, hat])
      rw [← hu] at h1
      refine greach_self ?_
      show ExtCol X Ps (colOf _)
      rw [block_col_true h1 (by omega) (by rw [e2, hat]), sk_extCol]; omega
    · have hs : (siteA X Y m d hA).1 = (X.length + 2, m + 1) := by rw [hsA, ite_eq_right (by simp [haf])]
      have h1 := next_σ_left_succ hA hℓ₁ hs (by rw [e2, haf])
      rw [← hu] at h1
      have hb1 : bit Vs (X.length + 1) m = false := by rw [c1, haf]
      have nσ1 : ¬ IsσSlot u := not_σ_left h1 (by omega) hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
      obtain ⟨h2, hb2⟩ := pass_l_lt hA hℓ₀ h1 (by omega) hb1 (by simp [idx])
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      refine greach_step (greach_self ?_)
      show ExtCol X Ps (colOf _)
      have := (cutSlot_facts hA h2 (by omega)).2.2.1
      rw [block_col_false h2 (by omega) hb2, sk_extCol]; omega
  have RsiteB : ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) (siteB X Y m d hA)) :=
    greach_step (R2 _ (skG_siteB X Y m d hA))
  -- from the left-cusp vertex
  have Rv : ∀ u : Slot Vs, u.1 = (X.length, 0) → ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) u) := by
    intro u hu
    have h1 := next_cusp_l hA hℓ₀ hu
    rw [← skG_of_not_σ X Y m d hA (not_σ_vertex hu)] at h1
    rcases Bool.eq_false_or_eq_true d with hdt | hdf
    · rw [ite_eq_left hdt] at h1
      have hs : skG X Y m d hA u = siteB X Y m d hA := Subtype.ext (by rw [h1, hsB, ite_eq_left hdt])
      exact greach_step (by rw [hs]; exact RsiteB)
    · rw [ite_eq_right (by simp [hdf])] at h1
      have hb1 : bit Vs (X.length + 1) (m + 1 + 1) = true := by rw [c3, hdf]; rfl
      have nσ1 : ¬ IsσSlot (skG X Y m d hA u) :=
        not_σ_right h1 (by omega) hb1 (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
      obtain ⟨h2, hb2⟩ := pass_r_ge hA hℓ₁ h1 (by omega) hb1 (by simp [idx, arity])
      simp only [arity, coarity, Nat.add_sub_cancel] at h2 hb2
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      refine greach_step (greach_step (greach_self ?_))
      show ExtCol X Ps (colOf _)
      rw [block_col_true h2 (by omega) hb2, sk_extCol]; omega
  -- from the successor of the arm slot
  have R1 : ∀ u : Slot Vs, u = next hA (siteB X Y m d hA) → ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) u) := by
    intro u hu
    rcases Bool.eq_false_or_eq_true d with hdt | hdf
    · have hs : (siteB X Y m d hA).1 = (X.length + 1, m + 1) := by rw [hsB, ite_eq_left hdt]
      have h1 := next_σ_right_succ hA hℓ₁ hs (by rw [c2, hdt])
      rw [← hu] at h1
      refine greach_self ?_
      show ExtCol X Ps (colOf _)
      rw [block_col_true h1 (by omega) (by rw [e1, hdt]), sk_extCol]; omega
    · have hs : (siteB X Y m d hA).1 = (X.length + 2, m) := by rw [hsB, ite_eq_right (by simp [hdf])]
      have h1 := next_σ_left_idx hA hℓ₁ hs (by rw [e1, hdf])
      rw [← hu] at h1
      have hb1 : bit Vs (X.length + 1) (m + 1) = false := by rw [c2, hdf]
      have nσ1 : ¬ IsσSlot u := not_σ_left h1 (by omega) hb1 (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
      have h2 := next_arm_l hA hk₀ hℓ₀ h1 (Or.inl rfl) hb1
      rw [← skG_of_not_σ X Y m d hA nσ1] at h2
      exact greach_step (Rv _ h2)
  have RsiteA : ∃ n, ExtPiece X Ps Y (((skG X Y m d hA) ^ n) (siteA X Y m d hA)) :=
    greach_step (R1 _ (skG_siteA X Y m d hA))
  intro u
  by_cases hext : ExtCol X Ps (colOf u)
  · exact greach_self hext
  -- the entries
  by_cases hentry : IsExtSlot X Ps u.1
  · obtain ⟨n, c, hmc, hc, -, -⟩ := hpass.pass u hentry hext
    exact ⟨n, by rw [hmc]; exact hc⟩
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu, sk_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · exact Rv u hu
    · exfalso; have := vertex_not_crossing hu; rw [hℓ₁] at this; exact Bool.noConfusion this
  have hp : p ≠ 0 := by omega
  obtain ⟨-, -, hk0, hk⟩ := cutSlot_facts hA hu hp
  cases hb : bit Vs k p
  · rw [block_col_false hu hp hb, sk_extCol] at hext
    have : k = X.length + 1 ∨ k = X.length + 2 := by omega
    rcases this with rfl | rfl
    · rcases lt_or_ge p (m + 1) with hpm | hpm
      · have nσ : ¬ IsσSlot u := not_σ_left hu hp hb (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        obtain ⟨h1, hb1⟩ := pass_l_lt hA hℓ₀ hu hp hb (by simpa [idx] using hpm)
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        refine greach_step (greach_self ?_)
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h1 hp).2.2.1
        rw [block_col_false h1 hp hb1, sk_extCol]; omega
      rcases lt_or_ge p (m + 3) with hpm3 | hpm3
      · have nσ : ¬ IsσSlot u := not_σ_left hu hp hb (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        have h1 := next_arm_l hA hk₀ hℓ₀ hu (by omega) hb
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        exact greach_step (Rv _ h1)
      · have nσ : ¬ IsσSlot u := not_σ_left hu hp hb (fun _ hj' => by rw [hℓ₀] at hj'; cases hj')
        obtain ⟨h1, hb1⟩ := pass_l_ge hA hℓ₀ hu hp hb (by simpa [idx, coarity] using hpm3)
        simp only [arity, coarity] at h1 hb1
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        refine greach_step (greach_self ?_)
        show ExtCol X Ps (colOf _)
        have := (cutSlot_facts hA h1 (by omega)).2.2.1
        rw [block_col_false h1 (by omega) hb1, sk_extCol]; omega
    · -- a right entry
      exfalso; apply hentry
      unfold IsExtSlot; rw [hu]; simp only
      rw [ite_eq_right hp]; right; simp
  · rw [block_col_true hu hp hb, sk_extCol] at hext
    have : k = X.length ∨ k = X.length + 1 := by omega
    rcases this with rfl | rfl
    · -- a left entry
      exfalso; apply hentry
      unfold IsExtSlot; rw [hu]; simp only
      rw [ite_eq_right hp]; left; exact le_rfl
    · rcases lt_or_ge p m with hpm | hpm
      · have nσ : ¬ IsσSlot u := not_σ_right hu hp hb (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
        obtain ⟨h1, hb1⟩ := pass_r_lt hA hℓ₁ hu hp hb (by simpa [idx] using hpm)
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        refine greach_step (greach_self ?_)
        show ExtCol X Ps (colOf _)
        rw [block_col_true h1 hp hb1, sk_extCol]; omega
      rcases lt_or_ge p (m + 2) with hpm2 | hpm2
      · rcases Nat.eq_or_lt_of_le hpm with hpe | hpe
        · -- the through-strand slot
          have hat : a = true := by rw [← hpe] at hb; exact c1.symm.trans hb
          have hs : u = siteA X Y m d hA := Subtype.ext (by rw [hu, hsA, ite_eq_left hat, hpe])
          rw [hs]; exact RsiteA
        · have hpe' : p = m + 1 := by omega
          have hdt : d = true := by rw [hpe'] at hb; exact c2.symm.trans hb
          have hs : u = siteB X Y m d hA := Subtype.ext (by rw [hu, hsB, ite_eq_left hdt, hpe'])
          rw [hs]; exact RsiteB
      · have nσ : ¬ IsσSlot u := not_σ_right hu hp hb (fun _ hj' => by rw [hℓ₁] at hj'; injection hj' with hj'; omega)
        obtain ⟨h1, hb1⟩ := pass_r_ge hA hℓ₁ hu hp hb (by simpa [idx, arity] using hpm2)
        simp only [arity, coarity, Nat.add_sub_cancel] at h1 hb1
        rw [← skG_of_not_σ X Y m d hA nσ] at h1
        refine greach_step (greach_self ?_)
        show ExtCol X Ps (colOf _)
        rw [block_col_true h1 hp hb1, sk_extCol]; omega

include hX hP hm hj in
/-- THE SMOOTHING HALF of the cusp-skein site: the σ-slot record of `A` smoothed at the site is the σ-slot
record of the compatible smoothing `C`. -/
theorem sk_smoothIso :
    Nonempty (RecordIso ((slotRecord hA IsσSlot (allActive hA)).smooth (siteX X Y m d hA))
      (slotRecord hC IsσSlot (allActive hC))) := by
  have hE := skc_sameEffect X m d a j hX hP hm hj
  have hPne := sk_Pne2 m d
  refine ⟨smoothRecordIso hA hC (ExtPiece X Ps Y) (ExtPiece X Pc Y) (φE X Ps Y Pc hPne hE hA) (siteX X Y m d hA)
    ?_ ?_ ?_ (fun _ hu => c1_σ_ext X Y j d hC hu)
    (conj_of_passageF X Ps Y Pc hPne hE hA hC (skG X Y m d hA) (fun _ hu => skG_of_ext X Y m d hA hu)
      (skc_passageF X Y m d a j hX hP hm hA hC hj))
    (sk_ghexit X Y m d a j hX hP hm hA hC hj) ?_
    (isσSlot_φE_iff X Ps Y Pc hPne hE hA) (fun _ hE' hσ => extPiece_σtwin X Ps Y hA hσ hE')
    (fun u hu => φE_σtwin X Ps Y Pc hPne hE hA hC u hu) (fun u _ => isDesc_φE X Ps Y Pc hPne hE hA u)
    (fun u _ => σsgn_φE X Ps Y Pc hPne hE hA u)⟩
  · intro u hu h1 h2
    by_contra hext
    have hint : IntSlot X Ps Y u := ⟨hu, hext⟩
    rcases (sk_int_iff X Y m d hA u).1 hint with h | h
    · exact h1 (by rw [h, siteX_val])
    · exact h2 (by rw [h, siteX_val, σtwin_siteA])
  · rw [siteX_val]; exact (siteA_int X Y m d hA).2
  · rw [siteX_val, σtwin_siteA]; exact (siteB_int X Y m d hA).2
  · intro u
    obtain ⟨n, hn⟩ := c1_hexit X Y j d hC u
    exact ⟨n, by rw [nextPerm_pow_apply]; exact hn⟩

include hP hm in
/-- the writhe of the site's factor is the sign of the site -/
theorem sk_writhe_factor : Word.writheFrom [Letter.l (m + 1) d, Letter.σ m] (P ++ a :: L) = if a = d then 1 else -1 := by
  have s1 : (Letter.l (m + 1) d).step (P ++ a :: L) = some (P ++ a :: d :: (!d) :: L) := by
    rw [show P ++ a :: L = (P ++ [a]) ++ L by simp,
      step_of_prefix (ℓ := .l (m + 1) d) (by idxomega) (by idxomega) (act_l _ _ _)]
    simp
  have s2 : (Letter.σ m).step (P ++ a :: d :: (!d) :: L) = some (P ++ d :: a :: (!d) :: L) :=
    step_of_prefix (ℓ := .σ m) (by idxomega) (by idxomega) (act_σ_cons _ _ _ _)
  have d1 : (P ++ a :: d :: (!d) :: L).drop (m - 1) = a :: d :: (!d) :: L := List.drop_left' hP
  rw [u1_writheFrom_cons s1, u1_writheFrom_cons s2, u1_writheFrom_nil, u1_signBit_σ_drop d1, u1_signBit_l]
  simp

end SkeinSmoothIso

/-! #### K. The disjoint-gadget commutation (ng:commutation): `X a b Y ↦ X b a' Y` with `b` above `a` -/

section Comm

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

theorem arity_reindex (ℓ : Letter) (n : ℕ) : (ℓ.reindex n).arity = ℓ.arity := by cases ℓ <;> rfl
theorem coarity_reindex (ℓ : Letter) (n : ℕ) : (ℓ.reindex n).coarity = ℓ.coarity := by cases ℓ <;> rfl

theorem cm_letters : letterAt Wc X.length = a ∧ letterAt Wc (X.length + 1) = b := by
  constructor
  · have := letterAt_block X Pc2 Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pc2 Y (i := 1) (by simp)
    simpa using this

theorem cm_letters' : letterAt Wc' X.length = b ∧ letterAt Wc' (X.length + 1) = a.reindex (a.idx + b.coarity - b.arity) := by
  constructor
  · have := letterAt_block X Pc2' Y (i := 0) (by simp)
    simpa using this
  · have := letterAt_block X Pc2' Y (i := 1) (by simp)
    simpa using this

theorem cm_length : (X ++ [a, b] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem cm_length' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).length = X.length + 2 + Y.length := by
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem cm_extCol (k : ℕ) : ExtCol X Pc2 k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by unfold ExtCol; simp
theorem cm_extCol' (k : ℕ) : ExtCol X Pc2' k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k := by unfold ExtCol; simp

theorem cm_shift {k : ℕ} (hk : k ≤ X.length ∨ X.length + 2 ≤ k) : shiftIdx X Pc2 Pc2' k = k := by
  unfold shiftIdx
  by_cases h : k ≤ X.length
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have e1 : ([a, b] : Word).length = 2 := rfl
    have e2 : ([b, a.reindex (a.idx + b.coarity - b.arity)] : Word).length = 2 := rfl
    rw [e1, e2]; omega

theorem cm_extPair {s : ℕ × ℕ} (hs : s.1 ≤ X.length ∨ X.length + 2 ≤ s.1) : extPair X Pc2 Pc2' s = s := by
  obtain ⟨k, p⟩ := s; simp only [extPair, cm_shift X a b hs]

theorem cm_Pne : ([a, b] : Word) ≠ [] := List.cons_ne_nil _ _

theorem cm_extPair_of_ext (c : Slot Wc) (hc : IsExtSlot X Pc2 c.1) : extPair X Pc2 Pc2' c.1 = c.1 := by
  apply cm_extPair
  obtain ⟨⟨k, p⟩, hs⟩ := c
  unfold IsExtSlot at hc
  simp only at hc ⊢
  split_ifs at hc with hp
  · unfold ExtCol at hc; simp at hc; omega
  · unfold ExtCut at hc; simp at hc; omega

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

include hab hW in
theorem cm_sameEffect : SameEffect X Pc2 Pc2' :=
  sameEffect_of_replace X Pc2 Y Pc2' hW (fun _ _ h => run_comm_above hab h)

include hab hW in
theorem cm_bits_ext (p : ℕ) :
    bit Wc X.length p = bit Wc' X.length p ∧ bit Wc (X.length + 2) p = bit Wc' (X.length + 2) p := by
  have hE := cm_sameEffect X Y a b hab hW
  have h0 := bit_ext X Pc2 Y Pc2' (cm_Pne a b) hE (k := X.length) (Or.inl le_rfl) p
  have h2 := bit_ext X Pc2 Y Pc2' (cm_Pne a b) hE (k := X.length + 2) (Or.inr (by simp)) p
  rw [cm_shift X a b (Or.inl le_rfl)] at h0
  rw [cm_shift X a b (Or.inr le_rfl)] at h2
  exact ⟨h0, h2⟩

include hW' in
theorem cm_b_pos : 1 ≤ b.idx := by
  have := letter_idx_pos hW' (k := X.length) (by rw [cm_length']; omega)
  rwa [(cm_letters' X Y a b).1] at this

include hW in
theorem cm_a_pos : 1 ≤ a.idx := by
  have := letter_idx_pos hW (k := X.length) (by rw [cm_length]; omega)
  rwa [(cm_letters X Y a b).1] at this

include hW in
/-- the interior `σ` slots of `W` are the `σ` slots of the two block columns -/
theorem cm_int_iff (u : Slot Wc) :
    IntSlot X Pc2 Y u ↔ IsσSlot u ∧ (colOf u = X.length ∨ colOf u = X.length + 1) := by
  have hlt := colOf_lt hW u
  rw [cm_length] at hlt
  constructor
  · rintro ⟨hu, hext⟩
    rw [cm_extCol] at hext
    exact ⟨hu, by omega⟩
  · rintro ⟨hu, hc⟩
    exact ⟨hu, by rw [cm_extCol]; omega⟩

include hW' in
theorem cm_int_iff' (u : Slot Wc') :
    IntSlot X Pc2' Y u ↔ IsσSlot u ∧ (colOf u = X.length ∨ colOf u = X.length + 1) := by
  have hlt := colOf_lt hW' u
  rw [cm_length'] at hlt
  constructor
  · rintro ⟨hu, hext⟩
    rw [cm_extCol'] at hext
    exact ⟨hu, by omega⟩
  · rintro ⟨hu, hc⟩
    exact ⟨hu, by rw [cm_extCol']; omega⟩

theorem cm_k₀ : X.length < (X ++ [a, b] ++ Y).length := by rw [cm_length]; omega
theorem cm_k₁ : X.length + 1 < (X ++ [a, b] ++ Y).length := by rw [cm_length]; omega
theorem cm_k₀' : X.length < (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).length := by rw [cm_length']; omega
theorem cm_k₁' : X.length + 1 < (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).length := by rw [cm_length']; omega

/-- the crossing-ness of the letters corresponds across the exchange -/
theorem cm_cross_k₀ {u : Slot Wc} (hu : IsσSlot u) (hc : colOf u = X.length) :
    (letterAt Wc' (X.length + 1)).isCrossing = true := by
  have := hu.1
  rw [hc, (cm_letters X Y a b).1] at this
  rw [(cm_letters' X Y a b).2, isCrossing_reindex]; exact this

theorem cm_cross_k₁ {u : Slot Wc} (hu : IsσSlot u) (hc : colOf u = X.length + 1) :
    (letterAt Wc' X.length).isCrossing = true := by
  have := hu.1
  rw [hc, (cm_letters X Y a b).2] at this
  rw [(cm_letters' X Y a b).1]; exact this

theorem cm_cross_k₀' {u : Slot Wc'} (hu : IsσSlot u) (hc : colOf u = X.length) :
    (letterAt Wc (X.length + 1)).isCrossing = true := by
  have := hu.1
  rw [hc, (cm_letters' X Y a b).1] at this
  rw [(cm_letters X Y a b).2]; exact this

theorem cm_cross_k₁' {u : Slot Wc'} (hu : IsσSlot u) (hc : colOf u = X.length + 1) :
    (letterAt Wc X.length).isCrossing = true := by
  have := hu.1
  rw [hc, (cm_letters' X Y a b).2, isCrossing_reindex] at this
  rw [(cm_letters X Y a b).1]; exact this

include hW hW' in
/-- the forward interior correspondence of the commutation -/
noncomputable def cmφI_to (u : {u // IntSlot X Pc2 Y u}) : {u' // IntSlot X Pc2' Y u'} :=
  if hc : colOf u.1 = X.length then
    if isDesc u.1 then
      ⟨σSlotA hW' (cm_k₁' X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₀ X Y a b u.2.1 hc)),
        (cm_int_iff' X Y a b hW' _).2 ⟨isσSlot_σSlotA hW' _ _, Or.inr (σSlotA_spec hW' _ _).1⟩⟩
    else
      ⟨σSlotB hW' (cm_k₁' X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₀ X Y a b u.2.1 hc)),
        (cm_int_iff' X Y a b hW' _).2 ⟨isσSlot_σSlotB hW' _ _, Or.inr (σSlotB_spec hW' _ _).1⟩⟩
  else
    have hc1 : colOf u.1 = X.length + 1 := ((cm_int_iff X Y a b hW u.1).1 u.2).2.resolve_left hc
    if isDesc u.1 then
      ⟨σSlotA hW' (cm_k₀' X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₁ X Y a b u.2.1 hc1)),
        (cm_int_iff' X Y a b hW' _).2 ⟨isσSlot_σSlotA hW' _ _, Or.inl (σSlotA_spec hW' _ _).1⟩⟩
    else
      ⟨σSlotB hW' (cm_k₀' X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₁ X Y a b u.2.1 hc1)),
        (cm_int_iff' X Y a b hW' _).2 ⟨isσSlot_σSlotB hW' _ _, Or.inl (σSlotB_spec hW' _ _).1⟩⟩

include hW hW' in
/-- the inverse interior correspondence of the commutation -/
noncomputable def cmφI_inv (u : {u' // IntSlot X Pc2' Y u'}) : {u // IntSlot X Pc2 Y u} :=
  if hc : colOf u.1 = X.length then
    if isDesc u.1 then
      ⟨σSlotA hW (cm_k₁ X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₀' X Y a b u.2.1 hc)),
        (cm_int_iff X Y a b hW _).2 ⟨isσSlot_σSlotA hW _ _, Or.inr (σSlotA_spec hW _ _).1⟩⟩
    else
      ⟨σSlotB hW (cm_k₁ X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₀' X Y a b u.2.1 hc)),
        (cm_int_iff X Y a b hW _).2 ⟨isσSlot_σSlotB hW _ _, Or.inr (σSlotB_spec hW _ _).1⟩⟩
  else
    have hc1 : colOf u.1 = X.length + 1 := ((cm_int_iff' X Y a b hW' u.1).1 u.2).2.resolve_left hc
    if isDesc u.1 then
      ⟨σSlotA hW (cm_k₀ X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₁' X Y a b u.2.1 hc1)),
        (cm_int_iff X Y a b hW _).2 ⟨isσSlot_σSlotA hW _ _, Or.inl (σSlotA_spec hW _ _).1⟩⟩
    else
      ⟨σSlotB hW (cm_k₀ X Y a b) (letterAt_σ_of_isCrossing (cm_cross_k₁' X Y a b u.2.1 hc1)),
        (cm_int_iff X Y a b hW _).2 ⟨isσSlot_σSlotB hW _ _, Or.inl (σSlotB_spec hW _ _).1⟩⟩

include hW hW' in
theorem cmφI_to_val₀ (u : {u // IntSlot X Pc2 Y u}) (hc : colOf u.1 = X.length)
    (hcr : (letterAt Wc' (X.length + 1)).isCrossing = true) :
    (cmφI_to X Y a b hW hW' u).1 =
      if isDesc u.1 then σSlotA hW' (cm_k₁' X Y a b) (letterAt_σ_of_isCrossing hcr)
      else σSlotB hW' (cm_k₁' X Y a b) (letterAt_σ_of_isCrossing hcr) := by
  unfold cmφI_to
  rw [dite_eq_left hc]
  split_ifs <;> rfl

include hW hW' in
theorem cmφI_to_val₁ (u : {u // IntSlot X Pc2 Y u}) (hc : colOf u.1 = X.length + 1)
    (hcr : (letterAt Wc' X.length).isCrossing = true) :
    (cmφI_to X Y a b hW hW' u).1 =
      if isDesc u.1 then σSlotA hW' (cm_k₀' X Y a b) (letterAt_σ_of_isCrossing hcr)
      else σSlotB hW' (cm_k₀' X Y a b) (letterAt_σ_of_isCrossing hcr) := by
  unfold cmφI_to
  rw [dite_eq_right (by omega)]
  split_ifs <;> rfl

include hW hW' in
theorem cmφI_inv_val₀ (u : {u' // IntSlot X Pc2' Y u'}) (hc : colOf u.1 = X.length)
    (hcr : (letterAt Wc (X.length + 1)).isCrossing = true) :
    (cmφI_inv X Y a b hW hW' u).1 =
      if isDesc u.1 then σSlotA hW (cm_k₁ X Y a b) (letterAt_σ_of_isCrossing hcr)
      else σSlotB hW (cm_k₁ X Y a b) (letterAt_σ_of_isCrossing hcr) := by
  unfold cmφI_inv
  rw [dite_eq_left hc]
  split_ifs <;> rfl

include hW hW' in
theorem cmφI_inv_val₁ (u : {u' // IntSlot X Pc2' Y u'}) (hc : colOf u.1 = X.length + 1)
    (hcr : (letterAt Wc X.length).isCrossing = true) :
    (cmφI_inv X Y a b hW hW' u).1 =
      if isDesc u.1 then σSlotA hW (cm_k₀ X Y a b) (letterAt_σ_of_isCrossing hcr)
      else σSlotB hW (cm_k₀ X Y a b) (letterAt_σ_of_isCrossing hcr) := by
  unfold cmφI_inv
  rw [dite_eq_right (by omega)]
  split_ifs <;> rfl

include hW hW' in
/-- column and over bit of the forward correspondence -/
theorem cmφI_to_spec (u : {u // IntSlot X Pc2 Y u}) :
    isDesc (cmφI_to X Y a b hW hW' u).1 = isDesc u.1 ∧
    (colOf u.1 = X.length → colOf (cmφI_to X Y a b hW hW' u).1 = X.length + 1) ∧
    (colOf u.1 = X.length + 1 → colOf (cmφI_to X Y a b hW hW' u).1 = X.length) := by
  obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u.1).1 u.2
  rcases hc with hc | hc
  · rw [cmφI_to_val₀ X Y a b hW hW' u hc (cm_cross_k₀ X Y a b hσ hc)]
    refine ⟨?_, fun _ => ?_, fun h => absurd (hc.symm.trans h) (by omega)⟩
    · split_ifs with hd
      · rw [isDesc_σSlotA, hd]
      · rw [isDesc_σSlotB, eq_comm, Bool.eq_false_iff]; exact hd
    · split_ifs
      · exact (σSlotA_spec hW' _ _).1
      · exact (σSlotB_spec hW' _ _).1
  · rw [cmφI_to_val₁ X Y a b hW hW' u hc (cm_cross_k₁ X Y a b hσ hc)]
    refine ⟨?_, fun h => absurd (hc.symm.trans h) (by omega), fun _ => ?_⟩
    · split_ifs with hd
      · rw [isDesc_σSlotA, hd]
      · rw [isDesc_σSlotB, eq_comm, Bool.eq_false_iff]; exact hd
    · split_ifs
      · exact (σSlotA_spec hW' _ _).1
      · exact (σSlotB_spec hW' _ _).1

include hW hW' in
theorem cmφI_inv_spec (u : {u' // IntSlot X Pc2' Y u'}) :
    isDesc (cmφI_inv X Y a b hW hW' u).1 = isDesc u.1 ∧
    (colOf u.1 = X.length → colOf (cmφI_inv X Y a b hW hW' u).1 = X.length + 1) ∧
    (colOf u.1 = X.length + 1 → colOf (cmφI_inv X Y a b hW hW' u).1 = X.length) := by
  obtain ⟨hσ, hc⟩ := (cm_int_iff' X Y a b hW' u.1).1 u.2
  rcases hc with hc | hc
  · rw [cmφI_inv_val₀ X Y a b hW hW' u hc (cm_cross_k₀' X Y a b hσ hc)]
    refine ⟨?_, fun _ => ?_, fun h => absurd (hc.symm.trans h) (by omega)⟩
    · split_ifs with hd
      · rw [isDesc_σSlotA, hd]
      · rw [isDesc_σSlotB, eq_comm, Bool.eq_false_iff]; exact hd
    · split_ifs
      · exact (σSlotA_spec hW _ _).1
      · exact (σSlotB_spec hW _ _).1
  · rw [cmφI_inv_val₁ X Y a b hW hW' u hc (cm_cross_k₁' X Y a b hσ hc)]
    refine ⟨?_, fun h => absurd (hc.symm.trans h) (by omega), fun _ => ?_⟩
    · split_ifs with hd
      · rw [isDesc_σSlotA, hd]
      · rw [isDesc_σSlotB, eq_comm, Bool.eq_false_iff]; exact hd
    · split_ifs
      · exact (σSlotA_spec hW _ _).1
      · exact (σSlotB_spec hW _ _).1

include hW hW' in
/-- THE INTERIOR SLOT CORRESPONDENCE of the commutation: the `σ` slots of `a` (column `|X|` of `W`, column
`|X|+1` of `W'`) and of `b` (column `|X|+1` of `W`, column `|X|` of `W'`), over bit preserved. -/
noncomputable def cmφI : {u // IntSlot X Pc2 Y u} ≃ {u' // IntSlot X Pc2' Y u'} where
  toFun := cmφI_to X Y a b hW hW'
  invFun := cmφI_inv X Y a b hW hW'
  left_inv u := by
    apply Subtype.ext
    obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u.1).1 u.2
    obtain ⟨hd, hc0, hc1⟩ := cmφI_to_spec X Y a b hW hW' u
    obtain ⟨hd', hc0', hc1'⟩ := cmφI_inv_spec X Y a b hW hW' (cmφI_to X Y a b hW hW' u)
    refine σslot_ext hW (cmφI_inv X Y a b hW hW' _).2.1 hσ ?_ (hd'.trans hd)
    rcases hc with hc | hc
    · rw [hc1' (hc0 hc), hc]
    · rw [hc0' (hc1 hc), hc]
  right_inv u := by
    apply Subtype.ext
    obtain ⟨hσ, hc⟩ := (cm_int_iff' X Y a b hW' u.1).1 u.2
    obtain ⟨hd, hc0, hc1⟩ := cmφI_inv_spec X Y a b hW hW' u
    obtain ⟨hd', hc0', hc1'⟩ := cmφI_to_spec X Y a b hW hW' (cmφI_inv X Y a b hW hW' u)
    refine σslot_ext hW' (cmφI_to X Y a b hW hW' _).2.1 hσ ?_ (hd'.trans hd)
    rcases hc with hc | hc
    · rw [hc1' (hc0 hc), hc]
    · rw [hc0' (hc1 hc), hc]

include hW hW' in
theorem cmφI_val (u : {u // IntSlot X Pc2 Y u}) : (cmφI X Y a b hW hW' u).1 = (cmφI_to X Y a b hW hW' u).1 := rfl

end Comm

section WindowSteps

variable {V : Word} (hV : V.Closed)
include hV

omit hV in
/-- a position above a letter is never one of a crossing's positions -/
theorem notσ_of_lt {ℓ : Letter} {k p : ℕ} (hℓ : letterAt V k = ℓ) (hp : p < ℓ.idx) :
    ∀ j, letterAt V k = .σ j → p ≠ j ∧ p ≠ j + 1 := by
  intro j hj
  rw [hℓ] at hj
  subst hj
  simp only [idx] at hp
  omega

omit hV in
theorem notσ_of_ge {ℓ : Letter} {k p : ℕ} (hℓ : letterAt V k = ℓ) (hp : ℓ.idx + ℓ.arity ≤ p) :
    ∀ j, letterAt V k = .σ j → p ≠ j ∧ p ≠ j + 1 := by
  intro j hj
  rw [hℓ] at hj
  subst hj
  simp only [idx, arity] at hp
  omega

/-- the right cusp: the rightward arm enters the vertex, which sends the traversal out along the other arm -/
theorem r_window {k j p : ℕ} (hℓ : letterAt V k = .r j) {s : Slot V} (hs : s.1 = (k, p)) (hp : p = j ∨ p = j + 1)
    (hb : bit V k p = true) :
    (next hV s).1 = (k, 0) ∧ (next hV (next hV s)).1 = (k, if bit V k j then j + 1 else j) ∧
      bit V k (if bit V k j then j + 1 else j) = false := by
  have hk := slot_col_lt hV hs
  have h1 := next_arm_r hV hk hℓ hs hp hb
  refine ⟨h1, next_cusp_r hV hℓ h1, ?_⟩
  obtain ⟨-, hne⟩ := r_bits hV hk hℓ
  cases hbj : bit V k j
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact hbj
  · simp only [↓reduceIte]
    rw [hbj] at hne
    cases h : bit V k (j + 1)
    · rfl
    · exact absurd rfl (h ▸ hne)

/-- the left cusp: the leftward arm enters the vertex, which sends the traversal out along the other arm -/
theorem l_window {k j q : ℕ} {d : Bool} (hℓ : letterAt V k = .l j d) (hk : k < V.length) {s : Slot V}
    (hs : s.1 = (k + 1, q)) (hq : q = j ∨ q = j + 1) (hb : bit V (k + 1) q = false) :
    (next hV s).1 = (k, 0) ∧ (next hV (next hV s)).1 = (k + 1, if d then j else j + 1) ∧
      bit V (k + 1) (if d then j else j + 1) = true := by
  have h1 := next_arm_l hV hk hℓ hs hq hb
  refine ⟨h1, next_cusp_l hV hℓ h1, ?_⟩
  obtain ⟨-, hb1, hb2⟩ := l_bits hV hk hℓ
  cases d
  · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hb2]; rfl
  · simp only [↓reduceIte]; exact hb1

/-- the crossing, rightward: the slot is a `σ` slot with the recorded over bit -/
theorem σ_window_right {k j p : ℕ} (hℓ : letterAt V k = .σ j) {s : Slot V} (hs : s.1 = (k, p)) (hp : p = j ∨ p = j + 1)
    (hb : bit V k p = true) :
    (next hV s).1 = (k + 1, if p = j then j + 1 else j) ∧ bit V (k + 1) (if p = j then j + 1 else j) = true ∧
      IsσSlot s ∧ isDesc s = decide (p = j) ∧ colOf s = k := by
  have hk := slot_col_lt hV hs
  obtain ⟨hj1, -, -, b1, b2⟩ := σ_facts hV hk hℓ
  have hp0 : p ≠ 0 := by omega
  have hcol : colOf s = k := block_col_true hs hp0 hb
  rcases hp with hpj | hpj
  · rw [ite_eq_left hpj]
    have hs' : s.1 = (k, j) := hpj ▸ hs
    have hb' : bit V k j = true := hpj ▸ hb
    have hsh : shapeOf s = .pass j (j + 1) := by
      unfold shapeOf; rw [hs']; simp only [show j ≠ 0 by omega, ↓reduceIte, hb', hℓ, posR_σ_idx]
    refine ⟨next_σ_right_idx hV hℓ hs' hb', by rw [b1, hb'], ⟨by rw [hcol, hℓ]; rfl, ?_⟩, ?_, hcol⟩
    · rw [hcol, hℓ, hsh]; simp [idx]
    · unfold isDesc; rw [hsh]; simp [hpj]
  · have hne : p ≠ j := by omega
    rw [ite_eq_right hne]
    have hs' : s.1 = (k, j + 1) := hpj ▸ hs
    have hb' : bit V k (j + 1) = true := hpj ▸ hb
    have hsh : shapeOf s = .pass (j + 1) j := by
      unfold shapeOf; rw [hs']; simp only [show j + 1 ≠ 0 by omega, ↓reduceIte, hb', hℓ, posR_σ_idx_succ]
    refine ⟨next_σ_right_succ hV hℓ hs' hb', by rw [b2, hb'], ⟨by rw [hcol, hℓ]; rfl, ?_⟩, ?_, hcol⟩
    · rw [hcol, hℓ, hsh]; simp [idx]
    · unfold isDesc; rw [hsh]; simp [hne]

/-- the crossing, leftward -/
theorem σ_window_left {k j q : ℕ} (hℓ : letterAt V k = .σ j) {s : Slot V} (hs : s.1 = (k + 1, q)) (hq : q = j ∨ q = j + 1)
    (hb : bit V (k + 1) q = false) :
    (next hV s).1 = (k, if q = j then j + 1 else j) ∧ bit V k (if q = j then j + 1 else j) = false ∧
      IsσSlot s ∧ isDesc s = decide (q = j + 1) ∧ colOf s = k := by
  have hk := lt_length_of_letterAt_σ hℓ
  obtain ⟨hj1, -, -, b1, b2⟩ := σ_facts hV hk hℓ
  have hq0 : q ≠ 0 := by omega
  have hcol : colOf s = k := by rw [block_col_false hs hq0 hb, Nat.add_sub_cancel]
  rcases hq with hqj | hqj
  · rw [ite_eq_left hqj]
    have hs' : s.1 = (k + 1, j) := hqj ▸ hs
    have hb' : bit V (k + 1) j = false := hqj ▸ hb
    have hsh : shapeOf s = .pass (j + 1) j := by
      unfold shapeOf; rw [hs']
      simp only [show j ≠ 0 by omega, ↓reduceIte, hb', Bool.false_eq_true, Nat.add_sub_cancel, hℓ, posL_σ_idx]
    have hne : ¬ (q = j + 1) := by omega
    refine ⟨next_σ_left_idx hV hℓ hs' hb', by rw [← b2, hb'], ⟨by rw [hcol, hℓ]; rfl, ?_⟩, ?_, hcol⟩
    · rw [hcol, hℓ, hsh]; simp [idx]
    · unfold isDesc; rw [hsh]; simp [hne]
  · have hne : q ≠ j := by omega
    rw [ite_eq_right hne]
    have hs' : s.1 = (k + 1, j + 1) := hqj ▸ hs
    have hb' : bit V (k + 1) (j + 1) = false := hqj ▸ hb
    have hsh : shapeOf s = .pass j (j + 1) := by
      unfold shapeOf; rw [hs']
      simp only [show j + 1 ≠ 0 by omega, ↓reduceIte, hb', Bool.false_eq_true, Nat.add_sub_cancel, hℓ, posL_σ_idx_succ]
    refine ⟨next_σ_left_succ hV hℓ hs' hb', by rw [← b1, hb'], ⟨by rw [hcol, hℓ]; rfl, ?_⟩, ?_, hcol⟩
    · rw [hcol, hℓ, hsh]; simp [idx]
    · unfold isDesc; rw [hsh]; simp [hqj]

end WindowSteps

section Hexit2

variable {V : Word} (hV : V.Closed)
include hV

/-- a vertex sends the traversal out along an arm of its cusp -/
theorem exit_vertex {ℓ : Letter} {k : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} (hs : s.1 = (k, 0)) :
    ∃ p', p' ≠ 0 ∧ ((next hV s).1 = (k + 1, p') ∧ bit V (k + 1) p' = true ∨
      (next hV s).1 = (k, p') ∧ bit V k p' = false) := by
  have hk := vertex_lt hs
  have hnc := vertex_not_crossing hs
  rw [hℓ] at hnc
  cases ℓ with
  | σ j => exact Bool.noConfusion hnc
  | l j d =>
    obtain ⟨hj, hb1, hb2⟩ := l_bits hV hk hℓ
    refine ⟨_, ?_, Or.inl ⟨next_cusp_l hV hℓ hs, ?_⟩⟩
    · split <;> omega
    · cases d
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [hb2]; rfl
      · simp only [↓reduceIte]; exact hb1
  | r j =>
    obtain ⟨hj, hne⟩ := r_bits hV hk hℓ
    refine ⟨_, ?_, Or.inr ⟨next_cusp_r hV hℓ hs, ?_⟩⟩
    · split <;> omega
    · cases hbj : bit V k j
      · simp only [Bool.false_eq_true, ↓reduceIte]; exact hbj
      · simp only [↓reduceIte]
        rw [hbj] at hne
        cases h : bit V k (j + 1)
        · rfl
        · exact absurd rfl (h ▸ hne)

/-- a rightward slot at a cut is a `σ` slot or leaves its letter's column within two steps -/
theorem exit_right {ℓ : Letter} {k p : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} (hs : s.1 = (k, p)) (hp : p ≠ 0)
    (hb : bit V k p = true) :
    IsσSlot s ∨ ∃ n p', p' ≠ 0 ∧ (((next hV)^[n] s).1 = (k + 1, p') ∧ bit V (k + 1) p' = true ∨
      ((next hV)^[n] s).1 = (k, p') ∧ bit V k p' = false ∧ ℓ.idx ≤ p' ∧ p' < ℓ.idx + ℓ.arity) := by
  have hk := slot_col_lt hV hs
  have hi := letter_idx_pos hV hk
  rw [hℓ] at hi
  rcases lt_or_ge p ℓ.idx with hlt | hge
  · obtain ⟨h1, hb1⟩ := pass_r_lt hV hℓ hs hp hb hlt
    exact Or.inr ⟨1, p, hp, Or.inl ⟨h1, hb1⟩⟩
  rcases lt_or_ge p (ℓ.idx + ℓ.arity) with hlt2 | hge2
  · cases ℓ with
    | σ j =>
      simp only [idx, arity] at hge hlt2
      exact Or.inl (σ_window_right hV hℓ hs (by omega) hb).2.2.1
    | l j d => simp only [arity] at hlt2; omega
    | r j =>
      simp only [idx, arity] at hge hlt2
      obtain ⟨-, h2, hb2⟩ := r_window hV hℓ hs (by omega) hb
      have := (r_bits hV hk hℓ).1
      refine Or.inr ⟨2, _, by split <;> omega, Or.inr ⟨?_, hb2, by simp only [idx]; split <;> omega,
        by simp only [idx, arity]; split <;> omega⟩⟩
      show (next hV (next hV s)).1 = _
      exact h2
  · obtain ⟨h1, hb1⟩ := pass_r_ge hV hℓ hs hp hb hge2
    exact Or.inr ⟨1, _, by omega, Or.inl ⟨h1, hb1⟩⟩

/-- a leftward slot at a cut is a `σ` slot or leaves its letter's column within two steps -/
theorem exit_left {ℓ : Letter} {k q : ℕ} (hℓ : letterAt V k = ℓ) {s : Slot V} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0)
    (hb : bit V (k + 1) q = false) :
    IsσSlot s ∨ ∃ n p', p' ≠ 0 ∧
      (((next hV)^[n] s).1 = (k + 1, p') ∧ bit V (k + 1) p' = true ∧ ℓ.idx ≤ p' ∧ p' < ℓ.idx + ℓ.coarity ∨
      ((next hV)^[n] s).1 = (k, p') ∧ bit V k p' = false) := by
  have hk : k < V.length := by have := slot_col_lt hV hs; omega
  have hi := letter_idx_pos hV hk
  rw [hℓ] at hi
  rcases lt_or_ge q ℓ.idx with hlt | hge
  · obtain ⟨h1, hb1⟩ := pass_l_lt hV hℓ hs hq hb hlt
    exact Or.inr ⟨1, q, hq, Or.inr ⟨h1, hb1⟩⟩
  rcases lt_or_ge q (ℓ.idx + ℓ.coarity) with hlt2 | hge2
  · cases ℓ with
    | σ j =>
      simp only [idx, coarity] at hge hlt2
      exact Or.inl (σ_window_left hV hℓ hs (by omega) hb).2.2.1
    | r j => simp only [coarity] at hlt2; omega
    | l j d =>
      simp only [idx, coarity] at hge hlt2
      obtain ⟨-, h2, hb2⟩ := l_window hV hℓ hk hs (by omega) hb
      have := (l_bits hV hk hℓ).1
      refine Or.inr ⟨2, _, by split <;> omega, Or.inl ⟨?_, hb2, by simp only [idx]; split <;> omega,
        by simp only [idx, coarity]; split <;> omega⟩⟩
      show (next hV (next hV s)).1 = _
      exact h2
  · obtain ⟨h1, hb1⟩ := pass_l_ge hV hℓ hs hq hb hge2
    exact Or.inr ⟨1, _, by omega, Or.inr ⟨h1, hb1⟩⟩

end Hexit2

section CommExit

variable {V : Word} (hV : V.Closed)

/-- the target of the two-letter exits: a slot in column `k-1` or `k+2` -/
def CExit (k : ℕ) (s : Slot V) : Prop :=
  (∃ p', p' ≠ 0 ∧ s.1 = (k + 1 + 1, p') ∧ bit V (k + 1 + 1) p' = true) ∨
  (∃ p', p' ≠ 0 ∧ s.1 = (k, p') ∧ bit V k p' = false)

/-- the traversal from `s` reaches a `σ` slot or leaves the two columns `k`, `k+1` -/
def CDone (k : ℕ) (s : Slot V) : Prop := ∃ n, IsσSlot ((next hV)^[n] s) ∨ CExit k ((next hV)^[n] s)

theorem cdone_of_iter {k : ℕ} {s : Slot V} (n : ℕ) (h : CDone hV k ((next hV)^[n] s)) : CDone hV k s := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + n, by rw [Function.iterate_add_apply]; exact hm⟩

variable {k : ℕ} {ℓa ℓb : Letter} (hℓa : letterAt V k = ℓa) (hℓb : letterAt V (k + 1) = ℓb)
  (hab : ℓb.idx + ℓb.arity ≤ ℓa.idx ∨ ℓa.idx + ℓa.coarity ≤ ℓb.idx)
include hV hℓa hℓb hab

/-- rightward at the middle cut -/
theorem cexit_D {s : Slot V} {p : ℕ} (hs : s.1 = (k + 1, p)) (hp : p ≠ 0) (hb : bit V (k + 1) p = true) :
    CDone hV k s := by
  have hk1 := slot_col_lt hV hs
  have hi := letter_idx_pos hV (by omega : k < V.length)
  rw [hℓa] at hi
  rcases exit_right hV hℓb hs hp hb with hσ | ⟨n, p', hp', ⟨h1, hb1⟩ | ⟨h1, hb1, hw1, hw2⟩⟩
  · exact ⟨0, Or.inl hσ⟩
  · exact ⟨n, Or.inr (Or.inl ⟨p', hp', h1, hb1⟩)⟩
  · rcases hab with hab | hab
    · obtain ⟨h2, hb2⟩ := pass_l_lt hV hℓa h1 hp' hb1 (by omega)
      exact ⟨n + 1, Or.inr (Or.inr ⟨p', hp', by rw [Function.iterate_succ_apply']; exact h2, hb2⟩)⟩
    · obtain ⟨h2, hb2⟩ := pass_l_ge hV hℓa h1 hp' hb1 (by omega)
      exact ⟨n + 1, Or.inr (Or.inr ⟨_, by omega, by rw [Function.iterate_succ_apply']; exact h2, hb2⟩)⟩

/-- leftward at the middle cut -/
theorem cexit_B {s : Slot V} {q : ℕ} (hs : s.1 = (k + 1, q)) (hq : q ≠ 0) (hb : bit V (k + 1) q = false) :
    CDone hV k s := by
  have hk1 := slot_col_lt hV hs
  have hi := letter_idx_pos hV hk1
  rw [hℓb] at hi
  rcases exit_left hV hℓa hs hq hb with hσ | ⟨n, p', hp', ⟨h1, hb1, hw1, hw2⟩ | ⟨h1, hb1⟩⟩
  · exact ⟨0, Or.inl hσ⟩
  · rcases hab with hab | hab
    · obtain ⟨h2, hb2⟩ := pass_r_ge hV hℓb h1 hp' hb1 (by omega)
      exact ⟨n + 1, Or.inr (Or.inl ⟨_, by omega, by rw [Function.iterate_succ_apply']; exact h2, hb2⟩)⟩
    · obtain ⟨h2, hb2⟩ := pass_r_lt hV hℓb h1 hp' hb1 (by omega)
      exact ⟨n + 1, Or.inr (Or.inl ⟨p', hp', by rw [Function.iterate_succ_apply']; exact h2, hb2⟩)⟩
  · exact ⟨n, Or.inr (Or.inr ⟨p', hp', h1, hb1⟩)⟩

/-- rightward at the first cut -/
theorem cexit_A {s : Slot V} {p : ℕ} (hs : s.1 = (k, p)) (hp : p ≠ 0) (hb : bit V k p = true) :
    CDone hV k s := by
  rcases exit_right hV hℓa hs hp hb with hσ | ⟨n, p', hp', ⟨h1, hb1⟩ | ⟨h1, hb1, -, -⟩⟩
  · exact ⟨0, Or.inl hσ⟩
  · exact cdone_of_iter hV n (cexit_D hV hℓa hℓb hab h1 hp' hb1)
  · exact ⟨n, Or.inr (Or.inr ⟨p', hp', h1, hb1⟩)⟩

/-- the first vertex -/
theorem cexit_C {s : Slot V} (hs : s.1 = (k, 0)) : CDone hV k s := by
  obtain ⟨p', hp', ⟨h1, hb1⟩ | ⟨h1, hb1⟩⟩ := exit_vertex hV hℓa hs
  · exact cdone_of_iter hV 1 (cexit_D hV hℓa hℓb hab (by rw [Function.iterate_one]; exact h1) hp' hb1)
  · exact ⟨1, Or.inr (Or.inr ⟨p', hp', by rw [Function.iterate_one]; exact h1, hb1⟩)⟩

/-- leftward at the last cut -/
theorem cexit_E {s : Slot V} {q : ℕ} (hs : s.1 = (k + 1 + 1, q)) (hq : q ≠ 0) (hb : bit V (k + 1 + 1) q = false) :
    CDone hV k s := by
  rcases exit_left hV hℓb hs hq hb with hσ | ⟨n, p', hp', ⟨h1, hb1, -, -⟩ | ⟨h1, hb1⟩⟩
  · exact ⟨0, Or.inl hσ⟩
  · exact ⟨n, Or.inr (Or.inl ⟨p', hp', h1, hb1⟩)⟩
  · exact cdone_of_iter hV n (cexit_B hV hℓa hℓb hab h1 hp' hb1)

/-- the second vertex -/
theorem cexit_F {s : Slot V} (hs : s.1 = (k + 1, 0)) : CDone hV k s := by
  obtain ⟨p', hp', ⟨h1, hb1⟩ | ⟨h1, hb1⟩⟩ := exit_vertex hV hℓb hs
  · exact ⟨1, Or.inr (Or.inl ⟨p', hp', by rw [Function.iterate_one]; exact h1, hb1⟩)⟩
  · exact cdone_of_iter hV 1 (cexit_B hV hℓa hℓb hab (by rw [Function.iterate_one]; exact h1) hp' hb1)

end CommExit

section HexitBlock

variable {X P Y : Word} (hV : (X ++ P ++ Y).Closed)
include hV

/-- every slot of a word with a two-letter block of non-interacting letters reaches an active slot -/
theorem hexit_of_comm (hext : ∀ k, ExtCol X P k ↔ k + 1 ≤ X.length ∨ X.length + 2 ≤ k) {ℓa ℓb : Letter}
    (hℓa : letterAt (X ++ P ++ Y) X.length = ℓa) (hℓb : letterAt (X ++ P ++ Y) (X.length + 1) = ℓb)
    (hab : ℓb.idx + ℓb.arity ≤ ℓa.idx ∨ ℓa.idx + ℓa.coarity ≤ ℓb.idx) (u : Slot (X ++ P ++ Y)) :
    ∃ n, ActE X P Y ((next hV)^[n] u) := by
  obtain ⟨k, p, hu⟩ : ∃ k p, u.1 = (k, p) := ⟨_, _, rfl⟩
  by_cases he : ExtCol X P (colOf u)
  · exact ⟨0, Or.inl he⟩
  have hcol : colOf u = X.length ∨ colOf u = X.length + 1 := by
    have := he
    rw [hext] at this
    omega
  suffices h : CDone hV X.length u by
    obtain ⟨n, hσ | ⟨p', hp', h1, hb1⟩ | ⟨p', hp', h1, hb1⟩⟩ := h
    · exact ⟨n, isσSlot_actE X P Y hσ⟩
    · refine ⟨n, Or.inl ?_⟩
      show ExtCol X P (colOf _)
      rw [block_col_true h1 hp' hb1, hext]; omega
    · refine ⟨n, Or.inl ?_⟩
      show ExtCol X P (colOf _)
      have := (cutSlot_facts hV h1 hp').2.2.1
      rw [block_col_false h1 hp' hb1, hext]; omega
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · rw [block_col_vertex hu] at hcol
    rcases hcol with rfl | rfl
    · exact cexit_C hV hℓa hℓb hab hu
    · exact cexit_F hV hℓa hℓb hab hu
  have hp : p ≠ 0 := by omega
  cases hb : bit (X ++ P ++ Y) k p
  · rw [block_col_false hu hp hb] at hcol
    have hk0 := (cutSlot_facts hV hu hp).2.2.1
    rcases hcol with h | h
    · have hk : k = X.length + 1 := by omega
      subst hk
      exact cexit_B hV hℓa hℓb hab hu hp hb
    · have hk : k = X.length + 1 + 1 := by omega
      subst hk
      exact cexit_E hV hℓa hℓb hab hu hp hb
  · rw [block_col_true hu hp hb] at hcol
    rcases hcol with rfl | rfl
    · exact cexit_A hV hℓa hℓb hab hu hp hb
    · exact cexit_D hV hℓa hℓb hab hu hp hb

end HexitBlock

section CommPassage

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

omit hW in
theorem notσ_of_ge' {V : Word} {ℓ : Letter} {k p : ℕ} (hℓ : letterAt V k = ℓ) (hp : ℓ.idx + ℓ.coarity ≤ p) :
    ∀ j, letterAt V k = .σ j → p ≠ j ∧ p ≠ j + 1 := by
  intro j hj
  rw [hℓ] at hj
  subst hj
  simp only [idx, coarity] at hp
  omega

/-- the coordinates of the two `σ` slots of a crossing column -/
theorem σSlotA_val {W : Word} (hW : W.Closed) {k j : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ j) :
    (σSlotA hW hk hℓ).1 = if bit W k j then (k, j) else (k + 1, j + 1) := by
  unfold σSlotA; split_ifs <;> rfl

theorem σSlotB_val {W : Word} (hW : W.Closed) {k j : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ j) :
    (σSlotB hW hk hℓ).1 = if bit W k (j + 1) then (k, j + 1) else (k + 1, j) := by
  unfold σSlotB; split_ifs <;> rfl

include hW hW' in
/-- twins correspond -/
theorem cmφI_twin (u : {u // IntSlot X Pc2 Y u}) :
    (cmφI X Y a b hW hW' ⟨σtwin hW u.1, ⟨isσSlot_σtwin hW u.2.1, by rw [colOf_σtwin hW u.2.1]; exact u.2.2⟩⟩).1 =
      σtwin hW' (cmφI X Y a b hW hW' u).1 := by
  rw [cmφI_val, cmφI_val]
  obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u.1).1 u.2
  obtain ⟨hd, hc0, hc1⟩ := cmφI_to_spec X Y a b hW hW' u
  obtain ⟨hd', hc0', hc1'⟩ := cmφI_to_spec X Y a b hW hW' ⟨σtwin hW u.1, _⟩
  have hσ1 : IsσSlot (cmφI_to X Y a b hW hW' u).1 := (cmφI_to X Y a b hW hW' u).2.1
  refine σslot_ext hW' (cmφI_to X Y a b hW hW' _).2.1 (isσSlot_σtwin hW' hσ1) ?_ ?_
  · rcases hc with hc | hc
    · exact (hc0' (by show colOf (σtwin hW u.1) = _; rw [colOf_σtwin hW hσ]; exact hc)).trans
        ((hc0 hc).symm.trans (colOf_σtwin hW' hσ1).symm)
    · exact (hc1' (by show colOf (σtwin hW u.1) = _; rw [colOf_σtwin hW hσ]; exact hc)).trans
        ((hc1 hc).symm.trans (colOf_σtwin hW' hσ1).symm)
  · refine hd'.trans ?_
    show isDesc (σtwin hW u.1) = isDesc (σtwin hW' (cmφI_to X Y a b hW hW' u).1)
    rw [isDesc_σtwin hW hσ, isDesc_σtwin hW' hσ1, hd]

theorem arity_of_crossing {ℓ : Letter} (h : ℓ.isCrossing = true) : ℓ.arity = 2 := by
  cases ℓ with
  | l _ _ => cases h
  | r _ => cases h
  | σ _ => rfl

theorem coarity_of_crossing {ℓ : Letter} (h : ℓ.isCrossing = true) : ℓ.coarity = 2 := by
  cases ℓ with
  | l _ _ => cases h
  | r _ => cases h
  | σ _ => rfl

theorem eq_σ_of_crossing {ℓ : Letter} (h : ℓ.isCrossing = true) : ℓ = .σ ℓ.idx := by
  cases ℓ with
  | l _ _ => cases h
  | r _ => cases h
  | σ _ => rfl

include hab hW hW' in
/-- signs correspond -/
theorem cmφI_sgn (u : {u // IntSlot X Pc2 Y u}) : σsgn (cmφI X Y a b hW hW' u).1 = σsgn u.1 := by
  rw [cmφI_val]
  obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u.1).1 u.2
  obtain ⟨-, hc0, hc1⟩ := cmφI_to_spec X Y a b hW hW' u
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  have hk₀ := cm_k₀ X Y a b
  have hk₀' := cm_k₀' X Y a b
  have hb1 := cm_b_pos X Y a b hW'
  have tE := cm_bits_ext X Y a b hab hW
  unfold σsgn σsgnCol
  rcases hc with hc | hc
  · rw [hc0 hc, hc, hℓa', hℓa, idx_reindex]
    have t1 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = bit Wc' X.length a.idx := by
      have := bit_succ_of_ge hW' hk₀' (p := a.idx) (by rw [hℓb']; exact hab)
      rwa [hℓb'] at this
    have t2 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity + 1) = bit Wc' X.length (a.idx + 1) := by
      have := bit_succ_of_ge hW' hk₀' (p := a.idx + 1) (by rw [hℓb']; omega)
      rw [hℓb'] at this
      rw [show a.idx + b.coarity - b.arity + 1 = a.idx + 1 + b.coarity - b.arity by omega]
      exact this
    rw [t1, t2, ← (tE a.idx).1, ← (tE (a.idx + 1)).1]
  · rw [hc1 hc, hc, hℓb', hℓb]
    have hcr : b.isCrossing = true := by have := hσ.1; rwa [hc, hℓb] at this
    have hb2 : b.arity = 2 := arity_of_crossing hcr
    have t1 : bit Wc (X.length + 1) b.idx = bit Wc X.length b.idx :=
      bit_succ_of_lt hW hk₀ (p := b.idx) hb1 (by rw [hℓa]; omega)
    have t2 : bit Wc (X.length + 1) (b.idx + 1) = bit Wc X.length (b.idx + 1) :=
      bit_succ_of_lt hW hk₀ (p := b.idx + 1) (by omega) (by rw [hℓa]; omega)
    rw [t1, t2, (tE b.idx).1, (tE (b.idx + 1)).1]

end CommPassage

section CommEntries

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

local notation "φc" => φA X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW (cmφI X Y a b hW hW')

include hab hW hW' in
theorem cm_φext (c : Slot Wc) (hc : ExtCol X Pc2 (colOf c)) : (φc ⟨c, Or.inl hc⟩).1.1 = c.1 :=
  (φA_val_ext' X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW _ ⟨c, Or.inl hc⟩ hc).trans
    (cm_extPair_of_ext X Y a b c (isExtSlot_of_extCol X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) c hc))

include hab hW hW' in
theorem cm_φint (c : Slot Wc) (hc : ActE X Pc2 Y c) (hint : IntSlot X Pc2 Y c) :
    (φc ⟨c, hc⟩).1 = (cmφI_to X Y a b hW hW' ⟨c, hint⟩).1 :=
  φA_val_int X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW _ ⟨c, hc⟩ hint.2

/-- the kinds with a nonempty read window / write window -/
theorem kind_of_arity {ℓ : Letter} (h : ℓ.arity ≠ 0) : (∃ j, ℓ = .r j) ∨ (∃ j, ℓ = .σ j) := by
  cases ℓ with
  | l _ _ => exact absurd rfl h
  | r j => exact Or.inl ⟨j, rfl⟩
  | σ j => exact Or.inr ⟨j, rfl⟩

theorem kind_of_coarity {ℓ : Letter} (h : ℓ.coarity ≠ 0) : (∃ j d, ℓ = .l j d) ∨ (∃ j, ℓ = .σ j) := by
  cases ℓ with
  | l j d => exact Or.inl ⟨j, d, rfl⟩
  | r _ => exact absurd rfl h
  | σ j => exact Or.inr ⟨j, rfl⟩

include hab hW hW' in
/-- the entries of the commutation block from the left -/
theorem cm_left (e : Slot Wc) (hext : IsExtSlot X Pc2 e.1) {p : ℕ} (he : e.1 = (X.length, p)) (hp : p ≠ 0)
    (hbit : bit Wc X.length p = true) :
    ∃ (m : ℕ) (c : Slot Wc) (hc : ActE X Pc2 Y c), (next hW)^[m] e = c ∧
      (∀ i < m, ¬ ActE X Pc2 Y ((next hW)^[i] e)) ∧
      ∃ (m' : ℕ) (b' : Slot Wc'), b'.1 = extPair X Pc2 Pc2' e.1 ∧
        (next hW')^[m'] b' = (φc ⟨c, hc⟩).1 ∧ ∀ i < m', ¬ ActE X Pc2' Y ((next hW')^[i] b') := by
  have hE := cm_sameEffect X Y a b hab hW
  have hPne := cm_Pne a b
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  have hk₀ := cm_k₀ X Y a b
  have hk₁ := cm_k₁ X Y a b
  have hk₀' := cm_k₀' X Y a b
  have hk₁' := cm_k₁' X Y a b
  have ha1 := cm_a_pos X Y a b hW
  have hb1 := cm_b_pos X Y a b hW'
  have tE := cm_bits_ext X Y a b hab hW
  have hidx' : (a.reindex (a.idx + b.coarity - b.arity)).idx = a.idx + b.coarity - b.arity := idx_reindex a _
  have har' := arity_reindex a (a.idx + b.coarity - b.arity)
  have hco' := coarity_reindex a (a.idx + b.coarity - b.arity)
  let e' : Slot Wc' := ⟨extPair X Pc2 Pc2' e.1, isSlot_ext X Pc2 Y Pc2' hPne hE e.2 hext⟩
  have he' : e'.1 = (X.length, p) := by
    show extPair X Pc2 Pc2' e.1 = _
    rw [he, cm_extPair X a b (Or.inl le_rfl)]
  have hbit' : bit Wc' X.length p = true := by rw [← (tE p).1]; exact hbit
  have φext := cm_φext X Y a b hab hW hW'
  have φint := cm_φint X Y a b hab hW hW'
  rcases lt_or_ge p b.idx with R1 | hpb
  · -- above both gadgets
    obtain ⟨h1, hb1e⟩ := pass_r_lt hW hℓa he hp hbit (by omega)
    obtain ⟨h2, hb2e⟩ := pass_r_lt hW hℓb h1 hp hb1e R1
    obtain ⟨h1', hb1'⟩ := pass_r_lt hW' hℓb' he' hp hbit' R1
    obtain ⟨h2', hb2'⟩ := pass_r_lt hW' hℓa' h1' hp hb1' (by rw [hidx']; omega)
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by rw [block_col_true h2 hp hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega) (not_σ_right he hp hbit (notσ_of_lt hℓa (by omega))))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true h1 hp hb1e, cm_extCol]; omega)
        (not_σ_right h1 hp hb1e (notσ_of_lt hℓb R1))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega) (not_σ_right he' hp hbit' (notσ_of_lt hℓb' R1)))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true h1' hp hb1', cm_extCol']; omega)
        (not_σ_right h1' hp hb1' (notσ_of_lt hℓa' (by rw [hidx']; omega)))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  rcases lt_or_ge p (b.idx + b.arity) with R2 | hpb2
  · -- the read window of `b`
    obtain ⟨h1, hb1e⟩ := pass_r_lt hW hℓa he hp hbit (by omega)
    have nE0 : ¬ ActE X Pc2 Y e :=
      not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega) (not_σ_right he hp hbit (notσ_of_lt hℓa (by omega)))
    rcases kind_of_arity (ℓ := b) (by omega) with ⟨j, hbj⟩ | ⟨j, hbj⟩
    · -- `b = r j`
      have hℓb2 : letterAt Wc (X.length + 1) = .r j := hℓb.trans hbj
      have hℓb'2 : letterAt Wc' X.length = .r j := hℓb'.trans hbj
      have hbidx : b.idx = j := by rw [hbj]; rfl
      have hbar : b.arity = 2 := by rw [hbj]; rfl
      obtain ⟨g1, g2, gb⟩ := r_window hW hℓb2 h1 (by omega) hb1e
      have hq0 : (if bit Wc (X.length + 1) j then j + 1 else j) ≠ 0 := by split_ifs <;> omega
      obtain ⟨h4, hb4⟩ := pass_l_lt hW hℓa (k := X.length) g2 hq0 gb (by split_ifs <;> omega)
      obtain ⟨g1', g2', gb'⟩ := r_window hW' hℓb'2 he' (by omega) hbit'
      have hqq : (if bit Wc (X.length + 1) j then j + 1 else j) = (if bit Wc' X.length j then j + 1 else j) := by
        rw [bit_succ_of_lt hW hk₀ (p := j) (by omega) (by rw [hℓa]; omega), (tE j).1]
      have hcE : ExtCol X Pc2 (colOf (next hW (next hW (next hW (next hW e))))) := by
        have := (cutSlot_facts hW h4 hq0).2.2.1
        rw [block_col_false h4 hq0 hb4, cm_extCol]; omega
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y) nE0
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true h1 hp hb1e, cm_extCol]; omega)
          (not_σ_right h1 hp hb1e (fun _ hj' => by rw [hℓb2] at hj'; cases hj')))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_vertex g1, cm_extCol]; omega) (not_σ_vertex g1))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false g2 hq0 gb, Nat.add_sub_cancel, cm_extCol]; omega)
          (not_σ_left g2 hq0 gb (notσ_of_lt hℓa (by split_ifs <;> omega)))) (apassage_end hW _))))
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
        (not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega)
          (not_σ_right he' hp hbit' (fun _ hj' => by rw [hℓb'2] at hj'; cases hj')))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_vertex g1', cm_extCol']; omega) (not_σ_vertex g1'))
          (apassage_end hW' _))
      refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
      rw [hc']; apply Subtype.ext; rw [φext _ hcE, h4, g2', hqq]
    · -- `b = σ j`: the entry reaches the crossing slot; in `W'` the entry is the crossing slot
      have hℓb2 : letterAt Wc (X.length + 1) = .σ j := hℓb.trans hbj
      have hℓb'2 : letterAt Wc' X.length = .σ j := hℓb'.trans hbj
      have hbidx : b.idx = j := by rw [hbj]; rfl
      have hbar : b.arity = 2 := by rw [hbj]; rfl
      obtain ⟨-, -, hσ1, hd1, hcol1⟩ := σ_window_right hW hℓb2 h1 (by omega) hb1e
      have hint1 : IntSlot X Pc2 Y (next hW e) := ⟨hσ1, by rw [hcol1, cm_extCol]; omega⟩
      obtain ⟨-, -, hσ', hd', hcol'⟩ := σ_window_right hW' hℓb'2 he' (by omega) hbit'
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y) nE0 (apassage_end hW _)
      refine ⟨n, _, Or.inr hint1, hc, hmin, 0, e', rfl, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      rw [Function.iterate_zero, id]
      refine Eq.trans ?_ (φint _ _ hint1).symm
      obtain ⟨hdφ, -, hcφ⟩ := cmφI_to_spec X Y a b hW hW' ⟨next hW e, hint1⟩
      exact σslot_ext hW' hσ' (cmφI_to X Y a b hW hW' _).2.1 (hcol'.trans (hcφ hcol1).symm)
        (hd'.trans (hd1.symm.trans hdφ.symm))
  rcases lt_or_ge p a.idx with R3 | hpa
  · -- between the gadgets
    obtain ⟨h1, hb1e⟩ := pass_r_lt hW hℓa he hp hbit R3
    obtain ⟨h2, hb2e⟩ := pass_r_ge hW hℓb h1 hp hb1e hpb2
    obtain ⟨h1', hb1'⟩ := pass_r_ge hW' hℓb' he' hp hbit' hpb2
    obtain ⟨h2', hb2'⟩ := pass_r_lt hW' hℓa' h1' (by omega) hb1' (by rw [hidx']; omega)
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      rw [block_col_true h2 (by omega) hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega) (not_σ_right he hp hbit (notσ_of_lt hℓa R3)))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true h1 hp hb1e, cm_extCol]; omega)
        (not_σ_right h1 hp hb1e (notσ_of_ge hℓb hpb2))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega) (not_σ_right he' hp hbit' (notσ_of_ge hℓb' hpb2)))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb1', cm_extCol']; omega)
        (not_σ_right h1' (by omega) hb1' (notσ_of_lt hℓa' (by rw [hidx']; omega)))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  rcases lt_or_ge p (a.idx + a.arity) with R4 | R5
  · -- the read window of `a`
    obtain ⟨h1', hb1'⟩ := pass_r_ge hW' hℓb' he' hp hbit' (by omega)
    have nE0' : ¬ ActE X Pc2' Y e' :=
      not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega) (not_σ_right he' hp hbit' (notσ_of_ge hℓb' (by omega)))
    rcases kind_of_arity (ℓ := a) (by omega) with ⟨i, hai⟩ | ⟨i, hai⟩
    · -- `a = r i`
      have hℓa2 : letterAt Wc X.length = .r i := hℓa.trans hai
      have hℓa'2 : letterAt Wc' (X.length + 1) = .r (a.idx + b.coarity - b.arity) := hℓa'.trans (by rw [hai]; rfl)
      have haidx : a.idx = i := by rw [hai]; rfl
      have haar : a.arity = 2 := by rw [hai]; rfl
      obtain ⟨g1, g2, gb⟩ := r_window hW hℓa2 he (by omega) hbit
      have hq0 : (if bit Wc X.length i then i + 1 else i) ≠ 0 := by split_ifs <;> omega
      have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
        have := (cutSlot_facts hW g2 hq0).2.2.1
        rw [block_col_false g2 hq0 gb, cm_extCol]; omega
      obtain ⟨g1', g2', gb'⟩ := r_window hW' hℓa'2 h1' (by omega) hb1'
      have hq0' : (if bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) then a.idx + b.coarity - b.arity + 1
          else a.idx + b.coarity - b.arity) ≠ 0 := by split_ifs <;> omega
      obtain ⟨h4', hb4'⟩ := pass_l_ge hW' hℓb' (k := X.length) g2' hq0' gb' (by split_ifs <;> omega)
      have t1 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = bit Wc X.length i := by
        have := bit_succ_of_ge hW' hk₀' (p := a.idx) (by rw [hℓb']; exact hab)
        rw [hℓb'] at this
        rw [this, ← (tE a.idx).1, haidx]
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
        (not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega)
          (not_σ_right he hp hbit (fun _ hj' => by rw [hℓa2] at hj'; cases hj')))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_vertex g1, cm_extCol]; omega) (not_σ_vertex g1))
          (apassage_end hW _))
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y) nE0'
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb1', cm_extCol']; omega)
          (not_σ_right h1' (by omega) hb1' (fun _ hj' => by rw [hℓa'2] at hj'; cases hj')))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_vertex g1', cm_extCol']; omega) (not_σ_vertex g1'))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false g2' hq0' gb', Nat.add_sub_cancel, cm_extCol']; omega)
          (not_σ_left g2' hq0' gb' (notσ_of_ge' hℓb' (by split_ifs <;> omega)))) (apassage_end hW' _))))
      refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
      rw [hc']; apply Subtype.ext; rw [φext _ hcE, g2, h4', t1]
      simp only [Prod.mk.injEq, true_and]
      split_ifs <;> omega
    · -- `a = σ i`: the entry is the crossing slot; in `W'` it reaches the crossing slot in one step
      have hℓa2 : letterAt Wc X.length = .σ i := hℓa.trans hai
      have hℓa'2 : letterAt Wc' (X.length + 1) = .σ (a.idx + b.coarity - b.arity) := hℓa'.trans (by rw [hai]; rfl)
      have haidx : a.idx = i := by rw [hai]; rfl
      have haar : a.arity = 2 := by rw [hai]; rfl
      obtain ⟨-, -, hσe, hde, hcole⟩ := σ_window_right hW hℓa2 he (by omega) hbit
      have hinte : IntSlot X Pc2 Y e := ⟨hσe, by rw [hcole, cm_extCol]; omega⟩
      obtain ⟨-, -, hσ1', hd1', hcol1'⟩ := σ_window_right hW' hℓa'2 h1' (by omega) hb1'
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y) nE0' (apassage_end hW' _)
      refine ⟨0, e, Or.inr hinte, rfl, fun _ h => absurd h (Nat.not_lt_zero _), n', e', rfl, ?_, hmin'⟩
      rw [hc']
      refine Eq.trans ?_ (φint _ _ hinte).symm
      obtain ⟨hdφ, hcφ, -⟩ := cmφI_to_spec X Y a b hW hW' ⟨e, hinte⟩
      refine σslot_ext hW' hσ1' (cmφI_to X Y a b hW hW' _).2.1 (hcol1'.trans (hcφ hcole).symm) ?_
      rw [hd1', hdφ, hde]
      exact decide_eq_decide.2 (by omega)
  · -- below both gadgets
    obtain ⟨h1, hb1e⟩ := pass_r_ge hW hℓa he hp hbit R5
    obtain ⟨h2, hb2e⟩ := pass_r_ge hW hℓb h1 (by omega) hb1e (by omega)
    obtain ⟨h1', hb1'⟩ := pass_r_ge hW' hℓb' he' hp hbit' (by omega)
    obtain ⟨h2', hb2'⟩ := pass_r_ge hW' hℓa' h1' (by omega) hb1' (by rw [hidx', har']; omega)
    rw [hco', har'] at h2' hb2'
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      rw [block_col_true h2 (by omega) hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_true he hp hbit, cm_extCol]; omega) (not_σ_right he hp hbit (notσ_of_ge hℓa R5)))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true h1 (by omega) hb1e, cm_extCol]; omega)
        (not_σ_right h1 (by omega) hb1e (notσ_of_ge hℓb (by omega)))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_true he' hp hbit', cm_extCol']; omega) (not_σ_right he' hp hbit' (notσ_of_ge hℓb' (by omega))))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb1', cm_extCol']; omega)
        (not_σ_right h1' (by omega) hb1' (notσ_of_ge hℓa' (by rw [hidx', har']; omega)))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
    simp only [Prod.mk.injEq, true_and]; omega

end CommEntries

section CommEntriesRight

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

local notation "φc" => φA X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW (cmφI X Y a b hW hW')

include hab hW hW' in
/-- the entries of the commutation block from the right -/
theorem cm_right (e : Slot Wc) (hext : IsExtSlot X Pc2 e.1) {q : ℕ} (he : e.1 = (X.length + 2, q)) (hq : q ≠ 0)
    (hbit : bit Wc (X.length + 2) q = false) :
    ∃ (m : ℕ) (c : Slot Wc) (hc : ActE X Pc2 Y c), (next hW)^[m] e = c ∧
      (∀ i < m, ¬ ActE X Pc2 Y ((next hW)^[i] e)) ∧
      ∃ (m' : ℕ) (b' : Slot Wc'), b'.1 = extPair X Pc2 Pc2' e.1 ∧
        (next hW')^[m'] b' = (φc ⟨c, hc⟩).1 ∧ ∀ i < m', ¬ ActE X Pc2' Y ((next hW')^[i] b') := by
  have hE := cm_sameEffect X Y a b hab hW
  have hPne := cm_Pne a b
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  have hk₀ := cm_k₀ X Y a b
  have hk₁ := cm_k₁ X Y a b
  have hk₀' := cm_k₀' X Y a b
  have hk₁' := cm_k₁' X Y a b
  have ha1 := cm_a_pos X Y a b hW
  have hb1 := cm_b_pos X Y a b hW'
  have tE := cm_bits_ext X Y a b hab hW
  have hidx' : (a.reindex (a.idx + b.coarity - b.arity)).idx = a.idx + b.coarity - b.arity := idx_reindex a _
  have har' := arity_reindex a (a.idx + b.coarity - b.arity)
  have hco' := coarity_reindex a (a.idx + b.coarity - b.arity)
  let e' : Slot Wc' := ⟨extPair X Pc2 Pc2' e.1, isSlot_ext X Pc2 Y Pc2' hPne hE e.2 hext⟩
  have he' : e'.1 = (X.length + 2, q) := by
    show extPair X Pc2 Pc2' e.1 = _
    rw [he, cm_extPair X a b (Or.inr le_rfl)]
  have he2 : e.1 = (X.length + 1 + 1, q) := he
  have he2' : e'.1 = (X.length + 1 + 1, q) := he'
  have hbit' : bit Wc' (X.length + 2) q = false := by rw [← (tE q).2]; exact hbit
  have φext := cm_φext X Y a b hab hW hW'
  have φint := cm_φint X Y a b hab hW hW'
  rcases lt_or_ge q b.idx with R1 | hqb
  · -- above both gadgets
    obtain ⟨h1, hb1e⟩ := pass_l_lt hW hℓb he2 hq hbit R1
    obtain ⟨h2, hb2e⟩ := pass_l_lt hW hℓa h1 hq hb1e (by omega)
    obtain ⟨h1', hb1'⟩ := pass_l_lt hW' hℓa' he2' hq hbit' (by rw [hidx']; omega)
    obtain ⟨h2', hb2'⟩ := pass_l_lt hW' hℓb' h1' hq hb1' R1
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      have := (cutSlot_facts hW h2 hq).2.2.1
      rw [block_col_false h2 hq hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left he2 hq hbit (notσ_of_lt hℓb R1)))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false h1 hq hb1e, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left h1 hq hb1e (notσ_of_lt hℓa (by omega)))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left he2' hq hbit' (notσ_of_lt hℓa' (by rw [hidx']; omega))))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false h1' hq hb1', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left h1' hq hb1' (notσ_of_lt hℓb' R1))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  rcases lt_or_ge q (b.idx + b.coarity) with R2 | hqb2
  · -- the write window of `b`
    have hqn : q < a.idx + b.coarity - b.arity := by omega
    obtain ⟨h1', hb1'⟩ := pass_l_lt hW' hℓa' he2' hq hbit' (by rw [hidx']; exact hqn)
    have nE0' : ¬ ActE X Pc2' Y e' :=
      not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left he2' hq hbit' (notσ_of_lt hℓa' (by rw [hidx']; exact hqn)))
    rcases kind_of_coarity (ℓ := b) (by omega) with ⟨j, d, hbj⟩ | ⟨j, hbj⟩
    · -- `b = l j d`
      have hℓb2 : letterAt Wc (X.length + 1) = .l j d := hℓb.trans hbj
      have hℓb'2 : letterAt Wc' X.length = .l j d := hℓb'.trans hbj
      have hbidx : b.idx = j := by rw [hbj]; rfl
      have hbco : b.coarity = 2 := by rw [hbj]; rfl
      obtain ⟨g1, g2, gb⟩ := l_window hW hℓb2 hk₁ he2 (by omega) hbit
      have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
        rw [block_col_true g2 (by split_ifs <;> omega) gb, cm_extCol]; omega
      obtain ⟨g1', g2', gb'⟩ := l_window hW' hℓb'2 hk₀' h1' (by omega) hb1'
      obtain ⟨h4', hb4'⟩ := pass_r_lt hW' hℓa' g2' (by split_ifs <;> omega) gb' (by rw [hidx']; split_ifs <;> omega)
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
        (not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
          (not_σ_left he2 hq hbit (fun _ hj' => by rw [hℓb2] at hj'; cases hj')))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_vertex g1, cm_extCol]; omega) (not_σ_vertex g1))
          (apassage_end hW _))
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y) nE0'
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false h1' hq hb1', Nat.add_sub_cancel, cm_extCol']; omega)
          (not_σ_left h1' hq hb1' (fun _ hj' => by rw [hℓb'2] at hj'; cases hj')))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_vertex g1', cm_extCol']; omega) (not_σ_vertex g1'))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_true g2' (by split_ifs <;> omega) gb', cm_extCol']; omega)
          (not_σ_right g2' (by split_ifs <;> omega) gb' (notσ_of_lt hℓa' (by rw [hidx']; split_ifs <;> omega))))
          (apassage_end hW' _))))
      refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
      rw [hc']; apply Subtype.ext; rw [φext _ hcE, g2, h4']
    · -- `b = σ j`: the entry is the crossing slot; in `W'` it reaches the crossing slot in one step
      have hℓb2 : letterAt Wc (X.length + 1) = .σ j := hℓb.trans hbj
      have hℓb'2 : letterAt Wc' X.length = .σ j := hℓb'.trans hbj
      have hbidx : b.idx = j := by rw [hbj]; rfl
      have hbco : b.coarity = 2 := by rw [hbj]; rfl
      obtain ⟨-, -, hσe, hde, hcole⟩ := σ_window_left hW hℓb2 he2 (by omega) hbit
      have hinte : IntSlot X Pc2 Y e := ⟨hσe, by rw [hcole, cm_extCol]; omega⟩
      obtain ⟨-, -, hσ1', hd1', hcol1'⟩ := σ_window_left hW' hℓb'2 h1' (by omega) hb1'
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y) nE0' (apassage_end hW' _)
      refine ⟨0, e, Or.inr hinte, rfl, fun _ h => absurd h (Nat.not_lt_zero _), n', e', rfl, ?_, hmin'⟩
      rw [hc']
      refine Eq.trans ?_ (φint _ _ hinte).symm
      obtain ⟨hdφ, -, hcφ⟩ := cmφI_to_spec X Y a b hW hW' ⟨e, hinte⟩
      exact σslot_ext hW' hσ1' (cmφI_to X Y a b hW hW' _).2.1 (hcol1'.trans (hcφ hcole).symm)
        (hd1'.trans (hde.symm.trans hdφ.symm))
  rcases lt_or_ge q (a.idx + b.coarity - b.arity) with R3 | hqn
  · -- between the gadgets
    obtain ⟨h1, hb1e⟩ := pass_l_ge hW hℓb he2 hq hbit hqb2
    obtain ⟨h2, hb2e⟩ := pass_l_lt hW hℓa h1 (by omega) hb1e (by omega)
    obtain ⟨h1', hb1'⟩ := pass_l_lt hW' hℓa' he2' hq hbit' (by rw [hidx']; exact R3)
    obtain ⟨h2', hb2'⟩ := pass_l_ge hW' hℓb' h1' hq hb1' hqb2
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      have := (cutSlot_facts hW h2 (by omega)).2.2.1
      rw [block_col_false h2 (by omega) hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left he2 hq hbit (notσ_of_ge' hℓb hqb2)))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hb1e, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left h1 (by omega) hb1e (notσ_of_lt hℓa (by omega)))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left he2' hq hbit' (notσ_of_lt hℓa' (by rw [hidx']; exact R3))))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false h1' hq hb1', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left h1' hq hb1' (notσ_of_ge' hℓb' hqb2))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
  rcases lt_or_ge q (a.idx + b.coarity - b.arity + a.coarity) with R4 | R5
  · -- the write window of `a`
    obtain ⟨h1, hb1e⟩ := pass_l_ge hW hℓb he2 hq hbit (by omega)
    have nE0 : ¬ ActE X Pc2 Y e :=
      not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left he2 hq hbit (notσ_of_ge' hℓb (by omega)))
    rcases kind_of_coarity (ℓ := a) (by omega) with ⟨i, d, hai⟩ | ⟨i, hai⟩
    · -- `a = l i d`
      have hℓa2 : letterAt Wc X.length = .l i d := hℓa.trans hai
      have hℓa'2 : letterAt Wc' (X.length + 1) = .l (a.idx + b.coarity - b.arity) d := hℓa'.trans (by rw [hai]; rfl)
      have haidx : a.idx = i := by rw [hai]; rfl
      have haco : a.coarity = 2 := by rw [hai]; rfl
      obtain ⟨g1, g2, gb⟩ := l_window hW hℓa2 hk₀ h1 (by omega) hb1e
      obtain ⟨h4, hb4⟩ := pass_r_ge hW hℓb g2 (by split_ifs <;> omega) gb (by split_ifs <;> omega)
      have hcE : ExtCol X Pc2 (colOf (next hW (next hW (next hW (next hW e))))) := by
        rw [block_col_true h4 (by split_ifs <;> omega) hb4, cm_extCol]; omega
      obtain ⟨g1', g2', gb'⟩ := l_window hW' hℓa'2 hk₁' he2' (by omega) hbit'
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y) nE0
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hb1e, Nat.add_sub_cancel, cm_extCol]; omega)
          (not_σ_left h1 (by omega) hb1e (fun _ hj' => by rw [hℓa2] at hj'; cases hj')))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_vertex g1, cm_extCol]; omega) (not_σ_vertex g1))
        (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_true g2 (by split_ifs <;> omega) gb, cm_extCol]; omega)
          (not_σ_right g2 (by split_ifs <;> omega) gb (notσ_of_ge hℓb (by split_ifs <;> omega)))) (apassage_end hW _))))
      obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
        (not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
          (not_σ_left he2' hq hbit' (fun _ hj' => by rw [hℓa'2] at hj'; cases hj')))
        (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_vertex g1', cm_extCol']; omega) (not_σ_vertex g1'))
          (apassage_end hW' _))
      refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
      rw [hc']; apply Subtype.ext; rw [φext _ hcE, h4, g2']
      simp only [Prod.mk.injEq, true_and]
      cases d <;> simp <;> omega
    · -- `a = σ i`: reaches the crossing slot in one step; in `W'` the entry is the crossing slot
      have hℓa2 : letterAt Wc X.length = .σ i := hℓa.trans hai
      have hℓa'2 : letterAt Wc' (X.length + 1) = .σ (a.idx + b.coarity - b.arity) := hℓa'.trans (by rw [hai]; rfl)
      have haidx : a.idx = i := by rw [hai]; rfl
      have haco : a.coarity = 2 := by rw [hai]; rfl
      have haar : a.arity = 2 := by rw [hai]; rfl
      obtain ⟨-, -, hσ1, hd1, hcol1⟩ := σ_window_left hW hℓa2 h1 (by omega) hb1e
      have hint1 : IntSlot X Pc2 Y (next hW e) := ⟨hσ1, by rw [hcol1, cm_extCol]; omega⟩
      obtain ⟨-, -, hσ', hd', hcol'⟩ := σ_window_left hW' hℓa'2 he2' (by omega) hbit'
      obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y) nE0 (apassage_end hW _)
      refine ⟨n, _, Or.inr hint1, hc, hmin, 0, e', rfl, ?_, fun _ h => absurd h (Nat.not_lt_zero _)⟩
      rw [Function.iterate_zero, id]
      refine Eq.trans ?_ (φint _ _ hint1).symm
      obtain ⟨hdφ, hcφ, -⟩ := cmφI_to_spec X Y a b hW hW' ⟨next hW e, hint1⟩
      refine σslot_ext hW' hσ' (cmφI_to X Y a b hW hW' _).2.1 (hcol'.trans (hcφ hcol1).symm) ?_
      rw [hd', hdφ, hd1]
      exact decide_eq_decide.2 (by omega)
  · -- below both gadgets
    obtain ⟨h1, hb1e⟩ := pass_l_ge hW hℓb he2 hq hbit (by omega)
    obtain ⟨h2, hb2e⟩ := pass_l_ge hW hℓa h1 (by omega) hb1e (by omega)
    obtain ⟨h1', hb1'⟩ := pass_l_ge hW' hℓa' he2' hq hbit' (by rw [hidx', hco']; exact R5)
    rw [har', hco'] at h1' hb1'
    obtain ⟨h2', hb2'⟩ := pass_l_ge hW' hℓb' h1' (by omega) hb1' (by omega)
    have hcE : ExtCol X Pc2 (colOf (next hW (next hW e))) := by
      have := (cutSlot_facts hW h2 (by omega)).2.2.1
      rw [block_col_false h2 (by omega) hb2e, cm_extCol]; omega
    obtain ⟨n, hc, hmin⟩ := apassage_step hW (ActE X Pc2 Y)
      (not_actE_of X Pc2 Y (by rw [block_col_false he2 hq hbit, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left he2 hq hbit (notσ_of_ge' hℓb (by omega))))
      (apassage_step hW _ (not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hb1e, Nat.add_sub_cancel, cm_extCol]; omega)
        (not_σ_left h1 (by omega) hb1e (notσ_of_ge' hℓa (by omega)))) (apassage_end hW _))
    obtain ⟨n', hc', hmin'⟩ := apassage_step hW' (ActE X Pc2' Y)
      (not_actE_of X Pc2' Y (by rw [block_col_false he2' hq hbit', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left he2' hq hbit' (notσ_of_ge' hℓa' (by rw [hidx', hco']; exact R5))))
      (apassage_step hW' _ (not_actE_of X Pc2' Y (by rw [block_col_false h1' (by omega) hb1', Nat.add_sub_cancel, cm_extCol']; omega)
        (not_σ_left h1' (by omega) hb1' (notσ_of_ge' hℓb' (by omega)))) (apassage_end hW' _))
    refine ⟨n, _, Or.inl hcE, hc, hmin, n', e', rfl, ?_, hmin'⟩
    rw [hc']; apply Subtype.ext; rw [φext _ hcE, h2, h2']
    simp only [Prod.mk.injEq, true_and]; omega

end CommEntriesRight

section CommInterior

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

local notation "φc" => φA X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW (cmφI X Y a b hW hW')

include hab hW hW' in
/-- the interior `σ` slots of the commutation block -/
theorem cm_interior (u : Slot Wc) (hu : IntSlot X Pc2 Y u) :
    ∃ (m : ℕ) (_ : 0 < m) (c : Slot Wc) (hc : ActE X Pc2 Y c), (next hW)^[m] u = c ∧
      (∀ i, 0 < i → i < m → ¬ ActE X Pc2 Y ((next hW)^[i] u)) ∧
      ∃ (m' : ℕ), 0 < m' ∧ (next hW')^[m'] (cmφI X Y a b hW hW' ⟨u, hu⟩).1 = (φc ⟨c, hc⟩).1 ∧
        ∀ i, 0 < i → i < m' → ¬ ActE X Pc2' Y ((next hW')^[i] (cmφI X Y a b hW hW' ⟨u, hu⟩).1) := by
  have hE := cm_sameEffect X Y a b hab hW
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  have hk₀ := cm_k₀ X Y a b
  have hk₁ := cm_k₁ X Y a b
  have hk₀' := cm_k₀' X Y a b
  have hk₁' := cm_k₁' X Y a b
  have ha1 := cm_a_pos X Y a b hW
  have hb1 := cm_b_pos X Y a b hW'
  have tE := cm_bits_ext X Y a b hab hW
  have hidx' : (a.reindex (a.idx + b.coarity - b.arity)).idx = a.idx + b.coarity - b.arity := idx_reindex a _
  have har' := arity_reindex a (a.idx + b.coarity - b.arity)
  have hco' := coarity_reindex a (a.idx + b.coarity - b.arity)
  have φext := cm_φext X Y a b hab hW hW'
  obtain ⟨hσ, hc⟩ := (cm_int_iff X Y a b hW u).1 hu
  rw [cmφI_val]
  obtain ⟨hdφ, hcφ0, hcφ1⟩ := cmφI_to_spec X Y a b hW hW' ⟨u, hu⟩
  rcases hc with hc | hc
  · -- a crossing letter `a`
    have hcr : a.isCrossing = true := by have := hσ.1; rwa [hc, hℓa] at this
    have hai : a = .σ a.idx := eq_σ_of_crossing hcr
    have hℓa2 : letterAt Wc X.length = .σ a.idx := hℓa.trans hai
    have hℓa'2 : letterAt Wc' (X.length + 1) = .σ (a.idx + b.coarity - b.arity) := hℓa'.trans (by rw [hai]; rfl)
    have haar : a.arity = 2 := arity_of_crossing hcr
    have haco : a.coarity = 2 := coarity_of_crossing hcr
    obtain ⟨-, -, -, b1, b2⟩ := σ_facts hW hk₀ hℓa2
    obtain ⟨-, -, -, b1', b2'⟩ := σ_facts hW' hk₁' hℓa'2
    have t1 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = bit Wc X.length a.idx := by
      have := bit_succ_of_ge hW' hk₀' (p := a.idx) (by rw [hℓb']; exact hab)
      rw [hℓb'] at this; rw [this, (tE a.idx).1]
    have t2 : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity + 1) = bit Wc X.length (a.idx + 1) := by
      have := bit_succ_of_ge hW' hk₀' (p := a.idx + 1) (by rw [hℓb']; omega)
      rw [hℓb'] at this
      rw [show a.idx + b.coarity - b.arity + 1 = a.idx + 1 + b.coarity - b.arity by omega, this, (tE (a.idx + 1)).1]
    have hcol1 : colOf (cmφI_to X Y a b hW hW' ⟨u, hu⟩).1 = X.length + 1 := hcφ0 hc
    have hcr' : (letterAt Wc' (X.length + 1)).isCrossing = true := by rw [hℓa', isCrossing_reindex]; exact hcr
    rw [cmφI_to_val₀ X Y a b hW hW' ⟨u, hu⟩ hc hcr']
    rcases eq_σSlotA_or_σSlotB hW hσ with huA | huB
    · -- the descending slot of `a`
      have hu1 : u.1 = if bit Wc X.length a.idx then (X.length, a.idx) else (X.length + 1, a.idx + 1) := by
        rw [huA, σSlotA_congr hW _ hk₀ _ hℓa2 hc, σSlotA_val]
      have hdu : isDesc u = true := by rw [huA]; exact isDesc_σSlotA hW _ _
      simp only [hdu, ↓reduceIte]
      rw [σSlotA_congr hW' hk₁' hk₁' (letterAt_σ_of_isCrossing hcr') hℓa'2 rfl]
      cases hba : bit Wc X.length a.idx
      · -- the leftward crossing strand: `(|X|+1, a.idx+1)` heading left
        rw [hba] at hu1; simp only [Bool.false_eq_true, ↓reduceIte] at hu1
        have hb1u : bit Wc (X.length + 1) (a.idx + 1) = false := by rw [b1, hba]
        have h1 := next_σ_left_succ hW hℓa2 hu1 hb1u
        have hcE : ExtCol X Pc2 (colOf (next hW u)) := by
          have := (cutSlot_facts hW h1 (by omega)).2.2.1
          rw [block_col_false h1 (by omega) (by rw [← b1, hb1u]), cm_extCol]; omega
        -- `W'`: `(|X|+2, n+1)` heading left, through the crossing, then below `b`
        have hs' : (σSlotA hW' hk₁' hℓa'2).1 = (X.length + 1 + 1, a.idx + b.coarity - b.arity + 1) := by
          rw [σSlotA_val, t1, hba]; rfl
        have hb1' : bit Wc' (X.length + 1 + 1) (a.idx + b.coarity - b.arity + 1) = false := by rw [b1', t1, hba]
        have h1' := next_σ_left_succ hW' hℓa'2 hs' hb1'
        have hb2' : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = false := by rw [t1, hba]
        obtain ⟨h2', hb2e⟩ := pass_l_ge hW' hℓb' (k := X.length) h1' (by omega) hb2' (by omega)
        refine ⟨1, one_pos, _, Or.inl hcE, rfl, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
          2, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [φext _ hcE, h1]
          show (next hW' (next hW' (σSlotA hW' hk₁' hℓa'2))).1 = _
          rw [h2']; simp only [Prod.mk.injEq, true_and]; omega
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2' Y (next hW' (σSlotA hW' hk₁' hℓa'2))
          exact not_actE_of X Pc2' Y (by rw [block_col_false h1' (by omega) hb2', Nat.add_sub_cancel, cm_extCol']; omega)
            (not_σ_left h1' (by omega) hb2' (notσ_of_ge' hℓb' (by omega)))
      · -- the rightward crossing strand: `(|X|, a.idx)` heading right
        rw [hba] at hu1; simp only [↓reduceIte] at hu1
        have h1 := next_σ_right_idx hW hℓa2 hu1 hba
        have hb1u : bit Wc (X.length + 1) (a.idx + 1) = true := by rw [b1, hba]
        obtain ⟨h2, hb2e⟩ := pass_r_ge hW hℓb h1 (by omega) hb1u (by omega)
        have hcE : ExtCol X Pc2 (colOf (next hW (next hW u))) := by
          rw [block_col_true h2 (by omega) hb2e, cm_extCol]; omega
        have hs' : (σSlotA hW' hk₁' hℓa'2).1 = (X.length + 1, a.idx + b.coarity - b.arity) := by
          rw [σSlotA_val, t1, hba]; rfl
        have hb1' : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity) = true := by rw [t1, hba]
        have h1' := next_σ_right_idx hW' hℓa'2 hs' hb1'
        refine ⟨2, by omega, _, Or.inl hcE, rfl, ?_, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2 Y (next hW u)
          exact not_actE_of X Pc2 Y (by rw [block_col_true h1 (by omega) hb1u, cm_extCol]; omega)
            (not_σ_right h1 (by omega) hb1u (notσ_of_ge hℓb (by omega)))
        · apply Subtype.ext
          rw [φext _ hcE, h2]
          show (next hW' (σSlotA hW' hk₁' hℓa'2)).1 = _
          rw [h1']; simp only [Prod.mk.injEq, true_and]; omega
    · -- the ascending slot of `a`
      have hu1 : u.1 = if bit Wc X.length (a.idx + 1) then (X.length, a.idx + 1) else (X.length + 1, a.idx) := by
        rw [huB, σSlotB_congr hW _ hk₀ _ hℓa2 hc, σSlotB_val]
      have hdu : isDesc u = false := by rw [huB]; exact isDesc_σSlotB hW _ _
      simp only [hdu, Bool.false_eq_true, ↓reduceIte]
      rw [σSlotB_congr hW' hk₁' hk₁' (letterAt_σ_of_isCrossing hcr') hℓa'2 rfl]
      cases hba : bit Wc X.length (a.idx + 1)
      · -- `(|X|+1, a.idx)` heading left
        rw [hba] at hu1; simp only [Bool.false_eq_true, ↓reduceIte] at hu1
        have hb1u : bit Wc (X.length + 1) a.idx = false := by rw [b2, hba]
        have h1 := next_σ_left_idx hW hℓa2 hu1 hb1u
        have hcE : ExtCol X Pc2 (colOf (next hW u)) := by
          have := (cutSlot_facts hW h1 (by omega)).2.2.1
          rw [block_col_false h1 (by omega) (by rw [← b2, hb1u]), cm_extCol]; omega
        have hs' : (σSlotB hW' hk₁' hℓa'2).1 = (X.length + 1 + 1, a.idx + b.coarity - b.arity) := by
          rw [σSlotB_val, t2, hba]; rfl
        have hb1' : bit Wc' (X.length + 1 + 1) (a.idx + b.coarity - b.arity) = false := by rw [b2', t2, hba]
        have h1' := next_σ_left_idx hW' hℓa'2 hs' hb1'
        have hb2' : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity + 1) = false := by rw [t2, hba]
        obtain ⟨h2', hb2e⟩ := pass_l_ge hW' hℓb' (k := X.length) h1' (by omega) hb2' (by omega)
        refine ⟨1, one_pos, _, Or.inl hcE, rfl, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
          2, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [φext _ hcE, h1]
          show (next hW' (next hW' (σSlotB hW' hk₁' hℓa'2))).1 = _
          rw [h2']; simp only [Prod.mk.injEq, true_and]; omega
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2' Y (next hW' (σSlotB hW' hk₁' hℓa'2))
          exact not_actE_of X Pc2' Y (by rw [block_col_false h1' (by omega) hb2', Nat.add_sub_cancel, cm_extCol']; omega)
            (not_σ_left h1' (by omega) hb2' (notσ_of_ge' hℓb' (by omega)))
      · -- `(|X|, a.idx+1)` heading right
        rw [hba] at hu1; simp only [↓reduceIte] at hu1
        have h1 := next_σ_right_succ hW hℓa2 hu1 hba
        have hb1u : bit Wc (X.length + 1) a.idx = true := by rw [b2, hba]
        obtain ⟨h2, hb2e⟩ := pass_r_ge hW hℓb h1 (by omega) hb1u (by omega)
        have hcE : ExtCol X Pc2 (colOf (next hW (next hW u))) := by
          rw [block_col_true h2 (by omega) hb2e, cm_extCol]; omega
        have hs' : (σSlotB hW' hk₁' hℓa'2).1 = (X.length + 1, a.idx + b.coarity - b.arity + 1) := by
          rw [σSlotB_val, t2, hba]; rfl
        have hb1' : bit Wc' (X.length + 1) (a.idx + b.coarity - b.arity + 1) = true := by rw [t2, hba]
        have h1' := next_σ_right_succ hW' hℓa'2 hs' hb1'
        refine ⟨2, by omega, _, Or.inl hcE, rfl, ?_, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2 Y (next hW u)
          exact not_actE_of X Pc2 Y (by rw [block_col_true h1 (by omega) hb1u, cm_extCol]; omega)
            (not_σ_right h1 (by omega) hb1u (notσ_of_ge hℓb (by omega)))
        · apply Subtype.ext
          rw [φext _ hcE, h2]
          show (next hW' (σSlotB hW' hk₁' hℓa'2)).1 = _
          rw [h1']
  · -- a crossing letter `b`
    have hcr : b.isCrossing = true := by have := hσ.1; rwa [hc, hℓb] at this
    have hbj : b = .σ b.idx := eq_σ_of_crossing hcr
    have hℓb2 : letterAt Wc (X.length + 1) = .σ b.idx := hℓb.trans hbj
    have hℓb'2 : letterAt Wc' X.length = .σ b.idx := hℓb'.trans hbj
    have hbar : b.arity = 2 := arity_of_crossing hcr
    have hbco : b.coarity = 2 := coarity_of_crossing hcr
    obtain ⟨-, -, -, b1, b2⟩ := σ_facts hW hk₁ hℓb2
    obtain ⟨-, -, -, b1', b2'⟩ := σ_facts hW' hk₀' hℓb'2
    have t1 : bit Wc' X.length b.idx = bit Wc (X.length + 1) b.idx := by
      rw [← (tE b.idx).1, bit_succ_of_lt hW hk₀ (p := b.idx) hb1 (by rw [hℓa]; omega)]
    have t2 : bit Wc' X.length (b.idx + 1) = bit Wc (X.length + 1) (b.idx + 1) := by
      rw [← (tE (b.idx + 1)).1, bit_succ_of_lt hW hk₀ (p := b.idx + 1) (by omega) (by rw [hℓa]; omega)]
    have hcr' : (letterAt Wc' X.length).isCrossing = true := by rw [hℓb']; exact hcr
    rw [cmφI_to_val₁ X Y a b hW hW' ⟨u, hu⟩ hc hcr']
    rcases eq_σSlotA_or_σSlotB hW hσ with huA | huB
    · have hu1 : u.1 = if bit Wc (X.length + 1) b.idx then (X.length + 1, b.idx) else (X.length + 1 + 1, b.idx + 1) := by
        rw [huA, σSlotA_congr hW _ hk₁ _ hℓb2 hc, σSlotA_val]
      have hdu : isDesc u = true := by rw [huA]; exact isDesc_σSlotA hW _ _
      simp only [hdu, ↓reduceIte]
      rw [σSlotA_congr hW' hk₀' hk₀' (letterAt_σ_of_isCrossing hcr') hℓb'2 rfl]
      cases hbb : bit Wc (X.length + 1) b.idx
      · -- `(|X|+2, b.idx+1)` heading left
        rw [hbb] at hu1; simp only [Bool.false_eq_true, ↓reduceIte] at hu1
        have hb1u : bit Wc (X.length + 1 + 1) (b.idx + 1) = false := by rw [b1, hbb]
        have h1 := next_σ_left_succ hW hℓb2 hu1 hb1u
        obtain ⟨h2, hb2e⟩ := pass_l_lt hW hℓa (k := X.length) h1 (by omega) hbb (by omega)
        have hcE : ExtCol X Pc2 (colOf (next hW (next hW u))) := by
          have := (cutSlot_facts hW h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2e, cm_extCol]; omega
        have hs' : (σSlotA hW' hk₀' hℓb'2).1 = (X.length + 1, b.idx + 1) := by
          rw [σSlotA_val, t1, hbb]; rfl
        have hb1' : bit Wc' (X.length + 1) (b.idx + 1) = false := by rw [b1', t1, hbb]
        have h1' := next_σ_left_succ hW' hℓb'2 hs' hb1'
        have hcE' : ExtCol X Pc2' (colOf (next hW' (σSlotA hW' hk₀' hℓb'2))) := by
          have := (cutSlot_facts hW' h1' (by omega)).2.2.1
          rw [block_col_false h1' (by omega) (by rw [← b1', hb1']), cm_extCol']; omega
        refine ⟨2, by omega, _, Or.inl hcE, rfl, ?_, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2 Y (next hW u)
          exact not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hbb, Nat.add_sub_cancel, cm_extCol]; omega)
            (not_σ_left h1 (by omega) hbb (notσ_of_lt hℓa (by omega)))
        · apply Subtype.ext
          rw [φext _ hcE, h2]
          show (next hW' (σSlotA hW' hk₀' hℓb'2)).1 = _
          rw [h1']
      · -- `(|X|+1, b.idx)` heading right
        rw [hbb] at hu1; simp only [↓reduceIte] at hu1
        have h1 := next_σ_right_idx hW hℓb2 hu1 hbb
        have hcE : ExtCol X Pc2 (colOf (next hW u)) := by
          rw [block_col_true h1 (by omega) (by rw [b1, hbb]), cm_extCol]; omega
        have hs' : (σSlotA hW' hk₀' hℓb'2).1 = (X.length, b.idx) := by rw [σSlotA_val, t1, hbb]; rfl
        have hb1' : bit Wc' X.length b.idx = true := by rw [t1, hbb]
        have h1' := next_σ_right_idx hW' hℓb'2 hs' hb1'
        have hb2' : bit Wc' (X.length + 1) (b.idx + 1) = true := by rw [b1', t1, hbb]
        obtain ⟨h2', hb2e⟩ := pass_r_lt hW' hℓa' h1' (by omega) hb2' (by rw [hidx']; omega)
        refine ⟨1, one_pos, _, Or.inl hcE, rfl, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
          2, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [φext _ hcE, h1]
          show (next hW' (next hW' (σSlotA hW' hk₀' hℓb'2))).1 = _
          rw [h2']
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2' Y (next hW' (σSlotA hW' hk₀' hℓb'2))
          exact not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb2', cm_extCol']; omega)
            (not_σ_right h1' (by omega) hb2' (notσ_of_lt hℓa' (by rw [hidx']; omega)))
    · have hu1 : u.1 = if bit Wc (X.length + 1) (b.idx + 1) then (X.length + 1, b.idx + 1) else (X.length + 1 + 1, b.idx) := by
        rw [huB, σSlotB_congr hW _ hk₁ _ hℓb2 hc, σSlotB_val]
      have hdu : isDesc u = false := by rw [huB]; exact isDesc_σSlotB hW _ _
      simp only [hdu, Bool.false_eq_true, ↓reduceIte]
      rw [σSlotB_congr hW' hk₀' hk₀' (letterAt_σ_of_isCrossing hcr') hℓb'2 rfl]
      cases hbb : bit Wc (X.length + 1) (b.idx + 1)
      · -- `(|X|+2, b.idx)` heading left
        rw [hbb] at hu1; simp only [Bool.false_eq_true, ↓reduceIte] at hu1
        have hb1u : bit Wc (X.length + 1 + 1) b.idx = false := by rw [b2, hbb]
        have h1 := next_σ_left_idx hW hℓb2 hu1 hb1u
        obtain ⟨h2, hb2e⟩ := pass_l_lt hW hℓa (k := X.length) h1 (by omega) hbb (by omega)
        have hcE : ExtCol X Pc2 (colOf (next hW (next hW u))) := by
          have := (cutSlot_facts hW h2 (by omega)).2.2.1
          rw [block_col_false h2 (by omega) hb2e, cm_extCol]; omega
        have hs' : (σSlotB hW' hk₀' hℓb'2).1 = (X.length + 1, b.idx) := by
          rw [σSlotB_val, t2, hbb]; rfl
        have hb1' : bit Wc' (X.length + 1) b.idx = false := by rw [b2', t2, hbb]
        have h1' := next_σ_left_idx hW' hℓb'2 hs' hb1'
        have hcE' : ExtCol X Pc2' (colOf (next hW' (σSlotB hW' hk₀' hℓb'2))) := by
          have := (cutSlot_facts hW' h1' (by omega)).2.2.1
          rw [block_col_false h1' (by omega) (by rw [← b2', hb1']), cm_extCol']; omega
        refine ⟨2, by omega, _, Or.inl hcE, rfl, ?_, 1, one_pos, ?_,
          fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _)⟩
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2 Y (next hW u)
          exact not_actE_of X Pc2 Y (by rw [block_col_false h1 (by omega) hbb, Nat.add_sub_cancel, cm_extCol]; omega)
            (not_σ_left h1 (by omega) hbb (notσ_of_lt hℓa (by omega)))
        · apply Subtype.ext
          rw [φext _ hcE, h2]
          show (next hW' (σSlotB hW' hk₀' hℓb'2)).1 = _
          rw [h1']
      · -- `(|X|+1, b.idx+1)` heading right
        rw [hbb] at hu1; simp only [↓reduceIte] at hu1
        have h1 := next_σ_right_succ hW hℓb2 hu1 hbb
        have hcE : ExtCol X Pc2 (colOf (next hW u)) := by
          rw [block_col_true h1 (by omega) (by rw [b2, hbb]), cm_extCol]; omega
        have hs' : (σSlotB hW' hk₀' hℓb'2).1 = (X.length, b.idx + 1) := by rw [σSlotB_val, t2, hbb]; rfl
        have hb1' : bit Wc' X.length (b.idx + 1) = true := by rw [t2, hbb]
        have h1' := next_σ_right_succ hW' hℓb'2 hs' hb1'
        have hb2' : bit Wc' (X.length + 1) b.idx = true := by rw [b2', t2, hbb]
        obtain ⟨h2', hb2e⟩ := pass_r_lt hW' hℓa' h1' (by omega) hb2' (by rw [hidx']; omega)
        refine ⟨1, one_pos, _, Or.inl hcE, rfl, fun i hi him => absurd (lt_of_lt_of_le hi (Nat.lt_succ_iff.1 him)) (lt_irrefl _),
          2, by omega, ?_, ?_⟩
        · apply Subtype.ext
          rw [φext _ hcE, h1]
          show (next hW' (next hW' (σSlotB hW' hk₀' hℓb'2))).1 = _
          rw [h2']
        · intro i hi him
          have : i = 1 := by omega
          subst this
          show ¬ ActE X Pc2' Y (next hW' (σSlotB hW' hk₀' hℓb'2))
          exact not_actE_of X Pc2' Y (by rw [block_col_true h1' (by omega) hb2', cm_extCol']; omega)
            (not_σ_right h1' (by omega) hb2' (notσ_of_lt hℓa' (by rw [hidx']; omega)))

include hab hW hW' in
/-- THE EXTENDED BLOCK PASSAGE of the commutation. -/
theorem cm_intPassage :
    IntPassage X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW hW' (cmφI X Y a b hW hW') := by
  constructor
  · intro e hext hcol
    rcases (entry_iff X Pc2 Y (cm_Pne a b) hW e).1 ⟨hext, hcol⟩ with ⟨p, he, hp, hbit⟩ | ⟨p, he, hp, hbit⟩
    · exact cm_left X Y a b hab hW hW' e hext he hp hbit
    · exact cm_right X Y a b hab hW hW' e hext he hp hbit
  · exact cm_interior X Y a b hab hW hW'

end CommInterior

section CommAssembly

variable (X Y : Word) (a b : Letter)

local notation "Wc" => X ++ [a, b] ++ Y
local notation "Pc2" => [a, b]
local notation "Wc'" => X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y
local notation "Pc2'" => [b, a.reindex (a.idx + b.coarity - b.arity)]

variable (hab : b.idx + b.arity ≤ a.idx)
variable (hW : (X ++ [a, b] ++ Y).Closed) (hW' : (X ++ [b, a.reindex (a.idx + b.coarity - b.arity)] ++ Y).Closed)

local notation "φc" => φA X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW (cmφI X Y a b hW hW')

include hab hW hW' in
/-- THE COMMUTATION RECORD ISOMORPHISM on the slot records: the active supersets are the exterior pieces
together with the interior `σ` slots of the two letters, matched by `cmφI`. -/
theorem cm_slotIso :
    Nonempty (RecordIso (slotRecord hW IsσSlot (allActive hW)) (slotRecord hW' IsσSlot (allActive hW'))) := by
  obtain ⟨hℓa, hℓb⟩ := cm_letters X Y a b
  obtain ⟨hℓb', hℓa'⟩ := cm_letters' X Y a b
  refine ⟨recordIsoOfConj hW hW' (ActE X Pc2 Y) (ActE X Pc2' Y) φc
    (conj_of_intPassage X Pc2 Y Pc2' (cm_Pne a b) (cm_sameEffect X Y a b hab hW) hW hW' _
      (cm_intPassage X Y a b hab hW hW'))
    (hexit_of_comm hW (cm_extCol X a b) hℓa hℓb (Or.inl hab))
    (hexit_of_comm hW' (cm_extCol' X a b) hℓb' hℓa' (Or.inr (by rw [idx_reindex]; omega)))
    (fun _ hu => isσSlot_actE X Pc2 Y hu) (fun _ hu => isσSlot_actE X Pc2' Y hu) ?_ ?_ ?_ ?_⟩
  · -- `σ` slots correspond
    intro u
    by_cases hext : ExtPiece X Pc2 Y u.1
    · rw [φA_val_ext X Pc2 Y Pc2' _ _ hW _ u hext]
      exact isσSlot_φE_iff X Pc2 Y Pc2' _ _ hW ⟨u.1, hext⟩
    · rw [φA_val_int X Pc2 Y Pc2' _ _ hW _ u hext]
      exact iff_of_true (cmφI X Y a b hW hW' ⟨u.1, u.2.resolve_left hext⟩).2.1 (u.2.resolve_left hext).1
  · -- twins correspond
    intro u hu
    by_cases hext : ExtPiece X Pc2 Y u.1
    · have hext2 : ExtPiece X Pc2 Y (σtwin hW u.1) := extPiece_σtwin X Pc2 Y hW hu hext
      rw [φA_val_ext X Pc2 Y Pc2' _ _ hW _ _ hext2, φA_val_ext X Pc2 Y Pc2' _ _ hW _ u hext]
      exact φE_σtwin X Pc2 Y Pc2' _ _ hW hW' ⟨u.1, hext⟩ hu
    · have hint : IntSlot X Pc2 Y u.1 := u.2.resolve_left hext
      have hext2 : ¬ ExtPiece X Pc2 Y (σtwin hW u.1) := by
        show ¬ ExtCol X Pc2 (colOf _); rw [colOf_σtwin hW hu]; exact hint.2
      rw [φA_val_int X Pc2 Y Pc2' _ _ hW _ _ hext2, φA_val_int X Pc2 Y Pc2' _ _ hW _ u hext]
      exact cmφI_twin X Y a b hW hW' ⟨u.1, hint⟩
  · -- over bits
    intro u hu
    by_cases hext : ExtPiece X Pc2 Y u.1
    · rw [φA_val_ext X Pc2 Y Pc2' _ _ hW _ u hext]
      exact isDesc_φE X Pc2 Y Pc2' _ _ hW ⟨u.1, hext⟩
    · rw [φA_val_int X Pc2 Y Pc2' _ _ hW _ u hext, cmφI_val]
      exact (cmφI_to_spec X Y a b hW hW' _).1
  · -- signs
    intro u hu
    by_cases hext : ExtPiece X Pc2 Y u.1
    · rw [φA_val_ext X Pc2 Y Pc2' _ _ hW _ u hext]
      exact σsgn_φE X Pc2 Y Pc2' _ _ hW ⟨u.1, hext⟩
    · rw [φA_val_int X Pc2 Y Pc2' _ _ hW _ u hext]
      exact cmφI_sgn X Y a b hab hW hW' ⟨u.1, u.2.resolve_left hext⟩

include hab in
/-- the commutation (above case) on the named records of the realizations -/
theorem cm_recordIso_above (W W' : OWord) (hWeq : W.letters = Wc) (hW'eq : W'.letters = Wc') :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  have hne : W.letters ≠ [] := by rw [hWeq]; simp
  have hne' : W'.letters ≠ [] := by rw [hW'eq]; simp
  obtain ⟨L, hL⟩ := W
  obtain ⟨L', hL'⟩ := W'
  simp only at hWeq hW'eq hne hne'
  subst hWeq hW'eq
  obtain ⟨κ⟩ := cm_slotIso X Y a b hab hL hL'
  exact ⟨(realizeRecordIso ⟨_, hL⟩ hne).trans (κ.trans (realizeRecordIso ⟨_, hL'⟩ hne').symm)⟩

end CommAssembly

end U3


/-! ### L-rec (unit U3, on the record core U2) — named-record isomorphisms (rp:record-polynomial
`presentations`, lp:split-circle in record form `P_addFree`, the accepted smoothing gate
`exists_smoothing_record_visit`).  Record of a realization: visits = the two slots of each `σ` letter,
successor = the next `σ` slot along the slot cycle `next` (`toSlot_succ`, `crossingParam_eq_half`), twin = the
other slot of the column, over = the descending strand (`overStrand_crossingOf`), sign = `sign_crossingOf`;
exterior slots of two words correspond by the index shift (`shiftIdx`, `next_ext`). -/

/-- LEAF (ng:commutation, sm-3:1929-1933 "After cusp rounding this is a positive page isotopy; equivalently,
the full named records are the same"). -/
theorem comm_recordIso {W W' : OWord} (h : IsComm W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  -- one direction of the exchange gives the isomorphism; `IsComm` is symmetric
  suffices key : ∀ {W W' : OWord}, IsCommStep W.letters W'.letters →
      Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) by
    rcases h with h | h
    · exact key h
    · obtain ⟨κ⟩ := key h
      exact ⟨κ.symm⟩
  intro W W' h
  obtain ⟨X, Y, a, b, hWeq, hpat⟩ := h
  rcases hpat with ⟨hab, hW'eq⟩ | ⟨hab, hW'eq⟩
  · exact U3.cm_recordIso_above X Y a b hab W W' hWeq hW'eq
  · -- the below case is the above case for the exchanged pair, read backwards
    have hb : a.idx + a.arity ≤ (b.reindex (b.idx + a.arity - a.coarity)).idx := by
      rw [Letter.idx_reindex]; omega
    obtain ⟨κ⟩ := U3.cm_recordIso_above X Y (b.reindex (b.idx + a.arity - a.coarity)) a hb W' W hW'eq (by
      rw [hWeq, Letter.idx_reindex, Letter.reindex_reindex,
        show b.idx + a.arity - a.coarity + a.coarity - a.arity = b.idx by omega, Letter.reindex_self])
    exact ⟨κ.symm⟩

/-- LEAF (ng:deletions, sm-3:2017-2019: after rounding the zigzag "is a simple ordinary arc, positively page
isotopic relative to its endpoints to the straightened arc" — no crossing is touched; every strand passes
through the block, the exterior visits and their cyclic orders are unchanged). -/
theorem zigzag_recordIso {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := by
  obtain ⟨X, Y, m, d, hm, hpat, hW'eq⟩ := h
  have hne' : W'.letters ≠ [] := IsZigzagDeletion.ne_nil ⟨X, Y, m, d, hm, hpat, hW'eq⟩ W.closed
  rcases hpat with hWeq | hWeq
  · exact U3.zb_recordIso X Y m d (hWeq ▸ W.closed) W W' hWeq hW'eq hne'
  · exact U3.za_recordIso X Y m d (hWeq ▸ W.closed) W W' hWeq hW'eq hne'

/-- LEAF (ng:circle, sm-3:2054-2059 "A standard circle separated by the word procedure has no mixed crossings
... Lemma lp:split-circle permits this nesting"): the record of the word with the circle is the record of the
remainder with one free (crossing-free) component added. -/
theorem circle_recordIso_addFree {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := by
  obtain ⟨X, Y, m, d, hm, hWeq, hW'eq, hne'⟩ := h
  exact U3.ci_recordIso X Y m d (hWeq ▸ W.closed) W W' hWeq hW'eq hne'

/-- The data one principal direction of the interchange supplies for its earlier branch `A` (sm-3:2091-2099
"Exchanging over and under at that crossing makes their local ordered crossing records identical, including
the boundary attachments.  After gluing any same actual exterior, the full named records are identical.  Thus
their polynomial values are the two crossing choices at one ordinary skein site"; sm-3:2119-2126 "Only the one
compatible smoothing is used"): the crossing `x` of the `σ` letter of `A`'s factor; the named record of
`realize A'` is that of the switch of `realize A` at `x`; an oriented smoothing of `realize A` at `x` (the
accepted `exists_smoothing_record_visit` supplies one with record `(realize A).record.smooth v`) carries the
named record of `realize C`; and the sign of `x` is the writhe difference `w_A − w_C` (the exterior writhe
`w₀` is `w_C`). -/
def SkeinSite (A A' C : OWord) : Prop :=
  ∃ x : (realize A).diagram.Γ.Crossing,
    Nonempty (RecordIso (realize A').diagram.record ((realize A).diagram.switch x).record) ∧
    (∃ D₀ : Diagram, IsOrientedSmoothing (realize A).diagram x D₀ ∧
      Nonempty (RecordIso D₀.record (realize C).diagram.record)) ∧
    ((realize A).diagram.sign x : ℤ) = (realize A).writhe - (realize C).writhe

/-- LEAF (ng:cusp-skein, the site for the printed direction `A = l_{m+1} σ_m`, `A' = l_m σ_{m+1}`, smoothing
`C_top`/`C_bottom` by the (t,u) table).  The other principal direction is the same leaf applied to
`IsCuspSkeinStep A' A C` (glue `skein_ineq_backward`). -/
theorem skein_site {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) : SkeinSite A A' C := by
  obtain ⟨X, Y, m, d, a, P, L, hm, hX, hP, hAe, hA'e, hCe⟩ := h
  obtain ⟨LA, hLA⟩ := A
  obtain ⟨LA', hLA'⟩ := A'
  obtain ⟨LC, hLC⟩ := C
  simp only at hAe hA'e hCe
  subst hAe hA'e
  have hne : (X ++ [Letter.l (m + 1) d, Letter.σ m] ++ Y) ≠ [] := by simp
  have hne' : (X ++ [Letter.l m d, Letter.σ (m + 1)] ++ Y) ≠ [] := by simp
  let ι := U2.realizeRecordIso ⟨_, hLA⟩ hne
  let ι' := U2.realizeRecordIso ⟨_, hLA'⟩ hne'
  let x₀ := U3.siteX X Y m d hLA
  let v := ι.Φ.symm x₀
  have hx : ι.Φ v = x₀ := Equiv.apply_symm_apply _ _
  refine ⟨v.1, ?_, ?_, ?_⟩
  · -- the switch half
    obtain ⟨κ⟩ := U3.sk_switchIso X Y m d a hLA hLA' hX hP hm
    have κ' := ι.switch v
    rw [hx] at κ'
    obtain ⟨jj⟩ := (realize ⟨_, hLA⟩).diagram.switch_record v.1 v rfl
    exact ⟨ι'.trans (κ.trans (κ'.symm.trans jj.symm))⟩
  · -- the smoothing half
    obtain ⟨D₀, hsm, ⟨θ⟩⟩ := exists_smoothing_record_visit (realize ⟨_, hLA⟩).diagram v.1 v rfl
    refine ⟨D₀, hsm, ?_⟩
    have sc := U3.smoothCongr ι v
    rw [hx] at sc
    rcases hCe with ⟨had, hCe⟩ | ⟨had, hCe⟩
    · subst hCe
      have hneC : (X ++ [Letter.l m d] ++ Y) ≠ [] := by simp
      obtain ⟨μ⟩ := U3.sk_smoothIso X Y m d a m hX hP hm hLA hLC (Or.inl ⟨had, rfl⟩)
      exact ⟨θ.trans (sc.trans (μ.trans (U2.realizeRecordIso ⟨_, hLC⟩ hneC).symm))⟩
    · subst hCe
      have hneC : (X ++ [Letter.l (m + 1) d] ++ Y) ≠ [] := by simp
      obtain ⟨μ⟩ := U3.sk_smoothIso X Y m d a (m + 1) hX hP hm hLA hLC (Or.inr ⟨had, rfl⟩)
      exact ⟨θ.trans (sc.trans (μ.trans (U2.realizeRecordIso ⟨_, hLC⟩ hneC).symm))⟩
  · -- the sign of the site is the writhe difference
    have h1 : (((realize ⟨_, hLA⟩).diagram.sign v.1 : SignType) : ℤ) = if a = d then 1 else -1 := by
      have := ι.sgn_eq v
      rw [hx] at this
      show (((realize ⟨_, hLA⟩).diagram.record.sgn v : SignType) : ℤ) = _
      rw [← this]
      exact U3.siteX_sgn X Y m d a hLA hX hP
    rw [h1, realize_writhe _ hne]
    unfold OWord.writheSyn
    simp only
    rw [u1_writheFrom_append₃ X _ Y hX (run_skein_A hm hP), U3.sk_writhe_factor m d a hP hm]
    rcases hCe with ⟨had, hCe⟩ | ⟨had, hCe⟩
    · subst hCe
      have hneC : (X ++ [Letter.l m d] ++ Y) ≠ [] := by simp
      rw [realize_writhe _ hneC]
      unfold OWord.writheSyn
      simp only
      subst had
      rw [u1_writheFrom_append₃ X _ Y hX (run_skein_Ctop hm hP), u1_writheFrom_cons
        (Letter.step_of_prefix (ℓ := .l m d) (by idxomega) (by idxomega) (Letter.act_l _ _ _)), u1_writheFrom_nil, u1_signBit_l]
      simp
    · subst hCe
      have hneC : (X ++ [Letter.l (m + 1) d] ++ Y) ≠ [] := by simp
      rw [realize_writhe _ hneC]
      unfold OWord.writheSyn
      simp only
      subst had
      have s : (Letter.l (m + 1) a).step (P ++ a :: L) = some (P ++ a :: a :: (!a) :: L) := by
        rw [show P ++ a :: L = (P ++ [a]) ++ L by simp,
          Letter.step_of_prefix (ℓ := .l (m + 1) a) (by idxomega) (by idxomega) (Letter.act_l _ _ _)]
        simp
      rw [u1_writheFrom_append₃ X _ Y hX (run_skein_Cbottom hm hP), u1_writheFrom_cons s, u1_writheFrom_nil,
        u1_signBit_l]
      simp

/-- LEAF (ng:cusp-skein "the unique compatible smoothing", FR-12): the interchange determines `C` — the two
principal words differ first at the cusp letter, which fixes `X`, `m`, `d`, `Y`; the through-strand bit is
read from `run X []`; the reverse-direction case is contradictory (`l (m+1) = l m'`, `l m = l (m'+1)`). -/
theorem skein_unique {A A' C C' : Word} (h : IsCuspSkein A A' C) (h' : IsCuspSkein A A' C') : C = C' := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact U3.skeinStep_unique h h'
  · exact (U3.skeinStep_not_both h h').elim
  · exact (U3.skeinStep_not_both h' h).elim
  · exact U3.skeinStep_unique h h'

/-! ### U4 infrastructure — the geometry core (unit U4; PLAN_FINAL.md §3 F1/F2, §4 "L-geo", §5 "U4 geometry core")

Convex move discs as finite intersections of closed half-planes (`HalfPlane`, `polygon`), the classification of
the pieces of a slot diagram relative to such a disc (`SegIn`/`SegOut`: a piece either has its open segment
strictly inside or strictly outside the disc — the "parallel-offset spectator argument" of F1 is one `SegOut`
witness per spectator piece), the vertex-moved slot diagrams `shadowMv`/`vertsOf` (any function `Slot W → Plane`
as the vertex tuples of the realization's shadow), their genericity and crossing set from a pairwise meeting
specification (`MeetSpec`, `GenericData`, `generic_of`, `slotDiagramData_of`), `Clean` on the disc's frontier,
the identity/slot-bijection `MoveMatch` (`MatchData`, `moveMatch_of`), the arcs of the disc as slot chains
(`Chain`, `arcCover_of`), and the congruences for equal-length words (`nextPair_congr`, `sameSlotEquiv`).
Consumers: U5 (`typeIII_site`) and U6 (`typeII_move`, `typeI_move`, `crossedCusp_move`). -/

namespace U4

open SM.FrontRealize SM.FrontWord.Letter Equiv

noncomputable section

/-! #### A. Half-planes and convex polygons -/

section Polygon

/-- A closed half-plane `{q | a₁ q₁ + a₂ q₂ ≤ b}` with a nonzero normal. -/
structure HalfPlane where
  a : Plane
  b : ℝ
  ha : a ≠ 0

namespace HalfPlane

variable (h : HalfPlane)

/-- the linear functional of the half-plane -/
def f (q : Plane) : ℝ := h.a.1 * q.1 + h.a.2 * q.2

/-- the closed half-plane -/
def cl : Set Plane := {q | h.f q ≤ h.b}

/-- the open half-plane -/
def op : Set Plane := {q | h.f q < h.b}

theorem f_add (p q : Plane) : h.f (p + q) = h.f p + h.f q := by simp only [f, Prod.fst_add, Prod.snd_add]; ring
theorem f_sub (p q : Plane) : h.f (p - q) = h.f p - h.f q := by simp only [f, Prod.fst_sub, Prod.snd_sub]; ring
theorem f_smul (t : ℝ) (q : Plane) : h.f (t • q) = t * h.f q := by
  simp only [f, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
theorem f_segPt (p q : Plane) (t : ℝ) : h.f (p + t • (q - p)) = h.f p + t * (h.f q - h.f p) := by
  rw [f_add, f_smul, f_sub]

theorem continuous_f : Continuous h.f := by
  unfold f
  fun_prop

theorem isClosed_cl : IsClosed h.cl := isClosed_le h.continuous_f continuous_const
theorem isOpen_op : IsOpen h.op := isOpen_lt h.continuous_f continuous_const
theorem op_subset_cl : h.op ⊆ h.cl := fun q hq => show h.f q ≤ h.b from le_of_lt hq

theorem convex_cl : Convex ℝ h.cl := by
  intro p hp q hq s t hs ht hst
  have hp' : h.f p ≤ h.b := hp
  have hq' : h.f q ≤ h.b := hq
  show h.f (s • p + t • q) ≤ h.b
  rw [f_add, f_smul, f_smul]
  calc s * h.f p + t * h.f q ≤ s * h.b + t * h.b := by gcongr
    _ = h.b := by rw [← add_mul, hst, one_mul]

/-- the squared norm of the normal is positive -/
theorem f_a_pos : 0 < h.f h.a := by
  have : h.f h.a = h.a.1 * h.a.1 + h.a.2 * h.a.2 := rfl
  rw [this]
  have h1 := mul_self_nonneg h.a.1
  have h2 := mul_self_nonneg h.a.2
  rcases eq_or_ne h.a.1 0 with hx | hx
  · have hy : h.a.2 ≠ 0 := fun hy => h.ha (Prod.ext hx hy)
    have := mul_self_pos.2 hy
    linarith
  · have := mul_self_pos.2 hx
    linarith

/-- The interior of a closed half-plane is the open half-plane. -/
theorem interior_cl : interior h.cl = h.op := by
  apply Set.Subset.antisymm
  · intro q hq
    rw [mem_interior_iff_mem_nhds] at hq
    have hcont : Continuous fun t : ℝ => q + t • h.a := by fun_prop
    have hlim : Filter.Tendsto (fun t : ℝ => q + t • h.a) (nhds 0) (nhds q) := by
      have := hcont.tendsto 0
      simpa using this
    have hev := hlim.eventually hq
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    have hmem : h.f (q + (ε / 2) • h.a) ≤ h.b :=
      hball (y := ε / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
    rw [f_add, f_smul] at hmem
    have hpos := h.f_a_pos
    show h.f q < h.b
    nlinarith
  · exact interior_maximal h.op_subset_cl h.isOpen_op

theorem mem_interior_cl_iff (q : Plane) : q ∈ interior h.cl ↔ h.f q < h.b := by rw [interior_cl]; rfl

end HalfPlane

/-- The convex polygon cut out by a finite list of half-planes. -/
def polygon : List HalfPlane → Set Plane
  | [] => Set.univ
  | h :: L => h.cl ∩ polygon L

theorem mem_polygon_iff (L : List HalfPlane) (q : Plane) : q ∈ polygon L ↔ ∀ h ∈ L, h.f q ≤ h.b := by
  induction L with
  | nil => simp [polygon]
  | cons h L ih =>
    simp only [polygon, Set.mem_inter_iff, ih, List.mem_cons, forall_eq_or_imp]
    rfl

theorem interior_polygon (L : List HalfPlane) : interior (polygon L) = {q | ∀ h ∈ L, h.f q < h.b} := by
  induction L with
  | nil => simp [polygon]
  | cons h L ih =>
    rw [polygon, interior_inter, ih, HalfPlane.interior_cl]
    ext q
    simp only [Set.mem_inter_iff, List.mem_cons, forall_eq_or_imp]
    exact Iff.rfl

theorem mem_interior_polygon_iff (L : List HalfPlane) (q : Plane) :
    q ∈ interior (polygon L) ↔ ∀ h ∈ L, h.f q < h.b := by rw [interior_polygon]; rfl

theorem isClosed_polygon (L : List HalfPlane) : IsClosed (polygon L) := by
  induction L with
  | nil => exact isClosed_univ
  | cons h L ih => exact h.isClosed_cl.inter ih

theorem convex_polygon (L : List HalfPlane) : Convex ℝ (polygon L) := by
  induction L with
  | nil => exact convex_univ
  | cons h L ih => exact h.convex_cl.inter ih

theorem interior_polygon_subset (L : List HalfPlane) : interior (polygon L) ⊆ polygon L := interior_subset

/-- A point of the polygon is on its frontier iff it saturates one of the inequalities. -/
theorem mem_frontier_polygon_iff (L : List HalfPlane) (q : Plane) :
    q ∈ frontier (polygon L) ↔ q ∈ polygon L ∧ ∃ h ∈ L, h.f q = h.b := by
  rw [(isClosed_polygon L).frontier_eq, Set.mem_sdiff, mem_interior_polygon_iff, mem_polygon_iff]
  constructor
  · rintro ⟨hq, hn⟩
    refine ⟨hq, ?_⟩
    obtain ⟨h, hn⟩ := not_forall.1 hn
    obtain ⟨hh, hle⟩ := not_imp.1 hn
    exact ⟨h, hh, le_antisymm (hq h hh) (not_lt.1 hle)⟩
  · rintro ⟨hq, h, hh, he⟩
    refine ⟨hq, fun hall => ?_⟩
    exact absurd (hall h hh) (by rw [he]; exact lt_irrefl _)

theorem mem_frontier_polygon_of (L : List HalfPlane) {q : Plane} (hq : q ∈ polygon L)
    (hn : q ∉ interior (polygon L)) : q ∈ frontier (polygon L) := by
  rw [(isClosed_polygon L).frontier_eq]; exact ⟨hq, hn⟩

theorem notMem_interior_of_mem_frontier (L : List HalfPlane) {q : Plane} (hq : q ∈ frontier (polygon L)) :
    q ∉ interior (polygon L) := by
  rw [(isClosed_polygon L).frontier_eq] at hq; exact hq.2

theorem mem_of_mem_frontier (L : List HalfPlane) {q : Plane} (hq : q ∈ frontier (polygon L)) : q ∈ polygon L := by
  rw [(isClosed_polygon L).frontier_eq] at hq; exact hq.1

/-- A polygon contained in a box, with a point satisfying every inequality strictly, is a disc. -/
theorem isDisc_polygon (L : List HalfPlane) {a b c d : ℝ}
    (hbox : ∀ q ∈ polygon L, a ≤ q.1 ∧ q.1 ≤ b ∧ c ≤ q.2 ∧ q.2 ≤ d)
    (hint : ∃ q : Plane, ∀ h ∈ L, h.f q < h.b) : IsDisc (polygon L) := by
  refine ⟨convex_polygon L, ?_, ?_⟩
  · apply Metric.isCompact_of_isClosed_isBounded (isClosed_polygon L)
    apply (isCompact_Icc.prod isCompact_Icc).isBounded.subset (t := Set.Icc a b ×ˢ Set.Icc c d)
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hbox q hq
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  · obtain ⟨q, hq⟩ := hint
    exact ⟨q, (mem_interior_polygon_iff L q).2 hq⟩

/-! Convenient half-planes: the four axis-parallel ones and a general lower/upper line `y ≥ c + s x`. -/

/-- `{x ≤ b}` -/
def HalfPlane.xle (b : ℝ) : HalfPlane := ⟨(1, 0), b, by simp⟩
/-- `{a ≤ x}` -/
def HalfPlane.xge (a : ℝ) : HalfPlane := ⟨(-1, 0), -a, by simp⟩
/-- `{y ≤ d}` -/
def HalfPlane.yle (d : ℝ) : HalfPlane := ⟨(0, 1), d, by simp⟩
/-- `{c ≤ y}` -/
def HalfPlane.yge (c : ℝ) : HalfPlane := ⟨(0, -1), -c, by simp⟩
/-- `{y ≤ c + s x}` -/
def HalfPlane.below (c s : ℝ) : HalfPlane := ⟨(-s, 1), c, by simp⟩
/-- `{c + s x ≤ y}` -/
def HalfPlane.above (c s : ℝ) : HalfPlane := ⟨(s, -1), -c, by simp⟩

@[simp] theorem HalfPlane.f_xle (b : ℝ) (q : Plane) : (HalfPlane.xle b).f q = q.1 := by simp [HalfPlane.f, HalfPlane.xle]
@[simp] theorem HalfPlane.b_xle (b : ℝ) : (HalfPlane.xle b).b = b := rfl
@[simp] theorem HalfPlane.f_xge (a : ℝ) (q : Plane) : (HalfPlane.xge a).f q = -q.1 := by simp [HalfPlane.f, HalfPlane.xge]
@[simp] theorem HalfPlane.b_xge (a : ℝ) : (HalfPlane.xge a).b = -a := rfl
@[simp] theorem HalfPlane.f_yle (d : ℝ) (q : Plane) : (HalfPlane.yle d).f q = q.2 := by simp [HalfPlane.f, HalfPlane.yle]
@[simp] theorem HalfPlane.b_yle (d : ℝ) : (HalfPlane.yle d).b = d := rfl
@[simp] theorem HalfPlane.f_yge (c : ℝ) (q : Plane) : (HalfPlane.yge c).f q = -q.2 := by simp [HalfPlane.f, HalfPlane.yge]
@[simp] theorem HalfPlane.b_yge (c : ℝ) : (HalfPlane.yge c).b = -c := rfl
@[simp] theorem HalfPlane.f_below (c s : ℝ) (q : Plane) : (HalfPlane.below c s).f q = -s * q.1 + q.2 := by
  simp [HalfPlane.f, HalfPlane.below]
@[simp] theorem HalfPlane.b_below (c s : ℝ) : (HalfPlane.below c s).b = c := rfl
@[simp] theorem HalfPlane.f_above (c s : ℝ) (q : Plane) : (HalfPlane.above c s).f q = s * q.1 - q.2 := by
  simp [HalfPlane.f, HalfPlane.above]; ring
@[simp] theorem HalfPlane.b_above (c s : ℝ) : (HalfPlane.above c s).b = -c := rfl

end Polygon

/-! #### B. Segments relative to a polygon -/

section Segments

/-- the point of the segment `[p₀, p₁]` at parameter `t` (the accepted `edgePoint` shape) -/
abbrev segPt (p₀ p₁ : Plane) (t : ℝ) : Plane := p₀ + t • (p₁ - p₀)

@[simp] theorem segPt_zero (p₀ p₁ : Plane) : segPt p₀ p₁ 0 = p₀ := by simp [segPt]
@[simp] theorem segPt_one (p₀ p₁ : Plane) : segPt p₀ p₁ 1 = p₁ := by simp [segPt]
theorem segPt_fst (p₀ p₁ : Plane) (t : ℝ) : (segPt p₀ p₁ t).1 = p₀.1 + t * (p₁.1 - p₀.1) := by
  simp [segPt]
theorem segPt_snd (p₀ p₁ : Plane) (t : ℝ) : (segPt p₀ p₁ t).2 = p₀.2 + t * (p₁.2 - p₀.2) := by
  simp [segPt]

/-- The segment parameter is determined by any coordinate in which the endpoints differ. -/
theorem segPt_fst_injective {p₀ p₁ : Plane} (h : p₀.1 ≠ p₁.1) {t t' : ℝ}
    (he : (segPt p₀ p₁ t).1 = (segPt p₀ p₁ t').1) : t = t' := by
  rw [segPt_fst, segPt_fst] at he
  have : (t - t') * (p₁.1 - p₀.1) = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · exact absurd (by linarith : p₀.1 = p₁.1) h

theorem segPt_injective {p₀ p₁ : Plane} (h : p₀ ≠ p₁) : Function.Injective (segPt p₀ p₁) := by
  intro t t' he
  have hne : p₁ - p₀ ≠ 0 := sub_ne_zero.2 (Ne.symm h)
  have : (t - t') • (p₁ - p₀) = 0 := by
    rw [sub_smul]
    have := congrArg (fun q => q - p₀) he
    simp only [segPt, add_sub_cancel_left] at this
    rw [this, sub_self]
  rcases smul_eq_zero.1 this with h1 | h1
  · linarith
  · exact absurd h1 hne

theorem segPt_reverse (p₀ p₁ : Plane) (t : ℝ) : segPt p₁ p₀ (1 - t) = segPt p₀ p₁ t := by
  simp only [segPt]; ext <;> simp <;> ring

variable (L : List HalfPlane)

/-- The open segment `(p₀, p₁)` lies in the open polygon and the endpoints in the closed polygon: for every
half-plane both endpoints satisfy the inequality, at least one strictly. -/
def SegIn (p₀ p₁ : Plane) : Prop := ∀ h ∈ L, h.f p₀ ≤ h.b ∧ h.f p₁ ≤ h.b ∧ (h.f p₀ < h.b ∨ h.f p₁ < h.b)

/-- The open segment `(p₀, p₁)` misses the closed polygon and the endpoints miss the open polygon: some
half-plane is violated by both endpoints, by at least one strictly. -/
def SegOut (p₀ p₁ : Plane) : Prop := ∃ h ∈ L, h.b ≤ h.f p₀ ∧ h.b ≤ h.f p₁ ∧ (h.b < h.f p₀ ∨ h.b < h.f p₁)

variable {L}

theorem SegIn.symm {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) : SegIn L p₁ p₀ := fun hp hh =>
  ⟨(h hp hh).2.1, (h hp hh).1, (h hp hh).2.2.symm⟩

theorem SegOut.symm {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) : SegOut L p₁ p₀ := by
  obtain ⟨hp, hh, h1, h2, h3⟩ := h
  exact ⟨hp, hh, h2, h1, h3.symm⟩

theorem SegIn.mem_interior {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    segPt p₀ p₁ t ∈ interior (polygon L) := by
  rw [mem_interior_polygon_iff]
  intro hp hh
  obtain ⟨a1, a2, a3⟩ := h hp hh
  rw [HalfPlane.f_segPt]
  rcases a3 with a3 | a3 <;> nlinarith

theorem SegIn.left_mem {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) : p₀ ∈ polygon L :=
  (mem_polygon_iff L p₀).2 fun hp hh => (h hp hh).1

theorem SegIn.right_mem {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) : p₁ ∈ polygon L :=
  (mem_polygon_iff L p₁).2 fun hp hh => (h hp hh).2.1

theorem SegIn.mem {p₀ p₁ : Plane} (h : SegIn L p₀ p₁) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    segPt p₀ p₁ t ∈ polygon L := by
  rcases h0.lt_or_eq with h0 | h0
  · rcases h1.lt_or_eq with h1 | h1
    · exact interior_subset (h.mem_interior h0 h1)
    · subst h1; rw [segPt_one]; exact h.right_mem
  · subst h0; rw [segPt_zero]; exact h.left_mem

theorem SegOut.notMem {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    segPt p₀ p₁ t ∉ polygon L := by
  rw [mem_polygon_iff]
  obtain ⟨hp, hh, a1, a2, a3⟩ := h
  intro hall
  have := hall hp hh
  rw [HalfPlane.f_segPt] at this
  rcases a3 with a3 | a3 <;> nlinarith

theorem SegOut.left_notMem_interior {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) : p₀ ∉ interior (polygon L) := by
  rw [mem_interior_polygon_iff]
  obtain ⟨hp, hh, a1, -, -⟩ := h
  intro hall
  exact absurd (hall hp hh) (not_lt.2 a1)

theorem SegOut.right_notMem_interior {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) : p₁ ∉ interior (polygon L) :=
  h.symm.left_notMem_interior

theorem SegOut.notMem_interior {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    segPt p₀ p₁ t ∉ interior (polygon L) := by
  rcases h0.lt_or_eq with h0 | h0
  · rcases h1.lt_or_eq with h1 | h1
    · exact fun hm => h.notMem h0 h1 (interior_subset hm)
    · subst h1; rw [segPt_one]; exact h.right_notMem_interior
  · subst h0; rw [segPt_zero]; exact h.left_notMem_interior

/-- A point of an outside segment lying in the closed polygon is an endpoint. -/
theorem SegOut.eq_end_of_mem {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hm : segPt p₀ p₁ t ∈ polygon L) : t = 0 ∨ t = 1 := by
  by_contra hc
  rw [not_or] at hc
  exact h.notMem (lt_of_le_of_ne h0 (Ne.symm hc.1)) (lt_of_le_of_ne h1 hc.2) hm

/-- No segment is both inside and outside. -/
theorem not_segIn_of_segOut {p₀ p₁ : Plane} (h : SegOut L p₀ p₁) : ¬ SegIn L p₀ p₁ := fun h' =>
  h.notMem (t := 1 / 2) (by norm_num) (by norm_num) (interior_subset (h'.mem_interior (by norm_num) (by norm_num)))

/-- A segment from a point of the open polygon to a point of the closed polygon is inside. -/
theorem segIn_of_interior_left {p₀ p₁ : Plane} (h0 : p₀ ∈ interior (polygon L)) (h1 : p₁ ∈ polygon L) :
    SegIn L p₀ p₁ := by
  rw [mem_interior_polygon_iff] at h0
  rw [mem_polygon_iff] at h1
  exact fun hp hh => ⟨(h0 hp hh).le, h1 hp hh, Or.inl (h0 hp hh)⟩

theorem segIn_of_interior_right {p₀ p₁ : Plane} (h0 : p₀ ∈ polygon L) (h1 : p₁ ∈ interior (polygon L)) :
    SegIn L p₀ p₁ := (segIn_of_interior_left h1 h0).symm

/-- A single violated half-plane, strict at one end, gives `SegOut`. -/
theorem segOut_of {p₀ p₁ : Plane} (h : HalfPlane) (hh : h ∈ L) (h0 : h.b ≤ h.f p₀) (h1 : h.b ≤ h.f p₁)
    (hs : h.b < h.f p₀ ∨ h.b < h.f p₁) : SegOut L p₀ p₁ := ⟨h, hh, h0, h1, hs⟩

/-- A strictly violated half-plane gives `SegOut`. -/
theorem segOut_of_lt {p₀ p₁ : Plane} (h : HalfPlane) (hh : h ∈ L) (h0 : h.b < h.f p₀) (h1 : h.b < h.f p₁) :
    SegOut L p₀ p₁ := ⟨h, hh, h0.le, h1.le, Or.inl h0⟩

end Segments

/-! #### C. Slot diagrams with moved vertices: any `mv : Slot W → Plane` as the vertex tuples of the realization's shadow -/

section SlotDiagram

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ [])

/-- The vertex tuples of the realization's shadow with the vertex of the slot `u` at `mv u`. -/
def vertsOf (mv : Slot W → Plane) : (shadowOf pl hW hne).Vertices := fun i j => mv (idxEquiv hW ⟨i, j⟩)

/-- The re-vertexed shadow: the strands, traversal points and components of the realization, the vertex of
slot `u` at `mv u`. -/
abbrev shadowMv (mv : Slot W → Plane) : Shadow := (shadowOf pl hW hne).withVertices (vertsOf pl hW hne mv)

/-- The realization's own vertices: `mv = pt`. -/
theorem vertsOf_pt : vertsOf pl hW hne (fun u => pt pl W u.1) = (shadowOf pl hW hne).vertices := rfl

theorem shadowMv_pt : shadowMv pl hW hne (fun u => pt pl W u.1) = shadowOf pl hW hne := rfl

variable (mv : Slot W → Plane)

/-- the slot at the tail of a strand of the re-vertexed shadow (the strands are `Idx hW`) -/
abbrev slotMv (s : (shadowMv pl hW hne mv).Strand) : Slot W := idxEquiv hW s

theorem slotMv_stStrand (u : Slot W) : slotMv pl hW hne mv (U2.stStrand pl hW hne (vertsOf pl hW hne mv) u) = u :=
  U2.idxEquiv_stStrand pl hW hne _ u

theorem stStrand_slotMv (s : (shadowMv pl hW hne mv).Strand) :
    U2.stStrand pl hW hne (vertsOf pl hW hne mv) (slotMv pl hW hne mv s) = s :=
  U2.stStrand_idxEquiv pl hW hne _ s

theorem slotMv_injective : Function.Injective (slotMv pl hW hne mv) := (idxEquiv hW).injective

theorem tail_mv (s : (shadowMv pl hW hne mv).Strand) :
    (shadowMv pl hW hne mv).tail s = mv (slotMv pl hW hne mv s) := rfl

theorem head_mv (s : (shadowMv pl hW hne mv).Strand) :
    (shadowMv pl hW hne mv).head s = mv (next hW (slotMv pl hW hne mv s)) := by
  obtain ⟨i, j⟩ := s
  have e := toSlot_succ hW i j
  exact congrArg mv e

theorem dir_mv (s : (shadowMv pl hW hne mv).Strand) :
    (shadowMv pl hW hne mv).dir s = mv (next hW (slotMv pl hW hne mv s)) - mv (slotMv pl hW hne mv s) := by
  have e : (shadowMv pl hW hne mv).dir s = (shadowMv pl hW hne mv).head s - (shadowMv pl hW hne mv).tail s := rfl
  rw [e, head_mv, tail_mv]

theorem edgePoint_mv (s : (shadowMv pl hW hne mv).Strand) (t : ℝ) :
    edgePoint ((shadowMv pl hW hne mv).comp s.1).P s.2 t =
      segPt (mv (slotMv pl hW hne mv s)) (mv (next hW (slotMv pl hW hne mv s))) t := by
  have e : edgePoint ((shadowMv pl hW hne mv).comp s.1).P s.2 t =
      (shadowMv pl hW hne mv).tail s + t • ((shadowMv pl hW hne mv).head s - (shadowMv pl hW hne mv).tail s) := rfl
  rw [e, tail_mv, head_mv]

/-- the slot of a traversal point -/
abbrev slotPtMv (p : (shadowMv pl hW hne mv).Pt) : Slot W := slotMv pl hW hne mv ⟨p.1, p.2.1⟩

theorem eval_mv (p : (shadowMv pl hW hne mv).Pt) :
    (shadowMv pl hW hne mv).eval p = segPt (mv (slotPtMv pl hW hne mv p)) (mv (next hW (slotPtMv pl hW hne mv p))) p.2.2.val := by
  obtain ⟨i, j, t⟩ := p
  exact edgePoint_mv pl hW hne mv ⟨i, j⟩ t.val

theorem mem_seg_mv_iff (s : (shadowMv pl hW hne mv).Strand) (q : Plane) :
    q ∈ (shadowMv pl hW hne mv).seg s ↔
      ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ q = segPt (mv (slotMv pl hW hne mv s)) (mv (next hW (slotMv pl hW hne mv s))) t := by
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, edgePoint_mv pl hW hne mv s t⟩
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, (edgePoint_mv pl hW hne mv s t).symm⟩

theorem mem_interior_mv_iff (s : (shadowMv pl hW hne mv).Strand) (q : Plane) :
    q ∈ (shadowMv pl hW hne mv).interior s ↔
      ∃ t, 0 < t ∧ t < 1 ∧ q = segPt (mv (slotMv pl hW hne mv s)) (mv (next hW (slotMv pl hW hne mv s))) t := by
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, edgePoint_mv pl hW hne mv s t⟩
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, (edgePoint_mv pl hW hne mv s t).symm⟩

/-- Adjacency of strands is adjacency of slots along the successor (the shadow structure is the realization's). -/
theorem adjacent_mv_iff (s t : (shadowMv pl hW hne mv).Strand) :
    (shadowMv pl hW hne mv).Adjacent s t ↔
      slotMv pl hW hne mv t = slotMv pl hW hne mv s ∨ slotMv pl hW hne mv t = next hW (slotMv pl hW hne mv s) ∨
        slotMv pl hW hne mv t = prev hW (slotMv pl hW hne mv s) :=
  adjacent_iff pl hW hne s t

theorem incidentTail_mv_of (s t : (shadowMv pl hW hne mv).Strand)
    (h : slotMv pl hW hne mv s = slotMv pl hW hne mv t ∨ slotMv pl hW hne mv s = next hW (slotMv pl hW hne mv t)) :
    (shadowMv pl hW hne mv).IncidentTail s t :=
  incidentTail_of pl hW hne s t h

/-- The strand of a slot as a strand of the re-vertexed shadow, and the traversal point of its tail. -/
abbrev strandMv (u : Slot W) : (shadowMv pl hW hne mv).Strand := U2.stStrand pl hW hne (vertsOf pl hW hne mv) u

/-- the traversal point at parameter `t` of the strand of the slot `u` -/
abbrev travMv (u : Slot W) (t : Set.Ico (0 : ℝ) 1) : (shadowMv pl hW hne mv).Pt :=
  ⟨(strandMv pl hW hne mv u).1, ((strandMv pl hW hne mv u).2, t)⟩

theorem slotPtMv_travMv (u : Slot W) (t : Set.Ico (0 : ℝ) 1) : slotPtMv pl hW hne mv (travMv pl hW hne mv u t) = u :=
  slotMv_stStrand pl hW hne mv u

theorem eval_travMv (u : Slot W) (t : Set.Ico (0 : ℝ) 1) :
    (shadowMv pl hW hne mv).eval (travMv pl hW hne mv u t) = segPt (mv u) (mv (next hW u)) t.val := by
  rw [eval_mv, slotPtMv_travMv]

theorem travMv_slotPtMv (p : (shadowMv pl hW hne mv).Pt) : travMv pl hW hne mv (slotPtMv pl hW hne mv p) p.2.2 = p := by
  obtain ⟨i, j, t⟩ := p
  have e : strandMv pl hW hne mv (slotPtMv pl hW hne mv ⟨i, j, t⟩) = ⟨i, j⟩ := stStrand_slotMv pl hW hne mv ⟨i, j⟩
  show (⟨(strandMv pl hW hne mv (slotPtMv pl hW hne mv ⟨i, j, t⟩)).1,
    ((strandMv pl hW hne mv (slotPtMv pl hW hne mv ⟨i, j, t⟩)).2, t)⟩ : (shadowMv pl hW hne mv).Pt) = ⟨i, j, t⟩
  rw [e]

/-- the traversal point of the tail vertex of a slot -/
abbrev vertexPt (u : Slot W) : (shadowMv pl hW hne mv).Pt := travMv pl hW hne mv u ⟨0, le_rfl, zero_lt_one⟩

theorem eval_vertexPt (u : Slot W) : (shadowMv pl hW hne mv).eval (vertexPt pl hW hne mv u) = mv u := by
  rw [eval_travMv]; simp

/-- An *unchanged* piece: both ends at the realization's grid points. -/
def Unch (u : Slot W) : Prop := mv u = pt pl W u.1 ∧ mv (next hW u) = pt pl W (next hW u).1

theorem unch_pt (u : Slot W) : Unch pl hW (fun u => pt pl W u.1) u := ⟨rfl, rfl⟩

omit hne in
/-- `piecePt` is affine in the parameter. -/
theorem segPt_piecePt (u : Slot W) (a b t : ℝ) :
    segPt (piecePt pl u a) (piecePt pl u b) t = piecePt pl u (a + t * (b - a)) := by
  simp only [segPt, piecePt, Placement.A, Shape.par]
  ext <;> simp <;> ring

omit hne in
/-- The segment of the realization's piece of `u` in the tail-to-head parametrization is the piece with the
parameter reversed on a leftward strand. -/
theorem segPt_pt (u : Slot W) (t : ℝ) :
    segPt (pt pl W u.1) (pt pl W (next hW u).1) t = piecePt pl u (if xsign u then t else 1 - t) := by
  rw [pt_eq_piecePt pl hW u, pt_next_eq_piecePt pl hW u, segPt_piecePt]
  congr 1
  split_ifs <;> ring

omit hne in
/-- An unchanged piece traces the realization's piece. -/
theorem segPt_unch {u : Slot W} (hu : Unch pl hW mv u) (t : ℝ) :
    segPt (mv u) (mv (next hW u)) t = piecePt pl u (if xsign u then t else 1 - t) := by
  rw [hu.1, hu.2, segPt_pt pl hW]

omit hne in
/-- The x-coordinates of the two ends of the realization's piece differ. -/
theorem pt_fst_ne_pt_next_fst (u : Slot W) : (pt pl W u.1).1 ≠ (pt pl W (next hW u).1).1 := by
  have := dir_slot_fst_ne_zero pl hW u
  intro h; apply this; rw [Prod.fst_sub, h, sub_self]

omit hne in
include hW in
/-- Both ends of the realization's piece of `u` have x-coordinate in the strip of its column. -/
theorem pt_fst_mem (u : Slot W) : pl.x (colOf u) ≤ (pt pl W u.1).1 ∧ (pt pl W u.1).1 ≤ pl.x (colOf u + 1) := by
  rw [pt_eq_piecePt pl hW u]
  exact piecePt_fst_mem pl hW u (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)

omit hne in
theorem pt_next_fst_mem (u : Slot W) :
    pl.x (colOf u) ≤ (pt pl W (next hW u).1).1 ∧ (pt pl W (next hW u).1).1 ≤ pl.x (colOf u + 1) := by
  rw [pt_next_eq_piecePt pl hW u]
  exact piecePt_fst_mem pl hW u (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)

omit mv in
/-- The diagram of the realization is the slot diagram with `mv = pt` (definitionally): the entry point for
using the tools of this section on `(realize W).diagram = (realizeAt .std W.closed h).diagram`. -/
theorem realizeAt_diagram_eq :
    (realizeAt pl hW hne).diagram =
      U2.mkDiagram pl hW hne (vertsOf pl hW hne (fun u => pt pl W u.1)) (generic pl hW hne)
        (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem := rfl

omit mv in
theorem realizeAt_data' :
    U2.SlotDiagramData pl hW hne (vertsOf pl hW hne (fun u => pt pl W u.1)) (generic pl hW hne)
      (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True) :=
  U2.realizeAt_data pl hW hne

end SlotDiagram

/-! #### D. The classification of the pieces of a slot diagram relative to a polygon; `Clean` -/

section Classify

variable (L : List HalfPlane) (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane)

/-- the piece of `u` is inside (open segment in the open polygon, ends in the closed polygon) -/
def PieceIn (u : Slot W) : Prop := SegIn L (mv u) (mv (next hW u))

/-- the piece of `u` is outside (open segment misses the closed polygon, ends miss the open polygon) -/
def PieceOut (u : Slot W) : Prop := SegOut L (mv u) (mv (next hW u))

theorem not_pieceIn_of_pieceOut {u : Slot W} (h : PieceOut L hW mv u) : ¬ PieceIn L hW mv u := not_segIn_of_segOut h

/-- A traversal point of a classified diagram evaluating on the frontier is a vertex point. -/
theorem frontier_pt_mv (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u) (p : (shadowMv pl hW hne mv).Pt)
    (hp : (shadowMv pl hW hne mv).eval p ∈ frontier (polygon L)) :
    p.2.2.val = 0 ∧ (shadowMv pl hW hne mv).eval p = mv (slotPtMv pl hW hne mv p) := by
  have ht := p.2.2.2
  rw [eval_mv] at hp ⊢
  have h0 : p.2.2.val = 0 := by
    by_contra hc
    have hpos : 0 < p.2.2.val := lt_of_le_of_ne ht.1 (Ne.symm hc)
    rcases hcl (slotPtMv pl hW hne mv p) with h | h
    · exact notMem_interior_of_mem_frontier L hp (h.mem_interior hpos ht.2)
    · exact h.notMem hpos ht.2 (mem_of_mem_frontier L hp)
  rw [h0]
  exact ⟨rfl, by simp⟩

/-- Two traversal points with the same evaluation on the frontier coincide (injective vertex function). -/
theorem frontier_injOn_mv (hinj : Function.Injective mv) (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u) :
    Set.InjOn (shadowMv pl hW hne mv).eval {p | (shadowMv pl hW hne mv).eval p ∈ frontier (polygon L)} := by
  intro p hp q hq hpq
  obtain ⟨hp0, hpe⟩ := frontier_pt_mv L pl hW hne mv hcl p hp
  obtain ⟨hq0, hqe⟩ := frontier_pt_mv L pl hW hne mv hcl q hq
  rw [hpe, hqe] at hpq
  have hslot := hinj hpq
  rw [← travMv_slotPtMv pl hW hne mv p, ← travMv_slotPtMv pl hW hne mv q, hslot]
  congr 1
  exact Subtype.ext (hp0.trans hq0.symm)

/-- The exit criterion in strand-index form: every component has a point of one of its pieces strictly outside
the polygon. -/
def ExitsMv : Prop :=
  ∀ i : Fin (numComp hW), ∃ (j : ZMod (period hW (rep hW i))) (t : Set.Ico (0 : ℝ) 1),
    segPt (mv (idxEquiv hW ⟨i, j⟩)) (mv (next hW (idxEquiv hW ⟨i, j⟩))) t.val ∉ polygon L

/-- The exit criterion from a slot-cycle statement: every cycle of `next` has an outside piece. -/
theorem exitsMv_of_sameCycle (hex : ∀ u : Slot W, ∃ v : Slot W, (nextPerm hW).SameCycle u v ∧ PieceOut L hW mv v) :
    ExitsMv L hW mv := by
  intro i
  obtain ⟨v, hsc, hv⟩ := hex (rep hW i)
  obtain ⟨i', n, hn, hv'⟩ := exists_rep_iterate hW v
  have hi : i' = i := by
    have h1 : (nextPerm hW).SameCycle (toSlot hW ⟨i', (n : ZMod (period hW (rep hW i')))⟩) (toSlot hW ⟨i, 0⟩) := by
      have e1 : toSlot hW ⟨i', (n : ZMod (period hW (rep hW i')))⟩ = v := by
        simp only [toSlot]; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn, hv']
      have e2 : toSlot hW ⟨i, 0⟩ = rep hW i := by simp [toSlot]
      rw [e1, e2]; exact hsc.symm
    exact (toSlot_fst_eq_iff hW _ _).2 h1
  subst hi
  refine ⟨(n : ZMod (period hW (rep hW i'))), ⟨1 / 2, by norm_num, by norm_num⟩, ?_⟩
  have e1 : idxEquiv hW ⟨i', (n : ZMod (period hW (rep hW i')))⟩ = v := by
    show toSlot hW ⟨i', (n : ZMod (period hW (rep hW i')))⟩ = v
    simp only [toSlot]; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn, hv']
  rw [e1]
  exact hv.notMem (by norm_num) (by norm_num)

theorem exits_mv (hex : ExitsMv L hW mv) :
    ∀ i : Fin (shadowMv pl hW hne mv).c, ∃ p, (shadowMv pl hW hne mv).eval ⟨i, p⟩ ∉ polygon L := by
  intro i
  obtain ⟨j, t, hj⟩ := hex i
  refine ⟨(j, t), ?_⟩
  have e : slotPtMv pl hW hne mv ⟨i, (j, t)⟩ = idxEquiv hW ⟨i, j⟩ := rfl
  rw [eval_mv, e]
  exact hj

/-- **Cleanness** of a classified slot diagram at a polygon: the frontier is met only at vertices, each once;
every component has a vertex outside. -/
theorem clean_mv (hinj : Function.Injective mv) (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u)
    (hex : ExitsMv L hW mv) (hgen : (shadowMv pl hW hne mv).Generic)
    (ov : (shadowMv pl hW hne mv).Crossing → (shadowMv pl hW hne mv).Strand) (hov : ∀ x, ov x ∈ x.val) :
    Clean (polygon L) (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov) where
  frontier_injOn := frontier_injOn_mv L pl hW hne mv hinj hcl
  exits := exits_mv L pl hW hne mv hex

/-- An unchanged piece of a column outside `[a, b)` is outside a polygon cut by the lines `x = pl.x a`, `x = pl.x b`. -/
theorem pieceOut_of_extCol {a b : ℕ} (ha : HalfPlane.xge (pl.x a) ∈ L) (hb : HalfPlane.xle (pl.x b) ∈ L)
    {u : Slot W} (hu : Unch pl hW mv u) (hcol : colOf u + 1 ≤ a ∨ b ≤ colOf u) : PieceOut L hW mv u := by
  unfold PieceOut
  rw [hu.1, hu.2]
  have h1 := pt_fst_mem pl hW u
  have h2 := pt_next_fst_mem pl hW u
  have hne' := pt_fst_ne_pt_next_fst pl hW u
  rcases hcol with hcol | hcol
  · have hle : pl.x (colOf u + 1) ≤ pl.x a := pl.x_le_x_iff.2 hcol
    refine segOut_of _ ha ?_ ?_ ?_
    · simp only [HalfPlane.f_xge, HalfPlane.b_xge]; linarith
    · simp only [HalfPlane.f_xge, HalfPlane.b_xge]; linarith
    · simp only [HalfPlane.f_xge, HalfPlane.b_xge]
      rcases lt_or_gt_of_ne hne' with h | h
      · left; linarith
      · right; linarith
  · have hle : pl.x b ≤ pl.x (colOf u) := pl.x_le_x_iff.2 hcol
    refine segOut_of _ hb ?_ ?_ ?_
    · simp only [HalfPlane.f_xle, HalfPlane.b_xle]; linarith
    · simp only [HalfPlane.f_xle, HalfPlane.b_xle]; linarith
    · simp only [HalfPlane.f_xle, HalfPlane.b_xle]
      rcases lt_or_gt_of_ne hne' with h | h
      · right; linarith
      · left; linarith

end Classify

/-! #### E. Genericity and the crossing set of a moved slot diagram from a pairwise meeting specification -/

section Generic

variable (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane) (K : ℕ → Prop)

/-- The `σ`-pair meeting of two pieces: both unchanged, one `σ` column in `K`, the two crossing shapes. -/
def SigmaMeet (u v : Slot W) : Prop :=
  Unch pl hW mv u ∧ Unch pl hW mv v ∧ colOf u = colOf v ∧ K (colOf u) ∧
    ∃ m, letterAt W (colOf u) = .σ m ∧
      ((shapeOf u = .pass m (m + 1) ∧ shapeOf v = .pass (m + 1) m) ∨
       (shapeOf u = .pass (m + 1) m ∧ shapeOf v = .pass m (m + 1)))

theorem SigmaMeet.symm {u v : Slot W} (h : SigmaMeet pl hW mv K u v) : SigmaMeet pl hW mv K v u := by
  obtain ⟨hu, hv, hc, hK, m, hℓ, hS⟩ := h
  refine ⟨hv, hu, hc.symm, hc ▸ hK, m, hc ▸ hℓ, ?_⟩
  rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

/-- **The meeting specification** of two pieces: every common point of the two segments is a common point
of one piece with itself, the shared vertex of two consecutive pieces, or the centre of a `σ` column of `K`
(both pieces unchanged). -/
def MeetSpec (u v : Slot W) : Prop :=
  ∀ τ τ' : ℝ, 0 ≤ τ → τ ≤ 1 → 0 ≤ τ' → τ' ≤ 1 →
    segPt (mv u) (mv (next hW u)) τ = segPt (mv v) (mv (next hW v)) τ' →
    (u = v ∧ τ = τ') ∨ (v = next hW u ∧ τ = 1 ∧ τ' = 0) ∨ (u = next hW v ∧ τ = 0 ∧ τ' = 1) ∨
    (τ = 1 / 2 ∧ τ' = 1 / 2 ∧ SigmaMeet pl hW mv K u v)

theorem MeetSpec.symm {u v : Slot W} (h : MeetSpec pl hW mv K u v) : MeetSpec pl hW mv K v u := by
  intro τ τ' h0 h1 h0' h1' he
  rcases h τ' τ h0' h1' h0 h1 he.symm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h3, h2⟩))
  · exact Or.inr (Or.inl ⟨h1, h3, h2⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨h2, h1, h3.symm⟩))

/-- An affine combination of two numbers `≤ M` equal to `M` is an end with that end equal to `M`. -/
theorem affine_eq_max {a b M τ : ℝ} (ha : a ≤ M) (hb : b ≤ M) (hab : a ≠ b) (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (h : a + τ * (b - a) = M) : (τ = 0 ∧ a = M) ∨ (τ = 1 ∧ b = M) := by
  rcases ha.lt_or_eq with ha | ha
  · rcases hb.lt_or_eq with hb | hb
    · exfalso
      rcases h0.lt_or_eq with hτ | hτ
      · nlinarith [mul_pos hτ (sub_pos.2 hb), mul_nonneg (sub_nonneg.2 h1) (sub_pos.2 ha).le]
      · subst hτ; linarith
    · right; refine ⟨?_, hb⟩
      have : (τ - 1) * (a - M) = 0 := by linear_combination -h + τ * hb
      rcases mul_eq_zero.1 this with h' | h'
      · linarith
      · exfalso; linarith
  · left; refine ⟨?_, ha⟩
    have hb' : b < M := lt_of_le_of_ne hb (fun e => hab (ha.trans e.symm))
    have : τ * (b - a) = 0 := by linear_combination h - ha
    rcases mul_eq_zero.1 this with h' | h'
    · exact h'
    · exfalso; linarith

theorem affine_eq_min {a b M τ : ℝ} (ha : M ≤ a) (hb : M ≤ b) (hab : a ≠ b) (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (h : a + τ * (b - a) = M) : (τ = 0 ∧ a = M) ∨ (τ = 1 ∧ b = M) := by
  have := affine_eq_max (a := -a) (b := -b) (M := -M) (τ := τ) (by linarith) (by linarith)
    (fun h' => hab (by linarith)) h0 h1 (by linarith)
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, by linarith⟩
  · exact Or.inr ⟨h1, by linarith⟩

/-- A common point of two pieces in different columns (x-coordinates as in the realization) is a shared
vertex of consecutive pieces. -/
theorem meetSpec_of_col_lt (hinj : Function.Injective mv) (hx : ∀ u, (mv u).1 = (pt pl W u.1).1)
    {u v : Slot W} (hlt : colOf u < colOf v) : MeetSpec pl hW mv K u v := by
  intro τ τ' h0 h1 h0' h1' he
  have hxu := pt_fst_mem pl hW u
  have hxu' := pt_next_fst_mem pl hW u
  have hxv := pt_fst_mem pl hW v
  have hxv' := pt_next_fst_mem pl hW v
  have hneu := pt_fst_ne_pt_next_fst pl hW u
  have hnev := pt_fst_ne_pt_next_fst pl hW v
  have hmid : pl.x (colOf u + 1) ≤ pl.x (colOf v) := pl.x_le_x_iff.2 hlt
  have hef := congrArg Prod.fst he
  rw [segPt_fst, segPt_fst, hx u, hx (next hW u), hx v, hx (next hW v)] at hef
  have hu_le : (pt pl W u.1).1 + τ * ((pt pl W (next hW u).1).1 - (pt pl W u.1).1) ≤ pl.x (colOf u + 1) := by
    nlinarith
  have hv_ge : pl.x (colOf v) ≤ (pt pl W v.1).1 + τ' * ((pt pl W (next hW v).1).1 - (pt pl W v.1).1) := by
    nlinarith
  have hequ : (pt pl W u.1).1 + τ * ((pt pl W (next hW u).1).1 - (pt pl W u.1).1) = pl.x (colOf u + 1) := by
    linarith
  have heqv : (pt pl W v.1).1 + τ' * ((pt pl W (next hW v).1).1 - (pt pl W v.1).1) = pl.x (colOf v) := by
    linarith
  have hcu := affine_eq_max hxu.2 hxu'.2 hneu h0 h1 hequ
  have hcv := affine_eq_min hxv.1 hxv'.1 hnev h0' h1' heqv
  -- the common point is a vertex of both pieces
  have key : ∀ (a b : Slot W), τ = (if a = u then 0 else 1) → τ' = (if b = v then 0 else 1) →
      (a = u ∨ a = next hW u) → (b = v ∨ b = next hW v) → mv a = mv b → a = b := fun a b _ _ _ _ h => hinj h
  rcases hcu with ⟨hτ, -⟩ | ⟨hτ, -⟩ <;> rcases hcv with ⟨hτ', -⟩ | ⟨hτ', -⟩ <;> subst hτ hτ' <;>
    simp only [segPt_zero, segPt_one] at he
  · exact absurd (congrArg colOf (hinj he)) (ne_of_lt hlt)
  · exact Or.inr (Or.inr (Or.inl ⟨hinj he, rfl, rfl⟩))
  · exact Or.inr (Or.inl ⟨(hinj he).symm, rfl, rfl⟩)
  · exact absurd (congrArg colOf (next_injective hW (hinj he))) (ne_of_lt hlt)

theorem meetSpec_of_col_ne (hinj : Function.Injective mv) (hx : ∀ u, (mv u).1 = (pt pl W u.1).1)
    {u v : Slot W} (hne' : colOf u ≠ colOf v) : MeetSpec pl hW mv K u v := by
  rcases lt_or_gt_of_ne hne' with h | h
  · exact meetSpec_of_col_lt pl hW mv K hinj hx h
  · exact (meetSpec_of_col_lt pl hW mv K hinj hx h).symm

omit hne in
/-- `piecePt` is injective in the parameter. -/
theorem piecePt_param_injective (u : Slot W) {τ τ' : ℝ} (h : piecePt pl u τ = piecePt pl u τ') : τ = τ' :=
  (shapeOf u).par_injective (pl.A_injective _ h)

omit hne in
/-- The end parameters of an unchanged piece in the tail-to-head parametrization. -/
theorem segPt_unch_eq_pt {u : Slot W} (hu : Unch pl hW mv u) {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    {c : Slot W} (hc : c = u ∨ c = next hW u)
    (h : pt pl W c.1 = piecePt pl u (if xsign u then τ else 1 - τ)) : (c = u ∧ τ = 0) ∨ (c = next hW u ∧ τ = 1) := by
  rcases hc with rfl | rfl
  · left; refine ⟨rfl, ?_⟩
    rw [pt_eq_piecePt pl hW] at h
    have := piecePt_param_injective pl _ h
    split_ifs at this <;> linarith
  · right; refine ⟨rfl, ?_⟩
    rw [pt_next_eq_piecePt pl hW] at h
    have := piecePt_param_injective pl _ h
    split_ifs at this <;> linarith

/-- Two unchanged pieces satisfy the meeting specification, given that every `σ` column with both crossing
pieces unchanged is in `K` (the realization's `common_point`). -/
theorem meetSpec_of_unch {u v : Slot W} (hu : Unch pl hW mv u) (hv : Unch pl hW mv v)
    (hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      Unch pl hW mv (σSlotA hW hk hℓ) → Unch pl hW mv (σSlotB hW hk hℓ) → K k) :
    MeetSpec pl hW mv K u v := by
  intro τ τ' h0 h1 h0' h1' he
  rw [segPt_unch pl hW mv hu, segPt_unch pl hW mv hv] at he
  have hτ0 : (0 : ℝ) ≤ if xsign u then τ else 1 - τ := by split_ifs <;> linarith
  have hτ1 : (if xsign u then τ else 1 - τ) ≤ 1 := by split_ifs <;> linarith
  have hτ0' : (0 : ℝ) ≤ if xsign v then τ' else 1 - τ' := by split_ifs <;> linarith
  have hτ1' : (if xsign v then τ' else 1 - τ') ≤ 1 := by split_ifs <;> linarith
  rcases common_point pl hW u v hτ0 hτ1 hτ0' hτ1' he with ⟨huv, hτ⟩ | ⟨c, hc, hcu, hcv⟩ | ⟨hcol, hτ, hτ', m, hℓ, hS⟩
  · left
    subst huv
    refine ⟨rfl, ?_⟩
    split_ifs at hτ <;> linarith
  · have e1 := segPt_unch_eq_pt pl hW mv hu h0 h1 hcu hc
    have e2 := segPt_unch_eq_pt pl hW mv hv h0' h1' hcv (by rw [hc, he])
    rcases e1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases e2 with ⟨h', rfl⟩ | ⟨h', rfl⟩
    · exact Or.inl ⟨h', rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨h', rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨h'.symm, rfl, rfl⟩)
    · exact Or.inl ⟨next_injective hW h', rfl⟩
  · right; right; right
    have hτh : τ = 1 / 2 := by split_ifs at hτ <;> linarith
    have hτh' : τ' = 1 / 2 := by split_ifs at hτ' <;> linarith
    refine ⟨hτh, hτh', hu, hv, hcol, ?_, m, hℓ, hS⟩
    have hk : colOf u < W.length := U2.colOf_lt hW u
    have hA := σSlotA_spec hW hk hℓ
    have hB := σSlotB_spec hW hk hℓ
    rcases hS with ⟨hSu, hSv⟩ | ⟨hSu, hSv⟩
    · have eu : u = σSlotA hW hk hℓ := slot_eq_of_piece_eq hW pl hA.1.symm (hSu.trans hA.2.1.symm)
      have ev : v = σSlotB hW hk hℓ := slot_eq_of_piece_eq hW pl (hcol.symm.trans hB.1.symm) (hSv.trans hB.2.1.symm)
      exact hK _ m hk hℓ (eu ▸ hu) (ev ▸ hv)
    · have eu : u = σSlotB hW hk hℓ := slot_eq_of_piece_eq hW pl hB.1.symm (hSu.trans hB.2.1.symm)
      have ev : v = σSlotA hW hk hℓ := slot_eq_of_piece_eq hW pl (hcol.symm.trans hA.1.symm) (hSv.trans hA.2.1.symm)
      exact hK _ m hk hℓ (ev ▸ hv) (eu ▸ hu)

/-- The data making a moved slot diagram generic with crossings exactly the `σ` columns of `K`: injective
vertices with the realization's x-coordinates, and the meeting specification for same-column pairs
(different columns are automatic: `meetSpec_of_col_ne`; unchanged pairs: `meetSpec_of_unch`). -/
structure GenericData : Prop where
  inj : Function.Injective mv
  xcoord : ∀ u, (mv u).1 = (pt pl W u.1).1
  meet : ∀ u v, u ≠ v → colOf u = colOf v → MeetSpec pl hW mv K u v

theorem GenericData.meetSpec (d : GenericData pl hW mv K) {u v : Slot W} (huv : u ≠ v) : MeetSpec pl hW mv K u v := by
  by_cases hc : colOf u = colOf v
  · exact d.meet u v huv hc
  · exact meetSpec_of_col_ne pl hW mv K d.inj d.xcoord hc

omit hne in
/-- At a cusp vertex the two arm ends have the same x-coordinate. -/
theorem pt_prev_fst_eq_pt_next_fst_of_cusp {u : Slot W} (hu : u.1.2 = 0) :
    (pt pl W (prev hW u).1).1 = (pt pl W (next hW u).1).1 := by
  obtain ⟨k, hk⟩ : ∃ k, u.1 = (k, 0) := ⟨u.1.1, Prod.ext rfl hu⟩
  have hn : (next hW u).1 = nextPair W (k, 0) := by rw [next_val, hk]
  have hp : (prev hW u).1 = prevPair W (k, 0) := by rw [prev_val, hk]
  rcases letterAt_of_cusp (W := W) (s := u) hu with ⟨m, d, hℓ⟩ | ⟨m, hℓ⟩
  · rw [hk] at hℓ
    have hm : 1 ≤ m := by
      have := u.2; rw [hk] at this
      rcases this with ⟨-, hk', -⟩ | ⟨h0, -⟩
      · obtain ⟨D⟩ := decomp hW k hk'; rw [hℓ] at D; have := D.hm; simpa [idx] using this
      · simp at h0
    rw [hn, hp, nextPair_cusp_l W hℓ, prevPair_cusp_l W hℓ,
      pt_cut pl W (by split_ifs <;> omega), pt_cut pl W (by split_ifs <;> omega)]
  · rw [hk] at hℓ
    have hm : 1 ≤ m := by
      have := u.2; rw [hk] at this
      rcases this with ⟨-, hk', -⟩ | ⟨h0, -⟩
      · obtain ⟨D⟩ := decomp hW k hk'; rw [hℓ] at D; have := D.hm; simpa [idx] using this
      · simp at h0
    rw [hn, hp, nextPair_cusp_r W hℓ, prevPair_cusp_r W hℓ,
      pt_cut pl W (by split_ifs <;> omega), pt_cut pl W (by split_ifs <;> omega)]

/-- **Genericity** of a moved slot diagram from its `GenericData`. -/
theorem generic_of (d : GenericData pl hW mv K) : (shadowMv pl hW hne mv).Generic where
  regular i := by
    rw [regular_iff_edges]
    intro j
    set u := slotMv pl hW hne mv ⟨i, j⟩ with hu
    have hout : edge ((shadowMv pl hW hne mv).comp i).P j = mv (next hW u) - mv u := dir_mv pl hW hne mv ⟨i, j⟩
    have hin : edge ((shadowMv pl hW hne mv).comp i).P (j - 1) = mv u - mv (prev hW u) := by
      have e := dir_mv pl hW hne mv ⟨i, j - 1⟩
      have e2 : slotMv pl hW hne mv ⟨i, j - 1⟩ = prev hW u := toSlot_pred hW i j
      rw [e2, next_prev] at e
      exact e
    rw [hout, hin]
    have hx1 : (mv (next hW u) - mv u).1 = (pt pl W (next hW u).1).1 - (pt pl W u.1).1 := by
      rw [Prod.fst_sub, d.xcoord, d.xcoord]
    have hx2 : (mv u - mv (prev hW u)).1 = (pt pl W u.1).1 - (pt pl W (prev hW u).1).1 := by
      rw [Prod.fst_sub, d.xcoord, d.xcoord]
    have hne1 : (pt pl W (next hW u).1 - pt pl W u.1).1 ≠ 0 := dir_slot_fst_ne_zero pl hW u
    have hne2 : (pt pl W (next hW (prev hW u)).1 - pt pl W (prev hW u).1).1 ≠ 0 := dir_slot_fst_ne_zero pl hW (prev hW u)
    rw [next_prev] at hne2
    rw [Prod.fst_sub] at hne1 hne2
    refine ⟨fun h0 => hne1 (by rw [← hx1, h0]; rfl), ?_⟩
    rintro ⟨r, hr, hrv⟩
    have hf := congrArg Prod.fst hrv
    rw [Prod.smul_fst, smul_eq_mul, hx1, hx2] at hf
    by_cases hcusp : u.1.2 = 0
    · -- cusp: the arm ends share their x-coordinate, so `r = -1` and the arm ends coincide
      have hsym := pt_prev_fst_eq_pt_next_fst_of_cusp pl hW hcusp
      have hr1 : r = -1 := by
        have : (r + 1) * ((pt pl W u.1).1 - (pt pl W (prev hW u).1).1) = 0 := by rw [hsym] at hf ⊢; linarith
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact absurd h' hne2
      rw [hr1, neg_one_smul] at hrv
      have : mv (next hW u) = mv (prev hW u) := by
        have := congrArg (fun q => q + mv u) hrv
        simp only [sub_add_cancel, neg_sub, sub_add_cancel] at this
        exact this
      have h2 := d.inj this
      exact next_next_ne hW u (by rw [h2, next_prev])
    · -- cut slot: both edges point in the x-direction `xsign u`
      have hxs : xsign (prev hW u) = xsign u := by
        have := xsign_next_iff hW (prev hW u)
        rw [next_prev] at this
        exact (this.2 hcusp).symm
      have h1 := dir_slot_fst_pos_iff pl hW (prev hW u)
      rw [next_prev, hxs] at h1
      have h2 := dir_slot_fst_pos_iff pl hW u
      rw [Prod.fst_sub] at h1 h2
      cases hxu : xsign u
      · rw [hxu] at h1 h2
        have a1 : (pt pl W u.1).1 - (pt pl W (prev hW u).1).1 < 0 :=
          lt_of_le_of_ne (not_lt.1 (fun h => by simpa using h1.1 h)) hne2
        have a2 : (pt pl W (next hW u).1).1 - (pt pl W u.1).1 < 0 :=
          lt_of_le_of_ne (not_lt.1 (fun h => by simpa using h2.1 h)) hne1
        nlinarith
      · rw [hxu] at h1 h2
        have a1 : 0 < (pt pl W u.1).1 - (pt pl W (prev hW u).1).1 := h1.2 rfl
        have a2 : 0 < (pt pl W (next hW u).1).1 - (pt pl W u.1).1 := h2.2 rfl
        nlinarith
  tail_off s t hinc := by
    intro hmem
    rw [mem_seg_mv_iff] at hmem
    obtain ⟨τ', h0', h1', hq⟩ := hmem
    rw [tail_mv] at hq
    set u := slotMv pl hW hne mv s
    set v := slotMv pl hW hne mv t
    have huv : u ≠ v := fun h => hinc (incidentTail_mv_of pl hW hne mv s t (Or.inl h))
    have he : segPt (mv u) (mv (next hW u)) 0 = segPt (mv v) (mv (next hW v)) τ' := by rw [segPt_zero]; exact hq
    rcases d.meetSpec pl hW mv K huv 0 τ' le_rfl zero_le_one h0' h1' he with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩
    · exact huv h
    · norm_num at h
    · exact hinc (incidentTail_mv_of pl hW hne mv s t (Or.inr h))
    · norm_num at h
  transverse s t hna hmeet := by
    obtain ⟨q, hqs, hqt⟩ := hmeet
    rw [mem_seg_mv_iff] at hqs hqt
    obtain ⟨τ, h0, h1, rfl⟩ := hqs
    obtain ⟨τ', h0', h1', hq⟩ := hqt
    set u := slotMv pl hW hne mv s with hu
    set v := slotMv pl hW hne mv t with hv
    have huv : u ≠ v := by
      intro h
      have : s = t := slotMv_injective pl hW hne mv h
      subst this
      exact hna (Shadow.Adjacent.refl _ s)
    rcases d.meetSpec pl hW mv K huv τ τ' h0 h1 h0' h1' hq with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨hτ, hτ', hσ⟩
    · exact absurd h huv
    · exact absurd ((adjacent_mv_iff pl hW hne mv s t).2 (Or.inr (Or.inl h))) hna
    · exact absurd ((adjacent_mv_iff pl hW hne mv s t).2 (Or.inr (Or.inr (by show v = prev hW u; rw [h, prev_next])))) hna
    · obtain ⟨hUu, hUv, hcol, -, m, hℓ, hS⟩ := hσ
      rw [dir_mv, dir_mv, ← hu, ← hv, hUu.1, hUu.2, hUv.1, hUv.2, dir_slot_eq pl hW u, dir_slot_eq pl hW v, hcol]
      have hw := pl.w_pos (colOf v)
      rcases hS with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2, Shape.vec_pass, Shape.vec_pass] <;>
        cases xsign u <;> cases xsign v <;> simp [det] <;> intro h0 <;> nlinarith [hw]
  no_triple := by
    rintro ⟨s, t, r, hst, htr, hsr, q, ⟨hqs, hqt⟩, hqr⟩
    rw [mem_interior_mv_iff] at hqs hqt hqr
    obtain ⟨τ₁, h10, h11, rfl⟩ := hqs
    obtain ⟨τ₂, h20, h21, hq2⟩ := hqt
    obtain ⟨τ₃, h30, h31, hq3⟩ := hqr
    set u := slotMv pl hW hne mv s with hu
    set v := slotMv pl hW hne mv t with hv
    set w := slotMv pl hW hne mv r with hw
    have huv : u ≠ v := fun h => hst (slotMv_injective pl hW hne mv h)
    have huw : u ≠ w := fun h => hsr (slotMv_injective pl hW hne mv h)
    have key : ∀ (v' : Slot W) (τ' : ℝ), u ≠ v' → 0 < τ' → τ' < 1 →
        segPt (mv u) (mv (next hW u)) τ₁ = segPt (mv v') (mv (next hW v')) τ' →
        colOf u = colOf v' ∧ ∃ m, letterAt W (colOf u) = .σ m ∧
          ((shapeOf u = .pass m (m + 1) ∧ shapeOf v' = .pass (m + 1) m) ∨
           (shapeOf u = .pass (m + 1) m ∧ shapeOf v' = .pass m (m + 1))) := by
      intro v' τ' huv' h0' h1' he
      rcases d.meetSpec pl hW mv K huv' τ₁ τ' h10.le h11.le h0'.le h1'.le he with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ |
        ⟨-, -, -, -, hcol, -, m, hℓ, hS⟩
      · exact absurd h huv'
      · exact absurd h (ne_of_lt h11)
      · exact absurd h (ne_of_gt h10)
      · exact ⟨hcol, m, hℓ, hS⟩
    obtain ⟨hc12, m, hℓ, hS12⟩ := key v τ₂ huv h20 h21 hq2
    obtain ⟨hc13, m', hℓ', hS13⟩ := key w τ₃ huw h30 h31 hq3
    rw [hℓ] at hℓ'
    obtain rfl := Letter.σ.inj hℓ'
    have hsh : shapeOf v = shapeOf w := by
      rcases hS12 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hS13 with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
      · rw [h2, h2']
      · rw [h1] at h1'; cases h1'
      · rw [h1] at h1'; cases h1'
      · rw [h2, h2']
    exact htr (slotMv_injective pl hW hne mv (slot_eq_of_piece_eq hW pl (hc12.symm.trans hc13) hsh))

/-- The canonical over strand of a moved slot diagram: the descending crossing strand of the column. -/
def ovMv (x : (shadowMv pl hW hne mv).Crossing) : (shadowMv pl hW hne mv).Strand :=
  if h : ∃ s ∈ x.val, U2.isDesc (idxEquiv hW s) = true then h.choose
  else (Finset.card_pos.1 (by rw [(shadowMv pl hW hne mv).crossing_card_two x]; norm_num)).choose

theorem ovMv_mem (x : (shadowMv pl hW hne mv).Crossing) : ovMv pl hW hne mv x ∈ x.val := by
  unfold ovMv
  split_ifs with h
  · exact h.choose_spec.1
  · exact (Finset.card_pos.1 (by rw [(shadowMv pl hW hne mv).crossing_card_two x]; norm_num)).choose_spec

theorem ovMv_eq_of_σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m)
    (x : (shadowMv pl hW hne mv).Crossing) (hx : x.val = U2.σpair pl hW hne (vertsOf pl hW hne mv) hk hℓ) :
    ovMv pl hW hne mv x = U2.stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ) := by
  have h : ∃ s ∈ x.val, U2.isDesc (idxEquiv hW s) = true :=
    ⟨_, by rw [hx]; exact U2.mem_σpair_A pl hW hne _ hk hℓ, by rw [U2.idxEquiv_stStrand]; exact U2.isDesc_σSlotA hW hk hℓ⟩
  unfold ovMv
  rw [dite_eq_left h]
  obtain ⟨hmem, hdesc⟩ := h.choose_spec
  have hmem' : h.choose ∈ U2.σpair pl hW hne (vertsOf pl hW hne mv) hk hℓ := by rw [← hx]; exact hmem
  rw [U2.mem_σpair_iff] at hmem'
  rcases hmem' with hA | hB
  · exact (U2.eq_stStrand_iff pl hW hne _ _ _).2 hA
  · exfalso
    rw [hB, U2.isDesc_σSlotB] at hdesc
    exact Bool.false_ne_true hdesc

/-- The crossings of a moved slot diagram are exactly the `σ` pairs of the columns of `K` (given `GenericData`
and `K k ↔` both crossing pieces of column `k` unchanged). -/
theorem isCrossing_mv_iff (d : GenericData pl hW mv K)
    (hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      K k ↔ Unch pl hW mv (σSlotA hW hk hℓ) ∧ Unch pl hW mv (σSlotB hW hk hℓ))
    (x : Finset (shadowMv pl hW hne mv).Strand) :
    (shadowMv pl hW hne mv).IsCrossing x ↔
      ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k ∧ x = U2.σpair pl hW hne (vertsOf pl hW hne mv) hk hℓ := by
  constructor
  · rintro ⟨s, t, rfl, hna, q, hqs, hqt⟩
    rw [mem_seg_mv_iff] at hqs hqt
    obtain ⟨τ, h0, h1, rfl⟩ := hqs
    obtain ⟨τ', h0', h1', hq⟩ := hqt
    set u := slotMv pl hW hne mv s with hu
    set v := slotMv pl hW hne mv t with hv
    have huv : u ≠ v := by
      intro h
      have : s = t := slotMv_injective pl hW hne mv h
      subst this
      exact hna (Shadow.Adjacent.refl _ s)
    rcases d.meetSpec pl hW mv K huv τ τ' h0 h1 h0' h1' hq with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -, -⟩ | ⟨-, -, hσ⟩
    · exact absurd h huv
    · exact absurd ((adjacent_mv_iff pl hW hne mv s t).2 (Or.inr (Or.inl h))) hna
    · exact absurd ((adjacent_mv_iff pl hW hne mv s t).2 (Or.inr (Or.inr (by show v = prev hW u; rw [h, prev_next])))) hna
    · obtain ⟨-, -, hcol, hKk, m, hℓ, hS⟩ := hσ
      have hk : colOf u < W.length := U2.colOf_lt hW u
      refine ⟨colOf u, m, hk, hℓ, hKk, ?_⟩
      have hA := σSlotA_spec hW hk hℓ
      have hB := σSlotB_spec hW hk hℓ
      have es : s = U2.stStrand pl hW hne (vertsOf pl hW hne mv) u := (stStrand_slotMv pl hW hne mv s).symm
      have et : t = U2.stStrand pl hW hne (vertsOf pl hW hne mv) v := (stStrand_slotMv pl hW hne mv t).symm
      rcases hS with ⟨hSu, hSv⟩ | ⟨hSu, hSv⟩
      · have eu : u = σSlotA hW hk hℓ := slot_eq_of_piece_eq hW pl hA.1.symm (hSu.trans hA.2.1.symm)
        have ev : v = σSlotB hW hk hℓ := slot_eq_of_piece_eq hW pl (hcol.symm.trans hB.1.symm) (hSv.trans hB.2.1.symm)
        rw [es, et]
        exact congrArg₂ (fun a b : Slot W => ({U2.stStrand pl hW hne (vertsOf pl hW hne mv) a,
          U2.stStrand pl hW hne (vertsOf pl hW hne mv) b} : Finset _)) eu ev
      · have eu : u = σSlotB hW hk hℓ := slot_eq_of_piece_eq hW pl hB.1.symm (hSu.trans hB.2.1.symm)
        have ev : v = σSlotA hW hk hℓ := slot_eq_of_piece_eq hW pl (hcol.symm.trans hA.1.symm) (hSv.trans hA.2.1.symm)
        rw [es, et, Finset.pair_comm]
        exact congrArg₂ (fun a b : Slot W => ({U2.stStrand pl hW hne (vertsOf pl hW hne mv) a,
          U2.stStrand pl hW hne (vertsOf pl hW hne mv) b} : Finset _)) ev eu
  · rintro ⟨k, m, hk, hℓ, hKk, rfl⟩
    obtain ⟨hUA, hUB⟩ := (hK k m hk hℓ).1 hKk
    have hA := σSlotA_spec hW hk hℓ
    have hB := σSlotB_spec hW hk hℓ
    refine ⟨_, _, rfl, ?_, ⟨piecePt pl (σSlotA hW hk hℓ) (1 / 2), ?_, ?_⟩⟩
    · exact not_adjacent_of_σ pl hW hne (hA.1.trans hB.1.symm) (Or.inl ⟨hA.2.1, hB.2.1⟩)
    · rw [mem_seg_mv_iff, slotMv_stStrand]
      refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      rw [segPt_unch pl hW mv hUA]
      split_ifs <;> norm_num
    · rw [mem_seg_mv_iff, slotMv_stStrand, σ_meet pl hW hk hℓ]
      refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
      rw [segPt_unch pl hW mv hUB]
      split_ifs <;> norm_num

/-- The column of a crossing whose strand set is a `σ` pair is in `K`. -/
theorem K_of_σpair (d : GenericData pl hW mv K)
    (hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      K k ↔ Unch pl hW mv (σSlotA hW hk hℓ) ∧ Unch pl hW mv (σSlotB hW hk hℓ))
    {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) (x : (shadowMv pl hW hne mv).Crossing)
    (hx : x.val = U2.σpair pl hW hne (vertsOf pl hW hne mv) hk hℓ) : K k := by
  obtain ⟨k', m', hk', hℓ', hK', hx'⟩ := (isCrossing_mv_iff pl hW hne mv K d hK x.val).1 x.2
  have hmem : U2.stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ) ∈
      U2.σpair pl hW hne (vertsOf pl hW hne mv) hk' hℓ' := by
    rw [← hx', hx]; exact U2.mem_σpair_A pl hW hne _ hk hℓ
  have hc := U2.colOf_of_mem_σpair pl hW hne _ hk' hℓ' hmem
  rw [U2.idxEquiv_stStrand, (σSlotA_spec hW hk hℓ).1] at hc
  subst hc
  exact hK'

/-- **The crossing set of a moved slot diagram**: exactly the `σ` pairs of the columns of `K`, over strand the
descending one, the printed sign — given `GenericData` and `K k ↔` both crossing pieces of column `k` unchanged. -/
theorem slotDiagramData_of (d : GenericData pl hW mv K)
    (hK : ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m),
      K k ↔ Unch pl hW mv (σSlotA hW hk hℓ) ∧ Unch pl hW mv (σSlotB hW hk hℓ)) :
    U2.SlotDiagramData pl hW hne (vertsOf pl hW hne mv) (generic_of pl hW hne mv K d) (ovMv pl hW hne mv)
      (ovMv_mem pl hW hne mv) K where
  cross := isCrossing_mv_iff pl hW hne mv K d hK
  overStrand x k m hk hℓ hx := ovMv_eq_of_σpair pl hW hne mv hk hℓ x hx
  sgn x k m hk hℓ hx := by
    obtain ⟨hUA, hUB⟩ := (hK k m hk hℓ).1 (K_of_σpair pl hW hne mv K d hK hk hℓ x hx)
    have eov : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) (generic_of pl hW hne mv K d) (ovMv pl hW hne mv)
        (ovMv_mem pl hW hne mv)).overStrand x = U2.stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ) :=
      ovMv_eq_of_σpair pl hW hne mv hk hℓ x hx
    have eun : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) (generic_of pl hW hne mv K d) (ovMv pl hW hne mv)
        (ovMv_mem pl hW hne mv)).underStrand x = U2.stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotB hW hk hℓ) := by
      symm
      refine Diagram.eq_under_of_mem_of_ne (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) (generic_of pl hW hne mv K d)
        (ovMv pl hW hne mv) (ovMv_mem pl hW hne mv)) x ?_ ?_
      · show _ ∈ x.val
        rw [hx]; exact U2.mem_σpair_B pl hW hne _ hk hℓ
      · rw [eov]
        intro h
        exact σSlotA_ne_σSlotB hW hk hℓ (U2.stStrand_injective pl hW hne _ h).symm
    unfold Diagram.sign
    rw [eov, eun]
    have e1 : (shadowMv pl hW hne mv).dir (U2.stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ)) =
        pt pl W (next hW (σSlotA hW hk hℓ)).1 - pt pl W (σSlotA hW hk hℓ).1 := by
      rw [dir_mv, slotMv_stStrand, hUA.1, hUA.2]
    have e2 : (shadowMv pl hW hne mv).dir (U2.stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotB hW hk hℓ)) =
        pt pl W (next hW (σSlotB hW hk hℓ)).1 - pt pl W (σSlotB hW hk hℓ).1 := by
      rw [dir_mv, slotMv_stStrand, hUB.1, hUB.2]
    show ((SignType.sign (det ((shadowMv pl hW hne mv).dir (U2.stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotA hW hk hℓ)))
      ((shadowMv pl hW hne mv).dir (U2.stStrand pl hW hne (vertsOf pl hW hne mv) (σSlotB hW hk hℓ)))) : SignType) : ℤ) = _
    have hA := σSlotA_spec hW hk hℓ
    have hB := σSlotB_spec hW hk hℓ
    have hw := pl.w_pos k
    rw [e1, e2, dir_slot_eq pl hW, dir_slot_eq pl hW, hA.1, hB.1, hA.2.1, hB.2.1, Shape.vec_pass, Shape.vec_pass,
      hA.2.2, hB.2.2]
    have hpos : ∀ r : ℝ, 0 < r → ((SignType.sign r : SignType) : ℤ) = 1 := fun r hr => by rw [sign_pos hr]; rfl
    have hneg : ∀ r : ℝ, r < 0 → ((SignType.sign r : SignType) : ℤ) = -1 := fun r hr => by rw [sign_neg hr]; rfl
    cases bit W k m <;> cases bit W k (m + 1) <;> simp [det] <;>
      first
      | exact hpos _ (by linarith)
      | exact hneg _ (by linarith)

end Generic

/-! #### F. The move match: an outside/component match of two slot diagrams from a slot bijection -/

section Match

variable (L : List HalfPlane) (pl : Placement) {W W' : Word} (hW : W.Closed) (hW' : W'.Closed) (hne : W ≠ [])
  (hne' : W' ≠ []) (mv : Slot W → Plane) (mv' : Slot W' → Plane) (ψ : Slot W ≃ Slot W')

/-- The data of a slot bijection matching two slot diagrams outside a polygon: both classified; outside pieces
correspond; vertices not in the open polygon are kept; vertices in the open polygon correspond; the successor
commutes with the bijection on outside pieces. -/
structure MatchData : Prop where
  cl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u
  cl' : ∀ u', PieceIn L hW' mv' u' ∨ PieceOut L hW' mv' u'
  out_iff : ∀ u, PieceOut L hW mv u ↔ PieceOut L hW' mv' (ψ u)
  pt_eq : ∀ u, mv u ∉ interior (polygon L) → mv' (ψ u) = mv u
  int_iff : ∀ u, mv u ∈ interior (polygon L) ↔ mv' (ψ u) ∈ interior (polygon L)
  next_eq : ∀ u, PieceOut L hW mv u → ψ (next hW u) = next hW' (ψ u)

/-- The strand map induced by the slot bijection (the strands are the slots, typed by the two words). -/
def ψStr (s : (shadowMv pl hW hne mv).Strand) : (shadowMv pl hW' hne' mv').Strand := (idxEquiv hW').symm (ψ (idxEquiv hW s))

theorem slotMv_ψStr (s : (shadowMv pl hW hne mv).Strand) :
    slotMv pl hW' hne' mv' (ψStr pl hW hW' hne hne' mv mv' ψ s) = ψ (slotMv pl hW hne mv s) :=
  Equiv.apply_symm_apply _ _

theorem ψStr_symm_ψStr (s : (shadowMv pl hW hne mv).Strand) :
    ψStr pl hW' hW hne' hne mv' mv ψ.symm (ψStr pl hW hW' hne hne' mv mv' ψ s) = s := by
  show (idxEquiv hW).symm (ψ.symm (idxEquiv hW' ((idxEquiv hW').symm (ψ (idxEquiv hW s))))) = s
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  exact (idxEquiv hW).symm_apply_apply s

theorem ψStr_injective : Function.Injective (ψStr pl hW hW' hne hne' mv mv' ψ) := fun s t h => by
  have := congrArg (ψStr pl hW' hW hne' hne mv' mv ψ.symm) h
  rwa [ψStr_symm_ψStr, ψStr_symm_ψStr] at this

theorem ψStr_strandMv (u : Slot W) :
    ψStr pl hW hW' hne hne' mv mv' ψ (strandMv pl hW hne mv u) = strandMv pl hW' hne' mv' (ψ u) := by
  unfold ψStr
  rw [U2.idxEquiv_stStrand]; rfl

/-- The traversal-point map: the same parameter on the corresponding strand. -/
def ψPt (p : (shadowMv pl hW hne mv).Pt) : (shadowMv pl hW' hne' mv').Pt :=
  ⟨(ψStr pl hW hW' hne hne' mv mv' ψ ⟨p.1, p.2.1⟩).1, ((ψStr pl hW hW' hne hne' mv mv' ψ ⟨p.1, p.2.1⟩).2, p.2.2)⟩

theorem ψPt_travMv (u : Slot W) (t : Set.Ico (0 : ℝ) 1) :
    ψPt pl hW hW' hne hne' mv mv' ψ (travMv pl hW hne mv u t) = travMv pl hW' hne' mv' (ψ u) t := by
  unfold ψPt
  have e : ψStr pl hW hW' hne hne' mv mv' ψ ⟨(strandMv pl hW hne mv u).1, (strandMv pl hW hne mv u).2⟩ =
      strandMv pl hW' hne' mv' (ψ u) := ψStr_strandMv pl hW hW' hne hne' mv mv' ψ u
  rw [e]

theorem slotPtMv_ψPt (p : (shadowMv pl hW hne mv).Pt) :
    slotPtMv pl hW' hne' mv' (ψPt pl hW hW' hne hne' mv mv' ψ p) = ψ (slotPtMv pl hW hne mv p) :=
  slotMv_ψStr pl hW hW' hne hne' mv mv' ψ _

theorem ψPt_param (p : (shadowMv pl hW hne mv).Pt) : (ψPt pl hW hW' hne hne' mv mv' ψ p).2.2 = p.2.2 := rfl

theorem ψPt_symm_ψPt (p : (shadowMv pl hW hne mv).Pt) :
    ψPt pl hW' hW hne' hne mv' mv ψ.symm (ψPt pl hW hW' hne hne' mv mv' ψ p) = p := by
  conv_lhs => rw [← travMv_slotPtMv pl hW hne mv p]
  rw [ψPt_travMv, ψPt_travMv, Equiv.symm_apply_apply, travMv_slotPtMv]

theorem eval_ψPt (p : (shadowMv pl hW hne mv).Pt) :
    (shadowMv pl hW' hne' mv').eval (ψPt pl hW hW' hne hne' mv mv' ψ p) =
      segPt (mv' (ψ (slotPtMv pl hW hne mv p))) (mv' (next hW' (ψ (slotPtMv pl hW hne mv p)))) p.2.2.val := by
  rw [eval_mv, slotPtMv_ψPt]; rfl

/-- The image of a strand set under the strand map. -/
def ψFin (x : Finset (shadowMv pl hW hne mv).Strand) : Finset (shadowMv pl hW' hne' mv').Strand :=
  x.map ⟨ψStr pl hW hW' hne hne' mv mv' ψ, ψStr_injective pl hW hW' hne hne' mv mv' ψ⟩

theorem ψFin_pair (s t : (shadowMv pl hW hne mv).Strand) :
    ψFin pl hW hW' hne hne' mv mv' ψ {s, t} = {ψStr pl hW hW' hne hne' mv mv' ψ s, ψStr pl hW hW' hne hne' mv mv' ψ t} := by
  unfold ψFin
  rw [Finset.map_insert, Finset.map_singleton]; rfl

theorem ψFin_symm_ψFin (x : Finset (shadowMv pl hW hne mv).Strand) :
    ψFin pl hW' hW hne' hne mv' mv ψ.symm (ψFin pl hW hW' hne hne' mv mv' ψ x) = x := by
  ext s
  simp only [ψFin, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    rw [ψStr_symm_ψStr]; exact hb
  · intro hs
    exact ⟨_, ⟨s, hs, rfl⟩, ψStr_symm_ψStr pl hW hW' hne hne' mv mv' ψ s⟩

theorem ψFin_σpair {k m : ℕ} (hk : k < W.length) (hℓ : letterAt W k = .σ m) {k' m' : ℕ} (hk' : k' < W'.length)
    (hℓ' : letterAt W' k' = .σ m') (hA : ψ (σSlotA hW hk hℓ) = σSlotA hW' hk' hℓ') (hB : ψ (σSlotB hW hk hℓ) = σSlotB hW' hk' hℓ') :
    ψFin pl hW hW' hne hne' mv mv' ψ (U2.σpair pl hW hne (vertsOf pl hW hne mv) hk hℓ) =
      U2.σpair pl hW' hne' (vertsOf pl hW' hne' mv') hk' hℓ' := by
  rw [U2.σpair, ψFin_pair, ψStr_strandMv, ψStr_strandMv, hA, hB]

/-- The strand arriving at the tail vertex of a strand corresponds to the predecessor slot. -/
theorem slotMv_pred (i : Fin (shadowMv pl hW hne mv).c) (j : ZMod ((shadowMv pl hW hne mv).comp i).k) :
    slotMv pl hW hne mv ⟨i, j - 1⟩ = prev hW (slotMv pl hW hne mv ⟨i, j⟩) := toSlot_pred hW i j

/-- A piece with a point strictly outside the polygon is an outside piece. -/
theorem pieceOut_of_notMem (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u) {u : Slot W} {t : ℝ} (h0 : 0 ≤ t)
    (h1 : t ≤ 1) (h : segPt (mv u) (mv (next hW u)) t ∉ polygon L) : PieceOut L hW mv u :=
  (hcl u).resolve_left (fun hin => h (hin.mem h0 h1))

/-- The crossing point of a crossing of a classified slot diagram is outside the open polygon iff its pieces are
outside pieces. -/
theorem crossingPoint_notMem_interior_iff (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u)
    (hgen : (shadowMv pl hW hne mv).Generic) (x : (shadowMv pl hW hne mv).Crossing)
    {s : (shadowMv pl hW hne mv).Strand} (hs : s ∈ x.val) :
    (shadowMv pl hW hne mv).crossingPoint x ∉ interior (polygon L) ↔ PieceOut L hW mv (slotMv pl hW hne mv s) := by
  have hmem := hgen.crossingPoint_mem_interior x hs
  rw [mem_interior_mv_iff] at hmem
  obtain ⟨t, h0, h1, ht⟩ := hmem
  rw [ht]
  constructor
  · intro h
    rcases hcl (slotMv pl hW hne mv s) with hin | hout
    · exact absurd (hin.mem_interior h0 h1) h
    · exact hout
  · intro hout h
    exact hout.notMem h0 h1 (interior_subset h)

/-- The correspondence of the outer `σ` columns: an outer crossing column of the first diagram goes to an
outer crossing column of the second with the two crossing slots corresponding. -/
def SigmaCorr (K K' : ℕ → Prop) : Prop :=
  ∀ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k → PieceOut L hW mv (σSlotA hW hk hℓ) →
    ∃ (k' m' : ℕ) (hk' : k' < W'.length) (hℓ' : letterAt W' k' = .σ m'), K' k' ∧
      ψ (σSlotA hW hk hℓ) = σSlotA hW' hk' hℓ' ∧ ψ (σSlotB hW hk hℓ) = σSlotB hW' hk' hℓ'

variable {L hW hW' mv mv' ψ}

theorem MatchData.symm (M : MatchData L hW hW' mv mv' ψ) : MatchData L hW' hW mv' mv ψ.symm where
  cl := M.cl'
  cl' := M.cl
  out_iff u' := by rw [M.out_iff (ψ.symm u'), Equiv.apply_symm_apply]
  pt_eq u' h := by
    have h' : mv (ψ.symm u') ∉ interior (polygon L) := by
      rw [M.int_iff (ψ.symm u'), Equiv.apply_symm_apply]; exact h
    have := M.pt_eq _ h'
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  int_iff u' := by rw [M.int_iff (ψ.symm u'), Equiv.apply_symm_apply]
  next_eq u' h := by
    have h' : PieceOut L hW mv (ψ.symm u') := by rw [M.out_iff, Equiv.apply_symm_apply]; exact h
    have := M.next_eq _ h'
    rw [Equiv.apply_symm_apply] at this
    rw [← this, Equiv.symm_apply_apply]

/-- On an outside piece the two ends are kept. -/
theorem MatchData.mv_eq_of_out (M : MatchData L hW hW' mv mv' ψ) {u : Slot W} (hu : PieceOut L hW mv u) :
    mv' (ψ u) = mv u := M.pt_eq u hu.left_notMem_interior

theorem MatchData.mv_next_eq_of_out (M : MatchData L hW hW' mv mv' ψ) {u : Slot W} (hu : PieceOut L hW mv u) :
    mv' (next hW' (ψ u)) = mv (next hW u) := by
  rw [← M.next_eq u hu]
  exact M.pt_eq _ hu.right_notMem_interior

theorem MatchData.segPt_eq_of_out (M : MatchData L hW hW' mv mv' ψ) {u : Slot W} (hu : PieceOut L hW mv u) (t : ℝ) :
    segPt (mv' (ψ u)) (mv' (next hW' (ψ u))) t = segPt (mv u) (mv (next hW u)) t := by
  rw [M.mv_eq_of_out hu, M.mv_next_eq_of_out hu]

theorem MatchData.pieceIn_of_not_out (M : MatchData L hW hW' mv mv' ψ) {u : Slot W} (hu : ¬ PieceOut L hW mv u) :
    PieceIn L hW mv u := (M.cl u).resolve_right hu

theorem MatchData.pieceIn'_of_not_out (M : MatchData L hW hW' mv mv' ψ) {u : Slot W} (hu : ¬ PieceOut L hW mv u) :
    PieceIn L hW' mv' (ψ u) := (M.cl' (ψ u)).resolve_right (fun h => hu ((M.out_iff u).2 h))

variable (M : MatchData L hW hW' mv mv' ψ)
include M

/-- The outside points correspond. -/
theorem MatchData.outside_iff (p : (shadowMv pl hW hne mv).Pt) :
    (shadowMv pl hW' hne' mv').eval (ψPt pl hW hW' hne hne' mv mv' ψ p) ∉ interior (polygon L) ↔
      (shadowMv pl hW hne mv).eval p ∉ interior (polygon L) := by
  rw [eval_ψPt, eval_mv]
  set u := slotPtMv pl hW hne mv p
  have ht := p.2.2.2
  by_cases hout : PieceOut L hW mv u
  · rw [M.segPt_eq_of_out hout]
  · have hin := M.pieceIn_of_not_out hout
    have hin' := M.pieceIn'_of_not_out hout
    rcases ht.1.lt_or_eq with h0 | h0
    · exact iff_of_false (fun h => h (hin'.mem_interior h0 ht.2)) (fun h => h (hin.mem_interior h0 ht.2))
    · rw [← h0, segPt_zero, segPt_zero]
      exact not_congr (M.int_iff u).symm

/-- The evaluation is kept on outside points. -/
theorem MatchData.eval_ψPt_of_outside (p : (shadowMv pl hW hne mv).Pt)
    (hp : (shadowMv pl hW hne mv).eval p ∉ interior (polygon L)) :
    (shadowMv pl hW' hne' mv').eval (ψPt pl hW hW' hne hne' mv mv' ψ p) = (shadowMv pl hW hne mv).eval p := by
  rw [eval_ψPt, eval_mv]
  set u := slotPtMv pl hW hne mv p
  have ht := p.2.2.2
  by_cases hout : PieceOut L hW mv u
  · exact M.segPt_eq_of_out hout _
  · have hin := M.pieceIn_of_not_out hout
    rw [eval_mv] at hp
    rcases ht.1.lt_or_eq with h0 | h0
    · exact absurd (hin.mem_interior h0 ht.2) hp
    · rw [← h0, segPt_zero] at hp ⊢
      rw [segPt_zero, M.pt_eq u hp]

/-- **The outside-point correspondence.** -/
def MatchData.outEquiv :
    (shadowMv pl hW hne mv).Outside (polygon L) ≃ (shadowMv pl hW' hne' mv').Outside (polygon L) where
  toFun p := ⟨ψPt pl hW hW' hne hne' mv mv' ψ p.1, (M.outside_iff pl hne hne' p.1).2 p.2⟩
  invFun q := ⟨ψPt pl hW' hW hne' hne mv' mv ψ.symm q.1, (M.symm.outside_iff pl hne' hne q.1).2 q.2⟩
  left_inv p := Subtype.ext (ψPt_symm_ψPt pl hW hW' hne hne' mv mv' ψ p.1)
  right_inv q := Subtype.ext (by
    have := ψPt_symm_ψPt pl hW' hW hne' hne mv' mv ψ.symm q.1
    rwa [Equiv.symm_symm] at this)

theorem MatchData.outEquiv_apply (p : (shadowMv pl hW hne mv).Outside (polygon L)) :
    (M.outEquiv pl hne hne' p).1 = ψPt pl hW hW' hne hne' mv mv' ψ p.1 := rfl

/-- A traversal point strictly outside the polygon lies on an outside piece. -/
theorem MatchData.pieceOut_of_eval_notMem (p : (shadowMv pl hW hne mv).Pt)
    (hp : (shadowMv pl hW hne mv).eval p ∉ polygon L) : PieceOut L hW mv (slotPtMv pl hW hne mv p) := by
  rw [eval_mv] at hp
  exact pieceOut_of_notMem L hW mv M.cl p.2.2.2.1 p.2.2.2.2.le hp

/-- The forward direction is kept at points strictly outside. -/
theorem MatchData.dir_ψPt (p : (shadowMv pl hW hne mv).Pt) (hp : (shadowMv pl hW hne mv).eval p ∉ polygon L) :
    (shadowMv pl hW' hne' mv').dir ((shadowMv pl hW' hne' mv').strandOf (ψPt pl hW hW' hne hne' mv mv' ψ p)) =
      (shadowMv pl hW hne mv).dir ((shadowMv pl hW hne mv).strandOf p) := by
  have hout := M.pieceOut_of_eval_notMem pl hne p hp
  obtain ⟨i, j, t⟩ := p
  rw [Shadow.strandOf_mk, Shadow.strandOf_mk, dir_mv, dir_mv]
  show mv' (next hW' (slotMv pl hW' hne' mv' (ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩))) -
    mv' (slotMv pl hW' hne' mv' (ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩)) = _
  rw [slotMv_ψStr]
  have hout' : PieceOut L hW mv (slotMv pl hW hne mv ⟨i, j⟩) := hout
  rw [M.mv_eq_of_out hout', M.mv_next_eq_of_out hout']

/-- The arriving direction is kept at points strictly outside. -/
theorem MatchData.dir_before_ψPt (p : (shadowMv pl hW hne mv).Pt) (hp : (shadowMv pl hW hne mv).eval p ∉ polygon L) :
    (shadowMv pl hW' hne' mv').dir ((shadowMv pl hW' hne' mv').strandBefore (ψPt pl hW hW' hne hne' mv mv' ψ p)) =
      (shadowMv pl hW hne mv).dir ((shadowMv pl hW hne mv).strandBefore p) := by
  by_cases ht : p.2.2.val = 0
  · have ht' : (ψPt pl hW hW' hne hne' mv mv' ψ p).2.2.val = 0 := ht
    rw [Shadow.strandBefore_of_zero _ p ht, Shadow.strandBefore_of_zero _ _ ht']
    obtain ⟨i, j, t⟩ := p
    set u := slotMv pl hW hne mv ⟨i, j⟩ with hu
    -- the point is the tail vertex `mv u`, strictly outside: the previous piece is outside
    have hmv : mv u ∉ polygon L := by
      rw [eval_mv] at hp
      have ht0 : t.val = 0 := ht
      rw [ht0, segPt_zero] at hp
      exact hp
    have hprev : PieceOut L hW mv (prev hW u) := by
      refine pieceOut_of_notMem L hW mv M.cl (t := 1) zero_le_one le_rfl ?_
      rw [segPt_one, next_prev]; exact hmv
    have hψprev : ψ (prev hW u) = prev hW' (ψ u) := by
      have := M.next_eq _ hprev
      rw [next_prev] at this
      rw [this, prev_next]
    obtain ⟨⟨i', j'⟩, hs⟩ : ∃ s', ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩ = s' := ⟨_, rfl⟩
    show (shadowMv pl hW' hne' mv').dir ⟨(ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩).1,
      (ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩).2 - 1⟩ = (shadowMv pl hW hne mv).dir ⟨i, j - 1⟩
    rw [hs]
    rw [dir_mv, dir_mv, slotMv_pred, slotMv_pred, ← hu, next_prev, next_prev]
    have e : slotMv pl hW' hne' mv' ⟨i', j'⟩ = ψ u := by rw [← hs, slotMv_ψStr]
    have e2 : mv' (ψ u) = mv u := by
      have h := M.mv_next_eq_of_out hprev
      rw [next_prev, hψprev, next_prev] at h
      exact h
    rw [e, ← hψprev, M.mv_eq_of_out hprev, e2]
  · have ht' : (ψPt pl hW hW' hne hne' mv mv' ψ p).2.2.val ≠ 0 := ht
    rw [Shadow.strandBefore_of_ne_zero _ p ht, Shadow.strandBefore_of_ne_zero _ _ ht']
    exact M.dir_ψPt pl hne hne' p hp

/-! ##### The outer crossings -/

variable (hgen : (shadowMv pl hW hne mv).Generic) (ov : (shadowMv pl hW hne mv).Crossing → (shadowMv pl hW hne mv).Strand)
  (hov : ∀ x, ov x ∈ x.val) (K : ℕ → Prop) (data : U2.SlotDiagramData pl hW hne (vertsOf pl hW hne mv) hgen ov hov K)
  (hgen' : (shadowMv pl hW' hne' mv').Generic) (ov' : (shadowMv pl hW' hne' mv').Crossing → (shadowMv pl hW' hne' mv').Strand)
  (hov' : ∀ x, ov' x ∈ x.val) (K' : ℕ → Prop) (data' : U2.SlotDiagramData pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov' K')

variable (hσ : SigmaCorr L hW hW' mv ψ K K')
include data data' hσ

/-- The corresponding outer crossing. -/
def MatchData.crossMap (x : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L)) :
    (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').OuterCrossing (polygon L) := by
  refine ⟨⟨ψFin pl hW hW' hne hne' mv mv' ψ x.1.val, ?_⟩, ?_⟩
  · obtain ⟨k, m, hk, hℓ, hKk, hx⟩ := (data.cross x.1.val).1 x.1.2
    have hout : PieceOut L hW mv (σSlotA hW hk hℓ) := by
      have := (crossingPoint_notMem_interior_iff L pl hW hne mv M.cl hgen x.1 (s := strandMv pl hW hne mv (σSlotA hW hk hℓ))
        (by rw [hx]; exact U2.mem_σpair_A pl hW hne _ hk hℓ)).1 x.2
      rwa [slotMv_stStrand] at this
    obtain ⟨k', m', hk', hℓ', hK', hA, hB⟩ := hσ k m hk hℓ hKk hout
    rw [hx, ψFin_σpair pl hW hW' hne hne' mv mv' ψ hk hℓ hk' hℓ' hA hB]
    exact (data'.cross _).2 ⟨k', m', hk', hℓ', hK', rfl⟩
  · obtain ⟨k, m, hk, hℓ, hKk, hx⟩ := (data.cross x.1.val).1 x.1.2
    have hout : PieceOut L hW mv (σSlotA hW hk hℓ) := by
      have := (crossingPoint_notMem_interior_iff L pl hW hne mv M.cl hgen x.1 (s := strandMv pl hW hne mv (σSlotA hW hk hℓ))
        (by rw [hx]; exact U2.mem_σpair_A pl hW hne _ hk hℓ)).1 x.2
      rwa [slotMv_stStrand] at this
    have hout' : PieceOut L hW' mv' (ψ (σSlotA hW hk hℓ)) := (M.out_iff _).1 hout
    refine (crossingPoint_notMem_interior_iff L pl hW' hne' mv' M.cl' hgen' _
      (s := strandMv pl hW' hne' mv' (ψ (σSlotA hW hk hℓ))) ?_).2 ?_
    · show _ ∈ ψFin pl hW hW' hne hne' mv mv' ψ x.1.val
      rw [hx, U2.σpair, ψFin_pair, ψStr_strandMv]
      exact Finset.mem_insert_self _ _
    · rw [slotMv_stStrand]; exact hout'

theorem MatchData.crossMap_val (x : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L)) :
    (M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x).1.val = ψFin pl hW hW' hne hne' mv mv' ψ x.1.val := rfl

omit data data' hσ in
/-- On an outside piece the corresponding strands trace the same segment. -/
theorem MatchData.seg_eq_of_out {u : Slot W} (hu : PieceOut L hW mv u) :
    (shadowMv pl hW' hne' mv').seg (strandMv pl hW' hne' mv' (ψ u)) = (shadowMv pl hW hne mv).seg (strandMv pl hW hne mv u) := by
  ext q
  rw [mem_seg_mv_iff, mem_seg_mv_iff, slotMv_stStrand, slotMv_stStrand]
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, M.segPt_eq_of_out hu t⟩
  · rintro ⟨t, h0, h1, rfl⟩
    exact ⟨t, h0, h1, (M.segPt_eq_of_out hu t).symm⟩

/-- The column data of an outer crossing: its `σ` column (in `K`), the outside crossing pieces, and the
corresponding column of the second diagram. -/
theorem MatchData.outer_spec (x : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L)) :
    ∃ (k m : ℕ) (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k ∧
      x.1.val = U2.σpair pl hW hne (vertsOf pl hW hne mv) hk hℓ ∧
      PieceOut L hW mv (σSlotA hW hk hℓ) ∧ PieceOut L hW mv (σSlotB hW hk hℓ) ∧
      ∃ (k' m' : ℕ) (hk' : k' < W'.length) (hℓ' : letterAt W' k' = .σ m'), K' k' ∧
        ψ (σSlotA hW hk hℓ) = σSlotA hW' hk' hℓ' ∧ ψ (σSlotB hW hk hℓ) = σSlotB hW' hk' hℓ' ∧
        (M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x).1.val =
          U2.σpair pl hW' hne' (vertsOf pl hW' hne' mv') hk' hℓ' := by
  obtain ⟨k, m, hk, hℓ, hKk, hx⟩ := (data.cross x.1.val).1 x.1.2
  have houtA : PieceOut L hW mv (σSlotA hW hk hℓ) := by
    have := (crossingPoint_notMem_interior_iff L pl hW hne mv M.cl hgen x.1 (s := strandMv pl hW hne mv (σSlotA hW hk hℓ))
      (by rw [hx]; exact U2.mem_σpair_A pl hW hne _ hk hℓ)).1 x.2
    rwa [slotMv_stStrand] at this
  have houtB : PieceOut L hW mv (σSlotB hW hk hℓ) := by
    have := (crossingPoint_notMem_interior_iff L pl hW hne mv M.cl hgen x.1 (s := strandMv pl hW hne mv (σSlotB hW hk hℓ))
      (by rw [hx]; exact U2.mem_σpair_B pl hW hne _ hk hℓ)).1 x.2
    rwa [slotMv_stStrand] at this
  obtain ⟨k', m', hk', hℓ', hK', hA, hB⟩ := hσ k m hk hℓ hKk houtA
  refine ⟨k, m, hk, hℓ, hKk, hx, houtA, houtB, k', m', hk', hℓ', hK', hA, hB, ?_⟩
  rw [MatchData.crossMap_val, hx, ψFin_σpair pl hW hW' hne hne' mv mv' ψ hk hℓ hk' hℓ' hA hB]

/-- The corresponding outer crossing has the same double point. -/
theorem MatchData.crossingPoint_crossMap (x : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L)) :
    (shadowMv pl hW' hne' mv').crossingPoint (M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x).1 =
      (shadowMv pl hW hne mv).crossingPoint x.1 := by
  obtain ⟨k, m, hk, hℓ, -, hx, houtA, houtB, k', m', hk', hℓ', -, hA, hB, hx'⟩ :=
    M.outer_spec pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x
  set y := M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x
  apply hgen.common_point_unique x.1
  intro s hs
  rw [hx, U2.mem_σpair_iff] at hs
  rcases hs with h | h
  · have es : s = strandMv pl hW hne mv (σSlotA hW hk hℓ) := (U2.eq_stStrand_iff pl hW hne _ s _).2 h
    rw [es, ← M.seg_eq_of_out pl hne hne' houtA, hA]
    exact (shadowMv pl hW' hne' mv').crossingPoint_mem y.1 (by rw [hx']; exact U2.mem_σpair_A pl hW' hne' _ hk' hℓ')
  · have es : s = strandMv pl hW hne mv (σSlotB hW hk hℓ) := (U2.eq_stStrand_iff pl hW hne _ s _).2 h
    rw [es, ← M.seg_eq_of_out pl hne hne' houtB, hB]
    exact (shadowMv pl hW' hne' mv').crossingPoint_mem y.1 (by rw [hx']; exact U2.mem_σpair_B pl hW' hne' _ hk' hℓ')

/-- The crossing parameter on corresponding outside strands is the same. -/
theorem MatchData.crossingParam_crossMap (x : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L))
    {u : Slot W} (hu : PieceOut L hW mv u) (hs : strandMv pl hW hne mv u ∈ x.1.val)
    (hs' : strandMv pl hW' hne' mv' (ψ u) ∈ (M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x).1.val) :
    (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').crossingParam _ hs' =
      (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).crossingParam x.1 hs := by
  set cp := (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).crossingParam x.1 hs with hcp
  set cp' := (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').crossingParam _ hs' with hcp'
  obtain ⟨-, -, e⟩ := (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).crossingParam_spec x.1 hs
  obtain ⟨-, -, e'⟩ := (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').crossingParam_spec _ hs'
  rw [M.crossingPoint_crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x] at e'
  rw [← hcp] at e
  rw [← hcp'] at e'
  have e1 : edgePoint ((shadowMv pl hW hne mv).comp (strandMv pl hW hne mv u).1).P (strandMv pl hW hne mv u).2 cp =
      segPt (mv u) (mv (next hW u)) cp := by rw [edgePoint_mv, slotMv_stStrand]
  have e2 : edgePoint ((shadowMv pl hW' hne' mv').comp (strandMv pl hW' hne' mv' (ψ u)).1).P (strandMv pl hW' hne' mv' (ψ u)).2 cp' =
      segPt (mv u) (mv (next hW u)) cp' := by rw [edgePoint_mv, slotMv_stStrand, M.segPt_eq_of_out hu]
  have hne0 : mv u ≠ mv (next hW u) := by
    intro h
    have := (shadowMv pl hW hne mv).edge_ne_zero hgen (strandMv pl hW hne mv u)
    rw [dir_mv, slotMv_stStrand, h, sub_self] at this
    exact this rfl
  apply segPt_injective hne0
  rw [← e1, ← e2, ← e, ← e']

omit M hov data hov' data' hσ in
/-- Traversal points with the same strand and the same parameter coincide. -/
theorem pt_ext' {Γ : Shadow} {p q : Γ.Pt} (h1 : (⟨p.1, p.2.1⟩ : Γ.Strand) = ⟨q.1, q.2.1⟩) (h2 : p.2.2.val = q.2.2.val) :
    p = q := by
  obtain ⟨i, j, t⟩ := p
  obtain ⟨i', j', t'⟩ := q
  simp only at h1 h2
  cases h1
  exact congrArg (fun t : Set.Ico (0 : ℝ) 1 => (⟨i, (j, t)⟩ : Γ.Pt)) (Subtype.ext h2)

/-- The over occurrence of an outer crossing corresponds. -/
theorem MatchData.ψPt_over (x : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L)) :
    ψPt pl hW hW' hne hne' mv mv' ψ
        ((U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).visitPt
          ((U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).overVisit x.1)) =
      (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').visitPt
        ((U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').overVisit
          (M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x).1) := by
  obtain ⟨k, m, hk, hℓ, -, hx, houtA, -, k', m', hk', hℓ', -, hA, -, hx'⟩ :=
    M.outer_spec pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x
  set y := M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x
  have eov : ov x.1 = strandMv pl hW hne mv (σSlotA hW hk hℓ) := data.overStrand x.1 k m hk hℓ hx
  have eov' : ov' y.1 = strandMv pl hW' hne' mv' (ψ (σSlotA hW hk hℓ)) := by
    rw [hA]; exact data'.overStrand y.1 k' m' hk' hℓ' hx'
  have hsA : strandMv pl hW hne mv (σSlotA hW hk hℓ) ∈ x.1.val := by rw [hx]; exact U2.mem_σpair_A pl hW hne _ hk hℓ
  have hsA' : strandMv pl hW' hne' mv' (ψ (σSlotA hW hk hℓ)) ∈ y.1.val := by
    rw [hx', hA]; exact U2.mem_σpair_A pl hW' hne' _ hk' hℓ'
  have hcp := M.crossingParam_crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x houtA hsA hsA'
  have key : ∀ (s : (shadowMv pl hW hne mv).Strand) (hs : s ∈ x.1.val) (s' : (shadowMv pl hW' hne' mv').Strand)
      (hs' : s' ∈ y.1.val), s = strandMv pl hW hne mv (σSlotA hW hk hℓ) →
      s' = strandMv pl hW' hne' mv' (ψ (σSlotA hW hk hℓ)) →
      (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').crossingParam y.1 hs' = (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).crossingParam x.1 hs := by
    intro s hs s' hs' e e'
    subst e; subst e'
    exact hcp
  unfold Diagram.visitPt Diagram.overVisit ψPt
  apply pt_ext'
  · show ψStr pl hW hW' hne hne' mv mv' ψ (ov x.1) = ov' y.1
    rw [eov, eov', ψStr_strandMv]
  · exact (key (ov x.1) (hov x.1) (ov' y.1) (hov' y.1) eov eov').symm

/-- The under occurrence of an outer crossing corresponds. -/
theorem MatchData.ψPt_under (x : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L)) :
    ψPt pl hW hW' hne hne' mv mv' ψ
        ((U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).visitPt
          ((U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).underVisit x.1)) =
      (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').visitPt
        ((U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').underVisit
          (M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x).1) := by
  obtain ⟨k, m, hk, hℓ, -, hx, -, houtB, k', m', hk', hℓ', -, hA, hB, hx'⟩ :=
    M.outer_spec pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x
  set y := M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x
  have eov : ov x.1 = strandMv pl hW hne mv (σSlotA hW hk hℓ) := data.overStrand x.1 k m hk hℓ hx
  have eov' : ov' y.1 = strandMv pl hW' hne' mv' (σSlotA hW' hk' hℓ') := data'.overStrand y.1 k' m' hk' hℓ' hx'
  have eun : (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).underStrand x.1 = strandMv pl hW hne mv (σSlotB hW hk hℓ) := by
    symm
    refine Diagram.eq_under_of_mem_of_ne (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov) x.1 ?_ ?_
    · show _ ∈ x.1.val
      rw [hx]; exact U2.mem_σpair_B pl hW hne _ hk hℓ
    · show _ ≠ ov x.1
      rw [eov]
      intro h
      exact σSlotA_ne_σSlotB hW hk hℓ (U2.stStrand_injective pl hW hne _ h).symm
  have eun' : (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').underStrand y.1 = strandMv pl hW' hne' mv' (ψ (σSlotB hW hk hℓ)) := by
    symm
    refine Diagram.eq_under_of_mem_of_ne (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov') y.1 ?_ ?_
    · show _ ∈ y.1.val
      rw [hx', hB]; exact U2.mem_σpair_B pl hW' hne' _ hk' hℓ'
    · show _ ≠ ov' y.1
      rw [eov', hB]
      intro h
      exact σSlotA_ne_σSlotB hW' hk' hℓ' (U2.stStrand_injective pl hW' hne' _ h).symm
  have hsB : strandMv pl hW hne mv (σSlotB hW hk hℓ) ∈ x.1.val := by rw [hx]; exact U2.mem_σpair_B pl hW hne _ hk hℓ
  have hsB' : strandMv pl hW' hne' mv' (ψ (σSlotB hW hk hℓ)) ∈ y.1.val := by
    rw [hx', hB]; exact U2.mem_σpair_B pl hW' hne' _ hk' hℓ'
  have hcp := M.crossingParam_crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x houtB hsB hsB'
  have key : ∀ (s : (shadowMv pl hW hne mv).Strand) (hs : s ∈ x.1.val) (s' : (shadowMv pl hW' hne' mv').Strand)
      (hs' : s' ∈ y.1.val), s = strandMv pl hW hne mv (σSlotB hW hk hℓ) →
      s' = strandMv pl hW' hne' mv' (ψ (σSlotB hW hk hℓ)) →
      (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').crossingParam y.1 hs' = (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).crossingParam x.1 hs := by
    intro s hs s' hs' e e'
    subst e; subst e'
    exact hcp
  unfold Diagram.visitPt Diagram.underVisit ψPt
  apply pt_ext'
  · show ψStr pl hW hW' hne hne' mv mv' ψ ((U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).underStrand x.1) = (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').underStrand y.1
    rw [eun, eun', ψStr_strandMv]
  · exact (key _ ((U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).under_mem x.1) _ ((U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').under_mem y.1) eun eun').symm

variable (hσ' : SigmaCorr L hW' hW mv' ψ.symm K' K)
include hσ'

/-- **The outer-crossing correspondence.** -/
def MatchData.crossEquiv :
    (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov).OuterCrossing (polygon L) ≃
      (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov').OuterCrossing (polygon L) where
  toFun := M.crossMap pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ
  invFun := M.symm.crossMap pl hne' hne hgen' ov' hov' K' data' hgen ov hov K data hσ'
  left_inv x := by
    apply Subtype.ext; apply Subtype.ext
    rw [MatchData.crossMap_val, MatchData.crossMap_val]
    exact ψFin_symm_ψFin pl hW hW' hne hne' mv mv' ψ x.1.val
  right_inv y := by
    apply Subtype.ext; apply Subtype.ext
    rw [MatchData.crossMap_val, MatchData.crossMap_val]
    have := ψFin_symm_ψFin pl hW' hW hne' hne mv' mv ψ.symm y.1.val
    rwa [Equiv.symm_symm] at this

variable (e : Fin (numComp hW) ≃ Fin (numComp hW'))
  (he : ∀ u : Slot W, mv u ∉ interior (polygon L) → U2.slotComp hW' (ψ u) = e (U2.slotComp hW u))
include e he

/-- **The move match** of two slot diagrams from a slot bijection matching them outside the polygon
(`MatchData`), the two crossing sets (`SlotDiagramData`), the correspondence of the outer `σ` columns in both
directions (`SigmaCorr`), and a component bijection respected on the vertices outside the open polygon. -/
def MatchData.moveMatch :
    MoveMatch (polygon L) (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov)
      (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov') where
  φ := M.outEquiv pl hne hne'
  eval_eq p := M.eval_ψPt_of_outside pl hne hne' p.1 p.2
  dir_pos p hp := ⟨1, one_pos, by rw [one_smul]; exact M.dir_ψPt pl hne hne' p.1 hp⟩
  dir_pos_before p hp := ⟨1, one_pos, by rw [one_smul]; exact M.dir_before_ψPt pl hne hne' p.1 hp⟩
  ψ := M.crossEquiv pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ hσ'
  over_eq x := Subtype.ext (M.ψPt_over pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x)
  under_eq x := Subtype.ext (M.ψPt_under pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ x)
  e := e
  comp_eq p := by
    rw [MatchData.outEquiv_apply]
    obtain ⟨⟨i, j, t⟩, hp⟩ := p
    set u := slotMv pl hW hne mv ⟨i, j⟩ with hu
    have hmv : mv u ∉ interior (polygon L) := by
      rw [eval_mv] at hp
      have ht := t.2
      rcases ht.1.lt_or_eq with h0 | h0
      · by_cases hout : PieceOut L hW mv u
        · exact hout.left_notMem_interior
        · exact absurd ((M.pieceIn_of_not_out hout).mem_interior h0 ht.2) hp
      · have ht0 : t.val = 0 := h0.symm
        rw [ht0, segPt_zero] at hp
        exact hp
    have h1 : (ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩).1 = U2.slotComp hW' (ψ u) := by
      have := U2.slotComp_idxEquiv hW' (ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩)
      rw [← this]
      exact congrArg (U2.slotComp hW') (slotMv_ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩)
    have h2 : i = U2.slotComp hW u := (U2.slotComp_idxEquiv hW ⟨i, j⟩).symm
    show (ψStr pl hW hW' hne hne' mv mv' ψ ⟨i, j⟩).1 = e i
    rw [h1, he u hmv]
    exact congrArg e h2.symm

end Match

/-! #### G. The arcs of a polygon as slot chains: `IsArc`, `ArcCover`, `Before` -/

section Arcs

/-- `A < B + t ↔ A < B ∨ (A = B ∧ 0 < t)` for naturals and `t ∈ [0, 1)`. -/
theorem nat_lt_add_iff (A B : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ((A : ℝ) < B + t) ↔ (A < B ∨ (A = B ∧ 0 < t)) := by
  constructor
  · intro h
    rcases lt_trichotomy A B with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', by subst h'; linarith⟩
    · exfalso
      have : (B : ℝ) + 1 ≤ A := by exact_mod_cast h'
      linarith
  · rintro (h | ⟨h, ht⟩)
    · have : (A : ℝ) + 1 ≤ B := by exact_mod_cast h
      linarith
    · subst h; linarith

/-- `B + t < C ↔ B < C` for naturals and `t ∈ [0, 1)`. -/
theorem nat_add_lt_iff (B C : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) : ((B : ℝ) + t < C) ↔ B < C := by
  constructor
  · intro h
    by_contra h'
    have : (C : ℝ) ≤ B := by exact_mod_cast not_lt.1 h'
    linarith
  · intro h
    have : (B : ℝ) + 1 ≤ C := by exact_mod_cast h
    linarith

/-- `B + t < B' + t' ↔ B < B' ∨ (B = B' ∧ t < t')` for naturals and `t, t' ∈ [0, 1)`. -/
theorem nat_add_lt_add_iff (B B' : ℕ) (t t' : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) (ht0' : 0 ≤ t') (ht1' : t' < 1) :
    ((B : ℝ) + t < B' + t') ↔ (B < B' ∨ (B = B' ∧ t < t')) := by
  constructor
  · intro h
    rcases lt_trichotomy B B' with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨h', by subst h'; linarith⟩
    · exfalso
      have : (B' : ℝ) + 1 ≤ B := by exact_mod_cast h'
      linarith
  · rintro (h | ⟨h, htt⟩)
    · have : (B : ℝ) + 1 ≤ B' := by exact_mod_cast h
      linarith
    · subst h; linarith

/-- The cyclic betweenness of the keys `A`, `B + t`, `C` where `B`, `C` are `A + j`, `A + n` reduced mod `k`
(`0 < n < k`, `j < k`, `t ∈ [0,1)`): the point `j` steps after the start, at parameter `t`, lies strictly between the
start and the stop iff `j < n` and it is not the start itself. -/
theorem cycBetween_key' (k A B C n j : ℕ) (hA : A < k) (hn0 : 0 < n) (hnk : n < k) (hj : j < k) (hBk : B < k) (hCk : C < k)
    (hB : B = A + j ∨ B + k = A + j) (hC : C = A + n ∨ C + k = A + n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    cycBetween (A : ℝ) ((B : ℝ) + t) (C : ℝ) ↔ (j < n ∧ (0 < j ∨ 0 < t)) := by
  unfold cycBetween
  rw [nat_lt_add_iff A B t ht0 ht1, nat_add_lt_iff B C t ht0 ht1, Nat.cast_lt]
  by_cases ht : 0 < t
  · simp only [ht, and_true, or_true]
    omega
  · simp only [ht, and_false, or_false]
    omega

theorem cycBetween_key (k A n j : ℕ) (hA : A < k) (hn0 : 0 < n) (hnk : n < k) (hj : j < k) (t : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) :
    cycBetween (A : ℝ) ((((A + j) % k : ℕ) : ℝ) + t) (((A + n) % k : ℕ) : ℝ) ↔ (j < n ∧ (0 < j ∨ 0 < t)) :=
  cycBetween_key' k A _ _ n j hA hn0 hnk hj (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (add_mod_cases k A j hA hj) (add_mod_cases k A n hA hnk) t ht0 ht1

/-- The cyclic betweenness of the keys of the start, a point `j` steps after it and a point `j'` steps after
it (both strictly after the start, both less than `k` steps). -/
theorem cycBetween_key2' (k A B B' j j' : ℕ) (hA : A < k) (hj : j < k) (hj' : j' < k) (hBk : B < k) (hBk' : B' < k)
    (hB : B = A + j ∨ B + k = A + j) (hB' : B' = A + j' ∨ B' + k = A + j') (t t' : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (ht0' : 0 ≤ t') (ht1' : t' < 1) (hp : 0 < j ∨ 0 < t) (hq : 0 < j' ∨ 0 < t') :
    cycBetween (A : ℝ) ((B : ℝ) + t) ((B' : ℝ) + t') ↔ (j < j' ∨ (j = j' ∧ t < t')) := by
  unfold cycBetween
  rw [nat_lt_add_iff A B t ht0 ht1, nat_add_lt_add_iff B B' t t' ht0 ht1 ht0' ht1', nat_add_lt_iff B' A t' ht0' ht1']
  by_cases ht : 0 < t <;> by_cases htt : t < t' <;> by_cases ht' : 0 < t'
  all_goals
    first
    | (exfalso; linarith)
    | (simp only [ht, htt, ht', and_true, and_false, or_true, or_false] at hp hq ⊢; omega)

theorem cycBetween_key2 (k A j j' : ℕ) (hA : A < k) (hj : j < k) (hj' : j' < k) (t t' : ℝ) (ht0 : 0 ≤ t)
    (ht1 : t < 1) (ht0' : 0 ≤ t') (ht1' : t' < 1) (hp : 0 < j ∨ 0 < t) (hq : 0 < j' ∨ 0 < t') :
    cycBetween (A : ℝ) ((((A + j) % k : ℕ) : ℝ) + t) ((((A + j') % k : ℕ) : ℝ) + t') ↔
      (j < j' ∨ (j = j' ∧ t < t')) :=
  cycBetween_key2' k A _ _ j j' hA hj hj' (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
    (add_mod_cases k A j hA hj) (add_mod_cases k A j' hA hj') t t' ht0 ht1 ht0' ht1' hp hq

variable (L : List HalfPlane) (pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane)

/-- A *chain*: `n ≥ 1` consecutive pieces `u₀, next u₀, …, next^[n-1] u₀` (the pieces of one arc of the disc). -/
structure Chain (W : Word) where
  u₀ : Slot W
  n : ℕ
  hn : 0 < n

namespace Chain

variable (c : Chain W)

/-- the `j`-th slot of the chain -/
def slot (j : ℕ) : Slot W := (next hW)^[j] c.u₀

@[simp] theorem slot_zero : c.slot hW 0 = c.u₀ := rfl

theorem slot_succ (j : ℕ) : c.slot hW (j + 1) = next hW (c.slot hW j) := Function.iterate_succ_apply' _ _ _

/-- the strand of the chain's `j`-th slot is `j` steps along the component of the entry strand -/
theorem strandMv_slot (j : ℕ) :
    strandMv pl hW hne mv (c.slot hW j) =
      ⟨(strandMv pl hW hne mv c.u₀).1, (strandMv pl hW hne mv c.u₀).2 + (j : ZMod _)⟩ := by
  have e := U2.idxEquiv_add hW (strandMv pl hW hne mv c.u₀).1 (strandMv pl hW hne mv c.u₀).2 j
  have e2 : idxEquiv hW ⟨(strandMv pl hW hne mv c.u₀).1, (strandMv pl hW hne mv c.u₀).2⟩ = c.u₀ :=
    U2.idxEquiv_stStrand pl hW hne (vertsOf pl hW hne mv) c.u₀
  rw [e2] at e
  apply (idxEquiv hW).injective
  rw [U2.idxEquiv_stStrand pl hW hne (vertsOf pl hW hne mv)]
  exact e.symm

/-- The arc of the chain: on the component of the entry slot, from the tail of its strand to the tail of the
strand `n` steps later. -/
def toArc : (shadowMv pl hW hne mv).Arc :=
  ⟨(strandMv pl hW hne mv c.u₀).1, ((strandMv pl hW hne mv c.u₀).2, ⟨0, le_rfl, zero_lt_one⟩),
    ((strandMv pl hW hne mv c.u₀).2 + (c.n : ZMod _), ⟨0, le_rfl, zero_lt_one⟩)⟩

theorem toArc_i : (c.toArc pl hW hne mv).i = (strandMv pl hW hne mv c.u₀).1 := rfl

theorem startPt_eq : (c.toArc pl hW hne mv).startPt = vertexPt pl hW hne mv c.u₀ := rfl

theorem stopPt_eq : (c.toArc pl hW hne mv).stopPt = vertexPt pl hW hne mv (c.slot hW c.n) := by
  unfold Shadow.Arc.stopPt toArc vertexPt travMv
  rw [strandMv_slot]

theorem eval_startPt : (shadowMv pl hW hne mv).eval (c.toArc pl hW hne mv).startPt = mv c.u₀ := by
  rw [startPt_eq, eval_vertexPt]

theorem eval_stopPt : (shadowMv pl hW hne mv).eval (c.toArc pl hW hne mv).stopPt = mv (c.slot hW c.n) := by
  rw [stopPt_eq, eval_vertexPt]

/-- Two chains with different entry slots give different arcs. -/
theorem toArc_ne {c c' : Chain W} (h : c.u₀ ≠ c'.u₀) : c.toArc pl hW hne mv ≠ c'.toArc pl hW hne mv := by
  intro he
  apply h
  have := congrArg (fun a : (shadowMv pl hW hne mv).Arc => (⟨a.i, a.start.1⟩ : (shadowMv pl hW hne mv).Strand)) he
  exact U2.stStrand_injective pl hW hne _ this

/-- The defining properties of a chain of inside pieces: the pieces are inside, the intermediate vertices are
in the open polygon, the piece before the entry and the piece at the stop are outside. -/
structure IsChain : Prop where
  pieceIn : ∀ j, j < c.n → PieceIn L hW mv (c.slot hW j)
  vertex_interior : ∀ j, 0 < j → j < c.n → mv (c.slot hW j) ∈ interior (polygon L)
  out_prev : PieceOut L hW mv (prev hW c.u₀)
  out_stop : PieceOut L hW mv (c.slot hW c.n)

/-- The period of the component of the chain (as the modulus of the strand labels). -/
theorem period_eq (c : Chain W) : ((shadowMv pl hW hne mv).comp (strandMv pl hW hne mv c.u₀).1).k = period hW c.u₀ := by
  show period hW (rep hW (strandMv pl hW hne mv c.u₀).1) = period hW c.u₀
  have e : c.u₀ = (next hW)^[(strandMv pl hW hne mv c.u₀).2.val] (rep hW (strandMv pl hW hne mv c.u₀).1) :=
    (U2.idxEquiv_stStrand pl hW hne (vertsOf pl hW hne mv) c.u₀).symm
  conv_rhs => rw [e]
  rw [period_iterate]

/-- the modulus of the arc's component -/
theorem k_eq (c : Chain W) : ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k = period hW c.u₀ :=
  period_eq pl hW hne mv c

theorem key_start (c : Chain W) :
    traversalKey (c.toArc pl hW hne mv).start = (((c.toArc pl hW hne mv).start.1.val : ℕ) : ℝ) := by
  show (((c.toArc pl hW hne mv).start.1.val : ℕ) : ℝ) + (0 : ℝ) = _
  ring

theorem key_stop (c : Chain W) :
    traversalKey (c.toArc pl hW hne mv).stop =
      ((((c.toArc pl hW hne mv).start.1.val + c.n) % ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k : ℕ) : ℝ) := by
  show ((((c.toArc pl hW hne mv).start.1 + (c.n : ZMod _)).val : ℕ) : ℝ) + (0 : ℝ) = _
  rw [ZMod.val_add, ZMod.val_natCast, Nat.add_mod_mod, add_zero]

theorem key_pt (c : Chain W) (b : ZMod ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k) (t : Set.Ico (0 : ℝ) 1) :
    traversalKey ((b, t) : TraversalPoint ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k) =
      ((((c.toArc pl hW hne mv).start.1.val + (b - (c.toArc pl hW hne mv).start.1).val) %
        ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k : ℕ) : ℝ) + t.val := by
  show ((b.val : ℕ) : ℝ) + t.val = _
  congr 1
  have e : b = (c.toArc pl hW hne mv).start.1 + (b - (c.toArc pl hW hne mv).start.1) := by ring
  conv_lhs => rw [e]
  rw [ZMod.val_add]

/-- The point `j` steps after the start, as a traversal point of the arc's component. -/
theorem travMv_slot_eq (c : Chain W) (j : ℕ) (t : Set.Ico (0 : ℝ) 1) :
    travMv pl hW hne mv (c.slot hW j) t =
      ⟨(c.toArc pl hW hne mv).i, ((c.toArc pl hW hne mv).start.1 + (j : ZMod _), t)⟩ := by
  unfold travMv
  rw [strandMv_slot]
  rfl

variable {c} {L hW mv}

theorem IsChain.entry_notMem_interior (h : c.IsChain L hW mv) : mv c.u₀ ∉ interior (polygon L) := by
  have := h.out_prev.right_notMem_interior
  rwa [next_prev] at this

theorem IsChain.stop_notMem_interior (h : c.IsChain L hW mv) : mv (c.slot hW c.n) ∉ interior (polygon L) :=
  h.out_stop.left_notMem_interior

theorem IsChain.entry_mem (h : c.IsChain L hW mv) : mv c.u₀ ∈ polygon L := (h.pieceIn 0 c.hn).left_mem

theorem IsChain.stop_mem (h : c.IsChain L hW mv) : mv (c.slot hW c.n) ∈ polygon L := by
  have hn := c.hn
  have := (h.pieceIn (c.n - 1) (by omega)).right_mem
  rwa [← slot_succ, Nat.sub_add_cancel hn] at this

theorem IsChain.entry_frontier (h : c.IsChain L hW mv) : mv c.u₀ ∈ frontier (polygon L) :=
  mem_frontier_polygon_of L h.entry_mem h.entry_notMem_interior

theorem IsChain.stop_frontier (h : c.IsChain L hW mv) : mv (c.slot hW c.n) ∈ frontier (polygon L) :=
  mem_frontier_polygon_of L h.stop_mem h.stop_notMem_interior

/-- The chain is shorter than the cycle of its entry slot. -/
theorem IsChain.n_lt_period (h : c.IsChain L hW mv) : c.n < period hW c.u₀ := by
  by_contra hle
  rw [not_lt] at hle
  have hper : c.slot hW (period hW c.u₀) = c.u₀ := iterate_period hW c.u₀
  rcases hle.lt_or_eq with hlt | heq
  · have := h.vertex_interior (period hW c.u₀) (period_pos hW _) hlt
    rw [hper] at this
    exact h.entry_notMem_interior this
  · have h1 := h.out_stop
    rw [← heq, hper] at h1
    exact not_segIn_of_segOut h1 (h.pieceIn 0 c.hn)

/-- A vertex of the chain's slot `j ≤ n` lies in the closed polygon. -/
theorem IsChain.slot_mem (h : c.IsChain L hW mv) {j : ℕ} (hj : j ≤ c.n) : mv (c.slot hW j) ∈ polygon L := by
  rcases hj.lt_or_eq with hj | hj
  · exact (h.pieceIn j hj).left_mem
  · subst hj; exact h.stop_mem

/-- **The inner points of the chain's arc**: the points of its pieces other than the start. -/
theorem IsChain.inner_iff (h : c.IsChain L hW mv) (p : (shadowMv pl hW hne mv).Pt) :
    (c.toArc pl hW hne mv).Inner p ↔
      ∃ j, j < c.n ∧ ∃ t : Set.Ico (0 : ℝ) 1, p = travMv pl hW hne mv (c.slot hW j) t ∧ (0 < j ∨ 0 < t.val) := by
  have hnk : c.n < ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k := by
    rw [k_eq]; exact h.n_lt_period
  have hkey : ∀ (b : ZMod ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k) (t : Set.Ico (0 : ℝ) 1),
      traversalBetween (c.toArc pl hW hne mv).start (b, t) (c.toArc pl hW hne mv).stop ↔
        ((b - (c.toArc pl hW hne mv).start.1).val < c.n ∧
          (0 < (b - (c.toArc pl hW hne mv).start.1).val ∨ 0 < t.val)) := by
    intro b t
    rw [traversalBetween_iff_cycBetween, key_start, key_stop, key_pt]
    exact cycBetween_key _ _ _ _ (ZMod.val_lt _) c.hn hnk (ZMod.val_lt _) t.val t.2.1 t.2.2
  constructor
  · rintro ⟨⟨b, t⟩, hbt, rfl⟩
    rw [hkey] at hbt
    refine ⟨(b - (c.toArc pl hW hne mv).start.1).val, hbt.1, t, ?_, hbt.2⟩
    rw [travMv_slot_eq, ZMod.natCast_zmod_val, add_sub_cancel]
  · rintro ⟨j, hj, t, rfl, hpos⟩
    refine ⟨((c.toArc pl hW hne mv).start.1 + (j : ZMod _), t), ?_, ?_⟩
    · have hjk : j < ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k := by omega
      rw [hkey, add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hjk]
      exact ⟨hj, hpos⟩
    · rw [travMv_slot_eq]

/-- **The points of the chain's arc**: the points of its pieces, and the stop vertex. -/
theorem IsChain.mem_iff (h : c.IsChain L hW mv) (p : (shadowMv pl hW hne mv).Pt) :
    (c.toArc pl hW hne mv).Mem p ↔
      (∃ j, j < c.n ∧ ∃ t : Set.Ico (0 : ℝ) 1, p = travMv pl hW hne mv (c.slot hW j) t) ∨
        p = vertexPt pl hW hne mv (c.slot hW c.n) := by
  unfold Shadow.Arc.Mem
  rw [startPt_eq, stopPt_eq, h.inner_iff pl hne]
  constructor
  · rintro (rfl | rfl | ⟨j, hj, t, rfl, -⟩)
    · exact Or.inl ⟨0, c.hn, _, rfl⟩
    · exact Or.inr rfl
    · exact Or.inl ⟨j, hj, t, rfl⟩
  · rintro (⟨j, hj, t, rfl⟩ | rfl)
    · rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rcases t.2.1.lt_or_eq with ht | ht
        · exact Or.inr (Or.inr ⟨0, c.hn, t, rfl, Or.inr ht⟩)
        · left
          unfold vertexPt
          congr 2
          exact Subtype.ext ht.symm
      · exact Or.inr (Or.inr ⟨j, hj, t, rfl, Or.inl hj0⟩)
    · exact Or.inr (Or.inl rfl)

/-- A point of a piece of the chain is on the arc. -/
theorem IsChain.mem_of_slot (h : c.IsChain L hW mv) {j : ℕ} (hj : j < c.n) (t : Set.Ico (0 : ℝ) 1) :
    (c.toArc pl hW hne mv).Mem (travMv pl hW hne mv (c.slot hW j) t) :=
  (h.mem_iff pl hne _).2 (Or.inl ⟨j, hj, t, rfl⟩)

/-- An interior point of a piece of the chain is an inner point of the arc. -/
theorem IsChain.inner_of_slot (h : c.IsChain L hW mv) {j : ℕ} (hj : j < c.n) (t : Set.Ico (0 : ℝ) 1)
    (ht : 0 < t.val) : (c.toArc pl hW hne mv).Inner (travMv pl hW hne mv (c.slot hW j) t) :=
  (h.inner_iff pl hne _).2 ⟨j, hj, t, rfl, Or.inr ht⟩

/-- **The traversal order along the chain's arc**: earlier piece, or the same piece and smaller parameter. -/
theorem IsChain.before_iff (h : c.IsChain L hW mv) {j j' : ℕ} (hj : j < c.n) (hj' : j' < c.n)
    (t t' : Set.Ico (0 : ℝ) 1) (hp : 0 < j ∨ 0 < t.val) (hq : 0 < j' ∨ 0 < t'.val) :
    (c.toArc pl hW hne mv).Before (travMv pl hW hne mv (c.slot hW j) t) (travMv pl hW hne mv (c.slot hW j') t') ↔
      (j < j' ∨ (j = j' ∧ t.val < t'.val)) := by
  have hnk : c.n < ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k := by
    rw [k_eq]; exact h.n_lt_period
  have hin1 : (c.toArc pl hW hne mv).Inner (travMv pl hW hne mv (c.slot hW j) t) :=
    (h.inner_iff pl hne _).2 ⟨j, hj, t, rfl, hp⟩
  have hin2 : (c.toArc pl hW hne mv).Inner (travMv pl hW hne mv (c.slot hW j') t') :=
    (h.inner_iff pl hne _).2 ⟨j', hj', t', rfl, hq⟩
  have hkey : ∀ (i i' : ℕ), i < c.n → i' < c.n → (0 < i ∨ 0 < t.val) → (0 < i' ∨ 0 < t'.val) →
      (traversalBetween (c.toArc pl hW hne mv).start ((c.toArc pl hW hne mv).start.1 + (i : ZMod _), t)
        ((c.toArc pl hW hne mv).start.1 + (i' : ZMod _), t') ↔ (i < i' ∨ (i = i' ∧ t.val < t'.val))) := by
    intro i i' hi hi' hp' hq'
    have hik : i < ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k := by omega
    have hik' : i' < ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k := by omega
    rw [traversalBetween_iff_cycBetween, key_start, key_pt, key_pt, add_sub_cancel_left, add_sub_cancel_left,
      ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hik, Nat.mod_eq_of_lt hik']
    exact cycBetween_key2 _ _ _ _ (ZMod.val_lt _) (by omega) (by omega) t.val t'.val t.2.1 t.2.2 t'.2.1 t'.2.2 hp' hq'
  unfold Shadow.Arc.Before
  constructor
  · rintro ⟨-, -, r, r', hr, hr', hb⟩
    rw [travMv_slot_eq] at hr hr'
    have er : r = ((c.toArc pl hW hne mv).start.1 + (j : ZMod _), t) := ((Sigma.mk.inj_iff.1 hr).2).symm.eq
    have er' : r' = ((c.toArc pl hW hne mv).start.1 + (j' : ZMod _), t') := ((Sigma.mk.inj_iff.1 hr').2).symm.eq
    rw [er, er'] at hb
    exact (hkey j j' hj hj' hp hq).1 hb
  · intro hlt
    refine ⟨hin1, hin2, ?_⟩
    have e1 := travMv_slot_eq pl hW hne mv c j t
    have e2 := travMv_slot_eq pl hW hne mv c j' t'
    have e3 := (hkey j j' hj hj' hp hq).2 hlt
    exact ⟨_, _, e1, e2, e3⟩

/-- **The chain's arc is an arc of the polygon.** -/
theorem IsChain.isArc (h : c.IsChain L hW mv) : (shadowMv pl hW hne mv).IsArc (polygon L) (c.toArc pl hW hne mv) where
  start_ne_stop := by
    intro he
    have hnk : c.n < ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k := by
      rw [k_eq]; exact h.n_lt_period
    have h1 := congrArg Prod.fst he
    have h2 : (c.n : ZMod ((shadowMv pl hW hne mv).comp (c.toArc pl hW hne mv).i).k) = 0 := by
      have e : (c.toArc pl hW hne mv).stop.1 = (c.toArc pl hW hne mv).start.1 + (c.n : ZMod _) := rfl
      rw [e] at h1
      exact (add_eq_left.1 h1.symm)
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd c.hn h2
    omega
  start_frontier := by rw [eval_startPt]; exact h.entry_frontier
  stop_frontier := by rw [eval_stopPt]; exact h.stop_frontier
  inner_interior p hp := by
    rw [h.inner_iff pl hne] at hp
    obtain ⟨j, hj, t, rfl, hpos⟩ := hp
    rw [eval_travMv]
    rcases t.2.1.lt_or_eq with ht | ht
    · exact (h.pieceIn j hj).mem_interior ht t.2.2
    · rw [← ht, segPt_zero]
      rcases hpos with hj0 | ht'
      · exact h.vertex_interior j hj0 hj
      · rw [← ht] at ht'; exact absurd ht' (lt_irrefl _)

end Chain

/-- The arcs of a finite list of chains. -/
def arcsOf (cs : List (Chain W)) : Set (shadowMv pl hW hne mv).Arc :=
  {a | ∃ c ∈ cs, a = c.toArc pl hW hne mv}

theorem mem_arcsOf (cs : List (Chain W)) (c : Chain W) (hc : c ∈ cs) : c.toArc pl hW hne mv ∈ arcsOf pl hW hne mv cs :=
  ⟨c, hc, rfl⟩

/-- **The arc cover of a polygon by chains**: every inside piece is on a listed chain, distinct chains share no
piece, and a piece leaving the polygon at a vertex of the polygon is preceded by an inside piece (no touching
from outside). -/
theorem arcCover_of (cs : List (Chain W)) (hall : ∀ c ∈ cs, c.IsChain L hW mv)
    (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u)
    (hcover : ∀ u, PieceIn L hW mv u → ∃ c ∈ cs, ∃ j, j < c.n ∧ c.slot hW j = u)
    (hdisj : ∀ c ∈ cs, ∀ c' ∈ cs, c ≠ c' → ∀ j, j < c.n → ∀ j', j' < c'.n → c.slot hW j ≠ c'.slot hW j')
    (htouch : ∀ u, PieceOut L hW mv u → mv u ∈ polygon L → PieceIn L hW mv (prev hW u)) :
    (shadowMv pl hW hne mv).ArcCover (polygon L) (arcsOf pl hW hne mv cs) where
  isArc a ha := by
    obtain ⟨c, hc, rfl⟩ := ha
    exact (hall c hc).isArc pl hne
  mem_iff p := by
    constructor
    · intro hp
      set u := slotPtMv pl hW hne mv p with hu
      have hpt : p = travMv pl hW hne mv u p.2.2 := (travMv_slotPtMv pl hW hne mv p).symm
      rw [eval_mv] at hp
      rcases hcl u with hin | hout
      · obtain ⟨c, hc, j, hj, hju⟩ := hcover u hin
        refine ⟨c.toArc pl hW hne mv, mem_arcsOf pl hW hne mv cs c hc, ?_⟩
        rw [(hall c hc).mem_iff pl hne]
        exact Or.inl ⟨j, hj, p.2.2, by rw [hpt, hju]⟩
      · have ht0 : p.2.2.val = 0 := by
          rcases hout.eq_end_of_mem p.2.2.2.1 p.2.2.2.2.le hp with h | h
          · exact h
          · exact absurd h (ne_of_lt p.2.2.2.2)
        rw [ht0, segPt_zero] at hp
        have hprev := htouch u hout hp
        obtain ⟨c, hc, j, hj, hju⟩ := hcover _ hprev
        have hIs := hall c hc
        have hu' : u = c.slot hW (j + 1) := by rw [Chain.slot_succ, hju, next_prev]
        have hjn : j + 1 = c.n := by
          by_contra hne'
          have hlt : j + 1 < c.n := lt_of_le_of_ne hj hne'
          exact hout.left_notMem_interior (hu' ▸ hIs.vertex_interior (j + 1) (Nat.succ_pos j) hlt)
        refine ⟨c.toArc pl hW hne mv, mem_arcsOf pl hW hne mv cs c hc, ?_⟩
        rw [hIs.mem_iff pl hne]
        right
        rw [hpt, ← hjn, ← hu']
        unfold vertexPt
        congr 2
        exact Subtype.ext ht0
    · rintro ⟨a, ⟨c, hc, rfl⟩, hmem⟩
      have hIs := hall c hc
      rw [hIs.mem_iff pl hne] at hmem
      rcases hmem with ⟨j, hj, t, rfl⟩ | rfl
      · rw [eval_travMv]
        exact (hIs.pieceIn j hj).mem t.2.1 t.2.2.le
      · rw [eval_vertexPt]
        exact hIs.stop_mem
  disjoint a ha b hb hab p hpa hpb := by
    obtain ⟨c, hc, rfl⟩ := ha
    obtain ⟨c', hc', rfl⟩ := hb
    have hcc : c ≠ c' := fun h => hab (by rw [h])
    have hIs := hall c hc
    have hIs' := hall c' hc'
    rw [hIs.mem_iff pl hne] at hpa
    rw [hIs'.mem_iff pl hne] at hpb
    -- the slot of `p` is determined
    have hslot : ∀ (v v' : Slot W) (t t' : Set.Ico (0 : ℝ) 1),
        travMv pl hW hne mv v t = travMv pl hW hne mv v' t' → v = v' := by
      intro v v' t t' h
      have := congrArg (slotPtMv pl hW hne mv) h
      rwa [slotPtMv_travMv, slotPtMv_travMv] at this
    rcases hpa with ⟨j, hj, t, rfl⟩ | hpa <;> rcases hpb with ⟨j', hj', t', hpb⟩ | hpb
    · exact hdisj c hc c' hc' hcc j hj j' hj' (hslot _ _ _ _ hpb)
    · have e := hslot _ _ _ _ hpb
      exact not_segIn_of_segOut hIs'.out_stop (e ▸ hIs.pieceIn j hj)
    · have e := hslot _ _ _ _ (hpa.symm.trans hpb)
      exact not_segIn_of_segOut hIs.out_stop (e ▸ hIs'.pieceIn j' hj')
    · have e := hslot _ _ _ _ (hpa.symm.trans hpb)
      have hn := c.hn
      have hn' := c'.hn
      have e' : c.slot hW (c.n - 1) = c'.slot hW (c'.n - 1) := by
        have h1 : c.slot hW c.n = next hW (c.slot hW (c.n - 1)) := by rw [← Chain.slot_succ, Nat.sub_add_cancel hn]
        have h2 : c'.slot hW c'.n = next hW (c'.slot hW (c'.n - 1)) := by rw [← Chain.slot_succ, Nat.sub_add_cancel hn']
        rw [h1, h2] at e
        exact next_injective hW e
      exact hdisj c hc c' hc' hcc _ (by omega) _ (by omega) e'

end Arcs

/-! #### H. Every component leaves a block without cusps of one kind: the extremal-vertex argument -/

section Exits

variable {W : Word} (hW : W.Closed)

/-- The column of a cusp slot is its cut index. -/
theorem colOf_of_cusp {v : Slot W} (hv : v.1.2 = 0) : colOf v = v.1.1 := by
  simp [colOf, hv]

open Classical in
/-- In a cycle of `next` all of whose pieces lie in the columns `[a, b)`, there is a right-cusp slot and a
left-cusp slot, both in columns of `[a, b)` (the rightmost and the leftmost vertices of the closed polygon). -/
theorem exists_cusps_of_no_ext (a b : ℕ) (u : Slot W)
    (h : ∀ v, (nextPerm hW).SameCycle u v → a ≤ colOf v ∧ colOf v < b) :
    (∃ v, (nextPerm hW).SameCycle u v ∧ v.1.2 = 0 ∧ (∃ m, letterAt W v.1.1 = .r m) ∧ a ≤ v.1.1 ∧ v.1.1 < b) ∧
    (∃ v, (nextPerm hW).SameCycle u v ∧ v.1.2 = 0 ∧ (∃ m d, letterAt W v.1.1 = .l m d) ∧ a ≤ v.1.1 ∧ v.1.1 < b) := by
  set S : Finset (Slot W) := Finset.univ.filter (fun v => (nextPerm hW).SameCycle u v) with hS
  have hmem : ∀ v, v ∈ S ↔ (nextPerm hW).SameCycle u v := by
    intro v; simp [hS]
  have hne : S.Nonempty := ⟨u, (hmem u).2 (Equiv.Perm.SameCycle.refl _ _)⟩
  have hnext : ∀ v, (nextPerm hW).SameCycle u v → (nextPerm hW).SameCycle u (next hW v) := fun v hv =>
    hv.trans ⟨1, by simp⟩
  have hprev : ∀ v, (nextPerm hW).SameCycle u v → (nextPerm hW).SameCycle u (prev hW v) := fun v hv =>
    hv.trans ⟨-1, by simp⟩
  -- a cusp at an extremal vertex
  have cusp : ∀ v, (nextPerm hW).SameCycle u v → xsign (prev hW v) ≠ xsign v → v.1.2 = 0 := by
    intro v hv hx
    by_contra h0
    apply hx
    have := (xsign_next_iff hW (prev hW v)).2 (by rw [next_prev]; exact h0)
    rw [next_prev] at this
    exact this.symm
  constructor
  · obtain ⟨v, hvS, hmax⟩ := S.exists_max_image xcoord2 hne
    have hv := (hmem v).1 hvS
    have hxv : xsign v = false := by
      by_contra hc
      have hc' : xsign v = true := by cases hx : xsign v; exact absurd hx hc; rfl
      have := (xcoord2_next hW v).1 hc'
      have := hmax _ ((hmem _).2 (hnext v hv))
      omega
    have hxp : xsign (prev hW v) = true := by
      by_contra hc
      have hc' : xsign (prev hW v) = false := by cases hx : xsign (prev hW v); rfl; exact absurd hx hc
      have := (xcoord2_next hW (prev hW v)).2 hc'
      rw [next_prev] at this
      have := hmax _ ((hmem _).2 (hprev v hv))
      omega
    have h0 : v.1.2 = 0 := cusp v hv (by rw [hxp, hxv]; decide)
    refine ⟨v, hv, h0, ?_, ?_⟩
    · rcases letterAt_of_cusp (W := W) (s := v) h0 with ⟨m, d, hℓ⟩ | ⟨m, hℓ⟩
      · exfalso
        have := xsign_cusp_l (s := v) (Prod.ext rfl h0) hℓ
        rw [hxv] at this; exact Bool.false_ne_true this
      · exact ⟨m, hℓ⟩
    · have := h v hv; rwa [colOf_of_cusp h0] at this
  · obtain ⟨v, hvS, hmin⟩ := S.exists_min_image xcoord2 hne
    have hv := (hmem v).1 hvS
    have hxv : xsign v = true := by
      by_contra hc
      have hc' : xsign v = false := by cases hx : xsign v; rfl; exact absurd hx hc
      have := (xcoord2_next hW v).2 hc'
      have := hmin _ ((hmem _).2 (hnext v hv))
      omega
    have hxp : xsign (prev hW v) = false := by
      by_contra hc
      have hc' : xsign (prev hW v) = true := by cases hx : xsign (prev hW v); exact absurd hx hc; rfl
      have := (xcoord2_next hW (prev hW v)).1 hc'
      rw [next_prev] at this
      have := hmin _ ((hmem _).2 (hprev v hv))
      omega
    have h0 : v.1.2 = 0 := cusp v hv (by rw [hxp, hxv]; decide)
    refine ⟨v, hv, h0, ?_, ?_⟩
    · rcases letterAt_of_cusp (W := W) (s := v) h0 with ⟨m, d, hℓ⟩ | ⟨m, hℓ⟩
      · exact ⟨m, d, hℓ⟩
      · exfalso
        have := xsign_cusp_r (s := v) (Prod.ext rfl h0) hℓ
        rw [hxv] at this; exact absurd this (by decide)
    · have := h v hv; rwa [colOf_of_cusp h0] at this

/-- A block of columns `[a, b)` without right cusps is left by every component. -/
theorem exists_ext_of_no_r (a b : ℕ) (hno : ∀ k, a ≤ k → k < b → ∀ m, letterAt W k ≠ .r m) (u : Slot W) :
    ∃ v, (nextPerm hW).SameCycle u v ∧ (colOf v + 1 ≤ a ∨ b ≤ colOf v) := by
  by_contra hc
  have h : ∀ v, (nextPerm hW).SameCycle u v → a ≤ colOf v ∧ colOf v < b := by
    intro v hv
    by_contra h'
    exact hc ⟨v, hv, by omega⟩
  obtain ⟨⟨v, -, -, ⟨m, hℓ⟩, ha, hb⟩, -⟩ := exists_cusps_of_no_ext hW a b u h
  exact hno _ ha hb m hℓ

/-- A block of columns `[a, b)` without left cusps is left by every component. -/
theorem exists_ext_of_no_l (a b : ℕ) (hno : ∀ k, a ≤ k → k < b → ∀ m d, letterAt W k ≠ .l m d) (u : Slot W) :
    ∃ v, (nextPerm hW).SameCycle u v ∧ (colOf v + 1 ≤ a ∨ b ≤ colOf v) := by
  by_contra hc
  have h : ∀ v, (nextPerm hW).SameCycle u v → a ≤ colOf v ∧ colOf v < b := by
    intro v hv
    by_contra h'
    exact hc ⟨v, hv, by omega⟩
  obtain ⟨-, ⟨v, -, -, ⟨m, d, hℓ⟩, ha, hb⟩⟩ := exists_cusps_of_no_ext hW a b u h
  exact hno _ ha hb m d hℓ

/-- The exit criterion for a polygon between the lines `x = pl.x a`, `x = pl.x b`, from an exterior piece in
every cycle (with the exterior pieces unchanged). -/
theorem exitsMv_of_ext (L : List HalfPlane) (pl : Placement) (mv : Slot W → Plane) {a b : ℕ}
    (ha : HalfPlane.xge (pl.x a) ∈ L) (hb : HalfPlane.xle (pl.x b) ∈ L)
    (hunch : ∀ v, (colOf v + 1 ≤ a ∨ b ≤ colOf v) → Unch pl hW mv v)
    (hex : ∀ u : Slot W, ∃ v, (nextPerm hW).SameCycle u v ∧ (colOf v + 1 ≤ a ∨ b ≤ colOf v)) :
    ExitsMv L hW mv := by
  apply exitsMv_of_sameCycle
  intro u
  obtain ⟨v, hv, hcol⟩ := hex u
  exact ⟨v, hv, pieceOut_of_extCol L pl hW mv ha hb (hunch v hcol) hcol⟩

end Exits

/-! #### I. Equal-length words: congruences of the slot combinatorics (for `typeIII_site`) -/

section Congr

variable (W W' : Word)

/-- The successor pair depends only on the letter of the column (cusp slots), the bit, and the position map of
the letter to the right (rightward) or to the left (leftward). -/
theorem nextPair_congr (k p : ℕ) (h0 : p = 0 → letterAt W k = letterAt W' k) (h0b : p = 0 → ∀ q, bit W k q = bit W' k q)
    (hb : p ≠ 0 → bit W k p = bit W' k p)
    (hR : p ≠ 0 → bit W k p = true → (letterAt W k).posR p = (letterAt W' k).posR p)
    (hL : p ≠ 0 → bit W k p = false → (letterAt W (k - 1)).posL p = (letterAt W' (k - 1)).posL p) :
    nextPair W (k, p) = nextPair W' (k, p) := by
  unfold nextPair
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    rw [h0 hp]
    cases letterAt W' k with
    | l m d => rfl
    | r m => dsimp only; rw [h0b hp m]
    | σ m => rfl
  · simp only [hp, ↓reduceIte]
    rw [← hb hp]
    cases hbb : bit W k p
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hL hp hbb]
    · simp only [↓reduceIte]
      rw [hR hp hbb]

theorem prevPair_congr (k p : ℕ) (h0 : p = 0 → letterAt W k = letterAt W' k) (h0b : p = 0 → ∀ q, bit W k q = bit W' k q)
    (hb : p ≠ 0 → bit W k p = bit W' k p)
    (hR : p ≠ 0 → bit W k p = false → (letterAt W k).posR p = (letterAt W' k).posR p)
    (hL : p ≠ 0 → bit W k p = true → (letterAt W (k - 1)).posL p = (letterAt W' (k - 1)).posL p) :
    prevPair W (k, p) = prevPair W' (k, p) := by
  unfold prevPair
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    rw [h0 hp]
    cases letterAt W' k with
    | l m d => rfl
    | r m => dsimp only; rw [h0b hp m]
    | σ m => rfl
  · simp only [hp, ↓reduceIte]
    rw [← hb hp]
    cases hbb : bit W k p
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hR hp hbb]
    · simp only [↓reduceIte]
      rw [hL hp hbb]

/-- The grid point of a slot depends only on the index of the column's letter (cusp slots). -/
theorem pt_congr (pl : Placement) (k p : ℕ) (h0 : p = 0 → (letterAt W k).idx = (letterAt W' k).idx) :
    pt pl W (k, p) = pt pl W' (k, p) := by
  unfold pt
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    rw [h0 hp]
  · simp only [hp, ↓reduceIte]

/-- The slot predicate depends on the lengths, the cut lengths and the kind of the letter. -/
theorem isSlot_congr (k p : ℕ) (hlen : W.length = W'.length) (hcut : (cut W k).length = (cut W' k).length)
    (h0 : (letterAt W k).isCrossing = (letterAt W' k).isCrossing) : IsSlot W (k, p) ↔ IsSlot W' (k, p) := by
  unfold IsSlot
  simp only
  rw [hlen, hcut, h0]

/-- The slots of two words with the same slot predicate. -/
def sameSlotEquiv (h : ∀ s, IsSlot W s ↔ IsSlot W' s) : Slot W ≃ Slot W' where
  toFun u := ⟨u.1, (h u.1).1 u.2⟩
  invFun u := ⟨u.1, (h u.1).2 u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem sameSlotEquiv_val (h : ∀ s, IsSlot W s ↔ IsSlot W' s) (u : Slot W) : (sameSlotEquiv W W' h u).1 = u.1 := rfl

@[simp] theorem sameSlotEquiv_symm_val (h : ∀ s, IsSlot W s ↔ IsSlot W' s) (u : Slot W') :
    ((sameSlotEquiv W W' h).symm u).1 = u.1 := rfl

/-- The successor corresponds under `sameSlotEquiv` when the successor pairs agree. -/
theorem sameSlotEquiv_next (hW : W.Closed) (hW' : W'.Closed) (h : ∀ s, IsSlot W s ↔ IsSlot W' s) (u : Slot W)
    (hn : nextPair W u.1 = nextPair W' u.1) :
    sameSlotEquiv W W' h (next hW u) = next hW' (sameSlotEquiv W W' h u) := by
  apply Subtype.ext
  rw [sameSlotEquiv_val, next_val, next_val, sameSlotEquiv_val, hn]

/-- The column of a slot depends only on the bit at a cut slot. -/
theorem colOf_congr (k p : ℕ) (hu : IsSlot W (k, p)) (hu' : IsSlot W' (k, p)) (hb : p ≠ 0 → bit W k p = bit W' k p) :
    colOf (⟨(k, p), hu⟩ : Slot W) = colOf (⟨(k, p), hu'⟩ : Slot W') := by
  unfold colOf
  by_cases hp : p = 0
  · simp [hp]
  · simp only [hp, ↓reduceIte]
    rw [hb hp]

/-- The x-direction of a slot depends only on the bit (cut slots) and the kind of the letter (cusp slots). -/
theorem xsign_congr (k p : ℕ) (hu : IsSlot W (k, p)) (hu' : IsSlot W' (k, p)) (hb : p ≠ 0 → bit W k p = bit W' k p)
    (h0 : p = 0 → letterAt W k = letterAt W' k) :
    xsign (⟨(k, p), hu⟩ : Slot W) = xsign (⟨(k, p), hu'⟩ : Slot W') := by
  unfold xsign
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    rw [h0 hp]
  · simp only [hp, ↓reduceIte]
    exact hb hp

end Congr

end

end U4

/-! ### L-geo (units U5, U6 on the geometry core U4) — the disc-local moves through the accepted
`RIData`/`RIIData`/`RIIIData` (`P_reidemeister_I/II/III`).  The move disc is a convex polygon hugging the
active strands (spectator strands run parallel one unit away, so such a disc exists; the full-height block
rectangle is NOT admissible: `ArcCover` forbids spectators).  For the length-changing patterns the comparison
diagram is a vertex-moved copy `D` of `realize W` (same shadow structure, the active strand's interior vertices
moved inside the disc, the removed crossings gone, everything else literally equal: `MoveMatch` with the
identity), whose named record is that of `realize W'` (record core U2, "active set" variant). -/

/-- LEAF (ng:front-III, sm-3:1995-2003 "an actual ordinary Reidemeister-III configuration ... The three
over/under choices give one strict height order ... Each physical pair crosses on both sides with the same
over/under bit and transported arrows"): the two standard realizations (same length, no cusp letter, so the
spectators are literally identical horizontal pieces) form an `RIII` site in the band disc
`[x_k, x_{k+3}] × [−(m+2)−ε, −m+ε]`; the arcs are the three strands entering at positions `m, m+1, m+2`,
named by height, the visit order along each arc reversed.  Either direction of `IsTypeIII` (the data are
symmetric in the two diagrams). -/
theorem typeIII_site {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    ∃ U : Set Plane, Nonempty (RIIIData U (realize W).diagram (realize W').diagram) := sorry

/-- LEAF (ng:front-II, sm-3:1979-1984 "the through-strand is under at both crossings [or over at both] ...
After rounding the cusp, the arcs bound an empty ordinary bigon with one common over-strand: an oriented
Reidemeister-II site"): a diagram `D` — `realize W` with the through-strand's two interior vertices in the
block lifted past the cusp arms — related to `realize W` by `RII` (the bigon disappears) and carrying the
named record of `realize W'` (no crossing left in the block; exterior visits and the block's connections of
the boundary slots agree).  All four variants of `IsTypeII` (right-cusp versions: the same strands backwards). -/
theorem typeII_move {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    ∃ D : Diagram, RII D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-- LEAF (ng:front-I, sm-3:1955-1963 "After rounding its two cusps, the unique crossing bounds an empty
ordinary monogon"): a diagram `D` — `realize W` with the curl's vertices moved so that the strand runs
through the block crossing-free — related to `realize W` by `RI` (the kink) and carrying the named record of
`realize W' = realize (X ++ Y)`. -/
theorem typeI_move {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-- LEAF (ng:deletions, sm-3:2027-2033 "a cusp whose own arms cross once.  Replace it by the uncrossed cusp
with the same two oriented boundary attachments.  After rounding, ordinary Reidemeister I deletes its empty
monogon"): a diagram `D` — `realize W` with the arms' interior vertices exchanged so that they no longer
cross — related to `realize W` by `RI` (a kink of sign −1) and carrying the named record of `realize W'`
(`l_i (!d)`: the bit flip is the arms' exchange of exits). -/
theorem crossedCusp_move {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    ∃ D : Diagram, RI D (realize W).diagram ∧
      Nonempty (RecordIso D.record (realize W').diagram.record) := sorry

/-! ### L-PL (unit U7) — the planarity fact for an arbitrary PL union of standard circles -/

section u7_helpers

/-! ### U7 helpers: PL chains as graphs of continuous functions -/

/-- The closed segment from `x` to `y`, as the image of `[0,1]`. -/
def u7_seg (x y : Plane) : Set Plane := (fun t : ℝ => x + t • (y - x)) '' Set.Icc (0 : ℝ) 1

theorem u7_mem_seg_iff {x y p : Plane} :
    p ∈ u7_seg x y ↔ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ p = x + t • (y - x) := by
  simp only [u7_seg, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨t, ⟨h0, h1⟩, rfl⟩; exact ⟨t, h0, h1, rfl⟩
  · rintro ⟨t, h0, h1, rfl⟩; exact ⟨t, ⟨h0, h1⟩, rfl⟩

theorem u7_seg_symm (x y : Plane) : u7_seg x y = u7_seg y x := by
  ext p
  simp only [u7_mem_seg_iff]
  constructor
  · rintro ⟨t, h0, h1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> simp <;> ring
  · rintro ⟨t, h0, h1, rfl⟩
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    ext <;> simp <;> ring

theorem u7_seg_isCompact (x y : Plane) : IsCompact (u7_seg x y) :=
  isCompact_Icc.image (by fun_prop)

theorem u7_left_mem_seg (x y : Plane) : x ∈ u7_seg x y :=
  u7_mem_seg_iff.2 ⟨0, le_rfl, zero_le_one, by simp⟩

theorem u7_right_mem_seg (x y : Plane) : y ∈ u7_seg x y :=
  u7_mem_seg_iff.2 ⟨1, zero_le_one, le_rfl, by simp⟩

/-- The x-range of a segment whose endpoints are ordered by `x`. -/
theorem u7_seg_fst_mem {x y p : Plane} (hxy : x.1 ≤ y.1) (hp : p ∈ u7_seg x y) :
    x.1 ≤ p.1 ∧ p.1 ≤ y.1 := by
  obtain ⟨t, h0, h1, rfl⟩ := u7_mem_seg_iff.1 hp
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
  constructor <;> nlinarith

/-- On a nonvertical segment the x-coordinate determines the point. -/
theorem u7_seg_eq_of_fst_eq {x y p q : Plane} (hxy : x.1 ≠ y.1) (hp : p ∈ u7_seg x y)
    (hq : q ∈ u7_seg x y) (h : p.1 = q.1) : p = q := by
  obtain ⟨t, -, -, rfl⟩ := u7_mem_seg_iff.1 hp
  obtain ⟨u, -, -, rfl⟩ := u7_mem_seg_iff.1 hq
  simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at h
  have hne : y.1 - x.1 ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have : t = u := mul_right_cancel₀ hne (by linarith)
  rw [this]

/-- The polygonal chain through `v 0, …, v n`. -/
def u7_chain (v : ℕ → Plane) (n : ℕ) : Set Plane := ⋃ j ∈ Set.Iio n, u7_seg (v j) (v (j + 1))

theorem u7_mem_chain_iff {v : ℕ → Plane} {n : ℕ} {p : Plane} :
    p ∈ u7_chain v n ↔ ∃ j, j < n ∧ p ∈ u7_seg (v j) (v (j + 1)) := by
  simp only [u7_chain, Set.mem_iUnion, Set.mem_Iio, exists_prop]

theorem u7_chain_isCompact (v : ℕ → Plane) (n : ℕ) : IsCompact (u7_chain v n) :=
  (Set.finite_Iio n).isCompact_biUnion fun _ _ => u7_seg_isCompact _ _

theorem u7_chain_lt {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    {a b : ℕ} (hab : a < b) (hb : b ≤ n) : (v a).1 < (v b).1 := by
  obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
  induction d with
  | zero => exact hv a (by omega)
  | succ d ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hv (a + d + 1) (by omega)
    rw [show a + (d + 1) + 1 = a + d + 1 + 1 by ring]
    exact h1.trans h2

theorem u7_chain_strictMono {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    StrictMonoOn (fun j => (v j).1) (Set.Iic n) := fun _ _ _ hb hab =>
  u7_chain_lt hv hab (Set.mem_Iic.1 hb)

theorem u7_chain_mono {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) : (v a).1 ≤ (v b).1 := by
  rcases hab.lt_or_eq with h | rfl
  · exact (u7_chain_lt hv h hb).le
  · exact le_rfl

theorem u7_chain_injOn {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    Set.InjOn Prod.fst (u7_chain v n) := by
  intro p hp q hq hpq
  obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
  obtain ⟨j', hj', hqj⟩ := u7_mem_chain_iff.1 hq
  wlog hle : j ≤ j' generalizing p q j j'
  · exact (this hq hp hpq.symm j' hj' hqj j hj hpj (by omega)).symm
  rcases hle.lt_or_eq with hlt | rfl
  · have h1 := u7_seg_fst_mem (hv j hj).le hpj
    have h2 := u7_seg_fst_mem (hv j' hj').le hqj
    have h3 : (v (j + 1)).1 ≤ (v j').1 := u7_chain_mono hv hlt hj'.le
    have e1 : p.1 = (v (j + 1)).1 := by linarith
    have e2 : q.1 = (v j').1 := by linarith
    have hp' : p = v (j + 1) := u7_seg_eq_of_fst_eq (hv j hj).ne hpj (u7_right_mem_seg _ _) e1
    have hq' : q = v j' := u7_seg_eq_of_fst_eq (hv j' hj').ne hqj (u7_left_mem_seg _ _) e2
    have hjj : j + 1 = j' := by
      by_contra hne
      have hlt' : j + 1 < j' := by omega
      have := (u7_chain_strictMono hv) (Set.mem_Iic.2 (by omega)) (Set.mem_Iic.2 hj'.le) hlt'
      simp only at this
      linarith
    rw [hp', hq', hjj]
  · exact u7_seg_eq_of_fst_eq (hv j hj).ne hpj hqj hpq

theorem u7_chain_fst_subset {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1) :
    Prod.fst '' u7_chain v n ⊆ Set.Icc (v 0).1 (v n).1 := by
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
  have h1 := u7_seg_fst_mem (hv j hj).le hpj
  have h2 := u7_chain_mono hv (Nat.zero_le j) hj.le
  have h3 := u7_chain_mono hv (Nat.succ_le_of_lt hj) le_rfl
  exact ⟨by linarith, by linarith⟩

theorem u7_chain_exists_piece {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    (hn : 0 < n) {x : ℝ} (hx : x ∈ Set.Icc (v 0).1 (v n).1) :
    ∃ j, j < n ∧ (v j).1 ≤ x ∧ x ≤ (v (j + 1)).1 := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hxn : x ≤ (v n).1
    · rcases Nat.eq_zero_or_pos n with rfl | hn'
      · exact ⟨0, by omega, hx.1, hx.2⟩
      · obtain ⟨j, hj, h1, h2⟩ := ih (fun j hj => hv j (by omega)) hn' ⟨hx.1, hxn⟩
        exact ⟨j, by omega, h1, h2⟩
    · exact ⟨n, by omega, (not_le.1 hxn).le, hx.2⟩

theorem u7_chain_fst_image {v : ℕ → Plane} {n : ℕ} (hv : ∀ j, j < n → (v j).1 < (v (j + 1)).1)
    (hn : 0 < n) : Prod.fst '' u7_chain v n = Set.Icc (v 0).1 (v n).1 := by
  refine Set.Subset.antisymm (u7_chain_fst_subset hv) ?_
  intro x hx
  obtain ⟨j, hj, h1, h2⟩ := u7_chain_exists_piece hv hn hx
  have hd : 0 < (v (j + 1)).1 - (v j).1 := sub_pos.2 (hv j hj)
  refine ⟨v j + ((x - (v j).1) / ((v (j + 1)).1 - (v j).1)) • (v (j + 1) - v j), ?_, ?_⟩
  · exact u7_mem_chain_iff.2 ⟨j, hj, u7_mem_seg_iff.2
      ⟨_, div_nonneg (by linarith) hd.le, (div_le_one hd).2 (by linarith), rfl⟩⟩
  · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
    field_simp
    ring

/-- A compact set that is the graph of a function over `Icc a b` is the graph of a continuous
function (compact → Hausdorff bijections are homeomorphisms). -/
theorem u7_exists_graphFun {K : Set Plane} {a b : ℝ} (hab : a ≤ b) (hK : IsCompact K)
    (hinj : Set.InjOn Prod.fst K) (himg : Prod.fst '' K = Set.Icc a b) :
    ∃ f : ℝ → ℝ, Continuous f ∧ (∀ x ∈ Set.Icc a b, (x, f x) ∈ K) ∧ (∀ p ∈ K, f p.1 = p.2) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let φ : K → Set.Icc a b := fun p => ⟨p.1.1, himg ▸ Set.mem_image_of_mem Prod.fst p.2⟩
  have hφc : Continuous φ := Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
  have hφinj : Function.Injective φ := by
    intro p q hpq
    exact Subtype.ext (hinj p.2 q.2 (congrArg Subtype.val hpq))
  have hφsurj : Function.Surjective φ := by
    intro x
    have hx : (x : ℝ) ∈ Prod.fst '' K := by rw [himg]; exact x.2
    obtain ⟨p, hp, hpx⟩ := hx
    exact ⟨⟨p, hp⟩, Subtype.ext hpx⟩
  let e : K ≃ Set.Icc a b := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have hec : Continuous e := hφc
  let h : K ≃ₜ Set.Icc a b := hec.homeoOfEquivCompactToT2
  have h1 : ∀ p : K, ((h p : Set.Icc a b) : ℝ) = (p.1).1 := fun p => rfl
  have hkey : ∀ x ∈ Set.Icc a b, ((h.symm (Set.projIcc a b hab x)).1).1 = x := by
    intro x hx
    have := h1 (h.symm (Set.projIcc a b hab x))
    rw [h.apply_symm_apply] at this
    rw [← this]
    exact congrArg Subtype.val (Set.projIcc_of_mem hab hx)
  have hmem : ∀ x ∈ Set.Icc a b, (x, ((h.symm (Set.projIcc a b hab x)).1).2) ∈ K := by
    intro x hx
    have hp := (h.symm (Set.projIcc a b hab x)).2
    rw [show (x, ((h.symm (Set.projIcc a b hab x)).1).2) = (h.symm (Set.projIcc a b hab x)).1 from
      Prod.ext (hkey x hx).symm rfl]
    exact hp
  refine ⟨fun x => ((h.symm (Set.projIcc a b hab x)).1).2, ?_, hmem, ?_⟩
  · exact continuous_snd.comp (continuous_subtype_val.comp (h.symm.continuous.comp continuous_projIcc))
  · intro p hp
    have hx : p.1 ∈ Set.Icc a b := himg ▸ ⟨p, hp, rfl⟩
    have := hinj (hmem p.1 hx) hp rfl
    have h2 : ((p.1, ((h.symm (Set.projIcc a b hab p.1)).1).2) : Plane).2 = p.2 := congrArg Prod.snd this
    exact h2


/-! ### U7 helpers: PL-front facts -/

variable (F : PLFront)

/-- The segment of a strand `⟨i, m⟩` as `u7_seg` between its two vertices. -/
theorem u7_seg_eq (i : Fin F.Γ.c) (m : ZMod (F.Γ.comp i).k) :
    F.Γ.seg ⟨i, m⟩ = u7_seg ((F.Γ.comp i).P m) ((F.Γ.comp i).P (m + 1)) := by
  ext p
  rw [Shadow.seg_mk, u7_mem_seg_iff]
  simp only [edgeSegment, edgePoint, edge, Set.mem_ofPred_eq]

/-- Along a run of vertices none of which is a cusp, the rightward bit is constant. -/
theorem u7_xdir_run (i : Fin F.Γ.c) (a : ZMod (F.Γ.comp i).k) (n : ℕ)
    (hno : ∀ j : ℕ, 0 < j → j < n → ¬ F.IsCusp ⟨i, a + j⟩) :
    ∀ j : ℕ, j < n → F.xdir ⟨i, a + j⟩ = F.xdir ⟨i, a⟩ := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have hnc := hno (j + 1) (Nat.succ_pos j) hj
    have h := F.xdir_prev_eq_of_not_isCusp hnc
    have hprev : F.prev ⟨i, a + ((j + 1 : ℕ) : ZMod (F.Γ.comp i).k)⟩ = ⟨i, a + j⟩ := by
      simp only [PLFront.prev, Nat.cast_succ]
      congr 1
      ring
    rw [hprev] at h
    rw [← h]
    exact ih (by omega)

/-- A vertex at which the rightward bit changes is a cusp. -/
theorem u7_isCusp_of_xdir_ne {s : F.Γ.Strand} (h : F.xdir (F.prev s) ≠ F.xdir s) : F.IsCusp s := by
  by_contra hc
  exact h (F.xdir_prev_eq_of_not_isCusp hc)

/-- The two arms of a cusp meet only at the cusp vertex (they are not collinear). -/
theorem u7_seg_prev_inter_cusp {s : F.Γ.Strand} (h : F.IsCusp s) {p : Plane}
    (hp : p ∈ F.Γ.seg (F.prev s)) (hq : p ∈ F.Γ.seg s) : p = F.Γ.tail s := by
  obtain ⟨i, m⟩ := s
  have hprev : F.prev ⟨i, m⟩ = ⟨i, m - 1⟩ := rfl
  rw [hprev, u7_seg_eq, sub_add_cancel] at hp
  rw [u7_seg_eq] at hq
  obtain ⟨t₁, -, -, hp'⟩ := u7_mem_seg_iff.1 hp
  obtain ⟨t₂, -, -, hq'⟩ := u7_mem_seg_iff.1 hq
  set P := (F.Γ.comp i).P with hP
  have hIn : F.eIn ⟨i, m⟩ = P m - P (m - 1) := by
    show F.Γ.dir ⟨i, m - 1⟩ = P m - P (m - 1)
    rw [Shadow.dir_mk]
    simp only [edge, hP]
    rw [sub_add_cancel]
  have hOut : F.eOut ⟨i, m⟩ = P (m + 1) - P m := rfl
  have hdet := F.cusp_det_ne_zero h
  rw [hIn, hOut] at hdet
  have hrel : (t₁ - 1) • (P m - P (m - 1)) = t₂ • (P (m + 1) - P m) := by
    have e := hp'.symm.trans hq'
    ext
    · have := congrArg Prod.fst e
      simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul] at this ⊢
      linarith
    · have := congrArg Prod.snd e
      simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul] at this ⊢
      linarith
  have hdet0 : t₂ * det (P m - P (m - 1)) (P (m + 1) - P m) = 0 := by
    have h3 : det (P m - P (m - 1)) (t₂ • (P (m + 1) - P m)) =
        t₂ * det (P m - P (m - 1)) (P (m + 1) - P m) := by
      simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [← h3, ← hrel]
    simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
    ring
  have ht₂ : t₂ = 0 := by
    rcases mul_eq_zero.1 hdet0 with h0 | h0
    · exact h0
    · exact absurd h0 hdet
  rw [hq', ht₂, zero_smul, add_zero]
  rfl


/-- The planarity fact on one component: with a unique left cusp `⟨i, ℓ⟩`, a unique right cusp `⟨i, r⟩`
and no crossing, the left cusp is downward iff the right cusp is not.  The two x-monotone arcs are graphs
of continuous functions over `[a, b]` whose difference never vanishes inside, so its sign at the two
ends agrees; the sign at each end is read off the arm heights (`isDownCusp_iff_armIn_above`). -/
theorem u7_down_iff_not_down (h : F.IsStandardCircles) (i : Fin F.Γ.c) (ℓ r : ZMod (F.Γ.comp i).k)
    (hL : F.IsLeftCusp ⟨i, ℓ⟩) (hR : F.IsRightCusp ⟨i, r⟩)
    (hLu : ∀ m, F.IsLeftCusp ⟨i, m⟩ → m = ℓ) (hRu : ∀ m, F.IsRightCusp ⟨i, m⟩ → m = r) :
    (F.IsDownCusp ⟨i, ℓ⟩ ↔ ¬ F.IsDownCusp ⟨i, r⟩) := by
  classical
  have hcusp : ∀ m, F.IsCusp ⟨i, m⟩ → m = ℓ ∨ m = r := fun m hm => by
    rcases (F.isCusp_iff _).1 hm with hl | hr
    · exact Or.inl (hLu m hl)
    · exact Or.inr (hRu m hr)
  have hℓr : ℓ ≠ r := by
    intro e
    subst e
    exact F.not_isLeftCusp_and_isRightCusp _ ⟨hL, hR⟩
  -- the number of rightward strands `n` and of leftward strands `m`
  set n := (r - ℓ).val with hn
  have hnk : n < (F.Γ.comp i).k := ZMod.val_lt _
  have hn0 : 0 < n := ZMod.val_pos.2 (sub_ne_zero.2 hℓr.symm)
  have hncast : (n : ZMod (F.Γ.comp i).k) = r - ℓ := ZMod.natCast_zmod_val _
  set m := (F.Γ.comp i).k - n with hm
  have hm0 : 0 < m := by omega
  have hmcast : (m : ZMod (F.Γ.comp i).k) = ℓ - r := by
    rw [hm, Nat.cast_sub hnk.le, ZMod.natCast_self, hncast]; ring
  have hcast_inj : ∀ j j' : ℕ, j < (F.Γ.comp i).k → j' < (F.Γ.comp i).k →
      (j : ZMod (F.Γ.comp i).k) = j' → j = j' := fun j j' hj hj' e => by
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at e
    exact e
  -- the rightward bits along the two runs
  have hA : ∀ j : ℕ, j < n → F.xdir ⟨i, ℓ + j⟩ = true := by
    have hrun := u7_xdir_run F i ℓ n (fun j hj0 hjn hc => by
      rcases hcusp _ hc with e | e
      · have e' : (j : ZMod (F.Γ.comp i).k) = ((0 : ℕ) : ZMod (F.Γ.comp i).k) := by
          rw [Nat.cast_zero]; exact (add_eq_left).1 e
        have := hcast_inj j 0 (by omega) (by omega) e'
        omega
      · have e' : (j : ZMod (F.Γ.comp i).k) = (n : ZMod (F.Γ.comp i).k) := by
          rw [hncast]; exact eq_sub_of_add_eq' e
        have := hcast_inj j n (by omega) hnk e'
        omega)
    intro j hj
    rw [hrun j hj]
    exact (F.xdir_eq_true_iff _).2 hL.2
  have hB : ∀ j : ℕ, j < m → F.xdir ⟨i, r + j⟩ = false := by
    have hrun := u7_xdir_run F i r m (fun j hj0 hjm hc => by
      rcases hcusp _ hc with e | e
      · have e' : (j : ZMod (F.Γ.comp i).k) = (m : ZMod (F.Γ.comp i).k) := by
          rw [hmcast]; exact eq_sub_of_add_eq' e
        have := hcast_inj j m (by omega) (by omega) e'
        omega
      · have e' : (j : ZMod (F.Γ.comp i).k) = ((0 : ℕ) : ZMod (F.Γ.comp i).k) := by
          rw [Nat.cast_zero]; exact (add_eq_left).1 e
        have := hcast_inj j 0 (by omega) (by omega) e'
        omega)
    intro j hj
    rw [hrun j hj]
    exact (F.xdir_eq_false_iff _).2 hR.2
  -- the two vertex chains
  set vA : ℕ → Plane := fun j => (F.Γ.comp i).P (ℓ + j) with hvAdef
  set vB : ℕ → Plane := fun j => (F.Γ.comp i).P (r + ((m - j : ℕ) : ZMod (F.Γ.comp i).k)) with hvBdef
  have hdirA : ∀ j : ℕ, F.Γ.dir ⟨i, ℓ + j⟩ = (F.Γ.comp i).P (ℓ + j + 1) - (F.Γ.comp i).P (ℓ + j) :=
    fun j => rfl
  have hdirB : ∀ j : ℕ, F.Γ.dir ⟨i, r + j⟩ = (F.Γ.comp i).P (r + j + 1) - (F.Γ.comp i).P (r + j) :=
    fun j => rfl
  have hvA : ∀ j, j < n → (vA j).1 < (vA (j + 1)).1 := fun j hj => by
    have hx := (F.xdir_eq_true_iff ⟨i, ℓ + j⟩).1 (hA j hj)
    rw [hdirA] at hx
    simp only [hvAdef, Nat.cast_succ, ← add_assoc]
    simp only [Prod.fst_sub] at hx
    linarith
  have hvB : ∀ j, j < m → (vB j).1 < (vB (j + 1)).1 := fun j hj => by
    have e1 : m - j = (m - (j + 1)) + 1 := by omega
    have hx := (F.xdir_eq_false_iff ⟨i, r + ((m - (j + 1) : ℕ) : ZMod (F.Γ.comp i).k)⟩).1
      (hB _ (by omega))
    rw [hdirB] at hx
    simp only [hvBdef]
    rw [e1, Nat.cast_succ, ← add_assoc]
    simp only [Prod.fst_sub] at hx
    linarith
  -- the strands' segments are the chain pieces
  have hsegA : ∀ j : ℕ, F.Γ.seg ⟨i, ℓ + j⟩ = u7_seg (vA j) (vA (j + 1)) := fun j => by
    rw [u7_seg_eq]
    simp only [hvAdef, Nat.cast_succ, ← add_assoc]
  have hsegB : ∀ j : ℕ, j < m →
      F.Γ.seg ⟨i, r + ((m - (j + 1) : ℕ) : ZMod (F.Γ.comp i).k)⟩ = u7_seg (vB j) (vB (j + 1)) :=
    fun j hj => by
    rw [u7_seg_eq, u7_seg_symm]
    simp only [hvBdef]
    rw [show m - j = (m - (j + 1)) + 1 by omega, Nat.cast_succ, ← add_assoc]
  set KA := u7_chain vA n with hKA
  set KB := u7_chain vB m with hKB
  have hKA_mem : ∀ p ∈ KA, ∃ j, j < n ∧ p ∈ F.Γ.seg ⟨i, ℓ + j⟩ := fun p hp => by
    obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
    exact ⟨j, hj, by rw [hsegA j]; exact hpj⟩
  have hKB_mem : ∀ p ∈ KB, ∃ j, j < m ∧ p ∈ F.Γ.seg ⟨i, r + j⟩ := fun p hp => by
    obtain ⟨j, hj, hpj⟩ := u7_mem_chain_iff.1 hp
    exact ⟨m - (j + 1), by omega, by rw [hsegB j hj]; exact hpj⟩
  -- endpoints
  have hvA0 : vA 0 = (F.Γ.comp i).P ℓ := by simp [hvAdef]
  have hvAn : vA n = (F.Γ.comp i).P r := by
    simp only [hvAdef]; rw [hncast]; congr 1; ring
  have hvB0 : vB 0 = (F.Γ.comp i).P ℓ := by
    simp only [hvBdef, Nat.sub_zero]; rw [hmcast]; congr 1; ring
  have hvBm : vB m = (F.Γ.comp i).P r := by simp [hvBdef]
  set a := ((F.Γ.comp i).P ℓ).1 with ha
  set b := ((F.Γ.comp i).P r).1 with hb
  have hab : a < b := by
    have := u7_chain_lt hvA hn0 le_rfl
    rwa [hvA0, hvAn] at this
  obtain ⟨fA, hfAc, hfA1, hfA2⟩ := u7_exists_graphFun hab.le (u7_chain_isCompact vA n)
    (u7_chain_injOn hvA) (by rw [u7_chain_fst_image hvA hn0, hvA0, hvAn])
  obtain ⟨fB, hfBc, hfB1, hfB2⟩ := u7_exists_graphFun hab.le (u7_chain_isCompact vB m)
    (u7_chain_injOn hvB) (by rw [u7_chain_fst_image hvB hm0, hvB0, hvBm])
  set g : ℝ → ℝ := fun x => fB x - fA x with hg
  have hgc : Continuous g := hfBc.sub hfAc
  -- (B) the two arcs never meet strictly between the cusps: no crossing, and adjacent strands of
  -- opposite bits meet at a cusp vertex only
  have hg0 : ∀ x ∈ Set.Ioo a b, g x ≠ 0 := by
    intro x hx hgx
    have hxI : x ∈ Set.Icc a b := Set.Ioo_subset_Icc_self hx
    have hpA := hfA1 x hxI
    have hpB := hfB1 x hxI
    have heq : fB x = fA x := sub_eq_zero.1 hgx
    rw [heq] at hpB
    obtain ⟨j, hj, hpj⟩ := hKA_mem _ hpA
    obtain ⟨j', hj', hpj'⟩ := hKB_mem _ hpB
    have hs : F.xdir ⟨i, ℓ + j⟩ = true := hA j hj
    have ht : F.xdir ⟨i, r + j'⟩ = false := hB j' hj'
    have hvertex : ∀ q : ZMod (F.Γ.comp i).k, ((x, fA x) : Plane) = (F.Γ.comp i).P q →
        F.IsCusp ⟨i, q⟩ → False := by
      intro q hpq hc
      have hx1 : x = ((F.Γ.comp i).P q).1 := congrArg Prod.fst hpq
      rcases hcusp q hc with e | e
      · rw [e] at hx1
        exact absurd hx1 (ne_of_gt hx.1)
      · rw [e] at hx1
        exact absurd hx1 (ne_of_lt hx.2)
    by_cases hadj : F.Γ.Adjacent ⟨i, ℓ + j⟩ ⟨i, r + j'⟩
    · rw [Shadow.adjacent_mk_iff] at hadj
      rcases hadj with h1 | h1 | h1
      · have e : r + (j' : ZMod (F.Γ.comp i).k) = ℓ + j - 1 := by linear_combination h1
        have hts : (⟨i, r + j'⟩ : F.Γ.Strand) = F.prev ⟨i, ℓ + j⟩ := by
          show _ = (⟨i, ℓ + j - 1⟩ : F.Γ.Strand)
          rw [e]
        have hc : F.IsCusp ⟨i, ℓ + j⟩ := u7_isCusp_of_xdir_ne F (by rw [← hts, ht, hs]; decide)
        have hp := u7_seg_prev_inter_cusp F hc (by rw [← hts]; exact hpj') hpj
        exact hvertex _ hp hc
      · have e : r + (j' : ZMod (F.Γ.comp i).k) = ℓ + j := by linear_combination h1
        rw [e, hs] at ht
        exact Bool.noConfusion ht
      · have e : ℓ + (j : ZMod (F.Γ.comp i).k) = r + j' - 1 := by
          linear_combination (-1 : ZMod (F.Γ.comp i).k) * h1
        have hst : (⟨i, ℓ + j⟩ : F.Γ.Strand) = F.prev ⟨i, r + j'⟩ := by
          show _ = (⟨i, r + j' - 1⟩ : F.Γ.Strand)
          rw [e]
        have hc : F.IsCusp ⟨i, r + j'⟩ := u7_isCusp_of_xdir_ne F (by rw [← hst, ht, hs]; decide)
        have hp := u7_seg_prev_inter_cusp F hc (by rw [← hst]; exact hpj) hpj'
        exact hvertex _ hp hc
    · have hcr : F.Γ.IsCrossing {⟨i, ℓ + j⟩, ⟨i, r + j'⟩} :=
        F.Γ.isCrossing_pair hadj ⟨_, hpj, hpj'⟩
      exact h.1.elim (⟨_, hcr⟩ : F.Γ.Crossing)
  -- (C) hence `g` has constant sign on `(a, b)` (intermediate value theorem)
  have hsign : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, 0 < g x → 0 < g y := by
    intro x hx y hy hgx
    by_contra hgy
    have hgy' : g y < 0 := lt_of_le_of_ne (not_lt.1 hgy) (hg0 y hy)
    obtain ⟨z, hz, hz0⟩ :=
      isPreconnected_Ioo.intermediate_value hy hx hgc.continuousOn ⟨hgy'.le, hgx.le⟩
    exact hg0 z hz hz0
  -- (D) the sign near the left cusp reads the arm heights there
  have hLc := hL.isCusp
  set e₁ := F.eOut ⟨i, ℓ⟩ with he₁
  set e₂ := F.armIn ⟨i, ℓ⟩ with he₂
  have he₁1 : 0 < e₁.1 := hL.2
  have he₂1 : 0 < e₂.1 := by
    have := hL.1
    simp only [he₂, PLFront.armIn, Prod.fst_neg]
    linarith
  have he₁def : e₁ = (F.Γ.comp i).P (ℓ + 1) - (F.Γ.comp i).P ℓ := rfl
  have he₂def : e₂ = (F.Γ.comp i).P (ℓ - 1) - (F.Γ.comp i).P ℓ := by
    show -(F.Γ.dir ⟨i, ℓ - 1⟩) = _
    rw [Shadow.dir_mk]
    simp only [edge]
    rw [sub_add_cancel, neg_sub]
  set δ := min e₁.1 e₂.1 / 2 with hδ
  have hmin : 0 < min e₁.1 e₂.1 := lt_min he₁1 he₂1
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hδ1 : δ < e₁.1 := by have := min_le_left e₁.1 e₂.1; rw [hδ]; linarith
  have hδ2 : δ < e₂.1 := by have := min_le_right e₁.1 e₂.1; rw [hδ]; linarith
  have hpA : ((F.Γ.comp i).P ℓ + (δ / e₁.1) • e₁) ∈ KA := by
    refine u7_mem_chain_iff.2 ⟨0, hn0, ?_⟩
    rw [← hsegA 0, Nat.cast_zero, add_zero, u7_seg_eq]
    exact u7_mem_seg_iff.2 ⟨δ / e₁.1, div_nonneg hδ0.le he₁1.le, (div_le_one he₁1).2 hδ1.le, rfl⟩
  have hpB : ((F.Γ.comp i).P ℓ + (δ / e₂.1) • e₂) ∈ KB := by
    refine u7_mem_chain_iff.2 ⟨0, hm0, ?_⟩
    rw [← hsegB 0 hm0]
    have e : r + ((m - (0 + 1) : ℕ) : ZMod (F.Γ.comp i).k) = ℓ - 1 := by
      rw [Nat.zero_add, Nat.cast_pred hm0, hmcast]; ring
    rw [e, u7_seg_eq, sub_add_cancel, u7_seg_symm]
    exact u7_mem_seg_iff.2 ⟨δ / e₂.1, div_nonneg hδ0.le he₂1.le, (div_le_one he₂1).2 hδ2.le,
      by rw [he₂def]⟩
  have hfAδ : fA (a + δ) = ((F.Γ.comp i).P ℓ).2 + (δ / e₁.1) * e₁.2 := by
    have h1 := hfA2 _ hpA
    have hx : ((F.Γ.comp i).P ℓ + (δ / e₁.1) • e₁).1 = a + δ := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_mul_cancel₀ _ he₁1.ne']
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hfBδ : fB (a + δ) = ((F.Γ.comp i).P ℓ).2 + (δ / e₂.1) * e₂.2 := by
    have h1 := hfB2 _ hpB
    have hx : ((F.Γ.comp i).P ℓ + (δ / e₂.1) • e₂).1 = a + δ := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_mul_cancel₀ _ he₂1.ne']
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hgδ : g (a + δ) = δ * (PLFront.armHeight e₂ - PLFront.armHeight e₁) := by
    simp only [hg, hfAδ, hfBδ, PLFront.armHeight, abs_of_pos he₁1, abs_of_pos he₂1]
    ring
  have hL_iff : F.IsDownCusp ⟨i, ℓ⟩ ↔ 0 < g (a + δ) := by
    rw [F.isDownCusp_iff_armIn_above hLc, hgδ]
    show PLFront.armHeight e₁ < PLFront.armHeight e₂ ↔ _
    constructor
    · intro hlt
      exact mul_pos hδ0 (sub_pos.2 hlt)
    · intro hpos
      by_contra hle
      have := mul_nonneg hδ0.le (sub_nonneg.2 (not_lt.1 hle))
      linarith
  have haδ : a + δ ∈ Set.Ioo a b := by
    refine ⟨by linarith, ?_⟩
    have h1 : (vA 1).1 = a + e₁.1 := by
      simp only [hvAdef, Nat.cast_one, he₁def, Prod.fst_sub]
      rw [ha]; ring
    have h2 := u7_chain_mono hvA (show 1 ≤ n from hn0) le_rfl
    rw [hvAn] at h2
    linarith [hb]
  -- (E) the sign near the right cusp reads the arm heights there
  have hRc := hR.isCusp
  set e₃ := F.eOut ⟨i, r⟩ with he₃
  set e₄ := F.armIn ⟨i, r⟩ with he₄
  have he₃1 : e₃.1 < 0 := hR.2
  have he₄1 : e₄.1 < 0 := by
    have := hR.1
    simp only [he₄, PLFront.armIn, Prod.fst_neg]
    linarith
  have he₃def : e₃ = (F.Γ.comp i).P (r + 1) - (F.Γ.comp i).P r := rfl
  have he₄def : e₄ = (F.Γ.comp i).P (r - 1) - (F.Γ.comp i).P r := by
    show -(F.Γ.dir ⟨i, r - 1⟩) = _
    rw [Shadow.dir_mk]
    simp only [edge]
    rw [sub_add_cancel, neg_sub]
  set δ' := min (-e₃.1) (-e₄.1) / 2 with hδ'
  have hmin' : 0 < min (-e₃.1) (-e₄.1) := lt_min (by linarith) (by linarith)
  have hδ'0 : 0 < δ' := by rw [hδ']; linarith
  have hδ'3 : δ' < -e₃.1 := by have := min_le_left (-e₃.1) (-e₄.1); rw [hδ']; linarith
  have hδ'4 : δ' < -e₄.1 := by have := min_le_right (-e₃.1) (-e₄.1); rw [hδ']; linarith
  have hpB' : ((F.Γ.comp i).P r + (δ' / (-e₃.1)) • e₃) ∈ KB := by
    refine u7_mem_chain_iff.2 ⟨m - 1, by omega, ?_⟩
    rw [← hsegB (m - 1) (by omega)]
    have e : r + ((m - (m - 1 + 1) : ℕ) : ZMod (F.Γ.comp i).k) = r := by
      rw [show m - (m - 1 + 1) = 0 by omega, Nat.cast_zero, add_zero]
    rw [e, u7_seg_eq]
    exact u7_mem_seg_iff.2 ⟨δ' / (-e₃.1), div_nonneg hδ'0.le (by linarith),
      (div_le_one (by linarith)).2 hδ'3.le, rfl⟩
  have hpA' : ((F.Γ.comp i).P r + (δ' / (-e₄.1)) • e₄) ∈ KA := by
    refine u7_mem_chain_iff.2 ⟨n - 1, by omega, ?_⟩
    rw [← hsegA (n - 1)]
    have e : ℓ + ((n - 1 : ℕ) : ZMod (F.Γ.comp i).k) = r - 1 := by
      rw [Nat.cast_pred hn0, hncast]; ring
    rw [e, u7_seg_eq, sub_add_cancel, u7_seg_symm]
    exact u7_mem_seg_iff.2 ⟨δ' / (-e₄.1), div_nonneg hδ'0.le (by linarith),
      (div_le_one (by linarith)).2 hδ'4.le, by rw [he₄def]⟩
  have hfBδ' : fB (b - δ') = ((F.Γ.comp i).P r).2 + (δ' / (-e₃.1)) * e₃.2 := by
    have h1 := hfB2 _ hpB'
    have hx : ((F.Γ.comp i).P r + (δ' / (-e₃.1)) • e₃).1 = b - δ' := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_neg, neg_mul, div_mul_cancel₀ _ he₃1.ne, ← sub_eq_add_neg]
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hfAδ' : fA (b - δ') = ((F.Γ.comp i).P r).2 + (δ' / (-e₄.1)) * e₄.2 := by
    have h1 := hfA2 _ hpA'
    have hx : ((F.Γ.comp i).P r + (δ' / (-e₄.1)) • e₄).1 = b - δ' := by
      simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
      rw [div_neg, neg_mul, div_mul_cancel₀ _ he₄1.ne, ← sub_eq_add_neg]
    rw [hx] at h1
    rw [h1]
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
  have hgδ' : g (b - δ') = δ' * (PLFront.armHeight e₃ - PLFront.armHeight e₄) := by
    simp only [hg, hfAδ', hfBδ', PLFront.armHeight, abs_of_neg he₃1, abs_of_neg he₄1]
    ring
  have hR_iff : F.IsDownCusp ⟨i, r⟩ ↔ g (b - δ') < 0 := by
    rw [F.isDownCusp_iff_armIn_above hRc, hgδ']
    show PLFront.armHeight e₃ < PLFront.armHeight e₄ ↔ _
    constructor
    · intro hlt
      exact mul_neg_of_pos_of_neg hδ'0 (sub_neg.2 hlt)
    · intro hneg
      by_contra hle
      have := mul_nonneg hδ'0.le (sub_nonneg.2 (not_lt.1 hle))
      linarith
  have hbδ' : b - δ' ∈ Set.Ioo a b := by
    refine ⟨?_, by linarith⟩
    have h1 : (vA (n - 1)).1 = b + e₄.1 := by
      simp only [hvAdef]
      rw [Nat.cast_pred hn0, hncast, he₄def, Prod.fst_sub,
        show ℓ + (r - ℓ - 1) = r - 1 by ring, hb]
      ring
    have h2 := u7_chain_mono hvA (Nat.zero_le (n - 1)) (Nat.sub_le n 1)
    rw [hvA0] at h2
    linarith [ha]
  -- (F) conclusion: `L` down ↔ `g > 0` on `(a, b)` ↔ `R` not down
  constructor
  · intro hdL hdR
    have h1 := hL_iff.1 hdL
    have h2 := hR_iff.1 hdR
    have := hsign _ haδ _ hbδ' h1
    linarith
  · intro hndR
    have h2 : 0 < g (b - δ') :=
      lt_of_le_of_ne (not_lt.1 (fun hlt => hndR (hR_iff.2 hlt))) (hg0 _ hbδ').symm
    exact hL_iff.2 (hsign _ hbδ' _ haδ h2)


/-- Each component of a union of standard circles has exactly one downward cusp: its two cusps are the
unique left and right cusps, and `u7_down_iff_not_down` says exactly one of them is downward. -/
theorem u7_card_down_eq_one (h : F.IsStandardCircles) (i : Fin F.Γ.c) :
    Nat.card {s : F.Γ.Strand // s.1 = i ∧ F.IsDownCusp s} = 1 := by
  obtain ⟨hLc, hRc⟩ := h.2 i
  rw [Nat.card_eq_one_iff_unique] at hLc hRc
  obtain ⟨⟨hLsub⟩, ⟨⟨L, hLi, hL⟩⟩⟩ := hLc
  obtain ⟨⟨hRsub⟩, ⟨⟨R, hRi, hR⟩⟩⟩ := hRc
  have hLu : ∀ s, s.1 = i → F.IsLeftCusp s → s = L := fun s hs hsl =>
    congrArg Subtype.val (hLsub ⟨s, hs, hsl⟩ ⟨L, hLi, hL⟩)
  have hRu : ∀ s, s.1 = i → F.IsRightCusp s → s = R := fun s hs hsr =>
    congrArg Subtype.val (hRsub ⟨s, hs, hsr⟩ ⟨R, hRi, hR⟩)
  obtain ⟨iL, ℓ⟩ := L
  obtain ⟨iR, r⟩ := R
  simp only at hLi hRi
  subst hLi
  subst hRi
  have hiff := u7_down_iff_not_down F h iR ℓ r hL hR
    (fun q hq => by have := hLu ⟨iR, q⟩ rfl hq; simpa using this)
    (fun q hq => by have := hRu ⟨iR, q⟩ rfl hq; simpa using this)
  have hcusp : ∀ s : F.Γ.Strand, s.1 = iR → F.IsCusp s → s = ⟨iR, ℓ⟩ ∨ s = ⟨iR, r⟩ :=
    fun s hs hc => by
    rcases (F.isCusp_iff s).1 hc with hl | hr
    · exact Or.inl (hLu s hs hl)
    · exact Or.inr (hRu s hs hr)
  rw [Nat.card_eq_one_iff_unique]
  by_cases hdL : F.IsDownCusp ⟨iR, ℓ⟩
  · have hdR : ¬ F.IsDownCusp ⟨iR, r⟩ := hiff.1 hdL
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨iR, ℓ⟩, rfl, hdL⟩⟩⟩
    have ha : a.1 = ⟨iR, ℓ⟩ := by
      rcases hcusp a.1 a.2.1 a.2.2.isCusp with e | e
      · exact e
      · exact absurd (e ▸ a.2.2) hdR
    have hb : b.1 = ⟨iR, ℓ⟩ := by
      rcases hcusp b.1 b.2.1 b.2.2.isCusp with e | e
      · exact e
      · exact absurd (e ▸ b.2.2) hdR
    exact Subtype.ext (ha.trans hb.symm)
  · have hdR : F.IsDownCusp ⟨iR, r⟩ := by
      by_contra hc
      exact hdL (hiff.2 hc)
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨⟨iR, r⟩, rfl, hdR⟩⟩⟩
    have ha : a.1 = ⟨iR, r⟩ := by
      rcases hcusp a.1 a.2.1 a.2.2.isCusp with e | e
      · exact absurd (e ▸ a.2.2) hdL
      · exact e
    have hb : b.1 = ⟨iR, r⟩ := by
      rcases hcusp b.1 b.2.1 b.2.2.isCusp with e | e
      · exact absurd (e ▸ b.2.2) hdL
      · exact e
    exact Subtype.ext (ha.trans hb.symm)

end u7_helpers

/-- LEAF (ng:circle, sm-3:2053-2054 "A simple crossing-free component with exactly one left and one right
cusp has D = 1"): on a `PLFront`, the two x-monotone PL arcs between the cusps of a component never meet, so
one lies above the other and exactly one cusp is traversed upper arm → lower arm.  (Accepted for
realizations: `FrontRealizeStandard.IsStandardCircles.downCount_eq_c`; word-layer fallback FR-11.) -/
theorem PLFront.IsStandardCircles.downCount_eq_c_general (F : PLFront) (h : F.IsStandardCircles) :
    F.downCount = F.Γ.c := by
  unfold PLFront.downCount
  rw [PLFront.card_subtype_eq_sum_comp]
  rw [Finset.sum_congr rfl fun i _ => u7_card_down_eq_one F h i]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  exact Finset.card_fin _

/-! ### L-smooth (unit U8) — the smooth clauses of row 76 -/

/-! ### U8D infrastructure -/

namespace U8D

open Filter Topology Set Metric Classical
open scoped NNReal

noncomputable section


/-! #### Part A: real-line toolbox — integer separation, `Int.fract`, stability of `cycBetween` -/

/-- `x` is at distance at least `2ε` from every integer -/
def Sep (ε x : ℝ) : Prop := ∀ m : ℤ, 2 * ε ≤ |x + m|

theorem Sep.neg {ε x : ℝ} (h : Sep ε x) : Sep ε (-x) := by
  intro m
  have := h (-m)
  rw [← abs_neg] at this
  push_cast at this ⊢
  convert this using 2; ring

theorem Sep.symm_sub {ε a b : ℝ} (h : Sep ε (a - b)) : Sep ε (b - a) := by
  have := h.neg; rwa [neg_sub] at this

theorem Sep.pos {ε x : ℝ} (h : Sep ε x) (hε : 0 < ε) : x ≠ 0 := by
  intro hx; have := h 0; simp [hx] at this; linarith

theorem fract_eq_add_int (x : ℝ) : Int.fract x = x + ((-⌊x⌋ : ℤ) : ℝ) := by
  rw [← Int.self_sub_floor]; push_cast; ring

/-- moving by less than the separation does not cross an integer -/
theorem fract_add_of_sep {ε x h : ℝ} (hs : Sep ε x) (hh : |h| < 2 * ε) :
    Int.fract (x + h) = Int.fract x + h := by
  have h1 : 2 * ε ≤ Int.fract x := by
    have := hs (-⌊x⌋)
    rwa [← fract_eq_add_int, abs_of_nonneg (Int.fract_nonneg x)] at this
  have h2 : 2 * ε ≤ 1 - Int.fract x := by
    have := hs (-⌊x⌋ - 1)
    have e : x + ((-⌊x⌋ - 1 : ℤ) : ℝ) = Int.fract x - 1 := by
      rw [fract_eq_add_int]; push_cast; ring
    rw [e, abs_of_nonpos (by linarith [Int.fract_lt_one x])] at this; linarith
  rw [abs_lt] at hh
  have e : Int.fract x + h = (x + h) + ((-⌊x⌋ : ℤ) : ℝ) := by rw [fract_eq_add_int]; ring
  calc Int.fract (x + h) = Int.fract ((x + h) + ((-⌊x⌋ : ℤ) : ℝ)) := (Int.fract_add_intCast _ _).symm
    _ = Int.fract (Int.fract x + h) := by rw [e]
    _ = Int.fract x + h := Int.fract_eq_self.2 ⟨by linarith, by linarith⟩

/-- two points within `ε` of separated points (mod 1) have distinct `Int.fract` -/
theorem fract_ne_of_sep {ε a b a' b' : ℝ} (hs : Sep ε (a - b)) (ha : |a' - a| < ε) (hb : |b' - b| < ε) :
    Int.fract a' ≠ Int.fract b' := by
  intro h
  obtain ⟨m, hm⟩ := Int.fract_eq_fract.1 h
  have := hs (-m)
  have e : a - b + ((-m : ℤ) : ℝ) = -((a' - a) - (b' - b)) := by push_cast; linarith
  rw [e, abs_neg] at this
  have h2 : |(a' - a) - (b' - b)| < 2 * ε := by
    calc |(a' - a) - (b' - b)| ≤ |a' - a| + |b' - b| := abs_sub _ _
      _ < ε + ε := add_lt_add ha hb
      _ = 2 * ε := by ring
  linarith

theorem not_cycBetween_self_mid (a b : ℝ) : ¬ cycBetween a b b := by
  unfold cycBetween
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩) <;> linarith

theorem fract_sub_of_mem_Ico {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1)
    (hab : a ≠ b) : Int.fract (b - a) = if a < b then b - a else b - a + 1 := by
  split_ifs with h
  · exact Int.fract_eq_self.2 ⟨by linarith, by linarith [hb.2, ha.1]⟩
  · have hba : b < a := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hab)
    rw [← Int.fract_add_one]
    exact Int.fract_eq_self.2 ⟨by linarith [hb.1, ha.2], by linarith⟩

/-- the cyclic order of three distinct points of the fundamental period: from `a` in the positive
direction, `b` is met before `c` -/
theorem cycBetween_iff_fract {a b c : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1)
    (hc : c ∈ Ico (0 : ℝ) 1) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    cycBetween a b c ↔ Int.fract (b - a) < Int.fract (c - a) := by
  rw [fract_sub_of_mem_Ico ha hb hab, fract_sub_of_mem_Ico ha hc hac]
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hbc with h2 | h2 <;>
    rcases lt_or_gt_of_ne hac with h3 | h3 <;>
    (first | rw [ite_eq_left_of_eq_true _ _ (eq_true h1)] | rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 h1.le))]) <;>
    (first | rw [ite_eq_left_of_eq_true _ _ (eq_true h3)] | rw [ite_eq_right_of_eq_false _ _ (eq_false (not_lt.2 h3.le))]) <;>
    unfold cycBetween <;>
    constructor <;>
    first
    | (rintro (⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩) <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2])
    | (intro h; first
        | exact Or.inl ⟨by linarith, by linarith⟩
        | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
        | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
        | (exfalso; linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2]))

/-- `Int.fract (Int.fract x - Int.fract y) = Int.fract (x - y)` -/
theorem fract_fract_sub_fract (x y : ℝ) : Int.fract (Int.fract x - Int.fract y) = Int.fract (x - y) := by
  have e : Int.fract x - Int.fract y = (x - y) + ((⌊y⌋ - ⌊x⌋ : ℤ) : ℝ) := by
    rw [fract_eq_add_int x, fract_eq_add_int y]; push_cast; ring
  rw [e, Int.fract_add_intCast]

theorem fract_sub_fract_eq_add_int (x y : ℝ) : ∃ m : ℤ, Int.fract x - Int.fract y = (x - y) + m :=
  ⟨⌊y⌋ - ⌊x⌋, by rw [fract_eq_add_int x, fract_eq_add_int y]; push_cast; ring⟩

/-- **Stability of the cyclic order.**  Three parameters `a b c` of the fundamental period, pairwise
separated (mod 1) by more than `2ε` when distinct, and perturbations `a' b' c'` within `ε` (equal
parameters perturbed equally): the cyclic order of the `Int.fract` of the perturbations is that of
the originals. -/
theorem cycBetween_fract_of_sep {ε a b c a' b' c' : ℝ} (ha : a ∈ Ico (0 : ℝ) 1)
    (hb : b ∈ Ico (0 : ℝ) 1) (hc : c ∈ Ico (0 : ℝ) 1)
    (hab : a ≠ b → Sep ε (a - b)) (hbc : b ≠ c → Sep ε (b - c)) (hac : a ≠ c → Sep ε (a - c))
    (hab' : a = b → a' = b') (hbc' : b = c → b' = c') (hac' : a = c → a' = c')
    (ha' : |a' - a| < ε) (hb' : |b' - b| < ε) (hc' : |c' - c| < ε) :
    cycBetween a b c ↔ cycBetween (Int.fract a') (Int.fract b') (Int.fract c') := by
  by_cases e1 : a = b
  · subst e1; rw [hab' rfl]
    exact ⟨fun h => (not_cycBetween_self_left _ _ h).elim, fun h => (not_cycBetween_self_left _ _ h).elim⟩
  by_cases e2 : b = c
  · subst e2; rw [hbc' rfl]
    exact ⟨fun h => (not_cycBetween_self_mid _ _ h).elim, fun h => (not_cycBetween_self_mid _ _ h).elim⟩
  by_cases e3 : a = c
  · subst e3; rw [hac' rfl]
    exact ⟨fun h => (not_cycBetween_self_right _ _ h).elim, fun h => (not_cycBetween_self_right _ _ h).elim⟩
  have sab := hab e1
  have sbc := hbc e2
  have sac := hac e3
  have fa : Int.fract a' ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have fb : Int.fract b' ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have fc : Int.fract c' ∈ Ico (0 : ℝ) 1 := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  rw [cycBetween_iff_fract ha hb hc e1 e2 e3,
    cycBetween_iff_fract fa fb fc (fract_ne_of_sep sab ha' hb') (fract_ne_of_sep sbc hb' hc')
      (fract_ne_of_sep sac ha' hc'),
    fract_fract_sub_fract, fract_fract_sub_fract]
  -- the perturbed differences
  have hε : 0 < ε := lt_of_le_of_lt (abs_nonneg _) ha'
  have eb : b' - a' = (b - a) + ((b' - b) - (a' - a)) := by ring
  have ec : c' - a' = (c - a) + ((c' - c) - (a' - a)) := by ring
  have hhb : |(b' - b) - (a' - a)| < 2 * ε := by
    calc |(b' - b) - (a' - a)| ≤ |b' - b| + |a' - a| := abs_sub _ _
      _ < ε + ε := add_lt_add hb' ha'
      _ = 2 * ε := by ring
  have hhc : |(c' - c) - (a' - a)| < 2 * ε := by
    calc |(c' - c) - (a' - a)| ≤ |c' - c| + |a' - a| := abs_sub _ _
      _ < ε + ε := add_lt_add hc' ha'
      _ = 2 * ε := by ring
  rw [eb, ec, fract_add_of_sep sab.symm_sub hhb, fract_add_of_sep sac.symm_sub hhc]
  -- the two originals are separated by at least `2ε`
  obtain ⟨m, hm⟩ := fract_sub_fract_eq_add_int (b - a) (c - a)
  have hsep : 2 * ε ≤ |Int.fract (b - a) - Int.fract (c - a)| := by
    rw [hm]; have := sbc m; convert this using 2; ring
  have hdiff : |((b' - b) - (a' - a)) - ((c' - c) - (a' - a))| < 2 * ε := by
    calc |((b' - b) - (a' - a)) - ((c' - c) - (a' - a))| = |(b' - b) - (c' - c)| := by ring_nf
      _ ≤ |b' - b| + |c' - c| := abs_sub _ _
      _ < ε + ε := add_lt_add hb' hc'
      _ = 2 * ε := by ring
  rw [abs_lt] at hdiff
  constructor
  · intro h
    rw [abs_of_neg (by linarith)] at hsep
    linarith
  · intro h
    by_contra h'
    rw [abs_of_nonneg (by linarith)] at hsep
    linarith


/-- the parameters within `ε` (mod 1) of `a` -/
def near (ε a : ℝ) : Set ℝ := {u | ∃ m : ℤ, u + m ∈ Ioo (a - ε) (a + ε)}

theorem isOpen_near (ε a : ℝ) : IsOpen (near ε a) := by
  have : near ε a = ⋃ m : ℤ, Ioo (a - ε - m) (a + ε - m) := by
    ext u
    constructor
    · rintro ⟨m, h1, h2⟩
      exact mem_iUnion.2 ⟨m, by constructor <;> linarith⟩
    · intro h
      obtain ⟨m, h1, h2⟩ := mem_iUnion.1 h
      exact ⟨m, by constructor <;> linarith⟩
  rw [this]; exact isOpen_iUnion fun m => isOpen_Ioo

/-- as `ε → 0⁺`, `ε` separates a non-integer from the integers -/
theorem eventually_sep {x : ℝ} (hx : Int.fract x ≠ 0) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Sep ε x := by
  have h1 : 0 < Int.fract x := lt_of_le_of_ne (Int.fract_nonneg x) (Ne.symm hx)
  have h2 : Int.fract x < 1 := Int.fract_lt_one x
  have hpos : (0 : ℝ) < min (Int.fract x) (1 - Int.fract x) / 2 := by
    apply half_pos; exact lt_min h1 (by linarith)
  refine Filter.eventually_of_mem (Ioo_mem_nhdsGT hpos) ?_
  intro ε hε m
  have hε2 : 2 * ε < min (Int.fract x) (1 - Int.fract x) := by linarith [hε.2]
  have hmin1 := min_le_left (Int.fract x) (1 - Int.fract x)
  have hmin2 := min_le_right (Int.fract x) (1 - Int.fract x)
  have e : x + m = Int.fract x + ((⌊x⌋ + m : ℤ) : ℝ) := by rw [fract_eq_add_int]; push_cast; ring
  rw [e]
  rcases le_or_gt 0 (⌊x⌋ + m) with hk | hk
  · have : (0 : ℝ) ≤ ((⌊x⌋ + m : ℤ) : ℝ) := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)]; linarith
  · have : ((⌊x⌋ + m : ℤ) : ℝ) ≤ -1 := by
      have : ⌊x⌋ + m ≤ -1 := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]; linarith

theorem fract_sub_ne_zero {a b : ℝ} (ha : a ∈ Ico (0 : ℝ) 1) (hb : b ∈ Ico (0 : ℝ) 1) (hne : a ≠ b) :
    Int.fract (a - b) ≠ 0 := by
  intro h
  obtain ⟨-, -, z, hz⟩ := Int.fract_eq_iff.1 h
  have h1 : (z : ℝ) < 1 := by linarith [ha.2, hb.1]
  have h2 : (-1 : ℝ) < z := by linarith [ha.1, hb.2]
  have h3 : z < 1 := by exact_mod_cast h1
  have h4 : -1 < z := by exact_mod_cast h2
  have hz0 : z = 0 := by omega
  subst hz0
  simp at hz
  exact hne (by linarith)


/-! #### Part C: persistence of a nondegenerate zero, uniformly in a parameter -/

/-- **Persistence of a nondegenerate zero.**  `Φ x` has a zero `y₀` at `x = x₀` with invertible
derivative `L`; `Φ` and its derivative are jointly continuous.  Then for every small radius `ε`,
and all `x` near `x₀`, `Φ x` has exactly one zero in the open ball of radius `ε` about `y₀`.
No implicit-function theorem in the parameter is used (the parameter space is arbitrary): the
mean-value inequality makes `Φ x` a linear approximation of `L` on the ball, which is injective
there and onto a ball about `Φ x y₀` (Mathlib's `ApproximatesLinearOn`). -/
theorem persist {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [Nontrivial E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {X : Type*} [TopologicalSpace X]
    (Φ : X → E → G) (DΦ : X → E → E →L[ℝ] G)
    (hderiv : ∀ x y, HasFDerivAt (Φ x) (DΦ x y) y)
    (hΦ : Continuous (fun p : X × E => Φ p.1 p.2))
    (hDΦ : Continuous (fun p : X × E => DΦ p.1 p.2))
    (x₀ : X) (y₀ : E) (h0 : Φ x₀ y₀ = 0) (L : E ≃L[ℝ] G) (hL : DΦ x₀ y₀ = L) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ᶠ x in 𝓝 x₀, ∃! y, y ∈ ball y₀ ε ∧ Φ x y = 0 := by
  set N : ℝ≥0 := ‖(L.symm : G →L[ℝ] E)‖₊ with hNdef
  have hLs : (L.symm : G →L[ℝ] E) ≠ 0 := by
    intro h
    obtain ⟨y, hy⟩ := exists_ne (0 : E)
    apply hy
    have h1 := L.symm_apply_apply y
    rw [show L.symm (L y) = (L.symm : G →L[ℝ] E) (L y) from rfl, h] at h1
    simpa using h1.symm
  have hN : 0 < N := nnnorm_pos.2 hLs
  have hNi : 0 < N⁻¹ := inv_pos.2 hN
  set c : ℝ≥0 := N⁻¹ / 2 with hcdef
  have hc : c < N⁻¹ := by
    rw [hcdef]; exact NNReal.half_lt_self hNi.ne'
  have hcpos : (0 : ℝ) < (N⁻¹ : ℝ≥0) - c := by
    rw [sub_pos]; exact_mod_cast hc
  -- the derivative is within `c` of `L` on a product neighbourhood
  have h1 : ∀ᶠ p : X × E in 𝓝 (x₀, y₀), ‖DΦ p.1 p.2 - (L : E →L[ℝ] G)‖ < c := by
    have hcont : Continuous (fun p : X × E => ‖DΦ p.1 p.2 - (L : E →L[ℝ] G)‖) :=
      (hDΦ.sub continuous_const).norm
    have := hcont.continuousAt (x := (x₀, y₀))
    simp only [ContinuousAt, hL, sub_self, norm_zero] at this
    exact this.eventually_lt_const (by exact_mod_cast (half_pos hNi : 0 < N⁻¹ / 2))
  rw [nhds_prod_eq, Filter.eventually_prod_iff] at h1
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := h1
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.eventually_nhds_iff.mp hpb
  refine ⟨ε₀ / 2, half_pos hε₀, fun ε hε hεε₀ => ?_⟩
  have hbound : ∀ x, pa x → ∀ y ∈ closedBall y₀ ε, ‖DΦ x y - (L : E →L[ℝ] G)‖ ≤ c := by
    intro x hx y hy
    have hy' : dist y y₀ < ε₀ := by
      rw [mem_closedBall] at hy; linarith
    exact (hab hx (hball hy')).le
  have happrox : ∀ x, pa x → ∀ r, 0 < r → r ≤ ε →
      ApproximatesLinearOn (Φ x) (L : E →L[ℝ] G) (closedBall y₀ r) c := by
    intro x hx r hr hrε y hy z hz
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun w _ => (hderiv x w).hasFDerivWithinAt)
      (fun w hw => hbound x hx w (closedBall_subset_closedBall hrε hw))
      (convex_closedBall y₀ r) hz hy
  -- existence: `Φ x y₀` is small for `x` near `x₀`
  have h2 : ∀ᶠ x in 𝓝 x₀, ‖Φ x y₀‖ < ((N⁻¹ : ℝ≥0) - c) * (ε / 2) := by
    have hcont : Continuous (fun x : X => ‖Φ x y₀‖) :=
      (hΦ.comp (continuous_id.prodMk continuous_const)).norm
    have := hcont.continuousAt (x := x₀)
    simp only [ContinuousAt, h0, norm_zero] at this
    exact this.eventually_lt_const (by positivity)
  filter_upwards [hpa, h2] with x hx hx2
  have hinj : InjOn (Φ x) (closedBall y₀ ε) :=
    (happrox x hx ε hε le_rfl).injOn (Or.inr hc)
  have hsurj := (happrox x hx (ε / 2) (half_pos hε) (half_le_self hε.le)).surjOn_closedBall_of_nonlinearRightInverse
    L.toNonlinearRightInverse (half_pos hε).le subset_rfl
  have hmem : (0 : G) ∈ closedBall (Φ x y₀) (((L.toNonlinearRightInverse.nnnorm : ℝ)⁻¹ - c) * (ε / 2)) := by
    rw [mem_closedBall, dist_zero_left]
    exact hx2.le
  obtain ⟨y, hy, hΦy⟩ := hsurj hmem
  refine ⟨y, ⟨?_, hΦy⟩, ?_⟩
  · rw [mem_ball]; rw [mem_closedBall] at hy; linarith
  · rintro z ⟨hz, hΦz⟩
    exact hinj (ball_subset_closedBall hz) (ball_subset_closedBall (by rw [mem_ball]; rw [mem_closedBall] at hy; linarith)) (hΦz.trans hΦy.symm)

/-! #### Part B: the jointly smooth family and its `u`-derivatives -/

/-- the parameter interval of a deformation, as a (preconnected) space -/
abbrev I : Type := Set.Icc (0 : ℝ) 1

instance : PreconnectedSpace I := Subtype.preconnectedSpace isPreconnected_Icc

/-- the region of joint smoothness -/
def dom : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ

theorem uniqueDiffOn_dom : UniqueDiffOn ℝ dom := UniqueDiffOn.prod (uniqueDiffOn_Icc zero_lt_one) uniqueDiffOn_univ

theorem mem_dom {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ) : (t, u) ∈ dom := ⟨ht, trivial⟩

variable {F F' : SmoothFront} (d : F.NonsingularDeformation F')

/-- the `i`-th component of `path t`, indexed by `Fin F.c` -/
def comp (t : ℝ) (i : Fin F.c) : SmoothLoop := (d.path t).comp (Fin.cast (d.c_eq t).symm i)

/-- the family, as a function of `(t, u)` -/
def Γ (i : Fin F.c) : ℝ × ℝ → Plane := fun p => (comp d p.1 i).γ p.2

theorem contDiffOn_Γ (i : Fin F.c) : ContDiffOn ℝ ∞ (Γ d i) dom := d.smooth i

/-- the `k`-th partial derivative in `u`, taken within `dom` -/
def pd (i : Fin F.c) : ℕ → ℝ × ℝ → Plane
  | 0 => Γ d i
  | k + 1 => fun p => fderivWithin ℝ (pd i k) dom p ((0 : ℝ), (1 : ℝ))

theorem contDiffOn_pd (i : Fin F.c) (k : ℕ) : ContDiffOn ℝ ∞ (pd d i k) dom := by
  induction k with
  | zero => exact contDiffOn_Γ d i
  | succ k ih =>
    show ContDiffOn ℝ ∞ (fun p => fderivWithin ℝ (pd d i k) dom p ((0 : ℝ), (1 : ℝ))) dom
    exact (((contDiffOn_infty_iff_fderivWithin uniqueDiffOn_dom).1 ih).2).clm_apply contDiffOn_const

theorem continuousOn_pd (i : Fin F.c) (k : ℕ) : ContinuousOn (pd d i k) dom :=
  (contDiffOn_pd d i k).continuousOn

/-- on the smooth region the partial derivatives are the iterated derivatives of the components -/
theorem pd_eq (i : Fin F.c) (k : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) (u : ℝ) :
    pd d i k (t, u) = iteratedDeriv k (comp d t i).γ u := by
  induction k generalizing u with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hfun : iteratedDeriv k (comp d t i).γ = fun u => pd d i k (t, u) :=
      funext fun u => (ih u).symm
    rw [hfun]
    show fderivWithin ℝ (pd d i k) dom (t, u) ((0 : ℝ), (1 : ℝ)) = deriv (fun u => pd d i k (t, u)) u
    have hd : HasFDerivWithinAt (pd d i k) (fderivWithin ℝ (pd d i k) dom (t, u)) dom (t, u) :=
      ((contDiffOn_pd d i k).differentiableOn (by decide) (t, u) (mem_dom ht u)).hasFDerivWithinAt
    have hl : HasDerivAt (fun u : ℝ => ((t, u) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) u :=
      (hasDerivAt_const u t).prodMk (hasDerivAt_id u)
    have := hd.comp_hasDerivWithinAt u (hl.hasDerivWithinAt (s := Set.univ)) (fun u _ => mem_dom ht u)
    rw [hasDerivWithinAt_univ] at this
    exact this.deriv.symm

/-- the partial derivatives as continuous functions on `I × ℝ` -/
def pdI (i : Fin F.c) (k : ℕ) : I × ℝ → Plane := fun p => pd d i k (p.1.1, p.2)

theorem continuous_pdI (i : Fin F.c) (k : ℕ) : Continuous (pdI d i k) :=
  (continuousOn_pd d i k).comp_continuous (by fun_prop) (fun p => mem_dom p.1.2 p.2)

theorem pdI_eq (i : Fin F.c) (k : ℕ) (t : I) (u : ℝ) :
    pdI d i k (t, u) = iteratedDeriv k (comp d t.1 i).γ u := pd_eq d i k t.2 u

/-- the components of `path t` are the reindexed components -/
theorem path_comp_eq (t : ℝ) (j : Fin (d.path t).c) :
    (d.path t).comp j = comp d t (Fin.cast (d.c_eq t) j) := by
  rfl

/-! The front notions of `path t` in terms of the family. -/

theorem eval_eq (t : I) (j : Fin (d.path t.1).c) (u : ℝ) :
    (d.path t.1).eval (j, u) = pdI d (Fin.cast (d.c_eq t.1) j) 0 (t, u) := by
  rw [pdI_eq, iteratedDeriv_zero, SmoothFront.eval_def, path_comp_eq]

theorem vel_eq (t : I) (j : Fin (d.path t.1).c) (u : ℝ) :
    (d.path t.1).vel (j, u) = pdI d (Fin.cast (d.c_eq t.1) j) 1 (t, u) := by
  rw [pdI_eq, iteratedDeriv_one, SmoothFront.vel_def, path_comp_eq]

theorem acc_eq (t : I) (j : Fin (d.path t.1).c) (u : ℝ) :
    (d.path t.1).acc (j, u) = pdI d (Fin.cast (d.c_eq t.1) j) 2 (t, u) := by
  rw [pdI_eq, SmoothFront.acc_def, path_comp_eq]

theorem jerk_eq (t : I) (j : Fin (d.path t.1).c) (u : ℝ) :
    (d.path t.1).jerk (j, u) = pdI d (Fin.cast (d.c_eq t.1) j) 3 (t, u) := by
  rw [pdI_eq, SmoothFront.jerk_def, path_comp_eq]

/-- derivative of the `k`-th partial in `u` for fixed `t` -/
theorem hasDerivAt_pdI (i : Fin F.c) (k : ℕ) (t : I) (u : ℝ) :
    HasDerivAt (fun u => pdI d i k (t, u)) (pdI d i (k + 1) (t, u)) u := by
  have hf : (fun u => pdI d i k (t, u)) = iteratedDeriv k (comp d t.1 i).γ :=
    funext fun u => pdI_eq d i k t u
  rw [hf, pdI_eq, iteratedDeriv_succ]
  exact (((comp d t.1 i).contDiff_iteratedDeriv k).differentiable (by decide) u).hasDerivAt

/-- reindexing the components between two members of the family -/
def ρ (t t' : ℝ) : Fin (d.path t).c ≃ Fin (d.path t').c :=
  finCongr (by rw [d.c_eq, d.c_eq])

@[simp] theorem cast_ρ (t t' : ℝ) (j : Fin (d.path t).c) :
    Fin.cast (d.c_eq t') (ρ d t t' j) = Fin.cast (d.c_eq t) j := by
  ext; simp [ρ]

@[simp] theorem ρ_symm_apply_cast (t t' : ℝ) (j : Fin (d.path t).c) :
    (ρ d t t').symm (ρ d t t' j) = j := Equiv.symm_apply_apply _ _

theorem ρ_val (t t' : ℝ) (j : Fin (d.path t).c) : ((ρ d t t' j : Fin _) : ℕ) = j := rfl
/-! #### Part D: cusps — local hypotheses, counting, and the analysis producing them -/

/-- a cusp is a zero of the `x`-velocity alone (`no_vertical`) -/
theorem isCusp_iff_fst (A : SmoothFront) (p : Param A.c) : A.IsCusp p ↔ (A.vel p).1 = 0 := by
  constructor
  · intro h; rw [show A.vel p = 0 from h]; rfl
  · intro h; by_contra hne; exact A.no_vertical p.1 p.2 hne h

/-- **Local cusp hypotheses** between a front `A` and a nearby front `B` (circles reindexed by `ρ`):
distinct cusps of `A` on one circle are separated by more than `2ε` (mod 1); each cusp of `A` has
exactly one cusp of `B` within `ε`, of the same direction; every cusp of `B` lies within `ε` (mod 1)
of a cusp of `A`. -/
structure CuspHyp (A B : SmoothFront) (ρ : Fin A.c ≃ Fin B.c) (ε : ℝ) : Prop where
  pos : 0 < ε
  sep : ∀ p ∈ A.cuspSet, ∀ q ∈ A.cuspSet, p.1 = q.1 → p ≠ q → Sep ε (p.2 - q.2)
  exu : ∀ p ∈ A.cuspSet, ∃! u, u ∈ Ioo (p.2 - ε) (p.2 + ε) ∧ B.IsCusp (ρ p.1, u)
  down : ∀ p ∈ A.cuspSet, ∀ u ∈ Ioo (p.2 - ε) (p.2 + ε), B.IsCusp (ρ p.1, u) →
    (B.IsDownCusp (ρ p.1, u) ↔ A.IsDownCusp p)
  nonew : ∀ q ∈ B.cuspSet, ∃ p ∈ A.cuspSet, ∃ m : ℤ, q.1 = ρ p.1 ∧ q.2 + m ∈ Ioo (p.2 - ε) (p.2 + ε)

namespace CuspHyp

variable {A B : SmoothFront} {ρ : Fin A.c ≃ Fin B.c} {ε : ℝ} (h : CuspHyp A B ρ ε)
include h

/-- the cusp of `B` near the cusp `p` of `A` -/
def φ (p : Param A.c) (hp : p ∈ A.cuspSet) : ℝ := Classical.choose (h.exu p hp).exists

theorem φ_mem (p : Param A.c) (hp : p ∈ A.cuspSet) : h.φ p hp ∈ Ioo (p.2 - ε) (p.2 + ε) :=
  (Classical.choose_spec (h.exu p hp).exists).1

theorem φ_cusp (p : Param A.c) (hp : p ∈ A.cuspSet) : B.IsCusp (ρ p.1, h.φ p hp) :=
  (Classical.choose_spec (h.exu p hp).exists).2

theorem φ_unique (p : Param A.c) (hp : p ∈ A.cuspSet) {u : ℝ} (hu : u ∈ Ioo (p.2 - ε) (p.2 + ε))
    (hc : B.IsCusp (ρ p.1, u)) : u = h.φ p hp :=
  (h.exu p hp).unique ⟨hu, hc⟩ ⟨h.φ_mem p hp, h.φ_cusp p hp⟩

theorem φ_abs (p : Param A.c) (hp : p ∈ A.cuspSet) : |h.φ p hp - p.2| < ε := by
  have := h.φ_mem p hp
  rw [abs_sub_lt_iff]; constructor <;> linarith [this.1, this.2]

/-- the image cusp, in the fundamental period -/
def f (p : Param A.c) (hp : p ∈ A.cuspSet) : Param B.c := (ρ p.1, Int.fract (h.φ p hp))

theorem sameParam_f (p : Param A.c) (hp : p ∈ A.cuspSet) :
    SameParam (ρ p.1, h.φ p hp) (h.f p hp) :=
  ⟨rfl, -⌊h.φ p hp⌋, fract_eq_add_int _⟩

theorem f_mem (p : Param A.c) (hp : p ∈ A.cuspSet) : h.f p hp ∈ B.cuspSet :=
  B.mem_cuspSet.2 ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩,
    (B.isCusp_iff_of_sameParam (h.sameParam_f p hp)).2 (h.φ_cusp p hp)⟩

theorem f_injective (p : Param A.c) (hp : p ∈ A.cuspSet) (q : Param A.c) (hq : q ∈ A.cuspSet)
    (heq : h.f p hp = h.f q hq) : p = q := by
  have h1 : ρ p.1 = ρ q.1 := congrArg Prod.fst heq
  have h1' : p.1 = q.1 := ρ.injective h1
  have h2 : Int.fract (h.φ p hp) = Int.fract (h.φ q hq) := congrArg Prod.snd heq
  by_contra hne
  exact fract_ne_of_sep (h.sep p hp q hq h1' hne) (h.φ_abs p hp) (h.φ_abs q hq) h2

theorem f_surjective (q : Param B.c) (hq : q ∈ B.cuspSet) :
    ∃ p, ∃ hp : p ∈ A.cuspSet, h.f p hp = q := by
  obtain ⟨p, hp, m, h1, hm⟩ := h.nonew q hq
  refine ⟨p, hp, ?_⟩
  have hqc : B.IsCusp q := B.isCusp_of_mem_cuspSet hq
  have hsp : SameParam q (ρ p.1, q.2 + m) := ⟨h1, m, rfl⟩
  have hc : B.IsCusp (ρ p.1, q.2 + m) := (B.isCusp_iff_of_sameParam hsp).2 hqc
  have := h.φ_unique p hp hm hc
  unfold f
  rw [← this, Int.fract_add_intCast, Int.fract_eq_self.2 (B.mem_cuspSet.1 hq).1]
  exact Prod.ext h1.symm rfl

theorem f_down (p : Param A.c) (hp : p ∈ A.cuspSet) : B.IsDownCusp (h.f p hp) ↔ A.IsDownCusp p := by
  rw [B.isDownCusp_iff_of_sameParam (h.sameParam_f p hp)]
  exact h.down p hp _ (h.φ_mem p hp) (h.φ_cusp p hp)

/-- the down-cusp counts agree -/
theorem downCount_eq : A.downCount = B.downCount := by
  unfold SmoothFront.downCount
  refine Finset.card_bij (fun p hp => h.f p (Finset.mem_filter.1 hp).1) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨h.f_mem p hp.1, (h.f_down p hp.1).2 hp.2⟩
  · intro p hp q hq heq
    exact h.f_injective p _ q _ heq
  · intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨p, hp, rfl⟩ := h.f_surjective q hq.1
    exact ⟨p, Finset.mem_filter.2 ⟨hp, (h.f_down p hp).1 hq.2⟩, rfl⟩

end CuspHyp

/-! ##### The analysis for cusps -/

section CuspAnalysis

include d

/-- the `x`-velocity of the family on component `i` -/
def gx (i : Fin F.c) : I × ℝ → ℝ := fun z => (pdI d i 1 z).1
/-- its `u`-derivative, the `x`-acceleration -/
def gxx (i : Fin F.c) : I × ℝ → ℝ := fun z => (pdI d i 2 z).1
/-- the cusp discriminant `x''·det(γ'', γ''')` of the family -/
def disc (i : Fin F.c) : I × ℝ → ℝ :=
  fun z => (pdI d i 2 z).1 * det (pdI d i 2 z) (pdI d i 3 z)

theorem continuous_gx (i : Fin F.c) : Continuous (gx d i) := (continuous_pdI d i 1).fst
theorem continuous_gxx (i : Fin F.c) : Continuous (gxx d i) := (continuous_pdI d i 2).fst
theorem continuous_disc (i : Fin F.c) : Continuous (disc d i) := by
  have h2 := continuous_pdI d i 2
  have h3 := continuous_pdI d i 3
  unfold disc det
  fun_prop

theorem isCusp_iff_gx (t : I) (p : Param (d.path t.1).c) :
    (d.path t.1).IsCusp p ↔ gx d (Fin.cast (d.c_eq t.1) p.1) (t, p.2) = 0 := by
  rw [isCusp_iff_fst, vel_eq]; rfl

theorem cuspDisc_eq (t : I) (p : Param (d.path t.1).c) :
    (d.path t.1).cuspDisc p = disc d (Fin.cast (d.c_eq t.1) p.1) (t, p.2) := by
  unfold SmoothFront.cuspDisc disc; rw [acc_eq, jerk_eq]

theorem hasDerivAt_gx (i : Fin F.c) (t : I) (u : ℝ) :
    HasDerivAt (fun u => gx d i (t, u)) (gxx d i (t, u)) u :=
  (hasDerivAt_pdI d i 1 t u).fst

variable (t₀ : I)

/-- persistence of a cusp along the family (1-D case of `persist`) -/
theorem cusp_persist (i : Fin F.c) (u₀ : ℝ) (h0 : gx d i (t₀, u₀) = 0) (h2 : gxx d i (t₀, u₀) ≠ 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ᶠ t in 𝓝 t₀, ∃! u, u ∈ Ioo (u₀ - ε) (u₀ + ε) ∧ gx d i (t, u) = 0 := by
  have := persist (X := I) (E := ℝ) (G := ℝ) (fun t u => gx d i (t, u))
    (fun t u => (1 : ℝ →L[ℝ] ℝ).smulRight (gxx d i (t, u)))
    (fun t u => (hasDerivAt_gx d i t u).hasFDerivAt)
    (continuous_gx d i)
    ((ContinuousLinearMap.smulRightL ℝ ℝ ℝ (1 : ℝ →L[ℝ] ℝ)).continuous.comp (continuous_gxx d i))
    t₀ u₀ h0 (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 _ h2)) rfl
  simpa only [Real.ball_eq_Ioo] using this

theorem cusp_exu (p : Param (d.path t₀.1).c) (hp : p ∈ (d.path t₀.1).cuspSet) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ᶠ t in 𝓝 t₀, ∃! u, u ∈ Ioo (p.2 - ε) (p.2 + ε) ∧
      (d.path t.1).IsCusp (ρ d t₀.1 t.1 p.1, u) := by
  have hc : (d.path t₀.1).IsCusp p := (d.path t₀.1).isCusp_of_mem_cuspSet hp
  have h0 : gx d (Fin.cast (d.c_eq t₀.1) p.1) (t₀, p.2) = 0 := (isCusp_iff_gx d t₀ p).1 hc
  have h2 : gxx d (Fin.cast (d.c_eq t₀.1) p.1) (t₀, p.2) ≠ 0 := by
    have := (d.path t₀.1).acc_fst_ne_zero_of_isCusp hc
    rwa [acc_eq] at this
  obtain ⟨ε₀, hε₀, H⟩ := cusp_persist d t₀ _ p.2 h0 h2
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => (H ε hε hεε₀).mono fun t ht => ?_⟩
  simpa only [isCusp_iff_gx, cast_ρ] using ht

theorem cusp_down (p : Param (d.path t₀.1).c) (hp : p ∈ (d.path t₀.1).cuspSet) :
    ∃ ε₁ > 0, ∀ᶠ t in 𝓝 t₀, ∀ u ∈ Ioo (p.2 - ε₁) (p.2 + ε₁),
      (d.path t.1).IsCusp (ρ d t₀.1 t.1 p.1, u) →
      ((d.path t.1).IsDownCusp (ρ d t₀.1 t.1 p.1, u) ↔ (d.path t₀.1).IsDownCusp p) := by
  set i := Fin.cast (d.c_eq t₀.1) p.1 with hi
  have hc := (d.path t₀.1).isCusp_of_mem_cuspSet hp
  have hne : disc d i (t₀, p.2) ≠ 0 := by
    have := (d.path t₀.1).cuspDisc_ne_zero_of_isCusp hc
    rwa [cuspDisc_eq] at this
  have hev : ∀ᶠ z : I × ℝ in 𝓝 (t₀, p.2), (disc d i z < 0 ↔ disc d i (t₀, p.2) < 0) := by
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · exact (Filter.Tendsto.eventually_lt_const hneg (continuous_disc d i).continuousAt).mono
        fun z hz => ⟨fun _ => hneg, fun _ => hz⟩
    · exact (Filter.Tendsto.eventually_const_lt hpos (continuous_disc d i).continuousAt).mono
        fun z hz => ⟨fun h => absurd hz (not_lt.2 h.le), fun h => absurd hpos (not_lt.2 h.le)⟩
  rw [nhds_prod_eq, eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := hev
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp hpb
  refine ⟨ε₁, hε₁, hpa.mono fun t ht u hu hcu => ?_⟩
  have hu' : dist u p.2 < ε₁ := by
    rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hu.1, hu.2]
  have key := hab ht (hball hu')
  unfold SmoothFront.IsDownCusp
  rw [cuspDisc_eq, cuspDisc_eq, cast_ρ]
  exact ⟨fun h => ⟨hc, key.1 h.2⟩, fun h => ⟨hcu, key.2 h.2⟩⟩

/-- no new cusps: eventually every cusp of `path t` is within `ε` (mod 1) of a cusp of `path t₀` -/
theorem cusp_nonew (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (t : I) in 𝓝 t₀, ∀ q : Param (d.path t.1).c, q ∈ (d.path t.1).cuspSet →
      ∃ p ∈ (d.path t₀.1).cuspSet, ∃ m : ℤ,
        q.1 = ρ d t₀.1 t.1 p.1 ∧ q.2 + m ∈ Ioo (p.2 - ε) (p.2 + ε) := by
  have key : ∀ i : Fin F.c, ∀ᶠ t in 𝓝 t₀, ∀ u ∈ Icc (0 : ℝ) 1, gx d i (t, u) = 0 →
      ∃ p ∈ (d.path t₀.1).cuspSet, Fin.cast (d.c_eq t₀.1) p.1 = i ∧ u ∈ near ε p.2 := by
    intro i
    set T := (d.path t₀.1).cuspSet.filter (fun p => Fin.cast (d.c_eq t₀.1) p.1 = i) with hT
    set K : Set ℝ := Icc 0 1 \ ⋃ p ∈ T, near ε p.2 with hK
    have hKc : IsCompact K :=
      isCompact_Icc.diff (isOpen_iUnion fun p => isOpen_iUnion fun _ => isOpen_near ε p.2)
    have hK0 : ∀ u ∈ K, gx d i (t₀, u) ≠ 0 := by
      rintro u ⟨hu1, hu2⟩ h0
      apply hu2
      set j : Fin (d.path t₀.1).c := Fin.cast (d.c_eq t₀.1).symm i with hj
      have hc : (d.path t₀.1).IsCusp (j, u) := (isCusp_iff_gx d t₀ (j, u)).2 h0
      have hmem := (d.path t₀.1).rep_mem_cuspSet hc
      refine mem_iUnion₂.2 ⟨SameParam.rep (j, u), Finset.mem_filter.2 ⟨hmem, Fin.ext rfl⟩, -⌊u⌋, ?_⟩
      show u + ((-⌊u⌋ : ℤ) : ℝ) ∈ Ioo (Int.fract u - ε) (Int.fract u + ε)
      rw [← fract_eq_add_int]
      exact ⟨by linarith, by linarith⟩
    have hev := hKc.eventually_forall_of_forall_eventually (x₀ := t₀) (P := fun t u => gx d i (t, u) ≠ 0)
      (fun u hu => (continuous_gx d i).continuousAt.eventually_ne (hK0 u hu))
    refine hev.mono fun t ht u hu h0 => ?_
    have hnK : u ∉ K := fun hK' => ht u hK' h0
    have hu' : u ∈ ⋃ p ∈ T, near ε p.2 := by
      by_contra hc; exact hnK ⟨hu, hc⟩
    obtain ⟨p, hp, hnear⟩ := mem_iUnion₂.1 hu'
    rw [Finset.mem_filter] at hp
    exact ⟨p, hp.1, hp.2, hnear⟩
  refine (Filter.eventually_all.2 key).mono fun t ht q hq => ?_
  have hqc := (d.path t.1).isCusp_of_mem_cuspSet hq
  have hq2 := ((d.path t.1).mem_cuspSet.1 hq).1
  have h0 : gx d (Fin.cast (d.c_eq t.1) q.1) (t, q.2) = 0 := (isCusp_iff_gx d t q).1 hqc
  obtain ⟨p, hp, hcast, m, hm⟩ := ht _ q.2 (Ico_subset_Icc_self hq2) h0
  refine ⟨p, hp, m, ?_, hm⟩
  apply Fin.ext
  have := congrArg Fin.val hcast
  simpa [ρ] using this.symm

/-- **the local cusp hypotheses hold near every parameter** -/
theorem eventually_cuspHyp :
    ∃ ε, ∀ᶠ t in 𝓝 t₀, CuspHyp (d.path t₀.1) (d.path t.1) (ρ d t₀.1 t.1) ε := by
  set A := d.path t₀.1 with hA
  have E1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  have E2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ A.cuspSet, ∀ q ∈ A.cuspSet, p.1 = q.1 → p ≠ q →
      Sep ε (p.2 - q.2) := by
    refine (Finset.eventually_all A.cuspSet).2 fun p hp => (Finset.eventually_all A.cuspSet).2 fun q hq => ?_
    by_cases hc : p.1 = q.1 ∧ p ≠ q
    · have hne : p.2 ≠ q.2 := fun h => hc.2 (Prod.ext hc.1 h)
      exact (eventually_sep (fract_sub_ne_zero (A.mem_cuspSet.1 hp).1 (A.mem_cuspSet.1 hq).1 hne)).mono
        fun ε h _ _ => h
    · exact Filter.Eventually.of_forall fun ε h1 h2 => absurd ⟨h1, h2⟩ hc
  have E3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ A.cuspSet, ∀ᶠ t in 𝓝 t₀, ∃! u, u ∈ Ioo (p.2 - ε) (p.2 + ε) ∧
      (d.path t.1).IsCusp (ρ d t₀.1 t.1 p.1, u) := by
    refine (Finset.eventually_all A.cuspSet).2 fun p hp => ?_
    obtain ⟨ε₀, hε₀, H⟩ := cusp_exu d t₀ p hp
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hε₀) fun ε hε => H ε hε.1 hε.2.le
  have E4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ A.cuspSet, ∀ᶠ t in 𝓝 t₀, ∀ u ∈ Ioo (p.2 - ε) (p.2 + ε),
      (d.path t.1).IsCusp (ρ d t₀.1 t.1 p.1, u) →
      ((d.path t.1).IsDownCusp (ρ d t₀.1 t.1 p.1, u) ↔ A.IsDownCusp p) := by
    refine (Finset.eventually_all A.cuspSet).2 fun p hp => ?_
    obtain ⟨ε₁, hε₁, H⟩ := cusp_down d t₀ p hp
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hε₁) fun ε hε => H.mono fun t ht u hu =>
      ht u (Ioo_subset_Ioo (by linarith [hε.2]) (by linarith [hε.2]) hu)
  obtain ⟨ε, hε1, hε2, hε3, hε4⟩ := (E1.and (E2.and (E3.and E4))).exists
  refine ⟨ε, ?_⟩
  have T3 := (Finset.eventually_all A.cuspSet).2 hε3
  have T4 := (Finset.eventually_all A.cuspSet).2 hε4
  have T5 := cusp_nonew d t₀ ε hε1
  filter_upwards [T3, T4, T5] with t h3 h4 h5
  exact ⟨hε1, hε2, h3, h4, h5⟩

/-- **`D` is invariant** under a nonsingular deformation. -/
theorem downCount_eq_of_deformation : F.downCount = F'.downCount := by
  have hlc : IsLocallyConstant (fun t : I => (d.path t.1).downCount) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨ε, hε⟩ := eventually_cuspHyp d t₀
    exact hε.mono fun t ht => ht.downCount_eq.symm
  have h := hlc.apply_eq_of_preconnectedSpace (⟨0, by norm_num⟩ : I) (⟨1, by norm_num⟩ : I)
  have h0 : d.path (⟨0, by norm_num⟩ : I).1 = F := d.start
  have h1 : d.path (⟨1, by norm_num⟩ : I).1 = F' := d.stop
  simp only [h0, h1] at h
  exact h

end CuspAnalysis
/-! #### Part G: the record of a front, its transport, and the local double-point hypotheses -/

/-- **The named record of a front transported to another front**: a bijection of circles and of
crossing occurrences preserving circles, the cyclic order of the occurrences along each circle,
meeting (the pairing), the over rule (smaller slope) and the over-first signs. -/
structure FrontRecEquiv (A B : SmoothFront) where
  e : Fin A.c ≃ Fin B.c
  Φ : A.Occ ≃ B.Occ
  comp_eq : ∀ p : A.Occ, (Φ p).1.1 = e p.1.1
  between_iff : ∀ p q r : A.Occ, p.1.1 = q.1.1 → q.1.1 = r.1.1 →
    (cycBetween p.1.2 q.1.2 r.1.2 ↔ cycBetween (Φ p).1.2 (Φ q).1.2 (Φ r).1.2)
  meet_iff : ∀ p q : A.Occ, p ≠ q → (A.eval p = A.eval q ↔ B.eval (Φ p) = B.eval (Φ q))
  slope_iff : ∀ p q : A.Occ, p ≠ q → A.eval p = A.eval q →
    (A.slope p < A.slope q ↔ B.slope (Φ p) < B.slope (Φ q))
  sign_eq : ∀ p q : A.Occ, p ≠ q → A.eval p = A.eval q → A.crossSign p q = B.crossSign (Φ p) (Φ q)

theorem fst_mem_occSet_of_mem_crossingPairs {A : SmoothFront} {a : Param A.c × Param A.c} (ha : a ∈ A.crossingPairs) :
    a.1 ∈ A.occSet :=
  A.fst_mem_occSet_of_mem_doubleSet (A.crossingPairs_subset_doubleSet ha)

theorem snd_mem_occSet_of_mem_crossingPairs {A : SmoothFront} {a : Param A.c × Param A.c} (ha : a ∈ A.crossingPairs) :
    a.2 ∈ A.occSet :=
  A.snd_mem_occSet_of_mem_doubleSet (A.crossingPairs_subset_doubleSet ha)

namespace FrontRecEquiv

variable {A B : SmoothFront} (ι : FrontRecEquiv A B)
include ι

theorem comp_eq_iff (p q : A.Occ) : (ι.Φ p).1.1 = (ι.Φ q).1.1 ↔ p.1.1 = q.1.1 := by
  rw [ι.comp_eq, ι.comp_eq, ι.e.apply_eq_iff_eq]

/-- the inverse transport -/
def symm : FrontRecEquiv B A where
  e := ι.e.symm
  Φ := ι.Φ.symm
  comp_eq p := by
    have := ι.comp_eq (ι.Φ.symm p)
    rw [Equiv.apply_symm_apply] at this
    rw [this, Equiv.symm_apply_apply]
  between_iff p q r hpq hqr := by
    have h1 : (ι.Φ.symm p).1.1 = (ι.Φ.symm q).1.1 := by
      rw [← ι.comp_eq_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hpq
    have h2 : (ι.Φ.symm q).1.1 = (ι.Φ.symm r).1.1 := by
      rw [← ι.comp_eq_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]; exact hqr
    have := ι.between_iff _ _ _ h1 h2
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  meet_iff p q hne := by
    have hne' : ι.Φ.symm p ≠ ι.Φ.symm q := fun h => hne (ι.Φ.symm.injective h)
    have := ι.meet_iff _ _ hne'
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  slope_iff p q hne he := by
    have hne' : ι.Φ.symm p ≠ ι.Φ.symm q := fun h => hne (ι.Φ.symm.injective h)
    have hm := ι.meet_iff _ _ hne'
    simp only [Equiv.apply_symm_apply] at hm
    have := ι.slope_iff _ _ hne' (hm.2 he)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm
  sign_eq p q hne he := by
    have hne' : ι.Φ.symm p ≠ ι.Φ.symm q := fun h => hne (ι.Φ.symm.injective h)
    have hm := ι.meet_iff _ _ hne'
    simp only [Equiv.apply_symm_apply] at hm
    have := ι.sign_eq _ _ hne' (hm.2 he)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm

/-- **the writhe is carried by the record** -/
theorem writhe_eq : A.writhe = B.writhe := by
  unfold SmoothFront.writhe
  refine Finset.sum_bij (fun a ha => ((ι.Φ ⟨a.1, fst_mem_occSet_of_mem_crossingPairs ha⟩).1,
    (ι.Φ ⟨a.2, snd_mem_occSet_of_mem_crossingPairs ha⟩).1)) ?_ ?_ ?_ ?_
  · intro a ha
    have h := A.mem_crossingPairs'.1 ha
    have hPQ : (⟨a.1, fst_mem_occSet_of_mem_crossingPairs ha⟩ : A.Occ) ≠
        ⟨a.2, snd_mem_occSet_of_mem_crossingPairs ha⟩ :=
      fun h' => h.1.2.2.1 (congrArg Subtype.val h')
    have hev : A.eval (⟨a.1, fst_mem_occSet_of_mem_crossingPairs ha⟩ : A.Occ) =
        A.eval (⟨a.2, snd_mem_occSet_of_mem_crossingPairs ha⟩ : A.Occ) := h.1.2.2.2
    rw [B.mem_crossingPairs']
    refine ⟨⟨(ι.Φ _).2.1, (ι.Φ _).2.1, ?_, (ι.meet_iff _ _ hPQ).1 hev⟩, (ι.slope_iff _ _ hPQ hev).1 h.2⟩
    intro h'; exact hPQ (ι.Φ.injective (Subtype.ext h'))
  · intro a ha a' ha' heq
    have h1 := congrArg Prod.fst heq
    have h2 := congrArg Prod.snd heq
    have e1 := congrArg Subtype.val (ι.Φ.injective (Subtype.ext h1))
    have e2 := congrArg Subtype.val (ι.Φ.injective (Subtype.ext h2))
    exact Prod.ext e1 e2
  · intro b hb
    have h := B.mem_crossingPairs'.1 hb
    set P' : B.Occ := ⟨b.1, fst_mem_occSet_of_mem_crossingPairs hb⟩ with hP'
    set Q' : B.Occ := ⟨b.2, snd_mem_occSet_of_mem_crossingPairs hb⟩ with hQ'
    have hPQ' : P' ≠ Q' := fun h' => h.1.2.2.1 (congrArg Subtype.val h')
    have hev' : B.eval P' = B.eval Q' := h.1.2.2.2
    have hne : ι.Φ.symm P' ≠ ι.Φ.symm Q' := fun h' => hPQ' (ι.Φ.symm.injective h')
    have hm := ι.meet_iff _ _ hne
    simp only [Equiv.apply_symm_apply] at hm
    have hs := ι.slope_iff _ _ hne (hm.2 hev')
    simp only [Equiv.apply_symm_apply] at hs
    have hmem : ((ι.Φ.symm P').1, (ι.Φ.symm Q').1) ∈ A.crossingPairs := by
      rw [A.mem_crossingPairs']
      exact ⟨⟨(ι.Φ.symm P').2.1, (ι.Φ.symm Q').2.1, fun h' => hne (Subtype.ext h'), hm.2 hev'⟩, hs.2 h.2⟩
    refine ⟨((ι.Φ.symm P').1, (ι.Φ.symm Q').1), hmem, ?_⟩
    have e1 : (⟨((ι.Φ.symm P').1, (ι.Φ.symm Q').1).1, fst_mem_occSet_of_mem_crossingPairs hmem⟩ : A.Occ) =
        ι.Φ.symm P' := Subtype.ext rfl
    have e2 : (⟨((ι.Φ.symm P').1, (ι.Φ.symm Q').1).2, snd_mem_occSet_of_mem_crossingPairs hmem⟩ : A.Occ) =
        ι.Φ.symm Q' := Subtype.ext rfl
    simp only [e1, e2, Equiv.apply_symm_apply]
    rfl
  · intro a ha
    have h := A.mem_crossingPairs'.1 ha
    exact ι.sign_eq ⟨a.1, fst_mem_occSet_of_mem_crossingPairs ha⟩ ⟨a.2, snd_mem_occSet_of_mem_crossingPairs ha⟩
      (fun h' => h.1.2.2.1 (congrArg Subtype.val h')) h.1.2.2.2

end FrontRecEquiv

/-- **transport of a polygonal reading**: a diagram carrying the record of `A` carries the record of `B`
once the record of `B` is transported to that of `A` -/
def transportMarking {A B : SmoothFront} (κ : FrontRecEquiv B A) {S : Diagram} (m : A.Marking S) :
    B.Marking S where
  e := κ.e.trans m.e
  Φ := κ.Φ.trans m.Φ
  comp_eq p := by
    show S.compOf (m.Φ (κ.Φ p)) = m.e (κ.e p.1.1)
    rw [m.comp_eq, κ.comp_eq]
  between_iff p q r hpq hqr := by
    show cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (S.visitCoord (m.Φ (κ.Φ p))) (S.visitCoord (m.Φ (κ.Φ q))) (S.visitCoord (m.Φ (κ.Φ r)))
    rw [κ.between_iff p q r hpq hqr]
    exact m.between_iff _ _ _ ((κ.comp_eq_iff p q).2 hpq) ((κ.comp_eq_iff q r).2 hqr)
  pair_eq p q hne he := m.pair_eq _ _ (fun h' => hne (κ.Φ.injective h')) ((κ.meet_iff p q hne).1 he)
  over_iff p q hne he := by
    show S.overBit (m.Φ (κ.Φ p)) = true ↔ B.slope p < B.slope q
    rw [m.over_iff _ _ (fun h' => hne (κ.Φ.injective h')) ((κ.meet_iff p q hne).1 he)]
    exact (κ.slope_iff p q hne he).symm
  sgn_eq p q hne he hs := by
    show ((S.sign (m.Φ (κ.Φ p)).1 : ℤ)) = B.crossSign p q
    rw [m.sgn_eq _ _ (fun h' => hne (κ.Φ.injective h')) ((κ.meet_iff p q hne).1 he)
      ((κ.slope_iff p q hne he).1 hs)]
    exact (κ.sign_eq p q hne he).symm

/-! ##### Partners of occurrences -/

/-- the partner of an occurrence is unique (`no_triple`) -/
theorem partner_unique (A : SmoothFront) {p q q' : Param A.c} (hp : p.2 ∈ Ico (0 : ℝ) 1)
    (hq : q.2 ∈ Ico (0 : ℝ) 1) (hq' : q'.2 ∈ Ico (0 : ℝ) 1) (hpq : p ≠ q) (hpq' : p ≠ q')
    (he : A.eval p = A.eval q) (he' : A.eval p = A.eval q') : q = q' := by
  by_contra hne
  exact A.no_triple p q q' (fun hs => hpq (SameParam.eq_of_mem_Ico hp hq hs))
    (fun hs => hne (SameParam.eq_of_mem_Ico hq hq' hs))
    (fun hs => hpq' (SameParam.eq_of_mem_Ico hp hq' hs)) he (he.symm.trans he')

/-- the partner of an occurrence: the other branch of its double point -/
def partner (A : SmoothFront) (p : A.Occ) : A.Occ :=
  Classical.choose (SmoothFront.Marking.exists_partner p)

theorem partner_ne (A : SmoothFront) (p : A.Occ) : p ≠ partner A p :=
  (Classical.choose_spec (SmoothFront.Marking.exists_partner p)).1

theorem eval_partner (A : SmoothFront) (p : A.Occ) : A.eval p = A.eval (partner A p) :=
  (Classical.choose_spec (SmoothFront.Marking.exists_partner p)).2

theorem eq_partner (A : SmoothFront) {p q : A.Occ} (hne : p ≠ q) (he : A.eval p = A.eval q) :
    q = partner A p :=
  Subtype.ext (partner_unique A p.2.1 q.2.1 (partner A p).2.1 (fun h => hne (Subtype.ext h))
    (fun h => partner_ne A p (Subtype.ext h)) he (eval_partner A p))

theorem partner_partner (A : SmoothFront) (p : A.Occ) : partner A (partner A p) = p :=
  (eq_partner A (partner_ne A p).symm (eval_partner A p).symm).symm

theorem mem_doubleSet_partner (A : SmoothFront) (p : A.Occ) : (p.1, (partner A p).1) ∈ A.doubleSet :=
  A.mem_doubleSet.2 ⟨p.2.1, (partner A p).2.1, fun h => partner_ne A p (Subtype.ext h), eval_partner A p⟩

/-! ##### The local double-point hypotheses -/

/-- the `ε`-box about a double point -/
def box (ε : ℝ) {c : ℕ} (a : Param c × Param c) : Set (ℝ × ℝ) :=
  Ioo (a.1.2 - ε) (a.1.2 + ε) ×ˢ Ioo (a.2.2 - ε) (a.2.2 + ε)

theorem mem_box {ε : ℝ} {c : ℕ} {a : Param c × Param c} {uv : ℝ × ℝ} :
    uv ∈ box ε a ↔ uv.1 ∈ Ioo (a.1.2 - ε) (a.1.2 + ε) ∧ uv.2 ∈ Ioo (a.2.2 - ε) (a.2.2 + ε) := Iff.rfl

/-- **Local double-point hypotheses** between `A` and a nearby front `B` (circles reindexed by `ρ`):
distinct occurrences of `A` on one circle are separated by more than `2ε` (mod 1); each double point
of `A` has exactly one double point of `B` in its `ε`-box, with the same over rule and sign; every
double point of `B` lies (mod 1) in the `ε`-box of a double point of `A`. -/
structure OccHyp (A B : SmoothFront) (ρ : Fin A.c ≃ Fin B.c) (ε : ℝ) : Prop where
  pos : 0 < ε
  sep : ∀ p ∈ A.occSet, ∀ q ∈ A.occSet, p.1 = q.1 → p ≠ q → Sep ε (p.2 - q.2)
  exu : ∀ a ∈ A.doubleSet, ∃! uv : ℝ × ℝ, uv ∈ box ε a ∧ B.eval (ρ a.1.1, uv.1) = B.eval (ρ a.2.1, uv.2)
  pres : ∀ a ∈ A.doubleSet, ∀ uv ∈ box ε a,
    (B.slope (ρ a.1.1, uv.1) < B.slope (ρ a.2.1, uv.2) ↔ A.slope a.1 < A.slope a.2) ∧
    B.crossSign (ρ a.1.1, uv.1) (ρ a.2.1, uv.2) = A.crossSign a.1 a.2
  nonew : ∀ b ∈ B.doubleSet, ∃ a ∈ A.doubleSet, ∃ m n : ℤ, b.1.1 = ρ a.1.1 ∧ b.2.1 = ρ a.2.1 ∧
    (b.1.2 + m, b.2.2 + n) ∈ box ε a

namespace OccHyp

variable {A B : SmoothFront} {ρ : Fin A.c ≃ Fin B.c} {ε : ℝ} (h : OccHyp A B ρ ε)
include h

/-- the double point of `B` in the box of the double point `a` of `A` -/
def sol (a : Param A.c × Param A.c) (ha : a ∈ A.doubleSet) : ℝ × ℝ :=
  Classical.choose (h.exu a ha).exists

theorem sol_mem (a : Param A.c × Param A.c) (ha : a ∈ A.doubleSet) : h.sol a ha ∈ box ε a :=
  (Classical.choose_spec (h.exu a ha).exists).1

theorem sol_eval (a : Param A.c × Param A.c) (ha : a ∈ A.doubleSet) :
    B.eval (ρ a.1.1, (h.sol a ha).1) = B.eval (ρ a.2.1, (h.sol a ha).2) :=
  (Classical.choose_spec (h.exu a ha).exists).2

theorem sol_unique (a : Param A.c × Param A.c) (ha : a ∈ A.doubleSet) {uv : ℝ × ℝ} (hmem : uv ∈ box ε a)
    (heq : B.eval (ρ a.1.1, uv.1) = B.eval (ρ a.2.1, uv.2)) : uv = h.sol a ha :=
  (h.exu a ha).unique ⟨hmem, heq⟩ ⟨h.sol_mem a ha, h.sol_eval a ha⟩

/-- the parameter of the image of the occurrence `p` -/
def φ (p : A.Occ) : ℝ := (h.sol (p.1, (partner A p).1) (mem_doubleSet_partner A p)).1

theorem φ_mem (p : A.Occ) : h.φ p ∈ Ioo (p.1.2 - ε) (p.1.2 + ε) :=
  (h.sol_mem (p.1, (partner A p).1) (mem_doubleSet_partner A p)).1

theorem φ_abs (p : A.Occ) : |h.φ p - p.1.2| < ε := by
  have := h.φ_mem p
  rw [abs_sub_lt_iff]; constructor <;> linarith [this.1, this.2]

/-- the image of the partner is the second coordinate of the solution -/
theorem φ_partner (p : A.Occ) :
    h.φ (partner A p) = (h.sol (p.1, (partner A p).1) (mem_doubleSet_partner A p)).2 := by
  unfold φ
  have hsw : h.sol ((partner A p).1, (partner A (partner A p)).1) (mem_doubleSet_partner A (partner A p)) =
      (h.sol (p.1, (partner A p).1) (mem_doubleSet_partner A p)).swap := by
    symm
    apply h.sol_unique
    · rw [mem_box]
      have hm := h.sol_mem (p.1, (partner A p).1) (mem_doubleSet_partner A p)
      rw [mem_box] at hm
      rw [partner_partner]
      exact ⟨hm.2, hm.1⟩
    · rw [partner_partner]
      exact (h.sol_eval (p.1, (partner A p).1) (mem_doubleSet_partner A p)).symm
  rw [hsw]; rfl

/-- the image occurrence, as a parameter of the fundamental period -/
def Φ₀ (p : A.Occ) : Param B.c := (ρ p.1.1, Int.fract (h.φ p))

theorem sameParam_Φ₀ (p : A.Occ) : SameParam (ρ p.1.1, h.φ p) (h.Φ₀ p) :=
  ⟨rfl, -⌊h.φ p⌋, fract_eq_add_int _⟩

theorem eval_Φ₀ (p : A.Occ) : B.eval (h.Φ₀ p) = B.eval (ρ p.1.1, h.φ p) :=
  SmoothFront.eval_of_sameParam (h.sameParam_Φ₀ p)

theorem slope_Φ₀ (p : A.Occ) : B.slope (h.Φ₀ p) = B.slope (ρ p.1.1, h.φ p) :=
  B.slope_of_sameParam (h.sameParam_Φ₀ p)

theorem crossSign_Φ₀ (p q : A.Occ) :
    B.crossSign (h.Φ₀ p) (h.Φ₀ q) = B.crossSign (ρ p.1.1, h.φ p) (ρ q.1.1, h.φ q) :=
  B.crossSign_of_sameParam (h.sameParam_Φ₀ p) (h.sameParam_Φ₀ q)

theorem Φ₀_ne (p q : A.Occ) (hne : p ≠ q) : h.Φ₀ p ≠ h.Φ₀ q := by
  intro heq
  have h1 : ρ p.1.1 = ρ q.1.1 := congrArg Prod.fst heq
  have h1' : p.1.1 = q.1.1 := ρ.injective h1
  have h2 : Int.fract (h.φ p) = Int.fract (h.φ q) := congrArg Prod.snd heq
  have hne' : p.1 ≠ q.1 := fun h' => hne (Subtype.ext h')
  exact fract_ne_of_sep (h.sep p.1 p.2 q.1 q.2 h1' hne') (h.φ_abs p) (h.φ_abs q) h2

theorem eval_Φ₀_partner (p : A.Occ) : B.eval (h.Φ₀ p) = B.eval (h.Φ₀ (partner A p)) := by
  rw [eval_Φ₀, eval_Φ₀, φ_partner]
  exact h.sol_eval (p.1, (partner A p).1) (mem_doubleSet_partner A p)

theorem Φ₀_mem (p : A.Occ) : h.Φ₀ p ∈ B.occSet :=
  B.mem_occSet.2 ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, h.Φ₀ (partner A p),
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, h.Φ₀_ne _ _ (partner_ne A p), h.eval_Φ₀_partner p⟩

/-- the occurrence map -/
def Φ (p : A.Occ) : B.Occ := ⟨h.Φ₀ p, h.Φ₀_mem p⟩

theorem Φ_injective : Function.Injective h.Φ := fun p q heq =>
  by_contra fun hne => h.Φ₀_ne p q hne (congrArg Subtype.val heq)

theorem Φ_surjective : Function.Surjective h.Φ := by
  intro p'
  have hb : (p'.1, (partner B p').1) ∈ B.doubleSet := mem_doubleSet_partner B p'
  obtain ⟨a, ha, m, n, h1, h2, hmn⟩ := h.nonew _ hb
  have haocc : a.1 ∈ A.occSet := A.fst_mem_occSet_of_mem_doubleSet ha
  have ha' := A.mem_doubleSet.1 ha
  have hQ : (partner A ⟨a.1, haocc⟩).1 = a.2 := by
    have := eq_partner A (p := ⟨a.1, haocc⟩) (q := ⟨a.2, A.snd_mem_occSet_of_mem_doubleSet ha⟩)
      (fun h' => ha'.2.2.1 (congrArg Subtype.val h')) ha'.2.2.2
    exact congrArg Subtype.val this.symm
  have hdp : ((⟨a.1, haocc⟩ : A.Occ).1, (partner A ⟨a.1, haocc⟩).1) = a := Prod.ext rfl hQ
  have hsol : ((p'.1.2 + m, (partner B p').1.2 + n) : ℝ × ℝ) =
      h.sol ((⟨a.1, haocc⟩ : A.Occ).1, (partner A ⟨a.1, haocc⟩).1) (mem_doubleSet_partner A _) := by
    apply h.sol_unique
    · rw [hdp]; exact hmn
    · rw [hdp]
      have e1 : B.eval (ρ a.1.1, p'.1.2 + m) = B.eval p'.1 :=
        SmoothFront.eval_of_sameParam (⟨h1, m, rfl⟩ : SameParam p'.1 (ρ a.1.1, p'.1.2 + m))
      have e2 : B.eval (ρ a.2.1, (partner B p').1.2 + n) = B.eval (partner B p').1 :=
        SmoothFront.eval_of_sameParam
          (⟨h2, n, rfl⟩ : SameParam (partner B p').1 (ρ a.2.1, (partner B p').1.2 + n))
      show B.eval (ρ a.1.1, p'.1.2 + m) = B.eval (ρ a.2.1, (partner B p').1.2 + n)
      rw [e1, e2]; exact eval_partner B p'
  refine ⟨⟨a.1, haocc⟩, Subtype.ext ?_⟩
  show (ρ a.1.1, Int.fract (h.φ ⟨a.1, haocc⟩)) = p'.1
  have hφ : h.φ ⟨a.1, haocc⟩ = p'.1.2 + m := by
    unfold φ; rw [← hsol]
  rw [hφ, Int.fract_add_intCast, Int.fract_eq_self.2 p'.2.1]
  exact Prod.ext h1.symm rfl

/-- the occurrence bijection -/
def toEquiv : A.Occ ≃ B.Occ := Equiv.ofBijective h.Φ ⟨h.Φ_injective, h.Φ_surjective⟩

theorem toEquiv_val (p : A.Occ) : (h.toEquiv p).1 = h.Φ₀ p := rfl

/-- **the local hypotheses transport the record** -/
def toFrontRecEquiv : FrontRecEquiv A B where
  e := ρ
  Φ := h.toEquiv
  comp_eq p := rfl
  between_iff p q r hpq hqr := by
    show cycBetween p.1.2 q.1.2 r.1.2 ↔
      cycBetween (Int.fract (h.φ p)) (Int.fract (h.φ q)) (Int.fract (h.φ r))
    apply cycBetween_fract_of_sep p.2.1 q.2.1 r.2.1
    · intro hne; exact h.sep p.1 p.2 q.1 q.2 hpq (fun h' => hne (congrArg Prod.snd h'))
    · intro hne; exact h.sep q.1 q.2 r.1 r.2 hqr (fun h' => hne (congrArg Prod.snd h'))
    · intro hne; exact h.sep p.1 p.2 r.1 r.2 (hpq.trans hqr) (fun h' => hne (congrArg Prod.snd h'))
    · intro heq; have : p = q := Subtype.ext (Prod.ext hpq heq); rw [this]
    · intro heq; have : q = r := Subtype.ext (Prod.ext hqr heq); rw [this]
    · intro heq; have : p = r := Subtype.ext (Prod.ext (hpq.trans hqr) heq); rw [this]
    · exact h.φ_abs p
    · exact h.φ_abs q
    · exact h.φ_abs r
  meet_iff p q hne := by
    constructor
    · intro he
      have hq : q = partner A p := eq_partner A hne he
      rw [hq]; exact h.eval_Φ₀_partner p
    · intro he
      have h1 : h.toEquiv q = partner B (h.toEquiv p) :=
        eq_partner B (fun h' => hne (h.toEquiv.injective h')) he
      have h2 : h.toEquiv (partner A p) = partner B (h.toEquiv p) :=
        eq_partner B (fun h' => partner_ne A p (h.toEquiv.injective h')) (h.eval_Φ₀_partner p)
      have : q = partner A p := h.toEquiv.injective (h1.trans h2.symm)
      rw [this]; exact eval_partner A p
  slope_iff p q hne he := by
    have hq : q = partner A p := eq_partner A hne he
    subst hq
    have := (h.pres (p.1, (partner A p).1) (mem_doubleSet_partner A p) _
      (h.sol_mem (p.1, (partner A p).1) (mem_doubleSet_partner A p))).1
    show A.slope p.1 < A.slope (partner A p).1 ↔ B.slope (h.Φ₀ p) < B.slope (h.Φ₀ (partner A p))
    rw [slope_Φ₀, slope_Φ₀, φ_partner]
    exact this.symm
  sign_eq p q hne he := by
    have hq : q = partner A p := eq_partner A hne he
    subst hq
    have := (h.pres (p.1, (partner A p).1) (mem_doubleSet_partner A p) _
      (h.sol_mem (p.1, (partner A p).1) (mem_doubleSet_partner A p))).2
    show A.crossSign p.1 (partner A p).1 = B.crossSign (h.Φ₀ p) (h.Φ₀ (partner A p))
    rw [crossSign_Φ₀, φ_partner]
    exact this.symm

end OccHyp
/-! #### Part F: the analysis for double points -/

/-- the sign of a continuous function is locally constant where it is nonzero -/
theorem eventually_sign_iff {X : Type*} [TopologicalSpace X] {f : X → ℝ} {x₀ : X}
    (hf : ContinuousAt f x₀) (h0 : f x₀ ≠ 0) :
    ∀ᶠ x in 𝓝 x₀, (f x < 0 ↔ f x₀ < 0) ∧ (0 < f x ↔ 0 < f x₀) := by
  rcases lt_or_gt_of_ne h0 with hneg | hpos
  · exact (Filter.Tendsto.eventually_lt_const hneg hf).mono fun z hz =>
      ⟨⟨fun _ => hneg, fun _ => hz⟩, ⟨fun h => absurd hz (not_lt.2 h.le), fun h => absurd hneg (not_lt.2 h.le)⟩⟩
  · exact (Filter.Tendsto.eventually_const_lt hpos hf).mono fun z hz =>
      ⟨⟨fun h => absurd hz (not_lt.2 h.le), fun h => absurd hpos (not_lt.2 h.le)⟩, ⟨fun _ => hpos, fun _ => hz⟩⟩

/-! ##### The linear equivalence `(s, r) ↦ s • a - r • b` of two independent vectors -/

/-- the linear map `(s, r) ↦ s • a - r • b` -/
def planeMap (a b : Plane) : ℝ × ℝ →L[ℝ] Plane :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight a - (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight b

theorem planeMap_apply (a b : Plane) (x : ℝ × ℝ) : planeMap a b x = x.1 • a - x.2 • b := rfl

/-- its inverse (Cramer) when `D = det a b ≠ 0` -/
def planeInv (a b : Plane) (D : ℝ) : Plane →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight ((b.2 / D, a.2 / D) : ℝ × ℝ) +
  (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight ((-b.1 / D, -a.1 / D) : ℝ × ℝ)

theorem planeInv_apply (a b : Plane) (D : ℝ) (w : Plane) :
    planeInv a b D w = w.1 • ((b.2 / D, a.2 / D) : ℝ × ℝ) + w.2 • ((-b.1 / D, -a.1 / D) : ℝ × ℝ) := rfl

/-- `(s, r) ↦ s • a - r • b` is a linear equivalence when `det a b ≠ 0` -/
def planeEquiv (a b : Plane) (hD : det a b ≠ 0) : (ℝ × ℝ) ≃L[ℝ] Plane :=
  ContinuousLinearEquiv.equivOfInverse (planeMap a b) (planeInv a b (det a b))
    (fun x => by
      rw [planeInv_apply, planeMap_apply]
      unfold det at hD ⊢
      have hinv := mul_inv_cancel₀ hD
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, Prod.snd_sub, Prod.smul_snd, smul_eq_mul]
        linear_combination x.1 * hinv
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, smul_eq_mul]
        linear_combination x.2 * hinv)
    (fun y => by
      rw [planeInv_apply, planeMap_apply]
      unfold det at hD ⊢
      have hinv := mul_inv_cancel₀ hD
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_sub, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination y.1 * hinv
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        linear_combination y.2 * hinv)

theorem coe_planeEquiv (a b : Plane) (hD : det a b ≠ 0) :
    (planeEquiv a b hD : ℝ × ℝ →L[ℝ] Plane) = planeMap a b := rfl

theorem box_mono {ε ε' : ℝ} (h : ε ≤ ε') {c : ℕ} (a : Param c × Param c) : box ε a ⊆ box ε' a :=
  Set.prod_mono (Ioo_subset_Ioo (by linarith) (by linarith)) (Ioo_subset_Ioo (by linarith) (by linarith))

/-! ##### Calculus: strict monotonicity from a nonvanishing third derivative -/

/-- if `f' φ = f'' φ = 0` and `f''' > 0` on an open interval containing `φ`, `f` is strictly
increasing there -/
theorem strictMonoOn_of_third_deriv_pos {f f₁ f₂ f₃ : ℝ → ℝ} (h1 : ∀ u, HasDerivAt f (f₁ u) u)
    (h2 : ∀ u, HasDerivAt f₁ (f₂ u) u) (h3 : ∀ u, HasDerivAt f₂ (f₃ u) u)
    {α β φ : ℝ} (hφ : φ ∈ Ioo α β) (hf1 : f₁ φ = 0) (hf2 : f₂ φ = 0)
    (hpos : ∀ u ∈ Ioo α β, 0 < f₃ u) : StrictMonoOn f (Ioo α β) := by
  have c0 : Continuous f := continuous_iff_continuousAt.2 fun u => (h1 u).continuousAt
  have c1 : Continuous f₁ := continuous_iff_continuousAt.2 fun u => (h2 u).continuousAt
  have c2 : Continuous f₂ := continuous_iff_continuousAt.2 fun u => (h3 u).continuousAt
  have d1 : deriv f = f₁ := funext fun u => (h1 u).deriv
  have d2 : deriv f₁ = f₂ := funext fun u => (h2 u).deriv
  have d3 : deriv f₂ = f₃ := funext fun u => (h3 u).deriv
  have m2 : StrictMonoOn f₂ (Ioo α β) :=
    strictMonoOn_of_deriv_pos (convex_Ioo α β) c2.continuousOn
      (by rw [interior_Ioo]; intro u hu; rw [d3]; exact hpos u hu)
  have f2neg : ∀ u ∈ Ioo α φ, f₂ u < 0 := fun u hu => by
    have := m2 ⟨hu.1, hu.2.trans hφ.2⟩ hφ hu.2; rwa [hf2] at this
  have f2pos : ∀ u ∈ Ioo φ β, 0 < f₂ u := fun u hu => by
    have := m2 hφ ⟨hφ.1.trans hu.1, hu.2⟩ hu.1; rwa [hf2] at this
  have a1 : StrictAntiOn f₁ (Ioc α φ) :=
    strictAntiOn_of_deriv_neg (convex_Ioc α φ) c1.continuousOn
      (by rw [interior_Ioc]; intro u hu; rw [d2]; exact f2neg u hu)
  have m1 : StrictMonoOn f₁ (Ico φ β) :=
    strictMonoOn_of_deriv_pos (convex_Ico φ β) c1.continuousOn
      (by rw [interior_Ico]; intro u hu; rw [d2]; exact f2pos u hu)
  have f1pos : ∀ u ∈ Ioo α β, u ≠ φ → 0 < f₁ u := by
    intro u hu hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := a1 ⟨hu.1, hlt.le⟩ ⟨hφ.1, le_rfl⟩ hlt; rwa [hf1] at this
    · have := m1 ⟨le_rfl, hφ.2⟩ ⟨hgt.le, hu.2⟩ hgt; rwa [hf1] at this
  have mL : StrictMonoOn f (Ioc α φ) :=
    strictMonoOn_of_deriv_pos (convex_Ioc α φ) c0.continuousOn
      (by rw [interior_Ioc]; intro u hu; rw [d1]; exact f1pos u ⟨hu.1, hu.2.trans hφ.2⟩ hu.2.ne)
  have mR : StrictMonoOn f (Ico φ β) :=
    strictMonoOn_of_deriv_pos (convex_Ico φ β) c0.continuousOn
      (by rw [interior_Ico]; intro u hu; rw [d1]; exact f1pos u ⟨hφ.1.trans hu.1, hu.2⟩ hu.1.ne')
  intro u hu v hv huv
  rcases le_or_gt u φ with hu' | hu'
  · rcases le_or_gt v φ with hv' | hv'
    · exact mL ⟨hu.1, hu'⟩ ⟨hv.1, hv'⟩ huv
    · calc f u ≤ f φ := by
            rcases eq_or_lt_of_le hu' with h | h
            · rw [h]
            · exact (mL ⟨hu.1, hu'⟩ ⟨hφ.1, le_rfl⟩ h).le
        _ < f v := mR ⟨le_rfl, hφ.2⟩ ⟨hv'.le, hv.2⟩ hv'
  · exact mR ⟨hu'.le, hu.2⟩ ⟨(hu'.trans huv).le, hv.2⟩ huv

/-- the same with either sign of `f'''`, as injectivity -/
theorem injOn_of_third_deriv {f f₁ f₂ f₃ : ℝ → ℝ} (h1 : ∀ u, HasDerivAt f (f₁ u) u)
    (h2 : ∀ u, HasDerivAt f₁ (f₂ u) u) (h3 : ∀ u, HasDerivAt f₂ (f₃ u) u)
    {α β φ : ℝ} (hφ : φ ∈ Ioo α β) (hf1 : f₁ φ = 0) (hf2 : f₂ φ = 0)
    (hsign : (∀ u ∈ Ioo α β, 0 < f₃ u) ∨ (∀ u ∈ Ioo α β, f₃ u < 0)) : InjOn f (Ioo α β) := by
  rcases hsign with hpos | hneg
  · exact (strictMonoOn_of_third_deriv_pos h1 h2 h3 hφ hf1 hf2 hpos).injOn
  · have := strictMonoOn_of_third_deriv_pos (f := fun u => -f u) (f₁ := fun u => -f₁ u)
      (f₂ := fun u => -f₂ u) (f₃ := fun u => -f₃ u) (fun u => (h1 u).neg) (fun u => (h2 u).neg)
      (fun u => (h3 u).neg) hφ (by simp [hf1]) (by simp [hf2]) (fun u hu => by simp; exact hneg u hu)
    intro u hu v hv huv
    exact this.injOn hu hv (by simp only [huv])

section DoubleAnalysis

include d

/-- the double-point map of the pair of components `(i, i')` -/
def Φ2 (i i' : Fin F.c) (t : I) (uv : ℝ × ℝ) : Plane := pdI d i 0 (t, uv.1) - pdI d i' 0 (t, uv.2)

/-- its derivative in `(u, v)` -/
def DΦ2 (i i' : Fin F.c) (t : I) (uv : ℝ × ℝ) : ℝ × ℝ →L[ℝ] Plane :=
  planeMap (pdI d i 1 (t, uv.1)) (pdI d i' 1 (t, uv.2))

theorem hasFDerivAt_Φ2 (i i' : Fin F.c) (t : I) (uv : ℝ × ℝ) :
    HasFDerivAt (Φ2 d i i' t) (DΦ2 d i i' t uv) uv := by
  have h1 : HasFDerivAt (fun uv : ℝ × ℝ => pdI d i 0 (t, uv.1))
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (pdI d i 1 (t, uv.1))) uv := by
    have := (hasDerivAt_pdI d i 0 t uv.1).hasFDerivAt.comp uv hasFDerivAt_fst
    refine this.congr_fderiv ?_
    ext <;> simp
  have h2 : HasFDerivAt (fun uv : ℝ × ℝ => pdI d i' 0 (t, uv.2))
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (pdI d i' 1 (t, uv.2))) uv := by
    have := (hasDerivAt_pdI d i' 0 t uv.2).hasFDerivAt.comp uv hasFDerivAt_snd
    refine this.congr_fderiv ?_
    ext <;> simp
  exact h1.sub h2

theorem continuous_Φ2 (i i' : Fin F.c) : Continuous (fun p : I × (ℝ × ℝ) => Φ2 d i i' p.1 p.2) := by
  have h1 := continuous_pdI d i 0
  have h2 := continuous_pdI d i' 0
  unfold Φ2; fun_prop

theorem continuous_DΦ2 (i i' : Fin F.c) : Continuous (fun p : I × (ℝ × ℝ) => DΦ2 d i i' p.1 p.2) := by
  have h1 := continuous_pdI d i 1
  have h2 := continuous_pdI d i' 1
  unfold DΦ2 planeMap
  refine Continuous.sub ?_ ?_
  · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) Plane
      (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous.comp (by fun_prop)
  · exact (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) Plane
      (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous.comp (by fun_prop)

variable (t₀ : I)

/-- persistence of a transverse double point along the family (2-D case of `persist`) -/
theorem double_persist (a : Param (d.path t₀.1).c × Param (d.path t₀.1).c)
    (ha : a ∈ (d.path t₀.1).doubleSet) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ᶠ t in 𝓝 t₀, ∃! uv : ℝ × ℝ, uv ∈ box ε a ∧
      (d.path t.1).eval (ρ d t₀.1 t.1 a.1.1, uv.1) = (d.path t.1).eval (ρ d t₀.1 t.1 a.2.1, uv.2) := by
  have hd : (d.path t₀.1).IsDouble a.1 a.2 := (d.path t₀.1).isDouble_of_mem_doubleSet ha
  have h0 : Φ2 d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) t₀ (a.1.2, a.2.2) = 0 := by
    unfold Φ2; rw [sub_eq_zero]
    have := hd.2
    rwa [eval_eq, eval_eq] at this
  have hdet : det (pdI d (Fin.cast (d.c_eq t₀.1) a.1.1) 1 (t₀, a.1.2))
      (pdI d (Fin.cast (d.c_eq t₀.1) a.2.1) 1 (t₀, a.2.2)) ≠ 0 := by
    have := (d.path t₀.1).det_vel_ne_zero_of_isDouble hd
    rwa [vel_eq, vel_eq] at this
  obtain ⟨ε₀, hε₀, H⟩ := persist (X := I) (E := ℝ × ℝ) (G := Plane) (Φ2 d _ _) (DΦ2 d _ _)
    (hasFDerivAt_Φ2 d _ _) (continuous_Φ2 d _ _) (continuous_DΦ2 d _ _) t₀ (a.1.2, a.2.2) h0
    (planeEquiv _ _ hdet) rfl
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => (H ε hε hεε₀).mono fun t ht => ?_⟩
  have hbox : ∀ uv : ℝ × ℝ, uv ∈ ball (a.1.2, a.2.2) ε ↔ uv ∈ box ε a := by
    intro uv; rw [← ball_prod_same, Real.ball_eq_Ioo, Real.ball_eq_Ioo]; rfl
  have heq : ∀ uv : ℝ × ℝ, Φ2 d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) t uv = 0 ↔
      (d.path t.1).eval (ρ d t₀.1 t.1 a.1.1, uv.1) = (d.path t.1).eval (ρ d t₀.1 t.1 a.2.1, uv.2) := by
    intro uv; simp only [Φ2, sub_eq_zero, eval_eq, cast_ρ]
  simpa only [hbox, heq] using ht

/-- the slope difference of the family at a pair of parameters -/
def slDiff (i i' : Fin F.c) : I × (ℝ × ℝ) → ℝ := fun z =>
  (pdI d i 1 (z.1, z.2.1)).2 / (pdI d i 1 (z.1, z.2.1)).1 -
    (pdI d i' 1 (z.1, z.2.2)).2 / (pdI d i' 1 (z.1, z.2.2)).1

/-- the tangent determinant of the family at a pair of parameters -/
def dtFun (i i' : Fin F.c) : I × (ℝ × ℝ) → ℝ := fun z =>
  det (pdI d i 1 (z.1, z.2.1)) (pdI d i' 1 (z.1, z.2.2))

theorem continuous_dtFun (i i' : Fin F.c) : Continuous (dtFun d i i') := by
  have h1 := continuous_pdI d i 1
  have h2 := continuous_pdI d i' 1
  unfold dtFun det; fun_prop

/-- the over rule and the sign at a double point persist on a box -/
theorem double_pres (a : Param (d.path t₀.1).c × Param (d.path t₀.1).c)
    (ha : a ∈ (d.path t₀.1).doubleSet) :
    ∃ ε₁ > 0, ∀ᶠ t in 𝓝 t₀, ∀ uv ∈ box ε₁ a,
      ((d.path t.1).slope (ρ d t₀.1 t.1 a.1.1, uv.1) < (d.path t.1).slope (ρ d t₀.1 t.1 a.2.1, uv.2) ↔
        (d.path t₀.1).slope a.1 < (d.path t₀.1).slope a.2) ∧
      (d.path t.1).crossSign (ρ d t₀.1 t.1 a.1.1, uv.1) (ρ d t₀.1 t.1 a.2.1, uv.2) =
        (d.path t₀.1).crossSign a.1 a.2 := by
  have hd : (d.path t₀.1).IsDouble a.1 a.2 := (d.path t₀.1).isDouble_of_mem_doubleSet ha
  have hc1 := continuous_pdI d (Fin.cast (d.c_eq t₀.1) a.1.1) 1
  have hc2 := continuous_pdI d (Fin.cast (d.c_eq t₀.1) a.2.1) 1
  have hx1 : (pdI d (Fin.cast (d.c_eq t₀.1) a.1.1) 1 (t₀, a.1.2)).1 ≠ 0 := by
    have := (d.path t₀.1).vel_fst_ne_zero_of_isDouble hd; rwa [vel_eq] at this
  have hx2 : (pdI d (Fin.cast (d.c_eq t₀.1) a.2.1) 1 (t₀, a.2.2)).1 ≠ 0 := by
    have := (d.path t₀.1).vel_fst_ne_zero_of_isDouble hd.symm; rwa [vel_eq] at this
  have hsl : ContinuousAt (slDiff d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1)) (t₀, (a.1.2, a.2.2)) := by
    unfold slDiff
    apply ContinuousAt.sub
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) hx1
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) hx2
  have hsl0 : slDiff d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (t₀, (a.1.2, a.2.2)) ≠ 0 := by
    have := (d.path t₀.1).slope_ne_of_isDouble hd
    unfold SmoothFront.slope at this
    rw [vel_eq, vel_eq] at this
    exact sub_ne_zero.2 this
  have hdt0 : dtFun d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (t₀, (a.1.2, a.2.2)) ≠ 0 := by
    have := (d.path t₀.1).det_vel_ne_zero_of_isDouble hd; rwa [vel_eq, vel_eq] at this
  have ev := (eventually_sign_iff hsl hsl0).and
    (eventually_sign_iff (continuous_dtFun d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1)).continuousAt hdt0)
  rw [nhds_prod_eq, eventually_prod_iff] at ev
  obtain ⟨pa, hpa, pb, hpb, hab⟩ := ev
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.eventually_nhds_iff.mp hpb
  refine ⟨ε₁, hε₁, hpa.mono fun t ht uv huv => ?_⟩
  have huv' : dist uv (a.1.2, a.2.2) < ε₁ := by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := huv
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_sub_lt_iff, abs_sub_lt_iff]
    dsimp only
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  obtain ⟨⟨k1, -⟩, ⟨-, k2⟩⟩ := hab ht (hball huv')
  constructor
  · have e : ∀ s : I, ∀ w : ℝ × ℝ,
        ((d.path s.1).slope (ρ d t₀.1 s.1 a.1.1, w.1) < (d.path s.1).slope (ρ d t₀.1 s.1 a.2.1, w.2) ↔
          slDiff d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (s, w) < 0) := by
      intro s w
      unfold SmoothFront.slope slDiff
      simp only [vel_eq, cast_ρ]
      rw [sub_neg]
    rw [e t uv, k1]
    unfold SmoothFront.slope slDiff
    rw [vel_eq, vel_eq, sub_neg]
  · have e2 : ∀ s : I, ∀ w : ℝ × ℝ,
        (d.path s.1).crossSign (ρ d t₀.1 s.1 a.1.1, w.1) (ρ d t₀.1 s.1 a.2.1, w.2) =
          if 0 < dtFun d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (s, w) then 1 else -1 := by
      intro s w
      unfold SmoothFront.crossSign dtFun
      simp only [vel_eq, cast_ρ]
    have e3 : (d.path t₀.1).crossSign a.1 a.2 = if 0 < dtFun d (Fin.cast (d.c_eq t₀.1) a.1.1) (Fin.cast (d.c_eq t₀.1) a.2.1) (t₀, (a.1.2, a.2.2)) then 1 else -1 := by
      unfold SmoothFront.crossSign dtFun
      rw [vel_eq, vel_eq]
    rw [e2 t uv, e3]
    exact if_congr k2 rfl rfl

/-! ##### Uniform local injectivity of the components -/

theorem hasDerivAt_det_pdI (a : Plane) (i : Fin F.c) (k : ℕ) (t : I) (u : ℝ) :
    HasDerivAt (fun u => det a (pdI d i k (t, u))) (det a (pdI d i (k + 1) (t, u))) u := by
  have h := hasDerivAt_pdI d i k t u
  have hs : HasDerivAt (fun u => (pdI d i k (t, u)).2) (pdI d i (k + 1) (t, u)).2 u := h.snd
  have hf : HasDerivAt (fun u => (pdI d i k (t, u)).1) (pdI d i (k + 1) (t, u)).1 u := h.fst
  unfold det
  exact (hs.const_mul a.1).sub (hf.const_mul a.2)

/-- the determinant `det(γ''(t, v), γ'''(t, u))` of component `i` (third-derivative test) -/
def Wfun (i : Fin F.c) : I × (ℝ × ℝ) → ℝ := fun z =>
  det (pdI d i 2 (z.1, z.2.2)) (pdI d i 3 (z.1, z.2.1))

theorem continuous_Wfun (i : Fin F.c) : Continuous (Wfun d i) := by
  have h2 := continuous_pdI d i 2
  have h3 := continuous_pdI d i 3
  unfold Wfun det; fun_prop

/-- near every parameter, the component `i` of `path t` is injective, uniformly for `t` near `t₀` -/
theorem injOn_near (i : Fin F.c) (u₀ : ℝ) :
    ∃ r > 0, ∀ᶠ t in 𝓝 t₀, InjOn (fun u => pdI d i 0 (t, u)) (Ioo (u₀ - r) (u₀ + r)) := by
  by_cases hreg : gx d i (t₀, u₀) = 0
  · -- a cusp of `path t₀`: the third-derivative argument
    have hc : (d.path t₀.1).IsCusp (Fin.cast (d.c_eq t₀.1).symm i, u₀) :=
      (isCusp_iff_gx d t₀ (Fin.cast (d.c_eq t₀.1).symm i, u₀)).2 hreg
    have hne : det (pdI d i 2 (t₀, u₀)) (pdI d i 3 (t₀, u₀)) ≠ 0 := by
      have := (d.path t₀.1).det_acc_jerk_ne_zero_of_isCusp hc; rwa [acc_eq, jerk_eq] at this
    have h2 : gxx d i (t₀, u₀) ≠ 0 := by
      have := (d.path t₀.1).acc_fst_ne_zero_of_isCusp hc; rwa [acc_eq] at this
    have hW0 : Wfun d i (t₀, (u₀, u₀)) ≠ 0 := hne
    have ev := eventually_sign_iff (continuous_Wfun d i).continuousAt hW0
    rw [nhds_prod_eq, eventually_prod_iff] at ev
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := ev
    obtain ⟨r₁, hr₁, hball⟩ := Metric.eventually_nhds_iff.mp hpb
    obtain ⟨ε₀, hε₀, H⟩ := cusp_persist d t₀ i u₀ hreg h2
    refine ⟨min r₁ ε₀, lt_min hr₁ hε₀, ?_⟩
    filter_upwards [hpa, H (min r₁ ε₀) (lt_min hr₁ hε₀) (min_le_right _ _)] with t ht hex
    obtain ⟨φ, ⟨hφ, hφ0⟩, -⟩ := hex
    have hWbox : ∀ u ∈ Ioo (u₀ - min r₁ ε₀) (u₀ + min r₁ ε₀), ∀ v ∈ Ioo (u₀ - min r₁ ε₀) (u₀ + min r₁ ε₀),
        (Wfun d i (t, (u, v)) < 0 ↔ Wfun d i (t₀, (u₀, u₀)) < 0) ∧
        (0 < Wfun d i (t, (u, v)) ↔ 0 < Wfun d i (t₀, (u₀, u₀))) := by
      intro u hu v hv
      apply hab ht; apply hball
      rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_sub_lt_iff, abs_sub_lt_iff]
      dsimp only
      have := min_le_left r₁ ε₀
      exact ⟨⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩, ⟨by linarith [hv.1, hv.2], by linarith [hv.1, hv.2]⟩⟩
    -- the velocity vanishes at the cusp `φ` of `path t`
    have hv0 : pdI d i 1 (t, φ) = 0 := by
      have hcusp : (d.path t.1).IsCusp (Fin.cast (d.c_eq t.1).symm i, φ) :=
        (isCusp_iff_fst _ _).2 (by rw [vel_eq]; exact hφ0)
      have : (d.path t.1).vel (Fin.cast (d.c_eq t.1).symm i, φ) = 0 := hcusp
      rw [vel_eq] at this
      exact this
    have hinj : InjOn (fun u => det (pdI d i 2 (t, φ)) (pdI d i 0 (t, u)))
        (Ioo (u₀ - min r₁ ε₀) (u₀ + min r₁ ε₀)) := by
      refine injOn_of_third_deriv (hasDerivAt_det_pdI d (pdI d i 2 (t, φ)) i 0 t)
        (hasDerivAt_det_pdI d (pdI d i 2 (t, φ)) i 1 t)
        (hasDerivAt_det_pdI d (pdI d i 2 (t, φ)) i 2 t) hφ ?_ ?_ ?_
      · show det (pdI d i 2 (t, φ)) (pdI d i 1 (t, φ)) = 0
        rw [hv0]; unfold det; simp
      · show det (pdI d i 2 (t, φ)) (pdI d i 2 (t, φ)) = 0
        unfold det; ring
      · rcases lt_or_gt_of_ne hW0 with hneg | hpos
        · right; intro u hu; exact (hWbox u hu φ hφ).1.2 hneg
        · left; intro u hu; exact (hWbox u hu φ hφ).2.2 hpos
    intro u hu v hv huv
    exact hinj hu hv (by simp only [huv])
  · -- a regular point: `x` is strictly monotone nearby
    have ev := eventually_sign_iff (continuous_gx d i).continuousAt hreg
    rw [nhds_prod_eq, eventually_prod_iff] at ev
    obtain ⟨pa, hpa, pb, hpb, hab⟩ := ev
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hpb
    refine ⟨r, hr, hpa.mono fun t ht => ?_⟩
    have hx : ∀ u ∈ Ioo (u₀ - r) (u₀ + r),
        (gx d i (t, u) < 0 ↔ gx d i (t₀, u₀) < 0) ∧ (0 < gx d i (t, u) ↔ 0 < gx d i (t₀, u₀)) :=
      fun u hu => hab ht (hball (by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hu.1, hu.2]))
    have hderiv : ∀ u, HasDerivAt (fun u => (pdI d i 0 (t, u)).1) (gx d i (t, u)) u :=
      fun u => (hasDerivAt_pdI d i 0 t u).fst
    have hcont : Continuous (fun u => (pdI d i 0 (t, u)).1) :=
      continuous_iff_continuousAt.2 fun u => (hderiv u).continuousAt
    have hd : deriv (fun u => (pdI d i 0 (t, u)).1) = fun u => gx d i (t, u) :=
      funext fun u => (hderiv u).deriv
    have hinj : InjOn (fun u => (pdI d i 0 (t, u)).1) (Ioo (u₀ - r) (u₀ + r)) := by
      rcases lt_or_gt_of_ne hreg with hneg | hpos
      · refine (strictAntiOn_of_deriv_neg (convex_Ioo _ _) hcont.continuousOn ?_).injOn
        rw [interior_Ioo]; intro u hu; rw [hd]; exact (hx u hu).1.2 hneg
      · refine (strictMonoOn_of_deriv_pos (convex_Ioo _ _) hcont.continuousOn ?_).injOn
        rw [interior_Ioo]; intro u hu; rw [hd]; exact (hx u hu).2.2 hpos
    intro u hu v hv huv
    exact hinj hu hv (congrArg Prod.fst huv)

/-- **uniform local injectivity**: eventually, two parameters of `[-1, 2]` closer than `η` with the
same image on component `i` coincide -/
theorem uniform_injOn (i : Fin F.c) :
    ∃ η > 0, ∀ᶠ t in 𝓝 t₀, ∀ u v : ℝ, u ∈ Icc (-1 : ℝ) 2 → v ∈ Icc (-1 : ℝ) 2 → |u - v| < η →
      pdI d i 0 (t, u) = pdI d i 0 (t, v) → u = v := by
  choose r hr using injOn_near d t₀ i
  have hK : IsCompact (Icc (-1 : ℝ) 2) := isCompact_Icc
  obtain ⟨T, -, hcover⟩ := hK.elim_nhds_subcover
    (fun u₀ => Ioo (u₀ - r u₀ / 2) (u₀ + r u₀ / 2))
    (fun u₀ _ => Ioo_mem_nhds (by linarith [(hr u₀).1]) (by linarith [(hr u₀).1]))
  have hTne : T.Nonempty := by
    have : (-1 : ℝ) ∈ ⋃ u₀ ∈ T, Ioo (u₀ - r u₀ / 2) (u₀ + r u₀ / 2) := hcover ⟨le_rfl, by norm_num⟩
    obtain ⟨u₀, hu₀, -⟩ := mem_iUnion₂.1 this
    exact ⟨u₀, hu₀⟩
  obtain ⟨u₁, hu₁, hmin⟩ := T.exists_min_image (fun u₀ => r u₀ / 2) hTne
  refine ⟨r u₁ / 2, half_pos (hr u₁).1, ?_⟩
  have hall : ∀ᶠ t in 𝓝 t₀, ∀ u₀ ∈ T, InjOn (fun u => pdI d i 0 (t, u)) (Ioo (u₀ - r u₀) (u₀ + r u₀)) :=
    (Finset.eventually_all T).2 fun u₀ _ => (hr u₀).2
  refine hall.mono fun t ht u v hu hv huv heq => ?_
  obtain ⟨u₀, hu₀, hu'⟩ := mem_iUnion₂.1 (hcover hu)
  have hle := hmin u₀ hu₀
  have hu'' : u ∈ Ioo (u₀ - r u₀) (u₀ + r u₀) := by
    constructor <;> linarith [hu'.1, hu'.2, (hr u₀).1]
  have hv'' : v ∈ Ioo (u₀ - r u₀) (u₀ + r u₀) := by
    rw [abs_sub_lt_iff] at huv
    constructor <;> linarith [hu'.1, hu'.2, huv.1, huv.2]
  exact ht u₀ hu₀ hu'' hv'' heq

/-- the parameters within `η` (mod 1) of the diagonal -/
def nearDiag (η : ℝ) : Set (ℝ × ℝ) := {uv | ∃ m : ℤ, |uv.1 - uv.2 - m| < η}

omit d in
theorem isOpen_nearDiag (η : ℝ) : IsOpen (nearDiag η) := by
  have : nearDiag η = ⋃ m : ℤ, {uv : ℝ × ℝ | |uv.1 - uv.2 - m| < η} := by
    ext uv; simp [nearDiag]
  rw [this]
  exact isOpen_iUnion fun m => isOpen_lt (by fun_prop) continuous_const

/-- no new double points: eventually every double point of `path t` lies (mod 1) in the `ε`-box of a
double point of `path t₀` -/
theorem double_nonew (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ (t : I) in 𝓝 t₀, ∀ b : Param (d.path t.1).c × Param (d.path t.1).c, b ∈ (d.path t.1).doubleSet →
      ∃ a ∈ (d.path t₀.1).doubleSet, ∃ m n : ℤ, b.1.1 = ρ d t₀.1 t.1 a.1.1 ∧ b.2.1 = ρ d t₀.1 t.1 a.2.1 ∧
        (b.1.2 + m, b.2.2 + n) ∈ box ε a := by
  have key : ∀ i i' : Fin F.c, ∀ᶠ t in 𝓝 t₀, ∀ u v : ℝ, u ∈ Icc (0 : ℝ) 1 → v ∈ Icc (0 : ℝ) 1 →
      pdI d i 0 (t, u) = pdI d i' 0 (t, v) →
      (i = i' ∧ ∃ m : ℤ, u = v + m) ∨
      ∃ a ∈ (d.path t₀.1).doubleSet, Fin.cast (d.c_eq t₀.1) a.1.1 = i ∧ Fin.cast (d.c_eq t₀.1) a.2.1 = i' ∧
        ∃ m n : ℤ, (u + m, v + n) ∈ box ε a := by
    intro i i'
    obtain ⟨η, hη, hULI⟩ := uniform_injOn d t₀ i
    set T := (d.path t₀.1).doubleSet.filter
      (fun a => Fin.cast (d.c_eq t₀.1) a.1.1 = i ∧ Fin.cast (d.c_eq t₀.1) a.2.1 = i') with hT
    set Ω : Set (ℝ × ℝ) := ⋃ a ∈ T, near ε a.1.2 ×ˢ near ε a.2.2 with hΩ_def
    set Δ : Set (ℝ × ℝ) := {uv | i = i' ∧ uv ∈ nearDiag (min η 1)} with hΔ_def
    have hΩ : IsOpen Ω :=
      isOpen_iUnion fun a => isOpen_iUnion fun _ => (isOpen_near _ _).prod (isOpen_near _ _)
    have hΔ : IsOpen Δ := by
      by_cases hii : i = i'
      · have : Δ = nearDiag (min η 1) := by ext; simp [hΔ_def, hii]
        rw [this]; exact isOpen_nearDiag _
      · have : Δ = ∅ := by ext; simp [hΔ_def, hii]
        rw [this]; exact isOpen_empty
    set K : Set (ℝ × ℝ) := (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) \ (Ω ∪ Δ) with hK_def
    have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).diff (hΩ.union hΔ)
    have hK0 : ∀ uv ∈ K, Φ2 d i i' t₀ uv ≠ 0 := by
      rintro ⟨u, v⟩ ⟨⟨hu, hv⟩, hnot⟩ h0
      apply hnot
      set j : Fin (d.path t₀.1).c := Fin.cast (d.c_eq t₀.1).symm i with hj
      set j' : Fin (d.path t₀.1).c := Fin.cast (d.c_eq t₀.1).symm i' with hj'
      have he : (d.path t₀.1).eval (j, u) = (d.path t₀.1).eval (j', v) := by
        rw [eval_eq, eval_eq]; exact sub_eq_zero.1 h0
      by_cases hsp : SameParam (j, u) (j', v)
      · right
        obtain ⟨hjj, m, hm⟩ := hsp
        have hii : i = i' := by
          have h1 : j = j' := hjj
          rw [hj, hj'] at h1
          exact Fin.ext (by have := congrArg Fin.val h1; simpa using this)
        refine ⟨hii, -m, ?_⟩
        show |u - v - ((-m : ℤ) : ℝ)| < min η 1
        have hm' : v = u + m := hm
        have e : u - v - ((-m : ℤ) : ℝ) = 0 := by rw [hm']; push_cast; ring
        rw [e, abs_zero]; exact lt_min hη one_pos
      · left
        have hd : ((j, Int.fract u), (j', Int.fract v)) ∈ (d.path t₀.1).doubleSet := by
          rw [(d.path t₀.1).mem_doubleSet]
          refine ⟨⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩, ?_, ?_⟩
          · intro heq
            apply hsp
            have h1 : j = j' := congrArg Prod.fst heq
            have h2 : Int.fract u = Int.fract v := congrArg Prod.snd heq
            obtain ⟨z, hz⟩ := Int.fract_eq_fract.1 h2
            exact ⟨h1, -z, by push_cast; linarith⟩
          · show (d.path t₀.1).eval (j, Int.fract u) = (d.path t₀.1).eval (j', Int.fract v)
            rw [SmoothFront.eval_of_sameParam (⟨rfl, -⌊u⌋, fract_eq_add_int u⟩ : SameParam (j, u) (j, Int.fract u)),
              SmoothFront.eval_of_sameParam (⟨rfl, -⌊v⌋, fract_eq_add_int v⟩ : SameParam (j', v) (j', Int.fract v))]
            exact he
        refine mem_iUnion₂.2 ⟨_, Finset.mem_filter.2 ⟨hd, Fin.ext rfl, Fin.ext rfl⟩, ⟨-⌊u⌋, ?_⟩, ⟨-⌊v⌋, ?_⟩⟩
        · show u + ((-⌊u⌋ : ℤ) : ℝ) ∈ Ioo (Int.fract u - ε) (Int.fract u + ε)
          rw [← fract_eq_add_int]; exact ⟨by linarith, by linarith⟩
        · show v + ((-⌊v⌋ : ℤ) : ℝ) ∈ Ioo (Int.fract v - ε) (Int.fract v + ε)
          rw [← fract_eq_add_int]; exact ⟨by linarith, by linarith⟩
    have hev := hK.eventually_forall_of_forall_eventually (x₀ := t₀) (P := fun t uv => Φ2 d i i' t uv ≠ 0)
      (fun uv huv => (continuous_Φ2 d i i').continuousAt.eventually_ne (hK0 uv huv))
    filter_upwards [hev, hULI] with t ht hU u v hu hv heq
    by_cases hΔm : (u, v) ∈ Δ
    · left
      obtain ⟨hii, m, hm⟩ := hΔm
      refine ⟨hii, m, ?_⟩
      subst hii
      have hm1 : |u - v - m| < 1 := lt_of_lt_of_le hm (min_le_right _ _)
      have hmη : |u - v - m| < η := lt_of_lt_of_le hm (min_le_left _ _)
      have hvm : v + m ∈ Icc (-1 : ℝ) 2 := by
        rw [abs_sub_lt_iff] at hm1
        constructor <;> linarith [hu.1, hu.2, hv.1, hv.2, hm1.1, hm1.2]
      have hper : pdI d i 0 (t, v + m) = pdI d i 0 (t, v) := by
        rw [pdI_eq, pdI_eq, iteratedDeriv_zero]
        exact (comp d t.1 i).eq_add_int m v
      exact hU u (v + m) (Icc_subset_Icc (by norm_num) (by norm_num) hu) hvm
        (by rw [show u - (v + m) = u - v - m by ring]; exact hmη) (heq.trans hper.symm)
    · by_cases hΩm : (u, v) ∈ Ω
      · right
        obtain ⟨a, ha, hm⟩ := mem_iUnion₂.1 hΩm
        rw [Finset.mem_filter] at ha
        obtain ⟨⟨m, hm1⟩, ⟨n, hn1⟩⟩ := hm
        exact ⟨a, ha.1, ha.2.1, ha.2.2, m, n, hm1, hn1⟩
      · exfalso
        have hK' : (u, v) ∈ K := ⟨⟨hu, hv⟩, fun h => h.elim hΩm hΔm⟩
        exact ht (u, v) hK' (by unfold Φ2; rw [sub_eq_zero]; exact heq)
  have hall := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun i' => key i i'
  refine hall.mono fun t ht b hb => ?_
  have hb' := (d.path t.1).mem_doubleSet.1 hb
  have hne : ¬ SameParam b.1 b.2 := fun hs => hb'.2.2.1 (SameParam.eq_of_mem_Ico hb'.1 hb'.2.1 hs)
  have heq : pdI d (Fin.cast (d.c_eq t.1) b.1.1) 0 (t, b.1.2) =
      pdI d (Fin.cast (d.c_eq t.1) b.2.1) 0 (t, b.2.2) := by
    rw [← eval_eq, ← eval_eq]; exact hb'.2.2.2
  rcases ht _ _ b.1.2 b.2.2 (Ico_subset_Icc_self hb'.1) (Ico_subset_Icc_self hb'.2.1) heq with
    ⟨hii, m, hm⟩ | ⟨a, ha, h1, h2, m, n, hmn⟩
  · exfalso
    apply hne
    refine ⟨Fin.ext (by have := congrArg Fin.val hii; simpa using this), -m, ?_⟩
    push_cast; linarith
  · refine ⟨a, ha, m, n, ?_, ?_, hmn⟩
    · apply Fin.ext; have := congrArg Fin.val h1; simpa [ρ] using this.symm
    · apply Fin.ext; have := congrArg Fin.val h2; simpa [ρ] using this.symm

/-- **the local double-point hypotheses hold near every parameter** -/
theorem eventually_occHyp :
    ∃ ε, ∀ᶠ t in 𝓝 t₀, OccHyp (d.path t₀.1) (d.path t.1) (ρ d t₀.1 t.1) ε := by
  have E1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := eventually_mem_nhdsWithin
  have E2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ (d.path t₀.1).occSet, ∀ q ∈ (d.path t₀.1).occSet, p.1 = q.1 → p ≠ q →
      Sep ε (p.2 - q.2) := by
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ (d.path t₀.1).occSet_finite.toFinset, ∀ q ∈ (d.path t₀.1).occSet_finite.toFinset,
        p.1 = q.1 → p ≠ q → Sep ε (p.2 - q.2) := by
      refine (Finset.eventually_all _).2 fun p hp => (Finset.eventually_all _).2 fun q hq => ?_
      rw [Set.Finite.mem_toFinset] at hp hq
      by_cases hc : p.1 = q.1 ∧ p ≠ q
      · have hne : p.2 ≠ q.2 := fun h => hc.2 (Prod.ext hc.1 h)
        exact (eventually_sep (fract_sub_ne_zero hp.1 hq.1 hne)).mono fun ε h _ _ => h
      · exact Filter.Eventually.of_forall fun ε h1 h2 => absurd ⟨h1, h2⟩ hc
    exact this.mono fun ε h p hp q hq =>
      h p ((d.path t₀.1).occSet_finite.mem_toFinset.2 hp) q ((d.path t₀.1).occSet_finite.mem_toFinset.2 hq)
  have E3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ (d.path t₀.1).doubleSet, ∀ᶠ t in 𝓝 t₀, ∃! uv : ℝ × ℝ, uv ∈ box ε a ∧
      (d.path t.1).eval (ρ d t₀.1 t.1 a.1.1, uv.1) = (d.path t.1).eval (ρ d t₀.1 t.1 a.2.1, uv.2) := by
    refine (Finset.eventually_all (d.path t₀.1).doubleSet).2 fun a ha => ?_
    obtain ⟨ε₀, hε₀, H⟩ := double_persist d t₀ a ha
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hε₀) fun ε hε => H ε hε.1 hε.2.le
  have E4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ a ∈ (d.path t₀.1).doubleSet, ∀ᶠ t in 𝓝 t₀, ∀ uv ∈ box ε a,
      ((d.path t.1).slope (ρ d t₀.1 t.1 a.1.1, uv.1) < (d.path t.1).slope (ρ d t₀.1 t.1 a.2.1, uv.2) ↔
        (d.path t₀.1).slope a.1 < (d.path t₀.1).slope a.2) ∧
      (d.path t.1).crossSign (ρ d t₀.1 t.1 a.1.1, uv.1) (ρ d t₀.1 t.1 a.2.1, uv.2) =
        (d.path t₀.1).crossSign a.1 a.2 := by
    refine (Finset.eventually_all (d.path t₀.1).doubleSet).2 fun a ha => ?_
    obtain ⟨ε₁, hε₁, H⟩ := double_pres d t₀ a ha
    exact Filter.eventually_of_mem (Ioo_mem_nhdsGT hε₁) fun ε hε => H.mono fun t ht uv huv =>
      ht uv (box_mono hε.2.le a huv)
  obtain ⟨ε, hε1, hε2, hε3, hε4⟩ := (E1.and (E2.and (E3.and E4))).exists
  refine ⟨ε, ?_⟩
  filter_upwards [(Finset.eventually_all (d.path t₀.1).doubleSet).2 hε3, (Finset.eventually_all (d.path t₀.1).doubleSet).2 hε4,
    double_nonew d t₀ ε hε1] with t h3 h4 h5
  exact ⟨hε1, hε2, h3, h4, h5⟩

/-- **`w` is invariant** under a nonsingular deformation. -/
theorem writhe_eq_of_deformation : F.writhe = F'.writhe := by
  have hlc : IsLocallyConstant (fun t : I => (d.path t.1).writhe) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨ε, hε⟩ := eventually_occHyp d t₀
    exact hε.mono fun t ht => ht.toFrontRecEquiv.writhe_eq.symm
  have h := hlc.apply_eq_of_preconnectedSpace (⟨0, by norm_num⟩ : I) (⟨1, by norm_num⟩ : I)
  have h0 : d.path (⟨0, by norm_num⟩ : I).1 = F := d.start
  have h1 : d.path (⟨1, by norm_num⟩ : I).1 = F' := d.stop
  simp only [h0, h1] at h
  exact h

/-- **the polygonal readings transport** along a nonsingular deformation. -/
theorem marking_nonempty_of_deformation (S : Diagram) (hS : Nonempty (F.Marking S)) :
    Nonempty (F'.Marking S) := by
  have hlc : IsLocallyConstant (fun t : I => decide (Nonempty ((d.path t.1).Marking S))) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t₀
    obtain ⟨ε, hε⟩ := eventually_occHyp d t₀
    refine hε.mono fun t ht => ?_
    have ι := ht.toFrontRecEquiv
    apply decide_eq_decide.2
    exact ⟨fun ⟨m⟩ => ⟨transportMarking ι m⟩, fun ⟨m⟩ => ⟨transportMarking ι.symm m⟩⟩
  have h := hlc.apply_eq_of_preconnectedSpace (⟨0, by norm_num⟩ : I) (⟨1, by norm_num⟩ : I)
  have h0 : d.path (⟨0, by norm_num⟩ : I).1 = F := d.start
  have h1 : d.path (⟨1, by norm_num⟩ : I).1 = F' := d.stop
  simp only [h0, h1] at h
  exact (decide_eq_decide.1 h).1 hS

/-- **`P` of the roundings is invariant** under a nonsingular deformation. -/
theorem P_eq_of_deformation (S S' : Diagram) (hS : F.IsRounding S) (hS' : F'.IsRounding S') :
    P S = P S' := by
  obtain ⟨m⟩ := marking_nonempty_of_deformation d S hS.marking_nonempty
  obtain ⟨ρ'⟩ := hS'
  have hS'' : F'.IsRounding S := ⟨⟨ρ'.G, ρ'.geom, m⟩⟩
  exact hS''.P_eq ⟨ρ'⟩

end DoubleAnalysis

end

end U8D

/-- LEAF (ng:commutation, sm-3:1934-1936 "A deformation without a singular event preserves the records, D and
w: signs, cusp directions and cyclic attachments cannot change"): `D`.  Along a jointly smooth family inside
the class, the cusp set `{x' = 0}` is a covering of `[0,1]` (`x'' ≠ 0` at every zero, vertical tangencies
excluded), on which the discriminant `x''·det(γ'', γ''')` is continuous and nonzero. -/
theorem deform_downCount (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.downCount = F'.downCount := h.elim fun d => U8D.downCount_eq_of_deformation d

/-- LEAF: the same for `w` (the transverse double points form a covering of `[0,1]`, no accumulation at a
semicubical cusp, `crossSign` continuous and nonzero). -/
theorem deform_writhe (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.writhe = F'.writhe := h.elim fun d => U8D.writhe_eq_of_deformation d

/-- LEAF: the same for the records of the roundings, hence (sm-3:1936-1937 "Lemma rp:record-polynomial gives
scalar equality") the polynomial: the `Marking` of `F` transports along the family to a `Marking` of `F'`. -/
theorem deform_P (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) (S S' : Diagram)
    (hS : F.IsRounding S) (hS' : F'.IsRounding S') : P S = P S' :=
  h.elim fun d => U8D.P_eq_of_deformation d S S' hS hS'

/-! ### U8R infrastructure — the representation leaf `represent` (unit U8R; PLAN_FINAL.md §4 "L-smooth",
§5 "U8 smooth"; plan and status in W2_U8R_REPORT.md).  The leaf is reduced to ONE remaining statement, the
sweep (`U8R.SweepStatement`): every rounding `S(F)` carries the named record of `F` itself (`U8R.frontRecord`,
def:gauss-record read on `F.Occ`; `U8R.markingRecordIso : Marking F S → RecordIso S.record (frontRecord F)`),
that record has `w(F)` and the crossing count of `F` (`frontRecord_writhe`, `frontRecord_crossingCount`), and
the realization of a word carries U2's slot record (`U2.realizeRecordIso`); so a word `W` represents `F` as
soon as its letter-traced down count is `D(F)`, its cusp letters are the cusps of `F`, and
`frontRecord F ≅ U2.slotRecord W` (`U8R.represent_of_slotRecordIso`, `U8R.represent_of_sweepStatement`).
A: the cyclic successor on a finite type with real keys (one cycle per fibre; the `Diagram.nextVisit`
construction made generic, with its characterisation `cycNext_eq_of`); B: `frontRecord`; B': its counts;
C: `markingRecordIso`; D-E: the reductions; F-H: analytic groundwork for the sweep (the x-velocity along a
circle, its constant sign between cusps and its sign change at a cusp, the finite set of singular x-values;
the cusp arcs — consecutive cusps alternate left/right, `x` is strictly monotone on each arc, the arcs cover
the circle, the fibre over any `x₀` is finite). -/
section U8RInfra

namespace U8R

open Equiv

noncomputable section

/-! #### A. The cyclic successor on a finite type with real keys, one cycle per fibre -/

section CycSucc

variable {α ι : Type*} [Fintype α] [DecidableEq α] [LinearOrder ι]
variable (comp : α → ι) (key : α → ℝ)
variable (hkey : ∀ a b, comp a = comp b → key a = key b → a = b)

/-- the lexicographic key `(fibre, real key)` -/
def lexKey (a : α) : ι ×ₗ ℝ := toLex (comp a, key a)

include hkey in
theorem lexKey_injective : Function.Injective (lexKey comp key) := by
  intro a b h
  have h' : (comp a, key a) = (comp b, key b) := toLex.injective h
  rw [Prod.mk.injEq] at h'
  exact hkey a b h'.1 h'.2

/-- the auxiliary linear order lifted from `lexKey` -/
@[instance_reducible]
def keyOrder : LinearOrder α := LinearOrder.lift' (lexKey comp key) (lexKey_injective comp key hkey)

theorem keyOrder_lt_iff {a b : α} (hc : comp a = comp b) :
    (letI := keyOrder comp key hkey; a < b) ↔ key a < key b := by
  let _ := keyOrder comp key hkey
  change lexKey comp key a < lexKey comp key b ↔ _
  unfold lexKey
  rw [Prod.Lex.lt_iff]
  simp only [ofLex_toLex, hc, lt_self_iff_false, false_or, true_and]

/-- the fibre of `i` -/
def fib (i : ι) : Finset α := Finset.univ.filter (fun a => comp a = i)

theorem mem_fib (i : ι) (a : α) : a ∈ fib comp i ↔ comp a = i := by simp [fib]

/-- the fibre sorted by key -/
def fibList (i : ι) : List α :=
  letI := keyOrder comp key hkey
  (fib comp i).sort

theorem fibList_nodup (i : ι) : (fibList comp key hkey i).Nodup := by
  let _ := keyOrder comp key hkey
  exact Finset.sort_nodup _ _

theorem mem_fibList (i : ι) (a : α) : a ∈ fibList comp key hkey i ↔ comp a = i := by
  let _ := keyOrder comp key hkey
  rw [fibList, Finset.mem_sort, mem_fib]

theorem self_mem_fibList (a : α) : a ∈ fibList comp key hkey (comp a) :=
  (mem_fibList comp key hkey _ a).mpr rfl

/-- the cyclic successor within the fibre -/
def cycNext (a : α) : α :=
  (fibList comp key hkey (comp a)).next a (self_mem_fibList comp key hkey a)

/-- the cyclic predecessor within the fibre -/
def cycPrev (a : α) : α :=
  (fibList comp key hkey (comp a)).prev a (self_mem_fibList comp key hkey a)

theorem cycNext_eq (a : α) {i : ι} (hi : comp a = i) (ha : a ∈ fibList comp key hkey i) :
    cycNext comp key hkey a = (fibList comp key hkey i).next a ha := by
  subst hi; rfl

theorem cycPrev_eq (a : α) {i : ι} (hi : comp a = i) (ha : a ∈ fibList comp key hkey i) :
    cycPrev comp key hkey a = (fibList comp key hkey i).prev a ha := by
  subst hi; rfl

theorem comp_cycNext (a : α) : comp (cycNext comp key hkey a) = comp a :=
  (mem_fibList comp key hkey _ _).mp (List.next_mem _ _ _)

theorem comp_cycPrev (a : α) : comp (cycPrev comp key hkey a) = comp a :=
  (mem_fibList comp key hkey _ _).mp (List.prev_mem _ _ _)

theorem cycPrev_cycNext (a : α) : cycPrev comp key hkey (cycNext comp key hkey a) = a := by
  rw [cycPrev_eq comp key hkey (cycNext comp key hkey a) (comp_cycNext comp key hkey a) (List.next_mem _ _ _)]
  exact List.prev_next _ (fibList_nodup comp key hkey _) a _

theorem cycNext_cycPrev (a : α) : cycNext comp key hkey (cycPrev comp key hkey a) = a := by
  rw [cycNext_eq comp key hkey (cycPrev comp key hkey a) (comp_cycPrev comp key hkey a) (List.prev_mem _ _ _)]
  exact List.next_prev _ (fibList_nodup comp key hkey _) a _

/-- the cyclic successor as a permutation -/
def cycSucc : Perm α where
  toFun := cycNext comp key hkey
  invFun := cycPrev comp key hkey
  left_inv := cycPrev_cycNext comp key hkey
  right_inv := cycNext_cycPrev comp key hkey

@[simp] theorem cycSucc_apply (a : α) : cycSucc comp key hkey a = cycNext comp key hkey a := rfl

theorem comp_cycSucc (a : α) : comp (cycSucc comp key hkey a) = comp a := comp_cycNext comp key hkey a

theorem cycNext_getElem (i : ι) (j : ℕ) (hj : j < (fibList comp key hkey i).length) :
    cycNext comp key hkey ((fibList comp key hkey i)[j]'hj) =
      (fibList comp key hkey i)[(j + 1) % (fibList comp key hkey i).length]'
        (Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le j) hj)) := by
  rw [cycNext_eq comp key hkey _ ((mem_fibList comp key hkey i _).mp (List.getElem_mem hj)) (List.getElem_mem hj)]
  exact List.next_getElem (fibList comp key hkey i) (fibList_nodup comp key hkey i) j hj

theorem cycSucc_sameCycle_getElem (i : ι) (j : ℕ) (hj : j < (fibList comp key hkey i).length) :
    (cycSucc comp key hkey).SameCycle ((fibList comp key hkey i)[(0 : ℕ)]'(lt_of_le_of_lt (Nat.zero_le j) hj))
      ((fibList comp key hkey i)[j]'hj) := by
  revert hj
  induction j with
  | zero => intro hj; exact Perm.SameCycle.refl _ _
  | succ j ih =>
    intro hj
    have hj' : j < (fibList comp key hkey i).length := (Nat.lt_succ_self j).trans hj
    have hc := Perm.sameCycle_apply_right.mpr (ih hj')
    rw [cycSucc_apply, cycNext_getElem comp key hkey i j hj'] at hc
    simpa only [Nat.mod_eq_of_lt hj] using hc

/-- one cycle per fibre -/
theorem cycSucc_sameCycle {a b : α} (h : comp a = comp b) : (cycSucc comp key hkey).SameCycle a b := by
  obtain ⟨j, hj, ha⟩ := List.getElem_of_mem (self_mem_fibList comp key hkey a)
  obtain ⟨k, hk, hb⟩ := List.getElem_of_mem ((mem_fibList comp key hkey (comp a) b).mpr h.symm)
  rw [← ha, ← hb]
  exact (cycSucc_sameCycle_getElem comp key hkey _ j hj).symm.trans (cycSucc_sameCycle_getElem comp key hkey _ k hk)

/-- no element of the fibre lies strictly between an element and its cyclic successor -/
theorem cycNext_no_between (a u : α) (hu : comp u = comp a) :
    ¬ cycBetween (key a) (key u) (key (cycNext comp key hkey a)) := by
  let _ := keyOrder comp key hkey
  have hd : (fun x y : α => LinearOrder.toDecidableEq x y) = (inferInstance : DecidableEq α) :=
    Subsingleton.elim _ _
  have hnext : @List.next α (fun x y : α => LinearOrder.toDecidableEq x y) (fib comp (comp a)).sort a
      ((Finset.mem_sort _).mpr ((mem_fib comp _ a).mpr rfl)) = cycNext comp key hkey a := by
    rw [hd]; rfl
  have hg := sorted_next_no_cyclic_between (fib comp (comp a))
    ((mem_fib comp _ a).mpr rfl) ((mem_fib comp _ _).mpr (comp_cycNext comp key hkey a)) hnext u
    ((mem_fib comp _ u).mpr hu)
  have e1 := keyOrder_lt_iff comp key hkey (a := a) (b := u) hu.symm
  have e2 := keyOrder_lt_iff comp key hkey (a := u) (b := cycNext comp key hkey a)
    (hu.trans (comp_cycNext comp key hkey a).symm)
  have e3 := keyOrder_lt_iff comp key hkey (a := cycNext comp key hkey a) (b := a) (comp_cycNext comp key hkey a)
  unfold cycBetween
  rw [e1, e2, e3] at hg
  exact hg

/-- the cyclic successor differs from the element unless it is alone in its fibre -/
theorem cycNext_ne_self (a w : α) (hw : comp w = comp a) (hne : w ≠ a) : cycNext comp key hkey a ≠ a := by
  apply list_next_ne_self _ (fibList_nodup comp key hkey _)
  have h1 : a ∈ fibList comp key hkey (comp a) := self_mem_fibList comp key hkey a
  have h2 : w ∈ fibList comp key hkey (comp a) := (mem_fibList comp key hkey _ w).mpr hw
  have hpos := List.length_pos_of_mem h1
  rcases Nat.lt_or_ge (fibList comp key hkey (comp a)).length 2 with hlt | hge
  · exfalso
    have hlen : (fibList comp key hkey (comp a)).length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx, List.mem_singleton] at h1 h2
    exact hne (h2.trans h1.symm)
  · exact hge

/-- an element alone in its fibre is its own cyclic successor -/
theorem cycNext_eq_self (a : α) (h : ∀ w, comp w = comp a → w = a) : cycNext comp key hkey a = a := by
  have hl : fibList comp key hkey (comp a) = [a] := by
    have hsub : ∀ w ∈ fibList comp key hkey (comp a), w = a :=
      fun w hw => h w ((mem_fibList comp key hkey _ w).mp hw)
    have hmem := self_mem_fibList comp key hkey a
    have hlen : (fibList comp key hkey (comp a)).length = 1 := by
      have hnd := fibList_nodup comp key hkey (comp a)
      by_contra hne
      have hpos := List.length_pos_of_mem hmem
      have h2 : 2 ≤ (fibList comp key hkey (comp a)).length := by omega
      have hne' := list_next_ne_self _ hnd h2 a hmem
      exact hne' (hsub _ (List.next_mem _ _ _))
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx] at hmem ⊢
    rw [List.mem_singleton] at hmem
    rw [hmem]
  have key' : ∀ (l : List α) (hl' : l = [a]) (ha : a ∈ l), l.next a ha = a := by
    rintro l rfl ha
    exact List.next_singleton a a ha
  exact key' _ hl _

/-- THE CHARACTERISATION: an element `b` of the fibre of `a` which differs from `a` whenever the fibre has
another element, and with nothing of the fibre strictly between `a` and `b`, is the cyclic successor. -/
theorem cycNext_eq_of (a b : α) (hb : comp b = comp a)
    (hne : ∀ w, comp w = comp a → w ≠ a → b ≠ a)
    (hbetw : ∀ u, comp u = comp a → ¬ cycBetween (key a) (key u) (key b)) :
    cycNext comp key hkey a = b := by
  by_cases hsingle : ∀ w, comp w = comp a → w = a
  · rw [cycNext_eq_self comp key hkey a hsingle]
    exact (hsingle b hb).symm
  · push Not at hsingle
    obtain ⟨w, hw, hwa⟩ := hsingle
    exact cycNext_unique_on (p := fun u => comp u = comp a) (k := key)
      (fun x y hx hy hk => hkey x y (hx.trans hy.symm) hk) rfl (comp_cycNext comp key hkey a) hb
      (cycNext_ne_self comp key hkey a w hw hwa) (hne w hw hwa)
      (fun u hu => cycNext_no_between comp key hkey a u hu) hbetw

end CycSucc

/-! #### B. The named record of a smooth front itself (def:gauss-record read on `F.Occ`) -/

section FrontRecord

variable (F : SmoothFront)

/-- the partner of a crossing occurrence: the other branch of its double point -/
def partner (p : F.Occ) : F.Occ := Classical.choose (SmoothFront.Marking.exists_partner p)

theorem partner_spec (p : F.Occ) : p ≠ partner F p ∧ F.eval p = F.eval (partner F p) :=
  Classical.choose_spec (SmoothFront.Marking.exists_partner p)

theorem partner_ne (p : F.Occ) : partner F p ≠ p := (partner_spec F p).1.symm

theorem eval_partner (p : F.Occ) : F.eval (partner F p) = F.eval p := (partner_spec F p).2.symm

theorem isDouble_partner (p : F.Occ) : F.IsDouble p.1 (partner F p).1 :=
  SmoothFront.Occ.isDouble_of_ne F (partner_spec F p).1 (partner_spec F p).2

/-- the partner is unique (`no_triple`) -/
theorem eq_partner_of {p q : F.Occ} (hne : p ≠ q) (he : F.eval p = F.eval q) : q = partner F p := by
  by_contra hqr
  obtain ⟨hpr, hpr'⟩ := partner_spec F p
  exact F.no_triple q.1 p.1 (partner F p).1 (SmoothFront.Occ.not_sameParam_of_ne hne.symm)
    (SmoothFront.Occ.not_sameParam_of_ne hpr) (SmoothFront.Occ.not_sameParam_of_ne hqr) he.symm hpr'

theorem partner_partner (p : F.Occ) : partner F (partner F p) = p :=
  (eq_partner_of F (partner_ne F p) (eval_partner F p)).symm

/-- the pairing involution -/
def partnerPerm : Perm F.Occ where
  toFun := partner F
  invFun := partner F
  left_inv := partner_partner F
  right_inv := partner_partner F

@[simp] theorem partnerPerm_apply (p : F.Occ) : partnerPerm F p = partner F p := rfl

/-- the circle of an occurrence -/
def occComp (p : F.Occ) : Fin F.c := p.1.1
/-- the parameter of an occurrence (in `[0,1)`) -/
def occKey (p : F.Occ) : ℝ := p.1.2

theorem occKey_inj (a b : F.Occ) (h1 : occComp F a = occComp F b) (h2 : occKey F a = occKey F b) : a = b :=
  Subtype.ext (Prod.ext h1 h2)

/-- the over bit: over = smaller slope -/
def frontOver (p : F.Occ) : Bool := decide (F.slope p.1 < F.slope (partner F p).1)

/-- the sign: the over-first tangent-determinant sign -/
def frontSgn (p : F.Occ) : SignType :=
  if F.slope p.1 < F.slope (partner F p).1 then SignType.sign (det (F.vel p.1) (F.vel (partner F p).1))
  else SignType.sign (det (F.vel (partner F p).1) (F.vel p.1))

theorem slope_ne_partner (p : F.Occ) : F.slope p.1 ≠ F.slope (partner F p).1 :=
  F.slope_ne_of_isDouble (isDouble_partner F p)

theorem frontOver_partner (p : F.Occ) : frontOver F (partner F p) = !frontOver F p := by
  unfold frontOver
  rw [partner_partner]
  by_cases h : F.slope p.1 < F.slope (partner F p).1
  · simp [h, lt_asymm h]
  · have h' : F.slope (partner F p).1 < F.slope p.1 :=
      lt_of_le_of_ne (not_lt.mp h) (slope_ne_partner F p).symm
    simp [h, h']

theorem frontSgn_partner (p : F.Occ) : frontSgn F (partner F p) = frontSgn F p := by
  unfold frontSgn
  rw [partner_partner]
  by_cases h : F.slope p.1 < F.slope (partner F p).1
  · simp [h, lt_asymm h]
  · have h' : F.slope (partner F p).1 < F.slope p.1 :=
      lt_of_le_of_ne (not_lt.mp h) (slope_ne_partner F p).symm
    simp [h, h']

theorem frontSgn_ne_zero (p : F.Occ) : frontSgn F p ≠ 0 := by
  unfold frontSgn
  have h1 := F.det_vel_ne_zero_of_isDouble (isDouble_partner F p)
  have h2 := F.det_vel_ne_zero_of_isDouble (isDouble_partner F p).symm
  split_ifs
  · exact sign_ne_zero.mpr h1
  · exact sign_ne_zero.mpr h2

/-- THE NAMED RECORD OF THE FRONT `F` (def:gauss-record read on the front's own occurrences, the
"named record of `F`" that every rounding `S(F)` carries by FR-1): circles `Fin F.c`, occurrences `F.Occ`,
successor = the cyclic successor of the parameters on each circle, pairing = the partner of the double
point, over = smaller slope, sign = the over-first tangent-determinant sign. -/
def frontRecord : Record where
  comps := Fin F.c
  M := F.Occ
  comp := occComp F
  succ := cycSucc (occComp F) (occKey F) (occKey_inj F)
  pair := partnerPerm F
  isOver := frontOver F
  sgn := frontSgn F
  succ_comp := comp_cycSucc (occComp F) (occKey F) (occKey_inj F)
  succ_cycle _ _ h := cycSucc_sameCycle (occComp F) (occKey F) (occKey_inj F) h
  pair_ne := partner_ne F
  pair_invol := partner_partner F
  bit_pair := frontOver_partner F
  sgn_pair := frontSgn_partner F
  sgn_ne := frontSgn_ne_zero F

@[simp] theorem frontRecord_comps : (frontRecord F).comps = Fin F.c := rfl
@[simp] theorem frontRecord_M : (frontRecord F).M = F.Occ := rfl
theorem frontRecord_comp (p : F.Occ) : (frontRecord F).comp p = p.1.1 := rfl
theorem frontRecord_succ (p : F.Occ) :
    (frontRecord F).succ p = cycNext (occComp F) (occKey F) (occKey_inj F) p := rfl
theorem frontRecord_pair (p : F.Occ) : (frontRecord F).pair p = partner F p := rfl
theorem frontRecord_isOver (p : F.Occ) : (frontRecord F).isOver p = frontOver F p := rfl
theorem frontRecord_sgn (p : F.Occ) : (frontRecord F).sgn p = frontSgn F p := rfl

end FrontRecord


/-! #### B'. The record of `F` has the writhe and the crossing count of `F` -/

section FrontRecordCounts

variable (F : SmoothFront)

theorem fst_mem_occSet_of_mem_crossingPairs {q : Param F.c × Param F.c} (hq : q ∈ F.crossingPairs) :
    q.1 ∈ F.occSet :=
  F.fst_mem_occSet_of_mem_doubleSet (F.crossingPairs_subset_doubleSet hq)

theorem partner_val_of_mem_crossingPairs {q : Param F.c × Param F.c} (hq : q ∈ F.crossingPairs) :
    (partner F ⟨q.1, fst_mem_occSet_of_mem_crossingPairs F hq⟩).1 = q.2 := by
  have hd := F.isDouble_of_mem_doubleSet (F.crossingPairs_subset_doubleSet hq)
  have hq2 : q.2 ∈ F.occSet := F.snd_mem_occSet_of_mem_doubleSet (F.crossingPairs_subset_doubleSet hq)
  have h := eq_partner_of F (p := ⟨q.1, fst_mem_occSet_of_mem_crossingPairs F hq⟩) (q := ⟨q.2, hq2⟩)
    (fun h => hd.1 (by
      have h' : q.1 = q.2 := congrArg Subtype.val h
      rw [h']; exact SameParam.refl _)) hd.2
  rw [← h]

theorem frontOver_of_mem_crossingPairs {q : Param F.c × Param F.c} (hq : q ∈ F.crossingPairs) :
    frontOver F ⟨q.1, fst_mem_occSet_of_mem_crossingPairs F hq⟩ = true := by
  unfold frontOver
  rw [decide_eq_true_iff, partner_val_of_mem_crossingPairs F hq]
  exact (F.mem_crossingPairs.mp hq).2

theorem over_pair_mem_crossingPairs (p : F.Occ) (hp : frontOver F p = true) :
    (p.1, (partner F p).1) ∈ F.crossingPairs := by
  rw [SmoothFront.mem_crossingPairs, SmoothFront.mem_doubleSet]
  refine ⟨⟨p.2.1, (partner F p).2.1, fun h => (partner_spec F p).1 (Subtype.ext h), (partner_spec F p).2⟩, ?_⟩
  unfold frontOver at hp
  exact decide_eq_true_iff.mp hp

/-- the over occurrences are the crossings (over-first pairs) -/
theorem sum_over_eq_sum_crossingPairs (g : Param F.c × Param F.c → ℤ) :
    ∑ p ∈ Finset.univ.filter (fun p : F.Occ => frontOver F p = true), g (p.1, (partner F p).1) =
      ∑ q ∈ F.crossingPairs, g q := by
  refine Finset.sum_bij' (fun p _ => (p.1, (partner F p).1))
    (fun q hq => ⟨q.1, fst_mem_occSet_of_mem_crossingPairs F hq⟩) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    exact over_pair_mem_crossingPairs F p (by simpa using hp)
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact frontOver_of_mem_crossingPairs F hq
  · intro p _; rfl
  · intro q hq
    exact Prod.ext rfl (partner_val_of_mem_crossingPairs F hq)
  · intro p _; rfl

/-- the record of `F` has the writhe of `F` -/
theorem frontRecord_writhe : (frontRecord F).writhe = F.writhe := by
  rw [Record.writhe_eq_sum_over]
  show ∑ p ∈ Finset.univ.filter (fun p : F.Occ => frontOver F p = true), ((frontSgn F p : SignType) : ℤ) =
    ∑ q ∈ F.crossingPairs, F.crossSign q.1 q.2
  rw [← sum_over_eq_sum_crossingPairs F (fun q => F.crossSign q.1 q.2)]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, frontOver, decide_eq_true_iff] at hp
  simp only [frontSgn, hp, ↓reduceIte]
  rw [F.crossSign_eq_sign (isDouble_partner F p)]

/-- the record of `F` has the crossing count of `F` -/
theorem frontRecord_crossingCount : (frontRecord F).crossingCount = F.crossingPairs.card := by
  have h := (frontRecord F).sum_eq_two_mul_sum_over (fun _ => (1 : ℤ)) (fun _ => rfl)
  have h2 := sum_over_eq_sum_crossingPairs F (fun _ => (1 : ℤ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ] at h h2
  have h' : Fintype.card F.Occ =
      2 * (Finset.univ.filter (fun p : F.Occ => frontOver F p = true)).card := by exact_mod_cast h
  have h2' : (Finset.univ.filter (fun p : F.Occ => frontOver F p = true)).card = F.crossingPairs.card := by
    exact_mod_cast h2
  show Fintype.card F.Occ / 2 = F.crossingPairs.card
  omega

end FrontRecordCounts

/-! #### C. Every polygonal reading of `F` (a `Marking`) is a named record isomorphism with `frontRecord F` -/

section MarkingIso

variable {F : SmoothFront} {S : Diagram}

/-- a `Marking F S` is a named record isomorphism `S.record ≅ frontRecord F` -/
def markingRecordIso (m : F.Marking S) : RecordIso S.record (frontRecord F) where
  e := m.e.symm
  Φ := m.Φ.symm
  comp_eq v := by
    show (m.Φ.symm v).1.1 = m.e.symm (S.compOf v)
    rw [m.compOf_eq_e v, Equiv.symm_apply_apply]
  succ_eq v := by
    show m.Φ.symm (S.nextVisit v) = cycNext (occComp F) (occKey F) (occKey_inj F) (m.Φ.symm v)
    symm
    apply cycNext_eq_of
    · show (m.Φ.symm (S.nextVisit v)).1.1 = (m.Φ.symm v).1.1
      exact (m.compOf_eq_iff _ _).mp (S.compOf_nextVisit v)
    · intro w hw hwv heq
      have hw' : S.compOf (m.Φ w) = S.compOf v := by
        rw [m.compOf_eq_iff, Equiv.symm_apply_apply]; exact hw
      have hne' : m.Φ w ≠ v := fun h => hwv (by rw [← h, Equiv.symm_apply_apply])
      apply S.nextVisit_ne_self v (m.Φ w) hw' hne'
      have := congrArg m.Φ heq
      rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this
    · intro u hu
      have hu' : S.compOf (m.Φ u) = S.compOf v := by
        rw [m.compOf_eq_iff, Equiv.symm_apply_apply]; exact hu
      have h := m.between_iff (m.Φ.symm v) u (m.Φ.symm (S.nextVisit v)) hu.symm
        (hu.trans ((m.compOf_eq_iff _ _).mp (S.compOf_nextVisit v)).symm)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
      show ¬ cycBetween (m.Φ.symm v).1.2 u.1.2 (m.Φ.symm (S.nextVisit v)).1.2
      rw [h]
      exact S.not_visitBetween_nextVisit v (m.Φ u) hu'
  pair_eq v := by
    show m.Φ.symm (S.twin v) = partner F (m.Φ.symm v)
    have hΦ : m.Φ (m.Φ.symm (S.twin v)) = S.twin (m.Φ (m.Φ.symm v)) := by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    obtain ⟨hne, he⟩ := m.partner_of_Φ_eq_twin hΦ
    exact eq_partner_of F hne he
  bit_eq v := by
    show frontOver F (m.Φ.symm v) = S.overBit v
    have h := m.over_iff (m.Φ.symm v) (partner F (m.Φ.symm v)) (partner_spec F _).1 (partner_spec F _).2
    rw [Equiv.apply_symm_apply] at h
    unfold frontOver
    rcases Bool.eq_false_or_eq_true (S.overBit v) with hb | hb
    · rw [hb, decide_eq_true_iff]; exact h.mp hb
    · rw [hb, decide_eq_false_iff_not]; intro h'; rw [← h] at h'; rw [h'] at hb; exact Bool.noConfusion hb
  sgn_eq v := by
    show frontSgn F (m.Φ.symm v) = S.sign v.1
    set p := m.Φ.symm v with hp
    have hv : m.Φ p = v := Equiv.apply_symm_apply _ _
    obtain ⟨hne, he⟩ := partner_spec F p
    have hd : F.IsDouble p.1 (partner F p).1 := isDouble_partner F p
    apply signType_intCast_injective
    unfold frontSgn
    by_cases hs : F.slope p.1 < F.slope (partner F p).1
    · simp only [hs, ↓reduceIte]
      have h1 := m.sgn_eq p (partner F p) hne he hs
      rw [hv, F.crossSign_eq_sign hd] at h1
      exact h1.symm
    · simp only [hs, ↓reduceIte]
      have hs' : F.slope (partner F p).1 < F.slope p.1 :=
        lt_of_le_of_ne (not_lt.mp hs) (slope_ne_partner F p).symm
      have h1 := m.sgn_eq (partner F p) p hne.symm he.symm hs'
      have e1 : (m.Φ (partner F p)).1 = v.1 := by rw [m.pair_eq p (partner F p) hne he, S.twin_fst, hv]
      rw [e1, F.crossSign_eq_sign hd.symm] at h1
      exact h1.symm

@[simp] theorem markingRecordIso_e (m : F.Marking S) (i : Fin S.Γ.c) : (markingRecordIso m).e i = m.e.symm i := rfl
@[simp] theorem markingRecordIso_Φ (m : F.Marking S) (v : S.Γ.Visit) : (markingRecordIso m).Φ v = m.Φ.symm v := rfl

/-- every rounding `S(F)` has the named record of `F` -/
theorem IsRounding.recordIso_frontRecord (h : F.IsRounding S) : Nonempty (RecordIso S.record (frontRecord F)) :=
  h.elim fun ρ => ⟨markingRecordIso ρ.marking⟩

end MarkingIso

/-! #### D. The reduction of `represent` to a word with the syntactic counts and the record of `F` -/

section Reduction

variable (F : SmoothFront)

/-- The representation clause for a word `W` follows from the syntactic counts (`realize_downCount`,
`realize_writhe`, `realize_sCount`) and a named record isomorphism `frontRecord F ≅ (realize W).diagram.record`:
every rounding carries `frontRecord F` (`markingRecordIso`). -/
theorem represent_of_frontRecordIso (W : OWord) (hne : W.letters ≠ [])
    (hD : F.downCount = W.downCountSyn) (hw : F.writhe = W.writheSyn) (hs : F.sCount = W.sCountSyn)
    (hrec : Nonempty (RecordIso (frontRecord F) (realize W).diagram.record)) :
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
      ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) := by
  refine ⟨by rw [realize_downCount W hne]; exact hD, by rw [realize_writhe W hne]; exact hw,
    by rw [realize_sCount W hne]; exact hs, fun S hS => ?_⟩
  obtain ⟨ρ⟩ := hS
  obtain ⟨ι⟩ := hrec
  exact ⟨(markingRecordIso ρ.marking).trans ι⟩

/-- the same through a `Marking` of the realization -/
theorem represent_of_marking (W : OWord) (hne : W.letters ≠ [])
    (hD : F.downCount = W.downCountSyn) (hw : F.writhe = W.writheSyn) (hs : F.sCount = W.sCountSyn)
    (hm : Nonempty (F.Marking (realize W).diagram)) :
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
      ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) :=
  represent_of_frontRecordIso F W hne hD hw hs (hm.map fun m => (markingRecordIso m).symm)

/-- The representation clause from the geometric counts `D`, `#cusps` alone and the record isomorphism:
`w` and the crossing count are carried by the named record (`frontRecord_writhe`, `frontRecord_crossingCount`,
`RecordIso.writhe_eq`, `RecordIso.crossingCount_eq`, `Diagram.record_writhe`, `Diagram.record_crossingCount`). -/
theorem represent_of_frontRecordIso_counts (W : OWord)
    (hD : F.downCount = (realize W).downCount) (hcusp : F.cuspSet.card = (realize W).cuspCount)
    (hrec : Nonempty (RecordIso (frontRecord F) (realize W).diagram.record)) :
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
      ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) := by
  obtain ⟨ι⟩ := hrec
  refine ⟨hD, ?_, ?_, fun S hS => hS.elim fun ρ => ⟨(markingRecordIso ρ.marking).trans ι⟩⟩
  · rw [← frontRecord_writhe F, ι.writhe_eq, Diagram.record_writhe]
    rfl
  · unfold SmoothFront.sCount PLFront.sCount
    rw [← frontRecord_crossingCount F, ι.crossingCount_eq, Diagram.record_crossingCount, hcusp]
    rfl

end Reduction

/-! #### E. The remaining obligation, isolated: THE SWEEP STATEMENT (through U2's slot record) -/

section Sweep

variable (F : SmoothFront)

/-- the reduction through U2's slot record of the word (`U2.realizeRecordIso`): `D` and the cusp count read
syntactically (`realize_downCount`, `realize_cuspCount`), `w` and the crossing count carried by the record -/
theorem represent_of_slotRecordIso (W : OWord) (hne : W.letters ≠ [])
    (hD : F.downCount = W.downCountSyn) (hcusp : F.cuspSet.card = W.letters.cuspCount)
    (hrec : Nonempty (RecordIso (frontRecord F) (U2.slotRecord W.closed U2.IsσSlot (U2.allActive W.closed)))) :
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
      ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) :=
  represent_of_frontRecordIso_counts F W (by rw [realize_downCount W hne]; exact hD)
    (by rw [realize_cuspCount W hne]; exact hcusp) (hrec.map fun ι => ι.trans (U2.realizeRecordIso W hne).symm)

/-- THE SWEEP STATEMENT — what remains of the leaf `represent` (W2_U8R_REPORT.md §2-§3): a nonempty closed
word with the letter-traced down count `D(F)`, the cusp count of `F`, and whose slot record (U2, all `σ` slots)
is the named record of `F`.  Produced by the vertical sweep of the printed proof (sm-3:1938-1947); `w(F)` and
the crossing count are then automatic (`frontRecord_writhe`, `frontRecord_crossingCount`). -/
def SweepStatement : Prop :=
  ∃ W : OWord, W.letters ≠ [] ∧ F.downCount = W.downCountSyn ∧ F.cuspSet.card = W.letters.cuspCount ∧
    Nonempty (RecordIso (frontRecord F) (U2.slotRecord W.closed U2.IsσSlot (U2.allActive W.closed)))

/-- `represent` from the sweep statement -/
theorem represent_of_sweepStatement (h : SweepStatement F) : ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) := by
  obtain ⟨W, hne, hD, hcusp, hrec⟩ := h
  exact ⟨W, represent_of_slotRecordIso F W hne hD hcusp hrec⟩

end Sweep


/-! #### F. Analytic groundwork for the sweep: the x-velocity along a circle, its sign between cusps and
its sign change at a cusp; the finite set of singular x-values -/

section XVel

open Filter Topology

variable (F : SmoothFront)

/-- the x-velocity `x'` of circle `i` -/
def xvel (i : Fin F.c) (t : ℝ) : ℝ := (deriv (F.comp i).γ t).1

theorem xvel_def (i : Fin F.c) (t : ℝ) : xvel F i t = (F.vel (i, t)).1 := rfl

theorem continuous_xvel (i : Fin F.c) : Continuous (xvel F i) := (F.comp i).continuous_deriv.fst

/-- the cusps are exactly the zeros of `x'` (`no_vertical`) -/
theorem isCusp_iff_xvel_eq_zero (i : Fin F.c) (t : ℝ) : F.IsCusp (i, t) ↔ xvel F i t = 0 := by
  constructor
  · intro h
    show (deriv (F.comp i).γ t).1 = 0
    rw [show deriv (F.comp i).γ t = 0 from h]; rfl
  · intro h
    by_contra hc
    exact F.no_vertical i t hc h

theorem xvel_ne_zero_of_not_isCusp {i : Fin F.c} {t : ℝ} (h : ¬ F.IsCusp (i, t)) : xvel F i t ≠ 0 :=
  fun h' => h ((isCusp_iff_xvel_eq_zero F i t).mpr h')

/-- On a cusp-free preconnected parameter set `x'` has constant sign (IVT on the continuous `x'`). -/
theorem xvel_mul_pos_of_cuspFree {i : Fin F.c} {s : Set ℝ} (hs : IsPreconnected s)
    (hc : ∀ t ∈ s, ¬ F.IsCusp (i, t)) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    0 < xvel F i a * xvel F i b := by
  have hna := xvel_ne_zero_of_not_isCusp F (hc a ha)
  have hnb := xvel_ne_zero_of_not_isCusp F (hc b hb)
  by_contra hle
  have hle' : xvel F i a * xvel F i b < 0 := lt_of_le_of_ne (not_lt.mp hle) (mul_ne_zero hna hnb)
  have hcont : ContinuousOn (xvel F i) s := (continuous_xvel F i).continuousOn
  rcases mul_neg_iff.mp hle' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨t, ht, ht0⟩ := hs.intermediate_value hb ha hcont ⟨h2.le, h1.le⟩
    exact hc t ht ((isCusp_iff_xvel_eq_zero F i t).mpr ht0)
  · obtain ⟨t, ht, ht0⟩ := hs.intermediate_value ha hb hcont ⟨h1.le, h2.le⟩
    exact hc t ht ((isCusp_iff_xvel_eq_zero F i t).mpr ht0)

theorem xvel_pos_of_cuspFree {i : Fin F.c} {s : Set ℝ} (hs : IsPreconnected s)
    (hc : ∀ t ∈ s, ¬ F.IsCusp (i, t)) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hpos : 0 < xvel F i a) :
    0 < xvel F i b :=
  (pos_iff_pos_of_mul_pos (xvel_mul_pos_of_cuspFree F hs hc ha hb)).mp hpos

theorem xvel_neg_of_cuspFree {i : Fin F.c} {s : Set ℝ} (hs : IsPreconnected s)
    (hc : ∀ t ∈ s, ¬ F.IsCusp (i, t)) {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) (hneg : xvel F i a < 0) :
    xvel F i b < 0 :=
  (neg_iff_neg_of_mul_pos (xvel_mul_pos_of_cuspFree F hs hc ha hb)).mp hneg

/-- `x'` is differentiable with derivative `x''` -/
theorem hasDerivAt_xvel (i : Fin F.c) (t : ℝ) : HasDerivAt (xvel F i) (F.acc (i, t)).1 t := by
  have hd : Differentiable ℝ (deriv (F.comp i).γ) := by
    have := (F.comp i).contDiff_iteratedDeriv 1
    rw [iteratedDeriv_one] at this
    exact this.differentiable (by decide)
  have h1 : HasDerivAt (deriv (F.comp i).γ) (iteratedDeriv 2 (F.comp i).γ t) t := by
    have := (hd t).hasDerivAt
    rwa [show deriv (deriv (F.comp i).γ) t = iteratedDeriv 2 (F.comp i).γ t by
      rw [iteratedDeriv_succ, iteratedDeriv_one]] at this
  exact h1.fst

/-- A real function vanishing at `a` with positive derivative there is negative just before `a` and
positive just after. -/
theorem sign_near_simple_zero {f : ℝ → ℝ} {f' a : ℝ} (hf : HasDerivAt f f' a) (h0 : f a = 0)
    (hpos : 0 < f') :
    ∃ δ > 0, ∀ t, dist t a < δ → (t < a → f t < 0) ∧ (a < t → 0 < f t) := by
  have hev : ∀ᶠ x in 𝓝 a, ‖f x - f a - (x - a) • f'‖ ≤ f' / 2 * ‖x - a‖ :=
    (hasDerivAt_iff_isLittleO.mp hf).def (half_pos hpos)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hev⟩ := hev
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have h := hev ht
  simp only [h0, sub_zero, smul_eq_mul, Real.norm_eq_abs] at h
  constructor
  · intro hlt
    rw [abs_of_neg (by linarith : t - a < 0)] at h
    have h2 := (abs_le.mp h).2
    have hm : 0 < f' * (a - t) := mul_pos hpos (by linarith)
    nlinarith
  · intro hgt
    rw [abs_of_pos (by linarith : 0 < t - a)] at h
    have h1 := (abs_le.mp h).1
    have hm : 0 < f' * (t - a) := mul_pos hpos (by linarith)
    nlinarith

/-- At a left cusp (`x'' > 0`) the traversal arrives moving leftward and leaves moving rightward. -/
theorem exists_xvel_sign_of_isLeftCusp {i : Fin F.c} {t₀ : ℝ} (h : F.IsLeftCusp (i, t₀)) :
    ∃ δ > 0, ∀ t, dist t t₀ < δ → (t < t₀ → xvel F i t < 0) ∧ (t₀ < t → 0 < xvel F i t) :=
  sign_near_simple_zero (hasDerivAt_xvel F i t₀) ((isCusp_iff_xvel_eq_zero F i t₀).mp h.1) h.2

/-- At a right cusp (`x'' < 0`) the traversal arrives moving rightward and leaves moving leftward. -/
theorem exists_xvel_sign_of_isRightCusp {i : Fin F.c} {t₀ : ℝ} (h : F.IsRightCusp (i, t₀)) :
    ∃ δ > 0, ∀ t, dist t t₀ < δ → (t < t₀ → 0 < xvel F i t) ∧ (t₀ < t → xvel F i t < 0) := by
  have h0 : (fun t => -xvel F i t) t₀ = 0 := by
    simp only [(isCusp_iff_xvel_eq_zero F i t₀).mp h.1, neg_zero]
  obtain ⟨δ, hδ, hs⟩ := sign_near_simple_zero (hasDerivAt_xvel F i t₀).neg h0 (neg_pos.mpr h.2)
  refine ⟨δ, hδ, fun t ht => ⟨fun hlt => ?_, fun hgt => ?_⟩⟩
  · have h1 : -xvel F i t < 0 := (hs t ht).1 hlt
    linarith
  · have h1 : 0 < -xvel F i t := (hs t ht).2 hgt
    linarith

/-- A cusp is a strict isolated zero of `x'`: no other cusp of the circle nearby. -/
theorem exists_no_cusp_near {i : Fin F.c} {t₀ : ℝ} (h : F.IsCusp (i, t₀)) :
    ∃ δ > 0, ∀ t, dist t t₀ < δ → t ≠ t₀ → ¬ F.IsCusp (i, t) := by
  rcases F.isLeftCusp_or_isRightCusp h with hl | hr
  · obtain ⟨δ, hδ, hs⟩ := exists_xvel_sign_of_isLeftCusp F hl
    refine ⟨δ, hδ, fun t ht hne hc => ?_⟩
    have h0 := (isCusp_iff_xvel_eq_zero F i t).mp hc
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := (hs t ht).1 hlt; linarith
    · have := (hs t ht).2 hgt; linarith
  · obtain ⟨δ, hδ, hs⟩ := exists_xvel_sign_of_isRightCusp F hr
    refine ⟨δ, hδ, fun t ht hne hc => ?_⟩
    have h0 := (isCusp_iff_xvel_eq_zero F i t).mp hc
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := (hs t ht).1 hlt; linarith
    · have := (hs t ht).2 hgt; linarith

/-- the singular x-values: the x-coordinates of the cusps and of the double points -/
def singX : Finset ℝ :=
  F.cuspSet.image (fun p => (F.eval p).1) ∪ F.doubleSet.image (fun q => (F.eval q.1).1)

theorem mem_singX_of_isCusp {p : Param F.c} (hp : F.IsCusp p) : (F.eval p).1 ∈ singX F := by
  unfold singX
  rw [Finset.mem_union, Finset.mem_image]
  left
  refine ⟨SameParam.rep p, F.rep_mem_cuspSet hp, ?_⟩
  rw [SmoothFront.eval_of_sameParam (SameParam.sameParam_rep p)]

theorem rep_pair_mem_doubleSet {p q : Param F.c} (h : F.IsDouble p q) :
    (SameParam.rep p, SameParam.rep q) ∈ F.doubleSet := by
  rw [SmoothFront.mem_doubleSet]
  refine ⟨SameParam.rep_mem_Ico p, SameParam.rep_mem_Ico q, fun heq => h.1 ?_, ?_⟩
  · have heq' : SameParam.rep p = SameParam.rep q := heq
    exact (SameParam.sameParam_rep p).trans (by rw [heq']; exact (SameParam.sameParam_rep q).symm)
  · show F.eval (SameParam.rep p) = F.eval (SameParam.rep q)
    rw [SmoothFront.eval_of_sameParam (SameParam.sameParam_rep p),
      SmoothFront.eval_of_sameParam (SameParam.sameParam_rep q)]
    exact h.2

theorem mem_singX_of_isDouble {p q : Param F.c} (h : F.IsDouble p q) : (F.eval p).1 ∈ singX F := by
  unfold singX
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
  right
  refine ⟨(SameParam.rep p, SameParam.rep q), rep_pair_mem_doubleSet F h, ?_⟩
  show (F.eval (SameParam.rep p)).1 = (F.eval p).1
  rw [SmoothFront.eval_of_sameParam (SameParam.sameParam_rep p)]

/-- off the singular x-values every point of the front is a regular non-double point -/
theorem regular_of_notMem_singX {p : Param F.c} (hp : (F.eval p).1 ∉ singX F) :
    ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q :=
  ⟨fun h => hp (mem_singX_of_isCusp F h), fun q h => hp (mem_singX_of_isDouble F h)⟩

end XVel

/-! #### G. The cusp arcs of a circle: consecutive cusps alternate left/right, `x` is strictly monotone on the
arc between them -/

section CuspArcs

variable (F : SmoothFront)

/-- the circle of a cusp -/
def cuspComp (c : F.Cusp) : Fin F.c := c.1.1
/-- the parameter of a cusp (in `[0,1)`) -/
def cuspKey (c : F.Cusp) : ℝ := c.1.2

theorem cuspKey_inj (a b : F.Cusp) (h1 : cuspComp F a = cuspComp F b) (h2 : cuspKey F a = cuspKey F b) : a = b :=
  Subtype.ext (Prod.ext h1 h2)

/-- the next cusp along the oriented circle -/
def nextCusp (c : F.Cusp) : F.Cusp := cycNext (cuspComp F) (cuspKey F) (cuspKey_inj F) c

theorem nextCusp_fst (c : F.Cusp) : (nextCusp F c).1.1 = c.1.1 :=
  comp_cycNext (cuspComp F) (cuspKey F) (cuspKey_inj F) c

theorem nextCusp_no_between (c u : F.Cusp) (hu : u.1.1 = c.1.1) :
    ¬ cycBetween c.1.2 u.1.2 (nextCusp F c).1.2 :=
  cycNext_no_between (cuspComp F) (cuspKey F) (cuspKey_inj F) c u hu

theorem eq_of_nextCusp_eq_self {c : F.Cusp} (h : nextCusp F c = c) (u : F.Cusp) (hu : u.1.1 = c.1.1) : u = c := by
  by_contra hne
  exact cycNext_ne_self (cuspComp F) (cuspKey F) (cuspKey_inj F) c u hu hne h

/-- the end of the arc from `c` to the next cusp, as a real parameter `> c.1.2` (the next cusp's parameter,
lifted by one period when the arc wraps around `0`) -/
def arcEnd (c : F.Cusp) : ℝ :=
  if c.1.2 < (nextCusp F c).1.2 then (nextCusp F c).1.2 else (nextCusp F c).1.2 + 1

theorem lt_arcEnd (c : F.Cusp) : c.1.2 < arcEnd F c := by
  unfold arcEnd
  split_ifs with h
  · exact h
  · have := c.mem_Ico.2
    have := (nextCusp F c).mem_Ico.1
    linarith

theorem arcEnd_le (c : F.Cusp) : arcEnd F c ≤ c.1.2 + 1 := by
  unfold arcEnd
  split_ifs with h
  · have := c.mem_Ico.1
    have := (nextCusp F c).mem_Ico.2
    linarith
  · linarith [not_lt.mp h]

theorem sameParam_arcEnd (c : F.Cusp) : SameParam (nextCusp F c).1 (c.1.1, arcEnd F c) := by
  refine ⟨nextCusp_fst F c, ?_⟩
  unfold arcEnd
  split_ifs
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩

theorem isCusp_arcEnd (c : F.Cusp) : F.IsCusp (c.1.1, arcEnd F c) :=
  (F.isCusp_iff_of_sameParam (sameParam_arcEnd F c)).mpr (nextCusp F c).isCusp

theorem isLeftCusp_iff_of_sameParam {p q : Param F.c} (h : SameParam p q) : F.IsLeftCusp q ↔ F.IsLeftCusp p := by
  unfold SmoothFront.IsLeftCusp
  rw [F.isCusp_iff_of_sameParam h, SmoothFront.acc_of_sameParam h]

theorem isRightCusp_iff_of_sameParam {p q : Param F.c} (h : SameParam p q) : F.IsRightCusp q ↔ F.IsRightCusp p := by
  unfold SmoothFront.IsRightCusp
  rw [F.isCusp_iff_of_sameParam h, SmoothFront.acc_of_sameParam h]

/-- no cusp strictly inside the arc from a cusp to the next -/
theorem not_isCusp_of_mem_arc (c : F.Cusp) {t : ℝ} (ht : t ∈ Set.Ioo c.1.2 (arcEnd F c)) :
    ¬ F.IsCusp (c.1.1, t) := by
  intro hc
  have hmem : SameParam.rep (c.1.1, t) ∈ F.cuspSet := F.rep_mem_cuspSet hc
  set u : F.Cusp := ⟨SameParam.rep (c.1.1, t), hmem⟩ with hu
  have hu1 : u.1.1 = c.1.1 := rfl
  have hu2 : u.1.2 = Int.fract t := rfl
  have hc0 := c.mem_Ico.1
  have hc1 := c.mem_Ico.2
  have hn0 := (nextCusp F c).mem_Ico.1
  have hn1 := (nextCusp F c).mem_Ico.2
  have hnb := nextCusp_no_between F c u hu1
  rw [hu2] at hnb
  obtain ⟨ht1, ht2⟩ := ht
  unfold arcEnd at ht2
  split_ifs at ht2 with hlt
  · -- the arc does not wrap: `t ∈ (c, next) ⊆ [0,1)`
    have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hfr] at hnb
    exact hnb (Or.inl ⟨ht1, ht2⟩)
  · rcases lt_or_eq_of_le (not_lt.mp hlt) with hlt' | heq
    · -- the arc wraps: `next < c`
      rcases lt_or_ge t 1 with ht3 | ht3
      · have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith, ht3⟩
        rw [hfr] at hnb
        exact hnb (Or.inr (Or.inr ⟨hlt', ht1⟩))
      · have hfr : Int.fract t = t - 1 := by
          rw [Int.fract_eq_iff]
          refine ⟨by linarith, by linarith, 1, by simp⟩
        rw [hfr] at hnb
        exact hnb (Or.inr (Or.inl ⟨by linarith, hlt'⟩))
    · -- the cusp is alone on its circle: every cusp of the circle is `c`
      have hnc : nextCusp F c = c := cuspKey_inj F _ _ (nextCusp_fst F c) heq
      have huc : u = c := eq_of_nextCusp_eq_self F hnc u hu1
      have hkey : Int.fract t = c.1.2 := by rw [← hu2, huc]
      have hfl : t = c.1.2 + ⌊t⌋ := by
        have := Int.fract_add_floor t
        linarith
      have h0 : (0 : ℝ) < ⌊t⌋ := by linarith
      have h1 : (⌊t⌋ : ℝ) < 1 := by linarith
      have h0' : (0 : ℤ) < ⌊t⌋ := by exact_mod_cast h0
      have h1' : ⌊t⌋ < (1 : ℤ) := by exact_mod_cast h1
      omega

theorem xvel_mul_pos_on_arc (c : F.Cusp) {a b : ℝ} (ha : a ∈ Set.Ioo c.1.2 (arcEnd F c))
    (hb : b ∈ Set.Ioo c.1.2 (arcEnd F c)) : 0 < xvel F c.1.1 a * xvel F c.1.1 b :=
  xvel_mul_pos_of_cuspFree F isPreconnected_Ioo (fun t ht => not_isCusp_of_mem_arc F c ht) ha hb

/-- a parameter of the arc within `δ` of its start -/
theorem exists_mem_arc_near (c : F.Cusp) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s, s ∈ Set.Ioo c.1.2 (arcEnd F c) ∧ dist s c.1.2 < δ := by
  have hlt := lt_arcEnd F c
  refine ⟨c.1.2 + min (δ / 2) ((arcEnd F c - c.1.2) / 2), ⟨?_, ?_⟩, ?_⟩
  · have : 0 < min (δ / 2) ((arcEnd F c - c.1.2) / 2) := lt_min (by linarith) (by linarith)
    linarith
  · have : min (δ / 2) ((arcEnd F c - c.1.2) / 2) ≤ (arcEnd F c - c.1.2) / 2 := min_le_right _ _
    linarith
  · rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (lt_min (by linarith) (by linarith))]
    have : min (δ / 2) ((arcEnd F c - c.1.2) / 2) ≤ δ / 2 := min_le_left _ _
    linarith

/-- a parameter of the arc within `δ` of its end -/
theorem exists_mem_arc_near_end (c : F.Cusp) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s, s ∈ Set.Ioo c.1.2 (arcEnd F c) ∧ dist s (arcEnd F c) < δ := by
  have hlt := lt_arcEnd F c
  refine ⟨arcEnd F c - min (δ / 2) ((arcEnd F c - c.1.2) / 2), ⟨?_, ?_⟩, ?_⟩
  · have : min (δ / 2) ((arcEnd F c - c.1.2) / 2) ≤ (arcEnd F c - c.1.2) / 2 := min_le_right _ _
    linarith
  · have : 0 < min (δ / 2) ((arcEnd F c - c.1.2) / 2) := lt_min (by linarith) (by linarith)
    linarith
  · rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (lt_min (by linarith) (by linarith))]
    have : min (δ / 2) ((arcEnd F c - c.1.2) / 2) ≤ δ / 2 := min_le_left _ _
    linarith

/-- after a left cusp the traversal moves rightward along the whole arc -/
theorem xvel_pos_on_arc_of_isLeftCusp (c : F.Cusp) (hl : F.IsLeftCusp c.1) {t : ℝ}
    (ht : t ∈ Set.Ioo c.1.2 (arcEnd F c)) : 0 < xvel F c.1.1 t := by
  obtain ⟨δ, hδ, hs⟩ := exists_xvel_sign_of_isLeftCusp F (i := c.1.1) (t₀ := c.1.2) hl
  obtain ⟨s, hs1, hs2⟩ := exists_mem_arc_near F c hδ
  have hpos : 0 < xvel F c.1.1 s := (hs s hs2).2 hs1.1
  exact xvel_pos_of_cuspFree F isPreconnected_Ioo (fun t ht => not_isCusp_of_mem_arc F c ht) hs1 ht hpos

/-- after a right cusp the traversal moves leftward along the whole arc -/
theorem xvel_neg_on_arc_of_isRightCusp (c : F.Cusp) (hr : F.IsRightCusp c.1) {t : ℝ}
    (ht : t ∈ Set.Ioo c.1.2 (arcEnd F c)) : xvel F c.1.1 t < 0 := by
  obtain ⟨δ, hδ, hs⟩ := exists_xvel_sign_of_isRightCusp F (i := c.1.1) (t₀ := c.1.2) hr
  obtain ⟨s, hs1, hs2⟩ := exists_mem_arc_near F c hδ
  have hneg : xvel F c.1.1 s < 0 := (hs s hs2).2 hs1.1
  exact xvel_neg_of_cuspFree F isPreconnected_Ioo (fun t ht => not_isCusp_of_mem_arc F c ht) hs1 ht hneg

/-- consecutive cusps alternate: the cusp after a left cusp is a right cusp -/
theorem isRightCusp_nextCusp_of_isLeftCusp (c : F.Cusp) (hl : F.IsLeftCusp c.1) :
    F.IsRightCusp (nextCusp F c).1 := by
  rw [← isRightCusp_iff_of_sameParam F (sameParam_arcEnd F c)]
  rcases F.isLeftCusp_or_isRightCusp (isCusp_arcEnd F c) with hl' | hr'
  · exfalso
    obtain ⟨δ, hδ, hs⟩ := exists_xvel_sign_of_isLeftCusp F hl'
    obtain ⟨s, hs1, hs2⟩ := exists_mem_arc_near_end F c hδ
    have h1 : xvel F c.1.1 s < 0 := (hs s hs2).1 hs1.2
    have h2 := xvel_pos_on_arc_of_isLeftCusp F c hl hs1
    linarith
  · exact hr'

/-- and the cusp after a right cusp is a left cusp -/
theorem isLeftCusp_nextCusp_of_isRightCusp (c : F.Cusp) (hr : F.IsRightCusp c.1) :
    F.IsLeftCusp (nextCusp F c).1 := by
  rw [← isLeftCusp_iff_of_sameParam F (sameParam_arcEnd F c)]
  rcases F.isLeftCusp_or_isRightCusp (isCusp_arcEnd F c) with hl' | hr'
  · exact hl'
  · exfalso
    obtain ⟨δ, hδ, hs⟩ := exists_xvel_sign_of_isRightCusp F hr'
    obtain ⟨s, hs1, hs2⟩ := exists_mem_arc_near_end F c hδ
    have h1 : 0 < xvel F c.1.1 s := (hs s hs2).1 hs1.2
    have h2 := xvel_neg_on_arc_of_isRightCusp F c hr hs1
    linarith

theorem left_right_absurd {p : Param F.c} (hl : F.IsLeftCusp p) (hr : F.IsRightCusp p) : False :=
  lt_asymm hl.2 hr.2

/-- no cusp is alone on its circle -/
theorem nextCusp_ne (c : F.Cusp) : nextCusp F c ≠ c := by
  intro h
  rcases F.isLeftCusp_or_isRightCusp c.isCusp with hl | hr
  · have := isRightCusp_nextCusp_of_isLeftCusp F c hl
    rw [h] at this
    exact left_right_absurd F hl this
  · have := isLeftCusp_nextCusp_of_isRightCusp F c hr
    rw [h] at this
    exact left_right_absurd F this hr

/-- every circle carries at least two cusps -/
theorem exists_two_cusps (i : Fin F.c) : ∃ c d : F.Cusp, c ≠ d ∧ c.1.1 = i ∧ d.1.1 = i := by
  obtain ⟨t, ht⟩ := F.exists_isCusp i
  refine ⟨⟨SameParam.rep (i, t), F.rep_mem_cuspSet ht⟩, nextCusp F ⟨SameParam.rep (i, t), F.rep_mem_cuspSet ht⟩,
    (nextCusp_ne F _).symm, rfl, nextCusp_fst F _⟩

theorem hasDerivAt_x (i : Fin F.c) (t : ℝ) : HasDerivAt (fun s => ((F.comp i).γ s).1) (xvel F i t) t :=
  ((F.comp i).hasDerivAt t).fst

/-- `x` is injective on the closed arc (Rolle: a repeated value would force `x' = 0`, a cusp, inside) -/
theorem injOn_x_arc (c : F.Cusp) :
    Set.InjOn (fun s => ((F.comp c.1.1).γ s).1) (Set.Icc c.1.2 (arcEnd F c)) := by
  intro s hs t ht hst
  by_contra hne
  have key : ∀ s t, s ∈ Set.Icc c.1.2 (arcEnd F c) → t ∈ Set.Icc c.1.2 (arcEnd F c) → s < t →
      ((F.comp c.1.1).γ s).1 = ((F.comp c.1.1).γ t).1 → False := by
    intro s t hs ht hlt hst
    obtain ⟨u, hu, hu0⟩ := exists_hasDerivAt_eq_zero hlt ((F.comp c.1.1).continuous.fst).continuousOn hst
      (fun x _ => hasDerivAt_x F c.1.1 x)
    exact not_isCusp_of_mem_arc F c ⟨lt_of_le_of_lt hs.1 hu.1, lt_of_lt_of_le hu.2 ht.2⟩
      ((isCusp_iff_xvel_eq_zero F _ _).mpr hu0)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key s t hs ht hlt hst
  · exact key t s ht hs hlt hst.symm

/-- `x` is strictly increasing on the closed arc after a left cusp -/
theorem strictMonoOn_x_of_isLeftCusp (c : F.Cusp) (hl : F.IsLeftCusp c.1) :
    StrictMonoOn (fun s => ((F.comp c.1.1).γ s).1) (Set.Icc c.1.2 (arcEnd F c)) := by
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (lt_arcEnd F c).le
    ((F.comp c.1.1).continuous.fst).continuousOn (injOn_x_arc F c) with h | h
  · exact h
  · exfalso
    obtain ⟨t₀, ht₀, -⟩ := exists_mem_arc_near F c one_pos
    have hpos := xvel_pos_on_arc_of_isLeftCusp F c hl ht₀
    have hd : HasDerivAt (fun s => ((F.comp c.1.1).γ s).1 - ((F.comp c.1.1).γ t₀).1) (xvel F c.1.1 t₀) t₀ :=
      (hasDerivAt_x F c.1.1 t₀).sub_const _
    obtain ⟨δ, hδ, hs⟩ := sign_near_simple_zero hd (sub_self _) hpos
    have hmin : 0 < min (δ / 2) ((arcEnd F c - t₀) / 2) := lt_min (by linarith) (by linarith [ht₀.2])
    set t := t₀ + min (δ / 2) ((arcEnd F c - t₀) / 2) with ht
    have htgt : t₀ < t := by linarith
    have htle : t ≤ arcEnd F c := by
      have := min_le_right (δ / 2) ((arcEnd F c - t₀) / 2); linarith
    have htd : dist t t₀ < δ := by
      rw [Real.dist_eq, ht, add_sub_cancel_left, abs_of_pos hmin]
      have := min_le_left (δ / 2) ((arcEnd F c - t₀) / 2); linarith
    have h1 : 0 < ((F.comp c.1.1).γ t).1 - ((F.comp c.1.1).γ t₀).1 := (hs t htd).2 htgt
    have h2 := h ⟨ht₀.1.le, ht₀.2.le⟩ ⟨by linarith [ht₀.1], htle⟩ htgt
    simp only at h2
    linarith

/-- `x` is strictly decreasing on the closed arc after a right cusp -/
theorem strictAntiOn_x_of_isRightCusp (c : F.Cusp) (hr : F.IsRightCusp c.1) :
    StrictAntiOn (fun s => ((F.comp c.1.1).γ s).1) (Set.Icc c.1.2 (arcEnd F c)) := by
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (lt_arcEnd F c).le
    ((F.comp c.1.1).continuous.fst).continuousOn (injOn_x_arc F c) with h | h
  · exfalso
    obtain ⟨t₀, ht₀, -⟩ := exists_mem_arc_near F c one_pos
    have hneg := xvel_neg_on_arc_of_isRightCusp F c hr ht₀
    have hd : HasDerivAt (fun s => ((F.comp c.1.1).γ t₀).1 - ((F.comp c.1.1).γ s).1) (-xvel F c.1.1 t₀) t₀ :=
      (hasDerivAt_x F c.1.1 t₀).const_sub _
    obtain ⟨δ, hδ, hs⟩ := sign_near_simple_zero hd (sub_self _) (neg_pos.mpr hneg)
    have hmin : 0 < min (δ / 2) ((arcEnd F c - t₀) / 2) := lt_min (by linarith) (by linarith [ht₀.2])
    set t := t₀ + min (δ / 2) ((arcEnd F c - t₀) / 2) with ht
    have htgt : t₀ < t := by linarith
    have htle : t ≤ arcEnd F c := by
      have := min_le_right (δ / 2) ((arcEnd F c - t₀) / 2); linarith
    have htd : dist t t₀ < δ := by
      rw [Real.dist_eq, ht, add_sub_cancel_left, abs_of_pos hmin]
      have := min_le_left (δ / 2) ((arcEnd F c - t₀) / 2); linarith
    have h1 : 0 < ((F.comp c.1.1).γ t₀).1 - ((F.comp c.1.1).γ t).1 := (hs t htd).2 htgt
    have h2 := h ⟨ht₀.1.le, ht₀.2.le⟩ ⟨by linarith [ht₀.1], htle⟩ htgt
    simp only at h2
    linarith
  · exact h

end CuspArcs

/-! #### H. The arcs cover the circle; the fibre over a non-singular `x` is finite -/

section ArcCover

variable (F : SmoothFront)

/-- the cusps of circle `i` -/
def circleCusps (i : Fin F.c) : Finset F.Cusp := Finset.univ.filter (fun c => c.1.1 = i)

theorem mem_circleCusps (i : Fin F.c) (c : F.Cusp) : c ∈ circleCusps F i ↔ c.1.1 = i := by
  simp [circleCusps]

theorem circleCusps_nonempty (i : Fin F.c) : (circleCusps F i).Nonempty := by
  obtain ⟨c, -, -, hc, -⟩ := exists_two_cusps F i
  exact ⟨c, (mem_circleCusps F i c).mpr hc⟩

/-- Every parameter of a circle lies (modulo the period) on the closed arc from some cusp to the next. -/
theorem exists_arc_mem (i : Fin F.c) (t : ℝ) :
    ∃ c : F.Cusp, c.1.1 = i ∧ ∃ t', SameParam (i, t) (i, t') ∧ t' ∈ Set.Icc c.1.2 (arcEnd F c) := by
  set r := Int.fract t with hr
  have hr0 : 0 ≤ r := Int.fract_nonneg t
  have hr1 : r < 1 := Int.fract_lt_one t
  have hsr : SameParam (i, t) (i, r) := SameParam.sameParam_rep (i, t)
  by_cases hbelow : ((circleCusps F i).filter (fun c => c.1.2 ≤ r)).Nonempty
  · -- the last cusp before `r`
    obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ (fun c : F.Cusp => c.1.2) hbelow
    rw [Finset.mem_filter, mem_circleCusps] at hc
    refine ⟨c, hc.1, r, hsr, hc.2, ?_⟩
    unfold arcEnd
    split_ifs with hlt
    · by_contra hgt
      push Not at hgt
      have hmem : nextCusp F c ∈ (circleCusps F i).filter (fun c => c.1.2 ≤ r) := by
        rw [Finset.mem_filter, mem_circleCusps]
        exact ⟨(nextCusp_fst F c).trans hc.1, hgt.le⟩
      have h' : (nextCusp F c).1.2 ≤ c.1.2 := hmax _ hmem
      linarith
    · have := (nextCusp F c).mem_Ico.1
      linarith
  · -- every cusp of the circle lies after `r`: wrap to the last cusp of the circle
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hbelow
    obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image _ (fun c : F.Cusp => c.1.2) (circleCusps_nonempty F i)
    rw [mem_circleCusps] at hc
    have hnext_le : (nextCusp F c).1.2 ≤ c.1.2 :=
      hmax _ ((mem_circleCusps F i _).mpr ((nextCusp_fst F c).trans hc))
    have hcr : r < c.1.2 := by
      have := hbelow ((mem_circleCusps F i c).mpr hc)
      simpa using this
    have hnr : r < (nextCusp F c).1.2 := by
      have := hbelow ((mem_circleCusps F i _).mpr ((nextCusp_fst F c).trans hc))
      simpa using this
    refine ⟨c, hc, r + 1, hsr.trans ⟨rfl, 1, by simp⟩, ?_, ?_⟩
    · have := c.mem_Ico.2; linarith
    · unfold arcEnd
      simp only [not_lt.mpr hnext_le, ↓reduceIte]
      linarith

/-- the parameters of circle `i` in the fundamental period lying over a given `x` -/
def fibre (i : Fin F.c) (x₀ : ℝ) : Set ℝ := {t | t ∈ Set.Ico (0 : ℝ) 1 ∧ ((F.comp i).γ t).1 = x₀}

/-- Over any `x₀` each closed cusp arc carries at most one parameter of the fibre, and the arcs are indexed
by the finitely many cusps: the fibre over any `x₀` is finite. -/
theorem fibre_finite (i : Fin F.c) (x₀ : ℝ) : (fibre F i x₀).Finite := by
  classical
  have : Nonempty F.Cusp := ⟨(exists_two_cusps F ⟨0, F.hc⟩).choose⟩
  -- to each fibre parameter attach an arc containing it (modulo the period) and the lift `t' ∈ {t, t + 1}`
  have hchoice : ∀ t ∈ fibre F i x₀, ∃ c : F.Cusp, c.1.1 = i ∧
      ∃ t', SameParam (i, t) (i, t') ∧ t' ∈ Set.Icc c.1.2 (arcEnd F c) := fun t _ => exists_arc_mem F i t
  choose! g hg using hchoice
  choose! lift hlift using fun t (ht : t ∈ fibre F i x₀) => (hg t ht).2
  have hdata : ∀ t, t ∈ fibre F i x₀ → ∃ n : ℤ, lift t = t + n ∧ ⌊lift t - t⌋ = n ∧ 0 ≤ n ∧ n ≤ 1 := by
    intro t ht
    obtain ⟨⟨-, n, hn⟩, hm⟩ := hlift t ht
    simp only at hn
    refine ⟨n, hn, by rw [hn, add_sub_cancel_left, Int.floor_intCast], ?_, ?_⟩
    · have h0 := (g t).mem_Ico.1
      have h1 : (-1 : ℝ) < n := by linarith [hm.1, ht.1.2]
      have h2 : (-1 : ℤ) < n := by exact_mod_cast h1
      omega
    · have h1 := (g t).mem_Ico.2
      have h2 := arcEnd_le F (g t)
      have h3 : (n : ℝ) < 2 := by linarith [hm.2, ht.1.1]
      have h4 : n < (2 : ℤ) := by exact_mod_cast h3
      omega
  -- the map `t ↦ (arc, the integer shift of the lift)` is injective on the fibre, with finite range
  refine Set.Finite.of_finite_image (f := fun t => (g t, ⌊lift t - t⌋)) ?_ ?_
  · refine ((Set.finite_univ (α := F.Cusp)).prod (Set.finite_Icc (0 : ℤ) 1)).subset ?_
    rintro ⟨c, n⟩ ⟨t, ht, hpt⟩
    simp only [Prod.mk.injEq] at hpt
    obtain ⟨n', -, hfl, h0, h1⟩ := hdata t ht
    refine ⟨Set.mem_univ _, ?_⟩
    show n ∈ Set.Icc (0 : ℤ) 1
    rw [← hpt.2, hfl]
    exact ⟨h0, h1⟩
  · intro s hs t ht hst
    simp only [Prod.mk.injEq] at hst
    obtain ⟨hgs, hgt⟩ := hst
    obtain ⟨n, hn, hfn, -, -⟩ := hdata s hs
    obtain ⟨m, hm, hfm, -, -⟩ := hdata t ht
    have hnm : n = m := by rw [← hfn, ← hfm, hgt]
    have hx : ((F.comp i).γ (lift s)).1 = ((F.comp i).γ (lift t)).1 := by
      rw [hn, hm, (F.comp i).eq_add_int n s, (F.comp i).eq_add_int m t, hs.2, ht.2]
    have hsm := (hlift s hs).2
    have htm := (hlift t ht).2
    have hcomp : (g s).1.1 = i := (hg s hs).1
    have htm' : lift t ∈ Set.Icc (g s).1.2 (arcEnd F (g s)) := by rw [hgs]; exact htm
    have hinj := injOn_x_arc F (g s) hsm htm'
    simp only [hcomp] at hinj
    have := hinj hx
    rw [hn, hm, hnm] at this
    linarith

/-- the parameters (all circles, fundamental period) over a given `x` -/
def totalFibre (x₀ : ℝ) : Set (Param F.c) := {p | p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ (F.eval p).1 = x₀}

theorem mem_totalFibre_iff (x₀ : ℝ) (p : Param F.c) :
    p ∈ totalFibre F x₀ ↔ p.1 ∈ (Set.univ : Set (Fin F.c)) ∧ p.2 ∈ fibre F p.1 x₀ :=
  ⟨fun h => ⟨Set.mem_univ _, h.1, h.2⟩, fun h => ⟨h.2.1, h.2.2⟩⟩

theorem totalFibre_finite (x₀ : ℝ) : (totalFibre F x₀).Finite := by
  have h : totalFibre F x₀ ⊆ ⋃ i : Fin F.c, (fun t => (i, t)) '' fibre F i x₀ := by
    intro p hp
    rw [Set.mem_iUnion]
    exact ⟨p.1, p.2, ⟨hp.1, hp.2⟩, rfl⟩
  exact (Set.finite_iUnion fun i => (fibre_finite F i x₀).image _).subset h

/-- over a non-singular `x₀` the fibre points have pairwise distinct heights (no double point there), so the
fibre is totally ordered by `z`: this order is the cut of the sweep -/
theorem snd_injOn_totalFibre {x₀ : ℝ} (hx₀ : x₀ ∉ singX F) :
    Set.InjOn (fun p => (F.eval p).2) (totalFibre F x₀) := by
  intro p hp q hq hz
  by_contra hne
  have he : F.eval p = F.eval q := Prod.ext (hp.2.trans hq.2.symm) hz
  have hd : F.IsDouble p q := ⟨fun hs => hne (SameParam.eq_of_mem_Ico hp.1 hq.1 hs), he⟩
  exact hx₀ (hp.2 ▸ mem_singX_of_isDouble F hd)

/-- over a non-singular `x₀` every fibre point is regular, hence carries a direction bit `0 < x'` -/
theorem xvel_ne_zero_of_mem_totalFibre {x₀ : ℝ} (hx₀ : x₀ ∉ singX F) {p : Param F.c}
    (hp : p ∈ totalFibre F x₀) : xvel F p.1 p.2 ≠ 0 :=
  xvel_ne_zero_of_not_isCusp F (fun h => hx₀ (hp.2 ▸ mem_singX_of_isCusp F h))


end ArcCover


end

end U8R

end U8RInfra

/-! ### U8R sweep — the leaf skeleton for `U8R.SweepStatement` (wave 3; plan `W3_U8R_PLAN.md`)

The vertical sweep of the printed proof (sm-3:1938-1947), organised in six units of leaves:
* **S1 the cut.** Over `x₀` the fibre is finite (`totalFibre_finite`); sorted by height (top to bottom) it is the
  list `fibreListBefore`/`fibreListAfter` (at a double point the over branch, of smaller slope, is above BEFORE the
  crossing and below AFTER it: the two sort keys `beforeLE`/`afterLE`).  Each fibre point carries the bits of its
  strands just before / just after its x-value (`beforeBits`/`afterBits`: none/two for a cusp, one otherwise), so
  `cutBefore x₀`/`cutAfter x₀` are the cuts just left/right of `x₀`, and `hybridCut x₀ z₀` (strands at height
  `≥ z₀` read "before", strands below read "after") is the cut between two events of one x-value.  The analytic
  leaves: the local graph structure at a regular point, compactness (no strands appear from nowhere), the two
  one-sided limits at the level of strand ENTRIES (`Cont`: an entry's continuation along the front), and the
  constancy of the cut between consecutive singular x-values.
* **S2 the cusp**, **S3 the crossing**: the local models (Taylor sign law `cusp_arm_sign`; `x` a strict local
  extremum at a cusp; the over branch above before / below after).
* **S4 the word.** The events (cusps and over-first crossing pairs) sorted by `(x, z)`, bottom first at equal `x`
  (`events`); the letter of an event at position `posOf` = 1 + the number of strands strictly above it in the
  hybrid cut; the run of the word through the hybrid cuts (`run_take_eq_hybrid`), closedness, the counts.
* **S5 the slot map** `Φ` (an occurrence ↦ `σSlotA`/`σSlotB` of its crossing's column) and the local record
  clauses `pair`, `isOver`, `sgn`.
* **S6 the traversal.** `slotAt i t` = the slot of the strand through `(i, t)` at the cut line of its x-value;
  its constancy along regular arcs and its `next`-jumps across singular x-values (through a regular point, a cusp
  vertex, a crossing); hence `succ ↔ firstReturn`, `comp`, and the circle bijection `e`.
The theorem `sweep_proof : SweepStatement F` and the leaf `represent` are PROVED from the leaves. -/
namespace U8R

open SM.FrontWord SM.FrontWord.Letter SM.FrontRealize Equiv

noncomputable section

section SweepDefs

variable (F : SmoothFront)

/-! #### S1. Coordinates, fibres, the sorted fibre lists and the cuts -/

/-- the x-coordinate of circle `i` at parameter `t` -/
def xOf (i : Fin F.c) (t : ℝ) : ℝ := ((F.comp i).γ t).1
/-- the z-coordinate (height) of circle `i` at parameter `t` -/
def zOf (i : Fin F.c) (t : ℝ) : ℝ := ((F.comp i).γ t).2
/-- the height of a parameter -/
def ht (p : Param F.c) : ℝ := (F.eval p).2
/-- the direction bit of a parameter: `true` iff the traversal moves rightward there -/
def dirBit (p : Param F.c) : Bool := decide (0 < xvel F p.1 p.2)

theorem xOf_def (i : Fin F.c) (t : ℝ) : xOf F i t = (F.eval (i, t)).1 := rfl
theorem zOf_def (i : Fin F.c) (t : ℝ) : zOf F i t = ht F (i, t) := rfl

/-- a default parameter (used only as the `getD` default of lists) -/
def dfltP : Param F.c := (⟨0, F.hc⟩, 0)

instance decIsCusp (p : Param F.c) : Decidable (F.IsCusp p) := by
  unfold SmoothFront.IsCusp; infer_instance
instance decIsLeftCusp (p : Param F.c) : Decidable (F.IsLeftCusp p) := by
  unfold SmoothFront.IsLeftCusp; infer_instance
instance decIsRightCusp (p : Param F.c) : Decidable (F.IsRightCusp p) := by
  unfold SmoothFront.IsRightCusp; infer_instance

/-- the finite fibre over `x₀` as a `Finset` (all circles, fundamental period) -/
def fibreFinset (x₀ : ℝ) : Finset (Param F.c) := (totalFibre_finite F x₀).toFinset

theorem mem_fibreFinset (x₀ : ℝ) (p : Param F.c) : p ∈ fibreFinset F x₀ ↔ p ∈ totalFibre F x₀ :=
  Set.Finite.mem_toFinset _

/-- the "before" order on fibre points: height descending, at equal height the smaller slope (the over branch)
first — the order of the strands just LEFT of a double point -/
def beforeLE (p q : Param F.c) : Bool :=
  decide (toLex (-(ht F p), F.slope p) ≤ toLex (-(ht F q), F.slope q))
/-- the "after" order: height descending, at equal height the larger slope (the under branch) first — the order
of the strands just RIGHT of a double point -/
def afterLE (p q : Param F.c) : Bool :=
  decide (toLex (-(ht F p), -(F.slope p)) ≤ toLex (-(ht F q), -(F.slope q)))

/-- the fibre over `x₀` sorted top to bottom in the "before" order -/
def fibreListBefore (x₀ : ℝ) : List (Param F.c) := (fibreFinset F x₀).toList.mergeSort (beforeLE F)
/-- the fibre over `x₀` sorted top to bottom in the "after" order -/
def fibreListAfter (x₀ : ℝ) : List (Param F.c) := (fibreFinset F x₀).toList.mergeSort (afterLE F)

theorem fibreListBefore_perm (x₀ : ℝ) : List.Perm (fibreListBefore F x₀) (fibreFinset F x₀).toList :=
  List.mergeSort_perm _ _
theorem fibreListAfter_perm (x₀ : ℝ) : List.Perm (fibreListAfter F x₀) (fibreFinset F x₀).toList :=
  List.mergeSort_perm _ _
theorem mem_fibreListBefore (x₀ : ℝ) (p : Param F.c) : p ∈ fibreListBefore F x₀ ↔ p ∈ totalFibre F x₀ := by
  rw [fibreListBefore, List.mem_mergeSort, Finset.mem_toList, mem_fibreFinset]
theorem mem_fibreListAfter (x₀ : ℝ) (p : Param F.c) : p ∈ fibreListAfter F x₀ ↔ p ∈ totalFibre F x₀ := by
  rw [fibreListAfter, List.mem_mergeSort, Finset.mem_toList, mem_fibreFinset]
theorem fibreListBefore_nodup (x₀ : ℝ) : (fibreListBefore F x₀).Nodup :=
  (fibreListBefore_perm F x₀).nodup_iff.mpr (Finset.nodup_toList _)
theorem fibreListAfter_nodup (x₀ : ℝ) : (fibreListAfter F x₀).Nodup :=
  (fibreListAfter_perm F x₀).nodup_iff.mpr (Finset.nodup_toList _)

theorem beforeLE_trans (p q r : Param F.c) (h1 : beforeLE F p q = true) (h2 : beforeLE F q r = true) :
    beforeLE F p r = true := by
  unfold beforeLE at *; rw [decide_eq_true_iff] at *; exact le_trans h1 h2
theorem beforeLE_total (p q : Param F.c) : (beforeLE F p q || beforeLE F q p) = true := by
  unfold beforeLE; rcases le_total (toLex (-(ht F p), F.slope p)) (toLex (-(ht F q), F.slope q)) with h | h <;> simp [h]
theorem afterLE_trans (p q r : Param F.c) (h1 : afterLE F p q = true) (h2 : afterLE F q r = true) :
    afterLE F p r = true := by
  unfold afterLE at *; rw [decide_eq_true_iff] at *; exact le_trans h1 h2
theorem afterLE_total (p q : Param F.c) : (afterLE F p q || afterLE F q p) = true := by
  unfold afterLE
  rcases le_total (toLex (-(ht F p), -(F.slope p))) (toLex (-(ht F q), -(F.slope q))) with h | h <;> simp [h]

theorem fibreListBefore_pairwise (x₀ : ℝ) : (fibreListBefore F x₀).Pairwise (fun p q => beforeLE F p q = true) :=
  List.pairwise_mergeSort (beforeLE_trans F) (beforeLE_total F) _
theorem fibreListAfter_pairwise (x₀ : ℝ) : (fibreListAfter F x₀).Pairwise (fun p q => afterLE F p q = true) :=
  List.pairwise_mergeSort (afterLE_trans F) (afterLE_total F) _

/-- The strands of a fibre point just BEFORE its x-value, top to bottom: none for a left cusp (both arms lie to
the right); two for a right cusp — the arriving arm travels rightward (`true`) and is the upper one iff the later
arm is the lower one, i.e. iff `cuspDisc < 0` (FR-2); one strand, with its direction bit, for any other point. -/
def beforeBits (p : Param F.c) : Cuts :=
  if F.IsLeftCusp p then []
  else if F.IsRightCusp p then (if F.cuspDisc p < 0 then [true, false] else [false, true])
  else [dirBit F p]

/-- The strands of a fibre point just AFTER its x-value, top to bottom: none for a right cusp; two for a left
cusp — the leaving arm travels rightward (`true`) and is the upper one iff `0 < cuspDisc` (FR-2); one otherwise. -/
def afterBits (p : Param F.c) : Cuts :=
  if F.IsRightCusp p then []
  else if F.IsLeftCusp p then (if 0 < F.cuspDisc p then [true, false] else [false, true])
  else [dirBit F p]

/-- the strand entries of a list of fibre points: `(p, j)`, `j` indexing the strands of `p` -/
def entriesOf (bits : Param F.c → Cuts) (L : List (Param F.c)) : List (Param F.c × ℕ) :=
  L.flatMap (fun p => (List.range (bits p).length).map (fun j => (p, j)))

/-- the bit of a strand entry -/
def entryBit (bits : Param F.c → Cuts) (a : Param F.c × ℕ) : Bool := (bits a.1).getD a.2 false

theorem map_entryBit_entriesOf (bits : Param F.c → Cuts) (L : List (Param F.c)) :
    (entriesOf F bits L).map (entryBit F bits) = L.flatMap bits := by
  unfold entriesOf
  rw [List.map_flatMap]
  congr 1
  funext p
  rw [List.map_map]
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, Function.comp, entryBit]
    exact List.getD_eq_getElem _ _ h2

/-- The cut with the fibre points satisfying `P` read "before" and the others "after" (the `P`-points are the
still unprocessed events and everything above them; `P := fun _ => true` gives `cutBefore`, `P := fun _ => false`
gives `cutAfter`). -/
def hybridCutP (x₀ : ℝ) (P : Param F.c → Bool) : Cuts :=
  ((fibreListBefore F x₀).filter P).flatMap (beforeBits F) ++
    ((fibreListAfter F x₀).filter (fun p => !P p)).flatMap (afterBits F)

/-- the strand entries of the hybrid cut, in the order of its bits -/
def hybridEntriesP (x₀ : ℝ) (P : Param F.c → Bool) : List (Param F.c × ℕ) :=
  entriesOf F (beforeBits F) ((fibreListBefore F x₀).filter P) ++
    entriesOf F (afterBits F) ((fibreListAfter F x₀).filter (fun p => !P p))

/-- the cut just left of `x₀` -/
def cutBefore (x₀ : ℝ) : Cuts := (fibreListBefore F x₀).flatMap (beforeBits F)
/-- the cut just right of `x₀` -/
def cutAfter (x₀ : ℝ) : Cuts := (fibreListAfter F x₀).flatMap (afterBits F)
/-- the strand entries just left of `x₀` -/
def entriesBefore (x₀ : ℝ) : List (Param F.c × ℕ) := entriesOf F (beforeBits F) (fibreListBefore F x₀)
/-- the strand entries just right of `x₀` -/
def entriesAfter (x₀ : ℝ) : List (Param F.c × ℕ) := entriesOf F (afterBits F) (fibreListAfter F x₀)
/-- the cut between two events of one x-value `x₀`: the strands at height `≥ z₀` read "before", the strands below
read "after" — the cut just BEFORE the event at height `z₀` is processed -/
def hybridCut (x₀ z₀ : ℝ) : Cuts := hybridCutP F x₀ (fun p => decide (z₀ ≤ ht F p))
/-- the cut just AFTER the event at height `z₀` is processed -/
def hybridCutStrict (x₀ z₀ : ℝ) : Cuts := hybridCutP F x₀ (fun p => decide (z₀ < ht F p))
/-- the strand entries of `hybridCut` -/
def hybridEntries (x₀ z₀ : ℝ) : List (Param F.c × ℕ) := hybridEntriesP F x₀ (fun p => decide (z₀ ≤ ht F p))

theorem cutBefore_eq_hybridCutP (x₀ : ℝ) : cutBefore F x₀ = hybridCutP F x₀ (fun _ => true) := by
  simp [cutBefore, hybridCutP]
theorem cutAfter_eq_hybridCutP (x₀ : ℝ) : cutAfter F x₀ = hybridCutP F x₀ (fun _ => false) := by
  simp [cutAfter, hybridCutP]

/-- `Cont q a`: the parameter `q` lies on the strand of the entry `a = (p, j)`, on the cusp-free arc adjacent to
`p` (no cusp strictly between the lifted parameter `s` of `q` and `p.2`); for a cusp `p` the arm is fixed by `j`:
the upper arm (`j = 0`) is the EARLIER arm (`s < p.2`) iff `cuspDisc p < 0` (FR-2; the same formula for the two
arms before a right cusp and the two arms after a left cusp). -/
def Cont (q : Param F.c) (a : Param F.c × ℕ) : Prop :=
  q.1 = a.1.1 ∧ ∃ s : ℝ, SameParam q (a.1.1, s) ∧ s ≠ a.1.2 ∧
    (∀ u, min s a.1.2 < u → u < max s a.1.2 → ¬ F.IsCusp (a.1.1, u)) ∧
    (F.IsCusp a.1 → ((s < a.1.2) ↔ (a.2 = 0 ↔ F.cuspDisc a.1 < 0)))

/-- the position (1-based, from the top) of a fibre point `q` over `x₀` among the fibre points: one plus the
number of fibre points strictly above it (the position of its strand at a non-singular `x₀`) -/
def posAt (x₀ : ℝ) (q : Param F.c) : ℕ := ((fibreFinset F x₀).filter (fun p => ht F q < ht F p)).card + 1

/-! #### S4. Events, letters, the word -/

/-- the crossings: the over-first pairs -/
abbrev Cross : Type := {q : Param F.c × Param F.c // q ∈ F.crossingPairs}
/-- the singular events of the sweep: cusps and crossings -/
abbrev Event : Type := F.Cusp ⊕ Cross F

/-- a parameter of the event's point (the over branch for a crossing) -/
def evPt : Event F → Param F.c
  | Sum.inl c => c.1
  | Sum.inr q => q.1.1
/-- the x-value of an event -/
def evX (e : Event F) : ℝ := (F.eval (evPt F e)).1
/-- the height of an event -/
def evZ (e : Event F) : ℝ := ht F (evPt F e)
/-- the sweep order of events: by x-value, ties broken bottom to top -/
def evLE (e e' : Event F) : Bool := decide (toLex (evX F e, evZ F e) ≤ toLex (evX F e', evZ F e'))

theorem evLE_trans (e e' e'' : Event F) (h1 : evLE F e e' = true) (h2 : evLE F e' e'' = true) :
    evLE F e e'' = true := by
  unfold evLE at *; rw [decide_eq_true_iff] at *; exact le_trans h1 h2
theorem evLE_total (e e' : Event F) : (evLE F e e' || evLE F e' e) = true := by
  unfold evLE; rcases le_total (toLex (evX F e, evZ F e)) (toLex (evX F e', evZ F e')) with h | h <;> simp [h]

/-- the events in sweep order -/
def events : List (Event F) := (Finset.univ : Finset (Event F)).toList.mergeSort (evLE F)

theorem mem_events (e : Event F) : e ∈ events F := by
  rw [events, List.mem_mergeSort, Finset.mem_toList]; exact Finset.mem_univ _
theorem events_nodup : (events F).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)
theorem events_pairwise_le : (events F).Pairwise (fun e e' => evLE F e e' = true) :=
  List.pairwise_mergeSort (evLE_trans F) (evLE_total F) _

/-- a lawful `BEq` on events (the `Sum` instance is not lawful), for `List.idxOf` -/
instance (priority := high) instBEqEvent : BEq (Event F) := ⟨fun a b => decide (a = b)⟩
instance instLawfulBEqEvent : LawfulBEq (Event F) where
  eq_of_beq {a b} h := of_decide_eq_true h
  rfl {a} := decide_eq_true rfl

/-- some cusp (every front has one) -/
def someCusp : F.Cusp := (exists_two_cusps F ⟨0, F.hc⟩).choose
/-- the event of column `k` (junk beyond the last column) -/
def eventAt (k : ℕ) : Event F := (events F).getD k (Sum.inl (someCusp F))
/-- the column of an event -/
def evIdx (e : Event F) : ℕ := (events F).idxOf e
/-- the x-value of column `k` -/
def colX (k : ℕ) : ℝ := evX F (eventAt F k)
/-- the height of the event of column `k` -/
def colZ (k : ℕ) : ℝ := evZ F (eventAt F k)

theorem evIdx_lt_length (e : Event F) : evIdx F e < (events F).length :=
  List.idxOf_lt_length_iff.mpr (mem_events F e)
theorem eventAt_evIdx (e : Event F) : eventAt F (evIdx F e) = e := by
  unfold eventAt; rw [List.getD_eq_getElem _ _ (evIdx_lt_length F e)]; exact List.getElem_idxOf _
theorem evIdx_eventAt {k : ℕ} (hk : k < (events F).length) : evIdx F (eventAt F k) = k := by
  unfold eventAt; rw [List.getD_eq_getElem _ _ hk]
  exact List.Nodup.idxOf_getElem (events_nodup F) _ _

/-- the position of an event: one plus the number of strands strictly above it in the cut just before it -/
def posOf (e : Event F) : ℕ :=
  (((fibreListBefore F (evX F e)).filter (fun p => decide (evZ F e < ht F p))).flatMap (beforeBits F)).length + 1

/-- The letter read at an event: a left cusp is `l m d` with `d` = "the upper new arm travels rightward" = "the
later arm is the upper one" = `0 < cuspDisc`; a right cusp is `r m`; a crossing is `σ m` (the over branch, of
smaller slope, is the upper strand before the crossing and descends: `σSlotA`). -/
def letterOf (e : Event F) : Letter :=
  match e with
  | Sum.inl c => if F.IsLeftCusp c.1 then Letter.l (posOf F (Sum.inl c)) (decide (0 < F.cuspDisc c.1))
      else Letter.r (posOf F (Sum.inl c))
  | Sum.inr q => Letter.σ (posOf F (Sum.inr q))

/-- THE WORD OF THE SWEEP -/
def word : Word := (events F).map (letterOf F)

theorem length_word : (word F).length = (events F).length := List.length_map _

theorem letterAt_word {k : ℕ} (hk : k < (events F).length) : letterAt (word F) k = letterOf F (eventAt F k) := by
  unfold letterAt word eventAt
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getD_eq_getElem _ _ hk, List.getElem_map]

theorem letterAt_word_evIdx (e : Event F) : letterAt (word F) (evIdx F e) = letterOf F e := by
  rw [letterAt_word F (evIdx_lt_length F e), eventAt_evIdx]

theorem evIdx_lt_length_word (e : Event F) : evIdx F e < (word F).length := by
  rw [length_word]; exact evIdx_lt_length F e

theorem letterAt_word_cross (q : Cross F) : letterAt (word F) (evIdx F (Sum.inr q)) = .σ (posOf F (Sum.inr q)) := by
  rw [letterAt_word_evIdx]; rfl

/-- the column of an x-value: the number of events strictly to its left (for `x ∉ singX` the cut line of `x`) -/
def colAt (x : ℝ) : ℕ := ((events F).filter (fun e => decide (evX F e < x))).length

/-! #### S4 leaves: the word is closed; its counts -/

/-- LEAF (S4): the word of the sweep is closed. -/
theorem word_closed : (word F).Closed := sorry

/-- the closed word of the sweep -/
def oword : OWord := ⟨word F, word_closed F⟩

@[simp] theorem oword_letters : (oword F).letters = word F := rfl

end SweepDefs

section SweepLeaves

variable (F : SmoothFront)

/-! #### S1 leaves: the cut at a non-singular x-value and its one-sided limits -/

/-- LEAF (S1): the sorted fibre list is determined by its specification: a nodup list of exactly the fibre points,
sorted in the "before" order, is `fibreListBefore` (`List.Perm.eq_of_pairwise`; two fibre points with equal
height and slope would be a double point with equal slopes, against `slope_ne_of_isDouble`). -/
theorem fibreListBefore_eq_of (x₀ : ℝ) (L : List (Param F.c)) (hnd : L.Nodup)
    (hmem : ∀ p, p ∈ L ↔ p ∈ totalFibre F x₀) (hsort : L.Pairwise (fun p q => beforeLE F p q = true)) :
    fibreListBefore F x₀ = L := sorry

/-- LEAF (S1): the same for the "after" order. -/
theorem fibreListAfter_eq_of (x₀ : ℝ) (L : List (Param F.c)) (hnd : L.Nodup)
    (hmem : ∀ p, p ∈ L ↔ p ∈ totalFibre F x₀) (hsort : L.Pairwise (fun p q => afterLE F p q = true)) :
    fibreListAfter F x₀ = L := sorry

/-- LEAF (S1): over a non-singular `x₀` every fibre point is regular (`regular_of_notMem_singX`), so both orders
agree (distinct heights, `snd_injOn_totalFibre`), every point has one strand, and the cut is the list of direction
bits of the fibre sorted by height. -/
theorem fibreListAfter_eq_fibreListBefore {x₀ : ℝ} (hx : x₀ ∉ singX F) :
    fibreListAfter F x₀ = fibreListBefore F x₀ := sorry

theorem cutBefore_eq_map_dirBit {x₀ : ℝ} (hx : x₀ ∉ singX F) :
    cutBefore F x₀ = (fibreListBefore F x₀).map (dirBit F) := sorry

theorem cutAfter_eq_cutBefore {x₀ : ℝ} (hx : x₀ ∉ singX F) : cutAfter F x₀ = cutBefore F x₀ := sorry

theorem entriesBefore_eq_of_notMem_singX {x₀ : ℝ} (hx : x₀ ∉ singX F) :
    entriesBefore F x₀ = (fibreListBefore F x₀).map (fun p => (p, 0)) := sorry

/-- LEAF (S1): the local graph structure at a regular parameter: no cusp nearby, `x` injective near `t₀`, and
every `x` near `x(t₀)` has a preimage as close to `t₀` as required (continuity of the inverse; IVT on the
strictly monotone `x`, `strictMonoOn_x_of_isLeftCusp` / `strictAntiOn_x_of_isRightCusp` on the arc through `t₀`,
`exists_arc_mem`). -/
theorem regular_local_graph {i : Fin F.c} {t₀ : ℝ} (h : ¬ F.IsCusp (i, t₀)) :
    ∃ δ > 0, (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), ¬ F.IsCusp (i, t)) ∧
      (∀ t₁ ∈ Set.Ioo (t₀ - δ) (t₀ + δ), ∀ t₂ ∈ Set.Ioo (t₀ - δ) (t₀ + δ), xOf F i t₁ = xOf F i t₂ → t₁ = t₂) ∧
      ∀ δ' ∈ Set.Ioc (0 : ℝ) δ, ∃ η > 0, ∀ x, |x - xOf F i t₀| < η →
        ∃ t ∈ Set.Ioo (t₀ - δ') (t₀ + δ'), xOf F i t = x := sorry

/-- LEAF (S1, compactness): all fibre points over `x` near `x₀` lie (modulo the period) within `δ` of a fibre point
over `x₀` on the same circle — no strand appears from nowhere (`IsCompact.exists_isMinOn` of `|x − x₀|` on the
compact set of parameters of `Fin c × [0,1]` at distance `≥ δ` from the fibre). -/
theorem exists_eta_fibre_near (x₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ x, |x - x₀| < η → ∀ q ∈ totalFibre F x, ∃ p ∈ totalFibre F x₀, q.1 = p.1 ∧
      ∃ n : ℤ, |q.2 + n - p.2| < δ := sorry

/-- LEAF (S1, the left limit at the level of strand entries): just left of any `a`, the entries of the cut are, in
order, continuations (`Cont`) of the entries of `entriesBefore a` (local models S2/S3 at the singular fibre points,
`regular_local_graph` at the regular ones, `exists_eta_fibre_near`, order preserved by continuity of heights, the
list identified through `fibreListBefore_eq_of`). -/
theorem entriesBefore_left_limit (a : ℝ) :
    ∃ η > 0, ∀ x ∈ Set.Ioo (a - η) a, (entriesBefore F x).length = (entriesBefore F a).length ∧
      ∀ j < (entriesBefore F a).length,
        Cont F ((entriesBefore F x).getD j (dfltP F, 0)).1 ((entriesBefore F a).getD j (dfltP F, 0)) := sorry

/-- LEAF (S1, the right limit): just right of any `a`, the entries of the cut are continuations of `entriesAfter a`. -/
theorem entriesAfter_right_limit (a : ℝ) :
    ∃ η > 0, ∀ x ∈ Set.Ioo a (a + η), (entriesBefore F x).length = (entriesAfter F a).length ∧
      ∀ j < (entriesAfter F a).length,
        Cont F ((entriesBefore F x).getD j (dfltP F, 0)).1 ((entriesAfter F a).getD j (dfltP F, 0)) := sorry

/-- LEAF (S1): a continuation carries the bit of its entry: a strand keeps its x-direction along a cusp-free arc
(`xvel_mul_pos_of_cuspFree`), and the arriving arm of a right cusp travels rightward
(`exists_xvel_sign_of_isRightCusp`). -/
theorem dirBit_of_cont_before {q : Param F.c} {a : Param F.c × ℕ} (ha : ¬ F.IsLeftCusp a.1)
    (hj : a.2 < (beforeBits F a.1).length) (h : Cont F q a) : dirBit F q = entryBit F (beforeBits F) a := sorry

/-- LEAF (S1): the same after the x-value: the leaving arm of a left cusp travels rightward. -/
theorem dirBit_of_cont_after {q : Param F.c} {a : Param F.c × ℕ} (ha : ¬ F.IsRightCusp a.1)
    (hj : a.2 < (afterBits F a.1).length) (h : Cont F q a) : dirBit F q = entryBit F (afterBits F) a := sorry

/-- LEAF (S1): the one-sided limits of the cut itself (bits), from the entry-level limits. -/
theorem cutBefore_left_limit (a : ℝ) : ∃ η > 0, ∀ x ∈ Set.Ioo (a - η) a, cutBefore F x = cutBefore F a := sorry

theorem cutAfter_right_limit (a : ℝ) : ∃ η > 0, ∀ x ∈ Set.Ioo a (a + η), cutBefore F x = cutAfter F a := sorry

/-- LEAF (S1): between consecutive singular x-values the cut is constant (`IsLocallyConstant` on the preconnected
gap, from the two limits and `cutAfter_eq_cutBefore`): the cut just right of `a` is the cut just left of `b`. -/
theorem cutAfter_eq_cutBefore_of_gap {a b : ℝ} (hab : a < b) (hgap : ∀ x ∈ Set.Ioo a b, x ∉ singX F) :
    cutAfter F a = cutBefore F b := sorry

/-- LEAF (S1): along a regular arc whose x-values avoid the singular set, the position of the strand in the fibre
and the column of its x-value are constant (the entry-level limits at each non-singular `x` give local constancy). -/
theorem posAt_const_of_arc {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hreg : ∀ t ∈ Set.Icc t₀ t₁, xOf F i t ∉ singX F) :
    posAt F (xOf F i t₀) (i, Int.fract t₀) = posAt F (xOf F i t₁) (i, Int.fract t₁) ∧
      colAt F (xOf F i t₀) = colAt F (xOf F i t₁) := sorry

/-! #### S2 leaves: the cusp local model -/

/-- LEAF (S2, Taylor): the two arms of a cusp at equal `x` — the later arm is the higher one iff `0 < cuspDisc`
(FR-2).  Truth: with `γ'' = (a, c)`, `γ''' = (b, d)`, matched arms `t₁ < t₀ < t₂` satisfy
`z(t₂) − z(t₁) = u³ (ad − bc)/(3a) + o(u³)`, whose sign is that of `a·det(γ'', γ''') = cuspDisc`
(checked numerically, W3_U8R_PLAN.md §2). -/
theorem cusp_arm_sign {i : Fin F.c} {t₀ : ℝ} (h : F.IsCusp (i, t₀)) :
    ∃ δ > 0, ∀ t₁ t₂, t₀ - δ < t₁ → t₁ < t₀ → t₀ < t₂ → t₂ < t₀ + δ → xOf F i t₁ = xOf F i t₂ →
      (zOf F i t₁ < zOf F i t₂ ↔ 0 < F.cuspDisc (i, t₀)) := sorry

/-- LEAF (S2): at a left cusp `x` has a strict local minimum — strictly decreasing before, increasing after — and no
other cusp lies nearby (`exists_no_cusp_near`, the arc monotonicity of §G on the two arcs meeting at the cusp). -/
theorem leftCusp_x_local {i : Fin F.c} {t₀ : ℝ} (h : F.IsLeftCusp (i, t₀)) :
    ∃ δ > 0, (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → ¬ F.IsCusp (i, t)) ∧
      StrictAntiOn (xOf F i) (Set.Ioc (t₀ - δ) t₀) ∧ StrictMonoOn (xOf F i) (Set.Ico t₀ (t₀ + δ)) := sorry

/-- LEAF (S2): at a right cusp `x` has a strict local maximum. -/
theorem rightCusp_x_local {i : Fin F.c} {t₀ : ℝ} (h : F.IsRightCusp (i, t₀)) :
    ∃ δ > 0, (∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → ¬ F.IsCusp (i, t)) ∧
      StrictMonoOn (xOf F i) (Set.Ioc (t₀ - δ) t₀) ∧ StrictAntiOn (xOf F i) (Set.Ico t₀ (t₀ + δ)) := sorry

/-- LEAF (S2): just right of a left cusp's x-value both arms are present, as close to the cusp parameter as
required (IVT on each monotone arm). -/
theorem leftCusp_arms {i : Fin F.c} {t₀ : ℝ} (h : F.IsLeftCusp (i, t₀)) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ η > 0, ∀ x ∈ Set.Ioo (xOf F i t₀) (xOf F i t₀ + η),
      (∃ t₁ ∈ Set.Ioo (t₀ - δ') t₀, xOf F i t₁ = x) ∧ ∃ t₂ ∈ Set.Ioo t₀ (t₀ + δ'), xOf F i t₂ = x := sorry

/-- LEAF (S2): just left of a right cusp's x-value both arms are present. -/
theorem rightCusp_arms {i : Fin F.c} {t₀ : ℝ} (h : F.IsRightCusp (i, t₀)) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ η > 0, ∀ x ∈ Set.Ioo (xOf F i t₀ - η) (xOf F i t₀),
      (∃ t₁ ∈ Set.Ioo (t₀ - δ') t₀, xOf F i t₁ = x) ∧ ∃ t₂ ∈ Set.Ioo t₀ (t₀ + δ'), xOf F i t₂ = x := sorry

/-! #### S3 leaf: the crossing local model -/

/-- LEAF (S3): near a double point the over branch (smaller slope, `IsOverUnder`) is ABOVE the under branch to the
left of the crossing and BELOW it to the right (`z_over − z_under ≈ (s_over − s_under)(x − x₀)`; both branches
regular, `vel_ne_zero_of_isDouble`; derivatives of the two graphs from `hasDerivAt_x` and the chain rule, or the
mean value theorem). -/
theorem cross_height_order {p q : Param F.c} (h : F.IsOverUnder p q) :
    ∃ δ > 0, ∀ t₁ t₂, |t₁ - p.2| < δ → |t₂ - q.2| < δ → xOf F p.1 t₁ = xOf F q.1 t₂ →
      (xOf F p.1 t₁ < (F.eval p).1 → zOf F q.1 t₂ < zOf F p.1 t₁) ∧
      ((F.eval p).1 < xOf F p.1 t₁ → zOf F p.1 t₁ < zOf F q.1 t₂) := sorry

/-! #### S4 leaves: events and the word -/

/-- LEAF (S4): distinct events have distinct points (`cusp_alone` for a cusp against anything, `no_triple` and
`not_swap_mem_crossingPairs` for two crossings). -/
theorem evKey_injective : Function.Injective (fun e : Event F => (evX F e, evZ F e)) := sorry

/-- LEAF (S4): the events are strictly sorted by `(x, z)` (`events_pairwise_le`, `events_nodup`, `evKey_injective`). -/
theorem events_pairwise_lt :
    (events F).Pairwise (fun e e' => toLex (evX F e, evZ F e) < toLex (evX F e', evZ F e')) := sorry

/-- LEAF (S4): columns are ordered by x-value. -/
theorem colX_mono {k k' : ℕ} (hk : k < k') (hk' : k' < (events F).length) : colX F k ≤ colX F k' := sorry

/-- LEAF (S4): the point of an event lies in the fibre over its x-value. -/
theorem evPt_mem_totalFibre (e : Event F) : evPt F e ∈ totalFibre F (evX F e) := sorry

/-- LEAF (S4): every singular fibre point is the point of an event at that x-value (a cusp is `Sum.inl` of its
representative; a double point lies in an over-first pair, `mem_crossingPairs_or_swap`). -/
theorem exists_event_of_singular {x₀ : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F x₀)
    (hs : F.IsCusp p ∨ ∃ q, F.IsDouble p q) : ∃ e : Event F, evX F e = x₀ ∧ evZ F e = ht F p := sorry

/-- LEAF (S4, the local step): the letter of an event is typed at the hybrid cut before it and produces the
hybrid cut after it (`step_prefix` with the prefix of length `posOf e − 1`; the points at height `evZ e` are
exactly the event's point(s), over branch first in the "before" order and under branch first in the "after" order;
`act` on `beforeBits`/`afterBits` of the event: `l` pushes `[d, !d] = afterBits`, `r` removes `beforeBits`
(two distinct bits), `σ` swaps the two branches). -/
theorem step_hybrid (e : Event F) :
    (letterOf F e).step (hybridCut F (evX F e) (evZ F e)) = some (hybridCutStrict F (evX F e) (evZ F e)) := sorry

/-- LEAF (S4): between two consecutive events of one x-value there are only regular strands (`before` = `after`
bits and orders), so the cut after the lower event is the cut before the upper one. -/
theorem hybridCutStrict_eq_hybridCut {k : ℕ} (hk : k + 1 < (events F).length) (hx : colX F k = colX F (k + 1)) :
    hybridCutStrict F (colX F k) (colZ F k) = hybridCut F (colX F (k + 1)) (colZ F (k + 1)) := sorry

/-- LEAF (S4): after the topmost event of an x-value the cut is `cutAfter`. -/
theorem hybridCutStrict_eq_cutAfter {k : ℕ} (hk : k < (events F).length)
    (htop : ∀ e : Event F, evX F e = colX F k → evZ F e ≤ colZ F k) :
    hybridCutStrict F (colX F k) (colZ F k) = cutAfter F (colX F k) := sorry

/-- LEAF (S4): before the lowest event of an x-value the cut is `cutBefore`. -/
theorem hybridCut_eq_cutBefore {k : ℕ} (hk : k < (events F).length)
    (hbot : ∀ e : Event F, evX F e = colX F k → colZ F k ≤ evZ F e) :
    hybridCut F (colX F k) (colZ F k) = cutBefore F (colX F k) := sorry

/-- LEAF (S4): nothing lies left of the first event: the minimum of `x` on the compact front is a cusp (`x' = 0`
there, `no_vertical`), a left cusp, and every fibre point over that x-value is a left cusp (a regular point or a
right cusp would continue to smaller `x`). -/
theorem cutBefore_first : cutBefore F (colX F 0) = [] := sorry

/-- LEAF (S4): nothing lies right of the last event. -/
theorem cutAfter_last : cutAfter F (colX F ((events F).length - 1)) = [] := sorry

/-- LEAF (S4, THE INVARIANT): the run of the word up to column `k` is the hybrid cut before the event of column
`k` (induction on `k`: `cutBefore_first`, `step_hybrid`, then `hybridCutStrict_eq_hybridCut` at a tie or
`hybridCutStrict_eq_cutAfter`, `cutAfter_eq_cutBefore_of_gap`, `hybridCut_eq_cutBefore` at a new x-value). -/
theorem run_take_eq_hybrid {k : ℕ} (hk : k < (events F).length) :
    Word.run ((word F).take k) [] = some (hybridCut F (colX F k) (colZ F k)) := sorry

/-- LEAF (S4): the word is nonempty (every circle has a cusp, `exists_two_cusps`). -/
theorem word_ne_nil : (oword F).letters ≠ [] := sorry

/-- LEAF (S4): one cusp letter per cusp (`List.countP_map`, `Fintype.card` of the `Sum`, `card_cusp`). -/
theorem cuspCount_eq : (word F).cuspCount = F.cuspSet.card := sorry

/-- LEAF (S4): the letter-traced down count is `D(F)`: at a left cusp `downBit (l m d) = 1 ↔ d = false ↔ cuspDisc < 0`;
at a right cusp the bit at position `m` of the hybrid cut (`run_take_eq_hybrid`, `step_hybrid`) is the upper
`beforeBit`, `true ↔ cuspDisc < 0`; crossings contribute `0` (`downCountFrom` unfolded along the run). -/
theorem downCountSyn_eq : (oword F).downCountSyn = F.downCount := sorry

/-- LEAF (S4/S6): for a non-singular `x` the cut of the word at the column of `x` is `cutBefore x`
(`run_take_eq_hybrid`, `hybridCut_eq_cutBefore` / `hybridCutStrict_eq_cutAfter`, `cutAfter_eq_cutBefore_of_gap`;
`[]` on both sides beyond the front). -/
theorem cut_word_colAt {x : ℝ} (hx : x ∉ singX F) : cut (word F) (colAt F x) = cutBefore F x := sorry

end SweepLeaves

/-! #### S5. The slot map `Φ` and the local record clauses -/

section SlotMap

variable (F : SmoothFront)

theorem frontOver_partner_eq_true_of {p : F.Occ} (h : ¬ frontOver F p = true) : frontOver F (partner F p) = true := by
  rw [frontOver_partner]; simpa using h

/-- the crossing (over-first pair) of an occurrence -/
def crossOf (p : F.Occ) : Cross F :=
  if h : frontOver F p = true then ⟨(p.1, (partner F p).1), over_pair_mem_crossingPairs F p h⟩
  else ⟨((partner F p).1, p.1), by
    have := over_pair_mem_crossingPairs F (partner F p) (frontOver_partner_eq_true_of F h)
    rwa [partner_partner] at this⟩

/-- THE SLOT OF AN OCCURRENCE: the descending strand `σSlotA` of its crossing's column if it is the over branch
(smaller slope: above before, below after), the ascending strand `σSlotB` otherwise. -/
def ΦFun (p : F.Occ) : Slot (word F) :=
  if frontOver F p = true then
    σSlotA (word_closed F) (evIdx_lt_length_word F (Sum.inr (crossOf F p))) (letterAt_word_cross F (crossOf F p))
  else σSlotB (word_closed F) (evIdx_lt_length_word F (Sum.inr (crossOf F p))) (letterAt_word_cross F (crossOf F p))

theorem isσSlot_ΦFun (p : F.Occ) : U2.IsσSlot (ΦFun F p) := by
  unfold ΦFun
  split_ifs
  · exact U2.isσSlot_σSlotA (word_closed F) _ _
  · exact U2.isσSlot_σSlotB (word_closed F) _ _

/-- the slot map into the `σ` slots -/
def ΦSub (p : F.Occ) : {u : Slot (word F) // U2.IsσSlot u} := ⟨ΦFun F p, isσSlot_ΦFun F p⟩

/-- LEAF (S5): `Φ` is a bijection onto the `σ` slots (injective: the column determines the crossing and the bit
the branch; surjective: `U2.isσSlot_iff` — every `σ` slot is `σSlotA`/`σSlotB` of a crossing column, whose event is
`Sum.inr q`, the image of `q`'s over/under branch). -/
theorem ΦSub_bijective : Function.Bijective (ΦSub F) := sorry

/-- the occurrence bijection of the record isomorphism -/
def occEquiv : F.Occ ≃ {u : Slot (word F) // U2.IsσSlot u} := Equiv.ofBijective _ (ΦSub_bijective F)

/-- LEAF (S5): the partner goes to the twin slot (`crossOf (partner p) = crossOf p`, `frontOver_partner`,
`U2.σtwin_σSlotA/B`). -/
theorem ΦFun_partner (p : F.Occ) : ΦFun F (partner F p) = U2.σtwin (word_closed F) (ΦFun F p) := sorry

/-- LEAF (S5): over = descending (`U2.isDesc_σSlotA/B`). -/
theorem isDesc_ΦFun (p : F.Occ) : U2.isDesc (ΦFun F p) = frontOver F p := sorry

/-- LEAF (S5): the signs agree: `σsgn` is `+1` iff the two bits of the column agree (`U2.coe_σsgnCol`); by
`run_take_eq_hybrid`/`step_hybrid` those bits are the direction bits of the over and under branches, and
`frontSgn = +1` iff their x-velocities have the same sign (`crossSign_eq_one_iff_of_isOverUnder`,
`crossSign_eq_sign`). -/
theorem σsgn_ΦFun (p : F.Occ) : U2.σsgn (ΦFun F p) = frontSgn F p := sorry

end SlotMap

/-! #### S6. The traversal: cusp vertices, the slot of a strand at its cut line, jumps, `succ ↔ firstReturn` -/

section Traversal

variable (F : SmoothFront)

theorem isSlot_cuspVertex (c : F.Cusp) : IsSlot (word F) (evIdx F (Sum.inl c), 0) := by
  refine Or.inl ⟨rfl, evIdx_lt_length_word F _, ?_⟩
  show (letterAt (word F) (evIdx F (Sum.inl c))).isCrossing = false
  rw [letterAt_word_evIdx]
  dsimp only [letterOf]; split_ifs <;> rfl

/-- the cusp vertex slot of a cusp -/
def cuspVertex (c : F.Cusp) : Slot (word F) := ⟨(evIdx F (Sum.inl c), 0), isSlot_cuspVertex F c⟩

/-- a cusp on each circle -/
def someCuspOn (i : Fin F.c) : F.Cusp := (circleCusps_nonempty F i).choose

theorem someCuspOn_fst (i : Fin F.c) : (someCuspOn F i).1.1 = i :=
  (mem_circleCusps F i _).mp (circleCusps_nonempty F i).choose_spec

/-- the component of a circle: the `next`-cycle of the cusp vertex of one of its cusps -/
def circleComp (i : Fin F.c) : Fin (numComp (word_closed F)) :=
  U2.slotComp (word_closed F) (cuspVertex F (someCuspOn F i))

/-- LEAF (S6): the slot of a strand at its cut line is a slot (`cut_word_colAt`; `posAt ≤` the fibre size). -/
theorem isSlot_slotAt {i : Fin F.c} {t : ℝ} (h : xOf F i t ∉ singX F) :
    IsSlot (word F) (colAt F (xOf F i t), posAt F (xOf F i t) (i, Int.fract t)) := sorry

/-- THE SLOT OF A STRAND at a non-singular x-value: the cut line of that x-value and the strand's position. -/
def slotAt (i : Fin F.c) (t : ℝ) (h : xOf F i t ∉ singX F) : Slot (word F) := ⟨_, isSlot_slotAt F h⟩

/-- LEAF (S6): the slot is constant along a regular arc avoiding the singular x-values (`posAt_const_of_arc`). -/
theorem slotAt_const {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁)
    (hreg : ∀ t ∈ Set.Icc t₀ t₁, xOf F i t ∉ singX F) :
    slotAt F i t₀ (hreg t₀ ⟨le_rfl, h01⟩) = slotAt F i t₁ (hreg t₁ ⟨h01, le_rfl⟩) := sorry

/-- LEAF (S6, jump through a regular point over a singular x-value): the slot advances by `next` steps through the
tie columns (`posR`/`posL` on positions not touched by the letters, `next_cases`, `run_take_eq_hybrid`), meeting no
`σ` slot. -/
theorem jump_regular {i : Fin F.c} {t : ℝ} (hx : xOf F i t ∈ singX F) (hc : ¬ F.IsCusp (i, t))
    (hd : ∀ q, ¬ F.IsDouble (i, t) q) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F i (t - ε') ∉ singX F) (h₂ : xOf F i (t + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F i (t - ε') h₁) = slotAt F i (t + ε') h₂ ∧
      ∀ j < m, ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i (t - ε') h₁)) := sorry

/-- LEAF (S6, jump through a cusp): the slot path passes the cusp vertex (`nextPair_cusp_l/r`, `posR_r_idx`,
`posL_l_idx`) and meets no `σ` slot. -/
theorem jump_cusp (c : F.Cusp) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F c.1.1 (c.1.2 - ε') ∉ singX F)
      (h₂ : xOf F c.1.1 (c.1.2 + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F c.1.1 (c.1.2 - ε') h₁) = slotAt F c.1.1 (c.1.2 + ε') h₂ ∧
      (∀ j < m, ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F c.1.1 (c.1.2 - ε') h₁))) ∧
      ∃ a < m, (next (word_closed F))^[a] (slotAt F c.1.1 (c.1.2 - ε') h₁) = cuspVertex F c := sorry

/-- LEAF (S6, jump through a crossing): the slot path passes exactly one `σ` slot, `Φ p` — reached when the strand
enters the crossing's column `k = evIdx (Sum.inr (crossOf p))` at position `m` (over) or `m+1` (under) from the
left, or at cut `k+1` from the right (`σSlotA`/`σSlotB` unfolded; `posR_σ_idx`, `posL_σ_idx`); NOTE the strand
may first pass tie columns of the same x-value below the crossing, so `Φ p` is in general NOT `slotAt (t_p − ε)`. -/
theorem jump_cross (p : F.Occ) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F p.1.1 (p.1.2 - ε') ∉ singX F)
      (h₂ : xOf F p.1.1 (p.1.2 + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F p.1.1 (p.1.2 - ε') h₁) = slotAt F p.1.1 (p.1.2 + ε') h₂ ∧
      ∃ a < m, (next (word_closed F))^[a] (slotAt F p.1.1 (p.1.2 - ε') h₁) = ΦFun F p ∧
        ∀ j < m, j ≠ a → ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F p.1.1 (p.1.2 - ε') h₁)) := sorry

/-- LEAF (S6, the path): along a parameter interval containing no occurrence of the circle, the slot path
(finitely many singular parameters in `[t₀, t₁]`; `slotAt_const` between them, `jump_regular`/`jump_cusp` at them)
meets no `σ` slot. -/
theorem path_no_occ {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ < t₁) (h₀ : xOf F i t₀ ∉ singX F)
    (h₁ : xOf F i t₁ ∉ singX F) (hno : ∀ p : F.Occ, p.1.1 = i → ∀ s ∈ Set.Ioo t₀ t₁, ¬ SameParam p.1 (i, s)) :
    ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
      ∀ j < m, ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i t₀ h₀)) := sorry

/-! ### S6b helpers -/
section S6bHelpers

/-! #### periodicity of `xOf` and `slotAt` in the parameter -/

theorem s6b_xOf_add_int (i : Fin F.c) (t : ℝ) (n : ℤ) : xOf F i (t + n) = xOf F i t := by
  unfold xOf; rw [(F.comp i).eq_add_int n t]

theorem s6b_fract_add_int (t : ℝ) (n : ℤ) : Int.fract (t + n) = Int.fract t := Int.fract_add_intCast t n

theorem s6b_slotAt_add_int {i : Fin F.c} {t : ℝ} (n : ℤ) (h : xOf F i t ∉ singX F)
    (h' : xOf F i (t + n) ∉ singX F) : slotAt F i (t + n) h' = slotAt F i t h := by
  apply Subtype.ext
  show (colAt F (xOf F i (t + n)), posAt F (xOf F i (t + n)) (i, Int.fract (t + n))) =
    (colAt F (xOf F i t), posAt F (xOf F i t) (i, Int.fract t))
  rw [s6b_xOf_add_int, s6b_fract_add_int]

theorem s6b_notMem_singX_add_int {i : Fin F.c} {t : ℝ} (n : ℤ) (h : xOf F i t ∉ singX F) :
    xOf F i (t + n) ∉ singX F := by rwa [s6b_xOf_add_int]

/-! #### the singular parameters of a circle in a bounded interval form a finite set -/

theorem s6b_singParams_finite (i : Fin F.c) (a b : ℝ) :
    {s : ℝ | s ∈ Set.Ioo a b ∧ xOf F i s ∈ singX F}.Finite := by
  have hsub : {s : ℝ | s ∈ Set.Ioo a b ∧ xOf F i s ∈ singX F} ⊆
      ⋃ x ∈ (singX F : Set ℝ), {s : ℝ | s ∈ Set.Icc a b ∧ xOf F i s = x} := by
    intro s hs
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, exists_prop]
    exact ⟨xOf F i s, hs.2, ⟨hs.1.1.le, hs.1.2.le⟩, rfl⟩
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet _) fun x _ => ?_) hsub
  -- `s ↦ (fract s, ⌊s⌋)` is injective into `fibre × Icc ⌊a⌋ ⌊b⌋`
  have hfin : ((fibre F i x) ×ˢ (Set.Icc (⌊a⌋ : ℤ) ⌊b⌋)).Finite :=
    (fibre_finite F i x).prod (Set.finite_Icc _ _)
  refine Set.Finite.of_finite_image (f := fun s : ℝ => (Int.fract s, ⌊s⌋)) (hfin.subset ?_) ?_
  · rintro ⟨u, n⟩ ⟨s, ⟨⟨hsa, hsb⟩, hsx⟩, hsu⟩
    simp only [Prod.mk.injEq] at hsu
    obtain ⟨rfl, rfl⟩ := hsu
    refine ⟨⟨⟨Int.fract_nonneg s, Int.fract_lt_one s⟩, ?_⟩, Int.floor_le_floor hsa, Int.floor_le_floor hsb⟩
    show xOf F i (Int.fract s) = x
    rw [← hsx]
    have : s = Int.fract s + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
    conv_rhs => rw [this]
    rw [s6b_xOf_add_int]
  · intro s _ s' _ hss'
    simp only [Prod.mk.injEq] at hss'
    have h1 : s = Int.fract s + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
    have h2 : s' = Int.fract s' + (⌊s'⌋ : ℤ) := by rw [Int.fract]; ring
    rw [h1, h2, hss'.1, hss'.2]

/-- the finite set of singular parameters strictly between `a` and `b` -/

def s6b_singParams (i : Fin F.c) (a b : ℝ) : Finset ℝ := (s6b_singParams_finite F i a b).toFinset

theorem s6b_mem_singParams (i : Fin F.c) (a b s : ℝ) :
    s ∈ s6b_singParams F i a b ↔ s ∈ Set.Ioo a b ∧ xOf F i s ∈ singX F := by
  unfold s6b_singParams; rw [Set.Finite.mem_toFinset]; rfl

/-! #### occurrences and cusps at lifted parameters -/

theorem s6b_isCusp_of_cusp_sameParam {i : Fin F.c} {s : ℝ} (c : F.Cusp) (h : SameParam c.1 (i, s)) :
    F.IsCusp (i, s) := (F.isCusp_iff_of_sameParam h).mpr c.isCusp

theorem s6b_not_isCusp_occ (p : F.Occ) : ¬ F.IsCusp p.1 := F.not_isCusp_of_isDouble (isDouble_partner F p)

theorem s6b_isDouble_of_occ_sameParam {i : Fin F.c} {s : ℝ} (p : F.Occ) (h : SameParam p.1 (i, s)) :
    F.IsDouble (i, s) (partner F p).1 := by
  obtain ⟨hne, he⟩ := isDouble_partner F p
  refine ⟨fun hs => hne (h.trans hs), ?_⟩
  rw [SmoothFront.eval_of_sameParam h]; exact he

theorem s6b_not_isCusp_of_occ_sameParam {i : Fin F.c} {s : ℝ} (p : F.Occ) (h : SameParam p.1 (i, s)) :
    ¬ F.IsCusp (i, s) := F.not_isCusp_of_isDouble (s6b_isDouble_of_occ_sameParam F p h)

/-- two occurrences at the same lifted parameter coincide -/

theorem s6b_occ_eq_of_sameParam {i : Fin F.c} {s : ℝ} (p p' : F.Occ) (h : SameParam p.1 (i, s))
    (h' : SameParam p'.1 (i, s)) : p = p' :=
  Subtype.ext (SameParam.eq_of_mem_Ico p.2.1 p'.2.1 (h.trans h'.symm))

theorem s6b_cusp_eq_of_sameParam {i : Fin F.c} {s : ℝ} (c c' : F.Cusp) (h : SameParam c.1 (i, s))
    (h' : SameParam c'.1 (i, s)) : c = c' :=
  Subtype.ext (SameParam.eq_of_mem_Ico c.mem_Ico c'.mem_Ico (h.trans h'.symm))

theorem s6b_sameParam_rep (i : Fin F.c) (s : ℝ) : SameParam (i, Int.fract s) (i, s) :=
  (SameParam.sameParam_rep (i, s)).symm

theorem s6b_eq_fract_add_floor (s : ℝ) : s = Int.fract s + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring

theorem s6b_slotAt_eq_of_eq_add {i : Fin F.c} {t t' : ℝ} {n : ℤ} (e : t' = t + n) (h : xOf F i t ∉ singX F)
    (h' : xOf F i t' ∉ singX F) : slotAt F i t' h' = slotAt F i t h := by
  subst e; exact s6b_slotAt_add_int F n h h'

theorem s6b_notMem_singX_of_eq_add {i : Fin F.c} {t t' : ℝ} {n : ℤ} (e : t' = t + n) (h : xOf F i t ∉ singX F) :
    xOf F i t' ∉ singX F := by subst e; exact s6b_notMem_singX_add_int F n h

/-- the occurrence of a double point at an arbitrary (lifted) parameter -/

theorem s6b_occ_of_isDouble {i : Fin F.c} {s : ℝ} {q : Param F.c} (hd : F.IsDouble (i, s) q) :
    (i, Int.fract s) ∈ F.occSet := by
  refine ⟨⟨Int.fract_nonneg s, Int.fract_lt_one s⟩, SameParam.rep q, SameParam.rep_mem_Ico q, ?_, ?_⟩
  · intro heq
    apply hd.1
    have h1 : SameParam (i, s) (i, Int.fract s) := SameParam.sameParam_rep (i, s)
    have h2 : SameParam q (SameParam.rep q) := SameParam.sameParam_rep q
    rw [← heq] at h2
    exact h1.trans h2.symm
  · rw [SmoothFront.eval_of_sameParam (SameParam.sameParam_rep q)]
    exact (SmoothFront.eval_of_sameParam (SameParam.sameParam_rep (i, s))).trans hd.2

/-- THE JUMP AT ANY SINGULAR PARAMETER (lifted from the three jump leaves by periodicity): the slot path across a
singular parameter `s` of circle `i`; every `σ` slot on it is `Φ` of an occurrence at `s`, and the cusp vertex of
every cusp at `s` is on it. -/

theorem s6b_jump {i : Fin F.c} {s : ℝ} (hs : xOf F i s ∈ singX F) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F i (s - ε') ∉ singX F) (h₂ : xOf F i (s + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F i (s - ε') h₁) = slotAt F i (s + ε') h₂ ∧
      (∀ j < m, U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i (s - ε') h₁)) →
        ∃ p : F.Occ, SameParam p.1 (i, s) ∧ (next (word_closed F))^[j] (slotAt F i (s - ε') h₁) = ΦFun F p) ∧
      (∀ c : F.Cusp, SameParam c.1 (i, s) →
        ∃ a < m, (next (word_closed F))^[a] (slotAt F i (s - ε') h₁) = cuspVertex F c) := by
  by_cases hc : F.IsCusp (i, s)
  · -- a cusp: `jump_cusp` at its representative, shifted by `⌊s⌋`
    obtain ⟨ε, hε, H⟩ := jump_cusp F ⟨SameParam.rep (i, s), F.rep_mem_cuspSet hc⟩
    refine ⟨ε, hε, fun ε' hε' => ?_⟩
    obtain ⟨h₁', h₂', m, hm, hpath, hnoσ, a, ha, hav⟩ := H ε' hε'
    have e₁ : s - ε' = (Int.fract s - ε') + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
    have e₂ : s + ε' = (Int.fract s + ε') + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
    have h₁'' : xOf F i (Int.fract s - ε') ∉ singX F := h₁'
    have h₂'' : xOf F i (Int.fract s + ε') ∉ singX F := h₂'
    refine ⟨s6b_notMem_singX_of_eq_add F e₁ h₁'', s6b_notMem_singX_of_eq_add F e₂ h₂'', m, hm, ?_, ?_, ?_⟩
    · rw [s6b_slotAt_eq_of_eq_add F e₁ h₁'', s6b_slotAt_eq_of_eq_add F e₂ h₂'']; exact hpath
    · intro j hj hσ
      rw [s6b_slotAt_eq_of_eq_add F e₁ h₁''] at hσ
      exact absurd hσ (hnoσ j hj)
    · intro c' hc'
      have hcc : c' = ⟨SameParam.rep (i, s), F.rep_mem_cuspSet hc⟩ :=
        s6b_cusp_eq_of_sameParam F c' _ hc' (s6b_sameParam_rep F i s)
      subst hcc
      refine ⟨a, ha, ?_⟩
      rw [s6b_slotAt_eq_of_eq_add F e₁ h₁'']; exact hav
  · by_cases hd : ∃ q, F.IsDouble (i, s) q
    · -- a double point: `jump_cross` at its occurrence, shifted by `⌊s⌋`
      obtain ⟨q, hq⟩ := hd
      obtain ⟨ε, hε, H⟩ := jump_cross F ⟨(i, Int.fract s), s6b_occ_of_isDouble F hq⟩
      refine ⟨ε, hε, fun ε' hε' => ?_⟩
      obtain ⟨h₁', h₂', m, hm, hpath, a, ha, hav, hnoσ⟩ := H ε' hε'
      have e₁ : s - ε' = (Int.fract s - ε') + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
      have e₂ : s + ε' = (Int.fract s + ε') + (⌊s⌋ : ℤ) := by rw [Int.fract]; ring
      have h₁'' : xOf F i (Int.fract s - ε') ∉ singX F := h₁'
      have h₂'' : xOf F i (Int.fract s + ε') ∉ singX F := h₂'
      refine ⟨s6b_notMem_singX_of_eq_add F e₁ h₁'', s6b_notMem_singX_of_eq_add F e₂ h₂'', m, hm, ?_, ?_, ?_⟩
      · rw [s6b_slotAt_eq_of_eq_add F e₁ h₁'', s6b_slotAt_eq_of_eq_add F e₂ h₂'']; exact hpath
      · intro j hj hσ
        rw [s6b_slotAt_eq_of_eq_add F e₁ h₁''] at hσ ⊢
        by_cases hja : j = a
        · subst hja
          exact ⟨_, s6b_sameParam_rep F i s, hav⟩
        · exact absurd hσ (hnoσ j hj hja)
      · intro c' hc'
        exact absurd (s6b_isCusp_of_cusp_sameParam F c' hc') hc
    · -- a regular point over a singular x-value
      push Not at hd
      obtain ⟨ε, hε, H⟩ := jump_regular F hs hc hd
      refine ⟨ε, hε, fun ε' hε' => ?_⟩
      obtain ⟨h₁', h₂', m, hm, hpath, hnoσ⟩ := H ε' hε'
      exact ⟨h₁', h₂', m, hm, hpath, fun j hj hσ => absurd hσ (hnoσ j hj),
        fun c' hc' => absurd (s6b_isCusp_of_cusp_sameParam F c' hc') hc⟩

/-! #### THE PATH along a parameter interval: induction on the singular parameters inside it -/

/-- `slotAt t₀` reaches `slotAt t₁` by `next` steps; every `σ` slot on the way is `Φ` of an occurrence of the
circle at a parameter strictly inside `(t₀, t₁)`; the cusp vertex of every cusp of the circle strictly inside is
on the way.  (Strong induction on the number of singular parameters inside; `slotAt_const` up to the first one,
`s6b_jump` across it.) -/

theorem s6b_path_aux {i : Fin F.c} {t₁ : ℝ} (h₁ : xOf F i t₁ ∉ singX F) (N : ℕ) :
    ∀ (t₀ : ℝ) (_h01 : t₀ < t₁) (h₀ : xOf F i t₀ ∉ singX F), (s6b_singParams F i t₀ t₁).card = N →
    ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
      (∀ j < m, U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i t₀ h₀)) →
        ∃ p : F.Occ, (∃ s ∈ Set.Ioo t₀ t₁, SameParam p.1 (i, s)) ∧
          (next (word_closed F))^[j] (slotAt F i t₀ h₀) = ΦFun F p) ∧
      (∀ c : F.Cusp, ∀ s ∈ Set.Ioo t₀ t₁, SameParam c.1 (i, s) →
        ∃ a < m, (next (word_closed F))^[a] (slotAt F i t₀ h₀) = cuspVertex F c) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro t₀ h01 h₀ hN
  by_cases hemp : s6b_singParams F i t₀ t₁ = ∅
  · -- no singular parameter inside: the slot is constant
    have hreg : ∀ t ∈ Set.Icc t₀ t₁, xOf F i t ∉ singX F := by
      intro t ht hsing
      rcases eq_or_lt_of_le ht.1 with rfl | hlt
      · exact h₀ hsing
      rcases eq_or_lt_of_le ht.2 with rfl | hlt'
      · exact h₁ hsing
      have : t ∈ s6b_singParams F i t₀ t₁ := (s6b_mem_singParams F i t₀ t₁ t).mpr ⟨⟨hlt, hlt'⟩, hsing⟩
      rw [hemp] at this; exact absurd this (Finset.notMem_empty t)
    refine ⟨0, ?_, fun j hj => absurd hj (Nat.not_lt_zero j), fun c s hs hcs => ?_⟩
    · rw [Function.iterate_zero_apply]
      exact slotAt_const F h01.le hreg
    · exfalso
      have hsing : xOf F i s ∈ singX F := mem_singX_of_isCusp F (s6b_isCusp_of_cusp_sameParam F c hcs)
      have : s ∈ s6b_singParams F i t₀ t₁ := (s6b_mem_singParams F i t₀ t₁ s).mpr ⟨hs, hsing⟩
      rw [hemp] at this; exact absurd this (Finset.notMem_empty s)
  · -- split at the smallest singular parameter `s₁`
    have hne : (s6b_singParams F i t₀ t₁).Nonempty := Finset.nonempty_iff_ne_empty.mpr hemp
    obtain ⟨s₁, hs₁mem, hmin⟩ : ∃ s₁ ∈ s6b_singParams F i t₀ t₁, ∀ s ∈ s6b_singParams F i t₀ t₁, s₁ ≤ s :=
      ⟨_, Finset.min'_mem _ hne, fun s hs => Finset.min'_le _ s hs⟩
    obtain ⟨hs₁Ioo, hs₁sing⟩ := (s6b_mem_singParams F i t₀ t₁ s₁).mp hs₁mem
    -- the gap to the next singular parameter
    obtain ⟨g, hg, hgap⟩ : ∃ g > 0, ∀ s ∈ s6b_singParams F i t₀ t₁, s ≠ s₁ → s₁ + g ≤ s := by
      by_cases hne' : ((s6b_singParams F i t₀ t₁).erase s₁).Nonempty
      · refine ⟨((s6b_singParams F i t₀ t₁).erase s₁).min' hne' - s₁, ?_, fun s hs hss => ?_⟩
        · have hm := Finset.min'_mem _ hne'
          rw [Finset.mem_erase] at hm
          have h1 := hmin _ hm.2
          have h2 := lt_of_le_of_ne h1 (Ne.symm hm.1)
          linarith
        · have : ((s6b_singParams F i t₀ t₁).erase s₁).min' hne' ≤ s :=
            Finset.min'_le _ _ (Finset.mem_erase.mpr ⟨hss, hs⟩)
          linarith
      · exact ⟨1, one_pos, fun s hs hss => absurd ⟨s, Finset.mem_erase.mpr ⟨hss, hs⟩⟩ hne'⟩
    obtain ⟨ε, hε, H⟩ := s6b_jump F hs₁sing
    obtain ⟨ε', hε'pos, hε'ε, hε'a, hε'b, hε'g⟩ :
        ∃ ε' > 0, ε' < ε ∧ ε' < s₁ - t₀ ∧ ε' < t₁ - s₁ ∧ ε' < g := by
      have h1 : 0 < s₁ - t₀ := by linarith [hs₁Ioo.1]
      have h2 : 0 < t₁ - s₁ := by linarith [hs₁Ioo.2]
      have hpos : 0 < min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) := lt_min (lt_min hε h1) (lt_min h2 hg)
      have m1 : min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
      have m2 : min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) ≤ s₁ - t₀ := (min_le_left _ _).trans (min_le_right _ _)
      have m3 : min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) ≤ t₁ - s₁ := (min_le_right _ _).trans (min_le_left _ _)
      have m4 : min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) ≤ g := (min_le_right _ _).trans (min_le_right _ _)
      exact ⟨min (min ε (s₁ - t₀)) (min (t₁ - s₁) g) / 2, half_pos hpos, by linarith, by linarith, by linarith,
        by linarith⟩
    obtain ⟨h₁', h₂', m₁, hm₁, hpath₁, hσ₁, hcusp₁⟩ := H ε' ⟨hε'pos, hε'ε⟩
    -- the slot is constant from `t₀` to `s₁ - ε'`
    have hA : ∀ t ∈ Set.Icc t₀ (s₁ - ε'), xOf F i t ∉ singX F := by
      intro t ht hsing
      rcases eq_or_lt_of_le ht.1 with rfl | hlt
      · exact h₀ hsing
      have htS : t ∈ s6b_singParams F i t₀ t₁ :=
        (s6b_mem_singParams F i t₀ t₁ t).mpr ⟨⟨hlt, by linarith [ht.2, hs₁Ioo.2]⟩, hsing⟩
      have := hmin t htS
      linarith [ht.2]
    have hconst : slotAt F i t₀ h₀ = slotAt F i (s₁ - ε') h₁' := slotAt_const F (by linarith) hA
    -- the induction hypothesis from `s₁ + ε'`
    have hcard : (s6b_singParams F i (s₁ + ε') t₁).card < N := by
      rw [← hN]
      apply Finset.card_lt_card
      have hsub : s6b_singParams F i (s₁ + ε') t₁ ⊆ s6b_singParams F i t₀ t₁ := by
        intro s hs
        obtain ⟨hsI, hss⟩ := (s6b_mem_singParams F i _ _ s).mp hs
        exact (s6b_mem_singParams F i t₀ t₁ s).mpr ⟨⟨by linarith [hsI.1, hs₁Ioo.1], hsI.2⟩, hss⟩
      refine (Finset.ssubset_iff_of_subset hsub).mpr ⟨s₁, hs₁mem, fun h => ?_⟩
      have := ((s6b_mem_singParams F i _ _ s₁).mp h).1.1
      linarith
    obtain ⟨m₂, hpath₂, hσ₂, hcusp₂⟩ := ih _ hcard (s₁ + ε') (by linarith) h₂' rfl
    refine ⟨m₂ + m₁, ?_, ?_, ?_⟩
    · rw [Function.iterate_add_apply, hconst, hpath₁, hpath₂]
    · intro j hj hσ
      rw [hconst] at hσ ⊢
      by_cases hjm : j < m₁
      · obtain ⟨p, hp, hpj⟩ := hσ₁ j hjm hσ
        exact ⟨p, ⟨s₁, hs₁Ioo, hp⟩, hpj⟩
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + m₁ := ⟨j - m₁, by omega⟩
        rw [Function.iterate_add_apply, hpath₁] at hσ ⊢
        obtain ⟨p, ⟨s, hs, hp⟩, hpj⟩ := hσ₂ j' (by omega) hσ
        exact ⟨p, ⟨s, ⟨by linarith [hs.1, hs₁Ioo.1], hs.2⟩, hp⟩, hpj⟩
    · intro c s hs hcs
      have hsing : xOf F i s ∈ singX F := mem_singX_of_isCusp F (s6b_isCusp_of_cusp_sameParam F c hcs)
      have hsS : s ∈ s6b_singParams F i t₀ t₁ := (s6b_mem_singParams F i t₀ t₁ s).mpr ⟨hs, hsing⟩
      rw [hconst]
      by_cases hss : s = s₁
      · rw [hss] at hcs
        obtain ⟨a, ha, hav⟩ := hcusp₁ c hcs
        exact ⟨a, by omega, hav⟩
      · have hge := hgap s hsS hss
        obtain ⟨a, ha, hav⟩ := hcusp₂ c s ⟨by linarith, hs.2⟩ hcs
        refine ⟨a + m₁, by omega, ?_⟩
        rw [Function.iterate_add_apply, hpath₁]; exact hav

/-- the path lemma in its direct form -/

theorem s6b_path {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ < t₁) (h₀ : xOf F i t₀ ∉ singX F)
    (h₁ : xOf F i t₁ ∉ singX F) :
    ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
      (∀ j < m, U2.IsσSlot ((next (word_closed F))^[j] (slotAt F i t₀ h₀)) →
        ∃ p : F.Occ, (∃ s ∈ Set.Ioo t₀ t₁, SameParam p.1 (i, s)) ∧
          (next (word_closed F))^[j] (slotAt F i t₀ h₀) = ΦFun F p) ∧
      (∀ c : F.Cusp, ∀ s ∈ Set.Ioo t₀ t₁, SameParam c.1 (i, s) →
        ∃ a < m, (next (word_closed F))^[a] (slotAt F i t₀ h₀) = cuspVertex F c) :=
  s6b_path_aux F h₁ _ t₀ h01 h₀ rfl

/-! #### cycles: slots of one circle lie on one cycle; a slot with position `0` is a cusp vertex -/

theorem s6b_sameCycle_slotAt {i : Fin F.c} {t t' : ℝ} (h : xOf F i t ∉ singX F) (h' : xOf F i t' ∉ singX F) :
    (nextPerm (word_closed F)).SameCycle (slotAt F i t h) (slotAt F i t' h') := by
  rcases lt_trichotomy t t' with hlt | rfl | hgt
  · obtain ⟨m, hm, -, -⟩ := s6b_path F hlt h h'
    exact sameCycle_of_iterate (word_closed F) (a := m) (b := 0) (by rw [Function.iterate_zero_apply]; exact hm)
  · exact Equiv.Perm.SameCycle.refl _ _
  · obtain ⟨m, hm, -, -⟩ := s6b_path F hgt h' h
    exact (sameCycle_of_iterate (word_closed F) (a := m) (b := 0)
      (by rw [Function.iterate_zero_apply]; exact hm)).symm

theorem s6b_slotAt_fst_eq {i j : Fin F.c} (hij : j = i) {t : ℝ} (h : xOf F j t ∉ singX F)
    (h' : xOf F i t ∉ singX F) : slotAt F j t h = slotAt F i t h' := by subst hij; rfl

/-- the cusp vertex of a cusp lies on the cycle of its circle -/

theorem s6b_sameCycle_cuspVertex (c : F.Cusp) {t : ℝ} (h : xOf F c.1.1 t ∉ singX F) :
    (nextPerm (word_closed F)).SameCycle (slotAt F c.1.1 t h) (cuspVertex F c) := by
  obtain ⟨ε, hε, H⟩ := jump_cusp F c
  obtain ⟨h₁, -, m, -, -, -, a, -, hav⟩ := H (ε / 2) ⟨half_pos hε, half_lt_self hε⟩
  exact (s6b_sameCycle_slotAt F h h₁).trans
    (sameCycle_of_iterate (word_closed F) (a := a) (b := 0) (by rw [Function.iterate_zero_apply]; exact hav))

/-- the slot of an occurrence lies on the cycle of its circle -/

theorem s6b_sameCycle_ΦFun (p : F.Occ) {t : ℝ} (h : xOf F p.1.1 t ∉ singX F) :
    (nextPerm (word_closed F)).SameCycle (slotAt F p.1.1 t h) (ΦFun F p) := by
  obtain ⟨ε, hε, H⟩ := jump_cross F p
  obtain ⟨h₁, -, m, -, -, a, -, hav, -⟩ := H (ε / 2) ⟨half_pos hε, half_lt_self hε⟩
  exact (s6b_sameCycle_slotAt F h h₁).trans
    (sameCycle_of_iterate (word_closed F) (a := a) (b := 0) (by rw [Function.iterate_zero_apply]; exact hav))

/-- every circle has a non-singular parameter -/

theorem s6b_exists_regular (i : Fin F.c) : ∃ t : ℝ, xOf F i t ∉ singX F := by
  obtain ⟨ε, hε, H⟩ := jump_cusp F (someCuspOn F i)
  obtain ⟨h₁, -⟩ := H (ε / 2) ⟨half_pos hε, half_lt_self hε⟩
  refine ⟨(someCuspOn F i).1.2 - ε / 2, ?_⟩
  rwa [someCuspOn_fst] at h₁

/-- the cycle of a cusp vertex is the component of its circle -/

theorem s6b_slotComp_cuspVertex (c : F.Cusp) :
    U2.slotComp (word_closed F) (cuspVertex F c) = circleComp F c.1.1 := by
  unfold circleComp
  rw [U2.slotComp_eq_iff]
  obtain ⟨t, ht⟩ := s6b_exists_regular F c.1.1
  have ht' : xOf F (someCuspOn F c.1.1).1.1 t ∉ singX F := by rwa [someCuspOn_fst]
  have e := s6b_slotAt_fst_eq F (someCuspOn_fst F c.1.1) ht' ht
  have h2 := s6b_sameCycle_cuspVertex F (someCuspOn F c.1.1) ht'
  rw [e] at h2
  exact (s6b_sameCycle_cuspVertex F c ht).symm.trans h2

/-- a slot at position `0` is the cusp vertex of the cusp of its column -/

theorem s6b_cuspVertex_of_snd_eq_zero (u : Slot (word F)) (h : u.1.2 = 0) : ∃ c : F.Cusp, u = cuspVertex F c := by
  obtain ⟨⟨k, p⟩, hu⟩ := u
  simp only at h
  subst h
  rcases hu with ⟨-, hk, hσ⟩ | ⟨h1, -, -⟩
  · have hk' : k < (events F).length := by rwa [length_word] at hk
    have hl := letterAt_word F hk'
    rcases he : eventAt F k with c | q
    · refine ⟨c, Subtype.ext ?_⟩
      show (k, 0) = (evIdx F (Sum.inl c), 0)
      rw [← he, evIdx_eventAt F hk']
    · exfalso
      simp only at hσ
      rw [hl, he] at hσ
      exact absurd hσ (by simp [letterOf, isCrossing])
  · simp at h1

/-! #### the cyclic successor of an occurrence: no occurrence strictly between, and the shifted crossing jump -/

/-- `jump_cross` at the parameter `p.1.2 + n` (periodicity) -/

theorem s6b_jump_cross_shift (p : F.Occ) (n : ℤ) :
    ∃ ε > 0, ∀ ε' ∈ Set.Ioo (0 : ℝ) ε, ∃ (h₁ : xOf F p.1.1 (p.1.2 + n - ε') ∉ singX F)
      (h₂ : xOf F p.1.1 (p.1.2 + n + ε') ∉ singX F) (m : ℕ),
      0 < m ∧ (next (word_closed F))^[m] (slotAt F p.1.1 (p.1.2 + n - ε') h₁) = slotAt F p.1.1 (p.1.2 + n + ε') h₂ ∧
      ∃ a < m, (next (word_closed F))^[a] (slotAt F p.1.1 (p.1.2 + n - ε') h₁) = ΦFun F p ∧
        ∀ j < m, j ≠ a → ¬ U2.IsσSlot ((next (word_closed F))^[j] (slotAt F p.1.1 (p.1.2 + n - ε') h₁)) := by
  obtain ⟨ε, hε, H⟩ := jump_cross F p
  refine ⟨ε, hε, fun ε' hε' => ?_⟩
  obtain ⟨h₁', h₂', m, hm, hpath, a, ha, hav, hnoσ⟩ := H ε' hε'
  have e₁ : p.1.2 + n - ε' = (p.1.2 - ε') + n := by ring
  have e₂ : p.1.2 + n + ε' = (p.1.2 + ε') + n := by ring
  refine ⟨s6b_notMem_singX_of_eq_add F e₁ h₁', s6b_notMem_singX_of_eq_add F e₂ h₂', m, hm, ?_, a, ha, ?_, ?_⟩
  · rw [s6b_slotAt_eq_of_eq_add F e₁ h₁', s6b_slotAt_eq_of_eq_add F e₂ h₂']; exact hpath
  · rw [s6b_slotAt_eq_of_eq_add F e₁ h₁']; exact hav
  · intro j hj hja
    rw [s6b_slotAt_eq_of_eq_add F e₁ h₁']
    exact hnoσ j hj hja

/-- no occurrence of the circle lies strictly between `p` and its cyclic successor (lifted to the real line:
the successor's parameter is read in `(p.1.2, p.1.2 + 1]`) -/

theorem s6b_no_occ_between (p q : F.Occ) {n : ℤ}
    (hn : n = if p.1.2 < (cycNext (occComp F) (occKey F) (occKey_inj F) p).1.2 then 0 else 1) {s : ℝ}
    (hs : s ∈ Set.Ioo p.1.2 ((cycNext (occComp F) (occKey F) (occKey_inj F) p).1.2 + n))
    (hq : SameParam q.1 (p.1.1, s)) : False := by
  obtain ⟨p', hp'⟩ : ∃ p', p' = cycNext (occComp F) (occKey F) (occKey_inj F) p := ⟨_, rfl⟩
  rw [← hp'] at hn hs
  have hcomp : occComp F p' = occComp F p := by rw [hp']; exact comp_cycNext (occComp F) (occKey F) (occKey_inj F) p
  have hqcomp : occComp F q = occComp F p := hq.1
  have hnb : ¬ cycBetween p.1.2 q.1.2 p'.1.2 := by
    have := cycNext_no_between (occComp F) (occKey F) (occKey_inj F) p q hqcomp
    rw [← hp'] at this
    exact this
  obtain ⟨-, z, hz⟩ := hq
  simp only at hz
  have hq0 := (SmoothFront.Occ.mem_Ico F q).1
  have hq1 := (SmoothFront.Occ.mem_Ico F q).2
  have hp0 := (SmoothFront.Occ.mem_Ico F p).1
  have hp1 := (SmoothFront.Occ.mem_Ico F p).2
  have hp'0 := (SmoothFront.Occ.mem_Ico F p').1
  have hp'1 := (SmoothFront.Occ.mem_Ico F p').2
  obtain ⟨hs1, hs2⟩ := hs
  by_cases hab : p.1.2 < p'.1.2
  · rw [if_pos hab] at hn
    subst hn
    push_cast at hs2
    -- `s ∈ (a, b) ⊆ [0, 1)`, so `z = 0`
    have hz1 : (z : ℝ) < 1 := by linarith
    have hz2 : (-1 : ℝ) < z := by linarith
    have hz3 : z < 1 := by exact_mod_cast hz1
    have hz4 : -1 < z := by exact_mod_cast hz2
    have hz0 : z = 0 := by omega
    subst hz0
    simp only [Int.cast_zero, add_zero] at hz
    exact hnb (Or.inl ⟨by linarith, by linarith⟩)
  · rw [if_neg hab] at hn
    subst hn
    push_cast at hs2
    push Not at hab
    rcases eq_or_lt_of_le hab with heq | hlt
    · -- `p' = p`: `p` is alone on its circle, so `q = p`, impossible strictly inside one period
      have hpp : p' = p := occKey_inj F p' p hcomp heq
      have halone : ∀ w : F.Occ, occComp F w = occComp F p → w = p := by
        intro w hw
        by_contra hne
        exact cycNext_ne_self (occComp F) (occKey F) (occKey_inj F) p w hw hne (hpp ▸ hp'.symm)
      have hqp : q = p := halone q hqcomp
      subst hqp
      rw [heq] at hs2
      have hz1 : (z : ℝ) < 1 := by linarith
      have hz2 : (0 : ℝ) < z := by linarith
      have hz3 : z < 1 := by exact_mod_cast hz1
      have hz4 : 0 < z := by exact_mod_cast hz2
      omega
    · by_cases hs1' : s < 1
      · have hz1 : (z : ℝ) < 1 := by linarith
        have hz2 : (-1 : ℝ) < z := by linarith
        have hz3 : z < 1 := by exact_mod_cast hz1
        have hz4 : -1 < z := by exact_mod_cast hz2
        have hz0 : z = 0 := by omega
        subst hz0
        simp only [Int.cast_zero, add_zero] at hz
        exact hnb (Or.inr (Or.inr ⟨hlt, by linarith⟩))
      · push Not at hs1'
        have hz1 : (z : ℝ) < 2 := by linarith
        have hz2 : (0 : ℝ) < z := by linarith
        have hz3 : z < 2 := by exact_mod_cast hz1
        have hz4 : 0 < z := by exact_mod_cast hz2
        have hz0 : z = 1 := by omega
        subst hz0
        simp only [Int.cast_one] at hz
        exact hnb (Or.inr (Or.inl ⟨by linarith, hlt⟩))

/-! #### CORE: the circle of a slot is preserved by `next`.  Stage 1: list lemmas -/

/-- splitting a filter of a list antitone in `f`: `P = Q ∨ R` with every `R`-value strictly below every `Q`-value -/

theorem s6b_filter_split {α : Type*} (f : α → ℝ) (P Q R : α → Bool) (hPQR : ∀ p, P p = (Q p || R p))
    (hRQ : ∀ p q, R p = true → Q q = true → f p < f q) :
    ∀ L : List α, L.Pairwise (fun p q => f q ≤ f p) → L.filter P = L.filter Q ++ L.filter R := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons p L ih =>
    intro hL
    rw [List.pairwise_cons] at hL
    obtain ⟨hp, hL⟩ := hL
    have ih' := ih hL
    by_cases hQ : Q p = true
    · have hP : P p = true := by rw [hPQR, hQ]; rfl
      have hR : R p = false := by
        by_contra h
        exact lt_irrefl _ (hRQ p p (by simpa using h) hQ)
      simp [List.filter_cons, hP, hQ, hR, ih']
    · have hQ' : Q p = false := by simpa using hQ
      by_cases hR : R p = true
      · have hP : P p = true := by rw [hPQR, hR]; simp
        have hQL : L.filter Q = [] := by
          rw [List.filter_eq_nil_iff]
          intro q hq hQq
          have h1 := hRQ p q hR hQq
          have h2 := hp q hq
          linarith
        have hPL : L.filter P = L.filter R := by
          apply List.filter_congr
          intro q hq
          rw [hPQR]
          have hQq : Q q = false := by
            by_contra h
            have h' : Q q = true := by simpa using h
            have h1 := hRQ p q hR h'
            have h2 := hp q hq
            linarith
          rw [hQq]; rfl
        simp [List.filter_cons, hP, hQ', hR, hQL, hPL]
      · have hR' : R p = false := by simpa using hR
        have hP : P p = false := by rw [hPQR, hQ', hR']; rfl
        simp [List.filter_cons, hP, hQ', hR', ih']

theorem s6b_entriesOf_append (bits : Param F.c → Cuts) (L L' : List (Param F.c)) :
    entriesOf F bits (L ++ L') = entriesOf F bits L ++ entriesOf F bits L' := by
  unfold entriesOf; rw [List.flatMap_append]

/-- the entries depend only on the number of bits of each point -/

theorem s6b_entriesOf_congr (bits bits' : Param F.c → Cuts) (L : List (Param F.c))
    (h : ∀ p ∈ L, (bits p).length = (bits' p).length) : entriesOf F bits L = entriesOf F bits' L := by
  unfold entriesOf
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h p (by simp), ih (fun q hq => h q (by simp [hq]))]

theorem s6b_entriesOf_singleton (bits : Param F.c → Cuts) (p : Param F.c) :
    entriesOf F bits [p] = (List.range (bits p).length).map (fun j => (p, j)) := by
  unfold entriesOf; simp

theorem s6b_entriesOf_eq_map (bits : Param F.c → Cuts) (L : List (Param F.c)) (h : ∀ p ∈ L, (bits p).length = 1) :
    entriesOf F bits L = L.map (fun p => (p, 0)) := by
  unfold entriesOf
  induction L with
  | nil => rfl
  | cons p L ih =>
    rw [List.flatMap_cons, List.map_cons, h p (by simp), ih (fun q hq => h q (by simp [hq]))]
    rfl

theorem s6b_length_entriesOf (bits : Param F.c → Cuts) (L : List (Param F.c)) :
    (entriesOf F bits L).length = (L.flatMap bits).length := by
  rw [← map_entryBit_entriesOf F bits L, List.length_map]

theorem s6b_eq_singleton_of_nodup {α : Type*} {L : List α} {a : α} (hnd : L.Nodup) (ha : a ∈ L)
    (h : ∀ b ∈ L, b = a) : L = [a] := by
  cases L with
  | nil => exact absurd ha (List.not_mem_nil)
  | cons b L' =>
    cases L' with
    | nil => rw [h b (by simp)]
    | cons c L'' =>
      exfalso
      have hb := h b (by simp)
      have hc := h c (by simp)
      rw [List.nodup_cons] at hnd
      exact hnd.1 (by rw [hb, ← hc]; simp)

theorem s6b_eq_pair_of_nodup_sorted {α : Type*} {L : List α} {o u : α} (R : α → α → Prop) (hnd : L.Nodup)
    (hmem : ∀ p, p ∈ L ↔ p = o ∨ p = u) (hne : o ≠ u) (hsort : L.Pairwise R) (hR : ¬ R u o) : L = [o, u] := by
  have hperm : L.Perm [o, u] :=
    (List.perm_ext_iff_of_nodup hnd (by simp [hne])).mpr (fun p => by rw [hmem]; simp)
  have hlen : L.length = 2 := by rw [hperm.length_eq]; rfl
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
  have ha : a = o ∨ a = u := (hmem a).mp (by simp)
  have hb : b = o ∨ b = u := (hmem b).mp (by simp)
  have hab : a ≠ b := by rw [List.nodup_cons] at hnd; simpa using hnd.1
  rw [List.pairwise_cons] at hsort
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · rfl
  · exact absurd (hsort.1 _ (by simp)) hR
  · exact absurd rfl hab

/-- two strictly `f`-sorted lists with the same members are equal -/

theorem s6b_sorted_eq {α : Type*} (f : α → ℝ) {L L' : List α} (hL : L.Pairwise (fun p q => f q < f p))
    (hL' : L'.Pairwise (fun p q => f q < f p)) (hmem : ∀ p, p ∈ L ↔ p ∈ L') : L = L' := by
  have : Std.Irrefl (fun p q : α => f q < f p) := ⟨fun p => lt_irrefl _⟩
  have : Std.Antisymm (fun p q : α => f q < f p) := ⟨fun p q h1 h2 => absurd (h1.trans h2) (lt_irrefl _)⟩
  exact List.Pairwise.eq_of_mem_iff hL hL' hmem

/-! #### Stage 2: the sorted events and regular fibre points -/

theorem s6b_colX_evIdx (e : Event F) : colX F (evIdx F e) = evX F e := by unfold colX; rw [eventAt_evIdx]

theorem s6b_colZ_evIdx (e : Event F) : colZ F (evIdx F e) = evZ F e := by unfold colZ; rw [eventAt_evIdx]

theorem s6b_fst_le_of_lex_lt {a b : ℝ × ℝ} (h : toLex a < toLex b) : a.1 ≤ b.1 := by
  rw [Prod.Lex.lt_iff] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

theorem s6b_key_lt_of_idx_lt {j j' : ℕ} (hj' : j' < (events F).length) (hjj' : j < j') :
    toLex (colX F j, colZ F j) < toLex (colX F j', colZ F j') := by
  have h := List.pairwise_iff_getElem.mp (events_pairwise_lt F) j j' (lt_trans hjj' hj') hj' hjj'
  unfold colX colZ eventAt
  rw [List.getD_eq_getElem _ _ (lt_trans hjj' hj'), List.getD_eq_getElem _ _ hj']
  exact h

theorem s6b_idx_lt_of_key_lt (e e' : Event F) (h : toLex (evX F e, evZ F e) < toLex (evX F e', evZ F e')) :
    evIdx F e < evIdx F e' := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · have hee : e = e' := by rw [← eventAt_evIdx F e, ← eventAt_evIdx F e', heq]
    subst hee
    exact lt_irrefl _ h
  · have h2 := s6b_key_lt_of_idx_lt F (evIdx_lt_length F e) hlt
    rw [s6b_colX_evIdx, s6b_colZ_evIdx, s6b_colX_evIdx, s6b_colZ_evIdx] at h2
    exact lt_asymm h h2

/-- no event lies strictly between two consecutive columns in the `(x, z)` order -/

theorem s6b_no_event_between {k : ℕ} (hk : k + 1 < (events F).length) (e : Event F)
    (h₀ : toLex (colX F k, colZ F k) < toLex (evX F e, evZ F e))
    (h₁ : toLex (evX F e, evZ F e) < toLex (colX F (k + 1), colZ F (k + 1))) : False := by
  have hk' : k < (events F).length := by omega
  have h0 := s6b_idx_lt_of_key_lt F (eventAt F k) e h₀
  have h1 := s6b_idx_lt_of_key_lt F e (eventAt F (k + 1)) h₁
  rw [evIdx_eventAt F hk'] at h0
  rw [evIdx_eventAt F hk] at h1
  omega

/-- the top event of an x-value: when the next column has a larger `x` (or there is none), no event at this `x`
is higher -/

theorem s6b_top {k : ℕ} (hk : k < (events F).length)
    (hnext : k + 1 = (events F).length ∨ colX F k < colX F (k + 1)) (e : Event F) (hx : evX F e = colX F k) :
    evZ F e ≤ colZ F k := by
  by_contra hlt
  push Not at hlt
  have hkey : toLex (colX F k, colZ F k) < toLex (evX F e, evZ F e) := by
    rw [Prod.Lex.lt_iff]; right; exact ⟨hx.symm, hlt⟩
  have hidx := s6b_idx_lt_of_key_lt F (eventAt F k) e hkey
  rw [evIdx_eventAt F hk] at hidx
  have hlen := evIdx_lt_length F e
  rcases hnext with hn | hn
  · omega
  · rcases eq_or_lt_of_le (show k + 1 ≤ evIdx F e by omega) with heq | hlt'
    · have := s6b_colX_evIdx F e
      rw [← heq] at this
      linarith
    · have h2 := s6b_fst_le_of_lex_lt (s6b_key_lt_of_idx_lt F hlen hlt')
      simp only at h2
      rw [s6b_colX_evIdx] at h2
      linarith

/-- the bottom event of an x-value: when the previous column has a smaller `x` (or there is none), no event at
this `x` is lower -/

theorem s6b_bot {k : ℕ} (hk : k < (events F).length) (hprev : k = 0 ∨ colX F (k - 1) < colX F k) (e : Event F)
    (hx : evX F e = colX F k) : colZ F k ≤ evZ F e := by
  by_contra hlt
  push Not at hlt
  have hkey : toLex (evX F e, evZ F e) < toLex (colX F k, colZ F k) := by
    rw [Prod.Lex.lt_iff]; right; exact ⟨hx, hlt⟩
  have hidx := s6b_idx_lt_of_key_lt F e (eventAt F k) hkey
  rw [evIdx_eventAt F hk] at hidx
  rcases hprev with hn | hn
  · omega
  · rcases eq_or_lt_of_le (show evIdx F e ≤ k - 1 by omega) with heq | hlt'
    · have := s6b_colX_evIdx F e
      rw [heq] at this
      linarith
    · have h2 := s6b_fst_le_of_lex_lt (s6b_key_lt_of_idx_lt F (show k - 1 < (events F).length by omega) hlt')
      simp only at h2
      rw [s6b_colX_evIdx] at h2
      linarith

/-- a fibre point whose height is not the height of any event at its x-value is regular -/

theorem s6b_regular_of_no_event {x : ℝ} {p : Param F.c} (hp : p ∈ totalFibre F x)
    (hno : ∀ e : Event F, evX F e = x → evZ F e ≠ ht F p) : ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q := by
  by_contra h
  have hs : F.IsCusp p ∨ ∃ q, F.IsDouble p q := by
    by_cases hc : F.IsCusp p
    · exact Or.inl hc
    · right
      by_contra hq
      push Not at hq
      exact h ⟨hc, hq⟩
  obtain ⟨e, hex, hez⟩ := exists_event_of_singular F hp hs
  exact hno e hex hez

theorem s6b_beforeBits_regular {p : Param F.c} (hc : ¬ F.IsCusp p) : beforeBits F p = [dirBit F p] := by
  unfold beforeBits
  rw [if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]

theorem s6b_afterBits_regular {p : Param F.c} (hc : ¬ F.IsCusp p) : afterBits F p = [dirBit F p] := by
  unfold afterBits
  rw [if_neg (fun h => hc h.1), if_neg (fun h => hc h.1)]

theorem s6b_ht_le_of_beforeLE {p q : Param F.c} (h : beforeLE F p q = true) : ht F q ≤ ht F p := by
  unfold beforeLE at h
  rw [decide_eq_true_iff, Prod.Lex.le_iff] at h
  rcases h with h | ⟨h, -⟩ <;> simp only [ofLex_toLex] at h <;> linarith

theorem s6b_ht_le_of_afterLE {p q : Param F.c} (h : afterLE F p q = true) : ht F q ≤ ht F p := by
  unfold afterLE at h
  rw [decide_eq_true_iff, Prod.Lex.le_iff] at h
  rcases h with h | ⟨h, -⟩ <;> simp only [ofLex_toLex] at h <;> linarith

theorem s6b_fibreListBefore_antitone (x : ℝ) : (fibreListBefore F x).Pairwise (fun p q => ht F q ≤ ht F p) :=
  (fibreListBefore_pairwise F x).imp (s6b_ht_le_of_beforeLE F)

theorem s6b_fibreListAfter_antitone (x : ℝ) : (fibreListAfter F x).Pairwise (fun p q => ht F q ≤ ht F p) :=
  (fibreListAfter_pairwise F x).imp (s6b_ht_le_of_afterLE F)

/-- two fibre points over one `x` at the same height coincide when one of them is not a double point -/

theorem s6b_ht_inj_of_regular {x : ℝ} {p q : Param F.c} (hp : p ∈ totalFibre F x) (hq : q ∈ totalFibre F x)
    (hreg : ∀ q', ¬ F.IsDouble p q') (h : ht F p = ht F q) : p = q := by
  by_contra hne
  exact hreg q ⟨fun hs => hne (SameParam.eq_of_mem_Ico hp.1 hq.1 hs), Prod.ext (hp.2.trans hq.2.symm) h⟩

theorem s6b_pairwise_lt_of_regular (x : ℝ) (L : List (Param F.c)) (hnd : L.Nodup)
    (hmemL : ∀ p ∈ L, p ∈ totalFibre F x) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p))
    (hreg : ∀ p ∈ L, ∀ q, ¬ F.IsDouble p q) : L.Pairwise (fun p q => ht F q < ht F p) := by
  have hnd' : L.Pairwise (fun p q => p ≠ q) := hnd
  refine (hnd'.and hL).imp_of_mem ?_
  intro p q hp hq ⟨hne, hle⟩
  exact lt_of_le_of_ne hle (fun heq => hne (s6b_ht_inj_of_regular F (hmemL p hp) (hmemL q hq) (hreg p hp) heq.symm))

/-- over one `x`, the "before" and "after" orders agree on a set of regular points, and so do their entries -/

theorem s6b_filter_eq_of_regular (x : ℝ) (P : Param F.c → Bool)
    (hreg : ∀ p ∈ totalFibre F x, P p = true → ∀ q, ¬ F.IsDouble p q) :
    (fibreListBefore F x).filter P = (fibreListAfter F x).filter P := by
  apply s6b_sorted_eq (ht F)
  · refine s6b_pairwise_lt_of_regular F x _ ((fibreListBefore_nodup F x).filter P) ?_
      ((s6b_fibreListBefore_antitone F x).filter P) ?_
    · intro p hp
      rw [List.mem_filter, mem_fibreListBefore] at hp
      exact hp.1
    · intro p hp
      rw [List.mem_filter, mem_fibreListBefore] at hp
      exact hreg p hp.1 hp.2
  · refine s6b_pairwise_lt_of_regular F x _ ((fibreListAfter_nodup F x).filter P) ?_
      ((s6b_fibreListAfter_antitone F x).filter P) ?_
    · intro p hp
      rw [List.mem_filter, mem_fibreListAfter] at hp
      exact hp.1
    · intro p hp
      rw [List.mem_filter, mem_fibreListAfter] at hp
      exact hreg p hp.1 hp.2
  · intro p
    rw [List.mem_filter, List.mem_filter, mem_fibreListBefore, mem_fibreListAfter]

theorem s6b_entries_regular_eq (x : ℝ) (P : Param F.c → Bool)
    (hreg : ∀ p ∈ totalFibre F x, P p = true → ¬ F.IsCusp p ∧ ∀ q, ¬ F.IsDouble p q) :
    entriesOf F (beforeBits F) ((fibreListBefore F x).filter P) =
      entriesOf F (afterBits F) ((fibreListAfter F x).filter P) := by
  rw [s6b_filter_eq_of_regular F x P (fun p hp hP => (hreg p hp hP).2)]
  apply s6b_entriesOf_congr
  intro p hp
  rw [List.mem_filter, mem_fibreListAfter] at hp
  rw [s6b_beforeBits_regular F (hreg p hp.1 hp.2).1, s6b_afterBits_regular F (hreg p hp.1 hp.2).1]

/-! #### Stage 3: the entry structure of a column: `A ++ E_b ++ B` before its event, `A ++ E_a ++ B` after it -/

/-- the entry list of column `k` (the hybrid cut before its event) -/

def s6b_entries (k : ℕ) : List (Param F.c × ℕ) := hybridEntries F (colX F k) (colZ F k)

/-- the entry list just after the event of column `k` -/

def s6b_entriesAfter (k : ℕ) : List (Param F.c × ℕ) :=
  hybridEntriesP F (colX F k) (fun p => decide (colZ F k < ht F p))

/-- the entries strictly above the event of column `k` -/

def s6b_A (k : ℕ) : List (Param F.c × ℕ) :=
  entriesOf F (beforeBits F) ((fibreListBefore F (colX F k)).filter (fun p => decide (colZ F k < ht F p)))

/-- the entries of the event's point(s) before the event -/

def s6b_Eb (k : ℕ) : List (Param F.c × ℕ) :=
  entriesOf F (beforeBits F) ((fibreListBefore F (colX F k)).filter (fun p => decide (ht F p = colZ F k)))

/-- the entries of the event's point(s) after the event -/

def s6b_Ea (k : ℕ) : List (Param F.c × ℕ) :=
  entriesOf F (afterBits F) ((fibreListAfter F (colX F k)).filter (fun p => decide (ht F p = colZ F k)))

/-- the entries strictly below the event of column `k` -/

def s6b_B (k : ℕ) : List (Param F.c × ℕ) :=
  entriesOf F (afterBits F) ((fibreListAfter F (colX F k)).filter (fun p => decide (ht F p < colZ F k)))

theorem s6b_not_decide_le (z : ℝ) (p : Param F.c) : (!decide (z ≤ ht F p)) = decide (ht F p < z) := by
  by_cases h : z ≤ ht F p
  · simp [h, not_lt.mpr h]
  · simp [h, not_le.mp h]

theorem s6b_not_decide_lt (z : ℝ) (p : Param F.c) : (!decide (z < ht F p)) = decide (ht F p ≤ z) := by
  by_cases h : z < ht F p
  · simp [h, not_le.mpr h]
  · simp [h, not_lt.mp h]

/-- `filter (z ≤ ht) = filter (z < ht) ++ filter (ht = z)` on an antitone list -/

theorem s6b_split_le (z : ℝ) (L : List (Param F.c)) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L.filter (fun p => decide (z ≤ ht F p)) =
      L.filter (fun p => decide (z < ht F p)) ++ L.filter (fun p => decide (ht F p = z)) := by
  apply s6b_filter_split (ht F) _ _ _ _ _ L hL
  · intro p
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    exact ⟨fun h => (lt_or_eq_of_le h).imp id Eq.symm, fun h => h.elim le_of_lt (fun h => h.symm.le)⟩
  · intro p q hp hq
    simp only [decide_eq_true_eq] at hp hq
    rw [hp]; exact hq

/-- `filter (ht ≤ z) = filter (ht = z) ++ filter (ht < z)` on an antitone list -/

theorem s6b_split_ge (z : ℝ) (L : List (Param F.c)) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L.filter (fun p => decide (ht F p ≤ z)) =
      L.filter (fun p => decide (ht F p = z)) ++ L.filter (fun p => decide (ht F p < z)) := by
  apply s6b_filter_split (ht F) _ _ _ _ _ L hL
  · intro p
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    exact ⟨fun h => (lt_or_eq_of_le h).symm, fun h => h.elim (fun h => h.le) le_of_lt⟩
  · intro p q hp hq
    simp only [decide_eq_true_eq] at hp hq
    rw [hq]; exact hp

/-- `L = filter (z < ht) ++ filter (ht ≤ z)` on an antitone list -/

theorem s6b_split_all_lt (z : ℝ) (L : List (Param F.c)) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L = L.filter (fun p => decide (z < ht F p)) ++ L.filter (fun p => decide (ht F p ≤ z)) := by
  have := s6b_filter_split (ht F) (fun _ => true) (fun p => decide (z < ht F p)) (fun p => decide (ht F p ≤ z))
    (fun p => by by_cases h : z < ht F p <;> simp [h, not_lt.mp]) (fun p q hp hq => by
      simp only [decide_eq_true_eq] at hp hq; linarith) L hL
  rwa [List.filter_true] at this

/-- `L = filter (z ≤ ht) ++ filter (ht < z)` on an antitone list -/

theorem s6b_split_all_le (z : ℝ) (L : List (Param F.c)) (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L = L.filter (fun p => decide (z ≤ ht F p)) ++ L.filter (fun p => decide (ht F p < z)) := by
  have := s6b_filter_split (ht F) (fun _ => true) (fun p => decide (z ≤ ht F p)) (fun p => decide (ht F p < z))
    (fun p => by by_cases h : z ≤ ht F p <;> simp [h, not_le.mp]) (fun p q hp hq => by
      simp only [decide_eq_true_eq] at hp hq; linarith) L hL
  rwa [List.filter_true] at this

/-- `filter (z₀ < ht) = filter (z₁ ≤ ht) ++ filter (z₀ < ht < z₁)` on an antitone list -/

theorem s6b_split_between_upper {z₀ z₁ : ℝ} (h : z₀ < z₁) (L : List (Param F.c))
    (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L.filter (fun p => decide (z₀ < ht F p)) =
      L.filter (fun p => decide (z₁ ≤ ht F p)) ++ L.filter (fun p => decide (z₀ < ht F p ∧ ht F p < z₁)) := by
  apply s6b_filter_split (ht F) _ _ _ _ _ L hL
  · intro p
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    constructor
    · intro hp
      by_cases h1 : z₁ ≤ ht F p
      · exact Or.inl h1
      · exact Or.inr ⟨hp, not_le.mp h1⟩
    · rintro (h1 | ⟨h1, -⟩)
      · linarith
      · exact h1
  · intro p q hp hq
    simp only [decide_eq_true_eq] at hp hq
    linarith [hp.2]

/-- `filter (ht < z₁) = filter (z₀ < ht < z₁) ++ filter (ht ≤ z₀)` on an antitone list -/

theorem s6b_split_between_lower {z₀ z₁ : ℝ} (h : z₀ < z₁) (L : List (Param F.c))
    (hL : L.Pairwise (fun p q => ht F q ≤ ht F p)) :
    L.filter (fun p => decide (ht F p < z₁)) =
      L.filter (fun p => decide (z₀ < ht F p ∧ ht F p < z₁)) ++ L.filter (fun p => decide (ht F p ≤ z₀)) := by
  apply s6b_filter_split (ht F) _ _ _ _ _ L hL
  · intro p
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    constructor
    · intro hp
      by_cases h1 : ht F p ≤ z₀
      · exact Or.inr h1
      · exact Or.inl ⟨not_le.mp h1, hp⟩
    · rintro (⟨-, h1⟩ | h1)
      · exact h1
      · linarith
  · intro p q hp hq
    simp only [decide_eq_true_eq] at hp hq
    linarith [hq.1]

/-- T1: the entries of a column are `A ++ E_b ++ B` -/

theorem s6b_entries_eq (k : ℕ) : s6b_entries F k = s6b_A F k ++ s6b_Eb F k ++ s6b_B F k := by
  unfold s6b_entries hybridEntries hybridEntriesP s6b_A s6b_Eb s6b_B
  rw [s6b_split_le F _ _ (s6b_fibreListBefore_antitone F _), s6b_entriesOf_append,
    List.filter_congr (fun p _ => s6b_not_decide_le F (colZ F k) p)]

/-- T2: the entries just after the event of a column are `A ++ E_a ++ B` -/

theorem s6b_entriesAfter_eq (k : ℕ) : s6b_entriesAfter F k = s6b_A F k ++ s6b_Ea F k ++ s6b_B F k := by
  unfold s6b_entriesAfter hybridEntriesP s6b_A s6b_Ea s6b_B
  rw [List.filter_congr (fun p _ => s6b_not_decide_lt F (colZ F k) p),
    s6b_split_ge F _ _ (s6b_fibreListAfter_antitone F _), s6b_entriesOf_append, List.append_assoc]

theorem s6b_idx_letterOf (e : Event F) : (letterOf F e).idx = posOf F e := by
  cases e with
  | inl c => simp only [letterOf]; split_ifs <;> rfl
  | inr q => rfl

/-- T3: the letter's index is one more than the number of entries above its event -/

theorem s6b_length_A {k : ℕ} (hk : k < (events F).length) : (s6b_A F k).length + 1 = (letterAt (word F) k).idx := by
  rw [letterAt_word F hk, s6b_idx_letterOf]
  unfold s6b_A
  rw [s6b_length_entriesOf]
  rfl

/-! the points at the event's height -/

theorem s6b_mem_totalFibre_iff' (x : ℝ) (p : Param F.c) :
    p ∈ totalFibre F x ↔ p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ (F.eval p).1 = x := Iff.rfl

theorem s6b_mem_midB_iff (k : ℕ) (p : Param F.c) :
    p ∈ (fibreListBefore F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) ↔
      p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ F.eval p = F.eval (evPt F (eventAt F k)) := by
  rw [List.mem_filter, mem_fibreListBefore, s6b_mem_totalFibre_iff', decide_eq_true_iff, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem s6b_mem_midA_iff (k : ℕ) (p : Param F.c) :
    p ∈ (fibreListAfter F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) ↔
      p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ F.eval p = F.eval (evPt F (eventAt F k)) := by
  rw [List.mem_filter, mem_fibreListAfter, s6b_mem_totalFibre_iff', decide_eq_true_iff, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- at a cusp event the only point at the event's height is the cusp (`cusp_alone`) -/

theorem s6b_mid_cusp {k : ℕ} {c : F.Cusp} (he : eventAt F k = Sum.inl c) :
    (fibreListBefore F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) = [c.1] ∧
    (fibreListAfter F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) = [c.1] := by
  have key : ∀ b : Param F.c, b.2 ∈ Set.Ico (0 : ℝ) 1 → F.eval b = F.eval c.1 → b = c.1 := by
    intro b hb heq
    by_contra hne
    have hns : ¬ SameParam c.1 b := fun hs => hne (SameParam.eq_of_mem_Ico c.mem_Ico hb hs).symm
    exact F.cusp_alone c.1 b hns c.isCusp heq.symm
  constructor
  · apply s6b_eq_singleton_of_nodup ((fibreListBefore_nodup F _).filter _)
    · rw [s6b_mem_midB_iff, he]; exact ⟨c.mem_Ico, rfl⟩
    · intro b hb
      rw [s6b_mem_midB_iff, he] at hb
      exact key b hb.1 hb.2
  · apply s6b_eq_singleton_of_nodup ((fibreListAfter_nodup F _).filter _)
    · rw [s6b_mem_midA_iff, he]; exact ⟨c.mem_Ico, rfl⟩
    · intro b hb
      rw [s6b_mem_midA_iff, he] at hb
      exact key b hb.1 hb.2

/-- at a crossing event the points at the event's height are the over and the under branch, over first in the
"before" order and under first in the "after" order (`no_triple`) -/

theorem s6b_mid_cross {k : ℕ} {q : Cross F} (he : eventAt F k = Sum.inr q) :
    (fibreListBefore F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) = [q.1.1, q.1.2] ∧
    (fibreListAfter F (colX F k)).filter (fun p => decide (ht F p = colZ F k)) = [q.1.2, q.1.1] := by
  obtain ⟨⟨ho, hu, hne, heval⟩, hslope⟩ := F.mem_crossingPairs'.mp q.2
  have hht : ht F q.1.2 = ht F q.1.1 := by unfold ht; rw [heval]
  have hmem : ∀ p : Param F.c, p.2 ∈ Set.Ico (0 : ℝ) 1 ∧ F.eval p = F.eval q.1.1 ↔ p = q.1.1 ∨ p = q.1.2 := by
    intro p
    constructor
    · rintro ⟨hp, hpe⟩
      by_contra hpq
      push Not at hpq
      exact F.no_triple p q.1.1 q.1.2 (fun hs => hpq.1 (SameParam.eq_of_mem_Ico hp ho hs))
        (fun hs => hne (SameParam.eq_of_mem_Ico ho hu hs)) (fun hs => hpq.2 (SameParam.eq_of_mem_Ico hp hu hs))
        hpe heval
    · rintro (rfl | rfl)
      · exact ⟨ho, rfl⟩
      · exact ⟨hu, heval.symm⟩
  constructor
  · apply s6b_eq_pair_of_nodup_sorted (fun p q => beforeLE F p q = true) ((fibreListBefore_nodup F _).filter _)
    · intro p; rw [s6b_mem_midB_iff, he]; exact hmem p
    · exact hne
    · exact (fibreListBefore_pairwise F _).filter _
    · intro h
      unfold beforeLE at h
      rw [decide_eq_true_iff, Prod.Lex.le_iff] at h
      simp only [ofLex_toLex] at h
      rcases h with h | ⟨-, h⟩
      · linarith
      · linarith
  · apply s6b_eq_pair_of_nodup_sorted (fun p q => afterLE F p q = true) ((fibreListAfter_nodup F _).filter _)
    · intro p; rw [s6b_mem_midA_iff, he]; exact (hmem p).trans or_comm
    · exact hne.symm
    · exact (fibreListAfter_pairwise F _).filter _
    · intro h
      unfold afterLE at h
      rw [decide_eq_true_iff, Prod.Lex.le_iff] at h
      simp only [ofLex_toLex] at h
      rcases h with h | ⟨-, h⟩
      · linarith
      · linarith

theorem s6b_length_afterBits_left {c : F.Cusp} (hl : F.IsLeftCusp c.1) : (afterBits F c.1).length = 2 := by
  unfold afterBits
  rw [if_neg (fun hr => left_right_absurd F hl hr), if_pos hl]
  split_ifs <;> rfl

theorem s6b_length_beforeBits_right {c : F.Cusp} (hr : F.IsRightCusp c.1) : (beforeBits F c.1).length = 2 := by
  unfold beforeBits
  rw [if_neg (fun hl => left_right_absurd F hl hr), if_pos hr]
  split_ifs <;> rfl

/-- the event entries at a left cusp -/

theorem s6b_Eb_Ea_left {k : ℕ} {c : F.Cusp} (he : eventAt F k = Sum.inl c) (hl : F.IsLeftCusp c.1) :
    s6b_Eb F k = [] ∧ s6b_Ea F k = [(c.1, 0), (c.1, 1)] := by
  obtain ⟨h1, h2⟩ := s6b_mid_cusp F he
  unfold s6b_Eb s6b_Ea
  rw [h1, h2, s6b_entriesOf_singleton, s6b_entriesOf_singleton, s6b_length_afterBits_left F hl]
  unfold beforeBits
  rw [if_pos hl]
  exact ⟨rfl, rfl⟩

/-- the event entries at a right cusp -/

theorem s6b_Eb_Ea_right {k : ℕ} {c : F.Cusp} (he : eventAt F k = Sum.inl c) (hl : ¬ F.IsLeftCusp c.1) :
    s6b_Eb F k = [(c.1, 0), (c.1, 1)] ∧ s6b_Ea F k = [] := by
  have hr : F.IsRightCusp c.1 := (F.isLeftCusp_or_isRightCusp c.isCusp).resolve_left hl
  obtain ⟨h1, h2⟩ := s6b_mid_cusp F he
  unfold s6b_Eb s6b_Ea
  rw [h1, h2, s6b_entriesOf_singleton, s6b_entriesOf_singleton, s6b_length_beforeBits_right F hr]
  unfold afterBits
  rw [if_pos hr]
  exact ⟨rfl, rfl⟩

/-- the event entries at a crossing -/

theorem s6b_Eb_Ea_cross {k : ℕ} {q : Cross F} (he : eventAt F k = Sum.inr q) :
    s6b_Eb F k = [(q.1.1, 0), (q.1.2, 0)] ∧ s6b_Ea F k = [(q.1.2, 0), (q.1.1, 0)] := by
  have hd := F.isOverUnder_of_mem_crossingPairs q.2
  have hno : ¬ F.IsCusp q.1.1 := F.not_isCusp_of_isDouble hd.1
  have hnu : ¬ F.IsCusp q.1.2 := F.not_isCusp_of_isDouble hd.1.symm
  obtain ⟨h1, h2⟩ := s6b_mid_cross F he
  unfold s6b_Eb s6b_Ea
  rw [h1, h2]
  constructor
  · rw [s6b_entriesOf_eq_map]
    · rfl
    · intro p hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [s6b_beforeBits_regular F hno]; rfl
      · rw [s6b_beforeBits_regular F hnu]; rfl
  · rw [s6b_entriesOf_eq_map]
    · rfl
    · intro p hp
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · rw [s6b_afterBits_regular F hnu]; rfl
      · rw [s6b_afterBits_regular F hno]; rfl

/-! the letter of a column determines the kind of its event -/

theorem s6b_event_of_letter_l {k m : ℕ} {d : Bool} (hk : k < (events F).length) (h : letterAt (word F) k = .l m d) :
    ∃ c : F.Cusp, eventAt F k = Sum.inl c ∧ F.IsLeftCusp c.1 ∧ m = posOf F (Sum.inl c) := by
  rw [letterAt_word F hk] at h
  rcases he : eventAt F k with c | q
  · rw [he] at h
    by_cases hl : F.IsLeftCusp c.1
    · simp only [letterOf, if_pos hl] at h
      exact ⟨c, rfl, hl, (Letter.l.inj h).1.symm⟩
    · simp only [letterOf, if_neg hl] at h
      cases h
  · rw [he] at h
    simp [letterOf] at h

theorem s6b_event_of_letter_r {k m : ℕ} (hk : k < (events F).length) (h : letterAt (word F) k = .r m) :
    ∃ c : F.Cusp, eventAt F k = Sum.inl c ∧ ¬ F.IsLeftCusp c.1 ∧ m = posOf F (Sum.inl c) := by
  rw [letterAt_word F hk] at h
  rcases he : eventAt F k with c | q
  · rw [he] at h
    by_cases hl : F.IsLeftCusp c.1
    · simp only [letterOf, if_pos hl] at h
      cases h
    · simp only [letterOf, if_neg hl] at h
      exact ⟨c, rfl, hl, (Letter.r.inj h).symm⟩
  · rw [he] at h
    simp [letterOf] at h

theorem s6b_event_of_letter_σ {k m : ℕ} (hk : k < (events F).length) (h : letterAt (word F) k = .σ m) :
    ∃ q : Cross F, eventAt F k = Sum.inr q ∧ m = posOf F (Sum.inr q) := by
  rw [letterAt_word F hk] at h
  rcases he : eventAt F k with c | q
  · rw [he] at h
    by_cases hl : F.IsLeftCusp c.1
    · simp only [letterOf, if_pos hl] at h
      cases h
    · simp only [letterOf, if_neg hl] at h
      cases h
  · rw [he] at h
    exact ⟨q, rfl, (Letter.σ.inj h).symm⟩

/-! #### Stage 4: the transition from a column to the next one (tie: list surgery; gap: the S1 limits) -/

/-- after the top event of an x-value the entries are `entriesAfter` -/

theorem s6b_entriesAfter_top {k : ℕ} (hk : k < (events F).length)
    (hnext : k + 1 = (events F).length ∨ colX F k < colX F (k + 1)) :
    s6b_entriesAfter F k = entriesAfter F (colX F k) := by
  unfold s6b_entriesAfter hybridEntriesP entriesAfter
  rw [List.filter_congr (fun p _ => s6b_not_decide_lt F (colZ F k) p)]
  conv_rhs => rw [s6b_split_all_lt F (colZ F k) _ (s6b_fibreListAfter_antitone F _)]
  rw [s6b_entriesOf_append]
  congr 1
  apply s6b_entries_regular_eq
  intro p hp hP
  rw [decide_eq_true_iff] at hP
  apply s6b_regular_of_no_event F hp
  intro e hex hez
  have := s6b_top F hk hnext e hex
  linarith

/-- before the bottom event of an x-value the entries are `entriesBefore` -/

theorem s6b_entries_bot {k : ℕ} (hk : k < (events F).length) (hprev : k = 0 ∨ colX F (k - 1) < colX F k) :
    s6b_entries F k = entriesBefore F (colX F k) := by
  unfold s6b_entries hybridEntries hybridEntriesP entriesBefore
  rw [List.filter_congr (fun p _ => s6b_not_decide_le F (colZ F k) p)]
  conv_rhs => rw [s6b_split_all_le F (colZ F k) _ (s6b_fibreListBefore_antitone F _)]
  rw [s6b_entriesOf_append]
  congr 1
  symm
  apply s6b_entries_regular_eq
  intro p hp hP
  rw [decide_eq_true_iff] at hP
  apply s6b_regular_of_no_event F hp
  intro e hex hez
  have := s6b_bot F hk hprev e hex
  linarith

theorem s6b_colZ_lt_of_tie {k : ℕ} (hk : k + 1 < (events F).length) (hx : colX F k = colX F (k + 1)) :
    colZ F k < colZ F (k + 1) := by
  have h := s6b_key_lt_of_idx_lt F hk (Nat.lt_succ_self k)
  rw [Prod.Lex.lt_iff] at h
  simp only [ofLex_toLex] at h
  rcases h with h | ⟨-, h⟩
  · rw [hx] at h; exact absurd h (lt_irrefl _)
  · exact h

/-- two consecutive events of one x-value: the entries after the lower one are the entries before the upper one -/

theorem s6b_entries_tie {k : ℕ} (hk : k + 1 < (events F).length) (hx : colX F k = colX F (k + 1)) :
    s6b_entries F (k + 1) = s6b_entriesAfter F k := by
  have hz := s6b_colZ_lt_of_tie F hk hx
  unfold s6b_entries s6b_entriesAfter hybridEntries hybridEntriesP
  rw [← hx]
  rw [List.filter_congr (fun p _ => s6b_not_decide_le F (colZ F (k + 1)) p),
    List.filter_congr (fun p _ => s6b_not_decide_lt F (colZ F k) p),
    s6b_split_between_upper F hz _ (s6b_fibreListBefore_antitone F _),
    s6b_split_between_lower F hz _ (s6b_fibreListAfter_antitone F _),
    s6b_entriesOf_append, s6b_entriesOf_append, List.append_assoc]
  congr 2
  symm
  apply s6b_entries_regular_eq
  intro p hp hP
  rw [decide_eq_true_iff] at hP
  apply s6b_regular_of_no_event F hp
  intro e hex hez
  apply s6b_no_event_between F hk e
  · rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; exact Or.inr ⟨hex.symm, by rw [hez]; exact hP.1⟩
  · rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; exact Or.inr ⟨by rw [hex, hx], by rw [hez]; exact hP.2⟩

/-- the circle of a strand entry -/

def s6b_circOf (a : Param F.c × ℕ) : Fin F.c := a.1.1

theorem s6b_entriesAfter_eq_entriesBefore {x : ℝ} (hx : x ∉ singX F) : entriesAfter F x = entriesBefore F x := by
  rw [entriesBefore_eq_of_notMem_singX F hx]
  unfold entriesAfter
  rw [fibreListAfter_eq_fibreListBefore F hx]
  apply s6b_entriesOf_eq_map
  intro p hp
  rw [mem_fibreListBefore] at hp
  have hreg := regular_of_notMem_singX F (p := p) (by rw [hp.2]; exact hx)
  rw [s6b_afterBits_regular F hreg.1]; rfl

/-- continuations preserve the circles of an entry list -/

theorem s6b_map_circ_eq_of_cont (L L' : List (Param F.c × ℕ)) (hlen : L.length = L'.length)
    (hc : ∀ j < L'.length, Cont F ((L.getD j (dfltP F, 0)).1) (L'.getD j (dfltP F, 0))) :
    L.map (s6b_circOf F) = L'.map (s6b_circOf F) := by
  apply List.ext_getElem
  · simp [hlen]
  · intro j h1 h2
    simp only [List.getElem_map]
    rw [List.length_map] at h1 h2
    have := (hc j h2).1
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    exact this

/-- the circle list of the cut is locally constant at a non-singular `x` (the S1 limits) -/

theorem s6b_circ_eventually {x : ℝ} (hx : x ∉ singX F) :
    ∀ᶠ y in nhds x, (entriesBefore F y).map (s6b_circOf F) = (entriesBefore F x).map (s6b_circOf F) := by
  obtain ⟨η₁, hη₁, H₁⟩ := entriesBefore_left_limit F x
  obtain ⟨η₂, hη₂, H₂⟩ := entriesAfter_right_limit F x
  have hmem : Set.Ioo (x - η₁) (x + η₂) ∈ nhds x := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hmem] with y hy
  rcases lt_trichotomy y x with hlt | rfl | hgt
  · obtain ⟨hlen, hc⟩ := H₁ y ⟨hy.1, hlt⟩
    exact s6b_map_circ_eq_of_cont F _ _ hlen hc
  · rfl
  · obtain ⟨hlen, hc⟩ := H₂ y ⟨hgt, hy.2⟩
    rw [← s6b_entriesAfter_eq_entriesBefore F hx]
    exact s6b_map_circ_eq_of_cont F _ _ hlen hc

/-- across a gap between singular x-values the circle list of the cut is constant: the circles just right of
`a` are the circles just left of `b` -/

theorem s6b_circ_gap {a b : ℝ} (hab : a < b) (hgap : ∀ x ∈ Set.Ioo a b, x ∉ singX F) :
    (entriesAfter F a).map (s6b_circOf F) = (entriesBefore F b).map (s6b_circOf F) := by
  let _ : TopologicalSpace (List (Fin F.c)) := ⊥
  have _ : DiscreteTopology (List (Fin F.c)) := ⟨rfl⟩
  have hcont : ContinuousOn (fun y => (entriesBefore F y).map (s6b_circOf F)) (Set.Ioo a b) := by
    intro y hy
    rw [ContinuousWithinAt, nhds_discrete, Filter.tendsto_pure]
    exact (s6b_circ_eventually F (hgap y hy)).filter_mono nhdsWithin_le_nhds
  obtain ⟨η₁, hη₁, H₁⟩ := entriesAfter_right_limit F a
  obtain ⟨η₂, hη₂, H₂⟩ := entriesBefore_left_limit F b
  obtain ⟨y₁, hy₁⟩ : ∃ y, y = a + min η₁ (b - a) / 2 := ⟨_, rfl⟩
  obtain ⟨y₂, hy₂⟩ : ∃ y, y = b - min η₂ (b - a) / 2 := ⟨_, rfl⟩
  have hm1 : 0 < min η₁ (b - a) := lt_min hη₁ (by linarith)
  have hm2 : 0 < min η₂ (b - a) := lt_min hη₂ (by linarith)
  have hm1a : min η₁ (b - a) ≤ η₁ := min_le_left _ _
  have hm1b : min η₁ (b - a) ≤ b - a := min_le_right _ _
  have hm2a : min η₂ (b - a) ≤ η₂ := min_le_left _ _
  have hm2b : min η₂ (b - a) ≤ b - a := min_le_right _ _
  have hy₁I : y₁ ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have hy₂I : y₂ ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
  have e1 : (entriesBefore F y₁).map (s6b_circOf F) = (entriesAfter F a).map (s6b_circOf F) := by
    obtain ⟨hlen, hc⟩ := H₁ y₁ ⟨by linarith, by linarith⟩
    exact s6b_map_circ_eq_of_cont F _ _ hlen hc
  have e2 : (entriesBefore F y₂).map (s6b_circOf F) = (entriesBefore F b).map (s6b_circOf F) := by
    obtain ⟨hlen, hc⟩ := H₂ y₂ ⟨by linarith, by linarith⟩
    exact s6b_map_circ_eq_of_cont F _ _ hlen hc
  rw [← e1, ← e2]
  exact isPreconnected_Ioo.constant hcont hy₁I hy₂I

/-- every singular x-value is the x-value of an event -/

theorem s6b_exists_event_of_mem_singX {x : ℝ} (hx : x ∈ singX F) : ∃ e : Event F, evX F e = x := by
  unfold singX at hx
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
  rcases hx with ⟨p, hp, hpx⟩ | ⟨q, hq, hqx⟩
  · exact ⟨Sum.inl ⟨p, hp⟩, hpx⟩
  · rcases F.mem_crossingPairs_or_swap hq with h | h
    · exact ⟨Sum.inr ⟨q, h⟩, hqx⟩
    · refine ⟨Sum.inr ⟨q.swap, h⟩, ?_⟩
      show (F.eval q.2).1 = x
      rw [← (F.mem_doubleSet.mp hq).2.2.2]; exact hqx

/-- THE TRANSITION: the circles of the entries of column `k + 1` are the circles of the entries just after the
event of column `k` -/

theorem s6b_circ_trans {k : ℕ} (hk : k + 1 < (events F).length) :
    (s6b_entries F (k + 1)).map (s6b_circOf F) = (s6b_entriesAfter F k).map (s6b_circOf F) := by
  have hk' : k < (events F).length := by omega
  have hle : colX F k ≤ colX F (k + 1) := colX_mono F (Nat.lt_succ_self k) hk
  rcases eq_or_lt_of_le hle with hx | hx
  · rw [s6b_entries_tie F hk hx]
  · rw [s6b_entriesAfter_top F hk' (Or.inr hx), s6b_entries_bot F hk (Or.inr (by simpa using hx))]
    symm
    apply s6b_circ_gap F hx
    intro x hxI hsing
    obtain ⟨e, he⟩ := s6b_exists_event_of_mem_singX F hsing
    apply s6b_no_event_between F hk e
    · rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; exact Or.inl (by rw [he]; exact hxI.1)
    · rw [Prod.Lex.lt_iff]; simp only [ofLex_toLex]; exact Or.inl (by rw [he]; exact hxI.2)

/-! #### Stage 5: the per-step invariance of the circle -/

/-- the circle at position `p` (1-based) of an entry list -/

def s6b_circAt (L : List (Param F.c × ℕ)) (p : ℕ) : Fin F.c := (L.getD (p - 1) (dfltP F, 0)).1.1

theorem s6b_circAt_eq_of_map_eq {L L' : List (Param F.c × ℕ)}
    (h : L.map (s6b_circOf F) = L'.map (s6b_circOf F)) (p : ℕ) : s6b_circAt F L p = s6b_circAt F L' p := by
  have h1 : s6b_circAt F L p = (L.map (s6b_circOf F)).getD (p - 1) (s6b_circOf F (dfltP F, 0)) := by
    rw [List.getD_map]; rfl
  have h2 : s6b_circAt F L' p = (L'.map (s6b_circOf F)).getD (p - 1) (s6b_circOf F (dfltP F, 0)) := by
    rw [List.getD_map]; rfl
  rw [h1, h2, h]

theorem s6b_getD_three (A E B : List (Param F.c × ℕ)) (n : ℕ) (d : Param F.c × ℕ) :
    (A ++ E ++ B).getD n d = if n < A.length then A.getD n d
      else if n < A.length + E.length then E.getD (n - A.length) d else B.getD (n - A.length - E.length) d := by
  rw [List.append_assoc]
  by_cases h1 : n < A.length
  · rw [List.getD_append _ _ _ _ h1, if_pos h1]
  · rw [List.getD_append_right _ _ _ _ (not_lt.mp h1), if_neg h1]
    by_cases h2 : n < A.length + E.length
    · rw [List.getD_append _ _ _ _ (by omega), if_pos h2]
    · rw [List.getD_append_right _ _ _ _ (by omega), if_neg h2]

theorem s6b_length_Eb_Ea {k : ℕ} (hk : k < (events F).length) :
    (s6b_Eb F k).length = (letterAt (word F) k).arity ∧ (s6b_Ea F k).length = (letterAt (word F) k).coarity := by
  rcases hℓ : letterAt (word F) k with ⟨m, d⟩ | ⟨m⟩ | ⟨m⟩
  · obtain ⟨c, he, hl, -⟩ := s6b_event_of_letter_l F hk hℓ
    obtain ⟨h1, h2⟩ := s6b_Eb_Ea_left F he hl
    rw [h1, h2]; exact ⟨rfl, rfl⟩
  · obtain ⟨c, he, hl, -⟩ := s6b_event_of_letter_r F hk hℓ
    obtain ⟨h1, h2⟩ := s6b_Eb_Ea_right F he hl
    rw [h1, h2]; exact ⟨rfl, rfl⟩
  · obtain ⟨q, he, -⟩ := s6b_event_of_letter_σ F hk hℓ
    obtain ⟨h1, h2⟩ := s6b_Eb_Ea_cross F he
    rw [h1, h2]; exact ⟨rfl, rfl⟩

/-- THE STEP: a strand passing a column rightward keeps its circle (`posR`) -/

theorem s6b_circAt_step {k : ℕ} (hk : k < (events F).length) {p q : ℕ} (hp : 1 ≤ p)
    (hq : (letterAt (word F) k).posR p = some q) :
    s6b_circAt F (s6b_entriesAfter F k) q = s6b_circAt F (s6b_entries F k) p := by
  have hA := s6b_length_A F hk
  obtain ⟨hEb, hEa⟩ := s6b_length_Eb_Ea F hk
  rw [s6b_entries_eq, s6b_entriesAfter_eq]
  unfold s6b_circAt
  rw [s6b_getD_three, s6b_getD_three]
  rcases lt_or_ge p (letterAt (word F) k).idx with hlt | hge
  · -- above the event: the position is kept
    rw [posR_of_lt hlt] at hq
    obtain rfl := Option.some.inj hq
    have h1 : p - 1 < (s6b_A F k).length := by omega
    rw [if_pos h1, if_pos h1]
  · rcases lt_or_ge p ((letterAt (word F) k).idx + (letterAt (word F) k).arity) with hmid | hge'
    · -- the event's own strands: only a crossing lets them pass, exchanging them
      rcases hℓ : letterAt (word F) k with ⟨m, d⟩ | ⟨m⟩ | ⟨m⟩
      · rw [hℓ] at hge hmid; simp only [idx, arity] at hge hmid; omega
      · rw [hℓ] at hq hge hmid; simp only [idx, arity] at hge hmid
        rw [posR_r, if_neg (not_lt.mpr hge), if_pos hmid] at hq
        cases hq
      · obtain ⟨q', he, -⟩ := s6b_event_of_letter_σ F hk hℓ
        obtain ⟨h1, h2⟩ := s6b_Eb_Ea_cross F he
        rw [hℓ] at hq hge hmid hA
        simp only [idx, arity] at hge hmid hA
        rw [posR_σ, if_neg (not_lt.mpr hge), if_pos hmid] at hq
        have hq' := Option.some.inj hq
        rw [h1, h2]
        simp only [List.length_cons, List.length_nil]
        rcases eq_or_lt_of_le hge with hpm | hlt'
        · -- p = m: the over strand descends to m + 1
          rw [if_pos hpm.symm] at hq'
          subst hq'
          split_ifs <;> try omega
          have e1 : m + 1 - 1 - (s6b_A F k).length = 1 := by omega
          have e2 : p - 1 - (s6b_A F k).length = 0 := by omega
          rw [e1, e2]; rfl
        · -- p = m + 1: the under strand ascends to m
          have hpm : p = m + 1 := by omega
          rw [if_neg (by omega)] at hq'
          subst hq'
          split_ifs <;> try omega
          have e1 : m - 1 - (s6b_A F k).length = 0 := by omega
          have e2 : p - 1 - (s6b_A F k).length = 1 := by omega
          rw [e1, e2]; rfl
    · -- below the event: the position shifts by the strand-count change
      rw [posR_of_ge hge'] at hq
      obtain rfl := Option.some.inj hq
      split_ifs <;> try omega
      have e : p + (letterAt (word F) k).coarity - (letterAt (word F) k).arity - 1 - (s6b_A F k).length -
          (s6b_Ea F k).length = p - 1 - (s6b_A F k).length - (s6b_Eb F k).length := by omega
      rw [e]

/-- the circle of a slot given as a pair: the cusp's circle at a cusp vertex, the entry's circle at a cut slot -/

def s6b_circPair (s : ℕ × ℕ) : Fin F.c :=
  if s.2 = 0 then (evPt F (eventAt F s.1)).1 else s6b_circAt F (s6b_entries F s.1) s.2

/-- THE CIRCLE OF A SLOT -/

def s6b_circ (u : Slot (word F)) : Fin F.c := s6b_circPair F u.1

theorem s6b_circPair_cusp (k : ℕ) : s6b_circPair F (k, 0) = (evPt F (eventAt F k)).1 := by simp [s6b_circPair]

theorem s6b_circPair_cut (k p : ℕ) (hp : p ≠ 0) : s6b_circPair F (k, p) = s6b_circAt F (s6b_entries F k) p := by
  simp [s6b_circPair, hp]

/-- at a right cusp the two arm positions before the event carry the cusp's circle -/

theorem s6b_circAt_arms_r {k m p : ℕ} (hk : k < (events F).length) (hℓ : letterAt (word F) k = .r m)
    (hpm : p = m ∨ p = m + 1) : s6b_circAt F (s6b_entries F k) p = (evPt F (eventAt F k)).1 := by
  obtain ⟨c, he, hl, -⟩ := s6b_event_of_letter_r F hk hℓ
  obtain ⟨hEb, -⟩ := s6b_Eb_Ea_right F he hl
  have hA := s6b_length_A F hk
  rw [hℓ] at hA; simp only [idx] at hA
  rw [he, s6b_entries_eq, hEb]
  unfold s6b_circAt
  rw [s6b_getD_three]
  simp only [List.length_cons, List.length_nil]
  rcases hpm with hpm | hpm
  · split_ifs <;> try omega
    have e : p - 1 - (s6b_A F k).length = 0 := by omega
    rw [e]; rfl
  · split_ifs <;> try omega
    have e : p - 1 - (s6b_A F k).length = 1 := by omega
    rw [e]; rfl

/-- at a left cusp the two arm positions after the event carry the cusp's circle -/

theorem s6b_circAt_arms_l {k m p : ℕ} {d : Bool} (hk : k < (events F).length) (hℓ : letterAt (word F) k = .l m d)
    (hpm : p = m ∨ p = m + 1) : s6b_circAt F (s6b_entriesAfter F k) p = (evPt F (eventAt F k)).1 := by
  obtain ⟨c, he, hl, -⟩ := s6b_event_of_letter_l F hk hℓ
  obtain ⟨-, hEa⟩ := s6b_Eb_Ea_left F he hl
  have hA := s6b_length_A F hk
  rw [hℓ] at hA; simp only [idx] at hA
  rw [he, s6b_entriesAfter_eq, hEa]
  unfold s6b_circAt
  rw [s6b_getD_three]
  simp only [List.length_cons, List.length_nil]
  rcases hpm with hpm | hpm
  · split_ifs <;> try omega
    have e : p - 1 - (s6b_A F k).length = 0 := by omega
    rw [e]; rfl
  · split_ifs <;> try omega
    have e : p - 1 - (s6b_A F k).length = 1 := by omega
    rw [e]; rfl

/-- `posL` is inverse to `posR` -/

theorem s6b_posR_of_posL {ℓ : Letter} {p q : ℕ} (h : ℓ.posL p = some q) : ℓ.posR q = some p := by
  unfold posL at h
  split_ifs at h with h1 h2
  · obtain rfl := Option.some.inj h
    exact posR_of_lt h1
  · cases ℓ with
    | l m d => cases h
    | r m => cases h
    | σ m =>
      simp only at h
      obtain rfl := Option.some.inj h
      simp only [idx, coarity] at h1 h2
      rw [posR_σ]
      by_cases hpm : p = m
      · subst hpm; simp
      · have hpm' : p = m + 1 := by omega
        subst hpm'; simp
  · obtain rfl := Option.some.inj h
    rw [posR_of_ge (by omega)]
    congr 1; omega

theorem s6b_cut_col_lt {k p : ℕ} (hp : 1 ≤ p) (hpk : p ≤ (cut (word F) k).length) : k < (events F).length := by
  have := (cutSlot_pos (word_closed F) hp hpk).2
  rwa [length_word] at this

/-- a slot with a positive position is a cut slot of a real column -/

theorem s6b_col_lt_of_slot {k p : ℕ} (h : IsSlot (word F) (k, p)) (hp : p ≠ 0) : k < (events F).length := by
  rcases h with ⟨h0, -, -⟩ | ⟨h1, h2, -⟩
  · exact absurd h0 hp
  · exact s6b_cut_col_lt F h1 h2

/-- THE INVARIANT: `next` preserves the circle of a slot -/

theorem s6b_circ_next (u : Slot (word F)) : s6b_circ F (next (word_closed F) u) = s6b_circ F u := by
  have hn := length_word F
  have hu := u.2
  have hnu := (next (word_closed F) u).2
  unfold s6b_circ
  rcases next_cases (word_closed F) u with
    ⟨k, p, q, hs, hp, -, hnx, hq, -, hposR, hk⟩ | ⟨k, p, m, hs, hp, -, hℓ, hpm, hnx, -, hk⟩ |
    ⟨k, p, q, hs, hp, -, hnx, hq, -, hposL, hk1, -⟩ | ⟨k, p, m, d, hs, hp, -, hℓ, hpm, hnx, -, -, hk1, -⟩ |
    ⟨k, m, d, hs, hℓ, hnx, -, -, hm, hk⟩ | ⟨k, m, hs, hℓ, hnx, -, hm, hk⟩
  · -- (1) rightward pass through the column
    rw [hnx] at hnu
    have hk1 : k + 1 < (events F).length := s6b_col_lt_of_slot F hnu (by omega)
    have hk' : k < (events F).length := by rwa [hn] at hk
    rw [hnx, hs, s6b_circPair_cut F _ _ (by omega), s6b_circPair_cut F _ _ (by omega),
      s6b_circAt_eq_of_map_eq F (s6b_circ_trans F hk1)]
    exact s6b_circAt_step F hk' hp hposR
  · -- (2) rightward into a right cusp vertex
    have hk' : k < (events F).length := by rwa [hn] at hk
    rw [hnx, hs, s6b_circPair_cusp, s6b_circPair_cut F _ _ (by omega)]
    exact (s6b_circAt_arms_r F hk' hℓ hpm).symm
  · -- (3) leftward pass through the column
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hs] at hu
    have hk1 : k' + 1 < (events F).length := s6b_col_lt_of_slot F hu (by omega)
    have hk' : k' < (events F).length := by omega
    simp only [Nat.add_sub_cancel] at hnx hposL
    rw [hnx, hs, s6b_circPair_cut F _ _ (by omega), s6b_circPair_cut F _ _ (by omega),
      s6b_circAt_eq_of_map_eq F (s6b_circ_trans F hk1)]
    exact (s6b_circAt_step F hk' hq (s6b_posR_of_posL hposL)).symm
  · -- (4) leftward into a left cusp vertex
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hs] at hu
    have hk1 : k' + 1 < (events F).length := s6b_col_lt_of_slot F hu (by omega)
    have hk' : k' < (events F).length := by omega
    simp only [Nat.add_sub_cancel] at hnx hℓ
    rw [hnx, hs, s6b_circPair_cusp, s6b_circPair_cut F _ _ (by omega),
      s6b_circAt_eq_of_map_eq F (s6b_circ_trans F hk1)]
    exact (s6b_circAt_arms_l F hk' hℓ hpm).symm
  · -- (5) out of a left cusp vertex along the new arms
    have hq : (if d = true then m else m + 1) = m ∨ (if d = true then m else m + 1) = m + 1 := by
      cases d <;> simp
    have hq0 : (if d = true then m else m + 1) ≠ 0 := by rcases hq with h | h <;> rw [h] <;> omega
    rw [hnx] at hnu
    have hk1 : k + 1 < (events F).length := s6b_col_lt_of_slot F hnu hq0
    have hk' : k < (events F).length := by omega
    rw [hnx, hs, s6b_circPair_cusp, s6b_circPair_cut F _ _ hq0, s6b_circAt_eq_of_map_eq F (s6b_circ_trans F hk1)]
    exact s6b_circAt_arms_l F hk' hℓ hq
  · -- (6) out of a right cusp vertex along the arriving arm
    have hq : (if bit (word F) k m = true then m + 1 else m) = m ∨
        (if bit (word F) k m = true then m + 1 else m) = m + 1 := by
      split_ifs <;> simp
    have hq0 : (if bit (word F) k m = true then m + 1 else m) ≠ 0 := by
      rcases hq with h | h <;> rw [h] <;> omega
    have hk' : k < (events F).length := by rwa [hn] at hk
    rw [hnx, hs, s6b_circPair_cusp, s6b_circPair_cut F _ _ hq0]
    exact s6b_circAt_arms_r F hk' hℓ hq

theorem s6b_circ_iterate (u : Slot (word F)) (j : ℕ) :
    s6b_circ F ((next (word_closed F))^[j] u) = s6b_circ F u := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', s6b_circ_next, ih]

theorem s6b_circ_of_sameCycle {u v : Slot (word F)} (h : (nextPerm (word_closed F)).SameCycle u v) :
    s6b_circ F u = s6b_circ F v := by
  obtain ⟨j, hj⟩ := exists_iterate_of_sameCycle (word_closed F) h
  rw [← hj, s6b_circ_iterate]

theorem s6b_circ_cuspVertex (c : F.Cusp) : s6b_circ F (cuspVertex F c) = c.1.1 := by
  show s6b_circPair F (evIdx F (Sum.inl c), 0) = c.1.1
  rw [s6b_circPair_cusp, eventAt_evIdx]; rfl

/-- the slot of a strand of circle `i` has circle `i` -/

theorem s6b_circ_slotAt {i : Fin F.c} {t : ℝ} (h : xOf F i t ∉ singX F) : s6b_circ F (slotAt F i t h) = i := by
  have ht' : xOf F (someCuspOn F i).1.1 t ∉ singX F := by rwa [someCuspOn_fst]
  have e := s6b_slotAt_fst_eq F (someCuspOn_fst F i) ht' h
  have hc := s6b_sameCycle_cuspVertex F (someCuspOn F i) ht'
  rw [e] at hc
  rw [s6b_circ_of_sameCycle F hc, s6b_circ_cuspVertex, someCuspOn_fst]

end S6bHelpers

/-- LEAF (S6, the path and the cusps): the slot path along a parameter interval passes the cusp vertex of every
cusp of the circle inside it, and every cusp vertex it passes belongs to a cusp of the circle. -/
theorem path_cusps {i : Fin F.c} {t₀ t₁ : ℝ} (h01 : t₀ < t₁) (h₀ : xOf F i t₀ ∉ singX F)
    (h₁ : xOf F i t₁ ∉ singX F) :
    ∃ m, (next (word_closed F))^[m] (slotAt F i t₀ h₀) = slotAt F i t₁ h₁ ∧
      (∀ c : F.Cusp, c.1.1 = i → ∀ s ∈ Set.Ioo t₀ t₁, SameParam c.1 (i, s) →
        ∃ j < m, (next (word_closed F))^[j] (slotAt F i t₀ h₀) = cuspVertex F c) ∧
      ∀ j < m, ∀ c : F.Cusp, (next (word_closed F))^[j] (slotAt F i t₀ h₀) = cuspVertex F c → c.1.1 = i := by
  obtain ⟨m, hm, -, hcusp⟩ := s6b_path F h01 h₀ h₁
  refine ⟨m, hm, fun c _ s hs hcs => hcusp c s hs hcs, ?_⟩
  intro j _ c hjc
  have := s6b_circ_iterate F (slotAt F i t₀ h₀) j
  rw [hjc, s6b_circ_cuspVertex, s6b_circ_slotAt] at this
  exact this

/-- LEAF (S6): every cycle of `next` carries a cusp vertex (a cycle of cut slots only would keep its x-direction,
`xsign_next_iff`, and strictly increase `xcoord2`, `xcoord2_next` — impossible on a finite cycle). -/
theorem exists_cuspVertex_sameCycle (u : Slot (word F)) :
    ∃ c : F.Cusp, (nextPerm (word_closed F)).SameCycle u (cuspVertex F c) := by
  by_contra hno
  push Not at hno
  have hcut : ∀ j, ((next (word_closed F))^[j] u).1.2 ≠ 0 := by
    intro j hj
    obtain ⟨c, hc⟩ := s6b_cuspVertex_of_snd_eq_zero F _ hj
    exact hno c (sameCycle_of_iterate (word_closed F) (a := j) (b := 0)
      (by rw [Function.iterate_zero_apply]; exact hc))
  have hsign : ∀ j, xsign ((next (word_closed F))^[j] u) = xsign u := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [Function.iterate_succ_apply', ← ih]
      have hc := hcut (j + 1)
      rw [Function.iterate_succ_apply'] at hc
      exact (xsign_next_iff (word_closed F) _).2 hc
  have hP := period_pos (word_closed F) u
  have hper := iterate_period (word_closed F) u
  cases hx : xsign u with
  | true =>
    have hmono : ∀ j, xcoord2 u + j ≤ xcoord2 ((next (word_closed F))^[j] u) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        have := (xcoord2_next (word_closed F) _).1 (by rw [hsign j]; exact hx)
        omega
    have := hmono (period (word_closed F) u)
    rw [hper] at this
    omega
  | false =>
    have hmono : ∀ j, xcoord2 ((next (word_closed F))^[j] u) + j ≤ xcoord2 u := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [Function.iterate_succ_apply']
        have := (xcoord2_next (word_closed F) _).2 (by rw [hsign j]; exact hx)
        omega
    have := hmono (period (word_closed F) u)
    rw [hper] at this
    omega

/-- LEAF (S6, `comp`): the slot of an occurrence lies on the cycle of its circle (`jump_cross` puts `Φ p` on the
path from `slotAt (t_p − ε)`, then `path_cusps` over one period reaches the cusp vertex of `someCuspOn`). -/
theorem slotComp_ΦFun (p : F.Occ) : U2.slotComp (word_closed F) (ΦFun F p) = circleComp F p.1.1 := by
  unfold circleComp
  rw [U2.slotComp_eq_iff]
  obtain ⟨t, ht⟩ := s6b_exists_regular F p.1.1
  have ht' : xOf F (someCuspOn F p.1.1).1.1 t ∉ singX F := by rwa [someCuspOn_fst]
  have e := s6b_slotAt_fst_eq F (someCuspOn_fst F p.1.1) ht' ht
  have h2 := s6b_sameCycle_cuspVertex F (someCuspOn F p.1.1) ht'
  rw [e] at h2
  exact (s6b_sameCycle_ΦFun F p ht).symm.trans h2

/-- LEAF (S6, `succ`, THE HEART): the first `σ` slot after `Φ p` along `next` is `Φ` of the next occurrence on the
circle (`jump_cross` at `p` puts `Φ p` at index `a` of the path from `slotAt (t_p − ε)`, `path_no_occ` up to the
successor — no occurrence strictly between, `cycNext_no_between` on `occComp`/`occKey`; `slotAt` is 1-periodic in
`t` for the wrap-around when `p` is alone — and `jump_cross` at the successor; then `firstReturn_eq_of_path`). -/
theorem ΦFun_cycNext (p : F.Occ) :
    ΦFun F (cycNext (occComp F) (occKey F) (occKey_inj F) p) =
      (firstReturn (nextPerm (word_closed F)) U2.IsσSlot (ΦSub F p)).1 := by
  obtain ⟨p', hp'⟩ : ∃ p', p' = cycNext (occComp F) (occKey F) (occKey_inj F) p := ⟨_, rfl⟩
  have hcomp : p'.1.1 = p.1.1 := by rw [hp']; exact comp_cycNext (occComp F) (occKey F) (occKey_inj F) p
  obtain ⟨n, hn⟩ : ∃ n : ℤ, n = if p.1.2 < p'.1.2 then 0 else 1 := ⟨_, rfl⟩
  have hlt : p.1.2 < p'.1.2 + n := by
    rw [hn]
    split_ifs with h
    · simpa using h
    · have := (SmoothFront.Occ.mem_Ico F p).2
      have := (SmoothFront.Occ.mem_Ico F p').1
      push_cast; linarith
  have hno : ∀ q : F.Occ, ∀ s ∈ Set.Ioo p.1.2 (p'.1.2 + n), ¬ SameParam q.1 (p.1.1, s) := by
    intro q s hs hq
    rw [hp'] at hn hs
    exact s6b_no_occ_between F p q hn hs hq
  rw [← hp']
  -- the three pieces of the path: across `p`, between, across `p'`
  obtain ⟨ε₁, hε₁, H₁⟩ := jump_cross F p
  obtain ⟨ε₃, hε₃, H₃⟩ := s6b_jump_cross_shift F p' n
  obtain ⟨ε', hε'pos, hε'1, hε'3, hε'mid⟩ : ∃ ε' > 0, ε' < ε₁ ∧ ε' < ε₃ ∧ 2 * ε' < p'.1.2 + n - p.1.2 := by
    have hpos : 0 < min (min ε₁ ε₃) ((p'.1.2 + n - p.1.2) / 2) :=
      lt_min (lt_min hε₁ hε₃) (by linarith)
    have m1 : min (min ε₁ ε₃) ((p'.1.2 + n - p.1.2) / 2) ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
    have m2 : min (min ε₁ ε₃) ((p'.1.2 + n - p.1.2) / 2) ≤ ε₃ := (min_le_left _ _).trans (min_le_right _ _)
    have m3 : min (min ε₁ ε₃) ((p'.1.2 + n - p.1.2) / 2) ≤ (p'.1.2 + n - p.1.2) / 2 := min_le_right _ _
    exact ⟨_ / 2, half_pos hpos, by linarith, by linarith, by linarith⟩
  obtain ⟨h₁, h₂, m₁, hm₁, hpathA, a₁, ha₁, hΦA, hnoσA⟩ := H₁ ε' ⟨hε'pos, hε'1⟩
  obtain ⟨h₃, h₄, m₃, hm₃, hpathC, a₃, ha₃, hΦC, hnoσC⟩ := H₃ ε' ⟨hε'pos, hε'3⟩
  have h₃' : xOf F p.1.1 (p'.1.2 + n - ε') ∉ singX F := by rw [← hcomp]; exact h₃
  obtain ⟨m₂, hpathB, hσB, -⟩ := s6b_path F (i := p.1.1) (t₀ := p.1.2 + ε') (t₁ := p'.1.2 + n - ε') (by linarith) h₂ h₃'
  have hfst : slotAt F p.1.1 (p'.1.2 + n - ε') h₃' = slotAt F p'.1.1 (p'.1.2 + n - ε') h₃ :=
    (s6b_slotAt_fst_eq F hcomp h₃ h₃').symm
  have hiter : ∀ k, (next (word_closed F))^[k] (ΦFun F p) =
      (next (word_closed F))^[k + a₁] (slotAt F p.1.1 (p.1.2 - ε') h₁) := by
    intro k; rw [← hΦA, ← Function.iterate_add_apply]
  have hBC : (next (word_closed F))^[a₃ + (m₂ + m₁)] (slotAt F p.1.1 (p.1.2 - ε') h₁) = ΦFun F p' := by
    rw [Function.iterate_add_apply, Function.iterate_add_apply, hpathA, hpathB, hfst, hΦC]
  have hMa : (m₁ - a₁) + m₂ + a₃ + a₁ = a₃ + (m₂ + m₁) := by omega
  have hend : (next (word_closed F))^[(m₁ - a₁) + m₂ + a₃] (ΦFun F p) = ΦFun F p' := by
    rw [hiter, hMa, hBC]
  have hMpos : 0 < (m₁ - a₁) + m₂ + a₃ := by omega
  rw [U2.firstReturn_eq_of_path (nextPerm (word_closed F)) U2.IsσSlot (ΦSub F p) hMpos ?_ ?_]
  · show ΦFun F p' = ((nextPerm (word_closed F)) ^ ((m₁ - a₁) + m₂ + a₃)) (ΦFun F p)
    rw [U2.nextPerm_pow_apply, hend]
  · show U2.IsσSlot (((nextPerm (word_closed F)) ^ ((m₁ - a₁) + m₂ + a₃)) (ΦFun F p))
    rw [U2.nextPerm_pow_apply, hend]
    exact isσSlot_ΦFun F p'
  · intro j hj0 hjM
    show ¬ U2.IsσSlot (((nextPerm (word_closed F)) ^ j) (ΦFun F p))
    rw [U2.nextPerm_pow_apply, hiter]
    by_cases hA : j + a₁ < m₁
    · exact hnoσA (j + a₁) hA (by omega)
    · by_cases hB : j + a₁ < m₁ + m₂
      · obtain ⟨j', hj'⟩ : ∃ j', j + a₁ = j' + m₁ := ⟨j + a₁ - m₁, by omega⟩
        rw [hj', Function.iterate_add_apply, hpathA]
        intro hσ
        obtain ⟨q, ⟨s, hs, hq⟩, -⟩ := hσB j' (by omega) hσ
        exact hno q s ⟨by linarith [hs.1], by linarith [hs.2]⟩ hq
      · obtain ⟨j'', hj''⟩ : ∃ j'', j + a₁ = j'' + (m₂ + m₁) := ⟨j + a₁ - (m₂ + m₁), by omega⟩
        rw [hj'', Function.iterate_add_apply, Function.iterate_add_apply, hpathA, hpathB, hfst]
        exact hnoσC j'' (by omega) (by omega)

/-- LEAF (S6): the circles of `F` correspond bijectively to the cycles of `next` (injective: every cusp vertex on the
cycle of a circle's traversal is a cusp of that circle, `path_cusps`; surjective: every cycle carries a cusp
vertex, `exists_cuspVertex_sameCycle`). -/
theorem circleComp_bijective : Function.Bijective (circleComp F) := by
  refine ⟨?_, ?_⟩
  · intro i i' h
    unfold circleComp at h
    rw [U2.slotComp_eq_iff] at h
    have := s6b_circ_of_sameCycle F h
    rwa [s6b_circ_cuspVertex, s6b_circ_cuspVertex, someCuspOn_fst, someCuspOn_fst] at this
  · intro j
    obtain ⟨c, hc⟩ := exists_cuspVertex_sameCycle F (rep (word_closed F) j)
    refine ⟨c.1.1, ?_⟩
    rw [← s6b_slotComp_cuspVertex, (U2.slotComp_eq_iff _ _ _).mpr hc.symm, U2.slotComp_eq_equivFin, orbitOf_rep,
      Equiv.apply_symm_apply]

/-- the circle bijection of the record isomorphism -/
def circleEquiv : Fin F.c ≃ Fin (numComp (word_closed F)) := Equiv.ofBijective _ (circleComp_bijective F)

end Traversal

/-! #### The assembly: the record isomorphism, the sweep statement, the leaf -/

section Assembly

variable (F : SmoothFront)

/-- THE RECORD ISOMORPHISM of the sweep, from the leaves. -/
def recordIso : RecordIso (frontRecord F) (U2.slotRecord (word_closed F) U2.IsσSlot (U2.allActive (word_closed F))) where
  e := circleEquiv F
  Φ := occEquiv F
  comp_eq p := slotComp_ΦFun F p
  succ_eq p := Subtype.ext (ΦFun_cycNext F p)
  pair_eq p := Subtype.ext (ΦFun_partner F p)
  bit_eq p := isDesc_ΦFun F p
  sgn_eq p := σsgn_ΦFun F p

/-- THE SWEEP STATEMENT, proved from the leaves. -/
theorem sweep_proof : SweepStatement F :=
  ⟨oword F, word_ne_nil F, (downCountSyn_eq F).symm, (cuspCount_eq F).symm, ⟨recordIso F⟩⟩

end Assembly

end

end U8R

/-- LEAF = THE REPRESENTATION THEOREM (ng:commutation sm-3:1924-1925, proof 1938-1947 "separate them by small
local x translations ... Reading successive vertical cuts then gives the finite elementary word"): the
block's analytic bridge (FINAL §8 risk 1; 7.5-11k lines; attacked last; rows 76 and 83 wait for it). -/
theorem represent (F : SmoothFront) : ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) :=
  U8R.represent_of_sweepStatement F (U8R.sweep_proof F)

end Leaves

/-! ## Glue (all proved) -/

/-! ### Degrees -/

/-- `deg_a δ^n = n` (`degAZ_mul` in the domain `R`). -/
theorem degAZ_delta_pow (n : ℕ) : degAZ (R.delta ^ n) = n := by
  induction n with
  | zero => simp [degAZ, degA_one]
  | succ n ih =>
    rw [pow_succ, degAZ_mul (pow_ne_zero _ delta_ne_zero) delta_ne_zero, ih, degAZ_delta]
    push_cast; ring

/-- "Solving the skein relation separately in the two directions" (sm-3:2132-2142): the recursion at a
positive crossing, solved for the switched diagram. -/
theorem switch_of_recursion_pos {f g h : R} (e : f = R.aInv * R.aInv * g + R.aInv * R.z * h) :
    g = R.a * R.a * f - R.a * R.z * h := by
  subst e
  linear_combination (-(g * (R.a * R.aInv + 1) + R.a * R.z * h)) * R.a_mul_aInv

/-- The recursion at a negative crossing, solved for the switched diagram. -/
theorem switch_of_recursion_neg {f g h : R} (e : f = R.a * R.a * g - R.a * R.z * h) :
    g = R.aInv * R.aInv * f + R.aInv * R.z * h := by
  subst e
  linear_combination (-(g * (R.a * R.aInv + 1) - R.aInv * R.z * h)) * R.a_mul_aInv

/-! ### Polynomial equalities from the leaves -/

/-- ng:commutation: `Δd = 0` (T-rec + rp:record-polynomial). -/
theorem P_comm {W W' : OWord} (h : IsComm W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram :=
  presentations _ _ (comm_recordIso h)

/-- ng:deletions, zigzag: `Δd = 0`. -/
theorem P_zigzag {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram :=
  presentations _ _ (zigzag_recordIso h)

/-- ng:circle (sm-3:2059 "For nonempty remainder, P_before = δ P_after"): lp:split-circle in record form. -/
theorem P_circleDeletion {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    P (realize W).diagram = R.delta * P (realize W').diagram :=
  P_addFree _ _ (circle_recordIso_addFree h)

/-- ng:front-III: `Δd = 0` (`P_reidemeister_III` on the site). -/
theorem P_typeIII {W W' : OWord} (h : IsTypeIII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨U, hU⟩ := typeIII_site h
  exact P_reidemeister_III ⟨U, Or.inl hU⟩

/-- ng:front-II: `Δd = 0` (`P_reidemeister_II` to the vertex-moved diagram, then its record). -/
theorem P_typeII {W W' : OWord} (h : IsTypeII W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := typeII_move h
  exact (P_reidemeister_II hR).symm.trans (presentations _ _ hrec)

/-- ng:front-I: `Δd = 0` (`P_reidemeister_I`, then the record). -/
theorem P_typeI {W W' : OWord} (h : IsTypeI W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := typeI_move h
  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)

/-- ng:deletions, crossed cusp: `Δd = 0`. -/
theorem P_crossedCusp {W W' : OWord} (h : IsCrossedCuspShortcut W.letters W'.letters) :
    P (realize W).diagram = P (realize W').diagram := by
  obtain ⟨D, hR, hrec⟩ := crossedCusp_move h
  exact (P_reidemeister_I hR).symm.trans (presentations _ _ hrec)


/-! ### The base and the standard circles -/

/-- ng:circle's second sentence for an arbitrary PL union of standard circles: `D = c` (L-PL), `w = 0`,
`P = δ^{c−1}` (lp:split-circle's crossing-free clause), so `B = c − (c − 1) − 1 = 0`. -/
theorem PLFront.IsStandardCircles.defect_eq_zero (F : PLFront) (h : F.IsStandardCircles) : F.defect = 0 := by
  rw [h.defect_eq, PLFront.IsStandardCircles.downCount_eq_c_general F h, P_crossingFree h.1, degAZ_delta_pow]
  have hc := F.Γ.hc
  have hcc : F.diagram.componentCount = F.Γ.c := rfl
  omega

/-- The base clause of the descent on the syntactic base of `SM.ng_finite_word` (ng:circle's `B = 0` for the
base, with the accepted planarity fact for realizations — independent of L-PL). -/
theorem base_defect_nonneg (W : OWord) (hW : W.IsStandardCircleBase) : 0 ≤ (realize W).defect := by
  have hstd := realize_isStandardCircles_of_base W hW
  have hD := realize_downCount_eq_c_of_base W hW
  rw [hstd.defect_eq, hD, P_crossingFree hstd.1, degAZ_delta_pow]
  have hc := (realize W).Γ.hc
  have hcc : (realize W).diagram.componentCount = (realize W).Γ.c := rfl
  omega

/-! ### The cusp-skein inequality from a site (display ng:skein-defect, sm-3:2127-2163) -/

/-- Display ng:skein-defect, first line, for the earlier branch `A` of the printed direction: the site lives
in `A`; positive `x` uses ng:skein-plus/degree-plus, negative `x` ng:skein-minus/degree-minus. -/
theorem skein_ineq_forward {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨x, hrec, ⟨D₀, hsm, hrec₀⟩, hsign⟩ := skein_site h
  obtain ⟨hDA, hDA', hw⟩ := skein_counts h
  have hPA' : P (realize A').diagram = P ((realize A).diagram.switch x) := presentations _ _ hrec
  have hP₀ : P D₀ = P (realize C).diagram := presentations _ _ hrec₀
  unfold PLFront.defect
  rw [hDA, hDA']
  rcases (realize A).diagram.sign_eq_one_or_neg_one x with h1 | h1
  · have hpos : (realize A).diagram.IsPositive x := ((realize A).diagram.isPositive_iff_sign_eq_one x).2 h1
    have e := P_recursion_pos hsm hpos
    rw [← hPA', hP₀] at e
    have hb := degAZ_le_of_eq_pos (P_ne_zero _) (P_ne_zero _) e (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)
  · have hneg : ¬ (realize A).diagram.IsPositive x := by
      intro hp
      have := ((realize A).diagram.isPositive_iff_sign_eq_one x).1 hp
      rw [this] at h1; exact absurd h1 (by decide)
    have e := P_recursion_neg hsm hneg
    rw [← hPA', hP₀] at e
    have hb := degAZ_le_of_eq_neg (P_ne_zero _) (P_ne_zero _) e (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

/-- Display ng:skein-defect, second line ("the other principal direction", sm-3:2164-2166 "Reflected ...
templates follow by relabeling their actual attachments and arrows in this local calculation"): the site
lives in `A'`, and the recursion is solved the other way (`switch_of_recursion_pos/neg`). -/
theorem skein_ineq_backward {A A' C : OWord} (h : IsCuspSkeinStep A'.letters A.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect := by
  obtain ⟨x, hrec, ⟨D₀, hsm, hrec₀⟩, hsign⟩ := skein_site h
  obtain ⟨hDA', hDA, hw⟩ := skein_counts h
  have hPA : P (realize A).diagram = P ((realize A').diagram.switch x) := presentations _ _ hrec
  have hP₀ : P D₀ = P (realize C).diagram := presentations _ _ hrec₀
  unfold PLFront.defect
  rw [hDA, hDA']
  rcases (realize A').diagram.sign_eq_one_or_neg_one x with h1 | h1
  · have hpos : (realize A').diagram.IsPositive x := ((realize A').diagram.isPositive_iff_sign_eq_one x).2 h1
    have e := P_recursion_pos hsm hpos
    rw [← hPA, hP₀] at e
    have e' := switch_of_recursion_pos e
    have hb := degAZ_le_of_eq_neg (P_ne_zero _) (P_ne_zero _) e' (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)
  · have hneg : ¬ (realize A').diagram.IsPositive x := by
      intro hp
      have := ((realize A').diagram.isPositive_iff_sign_eq_one x).1 hp
      rw [this] at h1; exact absurd h1 (by decide)
    have e := P_recursion_neg hsm hneg
    rw [← hPA, hP₀] at e
    have e' := switch_of_recursion_neg e
    have hb := degAZ_le_of_eq_pos (P_ne_zero _) (P_ne_zero _) e' (P_ne_zero _)
    rw [h1] at hsign
    simp at hsign
    rcases le_max_iff.1 hb with h2 | h2
    · exact le_trans (min_le_left _ _) (by omega)
    · exact le_trans (min_le_right _ _) (by omega)

end FrontRows

open FrontRows

/-! ## Assembly of the rows -/

/-- **ng:commutation** (row 76), assembled. -/
theorem ng_commutation : NgCommutationClauses where
  comm_D := fun _ _ h => (comm_counts h).1
  comm_w := fun _ _ h => (comm_counts h).2
  comm_d := fun _ _ h => by rw [P_comm h]
  comm_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(comm_counts h).1, (comm_counts h).2, P_comm h]
  deform_D := deform_downCount
  deform_w := deform_writhe
  deform_d := fun F F' h S S' hS hS' => by rw [deform_P F F' h S S' hS hS']
  deform_B := fun F F' h S S' hS hS' => by
    unfold SmoothFront.defect SmoothFront.dOf
    rw [deform_downCount F F' h, deform_writhe F F' h, deform_P F F' h S S' hS hS']
  represent := represent

/-- **ng:front-I** (row 77), assembled: display ng:type-I-counts and `Δd = 0` give `ΔB = 0` (sm-3:1967). -/
theorem ng_front_I : NgFrontIClauses where
  typeI_B := fun _ _ h => by
    obtain ⟨hD, hw⟩ := typeI_counts h
    unfold PLFront.defect
    rw [P_typeI h, hD, hw]
    push_cast; ring

/-- **ng:front-II** (row 78), assembled. -/
theorem ng_front_II : NgFrontIIClauses where
  typeII_D := fun _ _ h => (typeII_counts h).1
  typeII_w := fun _ _ h => (typeII_counts h).2
  typeII_d := fun _ _ h => by rw [P_typeII h]
  typeII_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(typeII_counts h).1, (typeII_counts h).2, P_typeII h]

/-- **ng:front-III** (row 79), assembled. -/
theorem ng_front_III : NgFrontIIIClauses where
  typeIII_D := fun _ _ h => (typeIII_counts h).1
  typeIII_w := fun _ _ h => (typeIII_counts h).2
  typeIII_d := fun _ _ h => by rw [P_typeIII h]
  typeIII_B := fun _ _ h => by
    unfold PLFront.defect
    rw [(typeIII_counts h).1, (typeIII_counts h).2, P_typeIII h]

/-- **ng:deletions** (row 80), assembled: the `s` clauses from the accepted syntactic counts through
`realize_sCount` (both words nonempty), the `B` clauses from the count displays and the polynomial leaves. -/
theorem ng_deletions : NgDeletionsClauses where
  zigzag_s := fun W W' h => by
    rw [realize_sCount W h.source_ne_nil, realize_sCount W' (IsZigzagDeletion.ne_nil h W.closed)]
    exact h.sCount
  zigzag_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := zigzag_counts h
    unfold PLFront.defect
    rw [P_zigzag h, hw]
    rcases hD with hD | hD
    · rw [hD]
    · rw [hD]; push_cast; omega
  crossedCusp_s := fun W W' h => by
    rw [realize_sCount W h.ne_nil.1, realize_sCount W' h.ne_nil.2]
    exact h.sCount
  crossedCusp_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := crossedCusp_counts h
    unfold PLFront.defect
    rw [P_crossedCusp h, hw]
    rcases hD with hD | hD <;> omega

/-- **ng:circle** (row 81), assembled: display ng:circle-counts with `deg_a (δ P) = deg_a P + 1` ("Its
product with the leading coefficient of P_after is nonzero because the coefficient ring is an integral
domain", sm-3:2061-2063: `degAZ_mul` in the domain `R`). -/
theorem ng_circle : NgCircleClauses where
  circleDeletion_B := fun W W' h => by
    obtain ⟨hw, hD⟩ := circleDeletion_counts h
    have hdeg : degAZ (P (realize W).diagram) = degAZ (P (realize W').diagram) + 1 := by
      rw [P_circleDeletion h, degAZ_mul delta_ne_zero (P_ne_zero _), degAZ_delta]; ring
    unfold PLFront.defect
    rw [hdeg, hw, hD]
    push_cast; ring
  single_B := fun F h _ => PLFront.IsStandardCircles.defect_eq_zero F h
  union_B := fun F h => PLFront.IsStandardCircles.defect_eq_zero F h

/-- **ng:cusp-skein** (row 82), assembled. -/
theorem ng_cusp_skein : NgCuspSkeinClauses where
  earlier_branch := fun _ _ _ h => by
    rcases h with h | h
    · exact skein_ineq_forward h
    · exact skein_ineq_backward h
  unique_smoothing := fun _ _ _ _ h h' => skein_unique h h'
  smoothing_s := fun A A' C h => by
    obtain ⟨hA, -, hC⟩ := h.ne_nil
    rw [realize_sCount A hA, realize_sCount C hC]
    exact h.sCount.2
  principal_s := fun A A' C h => by
    obtain ⟨hA, hA', -⟩ := h.ne_nil
    rw [realize_sCount A hA, realize_sCount A' hA']
    exact h.sCount.1

/-- Both displayed inequalities of ng:skein-defect (sm-3:2158-2163) from the row (the interchange is
symmetric in its principal branches). -/
theorem ng_cusp_skein_both {A A' C : OWord} (h : IsCuspSkein A.letters A'.letters C.letters) :
    min (realize A').defect (realize C).defect ≤ (realize A).defect ∧
    min (realize A).defect (realize C).defect ≤ (realize A').defect :=
  ⟨ng_cusp_skein.earlier_branch A A' C h, ng_cusp_skein.earlier_branch A' A C h.symm⟩

namespace FrontRows

/-! ## Row 83: the word bound, then the smooth front -/

/-- The seven laws of the descent (`Moves.Laws`) for the moves of `SM.ng_finite_word` with the geometric
`s`, `B` of the realization and the axiom's syntactic base: `pres_B` = rows 76(1), 77, 78, 79; `del_B` =
rows 80, 81(1); `skein_B` = row 82; `base_B` = row 81(2-3) on the syntactic base (`base_defect_nonneg`);
the three `s` laws are the accepted `wordMoves_pres_s/del_s/skein_s` (definitionally the same fields). -/
theorem certificate_laws :
    (wordMovesOf (fun W => (realize W).sCount) (fun W => (realize W).defect) OWord.IsStandardCircleBase).Laws where
  pres_B := fun F F' h => by
    rcases h with h | h | h | h
    · exact ng_commutation.comm_B F F' h
    · exact ng_front_I.typeI_B F F' h
    · exact ng_front_II.typeII_B F F' h
    · exact ng_front_III.typeIII_B F F' h
  pres_s := fun F F' h => wordMoves_pres_s F F' h
  del_B := fun F F' h => by
    rcases h with h | h | h
    · exact ng_deletions.zigzag_B F F' h
    · exact ng_deletions.crossedCusp_B F F' h
    · exact (ng_circle.circleDeletion_B F F' h).symm.le
  del_s := fun F F' h => wordMoves_del_s F F' h
  skein_B := fun F F' C h => ng_cusp_skein.earlier_branch F F' C h
  skein_s := fun F F' C h => wordMoves_skein_s F F' C h
  base_B := fun W hW => base_defect_nonneg W hW

/-- ng:local-front-bound on words (sm-3:2313-2343, the degree induction along the principal chains of
Literature input ng:finite-word): `B ≥ 0` on every closed oriented word's realization.  Consumes
`SM.ng_finite_word`.  The named companion of row 83 (not a field: the printed clause is on the smooth
class). -/
theorem word_bound : ∀ W : OWord, 0 ≤ (realize W).defect :=
  ng_finite_word_bound _ _ certificate_laws

end FrontRows

/-- **ng:local-front-bound** (row 83), assembled: the representation clause of ng:commutation carries `D`,
`w` and the rounding's record to a word; rp:record-polynomial (`presentations`) carries `P`; the word
bound gives `B ≥ 0`; display ng:defect converts (sm-3:2343). -/
theorem ng_local_front_bound : NgLocalFrontBoundClauses where
  front_inequality := fun F S hS => by
    obtain ⟨W, hD, hw, -, hrec⟩ := ng_commutation.represent F
    have hP : P S = P (realize W).diagram := presentations S _ (hrec S hS)
    have h0 := FrontRows.word_bound W
    rw [← F.defect_nonneg_iff S]
    unfold SmoothFront.defect SmoothFront.dOf
    rw [hD, hw, hP]
    exact h0

end SM
