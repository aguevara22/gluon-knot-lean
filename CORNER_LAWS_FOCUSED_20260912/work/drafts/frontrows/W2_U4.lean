import SM.FrontRealizeGeometry
import SM.FrontRealizeBase
import SM.FrontRealizeDeform
import SM.FrontInterfaces
import SM.FrontWordsBase
import SM.FrontGeomModel
import SM.PolynomialBlock

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

/-! ### L-rec (unit U3, on the record core U2) — named-record isomorphisms (rp:record-polynomial
`presentations`, lp:split-circle in record form `P_addFree`, the accepted smoothing gate
`exists_smoothing_record_visit`).  Record of a realization: visits = the two slots of each `σ` letter,
successor = the next `σ` slot along the slot cycle `next` (`toSlot_succ`, `crossingParam_eq_half`), twin = the
other slot of the column, over = the descending strand (`overStrand_crossingOf`), sign = `sign_crossingOf`;
exterior slots of two words correspond by the index shift (`shiftIdx`, `next_ext`). -/

/-- LEAF (ng:commutation, sm-3:1929-1933 "After cusp rounding this is a positive page isotopy; equivalently,
the full named records are the same"). -/
theorem comm_recordIso {W W' : OWord} (h : IsComm W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := sorry

/-- LEAF (ng:deletions, sm-3:2017-2019: after rounding the zigzag "is a simple ordinary arc, positively page
isotopic relative to its endpoints to the straightened arc" — no crossing is touched; every strand passes
through the block, the exterior visits and their cyclic orders are unchanged). -/
theorem zigzag_recordIso {W W' : OWord} (h : IsZigzagDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record) := sorry

/-- LEAF (ng:circle, sm-3:2054-2059 "A standard circle separated by the word procedure has no mixed crossings
... Lemma lp:split-circle permits this nesting"): the record of the word with the circle is the record of the
remainder with one free (crossing-free) component added. -/
theorem circle_recordIso_addFree {W W' : OWord} (h : IsCircleDeletion W.letters W'.letters) :
    Nonempty (RecordIso (realize W).diagram.record (realize W').diagram.record.addFree) := sorry

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
theorem skein_site {A A' C : OWord} (h : IsCuspSkeinStep A.letters A'.letters C.letters) : SkeinSite A A' C :=
  sorry

/-- LEAF (ng:cusp-skein "the unique compatible smoothing", FR-12): the interchange determines `C` — the two
principal words differ first at the cusp letter, which fixes `X`, `m`, `d`, `Y`; the through-strand bit is
read from `run X []`; the reverse-direction case is contradictory (`l (m+1) = l m'`, `l m = l (m'+1)`). -/
theorem skein_unique {A A' C C' : Word} (h : IsCuspSkein A A' C) (h' : IsCuspSkein A A' C') : C = C' :=
  sorry

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

/-- LEAF (ng:commutation, sm-3:1934-1936 "A deformation without a singular event preserves the records, D and
w: signs, cusp directions and cyclic attachments cannot change"): `D`.  Along a jointly smooth family inside
the class, the cusp set `{x' = 0}` is a covering of `[0,1]` (`x'' ≠ 0` at every zero, vertical tangencies
excluded), on which the discriminant `x''·det(γ'', γ''')` is continuous and nonzero. -/
theorem deform_downCount (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.downCount = F'.downCount := sorry

/-- LEAF: the same for `w` (the transverse double points form a covering of `[0,1]`, no accumulation at a
semicubical cusp, `crossSign` continuous and nonzero). -/
theorem deform_writhe (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) :
    F.writhe = F'.writhe := sorry

/-- LEAF: the same for the records of the roundings, hence (sm-3:1936-1937 "Lemma rp:record-polynomial gives
scalar equality") the polynomial: the `Marking` of `F` transports along the family to a `Marking` of `F'`. -/
theorem deform_P (F F' : SmoothFront) (h : Nonempty (F.NonsingularDeformation F')) (S S' : Diagram)
    (hS : F.IsRounding S) (hS' : F'.IsRounding S') : P S = P S' := sorry

/-- LEAF = THE REPRESENTATION THEOREM (ng:commutation sm-3:1924-1925, proof 1938-1947 "separate them by small
local x translations ... Reading successive vertical cuts then gives the finite elementary word"): the
block's analytic bridge (FINAL §8 risk 1; 7.5-11k lines; attacked last; rows 76 and 83 wait for it). -/
theorem represent (F : SmoothFront) : ∃ W : OWord,
    F.downCount = (realize W).downCount ∧ F.writhe = (realize W).writhe ∧ F.sCount = (realize W).sCount ∧
    ∀ S : Diagram, F.IsRounding S → Nonempty (RecordIso S.record (realize W).diagram.record) := sorry

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
