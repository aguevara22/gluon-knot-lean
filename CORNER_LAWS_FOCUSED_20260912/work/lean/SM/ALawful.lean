import SM.TreeChamber
import SM.FlatLawTree
import SM.CuspLawTree
import SM.VertexEdgeLawTree
import SM.TripleSilentLawsTree
import SM.SoftTheoremTree
import SM.ReversalShiftLaw
import SM.StarGenericLaw
import SM.SmallValuesLemma
import SM.Children
import SM.RootIndependence

/-! Source cor:A-lawful (reference/SM/sm-6-comparison.tex:105, frame SM15): `A` is a chamber
function on polygons. Main declaration: `SM.A_lawful : ALawfulData`. Statement fixed by the executor
(work/drafts/ALawful_statement.lean); proof by a Claude Code prover subagent (workflow prove-A-lawful / attempt A), checked
with `lake env lean` (placeholder-free, standard axioms) and ported verbatim from work/drafts/ALawfulA.lean (only the #print line
removed and this sentence added); attempt B (work/drafts/ALawfulB.lean) compiles as well and is kept as a cross-check.

Notation. `A(P) := A_g(P)` for any root `g`; the Lean `amplitude P hP hn` is the tree coefficient at
the root `0` (the main text's `A_n`, rooted at the last edge `E_n`, def:treesum), and the bundle
records that every root gives the same value on generic polygons (thm:root-indep-proof) and that
the value is invariant under the cyclic shift, hence well defined on the polygon space
`GenericPolygon n` (def:polygon, def:chamber). Walls and sides are those of the accepted law rows:
a wall germ `w : WallGerm n` (def:germ) with sides `w.sideTuple true t` (`P_+`, positive parameters)
and `w.sideTuple false s` (`P_-`); at a flat wall the sides are named by the turn at `j`
(`P_right`: `turn = -1`, `P_left`: `turn = 1`, thm:A-S3); at a cusp wall the loop side is
`w.cuspLoopSide b j` with `κ = ±1` the rotation jump (thm:A-S4); the deletion is
`deleteVertex w.center j = P(0) ∖ j`, the halves are `firstHalf`/`secondHalf w.center M a`
(`λ₁, λ₂`) and `s = w.contactSign M a` (thm:A-S7); the soft insertion is `softInsertion P j q ε` with
`(χ_- + χ_+)/2 = softAmplitudeMultiplier P j q` (thm:A-soft); `reversal P` is `P̄` (def:shift);
`K_1 = star 1` (counterclockwise triangle) and `K_{-1} = starNeg 1 = reversal (star 1)` (def:star). -/

namespace SM

open WallGerm SoftDuplication

variable {n : ℕ} [NeZero n]

/-- `A(P)`: the tree coefficient at the root `0` (the main text's `A_n`). -/
noncomputable def amplitude (P : LabelledTuple n) (hP : G1 P) (hn : 3 ≤ n) : ℤ :=
  treeCoefficient P hP 0 hn

/-- cor:A-lawful as printed on SM15. -/
structure ALawfulData : Prop where
  /-- `A(P) := A_g(P)` for any root `g`: on generic polygons every root gives the same value. -/
  root_independent : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (g : ZMod n), amplitude P hP.1 hn = treeCoefficient P hP.1 g hn
  /-- `A` is invariant under the cyclic shift, hence a function of the polygon. -/
  shift_invariant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (k : ZMod n), amplitude (shift k P) (g1_shift_forward k hP.1) hn = amplitude P hP.1 hn
  /-- `A` is well defined on generic polygons: it descends to the polygon space. -/
  descends : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n), ∃ A' : GenericPolygon n → ℤ,
    ∀ P : GenericTuple n, A' (polygonProjection P) = amplitude P.val P.property.1 hn
  /-- Chamber constancy (prop:A-chamber): constant on labelled chambers and on chambers of the
  polygon space. -/
  chamber_constant : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P Q : GenericTuple n),
    (Q ∈ labelledChamber P → amplitude Q.val Q.property.1 hn = amplitude P.val P.property.1 hn) ∧
    (polygonProjection Q ∈ chamber (polygonProjection P) →
      amplitude Q.val Q.property.1 hn = amplitude P.val P.property.1 hn)
  /-- Silence (thm:A-R3E (ii)): no jump across simple extension and pure-cut walls. -/
  silent : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n),
    (∀ M a : ZMod n, w.ExtensionAt M a → ∀ s t : w.SideParameter,
      amplitude (w.sideTuple true t).val (w.sideTuple true t).property.1 hn =
        amplitude (w.sideTuple false s).val (w.sideTuple false s).property.1 hn) ∧
    (∀ i j k : ZMod n, w.PureCutAt i j k → ∀ s t : w.SideParameter,
      amplitude (w.sideTuple true t).val (w.sideTuple true t).property.1 hn =
        amplitude (w.sideTuple false s).val (w.sideTuple false s).property.1 hn)
  /-- The flat law `A(P_right) - A(P_left) = A(P(0) ∖ j)` (thm:A-S3). -/
  flat_law : ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.FlatAt j),
    Generic (deleteVertex w.center j) ∧
    ∀ (sRight sLeft : w.Parameter) (hRight0 : sRight.val ≠ 0) (hLeft0 : sLeft.val ≠ 0),
      turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
      amplitude (w.curve sRight) (w.generic_punctured sRight hRight0).1
          (by have := hf.1; omega) -
        amplitude (w.curve sLeft) (w.generic_punctured sLeft hLeft0).1
          (by have := hf.1; omega) =
        amplitude (deleteVertex w.center j) (g1_deleteVertex hf.2.1) (by have := hf.1; omega)
  /-- The cusp law `A(P_loop) - A(P_no) = -κ A(P(0) ∖ j)` when the deletion satisfies (G1)
  (thm:A-S4): the right-hand side is read at every induced root `D_j(g)` of the deletion, and is
  `-κ · A(P(0) ∖ j)` when the deletion is generic. -/
  cusp_law : ∀ (n : ℕ) [NeZero n] (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.CuspAt j)
    (hQ : G1 (deleteVertex w.center j)),
    ∃ b : Bool, CuspCase w.center j b ∧ (∀ b' : Bool, CuspCase w.center j b' → b' = b) ∧
      ∃ κ : ℤ, (κ = -1 ∨ κ = 1) ∧
        ∀ s t : w.SideParameter,
          (rotationNumber (w.sideTuple (w.cuspLoopSide b j) s).val -
            rotationNumber (w.sideTuple (!(w.cuspLoopSide b j)) t).val = (κ : ℝ)) ∧
          (∀ g : ZMod (n + 1),
            amplitude (w.sideTuple (w.cuspLoopSide b j) s).val
                (w.sideTuple (w.cuspLoopSide b j) s).property.1 (by have := hf.1; omega) -
              amplitude (w.sideTuple (!(w.cuspLoopSide b j)) t).val
                (w.sideTuple (!(w.cuspLoopSide b j)) t).property.1 (by have := hf.1; omega) =
              -κ * treeCoefficient (deleteVertex w.center j) hQ (deletionRoot j g)
                (by have := hf.1; omega)) ∧
          (Generic (deleteVertex w.center j) →
            amplitude (w.sideTuple (w.cuspLoopSide b j) s).val
                (w.sideTuple (w.cuspLoopSide b j) s).property.1 (by have := hf.1; omega) -
              amplitude (w.sideTuple (!(w.cuspLoopSide b j)) t).val
                (w.sideTuple (!(w.cuspLoopSide b j)) t).property.1 (by have := hf.1; omega) =
              -κ * amplitude (deleteVertex w.center j) hQ (by have := hf.1; omega))
  /-- The vertex–edge law `A(P_+) - A(P_-) = s A(λ₁) A(λ₂)` (thm:A-S7), both branches. -/
  vertex_edge_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n)
    (hc : w.VertexEdgeAt M a),
    Generic (firstHalf w.center M a) ∧ Generic (secondHalf w.center M a) ∧
    ∀ s t : w.SideParameter,
      amplitude (w.sideTuple true t).val (w.sideTuple true t).property.1 hn -
        amplitude (w.sideTuple false s).val (w.sideTuple false s).property.1 hn =
        (w.contactSign M a : ℤ) *
          (amplitude (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
              (contactHalfSizes_bounds hn hc.1).1.1 *
            amplitude (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              (contactHalfSizes_bounds hn hc.1).2.1)
  /-- The triple law `A(P_+) = A(P_-)` (thm:A-R3E (i)). -/
  triple_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (e f k : ZMod n),
    w.TripleAt e f k → ∀ s t : w.SideParameter,
      amplitude (w.sideTuple true t).val (w.sideTuple true t).property.1 hn =
        amplitude (w.sideTuple false s).val (w.sideTuple false s).property.1 hn
  /-- The soft theorem `A(P_ε) = ((χ_- + χ_+)/2) A(P)` in every sector, for all small `ε`
  (thm:A-soft). -/
  soft_theorem : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (j : ZMod n) (q : Plane), SoftAdmissible P j q →
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ →
      ∃ hQ : Generic (softInsertion P j q ε),
        (amplitude (softInsertion P j q ε) hQ.1 (by omega) : ℚ) =
          softAmplitudeMultiplier P j q * (amplitude P hP.1 hn : ℚ)
  /-- Reversal `A(P̄) = (-1)^n A(P)` (prop:A-reversal (ii)). -/
  reversal_law : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P),
    amplitude (reversal P) (g1_reversal_forward hP.1) hn = (-1) ^ n * amplitude P hP.1 hn
  /-- `A(K_1) = -1` and `A(K_{-1}) = +1` on the counterclockwise and clockwise triangles
  (lem:A-small-values (i)). -/
  triangles : amplitude (star 1) (star_generic_law le_rfl).1.2.2.2.1.1 (by norm_num) = -1 ∧
    amplitude (starNeg 1) (star_generic_law le_rfl).1.2.2.2.2.1.1 (by norm_num) = 1

/-! ### Helpers (all prefixed `alA_`) -/

/-- `amplitude` is the tree coefficient at the root `0`. -/
theorem alA_amplitude_def (P : LabelledTuple n) (hP : G1 P) (hn : 3 ≤ n) :
    amplitude P hP hn = treeCoefficient P hP 0 hn := rfl

/-- On a generic polygon the amplitude equals the tree coefficient at any root. -/
theorem alA_amplitude_eq_root (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (hP1 : G1 P) (g : ZMod n) :
    amplitude P hP1 hn = treeCoefficient P hP1 g hn :=
  root_independence n hn P hP 0 g

/-- Any two tree coefficients of a generic polygon agree, with arbitrary (G1) witnesses. -/
theorem alA_treeCoefficient_root_eq (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P)
    (hP1 : G1 P) (g h : ZMod n) :
    treeCoefficient P hP1 g hn = treeCoefficient P hP1 h hn :=
  root_independence n hn P hP g h

/-- Transport of `amplitude` along an equality of tuples. -/
theorem alA_amplitude_congr {P Q : LabelledTuple n} (hPQ : P = Q) (hP : G1 P) (hQ : G1 Q)
    (hn : 3 ≤ n) : amplitude P hP hn = amplitude Q hQ hn := by
  subst hPQ; rfl

/-- Shift invariance of the amplitude on generic polygons. -/
theorem alA_shift_invariant (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (k : ZMod n) :
    amplitude (shift k P) (g1_shift_forward k hP.1) hn = amplitude P hP.1 hn := by
  have hgen : Generic (shift k P) := (generic_shift k P).mpr hP
  rw [alA_amplitude_eq_root hn (shift k P) hgen _ (0 - k)]
  exact treeCoefficient_shift P hP.1 0 k hn

/-- Compatibility of the amplitude with the cyclic setoid on generic tuples. -/
theorem alA_amplitude_compat (hn : 3 ≤ n) (P Q : GenericTuple n)
    (h : (genericCyclicSetoid n) P Q) :
    amplitude P.val P.property.1 hn = amplitude Q.val Q.property.1 hn := by
  obtain ⟨k, hk⟩ : ∃ k : ZMod n, Q.val = shift k P.val := h
  rw [alA_amplitude_congr hk Q.property.1 (g1_shift_forward k P.property.1) hn]
  exact (alA_shift_invariant hn P.val P.property k).symm

/-- The descended amplitude on the polygon space. -/
noncomputable def alA_polygonAmplitude (hn : 3 ≤ n) : GenericPolygon n → ℤ :=
  Quotient.lift (s := genericCyclicSetoid n)
    (fun P : GenericTuple n => amplitude P.val P.property.1 hn)
    (fun P Q h => alA_amplitude_compat hn P Q h)

theorem alA_polygonAmplitude_projection (hn : 3 ≤ n) (P : GenericTuple n) :
    alA_polygonAmplitude hn (polygonProjection P) = amplitude P.val P.property.1 hn := rfl

/-- The triangle values: `A(K_1) = -1`. -/
theorem alA_star_one :
    amplitude (star 1) (star_generic_law le_rfl).1.2.2.2.1.1 (by norm_num) = -1 := by
  obtain ⟨τ, -, hτ, hval⟩ := A_small_values_i (star 1) (star_generic_law le_rfl).1.2.2.2.1.1
  have h1 : τ = 1 := by
    rw [← hτ 0]
    exact (star_generic_law le_rfl).1.2.1.2.2.2.1 0
  rw [alA_amplitude_def, hval 0, h1]
  rfl

/-- The triangle values: `A(K_{-1}) = 1`. -/
theorem alA_starNeg_one :
    amplitude (starNeg 1) (star_generic_law le_rfl).1.2.2.2.2.1.1 (by norm_num) = 1 := by
  obtain ⟨τ, -, hτ, hval⟩ := A_small_values_i (starNeg 1) (star_generic_law le_rfl).1.2.2.2.2.1.1
  have h1 : τ = -1 := by
    rw [← hτ 0]
    exact (star_generic_law le_rfl).1.2.2.2.2.2.1 0
  rw [alA_amplitude_def, hval 0, h1]
  rfl

theorem A_lawful : ALawfulData where
  root_independent := fun n _ hn P hP g => alA_amplitude_eq_root hn P hP hP.1 g
  shift_invariant := fun n _ hn P hP k => alA_shift_invariant hn P hP k
  descends := fun n _ hn => ⟨alA_polygonAmplitude hn, alA_polygonAmplitude_projection hn⟩
  chamber_constant := by
    intro n _ hn P Q
    refine ⟨fun hQ => ?_, fun hQ => ?_⟩
    · exact ((A_chamber hn).2.1 P Q hQ 0).2.2.symm
    · obtain ⟨a, -, ha⟩ := (A_chamber hn).2.2.1 P Q hQ
      rw [alA_amplitude_eq_root hn Q.val Q.property _ (0 - a)]
      exact ha 0
  silent := by
    intro n _ hn w
    refine ⟨fun M a h s t => ?_, fun i j k h s t => ?_⟩
    · exact (triple_and_silent_laws_treeCoefficient hn).2.1 w M a h 0 s t
    · exact (triple_and_silent_laws_treeCoefficient hn).2.2 w i j k h 0 s t
  flat_law := by
    intro n _ w j hf
    have hn : 3 ≤ n := by have := hf.1; omega
    obtain ⟨hg, -⟩ := flat_children hn w hf
    refine ⟨hg, fun sRight sLeft hRight0 hLeft0 hR hL => ?_⟩
    have h := (flat_law_treeCoefficient w j hf).2.2 0 sRight sLeft hRight0 hLeft0 hR hL
    rw [alA_amplitude_def, alA_amplitude_def, alA_amplitude_def, h]
    exact alA_treeCoefficient_root_eq hn _ hg _ _ _
  cusp_law := by
    intro n _ w j hf hQ
    obtain ⟨b, hb, huniq, -, κ, hκ, hlaw⟩ := cusp_law_treeCoefficient w j hf hQ
    refine ⟨b, hb, huniq, κ, hκ, fun s t => ⟨(hlaw s t).1, fun g => ?_, fun hgen => ?_⟩⟩
    · have hn1 : 3 ≤ n + 1 := by have := hf.1; omega
      rw [alA_amplitude_eq_root hn1 _ (w.sideTuple (w.cuspLoopSide b j) s).property _ g,
        alA_amplitude_eq_root hn1 _ (w.sideTuple (!(w.cuspLoopSide b j)) t).property _ g]
      exact (hlaw s t).2 g
    · have hn : 3 ≤ n := by have := hf.1; omega
      rw [alA_amplitude_def, alA_amplitude_def, alA_amplitude_def, (hlaw s t).2 0]
      congr 1
      exact alA_treeCoefficient_root_eq hn _ hgen _ _ _
  vertex_edge_law := by
    intro n _ hn w M a hc
    obtain ⟨hg1, hg2, hs1, hs2, -⟩ := vertex_halves_children hn w hc
    refine ⟨hg1, hg2, fun s t => ?_⟩
    have h := (vertex_edge_law_treeCoefficient w M a hn hc).2.2.2.2 0 s t
    rw [alA_amplitude_def, alA_amplitude_def, alA_amplitude_def, alA_amplitude_def, h]
    congr 2
    · exact alA_treeCoefficient_root_eq hs1.1 _ hg1 _ _ _
    · exact alA_treeCoefficient_root_eq hs2.1 _ hg2 _ _ _
  triple_law := by
    intro n _ hn w e f k h s t
    exact ((triple_and_silent_laws_treeCoefficient hn).1 w e f k h 0 s t).2.2
  soft_theorem := by
    intro n _ hn P hP j q hq
    obtain ⟨ε1, hε1, -, hlaw⟩ := soft_theorem_treeCoefficient hn hP j q hq 1 one_pos
    refine ⟨ε1, hε1, fun ε hε hεlt => ?_⟩
    obtain ⟨hQ, hall⟩ := hlaw ε hε hεlt
    refine ⟨hQ, ?_⟩
    obtain ⟨g, ⟨hg, heq, -, -, -⟩, -⟩ := hall (softParentEdge j j) (softParentEdge_ne_soft j j)
    have hgj : j = g := softParentEdge_injective j hg
    subst hgj
    have hn1 : 3 ≤ n + 1 := by omega
    rw [alA_amplitude_eq_root hn1 _ hQ _ (softParentEdge j j),
      alA_amplitude_eq_root hn _ hP _ j]
    exact heq
  reversal_law := by
    intro n _ hn P hP
    have hgen : Generic (reversal P) := (generic_reversal P).mpr hP
    rw [alA_amplitude_eq_root hn _ hgen _ (1 - 0)]
    exact treeCoefficient_reversal P hP.1 0 hn
  triangles := ⟨alA_star_one, alA_starNeg_one⟩

end SM

