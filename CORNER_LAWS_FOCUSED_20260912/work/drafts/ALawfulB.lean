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
function on polygons. Main declaration: `SM.A_lawful : ALawfulData`. STATEMENT DRAFT (proof to be
supplied once `SM.root_independence` is in the library).

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

/-! ## Helpers for the proof of `A_lawful` -/

/-- On a generic polygon the amplitude equals the tree coefficient at every root
(thm:root-indep-proof). -/
theorem alB_amplitude_eq (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (g : ZMod n) :
    amplitude P hP.1 hn = treeCoefficient P hP.1 g hn :=
  root_independence n hn P hP 0 g

/-- The amplitude depends only on the tuple (proof irrelevance of the (G1) witness). -/
theorem alB_amplitude_congr (hn : 3 ≤ n) {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (h : P = Q) : amplitude P hP hn = amplitude Q hQ hn := by
  subst h
  rfl

/-- Shift invariance of the amplitude on generic polygons. -/
theorem alB_shift_invariant (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (k : ZMod n) :
    amplitude (shift k P) (g1_shift_forward k hP.1) hn = amplitude P hP.1 hn := by
  have hQ : Generic (shift k P) := ⟨g1_shift_forward k hP.1, ((generic_shift k P).mpr hP).2⟩
  calc amplitude (shift k P) (g1_shift_forward k hP.1) hn
      = treeCoefficient (shift k P) (g1_shift_forward k hP.1) (0 - k) hn :=
        alB_amplitude_eq hn (shift k P) hQ (0 - k)
    _ = treeCoefficient P hP.1 0 hn := treeCoefficient_shift P hP.1 0 k hn
    _ = amplitude P hP.1 hn := rfl

/-- Two cyclically equivalent generic tuples have the same amplitude. -/
theorem alB_amplitude_equiv (hn : 3 ≤ n) (P Q : GenericTuple n)
    (hPQ : ∃ k : ZMod n, Q.val = shift k P.val) :
    amplitude P.val P.property.1 hn = amplitude Q.val Q.property.1 hn := by
  obtain ⟨k, hk⟩ := hPQ
  calc amplitude P.val P.property.1 hn
      = amplitude (shift k P.val) (g1_shift_forward k P.property.1) hn :=
        (alB_shift_invariant hn P.val P.property k).symm
    _ = amplitude Q.val Q.property.1 hn :=
        alB_amplitude_congr hn _ _ hk.symm

/-- The amplitude descends to the polygon space. -/
theorem alB_descends (hn : 3 ≤ n) : ∃ A' : GenericPolygon n → ℤ,
    ∀ P : GenericTuple n, A' (polygonProjection P) = amplitude P.val P.property.1 hn :=
  ⟨Quotient.lift (fun P : GenericTuple n => amplitude P.val P.property.1 hn)
    (fun P Q hPQ => alB_amplitude_equiv hn P Q hPQ), fun _ => rfl⟩

/-- Chamber constancy on labelled chambers and on chambers of the polygon space. -/
theorem alB_chamber_constant (hn : 3 ≤ n) (P Q : GenericTuple n) :
    (Q ∈ labelledChamber P → amplitude Q.val Q.property.1 hn = amplitude P.val P.property.1 hn) ∧
    (polygonProjection Q ∈ chamber (polygonProjection P) →
      amplitude Q.val Q.property.1 hn = amplitude P.val P.property.1 hn) := by
  constructor
  · intro hQ
    exact ((A_chamber hn).2.1 P Q hQ 0).2.2.symm
  · intro hQ
    obtain ⟨a, _, h⟩ := (A_chamber hn).2.2.1 P Q hQ
    calc amplitude Q.val Q.property.1 hn
        = treeCoefficient Q.val Q.property.1 (0 - a) hn := alB_amplitude_eq hn Q.val Q.property _
      _ = treeCoefficient P.val P.property.1 0 hn := h 0
      _ = amplitude P.val P.property.1 hn := rfl

/-- A triangle with all turns `+1` has amplitude `-1` (lem:A-small-values (i)). -/
theorem alB_triangle_pos (P : LabelledTuple 3) (hP : G1 P) (hτ : ∀ i, turn P i = 1) :
    amplitude P hP (by norm_num) = -1 := by
  obtain ⟨τ, -, hτ', hval⟩ := A_small_values_i P hP
  have h1 : τ = 1 := by rw [← hτ' 0, hτ 0]
  subst h1
  have h := hval 0
  unfold amplitude
  rw [h]
  rfl

/-- A triangle with all turns `-1` has amplitude `+1` (lem:A-small-values (i)). -/
theorem alB_triangle_neg (P : LabelledTuple 3) (hP : G1 P) (hτ : ∀ i, turn P i = -1) :
    amplitude P hP (by norm_num) = 1 := by
  obtain ⟨τ, -, hτ', hval⟩ := A_small_values_i P hP
  have h1 : τ = -1 := by rw [← hτ' 0, hτ 0]
  subst h1
  have h := hval 0
  unfold amplitude
  rw [h]
  rfl

theorem A_lawful : ALawfulData where
  root_independent := fun n _ hn P hP g => alB_amplitude_eq hn P hP g
  shift_invariant := fun n _ hn P hP k => alB_shift_invariant hn P hP k
  descends := fun n _ hn => alB_descends hn
  chamber_constant := fun n _ hn P Q => alB_chamber_constant hn P Q
  silent := by
    intro n inst hn w
    obtain ⟨_, hext, hcut⟩ := triple_and_silent_laws_treeCoefficient hn
    refine ⟨fun M a hMa s t => ?_, fun i j k hijk s t => ?_⟩
    · exact hext w M a hMa 0 s t
    · exact hcut w i j k hijk 0 s t
  flat_law := by
    intro n inst w j hf
    have hn : 3 ≤ n := by have := hf.1; omega
    obtain ⟨hgen, -⟩ := flat_children hn w hf
    refine ⟨hgen, ?_⟩
    intro sRight sLeft hRight0 hLeft0 hR hL
    have key := (flat_law_treeCoefficient w j hf).2.2 0 sRight sLeft hRight0 hLeft0 hR hL
    unfold amplitude
    rw [key]
    exact root_independence n hn (deleteVertex w.center j) hgen (deletionRoot j 0) 0
  cusp_law := by
    intro n inst w j hf hQ
    have hn : 3 ≤ n := by have := hf.1; omega
    obtain ⟨b, hb, huniq, -, κ, hκ, hst⟩ := cusp_law_treeCoefficient w j hf hQ
    refine ⟨b, hb, huniq, κ, hκ, fun s t => ⟨(hst s t).1, fun g => ?_, fun hgen => ?_⟩⟩
    · have h1 := (hst s t).2 g
      rw [alB_amplitude_eq _ _ (w.sideTuple (w.cuspLoopSide b j) s).property g,
        alB_amplitude_eq _ _ (w.sideTuple (!(w.cuspLoopSide b j)) t).property g]
      exact h1
    · have h1 := (hst s t).2 0
      rw [alB_amplitude_eq _ _ (w.sideTuple (w.cuspLoopSide b j) s).property 0,
        alB_amplitude_eq _ _ (w.sideTuple (!(w.cuspLoopSide b j)) t).property 0, h1]
      unfold amplitude
      rw [root_independence n hn (deleteVertex w.center j) hgen (deletionRoot j 0) 0]
  vertex_edge_law := by
    intro n inst hn w M a hc
    obtain ⟨hg1, hg2, -, -, -⟩ := vertex_halves_children hn w hc
    refine ⟨hg1, hg2, fun s t => ?_⟩
    have key := (vertex_edge_law_treeCoefficient w M a hn hc).2.2.2.2 0 s t
    unfold amplitude
    rw [key, root_independence _ _ _ hg1 (halfRoots M a 0).1 0,
      root_independence _ _ _ hg2 (halfRoots M a 0).2 0]
  triple_law := by
    intro n inst hn w e f k ht s t
    exact ((triple_and_silent_laws_treeCoefficient hn).1 w e f k ht 0 s t).2.2
  soft_theorem := by
    intro n inst hn P hP j q hq
    obtain ⟨ε₁, hε₁, -, h⟩ := soft_theorem_treeCoefficient hn hP j q hq 1 one_pos
    refine ⟨ε₁, hε₁, fun ε hε hε' => ?_⟩
    obtain ⟨hQ, hall⟩ := h ε hε hε'
    refine ⟨hQ, ?_⟩
    obtain ⟨g, ⟨hg, hval, -, -, -⟩, -⟩ := hall (softParentEdge j j) (softParentEdge_ne_soft j j)
    have hgj : g = j := (softParentEdge_injective j hg).symm
    subst hgj
    rw [alB_amplitude_eq _ _ hQ (softParentEdge g g), alB_amplitude_eq hn P hP g]
    exact hval
  reversal_law := by
    intro n inst hn P hP
    have hR : Generic (reversal P) := ⟨g1_reversal_forward hP.1, ((generic_reversal P).mpr hP).2⟩
    rw [alB_amplitude_eq hn (reversal P) hR (1 - 0)]
    exact treeCoefficient_reversal P hP.1 0 hn
  triangles := by
    have hs := star_generic_law le_rfl
    exact ⟨alB_triangle_pos (star 1) _ hs.1.2.1.2.2.2.1,
      alB_triangle_neg (starNeg 1) _ hs.1.2.2.2.2.2.1⟩

end SM

#print axioms SM.A_lawful
