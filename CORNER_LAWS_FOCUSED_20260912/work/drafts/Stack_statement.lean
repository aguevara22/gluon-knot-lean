import SM.LocalPolynomial

/-! Source mp:stack (reference/SM/sm-3-statesum.tex:1494-1512, frame SM15): ordered stacked blocks,
including split unions. Main declaration: `SM.stack`.

Notation (namespace `SM.Link`): "an actual nonempty diagram" is `D : Diagram` (c ≥ 1 components,
`Fin D.Γ.c`); "partitioned into `q ≥ 1` nonempty tagged blocks" is a surjection `blk : Fin D.Γ.c → Fin q`
(block `i` is the fibre over `i`; surjectivity makes every block nonempty, and `q ≥ 1` follows); "at
every crossing between different blocks the smaller-index block is under the larger one" is: for a
crossing `x` with strands `s, t`, `blk s.1 < blk t.1 → D.underStrand x = s`; "the actual restriction
`D_i` retaining all components in block `i` and all crossings internal to it" is `D.restrict` to the
fibre (`blockRestrict`); `P` is `SM.P`, `δ` is `R.delta`. -/

namespace SM

open SM.Link

/-- The restriction of `D` to the components of block `i` (the fibre of `blk` over `i`). -/
noncomputable def blockRestrict (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q)
    (hblk : Function.Surjective blk) (i : Fin q) : Diagram :=
  D.restrict (Finset.univ.filter (fun c => blk c = i))
    (by obtain ⟨c, hc⟩ := hblk i; exact ⟨c, by simp [hc]⟩)

/-- "at every crossing between different blocks the smaller-index block is under the larger one" -/
def BlockOrdered (D : Diagram) {q : ℕ} (blk : Fin D.Γ.c → Fin q) : Prop :=
  ∀ (x : D.Γ.Crossing) (s t : D.Γ.Strand), s ∈ x.val → t ∈ x.val → blk s.1 < blk t.1 →
    D.underStrand x = s

/-- mp:stack as printed. -/
structure StackData : Prop where
  /-- eq. mp:stack-value: `P_D = δ^{q−1} ∏_{i=1}^q P_{D_i}`. -/
  stack : ∀ (D : Diagram) (q : ℕ) (blk : Fin D.Γ.c → Fin q) (hblk : Function.Surjective blk),
    BlockOrdered D blk →
    P D = R.delta ^ (q - 1) * ∏ i : Fin q, P (blockRestrict D blk hblk i)
  /-- "In particular `P_{A ⊔ B} = δ P_A P_B` for two nonempty diagrams presented without mixed
  crossings": a diagram partitioned into two blocks with no crossing between the blocks. -/
  split_union : ∀ (D : Diagram) (blk : Fin D.Γ.c → Fin 2) (hblk : Function.Surjective blk),
    (∀ (x : D.Γ.Crossing) (s t : D.Γ.Strand), s ∈ x.val → t ∈ x.val → blk s.1 = blk t.1) →
    P D = R.delta * P (blockRestrict D blk hblk 0) * P (blockRestrict D blk hblk 1)

theorem stack : StackData := by
  sorry

end SM
