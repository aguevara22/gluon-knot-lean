namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Source thm:A-R3E, all clauses. At a triple wall the complete data includes
every ordinary/root composition weight, every open sum, and the rooted output.
Exterior-extension and pure-cut walls assert only equality of the complete
output. Every physical root and both independent full germ-side parameters
remain quantified; no local-radius or child-genericity premise is added. -/
theorem tree_triple_and_silent_laws (hn : 3 ≤ n) :
    (∀ (w : WallGerm n) (e f k : ZMod n), w.TripleAt e f k →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        TreeDataEqual (w.sideTuple true t).val (w.sideTuple false s).val
          (w.sideTuple true t).property.1 (w.sideTuple false s).property.1 g hn) ∧
    (∀ (w : WallGerm n) (M a : ZMod n), w.ExtensionAt M a →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
          treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn) ∧
    (∀ (w : WallGerm n) (i j k : ZMod n), w.PureCutAt i j k →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
          treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w e f k ht g s t
    exact w.triple_wall_tree_data e f k hn ht g s t
  · intro w M a he g s t
    exact w.extension_tree_silent M a hn he g s t
  · intro w i j k hc g s t
    exact w.pure_cut_tree_silent i j k hn hc g s t

end
end SM
