namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]
attribute [local instance] IncreasingBoundaryTriple.contractedSize_neZero

/-- The complete first contraction tuple and cyclic covariance identify its
coefficient at the inherited physical root; all G1 and arity facts are derived. -/
theorem contactFirstArc_contracted_coefficient (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : (g - M).val < contactDistance M a)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    treeCoefficient (contractedWordTuple P g (contactFirstArcTriple g M a hn hc hu))
      (contractedWord_G1 P g (contactFirstArcTriple g M a hn hc hu)
        (by rw [contactFirstArcTriple_support]; exact hz))
      0 (by rw [contactFirstArcTriple_contractedSize]; exact (contactHalfSizes_bounds hn hc).1.1) =
      treeCoefficient (firstHalf P M a) (g1_firstHalf hn hc hz)
        ((g - M).val : ZMod (firstHalfSize M a)) (contactHalfSizes_bounds hn hc).1.1 := by
  have he := treeCoefficient_of_reindexed_tuple_eq (contactFirstArcTriple_contractedSize g M a hn hc hu)
    (contractedWordTuple P g (contactFirstArcTriple g M a hn hc hu))
    (shift ((g - M).val : ZMod (firstHalfSize M a)) (firstHalf P M a))
    (contractedWord_G1 P g (contactFirstArcTriple g M a hn hc hu)
      (by rw [contactFirstArcTriple_support]; exact hz))
    (g1_shift_forward _ (g1_firstHalf hn hc hz))
    (contactFirstArc_contracted_tuple P g M a hn hc hu)
    (by rw [contactFirstArcTriple_contractedSize]; exact (contactHalfSizes_bounds hn hc).1.1)
  have hs := treeCoefficient_shift (firstHalf P M a) (g1_firstHalf hn hc hz)
    ((g - M).val : ZMod (firstHalfSize M a)) ((g - M).val : ZMod (firstHalfSize M a))
    (contactHalfSizes_bounds hn hc).1.1
  rw [sub_self] at hs
  exact he.trans hs

/-- The complete second contraction retains the original root under the
source second-half indexing, including the final edge ending at M. -/
theorem contactSecondArc_contracted_coefficient (P : LabelledTuple n) (g M a : ZMod n)
    (hn : 3 ≤ n) (hc : ContactSeparated M a) (hu : contactDistance M a < (g - M).val)
    (hz : pointZeroTriples P = {contactSupport M a}) :
    treeCoefficient (contractedWordTuple P g (contactSecondArcTriple g M a hn hc hu))
      (contractedWord_G1 P g (contactSecondArcTriple g M a hn hc hu)
        (by rw [contactSecondArcTriple_support]; exact hz))
      0 (by rw [contactSecondArcTriple_contractedSize]; exact (contactHalfSizes_bounds hn hc).2.1) =
      treeCoefficient (secondHalf P M a) (g1_secondHalf hn hc hz)
        ((g - a).val : ZMod (secondHalfSize M a)) (contactHalfSizes_bounds hn hc).2.1 := by
  have he := treeCoefficient_of_reindexed_tuple_eq (contactSecondArcTriple_contractedSize g M a hn hc hu)
    (contractedWordTuple P g (contactSecondArcTriple g M a hn hc hu))
    (shift ((g - a).val : ZMod (secondHalfSize M a)) (secondHalf P M a))
    (contractedWord_G1 P g (contactSecondArcTriple g M a hn hc hu)
      (by rw [contactSecondArcTriple_support]; exact hz))
    (g1_shift_forward _ (g1_secondHalf hn hc hz))
    (contactSecondArc_contracted_tuple P g M a hn hc hu)
    (by rw [contactSecondArcTriple_contractedSize]; exact (contactHalfSizes_bounds hn hc).2.1)
  have hs := treeCoefficient_shift (secondHalf P M a) (g1_secondHalf hn hc hz)
    ((g - a).val : ZMod (secondHalfSize M a)) ((g - a).val : ZMod (secondHalfSize M a))
    (contactHalfSizes_bounds hn hc).2.1
  rw [sub_self] at hs
  exact he.trans hs

end
end SM
