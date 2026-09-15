import SM.Chambers

/-! Path-invariance clauses and the full aggregate for source prop:chambers. -/

namespace SM

variable {n : ℕ} {α : Type*} [TopologicalSpace α] [PreconnectedSpace α]

theorem generic_family_chi_constant {F : α → GenericTuple n} (hF : Continuous F)
    (s t : α) (i j k : ZMod n) : chi (F s).val i j k = chi (F t).val i j k :=
  PreconnectedSpace.constant inferInstance ((continuous_generic_chi i j k).comp hF)

theorem generic_family_crossing_constant (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) (c : Finset (ZMod n)) :
    IsCrossing (F s).val c ↔ IsCrossing (F t).val c :=
  crossing_iff_of_chi_eq hn (F s).property.1 (F t).property.1
    (generic_family_chi_constant hF s t) c

theorem generic_family_crossingSet_constant (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (s t : α) :
    {c | IsCrossing (F s).val c} = {c | IsCrossing (F t).val c} :=
  Set.ext (generic_family_crossing_constant hn hF s t)

theorem generic_family_edgeParameter_continuous (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (i j : ZMod n) (hcross : ∀ t, IsCrossing (F t).val {i, j}) :
    Continuous (fun t => edgeParameter (F t).val i j) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hc : Continuous (fun t => (F t).val) := continuous_subtype_val.comp hF
  exact continuousAt_cramerFirst ((continuous_vertex i).comp hc).continuousAt
    ((continuous_vertex j).comp hc).continuousAt ((continuous_edge i).comp hc).continuousAt
    ((continuous_edge j).comp hc).continuousAt
    (crossing_edgeParameter_det_ne_zero hn (F t).property.1 (hcross t))

theorem generic_family_crossingOrder_constant (hn : 3 ≤ n) {F : α → GenericTuple n}
    (hF : Continuous F) (t₀ : α) (i j k : ZMod n)
    (hij₀ : IsCrossing (F t₀).val {i, j}) (hik₀ : IsCrossing (F t₀).val {i, k})
    (s t : α) :
    (edgeParameter (F s).val i j < edgeParameter (F s).val i k ↔
      edgeParameter (F t).val i j < edgeParameter (F t).val i k) := by
  by_cases hjk : j = k
  · subst k
    simp
  have hij (r : α) : IsCrossing (F r).val {i, j} :=
    (generic_family_crossing_constant hn hF t₀ r {i, j}).mp hij₀
  have hik (r : α) : IsCrossing (F r).val {i, k} :=
    (generic_family_crossing_constant hn hF t₀ r {i, k}).mp hik₀
  have hcj := generic_family_edgeParameter_continuous hn hF i j hij
  have hck := generic_family_edgeParameter_continuous hn hF i k hik
  let d (r : α) : ℝ := edgeParameter (F r).val i k - edgeParameter (F r).val i j
  have hd (r : α) : d r ≠ 0 := sub_ne_zero.mpr
    (generic_edgeParameters_ne hn (F r).property hjk (hij r) (hik r)).symm
  have hsign : Continuous (fun r => SignType.sign (d r)) := by
    rw [continuous_iff_continuousAt]
    intro r
    exact (continuousAt_sign_of_ne_zero (hd r)).comp (hck.sub hcj).continuousAt
  have hs : SignType.sign (d s) = SignType.sign (d t) :=
    PreconnectedSpace.constant inferInstance hsign
  change (edgeParameter (F s).val i j < edgeParameter (F s).val i k ↔
    edgeParameter (F t).val i j < edgeParameter (F t).val i k)
  calc
    _ ↔ 0 < d s := sub_pos.symm
    _ ↔ SignType.sign (d s) = 1 := sign_eq_one_iff.symm
    _ ↔ SignType.sign (d t) = 1 := by rw [hs]
    _ ↔ 0 < d t := sign_eq_one_iff
    _ ↔ _ := sub_pos

/-- All conclusions of source prop:chambers. Path parameters run through the
actual closed unit interval; crossing supports are actual unordered edge pairs.
`crossingParameter_eq_edgeParameter` identifies the displayed formula with the
source's previously defined crossing parameter. Equal crossing partners are
included (their strict comparison is false at every time). -/
theorem chambers (hn : 3 ≤ n) :
    IsOpen {P : LabelledTuple n | Generic P} ∧
    (∀ P : GenericPolygon n, IsOpen (chamber P) ∧ IsPathConnected (chamber P)) ∧
    (∀ (P Q : GenericTuple n) (γ : Path P Q),
      (∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k) ∧
      (∀ s t : unitInterval, {c | IsCrossing (γ s).val c} = {c | IsCrossing (γ t).val c}) ∧
      (∀ i j k, IsCrossing P.val {i, j} → IsCrossing P.val {i, k} →
        ∀ s t : unitInterval,
          (edgeParameter (γ s).val i j < edgeParameter (γ s).val i k ↔
            edgeParameter (γ t).val i j < edgeParameter (γ t).val i k))) := by
  refine ⟨isOpen_Generic hn, chambers_open_pathConnected hn, ?_⟩
  intro P Q γ
  refine ⟨generic_family_chi_constant γ.continuous,
    generic_family_crossingSet_constant hn γ.continuous, ?_⟩
  intro i j k hij hik s t
  exact generic_family_crossingOrder_constant hn γ.continuous 0 i j k
    (by simpa using hij) (by simpa using hik) s t

end SM
