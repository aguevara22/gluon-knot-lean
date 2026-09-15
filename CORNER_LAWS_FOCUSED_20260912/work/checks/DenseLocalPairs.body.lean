namespace SM

open Set
noncomputable section
variable {X Y : Type*} [TopologicalSpace X]

/-- Pairwise constancy on the dense domain in a neighborhood of every point
constructs a unique locally constant extension. Every neighborhood premise
is explicit; this helper does not assume a silent-wall response. -/
theorem dense_local_pairs_extend (S : Set X) (hd : Dense S) (f : S → Y)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ a b : S, a.val ∈ U → b.val ∈ U → f a = f b) :
    ∃! F : X → Y, IsLocallyConstant F ∧ ∀ a : S, F a.val = f a := by
  classical
  choose U hU hx hpair using hlocal
  have hpoint : ∀ x : X, ∃ a : S, a.val ∈ U x := by
    intro x
    obtain ⟨y, hyS, hyU⟩ := hd.exists_mem_open (hU x) ⟨x, hx x⟩
    exact ⟨⟨y, hyS⟩, hyU⟩
  choose a ha using hpoint
  let F : X → Y := fun x => f (a x)
  have hvalue : ∀ x : X, ∀ b : S, b.val ∈ U x → f b = F x := by
    intro x b hb
    exact hpair x b (a x) hb (ha x)
  have hF : IsLocallyConstant F := by
    apply (IsLocallyConstant.iff_exists_open F).mpr
    intro x
    refine ⟨U x, hU x, hx x, ?_⟩
    intro y hy
    obtain ⟨z, hzS, hz⟩ := hd.exists_mem_open ((hU x).inter (hU y)) ⟨y, hy, hx y⟩
    exact (hvalue y ⟨z, hzS⟩ hz.2).symm.trans (hvalue x ⟨z, hzS⟩ hz.1)
  have hagree : ∀ b : S, F b.val = f b := fun b => (hvalue b.val b (hx b.val)).symm
  refine ⟨F, ⟨hF, hagree⟩, ?_⟩
  intro G hG
  funext x
  obtain ⟨U, hU, hxU, hGU⟩ := hG.1.exists_open x
  obtain ⟨V, hV, hxV, hFV⟩ := hF.exists_open x
  obtain ⟨z, hzS, hz⟩ := hd.exists_mem_open (hU.inter hV) ⟨x, hxU, hxV⟩
  calc
    G x = G z := (hGU z hz.1).symm
    _ = f ⟨z, hzS⟩ := hG.2 ⟨z, hzS⟩
    _ = F z := (hagree ⟨z, hzS⟩).symm
    _ = F x := hFV z hz.2

/-- On a connected parameter domain the preceding genuine extension is
constant, so all original dense-domain values agree. -/
theorem dense_local_pairs_constant [PreconnectedSpace X]
    (S : Set X) (hd : Dense S) (f : S → Y)
    (hlocal : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ a b : S, a.val ∈ U → b.val ∈ U → f a = f b) :
    ∀ a b : S, f a = f b := by
  obtain ⟨F, hF, huniq⟩ := dense_local_pairs_extend S hd f hlocal
  intro a b
  have he := hF.1.apply_eq_of_preconnectedSpace a.val b.val
  rw [hF.2 a, hF.2 b] at he
  exact he

end
end SM
