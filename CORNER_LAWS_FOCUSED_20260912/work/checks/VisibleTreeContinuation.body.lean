namespace SM

open Set
noncomputable section
variable {n : ℕ} [NeZero n]

/-- The source's finite polygonal chain yields an actual continuous path
inside the same set, by concatenating its real straight segments. -/
theorem polygonalJoin_joinedIn {S : Set (LabelledTuple n)} {P Q : LabelledTuple n}
    (hP : P ∈ S) (h : PolygonalJoin S P Q) : JoinedIn S P Q := by
  induction h with
  | refl => exact JoinedIn.refl hP
  | @tail b c hab hbc ih => exact ih.trans (JoinedIn.of_segment_subset hbc)

/-- A genuine visible connected-component chamber supplies a path in the
weak locus between any two of its labelled representatives. -/
theorem weak_visible_path (P Q : WeakTuple n) (hQ : Q ∈ labelledVisibleChamber P) :
    JoinedIn (weakLocus n) P.val Q.val := by
  have hPmem : P.val ∈ Subtype.val '' labelledVisibleChamber P :=
    ⟨P, mem_connectedComponent, rfl⟩
  have hQmem : Q.val ∈ Subtype.val '' labelledVisibleChamber P := ⟨Q, hQ, rfl⟩
  have hpoly := (weak_visible_components P).2 P.val hPmem Q.val hQmem
  exact (polygonalJoin_joinedIn hPmem hpoly).mono (by
    rintro R ⟨W, hW, rfl⟩
    exact W.property)

/-- Generic tree values agree on an actual visible chamber, with the same
physical root. The path and all silent-event response premises are derived. -/
theorem tree_coefficient_visible_chamber (hn : 3 ≤ n) (P Q : GenericTuple n)
    (g : ZMod n)
    (hQ : (⟨Q.val, generic_implies_weak hn Q.property⟩ : WeakTuple n) ∈
      labelledVisibleChamber ⟨P.val, generic_implies_weak hn P.property⟩) :
    treeCoefficient P.val P.property.1 g hn = treeCoefficient Q.val Q.property.1 g hn := by
  have hj := weak_visible_path ⟨P.val, generic_implies_weak hn P.property⟩
    ⟨Q.val, generic_implies_weak hn Q.property⟩ hQ
  let γ := hj.somePath
  have hfirst : Generic (γ 0) := by rw [γ.source]; exact P.property
  have hlast : Generic (γ 1) := by rw [γ.target]; exact Q.property
  have he := tree_coefficient_eq_along_weak_path hn γ γ.continuous
    (fun t => hj.somePath_mem t) hfirst hlast g
  have htuple0 : (⟨γ 0, hfirst⟩ : GenericTuple n) = P := Subtype.ext γ.source
  have htuple1 : (⟨γ 1, hlast⟩ : GenericTuple n) = Q := Subtype.ext γ.target
  have hc0 := congrArg (fun R : GenericTuple n => treeCoefficient R.val R.property.1 g hn) htuple0
  have hc1 := congrArg (fun R : GenericTuple n => treeCoefficient R.val R.property.1 g hn) htuple1
  exact hc0.symm.trans (he.trans hc1)

/-- Density in the actual open ambient component supplies a generic point
in every visible chamber, including chambers based at simultaneous silent zeros. -/
theorem visible_chamber_has_generic (hn : 3 ≤ n) (P : WeakTuple n) :
    ∃ Q : WeakTuple n, Q ∈ labelledVisibleChamber P ∧ Generic Q.val := by
  obtain ⟨Q, hQ, hG⟩ := generic_in_nonempty_open hn
    (Subtype.val '' labelledVisibleChamber P) (weak_visible_components P).1
    ⟨P.val, P, mem_connectedComponent, rfl⟩
  obtain ⟨R, hR, hRQ⟩ := hQ
  exact ⟨R, hR, by rw [hRQ]; exact hG⟩

/-- Source thm:A-continuation: the unique integer-valued continuation on the
whole weak locus, constant on actual visible connected-component chambers
and equal to the original tree formula on every generic tuple. The root is
fixed throughout; no formula is evaluated at a vanishing gate. -/
theorem A_continuation (hn : 3 ≤ n) (g : ZMod n) :
    ∃! F : WeakTuple n → ℤ,
      (∀ P Q : WeakTuple n, Q ∈ labelledVisibleChamber P → F Q = F P) ∧
      (∀ P : GenericTuple n,
        F ⟨P.val, generic_implies_weak hn P.property⟩ = treeCoefficient P.val P.property.1 g hn) := by
  classical
  choose pick hpick hgeneric using (fun P : WeakTuple n => visible_chamber_has_generic hn P)
  let F : WeakTuple n → ℤ := fun P => treeCoefficient (pick P).val (hgeneric P).1 g hn
  have hcommon : ∀ (P R : WeakTuple n), R ∈ labelledVisibleChamber P →
      ∀ hR : Generic R.val, F P = treeCoefficient R.val hR.1 g hn := by
    intro P R hRP hR
    have hmem : R ∈ labelledVisibleChamber (pick P) := by
      change R ∈ connectedComponent (pick P)
      rw [← connectedComponent_eq (hpick P)]
      exact hRP
    exact tree_coefficient_visible_chamber hn ⟨(pick P).val, hgeneric P⟩ ⟨R.val, hR⟩ g hmem
  have hconstant : ∀ P Q : WeakTuple n, Q ∈ labelledVisibleChamber P → F Q = F P := by
    intro P Q hQP
    have hmem : pick Q ∈ labelledVisibleChamber P := by
      change pick Q ∈ connectedComponent P
      rw [connectedComponent_eq hQP]
      exact hpick Q
    exact (hcommon P (pick Q) hmem (hgeneric Q)).symm
  have hagree : ∀ P : GenericTuple n,
      F ⟨P.val, generic_implies_weak hn P.property⟩ = treeCoefficient P.val P.property.1 g hn := by
    intro P
    exact hcommon ⟨P.val, generic_implies_weak hn P.property⟩
      ⟨P.val, generic_implies_weak hn P.property⟩ mem_connectedComponent P.property
  refine ⟨F, ⟨hconstant, hagree⟩, ?_⟩
  intro G hG
  funext P
  calc
    G P = G (pick P) := (hG.1 P (pick P) (hpick P)).symm
    _ = treeCoefficient (pick P).val (hgeneric P).1 g hn := hG.2 ⟨(pick P).val, hgeneric P⟩
    _ = F P := rfl

end
end SM
