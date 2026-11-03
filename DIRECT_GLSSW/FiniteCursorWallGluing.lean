import GenericVirtualCursorWall
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CursorWallTransport

/-- A finite set can be avoided on both sides of any center at all sufficiently
small positive radii; the center itself is allowed in the set. -/
theorem finite_punctured_radius (S : Finset ℝ) (r : ℝ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ ε : ℝ, 0<ε → ε<δ → r-ε∉S ∧ r+ε∉S := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert x S hx ih =>
    obtain ⟨δ,hδ,hd⟩ := ih
    by_cases he : x=r
    · refine ⟨δ,hδ,?_⟩
      intro ε hε hεδ
      obtain ⟨hl,hr⟩ := hd ε hε hεδ
      constructor <;> simp only [Finset.mem_insert,not_or]
      · exact ⟨by rw [he]; linarith,hl⟩
      · exact ⟨by rw [he]; linarith,hr⟩
    · refine ⟨min δ |r-x|,lt_min hδ (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm he))),?_⟩
      intro ε hε hεδ
      obtain ⟨hl,hr⟩ := hd ε hε (lt_of_lt_of_le hεδ (min_le_left _ _))
      have hh : ε < |r-x| := lt_of_lt_of_le hεδ (min_le_right _ _)
      constructor <;> simp only [Finset.mem_insert,not_or]
      · refine ⟨?_,hl⟩
        intro heq
        have hsub : r-x=ε := by linarith
        rw [hsub,abs_of_pos hε] at hh
        exact (lt_irrefl _ hh)
      · refine ⟨?_,hr⟩
        intro heq
        have hsub : r-x= -ε := by linarith
        rw [hsub,abs_neg,abs_of_pos hε] at hh
        exact (lt_irrefl _ hh)

/-- Finite one-dimensional wall gluing.  Chamber constancy and the two-sided
wall comparisons are internal inputs, to be discharged by determinant signs
and the actual geometric event theorem.  Values at the walls are unused. -/
theorem finite_wall_gluing {α : Type*} (S : Finset ℝ) (F : ℝ → α)
    (a b : ℝ) (hab : a≤b) (ha : a∉S) (hb : b∉S)
    (hch : ∀ x y : ℝ, a≤x → x≤y → y≤b → x∉S → y∉S →
      (∀ z∈S, ¬(x<z ∧ z<y)) → F x=F y)
    (hwall : ∀ r∈S, a<r → r<b → ∃ δ : ℝ, 0<δ ∧
      ∀ ε : ℝ, 0<ε → ε<δ → F (r-ε)=F (r+ε)) : F a=F b := by
  induction S using Finset.induction_on generalizing a b with
  | empty => exact hch a b le_rfl hab le_rfl ha hb (by simp)
  | @insert r S hr ih =>
    have hsub (l u : ℝ) (hal : a≤l) (hlu : l≤u) (hub : u≤b)
        (hl : l∉insert r S) (hu : u∉insert r S)
        (hout : r≤l ∨ u≤r) : F l=F u := by
      apply ih l u hlu (fun hh => hl (Finset.mem_insert_of_mem hh))
        (fun hh => hu (Finset.mem_insert_of_mem hh))
      · intro x y hlx hxy hyu hx hy hn
        have hxr : x≠r := by
          intro heq
          rcases hout with hout | hout
          · have he : l=r := by linarith
            exact hl (by simp [he])
          · have he : u=r := by linarith
            exact hu (by simp [he])
        have hyr : y≠r := by
          intro heq
          rcases hout with hout | hout
          · have he : l=r := by linarith
            exact hl (by simp [he])
          · have he : u=r := by linarith
            exact hu (by simp [he])
        apply hch x y (le_trans hal hlx) hxy (le_trans hyu hub)
          (by simpa only [Finset.mem_insert,not_or] using And.intro hxr hx)
          (by simpa only [Finset.mem_insert,not_or] using And.intro hyr hy)
        intro z hz hzxy
        rcases Finset.mem_insert.mp hz with hz | hz
        · subst z
          rcases hout with hout | hout <;> linarith [hzxy.1,hzxy.2]
        · exact hn z hz hzxy
      · intro x hx hlx hxu
        exact hwall x (Finset.mem_insert_of_mem hx) (lt_of_le_of_lt hal hlx)
          (lt_of_lt_of_le hxu hub)
    by_cases har : a<r
    · by_cases hrb : r<b
      · obtain ⟨δ,hδ,hw⟩ := hwall r (Finset.mem_insert_self _ _) har hrb
        obtain ⟨η,hη,havoid⟩ := finite_punctured_radius S r
        let ε := min δ (min η (min (r-a) (b-r))) / 2
        have hm : 0<min δ (min η (min (r-a) (b-r))) :=
          lt_min hδ (lt_min hη (lt_min (sub_pos.mpr har) (sub_pos.mpr hrb)))
        have hε : 0<ε := half_pos hm
        have hεm : ε<min δ (min η (min (r-a) (b-r))) := half_lt_self hm
        have hεδ : ε<δ := lt_of_lt_of_le hεm (min_le_left _ _)
        have hεη : ε<η := lt_of_lt_of_le hεm (le_trans (min_le_right _ _) (min_le_left _ _))
        have hεa : ε<r-a := lt_of_lt_of_le hεm (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))
        have hεb : ε<b-r := lt_of_lt_of_le hεm (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _)))
        obtain ⟨hl,hu⟩ := havoid ε hε hεη
        have hl' : r-ε∉insert r S := by
          simp only [Finset.mem_insert,not_or]
          exact ⟨by linarith,hl⟩
        have hu' : r+ε∉insert r S := by
          simp only [Finset.mem_insert,not_or]
          exact ⟨by linarith,hu⟩
        exact (hsub a (r-ε) le_rfl (by linarith) (by linarith) ha hl'
          (Or.inr (by linarith))).trans ((hw ε hε hεδ).trans
          (hsub (r+ε) b (by linarith) (by linarith) le_rfl hu' hb (Or.inl (by linarith))))
      · exact hsub a b le_rfl hab le_rfl ha hb (Or.inr (le_of_not_gt hrb))
    · exact hsub a b le_rfl hab le_rfl ha hb (Or.inl (le_of_not_gt har))

end DirectGLSSW.CursorWallTransport
