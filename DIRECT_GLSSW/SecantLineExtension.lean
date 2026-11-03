import FiniteAffineLineAvoidance

set_option autoImplicit false
namespace DirectGLSSW.SecantLineExtension
open FiniteAffineLineAvoidance
noncomputable section
attribute [local instance] Classical.propDecidable
abbrev Point := PlanarPoint ℝ

def rootOffset (u A B : Point) : ℝ :=
  -planarDet (A-B) (u-B) / planarDet (A-B) (1,0)
def baselineRoot (u A B : Point) : Point := u + (rootOffset u A B,0)

theorem baselineRoot_height (u A B : Point) (hu : u.2=0) :
    (baselineRoot u A B).2=0 := by simp [baselineRoot,hu]

theorem baselineRoot_on_carrier (u A B : Point)
    (h : planarDet (A-B) (1,0) ≠ 0) :
    planarDet (A-B) (baselineRoot u A B-B)=0 := by
  have he : planarDet (A-B) (baselineRoot u A B-B) =
      planarDet (A-B) (u-B) + rootOffset u A B * planarDet (A-B) (1,0) := by
    dsimp [baselineRoot,planarDet]; ring
  rw [he,rootOffset,div_mul_cancel₀ _ h]
  ring

theorem rootOffset_swap (u A B : Point) : rootOffset u A B = rootOffset u B A := by
  have hnum : planarDet (A-B) (u-B) = -planarDet (B-A) (u-A) := by
    dsimp [planarDet]; ring
  have hden : planarDet (A-B) (1,0) = -planarDet (B-A) (1,0) := by
    dsimp [planarDet]; ring
  simp only [rootOffset,hnum,hden,neg_neg,div_neg_eq_neg_div,neg_div]

theorem rootOffset_ne_of_avoidance (u A X C D : Point)
    (hXA : planarDet (X-A) (1,0) ≠ 0)
    (havoid : planarDet (baselineRoot u C D-A) (X-A) ≠ 0) :
    rootOffset u X A ≠ rootOffset u C D := by
  intro heq
  have hon := baselineRoot_on_carrier u X A hXA
  have hr : baselineRoot u X A = baselineRoot u C D := by
    simp only [baselineRoot,heq]
  rw [hr] at hon
  apply havoid
  calc
    planarDet (baselineRoot u C D-A) (X-A) =
      -planarDet (X-A) (baselineRoot u C D-A) := by dsimp [planarDet]; ring
    _ = 0 := by rw [hon]; ring

/-- One new vertex, close to an arbitrary target, with the finite exclusions needed
for G1, disjoint interior secant intercepts, and the final endpoint directions. -/
theorem exists_next_vertex {m : ℕ} (hm : 2 ≤ m) (R : Fin m → Point)
    (hinj : Function.Injective R)
    (hU : (R ⟨0,by omega⟩).2=0) (hV : (R ⟨1,by omega⟩).2=0)
    (hoff : ∀ i : Fin m, 2 ≤ i.val → (R i).2 ≠ 0)
    (p : Point) (η : ℝ) (hη : 0<η) :
    ∃ X : Point, |X.1-p.1|<η ∧ |X.2-p.2|<η ∧ X.2≠0 ∧
      (∀ i, X ≠ R i) ∧
      (∀ a b : Fin m, a≠b → planarDet (R b-R a) (X-R a) ≠ 0) ∧
      (∀ a b c : Fin m, 2≤a.val → 2≤b.val → 2≤c.val →
        planarDet (R a-R b) (1,0) ≠ 0 →
        planarDet (baselineRoot (R ⟨0,by omega⟩) (R a) (R b)-R c) (X-R c) ≠ 0) ∧
      (∀ a : Fin m, 2≤a.val →
        planarDet (R a-R ⟨0,by omega⟩) (X-R ⟨1,by omega⟩) ≠ 0) := by
  let u : Fin m := ⟨0,by omega⟩
  let v : Fin m := ⟨1,by omega⟩
  let pairLines : Finset (Point×Point) :=
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun z => z.1≠z.2)).image
      (fun z => (R z.1,R z.2))
  let rootLines : Finset (Point×Point) :=
    ((Finset.univ : Finset (Fin m × Fin m × Fin m)).filter
      (fun z => 2≤z.1.val ∧ 2≤z.2.1.val ∧ 2≤z.2.2.val ∧
        planarDet (R z.1-R z.2.1) (1,0)≠0)).image
      (fun z => (R z.2.2,baselineRoot (R u) (R z.1) (R z.2.1)))
  let outerLines : Finset (Point×Point) :=
    ((Finset.univ : Finset (Fin m)).filter (fun a => 2≤a.val)).image
      (fun a => (R v,R v+(R a-R u)))
  have hpairs : ∀ l∈pairLines, l.1≠l.2 := by
    intro l hl
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp hl
    exact fun he => (Finset.mem_filter.mp hab).2 (hinj he)
  have hroots : ∀ l∈rootLines, l.1≠l.2 := by
    intro l hl
    obtain ⟨⟨a,b,c⟩,hab,rfl⟩ := Finset.mem_image.mp hl
    have hc := (Finset.mem_filter.mp hab).2.2.2.1
    intro he
    have hy := congrArg Prod.snd he
    have hr := baselineRoot_height (R u) (R a) (R b) hU
    exact hoff c hc (hy.trans hr)
  have houters : ∀ l∈outerLines, l.1≠l.2 := by
    intro l hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    intro he
    have hr : R a=R u := by
      apply Prod.ext
      · have hh := congrArg Prod.fst he; dsimp at hh; linarith
      · have hh := congrArg Prod.snd he; dsimp at hh; linarith
    have hai := congrArg Fin.val (hinj hr)
    have ha2 := (Finset.mem_filter.mp ha).2
    dsimp [u] at hai
    omega
  obtain ⟨X,hx,hy,havoid⟩ := exists_near_avoiding_finite_lines
    (pairLines ∪ rootLines ∪ outerLines) (by
      intro l hl
      rcases Finset.mem_union.mp hl with hl|hl
      · rcases Finset.mem_union.mp hl with hl|hl
        · exact hpairs l hl
        · exact hroots l hl
      · exact houters l hl) p η hη
  have hpair : ∀ a b : Fin m, a≠b → planarDet (R b-R a) (X-R a)≠0 := by
    intro a b hab
    apply havoid (R a,R b)
    apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(a,b),by simp [hab],rfl⟩
  have huv : u≠v := by intro he; have := congrArg Fin.val he; simp [u,v] at this
  have hXy : X.2≠0 := by
    intro he
    have h := hpair u v huv
    apply h
    dsimp [planarDet]
    rw [hU,hV,he]
    ring
  refine ⟨X,hx,hy,hXy,?_,hpair,?_,?_⟩
  · intro i he
    by_cases hi : i=u
    · have hh := hpair u v huv
      apply hh
      rw [he,hi,sub_self]
      simp [planarDet]
    · have hh := hpair u i (Ne.symm hi)
      apply hh
      rw [he]
      simp [planarDet]
      ring
  · intro a b c ha hb hc hab
    apply havoid (R c,baselineRoot (R u) (R a) (R b))
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(a,b,c),by simp [ha,hb,hc,hab],rfl⟩
  · intro a ha
    have hh := havoid (R v,R v+(R a-R u)) (by
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨a,by simp [ha],rfl⟩)
    simpa only [add_sub_cancel_left] using hh








end
end DirectGLSSW.SecantLineExtension
