namespace SM.OrderedBoundaryTransport

noncomputable section

universe u
variable {n m : ℕ}

/-- Map both actual endpoints through an arbitrary increasing embedding. -/
def interval (e : Fin n ↪o Fin m) (I : BoundaryInterval n) : BoundaryInterval m where
  left := e I.left
  right := e I.right
  increasing := e.strictMono I.increasing

@[simp] theorem interval_left (e : Fin n ↪o Fin m) (I : BoundaryInterval n) :
    (interval e I).left = e I.left := rfl

@[simp] theorem interval_right (e : Fin n ↪o Fin m) (I : BoundaryInterval n) :
    (interval e I).right = e I.right := rfl

theorem interval_injective (e : Fin n ↪o Fin m) : Function.Injective (interval e) := by
  intro I J h
  cases I with
  | mk l r hi =>
    cases J with
    | mk l' r' hj =>
      have hl : l = l' := e.injective (congrArg BoundaryInterval.left h)
      have hr : r = r' := e.injective (congrArg BoundaryInterval.right h)
      cases hl
      cases hr
      rfl

/-- Map all three positions, preserving their strict order. -/
def triple (e : Fin n ↪o Fin m) (T : IncreasingBoundaryTriple n) :
    IncreasingBoundaryTriple m where
  lower := e T.lower
  middle := e T.middle
  upper := e T.upper
  lower_middle := e.strictMono T.lower_middle
  middle_upper := e.strictMono T.middle_upper

theorem triple_positions (e : Fin n ↪o Fin m) (T : IncreasingBoundaryTriple n) :
    (triple e T).lower = e T.lower ∧
    (triple e T).middle = e T.middle ∧
    (triple e T).upper = e T.upper := ⟨rfl, rfl, rfl⟩

theorem triple_injective (e : Fin n ↪o Fin m) : Function.Injective (triple e) := by
  intro T U h
  cases T with
  | mk l c r hl hc =>
    cases U with
    | mk l' c' r' hl' hc' =>
      have he₁ : l = l' := e.injective (congrArg IncreasingBoundaryTriple.lower h)
      have he₂ : c = c' := e.injective (congrArg IncreasingBoundaryTriple.middle h)
      have he₃ : r = r' := e.injective (congrArg IncreasingBoundaryTriple.upper h)
      cases he₁
      cases he₂
      cases he₃
      rfl

/-- Directly map the cuts, retaining the exact part count and all indices.
This is not a claim that every composition of the image interval is obtained. -/
def composition (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) : IntervalComposition (interval e I) where
  parts := π.parts
  parts_pos := π.parts_pos
  cut := fun k => e (π.cut k)
  strict := e.strictMono.comp π.strict
  first := congrArg e π.first
  last := congrArg e π.last

@[simp] theorem composition_parts (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) : (composition e π).parts = π.parts := rfl

@[simp] theorem composition_cut (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (k : Fin (π.parts + 1)) :
    (composition e π).cut k = e (π.cut k) := rfl

theorem composition_endpoints (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) :
    (composition e π).cut 0 = e I.left ∧
    (composition e π).cut (Fin.last π.parts) = e I.right :=
  ⟨congrArg e π.first, congrArg e π.last⟩

@[simp] theorem composition_part (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (k : Fin π.parts) :
    (composition e π).part k = interval e (π.part k) := rfl

@[simp] theorem composition_nearTriple (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    (composition e π).nearTriple k = triple e (π.nearTriple k) := rfl

@[simp] theorem composition_farTriple (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (k : Fin (π.parts - 1)) :
    (composition e π).farTriple k = triple e (π.farTriple k) := rfl

/-- The image of the complete cut set, including both endpoints. -/
def cutSet (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (S : BoundaryCutSet I) : BoundaryCutSet (interval e I) where
  cuts := S.cuts.image e
  left_mem := Finset.mem_image.mpr ⟨I.left, S.left_mem, rfl⟩
  right_mem := Finset.mem_image.mpr ⟨I.right, S.right_mem, rfl⟩
  bounds := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨e.monotone (S.bounds x hx).1, e.monotone (S.bounds x hx).2⟩

@[simp] theorem cutSet_cuts (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (S : BoundaryCutSet I) : (cutSet e S).cuts = S.cuts.image e := rfl

theorem cutSet_injective (e : Fin n ↪o Fin m) {I : BoundaryInterval n} :
    Function.Injective (cutSet e (I := I)) := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  intro S T h
  apply BoundaryCutSet.ext
  apply Finset.image_injective e.injective
  exact congrArg BoundaryCutSet.cuts h

/-- Direct cut transport agrees with the actual complete finite cut set. -/
@[simp] theorem composition_cutSet (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) : (composition e π).cutSet = cutSet e π.cutSet := by
  letI : NeZero m := ⟨by have := (e I.left).isLt; omega⟩
  apply BoundaryCutSet.ext
  change Finset.univ.image (fun k => e (π.cut k)) =
    (Finset.univ.image π.cut).image e
  rw [Finset.image_image]
  rfl

theorem composition_injective (e : Fin n ↪o Fin m) {I : BoundaryInterval n} :
    Function.Injective (composition e (I := I)) := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  intro π ρ h
  apply IntervalComposition.cutSet_injective
  apply cutSet_injective e
  have hs := congrArg IntervalComposition.cutSet h
  simpa only [composition_cutSet] using hs

/-- Sorting the image cut set recovers the directly mapped composition. -/
theorem cutSet_toComposition (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (S : BoundaryCutSet I) :
    letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
    letI : NeZero m := ⟨by have := (e I.left).isLt; omega⟩
    (cutSet e S).toComposition = composition e S.toComposition := by
  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩
  letI : NeZero m := ⟨by have := (e I.left).isLt; omega⟩
  change (cutSet e S).toComposition = composition e S.toComposition
  apply IntervalComposition.cutSet_injective
  rw [BoundaryCutSet.toComposition_cutSet, composition_cutSet,
    BoundaryCutSet.toComposition_cutSet]

variable {R : Type u}

def pullbackTripleArray (e : Fin n ↪o Fin m) (D : TripleArray m R) : TripleArray n R :=
  fun T => D (triple e T)

def pullbackIntervalArray (e : Fin n ↪o Fin m) (X : IntervalArray m R) : IntervalArray n R :=
  fun I => X (interval e I)

variable [CommRing R] [Invertible (2 : R)]

/-- Exact weight transport, with arbitrary arrays and no nonzero factors. -/
theorem nearFarWeight_pullback (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (D H : TripleArray m R) :
    (composition e π).nearFarWeight D H =
      π.nearFarWeight (pullbackTripleArray e D) (pullbackTripleArray e H) := by
  rfl

/-- Only the actual near/far factors of this composition need agree. -/
theorem nearFarWeight_transport (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (D₀ H₀ : TripleArray n R) (D₁ H₁ : TripleArray m R)
    (hD : ∀ k : Fin (π.parts - 1), D₁ (triple e (π.nearTriple k)) = D₀ (π.nearTriple k))
    (hH : ∀ k : Fin (π.parts - 1), H₁ (triple e (π.farTriple k)) = H₀ (π.farTriple k)) :
    (composition e π).nearFarWeight D₁ H₁ = π.nearFarWeight D₀ H₀ := by
  change (∏ k : Fin (π.parts - 1),
    (D₁ (triple e (π.nearTriple k)) - H₁ (triple e (π.farTriple k))) * ⅟ (2 : R)) =
      ∏ k : Fin (π.parts - 1), (D₀ (π.nearTriple k) - H₀ (π.farTriple k)) * ⅟ (2 : R)
  apply Finset.prod_congr rfl
  intro k hk
  rw [hD k, hH k]

/-- The child product uses the actual mapped child intervals. -/
theorem childProduct_transport (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (X₀ : IntervalArray n R) (X₁ : IntervalArray m R)
    (hX : ∀ k : Fin π.parts, X₁ (interval e (π.part k)) = X₀ (π.part k)) :
    (∏ k : Fin (composition e π).parts, X₁ ((composition e π).part k)) =
      ∏ k : Fin π.parts, X₀ (π.part k) := by
  change (∏ k : Fin π.parts, X₁ (interval e (π.part k))) =
    ∏ k : Fin π.parts, X₀ (π.part k)
  apply Finset.prod_congr rfl
  intro k hk
  exact hX k

/-- The complete raw transform summand, including its entire child product.
Unary weights remain empty products, and zero factors need not be cancelled. -/
theorem summand_transport (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (D₀ H₀ : TripleArray n R) (D₁ H₁ : TripleArray m R)
    (X₀ : IntervalArray n R) (X₁ : IntervalArray m R)
    (hD : ∀ k : Fin (π.parts - 1), D₁ (triple e (π.nearTriple k)) = D₀ (π.nearTriple k))
    (hH : ∀ k : Fin (π.parts - 1), H₁ (triple e (π.farTriple k)) = H₀ (π.farTriple k))
    (hX : ∀ k : Fin π.parts, X₁ (interval e (π.part k)) = X₀ (π.part k)) :
    (composition e π).nearFarWeight D₁ H₁ *
        (∏ k : Fin (composition e π).parts, X₁ ((composition e π).part k)) =
      π.nearFarWeight D₀ H₀ * ∏ k : Fin π.parts, X₀ (π.part k) := by
  rw [nearFarWeight_transport e π D₀ H₀ D₁ H₁ hD hH,
    childProduct_transport e π X₀ X₁ hX]

/-- Unconditional formulation using the exact pointwise pullback arrays. -/
theorem summand_pullback (e : Fin n ↪o Fin m) {I : BoundaryInterval n}
    (π : IntervalComposition I) (D H : TripleArray m R) (X : IntervalArray m R) :
    (composition e π).nearFarWeight D H *
        (∏ k : Fin (composition e π).parts, X ((composition e π).part k)) =
      π.nearFarWeight (pullbackTripleArray e D) (pullbackTripleArray e H) *
        ∏ k : Fin π.parts, pullbackIntervalArray e X (π.part k) := by
  apply summand_transport e π
  · intro k
    rfl
  · intro k
    rfl
  · intro k
    rfl

end

end SM.OrderedBoundaryTransport
