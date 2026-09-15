import SM.GeometricTransport
import SM.InterlaceSupports

/-! Actual alternating crossing visits and their graph on the geometric
record domain, with exact agreement and canonical transport. -/

namespace SM

variable {n : ℕ} {P Q : LabelledTuple n}

def geometricCrossingVisitBetween (hP : CrossingGeometry P) (x : Crossing P)
    (x₀ x₁ : {i // i ∈ x.val}) (y : Crossing P) (y₀ : {i // i ∈ y.val}) : Prop :=
  traversalBetween (geometricVisitPosition hP ⟨x, x₀⟩)
    (geometricVisitPosition hP ⟨y, y₀⟩) (geometricVisitPosition hP ⟨x, x₁⟩)

def GeometricInterlaces (hP : CrossingGeometry P) (x y : Crossing P) : Prop :=
  x ≠ y ∧ ∃ x₀ x₁ : {i // i ∈ x.val}, ∃ y₀ y₁ : {i // i ∈ y.val},
    x₀ ≠ x₁ ∧ y₀ ≠ y₁ ∧
    geometricCrossingVisitBetween hP x x₀ x₁ y y₀ ∧
    geometricCrossingVisitBetween hP x x₁ x₀ y y₁

theorem geometricInterlaces_irrefl (hP : CrossingGeometry P) (x : Crossing P) :
    ¬ GeometricInterlaces hP x x := fun h => h.1 rfl

theorem geometricInterlaces_symm (hP : CrossingGeometry P) {x y : Crossing P}
    (h : GeometricInterlaces hP x y) : GeometricInterlaces hP y x := by
  rcases h with ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀, h₁⟩
  obtain ⟨h₂, h₃⟩ := traversalAlternating_rotate h₀ h₁
  exact ⟨hxy.symm, y₀, y₁, x₁, x₀, hy, hx.symm, h₂, h₃⟩

def geometricInterlacementGraph (hP : CrossingGeometry P) : SimpleGraph (Crossing P) where
  Adj := GeometricInterlaces hP
  symm := ⟨fun _ _ h => geometricInterlaces_symm hP h⟩
  loopless := ⟨geometricInterlaces_irrefl hP⟩

theorem geometricInterlaces_iff_generic (hn : 3 ≤ n) (hP : Generic P)
    (h : CrossingGeometry P) (x y : Crossing P) :
    GeometricInterlaces h x y ↔ Interlaces hn hP x y := Iff.rfl

theorem geometricInterlacementGraph_eq_generic (hn : 3 ≤ n) (hP : Generic P)
    (h : CrossingGeometry P) : geometricInterlacementGraph h = interlacementGraph hn hP := rfl

theorem geometric_visitBetween_transport [NeZero n] (hP : CrossingGeometry P)
    (hQ : CrossingGeometry Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : CrossingParameterOrderAgrees P Q) (v w u : Visit P) :
    traversalBetween (geometricVisitPosition hP v) (geometricVisitPosition hP w)
      (geometricVisitPosition hP u) ↔
    traversalBetween (geometricVisitPosition hQ (visitTransport hs v))
      (geometricVisitPosition hQ (visitTransport hs w))
      (geometricVisitPosition hQ (visitTransport hs u)) := by
  exact or_congr
    (and_congr (geometric_visitKey_lt_transport hP hQ hs ho v w)
      (geometric_visitKey_lt_transport hP hQ hs ho w u))
    (or_congr
      (and_congr (geometric_visitKey_lt_transport hP hQ hs ho w u)
        (geometric_visitKey_lt_transport hP hQ hs ho u v))
      (and_congr (geometric_visitKey_lt_transport hP hQ hs ho u v)
        (geometric_visitKey_lt_transport hP hQ hs ho v w)))

theorem geometric_crossingBetween_transport [NeZero n] (hP : CrossingGeometry P)
    (hQ : CrossingGeometry Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : CrossingParameterOrderAgrees P Q) (x : Crossing P)
    (x₀ x₁ : {i // i ∈ x.val}) (y : Crossing P) (y₀ : {i // i ∈ y.val}) :
    geometricCrossingVisitBetween hP x x₀ x₁ y y₀ ↔
      geometricCrossingVisitBetween hQ (crossingTransport hs x) x₀ x₁
        (crossingTransport hs y) y₀ :=
  geometric_visitBetween_transport hP hQ hs ho ⟨x, x₀⟩ ⟨y, y₀⟩ ⟨x, x₁⟩

theorem geometric_interlaces_transport [NeZero n] (hP : CrossingGeometry P)
    (hQ : CrossingGeometry Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : CrossingParameterOrderAgrees P Q) (x y : Crossing P) :
    GeometricInterlaces hP x y ↔
      GeometricInterlaces hQ (crossingTransport hs x) (crossingTransport hs y) := by
  constructor
  · rintro ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀, h₁⟩
    refine ⟨fun he => hxy ((crossingTransport hs).injective he),
      x₀, x₁, y₀, y₁, hx, hy, ?_, ?_⟩
    · exact (geometric_crossingBetween_transport hP hQ hs ho x x₀ x₁ y y₀).mp h₀
    · exact (geometric_crossingBetween_transport hP hQ hs ho x x₁ x₀ y y₁).mp h₁
  · rintro ⟨hxy, x₀, x₁, y₀, y₁, hx, hy, h₀, h₁⟩
    refine ⟨fun he => hxy (congrArg (crossingTransport hs) he),
      x₀, x₁, y₀, y₁, hx, hy, ?_, ?_⟩
    · exact (geometric_crossingBetween_transport hP hQ hs ho x x₀ x₁ y y₀).mpr h₀
    · exact (geometric_crossingBetween_transport hP hQ hs ho x x₁ x₀ y y₁).mpr h₁

def geometricInterlacementTransportIso [NeZero n] (hP : CrossingGeometry P)
    (hQ : CrossingGeometry Q) (hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s)
    (ho : CrossingParameterOrderAgrees P Q) :
    geometricInterlacementGraph hP ≃g geometricInterlacementGraph hQ where
  toEquiv := crossingTransport hs
  map_rel_iff' := (geometric_interlaces_transport hP hQ hs ho _ _).symm

end SM
