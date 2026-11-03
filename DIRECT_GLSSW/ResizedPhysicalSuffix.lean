import PhysicalSuffixCursor
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
attribute [local instance] Classical.propDecidable

/-- Literal suffix with the arithmetic length equality made explicit; no edge
is added and every retained vertex is a vertex of the supplied open arc. -/
def suffixWord {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (a b : ℕ) (hs : a+b=n) :
    Fin (b+2) → PlanarPoint ℝ :=
  suffix (a:=a) (b:=b) (fun i => q (Fin.cast (congrArg (fun k=>k+2) hs) i))

theorem suffixWord_vertex {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)
    (a b : ℕ) (hs : a+b=n) (i : Fin (b+2)) :
    suffixWord q a b hs i = q ⟨a+i.val,by omega⟩ := rfl

def suffixWordCrossingEquiv {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (a b : ℕ) (hs : a+b=n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    Crossing (Cursor.moveStart (suffixWord q a b hs) θ) ≃
      {d : Crossing q // a ≤ d.val.1.val ∧ (d.val.1.val = a → θ < leftParameter q d)} := by
  subst n
  exact suffixCursorCrossingEquiv q hR θ h0 h1

theorem suffixWord_moveStart_regular {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
    (a b : ℕ) (hs : a+b=n) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1)
    (havoid : ∀ d : Crossing q, d.val.1.val = a → leftParameter q d ≠ θ) :
    Regular (Cursor.moveStart (suffixWord q a b hs) θ) := by
  subst n
  exact suffix_moveStart_regular q hR θ h0 h1 havoid

end DirectGLSSW.ActiveArc.Split
