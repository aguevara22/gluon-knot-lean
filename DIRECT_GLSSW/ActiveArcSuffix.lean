import ActiveArcCursorCrossings

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ)

/-- The literal suffix begins at vertex a, with only its physical edges. -/
def vertex (i : Fin (b+2)) : Fin (a+b+2) := ⟨a+i.val,by omega⟩
def edge (e : Fin (b+1)) : Fin (a+b+1) := ⟨a+e.val,by omega⟩
def suffix : Fin (b+2) → PlanarPoint ℝ := fun i => q (vertex i)

theorem vertex_injective : Function.Injective (vertex (a:=a) (b:=b)) := by
  intro i j h;apply Fin.ext;have hh:=congrArg Fin.val h;dsimp [vertex] at hh;omega

theorem edge_injective : Function.Injective (edge (a:=a) (b:=b)) := by
  intro i j h;apply Fin.ext;have hh:=congrArg Fin.val h;dsimp [edge] at hh;omega

@[simp] theorem vertex_castSucc (e : Fin (b+1)) :
    vertex (a:=a) e.castSucc=(edge (a:=a) e).castSucc := rfl
@[simp] theorem vertex_succ (e : Fin (b+1)) :
    vertex (a:=a) e.succ=(edge (a:=a) e).succ := by apply Fin.ext;simp [vertex,edge,Nat.add_assoc]

theorem suffix_edgeInterior (e : Fin (b+1)) (x : PlanarPoint ℝ) :
    edgeInterior (suffix q) e x ↔ edgeInterior q (edge e) x := by
  simp only [edgeInterior,suffix,vertex_castSucc,vertex_succ]

theorem suffix_tangent (e : Fin (b+1)) :
    suffix q e.succ-suffix q e.castSucc=q (edge e).succ-q (edge e).castSucc := by
  simp only [suffix,vertex_succ,vertex_castSucc]

theorem regular_suffix (hR : Regular q) : Regular (suffix q) := by
  constructor
  · intro e;rw [suffix_tangent];exact hR.edge_nonzero _
  · intro e f hef x he hf
    rw [suffix_tangent,suffix_tangent]
    exact hR.transverse _ _ (fun h => hef (edge_injective h)) x
      ((suffix_edgeInterior q e x).mp he) ((suffix_edgeInterior q f x).mp hf)
  · intro e f g x hef hfg hge h
    exact hR.noTriple _ _ _ x (fun h => hef (edge_injective h))
      (fun h => hfg (edge_injective h)) (fun h => hge (edge_injective h))
      ⟨(suffix_edgeInterior q e x).mp h.1,(suffix_edgeInterior q f x).mp h.2.1,
        (suffix_edgeInterior q g x).mp h.2.2⟩
  · intro e i hil hir hi
    apply hR.anchor_avoid (edge e) (vertex i)
    · intro hh;apply hil;apply vertex_injective;exact hh
    · intro hh;apply hir;apply vertex_injective;exact hh.trans (vertex_succ e).symm
    · exact (suffix_edgeInterior q e (q (vertex i))).mp hi

def suffixCrossingToOriginal (d : Crossing (suffix q)) : Crossing q :=
  ⟨(edge d.val.1,edge d.val.2),by
    constructor
    · change a+d.val.1.val<a+d.val.2.val;have hh:=d.property.1;exact Nat.add_lt_add_left hh a
    · obtain ⟨x,hx,hy⟩:=d.property.2
      exact ⟨x,(suffix_edgeInterior q _ _).mp hx,(suffix_edgeInterior q _ _).mp hy⟩⟩

theorem suffixCrossingToOriginal_injective : Function.Injective (suffixCrossingToOriginal q) := by
  intro d e h;apply Subtype.ext;apply Prod.ext
  · apply edge_injective;exact congrArg (fun c : Crossing q => c.val.1) h
  · apply edge_injective;exact congrArg (fun c : Crossing q => c.val.2) h

theorem suffixCrossingToOriginal_point (hR : Regular q) (d : Crossing (suffix q)) :
    crossingPoint q (suffixCrossingToOriginal q d)=crossingPoint (suffix q) d := by
  exact crossingPoint_eq_of_mem_regular q hR _ _
    ((suffix_edgeInterior q _ _).mp (crossingPoint_mem (suffix q) d).1)
    ((suffix_edgeInterior q _ _).mp (crossingPoint_mem (suffix q) d).2)

/-- A physical suffix contains exactly the original crossings with both edge labels at least a. -/
theorem suffixCrossing_range (d : Crossing q) :
    (∃ e, suffixCrossingToOriginal q e=d) ↔ a≤d.val.1.val := by
  constructor
  · rintro ⟨e,rfl⟩;change a≤a+e.val.1.val;omega
  · intro hd
    let e : Fin (b+1) := ⟨d.val.1.val-a,by have hh:=d.val.1.isLt;omega⟩
    let f : Fin (b+1) := ⟨d.val.2.val-a,by have hh:=d.val.2.isLt;have hh':=d.property.1;omega⟩
    have he : edge e=d.val.1 := by apply Fin.ext;dsimp [edge,e];omega
    have hf : edge f=d.val.2 := by apply Fin.ext;dsimp [edge,f];have hh:=d.property.1;omega
    have hef : e<f := by change d.val.1.val-a<d.val.2.val-a;have hh:=d.property.1;omega
    let z : Crossing (suffix q) := ⟨(e,f),hef,by
      obtain ⟨x,hx,hy⟩:=d.property.2
      refine ⟨x,(suffix_edgeInterior q e x).mpr ?_,(suffix_edgeInterior q f x).mpr ?_⟩
      · rw [he];exact hx
      · rw [hf];exact hy⟩
    refine ⟨z,?_⟩;apply Subtype.ext;exact Prod.ext he hf

def suffixCrossingEquiv : Crossing (suffix q) ≃ {d : Crossing q // a≤d.val.1.val} :=
  Equiv.ofBijective (fun e => ⟨suffixCrossingToOriginal q e,by change a≤a+e.val.1.val;omega⟩) ⟨by
    intro d e h;exact suffixCrossingToOriginal_injective q (congrArg Subtype.val h),by
    intro d
    obtain ⟨e,he⟩:=(suffixCrossing_range q d.val).mpr d.property
    exact ⟨e,Subtype.ext he⟩⟩

end DirectGLSSW.ActiveArc.Split
