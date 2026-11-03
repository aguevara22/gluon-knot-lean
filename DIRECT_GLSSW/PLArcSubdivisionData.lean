import DirectGLSSW.HOMFLY.PLDiagrams
import Mathlib.GroupTheory.Perm.Basic

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY.ArcSubdivision
open Equiv
attribute [local instance] Classical.propDecidable
variable (D : PLLinkDiagram) (e : Fin D.nArc) (t : ℝ)

/-- The exact point inserted on the selected physical arc. -/
def point : PlanarPoint ℝ :=
  affinePoint (D.vertexPoint (D.arcSource e)) (D.vertexPoint (D.arcTarget e)) t

def vertexPoint : Fin (D.nVertex+1) → PlanarPoint ℝ :=
  Fin.lastCases (point D e t) D.vertexPoint

def arcSource : Fin (D.nArc+1) → Fin (D.nVertex+1) :=
  Fin.lastCases (Fin.last D.nVertex) (fun a => (D.arcSource a).castSucc)

def arcTarget : Fin (D.nArc+1) → Fin (D.nVertex+1) :=
  Fin.lastCases (D.arcTarget e).castSucc
    (fun a => if a=e then Fin.last D.nVertex else (D.arcTarget a).castSucc)

def crossingVertex (c : Fin D.nCrossing) : Fin (D.nVertex+1) := (D.crossingVertex c).castSucc

def incoming (c : Fin D.nCrossing) (i : Fin 2) : Fin (D.nArc+1) :=
  if D.incoming c i=e then Fin.last D.nArc else (D.incoming c i).castSucc

def outgoing (c : Fin D.nCrossing) (i : Fin 2) : Fin (D.nArc+1) := (D.outgoing c i).castSucc

/-- Extend the old continuation by fixing the fresh arc label. -/
def liftedContinuation : Perm (Fin (D.nArc+1)) where
  toFun := Fin.lastCases (Fin.last D.nArc) (fun a => (D.continuation a).castSucc)
  invFun := Fin.lastCases (Fin.last D.nArc) (fun a => (D.continuation.symm a).castSucc)
  left_inv a := by induction a using Fin.lastCases <;> simp
  right_inv a := by induction a using Fin.lastCases <;> simp

/-- Insert the fresh second-half arc immediately after the selected old label. -/
def continuation : Perm (Fin (D.nArc+1)) :=
  liftedContinuation D * swap e.castSucc (Fin.last D.nArc)

/-- Collapse precisely the two split labels back to the selected original arc. -/
def collapse : Fin (D.nArc+1) → Fin D.nArc := Fin.lastCases e id

@[simp] theorem vertexPoint_old (v : Fin D.nVertex) : vertexPoint D e t v.castSucc=D.vertexPoint v := by simp [vertexPoint]
@[simp] theorem vertexPoint_new : vertexPoint D e t (Fin.last D.nVertex)=point D e t := by simp [vertexPoint]
@[simp] theorem arcSource_old (a : Fin D.nArc) : arcSource D a.castSucc=(D.arcSource a).castSucc := by simp [arcSource]
@[simp] theorem arcSource_new : arcSource D (Fin.last D.nArc)=Fin.last D.nVertex := by simp [arcSource]
@[simp] theorem arcTarget_old (a : Fin D.nArc) : arcTarget D e a.castSucc=if a=e then Fin.last D.nVertex else (D.arcTarget a).castSucc := by simp [arcTarget]
@[simp] theorem arcTarget_new : arcTarget D e (Fin.last D.nArc)=(D.arcTarget e).castSucc := by simp [arcTarget]
@[simp] theorem liftedContinuation_old (a : Fin D.nArc) : liftedContinuation D a.castSucc=(D.continuation a).castSucc := by simp [liftedContinuation]
@[simp] theorem liftedContinuation_new : liftedContinuation D (Fin.last D.nArc)=Fin.last D.nArc := by simp [liftedContinuation]
@[simp] theorem collapse_old (a : Fin D.nArc) : collapse D e a.castSucc=a := by simp [collapse]
@[simp] theorem collapse_new : collapse D e (Fin.last D.nArc)=e := by simp [collapse]
end DirectGLSSW.HOMFLY.ArcSubdivision
