import LeanLCAExactChallenge.Infinity.SimplicialOppositeHorns
import LeanLCAExactChallenge.Infinity.EquivalenceIntervalExtension

/-! # Equivalence edges and simplicial reversal -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Opposite Simplicial

/-- Reverse an edge when reversing a simplicial set. -/
def edgeOp {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Edge x y) : SSet.Edge (X := X.op) y x where
  edge := e.edge
  src_eq := by
    change X.op.δ 1 e.edge = y
    rw [SSet.op_δ]
    exact e.tgt_eq
  tgt_eq := by
    change X.op.δ 0 e.edge = x
    rw [SSet.op_δ]
    exact e.src_eq

@[simp]
lemma edgeOp_edge {X : SSet.{u}} {x y : X _⦋0⦌}
    (e : SSet.Edge x y) : (edgeOp e).edge = e.edge := rfl

@[simp]
lemma edgeOp_id {X : SSet.{u}} (x : X _⦋0⦌) :
    edgeOp (SSet.Edge.id x) = SSet.Edge.id (X := X.op) x := by
  apply SSet.Edge.ext
  change X.σ 0 x = X.op.σ 0 x
  rw [SSet.op_σ]
  rw [show Fin.rev (0 : Fin 1) = 0 from Fin.eq_zero _]
  rfl

/-- Reversing a composition triangle reverses the order of its two edges. -/
def compStructOp {X : SSet.{u}} {x y z : X _⦋0⦌}
    {f : SSet.Edge x y} {g : SSet.Edge y z} {h : SSet.Edge x z}
    (s : SSet.Edge.CompStruct f g h) :
    SSet.Edge.CompStruct (edgeOp g) (edgeOp f) (edgeOp h) where
  simplex := s.simplex
  d₂ := by
    change X.op.δ 2 s.simplex = g.edge
    rw [SSet.op_δ]
    exact s.d₀
  d₀ := by
    change X.op.δ 0 s.simplex = f.edge
    rw [SSet.op_δ]
    exact s.d₂
  d₁ := by
    change X.op.δ 1 s.simplex = h.edge
    rw [SSet.op_δ]
    exact s.d₁

/-- Simplicial reversal preserves equivalence edges. -/
theorem EdgeIsEquivalence.op {X : SSet.{u}} [SSet.Quasicategory X]
    {x y : X _⦋0⦌} {e : SSet.Edge x y} (he : EdgeIsEquivalence e) :
    EdgeIsEquivalence (edgeOp e) := by
  let d := Truncated.inverseTriangleDataOfEdgeIsEquivalence e he
  let g : SSet.Edge y x := SSet.Edge.ofTruncated d.inverse
  let sr : SSet.Edge.CompStruct e g (SSet.Edge.id x) :=
    SSet.Edge.CompStruct.ofTruncated d.rightTriangle
  let sl : SSet.Edge.CompStruct g e (SSet.Edge.id y) :=
    SSet.Edge.CompStruct.ofTruncated d.leftTriangle
  let gop : SSet.Edge (X := X.op) x y := edgeOp g
  let sright : SSet.Edge.CompStruct (edgeOp e) gop
      (SSet.Edge.id (X := X.op) y) := by
    simpa [gop, edgeOp_id] using compStructOp sl
  let sleft : SSet.Edge.CompStruct gop (edgeOp e)
      (SSet.Edge.id (X := X.op) x) := by
    simpa [gop, edgeOp_id] using compStructOp sr
  change IsIso (edgeHomotopyClass (edgeOp e))
  letI : IsIso (edgeHomotopyClass (edgeOp e)) :=
    ⟨⟨edgeHomotopyClass gop,
      (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
        sright.toTruncated).trans
          (SSet.Truncated.HomotopyCategory.homMk_id _),
      (SSet.Truncated.HomotopyCategory.homMk_comp_homMk
        sleft.toTruncated).trans
          (SSet.Truncated.HomotopyCategory.homMk_id _)⟩⟩
  infer_instance

end LeanLCAExactChallenge.Infinity
