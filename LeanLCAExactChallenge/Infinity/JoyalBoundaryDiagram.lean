import LeanLCAExactChallenge.Infinity.JoinBoundaryHornCorner
import LeanLCAExactChallenge.Infinity.JoyalDiagramSlices

/-! # Boundary diagram restriction left fibrations -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Simplicial

/-- Inner anodyneness of the normalized boundary–left-horn corners implies that restriction along the boundary is a left fibration. -/
theorem diagramUnderRestriction_boundary_leftFibration_of_normalized_corners
    (Q : SSet.{u}) [SSet.Quasicategory Q] (m : ℕ)
    (a : (Δ[m + 1] : SSet.{u}) ⟶ Q)
    (hcorners : ∀ (s : ℕ) (i : Fin (s + 2)),
      i < Fin.last (s + 1) →
        SSet.innerAnodyneExtensions
          (normalizedJoinBoundaryHornCornerMap.{u} m s i)) :
    LeftFibration
      (diagramUnderRestriction (SSet.boundary (m + 1)).ι a) := by
  apply diagramUnderRestriction_leftFibration_of_innerAnodyne_corners
  intro s i hi
  have h := hcorners s i hi
  change SSet.innerAnodyneExtensions
    (joinBoundaryHornCornerMap (m + 1) (s + 1) i)
  unfold normalizedJoinBoundaryHornCornerMap
    joinBoundaryHornStandardCornerMap at h
  rw [Category.assoc] at h
  exact (SSet.innerAnodyneExtensions.cancel_right_of_respectsIso
    (joinBoundaryHornCornerMap (m + 1) (s + 1) i)
    ((simplicialJoinStdSimplexIsoNat (m + 1) (s + 1)).hom ≫
      (leftJoinTargetIso m (s + 1)).inv)).mp h

end LeanLCAExactChallenge.Infinity
