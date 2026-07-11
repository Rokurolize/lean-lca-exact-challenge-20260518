import LeanLCAExactChallenge.Infinity.SimplicialJoin
import LeanLCAExactChallenge.Infinity.JoyalLeftFibration

/-!
# Representable under- and over-slices
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory Opposite Simplicial

/-- The representable under-slice at a vertex. -/
abbrev underSlice (Q : SSet.{u}) (z : Q _⟦0⟦) : SSet.{u} :=
  relativeDaySliceOverMap
    (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
    (emptyAugmentation.{u}.obj Q)
    (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm z))

/-- The universal fixed-base cone represented by the under-slice. -/
def underSliceUniversalCone (Q : SSet.{u}) (z : Q _⟦0⟦) :=
  (relativeDaySliceOverMapFixedBaseEquiv
    (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
    (emptyAugmentation.{u}.obj Q) (underSlice Q z)
    (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm z))) ( 𝟙 _)

/-- Forget the fixed initial vertex of an under-slice simplex. -/
def underSliceProjection (Q : SSet.{u}) (z : Q _⟦0⟦) :
    underSlice Q z ⟶ Q :=
  simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (underSlice Q z) ≫
    forgetAugmentation.{u}.map (underSliceUniversalCone Q z).1

/-- The representable over-slice, obtained by reversing an under-slice. -/
abbrev overSlice (Q : SSet.{u}) (z : Q _⟦0⟦) : SSet.{u} :=
  (underSlice Q.op z).op

/-- Forget the fixed final vertex of an over-slice simplex. -/
def overSliceProjection (Q : SSet.{u}) (z : Q _⟦0⟦) :
    overSlice Q z ⟶ Q :=
  SSet.opFunctor.map (underSliceProjection Q.op z) ≫
    (SSet.opFunctorCompOpFunctorIso.app Q).hom

end LeanLCAExactChallenge.Infinity
