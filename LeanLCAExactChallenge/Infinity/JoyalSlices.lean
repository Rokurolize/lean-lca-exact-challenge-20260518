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
open scoped CategoryTheory.MonoidalCategory.DayConvolution

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
/-- The fixed-base Day transpose is natural under precomposition of the simplicial
right variable. -/
theorem relativeDaySliceOverMapFixedBaseEquiv_precomp_fst
    (F G : AugmentedSSet.{u}) (a : F ⟶ G) {K K' : SSet.{u}}
    (h : K' ⟶ K) (f : K ⟶ relativeDaySliceOverMap F G a) :
    ((relativeDaySliceOverMapFixedBaseEquiv F G K' a) (h ≫ f)).1 =
      (augmentedDayTensorLeft F).map (emptyAugmentation.{u}.map h) ≫
        ((relativeDaySliceOverMapFixedBaseEquiv F G K a) f).1 := by
  apply (augmentedDayHomEquiv F (emptyAugmentation.obj K') G).injective
  rw [augmentedDayHomEquiv_precomp]
  unfold relativeDaySliceOverMapFixedBaseEquiv relativeDaySliceFixedBaseEquiv
  dsimp
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  let E := AugmentedSimplexCategory.equivAugmentedSimplicialObject (C := Type u)
  apply E.functor.map_injective
  apply CommaMorphism.ext
  · change forgetAugmentation.map
        (augmentedMapOfFixedUnderlying K' _ _ _ _) =
      forgetAugmentation.map (emptyAugmentation.map h ≫
        augmentedMapOfFixedUnderlying K _ _ _ _)
    rw [forgetAugmentation_augmentedMapOfFixedUnderlying, Functor.map_comp,
      forgetAugmentation_augmentedMapOfFixedUnderlying]
    rfl
  · apply ConcreteCategory.hom_ext
    rw [Functor.map_comp]
    intro x
    have hE {A B : AugmentedSSet.{u}} (τ : A ⟶ B)
        (y : A.obj (Opposite.op WithInitial.star)) :
        ConcreteCategory.hom (E.functor.map τ).right y =
          τ.app (Opposite.op WithInitial.star) y := rfl
    have hcomp {A B C : SimplicialObject.Augmented (Type u)}
        (α : A ⟶ B) (β : B ⟶ C) (y : A.right) :
        ConcreteCategory.hom (α ≫ β).right y =
          ConcreteCategory.hom β.right (ConcreteCategory.hom α.right y) := rfl
    have hx : x = emptyAugmentationStarPoint K' := by
      apply ConcreteCategory.congr_hom
        (Limits.terminal.hom_ext
          (ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦ x)))
          (ConcreteCategory.ofHom
            (TypeCat.Fun.mk (fun _ ↦ emptyAugmentationStarPoint K'))))
    subst x
    have hp : (emptyAugmentation.map h).app (Opposite.op WithInitial.star)
        (emptyAugmentationStarPoint K') = emptyAugmentationStarPoint K := by
      let fx : (emptyAugmentation.obj K).obj (Opposite.op WithInitial.star) ⟶
          (emptyAugmentation.obj K).obj (Opposite.op WithInitial.star) :=
        ConcreteCategory.ofHom (TypeCat.Fun.mk (fun _ ↦
          (emptyAugmentation.map h).app (Opposite.op WithInitial.star)
            (emptyAugmentationStarPoint K')))
      let ft : (emptyAugmentation.obj K).obj (Opposite.op WithInitial.star) ⟶
          (emptyAugmentation.obj K).obj (Opposite.op WithInitial.star) :=
        ConcreteCategory.ofHom
          (TypeCat.Fun.mk (fun _ ↦ emptyAugmentationStarPoint K))
      exact ConcreteCategory.congr_hom
        ((emptyAugmentationStarIsTerminal K).hom_ext fx ft)
          (emptyAugmentationStarPoint K)
    exact (augmentedMapOfFixedUnderlying_star K'
      (augmentedDayInternalHom F G) (dayInternalHomStarOfMap a) _ _).trans (by
        rw [hcomp, hE, hE]
        rw [hp, augmentedMapOfFixedUnderlying_star])

/-- The representable under-slice at a vertex. -/
abbrev underSlice (Q : SSet.{u}) (z : Q _⦋0⦌) : SSet.{u} :=
  relativeDaySliceOverMap
    (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
    (emptyAugmentation.{u}.obj Q)
    (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm z))

/-- The universal fixed-base cone represented by the under-slice. -/
def underSliceUniversalCone (Q : SSet.{u}) (z : Q _⦋0⦌) :=
  (relativeDaySliceOverMapFixedBaseEquiv
    (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
    (emptyAugmentation.{u}.obj Q) (underSlice Q z)
    (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm z))) ( 𝟙 _)

/-- Forget the fixed initial vertex of an under-slice simplex. -/
def underSliceProjection (Q : SSet.{u}) (z : Q _⦋0⦌) :
    underSlice Q z ⟶ Q :=
  simplicialJoinRightInclusion (Δ[0] : SSet.{u}) (underSlice Q z) ≫
    forgetAugmentation.{u}.map (underSliceUniversalCone Q z).1

/-- The representable over-slice, obtained by reversing an under-slice. -/
abbrev overSlice (Q : SSet.{u}) (z : Q _⦋0⦌) : SSet.{u} :=
  (underSlice Q.op z).op

/-- Forget the fixed final vertex of an over-slice simplex. -/
def overSliceProjection (Q : SSet.{u}) (z : Q _⦋0⦌) :
    overSlice Q z ⟶ Q :=
  SSet.opFunctor.map (underSliceProjection Q.op z) ≫
    (SSet.opFunctorCompOpFunctorIso.app Q).hom

end LeanLCAExactChallenge.Infinity
