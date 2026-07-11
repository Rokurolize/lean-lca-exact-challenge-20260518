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
  MonoidalCategory.ExternalProduct MonoidalCategory Prod

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

private theorem pointJoinRightInclusion_naturality
    {Y Y' : SSet.{u}} (g : Y ⟶ Y') :
    g ≫ simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Y' =
      simplicialJoinRightInclusion (Δ[0] : SSet.{u}) Y ≫
        simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) g := by
  apply NatTrans.ext
  funext U
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj Y
  let G' := emptyAugmentation.{u}.obj Y'
  letI := augmentedDayConvolution F G
  letI := augmentedDayConvolution F G'
  letI : Unique (F.obj (Opposite.op WithInitial.star)) :=
    (Limits.Types.isTerminalEquivUnique _)
      (emptyAugmentationStarIsTerminal (Δ[0] : SSet.{u}))
  let s : G.obj (AugmentedSimplexCategory.inclusion.op.obj U) ⟶
      (F ⊠ G).obj (Opposite.op WithInitial.star,
        AugmentedSimplexCategory.inclusion.op.obj U) :=
    ConcreteCategory.ofHom (TypeCat.Fun.mk (fun y ↦ (default, y)))
  let s' : G'.obj (AugmentedSimplexCategory.inclusion.op.obj U) ⟶
      (F ⊠ G').obj (Opposite.op WithInitial.star,
        AugmentedSimplexCategory.inclusion.op.obj U) :=
    ConcreteCategory.ofHom (TypeCat.Fun.mk (fun y ↦ (default, y)))
  change (emptyAugmentation.map g).app
      (AugmentedSimplexCategory.inclusion.op.obj U) ≫ s' ≫
      (CategoryTheory.MonoidalCategory.DayConvolution.unit F G').app
        (Opposite.op WithInitial.star, AugmentedSimplexCategory.inclusion.op.obj U) =
    s ≫ (CategoryTheory.MonoidalCategory.DayConvolution.unit F G).app
        (Opposite.op WithInitial.star, AugmentedSimplexCategory.inclusion.op.obj U) ≫
      (CategoryTheory.MonoidalCategory.DayConvolution.map
        (emptyAugmentation.map (𝟙 (Δ[0] : SSet.{u})))
        (emptyAugmentation.map g)).app _
  rw [emptyAugmentation.map_id]
  change _ = s ≫
    (CategoryTheory.MonoidalCategory.DayConvolution.unit F G).app
      (Opposite.op WithInitial.star, AugmentedSimplexCategory.inclusion.op.obj U) ≫
    (CategoryTheory.MonoidalCategory.DayConvolution.map
      (𝟙 F) (emptyAugmentation.map g)).app
        (Opposite.op WithInitial.star ⊗ AugmentedSimplexCategory.inclusion.op.obj U)
  rw [CategoryTheory.MonoidalCategory.DayConvolution.unit_app_map_app]
  have hpref : (emptyAugmentation.map g).app
        (AugmentedSimplexCategory.inclusion.op.obj U) ≫ s' =
      s ≫ (NatTrans.app (𝟙 F) (Opposite.op WithInitial.star) ⊗ₘ
        (emptyAugmentation.map g).app
          (AugmentedSimplexCategory.inclusion.op.obj U)) := by
    apply ConcreteCategory.hom_ext
    intro y
    rfl
  rw [← Category.assoc, hpref]
  exact Category.assoc _ _ _

/-- Restricting the fixed-base transpose of a slice simplex to its right factor
is composition with the under-slice projection. -/
theorem underSliceProjection_comp_eq_fixedBaseCone
    (Q : SSet.{u}) (z : Q _⦋0⦌) (K : SSet.{u})
    (f : K ⟶ underSlice Q z) :
    f ≫ underSliceProjection Q z =
      simplicialJoinRightInclusion (Δ[0] : SSet.{u}) K ≫
        forgetAugmentation.{u}.map
          ((relativeDaySliceOverMapFixedBaseEquiv
            (emptyAugmentation.{u}.obj (Δ[0] : SSet.{u}))
            (emptyAugmentation.{u}.obj Q) K
            (emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm z))) f).1 := by
  let F := emptyAugmentation.{u}.obj (Δ[0] : SSet.{u})
  let G := emptyAugmentation.{u}.obj Q
  let a := emptyAugmentation.{u}.map (SSet.yonedaEquiv.symm z)
  have ht := relativeDaySliceOverMapFixedBaseEquiv_precomp_fst
    F G a f (𝟙 (underSlice Q z))
  simp only [Category.comp_id] at ht
  dsimp only [F, G, a] at ht ⊢
  unfold underSliceProjection underSliceUniversalCone
  rw [ht]
  rw [← Category.assoc, pointJoinRightInclusion_naturality, Category.assoc]
  let T := (augmentedDayTensorLeft
    (emptyAugmentation.obj (Δ[0] : SSet.{u}))).map (emptyAugmentation.map f)
  let V := ((relativeDaySliceOverMapFixedBaseEquiv
      (emptyAugmentation.obj (Δ[0] : SSet.{u})) (emptyAugmentation.obj Q)
      (underSlice Q z) (emptyAugmentation.map (SSet.yonedaEquiv.symm z)))
        (𝟙 (underSlice Q z))).1
  have hc := (forgetAugmentation.{u}).map_comp T V
  have hT : forgetAugmentation.map T =
      simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) f := by
    unfold T simplicialJoinMap augmentedDayTensorLeft
    rw [emptyAugmentation.map_id]
    rfl
  change _ = simplicialJoinRightInclusion (Δ[0] : SSet.{u}) K ≫
    forgetAugmentation.map (T ≫ V)
  calc
    _ = simplicialJoinRightInclusion (Δ[0] : SSet.{u}) K ≫
        (simplicialJoinMap (𝟙 (Δ[0] : SSet.{u})) f ≫
          forgetAugmentation.map V) := Category.assoc _ _ _
    _ = simplicialJoinRightInclusion (Δ[0] : SSet.{u}) K ≫
        (forgetAugmentation.map T ≫ forgetAugmentation.map V) :=
      congrArg (fun k ↦ simplicialJoinRightInclusion
        (Δ[0] : SSet.{u}) K ≫ k)
        (congrArg (fun k ↦ k ≫ forgetAugmentation.map V) hT.symm)
    _ = _ := congrArg (fun k ↦ simplicialJoinRightInclusion
      (Δ[0] : SSet.{u}) K ≫ k) hc.symm

/-- The representable over-slice, obtained by reversing an under-slice. -/
abbrev overSlice (Q : SSet.{u}) (z : Q _⦋0⦌) : SSet.{u} :=
  (underSlice Q.op z).op

/-- Forget the fixed final vertex of an over-slice simplex. -/
def overSliceProjection (Q : SSet.{u}) (z : Q _⦋0⦌) :
    overSlice Q z ⟶ Q :=
  SSet.opFunctor.map (underSliceProjection Q.op z) ≫
    (SSet.opFunctorCompOpFunctorIso.app Q).hom

end LeanLCAExactChallenge.Infinity
