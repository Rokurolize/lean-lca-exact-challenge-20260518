import LeanLCAExactChallenge.LCA.Cokernel
import LeanLCAExactChallenge.Derived.Bounded
import LeanLCAExactChallenge.Derived.BoundedFiniteProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Localization.FiniteProducts
import Mathlib.CategoryTheory.Localization.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
W266: opposite finite-limit assembly.

This file assembles the checked local pieces into the strongest currently checked
consumer for finite limits in the opposite localization.  It ports the W263
finite-coproduct support proof locally, uses W281 to transport finite coproducts
to opposite finite products, uses W283 to transport direct `WalkingParallelPairᵒᵖ`
colimit stability to opposite `WalkingParallelPair` limit stability, and feeds the
result into the W255 finite-limit transfer consumer.

It intentionally leaves the nonlocal inputs explicit: direct
`WalkingParallelPairᵒᵖ` colimit stability, the opposite functor-category
localization input, and the identity-membership input required by W255.  This is
not a product-completion claim.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe w v₁ v₂ u₁ u₂ v u

namespace CategoryTheory

open Category Limits Functor

namespace Localization

variable {J : Type w} [Category.{v} J]
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]

namespace W266HasLimitsOfShapeAux

variable (J) [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]

lemma inverts :
    (W.functorCategory J).IsInvertedBy (lim ⋙ L) :=
  fun _ _ f hf => Localization.inverts L W _ (MorphismProperty.limMap f hf)

variable [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)]

noncomputable abbrev limitFunctor :
    (J ⥤ D) ⥤ D :=
  Localization.lift _ (inverts (L := L) (W := W) J) ((whiskeringRight J C D).obj L)

noncomputable def compLimitFunctorIso :
    ((whiskeringRight J C D).obj L) ⋙ limitFunctor (L := L) (W := W) J ≅ lim ⋙ L := by
  apply Localization.fac

instance :
    CatCommSq (Functor.const J) L
      ((whiskeringRight J C D).obj L) (Functor.const J) where
  iso := (Functor.compConstIso J L).symm

noncomputable instance :
    CatCommSq lim ((whiskeringRight J C D).obj L) L
      (limitFunctor (L := L) (W := W) J) where
  iso := (compLimitFunctorIso (L := L) (W := W) J).symm

noncomputable def adj :
    Functor.const J ⊣ limitFunctor (L := L) (W := W) J :=
  constLimAdj.localization L W ((whiskeringRight J C D).obj L)
    (W.functorCategory J) (Functor.const J) (limitFunctor (L := L) (W := W) J)

end W266HasLimitsOfShapeAux

include L W in
lemma hasLimitsOfShape_of_functorCategoryLocalization_w266
    (J : Type w) [Category.{v} J]
    [HasLimitsOfShape J C] [W.IsStableUnderLimitsOfShape J]
    [((whiskeringRight J C D).obj L).IsLocalization (W.functorCategory J)] :
    HasLimitsOfShape J D :=
  hasLimitsOfShape_iff_isLeftAdjoint_const.2
    (W266HasLimitsOfShapeAux.adj (L := L) (W := W) J).isLeftAdjoint

end Localization

end CategoryTheory

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Opposite

namespace OppositeFiniteLimitAssemblyW266

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A product of opposite objects gives a coproduct of the original objects. -/
lemma hasCoproduct_unop_of_hasProduct_op {J : Type w}
    {C : Type u} [Category.{v} C] (X : J → Cᵒᵖ) [HasProduct X] :
    HasCoproduct (fun j => (X j).unop) := by
  let F : Discrete J ⥤ C := Discrete.functor (fun j => (X j).unop)
  have e : (Discrete.opposite J).symm.functor ⋙ F.op ≅ Discrete.functor X := by
    refine Discrete.natIso ?_
    intro j
    cases j
    rfl
  haveI : HasLimit ((Discrete.opposite J).symm.functor ⋙ F.op) :=
    hasLimit_of_iso e.symm
  haveI : HasLimit F.op :=
    hasLimit_of_equivalence_comp (Discrete.opposite J).symm
  exact hasColimit_of_hasLimit_op F

/-- Stability under coproducts of shape `J` transports to stability under products in `Cᵒᵖ`. -/
theorem op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape
    {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) [W.RespectsIso] {J : Type w}
    [W.IsStableUnderCoproductsOfShape J] :
    W.op.IsStableUnderProductsOfShape J := by
  refine MorphismProperty.IsStableUnderProductsOfShape.mk W.op J ?_
  intro X₁ X₂ _ _ f hf
  let Z₁ : J → C := fun j => (X₁ j).unop
  let Z₂ : J → C := fun j => (X₂ j).unop
  let g : ∀ j, Z₂ j ⟶ Z₁ j := fun j => (f j).unop
  haveI : HasCoproduct Z₁ := hasCoproduct_unop_of_hasProduct_op X₁
  haveI : HasCoproduct Z₂ := hasCoproduct_unop_of_hasProduct_op X₂
  have hg : ∀ j, W (g j) := by
    intro j
    exact hf j
  let F₂ : Discrete J ⥤ C := Discrete.functor Z₂
  let F₁ : Discrete J ⥤ C := Discrete.functor Z₁
  let η : F₂ ⟶ F₁ := Discrete.natTrans (fun i => g i.as)
  have hη : W.functorCategory (Discrete J) η := by
    intro j
    exact hg j.as
  have hSigma : W (Limits.Sigma.map g) := by
    simpa [Limits.Sigma.map, η, F₁, F₂] using
      (MorphismProperty.colimMap (W := W) (J := Discrete J) η hη)
  let eo₁ : op (∐ Z₁) ≅ ∏ᶜ X₁ := by
    simpa [Z₁] using (opCoproductIsoProduct Z₁)
  let eo₂ : op (∐ Z₂) ≅ ∏ᶜ X₂ := by
    simpa [Z₂] using (opCoproductIsoProduct Z₂)
  let e₁ : (∏ᶜ X₁).unop ≅ ∐ Z₁ := eo₁.unop
  let e₂ : (∏ᶜ X₂).unop ≅ ∐ Z₂ := eo₂.unop
  refine (W.arrow_mk_iso_iff ?_).2 hSigma
  refine Arrow.isoMk e₂ e₁ ?_
  apply Quiver.Hom.op_inj
  apply Limits.Pi.hom_ext
  intro j
  dsimp [e₁, e₂, eo₁, eo₂]
  rw [Category.assoc, opCoproductIsoProduct_hom_comp_π]
  rw [Category.assoc, Limits.Pi.map_π]
  have hπ₁ : (opCoproductIsoProduct Z₁).hom ≫ Pi.π X₁ j = (Sigma.ι Z₁ j).op := by
    simpa [Z₁] using (opCoproductIsoProduct_hom_comp_π (Z := Z₁) j)
  conv_rhs => rw [← Category.assoc, hπ₁]
  rw [← op_comp, Limits.Sigma.ι_map]
  simp [g, Z₁, Z₂]

/-- Finite-coproduct stability transports to finite-product stability of the opposite property. -/
theorem op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts
    {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) [W.RespectsIso] [W.IsStableUnderFiniteCoproducts] :
    W.op.IsStableUnderFiniteProducts where
  isStableUnderProductsOfShape J _ :=
    op_isStableUnderProductsOfShape_of_isStableUnderCoproductsOfShape W (J := J)

/--
If `W` is stable under colimits of shape `Jᵒᵖ`, then `W.op` is stable under limits of shape
`J`.  This is the direct formal transport needed for opposite equalizer-style routes.
-/
theorem op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op
    {C : Type u} [Category.{v} C]
    (W : MorphismProperty C) {J : Type w} [Category J]
    [W.IsStableUnderColimitsOfShape Jᵒᵖ] :
    W.op.IsStableUnderLimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    have hfop : W.functorCategory (Jᵒᵖ) (NatTrans.leftOp f) := by
      intro j
      simpa using hf (unop j)
    exact
      MorphismProperty.IsStableUnderColimitsOfShape.condition
        X₂.leftOp X₁.leftOp (coconeLeftOpOfCone c₂) (coconeLeftOpOfCone c₁)
        (isColimitCoconeLeftOpOfCone X₂ h₂) (isColimitCoconeLeftOpOfCone X₁ h₁)
        (NatTrans.leftOp f) hfop φ.unop (by
          intro j
          simpa only [coconeLeftOpOfCone_ι_app, NatTrans.leftOp_app] using
            congrArg Quiver.Hom.unop (hφ (unop j)))

/--
Local W263-supported bridge: in a preadditive category, finite-coproduct stability
follows from finite-product stability because finite coproducts are finite
biproducts and the induced colimit and limit maps are isomorphic as arrows.
-/
theorem finiteCoproductStability_of_finiteProductStability
    (W : MorphismProperty C) [HasFiniteCoproducts C]
    [W.RespectsIso] [W.IsStableUnderFiniteProducts] :
    W.IsStableUnderFiniteCoproducts where
  isStableUnderCoproductsOfShape J _ := by
    refine MorphismProperty.IsStableUnderCoproductsOfShape.mk W J ?_
    intro X₁ X₂ _ _ f hf
    letI : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteCoproducts
    let F₁ : Discrete J ⥤ C := Discrete.functor X₁
    let F₂ : Discrete J ⥤ C := Discrete.functor X₂
    let η : F₁ ⟶ F₂ := Discrete.natTrans (fun j => f j.as)
    have hη : W.functorCategory (Discrete J) η := by
      intro j
      exact hf j.as
    have hLimitMap : W (Limits.limMap η) :=
      MorphismProperty.limMap (W := W) (J := Discrete J) η hη
    have hColimitMap : W (Limits.colimMap η) := by
      refine (W.arrow_mk_iso_iff ?_).2 hLimitMap
      refine Arrow.isoMk
        ((HasBiproductsOfShape.colimIsoLim (J := J) (C := C)).app F₁)
        ((HasBiproductsOfShape.colimIsoLim (J := J) (C := C)).app F₂) ?_
      exact (HasBiproductsOfShape.colimIsoLim (J := J) (C := C)).hom.naturality η |>.symm
    simpa [Limits.Sigma.map, η, F₁, F₂] using hColimitMap

/-- Direct finite-coproduct stability supplied by the W263 route. -/
theorem metrizableLCA_directFiniteCoproductStability :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteCoproducts := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteProducts :=
    BoundedFiniteProducts.isStableUnderFiniteProducts_metrizableLCA
  exact finiteCoproductStability_of_finiteProductStability
    (boundedExactWeakEquivalence MetrizableLCA.{0})

/-- Opposite finite-product stability obtained by composing W263 support with W281 transport. -/
theorem metrizableLCA_oppositeFiniteProductStability :
    ((boundedExactWeakEquivalence MetrizableLCA.{0}).op).IsStableUnderFiniteProducts := by
  letI : (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderFiniteCoproducts :=
    metrizableLCA_directFiniteCoproductStability
  exact op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts
    (boundedExactWeakEquivalence MetrizableLCA.{0})

abbrev MetrizableLCAWalkingParallelPairOpColimitStabilityNeeded : Prop :=
  (boundedExactWeakEquivalence MetrizableLCA.{0}).IsStableUnderColimitsOfShape
    WalkingParallelPairᵒᵖ

/-- Specialized W283 consumer for the `WalkingParallelPair` branch. -/
theorem metrizableLCA_oppositeWalkingParallelPairStability_of_directColimits
    (h : MetrizableLCAWalkingParallelPairOpColimitStabilityNeeded) :
    ((boundedExactWeakEquivalence MetrizableLCA.{0}).op).IsStableUnderLimitsOfShape
      WalkingParallelPair := by
  haveI := h
  exact op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op
    (boundedExactWeakEquivalence MetrizableLCA.{0}) (J := WalkingParallelPair)

structure SourceFiniteColimitInput (C : Type u) [Category.{v} C] : Prop where
  finiteColimits : HasFiniteColimits C

theorem boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits
    (C : Type u) [Category.{v} C] [Preadditive C] [HasFiniteColimits C] :
    HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits (BoundedComplexCategory C) := inferInstance
  exact Limits.hasFiniteColimits_opposite_iff.mp inferInstance

theorem boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput
    (C : Type u) [Category.{v} C] [Preadditive C]
    (h : SourceFiniteColimitInput C) :
    HasFiniteLimits (BoundedComplexCategory C)ᵒᵖ := by
  haveI : HasFiniteColimits C := h.finiteColimits
  exact boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimits C

theorem metrizableLCA_sourceFiniteColimitInput :
    SourceFiniteColimitInput MetrizableLCA.{u} where
  finiteColimits := inferInstance

theorem metrizableLCA_boundedComplexOp_hasFiniteLimits :
    HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
  boundedComplexOp_hasFiniteLimits_of_sourceFiniteColimitInput MetrizableLCA
    metrizableLCA_sourceFiniteColimitInput

theorem metrizableLCA_boundedComplexOp_hasFiniteProducts :
    HasFiniteProducts (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := by
  haveI : HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    metrizableLCA_boundedComplexOp_hasFiniteLimits
  infer_instance

theorem metrizableLCA_boundedComplexOp_hasEqualizers :
    HasEqualizers (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ := by
  haveI : HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
    metrizableLCA_boundedComplexOp_hasFiniteLimits
  infer_instance

structure MetrizableLCAConcreteSourceFiniteLimitFacts : Prop where
  finiteLimits : HasFiniteLimits (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ
  finiteProducts : HasFiniteProducts (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ
  equalizers : HasEqualizers (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ

theorem metrizableLCA_concreteSourceFiniteLimitFacts :
    MetrizableLCAConcreteSourceFiniteLimitFacts.{u} where
  finiteLimits := metrizableLCA_boundedComplexOp_hasFiniteLimits
  finiteProducts := metrizableLCA_boundedComplexOp_hasFiniteProducts
  equalizers := metrizableLCA_boundedComplexOp_hasEqualizers

abbrev metrizableLCA_oppositeWeakEquivalence :
    MorphismProperty (BoundedComplexCategory MetrizableLCA.{u})ᵒᵖ :=
  (boundedExactWeakEquivalence MetrizableLCA.{u}).op

abbrev MetrizableLCAOppositeFunctorCategoryLocalizationInput : Prop :=
  ((Functor.whiskeringRight WalkingParallelPair
      ((BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ)
      ((metrizableLCA_oppositeWeakEquivalence.{0}).Localization)).obj
      ((metrizableLCA_oppositeWeakEquivalence.{0}).Q)).IsLocalization
    ((metrizableLCA_oppositeWeakEquivalence.{0}).functorCategory WalkingParallelPair)

abbrev MetrizableLCAOppositeContainsIdentitiesInput : Prop :=
  ((boundedExactWeakEquivalence MetrizableLCA.{0}).op).ContainsIdentities

structure MetrizableLCAOppositeFiniteProductTransferInputs : Prop where
  containsIdentities : (metrizableLCA_oppositeWeakEquivalence.{0}).ContainsIdentities
  stableFiniteProducts : (metrizableLCA_oppositeWeakEquivalence.{0}).IsStableUnderFiniteProducts

structure MetrizableLCAOppositeEqualizerTransferInputs : Prop where
  stableWalkingParallelPair :
    (metrizableLCA_oppositeWeakEquivalence.{0}).IsStableUnderLimitsOfShape WalkingParallelPair
  functorCategoryLocalization : MetrizableLCAOppositeFunctorCategoryLocalizationInput

structure MetrizableLCAOppositeFiniteLimitTransferInputs : Prop where
  finiteProducts : MetrizableLCAOppositeFiniteProductTransferInputs
  equalizers : MetrizableLCAOppositeEqualizerTransferInputs

theorem metrizableLCA_oppositeLocalizationHasWalkingParallelPairLimits
    (hsource : MetrizableLCAConcreteSourceFiniteLimitFacts.{0})
    (htransfer : MetrizableLCAOppositeEqualizerTransferInputs) :
    HasLimitsOfShape WalkingParallelPair
      ((metrizableLCA_oppositeWeakEquivalence.{0}).Localization) := by
  haveI : HasEqualizers (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ := hsource.equalizers
  haveI :
      (metrizableLCA_oppositeWeakEquivalence.{0}).IsStableUnderLimitsOfShape
        WalkingParallelPair := htransfer.stableWalkingParallelPair
  haveI : MetrizableLCAOppositeFunctorCategoryLocalizationInput :=
    htransfer.functorCategoryLocalization
  haveI : HasLimitsOfShape WalkingParallelPair
      (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ := by
    infer_instance
  exact CategoryTheory.Localization.hasLimitsOfShape_of_functorCategoryLocalization_w266
    ((metrizableLCA_oppositeWeakEquivalence.{0}).Q)
    (metrizableLCA_oppositeWeakEquivalence.{0}) WalkingParallelPair

theorem metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs
    (hsource : MetrizableLCAConcreteSourceFiniteLimitFacts.{0})
    (htransfer : MetrizableLCAOppositeEqualizerTransferInputs) :
    HasEqualizers ((metrizableLCA_oppositeWeakEquivalence.{0}).Localization) :=
  metrizableLCA_oppositeLocalizationHasWalkingParallelPairLimits hsource htransfer

theorem metrizableLCA_oppositeLocalizationHasFiniteProducts_of_transferInputs
    (hsource : MetrizableLCAConcreteSourceFiniteLimitFacts.{0})
    (htransfer : MetrizableLCAOppositeFiniteProductTransferInputs) :
    HasFiniteProducts ((metrizableLCA_oppositeWeakEquivalence.{0}).Localization) := by
  haveI : HasFiniteProducts (BoundedComplexCategory MetrizableLCA.{0})ᵒᵖ :=
    hsource.finiteProducts
  haveI : (metrizableLCA_oppositeWeakEquivalence.{0}).ContainsIdentities :=
    htransfer.containsIdentities
  haveI : (metrizableLCA_oppositeWeakEquivalence.{0}).IsStableUnderFiniteProducts :=
    htransfer.stableFiniteProducts
  infer_instance

theorem metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs
    (hsource : MetrizableLCAConcreteSourceFiniteLimitFacts.{0})
    (htransfer : MetrizableLCAOppositeFiniteLimitTransferInputs) :
    HasFiniteLimits ((metrizableLCA_oppositeWeakEquivalence.{0}).Localization) := by
  letI : HasFiniteProducts ((metrizableLCA_oppositeWeakEquivalence.{0}).Localization) :=
    metrizableLCA_oppositeLocalizationHasFiniteProducts_of_transferInputs
      hsource htransfer.finiteProducts
  letI : HasEqualizers ((metrizableLCA_oppositeWeakEquivalence.{0}).Localization) :=
    metrizableLCA_oppositeLocalizationHasEqualizers_of_transferInputs
      hsource htransfer.equalizers
  exact hasFiniteLimits_of_hasEqualizers_and_finite_products

/--
The remaining nonlocal inputs after the W263/W281/W283 local stability transports.
These are exactly the fields needed to feed the W255 finite-limit consumer.
-/
structure MetrizableLCAOppositeFiniteLimitAssemblyInputs : Prop where
  containsIdentities : MetrizableLCAOppositeContainsIdentitiesInput
  directWalkingParallelPairOpColimits : MetrizableLCAWalkingParallelPairOpColimitStabilityNeeded
  functorCategoryLocalization : MetrizableLCAOppositeFunctorCategoryLocalizationInput

/-- W255 finite-product transfer inputs assembled from W263/W281 plus identity membership. -/
theorem metrizableLCA_finiteProductTransferInputs
    (h : MetrizableLCAOppositeFiniteLimitAssemblyInputs) :
    MetrizableLCAOppositeFiniteProductTransferInputs where
  containsIdentities := h.containsIdentities
  stableFiniteProducts := metrizableLCA_oppositeFiniteProductStability

/-- W255 equalizer transfer inputs assembled from W283 plus functor-category localization. -/
theorem metrizableLCA_equalizerTransferInputs
    (h : MetrizableLCAOppositeFiniteLimitAssemblyInputs) :
    MetrizableLCAOppositeEqualizerTransferInputs where
  stableWalkingParallelPair :=
    metrizableLCA_oppositeWalkingParallelPairStability_of_directColimits
      h.directWalkingParallelPairOpColimits
  functorCategoryLocalization := h.functorCategoryLocalization

/-- The single W255 transfer-input package produced by this assembly. -/
theorem metrizableLCA_finiteLimitTransferInputs
    (h : MetrizableLCAOppositeFiniteLimitAssemblyInputs) :
    MetrizableLCAOppositeFiniteLimitTransferInputs where
  finiteProducts := metrizableLCA_finiteProductTransferInputs h
  equalizers := metrizableLCA_equalizerTransferInputs h

/--
Strongest checked opposite finite-limit consumer: once the three explicit
assembly inputs are supplied, W255 gives finite limits in the opposite
localization.
-/
theorem metrizableLCA_oppositeLocalizationHasFiniteLimits_of_assemblyInputs
    (h : MetrizableLCAOppositeFiniteLimitAssemblyInputs) :
    HasFiniteLimits (((boundedExactWeakEquivalence MetrizableLCA.{0}).op).Localization) :=
  metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs
    metrizableLCA_concreteSourceFiniteLimitFacts
    (metrizableLCA_finiteLimitTransferInputs h)

/-- Machine-readable frontier for the W266 assembly. -/
structure OppositeFiniteLimitAssemblyState : Type where
  seed : String
  selectedRoute : String
  localStabilityTransport : List String
  remainingInputs : List String
  strongestConsumer : String
  productSuccessClaimed : Bool

def currentOppositeFiniteLimitAssemblyState : OppositeFiniteLimitAssemblyState where
  seed := "70311d1a4db4a3f3ef51d0277b9abc4b"
  selectedRoute := "W263 finite coproducts -> W281 opposite finite products; W283 direct WPP op-colimits -> opposite WPP limits; W255 finite-limit consumer"
  localStabilityTransport :=
    ["finiteCoproductStability_of_finiteProductStability",
      "metrizableLCA_directFiniteCoproductStability",
      "metrizableLCA_oppositeFiniteProductStability",
      "metrizableLCA_equalizerTransferInputs"]
  remainingInputs :=
    ["((boundedExactWeakEquivalence MetrizableLCA).op).ContainsIdentities",
      "(boundedExactWeakEquivalence MetrizableLCA).IsStableUnderColimitsOfShape WalkingParallelPair^op",
      "MetrizableLCAOppositeWalkingParallelPairFunctorCategoryLocalizationInput"]
  strongestConsumer := "metrizableLCA_oppositeLocalizationHasFiniteLimits_of_assemblyInputs"
  productSuccessClaimed := false

theorem currentOppositeFiniteLimitAssemblyState_productSuccess :
    currentOppositeFiniteLimitAssemblyState.productSuccessClaimed = false := rfl

def oppositeFiniteLimitAssemblyDeclarationNames : List String :=
  ["finiteCoproductStability_of_finiteProductStability",
    "metrizableLCA_directFiniteCoproductStability",
    "metrizableLCA_oppositeFiniteProductStability",
    "MetrizableLCAWalkingParallelPairOpColimitStabilityNeeded",
    "MetrizableLCAOppositeFunctorCategoryLocalizationInput",
    "MetrizableLCAOppositeContainsIdentitiesInput",
    "MetrizableLCAOppositeFiniteLimitAssemblyInputs",
    "metrizableLCA_finiteProductTransferInputs",
    "metrizableLCA_equalizerTransferInputs",
    "metrizableLCA_finiteLimitTransferInputs",
    "metrizableLCA_oppositeLocalizationHasFiniteLimits_of_assemblyInputs",
    "currentOppositeFiniteLimitAssemblyState"]

theorem oppositeFiniteLimitAssemblyDeclarationNames_count :
    oppositeFiniteLimitAssemblyDeclarationNames.length = 12 := rfl

section Checks

#check finiteCoproductStability_of_finiteProductStability
#check metrizableLCA_directFiniteCoproductStability
#check metrizableLCA_oppositeFiniteProductStability
#check op_isStableUnderFiniteProducts_of_isStableUnderFiniteCoproducts
#check op_isStableUnderLimitsOfShape_of_isStableUnderColimitsOfShape_op
#check metrizableLCA_oppositeWalkingParallelPairStability_of_directColimits
#check metrizableLCA_oppositeLocalizationHasFiniteLimits_of_transferInputs
#check MetrizableLCAOppositeFiniteLimitAssemblyInputs
#check metrizableLCA_finiteProductTransferInputs
#check metrizableLCA_equalizerTransferInputs
#check metrizableLCA_finiteLimitTransferInputs
#check metrizableLCA_oppositeLocalizationHasFiniteLimits_of_assemblyInputs
#check currentOppositeFiniteLimitAssemblyState
#check currentOppositeFiniteLimitAssemblyState_productSuccess
#check oppositeFiniteLimitAssemblyDeclarationNames
#check oppositeFiniteLimitAssemblyDeclarationNames_count

end Checks

end OppositeFiniteLimitAssemblyW266

end LeanLCAExactChallenge
