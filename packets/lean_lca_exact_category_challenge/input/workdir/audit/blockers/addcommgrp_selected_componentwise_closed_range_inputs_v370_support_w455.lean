import LeanLCAExactChallenge.Derived.AddCommGrpSnakeInputDifferenceCokernel
import LeanLCAExactChallenge.LCA.Cokernel
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.Preadditive
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.Topology.Defs.Induced

/-!
W455: selected componentwise closed-range inputs for the W452 projection bridge.

Seed: `efae3890ed42a5cac9682184`.

This file checks the accessible component maps of the selected short-complex
difference `(selectedMetrizableLeft S - selectedMetrizableRight S)` and packages
the exact closed-range evidence that should feed a future closed-range-to-
projection-colimit lift.  The existing copied W452/W442/W443 support files are
standalone worker files rather than importable modules, so the declarations
needed by the W452 consumer are kept locally in this namespace.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open Topology

namespace AddCommGrpSelectedComponentwiseClosedRangeInputsV370SupportW455

open AddCommGrpSnakeInputDifferenceCokernel
open WppOpExactAcyclicFrontierConsolidatedW318

/-- Local name for the short-complex functor forgetting topology. -/
abbrev forgottenShortComplexFunctor :
    ShortComplex MetrizableLCA.{0} ⥤ ShortComplex AddCommGrpCat.{0} :=
  (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}).mapShortComplex

/-- The underlying functor used by the one-component closed-range wrappers. -/
abbrev underlyingForgetfulFunctor : MetrizableLCA.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}

/-- The ordinary source object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinarySourceIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.zero

/-- The ordinary target object of a WPP diagram, transported into `WalkingParallelPairᵒᵖ`. -/
abbrev ordinaryTargetIndex : WalkingParallelPairᵒᵖ :=
  walkingParallelPairOpEquiv.functor.obj WalkingParallelPair.one

/-- The selected left arrow before forgetting topology. -/
def selectedMetrizableLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)

/-- The selected right arrow before forgetting topology. -/
def selectedMetrizableRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  S.map (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)

/-- The selected short-complex difference map whose projections W452 needs. -/
def selectedMetrizableDifference
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    S.obj ordinarySourceIndex ⟶ S.obj ordinaryTargetIndex :=
  selectedMetrizableLeft S - selectedMetrizableRight S

/-- First component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₁
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₁ ⟶ (S.obj ordinaryTargetIndex).X₁ :=
  (selectedMetrizableDifference S).τ₁

/-- Second component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₂
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₂ ⟶ (S.obj ordinaryTargetIndex).X₂ :=
  (selectedMetrizableDifference S).τ₂

/-- Third component of the selected difference map. -/
abbrev selectedMetrizableDifferenceπ₃
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).X₃ ⟶ (S.obj ordinaryTargetIndex).X₃ :=
  (selectedMetrizableDifference S).τ₃

/-- W443-style algebraic range subgroup after forgetting topology. -/
abbrev forgottenAlgebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup (underlyingForgetfulFunctor.obj Y) :=
  AddSubgroup.map (underlyingForgetfulFunctor.map f).hom
    (⊤ : AddSubgroup (underlyingForgetfulFunctor.obj X))

/-- The same algebraic range subgroup, kept in the topological target object. -/
abbrev algebraicRangeSubgroup {X Y : MetrizableLCA.{0}} (f : X ⟶ Y) :
    AddSubgroup Y :=
  AddSubgroup.map f.hom.toAddMonoidHom (⊤ : AddSubgroup X)

/-- The local algebraic range subgroup has carrier `Set.range f`. -/
theorem mem_algebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ algebraicRangeSubgroup f ↔ y ∈ Set.range (f : X → Y) := by
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- The forgotten algebraic range subgroup has the same carrier as the topological one. -/
theorem mem_forgottenAlgebraicRangeSubgroup_iff {X Y : MetrizableLCA.{0}}
    (f : X ⟶ Y) (y : Y) :
    y ∈ forgottenAlgebraicRangeSubgroup f ↔ y ∈ algebraicRangeSubgroup f := by
  rw [mem_algebraicRangeSubgroup_iff]
  constructor
  · intro hy
    rcases hy with ⟨x, _hx, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, trivial, rfl⟩

/-- Closedness of the underlying set range gives closedness of the algebraic range subgroup. -/
theorem isClosed_algebraicRangeSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    IsClosed (algebraicRangeSubgroup f : Set Y) := by
  rwa [Set.ext_iff.mpr (mem_algebraicRangeSubgroup_iff f)]

/-- In `Y`, a closed algebraic range is equal to the closed cokernel subgroup. -/
theorem algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    algebraicRangeSubgroup f = MetrizableLCA.cokernelSubgroup f := by
  apply le_antisymm
  · exact MetrizableLCA.range_le_cokernelSubgroup f
  · unfold MetrizableLCA.cokernelSubgroup
    apply AddSubgroup.topologicalClosure_minimal
    · intro y hy
      exact hy
    · exact isClosed_algebraicRangeSubgroup_of_isClosed_range f hclosed

/-- W443 closed-range equality for one projected component map. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosed : IsClosed (Set.range (f : X → Y))) :
    forgottenAlgebraicRangeSubgroup f =
      (MetrizableLCA.cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) := by
  ext y
  constructor
  · intro hy
    have hyalg : y ∈ algebraicRangeSubgroup f :=
      (mem_forgottenAlgebraicRangeSubgroup_iff f y).mp hy
    rw [algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed] at hyalg
    exact hyalg
  · intro hy
    have hyalg : y ∈ algebraicRangeSubgroup f := by
      rw [algebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f hclosed]
      exact hy
    exact (mem_forgottenAlgebraicRangeSubgroup_iff f y).mpr hyalg

/-- W443 closed-map wrapper for one projected component map. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedMap : IsClosedMap (f : X → Y)) :
    forgottenAlgebraicRangeSubgroup f =
      (MetrizableLCA.cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) := by
  refine forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f ?_
  simpa [Set.image_univ] using hclosedMap Set.univ isClosed_univ

/-- W443 closed-embedding wrapper for one projected component map. -/
theorem forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding
    {X Y : MetrizableLCA.{0}} (f : X ⟶ Y)
    (hclosedEmbedding : IsClosedEmbedding (f : X → Y)) :
    forgottenAlgebraicRangeSubgroup f =
      (MetrizableLCA.cokernelSubgroup f : AddSubgroup (underlyingForgetfulFunctor.obj Y)) :=
  forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range f
    hclosedEmbedding.isClosed_range

/-- The selected leg before forgetting topology. -/
def selectedMetrizableTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    S.obj ordinaryTargetIndex ⟶ cs.pt :=
  cs.ι.app ordinaryTargetIndex

/-- Cocone naturality says the selected target leg coequalizes the two WPP arrows. -/
theorem selectedMetrizableTargetCoconeLeg_parallel_pair
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    selectedMetrizableLeft S ≫ selectedMetrizableTargetCoconeLeg S cs =
      selectedMetrizableRight S ≫ selectedMetrizableTargetCoconeLeg S cs :=
  (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.left)).trans
    (cs.w (walkingParallelPairOpEquiv.functor.map WalkingParallelPairHom.right)).symm

/-- The selected target leg as a cofork in short complexes of metrizable LCA groups. -/
def selectedMetrizableTargetCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    Cofork (selectedMetrizableLeft S) (selectedMetrizableRight S) :=
  Cofork.ofπ (selectedMetrizableTargetCoconeLeg S cs)
    (selectedMetrizableTargetCoconeLeg_parallel_pair S cs)

/-- The selected metrizable target leg is a cokernel cofork for `(left - right)`. -/
def selectedMetrizableTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedMetrizableLeft S - selectedMetrizableRight S) :=
  Preadditive.cokernelCoforkOfCofork (selectedMetrizableTargetCofork S cs)

/-- The forgotten ordinary-left arrow of the WPP-op short-complex diagram. -/
def selectedForgottenLeft
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableLeft S)

/-- The forgotten ordinary-right arrow of the WPP-op short-complex diagram. -/
def selectedForgottenRight
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}) :
    (S.obj ordinarySourceIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableRight S)

/-- The selected forgotten-target cocone leg. -/
def selectedForgottenTargetCoconeLeg
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    (S.obj ordinaryTargetIndex).map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) ⟶
      cs.pt.map (forget₂ MetrizableLCA.{0} AddCommGrpCat.{0}) :=
  forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs)

/-- The selected forgotten leg is an explicit cokernel cofork. -/
def selectedForgottenTargetCokernelCofork
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    CokernelCofork (selectedForgottenLeft S - selectedForgottenRight S) :=
  CokernelCofork.ofπ (selectedForgottenTargetCoconeLeg S cs) (by
    rw [Preadditive.sub_comp, sub_eq_zero]
    change
      forgottenShortComplexFunctor.map (selectedMetrizableLeft S) ≫
          forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs) =
        forgottenShortComplexFunctor.map (selectedMetrizableRight S) ≫
          forgottenShortComplexFunctor.map (selectedMetrizableTargetCoconeLeg S cs)
    rw [← forgottenShortComplexFunctor.map_comp, ← forgottenShortComplexFunctor.map_comp,
      selectedMetrizableTargetCoconeLeg_parallel_pair S cs])

/-- The short-complex forgetful functor preserves zero morphisms, componentwise. -/
instance forgottenShortComplexFunctor_preservesZeroMorphisms :
    forgottenShortComplexFunctor.PreservesZeroMorphisms where
  map_zero S T := by
    ext x <;> rfl

/-- The short-complex forgetful functor is additive, componentwise. -/
instance forgottenShortComplexFunctor_additive :
    forgottenShortComplexFunctor.Additive where
  map_add {S T} {f g} := by
    ext x <;> rfl

/--
After rewriting `F.map (left - right)` to `F.map left - F.map right`, the mapped
selected metrizable cokernel cofork is the selected forgotten cokernel cofork.
-/
def precomposeSelectedForgottenCokernelCoforkIsoMap
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) :
    let p : parallelPair
        (forgottenShortComplexFunctor.map
          (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
        parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
      parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
    ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) ≅
      (selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor := by
  dsimp
  refine Cofork.ext (Iso.refl _) ?_
  simp only [Iso.refl_hom]
  rfl

/-- W452 componentwise cokernel-colimit data for the selected mapped cofork. -/
structure SelectedMappedCokernelComponentwiseInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hπ₁ :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))
  hπ₂ :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))
  hπ₃ :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))

/-- W452 assembly theorem from the three projection colimit inputs. -/
def selectedMappedCokernelColimitOfComponentwise
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    IsColimit
      ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) :=
  ShortComplex.isColimitOfIsColimitπ
    ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)
    H.hπ₁ H.hπ₂ H.hπ₃

/-- W452 bridge: componentwise inputs imply the selected forgotten cokernel cofork is colimiting. -/
def selectedForgottenTargetCokernelColimitOfComponentwise
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedMappedCokernelComponentwiseInputs S cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) := by
  let p : parallelPair
      (forgottenShortComplexFunctor.map
        (selectedMetrizableLeft S - selectedMetrizableRight S)) 0 ≅
      parallelPair (selectedForgottenLeft S - selectedForgottenRight S) 0 :=
    parallelPair.eqOfHomEq forgottenShortComplexFunctor.map_sub rfl
  let hMap :
      IsColimit
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor) :=
    selectedMappedCokernelColimitOfComponentwise H
  let hPre :
      IsColimit
        ((Cocone.precompose p.hom).obj (selectedForgottenTargetCokernelCofork S cs)) :=
    IsColimit.ofIsoColimit hMap
      (precomposeSelectedForgottenCokernelCoforkIsoMap S cs).symm
  exact (IsColimit.precomposeHomEquiv p (selectedForgottenTargetCokernelCofork S cs)) hPre

/-- Direct W452 projection-input consumer. -/
def selectedForgottenTargetCokernelColimitOfComponentwise'
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S)
    (hπ₁ :
      IsColimit
        ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)))
    (hπ₂ :
      IsColimit
        ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor)))
    (hπ₃ :
      IsColimit
        ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
          ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) :=
  selectedForgottenTargetCokernelColimitOfComponentwise
    ({ hπ₁ := hπ₁, hπ₂ := hπ₂, hπ₃ := hπ₃ } :
      SelectedMappedCokernelComponentwiseInputs S cs)

/--
Checked W455 boundary: exact component maps plus the closed-range equalities and
the still-missing projection colimit proofs for W452.
-/
structure SelectedComponentwiseClosedRangeProjectionInputs
    (S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0})
    (cs : Cocone S) : Type 1 where
  hclosedπ₁ : IsClosed (Set.range (selectedMetrizableDifferenceπ₁ S :
    (S.obj ordinarySourceIndex).X₁ → (S.obj ordinaryTargetIndex).X₁))
  hclosedπ₂ : IsClosed (Set.range (selectedMetrizableDifferenceπ₂ S :
    (S.obj ordinarySourceIndex).X₂ → (S.obj ordinaryTargetIndex).X₂))
  hclosedπ₃ : IsClosed (Set.range (selectedMetrizableDifferenceπ₃ S :
    (S.obj ordinarySourceIndex).X₃ → (S.obj ordinaryTargetIndex).X₃))
  hπ₁ :
    IsColimit
      ((ShortComplex.π₁ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))
  hπ₂ :
    IsColimit
      ((ShortComplex.π₂ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))
  hπ₃ :
    IsColimit
      ((ShortComplex.π₃ : ShortComplex AddCommGrpCat.{0} ⥤ AddCommGrpCat.{0}).mapCocone
        ((selectedMetrizableTargetCokernelCofork S cs).map forgottenShortComplexFunctor))

/-- The first closed-range input gives the W443 equality for the first selected component. -/
theorem selectedDifferenceπ₁_rangeEquality
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputs S cs) :
    forgottenAlgebraicRangeSubgroup (selectedMetrizableDifferenceπ₁ S) =
      (MetrizableLCA.cokernelSubgroup (selectedMetrizableDifferenceπ₁ S) :
        AddSubgroup (underlyingForgetfulFunctor.obj (S.obj ordinaryTargetIndex).X₁)) :=
  forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    (selectedMetrizableDifferenceπ₁ S) H.hclosedπ₁

/-- The second closed-range input gives the W443 equality for the second selected component. -/
theorem selectedDifferenceπ₂_rangeEquality
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputs S cs) :
    forgottenAlgebraicRangeSubgroup (selectedMetrizableDifferenceπ₂ S) =
      (MetrizableLCA.cokernelSubgroup (selectedMetrizableDifferenceπ₂ S) :
        AddSubgroup (underlyingForgetfulFunctor.obj (S.obj ordinaryTargetIndex).X₂)) :=
  forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    (selectedMetrizableDifferenceπ₂ S) H.hclosedπ₂

/-- The third closed-range input gives the W443 equality for the third selected component. -/
theorem selectedDifferenceπ₃_rangeEquality
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputs S cs) :
    forgottenAlgebraicRangeSubgroup (selectedMetrizableDifferenceπ₃ S) =
      (MetrizableLCA.cokernelSubgroup (selectedMetrizableDifferenceπ₃ S) :
        AddSubgroup (underlyingForgetfulFunctor.obj (S.obj ordinaryTargetIndex).X₃)) :=
  forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
    (selectedMetrizableDifferenceπ₃ S) H.hclosedπ₃

/-- The checked boundary consumes the projection fields into W452's componentwise input structure. -/
def selectedMappedCokernelComponentwiseInputsOfClosedRangeProjectionInputs
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputs S cs) :
    SelectedMappedCokernelComponentwiseInputs S cs where
  hπ₁ := H.hπ₁
  hπ₂ := H.hπ₂
  hπ₃ := H.hπ₃

/-- The checked boundary consumes W455 inputs into the W452 forgotten-target bridge. -/
def selectedForgottenTargetCokernelColimitOfClosedRangeProjectionInputs
    {S : WalkingParallelPairᵒᵖ ⥤ ShortComplex MetrizableLCA.{0}}
    {cs : Cocone S}
    (H : SelectedComponentwiseClosedRangeProjectionInputs S cs) :
    IsColimit (selectedForgottenTargetCokernelCofork S cs) :=
  selectedForgottenTargetCokernelColimitOfComponentwise
    (selectedMappedCokernelComponentwiseInputsOfClosedRangeProjectionInputs H)

/-- W455 checked support state. -/
structure AddCommGrpSelectedComponentwiseClosedRangeInputsV370SupportState : Type where
  seed : String
  checkedDeclarations : List String
  componentwiseClosedRangeResult : String
  w452BridgeConsumerResult : String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentAddCommGrpSelectedComponentwiseClosedRangeInputsV370SupportState :
    AddCommGrpSelectedComponentwiseClosedRangeInputsV370SupportState where
  seed := "efae3890ed42a5cac9682184"
  checkedDeclarations :=
    ["selectedMetrizableDifferenceπ₁",
      "selectedMetrizableDifferenceπ₂",
      "selectedMetrizableDifferenceπ₃",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap",
      "forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding",
      "SelectedMappedCokernelComponentwiseInputs",
      "selectedForgottenTargetCokernelColimitOfComponentwise",
      "selectedForgottenTargetCokernelColimitOfComponentwise'",
      "SelectedComponentwiseClosedRangeProjectionInputs",
      "selectedDifferenceπ₁_rangeEquality",
      "selectedDifferenceπ₂_rangeEquality",
      "selectedDifferenceπ₃_rangeEquality",
      "selectedMappedCokernelComponentwiseInputsOfClosedRangeProjectionInputs",
      "selectedForgottenTargetCokernelColimitOfClosedRangeProjectionInputs"]
  componentwiseClosedRangeResult := "partial"
  w452BridgeConsumerResult := "proved"
  remainingInputs :=
    ["A theorem turning each selected component closed-range equality into the corresponding projection `IsColimit` field of `SelectedMappedCokernelComponentwiseInputs S cs` is still missing.",
      "The W445 copied file named in the worker contract is absent from this worktree; W442/W443-style one-component wrappers were checked locally instead."]
  productSuccessClaimed := false

theorem currentAddCommGrpSelectedComponentwiseClosedRangeInputsV370SupportState_productSuccess :
    currentAddCommGrpSelectedComponentwiseClosedRangeInputsV370SupportState.productSuccessClaimed =
      false :=
  rfl

section Checks

#check selectedMetrizableDifferenceπ₁
#check selectedMetrizableDifferenceπ₂
#check selectedMetrizableDifferenceπ₃
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosed_range
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedMap
#check forgottenAlgebraicRangeSubgroup_eq_cokernelSubgroup_of_isClosedEmbedding
#check SelectedMappedCokernelComponentwiseInputs
#check selectedForgottenTargetCokernelColimitOfComponentwise
#check selectedForgottenTargetCokernelColimitOfComponentwise'
#check SelectedComponentwiseClosedRangeProjectionInputs
#check selectedDifferenceπ₁_rangeEquality
#check selectedDifferenceπ₂_rangeEquality
#check selectedDifferenceπ₃_rangeEquality
#check selectedMappedCokernelComponentwiseInputsOfClosedRangeProjectionInputs
#check selectedForgottenTargetCokernelColimitOfClosedRangeProjectionInputs
#check currentAddCommGrpSelectedComponentwiseClosedRangeInputsV370SupportState_productSuccess

end Checks

end AddCommGrpSelectedComponentwiseClosedRangeInputsV370SupportW455

end LeanLCAExactChallenge
