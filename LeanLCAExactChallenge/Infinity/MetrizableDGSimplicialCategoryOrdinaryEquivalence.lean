import LeanLCAExactChallenge.Infinity.MetrizableDGMappingZModuleVertices
import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategory

/-!
# The ordinary category underlying the direct dg simplicial enrichment

This file identifies the vertices of the direct Dold--Kan mapping simplicial sets with
ordinary morphisms of bounded complexes. It proves that enriched composition and identities
become the usual composition and identities under this identification, packages the result as
an ordinary functor, and proves that this functor is an equivalence of ordinary categories.

The final equivalence is deliberately only a `CategoryTheory.Equivalence`. It does not assert an
equivalence of simplicially enriched categories, simplicial nerves, or quasicategories.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open AlgebraicTopology
open CategoryTheory
open CategoryTheory.MonoidalCategory
open Opposite
open Simplicial

/-- Identify degree-zero elements of the direct mapping complex with bounded-complex morphisms. -/
def dgMappingDirectZModuleChainComplexZeroEquivBoundedHom
    (K L : ComplexCategory) :
    (dgMappingDirectZModuleChainComplex K L).X 0 ≃ (K ⟶ L) :=
  (HomologicalComplex.Hom.isoApp
      (dgMappingZModuleChainComplexIsoDirect K L) 0).symm.toLinearEquiv.toEquiv.trans
    (dgMappingZModuleChainComplexZeroEquivBoundedHom K L)

/-- Identify vertices of a direct Dold--Kan mapping simplicial set with complex morphisms. -/
def dgMappingDirectZModuleVerticesEquivBoundedMorphisms
    (K L : ComplexCategory) :
    dgMappingDirectZModuleSSet K L _⦋0⦌ ≃ (K ⟶ L) :=
  (zModuleDoldKanInverseZeroIso
      (dgMappingDirectZModuleChainComplex K L)).symm.toLinearEquiv.toEquiv.trans
    (dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L)

/-- Direct chain-level composition in degree zero becomes ordinary complex composition. -/
theorem dgMappingDirectZModuleChainComposition_zero_tmul
    (K L M : ComplexCategory)
    (x : (dgMappingDirectZModuleChainComplex K L).X 0)
    (y : (dgMappingDirectZModuleChainComplex L M).X 0) :
    dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K M
        ((dgTruncatedCompositionReversed K L M).f 0
          (HomologicalComplex.ιTensorObj
            (dgMappingDirectZModuleChainComplex L M)
            (dgMappingDirectZModuleChainComplex K L) 0 0 0 rfl
            (y ⊗ₜ[ℤ] x))) =
      dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L x ≫
        dgMappingDirectZModuleChainComplexZeroEquivBoundedHom L M y := by
  let x' := (dgMappingZModuleChainComplexIsoDirect K L).inv.f 0 x
  let y' := (dgMappingZModuleChainComplexIsoDirect L M).inv.f 0 y
  let iT := HomologicalComplex.ιTensorObj
    (dgMappingZModuleChainComplex L M)
    (dgMappingZModuleChainComplex K L) 0 0 0 rfl
  let iD := HomologicalComplex.ιTensorObj
    (dgMappingDirectZModuleChainComplex L M)
    (dgMappingDirectZModuleChainComplex K L) 0 0 0 rfl
  let fLM := (dgMappingZModuleChainComplexIsoDirect L M).hom.f 0
  let fKL := (dgMappingZModuleChainComplexIsoDirect K L).hom.f 0
  let t := (HomologicalComplex.tensorHom
    (dgMappingZModuleChainComplexIsoDirect L M).hom
    (dgMappingZModuleChainComplexIsoDirect K L).hom).f 0
  have hιraw := HomologicalComplex.ι_mapBifunctorMap
    (dgMappingZModuleChainComplexIsoDirect L M).hom
    (dgMappingZModuleChainComplexIsoDirect K L).hom
    (curriedTensor (ModuleCat ℤ)) (ComplexShape.down ℕ) 0 0 0 rfl
  have hι : iT ≫ t = (fLM ⊗ₘ fKL) ≫ iD := by
    simpa only [iT, t, fLM, fKL, iD,
      MonoidalCategory.tensorHom_def] using hιraw
  have hLM := HomologicalComplex.congr_hom
    (dgMappingZModuleChainComplexIsoDirect L M).inv_hom_id 0
  have hKL := HomologicalComplex.congr_hom
    (dgMappingZModuleChainComplexIsoDirect K L).inv_hom_id 0
  have hinput : t (iT (y' ⊗ₜ[ℤ] x')) = iD (y ⊗ₜ[ℤ] x) := by
    have hι' := ConcreteCategory.congr_hom hι (y' ⊗ₜ[ℤ] x')
    simpa only [CategoryTheory.comp_apply,
      ModuleCat.MonoidalCategory.tensorHom_tmul, y', x', fLM, fKL,
      HomologicalComplex.comp_f, HomologicalComplex.id_f,
      ModuleCat.id_apply] using hι'.trans (congrArg₂
        (fun a b => iD (a ⊗ₜ[ℤ] b))
        (ConcreteCategory.congr_hom hLM y)
        (ConcreteCategory.congr_hom hKL x))
  have h := dgMappingZModuleChainComposition_zero_tmul K L M x' y'
  rw [show (dgMappingZModuleChainComposition K L M).f 0
      (iT (y' ⊗ₜ[ℤ] x')) =
        (dgMappingZModuleChainComplexIsoDirect K M).inv.f 0
          ((dgTruncatedCompositionReversed K L M).f 0
            (iD (y ⊗ₜ[ℤ] x))) by
    simp only [dgMappingZModuleChainComposition,
      HomologicalComplex.comp_f, CategoryTheory.comp_apply]
    rw [hinput]] at h
  simpa [dgMappingDirectZModuleChainComplexZeroEquivBoundedHom,
    x', y'] using h

/-- Composition on direct Dold--Kan mapping simplicial modules. -/
def dgMappingDirectZModuleSimplicialComposition
    (K L M : ComplexCategory) :
    dgMappingDirectZModuleSimplicialModule K L ⊗
        dgMappingDirectZModuleSimplicialModule L M ⟶
      dgMappingDirectZModuleSimplicialModule K M :=
  (β_ (dgMappingDirectZModuleSimplicialModule K L)
      (dgMappingDirectZModuleSimplicialModule L M)).hom ≫
    DoldKanMonoidal.inverseTensorator
      DoldKanMonoidal.normalizedMooreOplaxMonoidal
      (dgMappingDirectZModuleChainComplex L M)
      (dgMappingDirectZModuleChainComplex K L) ≫
    DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map
      (dgTruncatedCompositionReversed K L M)

/-- The underlying simplicial-set composition induced by direct simplicial-module composition. -/
def dgMappingDirectZModuleSSetComposition
    (K L M : ComplexCategory) :
    dgMappingDirectZModuleSSet K L ⊗ dgMappingDirectZModuleSSet L M ⟶
      dgMappingDirectZModuleSSet K M :=
  simplicialZModuleTensorPairing
      (dgMappingDirectZModuleSimplicialModule K L)
      (dgMappingDirectZModuleSimplicialModule L M) ≫
    zModuleSimplicialForget.map
      (dgMappingDirectZModuleSimplicialComposition K L M)

/-- Degree-zero direct simplicial-module composition, expressed through normalized Moore chains. -/
theorem dgMappingDirectZModuleSimplicialComposition_f_zero
    (K L M : ComplexCategory) :
    (dgMappingDirectZModuleSimplicialComposition K L M).app (op ⦋0⦌) ≫
        (zModuleDoldKanInverseZeroIso
          (dgMappingDirectZModuleChainComplex K M)).inv =
      (β_ (dgMappingDirectZModuleSimplicialModule K L)
          (dgMappingDirectZModuleSimplicialModule L M)).hom.app (op ⦋0⦌) ≫
        (((zModuleDoldKanInverseZeroIso
              (dgMappingDirectZModuleChainComplex L M)).inv ⊗ₘ
            (zModuleDoldKanInverseZeroIso
              (dgMappingDirectZModuleChainComplex K L)).inv) ≫
          HomologicalComplex.ιTensorObj
            (dgMappingDirectZModuleChainComplex L M)
            (dgMappingDirectZModuleChainComplex K L) 0 0 0 rfl) ≫
        (dgTruncatedCompositionReversed K L M).f 0 := by
  let A := dgMappingDirectZModuleChainComplex K L
  let B := dgMappingDirectZModuleChainComplex L M
  let C := dgMappingDirectZModuleChainComplex K M
  let X := dgMappingDirectZModuleSimplicialModule K L
  let Y := dgMappingDirectZModuleSimplicialModule L M
  let c := dgTruncatedCompositionReversed K L M
  let μ := DoldKanMonoidal.inverseTensorator
    DoldKanMonoidal.normalizedMooreOplaxMonoidal B A
  let β := (β_ X Y).hom.app (op ⦋0⦌)
  let zA := (zModuleDoldKanInverseZeroIso A).inv
  let zB := (zModuleDoldKanInverseZeroIso B).inv
  let zC := (zModuleDoldKanInverseZeroIso C).inv
  let ι := HomologicalComplex.ιTensorObj B A 0 0 0 rfl
  have hc := zModuleDoldKanInverseZeroIso_inv_naturality c
  have hμ := inverseTensorator_f_zero B A
  change ((β ≫ μ.app (op ⦋0⦌)) ≫
      (DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map c).app
        (op ⦋0⦌)) ≫ zC =
    β ≫ ((zB ⊗ₘ zA) ≫ ι) ≫ c.f 0
  calc
    _ = (β ≫ μ.app (op ⦋0⦌)) ≫
        ((DoldKanMonoidal.zModuleDoldKanEquivalence.inverse.map c).app
          (op ⦋0⦌) ≫ zC) := Category.assoc _ _ _
    _ = (β ≫ μ.app (op ⦋0⦌)) ≫
        ((zModuleDoldKanInverseZeroIso (B ⊗ A)).inv ≫ c.f 0) :=
      congrArg (fun t => (β ≫ μ.app (op ⦋0⦌)) ≫ t) hc
    _ = β ≫
        ((μ.app (op ⦋0⦌) ≫
          (zModuleDoldKanInverseZeroIso (B ⊗ A)).inv) ≫ c.f 0) := by
      simp only [Category.assoc]
    _ = β ≫ (((zB ⊗ₘ zA) ≫ ι) ≫ c.f 0) :=
      congrArg (fun t => β ≫ (t ≫ c.f 0)) hμ
    _ = _ := by simp only [Category.assoc]

/-- Elementwise degree-zero formula for direct simplicial-module composition. -/
theorem dgMappingDirectZModuleSimplicialComposition_f_zero_apply
    (K L M : ComplexCategory)
    (f : (dgMappingDirectZModuleSimplicialModule K L).obj (op ⦋0⦌))
    (g : (dgMappingDirectZModuleSimplicialModule L M).obj (op ⦋0⦌)) :
    (zModuleDoldKanInverseZeroIso
        (dgMappingDirectZModuleChainComplex K M)).inv
      ((dgMappingDirectZModuleSimplicialComposition K L M).app
        (op ⦋0⦌) (f ⊗ₜ[ℤ] g)) =
      (dgTruncatedCompositionReversed K L M).f 0
        (HomologicalComplex.ιTensorObj
          (dgMappingDirectZModuleChainComplex L M)
          (dgMappingDirectZModuleChainComplex K L) 0 0 0 rfl
          (((zModuleDoldKanInverseZeroIso
              (dgMappingDirectZModuleChainComplex L M)).inv g) ⊗ₜ[ℤ]
            ((zModuleDoldKanInverseZeroIso
              (dgMappingDirectZModuleChainComplex K L)).inv f))) := by
  have h := ConcreteCategory.congr_hom
    (dgMappingDirectZModuleSimplicialComposition_f_zero K L M)
    (f ⊗ₜ[ℤ] g)
  simpa only [CategoryTheory.comp_apply,
    ModuleCat.MonoidalCategory.braiding_hom_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul] using h

/-- Elementwise degree-zero formula after forgetting to simplicial sets. -/
theorem dgMappingDirectZModuleSSetComposition_f_zero_apply
    (K L M : ComplexCategory)
    (f : (dgMappingDirectZModuleSimplicialModule K L).obj (op ⦋0⦌))
    (g : (dgMappingDirectZModuleSimplicialModule L M).obj (op ⦋0⦌)) :
    (zModuleDoldKanInverseZeroIso
        (dgMappingDirectZModuleChainComplex K M)).inv
      ((dgMappingDirectZModuleSSetComposition K L M).app (op ⦋0⦌) (f, g)) =
      (dgTruncatedCompositionReversed K L M).f 0
        (HomologicalComplex.ιTensorObj
          (dgMappingDirectZModuleChainComplex L M)
          (dgMappingDirectZModuleChainComplex K L) 0 0 0 rfl
          (((zModuleDoldKanInverseZeroIso
              (dgMappingDirectZModuleChainComplex L M)).inv g) ⊗ₜ[ℤ]
            ((zModuleDoldKanInverseZeroIso
              (dgMappingDirectZModuleChainComplex K L)).inv f))) := by
  simpa [dgMappingDirectZModuleSSetComposition,
    simplicialZModuleTensorPairing] using
      dgMappingDirectZModuleSimplicialComposition_f_zero_apply K L M f g

/-- The object of the opposite direct simplicial-module category represented by a complex. -/
def directDGSimplicialModuleObject
    (K : ComplexCategory) : DirectDGSimplicialModuleCategoryOp :=
  Opposite.op
    (show DirectDGSimplicialModuleCategory from Opposite.op K)

/-- The module-enriched composition is the explicit direct Dold--Kan composition. -/
theorem directDGModule_eComp_eq (K L M : ComplexCategory) :
    eComp DirectZSimp
        (directDGSimplicialModuleObject K)
        (directDGSimplicialModuleObject L)
        (directDGSimplicialModuleObject M) =
      dgMappingDirectZModuleSimplicialComposition K L M := by
  rfl

/-- The lax monoidal comparison for forgetting simplicial modules is tensor pairing. -/
theorem zModuleSimplicialForget_mu_eq_pairing
    (X Y : DirectZSimp) :
    Functor.LaxMonoidal.μ zModuleSimplicialForget X Y =
      simplicialZModuleTensorPairing X Y := by
  ext n xy
  obtain ⟨x, y⟩ := xy
  change Functor.LaxMonoidal.μ (forget (ModuleCat ℤ))
      (X.obj n) (Y.obj n) (x, y) =
    (show X.obj n from x) ⊗ₜ[ℤ] (show Y.obj n from y)
  have hi : (inferInstance : (forget (ModuleCat ℤ)).LaxMonoidal) =
      (ModuleCat.adj ℤ).rightAdjointLaxMonoidal := by
    apply Functor.LaxMonoidal.ext <;> rfl
  cases hi
  rw [Adjunction.rightAdjointLaxMonoidal_μ (ModuleCat.adj ℤ)]
  simp [ModuleCat.adj, ModuleCat.freeHomEquiv]

/-- Enriched composition in the direct simplicial category is the explicit set-level map. -/
theorem directDG_sHomComp_eq (K L M : ComplexCategory) :
    SimplicialCategory.sHomComp
        (directDGObject K) (directDGObject L) (directDGObject M) =
      dgMappingDirectZModuleSSetComposition K L M := by
  change eComp SSet
      (show DirectDGSSetEnrichedCategory from
        directDGSimplicialModuleObject K)
      (show DirectDGSSetEnrichedCategory from
        directDGSimplicialModuleObject L)
      (show DirectDGSSetEnrichedCategory from
        directDGSimplicialModuleObject M) = _
  rw [TransportEnrichment.eComp_eq]
  rw [zModuleSimplicialForget_mu_eq_pairing]
  rw [directDGModule_eComp_eq]
  rfl

/-- Vertex identification sends actual enriched composition to complex composition. -/
theorem dgMappingDirectZModuleVerticesEquivBoundedMorphisms_comp
    (K L M : ComplexCategory)
    (f : SimplicialCategory.sHom
      (directDGObject K) (directDGObject L) _⦋0⦌)
    (g : SimplicialCategory.sHom
      (directDGObject L) (directDGObject M) _⦋0⦌) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms K M
        ((SimplicialCategory.sHomComp
          (directDGObject K) (directDGObject L) (directDGObject M)).app
            (op ⦋0⦌) (f, g)) =
      dgMappingDirectZModuleVerticesEquivBoundedMorphisms K L f ≫
        dgMappingDirectZModuleVerticesEquivBoundedMorphisms L M g := by
  rw [directDG_sHomComp_eq]
  let x := (zModuleDoldKanInverseZeroIso
    (dgMappingDirectZModuleChainComplex K L)).inv f
  let y := (zModuleDoldKanInverseZeroIso
    (dgMappingDirectZModuleChainComplex L M)).inv g
  have hzero := dgMappingDirectZModuleSSetComposition_f_zero_apply K L M f g
  change dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K M
      ((zModuleDoldKanInverseZeroIso
        (dgMappingDirectZModuleChainComplex K M)).inv
        ((dgMappingDirectZModuleSSetComposition K L M).app
          (op ⦋0⦌) (f, g))) =
    dgMappingDirectZModuleChainComplexZeroEquivBoundedHom K L x ≫
      dgMappingDirectZModuleChainComplexZeroEquivBoundedHom L M y
  rw [hzero]
  exact dgMappingDirectZModuleChainComposition_zero_tmul K L M x y

/-- `homEquiv'` sends ordinary composition to composition of enriched vertices. -/
theorem directDG_homEquiv_comp
    {X Y Z : DirectDGSimplicialCategory}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    SimplicialCategory.homEquiv' X Z (f ≫ g) =
      (SimplicialCategory.sHomComp X Y Z).app (op ⦋0⦌)
      (SimplicialCategory.homEquiv' X Y f,
          SimplicialCategory.homEquiv' Y Z g) := by
  rfl

/-- Vertex identification sends the enriched identity vertex to the complex identity. -/
theorem dgMappingDirectZModuleVerticesEquivBoundedMorphisms_id
    (K : ComplexCategory) :
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms K K
        (SimplicialCategory.homEquiv'
          (directDGObject K) (directDGObject K) (𝟙 _)) =
      𝟙 K := by
  let X := directDGObject K
  let q : SimplicialCategory.sHom X X _⦋0⦌ :=
    (dgMappingDirectZModuleVerticesEquivBoundedMorphisms K K).symm (𝟙 K)
  let u : X ⟶ X := (SimplicialCategory.homEquiv' X X).symm q
  have hu : SimplicialCategory.homEquiv' X X u = q := by
    exact Equiv.apply_symm_apply _ _
  have hs :
      (SimplicialCategory.sHomComp X X X).app (op ⦋0⦌)
          (SimplicialCategory.homEquiv' X X (𝟙 X), q) = q := by
    calc
      _ = (SimplicialCategory.sHomComp X X X).app (op ⦋0⦌)
          (SimplicialCategory.homEquiv' X X (𝟙 X),
            SimplicialCategory.homEquiv' X X u) := congrArg
        (fun t => (SimplicialCategory.sHomComp X X X).app (op ⦋0⦌)
          (SimplicialCategory.homEquiv' X X (𝟙 X), t)) hu.symm
      _ = SimplicialCategory.homEquiv' X X ((𝟙 X) ≫ u) :=
        (directDG_homEquiv_comp (𝟙 X) u).symm
      _ = SimplicialCategory.homEquiv' X X u := by rw [Category.id_comp]
      _ = q := Equiv.apply_symm_apply _ _
  have hc := dgMappingDirectZModuleVerticesEquivBoundedMorphisms_comp
    K K K (SimplicialCategory.homEquiv' X X (𝟙 X)) q
  rw [hs, Equiv.apply_symm_apply, Category.comp_id] at hc
  exact hc.symm

/-- Forget the direct simplicial enrichment and recover the underlying bounded complex. -/
def directDGToComplexFunctor :
    DirectDGSimplicialCategory ⥤ ComplexCategory where
  obj X := directDGObjectEquiv.symm X
  map {X Y} f :=
    dgMappingDirectZModuleVerticesEquivBoundedMorphisms
      (directDGObjectEquiv.symm X) (directDGObjectEquiv.symm Y)
      (SimplicialCategory.homEquiv' X Y f)
  map_id X := by
    exact dgMappingDirectZModuleVerticesEquivBoundedMorphisms_id
      (directDGObjectEquiv.symm X)
  map_comp {X Y Z} f g := by
    rw [directDG_homEquiv_comp]
    exact dgMappingDirectZModuleVerticesEquivBoundedMorphisms_comp
      (directDGObjectEquiv.symm X)
      (directDGObjectEquiv.symm Y)
      (directDGObjectEquiv.symm Z)
      (SimplicialCategory.homEquiv' X Y f)
      (SimplicialCategory.homEquiv' Y Z g)

/-- The map on each hom-set induced by `directDGToComplexFunctor`, as an equivalence. -/
def directDGToComplexHomEquiv
    (X Y : DirectDGSimplicialCategory) :
    (X ⟶ Y) ≃
      (directDGToComplexFunctor.obj X ⟶
        directDGToComplexFunctor.obj Y) :=
  (SimplicialCategory.homEquiv' X Y).trans
    (dgMappingDirectZModuleVerticesEquivBoundedMorphisms
      (directDGObjectEquiv.symm X) (directDGObjectEquiv.symm Y))

/-- `directDGToComplexFunctor` is fully faithful on the underlying ordinary categories. -/
def directDGToComplexFullyFaithful :
    directDGToComplexFunctor.FullyFaithful where
  preimage {X Y} f := (directDGToComplexHomEquiv X Y).symm f
  map_preimage {X Y} f := by
    exact Equiv.apply_symm_apply (directDGToComplexHomEquiv X Y) f
  preimage_map {X Y} f := by
    exact Equiv.symm_apply_apply (directDGToComplexHomEquiv X Y) f

/-- Every bounded complex is in the essential image of `directDGToComplexFunctor`. -/
@[implicit_reducible]
def directDGToComplexEssSurj :
    directDGToComplexFunctor.EssSurj where
  mem_essImage K :=
    ⟨directDGObjectEquiv K,
      ⟨eqToIso (directDGObjectEquiv.left_inv K)⟩⟩

/-- The underlying ordinary functor from the direct dg simplicial category is an equivalence. -/
noncomputable instance directDGToComplexFunctorIsEquivalence :
    directDGToComplexFunctor.IsEquivalence where
  faithful := directDGToComplexFullyFaithful.faithful
  full := directDGToComplexFullyFaithful.full
  essSurj := directDGToComplexEssSurj

/--
The direct dg simplicial category and bounded complexes are equivalent as ordinary categories.

This statement does not claim compatibility at the level of simplicial enrichments or nerves.
-/
noncomputable def directDGSimplicialCategoryOrdinaryEquivalence :
    DirectDGSimplicialCategory ≌ ComplexCategory :=
  directDGToComplexFunctor.asEquivalence

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
