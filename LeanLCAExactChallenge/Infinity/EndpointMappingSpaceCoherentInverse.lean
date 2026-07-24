/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaceRecognition
import LeanLCAExactChallenge.Infinity.EndpointMappingSpaceKanAssembly
import LeanLCAExactChallenge.Infinity.JoyalSpecialOuterHornDuality
import LeanLCAExactChallenge.Infinity.JoyalParameterizedExtension
import LeanLCAExactChallenge.Infinity.StableEquivalenceTransferFull

/-! # Coherent inverse infrastructure of the coherent endpoint-fiber inverse

The first missing construction is a simplicial section theorem: the chosen object
representatives and counit components must extend simultaneously to a simplicial inverse and
an internal-Hom edge. Pointwise detection of equivalence edges and coherent postcomposition
lifting are independent all-dimensional interfaces. Together they give exactly
`EndpointFiberCoherentQuasiInverseContract`.
-/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge.Infinity

open CategoryTheory CategoryTheory.MonoidalClosed Opposite Simplicial
open CategoryTheory.MorphismProperty
open scoped Bicategory MonoidalCategory MonoidalClosed

/-- Evaluate an edge in a functor quasicategory at a source vertex. -/
def internalHomEdgeApp
    {K Q : SSet.QCat.{u}} {f g : K ⟶ Q}
    (e : SSet.Edge
      (SSet.unitHomEquiv ((ihom K.obj).obj Q.obj) (MonoidalClosed.curry' f.hom))
      (SSet.unitHomEquiv ((ihom K.obj).obj Q.obj) (MonoidalClosed.curry' g.hom)))
    (x : K.obj _⦋0⦌) : SSet.Edge (mapVertex f x) (mapVertex g x) :=
  SSet.Edge.castEndpoints
    (internalHomEvaluationAtVertex_vertex f x).symm
    (internalHomEvaluationAtVertex_vertex g x).symm
    (e.map (internalHomEvaluationAtVertex K.obj Q.obj x))

/-- A simplicial inverse and counit edge realizing the prescribed object and edge choices. -/
structure EndpointFiberCounitSectionData
    {X Y : SSet.QCat.{u}} (F : X ⟶ Y) (choices : EndpointFiberObjectChoice F) where
  inverse : Y ⟶ X
  inverse_obj : ∀ y : Y.obj _⦋0⦌, mapVertex inverse y = choices.preimage y
  counitEdge :
    SSet.Edge
      (SSet.unitHomEquiv ((ihom Y.obj).obj Y.obj)
        (MonoidalClosed.curry' (inverse ≫ F).hom))
      (SSet.unitHomEquiv ((ihom Y.obj).obj Y.obj)
        (MonoidalClosed.curry' ((𝟙 Y : Y ⟶ Y).hom)))
  counitEdge_app : ∀ y : Y.obj _⦋0⦌,
    (internalHomEdgeApp counitEdge y).edge = (choices.counitEdge y).edge
  counitEdge_app_isEquivalence : ∀ y : Y.obj _⦋0⦌,
    EdgeIsEquivalence (internalHomEdgeApp counitEdge y)

/-- First leaf: extend the chosen vertices and counit components to one simplicial section. -/
def EndpointFiberCounitSectionContract : Prop :=
  ∀ {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hX : ∀ x y : X.obj _⦋0⦌, SSet.Quasicategory (endpointFiber X.obj x y))
    (hY : ∀ x y : Y.obj _⦋0⦌, SSet.Quasicategory (endpointFiber Y.obj x y))
    (choices : EndpointFiberObjectChoice F),
    EndpointFiberLocalEquivalenceInput F hX hY →
      Nonempty (EndpointFiberCounitSectionData F choices)

/-- Second leaf: an internal-Hom edge is an equivalence when all vertex evaluations are. -/
def InternalHomPointwiseEquivalenceContract : Prop :=
  ∀ {K Q : SSet.QCat.{u}} {f g : K ⟶ Q}
    (e : SSet.Edge
      (SSet.unitHomEquiv ((ihom K.obj).obj Q.obj) (MonoidalClosed.curry' f.hom))
      (SSet.unitHomEquiv ((ihom K.obj).obj Q.obj) (MonoidalClosed.curry' g.hom))),
    (∀ x : K.obj _⦋0⦌, EdgeIsEquivalence (internalHomEdgeApp e x)) →
      EdgeIsEquivalence e

/-- Third leaf: local endpoint equivalences coherently lift the inverse counit whiskering to a
unit. This is the required postcomposition interface; no precomposition theorem is needed. -/
def EndpointFiberCoherentPostcompositionUnitContract : Prop :=
  ∀ {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hX : ∀ x y : X.obj _⦋0⦌, SSet.Quasicategory (endpointFiber X.obj x y))
    (hY : ∀ x y : Y.obj _⦋0⦌, SSet.Quasicategory (endpointFiber Y.obj x y)),
    EndpointFiberLocalEquivalenceInput F hX hY →
      ∀ (G : Y ⟶ X)
        (counitEdge : SSet.Edge
          (SSet.unitHomEquiv ((ihom Y.obj).obj Y.obj)
            (MonoidalClosed.curry' (G ≫ F).hom))
          (SSet.unitHomEquiv ((ihom Y.obj).obj Y.obj)
            (MonoidalClosed.curry' ((𝟙 Y : Y ⟶ Y).hom)))),
        EdgeIsEquivalence counitEdge →
          ∃ unitEdge : SSet.Edge
            (SSet.unitHomEquiv ((ihom X.obj).obj X.obj)
              (MonoidalClosed.curry' ((𝟙 X : X ⟶ X).hom)))
            (SSet.unitHomEquiv ((ihom X.obj).obj X.obj)
              (MonoidalClosed.curry' (F ≫ G).hom)),
            EdgeIsEquivalence unitEdge

/-- The three independent leaves assemble the tracked coherent quasi-inverse contract. -/
theorem endpointFiberCoherentQuasiInverse_of_decomposition
    (hsection : EndpointFiberCounitSectionContract.{u})
    (hpointwise : InternalHomPointwiseEquivalenceContract.{u})
    (hpost : EndpointFiberCoherentPostcompositionUnitContract.{u}) :
    EndpointFiberCoherentQuasiInverseContract.{u} := by
  intro X Y F hX hY choices hlocal
  obtain ⟨data⟩ := hsection F hX hY choices hlocal
  have hcounit : EdgeIsEquivalence data.counitEdge :=
    hpointwise data.counitEdge data.counitEdge_app_isEquivalence
  obtain ⟨unitEdge, hunit⟩ := hpost F hX hY hlocal data.inverse
    data.counitEdge hcounit
  exact ⟨
    { inverse := data.inverse
      unitEdge := unitEdge
      unitEdge_isEquivalence := hunit
      counitEdge := data.counitEdge
      counitEdge_isEquivalence := hcounit }⟩

structure EndpointFiberCounitSectionExtensionData
    {X Y : SSet.QCat.{u}} (F : X ⟶ Y) (choices : EndpointFiberObjectChoice F) where
  inverse : Y ⟶ X
  inverse_obj : ∀ y : Y.obj _⦋0⦌, mapVertex inverse y = choices.preimage y
  counitEdge :
    SSet.Edge
      (SSet.unitHomEquiv ((ihom Y.obj).obj Y.obj)
        (MonoidalClosed.curry' (inverse ≫ F).hom))
      (SSet.unitHomEquiv ((ihom Y.obj).obj Y.obj)
        (MonoidalClosed.curry' ((𝟙 Y : Y ⟶ Y).hom)))
  counitEdge_app : ∀ y : Y.obj _⦋0⦌,
    (internalHomEdgeApp counitEdge y).edge = (choices.counitEdge y).edge

def EndpointFiberCounitSectionExtensionContract : Prop :=
  ∀ {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hX : ∀ x y : X.obj _⦋0⦌, SSet.Quasicategory (endpointFiber X.obj x y))
    (hY : ∀ x y : Y.obj _⦋0⦌, SSet.Quasicategory (endpointFiber Y.obj x y))
    (choices : EndpointFiberObjectChoice F),
    EndpointFiberLocalEquivalenceInput F hX hY →
      Nonempty (EndpointFiberCounitSectionExtensionData F choices)

theorem edgeIsEquivalence_of_edge_eq
    {X : SSet.{u}} {x₀ x₁ y₀ y₁ : X _⦋0⦌}
    (e : SSet.Edge x₀ x₁) (f : SSet.Edge y₀ y₁)
    (h : e.edge = f.edge) (hf : EdgeIsEquivalence f) : EdgeIsEquivalence e := by
  let f' := SSet.Edge.castEndpoints
    (e.src_eq.symm.trans (h.symm ▸ f.src_eq))
    (e.tgt_eq.symm.trans (h.symm ▸ f.tgt_eq)) f
  have hf' : EdgeIsEquivalence f' := hf.castEndpoints
    (e.src_eq.symm.trans (h.symm ▸ f.src_eq))
    (e.tgt_eq.symm.trans (h.symm ▸ f.tgt_eq))
  have hfe : f' = e := by
    apply SSet.Edge.ext
    simp only [f', SSet.Edge.castEndpoints_edge, h]
  simpa only [hfe] using hf'

noncomputable def EndpointFiberCounitSectionExtensionData.toSectionData
    {X Y : SSet.QCat.{u}} {F : X ⟶ Y} {choices : EndpointFiberObjectChoice F}
    (data : EndpointFiberCounitSectionExtensionData F choices) :
    EndpointFiberCounitSectionData F choices where
  inverse := data.inverse
  inverse_obj := data.inverse_obj
  counitEdge := data.counitEdge
  counitEdge_app := data.counitEdge_app
  counitEdge_app_isEquivalence := by
    intro y
    exact edgeIsEquivalence_of_edge_eq (internalHomEdgeApp data.counitEdge y)
      (choices.counitEdge y) (data.counitEdge_app y) (choices.counitEdge_isEquivalence y)

/-- The missing joint extension interface is sufficient for the frozen contract. -/
theorem endpointFiberCounitSectionContract_of_extension
    (hext : EndpointFiberCounitSectionExtensionContract.{u}) :
    EndpointFiberCounitSectionContract.{u} := by
  intro X Y F hX hY choices hlocal
  obtain ⟨data⟩ := hext F hX hY choices hlocal
  exact ⟨data.toSectionData⟩


private lemma internalHomVertexMap_transpose_app
    {A B Q : SSet.{u}} (a : A ⟶ (ihom B).obj Q) (x : B _⦋0⦌) :
    internalHomVertexMap A Q ((transposeInternalHom a).app _ x) =
      a ≫ internalHomEvaluationAtVertex B Q x := by
  apply MonoidalClosed.curry'_injective
  rw [internalHomVertexMap, MonoidalClosed.curry'_uncurry']
  rw [parameterizedUnitHomEquiv_symm_natural]
  apply MonoidalClosed.uncurry_injective
  unfold transposeInternalHom internalHomEvaluationAtVertex MonoidalClosed.curry'
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    MonoidalClosed.uncurry_curry, MonoidalClosed.uncurry_eq]
  rw [BraidedCategory.braiding_naturality_right_assoc]
  ext U z
  rfl

/-- Second leaf: an internal-Hom edge is an equivalence when all vertex evaluations are. -/
theorem internalHomPointwiseEquivalenceContract :
    InternalHomPointwiseEquivalenceContract.{u} := by
  intro K Q f g e he
  let a : (Δ[1] : SSet.{u}) ⟶ (ihom K.obj).obj Q.obj :=
    SSet.yonedaEquiv.symm e.edge
  let aT : K.obj ⟶ (ihom (Δ[1] : SSet.{u})).obj Q.obj :=
    transposeInternalHom a
  have haT_vertex : ∀ x : K.obj _⦋0⦌,
      EdgeIsEquivalence (SSet.Edge.mk' (SSet.yonedaEquiv
        (internalHomVertexMap (Δ[1] : SSet.{u}) Q.obj (aT.app _ x)))) := by
    intro x
    let ex := internalHomEdgeApp e x
    let ex' := SSet.Edge.castEndpoints ex.src_eq ex.tgt_eq ex
    have hex' : EdgeIsEquivalence ex' :=
      (he x).castEndpoints ex.src_eq ex.tgt_eq
    have hex'_eq : ex' = SSet.Edge.mk' ex.edge := by
      apply SSet.Edge.ext
      simp only [ex', SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]
    have hex : EdgeIsEquivalence (SSet.Edge.mk' ex.edge) := by
      simpa only [hex'_eq] using hex'
    rw [internalHomVertexMap_transpose_app]
    have hedge : SSet.yonedaEquiv
          (a ≫ internalHomEvaluationAtVertex K.obj Q.obj x) = ex.edge := by
      simp only [SSet.yonedaEquiv_comp, a, Equiv.apply_symm_apply, ex,
        internalHomEdgeApp, SSet.Edge.castEndpoints_edge, SSet.Edge.map_edge]
    rw [hedge]
    exact hex
  let eFamily : K.obj ⟶ (equivalenceEdgeInternalHom Q.obj : SSet.{u}) :=
    SSet.Subcomplex.lift aT (by
      rintro U _ ⟨s, rfl⟩ i
      rw [← NatTrans.naturality_apply aT
        (SimplexCategory.const ⦋0⦌ U.unop i).op s]
      exact haT_vertex _)
  letI : SSet.Quasicategory Q.obj := Q.property
  let p := equivalenceIntervalRestrictionToEquivalenceEdges Q.obj
  have hp : (monomorphisms SSet.{u}).rlp p :=
    intervalRestriction_mem_monomorphisms_rlp_of_specialLeftHornFillers
      Q.obj (hasAllSpecialLeftHornFillers_direct Q.obj)
  let sectionMap : (equivalenceEdgeInternalHom Q.obj : SSet.{u}) ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q.obj :=
    sectionOfMonoRLP p hp
  let F : K.obj ⟶
      (ihom (CategoryTheory.nerve EquivalenceInterval.{u})).obj Q.obj :=
    eFamily ≫ sectionMap
  have hFpre : F ≫ internalHomPrecomp equivalenceIntervalInclusion Q.obj = aT := by
    calc
      _ = eFamily ≫ (sectionMap ≫ p) ≫ (equivalenceEdgeInternalHom Q.obj).ι := by
        dsimp only [F, p]
        simp only [Category.assoc]
        rw [equivalenceIntervalRestrictionToEquivalenceEdges_comp_inclusion]
      _ = eFamily ≫ (equivalenceEdgeInternalHom Q.obj).ι := by
        rw [sectionOfMonoRLP_comp]
        simp
      _ = aT := SSet.Subcomplex.lift_ι _ _
  let FT : CategoryTheory.nerve EquivalenceInterval.{u} ⟶
      (ihom K.obj).obj Q.obj := transposeInternalHom F
  have hFTrestrict : equivalenceIntervalInclusion ≫ FT = a := by
    calc
      _ = transposeInternalHom
          (F ≫ internalHomPrecomp equivalenceIntervalInclusion Q.obj) :=
        transposeInternalHom_pre equivalenceIntervalInclusion F
      _ = transposeInternalHom aT := congrArg transposeInternalHom hFpre
      _ = a := transposeInternalHom_transpose a
  have hrestriction : equivalenceIntervalRestriction FT = e.edge := by
    have h := congrArg SSet.yonedaEquiv hFTrestrict
    simpa only [equivalenceIntervalRestriction, equivalenceIntervalInclusion,
      SSet.Edge.map_edge, SSet.yonedaEquiv_comp, a, Equiv.apply_symm_apply] using h
  have he' : EdgeIsEquivalence (SSet.Edge.mk' e.edge) := by
    rw [← hrestriction]
    exact equivalenceIntervalRestriction_isEquivalence FT
  let ec := SSet.Edge.castEndpoints e.src_eq.symm e.tgt_eq.symm
    (SSet.Edge.mk' e.edge)
  have hec : ec = e := by
    apply SSet.Edge.ext
    simp only [ec, SSet.Edge.castEndpoints_edge, SSet.Edge.mk'_edge]
  rw [← hec]
  exact he'.castEndpoints e.src_eq.symm e.tgt_eq.symm


local instance endpointPostcompositionHomCategory (A B : SSet.QCat.{u}) : Category (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- Postcomposition by `F` on the ordinary hom categories of the quasicategory bicategory. -/
def endpointPostcompositionHomFunctor {X Y : SSet.QCat.{u}} (F : X ⟶ Y) :
    (X ⟶ X) ⥤ (X ⟶ Y) where
  obj H := H ≫ F
  map α := α ▷ F
  map_id H := Bicategory.id_whiskerRight H F
  map_comp α β := Bicategory.comp_whiskerRight α β F

/-- The exact missing coherent interface: endpointwise equivalences must make
postcomposition fully faithful on the entire functor hom category. -/
def EndpointFiberPostcompositionFullyFaithfulContract : Prop :=
  ∀ {X Y : SSet.QCat.{u}} (F : X ⟶ Y)
    (hX : ∀ x y : X.obj _⦋0⦌, SSet.Quasicategory (endpointFiber X.obj x y))
    (hY : ∀ x y : Y.obj _⦋0⦌, SSet.Quasicategory (endpointFiber Y.obj x y)),
    EndpointFiberLocalEquivalenceInput F hX hY →
      Nonempty (endpointPostcompositionHomFunctor F).FullyFaithful

/-- The tracked special outer horn and parameterized extension machinery gives the
equivalence interval restriction the right lifting property against every monomorphism. -/
theorem endpointFiberEquivalenceIntervalRestriction_monoRLP
    (Q : SSet.QCat.{u}) (x y : Q.obj _⦋0⦌) :
    (CategoryTheory.MorphismProperty.monomorphisms SSet.{u}).rlp
      (equivalenceIntervalRestrictionToEquivalenceEdges (endpointFiber Q.obj x y)) := by
  letI : SSet.Quasicategory Q.obj := Q.property
  letI : SSet.KanComplex (endpointFiber Q.obj x y) := endpointFiber_kan Q.obj x y
  letI : SSet.Quasicategory (endpointFiber Q.obj x y) := inferInstance
  exact intervalRestriction_mem_monomorphisms_rlp_of_specialLeftHornFillers
    (endpointFiber Q.obj x y)
    (hasAllSpecialLeftHornFillers_direct (endpointFiber Q.obj x y))

/-- Full faithfulness of coherent postcomposition is exactly sufficient to lift the
counit inverse to the required unit equivalence edge. -/
theorem endpointFiberCoherentPostcompositionUnit_of_fullyFaithful
    (hpost : EndpointFiberPostcompositionFullyFaithfulContract.{u}) :
    EndpointFiberCoherentPostcompositionUnitContract.{u} := by
  intro X Y F hX hY hlocal G counitEdge hcounit
  let counit : G ≫ F ≅ 𝟙 Y :=
    twoIsoOfInternalHomEquivalenceEdge counitEdge hcounit
  let imageUnit : (endpointPostcompositionHomFunctor F).obj (𝟙 X) ≅
      (endpointPostcompositionHomFunctor F).obj (F ≫ G) :=
    Bicategory.leftUnitor F ≪≫ (Bicategory.rightUnitor F).symm ≪≫
      Bicategory.whiskerLeftIso F counit.symm ≪≫ (α_ F G F).symm
  let hfullyFaithful := (hpost F hX hY hlocal).some
  let unit : (𝟙 X) ≅ F ≫ G :=
    hfullyFaithful.preimageIso imageUnit
  exact ⟨internalHomEdgeOfTwoIso unit, internalHomEdgeOfTwoIso_isEquivalence unit⟩

/-- The proved pointwise detection theorem reduces recognition to the two remaining coherent
construction interfaces. -/
theorem endpointFiberRecognition_of_sectionExtension_and_fullyFaithful
    (hsection : EndpointFiberCounitSectionExtensionContract.{u})
    (hpost : EndpointFiberPostcompositionFullyFaithfulContract.{u}) :
    EndpointFiberRecognitionContract.{u} :=
  endpointFiberRecognition_of_coherentQuasiInverse
    (endpointFiberCoherentQuasiInverse_of_decomposition
      (endpointFiberCounitSectionContract_of_extension hsection)
      internalHomPointwiseEquivalenceContract
      (endpointFiberCoherentPostcompositionUnit_of_fullyFaithful hpost))

end LeanLCAExactChallenge.Infinity
