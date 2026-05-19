import LeanLCAExactChallenge.Derived.Bounded

/-!
Selected cochain restricted-isomorphism payload guard.

If the endpoint bounded representatives are related to the selected mapping-cone
source and cone by actual cochain-complex isomorphisms, then the existing
`boundedHomotopyObjectTrianglehIso13Realization` consumer is discharged. The weaker
case of mere homotopy-category isomorphisms is intentionally not asserted here.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

omit [QuillenExactCategory C] in
/-- Selected cochain data for one distinguished triangle. -/
structure BoundedTrianglehIso13SelectedCochainPayload
    [HasZeroObject C] [HasBinaryBiproducts C]
    (T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))) where
  sourceRepresentative : CochainComplex C ℤ
  coneRepresentative : CochainComplex C ℤ
  selectedSource : CochainComplex C ℤ
  selectedTarget : CochainComplex C ℤ
  selectedMap : selectedSource ⟶ selectedTarget
  triangleSourceIso :
    (CochainComplex.mappingCone.triangleh selectedMap).obj₁ ≅ T.obj₁
  triangleConeIso :
    (CochainComplex.mappingCone.triangleh selectedMap).obj₃ ≅ T.obj₃
  sourceIso : sourceRepresentative ≅ selectedSource
  coneIso : coneRepresentative ≅ CochainComplex.mappingCone selectedMap
  triangleComm :
    (CochainComplex.mappingCone.triangleh selectedMap).mor₃ ≫
        (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map
          triangleSourceIso.hom =
      triangleConeIso.hom ≫ T.mor₃
  sourceBounded : boundedCochainComplex C sourceRepresentative
  coneBounded : boundedCochainComplex C coneRepresentative

omit [QuillenExactCategory C] in
/-- A per-triangle selected-cochain strictification theorem shape. -/
abbrev boundedTrianglehIso13SelectedCochainStrictification
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    boundedHomotopyObject C T.obj₁ →
    boundedHomotopyObject C T.obj₃ →
    Nonempty (BoundedTrianglehIso13SelectedCochainPayload C T)

omit [QuillenExactCategory C] in
/-- A restricted endpoint payload with strict cochain-complex isomorphisms. -/
abbrev boundedTrianglehIso13RestrictedEndpointCochainIsoPayload
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    boundedHomotopyObject C T.obj₁ →
    boundedHomotopyObject C T.obj₃ →
    ∃ (Ksrc Kcone K L : CochainComplex C ℤ) (f : K ⟶ L)
      (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
      (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃),
        (CochainComplex.mappingCone.triangleh f).mor₃ ≫
            (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
          e₃.hom ≫ T.mor₃ ∧
        boundedCochainComplex C Ksrc ∧
        boundedCochainComplex C Kcone ∧
        Nonempty (Ksrc ≅ K) ∧
        Nonempty (Kcone ≅ CochainComplex.mappingCone f)

omit [QuillenExactCategory C] in
/-- Local copy of the cochain-data strictification shape used for direct comparison. -/
abbrev boundedTrianglehIso13CochainDataStrictification_w114
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    boundedHomotopyObject C T.obj₁ →
    boundedHomotopyObject C T.obj₃ →
    ∃ (Ksrc Kcone K L : CochainComplex C ℤ) (f : K ⟶ L)
      (e₁ : (CochainComplex.mappingCone.triangleh f).obj₁ ≅ T.obj₁)
      (e₃ : (CochainComplex.mappingCone.triangleh f).obj₃ ≅ T.obj₃)
      (_eK : Ksrc ≅ K) (_eCone : Kcone ≅ CochainComplex.mappingCone f),
        (CochainComplex.mappingCone.triangleh f).mor₃ ≫
            (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map e₁.hom =
          e₃.hom ≫ T.mor₃ ∧
        boundedCochainComplex C Ksrc ∧
        boundedCochainComplex C Kcone

omit [QuillenExactCategory C] in
/-- The restricted cochain-isomorphism payload constructs the named selected payload. -/
theorem boundedTrianglehIso13SelectedCochainStrictification_of_restricted_endpoint_cochain_isos
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C) :
    boundedTrianglehIso13SelectedCochainStrictification C := by
  intro T hT h₁ h₃
  rcases strictify hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, comm, hKsrc, hKcone, hK, hCone⟩
  exact ⟨{
    sourceRepresentative := Ksrc
    coneRepresentative := Kcone
    selectedSource := K
    selectedTarget := L
    selectedMap := f
    triangleSourceIso := e₁
    triangleConeIso := e₃
    sourceIso := hK.some
    coneIso := hCone.some
    triangleComm := comm
    sourceBounded := hKsrc
    coneBounded := hKcone }⟩

omit [QuillenExactCategory C] in
/-- The selected payload is strong enough for the current bounded strict-realization consumer. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_selected_cochain_payload_w114
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13SelectedCochainStrictification C) :
    boundedHomotopyObjectTrianglehIso13Realization C := by
  intro T hT h₁ h₃
  rcases strictify hT h₁ h₃ with ⟨payload⟩
  exact
    ⟨payload.selectedSource, payload.selectedTarget, payload.selectedMap,
      payload.triangleSourceIso, payload.triangleConeIso, payload.triangleComm,
      (boundedCochainComplex C).prop_of_iso payload.sourceIso payload.sourceBounded,
      (boundedCochainComplex C).prop_of_iso payload.coneIso payload.coneBounded⟩

omit [QuillenExactCategory C] in
/-- Direct restricted-hypothesis route to the existing bounded strict-realization input. -/
theorem boundedHomotopyObjectTrianglehIso13Realization_of_restricted_endpoint_cochain_isos
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C) :
    boundedHomotopyObjectTrianglehIso13Realization C :=
  boundedHomotopyObjectTrianglehIso13Realization_of_selected_cochain_payload_w114 C
    (boundedTrianglehIso13SelectedCochainStrictification_of_restricted_endpoint_cochain_isos
      C strictify)

omit [QuillenExactCategory C] in
/-- The restricted endpoint-cochain-isomorphism payload gives the cochain-data shape. -/
theorem boundedTrianglehIso13CochainDataStrictification_of_restricted_endpoint_cochain_isos_w114
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C) :
    boundedTrianglehIso13CochainDataStrictification_w114 C := by
  intro T hT h₁ h₃
  rcases strictify hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, comm, hKsrc, hKcone, hK, hCone⟩
  exact ⟨Ksrc, Kcone, K, L, f, e₁, e₃, hK.some, hCone.some, comm, hKsrc, hKcone⟩

omit [QuillenExactCategory C] in
/-- Conversely, cochain-data strictification gives the restricted payload. -/
theorem boundedTrianglehIso13RestrictedEndpointCochainIsoPayload_of_cochain_data_w114
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : boundedTrianglehIso13CochainDataStrictification_w114 C) :
    boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C := by
  intro T hT h₁ h₃
  rcases strictify hT h₁ h₃ with
    ⟨Ksrc, Kcone, K, L, f, e₁, e₃, eK, eCone, comm, hKsrc, hKcone⟩
  exact ⟨Ksrc, Kcone, K, L, f, e₁, e₃, comm, hKsrc, hKcone, ⟨eK⟩, ⟨eCone⟩⟩

omit [QuillenExactCategory C] in
/-- The restricted cochain-isomorphism formulation and the cochain-data formulation agree. -/
theorem boundedTrianglehIso13RestrictedEndpointCochainIsoPayload_iff_cochain_data_w114
    [HasZeroObject C] [HasBinaryBiproducts C] :
    boundedTrianglehIso13RestrictedEndpointCochainIsoPayload C ↔
      boundedTrianglehIso13CochainDataStrictification_w114 C := by
  constructor
  · exact boundedTrianglehIso13CochainDataStrictification_of_restricted_endpoint_cochain_isos_w114 C
  · exact boundedTrianglehIso13RestrictedEndpointCochainIsoPayload_of_cochain_data_w114 C

#check BoundedTrianglehIso13SelectedCochainPayload
#check boundedTrianglehIso13SelectedCochainStrictification
#check boundedTrianglehIso13RestrictedEndpointCochainIsoPayload
#check boundedTrianglehIso13CochainDataStrictification_w114
#check boundedHomotopyObjectTrianglehIso13Realization_of_restricted_endpoint_cochain_isos
#check boundedTrianglehIso13RestrictedEndpointCochainIsoPayload_iff_cochain_data_w114

end LeanLCAExactChallenge
