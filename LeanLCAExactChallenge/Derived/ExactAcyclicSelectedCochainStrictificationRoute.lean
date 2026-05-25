import LeanLCAExactChallenge.Derived.StrictRealizationDirectSourceStableRoute

/-!
W847 names the exact-acyclic selected-cochain strictification boundary feeding
the W783/W846 direct-source stable route.

The boundary is intentionally local to a distinguished triangle and asks for a
standard mapping-cone presentation whose selected target complex is strictly
exact acyclic. It avoids the over-strong unrestricted endpoint strictification
principle refuted in `ContractibleTail`.
-/

set_option autoImplicit false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/--
Cochain-level data for a chosen exact-acyclic mapping-cone presentation of one
distinguished triangle.
-/
structure ExactAcyclicTrianglehIso13SelectedCochainPayload
    [HasZeroObject C] [HasBinaryBiproducts C]
    (T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))) where
  selectedSource : CochainComplex C ℤ
  selectedTarget : CochainComplex C ℤ
  selectedMap : selectedSource ⟶ selectedTarget
  triangleSourceIso :
    (CochainComplex.mappingCone.triangleh selectedMap).obj₁ ≅ T.obj₁
  triangleConeIso :
    (CochainComplex.mappingCone.triangleh selectedMap).obj₃ ≅ T.obj₃
  triangleComm :
    (CochainComplex.mappingCone.triangleh selectedMap).mor₃ ≫
        (shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) (1 : ℤ)).map
          triangleSourceIso.hom =
      triangleConeIso.hom ≫ T.mor₃
  targetExactAcyclic : exactAcyclic C selectedTarget

/--
The exact-acyclic per-triangle strictification principle. This is equivalent
to the W783 strict realization input, but exposes the selected cochain payload
as the proof obligation to construct.
-/
abbrev exactAcyclicTrianglehIso13SelectedCochainStrictification
    [HasZeroObject C] [HasBinaryBiproducts C] : Prop :=
  ∀ {T : Pretriangulated.Triangle (HomotopyCategory C (ComplexShape.up ℤ))},
    T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) →
    exactAcyclicHomotopyObject C T.obj₁ →
    exactAcyclicHomotopyObject C T.obj₃ →
    Nonempty (ExactAcyclicTrianglehIso13SelectedCochainPayload C T)

/-- The selected cochain payload supplies the W783 strict-realization input. -/
theorem exactAcyclicHomotopyObjectTrianglehIso13Realization_of_selected_cochain
    [HasZeroObject C] [HasBinaryBiproducts C]
    (strictify : exactAcyclicTrianglehIso13SelectedCochainStrictification C) :
    exactAcyclicHomotopyObjectTrianglehIso13Realization C := by
  intro T hT h₁ h₃
  rcases strictify hT h₁ h₃ with ⟨payload⟩
  exact
    ⟨payload.selectedSource, payload.selectedTarget, payload.selectedMap,
      payload.triangleSourceIso, payload.triangleConeIso,
      payload.triangleComm, payload.targetExactAcyclic⟩

/--
The existing strict-realization input itself supplies the selected cochain
payload; choose the W783 source and target as the selected complexes.
-/
theorem exactAcyclicTrianglehIso13SelectedCochainStrictification_of_realization
    [HasZeroObject C] [HasBinaryBiproducts C]
    (realize : exactAcyclicHomotopyObjectTrianglehIso13Realization C) :
    exactAcyclicTrianglehIso13SelectedCochainStrictification C := by
  intro T hT h₁ h₃
  rcases realize hT h₁ h₃ with ⟨K, L, f, e₁, e₃, comm, hL⟩
  exact ⟨{
    selectedSource := K
    selectedTarget := L
    selectedMap := f
    triangleSourceIso := e₁
    triangleConeIso := e₃
    triangleComm := comm
    targetExactAcyclic := hL }⟩

/--
The W847 selected-cochain strictification is exactly the W783
strict-realization input, stated with a named per-triangle payload.
-/
theorem exactAcyclicTrianglehIso13SelectedCochainStrictification_iff_realization
    [HasZeroObject C] [HasBinaryBiproducts C] :
    exactAcyclicTrianglehIso13SelectedCochainStrictification C ↔
      exactAcyclicHomotopyObjectTrianglehIso13Realization C :=
  ⟨exactAcyclicHomotopyObjectTrianglehIso13Realization_of_selected_cochain C,
    exactAcyclicTrianglehIso13SelectedCochainStrictification_of_realization C⟩

namespace Dbounded

/-- W847 selected-cochain strictification input for MetrizableLCA. -/
abbrev MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847 :
    Prop :=
  exactAcyclicTrianglehIso13SelectedCochainStrictification MetrizableLCA.{0}

/-- W847 selected-cochain strictification converted to W783 strict realization. -/
theorem trianglehRealizationOfSelectedCochainStrictificationW847
    (strictify :
      MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847) :
    MetrizableExactAcyclicHomotopyObjectTrianglehIso13RealizationW783 :=
  exactAcyclicHomotopyObjectTrianglehIso13Realization_of_selected_cochain
    MetrizableLCA.{0} strictify

/--
W847 closed-map data using selected-cochain strictification instead of the raw
W783 strict-realization premise.
-/
structure
    MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735
  selectedCochainStrictification :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847

/--
W847 closed-embedding data using selected-cochain strictification instead of
the raw W783 strict-realization premise.
-/
structure
    MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847 :
    Type 2 where
  exactInputs :
    MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735
  selectedCochainStrictification :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847

/-- W847 closed-map data converted to the W846 strict-realization route. -/
noncomputable def closedMapStrictRealizationDataOfSelectedCochainW847
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedMapStrictRealizationDirectSourceStableRouteDataW846
    where
  exactInputs := data.exactInputs
  trianglehRealization :=
    trianglehRealizationOfSelectedCochainStrictificationW847
      data.selectedCochainStrictification

/-- W847 closed-embedding data converted to the W846 strict-realization route. -/
noncomputable def closedEmbeddingStrictRealizationDataOfSelectedCochainW847
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedEmbeddingStrictRealizationDirectSourceStableRouteDataW846
    where
  exactInputs := data.exactInputs
  trianglehRealization :=
    trianglehRealizationOfSelectedCochainStrictificationW847
      data.selectedCochainStrictification

/-- W847 closed-map data converted to the W845 iso-closure direct-source route. -/
noncomputable def closedMapIsoClosureDataOfSelectedCochainW847
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedMapIsoClosureDirectSourceStableRouteDataW845 :=
  closedMapIsoClosureDataOfStrictDirectSourceW846
    (closedMapStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-embedding data converted to the W845 iso-closure direct-source route. -/
noncomputable def closedEmbeddingIsoClosureDataOfSelectedCochainW847
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedEmbeddingIsoClosureDirectSourceStableRouteDataW845 :=
  closedEmbeddingIsoClosureDataOfStrictDirectSourceW846
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-map data converted to the W844 target-isomorphism surface. -/
noncomputable def closedMapTargetIsoDataOfSelectedCochainW847
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedMapTargetIsoDirectSourceStableRouteDataW844 :=
  closedMapTargetIsoDataOfStrictDirectSourceW846
    (closedMapStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-embedding data converted to the W844 target-isomorphism surface. -/
noncomputable def closedEmbeddingTargetIsoDataOfSelectedCochainW847
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedEmbeddingTargetIsoDirectSourceStableRouteDataW844 :=
  closedEmbeddingTargetIsoDataOfStrictDirectSourceW846
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-map data converted to the W839 target homology-zero surface. -/
noncomputable def closedMapTargetHomologyZeroDataOfSelectedCochainW847
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedMapTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedMapTargetHomologyZeroDataOfStrictDirectSourceW846
    (closedMapStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-embedding data converted to the W839 target homology-zero surface. -/
noncomputable def closedEmbeddingTargetHomologyZeroDataOfSelectedCochainW847
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    MetrizableClosedEmbeddingTargetHomologyZeroStrictRealizationLeftCalculusDataW839 :=
  closedEmbeddingTargetHomologyZeroDataOfStrictDirectSourceW846
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-map route preserves the W846 direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedMapSelectedCochainW847
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedMapStrictDirectSourceW846
    (closedMapStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-embedding route preserves the W846 direct bounded left calculus. -/
theorem directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainW847
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    (boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions :=
  directBoundedLeftCalculusOfClosedEmbeddingStrictDirectSourceW846
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-map route derives all stable fields through W846. -/
noncomputable def remainingStableFieldsOfClosedMapSelectedCochainW847
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedMapW840
        (closedMapTargetHomologyZeroDataOfSelectedCochainW847 data)) :=
  remainingStableFieldsOfClosedMapStrictDirectSourceW846
    (closedMapStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-embedding route derives all stable fields through W846. -/
noncomputable def remainingStableFieldsOfClosedEmbeddingSelectedCochainW847
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    Dbounded.MetrizableRemainingStableSemanticFields
      (targetHomologyZeroLeftCalculusFieldsOfClosedEmbeddingW840
        (closedEmbeddingTargetHomologyZeroDataOfSelectedCochainW847 data)) :=
  remainingStableFieldsOfClosedEmbeddingStrictDirectSourceW846
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-map stable package from selected-cochain strictification data. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedMapSelectedCochainW847
    (data :
      MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedMapStrictDirectSourceW846
    (closedMapStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 closed-embedding stable package from selected-cochain strictification data. -/
noncomputable def boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainW847
    (data :
      MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847) :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  boundedDerivedInfinityCategoryOfClosedEmbeddingStrictDirectSourceW846
    (closedEmbeddingStrictRealizationDataOfSelectedCochainW847 data)

/-- W847 has one bundled route input: the selected-cochain direct-source data. -/
def selectedCochainDirectSourceStableRouteInputNamesW847 : List String :=
  ["W847 exact-acyclic selected-cochain direct-source stable route data"]

/-- W847 keeps the route to one bundled input. -/
theorem selectedCochainDirectSourceStableRouteInputNamesW847_count :
    Dbounded.selectedCochainDirectSourceStableRouteInputNamesW847.length =
      1 :=
  rfl

/--
Expanded W847 requirements are the W735 exact-input branch and the precise
selected-cochain strictification theorem replacing W783's raw Prop.
-/
def selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847 :
    List String :=
  ["W735 closed-map or closed-embedding exact inputs, including W721 data",
    "W847 exact-acyclic selected-cochain strictification: every relevant\
      distinguished triangle has a standard mapping-cone representative with\
      endpoint isomorphisms and strictly exact-acyclic selected target"]

/-- The W847 expanded stable route has two concrete requirements. -/
theorem selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847_count :
    Dbounded.selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847.length =
      2 :=
  rfl

/-- Current checked W847 state for the selected-cochain boundary. -/
structure MetrizableSelectedCochainDirectSourceStableRouteStateW847 :
    Type where
  seed : String
  declarations : List String
  boundaryResult : String
  conversionResult : String
  leftCalculusResult : String
  stablePackageResult : String
  derivedInputs : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

/-- Current checked W847 state. -/
def currentMetrizableSelectedCochainDirectSourceStableRouteStateW847 :
    Dbounded.MetrizableSelectedCochainDirectSourceStableRouteStateW847
    where
  seed := "w847-exact-acyclic-selected-cochain-direct-source-stable-route"
  declarations :=
    ["ExactAcyclicTrianglehIso13SelectedCochainPayload",
      "exactAcyclicTrianglehIso13SelectedCochainStrictification",
      "exactAcyclicHomotopyObjectTrianglehIso13Realization_of_selected_cochain",
      "exactAcyclicTrianglehIso13SelectedCochainStrictification_of_realization",
      "exactAcyclicTrianglehIso13SelectedCochainStrictification_iff_realization",
      "MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847",
      "trianglehRealizationOfSelectedCochainStrictificationW847",
      "MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847",
      "MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847",
      "closedMapStrictRealizationDataOfSelectedCochainW847",
      "closedEmbeddingStrictRealizationDataOfSelectedCochainW847",
      "closedMapIsoClosureDataOfSelectedCochainW847",
      "closedEmbeddingIsoClosureDataOfSelectedCochainW847",
      "closedMapTargetIsoDataOfSelectedCochainW847",
      "closedEmbeddingTargetIsoDataOfSelectedCochainW847",
      "closedMapTargetHomologyZeroDataOfSelectedCochainW847",
      "closedEmbeddingTargetHomologyZeroDataOfSelectedCochainW847",
      "directBoundedLeftCalculusOfClosedMapSelectedCochainW847",
      "directBoundedLeftCalculusOfClosedEmbeddingSelectedCochainW847",
      "remainingStableFieldsOfClosedMapSelectedCochainW847",
      "remainingStableFieldsOfClosedEmbeddingSelectedCochainW847",
      "boundedDerivedInfinityCategoryOfClosedMapSelectedCochainW847",
      "boundedDerivedInfinityCategoryOfClosedEmbeddingSelectedCochainW847",
      "selectedCochainDirectSourceStableRouteInputNamesW847",
      "selectedCochainDirectSourceStableRouteInputNamesW847_count",
      "selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847",
      "selectedCochainDirectSourceStableRouteExpandedRequiredFieldNamesW847_count"]
  boundaryResult :=
    "proved: the exact-acyclic selected-cochain payload is equivalent to\
      W783's strict realization input and exposes the per-triangle theorem to\
      construct"
  conversionResult :=
    "proved: W847 selected-cochain strictification feeds W846 strict-realization direct-source data"
  leftCalculusResult :=
    "proved: W847 preserves W846 direct bounded left calculus through the\
      selected-cochain conversion"
  stablePackageResult :=
    "proved: W847 assembles the W846 stable package from selected-cochain strictification data"
  derivedInputs :=
    ["W783 exact-acyclic homotopy-object strict realization data from W847",
      "W651 exact-acyclic iso-closure strict realization data through W846",
      "W784 target-isomorphism realization data through W846/W845",
      "W790 target homology-zero realization data through W846/W845",
      "finite-limit, finite-colimit, pretriangulated, and triangulated fields\
        through W846/W842"]
  remainingInputs :=
    ["construct W735 closed-map or closed-embedding exact inputs, including W721\
        localized-right-adjoint payload and W722 source-triangulation payload",
      "prove W847 selected-cochain strictification for MetrizableLCA using\
        hypotheses stronger than the false unrestricted endpoint strictification",
      "produce the immutable original four-task completion witness and clean\
        review packet only after concrete task-4 inputs are solved"]
  productSuccessClaimed := false

theorem currentW847SelectedCochainDirectSourceStableRoute_productSuccess :
    (let state :=
        currentMetrizableSelectedCochainDirectSourceStableRouteStateW847;
      state.productSuccessClaimed) =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
