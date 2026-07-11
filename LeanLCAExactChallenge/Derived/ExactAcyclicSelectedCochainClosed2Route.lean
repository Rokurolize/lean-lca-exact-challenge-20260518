import LeanLCAExactChallenge.Derived.ExactAcyclicSelectedCochainStrictificationRoute

/-!
W848 identifies the exact middle-object closure needed after W847.

The selected-cochain payload is not another semantic input once the
exact-acyclic homotopy-object predicate is closed in the middle object and
exact acyclicity is invariant under homotopy equivalence: mathlib's
distinguished-triangle presentation supplies the selected source, target, and
endpoint triangle isomorphisms, and the closed₂ witness plus invariance proves
the selected target is strictly exact acyclic.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

variable (C : Type u) [Category.{v} C] [Preadditive C] [QuillenExactCategory C]

/--
Exact-acyclic middle-object closure plus homotopy-equivalence invariance
constructs the W847 selected-cochain strictification payload directly from the
distinguished-triangle mapping-cone presentation.
-/
theorem exactAcyclicTrianglehIso13SelectedCochainStrictification_of_closed2_homotopyEquivInvariance
    [HasZeroObject C] [HasBinaryBiproducts C]
    (closed2 : (exactAcyclicHomotopyObject C).IsTriangulatedClosed₂)
    (invariance : ExactAcyclicHomotopyEquivInvarianceInput C) :
    exactAcyclicTrianglehIso13SelectedCochainStrictification C := by
  letI : (exactAcyclicHomotopyObject C).IsTriangulatedClosed₂ := closed2
  letI : (exactAcyclicHomotopyObject C).IsClosedUnderIsomorphisms :=
    exactAcyclicHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance
      C invariance
  intro T hT h₁ h₃
  have h₂ : (exactAcyclicHomotopyObject C).isoClosure T.obj₂ :=
    ObjectProperty.ext_of_isTriangulatedClosed₂'
      (P := exactAcyclicHomotopyObject C) T hT h₁ h₃
  rcases h₂ with ⟨X₂, hX₂, ⟨eX₂⟩⟩
  have hT₂ : exactAcyclicHomotopyObject C T.obj₂ :=
    (exactAcyclicHomotopyObject C).prop_of_iso eX₂.symm hX₂
  rcases hT with ⟨K, L, f, ⟨e⟩⟩
  have hSelectedTarget :
      exactAcyclicHomotopyObject C (CochainComplex.mappingCone.triangleh f).obj₂ :=
    (exactAcyclicHomotopyObject C).prop_of_iso
      (Pretriangulated.Triangle.π₂.mapIso e) hT₂
  have hL : exactAcyclic C L := by
    exact hSelectedTarget
  exact ⟨{
    selectedSource := K
    selectedTarget := L
    selectedMap := f
    triangleSourceIso := (Pretriangulated.Triangle.π₁.mapIso e).symm
    triangleConeIso := (Pretriangulated.Triangle.π₃.mapIso e).symm
    triangleComm := by
      exact e.inv.comm₃
    targetExactAcyclic := hL }⟩

namespace Dbounded

/-- W848 MetrizableLCA alias for exact-acyclic homotopy-object middle closure. -/
abbrev MetrizableExactAcyclicHomotopyObjectClosed2W848 :
    Prop :=
  (exactAcyclicHomotopyObject MetrizableLCA.{0}).IsTriangulatedClosed₂

/--
W848 generic MetrizableLCA route: exact-acyclic Closed₂ and homotopy
invariance suffice to construct W847 selected-cochain strictification.
-/
theorem selectedCochainStrictificationOfClosed2HomotopyInvarianceW848
    (closed2 : MetrizableExactAcyclicHomotopyObjectClosed2W848)
    (invariance : ExactAcyclicHomotopyEquivInvarianceInput MetrizableLCA.{0}) :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847 :=
  exactAcyclicTrianglehIso13SelectedCochainStrictification_of_closed2_homotopyEquivInvariance
    MetrizableLCA.{0} closed2 invariance

/-- W848 derives the homotopy-invariance half from closed-map W735 exact inputs. -/
theorem homotopyEquivInvarianceOfClosedMapExactInputsW848
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735) :
    ExactAcyclicHomotopyEquivInvarianceInput MetrizableLCA.{0} :=
  exactAcyclicHomotopyEquivInvarianceInput_of_homologyDetection
    MetrizableLCA.{0}
    (homologyDetectionOfClosedMapExactInputsW812 comparisonIso exactInputs)

/--
W848 closed-map route: W735 exact inputs supply homotopy invariance, so the
remaining W847 selected-cochain step is exact-acyclic Closed₂.
-/
theorem selectedCochainStrictificationOfClosedMapExactInputsClosed2W848
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735)
    (closed2 : MetrizableExactAcyclicHomotopyObjectClosed2W848) :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847 :=
  selectedCochainStrictificationOfClosed2HomotopyInvarianceW848 closed2
    (homotopyEquivInvarianceOfClosedMapExactInputsW848 comparisonIso exactInputs)

/-- W848 derives the homotopy-invariance half from closed-embedding W735 exact inputs. -/
theorem homotopyEquivInvarianceOfClosedEmbeddingExactInputsW848
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735) :
    ExactAcyclicHomotopyEquivInvarianceInput MetrizableLCA.{0} :=
  exactAcyclicHomotopyEquivInvarianceInput_of_homologyDetection
    MetrizableLCA.{0}
    (homologyDetectionOfClosedEmbeddingExactInputsW812 comparisonIso exactInputs)

/--
W848 closed-embedding route: W735 exact inputs supply homotopy invariance, so
the remaining W847 selected-cochain step is exact-acyclic Closed₂.
-/
theorem selectedCochainStrictificationOfClosedEmbeddingExactInputsClosed2W848
    (comparisonIso :
      ∀ S : ShortComplex MetrizableLCA.{0},
        IsIso (leftRightHomologyComparison_of_metrizableKernelCokernelW736 S))
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735)
    (closed2 : MetrizableExactAcyclicHomotopyObjectClosed2W848) :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847 :=
  selectedCochainStrictificationOfClosed2HomotopyInvarianceW848 closed2
    (homotopyEquivInvarianceOfClosedEmbeddingExactInputsW848 comparisonIso exactInputs)

/--
W848 kernel/cokernel-conditioned route: W681 supplies exact-acyclic
homotopy-object Closed2 once W839 has produced HasHomology for every
MetrizableLCA cochain complex.
-/
theorem closed2OfKernelCokernelConditionedW848
    (kernelCokernelTopology :
      MetrizableExactAtKernelCokernelConditionedTopologyInputs) :
    MetrizableExactAcyclicHomotopyObjectClosed2W848 :=
  metrizableExactAcyclicHomotopyObjectClosed2_of_kernelCokernelConditionedW681
    cochainHasHomology_of_comparisonBijectivityW839
    kernelCokernelTopology

/--
W848 closed-map route with the Closed2 leaf discharged by the
kernel/cokernel-conditioned W681 topology input and W831 comparison
bijectivity.
-/
theorem selectedCochainStrictificationOfClosedMapExactInputsKernelCokernelConditionedW848
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735)
    (kernelCokernelTopology :
      MetrizableExactAtKernelCokernelConditionedTopologyInputs) :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847 :=
  selectedCochainStrictificationOfClosedMapExactInputsClosed2W848
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs
    (closed2OfKernelCokernelConditionedW848 kernelCokernelTopology)

/--
W848 closed-embedding route with the Closed2 leaf discharged by the
kernel/cokernel-conditioned W681 topology input and W831 comparison
bijectivity.
-/
theorem selectedCochainStrictificationOfClosedEmbeddingExactInputsKernelCokernelConditionedW848
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735)
    (kernelCokernelTopology :
      MetrizableExactAtKernelCokernelConditionedTopologyInputs) :
    MetrizableExactAcyclicTrianglehIso13SelectedCochainStrictificationW847 :=
  selectedCochainStrictificationOfClosedEmbeddingExactInputsClosed2W848
    universalLeftRightComparisonIso_of_comparisonBijectivityW831
    exactInputs
    (closed2OfKernelCokernelConditionedW848 kernelCokernelTopology)

/--
W848 closed-map W847 data assembled from W735 exact inputs plus the W681
kernel/cokernel-conditioned topology input.
-/
noncomputable def closedMapSelectedCochainDataOfKernelCokernelConditionedW848
    (exactInputs :
      MetrizableWppClosedMapCategoryHomologyInstanceConcreteLeafInputsW735)
    (kernelCokernelTopology :
      MetrizableExactAtKernelCokernelConditionedTopologyInputs) :
    MetrizableClosedMapExactAcyclicSelectedCochainDirectSourceStableRouteDataW847
    where
  exactInputs := exactInputs
  selectedCochainStrictification :=
    selectedCochainStrictificationOfClosedMapExactInputsKernelCokernelConditionedW848
      exactInputs
      kernelCokernelTopology

/--
W848 closed-embedding W847 data assembled from W735 exact inputs plus the W681
kernel/cokernel-conditioned topology input.
-/
noncomputable def closedEmbeddingSelectedCochainDataOfKernelCokernelConditionedW848
    (exactInputs :
      MetrizableWppClosedEmbeddingCategoryHomologyInstanceConcreteLeafInputsW735)
    (kernelCokernelTopology :
      MetrizableExactAtKernelCokernelConditionedTopologyInputs) :
    MetrizableClosedEmbeddingExactAcyclicSelectedCochainDirectSourceStableRouteDataW847
    where
  exactInputs := exactInputs
  selectedCochainStrictification :=
    selectedCochainStrictificationOfClosedEmbeddingExactInputsKernelCokernelConditionedW848
      exactInputs
      kernelCokernelTopology

def selectedCochainClosed2RouteInputNamesW848 : List String :=
  ["exact-acyclic homotopy-object Closed₂ for MetrizableLCA",
    "universal IsIso for every MetrizableLCA left-right homology comparison",
    "one W735 closed-map or closed-embedding exact-input branch"]

theorem selectedCochainClosed2RouteInputNamesW848_count :
    selectedCochainClosed2RouteInputNamesW848.length = 3 :=
  rfl

def selectedCochainKernelCokernelConditionedRouteInputNamesW848 : List String :=
  ["MetrizableExactAtKernelCokernelConditionedTopologyInputs",
    "one W735 closed-map or closed-embedding exact-input branch"]

theorem selectedCochainKernelCokernelConditionedRouteInputNamesW848_count :
    selectedCochainKernelCokernelConditionedRouteInputNamesW848.length = 2 :=
  rfl

structure MetrizableSelectedCochainClosed2RouteStateW848 :
    Type where
  seed : String
  declarations : List String
  selectedPayloadResult : String
  w735InvarianceResult : String
  rejectedRoutes : List String
  remainingInputs : List String
  productSuccessClaimed : Bool

def currentMetrizableSelectedCochainClosed2RouteStateW848 :
    MetrizableSelectedCochainClosed2RouteStateW848
    where
  seed := "w848-exact-selected-cochain-closed2-route"
  declarations :=
    ["exactAcyclicTrianglehIso13SelectedCochainStrictification_of_closed2_\
      homotopyEquivInvariance",
      "Dbounded.selectedCochainStrictificationOfClosed2HomotopyInvarianceW848",
      "Dbounded.homotopyEquivInvarianceOfClosedMapExactInputsW848",
      "Dbounded.selectedCochainStrictificationOfClosedMapExactInputsClosed2W848",
      "Dbounded.homotopyEquivInvarianceOfClosedEmbeddingExactInputsW848",
      "Dbounded.selectedCochainStrictificationOfClosedEmbeddingExactInputsClosed2W848",
      "Dbounded.closed2OfKernelCokernelConditionedW848",
      "Dbounded.selectedCochainStrictificationOfClosedMapExactInputs" ++
        "KernelCokernelConditionedW848",
      "Dbounded.selectedCochainStrictificationOfClosedEmbeddingExactInputs" ++
        "KernelCokernelConditionedW848",
      "Dbounded.closedMapSelectedCochainDataOfKernelCokernelConditionedW848",
      "Dbounded.closedEmbeddingSelectedCochainDataOfKernelCokernelConditionedW848",
      "Dbounded.selectedCochainClosed2RouteInputNamesW848",
      "Dbounded.selectedCochainClosed2RouteInputNamesW848_count",
      "Dbounded.selectedCochainKernelCokernelConditionedRouteInputNamesW848",
      "Dbounded.selectedCochainKernelCokernelConditionedRouteInputNamesW848_count"]
  selectedPayloadResult :=
    "proved: exact-acyclic Closed₂ plus homotopy-equivalence invariance constructs\
      the W847 selected cochain payload from the distinguished-triangle\
      mapping-cone presentation; W681 also discharges the Closed₂ leaf from\
      kernel/cokernel-conditioned topology and W839 HasHomology"
  w735InvarianceResult :=
    "proved: W812/W735 homology detection supplies the homotopy-invariance half\
      for both closed-map and closed-embedding exact-input branches; W831\
      supplies the universal comparison isomorphism used by the conditioned\
      branch"
  rejectedRoutes :=
    ["Closed₂ alone only produces an isomorphism-closure middle object; the\
        selected target complex becomes strictly exact acyclic only after\
        homotopy-equivalence invariance",
      "the bounded endpoint strictification obstruction remains separate and\
        cannot be bypassed by arbitrary homotopy-category endpoint isomorphisms"]
  remainingInputs :=
    ["construct MetrizableExactAtKernelCokernelConditionedTopologyInputs",
      "construct concrete values for one W735 exact-input branch"]
  productSuccessClaimed := false

theorem currentW848SelectedCochainClosed2Route_productSuccess :
    currentMetrizableSelectedCochainClosed2RouteStateW848.productSuccessClaimed =
      false :=
  rfl

end Dbounded

end LeanLCAExactChallenge
