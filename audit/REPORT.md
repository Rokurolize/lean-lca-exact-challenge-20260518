# Verification Report

## Target and mode

Target: `LeanLCAExactChallenge`, exact-category acyclicity and bounded weak equivalences for the bounded derived construction over `MetrizableLCA`.

Mode: corrective formal audit / Lean formalization continuation.

## Scope

This pass isolates and replaces the mathematically invalid acyclicity shape used by the legacy predicate

```lean
exactAcyclic C K := ∀ i, QuillenExactCategory.Conflation (K.sc i)
```

with a cycle-object predicate. The corrected bounded homotopy Verdier route is now
triangulated; the legacy localization stack is not globally refactored in this pass.

## Method

1. Restored the supplied offline bundle and verified the SHA256 of the recombined archive.
2. Avoided network-dependent `lake env` commands after observing that Lake tries to update the mathlib URL and reclone it.
3. Added `LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean`.
4. Added the new module to `LeanLCAExactChallenge.lean`.
5. Type-checked the new module using Lean 4.30.0 and the restored local `.lake` artifacts.
6. Generated `.olean` / `.ilean` for the new module and checked the top-level import file.
7. Added API, isomorphism transport, mapping-cone congruence, zero-object acyclicity, shift closure, and MetrizableLCA binary biproduct closure in `ExactAcyclicCorrect.lean`.
8. Added `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.lean`, porting the corrected bounded weak-equivalence closure surface: arrow isomorphism invariance, shift compatibility, finite product closure over default-universe `MetrizableLCA`, and finite products of corrected bounded weak equivalences.
9. Added `LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.lean`, a separate corrected localization surface with `BoundedDerivedCategoryWithCycles`, `DboundedWithCycles`, and `DboundedWithCycles.localization` based on `boundedExactWeakEquivalenceWithCycles`.
10. Added `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean`, a corrected MetrizableLCA stable package assumption surface tied to `DboundedWithCycles` and `boundedExactWeakEquivalenceWithCycles`.
11. Added a corrected zero-object helper for `DboundedWithCycles` under the corrected left-calculus hypothesis.
12. Extended `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean` with the first homotopy-invariance bridge for the corrected route: the mapping cone of a homotopy equivalence is contractible in the homotopy category sense, and homotopy equivalences of bounded complexes are `boundedExactWeakEquivalenceWithCycles`.
13. Added `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean`, the corrected homotopy-category object-property surface: `exactAcyclicWithCyclesHomotopyObject`, its iso-closure, corrected `trW` mapping-cone detection, and the checked comparison from direct bounded corrected weak equivalences into the corrected homotopy `trW` pullback.
14. Constructed corrected cycle objects for mapping cones and proved
    `MetrizableLCA.exactAcyclicWithCycles_mappingCone` without topology or homology-detection
    assumptions.
15. Used strict cone triangles and fullness of the homotopy quotient to prove unconditional
    `IsTriangulatedClosed₃` and `IsTriangulatedClosed₂` for the corrected metrizable
    homotopy iso-closure.
16. Added `BoundedDerivedWithCycles.Metrizable.homotopyVerdierTriangulatedPackage`, the
    unconditional ordinary triangulated semantics of the corrected bounded homotopy Verdier
    quotient, while recording that its ordinary nerve is not a genuine stable
    infinity-category enhancement.
17. Added a genuine quasicategory foundation: bicategorical equivalences, functorial
    inner-fibrant replacement, equivalence edges, relative infinity functors, pointedness, and
    finite infinity-(co)limits stated through bicategorical adjunctions.
18. Replaced the raw corrected weak-equivalence class as a relative-category input by its
    multiplicative closure and proved that maps into any multiplicative target invert this
    closure exactly when they invert the original corrected cone weak equivalences.
19. Constructed pairwise Dold--Kan mapping carriers from the nonpositive Hom complex, proved
    that their vertices are bounded cochain maps, and transported associative unital
    composition at degree zero.
20. Formalized stable quasicategories by cartesian and cocartesian squares defined as essential
    images of right and left Kan extensions in the strict bicategory of quasicategories.
21. Extended every identity vertex to an actual simplicial map from the monoidal unit and
    packaged the exact all-degree composition, associativity, and unit target as
    `DgMappingEnrichment` without asserting an unconstructed inhabitant.
22. Proved that an Alexander--Whitney oplax monoidal structure on normalized Moore chains of
    integer modules induces the complete coherent lax monoidal structure on the Dold--Kan
    inverse by adjunction, and identified its tensorator with the adjoint of Alexander--Whitney
    followed by the Dold--Kan counits.
23. Transported each truncated additive-group Hom complex through the equivalence with integer
    modules, built its tensor-compatible Dold--Kan simplicial carrier, identified its vertices
    with bounded-complex morphisms, and constructed its all-degree identity map.
24. Realized homogeneous cochain composition as a linear map over `ℤ`, descended it to an
    actual morphism from the algebraic tensor product, and proved its value on pure tensors.
25. Constructed the Hom cochain complex directly in integer modules and assembled the reversed
    tensor summands into a genuine chain map. Its commutation with differentials is proved from
    `HomComplex.δ_comp`, with the reversal matching mathlib's total-complex signs.
26. Identified the direct and equivalence-transported integer-module Hom complexes canonically,
    proved that integer-module transport commutes with the nonpositive truncation used here,
    including the cycle object in boundary degree zero, and obtained an isomorphism between the
    two mapping chain-complex carriers.
27. Constructed composition on every summand of the tensor product of the truncated direct Hom
    complexes. In degree zero, proved from `HomComplex.δ_comp` and the two cycle inclusions that
    composition is again a cocycle, lifted it to the output cycle object, and assembled all
    summands into degreewise tensor-composition maps.
28. Proved that the truncated degreewise composition maps commute with the total-complex
    differentials. The proof handles both boundary cases and the positive-positive case,
    rewrites the two total differentials through the canonical truncation inclusions, and uses
    `HomComplex.δ_comp` with the required Koszul sign. The maps now assemble into the genuine
    chain map `dgTruncatedCompositionReversed`.
29. Transported the chain composition back to the equivalence-transported integer-module
    carriers and applied the Dold--Kan inverse tensorator parametrically in a normalized
    Alexander--Whitney oplax structure. A natural pure-tensor pairing converts the cartesian
    product of the underlying simplicial sets to the underlying tensor product, yielding
    `dgMappingZModuleSSetComposition`. The oplax structure itself remains to be constructed.
30. Constructed the explicit degreewise Alexander--Whitney formula on alternating face-map
    complexes as the finite sum over front/back cuts, proved its naturality in both simplicial
    modules and its degree-zero formula, and formed the normalized degreewise candidate by the
    Moore inclusion and the two `PInfty` projectors. Proved the front/back face identities and
    the two boundary identities that drive the chain-law cancellation. The differential law
    and oplax coherence remain to be assembled.
31. Added canonical projections from each total tensor degree to its finite family of cut
    components and proved that these projections jointly detect maps into the total tensor.
    The Alexander--Whitney degree sum now projects exactly to its selected front/back summand.
    Proved the first differential-component formula: the cut `(p+1,q)` contributes precisely
    the first-factor differential to `(p,q)`, while its second-factor contribution vanishes.
    The symmetric second-component formula and the final boundary cancellation remain next.
32. Proved the symmetric second differential-component formula: the cut `(p,q+1)` contributes
    the second-factor differential to `(p,q)` with the total-complex sign `(-1)^p`, while its
    first-factor contribution vanishes. Both tensor differential contributions are now
    compiler-checked. Internal-face reindexing and cancellation of the two boundary terms are
    the next algebraic layer toward the normalized Alexander--Whitney chain map.
33. Proved the remaining Alexander--Whitney chain calculation. The early and late internal
    faces are reindexed against the source alternating differential, the two faces at the cut
    are identified and cancel with opposite signs, and every nonadjacent target summand is
    proved zero after projection. Joint detection by all pair projections then proves the full
    unnormalized chain-map identity. The resulting `alternatingAlexanderWhitney` is a natural
    chain map, not merely a family of degreewise candidates.
34. Composed the normalized Moore inclusion, the unnormalized chain map, and the two `PInfty`
    retractions to construct the genuine natural chain map `normalizedAlexanderWhitney`.
    Constructed its monoidal-unit map and identified that map with the standard augmentation
    of alternating chains. `normalizedMooreOplaxMonoidalCandidate` now discharges both
    naturality fields and exposes exactly the three remaining strict coherence obligations:
    associativity and the left and right unit laws.
35. Proved both unit coherence laws for the Alexander--Whitney tensorator. The proofs first
    isolate the unique surviving cut against the alternating-chain augmentation, then transport
    the resulting left and right unit identities through the normalized Moore inclusion and
    `PInfty` retractions. The typed oplax constructor now has only associativity left to prove.
36. Proved the projector law required by normalized associativity without asserting the false
    claim that raw Alexander--Whitney lands in the normalized tensor subcomplex. Cutwise, every
    source degeneracy makes either the front or back simplex map non-monic, so the corresponding
    output `PInfty` kills that cut. Hence the compressed Alexander--Whitney map annihilates the
    complementary `QInfty` projector and is fixed by `PInfty` on its diagonal source.
37. Proved Alexander--Whitney coassociativity and completed the normalized oplax-monoidal
    package. The unnormalized proof compares both iterated maps after every triple tensor
    projection. The normalized proof transports that equality through the Moore inclusion,
    the retained source projector, associator naturality, and all three Moore retractions.
    The resulting `normalizedMooreOplaxMonoidal` is an actual inhabitant, not an assumption or
    a constructor with remaining coherence hypotheses.
38. Constructed the identity cocycle in every direct integer-module truncated Hom complex and
    promoted it to `dgMappingDirectZModuleChainIdentity`. Both chain-level unit laws for
    `dgTruncatedCompositionReversed` are proved after cancellation through the faithful
    truncation-to-restriction map and reduction to identity composition of homogeneous
    cochains.
39. Proved strict associativity of direct truncated Hom composition. The component theorem
    cancels the target truncation inclusion, reduces a threefold tensor to pure tensors, and
    applies associativity of homogeneous cochain composition. Triple total-degree projection
    extensionality then upgrades it to the chain-map law
    `dgTruncatedCompositionReversed_assoc`.
40. Packaged the direct dg data into a genuine higher carrier. The chain unit and composition
    laws define an enrichment of `ComplexCategoryᵒᵖ`; the actual Alexander--Whitney-induced
    Dold--Kan lax structure transports it to simplicial integer modules. Enriched opposite,
    degreewise forgetful lax transport to simplicial sets, and `ForgetEnrichment` produce the
    genuine `DirectDGSimplicialCategory`. Its Hom object is definitionally the direct
    Dold--Kan mapping simplicial set. The homotopy coherent nerve and its chosen inner-fibrant
    replacement give `directDGQCat : SSet.QCat`, together with an inner-anodyne replacement
    map. This carrier is deliberately not called the derived infinity category before
    localization at the corrected weak equivalences.
41. Constructed a generic equivalence-forcing presentation for any ordinary relative
    category. For every specified weak arrow, Lean attaches a copy of the free-living
    equivalence along its forward `1`-simplex, using one coproduct pushout, and then applies
    the functorial inner-fibrant replacement. A new nerve lemma proves that an ordinary
    isomorphism gives an equivalence edge. Endpoint transport across the pushout condition
    then gives every selected edge an explicit `EquivalenceIntervalExtension`; the generic
    extension-to-equivalence theorem shows that it becomes an `EdgeIsEquivalence` in the
    resulting genuine quasicategory.
42. Specialized the equivalence-forcing construction to bounded metrizable complexes and
    `GeneratedWeakEquivalence`. The resulting `metrizableEquivalenceForcingQCat` comes with a
    compiler-checked `RelativeInfinityFunctor`; its map inverts the complete generated class
    and, by the proved raw-to-generated inclusion, every corrected cone weak equivalence.
    The name intentionally records only equivalence forcing: the infinity-localization
    universal property, stability, and Verdier comparison remain unproved.
43. Formalized two honest localization specifications. `BicategoricalTwoLocalizationProperty`
    controls only homotopy categories of mapping objects and is explicitly labeled
    2-truncated. `MappingQuasicategoryLocalizationProperty` instead requires, for every target
    quasicategory, an equivalence from the full mapping quasicategory to the full subcomplex of
    weak-equivalence-inverting functors. Its internal-Hom and full-subcomplex quasicategory
    witnesses remain explicit in the pinned library, and no concrete candidate is asserted to
    satisfy the complete specification. Full vertex-spanned subcomplexes are nevertheless
    proved to preserve quasicategories. The only remaining closure premise is ambient internal
    Hom; `quasicategory_ihom_of_innerHornPushoutProduct` derives it from the exact inner-horn
    pushout-product statement missing from v4.30.
44. Computed the normalized Alexander--Whitney dg composition on vertices. The degree-zero
    Dold--Kan counit, normalized tensorator, transported cochain, and pure-tensor calculations
    culminate in `dgMappingZModuleVerticesEquivBoundedMorphisms_comp`, identifying simplicial
    composition with ordinary bounded-complex composition.
45. Applied ordinary localization to the proved edge inversion. The induced
    `metrizableEquivalenceForcingHomotopyFunctor` inverts every raw corrected weak equivalence,
    so it factors canonically through `DboundedWithCycles MetrizableLCA`. The resulting
    `metrizableCorrectedDerivedToEquivalenceForcingHomotopy` and its factorization isomorphism
    are compiler checked. This constructs the comparison functor but does not assert that it
    is an equivalence.
46. Connected equivalence forcing directly to the marked localization specification. The
    generic and metrizable maps now satisfy `InvertsMarkedEdges` for the complete relative
    marking, not only one arrow at a time. Precomposition by any marking-inverting map is
    proved to factor through the relative full mapping subcomplex, and the metrizable
    specialization names this canonical comparison. Thus the candidate inhabits the inversion
    component of both specifications and the factorization component of the mapping-
    quasicategory specification. No `BicategoricalTwoLocalizationAt` comparison functor is
    constructed. The mapping-object bicategorical equivalence remains open.
47. Isolated the vertex-level free-equivalence extension condition used by the cell model.
    `EquivalenceIntervalExtension` packages a coherent map from the free-living equivalence,
    and Lean proves that every such extension represents an equivalence edge. The desired
    converse on individual edges is stated as `EveryEquivalenceEdgeExtends` and as surjectivity
    of the restriction map. Ordinary-nerve isomorphisms have explicit extensions. Separately, the
    2-truncated quasicategory API extracts an inverse edge and both triangle fillers from an
    isomorphism class. Pinned mathlib lacks the comparison and outer-horn theory needed even
    for this vertex converse. Moreover, the localization proof requires the parametrized
    restriction from free-equivalence mapping objects to be a categorical equivalence onto the
    full equivalence-edge subcomplex; vertex surjectivity alone is insufficient. Equivalence
    forcing supplies extensions for its selected arrows directly.
48. Reduced inner-anodyne mapping invariance to the exact missing cartesian
    pushout-product theorem. Assuming inner horns remain inner anodyne after pushout-product
    with arbitrary monomorphisms, Lean proves that precomposition along any inner-anodyne map
    has the right lifting property against every monomorphism. Independently, any map with
    that lifting property has a strict section and a fiberwise contraction parametrized by
    the free-living equivalence; the induced self-internal-Hom edge is an equivalence. The
    endpoint-to-Cat-enriched-2-isomorphism and adjointification bridge needed for
    `IsBicategoricalEquivalence` remains absent and is not claimed.

## Assumption list

- Existing `QuillenExactCategory.Conflation` is the intended exact-category conflation predicate.
- Existing `MetrizableLCA.quillenConflation_iff_challengeExactSequence` correctly connects `QuillenExactCategory.Conflation` with `challengeExactSequence`.
- The new closure proofs still reuse existing project infrastructure for finite product decompositions and mapping-cone product comparison, including W151's Option-product comparison and the existing finite mapping-cone comparison input.
- The existing legacy `Dbounded` route remains in the repository and is not globally replaced in this pass.
- The legacy direct-chain stable bridge remains conditional. The honest bounded homotopy
  Verdier quotient now has an unconditional ordinary triangulated package and does not reuse
  legacy `Dbounded` semantic packages.
- The inner-fibrant replacement unit is proved inner anodyne, but is not claimed to be a Joyal
  categorical equivalence: that comparison theorem is absent from pinned mathlib v4.30.
- The new infinity-limit predicates are genuine adjoint definitions, not inhabitants for the
  corrected derived carrier. Their explicit internal-hom quasicategory proof argument records
  another theorem missing from v4.30 rather than hiding it as an assumption.

## Findings

### Critical: legacy `exactAcyclic` is not exact-category acyclicity of complexes

The old definition requires a conflation on `K.sc i`, i.e. on the short complex `K.X i -> K.X (i+1) -> K.X (i+2)`. This makes adjacent differentials themselves the maps in short exact sequences. The usual exact-category acyclicity needs cycle objects `Z^i` and conflations `Z^i -> K^i -> Z^(i+1)`, with the differential factoring as `K^i -> Z^(i+1) -> K^(i+1)`.

### Implemented correction

The new file introduces:

```lean
structure ExactAcyclicWithCyclesData (K : CochainComplex C ℤ) where
  Z : ℤ → C
  incl : ∀ i : ℤ, Z i ⟶ K.X i
  proj : ∀ i : ℤ, K.X i ⟶ Z (i + 1)
  zero : ∀ i : ℤ, incl i ≫ proj i = 0
  conflation : ∀ i : ℤ,
    QuillenExactCategory.Conflation (ShortComplex.mk (incl i) (proj i) (zero i))
  d_eq : ∀ i : ℤ, proj i ≫ incl (i + 1) = K.d i (i + 1)
```

and the predicate:

```lean
def exactAcyclicWithCycles (K : CochainComplex C ℤ) : Prop :=
  Nonempty (ExactAcyclicWithCyclesData C K)
```

The `Nonempty` wrapper is necessary because the witness contains data and therefore cannot be stored in a `Prop` structure with usable projections.

### MetrizableLCA bridge

The theorem

```lean
theorem MetrizableLCA.exactAcyclicWithCycles_iff_challengeCycleExactSequences
```

proves that the corrected predicate is equivalent to the existence of cycle objects whose short complexes satisfy `challengeExactSequence` and whose maps factor the differentials.

### Corrected bounded weak equivalence

The new definition

```lean
def boundedExactWeakEquivalenceWithCycles [HasBinaryBiproducts C] :
    MorphismProperty (BoundedComplexCategory C)
```

uses the corrected mapping-cone acyclicity predicate instead of the legacy degreewise one.

### Corrected closure API

The corrected route now has Lean-checked API for:

- `ExactAcyclicWithCyclesData.ofIso`
- `exactAcyclicWithCycles_of_iso`
- `exactAcyclicWithCycles_mappingCone_congr_iff`
- `ExactAcyclicWithCyclesData.shift`
- `exactAcyclicWithCycles_shift`
- `exactAcyclicWithCycles_shift_iff`
- `exactAcyclicWithCycles_mappingCone_shift_iff`
- `MetrizableLCA.cyclesDataMap`
- `MetrizableLCA.cyclesDataMap_incl`
- `MetrizableLCA.cyclesData_proj_map`
- `MetrizableLCA.mappingConeCyclesProj_deflation`
- `MetrizableLCA.mappingConeCyclesIncl_isLimit`
- `MetrizableLCA.mappingConeCyclesConflation`
- `MetrizableLCA.cyclesDataMappingCone`
- `MetrizableLCA.exactAcyclicWithCycles_mappingCone`
- `MetrizableLCA.exactAcyclicWithCycles_biprod`
- `ExactAcyclicWithCyclesClosure.boundedExactWeakEquivalenceWithCycles_respectsIso`
- `ExactAcyclicWithCyclesClosure.boundedExactWeakEquivalenceWithCycles_isCompatibleWithShift`
- `ExactAcyclicWithCyclesClosure.MetrizableLCA.finiteExactAcyclicWithCyclesProductClosure_of_w151`
- `ExactAcyclicWithCyclesClosure.MetrizableLCA.isStableUnderFiniteProducts_metrizableLCA`
- `ExactAcyclicWithCyclesClosure.MetrizableLCA.isStableUnderFiniteCoproducts_metrizableLCA`
- `ExactAcyclicWithCyclesClosure.MetrizableLCA.isStableUnderFiniteProducts_op_metrizableLCA`
- `BoundedDerivedCategoryWithCycles`
- `DboundedWithCycles`
- `DboundedWithCycles.localization`
- `DboundedWithCycles.MetrizableLCA.hasFiniteProducts`
- `DboundedWithCycles.hasFiniteBiproductsOfStableFiniteProducts`
- `DboundedWithCycles.hasFiniteCoproductsOfStableFiniteProducts`
- `DboundedWithCycles.MetrizableLCA.hasFiniteBiproducts`
- `DboundedWithCycles.MetrizableLCA.hasFiniteCoproducts`
- `DboundedWithCycles.MetrizableLCA.hasFiniteLimitsOfEqualizers`
- `DboundedWithCycles.MetrizableLCA.hasFiniteColimitsOfCoequalizers`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputs`
- `DboundedWithCycles.MetrizableLCA.hasEqualizersOfWalkingParallelPairTransfer`
- `DboundedWithCycles.MetrizableLCA.hasCoequalizersOfWalkingParallelPairTransfer`
- `DboundedWithCycles.MetrizableLCA.hasFiniteLimitsOfWalkingParallelPairTransfer`
- `DboundedWithCycles.MetrizableLCA.hasFiniteColimitsOfWalkingParallelPairTransfer`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairObjectwiseLocalizationFunctor`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFunctorCategoryLocalizationInput`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairObjectwiseLocalization_inverts`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFunctorCategoryFixedTargetFields`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFunctorCategoryRemainingFixedTargetData`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFunctorCategoryRemainingFixedTargetInputs`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairFunctorCategoryLocalization_of_fixedTargetData`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromFixedTargets`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairFiniteShapeTransferInputs_of_fixedTargets`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairStrictPreimageData`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairStrictPreimageMapData`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairLiftBlueprint`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairNormalizedLiftBlueprint`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFixedTargetBlueprintInputs`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairNormalizedFixedTargetInputs`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairFixedTargetInputs_of_normalized`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairFixedTargetInputs_of_blueprint`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairFunctorCategoryLocalization_of_blueprint`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairFunctorCategoryLocalization_of_normalized`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromBlueprint`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairFiniteShapeTransferInputs_of_blueprint`
- `DboundedWithCycles.MetrizableLCA.WalkingParallelPairFiniteShapeTransferInputsFromNormalized`
- `DboundedWithCycles.MetrizableLCA.walkingParallelPairFiniteShapeTransferInputs_of_normalized`
- `DboundedWithCycles.hasZeroObjectOfHasLeftCalculusOfFractions`
- `DboundedWithCycles.MetrizableLCA.hasZeroObject`
- `mappingCone_contractingHomotopy_of_homotopyEquiv`
- `boundedExactWeakEquivalenceWithCycles_of_contractibleMappingCone`
- `boundedExactWeakEquivalenceWithCycles_id`
- `boundedExactWeakEquivalenceWithCycles_containsIdentities`
- `boundedExactWeakEquivalenceWithCycles_of_homotopyEquiv`
- `homotopyEquivalences_le_boundedExactWeakEquivalenceWithCycles`
- `exactAcyclicWithCyclesHomotopyObject`
- `ExactAcyclicWithCyclesHomotopyEquivInvarianceInput`
- `ExactAcyclicWithCyclesHomologyDetectionInput`
- `ExactAcyclicWithCyclesExactAtDetectionInput`
- `ExactAcyclicWithCyclesExactAtReverseDetectionInput`
- `MetrizableLCA.exactAt_of_exactAcyclicWithCycles`
- `MetrizableLCA.forgetToAddCommGrpCat_exactAt_of_cyclesData`
- `MetrizableLCA.forgetToAddCommGrpCat_exactAt_of_exactAcyclicWithCycles`
- `MetrizableLCA.exactAt_of_forgetToAddCommGrpCat_exactAt`
- `MetrizableLCA.exactAtCycleBoundary`
- `MetrizableLCA.exactAtCycleBoundary_epi_of_exactAt`
- `MetrizableLCA.exactAtCanonicalCycleShortComplex`
- `MetrizableLCA.exists_preimage_kernel_ι_of_apply_eq_zero`
- `MetrizableLCA.exactAtCycleBoundary_surjective_of_exactAt`
- `MetrizableLCA.isOpenMap_of_injective_comp_open`
- `MetrizableLCA.isOpenMap_of_surjective_sigmaCompact`
- `MetrizableLCA.exactAtCycleBoundary_openMap_of_differential_openMap`
- `MetrizableLCA.ExactAtCanonicalCycleDifferentialOpenMapInput`
- `MetrizableLCA.ExactAtCanonicalCycleOpenMapInput`
- `MetrizableLCA.ExactAtCanonicalCycleSigmaCompactSourceInput`
- `MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput`
- `MetrizableLCA.ExactAtCanonicalCycleDifferentialTopologyInput`
- `MetrizableLCA.ExactAtCanonicalCycleSigmaCompactSourceTopologyInput`
- `MetrizableLCA.exactAtCanonicalCycleBoundaryTopologyInput_of_differentialTopologyInput`
- `MetrizableLCA.exactAtCanonicalCycleBoundaryTopologyInput_of_sigmaCompactSourceTopologyInput`
- `MetrizableLCA.exactAtCanonicalCycleOpenMapInput_of_differentialOpenMapInput`
- `MetrizableLCA.exactAtCanonicalCycleOpenMapInput_of_sigmaCompactSourceInput`
- `MetrizableLCA.ExactAtCanonicalCycleStrictInput`
- `MetrizableLCA.exactAtCanonicalCycleStrictInput_of_openMapInput`
- `MetrizableLCA.exactAtCanonicalCycleStrictInput_of_boundaryTopologyInput`
- `MetrizableLCA.exactAcyclicWithCycles_of_exactAtCanonicalCycleStrictInput`
- `exactAcyclicWithCyclesExactAtReverseDetectionInput_of_metrizableCanonicalCycleStrict`
- `exactAcyclicWithCyclesExactAtReverseDetectionInput_of_metrizableCanonicalCycleOpenMap`
- `exactAcyclicWithCyclesExactAtReverseDetectionInput_of_metrizableBoundaryTopology`
- `exactAcyclicWithCyclesExactAtReverseDetectionInput_of_metrizableSigmaCompactSource`
- `exactAcyclicWithCyclesExactAtReverseDetectionInput_of_metrizableSigmaCompactTopology`
- `exactAcyclicWithCyclesExactAtReverseDetectionInput_of_metrizableDifferentialOpenMap`
- `exactAcyclicWithCyclesExactAtReverseDetectionInput_of_metrizableDifferentialTopology`
- `exactAcyclicWithCyclesExactAtDetectionInput_of_metrizableReverse`
- `exactAcyclicWithCyclesHomologyDetectionInput_of_exactAtDetection`
- `exactAcyclicWithCyclesHomotopyObject_eq_homologicalKernel_of_homologyDetection`
- `exactAcyclicWithCyclesHomotopyObject_isTriangulatedClosed2_of_homologicalKernel`
- `exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_homologyDetection`
- `exactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance`
- `exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_isClosedUnderIsomorphisms`
- `exactAcyclicWithCyclesHomotopyEquivInvarianceInput_iff_isClosedUnderIsomorphisms`
- `exactAcyclicWithCyclesHomotopyIsoClosure`
- `metrizableExactAcyclicWithCyclesHomotopyIsoClosure_distinguished_ext3_of_triangleh_iso12`
- `metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed3`
- `metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_direct`
- `metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2`
- `exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2`
- `exactAcyclicWithCyclesHomotopyObject_triangleh_ext2`
- `exactAcyclicWithCyclesHomotopyObject_distinguished_ext2_of_triangleh_iso13`
- `exactAcyclicWithCyclesHomotopyIsoClosureTrianglehIso13Realization`
- `exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_triangleh_iso13_realization`
- `exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject`
- `exactAcyclicWithCyclesHomotopyObject_isTriangulated_of_isTriangulatedClosed2`
- `exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated`
- `exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulated`
- `exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_closed2`
- `exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_closed2`
- `exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_isoClosureClosed2`
- `exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_isoClosureClosed2`
- `exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_homotopyObjectClosed2`
- `exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_homotopyObjectClosed2`
- `exactAcyclicWithCyclesHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_closed2`
- `exactAcyclicWithCyclesHomotopyIsoClosure_trW_hasRightCalculusOfFractions_of_closed2`
- `boundedExactAcyclicWithCyclesHomotopyObject`
- `boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2`
- `BoundedExactAcyclicWithCyclesHomotopyVerdierCategory`
- `boundedExactAcyclicWithCyclesHomotopyObjectToIsoClosure_trW`
- `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_preadditive_of_closed2`
- `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_localization_additive_of_closed2`
- `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_hasZeroObject_of_closed2`
- `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_hasShift_of_closed2`
- `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_shiftFunctor_additive_of_closed2`
- `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_pretriangulated_of_closed2`
- `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_isTriangulated_of_closed2`
- `exactAcyclicWithCyclesHomotopyObject_trW_quotient_map_of_exactAcyclicWithCycles_mappingCone`
- `exactAcyclicWithCyclesHomotopyObject_trW_quotient_map_iff_exactAcyclicWithCycles_mappingCone`
- `exactAcyclicWithCyclesHomotopyIsoClosure_trW_quotient_map_iff_mappingCone`
- `boundedExactWeakEquivalenceWithCycles_le_exactAcyclicWithCyclesHomotopy_trW_inverseImage`
- `boundedHomotopyObject_isTriangulatedClosed3`
- `boundedHomotopyObject_isTriangulatedClosed2_direct`
- `boundedHomotopyExactWeakEquivalenceWithCycles`
- `boundedHomotopyExactWeakEquivalenceWithCycles_containsIdentities`
- `boundedHomotopyExactWeakEquivalenceWithCyclesToIsoClosure_trW`
- `boundedHomotopyExactWeakEquivalenceWithCyclesToBoundedHomotopy_trW`
- `boundedHomotopyExactWeakEquivalenceWithCycles_eq_boundedHomotopy_trW_inverseImage`
- `boundedHomotopyWithCyclesLocalizedVerdierFunctor`
- `BoundedHomotopyWithCyclesLocalizedRightAdjointInput`
- `BoundedHomotopyWithCyclesLocalizedLeftAdjointInput`
- `boundedHomotopyExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_adjoint`
- `boundedHomotopyExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint`
- `boundedHomotopyExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_adjoint`
- `boundedHomotopyExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint`
- `boundedExactWeakEquivalenceWithCycles_le_boundedHomotopyExactWeakEquivalenceWithCycles`
- `boundedHomotopyExactWeakEquivalenceWithCycles_iff_mappingCone_isoClosure`
- `boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_isoClosed`
- `boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_isoClosed`
- `boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_homotopyEquivInvariance`
- `boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopy_trW_of_homotopyEquivInvariance`
- `boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_homotopyEquivInvariance`
- `boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_homotopyEquivInvariance`
- `boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint`
- `boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint`
- `BoundedHomotopyExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput`
- `BoundedHomotopyExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.of_comp`
- `BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput`
- `BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.ofHomotopy`
- `MorphismProperty.le_map_inverseImage_of_full_essSurj`
- `boundedCochainComplex_cylinder`
- `BoundedComplexCategory.precylinder`
- `BoundedComplexCategory.homotopyQuotientBounded_essSurj`
- `BoundedComplexCategory.homotopyQuotientBounded_full`
- `BoundedComplexCategory.homotopyQuotientBounded_isLocalization`
- `boundedExactWeakEquivalenceWithCyclesToBoundedVerdier_isLocalizedEquivalence`
- `DboundedWithCycles.boundedVerdierLocalizedFunctorOfInput`
- `DboundedWithCycles.boundedVerdierLocalizedFunctorOfInput_commShift`
- `DboundedWithCycles.preadditiveOfBoundedVerdierLocalizationInput`
- `DboundedWithCycles.hasZeroObjectOfBoundedVerdierLocalizationInput`
- `DboundedWithCycles.hasFiniteProductsOfBoundedVerdierLocalizationInput`
- `DboundedWithCycles.hasFiniteCoproductsOfBoundedVerdierLocalizationInput`
- `DboundedWithCycles.hasFiniteBiproductsOfBoundedVerdierLocalizationInput`
- `DboundedWithCycles.shiftFunctor_additiveOfBoundedVerdierLocalizationInput`
- `DboundedWithCycles.pretriangulatedOfBoundedVerdierLocalizationInput`
- `DboundedWithCycles.distinguished_iff_boundedVerdierLocalizedFunctorOfInput`
- `DboundedWithCycles.isTriangulatedOfBoundedVerdierLocalizationInput`
- `exactAcyclicWithCyclesHomotopyObject_isTriangulatedClosed2_of_isoClosure_closed2`
- `exactAcyclicWithCyclesHomotopyObject_isTriangulatedClosed2_of_descent_realization`
- `BoundedDerivedWithCycles.Metrizable.preadditiveOfBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.hasZeroObjectOfBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.hasFiniteProductsOfBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.hasFiniteCoproductsOfBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.hasFiniteLimitsOfWalkingParallelPairBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.hasFiniteColimitsOfWalkingParallelPairBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.hasFiniteBiproductsOfBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.shiftFunctorAdditiveOfBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.boundedHomotopyClosed2`
- `BoundedDerivedWithCycles.Metrizable.boundedHomotopyClosed2OfTrianglehIso13Realization`
- `BoundedDerivedWithCycles.Metrizable.exactAcyclicWithCyclesHomotopyObjectClosed2OfDescentRealization`
- `BoundedDerivedWithCycles.Metrizable.hasHomologyOfComparisonBijectivity`
- `BoundedDerivedWithCycles.Metrizable.exactAtReverseDetectionInputOfBoundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.homologyDetectionInputOfBoundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.comparisonHomologyKernelObject`
- `BoundedDerivedWithCycles.Metrizable.exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject`
- `BoundedDerivedWithCycles.Metrizable.forgetfulHomologyKernelFunctor`
- `BoundedDerivedWithCycles.Metrizable.forgetfulHomologicalKernel_of_exactAcyclicWithCyclesHomotopyObject`
- `BoundedDerivedWithCycles.Metrizable.ExactAcyclicWithCyclesForgetfulHomologicalKernelExactAtInput`
- `BoundedDerivedWithCycles.Metrizable.forgetfulHomologicalKernelExactAtInput`
- `BoundedDerivedWithCycles.Metrizable.forgetfulHomologicalKernelExactAtInput_of_preservesHomology`
- `BoundedDerivedWithCycles.Metrizable.ExactAcyclicWithCyclesForgetfulHomologicalKernelReversePayload`
- `BoundedDerivedWithCycles.Metrizable.forgetfulHomologicalKernelReversePayload_of_exactAtInput`
- `BoundedDerivedWithCycles.Metrizable.forgetfulHomologicalKernelReversePayload_of_boundaryTopologyPreservesHomology`
- `BoundedDerivedWithCycles.Metrizable.forgetfulHomologicalKernelReversePayload_of_boundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.exactAcyclicWithCyclesHomotopyObject_eq_forgetfulHomologicalKernel`
- `BoundedDerivedWithCycles.Metrizable.exactAcyclicWithCyclesHomotopyObjectClosed2OfForgetfulHomologicalKernel`
- `BoundedDerivedWithCycles.Metrizable.exactAcyclicWithCyclesHomotopyEquivInvarianceInputOfForgetfulHomologicalKernel`
- `BoundedDerivedWithCycles.Metrizable.leftCalculusAssumptionOfHomotopyVerdier`
- `BoundedDerivedWithCycles.Metrizable.RightCalculusAssumption`
- `BoundedDerivedWithCycles.Metrizable.rightCalculusAssumptionOfHomotopyVerdier`
- `BoundedDerivedWithCycles.Metrizable.stableSemanticInputOfHomotopyVerdierWalkingParallelPairTransfer`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfHomotopyVerdierWalkingParallelPairTransfer`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfHomotopyVerdierWalkingParallelPairBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfWalkingParallelPairBoundedVerdierLocalizationInput`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificDifferentialOpenMapInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificSigmaCompactSourceInputs`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificInputsOfDifferentialOpenMap`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificInputsOfSigmaCompactSource`
- `BoundedDerivedWithCycles.Metrizable.homologyDetectionInputOfRouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject_of_routeSpecific`
- `BoundedDerivedWithCycles.Metrizable.exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject_of_differential`
- `BoundedDerivedWithCycles.Metrizable.exactAcyclicWithCyclesHomotopyObject_eq_comparisonHomologyKernelObject_of_sigmaCompact`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificDifferentialOpenMapLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificSigmaCompactSourceLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificLeftCalculusInputsOfDifferentialOpenMap`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificLeftCalculusInputsOfSigmaCompactSource`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfRouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfRouteSpecificDifferentialOpenMapInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfRouteSpecificSigmaCompactSourceInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificDifferentialOpenMapInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificDifferentialOpenMapInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificDifferentialOpenMapInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificDifferentialOpenMapInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificSigmaCompactSourceInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificSigmaCompactSourceInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificSigmaCompactSourceInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificSigmaCompactSourceInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageWithLeftCalculusOfRouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.leftCalculusOfRouteSpecificInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageWithLeftCalculusOfRouteSpecificDifferentialOpenMapInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageWithLeftCalculusOfRouteSpecificSigmaCompactSourceInputs`
- `BoundedDerivedWithCycles.Metrizable.leftCalculusOfRouteSpecificDifferentialOpenMapInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificDifferentialOpenMapLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificDifferentialOpenMapLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificDifferentialOpenMapLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificDifferentialOpenMapLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.leftCalculusOfRouteSpecificSigmaCompactSourceInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificSigmaCompactSourceLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificSigmaCompactSourceLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificSigmaCompactSourceLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificSigmaCompactSourceLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificForgetfulKernelInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificForgetfulKernelLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificForgetfulKernelBoundaryInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfRouteSpecificForgetfulKernelInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelInputs`
- `BoundedDerivedWithCycles.Metrizable.leftCalculusOfRouteSpecificForgetfulKernelInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificForgetfulKernelLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificForgetfulKernelLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificForgetfulKernelLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificForgetfulKernelLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificForgetfulKernelExactAtInputs`
- `BoundedDerivedWithCycles.Metrizable.RouteSpecificForgetfulKernelExactAtLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelInputsOfExactAt`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelLeftCalculusInputsOfExactAt`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelInputsOfBoundary`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelLeftCalculusInputsOfBoundary`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfRouteSpecificForgetfulKernelExactAtInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelExactAtInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfRouteSpecificForgetfulKernelBoundaryInputs`
- `BoundedDerivedWithCycles.Metrizable.stablePackageWithLeftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificForgetfulKernelBoundaryInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificForgetfulKernelBoundaryInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificForgetfulKernelBoundaryInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificForgetfulKernelBoundaryInputs`
- `BoundedDerivedWithCycles.Metrizable.leftCalculusOfRouteSpecificForgetfulKernelBoundaryInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificForgetfulKernelBoundaryLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificForgetfulKernelBoundaryLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificForgetfulKernelBoundaryLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificForgetfulKernelBoundaryLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificForgetfulKernelExactAtInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificForgetfulKernelExactAtInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificForgetfulKernelExactAtInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificForgetfulKernelExactAtInputs`
- `BoundedDerivedWithCycles.Metrizable.leftCalculusOfRouteSpecificForgetfulKernelExactAtInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteLimitsOfRouteSpecificForgetfulKernelExactAtLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.finiteColimitsOfRouteSpecificForgetfulKernelExactAtLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfRouteSpecificForgetfulKernelExactAtLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfRouteSpecificForgetfulKernelExactAtLeftCalculusInputs`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificInputNames`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificLeftCalculusInputNames`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelInputNames`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelLeftCalculusInputNames`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelBoundaryInputNames`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelBoundaryLeftCalculusInputNames`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelExactAtInputNames`
- `BoundedDerivedWithCycles.Metrizable.routeSpecificForgetfulKernelExactAtLeftCalculusInputNames`
- `BoundedDerivedWithCycles.Metrizable.HomotopyVerdierWeakEquivalence`
- `BoundedDerivedWithCycles.Metrizable.HomotopyVerdierCategory`
- `BoundedDerivedWithCycles.Metrizable.HomotopyVerdierOrdinaryNerve`
- `BoundedDerivedWithCycles.Metrizable.HomotopyVerdierTriangulatedPackage`
- `BoundedDerivedWithCycles.Metrizable.homotopyVerdierTriangulatedPackage`
- `BoundedDerivedWithCycles.Metrizable.StablePackage`
- `BoundedDerivedWithCycles.Metrizable.StablePackageWithLeftCalculus`
- `BoundedDerivedWithCycles.Metrizable.StableCorePackage`
- `BoundedDerivedWithCycles.Metrizable.stableCorePackageOfForgetfulKernelReverse`
- `BoundedDerivedWithCycles.Metrizable.stableCorePackageOfForgetfulKernelBoundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.preadditiveOfForgetfulKernelBoundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.finiteProductsOfForgetfulKernelBoundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.finiteCoproductsOfForgetfulKernelBoundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.pretriangulatedOfForgetfulKernelBoundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.isTriangulatedOfForgetfulKernelBoundaryTopology`
- `BoundedDerivedWithCycles.Metrizable.LeftCalculusAssumption`
- `BoundedDerivedWithCycles.Metrizable.LeftCalculusSemanticFields`
- `BoundedDerivedWithCycles.Metrizable.RemainingStableSemanticFields`
- `BoundedDerivedWithCycles.Metrizable.StableSemanticInput`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfLeftCalculus`

## List of sorry / unproven spots

The new corrected derived and `Infinity` modules contain no `sorry` or `admit`.

Unproved in this pass:

- Replacement of the existing `Dbounded` localization to use the new weak equivalences throughout the old theorem stack.
- A direct-chain composite-localization equivalence between `DboundedWithCycles` and the
  corrected bounded homotopy Verdier quotient. Raw-chain left calculus is not substituted for
  this comparison because the strict Ore claim is generally false.
- A genuine stable infinity-category enhancement. The new local API can express equivalence,
  relative edge inversion, pointedness, finite infinity-(co)limits, and bicartesian-square
  stability. Pairwise Dold--Kan mapping carriers are inhabited and their vertices are bounded
  cochain maps; their identity maps exist through all simplicial degrees. The missing work is
  an inhabitant of the checked simplicial-composition interface, the derived localization
  universal property, an inhabited stable structure, and comparison with
  `HomotopyVerdierCategory`.
- Ordinary finite limits and finite colimits on `DboundedWithCycles MetrizableLCA.{0}` are not
  listed as proof obligations: they conflict with the non-split-extension behavior of an
  ordinary triangulated derived category. The legacy success-bearing package still requests
  them, so its success marker remains false.

## Verification commands

The successful checks were run with direct `lean`, not with `lake env`, because Lake attempts network dependency repair in this restored bundle.

```bash
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.30.0/bin:$PATH"
LIBS=$(find -L .lake -path '*/build/lib/lean' -type d | sort | paste -sd: -)
LDLIBS=$(find -L .lake -path '*/build/lib' -type d | sort | paste -sd: -)
export LEAN_PATH="$LIBS:$PWD"
export LD_LIBRARY_PATH="$LDLIBS"
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.ilean \
  LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.ilean \
  LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.lean
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.ilean \
  LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.lean
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.ilean \
  LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.ilean \
  LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.ilean \
  LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean
lean -j1 LeanLCAExactChallenge.lean
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean \
  LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean \
  LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean
awk 'length($0) > 100 {print FILENAME ":" FNR ":" length($0)}' \
  LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean \
  LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean \
  LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean
git diff --check
```

All listed checks exited with code 0 in the restored offline bundle; the line-length check produced no output. WSL handoff should re-run the same direct-`lean` checks with the local toolchain path available in that checkout.

## Version policy

This milestone remains intentionally verified on the repository-pinned toolchain. Live local evidence at the version-policy check was: `lean-toolchain` contains `leanprover/lean4:v4.30.0`; `lean --version` reports Lean 4.30.0 commit `d024af099ca4bf2c86f649261ebf59565dc8c622`; `lake-manifest.json` pins mathlib to rev `c5ea00351c28e24afc9f0f84379aa41082b1188f` with `inputRev` `v4.30.0`; and the restored `.lake/packages/mathlib` checkout is tagged `v4.30.0` with matching toolchain `leanprover/lean4:v4.30.0`.

Official GitHub release data observed during the version-policy check showed Lean stable `v4.31.0`, Lean prerelease `v4.32.0-rc1`, mathlib stable `v4.31.0`, and mathlib prerelease `v4.32.0-rc1`; mathlib master's `lean-toolchain` was `leanprover/lean4:v4.32.0-rc1`. The local machine has Lean toolchains for `v4.31.0` and `v4.32.0-rc1`, but the restored verified dependency cache is `v4.30.0`-only.

A stable `v4.31.0` migration was not committed because changing `lean-toolchain` alone would create an incoherent verification state: the manifest, mathlib checkout, inherited dependencies, and compiled `.olean` artifacts all need to move together. A valid stable migration requires a separate coherent Lake dependency update plus rebuilt or fetched `v4.31.0` artifacts, followed by the full baseline direct-Lean checks. Until that separate migration is completed, the proof route is verified against the repository pin.

## Repository state

The checked code milestone was committed as `43009683` (`Add corrected metrizable cycles stable bridge`) on branch `integrate-cycle-object-main-20260708`, then an audit-status commit `9e4547a0` (`Record corrected cycles bridge push status`) was pushed. A live post-fetch check before the version-policy audit update showed local `HEAD` and `origin/main` both at `9e4547a0`. The only untracked local paths observed were the `.lake` symlink used for local direct-Lean checking and `2026-07-08-085025-local-command-caveatcaveat-the-messages-below.txt`; neither was staged or committed.

## Idempotent completeness milestone

`LeanLCAExactChallenge/LCA/IdempotentComplete.lean` now proves
`IsIdempotentComplete MetrizableLCA.{u}` via mathlib's
`isIdempotentComplete_iff_hasEqualizer_of_id_and_idempotent` and the existing
`HasFiniteLimits MetrizableLCA` equalizer infrastructure from `LCA.Pullback`.
This is a foundation for the corrected route: homotopy-invariance of
`exactAcyclicWithCycles` and "contractible implies acyclic" (the Bühler
Chapter 10 arguments) require (weak) idempotent completeness, and both are
prerequisites for presenting the corrected acyclics as a triangulated object
property of the bounded homotopy category. Verified by direct
`lean -j1 LeanLCAExactChallenge/LCA/IdempotentComplete.lean` and
`lean -j1 LeanLCAExactChallenge.lean`, both exit code 0, and the file contains
no `sorry`, `admit`, `axiom`, or `unsafe`.

## Contractible-implies-acyclic milestone

`LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean` now proves, at
general exact-category level (Bühler, Exact categories, Prop. 10.9 pattern):

- `exactAcyclicWithCycles_of_contractingHomotopy` — for `C` preadditive with
  `QuillenExactCategory C` and `IsIdempotentComplete C`, any cochain complex with a
  contracting homotopy `Homotopy (𝟙 K) 0` satisfies `exactAcyclicWithCycles C K`;
- `MetrizableLCA.exactAcyclicWithCycles_of_contractingHomotopy` — the MetrizableLCA
  specialization via the idempotent-completeness instance.

Proof content: the homotopy identity `𝟙 = dNext + prevD` yields orthogonal idempotents
degreewise; splitting the cycle idempotent through `IsIdempotentComplete` produces the
cycle objects; the resulting degreewise split short complexes are conflations via the
project's `QuillenExactCategory.split_conflation`; the differential factors through the
splittings. No legacy `exactAcyclic` ingredient is used. Verified by direct
`lean -j1` on the new file and on `LeanLCAExactChallenge.lean`, both exit code 0, and
the file contains no `sorry`, `admit`, `axiom`, or `unsafe`.

## Homotopy-equivalences corrected weak-equivalence milestone

`LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean` now also proves the first formal M3 bridge:

- `mappingCone_contractingHomotopy_of_homotopyEquiv` — if `e : HomotopyEquiv K L`, then `mappingCone e.hom` has a contracting homotopy. The proof uses `HomotopyCategory.isoOfHomotopyEquiv`, the distinguished mapping-cone triangle, `Triangle.isZero₃_of_isIso₁`, and `HomotopyCategory.isZero_quotient_obj_iff`, not the legacy degreewise acyclicity predicate.
- `boundedExactWeakEquivalenceWithCycles_of_contractibleMappingCone` and `boundedExactWeakEquivalenceWithCycles_id` — contractible mapping cones and identities are corrected bounded weak equivalences by the already-proved contractible-implies-corrected-acyclic theorem.
- `boundedExactWeakEquivalenceWithCycles_containsIdentities`, `boundedExactWeakEquivalenceWithCycles_of_homotopyEquiv`, and `homotopyEquivalences_le_boundedExactWeakEquivalenceWithCycles` — the corrected bounded weak-equivalence class contains all homotopy equivalences of bounded complexes.

This is real progress toward the Q/Qh route, because the corrected chain localization functor
has the Lean-checked input needed to invert homotopy equivalences. The cone/triangle closure
required by the homotopy Verdier route has since been proved directly; a strict direct-chain
localization comparison remains a separate compatibility question.

## Corrected homotopy-object `trW` surface

`LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean` now mirrors the non-legacy part of the old Verdier skeleton with corrected predicates only. It defines the homotopy-category object predicate `exactAcyclicWithCyclesHomotopyObject`, its iso-closure `exactAcyclicWithCyclesHomotopyIsoClosure`, and `boundedHomotopyExactWeakEquivalenceWithCycles`.

The file proves zero-object containment, iso-closure shift stability, `ObjectProperty.trW_isoClosure` compatibility, direct cone-acyclic maps entering the corrected homotopy `trW` class, the conditional equivalence between direct cone acyclicity and `trW` after homotopy-category descent, and the unconditional inclusion `boundedExactWeakEquivalenceWithCycles ≤ boundedHomotopyExactWeakEquivalenceWithCycles`.

The homotopy-descent assumption is now a checked Lean input surface, `ExactAcyclicWithCyclesHomotopyEquivInvarianceInput`. Lean proves this input equivalent to homotopy-category isomorphism closedness of `exactAcyclicWithCyclesHomotopyObject`, and from it proves the direct/homotopy pullback equality `boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_homotopyEquivInvariance`. The surface is no longer only opaque at the stable bridge: `MetrizableLCA.exactAt_of_exactAcyclicWithCycles` now proves the forward direction from corrected cycle-object data to degreewise `ExactAt` using the strict cycle conflations as kernels and the previous cycle projection as an epimorphic kernel lift. The reverse direction is reduced to canonical kernel cycle objects: `MetrizableLCA.exactAtCycleBoundary` is the boundary-to-next-kernel lift, `MetrizableLCA.exactAtCanonicalCycleShortComplex` packages the canonical short complex `kernel d_i -> K_i -> kernel d_{i+1}`, `MetrizableLCA.exists_preimage_kernel_ι_of_apply_eq_zero` proves the elementwise kernel preimage property for the categorical kernel object, `MetrizableLCA.exactAtCycleBoundary_epi_of_exactAt` proves that degreewise `ExactAt` makes the canonical boundary map categorically epi, and `MetrizableLCA.exactAtCycleBoundary_surjective_of_exactAt` remains only as a compatibility lemma for external routes that already supply global forgetful homology preservation. The corrected stable route no longer assumes strict exactness, canonical-boundary surjectivity, or global forgetful homology preservation of the canonical cycle short complexes: its route-specific `MetrizableLCA.ExactAtCanonicalCycleBoundaryTopologyInput` now records only openness of `exactAtCycleBoundary K i` for degreewise `ExactAt` complexes. `MetrizableLCA.exactAtCanonicalCycleStrictInput_of_boundaryTopologyInput` and the compatibility reducer `MetrizableLCA.exactAtCanonicalCycleStrictInput_of_openMapInput` combine that openness with a cochain-homology provider, categorical epimorphy from `ExactAt`, the cokernel-top/open-map surjectivity criterion, the checked closed-kernel embedding, the kernel-preimage lemma, and the algebraic exactness argument to build `MetrizableLCA.ExactAtCanonicalCycleStrictInput` directly. Lean turns that strict input into `ExactAcyclicWithCyclesExactAtReverseDetectionInput`, upgrades it to `ExactAcyclicWithCyclesExactAtDetectionInput` using the checked forward theorem, then to `ExactAcyclicWithCyclesHomologyDetectionInput` with `HomologicalComplex.exactAt_iff_isZero_homology`, identifies the corrected homotopy-object predicate with the homological kernel of the degree-zero homology functor, and finally proves `exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_homologyDetection` using `HomotopyEquiv.toHomologyIso`. It also exposes the generic homological-kernel closure theorem `exactAcyclicWithCyclesHomotopyObject_isTriangulatedClosed2_of_homologicalKernel`; for `MetrizableLCA` this is only an identification aid for now, because the available W821 `CategoryWithHomology` structure is not the abelian mathlib homological-functor instance. The differential and sigma-compact topology reducers now feed that same local boundary-openness surface: `MetrizableLCA.isOpenMap_of_injective_comp_open` and `MetrizableLCA.exactAtCycleBoundary_openMap_of_differential_openMap` reduce boundary openness to ordinary differential openness without any local surjectivity field, while `MetrizableLCA.isOpenMap_of_surjective_sigmaCompact` reduces boundary openness to sigma-compact source plus the still-explicit local boundary surjectivity needed by the open mapping theorem. The compatibility `MetrizableLCA.ExactAtCanonicalCycleOpenMapInput` and `MetrizableLCA.ExactAtCanonicalCycleDifferentialOpenMapInput` no longer bundle global forgetful homology preservation; the sigma-compact compatibility input records only the local boundary surjectivity needed to invoke the open mapping theorem.

The corrected cycle data now also proves degreewise exactness after forgetting topology: `MetrizableLCA.forgetToAddCommGrpCat_exactAt_of_exactAcyclicWithCycles` uses only the strict cycle conflations, kernel inclusions, and boundary factorization, not a global `PreservesHomology` theorem for `forget₂ MetrizableLCA AddCommGrpCat`. Conversely, `MetrizableLCA.exactAt_of_forgetToAddCommGrpCat_exactAt` reflects degreewise abelian-group exactness back to categorical `MetrizableLCA` exactness by proving the relevant kernel lift is surjective, hence epi, using the W821 homology provider only for the target `HasHomology` field. `MetrizableStableBridgeWithCycles.lean` packages this as a forward inclusion `exactAcyclicWithCyclesHomotopyObject MetrizableLCA ≤ forgetfulHomologyKernelFunctor.homologicalKernel`; the new no-input `forgetfulHomologicalKernelExactAtInput` turns forgetful-kernel membership back into degreewise `MetrizableLCA` exactness, and `forgetfulHomologicalKernelReversePayload_of_boundaryTopology` combines that reflection with canonical boundary topology to recover corrected cycle acyclicity. With the resulting reverse payload, Lean identifies the corrected acyclic objects with an abelian-group homological kernel, derives corrected `Closed₂` and homotopy descent from the generic homological-kernel theorem, and builds an alternate stable package needing only boundary topology plus WPP normalized finite-shape transfer. The same reverse payload now also feeds `StableCorePackage`: boundary topology alone supplies corrected preadditivity, zero object, finite products, finite biproducts, finite coproducts, shift additivity, `Pretriangulated`, and `IsTriangulated`, leaving WPP transfer only for finite limits and finite colimits in this route. The older `forgetfulHomologicalKernelExactAtInput_of_preservesHomology` remains as a compatibility theorem, but global forgetful homology preservation is no longer needed to discharge the exactness-reflection piece. `RouteSpecificForgetfulKernelBoundaryInputs` and `RouteSpecificForgetfulKernelBoundaryLeftCalculusInputs` now expose the requested finite limits, finite colimits, `Pretriangulated`, `IsTriangulated`, and left-calculus fields directly from the reduced boundary-only route.

The same file exposes the generic conditional triangulated-object surface: once the corrected
object predicate has `IsTriangulatedClosed₂`, Lean supplies `IsTriangulated` for both the
predicate and its isomorphism closure. It also proves that homotopy descent reflects
`Closed₂` from the iso-closure back to the underlying predicate. For `MetrizableLCA`, the
iso-closure premise is discharged directly below.

For `MetrizableLCA`, that iso-closure premise is now discharged intrinsically. The explicit
pullback cycle objects of a mapping cone give
`MetrizableLCA.exactAcyclicWithCycles_mappingCone`; fullness of the homotopy quotient then
realizes an arbitrary distinguished triangle's first morphism by a cochain map and identifies
its third object with that corrected acyclic cone. Lean packages this as
`metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed3` and derives
`metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_direct` by rotation.

The corrected homotopy surface now carries the two-sided calculus bridge as well: if the corrected iso-closed homotopy object predicate has `IsTriangulatedClosed₂`, Lean proves Verdier left and right calculus for the homotopy `trW` class. With the recorded localized right-adjoint/unit input it pulls left calculus back to `boundedHomotopyExactWeakEquivalenceWithCycles`; with the recorded localized left-adjoint/counit input it pulls right calculus back. With homotopy descent, Lean transfers both calculi to `boundedExactWeakEquivalenceWithCycles`. `MetrizableStableBridgeWithCycles.lean` exposes these as `leftCalculusAssumptionOfHomotopyVerdier` and `rightCalculusAssumptionOfHomotopyVerdier`.

The corrected route now also has the bounded-homotopy object-property layer: `boundedExactAcyclicWithCyclesHomotopyObject` is the inverse image of the corrected iso-closed homotopy acyclic objects along `BoundedHomotopyCategory.ι`, and under corrected-acyclic closed₂ Lean proves it is triangulated. The bounded-source closed₂ input has been discharged directly: Lean proves bounded homotopy objects are closed under third objects by lifting the transported first morphism through the full bounded homotopy quotient and representing the third object by a bounded mapping cone, then derives middle-object `Closed₂` by rotation. This mirrors the Q/Qh structural layer without using legacy bounded weak equivalences as evidence.

The generic bounded homotopy Verdier quotient surface is parameterized by the same closed₂
inputs. For `MetrizableLCA`, both inputs are now unconditional, and
`BoundedDerivedWithCycles.Metrizable.homotopyVerdierTriangulatedPackage` constructs left and
right Verdier calculus, preadditivity, zero object, finite
products/coproducts/biproducts, shift additivity, `Pretriangulated`, and `IsTriangulated` for
the corrected quotient. Its `HomotopyVerdierOrdinaryNerve` remains only the ordinary nerve of
that triangulated category, not a proved stable infinity-category enhancement.

The bounded-complex homotopy pullback class is now checked equivalent to the bounded-homotopy `trW` pullback along `BoundedComplexCategory.homotopyQuotientBounded`. With the explicit homotopy-descent input, Lean identifies direct corrected weak equivalences with that bounded-homotopy `trW` pullback as well.

The bounded homotopy quotient itself is no longer an opaque functor in this layer. `Bounded.lean` now proves bounded complexes are closed under the standard cylinder, defines the internal bounded pre-cylinder, proves the lifted bounded homotopy quotient is full and essentially surjective, and registers `BoundedComplexCategory.homotopyQuotientBounded_isLocalization` as the localization at bounded homotopy equivalences. This provides the first-stage localization input used by the checked composite-localization proof.

The corrected derived surface now derives finite biproducts and finite coproducts from corrected left calculus and finite-product stability. It also derives finite limits from equalizers plus corrected finite products, and finite colimits from coequalizers plus corrected finite coproducts. The equalizer and coequalizer fields now have a corrected WPP transfer surface: `WalkingParallelPairFiniteShapeTransferInputs` packages corrected weak-equivalence stability for the walking parallel pair and the corrected functor-category localization instance, and Lean turns it into equalizers and coequalizers in `DboundedWithCycles MetrizableLCA`. The corrected functor-category localization field is no longer completely opaque: the fixed-target and blueprint APIs reduce it to objectwise inversion, which is proved, plus normalized strict representatives and the two uniqueness obligations required by `Functor.IsLocalization.mk'`. The corrected weak-equivalence class itself is also checked stable under finite coproducts, and its opposite class is checked stable under finite products. The stable bridge now records the independently transported bounded-Verdier semantic fields for preadditivity, zero object, finite products, finite biproducts, finite coproducts, all shift functor additivity, suspension additivity, pretriangulated structure, and triangulated structure; its finite-limit and finite-colimit fields are assembled from those finite product/coproduct fields plus the corrected WPP normalized transfer input.

The corrected Q/Qh comparison layer now exists as ordinary category API. `ExactAcyclicWithCyclesHomotopy.lean` defines `ExactAcyclicWithCyclesHomotopyVerdierCategory` and `BoundedHomotopyDerivedCategoryWithCycles`, the corrected homotopy-pullback localization, and constructs its comparison functors to the ambient corrected homotopy Verdier quotient and to the bounded corrected homotopy Verdier quotient. It also defines the bounded-to-ambient Verdier comparison, `DboundedWithCycles.homotopyComparison`, routed and direct ambient Verdier comparisons, routed and direct bounded Verdier comparisons, their localization-commuting isomorphisms, the routed/direct comparison isomorphisms, the bounded-to-ambient composition isomorphisms, and the conditional equivalence `DboundedWithCycles.homotopyComparisonEquivalenceOfIsoClosed` under homotopy descent. These declarations use only `boundedExactWeakEquivalenceWithCycles`, `boundedHomotopyExactWeakEquivalenceWithCycles`, and corrected `trW` localizer morphisms.

The direct corrected weak-equivalence localizer now has a checked localized-equivalence reduction for the bounded corrected homotopy Verdier quotient. `BoundedHomotopyExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.of_comp` proves the composite `BoundedComplexCategory.homotopyQuotientBounded C ⋙ (boundedExactAcyclicWithCyclesHomotopyObject C).trW.Q` is a localization of the homotopy-pullback class `boundedHomotopyExactWeakEquivalenceWithCycles C`, using mathlib's `Functor.IsLocalization.comp`, the bounded homotopy quotient localization, the already-proved pullback equality, and a new full/essentially-surjective map-inverse-image lemma for morphism properties. `BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput.ofHomotopy` turns this checked homotopy composite into the direct localization input using homotopy descent. From that derived direct input, `boundedExactWeakEquivalenceWithCyclesToBoundedVerdier_isLocalizedEquivalence` applies mathlib's `LocalizerMorphism.IsLocalizedEquivalence.of_isLocalization_of_isLocalization` to prove that the direct localizer morphism is a localized equivalence. This removes the previous homotopy-level composite-localization assumption and does not consume legacy weak equivalences.

That localized-equivalence reduction now also supplies independent corrected preadditivity, zero-object, finite-product, finite-coproduct, finite-biproduct, shift-additivity, pretriangulated, and triangulated routes. `DboundedWithCycles.preadditiveOfBoundedVerdierLocalizationInput` transports preadditivity back from the bounded corrected homotopy Verdier quotient along the induced equivalence using mathlib's fully-faithful preadditive transfer, `DboundedWithCycles.hasZeroObjectOfBoundedVerdierLocalizationInput` reflects a zero object through the same equivalence, the finite product/coproduct/biproduct builders transport the finite product and coproduct instances supplied by the pretriangulated bounded Verdier quotient, `DboundedWithCycles.shiftFunctor_additiveOfBoundedVerdierLocalizationInput` transports additivity of localized shifts through the same shift-compatible localized functor, `DboundedWithCycles.pretriangulatedOfBoundedVerdierLocalizationInput` pulls back the distinguished-triangle predicate and pretriangulated axioms through the same corrected localized equivalence, and `DboundedWithCycles.isTriangulatedOfBoundedVerdierLocalizationInput` applies mathlib's fully faithful triangulated functor transfer after proving the localized functor sends the pulled-back distinguished triangles to the bounded Verdier distinguished triangles. The metrizable bridge exposes these fields with matching names in `BoundedDerivedWithCycles.Metrizable`. Corrected acyclic closed₂ is now unconditional for `MetrizableLCA`; only the direct composite-localization comparison remains conditional when transporting these fields back to `DboundedWithCycles`.

The direct-chain compatibility bridge also retains a conditional constructor.
`RouteSpecificInputs` now has exactly two fields: canonical boundary topology and normalized
WPP transfer. Intrinsic cone closure removed the former strict-realization field.
`RouteSpecificLeftCalculusInputs` adds only
`BoundedHomotopyWithCyclesLocalizedRightAdjointInput MetrizableLCA`, so
`routeSpecificInputNames` and `routeSpecificLeftCalculusInputNames` have lengths two and three,
respectively. These declarations remain useful compatibility reducers, but their raw-chain
calculus and ordinary finite-(co)limit conclusions are not the honest Verdier target.

The same bridge exposes an alternate forgetful-kernel compatibility route. Its proved forward inclusion sends corrected acyclic homotopy objects into the abelian-group homological kernel of `forgetfulHomologyKernelFunctor`; boundary topology supplies the reverse payload because exactness reflection from the forgetful homological kernel is Lean-checked directly. `RouteSpecificForgetfulKernelInputs` records the abstract two-field reverse-payload route, while the concrete `RouteSpecificForgetfulKernelBoundaryInputs` has exactly two legacy stable-package fields, canonical boundary topology and WPP normalized finite-shape transfer. The WPP-free `stableCorePackageOfForgetfulKernelBoundaryTopology`, `pretriangulatedOfForgetfulKernelBoundaryTopology`, and `isTriangulatedOfForgetfulKernelBoundaryTopology` show that the ordinary triangulated fields do not wait on WPP transfer. The exactness-reflection variants remain compatibility wrappers. `currentMetrizableStableBridgeWithCyclesProductSuccessClaimed` remains false.

The new unconditional homotopy Verdier package consumes none of those topology, detection,
strict-realization, localized-adjoint, or WPP inputs. It also consumes no legacy
`boundedExactWeakEquivalence` or legacy `Dbounded` fact. Those route-specific interfaces now
document only the optional comparison back to the direct chain localization and the obsolete
literal finite-(co)limit package, not the construction of the honest ordinary triangulated
Verdier quotient.

## Literal corrected-package blocker (2026-07-10)

The route inputs above are useful conditional interfaces, but three of them must not be
presented as an assumption surface that is expected to be inhabited. The detailed audit is
[`audit/BLOCKER_CORRECTED_DBOUNDED_LITERAL_FIELDS.md`](BLOCKER_CORRECTED_DBOUNDED_LITERAL_FIELDS.md).

- Raw chain-level cone quasi-isomorphisms do not in general satisfy strict
  Gabriel--Zisman Ore calculus. The valid calculus target is the corrected Verdier class
  `P.trW` in the bounded homotopy category.
- The ordinary triangulated category `DboundedWithCycles MetrizableLCA` is not expected to
  have categorical finite limits or colimits. Those fields would force splitting behavior
  incompatible with the strict non-split conflation `ℤ ↪ ℝ ↠ 𝕋`.
- Corrected weak equivalences are not stable under walking-parallel-pair equalizers or
  coequalizers merely because they are objectwise corrected weak equivalences. Kernels and
  cokernels of maps between acyclic complexes can have nonzero homology, already over a
  field. Thus the WPP stability field is a false transfer premise, not the missing proof of
  ordinary finite limits or colimits.

The intrinsic cone/extension frontier is now complete for the needed metrizable mapping-cone
case. Lean constructs the cone cycle objects, proves their displayed short complexes are
conflations, derives unconditional `Closed₃`/`Closed₂` for the corrected homotopy
iso-closure, and constructs the ordinary triangulated bounded homotopy Verdier package.

The remaining honest frontier is task-4 construction. The repository now has compiler-checked
quasicategory semantics for equivalences, inner-fibrant replacement, relative edge inversion,
pointedness, finite infinity-(co)limits, and bicartesian-square stability. It also has the
correct multiplicative relative subcategory generated by the corrected metrizable weak
equivalences. The pairwise higher mapping carriers now form a genuine simplicial category,
and the homotopy coherent nerve has a bundled quasicategorical replacement. A second,
ordinary-nerve cell presentation freely forces every generated corrected weak arrow to become
an equivalence and has a bundled quasicategorical replacement; the inversion theorem is
checked. Its infinity-localization universal property remains absent. The ordinary nerve of
the already-localized Verdier category cannot substitute for either construction because it
has already discarded higher mapping spaces.

The repository now uses `CochainComplex.HomComplex`, nonpositive truncation, and Dold--Kan to
build the pairwise simplicial mapping carriers. It proves their vertices are precisely bounded
cochain maps, transports associative unital composition at degree zero, and extends identities
through all simplicial degrees. `DgMappingEnrichment` now states the exact remaining coherent
composition target. `inverseLaxMonoidalOfNormalizedOplax` proves that its Dold--Kan coherence
can be generated by adjunction. The Hom complexes now live in the required integer-module
tensor category via `dgMappingZModuleChainComplex`; `dgCochainCompTensor` supplies the actual
tensor morphism on every homogeneous pair; and their Dold--Kan carriers retain the correct
vertices and identity simplices. `dgHomZModuleCompositionReversed` now assembles those maps into
a genuine chain map before truncation, using the factor order dictated by total-complex signs.
The directly constructed and transported carriers are now canonically isomorphic, including
the cycle-object boundary of the truncation. Composition now exists on every summand of the
tensor of the nonpositive truncations, including a proved cycle-valued boundary component.
`dgTruncatedCompositionReversed` proves that these maps commute with the total differential and
assembles them into a genuine chain map. The transported chain map is now connected
parametrically to the Dold--Kan inverse tensorator and to an underlying simplicial-set
composition. The Alexander--Whitney formula is now a natural chain map: finite cut projections
detect the target maps, internal faces reindex to the source differential, and the two boundary
faces cancel with opposite signs. Composing with the normalized Moore inclusion and `PInfty`
retractions gives the natural normalized chain map. Its unit map is constructed and identified
with the standard alternating-chain augmentation. Both oplax naturality laws, both unit
coherence laws, and associativity are proved. The unnormalized associativity proof detects maps
on every triple tensor summand, and the normalized proof transports it through the Moore
inclusion and retractions. The required source-projector fixed-point law for the compressed
Alexander--Whitney map is proved by degeneracy annihilation, and
`normalizedMooreOplaxMonoidal` packages the resulting structure. The direct chain composition
now satisfies both unit laws and strict associativity. These laws define a chain enrichment on
the opposite bounded-complex object type; Dold--Kan lax transport, enriched opposite, and
degreewise forgetful transport produce `DirectDGSimplicialCategory`. Its enriched Hom is the
direct Dold--Kan mapping simplicial set. `directDGHomotopyCoherentNerve` and
`directDGQCat` provide the nerve and a bundled quasicategory replacement, with an inner-anodyne
unit. A separate degree-zero calculation now proves that the transported normalized
Alexander--Whitney composition agrees on vertices with ordinary bounded-complex composition.
The work still requires a relative infinity-localization at
`GeneratedWeakEquivalence`, stability of the localized carrier, and homotopy-category
comparison with the corrected Verdier quotient. The success marker therefore remains false.

The ordinary-nerve route now also has a concrete cell model. `EquivalenceForcing.lean` takes
the coproduct of all selected `1`-simplices, attaches one free-living equivalence to each by a
pushout, and applies inner-fibrant replacement. The generic pushout calculation and the
ordinary-nerve isomorphism lemma prove selected-edge inversion. Its metrizable specialization
packages the result as a `RelativeInfinityFunctor` and proves inversion both for
`GeneratedWeakEquivalence` and for the raw corrected class. It also packages the same fact as
`InvertsMarkedEdges` for the full relative marking. Pinned mathlib still lacks the
functor-quasicategory, free-equivalence extension, inner-anodyne mapping-invariance, and Joyal
homotopy-pushout theorems needed to promote this carrier to a proved infinity-localization.
`Localization.lean` now states the missing universal property at the full mapping-quasicategory
level, separately from an explicitly 2-truncated hom-category version. Full vertex-spanned
subcomplexes are proved to preserve quasicategories, and the ambient functor-quasicategory
closure is reduced to the precise inner-horn pushout-product theorem missing from v4.30. The
canonical internal-Hom precomposition is proved to land in the relative mapping subcomplex;
its bicategorical equivalence remains unproved. The inversion also yields a canonical functor
from the corrected ordinary localization into the homotopy category of the equivalence-forcing
carrier. Proving that functor an equivalence remains part of the Verdier comparison frontier.

The full published verification suite passes after the addition: the project and audit
dependency builds, generated-file checks, forbidden-token checks, declaration checks,
external-source checks, axiom checks, and diff-hygiene audits all exited successfully. One
historical W1496 assertion in `audit/OriginalFourTaskCompletionDeclarations.lean` still expected
the pre-`4eace4f7` value `false`; it now matches that commit's source and contract value `true`.
This audit-only correction does not change the corrected bridge marker below.

## Conclusion

The invalid degreewise acyclicity definition is isolated from the corrected construction.
The corrected route now has explicit cycle data, intrinsic metrizable mapping-cone closure,
unconditional distinguished-triangle closure of the corrected homotopy iso-closure, two-sided
Verdier calculus in the bounded homotopy category, and an unconditional ordinary package with
preadditivity, zero object, finite products/coproducts/biproducts, shift additivity,
`Pretriangulated`, and `IsTriangulated`.

This proves the honest ordinary triangulated bounded-derived semantics and now formalizes the
first genuine quasicategory layers needed to go beyond it, including a coherent Dold--Kan
simplicial category, its homotopy coherent nerve, a bundled quasicategory replacement, and the
bicartesian-square definition of stability. It also constructs an ordinary-nerve
equivalence-forcing quasicategory and proves that all corrected weak equivalences are inverted.
It also formalizes the full mapping-quasicategory localization specification and constructs
the canonical ordinary comparison functor out of the corrected localization. It does not yet
construct the stable derived infinity category: inhabitation of that universal property,
comparison with the dg carrier, the stability proof, and proof that the ordinary comparison
is an equivalence remain. Nor does it justify raw-chain Ore calculus or ordinary finite
limits/colimits. Therefore the corrected bridge success marker must remain false until the
localized stable-infinity construction is inhabited and verified.
