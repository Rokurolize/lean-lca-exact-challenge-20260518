# Next Steps: cycle-object exact acyclicity

Remote branch: `cycle-object-exact-acyclic-handoff-20260708`.

Implemented files:

- `LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean`
- `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.lean`
- `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean`
- `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean`
- `LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.lean`
- `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean`
- `LeanLCAExactChallenge/Infinity/Basic.lean`
- `LeanLCAExactChallenge/Infinity/FunctorQuasicategory.lean`
- `LeanLCAExactChallenge/Infinity/InnerFibrantReplacement.lean`
- `LeanLCAExactChallenge/Infinity/Relative.lean`
- `LeanLCAExactChallenge/Infinity/Localization.lean`
- `LeanLCAExactChallenge/Infinity/EquivalenceForcing.lean`
- `LeanLCAExactChallenge/Infinity/EquivalenceIntervalExtension.lean`
- `LeanLCAExactChallenge/Infinity/InnerAnodyneMapping.lean`
- `LeanLCAExactChallenge/Infinity/Limits.lean`
- `LeanLCAExactChallenge/Infinity/Stable.lean`
- `LeanLCAExactChallenge/Infinity/DoldKanMonoidal.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitney.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitneyProjectors.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitneyUnits.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitneyCoassociativity.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitneyAssociativityCore.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitneyAssociativityNaturality.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitneyAssociativityLeft.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitneyAssociativityRight.lean`
- `LeanLCAExactChallenge/Infinity/AlexanderWhitneyAssociativity.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableRelative.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableEquivalenceForcing.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableEquivalenceForcingHomotopy.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGMapping.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGMappingZModule.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGMappingZModuleUnits.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGMappingZModuleAssociativity.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGMappingZModuleVertexAlexanderWhitney.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGMappingZModuleVertexTensorator.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGMappingZModuleVertexComposition.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGMappingZModuleVertices.lean`
- `LeanLCAExactChallenge/Infinity/MetrizableDGSimplicialCategory.lean`
- `audit/SCOPE.md`
- `audit/REPORT.md`
- `audit/BLOCKER_CORRECTED_DBOUNDED_LITERAL_FIELDS.md`

Verification command summary:

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
lake env lean -j1 LeanLCAExactChallenge/Infinity/MetrizableDGMapping.lean
lake env lean -j1 LeanLCAExactChallenge/Infinity/Stable.lean
lake build LeanLCAExactChallenge
lake env lean -j1 audit/OriginalFourTaskCompletionDeclarations.lean
lean -j1 LeanLCAExactChallenge.lean
```

Remaining tasks:

1. Continue the selected genuine stable-infinity target from the new `Infinity` modules.
   The pairwise mapping carriers are now constructed from `CochainComplex.HomComplex`,
   nonpositive truncation, and Dold--Kan. `inverseLaxMonoidalOfNormalizedOplax` proves that
   all Dold--Kan inverse coherences follow automatically from an Alexander--Whitney oplax
   structure on normalized
   Moore chains. `dgCochainCompTensor` now realizes every homogeneous Hom-complex pairing as
   an actual integer-module tensor-product morphism. `dgHomZModuleCompositionReversed` now
   assembles the reversed summands into a morphism of the direct integer-module Hom cochain
   complexes, with its differential law proved from `δ_comp`. Reversal is required by mathlib's
   total-complex sign convention. The direct and transported Hom complexes are now connected
   both before and after nonpositive truncation by canonical isomorphisms; the boundary degree
   uses preservation of cycles. Composition on every tensor summand of the two truncations is
   now constructed; in boundary degree zero it is proved to be a cocycle and lifted to the
   output cycle object. `dgTruncatedCompositionReversed` now proves that the assembled maps
   commute with the chain differentials, including both boundary cases and the total-complex
   sign in the positive-positive case. `dgMappingZModuleSimplicialComposition` now applies the
   Dold--Kan inverse tensorator parametrically, and `dgMappingZModuleSSetComposition` supplies
   the resulting underlying simplicial-set composition. The explicit Alexander--Whitney
   front/back summands, their finite degreewise sum and naturality, the normalized degreewise
   candidate, and the key face/boundary identities are now formalized in
   `Infinity/AlexanderWhitney.lean`. Finite cut projections now jointly detect maps into total
   tensor degrees, recover the selected AW summand, and compute both tensor differential
   contributions, including the `(-1)^p` sign on the second factor. Internal-face reindexing
   and cancellation of the two boundary terms are now proved, and projection extensionality
   upgrades the calculation to the full natural chain map `alternatingAlexanderWhitney`.
   The normalized inclusion and two `PInfty` retractions now assemble the natural chain map
   `normalizedAlexanderWhitney`; its monoidal-unit map is also constructed and identified with
   the standard alternating-chain augmentation. Both unit coherence laws are now proved in
   `Infinity/AlexanderWhitneyUnits.lean`, including their normalized forms after transport
   through the Moore inclusion and `PInfty` retractions.
   `Infinity/AlexanderWhitneyProjectors.lean` proves the correct retained-projector law:
   the compressed map is fixed by `PInfty` on its diagonal source because it annihilates every
   source degeneracy after the two output projectors. Do not replace this with the false claim
   that raw Alexander--Whitney itself lands in the normalized tensor subcomplex.
   The unnormalized Alexander--Whitney map is now proved coassociative by detection on every
   triple tensor summand. The normalized associativity proof transports that equality through
   the Moore inclusion and the three retractions. Together with the two unit laws this gives
   the actual inhabitant `normalizedMooreOplaxMonoidal` of `NormalizedMooreOplaxMonoidal`.
   The direct carrier now has exact chain-level left and right unit laws and associativity.
   These laws inhabit an `EnrichedCategory` on `ComplexCategoryᵒᵖ`; the actual Dold--Kan
   lax structure transports it to simplicial integer modules. Taking the enriched opposite,
   transporting degreewise to simplicial sets, and applying `ForgetEnrichment` gives the
   genuine `DirectDGSimplicialCategory`. Its enriched Hom is definitionally the direct
   Dold--Kan mapping simplicial set. `directDGHomotopyCoherentNerve` and the chosen
   inner-fibrant replacement `directDGQCat` now supply a bundled genuine quasicategory and an
   inner-anodyne replacement map.
   The transported normalized Alexander--Whitney composition is now also computed on
   vertices: `dgMappingZModuleVerticesEquivBoundedMorphisms_comp` proves that it is exactly
   ordinary composition of bounded-complex morphisms.
   Independently, `EquivalenceForcing.lean` constructs the standard ordinary-nerve cell
   presentation that attaches a free-living equivalence to every selected weak arrow and then
   applies inner-fibrant replacement. Its metrizable specialization is the genuine
   quasicategory `metrizableEquivalenceForcingQCat`. Lean proves that its canonical map sends
   every arrow in `GeneratedWeakEquivalence`, and hence every raw corrected weak equivalence,
   to an equivalence edge. Each selected arrow now has an explicit
   `EquivalenceIntervalExtension`, so this is coherent inversion data, not yet a localization
   theorem.
   `Localization.lean` records both the explicitly 2-truncated hom-category localization
   property and the honest mapping-quasicategory universal property, using the full mapping
   subcomplex spanned by weak-equivalence-inverting functors. No concrete candidate is claimed
   to inhabit either complete specification. Full vertex-spanned subcomplexes, including the
   relative mapping object, are proved to be quasicategories whenever their ambient mapping
   object is. `FunctorQuasicategory.lean` reduces that ambient closure to the exact inner-horn
   pushout-product statement absent from v4.30; it does not construct an inhabitant. The
   equivalence-forcing map is now packaged as inverting the complete marked edge class, so it
   discharges the inversion field of both specifications. Precomposition by any such map is
   proved to factor canonically through the relative full mapping subcomplex; the metrizable
   candidate exposes this map as `metrizableEquivalenceForcingMappingComparison`. Its
   bicategorical equivalence is not proved. The inversion data also induces the canonical
   ordinary functor
   `metrizableCorrectedDerivedToEquivalenceForcingHomotopy` from the corrected ordinary
   localization to the homotopy category of the equivalence-forcing quasicategory, together
   with its localization factorization isomorphism. Its equivalence is not yet proved.
   `EquivalenceIntervalExtension.lean` isolates a vertex-level missing condition:
   `EveryEquivalenceEdgeExtends Q` says that every equivalence edge of a quasicategory extends
   coherently to the free-living equivalence. Lean proves that an extension implies
   equivalence, extends ordinary-nerve isomorphisms explicitly, and uses the separate
   2-truncated API to produce an inverse edge with both triangle fillers. No general vertex
   converse is claimed. Even that converse would be insufficient for localization: the full
   parametrized restriction map must be a categorical equivalence onto the equivalence-edge
   mapping subcomplex. The equivalence-forcing map itself already carries chosen extensions
   for its selected arrows.
   `InnerAnodyneMapping.lean` isolates the other replacement-side input: inner-horn
   pushout-products with arbitrary monomorphisms. Under that explicit property, restriction
   along any inner-anodyne map has the right lifting property against every monomorphism.
   Such a restriction has a strict section and a fiberwise free-equivalence contraction, but
   the pinned Cat-enriched QCat API does not yet turn that contraction into the required
   `IsBicategoricalEquivalence`; no such conclusion is asserted.
   The remaining task-4 frontier is to prove the infinity-localization universal property,
   compare this ordinary-nerve carrier with the coherent dg carrier, prove the localized
   quasicategory stable, and identify its homotopy category with the corrected ordinary
   Verdier quotient. Pinned mathlib v4.30 has no ready-made quasicategorical or simplicial
   localization API, so do not present either current carrier as the derived infinity
   category.
   Do not use the ordinary nerve of the Verdier quotient as the enhancement.
2. If compatibility with the direct chain localization remains required, prove the
   composite-localization statement recorded by
   `BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput`. Do not replace it
   with the generally false raw-chain Ore calculus claim.
3. Revise the success-bearing package to request the honest ordinary stable core: zero object,
   finite products, finite coproducts, finite biproducts, shift additivity,
   `Pretriangulated`, and `IsTriangulated`. Raw chain-level calculus and ordinary finite
   limits/colimits are blocked by `audit/BLOCKER_CORRECTED_DBOUNDED_LITERAL_FIELDS.md` and must
   not be filled by assumptions. Keep the success marker false until this specification change
   or a genuine stable-infinity construction is complete.
4. If migrating to mathlib v4.31, do so only in an isolated sibling worktree. The migration
   must update `lean-toolchain` and Lake dependencies coherently, must not reuse `v4.30.0`
   compiled artifacts as evidence, and must pass the baseline checks. The useful added theorem
   is internal-hom quasicategory closure; the migration does not provide dg localization,
   stability, or monoidal Dold--Kan.
5. Migrate legacy `exactAcyclic` lemmas theorem-by-theorem only when the corresponding corrected theorem is needed.
6. Keep the legacy degreewise `boundedExactWeakEquivalence` route labeled as compatibility-only.

Completed corrected closure milestones:

- Functorial corrected cycle objects: `MetrizableLCA.cyclesDataMap`,
  `cyclesDataMap_incl`, and `cyclesData_proj_map` construct and characterize the map on
  chosen cycle objects induced by any cochain map.
- Intrinsic mapping-cone closure: `MetrizableLCA.cyclesDataMappingCone` constructs the cone
  cycle data, while `MetrizableLCA.mappingConeCyclesConflation` and
  `MetrizableLCA.exactAcyclicWithCycles_mappingCone` prove that the mapping cone of a map
  between corrected acyclic complexes is corrected acyclic.
- Idempotent completeness: `IsIdempotentComplete MetrizableLCA.{u}` in
  `LeanLCAExactChallenge/LCA/IdempotentComplete.lean`, foundation for
  homotopy-invariance and contractible-implies-acyclic for
  `exactAcyclicWithCycles`.
- Contractible implies corrected-acyclic:
  `exactAcyclicWithCycles_of_contractingHomotopy` (general exact-category level over
  `IsIdempotentComplete`) and its MetrizableLCA specialization in
  `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean`.
- Homotopy equivalences of bounded complexes are corrected weak equivalences:
  `mappingCone_contractingHomotopy_of_homotopyEquiv`,
  `boundedExactWeakEquivalenceWithCycles_of_homotopyEquiv`, and
  `homotopyEquivalences_le_boundedExactWeakEquivalenceWithCycles` in
  `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean`.
- Corrected homotopy-object `trW` surface:
  `exactAcyclicWithCyclesHomotopyObject`,
  `ExactAcyclicWithCyclesHomotopyEquivInvarianceInput`,
  `exactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance`,
  `exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_isClosedUnderIsomorphisms`,
  `exactAcyclicWithCyclesHomotopyEquivInvarianceInput_iff_isClosedUnderIsomorphisms`,
  `exactAcyclicWithCyclesHomotopyIsoClosure`,
  `exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2`,
  `exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_of_homotopyObject`,
  `exactAcyclicWithCyclesHomotopyObject_isTriangulated_of_isTriangulatedClosed2`,
  `exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_isTriangulated`,
  `exactAcyclicWithCyclesHomotopyObject_trW_hasRightCalculusOfFractions_of_isTriangulated`,
  `exactAcyclicWithCyclesHomotopyObject_trW_hasLeftCalculusOfFractions_of_closed2`,
  `exactAcyclicWithCyclesHomotopyIsoClosure_trW_hasLeftCalculusOfFractions_of_closed2`,
  `boundedExactAcyclicWithCyclesHomotopyObject`,
  `boundedExactAcyclicWithCyclesHomotopyObject_isTriangulated_of_closed2`,
  `BoundedExactAcyclicWithCyclesHomotopyVerdierCategory`,
  `boundedExactAcyclicWithCyclesHomotopyObjectToIsoClosure_trW`,
  `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_pretriangulated_of_closed2`,
  `boundedExactAcyclicWithCyclesHomotopyVerdierCategory_isTriangulated_of_closed2`,
  `boundedHomotopyExactWeakEquivalenceWithCyclesToBoundedHomotopy_trW`,
  `boundedHomotopyExactWeakEquivalenceWithCycles_eq_boundedHomotopy_trW_inverseImage`,
  `boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopy_trW_of_homotopyEquivInvariance`,
  `boundedHomotopyWithCyclesLocalizedVerdierFunctor`,
  `BoundedHomotopyWithCyclesLocalizedRightAdjointInput`,
  `BoundedHomotopyWithCyclesLocalizedLeftAdjointInput`,
  `boundedHomotopyExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint`,
  `boundedHomotopyExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint`,
  `boundedExactWeakEquivalenceWithCycles_hasLeftCalculusOfFractions_of_closed2Adjoint`,
  `boundedExactWeakEquivalenceWithCycles_hasRightCalculusOfFractions_of_closed2Adjoint`,
  `boundedHomotopyExactWeakEquivalenceWithCycles`, and the checked inclusion
  `boundedExactWeakEquivalenceWithCycles_le_boundedHomotopyExactWeakEquivalenceWithCycles`
  plus the checked conditional equality
  `boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_homotopyEquivInvariance`
  in `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean`.
- Unconditional corrected homotopy Verdier triangulation:
  `metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed3`,
  `metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_direct`, and
  `BoundedDerivedWithCycles.Metrizable.homotopyVerdierTriangulatedPackage` supply the
  corrected Verdier calculus and ordinary triangulated semantics without topology,
  homology-detection, strict-realization, or WPP-transfer inputs. Its
  `HomotopyVerdierOrdinaryNerve` is only an ordinary nerve, not a proved stable
  infinity-category enhancement.
- Direct-to-bounded-Verdier localized-equivalence reduction: `BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput` and `boundedExactWeakEquivalenceWithCyclesToBoundedVerdier_isLocalizedEquivalence` in `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean`.
- Independent bounded-Verdier preadditivity, zero-object, finite-product, finite-coproduct, finite-biproduct, and shift-additivity transfer: `DboundedWithCycles.preadditiveOfBoundedVerdierLocalizationInput`, `DboundedWithCycles.hasZeroObjectOfBoundedVerdierLocalizationInput`, `DboundedWithCycles.hasFiniteProductsOfBoundedVerdierLocalizationInput`, `DboundedWithCycles.hasFiniteCoproductsOfBoundedVerdierLocalizationInput`, `DboundedWithCycles.hasFiniteBiproductsOfBoundedVerdierLocalizationInput`, `DboundedWithCycles.shiftFunctor_additiveOfBoundedVerdierLocalizationInput`, and the matching `BoundedDerivedWithCycles.Metrizable.*BoundedVerdierLocalizationInput` wrappers.

- Mapping-cone isomorphism invariance.
- Shift closure and bounded weak-equivalence shift compatibility.
- MetrizableLCA binary biproduct closure.
- MetrizableLCA finite-product closure via W151 Option-product decomposition.
- Corrected bounded weak-equivalence finite-product and finite-coproduct stability over default-universe `MetrizableLCA`, plus finite-product stability for the opposite corrected weak-equivalence class.
- Separate corrected localization surface: `BoundedDerivedCategoryWithCycles`, `DboundedWithCycles`, and `DboundedWithCycles.localization`.
- Corrected finite biproduct/coproduct semantic surface: `DboundedWithCycles.hasFiniteBiproductsOfStableFiniteProducts`, `DboundedWithCycles.hasFiniteCoproductsOfStableFiniteProducts`, `DboundedWithCycles.MetrizableLCA.hasFiniteBiproducts`, and `DboundedWithCycles.MetrizableLCA.hasFiniteCoproducts`.
- Corrected Metrizable stable bridge assumption surface: `BoundedDerivedWithCycles.Metrizable.StablePackage`, explicit with-cycles left calculus, derived preadditive/zero/finite-products/finite-biproducts/finite-coproducts/shift-additivity fields, and remaining finite-limit/finite-colimit/pretriangulated/triangulated assumptions.
- Corrected Metrizable homotopy Verdier calculus builders: `BoundedDerivedWithCycles.Metrizable.leftCalculusAssumptionOfHomotopyVerdier` and `BoundedDerivedWithCycles.Metrizable.rightCalculusAssumptionOfHomotopyVerdier`.
- Version-policy blocker recorded: the repository remains verified on its coherent `v4.30.0` pin because the restored manifest, mathlib checkout, and compiled dependency cache are `v4.30.0`-only; stable `v4.31.0` requires a separate coherent dependency migration and full baseline verification.

Note: the older checkout at `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518` had unrelated dirty files before this work began. Continue using the clean integration worktree unless the user explicitly asks otherwise.
