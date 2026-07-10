# Blocker: literal corrected `DboundedWithCycles` package

Date: 2026-07-10

## Blocked objective

The active objective requires all of the following simultaneously:

- `(boundedExactWeakEquivalenceWithCycles MetrizableLCA).HasLeftCalculusOfFractions`
  in `BoundedComplexCategory MetrizableLCA`;
- `HasFiniteLimits (DboundedWithCycles MetrizableLCA)`;
- `HasFiniteColimits (DboundedWithCycles MetrizableLCA)`;
- `Pretriangulated (DboundedWithCycles MetrizableLCA)`;
- `IsTriangulated (DboundedWithCycles MetrizableLCA)`.

The last two are valid derived-category targets. The first three are not honest targets for
the raw chain localization and its ordinary homotopy category.

## Reproducible Lean state

After rebuilding the modified dependency chain through
`MetrizableStableBridgeWithCycles.lean`, a direct `#synth` probe reports:

```text
failed to synthesize HasFiniteLimits (DboundedWithCycles MetrizableLCA)
failed to synthesize HasFiniteColimits (DboundedWithCycles MetrizableLCA)
failed to synthesize HasZeroObject (DboundedWithCycles MetrizableLCA)
failed to synthesize Preadditive (DboundedWithCycles MetrizableLCA)
failed to synthesize
  (boundedExactWeakEquivalenceWithCycles MetrizableLCA).HasLeftCalculusOfFractions
```

The `Pretriangulated` and `IsTriangulated` probes stop first on their prerequisite instances;
the bridge currently constructs those structures only from explicit route inputs.

The dependency-ordered direct checks all exit successfully, including:

```text
ExactAcyclicCorrect.lean
ExactAcyclicWithCyclesClosure.lean
ExactAcyclicWithCyclesContractible.lean
BoundedDerivedWithCycles.lean
ExactAcyclicWithCyclesHomotopy.lean
MetrizableStableBridgeWithCycles.lean
LeanLCAExactChallenge.lean
```

Thus this is not a compiler failure or stale-olean artifact. It is the remaining semantic
frontier.

## Mathematical obstruction

### Raw chain-level calculus

Cone quasi-isomorphisms in the category of complexes do not in general satisfy the strict
Gabriel--Zisman Ore axioms. The standard fraction calculus is available after quotienting by
chain homotopy, for the Verdier class `P.trW` in the bounded homotopy category. A mapping
cylinder can replace a diagram by one that commutes up to homotopy; that does not establish
the strict equality required by `MorphismProperty.HasLeftCalculusOfFractions` in the original
chain category.

The current `BoundedHomotopyWithCyclesLocalizedRightAdjointInput` is therefore not a missing
routine construction. It is a sufficient assumption aimed back at the wrong source-level
conclusion. The honest comparison target is a functor

```text
Lh : BoundedHomotopyCategory MetrizableLCA ⥤
  DboundedWithCycles MetrizableLCA
```

with `Lh.IsLocalization P.trW` and `Lh.CommShift ℤ`.

### Ordinary finite limits and colimits

An ordinary triangulated derived category generally has weak kernels and weak cokernels from
triangles, not categorical kernels and cokernels. In a triangulated category every categorical
monomorphism splits and every categorical epimorphism splits. Applying categorical kernels or
cokernels to the triangle induced by the non-split strict conflation

```text
ℤ ↪ ℝ ↠ 𝕋
```

would force a splitting. No continuous retraction `ℝ ⟶ ℤ` exists, and no continuous section
`𝕋 ⟶ ℝ` exists. Consequently the ordinary category cannot honestly carry both the requested
triangulated structure and all finite limits/colimits.

The current walking-parallel-pair route also assumes a false preservation principle. Even for
bounded complexes of vector spaces, an objectwise quasi-isomorphism of parallel-pair diagrams
need not remain a quasi-isomorphism after taking the degreewise equalizer: a map between
acyclic complexes can have a kernel with nonzero homology. Hence
`WalkingParallelPairFiniteShapeTransferInputsFromNormalized` must not be treated as a proof
obligation that is expected to be inhabited.

## Attempts and evidence

- Inspected and rebuilt the corrected cycle-object, closure, contractible, homotopy, localization,
  and stable-bridge modules in dependency order.
- Confirmed that no unconditional instance for any of the five requested fields is currently
  synthesized.
- Audited the boundary-topology, WPP transfer, and localized-adjoint reducers. They are
  conditional interfaces, not constructions of their inputs.
- Checked the repository handover's M3--M9 architecture against the current sources.
- Obtained an independent architecture review over the bridge, homotopy layer, localization
  layer, and handover. Its recommendation agrees with the local evidence: retain the Verdier
  route for triangulation and reject the three literal source/ordinary-category targets.
- Verified externally that the standard exact-category construction is the Verdier quotient of
  the homotopy category by acyclic complexes (Theo Bühler, *Exact Categories*, section 10), and
  that raw complexes and their homotopy category have different fraction-calculus behavior.

## Lean-proved progress that remains valid

- contractible complexes are `exactAcyclicWithCycles`;
- homotopy equivalences of bounded complexes are
  `boundedExactWeakEquivalenceWithCycles`;
- `MetrizableLCA.cyclesDataMap` constructs the map induced by any cochain map on chosen
  corrected cycle objects, with both inclusion and projection naturality proved;
- `MetrizableLCA.cyclesDataMappingCone` constructs corrected cycle data on the mapping cone
  of a map between corrected acyclic complexes, and
  `MetrizableLCA.exactAcyclicWithCycles_mappingCone` proves intrinsic cone closure;
- `metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed3` and
  `metrizableExactAcyclicWithCyclesHomotopyIsoClosure_isTriangulatedClosed2_direct` prove
  unconditional distinguished-triangle closure of the corrected homotopy iso-closure;
- bounded homotopy objects are directly `IsTriangulatedClosed₂`;
- the bounded homotopy quotient localization and corrected Q/Qh comparison layers compile;
- `BoundedDerivedWithCycles.Metrizable.homotopyVerdierTriangulatedPackage` now supplies
  corrected Verdier left and right calculus, preadditivity, zero, finite
  products/coproducts/biproducts, shift additivity, `Pretriangulated`, and `IsTriangulated`
  unconditionally for the bounded homotopy Verdier quotient.

The remaining task-4 gap is not another ordinary triangulated-category lemma. The pinned
mathlib exposes quasicategories, their strict bicategory, cartesian internal homs, inner horn
fibrations, and the small-object argument, but no ready-made stable-quasicategory or
infinity-localization API. The repository now builds the honest foundation available from
those pieces:

- `Infinity.IsBicategoricalEquivalence` is adjoint equivalence in the strict bicategory of
  quasicategories;
- `Infinity.innerFibrantReplacementFunctor` gives a functorial inner-fibrant replacement with
  an inner-anodyne unit and a genuine quasicategory target;
- `Infinity.EdgeIsEquivalence` and `Infinity.RelativeInfinityFunctor` express actual
  equivalence-edge inversion;
- `Infinity.PointedStructure`, `HasLimitsOfShape`, and `HasColimitsOfShape` express pointedness
  and infinity-(co)limits by bicategorical adjunctions;
- `Infinity.StableInfinityStructure` expresses stability by equivalence of cartesian and
  cocartesian squares defined through right and left Kan-extension essential images;
- `Infinity.MetrizableBoundedComplexes.GeneratedWeakEquivalence` is the multiplicative closure
  of the corrected cone weak equivalences, and its universal inequality shows that inverting
  it is equivalent to inverting the raw corrected class against any multiplicative target;
- `Infinity.MetrizableBoundedComplexes.dgMappingSSet` constructs the pairwise Dold--Kan
  mapping carriers, with vertices proved equivalent to bounded cochain maps and associative
  unital composition proved at degree zero;
- `Infinity.MetrizableBoundedComplexes.dgMappingIdentitySSetMap` supplies the identity through
  every simplicial degree, while `DgMappingEnrichment` fixes the exact remaining coherent
  composition target without claiming an inhabitant;
- `Infinity.DoldKanMonoidal.inverseLaxMonoidalOfNormalizedOplax` proves that a normalized
  Alexander--Whitney oplax structure generates the coherent Dold--Kan inverse tensorator and
  all its associativity and unit laws by adjunction;
- `Infinity.MetrizableBoundedComplexes.dgMappingZModuleSSet` is the tensor-compatible
  integer-module mapping carrier, with its vertices identified with bounded morphisms and its
  identity extended through all simplicial degrees.
- `Infinity.MetrizableBoundedComplexes.dgCochainCompTensor` realizes homogeneous cochain
  composition as an actual integer-module tensor-product morphism and computes on pure tensors.
- `Infinity.MetrizableBoundedComplexes.dgHomZModuleCompositionReversed` assembles the reversed
  homogeneous summands into a genuine integer-module Hom-complex chain map using `δ_comp`.

None of these declarations promotes `HomotopyVerdierOrdinaryNerve`: an ordinary nerve loses
the higher mapping spaces needed for stability. The inner-fibrant replacement unit is also not
called a categorical equivalence, since that comparison theorem is absent from mathlib v4.30.

## Selected continuation route

The active task selects the genuine stable-infinity route. The constructive frontier is:

1. compare the tensor of `dgMappingDirectZModuleChainComplex` truncations with the truncation of
   `dgHomZModuleCompositionReversed`, and identify the direct truncation with the transported
   `dgMappingZModuleChainComplex`; construct `NormalizedMooreOplaxMonoidal`; then use its
   Dold--Kan tensorator and that chain map for composition on `dgMappingZModuleSSet`;
2. construct a dg or simplicial quotient by the corrected acyclic subcategory and prove that
   its unit inverts `GeneratedWeakEquivalence` with the infinity-localization universal
   property;
3. inhabit pointed finite infinity-(co)completeness and the checked bicartesian-square stability
   interface for that quotient;
4. identify its homotopy category with the checked corrected homotopy Verdier quotient.

Mathlib v4.31 adds the theorem that internal hom into a quasicategory is a quasicategory, which
would simplify the universal-property layer, but it does not supply dg nerves, simplicial
localization, stable quasicategories, or monoidal Dold--Kan. A dependency migration is therefore
helpful but not an end-to-end unblock by itself.

In the pinned v4.30 API, a direct compiler probe cannot synthesize the normalized Moore
functor's `OplaxMonoidal` structure. The repository now checks the bilinear homogeneous cochain
composition as `dgCochainCompBilinear`, its tensor lift as `dgCochainCompTensor`, and the formal
adjunction step from normalized Alexander--Whitney to the Dold--Kan inverse tensorator. It now
also checks `dgHomZModuleCompositionReversed`, whose chain-map law is the required `δ_comp`
Leibniz identity. The precise next gap is compatibility with nonpositive truncation and the
transported carrier, followed by the Alexander--Whitney chain map and its oplax laws; the
untruncated tensor pairing and Dold--Kan adjunction coherence are already present.

`currentMetrizableStableBridgeWithCyclesProductSuccessClaimed` must remain false until this
construction is inhabited and verified. Flipping it or filling the three obstructed
raw/ordinary fields through assumptions would be a false success claim.
