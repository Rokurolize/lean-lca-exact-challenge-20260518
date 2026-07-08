# Verification Report

## Target and mode

Target: `LeanLCAExactChallenge`, exact-category acyclicity and bounded weak equivalences for the bounded derived construction over `MetrizableLCA`.

Mode: corrective formal audit / Lean formalization continuation.

## Scope

This pass isolates and replaces the mathematically invalid acyclicity shape used by the legacy predicate

```lean
exactAcyclic C K := ∀ i, QuillenExactCategory.Conflation (K.sc i)
```

with a cycle-object predicate. The full Verdier/localization proof stack is not refactored in this pass.

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

## Assumption list

- Existing `QuillenExactCategory.Conflation` is the intended exact-category conflation predicate.
- Existing `MetrizableLCA.quillenConflation_iff_challengeExactSequence` correctly connects `QuillenExactCategory.Conflation` with `challengeExactSequence`.
- The new closure proofs still reuse existing project infrastructure for finite product decompositions and mapping-cone product comparison, including W151's Option-product comparison and the existing finite mapping-cone comparison input.
- The existing legacy `Dbounded` route remains in the repository and is not globally replaced in this pass.
- The corrected stable bridge is intentionally conditional: it exposes the exact remaining stable fields as assumptions instead of reusing legacy `Dbounded` semantic packages.

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
- `exactAcyclicWithCyclesHomotopyObject_isClosedUnderIsomorphisms_of_homotopyEquivInvariance`
- `exactAcyclicWithCyclesHomotopyEquivInvarianceInput_of_isClosedUnderIsomorphisms`
- `exactAcyclicWithCyclesHomotopyEquivInvarianceInput_iff_isClosedUnderIsomorphisms`
- `exactAcyclicWithCyclesHomotopyIsoClosure`
- `exactAcyclicWithCyclesHomotopyIsoClosure_isTriangulated_of_isTriangulatedClosed2`
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
- `BoundedDerivedWithCycles.Metrizable.leftCalculusAssumptionOfHomotopyVerdier`
- `BoundedDerivedWithCycles.Metrizable.RightCalculusAssumption`
- `BoundedDerivedWithCycles.Metrizable.rightCalculusAssumptionOfHomotopyVerdier`
- `BoundedDerivedWithCycles.Metrizable.StablePackage`
- `BoundedDerivedWithCycles.Metrizable.LeftCalculusAssumption`
- `BoundedDerivedWithCycles.Metrizable.LeftCalculusSemanticFields`
- `BoundedDerivedWithCycles.Metrizable.RemainingStableSemanticFields`
- `BoundedDerivedWithCycles.Metrizable.StableSemanticInput`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfLeftCalculus`

## List of sorry / unproven spots

The new files `LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean`, `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.lean`, `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean`, `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean`, `LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.lean`, and `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean` contain no `sorry` or `admit`.

Unproved in this pass:

- Replacement of the existing `Dbounded` localization to use the new weak equivalences throughout the old theorem stack.
- A proof that `boundedExactWeakEquivalenceWithCycles` has a left calculus of fractions. The corrected `DboundedWithCycles` surface is defined, finite products, zero object, preadditivity, and shift additivity are available conditionally on this calculus instance, and `leftCalculusAssumptionOfHomotopyVerdier` now reduces the assumption to explicit corrected homotopy Verdier inputs.
- The completed homotopy-equivalence inclusion is not yet the full Verdier comparison: the reverse comparison with the bounded homotopy `trW` class still needs the corrected acyclic-object distinguished-triangle closure.
- Inhabited corrected finite limits, finite colimits, pretriangulated structure, and triangulated structure for `DboundedWithCycles MetrizableLCA.{0}`. Finite products, finite biproducts, and finite coproducts are now derived from corrected left calculus; the new `BoundedDerivedWithCycles.Metrizable.RemainingStableSemanticFields` record remains the checked assumption surface for the remaining fields.

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
```

All listed checks exited with code 0 in the restored offline bundle. WSL handoff should re-run the same direct-`lean` checks with the local toolchain path available in that checkout.

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

This is real progress toward the Q/Qh route, because the corrected chain localization functor now has the Lean-checked input needed to invert homotopy equivalences. It does not yet prove the full `trW` comparison or calculus of fractions; those still require the corrected acyclic-object cone/triangle closure.

## Corrected homotopy-object `trW` surface

`LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean` now mirrors the non-legacy part of the old Verdier skeleton with corrected predicates only. It defines the homotopy-category object predicate `exactAcyclicWithCyclesHomotopyObject`, its iso-closure `exactAcyclicWithCyclesHomotopyIsoClosure`, and `boundedHomotopyExactWeakEquivalenceWithCycles`.

The file proves zero-object containment, iso-closure shift stability, `ObjectProperty.trW_isoClosure` compatibility, direct cone-acyclic maps entering the corrected homotopy `trW` class, the conditional equivalence between direct cone acyclicity and `trW` after homotopy-category descent, and the unconditional inclusion `boundedExactWeakEquivalenceWithCycles ≤ boundedHomotopyExactWeakEquivalenceWithCycles`.

The homotopy-descent assumption is now a checked Lean input surface, `ExactAcyclicWithCyclesHomotopyEquivInvarianceInput`. Lean proves this input equivalent to homotopy-category isomorphism closedness of `exactAcyclicWithCyclesHomotopyObject`, and from it proves the direct/homotopy pullback equality `boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_homotopyEquivInvariance`.

The same file now also exposes the corrected conditional triangulated-object surface: once the corrected object predicate has the required `IsTriangulatedClosed₂` closure, Lean supplies `IsTriangulated` for both the object predicate and its isomorphism closure.

The corrected homotopy surface now carries the two-sided calculus bridge as well: if the corrected iso-closed homotopy object predicate has `IsTriangulatedClosed₂`, Lean proves Verdier left and right calculus for the homotopy `trW` class. With the recorded localized right-adjoint/unit input it pulls left calculus back to `boundedHomotopyExactWeakEquivalenceWithCycles`; with the recorded localized left-adjoint/counit input it pulls right calculus back. With homotopy descent, Lean transfers both calculi to `boundedExactWeakEquivalenceWithCycles`. `MetrizableStableBridgeWithCycles.lean` exposes these as `leftCalculusAssumptionOfHomotopyVerdier` and `rightCalculusAssumptionOfHomotopyVerdier`.

The corrected route now also has the bounded-homotopy object-property layer: `boundedExactAcyclicWithCyclesHomotopyObject` is the inverse image of the corrected iso-closed homotopy acyclic objects along `BoundedHomotopyCategory.ι`, and under the bounded-source and corrected-acyclic closed₂ inputs Lean proves it is triangulated. This mirrors the Q/Qh structural layer without using legacy bounded weak equivalences as evidence.

The bounded homotopy Verdier quotient surface is also checked conditionally: under the same closed₂ inputs, Lean constructs `BoundedExactAcyclicWithCyclesHomotopyVerdierCategory` with preadditive, zero-object, shift-additivity, pretriangulated, and triangulated instances, plus the localizer morphism from bounded corrected homotopy `trW` to the ambient corrected homotopy `trW`. This is still a homotopy-quotient layer rather than the final `DboundedWithCycles` stable package, but it removes another generic structural gap in the corrected Q/Qh route.

The bounded-complex homotopy pullback class is now checked equivalent to the bounded-homotopy `trW` pullback along `BoundedComplexCategory.homotopyQuotientBounded`. With the explicit homotopy-descent input, Lean identifies direct corrected weak equivalences with that bounded-homotopy `trW` pullback as well.

The corrected derived surface now derives finite biproducts and finite coproducts from corrected left calculus and finite-product stability. The corrected weak-equivalence class itself is also checked stable under finite coproducts, and its opposite class is checked stable under finite products. The stable bridge therefore records eight checked left-calculus semantic fields: left calculus, preadditivity, zero object, finite products, finite biproducts, finite coproducts, all shift functor additivity, and suspension additivity.

The corrected Q/Qh comparison layer now exists as ordinary category API. `ExactAcyclicWithCyclesHomotopy.lean` defines `ExactAcyclicWithCyclesHomotopyVerdierCategory` and `BoundedHomotopyDerivedCategoryWithCycles`, the corrected homotopy-pullback localization, and constructs its comparison functors to the ambient corrected homotopy Verdier quotient and to the bounded corrected homotopy Verdier quotient. It also defines the bounded-to-ambient Verdier comparison, `DboundedWithCycles.homotopyComparison`, routed and direct ambient Verdier comparisons, routed and direct bounded Verdier comparisons, their localization-commuting isomorphisms, the routed/direct comparison isomorphisms, the bounded-to-ambient composition isomorphisms, and the conditional equivalence `DboundedWithCycles.homotopyComparisonEquivalenceOfIsoClosed` under homotopy descent. These declarations use only `boundedExactWeakEquivalenceWithCycles`, `boundedHomotopyExactWeakEquivalenceWithCycles`, and corrected `trW` localizer morphisms.

This does not consume legacy `boundedExactWeakEquivalence` or legacy `Dbounded` facts. The remaining mathematical assumption is explicit: the corrected object predicate still needs the cone/distinguished-triangle closure that makes it descend through homotopy-category isomorphisms and become triangulated.

## Conclusion

The invalid degreewise acyclicity definition is now isolated from the corrected construction. The project has a Lean-checked replacement predicate, checked `MetrizableLCA` bridge, checked isomorphism/shift/biproduct/finite-product closure, checked corrected bounded weak-equivalence finite-product stability, checked contractible and homotopy-equivalence bridges, a checked corrected homotopy-object `trW` surface, a checked corrected `DboundedWithCycles` localization surface, checked corrected Q/Qh comparison functors, checked finite product/biproduct/coproduct semantic fields, and a checked corrected Metrizable stable package assumption surface. The next formalization step is the corrected acyclic-object cone/distinguished-triangle closure, followed by transporting pretriangulated and triangulated structure to `DboundedWithCycles` without relying on legacy `boundedExactWeakEquivalence`.
