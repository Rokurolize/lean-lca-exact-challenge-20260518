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
- `BoundedDerivedCategoryWithCycles`
- `DboundedWithCycles`
- `DboundedWithCycles.localization`
- `DboundedWithCycles.MetrizableLCA.hasFiniteProducts`
- `DboundedWithCycles.hasZeroObjectOfHasLeftCalculusOfFractions`
- `DboundedWithCycles.MetrizableLCA.hasZeroObject`
- `BoundedDerivedWithCycles.Metrizable.StablePackage`
- `BoundedDerivedWithCycles.Metrizable.LeftCalculusAssumption`
- `BoundedDerivedWithCycles.Metrizable.LeftCalculusSemanticFields`
- `BoundedDerivedWithCycles.Metrizable.RemainingStableSemanticFields`
- `BoundedDerivedWithCycles.Metrizable.StableSemanticInput`
- `BoundedDerivedWithCycles.Metrizable.stablePackageOfLeftCalculus`

## List of sorry / unproven spots

The new files `LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean`, `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.lean`, `LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.lean`, and `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean` contain no `sorry` or `admit`.

Unproved in this pass:

- Replacement of the existing `Dbounded` localization to use the new weak equivalences throughout the old theorem stack.
- A proof that `boundedExactWeakEquivalenceWithCycles` has a left calculus of fractions. The corrected `DboundedWithCycles` surface is defined, and finite products, zero object, preadditivity, and shift additivity are available conditionally on this calculus instance.
- Inhabited corrected finite limits, finite colimits, pretriangulated structure, and triangulated structure for `DboundedWithCycles MetrizableLCA.{0}`. The new `BoundedDerivedWithCycles.Metrizable.RemainingStableSemanticFields` record is the checked assumption surface for these fields.

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

## Conclusion

The invalid degreewise acyclicity definition is now isolated from the corrected construction. The project has a Lean-checked replacement predicate, checked `MetrizableLCA` bridge, checked isomorphism/shift/biproduct/finite-product closure, checked corrected bounded weak-equivalence finite-product stability, a checked corrected `DboundedWithCycles` localization surface, and a checked corrected Metrizable stable package assumption surface. The next formalization step is to prove or port the left-calculus-of-fractions input for `boundedExactWeakEquivalenceWithCycles`, then inhabit the remaining corrected finite-limit, finite-colimit, pretriangulated, and triangulated fields without relying on legacy `boundedExactWeakEquivalence`.
