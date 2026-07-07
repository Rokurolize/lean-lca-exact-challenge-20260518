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

## Assumption list

- Existing `QuillenExactCategory.Conflation` is the intended exact-category conflation predicate.
- Existing `MetrizableLCA.quillenConflation_iff_challengeExactSequence` correctly connects `QuillenExactCategory.Conflation` with `challengeExactSequence`.
- This pass does not prove closure of the new predicate under shifts, biproducts, or mapping-cone comparison isomorphisms.

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

## List of sorry / unproven spots

The new file `LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean` contains no `sorry` or `admit`.

Unproved in this pass:

- Closure under shifts.
- Closure under binary biproducts and finite products.
- Invariance under mapping-cone isomorphism.
- Replacement of the existing `Dbounded` localization to use the new weak equivalences throughout the old theorem stack.

## Verification commands

The successful checks were run with direct `lean`, not with `lake env`, because Lake attempts network dependency repair in this restored bundle.

```bash
export PATH="$PWD/.elan/toolchains/leanprover--lean4---v4.30.0/bin:$PATH"
LIBS=$(find .lake -path '*/build/lib/lean' -type d | sort | paste -sd: -)
LDLIBS=$(find .lake -path '*/build/lib' -type d | sort | paste -sd: -)
export LEAN_PATH="$LIBS:$PWD"
export LD_LIBRARY_PATH="$LDLIBS"
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.ilean \
  LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean
lean -j1 LeanLCAExactChallenge.lean
```

Both checks exited with code 0 in the restored offline bundle. WSL handoff should re-run the same direct-`lean` checks with the local toolchain path available in that checkout.

## Conclusion

The invalid degreewise acyclicity definition is now isolated from the corrected construction. The project has a Lean-checked replacement predicate and a checked `MetrizableLCA` bridge. The next formalization step is to migrate the localization and closure lemmas from the old `exactAcyclic` predicate to `exactAcyclicWithCycles`, starting with mapping-cone isomorphism invariance and shift closure.
