# Next Steps: cycle-object exact acyclicity

Remote branch: `cycle-object-exact-acyclic-handoff-20260708`.

Implemented files:

- `LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean`
- `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.lean`
- `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesContractible.lean`
- `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean`
- `LeanLCAExactChallenge/Derived/BoundedDerivedWithCycles.lean`
- `LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean`
- `audit/SCOPE.md`
- `audit/REPORT.md`

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
lean -j1 LeanLCAExactChallenge.lean
```

Remaining tasks:

1. Prove corrected acyclic-object cone/distinguished-triangle closure and discharge `ExactAcyclicWithCyclesHomotopyEquivInvarianceInput`, then use the checked equality theorem to compare `boundedExactWeakEquivalenceWithCycles` with the bounded homotopy `trW` class.
2. Prove or port the Q/Qh localization route that replaces the chain-level left-calculus assumption for `boundedExactWeakEquivalenceWithCycles`.
3. Inhabit the corrected replacement stable package for `DboundedWithCycles MetrizableLCA.{0}`: pretriangulated and triangulated structures, plus the honest finite-product/finite-coproduct or biproduct surface. Do not try to prove ordinary finite limits/finite colimits unless the mathematical objection in `audit/HANDOVER.md` is overturned.
4. Attempt the Lean/mathlib stable-version migration only in an isolated sibling worktree. The attempt must update `lean-toolchain` and Lake dependencies coherently, must not reuse `v4.30.0` compiled artifacts as evidence, and must pass the baseline direct-Lean checks before any migration commit.
5. Migrate legacy `exactAcyclic` lemmas theorem-by-theorem only when the corresponding corrected theorem is needed.
6. Keep the legacy degreewise `boundedExactWeakEquivalence` route labeled as compatibility-only.

Completed corrected closure milestones:

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
  `exactAcyclicWithCyclesHomotopyIsoClosure`,
  `boundedHomotopyExactWeakEquivalenceWithCycles`, and the checked inclusion
  `boundedExactWeakEquivalenceWithCycles_le_boundedHomotopyExactWeakEquivalenceWithCycles`
  plus the checked conditional equality
  `boundedExactWeakEquivalenceWithCycles_eq_boundedHomotopyWithCycles_of_homotopyEquivInvariance`
  in `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesHomotopy.lean`.

- Mapping-cone isomorphism invariance.
- Shift closure and bounded weak-equivalence shift compatibility.
- MetrizableLCA binary biproduct closure.
- MetrizableLCA finite-product closure via W151 Option-product decomposition.
- Corrected bounded weak-equivalence finite-product stability over default-universe `MetrizableLCA`.
- Separate corrected localization surface: `BoundedDerivedCategoryWithCycles`, `DboundedWithCycles`, and `DboundedWithCycles.localization`.
- Corrected Metrizable stable bridge assumption surface: `BoundedDerivedWithCycles.Metrizable.StablePackage`, explicit with-cycles left calculus, derived preadditive/zero/finite-products/shift-additivity fields, and remaining finite-limit/finite-colimit/pretriangulated/triangulated assumptions.
- Version-policy blocker recorded: the repository remains verified on its coherent `v4.30.0` pin because the restored manifest, mathlib checkout, and compiled dependency cache are `v4.30.0`-only; stable `v4.31.0` requires a separate coherent dependency migration and full baseline verification.

Note: the older checkout at `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518` had unrelated dirty files before this work began. Continue using the clean integration worktree unless the user explicitly asks otherwise.
