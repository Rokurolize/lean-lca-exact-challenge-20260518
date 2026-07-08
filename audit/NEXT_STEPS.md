# Next Steps: cycle-object exact acyclicity

Remote branch: `cycle-object-exact-acyclic-handoff-20260708`.

Implemented files:

- `LeanLCAExactChallenge/Derived/ExactAcyclicCorrect.lean`
- `LeanLCAExactChallenge/Derived/ExactAcyclicWithCyclesClosure.lean`
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
lean -j1 -o .lake/build/lib/lean/LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.olean \
  -i .lake/build/lib/lean/LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.ilean \
  LeanLCAExactChallenge/BoundedDerived/MetrizableStableBridgeWithCycles.lean
lean -j1 LeanLCAExactChallenge.lean
```

Remaining tasks:

1. Prove or port a left-calculus-of-fractions theorem for `boundedExactWeakEquivalenceWithCycles`.
2. Inhabit `BoundedDerivedWithCycles.Metrizable.RemainingStableSemanticFields` by proving corrected finite limits, finite colimits, pretriangulated structure, and triangulated structure for `DboundedWithCycles MetrizableLCA.{0}`.
3. Migrate legacy `exactAcyclic` lemmas theorem-by-theorem only when the corresponding corrected theorem is needed.
4. Keep the legacy degreewise `boundedExactWeakEquivalence` route labeled as compatibility-only.

Completed corrected closure milestones:

- Mapping-cone isomorphism invariance.
- Shift closure and bounded weak-equivalence shift compatibility.
- MetrizableLCA binary biproduct closure.
- MetrizableLCA finite-product closure via W151 Option-product decomposition.
- Corrected bounded weak-equivalence finite-product stability over default-universe `MetrizableLCA`.
- Separate corrected localization surface: `BoundedDerivedCategoryWithCycles`, `DboundedWithCycles`, and `DboundedWithCycles.localization`.
- Corrected Metrizable stable bridge assumption surface: `BoundedDerivedWithCycles.Metrizable.StablePackage`, explicit with-cycles left calculus, derived preadditive/zero/finite-products/shift-additivity fields, and remaining finite-limit/finite-colimit/pretriangulated/triangulated assumptions.

Note: the older checkout at `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518` had unrelated dirty files before this work began. Continue using the clean integration worktree unless the user explicitly asks otherwise.
