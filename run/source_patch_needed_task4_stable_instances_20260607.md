# Source Patch Needed: Task 4 Stable `Dbounded MetrizableLCA` Instances

Generated UTC: 2026-06-06T18:12:20Z.

Worktree: `/home/roku/codex-thread-workspaces/019e5c90-4877-77a1-a792-34feb85174ab/worktrees/lean-lca-clean-positive-witness-20260607`.

Branch and base: `goal-clean-positive-witness-20260607` at `b4bc72c899ca364dfd71c3851685ff611bdbdc0f`.

This is a Tier A proof-search handoff for the active human-centered positive-witness goal. It does not claim product success. It records why the existing Task 4 bounded-derived infinity-category route is not yet a nullary positive witness.

## Files Checked

- `LeanLCAExactChallenge/ExactCategory/Basic.lean`
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`
- `LeanLCAExactChallenge/Ext/Yoneda.lean`
- `LeanLCAExactChallenge/Derived/Bounded.lean`
- `LeanLCAExactChallenge/Derived/OriginalFourTaskContractCompletion.lean`
- `audit/ProductSuccessDeclarations.lean`
- `audit/OriginalFourTaskCompletionDeclarations.lean`
- `audit/external_audit.py`
- `audit/original_four_task_contract_audit.py`

## Current Source Facts

`LeanLCAExactChallenge/Derived/Bounded.lean` already has a product-facing typeclass route:

```lean
Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances
```

The probe `run/probe_task4_stable_instance_gap_20260607.lean` confirms that its type is:

```lean
[Preadditive (Dbounded MetrizableLCA)]
[HasFiniteLimits (Dbounded MetrizableLCA)]
[HasFiniteColimits (Dbounded MetrizableLCA)]
[HasZeroObject (Dbounded MetrizableLCA)]
[∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA) n).Additive]
[Pretriangulated (Dbounded MetrizableLCA)]
[IsTriangulated (Dbounded MetrizableLCA)] :
  BoundedDerivedInfinityCategory MetrizableLCA (Dbounded.infinityCategory MetrizableLCA)
```

The same file records the current count as seven stable instance families:

```lean
Dbounded.metrizableStableInstanceFieldNames_count :
  Dbounded.metrizableStableInstanceFieldNames.length = 7
```

`Derived/Bounded.lean` also splits these obligations. A direct bounded-left-calculus instance for `(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions` supplies `Preadditive`, `HasZeroObject`, and shift additivity through `Dbounded.metrizableLeftCalculusSemanticFields`. The remaining packaged interface is:

```lean
Dbounded.MetrizableRemainingStableSemanticFields
```

It still requires:

```lean
HasFiniteLimits (Dbounded MetrizableLCA.{0})
HasFiniteColimits (Dbounded MetrizableLCA.{0})
Pretriangulated (Dbounded MetrizableLCA.{0})
IsTriangulated (Dbounded MetrizableLCA.{0})
```

## Probe Evidence

The first probe run failed before mathematical checking because this isolated worktree had no local `.olean` files yet:

```text
run/w_clean_20260607_probe_task4_stable_instance_gap.status: exit_code=1
run/w_clean_20260607_probe_task4_stable_instance_gap.log: unknown module prefix 'LeanLCAExactChallenge'
```

The prerequisite focused build then succeeded:

```text
lake build LeanLCAExactChallenge.Derived.Bounded
run/w_clean_20260607_build_derived_bounded_for_probe.status: exit_code=0
run/w_clean_20260607_build_derived_bounded_for_probe.log: Build completed successfully (2034 jobs).
```

After that build, the same probe reached the real source gap:

```text
lake env lean run/probe_task4_stable_instance_gap_20260607.lean
run/w_clean_20260607_probe_task4_stable_instance_gap_after_build.status: exit_code=1
```

Lean accepted the `#check` lines but failed on the required instances:

```text
error: failed to synthesize
  Preadditive (Dbounded MetrizableLCA)

error: failed to synthesize
  HasFiniteLimits (Dbounded MetrizableLCA)

error: failed to synthesize
  HasFiniteColimits (Dbounded MetrizableLCA)

error: failed to synthesize
  HasZeroObject (Dbounded MetrizableLCA)

error(lean.synthInstanceFailed): failed to synthesize instance of type class
  Preadditive (Dbounded MetrizableLCA)
```

The final example in the probe:

```lean
example :
    BoundedDerivedInfinityCategory MetrizableLCA.{0}
      (Dbounded.infinityCategory MetrizableLCA.{0}) :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances
```

also fails at `Preadditive (Dbounded MetrizableLCA)`, so the current source cannot expose a nullary Task 4 witness honestly.

## Source Patch Needed

The smallest useful source patch is not another route declaration. It is a canonical proof/API that constructs the stable ordinary-category structure on `Dbounded MetrizableLCA.{0}` from the existing exact weak-equivalence localization.

One acceptable target shape is:

```lean
noncomputable def Dbounded.metrizableRemainingStableSemanticFieldsOfLocalization
    [(boundedExactWeakEquivalence MetrizableLCA.{0}).HasLeftCalculusOfFractions] :
    Dbounded.MetrizableRemainingStableSemanticFields
      Dbounded.metrizableLeftCalculusSemanticFields
```

That statement must prove, not assume, finite limits, finite colimits, `Pretriangulated`, and `IsTriangulated` for `Dbounded MetrizableLCA.{0}`.

If the local mathlib API cannot construct finite limits or triangulated structure for this localization from the available `MorphismProperty` and `Localization` interfaces, the source patch should instead introduce the missing general theorem at the localization level. The theorem should specialize to:

```lean
HasFiniteLimits (Dbounded MetrizableLCA.{0})
HasFiniteColimits (Dbounded MetrizableLCA.{0})
Pretriangulated (Dbounded MetrizableLCA.{0})
IsTriangulated (Dbounded MetrizableLCA.{0})
```

The final positive witness should then consume the resulting fields through the existing `Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances` or the existing left-calculus semantic route, with no caller-supplied semantic input or certificate adapter.

## Stop Reason

No source edit is made in this checkpoint because the current failure is instance synthesis for stable `Dbounded MetrizableLCA` structure, not a local term elaboration problem. Adding another wrapper around `Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances` would preserve the same missing instances and would not satisfy the human-centered goal contract.

Product success remains false. Do not call `update_goal` from this checkpoint.
