# Source Patch Needed Handoff: Task 4 Stable `Dbounded MetrizableLCA` Instances

Generated UTC: 2026-06-07T22:14:19Z

Worktree HEAD at proof search start: `6c498a7b9e417b2d29bc400062ae5f17a5e1ceb7`

Outcome: `source_patch_needed_handoff`

Product success: false. No final positive witness is claimed.

## Bounded Search Result

The product-facing bounded-derived facade already exposes `BoundedDerived.Metrizable.StablePackage`, and `LeanLCAExactChallenge.Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances` is the intended nullary route once stable category instances exist. A bounded proof-search probe attempted to instantiate that route without caller-supplied semantic data.

Exact attempted final-surface statement:

```lean
import LeanLCAExactChallenge.BoundedDerived.Basic

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

noncomputable def attemptedOriginalFourTaskStablePackage :
    BoundedDerived.Metrizable.StablePackage :=
  Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances

end LeanLCAExactChallenge
```

This fails because Lean cannot synthesize the stable categorical instances on `Dbounded MetrizableLCA.{0}`.

## Exact Missing Interfaces

To turn task 4 into a contract-valid nullary witness, source needs concrete, mathlib-quality instances or theorems providing:

```lean
instance : Preadditive (Dbounded MetrizableLCA.{0})
instance : HasFiniteLimits (Dbounded MetrizableLCA.{0})
instance : HasFiniteColimits (Dbounded MetrizableLCA.{0})
instance : HasZeroObject (Dbounded MetrizableLCA.{0})
instance : ∀ n : ℤ, (shiftFunctor (Dbounded MetrizableLCA.{0}) n).Additive
instance : Pretriangulated (Dbounded MetrizableLCA.{0})
instance : IsTriangulated (Dbounded MetrizableLCA.{0})
```

The existing semantic-input path is not enough for final product success because the positive-witness contract forbids completing the stable infinity-category obligation from caller-supplied records whose fields are the desired conclusions.

## Attempted Proof Evidence

Probe file:

`run/w_clean_20260608_task4_stable_instance_source_patch_needed/stable_instance_probe.lean`

Expected-failure output:

`run/w_clean_20260608_task4_stable_instance_source_patch_needed/stable_instance_probe.expected_failure.log`

Expected-failure exit code:

`run/w_clean_20260608_task4_stable_instance_source_patch_needed/stable_instance_probe.expected_failure.exit`

The expected failure is useful evidence only because it targets the exact nullary stable package route needed for task 4. It is not a product-success proof and does not weaken the original four-task contract.

## Next Source Patch

Implement the concrete stable structure on the localized bounded derived category:

1. Provide or derive the preadditive and zero-object structure for `Dbounded MetrizableLCA.{0}` from the bounded-complex localization.
2. Lift finite limits and finite colimits through the exact weak-equivalence localization, or prove the required universal constructions directly in `Dbounded`.
3. Establish shift additivity for all integer shifts on `Dbounded`.
4. Add the pretriangulated and triangulated structure expected by `BoundedDerivedInfinityCategory`.
5. After those instances synthesize, add the final field in the product witness by using `Dbounded.boundedDerivedInfinityCategoryOfMetrizableStableInstances` without explicit semantic input.
