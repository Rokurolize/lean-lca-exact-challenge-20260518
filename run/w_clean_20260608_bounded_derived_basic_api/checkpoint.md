# Nonterminal bounded derived basic API checkpoint

Generated UTC: 2026-06-07T20:34:00Z

Base HEAD before this checkpoint: `0611d496c1906d0c6ee53aca99bc4f24c143c913`

## Scope

This checkpoint adds `LeanLCAExactChallenge.BoundedDerived.Basic`, a short product-facing facade for the bounded derived category. It names the ordinary localization `D^b(C,E)`, its quasicategory nerve, the strict metrizable LCA specialization, the exact-acyclic mapping-cone weak-equivalence criterion, and stable package projections without exposing route-history terminology.

New declarations:

- `LeanLCAExactChallenge.BoundedDerived.OrdinaryCategory`
- `LeanLCAExactChallenge.BoundedDerived.localization`
- `LeanLCAExactChallenge.BoundedDerived.of`
- `LeanLCAExactChallenge.BoundedDerived.infinityCategory`
- `LeanLCAExactChallenge.BoundedDerived.infinityNerve`
- `LeanLCAExactChallenge.BoundedDerived.infinityNerve_quasicategory`
- `LeanLCAExactChallenge.BoundedDerived.homotopyCategoryIso`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.ComplexCategory`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.OrdinaryCategory`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.localization`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.of`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.infinityCategory`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.infinityNerve`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.infinityNerve_quasicategory`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.homotopyCategoryIso`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.WeakEquivalence`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.exactAcyclicMappingCone`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.weakEquivalence_iff_exactAcyclicMappingCone`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.StablePackage`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_carrier`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_preadditive`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_finiteLimits`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_finiteColimits`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_zeroObject`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_shiftAdditive`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_suspensionAdditive`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_pretriangulated`
- `LeanLCAExactChallenge.BoundedDerived.Metrizable.stablePackage_triangulated`

Touched files:

- `LeanLCAExactChallenge/BoundedDerived/Basic.lean`
- `LeanLCAExactChallenge.lean`
- `audit/RequiredDeclarations.lean`
- `audit/OriginalFourTaskCompletionDeclarations.lean`
- `terminal_outcome/terminal_outcome.json`
- `run/goal_identity_20260602_human_centered_positive_witness.json`
- `run/resumption_gate_20260608_canonical_four_task_api_next/*`

## Obligations

Discharged or derived:

- Re-exported the existing `Dbounded` ordinary category, localization, object constructor, infinity-category nerve, quasicategory proof, and homotopy-category comparison under the short `BoundedDerived` namespace.
- Added a strict metrizable LCA specialization for the same surface.
- Re-exposed the metrizable bounded weak-equivalence mapping-cone iff through names that do not mention internal route scaffolding.
- Added stable package projection helpers for the metrizable bounded-derived infinity-category package.
- Connected the facade to both required-declaration and original-four audit surfaces.

Still carried:

- No `OriginalFourTaskProductSuccess` witness exists.
- The facade does not construct missing stable fields; it names and projects already available package structure.
- The full bounded derived infinity-category obligation remains incomplete under the original four-task contract.

Product-facing debt:

- No product-success Boolean, final product witness, or global completion claim was introduced.
- The new facade is API cleanup and witness-integration preparation, not product success.

## Verification

Commands run:

- `lake env lean LeanLCAExactChallenge/BoundedDerived/Basic.lean`
- `lake build LeanLCAExactChallenge.BoundedDerived.Basic`
- `lake env lean LeanLCAExactChallenge.lean`
- `lake env lean audit/RequiredDeclarations.lean > /tmp/lean-lca-required-declarations-bounded-derived-basic-20260608.log`
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean > /tmp/lean-lca-original-four-bounded-derived-basic-20260608.log`
- `jq empty terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json run/resumption_gate_20260608_canonical_four_task_api_next/terminal_outcome_summary.json`
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/BoundedDerived/Basic.lean LeanLCAExactChallenge.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean`
- `git diff --check -- LeanLCAExactChallenge/BoundedDerived/Basic.lean LeanLCAExactChallenge.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json run/resumption_gate_20260608_canonical_four_task_api_next run/w_clean_20260608_bounded_derived_basic_api/checkpoint.md`
- Product-success true-pattern scan saved to `run/w_clean_20260608_bounded_derived_basic_api/product_success_true_scan.raw` with 195 known audit or negative-fixture-context matches.
- Product-success false-pattern scan saved to `run/w_clean_20260608_bounded_derived_basic_api/product_success_false_scan.raw` with 1526 matches.
- `python3 audit/original_four_task_contract_audit.py --root . --contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_original_four_task_completion_contract_20260526.md --positive-witness-contract /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_false_positive_recovery_20260530/lean_lca_positive_witness_completion_contract_20260530.md --terminal-outcome terminal_outcome/terminal_outcome.json`

The direct module, module build, root import, required-declarations audit, and original-four audit completed successfully. A broader `lake build LeanLCAExactChallenge` was started as an extra check after these successes, then stopped after it entered a long rebuild of unrelated existing route modules; it is not counted as a successful verification command.

Additional audit note: `python3 audit/external_audit.py --root . --terminal-outcome terminal_outcome/terminal_outcome.json` was attempted after adding `terminal_outcome.reference_route_log`. It still failed on `manifest hash mismatch for LeanLCAExactChallenge/Derived/Bounded.lean`, which is a pre-existing manifest consistency issue outside this checkpoint's touched source files.

## Product Status

Product success remains false. This checkpoint does not add `OriginalFourTaskProductSuccess`; it only exposes a cleaner bounded-derived public API over existing nonterminal evidence.
