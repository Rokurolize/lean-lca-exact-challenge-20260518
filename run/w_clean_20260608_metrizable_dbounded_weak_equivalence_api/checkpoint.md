# Nonterminal MetrizableLCA Dbounded weak-equivalence API checkpoint

Generated UTC: 2026-06-07T19:08:16Z

Base HEAD before this checkpoint: `ba9ae8cb5033c5a88bffff2dda230bd72d5c994e`

## Scope

This checkpoint exposes the bounded derived weak-equivalence surface directly at the strict metrizable LCA level. It makes the Task 2 to Task 4 connection easier to consume by final witness code without reopening the generic `BoundedComplexCategory` and `boundedExactWeakEquivalence` parameters at every call site.

New declarations:

- `LeanLCAExactChallenge.Dbounded.metrizableOf`
- `LeanLCAExactChallenge.Dbounded.metrizableLocalization_obj`
- `LeanLCAExactChallenge.Dbounded.metrizableWeakEquivalence`
- `LeanLCAExactChallenge.Dbounded.metrizableExactAcyclicMappingCone`
- `LeanLCAExactChallenge.Dbounded.exactAcyclicMappingCone_of_metrizableWeakEquivalence`
- `LeanLCAExactChallenge.Dbounded.metrizableWeakEquivalence_of_exactAcyclicMappingCone`

Updated declaration:

- `LeanLCAExactChallenge.Dbounded.metrizableWeakEquivalence_iff_exactAcyclicMappingCone`

Touched files:

- `LeanLCAExactChallenge/Derived/Bounded.lean`
- `audit/RequiredDeclarations.lean`
- `audit/OriginalFourTaskCompletionDeclarations.lean`
- `terminal_outcome/terminal_outcome.json`
- `run/resumption_gate_20260608_metrizable_dbounded_next/*`

## Obligations

Discharged or derived:

- Derived a small strict MetrizableLCA API from the generic bounded weak-equivalence mapping-cone API.
- Preserved the existing generic bounded exact weak-equivalence declarations and exposed direct MetrizableLCA introduction and elimination lemmas for the exact-acyclic mapping-cone condition.

Still carried:

- No `OriginalFourTaskProductSuccess` witness exists.
- The full bounded derived infinity-category stable structure for `D^b(MetrizableLCA, E)` remains incomplete under the original four-task contract.

Product-facing debt:

- No new W-number or route-history declaration was introduced.
- No new global instance, assumption input, source-patch adapter, or product-success Boolean was introduced.

## Verification

Commands run:

- `git status --short --branch --untracked-files=all > run/resumption_gate_20260608_metrizable_dbounded_next/git_status.txt`
- `git rev-parse HEAD > run/resumption_gate_20260608_metrizable_dbounded_next/head.txt`
- `git rev-parse origin/main > run/resumption_gate_20260608_metrizable_dbounded_next/origin_main.txt`
- `git ls-remote origin refs/heads/main refs/heads/goal-clean-positive-witness-20260607 > run/resumption_gate_20260608_metrizable_dbounded_next/ls_remote_heads.txt`
- `jq '{outcome, product_success, product_complete, update_goal_allowed, git_head, proof_search_checkpoint, obligations_discharged, obligations_derived_or_eliminated, new_frontier_input_count}' terminal_outcome/terminal_outcome.json > run/resumption_gate_20260608_metrizable_dbounded_next/terminal_outcome_summary.json`
- `rg -n 'OriginalFourTaskProductSuccess|originalFourTaskProductSuccess|productSuccessClaimed\s*:=\s*true|productSuccessClaimed\s*=\s*true' LeanLCAExactChallenge audit > run/resumption_gate_20260608_metrizable_dbounded_next/product_success_scan.txt`
- `{ printf 'pattern: productSuccessClaimed\\s*:=\\s*false|productSuccessClaimed\\s*=\\s*false\n'; printf 'total_matches\t'; rg -n 'productSuccessClaimed\s*:=\s*false|productSuccessClaimed\s*=\s*false' LeanLCAExactChallenge audit -g '!audit/negative_fixtures/**' | wc -l; rg -n 'productSuccessClaimed\s*:=\s*false|productSuccessClaimed\s*=\s*false' LeanLCAExactChallenge audit -g '!audit/negative_fixtures/**' | sed -n '1,80p'; } > run/resumption_gate_20260608_metrizable_dbounded_next/product_success_false_scan.txt`
- `lake env lean LeanLCAExactChallenge/Derived/Bounded.lean`
- `lake build LeanLCAExactChallenge.Derived.Bounded`
- `lake env lean audit/RequiredDeclarations.lean > /tmp/lean-lca-required-declarations-metrizable-dbounded-api-20260608.log`
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean > /tmp/lean-lca-original-four-completion-metrizable-dbounded-api-20260608.log`
- `jq empty terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json run/resumption_gate_20260608_metrizable_dbounded_next/terminal_outcome_summary.json`
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Derived/Bounded.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean`
- `git diff --check -- LeanLCAExactChallenge/Derived/Bounded.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean terminal_outcome/terminal_outcome.json run/resumption_gate_20260608_metrizable_dbounded_next run/w_clean_20260608_metrizable_dbounded_weak_equivalence_api/checkpoint.md`
- `rg -n 'OriginalFourTaskProductSuccess|originalFourTaskProductSuccess|productSuccessClaimed\s*:=\s*true|productSuccessClaimed\s*=\s*true' LeanLCAExactChallenge audit`

The direct Lean check and target build completed with existing warnings only. The audit files completed after rebuilding `LeanLCAExactChallenge.Derived.Bounded`.
The final JSON, forbidden-token, and whitespace checks passed. The product-success scan returned only audit scripts, negative fixtures, and the existing route-guard text, so it did not establish a positive witness.

## Product Status

Product success remains false. This checkpoint does not add `OriginalFourTaskProductSuccess`; it only strengthens the strict MetrizableLCA bounded-derived weak-equivalence connection.
