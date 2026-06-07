# Nonterminal bounded exact weak-equivalence mapping-cone API checkpoint

Generated UTC: 2026-06-07T18:38:28Z

Base HEAD before this checkpoint: `cc4512f6c146fa483f61897c2912488ba8a9f70c`

## Scope

This checkpoint adds a small direct API for Task 4 bounded derived work. It exposes bounded exact weak equivalences as exactly the bounded morphisms whose mapping cone is exact-acyclic, without requiring downstream code to unfold `boundedExactWeakEquivalence`.

New declarations:

- `LeanLCAExactChallenge.boundedExactWeakEquivalence_iff_exactAcyclic_mappingCone`
- `LeanLCAExactChallenge.exactAcyclic_mappingCone_of_boundedExactWeakEquivalence`
- `LeanLCAExactChallenge.boundedExactWeakEquivalence_of_exactAcyclic_mappingCone`

Touched files:

- `LeanLCAExactChallenge/Derived/Bounded.lean`
- `audit/RequiredDeclarations.lean`
- `audit/OriginalFourTaskCompletionDeclarations.lean`
- `terminal_outcome/terminal_outcome.json`
- `run/resumption_gate_20260608_bounded_next/*`

## Verification

Commands run:

- `lake env lean LeanLCAExactChallenge/Derived/Bounded.lean`
- `lake build LeanLCAExactChallenge.Derived.Bounded`
- `lake env lean audit/RequiredDeclarations.lean > /tmp/lean-lca-required-declarations-bounded-cone-api-20260608.log`
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean > /tmp/lean-lca-original-four-completion-bounded-cone-api-20260608.log`
- `jq empty terminal_outcome/terminal_outcome.json run/goal_identity_20260602_human_centered_positive_witness.json run/resumption_gate_20260608_bounded_next/terminal_outcome_summary.json`
- `scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge/Derived/Bounded.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean`
- `git diff --check -- LeanLCAExactChallenge/Derived/Bounded.lean audit/RequiredDeclarations.lean audit/OriginalFourTaskCompletionDeclarations.lean terminal_outcome/terminal_outcome.json run/resumption_gate_20260608_bounded_next run/w_clean_20260608_bounded_exact_weak_equivalence_mapping_cone_api/checkpoint.md`

Expected existing warnings were observed in `Bounded.lean` and imported LCA modules. The new declarations checked, and the audit files completed after rebuilding `LeanLCAExactChallenge.Derived.Bounded`.

## Product Status

Product success remains false. No `OriginalFourTaskProductSuccess` surface has been added, and this checkpoint is not a final completion claim.
