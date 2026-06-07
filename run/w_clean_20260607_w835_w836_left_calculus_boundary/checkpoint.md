# W835-W836 left-calculus boundary checkpoint

UTC: 2026-06-07T10:10:09Z

Starting HEAD: 3764af3ae977222f4df6abfd73a85827e8235e39

Scope:
- Exposed W835 exact-inputs iso-closure left-calculus declarations in Required and Original audit surfaces.
- Exposed W836 branch-localized exact-inputs left-calculus declarations in Required and Original audit surfaces.
- Preserved nonterminal product-success state; the target route states still carry `productSuccessClaimed := false`.

Changed audit surfaces:
- `audit/RequiredDeclarations.lean`
- `audit/OriginalFourTaskCompletionDeclarations.lean`

Verification commands:
- `lake env lean LeanLCAExactChallenge/Derived/ExactInputsLeftCalculusRoute.lean`
- `lake env lean LeanLCAExactChallenge/Derived/BranchLocalizedExactInputsLeftCalculusRoute.lean`
- `lake build LeanLCAExactChallenge.Derived.BranchLocalizedExactInputsLeftCalculusRoute`
- `lake env lean audit/RequiredDeclarations.lean`
- `lake env lean audit/ProductSuccessDeclarations.lean`
- `lake env lean audit/OriginalFourTaskCompletionDeclarations.lean`
- `git diff --check`
- `rg -n 'sorry|admit|axiom|unsafe'`
- completion-claim and declaration-presence scans

Evidence:
- `w835_target_lean.log`: exit 0
- `w836_target_lean.log`: exit 0
- `left_calculus_boundary_build.log`: exit 0 with pre-existing project warnings
- `required_audit.log`: exit 0
- `product_success_audit.log`: exit 0
- `original_four_audit.log`: exit 0
- `diff_check.log`: exit 0
- `diff_check_post.log`: exit 0
- `forbidden_tokens.log`: no matches
- `completion_claim_scan.log`: no matches
- `true_boolean_scan.log`: no matches
- `declaration_presence_scan.tsv`: representative W835/W836 declarations present in Required, ProductSuccess, and Original audits

Completion status:
- Nonterminal checkpoint only.
- No product-success claim is made.
