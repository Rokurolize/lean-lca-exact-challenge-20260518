# Goal: Product-Success Lean Formalization Challenge for Exact LCA Categories

Target workdir: `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518`

Start command for the non-consultant TUI session:

```text
/goal follow the instructions in /home/roku/codex-consultant-20260517/outputs/proposed_goals/lean_lca_exact_category_challenge_goal_20260518.md
```

## Objective

Produce a machine-checked Lean/mathlib formalization of the following four-part challenge:

1. Formalize exact categories in Quillen's sense.
2. Formalize and prove that the category of metrizable locally compact abelian groups, with strict short exact sequences given by closed inclusions, open surjections, and algebraic kernel/cokernel after forgetting topology, is an exact category.
3. Formalize Yoneda-Ext groups for this exact category.
4. Formalize the bounded derived infinity-category `D^b(C,E)` for this exact category.

This is intentionally ambitious and product-success only. The full four-part result is the only completion target. Missing mathlib foundations are work items to implement locally in this repository, not a reason to complete with a handoff. If a required exact-category, quasi-abelian, Yoneda-Ext, or bounded derived infinity-category foundation is absent from current mathlib, build the missing Lean interface, definitions, lemmas, and proofs locally until the requested theorem and constructions compile.

Do not call `update_goal(status="complete")` while any part remains incomplete. A source-patch-needed handoff, gap report, blocked report, or "strongest frontier" is useful progress evidence, but it is not a terminal outcome for this Goal.

## Benchmark Intent And Reader Context

This run is also an evaluation of Codex as an autonomous mathematical software-engineering agent. The human audience is primarily Japanese readers, including the requester and 羊飼いPさん. The point is not merely to produce any artifact named "exact category"; the point is to make it possible to judge how Codex researched unfamiliar mathematics, mapped it to current mathlib, chose a formalization strategy, and honestly reported what was proved, what was only scaffolded, and what remains blocked.

If you find a decisive shortcut by web research, source search, existing mathlib API, an existing implementation, or a paper that collapses the expected difficulty, disclose it plainly. This is good evidence, not cheating, as long as the route is documented. Do not hide the route by presenting the final Lean code as if it was derived from first principles.

Required transparency artifact:

```text
docs/research/reference_route_log.md
```

This file must be written in Japanese and must explain:

- which references, source files, library APIs, and searches materially changed the plan;
- what each important reference contributed;
- whether any reference made the task easier than the original prompt likely implied;
- which parts are original local formalization work versus adaptation of existing mathlib patterns;
- which failed searches or false leads mattered for the final strategy.

The final review packet and final response must preserve this evaluation context. A packet that only contains Lean files and command outputs, with no readable account of how the agent proceeded, is incomplete.

## Japanese-Language Deliverables

The working language inside Lean declarations may follow mathlib conventions and may use English identifiers. However, user-facing explanatory deliverables must be Japanese unless a quoted source title or Lean/API name is naturally English.

At minimum, these files must contain substantive Japanese prose:

```text
README_FOR_REVIEW.md
docs/research/sources.md
docs/research/reference_route_log.md
docs/research/mathlib_gap_analysis.md
terminal_outcome/terminal_outcome.json
```

For JSON files, fields such as `summary`, `known_gaps`, and any human-readable notes should be Japanese. The final response to the user must also be Japanese.

## Current Environment

Use the prepared project:

```text
/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518
```

The project was initialized with mathlib and a working cache:

```bash
lake +leanprover/lean4:v4.30.0-rc2 init LeanLCAExactChallenge math
```

Known passing baseline before this goal was assigned:

```bash
lake build
scripts/check_mathlib_survey.sh
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
```

Baseline evidence: `lake build` completed successfully with 1786 jobs, and `LeanLCAExactChallenge/MathlibSurvey.lean` checked these mathlib anchors:

```text
TopCat
TopCat.Hom
AddGroupTopology
LocallyCompactSpace
MetricSpace
AddCommGrpCat
AddCommGrpCat.Hom
CategoryTheory.ShortComplex
CategoryTheory.ShortComplex.Exact
DerivedCategory
HasDerivedCategory
CategoryTheory.Abelian.Ext
CategoryTheory.Abelian
CategoryTheory.Preadditive
CategoryTheory.Limits.HasKernel
CategoryTheory.Limits.HasCokernel
```

## Primary Sources To Use

Use primary or near-primary sources. Prefer local mathlib source in `.lake/packages/mathlib/Mathlib` over memory.

Lean/mathlib sources:

- `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Category/TopCat/Basic.html`
- `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/ShortComplex/ConcreteCategory.html`
- `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/DerivedCategory/Basic.html`
- `https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.html`
- `.lake/packages/mathlib/Mathlib/CategoryTheory/Abelian/Basic.lean`
- `.lake/packages/mathlib/Mathlib/Algebra/Homology/ShortComplex/Exact.lean`
- `.lake/packages/mathlib/Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`
- `.lake/packages/mathlib/Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`

Mathematical sources:

- Quillen, Higher Algebraic K-Theory I, for the original exact-category notion.
- Bühler, Exact Categories, arXiv:0811.1480, `https://arxiv.org/abs/0811.1480`.
- Hoffmann and Spitzweck, Homological algebra with locally compact abelian groups, arXiv:math/0510345, `https://arxiv.org/abs/math/0510345`.
- Schneiders, Quasi-abelian categories and sheaves, `https://smf.emath.fr/publications/categories-et-faisceaux-quasi-abeliens`.

Record any additional sources you rely on in `docs/research/sources.md`, with URLs and the exact Lean/math statements they support.

## Completion Contract

Completion type: product-success.

The only terminal outcome that may call `update_goal(status="complete")` is `product_success`, with `terminal_outcome/terminal_outcome.json.product_complete=true`.

Non-success states such as missing API, source patch needed, mathematical uncertainty, external tool failure, time pressure, context pressure, or partial handoff are not completion states. If one of those occurs, record the state in progress notes and continue researching or implementing. If the state truly requires human input, ask for that input, but do not call `update_goal(status="complete")`.

Previous artifacts in this workdir may say `source_patch_needed_handoff` or `product_complete=false`. Treat them as historical evidence from an earlier, insufficiently ambitious Goal. They must not be reused as the final terminal outcome for this Goal.

## Required Work Products

All writes must stay under:

```text
/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518
```

Required files or equivalent stronger artifacts:

```text
LeanLCAExactChallenge/ExactCategory/Basic.lean
LeanLCAExactChallenge/ExactCategory/Conflation.lean
LeanLCAExactChallenge/LCA/Basic.lean
LeanLCAExactChallenge/LCA/StrictExact.lean
LeanLCAExactChallenge/LCA/ExactCategory.lean
LeanLCAExactChallenge/Ext/Yoneda.lean
LeanLCAExactChallenge/Derived/Bounded.lean
audit/RequiredDeclarations.lean
audit/ProductSuccessDeclarations.lean
audit/external_audit.py
docs/research/sources.md
docs/research/reference_route_log.md
docs/research/mathlib_gap_analysis.md
terminal_outcome/terminal_outcome.json
README_FOR_REVIEW.md
manifest.json
```

You may choose different internal module names only if `audit/RequiredDeclarations.lean` exposes the exact public declarations listed below.

## Required Public Declarations

`audit/RequiredDeclarations.lean` must compile and include `#check` lines for these public declarations:

```lean
#check LeanLCAExactChallenge.QuillenExactCategory
#check LeanLCAExactChallenge.QuillenExactCategory.Conflation
#check LeanLCAExactChallenge.QuillenExactCategory.inflation
#check LeanLCAExactChallenge.QuillenExactCategory.deflation
#check LeanLCAExactChallenge.QuillenExactCategory.split_conflation
#check LeanLCAExactChallenge.QuillenExactCategory.pushout_inflation
#check LeanLCAExactChallenge.QuillenExactCategory.pullback_deflation

#check LeanLCAExactChallenge.MetrizableLCA
#check LeanLCAExactChallenge.MetrizableLCA.Hom
#check LeanLCAExactChallenge.MetrizableLCA.strictShortExact
#check LeanLCAExactChallenge.MetrizableLCA.closed_inclusion_of_strict
#check LeanLCAExactChallenge.MetrizableLCA.open_surjection_of_strict
#check LeanLCAExactChallenge.MetrizableLCA.algebraic_kernel_of_strict
#check LeanLCAExactChallenge.MetrizableLCA.algebraic_cokernel_of_strict
#check LeanLCAExactChallenge.MetrizableLCA.quillenExactCategory

#check LeanLCAExactChallenge.YonedaExt
#check LeanLCAExactChallenge.YonedaExt.zero_equiv_hom
#check LeanLCAExactChallenge.YonedaExt.baer_sum
#check LeanLCAExactChallenge.YonedaExt.instAddCommGroup

#check LeanLCAExactChallenge.BoundedDerivedInfinityCategory
#check LeanLCAExactChallenge.Dbounded
```

For product success, these declarations must not merely package assumptions. The declarations for the LCA exact category must connect the strict-sequence conditions to the Quillen exact-category axioms by proofs using mathlib definitions, local lemmas, and cited source-compatible mathematics.

Add `audit/ProductSuccessDeclarations.lean` to check the stronger product contract. It must compile and must verify, by `#check`, `#guard_msgs`, `example`, or another Lean-native mechanism, that:

- `LeanLCAExactChallenge.MetrizableLCA.quillenExactCategory` is available without a source-patch assumption argument such as `StrictExactQuillenAxioms`;
- exact-category Yoneda-Ext groups are defined for the strict metrizable LCA exact category, not only as a wrapper around `CategoryTheory.Abelian.Ext`;
- the bounded derived infinity-category construction is defined for the strict metrizable LCA exact category, not only as a placeholder interface that assumes a construction exists;
- no public product declaration depends on an explicitly named "assumption", "source patch", "blocker", "frontier", or "gap" class.

## Formalization Standards

Use Lean/mathlib conventions:

- Keep `relaxedAutoImplicit = false`.
- Prefer structures/classes that expose reusable fields and theorem names, not opaque existential blobs.
- Use `CategoryTheory.ShortComplex` where appropriate.
- Reuse `TopCat`, `AddCommGrpCat`, `AddGroupTopology`, `LocallyCompactSpace`, `MetricSpace`, `ShortComplex.Exact`, `DerivedCategory`, and `Abelian.Ext` where they fit.
- Do not add `axiom`, `unsafe`, `sorry`, `admit`, or trust-me theorem stubs.
- Do not redefine a mathlib concept under a new name without first checking whether mathlib already has it.
- Do not use `by classical exact ...` to hide a missing construction behind an assumption.
- Do not introduce any product-facing class or theorem whose purpose is to assume the requested result, such as `StrictExactQuillenAxioms`, `SourcePatch`, `ConstructionAssumption`, `ProductAssumption`, or a renamed equivalent.
- If an intended product theorem appears to need a missing library theorem, first create a minimal `audit/blockers/*.lean` reproduction for diagnosis, then implement the missing theorem locally. Blocker reproductions may remain as historical diagnosis only if the final product no longer depends on the blocker.

## Verification Oracle

Product success requires all of the following to pass from a clean checkout of the workdir:

```bash
lake build
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
lake env lean audit/RequiredDeclarations.lean
lake env lean audit/ProductSuccessDeclarations.lean
python3 audit/external_audit.py --root "$PWD" --terminal-outcome terminal_outcome/terminal_outcome.json
git diff --check
```

`audit/external_audit.py` must be read-only by default and must fail on:

- missing required files;
- failing `lake build` evidence;
- missing or stale `audit/RequiredDeclarations.lean` evidence;
- missing or stale `audit/ProductSuccessDeclarations.lean` evidence;
- missing `docs/research/reference_route_log.md`, or a route log that does not explain the role of references/searches in Japanese;
- missing Japanese explanatory prose in `README_FOR_REVIEW.md`, `docs/research/sources.md`, `docs/research/mathlib_gap_analysis.md`, or human-readable `terminal_outcome.json` fields;
- any `sorry`, `admit`, `axiom`, or `unsafe` in local Lean sources;
- any final required declaration that depends on a source-patch assumption, blocker class, placeholder interface, or unproved local assumption;
- `terminal_outcome.json.outcome` other than `product_success`;
- `terminal_outcome.json.product_complete` other than `true`;
- nonempty `terminal_outcome.json.known_gaps`;
- any final response or packet metadata that claims completion while listing remaining gaps;
- packet-internal final zip SHA256 treated as authoritative;
- stale terminal state such as `pending`, `in_progress`, `not_run`, `blocked`, `source_patch_needed_handoff`, or `failed_nonterminal` while claiming product success.

## Review Packet Requirement

Before calling `update_goal(status="complete")`, create a review packet under:

```text
packets/lean_lca_exact_category_challenge/
```

Preferred structure:

```text
README_FOR_REVIEW.md
manifest.json
external_audit.py
goal-directive/
initial/
input/
run/
audit/
terminal_outcome/
```

Also create:

```text
packets/lean_lca_exact_category_challenge.zip
packets/lean_lca_exact_category_challenge.zip.sha256
```

The final zip SHA256 is authoritative only in the external `.sha256` sidecar or an external build-provenance file outside the zip. Do not put the zip's final SHA256 inside `manifest.json`, `README_FOR_REVIEW.md`, `terminal_outcome.json`, or any other packet-internal file as authoritative evidence. Inside the packet use per-file hashes or a content hash tree.

Required negative fixture:

```text
audit/negative_fixtures/self_referential_zip_sha_authoritative/
```

The external audit must fail this fixture if a packet-internal manifest or terminal-outcome file treats the packet zip's own final SHA256 as authoritative.

## Terminal Outcomes

Write `terminal_outcome/terminal_outcome.json` using this shape:

```json
{
  "outcome": "product_success",
  "product_complete": true,
  "update_goal_allowed": true,
  "summary": "",
  "verified_commands": [],
  "required_declarations_checked": [],
  "known_gaps": [],
  "packet_zip": "",
  "packet_sha256_sidecar": "",
  "git_commit": ""
}
```

### product_success

`product_complete=true`.

You may call `update_goal(status="complete")` only if all verification-oracle commands pass, the review packet passes clean extraction audit, and the public declarations represent the full four-part challenge without forbidden placeholders or unproved axioms.

### Non-Completion States

The following states may be recorded in progress notes or scratch diagnostics, but they may not be used as terminal outcomes and may not call `update_goal(status="complete")`:

- `source_patch_needed_handoff`;
- `mathematically_false_or_misstated`;
- `blocked_external`;
- `failed_nonterminal`;
- any state with `product_complete=false`;
- any state with nonempty `known_gaps`;
- any state that recommends "next work" required to finish the four-part theorem.

If you reach one of these states, continue the work, ask the user for a specific mathematical decision, or leave the Goal active. Do not finish the Goal with unresolved gaps.

## Forbidden Operations

- Do not launch `codex`, `codex-patched`, `codex-exec`, other Codex workers, or subagents from inside this TUI session.
- Do not mutate `/home/roku/codex-consultant-20260517` except reading this goal.
- Do not push to GitHub.
- Do not change global Lean/elan defaults.
- Do not edit files outside `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518`.
- Do not claim product success for a bounded handoff.
- Do not call `update_goal(status="complete")` for any outcome other than `product_success`.
- Do not complete with `source_patch_needed_handoff`, `blocked_external`, `failed_nonterminal`, or any `product_complete=false` terminal outcome.
- Do not treat "mathlib does not have this" as a blocker; implement the missing layer locally unless the user makes a mathematical scope decision.

## Git Expectations

Use Git locally in the target workdir. Commit the prepared baseline and subsequent logical changes when they are coherent. The final terminal outcome should include the final commit hash if a commit was made. Do not commit `.lake/`, build artifacts, packet zips, large logs, secrets, or private progress TSV files.

## Final Response Format

When finished, respond in Japanese with:

```text
outcome:
product_complete:
update_goal_called:
workdir:
final_commit:
verified_commands:
packet_zip:
packet_sha256_sidecar:
terminal_outcome_json:
reference_route_log:
remaining_gaps:
next_recommended_goal:
```

For a completed run, `remaining_gaps` must be `[]` or an explicit Japanese statement that there are no remaining product gaps. `next_recommended_goal` may suggest downstream polish, upstreaming, or independent review, but it must not name work required to finish the four-part challenge.
