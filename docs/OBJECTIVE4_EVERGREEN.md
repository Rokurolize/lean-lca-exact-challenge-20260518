# Objective 4 evergreen contract

This document records the progress-independent meaning of the instruction `目的4を完了してください`.

It must remain valid when branches, theorem names around intermediate constructions, current blockers, and implementation progress change.

Current progress belongs in `docs/STATUS.md`, the checked-out source tree, and `git log`.

Historical checkpoints and scratch files are evidence and working material only; they are not the source of truth for the current implementation.

## Shorthand instruction

When the user says only `目的4を完了してください`, use DevSpace and work in:

```text
/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518
```

The repository is:

```text
Rokurolize/lean-lca-exact-challenge-20260518
```

Do not ask which repository, which objective, or whether tools may be used.

The instruction means to resume from the current verified repository state and complete Objective 4 end to end.

It does not mean to reproduce the last conversation's plan, continue from a remembered line number, or trust an old blocker report without checking the source.

## Mathematical objective

Objective 4 is the genuine bounded derived infinity-category enhancement `D^b(C,E)` for the exact category built from `MetrizableLCA`.

The corrected exact-category route is based on cycle-object acyclicity through `exactAcyclicWithCycles` and weak equivalences through `boundedExactWeakEquivalenceWithCycles`.

The ordinary triangulated bounded-derived category is a baseline that must remain valid, but an ordinary Verdier quotient or triangulated equivalence alone does not complete Objective 4.

The legacy degreewise `exactAcyclic` and `boundedExactWeakEquivalence` route is compatibility-only.

Migrate a legacy lemma only when a corrected theorem genuinely needs it.

Do not replace the corrected route with the legacy route.

## Public completion obligations

Objective 4 is incomplete until the following public mathematical content is inhabited without additional assumptions.

### Base-change comparison

The proposition

```lean
MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence
```

must be proved.

This means that

```lean
metrizableOrdinaryToDirectDGBaseChangeQCatMap
```

is a bicategorical equivalence between the ordinary equivalence-forcing localization carrier and the localized coherent direct-DG carrier.

The proof must be a genuine Dwyer-Kan comparison or a corrected Drinfeld DG-quotient comparison.

A proof may pass through the corrected Drinfeld quotient, an enriched universal property, objectwise mapping-space equivalences, endpoint-fiber recognition, or another mathematically equivalent route.

A reduction theorem is not the missing proof.

In particular, the following facts do not by themselves prove the base-change equivalence:

- inversion of generated weak edges;
- essential surjectivity on homotopy categories;
- a strict comparison triangle;
- free-equivalence interval extension;
- a monomorphism right-lifting property that only establishes the ordinary mapping-localization property;
- definitions of endpoint-recognition input contracts without inhabitants;
- a conditional theorem that accepts `MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence` or an equivalent missing property as an argument.

### Stable square calculus

A genuine stable square calculus must be constructed for the final bounded-derived localization quasicategory.

The fixed ordinary localization carrier is:

```lean
metrizableEquivalenceForcingQCat
```

The final public result must at least provide:

```lean
StableSquareCalculus metrizableEquivalenceForcingQCat
```

or a public `StableInfinityStructure metrizableEquivalenceForcingQCat` that is converted to the equivalent `StableSquareCalculus` structure.

It is valid to construct the stable structure first on

```lean
directDGEquivalenceForcingQCat
```

and transfer it across the proved base-change bicategorical equivalence.

The stable structure must genuinely contain all of the following data and proofs:

- a zero object through `PointedStructure`;
- limits and colimits for every finite simplicial indexing set through `HasFiniteInfinityBicompleteness`;
- the quasicategory structures required for square and corner internal Homs;
- a right Kan extension adjunction for the pullback corner restriction;
- a left Kan extension adjunction for the pushout corner restriction;
- a proof that every square is cartesian exactly when it is cocartesian.

A mapping-cone object, a chain-level pullback, or an objectwise path-fiber calculation is necessary input but is not by itself a `StableSquareCalculus` inhabitant.

Finite products, finite coproducts, or ordinary finite limits in the homotopy category are not substitutes for finite infinity-bicompleteness.

Definitions of corner-extension or finite-bicompleteness contracts are not substitutes for inhabitants of those contracts.

### Final package

The final unconditional bounded-derived infinity-category package must be public, imported by the repository's normal public import surface, and usable without supplying any of the previously missing propositions as parameters.

`LeanLCAExactChallenge.lean` must import the completed public modules.

`docs/STATUS.md` may be changed from `Partial` only after the public package and every required verification gate pass.

Objective 4 is not complete merely because two isolated declarations type-check if the final package still depends on assumptions, is not exported, or cannot be built from the repository root.

## Corrected Drinfeld quotient route

The corrected Drinfeld quotient is a valid route to the base-change theorem.

The route requires more than the carrier and DG laws.

A complete enriched-universal-property route must provide, as actual public constructions and proofs:

- evaluation of arbitrary corrected Drinfeld words in every target enriched category equipped with compatible contracting elements;
- compatibility of word evaluation with the full quotient differential, including all internal and contraction terms with the correct signs;
- a cochain map on each quotient Hom object;
- preservation of enriched identities;
- preservation of enriched composition;
- restriction to the original coefficient-changed DG functor;
- existence of the enriched extension;
- uniqueness at the functor level;
- the required natural-transformation or mapping-category statement when the chosen localization theorem needs full enriched universal equivalence rather than object-level existence;
- an objectwise mapping-space comparison after truncation, Dold-Kan, and coherent nerve;
- the comparison triangle needed to identify that objectwise result with the actual base-change map.

Do not publish a conditional alias such as a theorem whose only proof is to return an input assumption carrying the missing universal property.

Do not weaken a universal property to raw object and Hom data if the downstream theorem requires an enriched functor or equivalence of functor categories.

## Stable construction route

The raw direct-DG coherent nerve carries useful zero, shift, cone, and mapping-complex calculations.

Transporting those calculations to the final localization requires actual comparison maps and descent proofs.

The following interfaces must not be silently identified:

- a Dold-Kan enriched Hom simplicial set;
- an endpoint fiber or cylindrical mapping space of the coherent nerve;
- the corresponding mapping space after equivalence forcing;
- the mapping space in `metrizableEquivalenceForcingQCat`.

Whenever stability evidence moves between these interfaces, construct the map and prove the required equivalence or pullback preservation.

For finite infinity-bicompleteness, prove adjoints to constant-diagram functors for every finite simplicial set, or prove an equivalent theorem already recognized by the repository's public definitions.

Do not infer all finite infinity-limits from only a zero object and pullbacks unless the finite-cell gluing theorem that justifies the inference is formalized.

Do not infer all finite infinity-colimits from only a zero object and pushouts without the dual formalized gluing theorem.

## Invalid shortcuts

The following shortcuts are forbidden throughout Objective 4 work:

- `sorry`;
- `admit`;
- a new `axiom` or opaque trust declaration;
- `unsafe` declarations used to bypass proof obligations;
- `native_decide` as a replacement for the mathematical proof;
- warning or linter suppression used to hide an unresolved issue;
- strengthening a public theorem with an extra hypothesis that is exactly the missing result;
- weakening or renaming a required public theorem to make a different statement easier to prove;
- replacing a structure inhabitant with `Nonempty` when downstream code requires the structure itself;
- proving only a contract or residual proposition and reporting the original theorem complete;
- treating mock, documentation, or status declarations as mathematical evidence;
- relying on an uncompiled scratch theorem;
- counting a theorem that imports a file containing forbidden tokens as verified;
- assuming the desired equivalence because both sides model the same informal mathematics.

Only the standard axioms accepted by this repository's Lean trust basis may remain in final `#print axioms` output, normally `propext`, `Classical.choice`, and `Quot.sound` where genuinely required.

Do not migrate `lean-toolchain`, mathlib, or Lake dependency versions as part of Objective 4 unless the user separately requests a migration.

Do not reuse build artifacts from a different Lean or dependency revision as verification evidence.

If compatibility with a direct chain localization is still required, use the composite-localization route represented by `BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput`.

Do not replace it with the generally false raw-chain Ore-calculus claim.

## Start-of-session procedure

At the beginning of every new Objective 4 session:

1. Open `/home/roku/src/Rokurolize/lean-lca-exact-challenge-20260518` with DevSpace.
2. Read the global instructions, repository `AGENTS.md`, this file, the installed Lean 4 skill, and the current `docs/STATUS.md`.
3. Run `git status --short --branch`, `git diff --check`, `git diff --stat`, and inspect untracked files.
4. Read recent `git log` and identify the current relationship between `HEAD`, the working branch, and `origin/main`.
5. Check active Lean, Lake, and other heavy processes before starting expensive verification.
6. Derive the current mathematical blocker from checked source and compiler output.
7. Treat current source and Git history as authoritative over old conversation summaries and dated checkpoint files.

Do not reset, clean, stash, discard, overwrite, or move existing changes merely to obtain a clean tree.

Treat existing changes as work that must be understood and preserved, regardless of which prior session created them.

Do not delete untracked scratch files until their useful declarations have been assessed and any needed content has been promoted safely.

If the checkout contains unrelated dirty state and isolation is necessary, create a clean worktree from the appropriate current base without moving or destroying the dirty state.

Do not create a new worktree automatically when the existing checkout is the correct place to continue.

Do not assume a branch name recorded in an old handoff still exists or remains the right branch.

Do not ask the user to repeat context that can be recovered from the repository.

## Lean development procedure

Read `.agents/skills/lean4/SKILL.md` before editing Lean files.

Search the repository and mathlib for existing lemmas before proving transport, finite-index, tensor, category, or Dold-Kan facts from first principles.

Keep theorem statements, public signatures, and docstrings unchanged unless changing the API is mathematically necessary and compatible with the final objective.

Compile incrementally with:

```bash
lake env lean -j1 <touched-file>
```

Use the pinned Lean toolchain from the repository.

When another heavy workload is active or memory pressure is plausible, use `roku-resource-lease` and `LEAN_NUM_THREADS=1` for Lean checks.

Do not run overlapping compilers against the same scratch file.

Move verified reusable declarations out of `Scratch*.lean` modules into appropriately named public modules before treating them as delivered implementation.

Scratch files may contain experiments, duplicated names, stale routes, or incomplete proofs; importing a scratch file into the public root is not a substitute for curating it.

## Verification gates

Before Objective 4 can be reported complete, all of the following must pass from the final branch and exact final commit:

```bash
lake build LeanLCAExactChallenge
lake env lean -j1 LeanLCAExactChallenge.lean
scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge
scripts/audit_no_generated_files.sh
git diff --check
```

Every newly added or materially changed Lean file must also have passed an individual `lake env lean -j1 <file>` check during development.

Run `#print axioms` on at least:

```lean
MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence
```

and the final public stable-square or stable-infinity declaration for `metrizableEquivalenceForcingQCat`, together with the final bounded-derived infinity-category package declaration.

Inspect the output rather than merely running the command.

The final tree must contain no forbidden Lean tokens in the audited scope and no tracked generated logs, build products, or terminal transcripts.

Warnings that indicate unused assumptions, malformed declarations, failed simplification, or suspicious proof structure must be resolved rather than hidden.

## Delivery gates

Stage only files intentionally changed for Objective 4.

Print and inspect the exact staged file set before committing.

Use descriptive commits.

Do not force-push.

Push a branch, open a PR, review the final diff and checks, and merge to `main` only after all mathematical and verification gates pass.

The instruction `目的4を完了してください` authorizes those delivery actions only when completion is genuine.

Do not merge a partial milestone merely to satisfy the word `完了`.

If work stops before completion, report the exact proved boundary, the exact remaining theorem or compiler goal, the commands that passed, and the fact that no completion claim or final merge was made.

## Progress-independent reporting rule

Never claim Objective 4 complete while any required inhabitant, comparison map, descent theorem, adjunction, finite-shape construction, bicartesian recognition theorem, public export, verification gate, or final merge remains missing.

Do not measure completion by lines of Lean written, number of scratch lemmas, elapsed time, or apparent proximity of the current goal.

Completion is determined only by the public mathematical obligations and delivery gates in this document.
