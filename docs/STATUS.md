# Status

Honest snapshot of the four project objectives. Updated at milestones only; see git log for day-to-day history.

## Objective status

| # | Objective | Status |
|---|---|---|
| 1 | Quillen exact category formalized | Complete |
| 2 | `(MetrizableLCA, E)` is an exact category | Complete |
| 3 | Yoneda Ext groups | Complete |
| 4 | Bounded derived ∞-category `D^b(C,E)` | Partial |

### Objective 4 detail

The ordinary triangulated bounded-derived semantics is proved: the corrected cycle-object acyclicity route, the Verdier quotient, and the full ordinary stable package (preadditivity, zero object, finite products, coproducts, biproducts, shift additivity, `Pretriangulated`, and `IsTriangulated`) are formalized and unconditional.

The genuine stable ∞-category enhancement is in progress and is not complete. The all-dimensional Joyal special-left-outer-horn theorem is proved without assumptions. Its parameterized extension gives the presentation comparison the right lifting property against every simplicial monomorphism, so the ordinary-nerve equivalence-forcing quasicategory now satisfies the full mapping-quasicategory localization universal property. The induced homotopy functor is an ordinary localization, and the canonical comparison from the corrected bounded derived category to its homotopy category is proved to be an equivalence.

The coherent DG side now has a canonical map from the ordinary nerve, an all-dimensional compatible inner-horn filler, and therefore a verified direct DG homotopy-coherent quasicategory. It also has an equivalence-forced localized coherent-nerve candidate that explicitly inverts every generated corrected weak edge and an explicit base-change map from the ordinary localization presentation. The required Dwyer–Kan or Drinfeld comparison is isolated as the statement that this base-change map is a bicategorical equivalence; it remains unproved. Conditional on exactly that proposition, the full mapping-localization property, homotopy-category equivalence, corrected-derived comparison, and canonical factorization have been transferred to the coherent DG candidate. At chain level, mapping cones are actual bounded DG objects, their maps-out complexes are strictly isomorphic to the expected path fibers, and this identity has been transported through truncation and Dold–Kan to a pullback theorem for the enriched mapping simplicial sets. The corrected Drinfeld quotient carrier and its general square-zero differential cancellation are formalized. `quotientCompositionMap`, `quotientIdentityElement`, both quotient unit laws, summand associativity, large-summand associativity, `quotientCompositionMap_assoc`, the finite-sum large-summand Leibniz identity, and its universe-matched coefficient tensor lift are proved. The remaining composition work is bundling these data as a DG category; the quotient universal property and objectwise Dwyer–Kan comparison also remain.

Still missing, and required before objective 4 can be called complete:

1. Prove the Dwyer–Kan or Drinfeld base-change comparison between the ordinary localization carrier and the localized coherent DG carrier.
2. Construct and verify the genuine stable square calculus for the localized quasicategory, including finite ∞-bicompleteness and the equivalence of cartesian and cocartesian squares.

Do not claim objective 4 complete until the localization universal property, DG-carrier comparison, genuine stability proof, and ordinary comparison equivalence are all inhabited and verified. The first and fourth items are now complete; the second and third remain mandatory.

## Remaining tasks

1. Prove `MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence` by a genuine Dwyer–Kan or corrected Drinfeld DG-quotient comparison; the free-equivalence interval mono-RLP alone does not compare the ordinary and coherent base mapping objects.
2. Finish the corrected Drinfeld quotient: bundle the existing composition, identity, differential, associativity, unit laws, and proved quotient coefficient Leibniz identity as a DG category, prove the quotient universal property, and derive the objectwise mapping-space comparison needed for `MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence`.
3. Turn the enriched zero object and mapping-cone path-fiber pullback into the corner-extension adjunctions, finite ∞-bicompleteness, and bicartesian-square theorem required by `StableSquareCalculus`.
4. Transfer the verified stable structure across the localization comparison and package the final bounded derived ∞-category only after that transfer is checked.
5. If compatibility with the direct chain localization is still required, prove the composite-localization statement recorded by `BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput`; do not replace it with the generally false raw-chain Ore-calculus claim.
6. Keep the honest ordinary stable core as the objective-4 baseline and do not fill remaining ∞-categorical gaps with assumptions.
7. Any future mathlib migration must update `lean-toolchain` and Lake dependencies coherently and must not reuse older compiled artifacts as evidence.
8. Migrate legacy `exactAcyclic` lemmas theorem by theorem only when a corrected theorem needs them, and keep the legacy degreewise `boundedExactWeakEquivalence` route labeled compatibility-only.

## Verification

Full build:

```bash
lake build LeanLCAExactChallenge
```

Fast single-file check while iterating:

```bash
lake env lean -j1 <path/to/File.lean>
```

If `lake env` is unavailable offline, fall back to the direct `LEAN_PATH` incantation:

```bash
export PATH="$HOME/.elan/toolchains/leanprover--lean4---v4.31.0/bin:$PATH"
LIBS=$(find -L .lake -path '*/build/lib/lean' -type d | sort | paste -sd: -)
LDLIBS=$(find -L .lake -path '*/build/lib' -type d | sort | paste -sd: -)
export LEAN_PATH="$LIBS:$PWD"
export LD_LIBRARY_PATH="$LDLIBS"
lean -j1 -o .lake/build/lib/lean/<Path/To/File>.olean \
  -i .lake/build/lib/lean/<Path/To/File>.ilean \
  <path/to/File.lean>
```

## Notes

1. This file is updated at milestones only, not per commit. Day-to-day history lives in `git log`.
