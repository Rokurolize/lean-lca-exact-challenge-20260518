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

The coherent DG side now has a canonical map from the ordinary nerve, an all-dimensional compatible inner-horn filler, and therefore a verified direct DG homotopy-coherent quasicategory. It also has an equivalence-forced localized coherent-nerve candidate that explicitly inverts every generated corrected weak edge and an explicit base-change map from the ordinary localization presentation. The direct localization map is proved essentially surjective on homotopy categories: the proof composes the ordinary equivalence, surjectivity of the ordinary-to-coherent nerve map on vertices, vertex preservation by free-equivalence forcing, and vertex preservation by inner-fibrant replacement. The strict localization triangle transfers this result to the base-change map. The required Dwyer–Kan or Drinfeld comparison is still the statement that this base-change map is a bicategorical equivalence. An endpoint-fiber recognition theorem now reduces that statement to three explicit inputs: coherent extension of the chosen object representatives and counit edges, full faithfulness of coherent postcomposition, and equivalence of every fixed-endpoint mapping-space map. Conditional on the base-change equivalence, the full mapping-localization property, homotopy-category equivalence, corrected-derived comparison, and canonical factorization have been transferred to the coherent DG candidate. At chain level, mapping cones are actual bounded DG objects, their maps-out complexes are strictly isomorphic to the expected path fibers, and this identity has been transported through truncation and Dold–Kan to a pullback theorem for the enriched mapping simplicial sets. The corrected Drinfeld quotient carrier, differential, composition, identity, associativity, unit laws, and coefficient Leibniz identity are formalized and packaged as a DG-enriched category. Any enriched functor on the original coefficient DG category equipped with chosen contracting elements now evaluates every corrected Drinfeld word; this evaluation commutes with the full quotient differential, is packaged as `evaluateCochainMap`, restricts to the supplied original enriched functor, and preserves enriched identities. Canonical positive-append coordinates and the positive-word head/contraction/tail decomposition are now formalized, including transport of the raw degree profile and its summand module. The appended positive profile is further identified as the unchanged head coordinate followed by the appended recursive tail, and this dependent transport is lifted to a canonical head-factor/tail-summand tensor decomposition. At the composition boundary, the positive head factor is now proved to pass through unchanged: the boundary module and boundary map reduce to the tail, and the full adjacent-merge tensor map is the tail merge prefixed by that head. Removing the surrounding equality transports upgrades this to an exact recursive factorization of `summandCompositionRemainder` through the tail remainder with the head fixed. Combining that factorization with the append tensor isomorphism now gives the corresponding exact recursion for `summandCompositionMap`: after canonical target transport, the head factor is fixed and only the tail composition map is applied. Multiplicativity of the cochain map, the resulting enriched-functor extension, the enriched universal property, and the objectwise Dwyer–Kan comparison remain unproved.

The evaluation-side and composition-side positive target isomorphisms are now proved to have exactly the same hom map, so the multiplicativity induction no longer has a transport mismatch between its recursive evaluation and recursive composition coordinates.

In those common coordinates, evaluation of an appended positive word is now expanded recursively. On pure head/tail tensors it is the enriched composition of the contracted head with the recursively evaluated appended tail. The remaining positive-append transports are also normalized back to the original coordinates: the head degree and contraction reduce to those of the original positive word, the recursive tail evaluation reduces to evaluation of the appended original tail profile, and the resulting pure-tensor formula is ready for the multiplicativity induction.

The positive-length multiplicativity induction step is now proved on canonical pure head/tail coordinates. Recursive summand composition fixes the head and composes only the tail; assuming multiplicativity for that tail, normalized evaluation recursion and target associativity prove multiplicativity for the full positive word.

The terminal zero-length case is also proved: composing two zero-word summands, transporting the result through the canonical dependent coordinates, and evaluating agrees with enriched composition of the two original DG morphism images. The zero-length left-word case against an arbitrary positive right word, followed by the linear/cochain-level assembly, remains open.

The coordinate layer for that remaining case is now public. The first ordinary factor of a positive word and its formal singleton contraction are represented by explicit summand maps; their direct target keeps the original head factor and the contraction's remaining identity factor. Comparison with the actual quotient composition and subsequent tail assembly remain open.

The comparison with actual quotient summand composition is now proved. The nil/singleton boundary is normalized to ordinary DG composition, its first identity factor acts as a right unit, and composing the positive head with the formal contraction equals the direct head/remaining-identity coordinates. Adjoining and identifying the positive tail remains open.

Still missing, and required before objective 4 can be called complete:

1. Prove the Dwyer–Kan or Drinfeld base-change comparison between the ordinary localization carrier and the localized coherent DG carrier.
2. Construct and verify the genuine stable square calculus for the localized quasicategory, including finite ∞-bicompleteness and the equivalence of cartesian and cocartesian squares.

Do not claim objective 4 complete until the localization universal property, DG-carrier comparison, genuine stability proof, and ordinary comparison equivalence are all inhabited and verified. The first and fourth items are now complete; the second and third remain mandatory.

## Remaining tasks

1. Prove `MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence` by a genuine Dwyer–Kan or corrected Drinfeld DG-quotient comparison; the free-equivalence interval mono-RLP alone does not compare the ordinary and coherent base mapping objects.
2. Prove multiplicativity of `evaluateCochainMap`, package it as the enriched-functor extension, prove the enriched universal property of the corrected Drinfeld quotient, and derive the objectwise mapping-space comparison needed for `MetrizableOrdinaryToDirectDGBaseChangeIsEquivalence`.
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
