# Status

Honest snapshot of the four project objectives. Updated at milestones only — see git log
for day-to-day history.

## Objective status

| # | Objective | Status |
|---|---|---|
| 1 | Quillen exact category formalized | Complete |
| 2 | `(MetrizableLCA, E)` is an exact category | Complete |
| 3 | Yoneda Ext groups | Complete |
| 4 | Bounded derived ∞-category `D^b(C,E)` | **Partial** |

### Objective 4 detail

The ordinary triangulated bounded-derived semantics is proved: the corrected cycle-object
acyclicity route, the Verdier quotient, and the full ordinary stable package
(preadditivity, zero object, finite products/coproducts/biproducts, shift additivity,
`Pretriangulated`, `IsTriangulated`) are formalized and unconditional.

The genuine stable ∞-category (quasicategory) enhancement is **in progress, not complete**.
Built so far: a coherent Dold-Kan simplicial category and its homotopy-coherent nerve, an
ordinary-nerve equivalence-forcing quasicategory that inverts every corrected weak
equivalence, and the full mapping-quasicategory localization specification together with
the canonical ordinary comparison functor out of the corrected localization. The generic
bridge from a quasicategory map having the right lifting property against every simplicial
monomorphism to a bicategorical equivalence is also inhabited. Mathlib v4.31's cartesian
pushout-product theorem is now integrated: functor simplicial sets are unconditionally
quasicategories, and mapping out of an inner-fibrant replacement is proved to be a
bicategorical equivalence. For the equivalence-forcing candidate, the final mapping
comparison is factored through the free-equivalence pushout presentation; its mapping object
is identified as the expected pullback, and a verified sufficient route to the full localization
property is the still-uninhabited mono-RLP of the presentation comparison at every target
quasicategory.

Still missing, and required before objective 4 can be called complete:

- Inhabitation of the ∞-localization universal property (a concrete candidate satisfying
  the full mapping-quasicategory specification). For the current candidate, a verified
  sufficient next target is the presentation-comparison mono-RLP described above.
- Comparison of the ordinary-nerve carrier with the coherent dg carrier.
- The stability proof for the localized quasicategory.
- Proof that the ordinary comparison functor is an equivalence.

**Do not claim objective 4 complete until these four items are inhabited and verified.**
This is a mandatory honesty marker for this repository.

## Remaining tasks

Condensed from prior `NEXT_STEPS.md`:

1. Continue the stable-∞ construction from the `LeanLCAExactChallenge/Infinity/` modules:
   prove the ∞-localization universal property, compare the ordinary-nerve carrier with the
   coherent dg carrier, prove the localized quasicategory stable, and identify its homotopy
   category with the corrected ordinary Verdier quotient. Pinned mathlib v4.31 has no
   ready-made quasicategorical or simplicial localization API — do not present either
   current carrier as the finished derived ∞-category.
2. If compatibility with the direct chain localization is still required, prove the
   composite-localization statement recorded by
   `BoundedExactWeakEquivalenceWithCyclesBoundedVerdierLocalizationInput` — do not replace it
   with the (generally false) raw-chain Ore calculus claim.
3. Keep the honest ordinary stable core (zero object, finite products/coproducts/biproducts,
   shift additivity, `Pretriangulated`, `IsTriangulated`) as the objective-4 baseline; raw
   chain-level calculus and ordinary finite limits/colimits remain blocked — see
   `docs/research/BLOCKER_CORRECTED_DBOUNDED_LITERAL_FIELDS.md` and do not fill the gap with
   assumptions.
4. Any future migration to a newer mathlib pin must update `lean-toolchain` and Lake
   dependencies coherently and must not reuse older compiled artifacts as evidence.
5. Migrate legacy `exactAcyclic` lemmas theorem-by-theorem only when the corresponding
   corrected theorem is actually needed.
6. Keep the legacy degreewise `boundedExactWeakEquivalence` route labeled compatibility-only.

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

- This file is updated at milestones only, not per commit. Day-to-day history lives in
  `git log`.
- For the current detailed blocker analysis, see
  `docs/research/BLOCKER_CORRECTED_DBOUNDED_LITERAL_FIELDS.md`.
