# Alternating Tail Extend Transport Probe

Generated: 2026-05-19T23:00:00Z

This note records the v138 parent probe for transporting the concrete Nat-indexed alternating-tail contraction toward the `ℤ`-indexed right tail used by the bounded-derived obstruction.

## Lean artifacts

- `LeanLCAExactChallenge/AlternatingTailExtendTransport.lean`
- `audit/blockers/alternating_tail_extend_transport_probe.lean`

The module packages the Nat alternating tail and its contracting homotopy as library declarations, then defines
`intAlternatingTailGE p := natAlternatingTail.extend (ComplexShape.embeddingUpIntGE p)`.

It proves:

- `intAlternatingTailGE_extendMap_id`
- `intAlternatingTailGE_extendMap_zero`

These lemmas confirm that the identity and zero endpoint maps of the Nat contraction transport through `HomologicalComplex.extendMap` to the right-unbounded `ℤ`-indexed tail.

## Frontier result

The attempted direct use of `Functor.mapHomotopy` was rejected by Lean because `Functor.mapHomotopy` acts on additive functors between object categories, while `ComplexShape.Embedding.extendFunctor` changes the complex shape. The current positive result is therefore endpoint transport, not a transported `Homotopy` object.

The remaining proof obligation is to build a shape-extension homotopy transport API, or explicitly construct the extended homotopy family on the `ℤ`-indexed tail using `extendXIso` and the zero-object behavior outside the image of `embeddingUpIntGE`.
