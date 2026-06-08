# Alternating Tail Extend Transport Probe

This note records the parent-side probe that transports a concrete Nat-indexed alternating-tail contraction to the right-unbounded `Int`-indexed tail used by the bounded-derived obstruction.

## Lean Surface

`LeanLCAExactChallenge/AlternatingTailExtendTransport.lean` packages the Nat-indexed alternating tail and contracting homotopy as library declarations. It defines `intAlternatingTailGE p := natAlternatingTail.extend (ComplexShape.embeddingUpIntGE p)`.

Checked declarations include:

```lean
LeanLCAExactChallenge.natAlternatingTailContractingHomotopy
LeanLCAExactChallenge.intAlternatingTailGE
LeanLCAExactChallenge.intAlternatingTailGEContractingHomotopy
LeanLCAExactChallenge.intAlternatingTailGEHomotopyEquivZero
LeanLCAExactChallenge.intAlternatingTailGE_hasUpperUnboundedNonzeroTerms
```

## Search Result

The first attempted route used `Functor.mapHomotopy`, but that API is for additive functors between object categories and does not directly transport along the shape-changing `ComplexShape.Embedding.extendFunctor`.

The useful existing API is `Homotopy.extend`, together with `Homotopy.extend_hom_eq` and `Homotopy.extendEquiv`. This transports `Homotopy (1 natAlternatingTail) 0` along `ComplexShape.embeddingUpIntGE p` to the `Int`-indexed tail.

## Current Boundary

The concrete tail is contractible and has nonzero terms arbitrarily far to the right. This moves the obstruction from homotopy transport to representative selection: future work must connect this tail to the existing strictification or boundedness-transport obstruction without claiming that bare homotopy equivalence preserves strict boundedness.
