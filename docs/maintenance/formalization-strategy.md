# Formalization Strategy

The project should converge on one source-level product contract: `OriginalFourTaskProductSuccess` is complete only when Lean checks the exact-category, metrizable LCA exact-category, Yoneda Ext, and stable bounded-derived infinity-category witnesses without relying on terminal metadata.

The public import surface should stay small and mathematical: exact-category interfaces, metrizable LCA constructions, Yoneda Ext, bounded-derived base definitions, finite-product support, stable-boundary bridge APIs, and original-four-task product data.

Long W-number route modules are exploratory route ledgers, not public API; they may stay in the tree while they compile and are used by audit declarations, but they should not be imported from the root module unless they become a named reusable theorem family.

Future route work should replace provider assumptions with concrete constructions or record a precise theorem gap in `docs/research/`; adding another metadata wrapper is not progress toward the product contract.

Prefer existing mathlib abstractions before local wrappers: use category-theory kernels, cokernels, short complexes, localizations, finite products, and exactness APIs directly when they fit, and document any local replacement with the missing mathlib theorem that would retire it.

The stable bounded-derived route must consume concrete field evidence for finite limits, finite colimits, suspension/loop equivalence, and pushout/pullback compatibility; an ordinary nerve, a certificate name alone, or a terminal outcome is not enough.

Audit files should import route modules explicitly, and the root `LeanLCAExactChallenge.lean` should expose only the intended review and user-facing modules.
