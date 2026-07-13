# Formalization Strategy

The project converges on source-level witnesses for the four objectives: the exact-category, metrizable LCA, and Yoneda Ext constructions are complete, while the stable bounded-derived infinity-category remains complete only when Lean checks the localization, coherent DG comparison, genuine stability, and ordinary comparison data.

The public import surface stays small and mathematical: exact-category interfaces, metrizable LCA constructions, Yoneda Ext, the corrected ordinary Verdier package, mapping-quasicategory localization, coherent DG constructions, and the genuine stability interface.

Exploratory route ledgers, assumption relays, status booleans, and provider-name adapters do not belong in the source tree. A retained module must contribute a checked mathematical construction or directly support a stated remaining theorem.

Future work should replace assumptions with concrete constructions or isolate the smallest precise theorem gap in `docs/STATUS.md`; adding metadata wrappers is not mathematical progress.

Prefer existing mathlib abstractions before local wrappers: use category-theory kernels, cokernels, short complexes, localizations, finite products, and exactness APIs directly when they fit, and document any local replacement with the missing mathlib theorem that would retire it.

The stable bounded-derived route must construct finite infinity-limits, finite infinity-colimits, corner-extension adjunctions, and the equivalence of cartesian and cocartesian squares; an ordinary triangulated nerve is not enough.

The root `LeanLCAExactChallenge.lean` imports every retained project module so the full build checks the complete maintained surface and unreachable source is visible as dead weight.
