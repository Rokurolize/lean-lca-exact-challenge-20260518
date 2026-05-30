# W973 provider search ledger

Baseline: W972 is the current clean target-no-univ-data route. It verifies a nonterminal route with 17 explicit inputs, including two W961 closed-embedding closedness fields: selected-difference closed-embedding components and the mapped explicit cokernel closed-embedding provider.

Decision: W973 adds `ClosedEmbeddingClosednessDataProviderW973`, a branch-specific provider for those two closed-embedding fields. It intentionally does not widen back to `MetrizableWppDiagramAndMappedCokernelClosednessDataProviderW725`, because W725 can also be the closed-map branch and therefore cannot project closed-embedding components in general.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| W725 closedness data directly | Use the older matched closedness provider | Unsafe for this route because W725 is a closed-map-or-closed-embedding branch sum, while W972 needs closed-embedding fields. |
| Endpoint strict-exact data | Bundle endpoint closed/open/cokernel/kernel fields | Existing endpoint strict-exact data does not directly recover the kernel-equality and cokernel-top fields used by W972. |
| W945 localized-unit data | Bundle right adjoint, adjunction, and unit witness | W972 has lower-level kernel/cokernel/chosen-isomorphism fields, so this needs a separate alignment. |

Result: selected for W973. Explicit input names drop from 17 to 16. Product success remains false because the W973 field surface still consists of explicit assumptions and does not construct the original four-task completion witness.
