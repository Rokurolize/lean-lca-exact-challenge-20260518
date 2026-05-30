# W980 provider search ledger

Baseline: W979 split one W977 full-data provider into the W971 component-field record and rebuilt the provider through W978. Product success remained false because the W977 provider itself was still assumed and the split surface still exposed 18 W971 obligations.

Decision: W980 targets one concrete part of that split surface: the endpoint kernel/cokernel-top provider. It replaces the W974 endpoint provider assumption by a single endpoint strict short-exact family, then constructs W974 data by projecting closed inclusion and open map from `StrictShortExact`, deriving cokernel-top from surjectivity, and deriving kernel equality from the algebraic exactness field.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| Construct W977 full data outright | Remove the top-level provider assumption | Still unsupported: no no-argument construction exists for the boundary/relation, target, closedness, normalized-source, localized-adjunction, or unit mapping-cone providers. |
| Attack localized adjunction | Potentially remove two categorical fields | The current local APIs expose a provider boundary, but no no-argument adjoint/adjunction constructor was identified. |
| Attack boundary/relation or target no-univ data | Potentially remove older topological fields | These are broader topological obligations; endpoint strict exactness has direct local projection lemmas already available. |

Result: selected for W980. The route verifies the endpoint W974 provider is constructible from a strict short-exact family, reducing that local endpoint surface from four fields to one strict-exact family. Product success remains false because the W980 route still assumes seven provider-level inputs and no original four-task completion witness exists.
