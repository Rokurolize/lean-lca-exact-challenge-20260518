# W938 Provider Search Ledger

Run root: `/home/roku/codex-consultant-20260517/outputs/lean_lca_hourly_strategy_runs/20260526T162329Z_codex_parent_w938_endpoint_strict_exact_unit_strict_exact_components_route`

Baseline: W937 commit `31f23cc`, with product success still false and 39 explicit route inputs remaining.

| Candidate | Expected Lean surface | Prior evidence | Decision |
| --- | --- | --- | --- |
| Endpoint strict-exact consolidation | Replace W937's separate endpoint closed-embedding, open-map, and ExactAt-to-ShortExact fields with one endpoint `MetrizableLCA.strictShortExact` field | `StrictShortExact` provides closed inclusion, open map, and surjectivity; a focused probe showed `K.ExactAt i` plus strict surjectivity builds `(K.sc i).ShortExact` without needing `Balanced MetrizableLCA` | Selected for W938. |
| ExactAt-conditioned endpoint strict exactness | Use `K.ExactAt i → MetrizableLCA.strictShortExact (K.sc i)` as the endpoint field | W937's closed-embedding and open-map endpoint fields are unconditioned in the current route, so an ExactAt-conditioned strict field cannot project to W937 without weakening the route shape | Rejected for W938. |
| Strict-exact-to-ShortExact without ExactAt | Derive `S.ShortExact` from `MetrizableLCA.strictShortExact S` alone | `ShortComplex.exact_of_f_is_kernel` avoided balancedness but exposed a separate `S.HasHomology` requirement; the current endpoint route already has `ExactAt`, which is the cheaper exactness source | Deferred. |
| Concrete endpoint strict-exact construction | Construct the actual endpoint strict exact witness instead of exposing it as a field | No no-argument construction for arbitrary endpoint short complexes was identified in this pass | Deferred. |

Validation target: `LeanLCAExactChallenge/Derived/ClosedMapTargetCompactNoUnivMembershipEndpointStrictExactUnitStrictExactComponentsPrimitiveFieldRoute.lean`.
