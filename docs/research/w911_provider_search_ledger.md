# W911 Provider Search Ledger

W910 is the current closed-map source-fields target-fields relation-fields route. It verifies a nonterminal stable ExactAt route with 35 explicit inputs, including one bundled `MetrizableWppEndpointTopologyFactsProviderW856` endpoint-topology provider and one bundled `MetrizableWppLocalizedRightAdjointDataProviderW721` localized-right-adjoint provider.

The next supported provider boundary is W856. `MetrizableWppEndpointTopologyFactsProviderW856` contains exactly three fields: endpoint incoming maps are closed embeddings, endpoint outgoing maps are open, and endpoint `ExactAt` hypotheses imply the outgoing maps are epis.

W911 therefore replaces the single W856 provider input with those three fields and reconstructs W856 through `endpointTopologyFactsOfFieldsW911`. The route then projects back to W910 through `w910LeavesOfEndpointFieldsW911`.

This is intentionally nonterminal. W519 already supplies the forgetful homology-preservation part of W720 through the W856 closedness branch, so W911 does not reintroduce a separate forgetful homology-preservation assumption.

After W911, the route has 37 remaining explicit inputs. Deferred provider boundaries include W721 localized-right-adjoint fields, fixed-target uniqueness obligations, source-image normalization, branch-selection or no-argument witnesses, and the final review packet.
