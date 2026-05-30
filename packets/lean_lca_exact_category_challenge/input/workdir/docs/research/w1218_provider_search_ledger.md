# W1218 Provider Search Ledger

- Goal: replace W1217's W981 endpoint/unit-strict-exact provider input surface with an already checked W982 localized-unit-choice provider surface.
- Reused route: W1011 constructs W981 endpoint/unit-strict-exact data from `BoundaryRelationTargetNoUnivClosedEmbeddingEndpointStrictExactLocalizedUnitChoiceDataProviderW982`.
- Bridge: W1218 feeds `unitStrictExactIsoDataOfLocalizedUnitChoiceW1011` into W1217, preserving the existing nonterminal chain.
- Result: explicit inputs move from 7 W981 endpoint/unit-strict-exact provider inputs to 6 W982 localized-unit-choice provider inputs.
- Product status: nonterminal; no product success claim or review packet readiness claim is made.
