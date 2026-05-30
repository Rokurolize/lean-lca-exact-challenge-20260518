# W1301 Provider Search Ledger

W1301 inspects the endpoint-localized-unit boundary exposed after W1300.

- Checked surface: `endpointLocalizedUnitChoiceFullDataInputNamesW983`.
- Count: `5`, witnessed by `canonicalW983EndpointLocalizedUnitUnpackedInputNamesW1301_count`.
- Comparison: W983 expands the W984 full-data surface from `4` to `5`, and expands the current W1270 one-input W987 obligation from `1` to `5`.
- Primitive-route check: `closedMapBoundaryRelationDataTargetNoUnivClosednessDataNormalizedSourceTriangulationDataEndpointLocalizedUnitDataFieldsInputNamesW949` has count `4`, still larger than the current W1270 one-input surface.
- Repack check: `repackEndpointLocalizedUnitDataW1301_eq` proves that unpacking W949 into endpoint strict-exact witnesses and W945 localized-unit data, then repacking, recovers the same provider.

Conclusion: W983/W949 endpoint-localized-unit unpacking does not close the remaining W987 obligation. Product success is not claimed.
