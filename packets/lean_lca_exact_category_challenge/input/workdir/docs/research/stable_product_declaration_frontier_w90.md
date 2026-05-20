# Stable Product Declaration Frontier W90

This note follows the w85 projection-audit frontier and moves the review boundary one step closer to `audit/ProductSuccessDeclarations.lean`.

The proposed Lean-side product checker is `ProductSuccessDeclarationFrontier.DboundedStableCertificateReady` in `audit/blockers/stable_product_declaration_frontier_w90.lean`. It consumes one future `StableInfinityAudit.DboundedStableCertificate (Dbounded.infinityCategory C)` and requires four independent projections from that same certificate: `finiteLimits`, `finiteColimits`, `suspensionLoopEquivalence`, and `pushoutPullbackCompatibility`.

The file intentionally defines this as an audit/blocker skeleton, not as current product evidence. The current product-facing evidence still stops at `Dbounded.infinityCategory`, `Dbounded.infinityNerve`, and `Dbounded.infinityNerve_quasicategory`; `ordinary_nerve_only` records that this remains an ordinary quasicategory witness and does not satisfy the stable certificate checker.

External audit should continue to reject marker-only stable claims, ordinary-nerve-only product claims, and stable-certificate names without concrete field evidence. Lean semantic checking should begin at the point where the real `StableInfinityAudit.DboundedStableCertificate` API exists and `audit/ProductSuccessDeclarations.lean` can project all four stable fields from a single certificate term.
