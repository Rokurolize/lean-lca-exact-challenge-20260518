# W974 provider search ledger

Baseline: W973 is the current clean closed-embedding-closedness-data route. It verifies a nonterminal route with 16 explicit inputs, including four endpoint fields: endpoint closed embedding, endpoint open map, endpoint cokernel-top, and endpoint kernel equality.

Decision: W974 adds `EndpointKernelCokernelTopDataProviderW974` to package exactly those four endpoint fields. The route projects W974 data back to W973, rebuilds W973 leaves, and delegates through the existing W973/W972 stack.

Rejected alternatives:

| Candidate | Effect | Reason deferred |
| --- | --- | --- |
| W726 endpoint/localized data | Bundle endpoint topology and localized right-adjoint data | W726 provides strict-topology/localized data, not the kernel-equality and cokernel-top endpoint surface used by W973. |
| W857 endpoint kernel/cokernel facts | Use `ExactAt` kernel/cokernel facts | W857 works over `ExactAt` facts for a different topology input, not W973's direct closed/open/cokernel-top/kernel-equality fields. |
| Endpoint strict-exact data | Use a strict short exact witness | It does not directly recover the endpoint kernel-equality and cokernel-top fields without additional lemmas or choices, so W974 keeps the current lower field surface exact. |

Result: selected for W974. Explicit input names drop from 16 to 13. Product success remains false because the remaining W974 field surface still consists of explicit assumptions and does not construct the original four-task completion witness.
