# Alternating Tail Extend Transport Probe

Generated: 2026-05-19T23:20:00Z

このメモは、Nat添字の具体的なalternating-tail収縮を、bounded-derived obstructionで使う`ℤ`添字右tailへ移す親側probeを記録する。

## Lean artifacts

- `LeanLCAExactChallenge/AlternatingTailExtendTransport.lean`
- `audit/blockers/alternating_tail_extend_transport_probe.lean`

このmoduleはNat添字のalternating tailとcontracting homotopyをライブラリ宣言としてまとめ、`intAlternatingTailGE p := natAlternatingTail.extend (ComplexShape.embeddingUpIntGE p)`を定義する。

確認済みの宣言は次のとおり。

- `intAlternatingTailGE_extendMap_id`
- `intAlternatingTailGE_extendMap_zero`
- `transportedNatTailHomotopy`
- `intAlternatingTailGEContractingHomotopy`
- `transportedNatTailHomotopy_hom_eq`
- `intAlternatingTailGEHomotopyEquivZero`
- `intAlternatingTailGE_hasUpperUnboundedNonzeroTerms`

`intAlternatingTailGE_extendMap_id`と`intAlternatingTailGE_extendMap_zero`は、Nat側収縮の端点写像が`HomologicalComplex.extendMap`で右非有界`ℤ`添字tailへ移ることを確認する。w111の結果を読んだ後、mathlibにはshape-changing homotopy transportそのものとして`Homotopy.extend`、`Homotopy.extend_hom_eq`、`Homotopy.extendEquiv`が既にあることを確認した。親側ではこれを使い、`intAlternatingTailGEContractingHomotopy`まで構成した。

## Frontier result

最初に試した`Functor.mapHomotopy`は、対象圏間の加法的関手用であり、複体のshapeを変える`ComplexShape.Embedding.extendFunctor`には直接使えなかった。この失敗は正しい境界だったが、必要なAPIは別名で存在していた。`Homotopy.extend`は`ComplexShape.embeddingUpIntGE p`に沿ってNat側の`Homotopy (𝟙 natAlternatingTail) 0`を`ℤ`添字tailへ移す。

さらに`intAlternatingTailGEHomotopyEquivZero`で零複体とのhomotopy equivalenceを作り、`intAlternatingTailGE_hasUpperUnboundedNonzeroTerms`で各上界より右に非零項があることも証明した。これにより、contractible tail具体例の局所課題は「Homotopy輸送」から「この具体的tailを既存のstrictification/representative-selection obstructionとどう接続するか」へ移った。
