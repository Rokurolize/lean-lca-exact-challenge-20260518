# 使用した出典

## Lean/mathlib

- ローカルmathlib `Mathlib/Topology/Category/TopCat/Basic.lean`: `TopCat`、`TopCat.Hom`、連続写像、位相空間の圏を確認した。
- ローカルmathlib `Mathlib/Algebra/Category/Grp/Basic.lean`と`Preadditive.lean`: `AddCommGrpCat`、bundleされた加法可換群、zero morphismを確認した。
- ローカルmathlib `Mathlib/Topology/Algebra/ContinuousMonoidHom.lean`: `MetrizableLCA.Hom`で使う連続加法準同型の根拠にした。
- ローカルmathlib `Mathlib/Topology/Metrizable/Basic.lean`: `TopologicalSpace.MetrizableSpace`の根拠にした。
- ローカルmathlib `Mathlib/Topology/Constructions/SumProd.lean`: split short complexを積への同型として扱うときの`continuous_fst`、`continuous_snd`、`isOpenMap_snd`、積への埋め込みを確認した。
- ローカルmathlib `Mathlib/Topology/Maps/Basic.lean`: `IsClosedEmbedding`の合成と同型による移送の根拠にした。
- ローカルmathlib `Mathlib/Topology/Compactness/LocallyCompact.lean`: pullback objectを閉部分空間として作るとき、local compactnessを継承する根拠にした。
- ローカルmathlib `Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean`: `MetrizableLCA`の明示的pullback coneがlimitであることを示すために使った。
- ローカルmathlib `Mathlib/Algebra/Homology/ShortComplex/Basic.lean`、`Exact.lean`、`ShortExact.lean`: `ShortComplex`、`ShortComplex.Exact`、`ShortComplex.ShortExact`の根拠にした。
- ローカルmathlib `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`: Quillen exact-categoryインターフェイスで使うpushout/pullback名と、明示的pushoutをcategorical pushoutへ移す同型の根拠にした。
- ローカルmathlib `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`: abelian category側のderived category境界を確認した。
- ローカルmathlib `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`: `CategoryTheory.Abelian.Ext`、degree zeroのHom同値、加法群instance、Extの合成を確認した。
- ローカルmathlib `Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean`: `MetrizableLCA`のbinary biproduct instanceを積で作るために使った。
- ローカルmathlib `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`: cochain complexのmapping coneを確認し、exact weak equivalenceをconeのexact acyclicityで定義するために使った。
- ローカルmathlib `Mathlib/CategoryTheory/Localization/HasLocalization.lean`と`Predicate.lean`: morphism propertyのlocalized categoryとlocalization functorを使って`Dbounded`を構成するために使った。
- ローカル確認用anchor: `LeanLCAExactChallenge/MathlibSurvey.lean`。

## 数学文献

- Daniel Quillen, "Higher Algebraic K-Theory I": exact categoryという目標概念の原典として参照した。
- Theo Bühler, "Exact Categories", arXiv:0811.1480, https://arxiv.org/abs/0811.1480 。Quillen exact categoryの枠組みと、exact categoryからderived categoryを作る方向を確認するために使った。
- Norbert Hoffmann and Markus Spitzweck, "Homological algebra with locally compact abelian groups", arXiv:math/0510345, https://arxiv.org/abs/math/0510345 。LCA群をquasi-abelian categoryとして扱う方針を確認するために使った。
- Jean-Pierre Schneiders, "Quasi-Abelian Categories and Sheaves", SMF, https://smf.emath.fr/publications/categories-et-faisceaux-quasi-abeliens 。Hoffmann-Spitzweckが依拠するquasi-abelian categoryの背景として使った。

## ローカル形式化成果

- `LeanLCAExactChallenge/ExactCategory/Basic.lean`: Quillen exact categoryのローカルinterfaceをコンパイル確認した。
- `LeanLCAExactChallenge/LCA/Basic.lean`: metrizable LCA groupsのbundleされた圏、射、preadditive構造、binary biproductをコンパイル確認した。
- `LeanLCAExactChallenge/LCA/StrictExact.lean`: strict sequence述語、代数的kernel/cokernel accessor、split strict exactness、同型不変性をコンパイル確認した。
- `LeanLCAExactChallenge/LCA/Pullback.lean`: `MetrizableLCA`のpullback object、limit cone、strict sequenceのcategorical pullback安定性をコンパイル確認した。
- `LeanLCAExactChallenge/LCA/Pushout.lean`: 閉部分群商、明示的pushout、関係部分群の閉性、標準射の閉埋め込み性、余核写像の開全射性と代数的完全性、strict sequenceのcategorical pushout安定性をコンパイル確認した。
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`: strict LCA exact-category instanceを未証明引数なしでコンパイル確認した。
- `LeanLCAExactChallenge/Ext/Yoneda.lean`: exact categoryのconflation chainから作るローカル`YonedaExt`をコンパイル確認した。degree 0はHom、正次数はextension chainを生成元とする自由加法可換群を、extension鎖の同型、hom等式、分裂一段拡大を零元にする関係、Baer sum witnessから来る関係で割った群である。分裂一段拡大が0になり、Baer sum witnessがある場合に一段Extで`sum = e₁ + e₂`になる定理も確認した。
- `LeanLCAExactChallenge/Derived/Bounded.lean`: bounded cochain complexのfull subcategoryを、mapping coneがexact acyclicである射でlocalizeする`Dbounded`をコンパイル確認した。
