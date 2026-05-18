# 使用した出典

## Lean/mathlib

- ローカルmathlib `Mathlib/Topology/Category/TopCat/Basic.lean`: `TopCat`、`TopCat.Hom`、連続写像、位相空間の圏を確認した。
- ローカルmathlib `Mathlib/Algebra/Category/Grp/Basic.lean`と`Preadditive.lean`: `AddCommGrpCat`、bundleされた加法可換群、zero morphismを確認した。
- ローカルmathlib `Mathlib/Topology/Algebra/ContinuousMonoidHom.lean`: `MetrizableLCA.Hom`で使う連続加法準同型の根拠にした。
- ローカルmathlib `Mathlib/Topology/Metrizable/Basic.lean`: `TopologicalSpace.MetrizableSpace`の根拠にした。
- ローカルmathlib `Mathlib/Algebra/Homology/ShortComplex/Basic.lean`、`Exact.lean`、`ShortExact.lean`: `ShortComplex`、`ShortComplex.Exact`、`ShortComplex.ShortExact`の根拠にした。
- ローカルmathlib `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`: Quillen exact-categoryインターフェイスで使うpushout/pullback名の根拠にした。
- ローカルmathlib `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`: abelian category側のderived category境界を確認した。
- ローカルmathlib `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`: `CategoryTheory.Abelian.Ext`、degree zeroのHom同値、加法群instance、Extの合成を確認した。
- ローカル確認用anchor: `LeanLCAExactChallenge/MathlibSurvey.lean`。

## 数学文献

- Daniel Quillen, "Higher Algebraic K-Theory I": exact categoryという目標概念の原典として参照した。
- Theo Bühler, "Exact Categories", arXiv:0811.1480, https://arxiv.org/abs/0811.1480 。Quillen exact categoryの枠組みと、exact categoryからderived categoryを作る方向を確認するために使った。
- Norbert Hoffmann and Markus Spitzweck, "Homological algebra with locally compact abelian groups", arXiv:math/0510345, https://arxiv.org/abs/math/0510345 。LCA群をquasi-abelian categoryとして扱う方針を確認するために使った。
- Jean-Pierre Schneiders, "Quasi-Abelian Categories and Sheaves", SMF, https://smf.emath.fr/publications/categories-et-faisceaux-quasi-abeliens 。Hoffmann-Spitzweckが依拠するquasi-abelian categoryの背景として使った。

## ローカル形式化成果

- `LeanLCAExactChallenge/ExactCategory/Basic.lean`: Quillen exact categoryのローカルinterfaceをコンパイル確認した。
- `LeanLCAExactChallenge/LCA/Basic.lean`: metrizable LCA groupsのbundleされた圏と射の層をコンパイル確認した。
- `LeanLCAExactChallenge/LCA/StrictExact.lean`: strict sequence述語と代数的kernel/cokernel accessorをコンパイル確認した。
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`: strict LCA exact-category定理が未整備である境界を、明示的なsource-patch仮定としてコンパイル確認した。
- `LeanLCAExactChallenge/Ext/Yoneda.lean`: abelian category Extに到達できる境界をコンパイル確認した。
- `LeanLCAExactChallenge/Derived/Bounded.lean`: exact categoryのbounded derived infinity-categoryに必要な構成interfaceをコンパイル確認した。
