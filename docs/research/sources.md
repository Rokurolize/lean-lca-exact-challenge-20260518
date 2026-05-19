# 使用した出典

## Lean/mathlib

- ローカルmathlib `Mathlib/Topology/Category/TopCat/Basic.lean`: `TopCat`、`TopCat.Hom`、連続写像、位相空間の圏を確認した。
- ローカルmathlib `Mathlib/Algebra/Category/Grp/Basic.lean`と`Preadditive.lean`: `AddCommGrpCat`、bundleされた加法可換群、zero morphismを確認した。
- ローカルmathlib `Mathlib/Topology/Algebra/ContinuousMonoidHom.lean`: `MetrizableLCA.Hom`で使う連続加法準同型の根拠にした。
- ローカルmathlib `Mathlib/Topology/Metrizable/Basic.lean`: `TopologicalSpace.MetrizableSpace`の根拠にした。
- ローカルmathlib `Mathlib/Topology/Constructions/SumProd.lean`: split short complexを積への同型として扱うときの`continuous_fst`、`continuous_snd`、`isOpenMap_snd`、積への埋め込み、`IsClosedEmbedding.prodMap`、`IsOpenMap.prodMap`を確認した。
- ローカルmathlib `Mathlib/Topology/Maps/Basic.lean`: `IsClosedEmbedding`の合成と同型による移送の根拠にした。
- ローカルmathlib `Mathlib/Topology/Compactness/LocallyCompact.lean`: pullback objectを閉部分空間として作るとき、local compactnessを継承する根拠にした。
- ローカルmathlib `Mathlib/CategoryTheory/Limits/Shapes/Pullback/PullbackCone.lean`: `MetrizableLCA`の明示的pullback coneがlimitであることを示すために使った。
- ローカルmathlib `Mathlib/Algebra/Homology/ShortComplex/Basic.lean`、`Exact.lean`、`ShortExact.lean`: `ShortComplex`、`ShortComplex.Exact`、`ShortComplex.ShortExact`の根拠にした。
- ローカルmathlib `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean`: Quillen exact-categoryインターフェイスで使うpushout/pullback名と、明示的pushoutをcategorical pushoutへ移す同型の根拠にした。
- ローカルmathlib `Mathlib/Algebra/Homology/DerivedCategory/Basic.lean`: abelian category側のderived category境界を確認した。
- ローカルmathlib `Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`: `CategoryTheory.Abelian.Ext`、degree zeroのHom同値、加法群instance、Extの合成を確認した。
- ローカルmathlib `Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean`: `MetrizableLCA`のbinary biproduct instanceを積で作ること、明示的な積モデルからmathlibのchosen binary biproductへの同型を作ること、対角・余対角を`biprod.lift`/`biprod.desc`として扱うことに使った。
- ローカルmathlib `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`: cochain complexのmapping coneを確認し、exact weak equivalenceをconeのexact acyclicityで定義するために使った。
- ローカルmathlib `Mathlib/CategoryTheory/Localization/HasLocalization.lean`と`Predicate.lean`: morphism propertyのlocalized categoryとlocalization functorを使って`Dbounded`を構成するために使った。
- ローカルmathlib `Mathlib/AlgebraicTopology/SimplicialSet/Nerve.lean`と`Mathlib/AlgebraicTopology/Quasicategory/Nerve.lean`: ordinary categoryのnerveがsimplicial setでありquasicategoryになることを確認し、`BoundedDerivedInfinityCategory`を`Dbounded`のnerveとして公開するために使った。
- ローカルmathlib `Mathlib/AlgebraicTopology/Quasicategory/StrictBicategory.lean`: quasicategoryのfull subcategory `SSet.QCat`を確認し、bounded derived quasicategoryをproduct-facingな対象として返すために使った。
- ローカルmathlib `Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.lean`: nerveとhomotopy category functorの随伴、および`nerveFunctorCompHoFunctorIso`を確認し、`Dbounded.infinityNerve`のhomotopy categoryが`Dbounded`へ戻ることを示すために使った。
- ローカルmathlib `Mathlib/CategoryTheory/Localization/Triangulated.lean`: ordinary pretriangulated/triangulated structureをlocalizationへ移すAPIを確認した。これはstable infinity-categoryそのものではないが、exact acyclic complexesをhomotopy category側で扱う次の経路の基礎になる。
- ローカルmathlib `Mathlib/Algebra/Homology/HomotopyCategory/Triangulated.lean`: additive category上のcochain complexのhomotopy categoryがtriangulatedになる経路を確認した。現在の`Dbounded`はまだこのhomotopy-category経路へ接続していない。
- ローカルmathlib `Mathlib/CategoryTheory/ObjectProperty/Shift.lean`と`Mathlib/CategoryTheory/ObjectProperty/ShiftAdditive.lean`: object propertyで切ったfull subcategoryがshiftで閉じる場合の`HasShift`とadditive shift functorを確認し、`BoundedComplexCategory`のshift前提整備に使った。
- ローカルmathlib `Mathlib/Algebra/Homology/Embedding/CochainComplex.lean`: cochain complexのstrict lower/upper boundsがshiftと同型で移るAPIを確認し、bounded cochain complexの同型閉性とshift閉性の証明に使った。
- ローカルmathlib `Mathlib/CategoryTheory/ObjectProperty/ContainsZero.lean`: object propertyがzero objectを含む場合にfull subcategoryへzero objectを移すAPIを確認し、bounded cochain complexのzero object前提整備に使った。
- ローカルmathlib `Mathlib/CategoryTheory/Localization/CalculusOfFractions/Preadditive.lean`: left calculus of fractions仮定下でlocalized categoryへpreadditive構造、localization functorのadditivity、zero objectを移すAPIを確認し、`Dbounded`の条件付きpreadditive/zero構造に使った。
- ローカルmathlib `Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean`: 自然同型を介したfunctor additivityを確認し、left calculus of fractions仮定下でlocalized shift functorのadditivityを得るために使った。
- 監査上の注意: このnerve経路はstable infinity-categoryの有限極限・有限余極限・suspension equivalenceを与えない。そのため外部監査には、ordinary nerveをproduct successとして主張する負例を拒否する検査を追加した。
- ローカル確認用anchor: `LeanLCAExactChallenge/MathlibSurvey.lean`。

## 数学文献

- Daniel Quillen, "Higher Algebraic K-Theory I": exact categoryという目標概念の原典として参照した。
- Theo Bühler, "Exact Categories", arXiv:0811.1480, https://arxiv.org/abs/0811.1480 。Quillen exact categoryの枠組みと、exact categoryからderived categoryを作る方向を確認するために使った。
- Norbert Hoffmann and Markus Spitzweck, "Homological algebra with locally compact abelian groups", arXiv:math/0510345, https://arxiv.org/abs/math/0510345 。LCA群をquasi-abelian categoryとして扱う方針を確認するために使った。
- Jean-Pierre Schneiders, "Quasi-Abelian Categories and Sheaves", SMF, https://smf.emath.fr/publications/categories-et-faisceaux-quasi-abeliens 。Hoffmann-Spitzweckが依拠するquasi-abelian categoryの背景として使った。

## ローカル形式化成果

- `LeanLCAExactChallenge/ExactCategory/Basic.lean`: Quillen exact categoryのローカルinterfaceをコンパイル確認した。
- `LeanLCAExactChallenge/LCA/Basic.lean`: metrizable LCA groupsのbundleされた圏、射、preadditive構造、binary biproduct、biproduct間のcoordinatewise map、明示的な積モデルとchosen binary biproductの同型、対角、余対角をコンパイル確認した。
- `LeanLCAExactChallenge/LCA/StrictExact.lean`: strict sequence述語、代数的kernel/cokernel accessor、split strict exactness、同型不変性、coordinatewise binary biproductでのstrict exactnessをコンパイル確認した。
- `LeanLCAExactChallenge/LCA/Pullback.lean`: `MetrizableLCA`のpullback object、limit cone、strict sequenceのcategorical pullback安定性をコンパイル確認した。
- `LeanLCAExactChallenge/LCA/Pushout.lean`: 閉部分群商、明示的pushout、関係部分群の閉性、標準射の閉埋め込み性、余核写像の開全射性と代数的完全性、strict sequenceのcategorical pushout安定性をコンパイル確認した。
- `LeanLCAExactChallenge/LCA/ExactCategory.lean`: strict LCA exact-category instanceを未証明引数なしでコンパイル確認した。
- `LeanLCAExactChallenge/Ext/Yoneda.lean`: exact categoryのconflation chainから作るローカル`YonedaExt`をコンパイル確認した。degree 0はHom、正次数はextension chainを生成元とする自由加法可換群を、extension鎖の同型、hom等式、分裂一段拡大を零元にする関係、split factorを含む鎖を零元にする関係、Baer sum witnessから来る関係、hom tail pushout witnessから来る関係で割った群である。分裂一段拡大とsplit factorを含む正次数鎖が0になり、Baer sum witnessがある場合に一段Extで`sum = e₁ + e₂`になり、`baer_sum`も同じ結果を返す定理も確認した。正次数の関係部分群に`sum - a - b`が入る任意のextension chainから同じ加法等式と`baer_sum`等式を出す汎用補題、一段拡大を左からspliceする写像が商群へ降りること、分裂一段拡大を左からspliceした値が0になること、純粋な一段拡大列からなる正次数鎖を固定した左spliceが右側の商群へ降りること、その固定左鎖に分裂因子があれば積が0になること、左端一段拡大の同型関係とBaer和を固定tailの前へ貼っても等式・加法等式・`baer_sum`等式が得られること、一段拡大の後ろにdegree 0のhom tailが付く一段ケースをpushout拡大へ落とす等式、任意正次数chainのdegree 0 tail合成を再帰的pushout normal formへ落とす等式、degree 0のhomが一段拡大の前に付くhead側をpullback拡大へ置き換えるgenerator-level作用も確認した。MetrizableLCAでは、一段拡大2つからcoordinatewise product extensionを作り、chosen binary biproduct端点へ移送し、さらに対角pullbackと余対角pushoutを使って任意の一段拡大対に対する標準的なBaer sum witnessを構成した。
- `LeanLCAExactChallenge/Derived/Bounded.lean`: bounded cochain complexのfull subcategoryを、mapping coneがexact acyclicである射でlocalizeする`Dbounded`をコンパイル確認した。さらに`BoundedDerivedInfinityCategory`を`Dbounded`のnerveが定める`SSet.QCat`として公開し、`Dbounded.infinityNerve_quasicategory`と`Dbounded.homotopyCategoryIso`でquasicategory性とhomotopy category比較を確認した。v76では`BoundedComplexCategory`、boundednessの同型閉性・shift閉性、exact acyclicityの同型不変性を確認した。v77ではexact acyclicityとbounded exact weak equivalenceのshift互換性を確認した。v78ではbounded complex側のzero objectと、left calculus of fractions仮定下の`Dbounded`のpreadditive/zero/additive shift APIを確認した。
