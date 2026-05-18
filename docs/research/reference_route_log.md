# 参照経路ログ

## 目的

このログは、Leanコードそのものでは見えにくい調査経路を読める形で残すためのものだ。今回の成果物は、strict metrizable LCA列がQuillen exact categoryをなすところまではローカルLean証明で到達し、さらにYoneda extension chainの局所的な商群とbounded complexのlocalizationまで進めた。そのうえで、標準的なYoneda Extとbounded derived infinity-categoryとして何が残るかを明示する記録である。

## 方針を変えた参照と検索

- ローカルmathlibの`LeanLCAExactChallenge/MathlibSurvey.lean`と`scripts/check_mathlib_survey.sh`により、`TopCat`、`AddCommGrpCat`、`ShortComplex`、`DerivedCategory`、`CategoryTheory.Abelian.Ext`が利用可能だと確認した。これにより、最初から低水準の圏、短完全列、Ext風の型を自作する方針は採らず、既存APIに薄く接続する方針にした。
- `.lake/packages/mathlib/Mathlib`に対する`rg`検索で、Quillen exact categoryそのもののmodule/classは見つからなかった。`Quasi`を含む大量のヒットはquasi-isomorphismやquasicategoryなど別概念が多く、LCA群のquasi-abelian category定理には直結しなかった。この検索結果により、exact-category interfaceとstrict LCA安定性補題をローカルで実装する方針にした。
- Bühler, "Exact Categories"は、Quillenのexact categoryを短完全列のclassとして扱うこと、またexact categoryのderived categoryが目標概念として自然であることを確認するために使った。ローカルの`QuillenExactCategory`はこの文献の用語に合わせて、conflation、inflation、deflation、pushout/pullback安定性を表に出している。
- Hoffmann-Spitzweck, "Homological algebra with locally compact abelian groups"は、LCA群をquasi-abelian categoryとして扱う経路を示していた。この参照により、strict LCA sequenceからexact categoryへ進む数学的方向は妥当だと判断したが、その定理をLeanでそのまま呼べるmathlib APIは確認できなかった。
- Schneiders, "Quasi-Abelian Categories and Sheaves"は、Hoffmann-Spitzweckが依拠するquasi-abelian categoryの背景として参照した。これは「閉埋め込みと開全射」というstrict morphismの安定性を証明するなら、quasi-abelian category側の理論をmathlibへ入れる必要がある、というgapの説明に使った。
- mathlibの`Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`と生成ドキュメントは、`CategoryTheory.Abelian.Ext`が既に存在し、`instAddCommGroup`やdegree zeroのHomとの関係も提供していることを示した。これは作業をかなり楽にした近道だが、対象はabelian categoryなので、exact category上のYoneda Extを完成させる近道ではなかった。
- mathlibの`ShortComplex.Splitting`、`Topology.Constructions`の積空間API、`IsClosedEmbedding`と`IsOpenMap`の合成APIを調べ直したことで、split short complexがstrict short exact sequenceになる証明と、strict short exact sequenceの同型不変性をローカルで実装できた。この調査により、pushout/pullback安定性をローカル補題として個別に証明する方針へ進んだ。
- `TopCat`のpullbackが部分空間として実装されていること、閉部分空間がlocal compactnessを継承すること、任意部分型がmetrizabilityを継承することを確認した。この経路により、`MetrizableLCA`のpullback objectを積の閉部分群として構成し、limit cone、射影の全射性と開写像性補題、kernel mapの代数的完全性移送と閉埋め込み移送をローカルで証明できた。さらに`limit.isoLimitCone`でmathlibの選んだcategorical pullbackへ移し、deflationのpullback安定性をローカル証明へ変えた。
- mathlibの`Topology/Algebra/Group/Quotient.lean`、`Topology/Algebra/IsUniformGroup`、`Topology/Metrizable/Basic`を確認し、閉部分群による商が局所コンパクト性を継承し、商加法群の右一様性と第一可算性からmetrizabilityを得られることをローカル補題として組み立てた。これにより`MetrizableLCA`の閉部分群商を一般化し、pushout候補を`(X₂ × Y) / range (x ↦ (f x, -a x))`として構成できた。
- `PushoutCocone.IsColimit.mk`、`QuotientAddGroup.lift`、`QuotientAddGroup.eq_iff_sub_mem`を使う経路に切り替えたことで、明示的pushoutの余極限性、標準余核写像、余核写像の開全射性、代数的完全性をLeanで確認できた。さらに`Topology.isEmbedding_graph`、`isClosed_eq`、`IsClosedEmbedding.prodMap`、`IsQuotientMap.isClosed_preimage`を組み合わせ、関係部分群の閉性と`Y ⟶ pushout`の閉埋め込み性もローカル補題として閉じた。これにより`MetrizableLCA.quillenExactCategory`は未証明引数なしのinstanceになった。
- `Mathlib/CategoryTheory/Limits/Shapes/BinaryBiproducts.lean`を確認し、`MetrizableLCA`の積をbinary biproductとして登録した。これにより、cochain complexのmapping coneを使うために必要な`HasBinaryBiproducts MetrizableLCA`を満たせた。
- `Mathlib/GroupTheory/QuotientGroup.Basic`と`FreeAbelianGroup`を組み合わせ、正次数の`YonedaExt`をextension chainの自由加法可換群そのものではなく、明示した生成関係で割る方針へ進めた。今回入れた関係は、hom等式、termwiseな一段拡大の同型、分裂一段拡大を零元にする関係である。これは標準的なYoneda Extに近づくが、任意の鎖同型、Baer sum図式、Yoneda積の関係はまだ残る。
- `Mathlib/Algebra/Homology/HomotopyCategory/MappingCone.lean`と`Mathlib/CategoryTheory/Localization/HasLocalization.lean`を確認したことで、bounded cochain complexのfull subcategoryを、mapping coneがexact acyclicである射でlocalizeする方針へ切り替えた。これは当初の単なるfull subcategory modelより強い近道だったが、ordinary categoryのlocalizationであり、stable infinity-categoryそのものではない。

## 既存APIへの適応とローカル作業の分担

既存APIに適応した部分は、`ShortComplex`をexact category interfaceの土台にしたこと、`TopCat`や連続写像のclassを`MetrizableLCA`のbundleに使ったこと、`FreeAbelianGroup`とadditive quotientをextension chain群の加法構造に使ったこと、`CochainComplex.mappingCone`と`MorphismProperty.Localization`をbounded derived側のlocalizationに使ったことである。

ローカルで新しく作った部分は、`QuillenExactCategory` class、`MetrizableLCA` category、`strictShortExact`述語、split strict exactness証明、同型不変性証明、明示的pullback object、pullback射影の全射性と開写像性補題、pullback kernel mapの代数的完全性補題と閉埋め込み補題、categorical pullbackへの移送補題、閉部分群商の`MetrizableLCA`化、明示的pushout、pushout関係部分群の閉性、`Y ⟶ pushout`の閉埋め込み性、pushout余極限性、pushoutの余核写像に関する開全射性と代数的完全性、categorical pushoutへの移送補題、`QuillenExactCategory MetrizableLCA` instance、`MetrizableLCA`のbinary biproduct、exact-category conflation chainから作る`YonedaExt`、Yoneda chainの局所的な商関係、そしてbounded exact weak equivalenceでlocalizeする`Dbounded`である。

## 失敗した探索とfalse lead

`ExactCategory`、`QuillenExactCategory`、`QuasiAbelian`に相当するmathlib宣言を探したが、今回のローカルmathlibでは直接使える宣言は見つからなかった。`QuasiIso`や`Quasicategory`のAPIは多数見つかったが、要求されているquasi-abelian categoryやQuillen exact categoryとは別の概念だった。

`DerivedCategory`は存在したが、確認できたAPIはabelian categoryを前提にしていた。したがって、`D^b(C,E)`をexact categoryから直接作る部分は既存APIで短縮できなかった。

pushoutについては、商群と開商写像のAPIは有効だったが、閉埋め込み`f`と任意の連続準同型`a`から`range (x ↦ (f x, -a x))`の閉性を直接返す既存補題は見つからなかった。最終的には、閉グラフ補題をローカルで作り、shear homeomorphismと閉埋め込みの積を使ってこの不足を補った。

## 近道の有無

有効な近道は三つあった。第一に、`ShortComplex`が既にあり、conflationの入れ物を自作せずに済んだ。第二に、`FreeAbelianGroup`とadditive quotientがあり、extension chainを生成元とする商群を短く実装できた。第三に、`CochainComplex.mappingCone`と`MorphismProperty.Localization`があり、bounded complexのlocalizationを一から商圏として作らずに済んだ。

ただし、これらだけではproduct theoremは完成しない。strict metrizable LCA sequenceのpushout/pullback安定性はローカル証明で閉じ、Yoneda extension chainの局所的な商群とordinary localizationとしての`Dbounded`まではコンパイルした。しかし標準的なYoneda Extで必要な任意の鎖同型、Baer sum図式、Yoneda積の関係、stable infinity-categoryとしてのenhancementは未解決のままである。
