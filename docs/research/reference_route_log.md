# 参照経路ログ

## 目的

このログは、Leanコードそのものでは見えにくい調査経路を読める形で残すためのものだ。今回の成果物は、exact LCA categoryの完全な形式化ではなく、どこまでが既存mathlibに乗り、どこからsource patchが必要になるかを明示するhandoffである。

## 方針を変えた参照と検索

- ローカルmathlibの`LeanLCAExactChallenge/MathlibSurvey.lean`と`scripts/check_mathlib_survey.sh`により、`TopCat`、`AddCommGrpCat`、`ShortComplex`、`DerivedCategory`、`CategoryTheory.Abelian.Ext`が利用可能だと確認した。これにより、最初から低水準の圏、短完全列、Ext風の型を自作する方針は採らず、既存APIに薄く接続する方針にした。
- `.lake/packages/mathlib/Mathlib`に対する`rg`検索で、Quillen exact categoryそのもののmodule/classは見つからなかった。`Quasi`を含む大量のヒットはquasi-isomorphismやquasicategoryなど別概念が多く、LCA群のquasi-abelian category定理には直結しなかった。この検索結果が、product successではなくsource-patch-needed handoffへ切り替える決定打になった。
- Bühler, "Exact Categories"は、Quillenのexact categoryを短完全列のclassとして扱うこと、またexact categoryのderived categoryが目標概念として自然であることを確認するために使った。ローカルの`QuillenExactCategory`はこの文献の用語に合わせて、conflation、inflation、deflation、pushout/pullback安定性を表に出している。
- Hoffmann-Spitzweck, "Homological algebra with locally compact abelian groups"は、LCA群をquasi-abelian categoryとして扱う経路を示していた。この参照により、strict LCA sequenceからexact categoryへ進む数学的方向は妥当だと判断したが、その定理をLeanでそのまま呼べるmathlib APIは確認できなかった。
- Schneiders, "Quasi-Abelian Categories and Sheaves"は、Hoffmann-Spitzweckが依拠するquasi-abelian categoryの背景として参照した。これは「閉埋め込みと開全射」というstrict morphismの安定性を証明するなら、quasi-abelian category側の理論をmathlibへ入れる必要がある、というgapの説明に使った。
- mathlibの`Mathlib/Algebra/Homology/DerivedCategory/Ext/Basic.lean`と生成ドキュメントは、`CategoryTheory.Abelian.Ext`が既に存在し、`instAddCommGroup`やdegree zeroのHomとの関係も提供していることを示した。これは作業をかなり楽にした近道だが、対象はabelian categoryなので、exact category上のYoneda Extを完成させる近道ではなかった。
- mathlibの`ShortComplex.Splitting`、`Topology.Constructions`の積空間API、`IsClosedEmbedding`と`IsOpenMap`の合成APIを調べ直したことで、split short complexがstrict short exact sequenceになる証明と、strict short exact sequenceの同型不変性をローカルで実装できた。この調査により、`StrictExactQuillenAxioms`の役割はpushout/pullback安定性の境界へ縮んだ。
- `TopCat`のpullbackが部分空間として実装されていること、閉部分空間がlocal compactnessを継承すること、任意部分型がmetrizabilityを継承することを確認した。この経路により、`MetrizableLCA`のpullback objectを積の閉部分群として構成し、limit cone、射影の全射性補題、kernel mapの代数的完全性移送と閉埋め込み移送をローカルで証明できた。

## 既存APIへの適応とローカル作業の分担

既存APIに適応した部分は、`ShortComplex`をexact category interfaceの土台にしたこと、`TopCat`や連続写像のclassを`MetrizableLCA`のbundleに使ったこと、`CategoryTheory.Abelian.Ext`を`YonedaExt`の確認済み境界として包んだことである。

ローカルで新しく作った部分は、`QuillenExactCategory` class、`MetrizableLCA` category、`strictShortExact`述語、split strict exactness証明、同型不変性証明、明示的pullback object、pullback射影の全射性補題、pullback kernel mapの代数的完全性補題と閉埋め込み補題、`StrictExactQuillenAxioms`というpushout/pullback安定性のsource-patch境界、そして`BoundedDerivedInfinityCategory`という構成interfaceである。`StrictExactQuillenAxioms`とderived側のinterfaceは完成済み定理ではなく、後続のsource patchが置き換えるべき境界をLeanで壊れない形にしたものだ。

## 失敗した探索とfalse lead

`ExactCategory`、`QuillenExactCategory`、`QuasiAbelian`に相当するmathlib宣言を探したが、今回のローカルmathlibでは直接使える宣言は見つからなかった。`QuasiIso`や`Quasicategory`のAPIは多数見つかったが、要求されているquasi-abelian categoryやQuillen exact categoryとは別の概念だった。

`DerivedCategory`は存在したが、確認できたAPIはabelian categoryを前提にしていた。したがって、`D^b(C,E)`をexact categoryから直接作る部分は既存APIで短縮できなかった。

## 近道の有無

有効な近道は二つあった。第一に、`ShortComplex`が既にあり、conflationの入れ物を自作せずに済んだ。第二に、abelian categoryの`Ext` APIがあり、Extの加法群構造をローカルで再構成せずに、確認済み境界として提示できた。

ただし、これらはproduct theoremを完成させる近道ではない。strict metrizable LCA sequenceのpushout/pullback安定性、exact category上のYoneda Ext、bounded derived infinity-categoryは未解決のままであり、`audit/blockers/`のLeanファイルで再現されるsource patch課題として残した。
