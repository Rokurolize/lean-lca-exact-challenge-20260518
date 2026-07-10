import LeanLCAExactChallenge.Infinity.MetrizableDGSimplicialCategoryOrdinaryEquivalence

/-!
# Audit: ordinary direct dg category equivalence

These checks cover the vertex comparison, its compatibility with actual enriched composition and
identities, and the resulting equivalence of underlying ordinary categories. They intentionally do
not assert an equivalence of simplicial enrichments, nerves, or quasicategories.
-/

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes

open CategoryTheory

#check dgMappingDirectZModuleVerticesEquivBoundedMorphisms
#check dgMappingDirectZModuleVerticesEquivBoundedMorphisms_comp
#check dgMappingDirectZModuleVerticesEquivBoundedMorphisms_id
#check directDGToComplexFunctor
#check directDGToComplexHomEquiv
#check directDGToComplexFullyFaithful
#check directDGToComplexEssSurj
#check directDGSimplicialCategoryOrdinaryEquivalence

example :
    directDGSimplicialCategoryOrdinaryEquivalence.functor =
      directDGToComplexFunctor := by
  rfl

end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
