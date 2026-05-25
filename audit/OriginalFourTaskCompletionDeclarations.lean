import LeanLCAExactChallenge

set_option autoImplicit false

/-!
Lean-native original four-task contract audit surface.

This file is intentionally nonterminal for the current source tree: it checks the public names from
the immutable contract and records, in Lean, that the current task-4 surface still has not supplied a
contract-completing stable bounded derived infinity-category witness.
-/

#check LeanLCAExactChallenge.QuillenExactCategory
#check LeanLCAExactChallenge.QuillenExactCategory.Conflation
#check LeanLCAExactChallenge.QuillenExactCategory.inflation
#check LeanLCAExactChallenge.QuillenExactCategory.deflation
#check LeanLCAExactChallenge.QuillenExactCategory.split_conflation
#check LeanLCAExactChallenge.QuillenExactCategory.pushout_inflation
#check LeanLCAExactChallenge.QuillenExactCategory.pullback_deflation

#check LeanLCAExactChallenge.MetrizableLCA
#check LeanLCAExactChallenge.MetrizableLCA.Hom
#check LeanLCAExactChallenge.MetrizableLCA.strictShortExact
#check LeanLCAExactChallenge.MetrizableLCA.closed_inclusion_of_strict
#check LeanLCAExactChallenge.MetrizableLCA.open_surjection_of_strict
#check LeanLCAExactChallenge.MetrizableLCA.algebraic_kernel_of_strict
#check LeanLCAExactChallenge.MetrizableLCA.algebraic_cokernel_of_strict
#check LeanLCAExactChallenge.MetrizableLCA.quillenExactCategory

#check LeanLCAExactChallenge.YonedaExt
#check LeanLCAExactChallenge.YonedaExt.zero_equiv_hom
#check LeanLCAExactChallenge.YonedaExt.baer_sum
#check LeanLCAExactChallenge.YonedaExt.instAddCommGroup

#check LeanLCAExactChallenge.BoundedDerivedInfinityCategory
#check LeanLCAExactChallenge.Dbounded

namespace LeanLCAExactChallenge

theorem originalFourTaskContract_currentOrdinaryRouteRejected :
    Dbounded.StableRouteAttempt.accepted
      (Dbounded.currentOrdinaryStableRouteAttempt MetrizableLCA.{0}) = false :=
  Dbounded.currentOrdinaryStableRouteAttempt_rejected MetrizableLCA.{0}

theorem originalFourTaskContract_currentSemanticRouteNonterminal :
    Dbounded.currentMetrizableSemanticStableRouteState.productSuccessClaimed = false :=
  Dbounded.currentMetrizableSemanticStableRouteState_productSuccess

end LeanLCAExactChallenge
