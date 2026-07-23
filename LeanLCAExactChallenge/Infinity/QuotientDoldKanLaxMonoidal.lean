/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.QuotientAlexanderWhitneyAssociativity

/-!
# Lax monoidal Dold--Kan inverse for the corrected quotient

The normalized Alexander--Whitney oplax structure transfers across the Dold--Kan adjunction
to a lax monoidal structure on the inverse functor over the corrected quotient coefficient
ring.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge
namespace Infinity
namespace MetrizableBoundedComplexes
namespace DrinfeldWord
namespace QuotientDoldKanMonoidal

open CategoryTheory
open CategoryTheory.MonoidalCategory

/-- The lax monoidal structure on the quotient-coefficient Dold--Kan inverse induced by the
verified normalized Alexander--Whitney oplax structure. -/
@[implicit_reducible]
def quotientInverseLaxMonoidal :
    quotientModuleDoldKanEquivalence.inverse.LaxMonoidal :=
  inverseLaxMonoidalOfNormalizedOplax normalizedMooreOplaxMonoidal

/-- The quotient Dold--Kan inverse tensorator obtained from normalized Alexander--Whitney. -/
def quotientInverseTensorator (K L : QuotientChain) :
    quotientModuleDoldKanEquivalence.inverse.obj K ⊗
        quotientModuleDoldKanEquivalence.inverse.obj L ⟶
      quotientModuleDoldKanEquivalence.inverse.obj (K ⊗ L) :=
  inverseTensorator normalizedMooreOplaxMonoidal K L

end QuotientDoldKanMonoidal
end DrinfeldWord
end MetrizableBoundedComplexes
end Infinity
end LeanLCAExactChallenge
