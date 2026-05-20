import LeanLCAExactChallenge.LCA.Cokernel

/-!
Audit check for the concrete `MetrizableLCA` cokernel and finite-colimit implementation.

Unlike W235, this file checks the product module that constructs cokernels by quotienting by
the closed algebraic range closure.
-/

set_option autoImplicit false

namespace LeanLCAExactChallenge

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace MetrizableLCACokernelProductW252

theorem hasCokernels : HasCokernels MetrizableLCA.{u} := inferInstance

theorem hasFiniteColimits : HasFiniteColimits MetrizableLCA.{u} := inferInstance

def implementedDeclarations : List String :=
  ["MetrizableLCA.cokernelSubgroup",
    "MetrizableLCA.cokernelObj",
    "MetrizableLCA.cokernelπ",
    "MetrizableLCA.cokernelIsColimit",
    "MetrizableLCA.instHasCokernels",
    "MetrizableLCA.instHasFiniteColimits"]

theorem implementedDeclarations_count :
    implementedDeclarations.length = 6 := rfl

section Checks

#check MetrizableLCA.cokernelSubgroup
#check MetrizableLCA.range_le_cokernelSubgroup
#check MetrizableLCA.map_mem_cokernelSubgroup
#check MetrizableLCA.cokernelObj
#check MetrizableLCA.cokernelπ
#check MetrizableLCA.comp_cokernelπ
#check MetrizableLCA.cokernel_desc_ker_le
#check MetrizableLCA.cokernelDesc
#check MetrizableLCA.cokernelπ_desc
#check MetrizableLCA.cokernelDesc_unique
#check MetrizableLCA.cokernelIsColimit
#check MetrizableLCA.instHasCokernel
#check MetrizableLCA.instHasCokernels
#check MetrizableLCA.instHasFiniteColimits
#check hasCokernels
#check hasFiniteColimits
#check implementedDeclarations
#check implementedDeclarations_count

end Checks

end MetrizableLCACokernelProductW252

end LeanLCAExactChallenge
