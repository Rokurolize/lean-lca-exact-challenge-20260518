/-
Copyright (c) 2026 Rokurolize. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rokurolize
-/

import LeanLCAExactChallenge.Infinity.EndpointMappingSpaceEdges
import LeanLCAExactChallenge.Infinity.EndpointMappingSpaceInnerHorns
import LeanLCAExactChallenge.Infinity.QuasicategoryAllEdgesKan

/-! # Kan structure on fixed-endpoint mapping spaces -/

set_option autoImplicit false

noncomputable section

universe u

namespace LeanLCAExactChallenge
namespace Infinity

open CategoryTheory Opposite Simplicial

/-- Every fixed-endpoint mapping space of a quasicategory is a Kan complex. -/
theorem endpointFiber_kan
    (Q : SSet.{u}) [SSet.Quasicategory Q] (x y : Q _⦋0⦌) :
    SSet.KanComplex (endpointFiber Q x y) := by
  letI : SSet.Quasicategory (endpointFiber Q x y) :=
    { hornFilling' := by
        intro n k a h0 hn
        obtain ⟨b, hb⟩ := endpointFiber_innerHorn_filling Q inferInstance x y
          (n + 1) k h0 hn a
        exact ⟨b, hb.symm⟩ }
  exact quasicategory_all_edges_equivalences_kan _
    (endpointFiber_edges_are_equivalences Q x y)

/-- The uniform contract asserting that all fixed-endpoint mapping spaces are Kan. -/
theorem endpointFibersAreKan : EndpointFibersAreKanContract.{u} := by
  intro Q x y
  letI : SSet.Quasicategory Q.obj := Q.property
  exact endpointFiber_kan Q.obj x y

end Infinity
end LeanLCAExactChallenge
