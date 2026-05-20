import LeanLCAExactChallenge.LCA.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
W384: iso transport for W381's ordinary-to-transported relation fields.

W381 reduces the remaining transported relation-field work to point
identifications, descended-map conjugacy, and transport of injectivity,
`IsInducing`, and closed range.  This file proves the reusable transport
lemmas once the point isomorphisms and conjugacy are available.
-/

set_option autoImplicit false

noncomputable section

namespace LeanLCAExactChallenge

open CategoryTheory
open Topology

namespace MetrizableLCA

/-- A categorical isomorphism in `MetrizableLCA` is a homeomorphism on carriers. -/
noncomputable def isoHomeomorph {A B : MetrizableLCA.{0}} (e : A ≅ B) : A ≃ₜ B where
  toFun := e.hom
  invFun := e.inv
  left_inv := by
    intro x
    have h := congrArg (fun m : A ⟶ A => (m : A → A) x) e.hom_inv_id
    simpa using h
  right_inv := by
    intro y
    have h := congrArg (fun m : B ⟶ B => (m : B → B) y) e.inv_hom_id
    simpa using h
  continuous_toFun := (Hom.hom e.hom).continuous
  continuous_invFun := (Hom.hom e.inv).continuous

/--
Injectivity transports across source/target isomorphisms when the transported
map is conjugate to the ordinary map.
-/
theorem injective_of_iso_conjugate {A A' B B' : MetrizableLCA.{0}}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (hconj : ∀ x : A', f' x = eB.hom (f (eA.inv x)))
    (hf : Function.Injective (f : A → B)) :
    Function.Injective (f' : A' → B') := by
  intro x y hxy
  have hb :
      (eB.hom : B → B') (f (eA.inv x)) =
        (eB.hom : B → B') (f (eA.inv y)) := by
    rw [← hconj x, ← hconj y]
    exact hxy
  have hfx : f (eA.inv x) = f (eA.inv y) :=
    (isoHomeomorph eB).injective hb
  have hxy' : eA.inv x = eA.inv y := hf hfx
  exact (isoHomeomorph eA).symm.injective hxy'

/--
The `IsInducing` field transports across source/target isomorphisms when the
transported map is conjugate to the ordinary map.
-/
theorem isInducing_of_iso_conjugate {A A' B B' : MetrizableLCA.{0}}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (hconj : ∀ x : A', f' x = eB.hom (f (eA.inv x)))
    (hf : IsInducing (f : A → B)) :
    IsInducing (f' : A' → B') := by
  have hfun :
      (f' : A' → B') =
        (isoHomeomorph eB) ∘ (f : A → B) ∘ (isoHomeomorph eA).symm := by
    funext x
    exact hconj x
  rw [hfun]
  exact (isoHomeomorph eB).isInducing.comp
    (hf.comp (isoHomeomorph eA).symm.isInducing)

/--
Closed range transports across source/target isomorphisms when the transported
map is conjugate to the ordinary map.
-/
theorem isClosed_range_of_iso_conjugate {A A' B B' : MetrizableLCA.{0}}
    (eA : A ≅ A') (eB : B ≅ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (hconj : ∀ x : A', f' x = eB.hom (f (eA.inv x)))
    (hf : IsClosed (Set.range (f : A → B))) :
    IsClosed (Set.range (f' : A' → B')) := by
  have hrange :
      Set.range (f' : A' → B') =
        (isoHomeomorph eB) '' Set.range (f : A → B) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨f (eA.inv x), ⟨eA.inv x, rfl⟩, ?_⟩
      exact (hconj x).symm
    · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
      refine ⟨eA.hom a, ?_⟩
      simpa using hconj (eA.hom a)
  rw [hrange]
  exact (isoHomeomorph eB).isClosed_image.mpr hf

/-- W384 declaration names for audit traceability. -/
def w384SupportDeclarationNames : List String :=
  ["MetrizableLCA.isoHomeomorph",
    "MetrizableLCA.injective_of_iso_conjugate",
    "MetrizableLCA.isInducing_of_iso_conjugate",
    "MetrizableLCA.isClosed_range_of_iso_conjugate"]

theorem w384SupportDeclarationNames_count :
    w384SupportDeclarationNames.length = 4 := rfl

/-- Machine-readable state for this checked W384 support file. -/
structure WppOpLeftLcaIsoFieldTransportV370StateW384 : Type where
  checkedFacts : List String
  remainingInputs : List String
  subgoalSuccessClaimed : Bool
  productSuccessClaimed : Bool

def currentWppOpLeftLcaIsoFieldTransportV370StateW384 :
    WppOpLeftLcaIsoFieldTransportV370StateW384 where
  checkedFacts :=
    ["categorical MetrizableLCA isomorphisms give carrier homeomorphisms",
      "injectivity transports across source and target point isomorphisms under conjugacy",
      "IsInducing transports across source and target point isomorphisms under conjugacy",
      "closed range transports across source and target point isomorphisms under conjugacy"]
  remainingInputs :=
    ["construct the source point isomorphism",
      "construct the target point isomorphism",
      "prove the transported descended map is conjugate to the ordinary descended quotient map"]
  subgoalSuccessClaimed := true
  productSuccessClaimed := false

theorem currentWppOpLeftLcaIsoFieldTransportV370StateW384_productSuccess :
    currentWppOpLeftLcaIsoFieldTransportV370StateW384.productSuccessClaimed = false := rfl

section Checks

#check isoHomeomorph
#check injective_of_iso_conjugate
#check isInducing_of_iso_conjugate
#check isClosed_range_of_iso_conjugate
#check w384SupportDeclarationNames_count
#check currentWppOpLeftLcaIsoFieldTransportV370StateW384_productSuccess

end Checks

end MetrizableLCA

end LeanLCAExactChallenge
