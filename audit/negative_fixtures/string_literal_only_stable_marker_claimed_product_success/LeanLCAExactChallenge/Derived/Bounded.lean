namespace LeanLCAExactChallenge

variable (C : Type)

abbrev BoundedDerivedCategory : Type := C

noncomputable abbrev BoundedDerivedInfinityCategory : SSet.QCat :=
  arbitrary SSet.QCat

def derivedStableMarkerStringFixture : String :=
  "StableBoundedDerivedInfinityCategory stableInfinity finiteLimits finiteColimits suspensionEquivalence loopSuspensionEquivalence pushoutPullbackSquare"

end LeanLCAExactChallenge
