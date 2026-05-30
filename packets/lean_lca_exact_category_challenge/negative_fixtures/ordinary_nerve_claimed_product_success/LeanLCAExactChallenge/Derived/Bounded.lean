namespace LeanLCAExactChallenge

variable (C : Type)

abbrev BoundedDerivedCategory : Type := C

noncomputable abbrev BoundedDerivedInfinityCategory : SSet.QCat :=
  ⟨CategoryTheory.nerve (BoundedDerivedCategory C), inferInstance⟩

end LeanLCAExactChallenge
