namespace LeanLCAExactChallenge

structure BoundedDerivedInfinityCategory where
  finiteLimits : Prop
  finiteColimits : Prop
  suspensionLoopEquivalence : Prop
  pushoutPullbackCompatibility : Prop
  finiteLimits_ready : finiteLimits
  finiteColimits_ready : finiteColimits
  suspensionLoopEquivalence_ready : suspensionLoopEquivalence
  pushoutPullbackCompatibility_ready : pushoutPullbackCompatibility

end LeanLCAExactChallenge
