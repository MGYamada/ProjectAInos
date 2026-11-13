import ProjectAInos

open ProjectAInos ProjectAInos.QuantumFieldTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (F : ScalarField H)

example [CompleteSpace H] (f : Test) : (F.operator f).IsClosable :=
  F.operator_closable f

example (Ω : F.domain) (a b : List Test) (f : Test) :
    F.insertionDistribution Ω a b f = F.expectation Ω (a ++ f :: b) :=
  F.insertionDistribution_apply Ω a b f

example {ι : Type*} (Ω : F.domain) (s : Finset ι) (c : ι → ℂ) (w : ι → List Test) :
    0 ≤ (∑ i ∈ s, ∑ j ∈ s, star (c i) * c j *
      F.expectation Ω (ScalarField.adjointWord (w i) ++ w j)).re :=
  F.word_positivity Ω s c w

example (p : SpecialRelativity.Spacetime) : (pointEvaluation p).IsLocal :=
  pointEvaluation_local p
