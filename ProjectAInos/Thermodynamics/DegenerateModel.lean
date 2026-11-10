module

public import ProjectAInos.Thermodynamics.Cone
public import ProjectAInos.Thermodynamics.Models

/-!
# A stable model without irreversible processes

Real state coordinates with the equality order give a nontrivial state space
whose process cone and process span both vanish.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

/-- A real state coordinate with accessibility given by equality. -/
def EqualityState := ℝ

namespace EqualityState

instance : AddCommGroup EqualityState := inferInstanceAs (AddCommGroup ℝ)
instance : Module ℝ EqualityState := inferInstanceAs (Module ℝ ℝ)

instance : PartialOrder EqualityState where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

instance : IsOrderedAddMonoid EqualityState where
  add_le_add_left _ _ h _ := congrArg (· + _) h

instance : PosSMulMono ℝ≥0 EqualityState where
  smul_le_smul_of_nonneg_left {a} _ {x y} h :=
    congrArg (fun z : EqualityState => a • z) (show x = y from h)

/-- Equality is stable under vanishing real perturbations. -/
theorem stability : Stability EqualityState := by
  intro x y z₀ z₁ ε _ hε h
  have lim (a b : ℝ) : Tendsto (fun n => a + (ε n : ℝ) * b) atTop (𝓝 a) := by
    simpa using tendsto_const_nhds.add ((NNReal.tendsto_coe.mpr hε).mul_const b)
  have heq (n : ℕ) :
      (show ℝ from x) + (ε n : ℝ) * (show ℝ from z₀) =
        (show ℝ from y) + (ε n : ℝ) * (show ℝ from z₁) := h n
  change x = y
  apply le_antisymm (α := ℝ)
  · exact le_of_tendsto_of_tendsto' (lim x z₀) (lim y z₁) (fun n => (heq n).le)
  · exact le_of_tendsto_of_tendsto' (lim y z₁) (lim x z₀) (fun n => (heq n).ge)

/-- Exchange comparison holds because accessible pairs are identical. -/
theorem exchangeComparison : ExchangeComparison EqualityState := by
  intro x y u v hxy huv
  change x = y at hxy
  change u = v at huv
  exact Or.inl (by rw [hxy, huv])

/-- Every accessible formal difference is zero. -/
theorem processCone_eq_bot : processCone EqualityState = ⊥ := by
  apply le_antisymm
  · rintro v ⟨x, y, h, rfl⟩
    change x = y at h
    simp [h]
  · exact bot_le

/-- A nontrivial state space can have no entropy direction. -/
theorem processSpan_eq_bot : processSpan EqualityState = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    simpa [processCone_eq_bot] using hx
  · exact bot_le

end EqualityState

end ProjectAInos.Thermodynamics
