module

public import ProjectAInos.Thermodynamics.Calibration
public import ProjectAInos.Thermodynamics.ThermalFamily

/-!
# Calibrators from nonunique thermal splitting

Two equilibrium splits of one joined state are adiabatically equivalent.
If their first components form a strict pair, cancellation forces the second
components to form the oppositely ordered strict pair. In particular, distinct
splits give a calibrator when fixed-work energy order is strict. This proves
the nonunique-splitting branch of the calibrator argument, without assuming
that such splits always exist.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics.Physical

variable {X : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X]

/-- Two strict reference pairs whose crossed products are adiabatically equivalent. -/
def IsEntropyCalibrator (P : Accessibility X) (x₀ x₁ y₀ y₁ : X) : Prop :=
  (P.relation x₀ x₁ ∧ ¬ P.relation x₁ x₀) ∧
    (P.relation y₀ y₁ ∧ ¬ P.relation y₁ y₀) ∧
      (P.relation (x₀ + y₁) (x₁ + y₀) ∧ P.relation (x₁ + y₀) (x₀ + y₁))

namespace ThermalJoin

variable {P : Accessibility X} {W₁ W₂ : Type*}
variable {Γ₁ : Set (ℝ × W₁)} {Γ₂ : Set (ℝ × W₂)}
variable {represent₁ : Γ₁ → X} {represent₂ : Γ₂ → X}
variable (J : ThermalJoin P Γ₁ Γ₂ represent₁ represent₂)

/-- Equilibrium splits of the same joined coordinates are adiabatically equivalent. -/
theorem equivalent_equilibrium_splits (x₀ x₁ : Γ₁) (y₀ y₁ : Γ₂)
    (hjoin : joinedState x₀ y₀ = joinedState x₁ y₁)
    (h₀ : J.Equilibrium x₀ y₀) (h₁ : J.Equilibrium x₁ y₁) :
    P.relation (represent₁ x₀ + represent₂ y₀) (represent₁ x₁ + represent₂ y₁) ∧
      P.relation (represent₁ x₁ + represent₂ y₁) (represent₁ x₀ + represent₂ y₀) := by
  constructor
  · apply P.trans (J.contact x₀ y₀)
    simpa only [Equilibrium, hjoin] using h₁
  · apply P.trans (J.contact x₁ y₁)
    simpa only [Equilibrium, ← hjoin] using h₀

/-- A strict change in the first component forces the reverse strict change in
the second component, producing the crossed entropy calibrator. -/
theorem calibrator_of_strict_equilibrium_splits (x₀ x₁ : Γ₁) (y₀ y₁ : Γ₂)
    (hjoin : joinedState x₀ y₀ = joinedState x₁ y₁)
    (h₀ : J.Equilibrium x₀ y₀) (h₁ : J.Equilibrium x₁ y₁)
    (hstrict : P.relation (represent₁ x₀) (represent₁ x₁) ∧
      ¬ P.relation (represent₁ x₁) (represent₁ x₀)) :
    IsEntropyCalibrator P (represent₁ x₀) (represent₁ x₁) (represent₂ y₁) (represent₂ y₀) := by
  have hcross := J.equivalent_equilibrium_splits x₀ x₁ y₀ y₁ hjoin h₀ h₁
  exact ⟨hstrict, P.strict_reference_of_crossed hstrict hcross, hcross⟩

/-- Nonunique equilibrium splitting yields calibrators under the positive
fixed-work energy-order theorem. That order theorem is an explicit geometric
input here; no comparison of arbitrary product states is assumed. -/
theorem exists_calibrator_of_distinct_equilibrium_splits
    (henergy : ∀ a b : Γ₁, a.val.2 = b.val.2 → a.val.1 < b.val.1 →
      P.relation (represent₁ a) (represent₁ b) ∧ ¬ P.relation (represent₁ b) (represent₁ a))
    (x₀ x₁ : Γ₁) (y₀ y₁ : Γ₂) (hne : x₀ ≠ x₁)
    (hjoin : joinedState x₀ y₀ = joinedState x₁ y₁)
    (h₀ : J.Equilibrium x₀ y₀) (h₁ : J.Equilibrium x₁ y₁) :
    ∃ a b : Γ₁, ∃ c d : Γ₂,
      IsEntropyCalibrator P (represent₁ a) (represent₁ b) (represent₂ c) (represent₂ d) := by
  have hwork : x₀.val.2 = x₁.val.2 :=
    congrArg (fun z : joinedDomain Γ₁ Γ₂ => z.val.2.1) hjoin
  have hune : x₀.val.1 ≠ x₁.val.1 := by
    intro h
    exact hne (Subtype.ext (Prod.ext h hwork))
  rcases lt_or_gt_of_ne hune with h | h
  · exact ⟨x₀, x₁, y₁, y₀,
      J.calibrator_of_strict_equilibrium_splits x₀ x₁ y₀ y₁ hjoin h₀ h₁ (henergy _ _ hwork h)⟩
  · exact ⟨x₁, x₀, y₀, y₁,
      J.calibrator_of_strict_equilibrium_splits x₁ x₀ y₁ y₀ hjoin.symm h₁ h₀ (henergy _ _ hwork.symm h)⟩

end ThermalJoin

end ProjectAInos.Thermodynamics.Physical
