module

public import ProjectAInos.Thermodynamics.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Shared conclusions of physical entropy theorems

These predicates name the common conclusions of the calibrated and reacting
entropy endpoints. Additivity is carried by the bundled entropy maps; the
fields record extensivity, the criterion within a composition label, and the
additional conclusions for reactions. They impose no new physical premises.
-/

@[expose] public section

open scoped NNReal

namespace ProjectAInos.Thermodynamics

variable {X Γ : Type*} [AddCommMonoid X] [DistribMulAction ℝ≥0 X] [AddCommMonoid Γ]

/-- An additive entropy is extensive and characterizes accessibility within
each composition label. Monotonicity between different labels is not required. -/
structure CalibratedEntropyPrinciple (label : X →+ Γ) (accessible : X → X → Prop)
    (entropy : X →+ ℝ) : Prop where
  extensive : ∀ (r : ℝ≥0) x, entropy (r • x) = (r : ℝ) * entropy x
  criterion : ∀ x y, label x = label y → (accessible x y ↔ entropy x ≤ entropy y)

/-- A calibrated entropy corrected by extensive composition constants is
monotone for every accessible process. Both functions retain the same
equal-label criterion, expressed by `CalibratedEntropyPrinciple`. -/
structure WeakEntropyPrinciple [Module ℝ≥0 Γ]
    (label : X →+ Γ) (accessible : X → X → Prop)
    (entropy totalEntropy : X →+ ℝ) (B : Γ →ₗ[ℝ≥0] ℝ) : Prop where
  decomposition : ∀ x, totalEntropy x = entropy x + B (label x)
  calibrated : CalibratedEntropyPrinciple label accessible entropy
  total : CalibratedEntropyPrinciple label accessible totalEntropy
  monotone : ∀ x y, accessible x y → totalEntropy x ≤ totalEntropy y

end ProjectAInos.Thermodynamics
