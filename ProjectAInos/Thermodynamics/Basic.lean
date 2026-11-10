module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.UniformSpace.Real

/-!
# Thermodynamic stability

The algebraic development starts with the partially ordered semimodule of
states modulo adiabatic equivalence. Here, `x ≤ y` represents adiabatic
accessibility from `x` to `y`.
-/

@[expose] public section

open Filter
open scoped NNReal Topology

namespace ProjectAInos.Thermodynamics

/-- A fixed positive scale tending to zero, used in the stability arguments. -/
noncomputable abbrev reciprocalNatSucc (n : ℕ) : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)

theorem reciprocalNatSucc_pos (n : ℕ) : 0 < reciprocalNatSucc n := by
  positivity

theorem tendsto_reciprocalNatSucc : Tendsto reciprocalNatSucc atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The stability axiom (A6) on the ordered semimodule of thermodynamic states.
If a sequence of positive scales tends to zero and the corresponding auxiliary
states allow every transition in the sequence, then the transition holds
without the auxiliary states. -/
def Stability (M : Type*) [AddCommMonoid M] [PartialOrder M] [Module ℝ≥0 M] : Prop :=
  ∀ (x y z₀ z₁ : M) (ε : ℕ → ℝ≥0),
    (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      (∀ n, x + ε n • z₀ ≤ y + ε n • z₁) → x ≤ y

/-- Apply stability along the fixed scales `1 / (n + 1)`. -/
theorem Stability.of_reciprocalNatSucc {M : Type*} [AddCommMonoid M]
    [PartialOrder M] [Module ℝ≥0 M] (hS : Stability M) (x y z₀ z₁ : M)
    (h : ∀ n, x + reciprocalNatSucc n • z₀ ≤ y + reciprocalNatSucc n • z₁) :
    x ≤ y :=
  hS x y z₀ z₁ reciprocalNatSucc reciprocalNatSucc_pos tendsto_reciprocalNatSucc h

end ProjectAInos.Thermodynamics
