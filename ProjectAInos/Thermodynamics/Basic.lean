module

public import Mathlib.Algebra.Module.Defs
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

/-- The stability axiom (A6) on the ordered semimodule of thermodynamic states.
If a sequence of positive scales tends to zero and the corresponding auxiliary
states allow every transition in the sequence, then the transition holds
without the auxiliary states. -/
def Stability (M : Type*) [AddCommMonoid M] [PartialOrder M] [Module ℝ≥0 M] : Prop :=
  ∀ (x y z₀ z₁ : M) (ε : ℕ → ℝ≥0),
    (∀ n, 0 < ε n) → Tendsto ε atTop (𝓝 0) →
      (∀ n, x + ε n • z₀ ≤ y + ε n • z₁) → x ≤ y

end ProjectAInos.Thermodynamics
