/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.VariationDensity
public import ProjectAInos.Variational.IntervalParameter

/-! # Actual action derivatives for manifold curve families

Only local joint C² regularity along the finite reference segment is
required. Compactness justifies differentiation under the integral even
when the curve crosses chart boundaries.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace ProjectAInos.GeneralRelativity

open SmoothGeometry LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "J" => 𝓘(ℝ, ℝ × ℝ)

/-- Differentiate the actual quadratic action of a genuine manifold family.
There are no causal, endpoint-variation or single-chart restrictions. -/
theorem quadraticAction_family_hasDerivAt (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t)) :
    HasDerivAt (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b)
      (∫ t in a..b, g.form (Γ (ε₀, t))
        (g.covariantAlong (γ := fun s => Γ (ε₀, s))
          (fun s => familyVelocity Γ (1, 0) (ε₀, s)) t)
        (curveVelocity (fun s => Γ (ε₀, s)) t)) ε₀ :=
  Variational.hasDerivAt_intervalIntegral_of_contDiffAt
    (fun t ht => contDiffAt_const.mul (familyMetricVelocity_contDiffAt g (hΓ t ht)))
    (fun t ht => quadraticDensity_hasDerivAt g (hΓ t ht))

/-- The actual massive action can be differentiated from timelikeness only
on the reference segment; compactness supplies a common admissible neighborhood. -/
theorem freeAction_family_hasDerivAt (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t)) :
    HasDerivAt (fun ε => freeAction g m (fun t => Γ (ε, t)) a b)
      (∫ t in a..b, (m / speedAlong g (fun s => Γ (ε₀, s)) t) * g.form (Γ (ε₀, t))
        (g.covariantAlong (γ := fun s => Γ (ε₀, s))
          (fun s => familyVelocity Γ (1, 0) (ε₀, s)) t)
        (curveVelocity (fun s => Γ (ε₀, s)) t)) ε₀ := by
  simpa only [freeAction, properTime, intervalIntegral.integral_const_mul] using
    Variational.hasDerivAt_intervalIntegral_of_contDiffAt
      (fun t ht => freeFamilyDensity_contDiffAt g m (hΓ t ht) (hv t ht))
      (fun t ht => freeDensity_hasDerivAt g m (hΓ t ht) (hv t ht))

/-- First variations glue over a subdivision, including when the reference
curve changes coordinate charts at the junction. -/
theorem quadraticAction_family_deriv_add (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hΓ : ∀ t ∈ uIcc a c, ContMDiffAt J I 2 Γ (ε₀, t)) :
    deriv (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b) ε₀ +
      deriv (fun ε => quadraticAction g (fun t => Γ (ε, t)) b c) ε₀ =
      deriv (fun ε => quadraticAction g (fun t => Γ (ε, t)) a c) ε₀ := by
  have hsub₁ : uIcc a b ⊆ uIcc a c := by
    rw [uIcc_of_le hab, uIcc_of_le (hab.trans hbc)]
    exact Icc_subset_Icc le_rfl hbc
  have hsub₂ : uIcc b c ⊆ uIcc a c := by
    rw [uIcc_of_le hbc, uIcc_of_le (hab.trans hbc)]
    exact Icc_subset_Icc hab le_rfl
  have hc := Variational.continuousOn_parameter_derivative
    (fun t ht => contDiffAt_const.mul (familyMetricVelocity_contDiffAt g (hΓ t ht)))
    (fun t ht => quadraticDensity_hasDerivAt g (hΓ t ht))
  rw [(quadraticAction_family_hasDerivAt g (fun t ht => hΓ t (hsub₁ ht))).deriv,
    (quadraticAction_family_hasDerivAt g (fun t ht => hΓ t (hsub₂ ht))).deriv,
    (quadraticAction_family_hasDerivAt g hΓ).deriv]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hc.mono hsub₁).intervalIntegrable (hc.mono hsub₂).intervalIntegrable

/-- The massive first variation also glues over finite subdivisions without
assuming that all segments use the same coordinate chart. -/
theorem freeAction_family_deriv_add (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hΓ : ∀ t ∈ uIcc a c, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a c, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t)) :
    deriv (fun ε => freeAction g m (fun t => Γ (ε, t)) a b) ε₀ +
      deriv (fun ε => freeAction g m (fun t => Γ (ε, t)) b c) ε₀ =
      deriv (fun ε => freeAction g m (fun t => Γ (ε, t)) a c) ε₀ := by
  have hsub₁ : uIcc a b ⊆ uIcc a c := by
    rw [uIcc_of_le hab, uIcc_of_le (hab.trans hbc)]
    exact Icc_subset_Icc le_rfl hbc
  have hsub₂ : uIcc b c ⊆ uIcc a c := by
    rw [uIcc_of_le hbc, uIcc_of_le (hab.trans hbc)]
    exact Icc_subset_Icc hab le_rfl
  have hc := Variational.continuousOn_parameter_derivative
    (fun t ht => freeFamilyDensity_contDiffAt g m (hΓ t ht) (hv t ht))
    (fun t ht => freeDensity_hasDerivAt g m (hΓ t ht) (hv t ht))
  rw [(freeAction_family_hasDerivAt g m (fun t ht => hΓ t (hsub₁ ht))
      (fun t ht => hv t (hsub₁ ht))).deriv,
    (freeAction_family_hasDerivAt g m (fun t ht => hΓ t (hsub₂ ht))
      (fun t ht => hv t (hsub₂ ht))).deriv,
    (freeAction_family_hasDerivAt g m hΓ hv).deriv]
  exact intervalIntegral.integral_add_adjacent_intervals
    (hc.mono hsub₁).intervalIntegrable (hc.mono hsub₂).intervalIntegrable

end ProjectAInos.GeneralRelativity
