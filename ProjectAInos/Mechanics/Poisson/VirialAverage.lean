/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.Trajectory
public import ProjectAInos.Mechanics.Poisson.Virial
public import ProjectAInos.Mechanics.TimePrimitive
public import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-!
# The virial theorem for time averages

The time average over `[0, τ]` of the derivative of a bounded function of time
tends to zero as `τ → ∞`, because the integral of the derivative is the
increment of the function.

Along a trajectory of `H = Σᵢ pᵢ²/2mᵢ + U` with `U` homogeneous of degree `k`
in the positions, `d/dt Σᵢ qᵢ pᵢ = 2T − kU`. If the motion is bounded, in the
sense that `Σᵢ qᵢ pᵢ` is bounded, the time average of `2T − kU` tends to zero
(Landau–Lifshitz (10.5)–(10.7)): `2 ⟨T⟩ = k ⟨U⟩`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Filter
open scoped Topology

/-- The time average over `[0, τ]` of the derivative of a bounded function of
time tends to zero as `τ → ∞`. -/
theorem TimeFunction.tendsto_average_timeDerivative {G : TimeFunction} {B : ℝ}
    (hB : ∀ t : ℝ, |G fun _ => t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ, timeDerivative G fun _ => t) atTop
      (𝓝 0) := by
  have hlim : Tendsto (fun τ : ℝ => (2 * B) / τ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  rw [← TimeFunction.apply_sub_apply_eq_integral, Real.norm_eq_abs, abs_mul,
    abs_of_pos (one_div_pos.mpr hτ), one_div, inv_mul_eq_div]
  have h1 : |G (fun _ => τ) - G fun _ => 0| ≤ 2 * B := by
    have := abs_sub (G fun _ => τ) (G fun _ => 0)
    linarith [hB τ, hB 0]
  exact div_le_div_of_nonneg_right h1 hτ.le

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The virial theorem (Landau–Lifshitz §10): along a trajectory of
`H = Σᵢ pᵢ²/2mᵢ + U` on which `Σᵢ qᵢ pᵢ` is bounded, with `U` a function of the
positions that satisfies Euler's relation of degree `k`, the time average of
`2T − kU` tends to zero. -/
theorem IsTrajectory.tendsto_average_virial (m : ι → ℝ) {U : PhaseSpace ι} {k : ℝ}
    (hU : ∑ i, q i * partialDerivation (Sum.inl i) U = algebraMap ℝ (PhaseSpace ι) k * U)
    (hUp : ∀ i, partialDerivation (Sum.inr i) U = 0) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (kineticEnergy m + U) c) {B : ℝ}
    (hB : ∀ t : ℝ, |FreeSmoothRing.lift c dilation fun _ => t| ≤ B) :
    Tendsto (fun τ : ℝ => (1 / τ) * ∫ t in (0 : ℝ)..τ,
      FreeSmoothRing.lift c (2 * kineticEnergy m - algebraMap ℝ (PhaseSpace ι) k * U)
        fun _ => t) atTop (𝓝 0) := by
  have hD : timeDerivative (FreeSmoothRing.lift c dilation) =
      FreeSmoothRing.lift c (2 * kineticEnergy m - algebraMap ℝ (PhaseSpace ι) k * U) := by
    rw [h.timeDerivative_lift, virial m hU hUp]
  rw [← hD]
  exact TimeFunction.tendsto_average_timeDerivative hB

end ProjectAInos.Mechanics
