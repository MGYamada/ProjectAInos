/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.VariationAction
public import ProjectAInos.GeneralRelativity.ProperTimeParameter

/-! # Boundary terms in native manifold action variations

Metric compatibility gives integration by parts intrinsically. There is no
choice of chart in the endpoint pairings or in the acceleration residual.
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

/-- The quadratic endpoint pairing is C¹ without a global coordinate chart. -/
theorem familyBoundary_contDiffAt (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ t : ℝ} (hΓ : ContMDiffAt J I 2 Γ (ε₀, t)) :
    ContDiffAt ℝ 1 (fun s => g.form (Γ (ε₀, s))
      (familyVelocity Γ (1, 0) (ε₀, s)) (curveVelocity (fun u => Γ (ε₀, u)) s)) t :=
  g.contDiffAt_pairing_along ((familySlice_contMDiffAt hΓ).of_le (by norm_num))
    (familyVariation_contMDiffAt hΓ) (curveVelocity_contMDiffAt (familySlice_contMDiffAt hΓ))

/-- Derivative of the native endpoint pairing. -/
theorem familyBoundary_hasDerivAt (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ t : ℝ} (hΓ : ContMDiffAt J I 2 Γ (ε₀, t)) :
    HasDerivAt (fun s => g.form (Γ (ε₀, s))
      (familyVelocity Γ (1, 0) (ε₀, s)) (curveVelocity (fun u => Γ (ε₀, u)) s))
      (g.form (Γ (ε₀, t))
        (g.covariantAlong (γ := fun s => Γ (ε₀, s))
          (fun s => familyVelocity Γ (1, 0) (ε₀, s)) t)
        (curveVelocity (fun s => Γ (ε₀, s)) t) +
      g.form (Γ (ε₀, t)) (familyVelocity Γ (1, 0) (ε₀, t))
        (g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t)) t :=
  g.hasDerivAt_pairing_along ((familySlice_contMDiffAt hΓ).mdifferentiableAt (by norm_num))
    ((familyVariation_contMDiffAt hΓ).mdifferentiableAt (by norm_num))
    ((curveVelocity_contMDiffAt (n := 1) (familySlice_contMDiffAt hΓ)).mdifferentiableAt
      (by norm_num))

/-- Full first variation of the quadratic action on an arbitrary Lorentz
manifold, retaining the endpoint pairing for non-fixed endpoints. -/
theorem quadraticAction_family_firstVariation (g : LorentzMetric .timeNegative d M)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t)) :
    HasDerivAt (fun ε => quadraticAction g (fun t => Γ (ε, t)) a b)
      ((g.form (Γ (ε₀, b)) (familyVelocity Γ (1, 0) (ε₀, b))
          (curveVelocity (fun s => Γ (ε₀, s)) b) -
        g.form (Γ (ε₀, a)) (familyVelocity Γ (1, 0) (ε₀, a))
          (curveVelocity (fun s => Γ (ε₀, s)) a)) +
        ∫ t in a..b, -g.form (Γ (ε₀, t)) (familyVelocity Γ (1, 0) (ε₀, t))
          (g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t)) ε₀ := by
  have hc := Variational.continuousOn_parameter_derivative
    (fun t ht => contDiffAt_const.mul (familyMetricVelocity_contDiffAt g (hΓ t ht)))
    (fun t ht => quadraticDensity_hasDerivAt g (hΓ t ht))
  apply (quadraticAction_family_hasDerivAt g hΓ).congr_deriv
  apply Variational.integral_eq_boundary_add_residual
    (fun t ht => familyBoundary_contDiffAt g (hΓ t ht)) hc
  intro t ht
  simpa only [sub_neg_eq_add] using familyBoundary_hasDerivAt g (hΓ t ht)

/-- The massive first variation retains its endpoint momentum pairing and
the proper-speed derivative in the non-affine acceleration residual. -/
theorem freeAction_family_firstVariation (g : LorentzMetric .timeNegative d M) (m : ℝ)
    {Γ : ℝ × ℝ → M} {ε₀ a b : ℝ}
    (hΓ : ∀ t ∈ uIcc a b, ContMDiffAt J I 2 Γ (ε₀, t))
    (hv : ∀ t ∈ uIcc a b, Timelike g (curveVelocity (fun s => Γ (ε₀, s)) t)) :
    HasDerivAt (fun ε => freeAction g m (fun t => Γ (ε, t)) a b)
      (((m / speedAlong g (fun s => Γ (ε₀, s)) b) *
          g.form (Γ (ε₀, b)) (familyVelocity Γ (1, 0) (ε₀, b))
            (curveVelocity (fun s => Γ (ε₀, s)) b) -
        (m / speedAlong g (fun s => Γ (ε₀, s)) a) *
          g.form (Γ (ε₀, a)) (familyVelocity Γ (1, 0) (ε₀, a))
            (curveVelocity (fun s => Γ (ε₀, s)) a)) +
        ∫ t in a..b, -(m / speedAlong g (fun s => Γ (ε₀, s)) t) *
          g.form (Γ (ε₀, t)) (familyVelocity Γ (1, 0) (ε₀, t))
            (g.covariantAlong (curveVelocity (fun s => Γ (ε₀, s))) t -
              (deriv (speedAlong g (fun s => Γ (ε₀, s))) t /
                speedAlong g (fun s => Γ (ε₀, s)) t) •
                curveVelocity (fun s => Γ (ε₀, s)) t)) ε₀ := by
  have hc := Variational.continuousOn_parameter_derivative
    (fun t ht => freeFamilyDensity_contDiffAt g m (hΓ t ht) (hv t ht))
    (fun t ht => freeDensity_hasDerivAt g m (hΓ t ht) (hv t ht))
  have hs : ∀ t ∈ uIcc a b, speedAlong g (fun s => Γ (ε₀, s)) t ≠ 0 :=
    fun t ht => ne_of_gt ((properSpeed_pos_iff g _).mpr (hv t ht))
  have hspeed : ∀ t ∈ uIcc a b,
      ContDiffAt ℝ 1 (speedAlong g (fun s => Γ (ε₀, s))) t :=
    fun t ht => contDiffAt_speedAlong g (familySlice_contMDiffAt (hΓ t ht)) (hv t ht)
  apply (freeAction_family_hasDerivAt g m hΓ hv).congr_deriv
  apply Variational.integral_eq_boundary_add_residual
    (fun t ht => (contDiffAt_const.div (hspeed t ht) (hs t ht)).mul
      (familyBoundary_contDiffAt g (hΓ t ht))) hc
  intro t ht
  have hd := ((hasDerivAt_const t m).div
    ((hspeed t ht).differentiableAt (by norm_num)).hasDerivAt (hs t ht)).mul
      (familyBoundary_hasDerivAt g (hΓ t ht))
  apply hd.congr_deriv
  simp only [map_sub, map_smul, smul_eq_mul, Pi.div_apply]
  ring

end ProjectAInos.GeneralRelativity
