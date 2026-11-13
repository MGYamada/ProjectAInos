/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormDerivative

/-! # Covariant differentiation commutes with metric raising

Metric compatibility determines the derivative of a raised covector.
The formulas use locally differentiable sections of the actual bundles.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The derivative of `sharp α` is the raised covector derivative. -/
theorem leviCivita_sharp_pairing {α : ∀ x : M, TM x →L[ℝ] ℝ} {V : ∀ x, TM x} {x : M}
    (hα : MDifferentiableAt I ((I).prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (α y)) x)
    (hV : MDifferentiableAt I ((I).prod I) (T% V) x) (u : TM x) :
    g.form x (g.leviCivita (fun y => g.sharp y (α y)) x u) (V x) =
      mvfderiv I (fun y => α y (V y)) x u - α x (g.leviCivita V x u) := by
  have hs := (g.sharp_smooth.mdifferentiableAt (by simp)).clm_bundle_apply hα
  have h := g.leviCivita_metricCompatible u hs hV
  simp only [ContinuousLinearEquiv.coe_coe, g.form_sharp_left] at h
  linarith

/-- Inverse-metric pairing differentiates by the covariant product rule. -/
theorem inversePairing_derivative {α β : ∀ x : M, TM x →L[ℝ] ℝ} {x : M}
    (hα : MDifferentiableAt I ((I).prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (α y)) x)
    (hβ : MDifferentiableAt I ((I).prod 𝓘(ℝ, E →L[ℝ] ℝ))
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (β y)) x) (u : TM x) :
    mvfderiv I (fun y => α y (g.sharp y (β y))) x u =
      β x (g.leviCivita (fun y => g.sharp y (α y)) x u) +
        α x (g.leviCivita (fun y => g.sharp y (β y)) x u) := by
  have h := g.leviCivita_metricCompatible u
    ((g.sharp_smooth.mdifferentiableAt (by simp)).clm_bundle_apply hα)
    ((g.sharp_smooth.mdifferentiableAt (by simp)).clm_bundle_apply hβ)
  simpa only [ContinuousLinearEquiv.coe_coe, g.form_sharp_left, g.form_sharp_right] using h

/-- Raising the covector output of a two-form commutes with differentiation.
The remaining correction is exactly the derivative of its input vector. -/
theorem leviCivita_twoForm_raise (F : SmoothForm I M 2) {X Y : ∀ x, TM x} {x : M}
    (hX : MDifferentiableAt I ((I).prod I) (T% X) x)
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) x) (u : TM x) :
    g.form x (g.leviCivita (fun y => g.sharp y (twoFormBilinear (F y) (X y))) x u) (Y x) =
      g.twoFormDerivative F x (X x) (Y x) u + F x ![g.leviCivita X x u, Y x] := by
  have hα := ((smoothTwoFormBilinear F).contMDiff x).mdifferentiableAt (by simp)
  have h := g.leviCivita_sharp_pairing (hα.clm_bundle_apply hX) hY u
  simp only [smoothTwoFormBilinear_apply] at h
  change g.form x (g.leviCivita
    (fun y => g.sharp y (twoFormBilinear (F y) (X y))) x u) (Y x) = _ at h
  rw [h, g.twoFormDerivative_apply F hX hY u]
  ring

end ProjectAInos.SmoothGeometry.LorentzMetric
