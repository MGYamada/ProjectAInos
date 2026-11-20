/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Potential.KernelFourier
import ProjectAinos.Electrodynamics.CoulombFourier

/-! Public consumers of the Fourier resolution of the electrostatic field (Landau–Lifshitz §51):
the Fourier pairing of the Newton kernel with the symbol `1/(4π²|ξ|²)` by Gaussian
subordination; the transform of the potential and of the field in pairing form and in `𝓢′`, and
the zero-frequency prescription against constants with the decaying solution.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section

section KernelFourier

open MeasureTheory Filter Set Metric Real

open scoped Topology FourierTransform SchwartzMap Complex ContDiff

namespace ProjectAinos.SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example (ξ : E3) :
    ℝ :=
  newtonSymbol ξ

example (ξ : E3) :
    0 ≤ newtonSymbol ξ :=
  newtonSymbol_nonneg ξ

example (x : E3) :
    newtonKernel x = (4 * π)⁻¹ * ‖x‖ ^ (-1 : ℝ) :=
  kernelFourier_newtonKernel_eq_rpow x

example (ξ : E3) :
    newtonSymbol ξ = (4 * π ^ 2)⁻¹ * ‖ξ‖ ^ (-2 : ℝ) :=
  kernelFourier_newtonSymbol_eq_rpow ξ

example {α : ℝ} (hα0 : 0 ≤ α) (hα : α < 3) {f : E3 → ℂ} (hf : Integrable f) (hfc : Continuous f) :
    Integrable fun x : E3 => ‖x‖ ^ (-α) * ‖f x‖ :=
  kernelFourier_integrable_rpow_mul hα0 hα hf hfc

example {f : E3 → ℂ} (hf : Integrable f) (hfc : Continuous f) :
    Integrable fun x => (newtonKernel x : ℂ) * f x :=
  kernelFourier_integrable_newtonKernel_mul hf hfc

example {f : E3 → ℂ} (hf : Integrable f) (hfc : Continuous f) :
    Integrable fun x => (newtonSymbol x : ℂ) * f x :=
  kernelFourier_integrable_newtonSymbol_mul hf hfc

example {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ (-(1 / 2) : ℝ) * rexp (-(r * t)) = √π * (√r)⁻¹ :=
  kernelFourier_integral_rpow_exp hr

example {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ) * rexp (-(r * t))) (Ioi 0) :=
  kernelFourier_integrableOn_rpow_exp hr

example {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t ^ (-2 : ℝ) * rexp (-(a * t⁻¹)) = a⁻¹ :=
  kernelFourier_integral_rpow_exp_inv ha

example {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (-2 : ℝ) * rexp (-(a * t⁻¹))) (Ioi 0) :=
  kernelFourier_integrableOn_rpow_exp_inv ha

example {f g : E3 → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ x, f x * 𝓕 g x = ∫ ξ, 𝓕 f ξ * g ξ :=
  kernelFourier_integral_mul_fourier hf hg

example {f : E3 → ℂ} (hf : Integrable f) (χ : 𝓢(E3, ℂ)) (y : E3) :
    ∫ x, f (x - y) * 𝓕 χ x = 𝓕 (fun ξ => 𝓕 f ξ * χ ξ) y :=
  kernelFourier_integral_comp_sub_mul_fourier hf χ y

example {t : ℝ} (ht : 0 < t) (χ : 𝓢(E3, ℂ)) :
    ∫ z, rexp (-(‖z‖ ^ 2 * t)) • 𝓕 χ z =
      ∫ ξ, ((π / t) ^ (3 / 2 : ℝ) * rexp (-(π ^ 2 * ‖ξ‖ ^ 2 * t⁻¹))) • χ ξ :=
  kernelFourier_integral_gaussian_smul_fourier ht χ

example (χ : 𝓢(E3, ℂ)) :
    ∫ z, (newtonKernel z : ℂ) * 𝓕 χ z = ∫ ξ, (newtonSymbol ξ : ℂ) * χ ξ :=
  integral_newtonKernel_mul_fourier χ

example (χ : 𝓢(E3, ℂ)) :
    ∫ x, 𝓕 χ x = χ 0 :=
  integral_fourier_eq_apply_zero χ

example :
    ContDiffBump (0 : E3) :=
  kernelFourier_bump

example :
    ContDiff ℝ ∞ fun x : E3 => (kernelFourier_bump x : ℂ) :=
  kernelFourier_contDiff_bump

example :
    HasCompactSupport fun x : E3 => (kernelFourier_bump x : ℂ) :=
  kernelFourier_hasCompactSupport_bump

example :
    ∃ χ : 𝓢(E3, ℂ), χ 0 = 1 :=
  exists_schwartzMap_apply_zero_eq_one

end ProjectAinos.SmoothGeometry.Potential

end KernelFourier

section CoulombFourier

open MeasureTheory Filter Set Metric Real

open scoped Topology FourierTransform SchwartzMap ContDiff Laplacian

namespace ProjectAinos.Electrodynamics.CoulombFourier

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) :
    ∃ ρc : 𝓢(E3, ℂ), ∀ x, ρc x = ρ x :=
  exists_schwartzMap_eq_ofReal hρ hcρ

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    ∃ A, ∀ x, |newtonPotential ρ x| ≤ A :=
  exists_abs_newtonPotential_le_const hρ hcρ

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    Continuous (newtonPotential ρ) :=
  continuous_newtonPotential hρ hcρ

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {g : E3 → ℝ}
    (hg : Integrable g) :
    Integrable fun x => newtonPotential ρ x * g x :=
  integrable_newtonPotential_mul hρ hcρ hg

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {g : E3 → ℂ}
    (hg : Integrable g) :
    Integrable fun x => (newtonPotential ρ x : ℂ) * g x :=
  integrable_newtonPotential_mul_complex hρ hcρ hg

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (χ : 𝓢(E3, ℂ)) :
    ∫ x, (newtonPotential ρ x : ℂ) * 𝓕 χ x =
      ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) :=
  fourier_newtonPotential_apply hρ hcρ χ

open LineDeriv in

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (v : E3) (χ : 𝓢(E3, ℂ)) :
    ∫ x, (fderiv ℝ (newtonPotential ρ) x v : ℂ) * 𝓕 χ x =
      ∫ ξ, (newtonSymbol ξ : ℂ) *
        (𝓕 (fun x => (ρ x : ℂ)) ξ * (2 * π * Complex.I * inner ℝ ξ v * χ ξ)) :=
  fourier_fderiv_newtonPotential_apply hρ hcρ v χ

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (i : Fin 3) (χ : 𝓢(E3, ℂ)) :
    ∫ x, (-fderiv ℝ (newtonPotential ρ) x (EuclideanSpace.single i 1) : ℂ) * 𝓕 χ x =
      ∫ ξ, (newtonSymbol ξ : ℂ) *
        (𝓕 (fun x => (ρ x : ℂ)) ξ * (-(2 * π * Complex.I) * ξ i * χ ξ)) :=
  fourier_electricField_apply hρ hcρ i χ

example {ρ : E3 → ℝ} (hcρ : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (c : ℝ) (x : E3) :
    -Δ (fun y => newtonPotential ρ y + c) x = ρ x :=
  neg_laplacian_newtonPotential_add_const hcρ hρ c x

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (c : ℝ) (χ : 𝓢(E3, ℂ)) :
    ∫ x, ((newtonPotential ρ x + c : ℝ) : ℂ) * 𝓕 χ x =
      (∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ)) + c * χ 0 :=
  fourier_newtonPotential_add_const hρ hcρ c χ

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (c : ℝ) :
    (∀ χ : 𝓢(E3, ℂ), ∫ x, ((newtonPotential ρ x + c : ℝ) : ℂ) * 𝓕 χ x =
      ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ)) ↔ c = 0 :=
  fourier_newtonPotential_add_const_eq_iff hρ hcρ c

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) (c : ℝ) :
    Tendsto (fun x => newtonPotential ρ x + c) (cocompact E3) (𝓝 0) ↔ c = 0 :=
  tendsto_newtonPotential_add_const_iff hρ hcρ c

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (c : ℝ) :
    Tendsto (fun x => newtonPotential ρ x + c) (cocompact E3) (𝓝 0) ↔
      ∀ χ : 𝓢(E3, ℂ), ∫ x, ((newtonPotential ρ x + c : ℝ) : ℂ) * 𝓕 χ x =
        ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) :=
  tendsto_newtonPotential_add_const_iff_fourier hρ hcρ c

example {ρ u : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (hu : ContDiff ℝ 2 u)
    (hΔ : ∀ x, -Δ u x = ρ x) (hlim : Tendsto u (cocompact E3) (𝓝 0)) (χ : 𝓢(E3, ℂ)) :
    ∫ x, (u x : ℂ) * 𝓕 χ x = ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) :=
  fourier_eq_of_tendsto hρ hcρ hu hΔ hlim χ

open Classical in

example (u : E3 → ℝ) :
    𝓢'(E3, ℂ) :=
  boundedTempered u

example {u : E3 → ℝ} (hu : MemLp (fun x => (u x : ℂ)) ⊤) (χ : 𝓢(E3, ℂ)) :
    boundedTempered u χ = ∫ x, (u x : ℂ) * χ x :=
  boundedTempered_apply hu χ

example {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    MemLp (fun x => (newtonPotential ρ x : ℂ)) ⊤ :=
  memLp_top_newtonPotential hρ hcρ

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (χ : 𝓢(E3, ℂ)) :
    𝓕 (boundedTempered (newtonPotential ρ)) χ =
      ∫ ξ, (newtonSymbol ξ : ℂ) * (𝓕 (fun x => (ρ x : ℂ)) ξ * χ ξ) :=
  fourier_boundedTempered_newtonPotential_apply hρ hcρ χ

example {ρ : E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) (c : ℝ) :
    𝓕 (boundedTempered fun x => newtonPotential ρ x + c) =
      𝓕 (boundedTempered (newtonPotential ρ)) + (c : ℂ) • TemperedDistribution.delta 0 :=
  fourier_boundedTempered_newtonPotential_add_const hρ hcρ c

example :
    ∃ ρ : E3 → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ ρ 0 = 1 :=
  exists_density

example :
    ∃ ρ u : E3 → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
    ρ 0 = 1 ∧ ContDiff ℝ 2 u ∧ (∀ x, -Δ u x = ρ x) ∧ Tendsto u (cocompact E3) (𝓝 0) :=
  exists_decaying_solution

end ProjectAinos.Electrodynamics.CoulombFourier

end CoulombFourier
