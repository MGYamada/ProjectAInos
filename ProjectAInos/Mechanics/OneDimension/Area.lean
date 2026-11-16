/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.OneDimension.Orbit
public import ProjectAInos.Variational.IntervalParameter
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The period is the derivative of the area with respect to the energy

`orbitArea m U a b` is the integral `∮ p dx` over the level curve of a well,
in the angle of `Orbit`. It is twice the integral of `√(2m (E − U))` between
the turning points (`IsWell.orbitArea_eq`).

`hasDerivAt_orbitArea` is Proposition 68 (Landau–Lifshitz §11): along a smooth
family of wells `α(E) < β(E)`,

`d/dE ∮ p dx = T(E)`.

The derivative of `p x_θ` in the energy is `λ` plus the derivative in `θ` of
`p ∂x/∂E`: this is the derivative in the energy of the identity
`p²/2m + U(x) = E` on the curve, together with the tangency of the curve to
the Hamiltonian field. The second term integrates to zero over the closed
curve. The square root is never differentiated at a turning point.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Real Topology ContDiff

namespace ProjectAInos.Mechanics.OneDim

variable {U : ℝ → ℝ} {E a b m : ℝ}

/-- The area `∮ p dx` enclosed by the level curve, as an integral over the
angle. -/
def orbitArea (m : ℝ) (U : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * π, orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ)

namespace IsWell

theorem continuous_orbitMomentum (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (m : ℝ) :
    Continuous (orbitMomentum m U a b) :=
  continuous_iff_continuousAt.mpr fun θ => (h.hasDerivAt_orbitMomentum hU m θ).continuousAt

/-- On the upper half of the curve the momentum is the positive root. -/
theorem orbitMomentum_eq_sqrt (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m)
    {θ : ℝ} (hθ : θ ∈ Icc 0 π) :
    orbitMomentum m U a b θ = √(2 * m * (E - U (orbitPosition a b θ))) := by
  have hnonneg : 0 ≤ orbitMomentum m U a b θ := by
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hr : 0 ≤ (b - a) / 2 := by linarith [h.lt]
    rw [orbitMomentum]
    positivity
  rw [← h.orbitMomentum_sq hU hm, Real.sqrt_sq hnonneg]

/-- The area is twice the integral of the momentum between the turning points:
`∮ p dx = 2 ∫ₐᵇ √(2m (E − U(x))) dx`. -/
theorem orbitArea_eq (h : IsWell U E a b) (hU : ContDiff ℝ ∞ U) (hm : 0 < m) :
    orbitArea m U a b = 2 * ∫ x in a..b, √(2 * m * (E - U x)) := by
  have hc : Continuous fun θ => orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ) :=
    (h.continuous_orbitMomentum hU m).mul (continuous_const.mul Real.continuous_sin)
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 π) (hc.intervalIntegrable π (2 * π))).symm
  have hsecond : ∫ θ in π..2 * π, orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ) =
      ∫ θ in (0 : ℝ)..π, orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ) := by
    have hsub := intervalIntegral.integral_comp_sub_left (a := 0) (b := π)
      (fun θ => orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ)) (2 * π)
    have hfun : (fun θ => orbitMomentum m U a b (2 * π - θ) *
        ((b - a) / 2 * Real.sin (2 * π - θ))) =
        fun θ => orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ) := by
      funext θ
      have e : 2 * π - θ = -θ + 2 * π := by ring
      rw [e, orbitMomentum_add_two_pi, orbitMomentum_neg, Real.sin_add_two_pi, Real.sin_neg]
      ring
    rw [hfun] at hsub
    rw [hsub]
    congr 1 <;> ring
  have hg : Continuous fun x => √(2 * m * (E - U x)) :=
    Real.continuous_sqrt.comp (continuous_const.mul (continuous_const.sub hU.continuous))
  have hsubst := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := π)
    (f := orbitPosition a b) (f' := fun θ => (b - a) / 2 * Real.sin θ)
    (g := fun x => √(2 * m * (E - U x)))
    (fun θ _ => hasDerivAt_orbitPosition a b θ)
    (continuous_const.mul Real.continuous_sin).continuousOn hg
  rw [orbitPosition_zero, orbitPosition_pi] at hsubst
  have hhalf : ∫ θ in (0 : ℝ)..π, orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ) =
      ∫ x in a..b, √(2 * m * (E - U x)) := by
    rw [← hsubst]
    refine intervalIntegral.integral_congr fun θ hθ => ?_
    rw [uIcc_of_le Real.pi_pos.le] at hθ
    change orbitMomentum m U a b θ * ((b - a) / 2 * Real.sin θ) =
      √(2 * m * (E - U (orbitPosition a b θ))) * ((b - a) / 2 * Real.sin θ)
    rw [h.orbitMomentum_eq_sqrt hU hm hθ]
  rw [orbitArea, hsplit, hsecond, hhalf]
  ring

end IsWell

/-- The momentum on the level curves of a smooth family of wells is a smooth
function of the energy and the angle. -/
theorem contDiffOn_orbitMomentum_family (hU : ContDiff ℝ ∞ U) (m : ℝ) {J : Set ℝ}
    {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => orbitMomentum m U (α p.1) (β p.1) p.2)
      (Prod.fst ⁻¹' J) := by
  have hαO : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1) (Prod.fst ⁻¹' J) :=
    hα.comp contDiffOn_fst fun p hp => hp
  have hβO : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1) (Prod.fst ⁻¹' J) :=
    hβ.comp contDiffOn_fst fun p hp => hp
  have hcos : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.cos p.2) (Prod.fst ⁻¹' J) :=
    (Real.contDiff_cos.comp contDiff_snd).contDiffOn
  have hsin : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.sin p.2) (Prod.fst ⁻¹' J) :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hX : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => orbitPosition (α p.1) (β p.1) p.2)
      (Prod.fst ⁻¹' J) :=
    ((hαO.add hβO).div_const 2).sub (((hβO.sub hαO).div_const 2).mul hcos)
  have hWf : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      wellFactor U (α p.1) (β p.1) (orbitPosition (α p.1) (β p.1) p.2)) (Prod.fst ⁻¹' J) :=
    (contDiff_wellFactor hU).comp_contDiffOn (hαO.prodMk (hβO.prodMk hX))
  exact (contDiffOn_const.mul (((hβO.sub hαO).div_const 2).mul hsin)).mul
    (hWf.sqrt fun p hp => ((hw p.1 hp).wellFactor_orbitPosition_pos hU p.2).ne')

/-- The derivative in the energy of the position on the level curve, at a fixed
angle. -/
theorem hasDerivAt_orbitPosition_energy {α β : ℝ → ℝ} {E₀ α' β' : ℝ}
    (hα : HasDerivAt α α' E₀) (hβ : HasDerivAt β β' E₀) (θ : ℝ) :
    HasDerivAt (fun E => orbitPosition (α E) (β E) θ)
      ((α' + β') / 2 - (β' - α') / 2 * Real.cos θ) E₀ :=
  ((hα.add hβ).div_const 2).sub (((hβ.sub hα).div_const 2).mul_const (Real.cos θ))

/-- The derivative in the energy of the identity `p²/2m + U(x) = E` on the level
curves of a family of wells: `p ∂p/∂E / m + U′(x) ∂x/∂E = 1`. -/
theorem orbitMomentum_mul_deriv_energy (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ}
    (hJ : IsOpen J) {α β : ℝ → ℝ} (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {E₀ : ℝ}
    (hE₀ : E₀ ∈ J) {α' β' PE : ℝ} (hα : HasDerivAt α α' E₀) (hβ : HasDerivAt β β' E₀)
    {θ : ℝ} (hPE : HasDerivAt (fun E => orbitMomentum m U (α E) (β E) θ) PE E₀) :
    orbitMomentum m U (α E₀) (β E₀) θ * PE / m +
      deriv U (orbitPosition (α E₀) (β E₀) θ) *
        ((α' + β') / 2 - (β' - α') / 2 * Real.cos θ) = 1 := by
  have h1 := (hPE.mul hPE).div_const (2 * m)
  have h2 := ((hU.differentiable (by simp) _).hasDerivAt).comp E₀
    (hasDerivAt_orbitPosition_energy hα hβ θ)
  have h3 := h1.add h2
  have hev : (fun E => E) =ᶠ[𝓝 E₀] fun E =>
      orbitMomentum m U (α E) (β E) θ * orbitMomentum m U (α E) (β E) θ / (2 * m) +
        U (orbitPosition (α E) (β E) θ) :=
    Filter.eventually_of_mem (hJ.mem_nhds hE₀) fun E hE => by
      have he := (hw E hE).orbit_energy hU hm θ
      rw [pow_two] at he
      exact he.symm
  have h4 := (h3.congr_of_eventuallyEq hev).unique (hasDerivAt_id E₀)
  linear_combination h4

/-- Proposition 68 (Landau–Lifshitz §11): along a smooth family of wells the
derivative of the area `∮ p dx` with respect to the energy is the period. -/
theorem hasDerivAt_orbitArea (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {J : Set ℝ} (hJ : IsOpen J)
    {α β : ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α J) (hβ : ContDiffOn ℝ ∞ β J)
    (hw : ∀ E ∈ J, IsWell U E (α E) (β E)) {E₀ : ℝ} (hE₀ : E₀ ∈ J) :
    HasDerivAt (fun E => orbitArea m U (α E) (β E)) (orbitPeriod m U (α E₀) (β E₀)) E₀ := by
  have h₀ := hw E₀ hE₀
  have hαd : HasDerivAt α (deriv α E₀) E₀ :=
    ((hα.contDiffAt (hJ.mem_nhds hE₀)).differentiableAt (by simp)).hasDerivAt
  have hβd : HasDerivAt β (deriv β E₀) E₀ :=
    ((hβ.contDiffAt (hJ.mem_nhds hE₀)).differentiableAt (by simp)).hasDerivAt
  have hO : IsOpen (Prod.fst ⁻¹' J : Set (ℝ × ℝ)) := hJ.preimage continuous_fst
  have hαO : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => α p.1) (Prod.fst ⁻¹' J) :=
    hα.comp contDiffOn_fst fun p hp => hp
  have hβO : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => β p.1) (Prod.fst ⁻¹' J) :=
    hβ.comp contDiffOn_fst fun p hp => hp
  have hsin : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => Real.sin p.2) (Prod.fst ⁻¹' J) :=
    (Real.contDiff_sin.comp contDiff_snd).contDiffOn
  have hP := contDiffOn_orbitMomentum_family hU m hα hβ hw
  have hF : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      orbitMomentum m U (α p.1) (β p.1) p.2 * ((β p.1 - α p.1) / 2 * Real.sin p.2))
      (Prod.fst ⁻¹' J) :=
    hP.mul (((hβO.sub hαO).div_const 2).mul hsin)
  -- the derivatives in the energy at the reference energy
  have hline : ∀ θ : ℝ, HasDerivAt (fun E : ℝ => (E, θ)) ((1 : ℝ), (0 : ℝ)) E₀ := fun θ =>
    (hasDerivAt_id E₀).prodMk (hasDerivAt_const E₀ θ)
  have hPE : ∀ θ : ℝ, HasDerivAt (fun E => orbitMomentum m U (α E) (β E) θ)
      (fderiv ℝ (fun p : ℝ × ℝ => orbitMomentum m U (α p.1) (β p.1) p.2) (E₀, θ) (1, 0))
      E₀ := by
    intro θ
    have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => orbitMomentum m U (α p.1) (β p.1) p.2)
        (E₀, θ) :=
      (hP.contDiffAt (hO.mem_nhds (show (E₀, θ) ∈ Prod.fst ⁻¹' J from hE₀))).differentiableAt
        (by simp)
    exact HasFDerivAt.comp_hasDerivAt (f := fun E : ℝ => (E, θ)) E₀ hd.hasFDerivAt (hline θ)
  have hr : HasDerivAt (fun E => (β E - α E) / 2) ((deriv β E₀ - deriv α E₀) / 2) E₀ :=
    (hβd.sub hαd).div_const 2
  -- the derivative of the identity `p²/2m + U(x) = E` in the energy
  have henergy : ∀ θ : ℝ, orbitMomentum m U (α E₀) (β E₀) θ *
      fderiv ℝ (fun p : ℝ × ℝ => orbitMomentum m U (α p.1) (β p.1) p.2) (E₀, θ) (1, 0) / m +
      deriv U (orbitPosition (α E₀) (β E₀) θ) *
        ((deriv α E₀ + deriv β E₀) / 2 - (deriv β E₀ - deriv α E₀) / 2 * Real.cos θ) = 1 :=
    fun θ => orbitMomentum_mul_deriv_energy hU hm hJ hw hE₀ hαd hβd (hPE θ)
  -- differentiation under the integral sign
  have hD : ∀ θ ∈ uIcc (0 : ℝ) (2 * π), HasDerivAt
      (fun E => (fun p : ℝ × ℝ => orbitMomentum m U (α p.1) (β p.1) p.2 *
        ((β p.1 - α p.1) / 2 * Real.sin p.2)) (E, θ))
      ((fun θ => fderiv ℝ (fun p : ℝ × ℝ => orbitMomentum m U (α p.1) (β p.1) p.2) (E₀, θ)
          (1, 0) * ((β E₀ - α E₀) / 2 * Real.sin θ) +
        orbitMomentum m U (α E₀) (β E₀) θ * ((deriv β E₀ - deriv α E₀) / 2 * Real.sin θ)) θ)
      E₀ :=
    fun θ _ => (hPE θ).mul (hr.mul_const (Real.sin θ))
  have hmain := Variational.hasDerivAt_intervalIntegral_of_contDiffAt
    (fun θ _ => (hF.contDiffAt (hO.mem_nhds (show (E₀, θ) ∈ Prod.fst ⁻¹' J from hE₀))).of_le
      (by simp)) hD
  refine hmain.congr_deriv ?_
  -- the integrand is the rate plus a derivative in the angle
  have hG : ∀ θ : ℝ, HasDerivAt
      (fun θ => orbitMomentum m U (α E₀) (β E₀) θ *
        ((deriv α E₀ + deriv β E₀) / 2 - (deriv β E₀ - deriv α E₀) / 2 * Real.cos θ))
      (-(orbitRate m U (α E₀) (β E₀) θ * deriv U (orbitPosition (α E₀) (β E₀) θ)) *
          ((deriv α E₀ + deriv β E₀) / 2 - (deriv β E₀ - deriv α E₀) / 2 * Real.cos θ) +
        orbitMomentum m U (α E₀) (β E₀) θ * ((deriv β E₀ - deriv α E₀) / 2 * Real.sin θ)) θ := by
    intro θ
    have hx : HasDerivAt (fun θ : ℝ => (deriv α E₀ + deriv β E₀) / 2 -
        (deriv β E₀ - deriv α E₀) / 2 * Real.cos θ)
        ((deriv β E₀ - deriv α E₀) / 2 * Real.sin θ) θ := by
      refine (((Real.hasDerivAt_cos θ).const_mul ((deriv β E₀ - deriv α E₀) / 2)).const_sub
        ((deriv α E₀ + deriv β E₀) / 2)).congr_deriv ?_
      ring
    exact (h₀.hasDerivAt_orbitMomentum hU m θ).mul hx
  have hpt : ∀ θ : ℝ,
      fderiv ℝ (fun p : ℝ × ℝ => orbitMomentum m U (α p.1) (β p.1) p.2) (E₀, θ) (1, 0) *
          ((β E₀ - α E₀) / 2 * Real.sin θ) +
        orbitMomentum m U (α E₀) (β E₀) θ * ((deriv β E₀ - deriv α E₀) / 2 * Real.sin θ) =
      orbitRate m U (α E₀) (β E₀) θ +
        (-(orbitRate m U (α E₀) (β E₀) θ * deriv U (orbitPosition (α E₀) (β E₀) θ)) *
            ((deriv α E₀ + deriv β E₀) / 2 - (deriv β E₀ - deriv α E₀) / 2 * Real.cos θ) +
          orbitMomentum m U (α E₀) (β E₀) θ *
            ((deriv β E₀ - deriv α E₀) / 2 * Real.sin θ)) := by
    intro θ
    have htan := h₀.orbitRate_mul_orbitMomentum hU hm θ
    have hen := henergy θ
    rw [← htan]
    linear_combination (orbitRate m U (α E₀) (β E₀) θ) * hen
  have hcrate : Continuous (orbitRate m U (α E₀) (β E₀)) := by
    have hWc : Continuous fun θ => wellFactor U (α E₀) (β E₀) (orbitPosition (α E₀) (β E₀) θ) :=
      (contDiff_wellFactor_right hU _ _).continuous.comp (contDiff_orbitPosition _ _).continuous
    exact continuous_const.div (Real.continuous_sqrt.comp hWc) fun θ =>
      (Real.sqrt_pos.mpr (h₀.wellFactor_orbitPosition_pos hU θ)).ne'
  have hcG : Continuous fun θ =>
      -(orbitRate m U (α E₀) (β E₀) θ * deriv U (orbitPosition (α E₀) (β E₀) θ)) *
          ((deriv α E₀ + deriv β E₀) / 2 - (deriv β E₀ - deriv α E₀) / 2 * Real.cos θ) +
        orbitMomentum m U (α E₀) (β E₀) θ * ((deriv β E₀ - deriv α E₀) / 2 * Real.sin θ) := by
    have hdU : Continuous fun θ => deriv U (orbitPosition (α E₀) (β E₀) θ) :=
      (hU.continuous_deriv (by simp)).comp (contDiff_orbitPosition _ _).continuous
    exact ((hcrate.mul hdU).neg.mul (continuous_const.sub
      (continuous_const.mul Real.continuous_cos))).add
        ((h₀.continuous_orbitMomentum hU m).mul (continuous_const.mul Real.continuous_sin))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 2 * π)
    (fun θ _ => hG θ) (hcG.intervalIntegrable _ _)
  have hzero : orbitMomentum m U (α E₀) (β E₀) (2 * π) = 0 := by
    have e : (2 * π : ℝ) = 0 + 2 * π := by ring
    rw [e, orbitMomentum_add_two_pi, orbitMomentum_zero]
  rw [intervalIntegral.integral_congr fun θ _ => hpt θ,
    intervalIntegral.integral_add (hcrate.intervalIntegrable _ _) (hcG.intervalIntegrable _ _),
    hftc, hzero, orbitMomentum_zero, orbitPeriod]
  ring

/-- Proposition 68 at a single well: the turning points extend to a smooth
family of wells over an open set of energies, and the derivative of the area
with respect to the energy is the period. -/
theorem IsWell.exists_hasDerivAt_orbitArea (hU : ContDiff ℝ ∞ U) (hm : 0 < m) {E₀ a₀ b₀ : ℝ}
    (h : IsWell U E₀ a₀ b₀) :
    ∃ (J : Set ℝ) (α β : ℝ → ℝ), IsOpen J ∧ E₀ ∈ J ∧ α E₀ = a₀ ∧ β E₀ = b₀ ∧
      ContDiffOn ℝ ∞ α J ∧ ContDiffOn ℝ ∞ β J ∧ (∀ E ∈ J, IsWell U E (α E) (β E)) ∧
      HasDerivAt (fun E => orbitArea m U (α E) (β E)) (orbitPeriod m U a₀ b₀) E₀ := by
  obtain ⟨J, α, β, hJ, hE₀, hα₀, hβ₀, hα, hβ, hw⟩ := h.exists_family hU
  refine ⟨J, α, β, hJ, hE₀, hα₀, hβ₀, hα, hβ, hw, ?_⟩
  have hd := hasDerivAt_orbitArea hU hm hJ hα hβ hw hE₀
  rwa [hα₀, hβ₀] at hd

end ProjectAInos.Mechanics.OneDim
