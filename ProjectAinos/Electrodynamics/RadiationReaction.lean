/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.DarwinPointCharge
public import ProjectAinos.Electrodynamics.Examples
public import ProjectAinos.Mechanics.Oscillations.Forced
import Mathlib.Tactic

/-!
# Radiation damping

Landau–Lifshitz, *The Classical Theory of Fields*, §75 (radiation damping) and §76 (radiation
damping in the relativistic case), with `c = 1` and the units with `div E = ρ`, in which the
coefficient `2e²/3c³` of the book is `(2/3)(e²/4π)`. A source `(ρ, 𝐣)(s, x)` is made slow by
`ρ_κ(t, x) = ρ(κt, x)`, `𝐣_κ(t, x) = κ𝐣(κt, x)` (`SlowSource` of
`Electrodynamics.DarwinLagrangian`); the motion of the charges is prescribed throughout.

* Moments: `dipoleMoment` `dᵢ(s) = ∫ zᵢ ρ(s, z) dz`, `iterate_deriv_dipoleMoment`,
  `dipoleMoment_iterate_three` (`d⃛ᵢ = ∫ ∂ₛ²jᵢ`), the integration by parts
  `integral_mul_spaceDeriv`, and `slowTerm_three_spaceDeriv`: the term `κ³` of the slow expansion
  of `∇φ` is the uniform `(1/3)(1/4π) κ³ d⃛`.
* **The damping field** `dampingField_expansion` (75.5): under the bounds `DampingBounds M`, at
  `‖x‖ ≤ R`, `E = E' + (2/3)(1/4π) κ³ d⃛(κt)` up to `(M(R + a)⁶/72 + M(R + a)⁴/6) κ⁴`, with the
  field `E'` of the potentials of Darwin; `spaceDeriv_vector_sub_cubic` (the magnetic field of
  Darwin is exact to `O(κ³)`) and `lorentzDensity_expansion` (the density `E + 𝐯 × B`).
* **The self-force**: a rigid charge `eη(x − R(s))` with an even profile on a smooth bounded path
  is a slow source (`slowSource_rigid`); parity about the moving centre (`ReflectsAbout`,
  `integral_mul_eq_zero_of_odd`). `selfForce_darwin`: its own potentials of Darwin exert exactly
  `−Σₖ δmᵢₖ v̇ₖ` with the mass tensor `selfMass`, the kernel of Darwin averaged over the charge;
  `trace_selfMass`: `Σᵢ δmᵢᵢ = 4U` with the self-energy `selfEnergy`, so `δm = (4/3)U` for an
  isotropic charge. `selfForce_expansion` (75.8): the self-force of the retarded field is
  `−Σₖ δmᵢₖ v̇ₖ + (2/3)(e²/4π) v̈ᵢ + O(κ⁴)`. Instances: `exists_dampingBounds_of_periodic`,
  `selfForce_expansion_oscillating`.
* **The work** `work_dampingForce_eq` (75.9): `∫ 𝐟 · 𝐯 dt = −(2/3)(e²/4π) ∫ v̇² dt` plus the term
  of Schott `(2/3)(e²/4π) [v̇ · 𝐯]`, with `dampingForce` `𝐟 = (2/3)(e²/4π) v̈`.
* **Runaways**: `abrahamLorentz_free` (`v̇(t) = e^{t/τ} v̇(0)` for `m v̇ = (2/3)(e²/4π) v̈`),
  `runaway` (solutions with unbounded acceleration and no force), `abrahamLorentz_free_eq_zero`.
* **The charged oscillator**: `IsReducedOscillator`, `reducedOscillator` (the reduced equation is
  `IsForced` with `γ = e²ω₀²/(12πm)`), `reducedOscillator_free`, `abrahamLorentz_residual` (the
  residual of the equation of Abraham and Lorentz is `−τ²ü`), `isReducedOscillator_damped`.
* **§76**: `lorentzDiracForce` `(2/3)(e²/4π)(ü + (ü · u)u)` (76.2) and `lorentzDirac_orthogonal`;
  `lorentzDiracForce_eq_of_unit` (`ü − (u̇ · u̇)u`); `lorentzDirac_nonrelativistic`: at an instant
  of rest it is `(0, (2/3)(e²/4π) x⃛)`, with the instance `lorentzDirac_nonrelativistic_hyperbolic`;
  `radiatedMomentumRate` and `integral_lorentzDirac_eq` (the impulse is the change of the term of
  Schott minus the radiated four-momentum); `landauLifshitzForce` (76.3),
  `landauLifshitz_orthogonal` and `lorentzDirac_eq_landauLifshitz` (on the motion without
  damping); hyperbolic motion in a constant field: `lorentzDiracForce_hyperbolaVelocity`,
  `hyperbola_lorentzDirac_equation`, `landauLifshitzForce_hyperbola`,
  `integral_radiatedMomentumRate_hyperbola`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.RadiationReaction

open SmoothGeometry SmoothGeometry.Wave SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Moments of a source and integration by parts -/

/-- The iterated time derivatives of a smooth function are smooth. -/
theorem contDiff_iterate_timeDeriv_infty {f : ℝ × E3 → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (timeDeriv^[k] f) := by
  induction k generalizing f with
  | zero => exact hf
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    exact ih (contDiff_infty_timeDeriv hf)

/-- An integral against a weight `w` over the slice at the time `s` is the integral against the
reflected kernel at the origin. -/
theorem integral_weight_mul_eq_kernelIntegral (w : E3 → ℝ) (F : ℝ × E3 → ℝ) (s : ℝ) :
    ∫ z, w z * F (s, z) = kernelIntegral (fun y => w (-y)) F (s, 0) := by
  rw [kernelIntegral, ← integral_neg_eq_self]
  congr 1
  funext y
  simp [smul_eq_mul]

/-- **Differentiation of a moment**: for a `C¹` function supported in a cylinder and a continuous
weight, `d/ds ∫ w(z) F(s, z) dz = ∫ w(z) ∂ₛF(s, z) dz`. -/
theorem hasDerivAt_integral_weight_mul {w : E3 → ℝ} (hw : Continuous w) {F : ℝ × E3 → ℝ}
    (hF : ContDiff ℝ 1 F) {a : ℝ} (hs : SpatialSupport a F) (s : ℝ) :
    HasDerivAt (fun s => ∫ z, w z * F (s, z)) (∫ z, w z * timeDeriv F (s, z)) s := by
  have hK : LocallyIntegrable fun y : E3 => w (-y) := (hw.comp continuous_neg).locallyIntegrable
  have hd : DifferentiableAt ℝ (kernelIntegral (fun y => w (-y)) F) (s, 0) :=
    (hasFDerivAt_kernelIntegral hK hF (hs.kernelSupport _) (s, 0)).differentiableAt
  have h := hasDerivAt_timeSlice_of_differentiableAt hd
  rw [timeDeriv_kernelIntegral hK hF (hs.kernelSupport _)] at h
  simp only [integral_weight_mul_eq_kernelIntegral w]
  exact h

/-- Two moments that agree at all times have equal derivatives. -/
theorem integral_weight_mul_timeDeriv_eq {w₁ w₂ : E3 → ℝ} (hw₁ : Continuous w₁)
    (hw₂ : Continuous w₂) {F₁ F₂ : ℝ × E3 → ℝ} (h₁ : ContDiff ℝ 1 F₁) (h₂ : ContDiff ℝ 1 F₂)
    {a : ℝ} (hs₁ : SpatialSupport a F₁) (hs₂ : SpatialSupport a F₂)
    (heq : ∀ s, ∫ z, w₁ z * F₁ (s, z) = ∫ z, w₂ z * F₂ (s, z)) (s : ℝ) :
    ∫ z, w₁ z * timeDeriv F₁ (s, z) = ∫ z, w₂ z * timeDeriv F₂ (s, z) := by
  have e : (fun s => ∫ z, w₁ z * F₁ (s, z)) = fun s => ∫ z, w₂ z * F₂ (s, z) := funext heq
  have d₁ := hasDerivAt_integral_weight_mul hw₁ h₁ hs₁ s
  rw [e] at d₁
  exact d₁.unique (hasDerivAt_integral_weight_mul hw₂ h₂ hs₂ s)

/-- The dipole moment `dᵢ(s) = ∫ zᵢ ρ(s, z) dz` of a charge density. -/
def dipoleMoment (ρ : ℝ × E3 → ℝ) (i : Fin 3) (s : ℝ) : ℝ := ∫ z, z i * ρ (s, z)

theorem continuous_component (i : Fin 3) : Continuous fun z : E3 => z i :=
  (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous

/-- The derivative of the dipole moment is the dipole moment of `∂ₛρ`. -/
theorem hasDerivAt_dipoleMoment {ρ : ℝ × E3 → ℝ} (hρ : ContDiff ℝ 1 ρ) {a : ℝ}
    (hs : SpatialSupport a ρ) (i : Fin 3) (s : ℝ) :
    HasDerivAt (dipoleMoment ρ i) (dipoleMoment (timeDeriv ρ) i s) s :=
  hasDerivAt_integral_weight_mul (continuous_component i) hρ hs s

/-- `dⁿdᵢ/dsⁿ` is the dipole moment of `∂ₛⁿρ`. -/
theorem iterate_deriv_dipoleMoment {ρ : ℝ × E3 → ℝ} (hρ : ContDiff ℝ ∞ ρ) {a : ℝ}
    (hs : SpatialSupport a ρ) (i : Fin 3) (n : ℕ) :
    deriv^[n] (dipoleMoment ρ i) = dipoleMoment (timeDeriv^[n] ρ) i := by
  induction n generalizing ρ with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hd : deriv (dipoleMoment ρ i) = dipoleMoment (timeDeriv ρ) i :=
      funext fun s => (hasDerivAt_dipoleMoment (hρ.of_le (by simp)) hs i s).deriv
    rw [hd]
    exact ih (contDiff_infty_timeDeriv hρ) hs.timeDeriv

/-- **Integration by parts** on the slices: for a `C¹` weight `w` and a `C¹` function supported in
a cylinder, `∫ w ∂ₖG(s, ·) = −∫ (∂ₖw) G(s, ·)`. -/
theorem integral_mul_spaceDeriv {w : E3 → ℝ} (hw : ContDiff ℝ 1 w) {G : ℝ × E3 → ℝ}
    (hG : ContDiff ℝ 1 G) {a : ℝ} (hs : SpatialSupport a G) (s : ℝ) (k : Fin 3) :
    ∫ z, w z * spaceDeriv k G (s, z) =
      -∫ z, fderiv ℝ w z (EuclideanSpace.single k 1) * G (s, z) := by
  set F : ℝ × E3 → ℝ := fun p => w p.2 * G p with hFdef
  have hF : ContDiff ℝ 1 F := (hw.comp contDiff_snd).mul hG
  have hFs : SpatialSupport a F := hs.mono fun p hp => by simp [hFdef, hp]
  have hder : ∀ z, spaceDeriv k F (s, z) =
      fderiv ℝ w z (EuclideanSpace.single k 1) * G (s, z) + w z * spaceDeriv k G (s, z) := by
    intro z
    have hw' := (hw.differentiable one_ne_zero z).hasFDerivAt
    have hG' := (hG.differentiable one_ne_zero (s, z)).hasFDerivAt
    have h : HasFDerivAt F (w z • fderiv ℝ G (s, z) +
        G (s, z) • (fderiv ℝ w z).comp (ContinuousLinearMap.snd ℝ ℝ E3)) (s, z) :=
      (hw'.comp (s, z) hasFDerivAt_snd).mul hG'
    rw [spaceDeriv, h.fderiv, spaceDeriv]
    simp [smul_eq_mul]
    ring
  have h0 := integral_spaceDeriv_eq_zero hF hFs s k
  simp only [hder] at h0
  have hcs : Continuous fun z : E3 => G (s, z) :=
    hG.continuous.comp (continuous_const.prodMk continuous_id)
  have i1 : Integrable fun z => fderiv ℝ w z (EuclideanSpace.single k 1) * G (s, z) :=
    (((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const).mul
      hcs).integrable_of_hasCompactSupport (hs.hasCompactSupport_slice s).mul_left
  have i2 : Integrable fun z => w z * spaceDeriv k G (s, z) :=
    (hw.continuous.mul ((contDiff_spaceDeriv (n := 0) (by simpa using hG) k).continuous.comp
      (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
      ((hs.spaceDeriv k).hasCompactSupport_slice s).mul_left
  rw [integral_add i1 i2] at h0
  linarith

/-- The derivative of the coordinate `zᵢ` along `eₖ` is `δᵢₖ`. -/
theorem fderiv_component (i k : Fin 3) (z : E3) :
    fderiv ℝ (fun z : E3 => z i) z (EuclideanSpace.single k 1) = if i = k then 1 else 0 := by
  have h : HasFDerivAt (fun z : E3 => z i) (EuclideanSpace.proj i : E3 →L[ℝ] ℝ) z :=
    (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).hasFDerivAt
  rw [h.fderiv]
  simp

/-! ### The moments of a slow source -/

variable {a : ℝ} {ρ : ℝ × E3 → ℝ} {j : Fin 3 → ℝ × E3 → ℝ}

/-- The charge is conserved at every order: `∫ ∂ₛⁿ⁺¹ρ(s, z) dz = 0`. -/
theorem integral_iterate_timeDeriv_eq_zero (h : SlowSource a ρ j) (n : ℕ) (s : ℝ) :
    ∫ z, timeDeriv^[n + 1] ρ (s, z) = 0 := by
  induction n generalizing s with
  | zero => simpa using h.integral_timeDeriv s
  | succ n ih =>
    have hc : ContDiff ℝ 1 (timeDeriv^[n + 1] ρ) :=
      (contDiff_iterate_timeDeriv_infty h.smooth_charge (n + 1)).of_le (by simp)
    have hd := hasDerivAt_integral_weight_mul (w := fun _ => (1 : ℝ)) continuous_const hc
      (h.support_charge.iterate_timeDeriv (n + 1)) s
    have hconst : (fun s => ∫ z, (fun _ : E3 => (1 : ℝ)) z * timeDeriv^[n + 1] ρ (s, z)) =
        fun _ => 0 := funext fun s => by simpa using ih s
    rw [hconst] at hd
    have := hd.unique (hasDerivAt_const s 0)
    rw [Function.iterate_succ_apply']
    simpa using this

/-- The derivative of the dipole moment is the total current: `∫ zᵢ ∂ₛρ = ∫ jᵢ`. -/
theorem dipoleMoment_timeDeriv (h : SlowSource a ρ j) (i : Fin 3) (s : ℝ) :
    dipoleMoment (timeDeriv ρ) i s = ∫ z, j i (s, z) := by
  have hj1 : ∀ k, ContDiff ℝ 1 (j k) := fun k => (h.smooth_current k).of_le (by simp)
  have hw : ContDiff ℝ 1 (fun z : E3 => z i) := (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff
  have he : (fun z : E3 => z i * timeDeriv ρ (s, z)) =
      fun z => -∑ k, z i * spaceDeriv k (j k) (s, z) := by
    funext z
    have hc : timeDeriv ρ (s, z) = -∑ k, spaceDeriv k (j k) (s, z) := by
      linarith [h.continuity (s, z)]
    rw [hc, mul_neg, Finset.mul_sum]
  have hint : ∀ k, Integrable fun z : E3 => z i * spaceDeriv k (j k) (s, z) := fun k =>
    ((continuous_component i).mul ((contDiff_spaceDeriv (n := 0) (by simpa using hj1 k)
      k).continuous.comp (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
      (((h.support_current k).spaceDeriv k).hasCompactSupport_slice s).mul_left
  have hk : ∀ k, ∫ z, z i * spaceDeriv k (j k) (s, z) =
      -(if i = k then ∫ z, j k (s, z) else 0) := by
    intro k
    rw [integral_mul_spaceDeriv hw (hj1 k) (h.support_current k) s k]
    simp only [fderiv_component]
    split_ifs <;> simp
  unfold dipoleMoment
  rw [he, integral_neg, integral_finsetSum _ fun k _ => hint k]
  simp only [hk, Finset.sum_neg_distrib, neg_neg]
  simp

/-- **The third derivative of the dipole moment** of a slow source:
`d⃛ᵢ = ∫ zᵢ ∂ₛ³ρ = ∫ ∂ₛ²jᵢ`. -/
theorem dipoleMoment_iterate_three (h : SlowSource a ρ j) (i : Fin 3) (s : ℝ) :
    dipoleMoment (timeDeriv^[3] ρ) i s = ∫ z, timeDeriv^[2] (j i) (s, z) := by
  have hρ := h.smooth_charge
  have hji := h.smooth_current i
  have hw : Continuous fun z : E3 => z i := continuous_component i
  have h1 : ∀ s, ∫ z, z i * timeDeriv ρ (s, z) =
      ∫ z, (fun _ : E3 => (1 : ℝ)) z * j i (s, z) := fun s => by
    simpa [dipoleMoment] using dipoleMoment_timeDeriv h i s
  have h2 : ∀ s, ∫ z, z i * timeDeriv (timeDeriv ρ) (s, z) =
      ∫ z, (fun _ : E3 => (1 : ℝ)) z * timeDeriv (j i) (s, z) :=
    integral_weight_mul_timeDeriv_eq hw continuous_const
      ((contDiff_infty_timeDeriv hρ).of_le (by simp)) (hji.of_le (by simp))
      h.support_charge.timeDeriv (h.support_current i) h1
  have h3 := integral_weight_mul_timeDeriv_eq hw continuous_const
    ((contDiff_infty_timeDeriv (contDiff_infty_timeDeriv hρ)).of_le (by simp))
    ((contDiff_infty_timeDeriv hji).of_le (by simp)) h.support_charge.timeDeriv.timeDeriv
    (h.support_current i).timeDeriv h2 s
  simpa [dipoleMoment] using h3

/-- **The third term of the slow expansion of the gradient of the scalar potential**: by the
integration by parts `∫ ‖x − z‖² ∂ᵢg = ∫ 2(x − z)ᵢ g` and the conservation of the charge,
`(4π)⁻¹ ∫ ‖y‖² ∂ᵢ∂ₛ³ρ(s, x − y) dy = −2 (4π)⁻¹ d⃛ᵢ(s)` at every point. -/
theorem slowTerm_three_spaceDeriv (h : SlowSource a ρ j) (i : Fin 3) (s : ℝ) (x : E3) :
    slowTerm 3 (spaceDeriv i ρ) s x =
      -(2 * (4 * π)⁻¹) * dipoleMoment (timeDeriv^[3] ρ) i s := by
  have hρ := h.smooth_charge
  have hgc : ContDiff ℝ ∞ (timeDeriv^[3] ρ) := contDiff_iterate_timeDeriv_infty hρ 3
  have hgs : SpatialSupport a (timeDeriv^[3] ρ) := h.support_charge.iterate_timeDeriv 3
  have hcomm : timeDeriv^[3] (spaceDeriv i ρ) = spaceDeriv i (timeDeriv^[3] ρ) :=
    iterate_timeDeriv_spaceDeriv (N := 4) (hρ.of_le (by simp)) i (by norm_num)
  have hker : ∀ y : E3, Potential.newtonKernel y * ‖y‖ ^ 3 = (4 * π)⁻¹ * ‖y‖ ^ 2 := by
    intro y
    rw [pow_succ, ← mul_assoc, newtonKernel_mul_norm_sq]
    ring
  have e1 : slowTerm 3 (spaceDeriv i ρ) s x =
      (4 * π)⁻¹ * ∫ z, ‖x - z‖ ^ 2 * spaceDeriv i (timeDeriv^[3] ρ) (s, z) := by
    rw [slowTerm, hcomm, ← integral_const_mul, ← integral_sub_left_eq_self
      (fun z => (4 * π)⁻¹ * (‖x - z‖ ^ 2 * spaceDeriv i (timeDeriv^[3] ρ) (s, z))) volume x]
    congr 1
    funext y
    simp only [sub_sub_cancel]
    rw [← mul_assoc, hker]
    ring
  have hwc : ContDiff ℝ 1 (fun z : E3 => ‖x - z‖ ^ 2) :=
    (contDiff_const.sub contDiff_id).norm_sq ℝ
  set c : ℝ := x i with hc
  set w : E3 → ℝ := fun z => z i with hw
  have hwd : ∀ z, fderiv ℝ (fun z : E3 => ‖x - z‖ ^ 2) z (EuclideanSpace.single i 1) =
      -(2 * (c - w z)) := by
    intro z
    have hd : HasFDerivAt (fun z : E3 => ‖x - z‖ ^ 2)
        (2 • (innerSL ℝ (x - z)).comp (-ContinuousLinearMap.id ℝ E3)) z :=
      ((hasFDerivAt_id z).const_sub x).norm_sq
    rw [hd.fderiv]
    simp [EuclideanSpace.inner_single_right, hc, hw]
    ring
  have e2 := integral_mul_spaceDeriv hwc (hgc.of_le (by simp)) hgs s i
  simp only [hwd] at e2
  have hgcont : Continuous fun z : E3 => timeDeriv^[3] ρ (s, z) :=
    hgc.continuous.comp (continuous_const.prodMk continuous_id)
  have hint1 : Integrable fun z : E3 => timeDeriv^[3] ρ (s, z) :=
    hgcont.integrable_of_hasCompactSupport (hgs.hasCompactSupport_slice s)
  have hint2 : Integrable fun z : E3 => w z * timeDeriv^[3] ρ (s, z) :=
    ((continuous_component i).mul hgcont).integrable_of_hasCompactSupport
      (hgs.hasCompactSupport_slice s).mul_left
  have h0 : ∫ z, timeDeriv^[3] ρ (s, z) = 0 := integral_iterate_timeDeriv_eq_zero h 2 s
  have e3 : ∫ z, -(2 * (c - w z)) * timeDeriv^[3] ρ (s, z) =
      2 * ∫ z, w z * timeDeriv^[3] ρ (s, z) := by
    have he : (fun z : E3 => -(2 * (c - w z)) * timeDeriv^[3] ρ (s, z)) =
        fun z => -(2 * c) * timeDeriv^[3] ρ (s, z) + 2 * (w z * timeDeriv^[3] ρ (s, z)) := by
      funext z
      ring
    rw [he, integral_add (hint1.const_mul _) (hint2.const_mul _), integral_const_mul,
      integral_const_mul, h0, mul_zero, zero_add]
  rw [e1, e2, e3, dipoleMoment]
  ring

/-! ### The damping field -/

/-- Bounds on the derivatives of a slow source for the expansion of its fields to the third
order: `|∂ₛ⁴∂ᵢρ|`, `|∂ₛ³jᵢ|` and `|∂ₛ²∂ₗjᵢ|` are at most `M`. -/
structure DampingBounds (M : ℝ) (ρ : ℝ × E3 → ℝ) (j : Fin 3 → ℝ × E3 → ℝ) : Prop where
  /-- The fourth time derivatives of the gradient of the charge. -/
  charge : ∀ i p, |timeDeriv^[4] (spaceDeriv i ρ) p| ≤ M
  /-- The third time derivatives of the current. -/
  current : ∀ i p, |timeDeriv^[3] (j i) p| ≤ M
  /-- The second time derivatives of the spatial derivatives of the current. -/
  current_space : ∀ i l p, |timeDeriv^[2] (spaceDeriv l (j i)) p| ≤ M

/-- **The damping field** (Landau–Lifshitz (75.5)): for a slow source with the bounds
`DampingBounds M`, at a point `‖x‖ ≤ R`, the electric field of the retarded potentials is the
field of the potentials of Darwin plus the spatially uniform field `(2/3)(1/4π) κ³ d⃛(κt)`, up to
`(M (R + a)⁶/72 + M (R + a)⁴/6) κ⁴`. The term `κ³` of `−∇φ` is `−(1/3)(1/4π) κ³ d⃛` and that of
`−∂ₜ𝐚` is `(1/4π) κ³ d⃛`; both are independent of the point. The statement is about the field,
which every gauge transformation keeps (`electricOf_gauge`); in the gauge of Landau–Lifshitz
(75.3) the same uniform field is `−∂ₜ` of the potential `𝐀 = −(2/3)(1/4π) κ² d̈(κt)`. -/
theorem dampingField_expansion (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ}
    (hM : DampingBounds M ρ j) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R)
    (i : Fin 3) :
    |electricOf (slowScalar κ ρ) (slowVector κ j) i (t, x) -
        electricOf (darwinScalar κ ρ) (darwinVector κ j) i (t, x) -
        2 / 3 * (4 * π)⁻¹ * κ ^ 3 * deriv^[3] (dipoleMoment ρ i) (κ * t)| ≤
      (M * (R + a) ^ 6 / 72 + M * (R + a) ^ 4 / 6) * κ ^ 4 := by
  have hρ := h.smooth_charge
  have hj := h.smooth_current i
  have hjs := h.support_current i
  rw [iterate_deriv_dipoleMoment hρ h.support_charge, dipoleMoment_iterate_three h]
  set D := ∫ z, timeDeriv^[2] (j i) (κ * t, z) with hD
  -- the gradient of the scalar potential to the third order
  have Hs := retardedIntegral_slow_expansion (n := 3)
    ((contDiff_infty_spaceDeriv hρ i).of_le (by simp)) ha (h.support_charge.spaceDeriv i)
    (hM.charge i) hκ t hx
  have h0 : slowTerm 0 (spaceDeriv i ρ) (κ * t) x = spaceDeriv i (darwinScalar κ ρ) (t, x) := by
    rw [darwinScalar, spaceDeriv_kernelIntegral_slow Potential.locallyIntegrable_newtonKernel
      (hρ.of_le (by simp)) h.support_charge]
    simp [slowTerm, kernelIntegral, slow, smul_eq_mul]
  have h1 : slowTerm 1 (spaceDeriv i ρ) (κ * t) x = 0 := by
    rw [slowTerm_one]
    have he : (fun z => timeDeriv (spaceDeriv i ρ) (κ * t, z)) =
        fun z => spaceDeriv i (timeDeriv ρ) (κ * t, z) :=
      funext fun z => timeDeriv_spaceDeriv (hρ.of_le (by simp)).contDiffAt i
    rw [he, integral_spaceDeriv_eq_zero (contDiff_timeDeriv (n := 1) (hρ.of_le (by simp)))
      h.support_charge.timeDeriv, mul_zero]
  have h2 : κ ^ 2 / 2 * slowTerm 2 (spaceDeriv i ρ) (κ * t) x =
      spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) := by
    rw [slowTerm_two, h.spaceDeriv_timeDeriv_darwinGauge, kernelIntegral,
      iterate_timeDeriv_spaceDeriv (N := 3) (hρ.of_le (by simp)) i (by norm_num)]
    simp only [smul_eq_mul, slow, Prod.mk_sub_mk, sub_zero]
    rw [Function.iterate_succ_apply, Function.iterate_one]
    ring
  have h3 : slowTerm 3 (spaceDeriv i ρ) (κ * t) x = -(2 * (4 * π)⁻¹) * D := by
    rw [slowTerm_three_spaceDeriv h, dipoleMoment_iterate_three h]
  have hsum : ∑ k ∈ Finset.range (3 + 1), (-κ) ^ k / (k.factorial : ℝ) *
      slowTerm k (spaceDeriv i ρ) (κ * t) x =
      spaceDeriv i (darwinScalar κ ρ) (t, x) + spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) +
        κ ^ 3 / 3 * (4 * π)⁻¹ * D := by
    rw [← h0, ← h2]
    simp [Finset.sum_range_succ, h1, h3, Nat.factorial]
    ring
  rw [hsum] at Hs
  -- the time derivative of the vector potential to the third order
  have Hv := retardedIntegral_slow_expansion (n := 1)
    ((contDiff_infty_timeDeriv hj).of_le (by simp)) ha hjs.timeDeriv (hM.current i) hκ t hx
  have v0 : slowTerm 0 (timeDeriv (j i)) (κ * t) x =
      kernelIntegral Potential.newtonKernel (slow κ (timeDeriv (j i))) (t, x) := by
    simp [slowTerm, kernelIntegral, slow, smul_eq_mul]
  have v1 : slowTerm 1 (timeDeriv (j i)) (κ * t) x = (4 * π)⁻¹ * D := by
    rw [slowTerm_one]
    rfl
  have hvsum : ∑ k ∈ Finset.range (1 + 1), (-κ) ^ k / (k.factorial : ℝ) *
      slowTerm k (timeDeriv (j i)) (κ * t) x =
      kernelIntegral Potential.newtonKernel (slow κ (timeDeriv (j i))) (t, x) -
        κ * ((4 * π)⁻¹ * D) := by
    rw [← v0, ← v1]
    simp [Finset.sum_range_succ]
    ring
  rw [hvsum] at Hv
  -- the fields
  have hχ : ContDiff ℝ ∞ (darwinGauge κ ρ) := h.contDiff_darwinGauge κ
  have hR : Differentiable ℝ (retardedIntegral (slow κ (j i))) :=
    (contDiff_retardedIntegral (contDiff_slow hj κ) (hjs.slow κ).subluminalSupport).differentiable
      (by simp)
  have hN : Differentiable ℝ (kernelIntegral Potential.newtonKernel (slow κ (j i))) :=
    (contDiff_kernelIntegral Potential.locallyIntegrable_newtonKernel (contDiff_slow hj κ)
      ((hjs.slow κ).kernelSupport _)).differentiable (by simp)
  have hχi : Differentiable ℝ (spaceDeriv i (darwinGauge κ ρ)) :=
    (contDiff_infty_spaceDeriv hχ i).differentiable (by simp)
  have eS : spaceDeriv i (slowScalar κ ρ) (t, x) =
      retardedIntegral (slow κ (spaceDeriv i ρ)) (t, x) := by
    rw [slowScalar, spaceDeriv_retardedIntegral_slow (hρ.of_le (by simp)) h.support_charge]
  have eV : timeDeriv (slowVector κ j i) (t, x) =
      κ * (κ * retardedIntegral (slow κ (timeDeriv (j i))) (t, x)) := by
    rw [SlowSource.slowVector_eq, timeDeriv_const_mul (hR _),
      timeDeriv_retardedIntegral_slow (hj.of_le (by simp)) hjs]
  have eD : timeDeriv (darwinVector κ j i) (t, x) =
      κ * (κ * kernelIntegral Potential.newtonKernel (slow κ (timeDeriv (j i))) (t, x)) +
        spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x) := by
    rw [show darwinVector κ j i = fun p => κ * kernelIntegral Potential.newtonKernel
        (slow κ (j i)) p + spaceDeriv i (darwinGauge κ ρ) p from funext (h.darwinVector_eq κ i),
      timeDeriv_fun_add ((hN _).const_mul κ) (hχi _), timeDeriv_const_mul (hN _),
      timeDeriv_kernelIntegral_slow Potential.locallyIntegrable_newtonKernel (hj.of_le (by simp))
        hjs, timeDeriv_spaceDeriv (hχ.of_le (by simp)).contDiffAt i]
  simp only [electricOf]
  rw [eS, eV, eD]
  set A := retardedIntegral (slow κ (spaceDeriv i ρ)) (t, x)
  set B := retardedIntegral (slow κ (timeDeriv (j i))) (t, x)
  set φ' := spaceDeriv i (darwinScalar κ ρ) (t, x)
  set χ' := spaceDeriv i (timeDeriv (darwinGauge κ ρ)) (t, x)
  set N := kernelIntegral Potential.newtonKernel (slow κ (timeDeriv (j i))) (t, x)
  have key : -A - κ * (κ * B) - (-φ' - (κ * (κ * N) + χ')) - 2 / 3 * (4 * π)⁻¹ * κ ^ 3 * D =
      -(A - (φ' + χ' + κ ^ 3 / 3 * (4 * π)⁻¹ * D)) - κ ^ 2 * (B - (N - κ * ((4 * π)⁻¹ * D))) := by
    ring
  rw [key]
  have hb1 : M * (R + a) ^ (3 + 3) / (3 * ((3 + 1).factorial : ℝ)) * κ ^ (3 + 1) =
      M * (R + a) ^ 6 / 72 * κ ^ 4 := by
    norm_num [Nat.factorial]
  have hb2 : M * (R + a) ^ (1 + 3) / (3 * ((1 + 1).factorial : ℝ)) * κ ^ (1 + 1) =
      M * (R + a) ^ 4 / 6 * κ ^ 2 := by
    norm_num [Nat.factorial]
  rw [hb1] at Hs
  rw [hb2] at Hv
  have hκ2 : 0 ≤ κ ^ 2 := by positivity
  calc |-(A - (φ' + χ' + κ ^ 3 / 3 * (4 * π)⁻¹ * D)) - κ ^ 2 * (B - (N - κ * ((4 * π)⁻¹ * D)))|
      ≤ |A - (φ' + χ' + κ ^ 3 / 3 * (4 * π)⁻¹ * D)| +
          κ ^ 2 * |B - (N - κ * ((4 * π)⁻¹ * D))| := by
        rw [← abs_of_nonneg hκ2, ← abs_mul, abs_of_nonneg hκ2]
        have := abs_sub (-(A - (φ' + χ' + κ ^ 3 / 3 * (4 * π)⁻¹ * D)))
          (κ ^ 2 * (B - (N - κ * ((4 * π)⁻¹ * D))))
        rwa [abs_neg] at this
    _ ≤ M * (R + a) ^ 6 / 72 * κ ^ 4 + κ ^ 2 * (M * (R + a) ^ 4 / 6 * κ ^ 2) := by
        gcongr
    _ = (M * (R + a) ^ 6 / 72 + M * (R + a) ^ 4 / 6) * κ ^ 4 := by ring

/-- **The spatial derivatives of the vector potential to the third order**: with
`|∂ₛ²∂ₗjₖ| ≤ M`, at `‖x‖ ≤ R`, `|∂ₗaₖ − ∂ₗa'ₖ + ∂ₗ∂ₖχ| ≤ M (R + a)⁴ κ³/6`; the term of the first
order `−κ² (4π)⁻¹ ∫ ∂ₛ∂ₗjₖ` vanishes, so the magnetic field of Darwin is exact to `O(κ³)`. -/
theorem spaceDeriv_vector_sub_cubic (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ} (k l : Fin 3)
    (hM : ∀ p, |timeDeriv^[2] (spaceDeriv l (j k)) p| ≤ M) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ)
    {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R) :
    |spaceDeriv l (slowVector κ j k) (t, x) - spaceDeriv l (darwinVector κ j k) (t, x) +
        spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x)| ≤ M * (R + a) ^ 4 / 6 * κ ^ 3 := by
  have hj : ContDiff ℝ ∞ (j k) := h.smooth_current k
  have hjs : SpatialSupport a (j k) := h.support_current k
  have hχ : ContDiff ℝ ∞ (darwinGauge κ ρ) := h.contDiff_darwinGauge κ
  have hR : Differentiable ℝ (retardedIntegral (slow κ (j k))) :=
    (contDiff_retardedIntegral (contDiff_slow hj κ) (hjs.slow κ).subluminalSupport).differentiable
      (by simp)
  have hN : Differentiable ℝ (kernelIntegral Potential.newtonKernel (slow κ (j k))) :=
    (contDiff_kernelIntegral Potential.locallyIntegrable_newtonKernel (contDiff_slow hj κ)
      ((hjs.slow κ).kernelSupport _)).differentiable (by simp)
  have hχk : Differentiable ℝ (spaceDeriv k (darwinGauge κ ρ)) :=
    (contDiff_infty_spaceDeriv hχ k).differentiable (by simp)
  have e1 : spaceDeriv l (slowVector κ j k) (t, x) =
      κ * retardedIntegral (slow κ (spaceDeriv l (j k))) (t, x) := by
    rw [SlowSource.slowVector_eq, spaceDeriv_const_mul (hR _),
      spaceDeriv_retardedIntegral_slow (hj.of_le (by simp)) hjs]
  have e2 : spaceDeriv l (darwinVector κ j k) (t, x) =
      κ * kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x) +
        spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x) := by
    rw [show darwinVector κ j k = fun p => κ * kernelIntegral Potential.newtonKernel
        (slow κ (j k)) p + spaceDeriv k (darwinGauge κ ρ) p from funext (h.darwinVector_eq κ k),
      spaceDeriv_fun_add ((hN _).const_mul κ) (hχk _), spaceDeriv_const_mul (hN _),
      spaceDeriv_kernelIntegral_slow Potential.locallyIntegrable_newtonKernel
        (hj.of_le (by simp)) hjs]
  have H := retardedIntegral_slow_expansion (n := 1)
    ((contDiff_infty_spaceDeriv hj l).of_le (by simp)) ha (hjs.spaceDeriv l) hM hκ t hx
  have v0 : slowTerm 0 (spaceDeriv l (j k)) (κ * t) x =
      kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x) := by
    simp [slowTerm, kernelIntegral, slow, smul_eq_mul]
  have v1 : slowTerm 1 (spaceDeriv l (j k)) (κ * t) x = 0 := by
    rw [slowTerm_one]
    have he : (fun z => timeDeriv (spaceDeriv l (j k)) (κ * t, z)) =
        fun z => spaceDeriv l (timeDeriv (j k)) (κ * t, z) :=
      funext fun z => timeDeriv_spaceDeriv (hj.of_le (by simp)).contDiffAt l
    rw [he, integral_spaceDeriv_eq_zero (contDiff_timeDeriv (n := 1) (hj.of_le (by simp)))
      hjs.timeDeriv, mul_zero]
  have hs : ∑ m ∈ Finset.range (1 + 1), (-κ) ^ m / (m.factorial : ℝ) *
      slowTerm m (spaceDeriv l (j k)) (κ * t) x =
      kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x) := by
    rw [← v0]
    simp [Finset.sum_range_succ, v1]
  rw [hs] at H
  have hb : M * (R + a) ^ (1 + 3) / (3 * ((1 + 1).factorial : ℝ)) * κ ^ (1 + 1) =
      M * (R + a) ^ 4 / 6 * κ ^ 2 := by
    norm_num [Nat.factorial]
  rw [hb] at H
  rw [e1, e2]
  have he : κ * retardedIntegral (slow κ (spaceDeriv l (j k))) (t, x) -
      (κ * kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x) +
        spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x)) +
      spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x) =
      κ * (retardedIntegral (slow κ (spaceDeriv l (j k))) (t, x) -
        kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x)) := by ring
  rw [he, abs_mul, abs_of_nonneg hκ]
  calc κ * |retardedIntegral (slow κ (spaceDeriv l (j k))) (t, x) -
        kernelIntegral Potential.newtonKernel (slow κ (spaceDeriv l (j k))) (t, x)|
      ≤ κ * (M * (R + a) ^ 4 / 6 * κ ^ 2) := mul_le_mul_of_nonneg_left H hκ
    _ = M * (R + a) ^ 4 / 6 * κ ^ 3 := by ring

/-- **The Lorentz density to the third order**: for a slow source with the bounds
`DampingBounds M`, at `‖x‖ ≤ R` and a velocity `‖𝐯‖ ≤ Vκ`, the density `E + 𝐯 × B` of the
retarded field is that of the potentials of Darwin plus the damping field
`(2/3)(1/4π) κ³ d⃛(κt)`, up to `(M (R + a)⁶/72 + M (R + a)⁴/6 + V M (R + a)⁴) κ⁴`. -/
theorem lorentzDensity_expansion (h : SlowSource a ρ j) (ha : 0 ≤ a) {M : ℝ}
    (hM : DampingBounds M ρ j) {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) {x : E3} {R : ℝ} (hx : ‖x‖ ≤ R)
    {v : E3} {V : ℝ} (hv : ‖v‖ ≤ V * κ) (i : Fin 3) :
    |lorentzDensity (slowScalar κ ρ) (slowVector κ j) v i (t, x) -
        lorentzDensity (darwinScalar κ ρ) (darwinVector κ j) v i (t, x) -
        2 / 3 * (4 * π)⁻¹ * κ ^ 3 * deriv^[3] (dipoleMoment ρ i) (κ * t)| ≤
      (M * (R + a) ^ 6 / 72 + M * (R + a) ^ 4 / 6 + V * (M * (R + a) ^ 4)) * κ ^ 4 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM.current i (t, x))
  set e1 := electricOf (slowScalar κ ρ) (slowVector κ j) i (t, x) -
    electricOf (darwinScalar κ ρ) (darwinVector κ j) i (t, x) -
    2 / 3 * (4 * π)⁻¹ * κ ^ 3 * deriv^[3] (dipoleMoment ρ i) (κ * t) with he1
  set m : Fin 3 → Fin 3 → ℝ := fun l k => spaceDeriv l (slowVector κ j k) (t, x) -
    spaceDeriv l (darwinVector κ j k) (t, x) + spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x)
    with hm
  have hsym : ∀ l k, spaceDeriv l (spaceDeriv k (darwinGauge κ ρ)) (t, x) =
      spaceDeriv k (spaceDeriv l (darwinGauge κ ρ)) (t, x) := fun l k =>
    spaceDeriv_spaceDeriv_comm ((h.contDiff_darwinGauge κ).of_le (by simp)).contDiffAt l k
  have hid : lorentzDensity (slowScalar κ ρ) (slowVector κ j) v i (t, x) -
      lorentzDensity (darwinScalar κ ρ) (darwinVector κ j) v i (t, x) -
      2 / 3 * (4 * π)⁻¹ * κ ^ 3 * deriv^[3] (dipoleMoment ρ i) (κ * t) =
      e1 + ∑ k, v k * (m i k - m k i) := by
    rw [lorentzDensity, lorentzDensity, crossProduct_magneticOf, crossProduct_magneticOf]
    have hk : ∀ k, v k * (m i k - m k i) =
        v k * (spaceDeriv i (slowVector κ j k) (t, x) - spaceDeriv k (slowVector κ j i) (t, x)) -
        v k * (spaceDeriv i (darwinVector κ j k) (t, x) -
          spaceDeriv k (darwinVector κ j i) (t, x)) := fun k => by
      simp only [hm]
      rw [hsym i k]
      ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_sub_distrib, he1]
    ring
  have hb1 := dampingField_expansion h ha hM hκ t hx i
  have hbm : ∀ l k, |m l k| ≤ M * (R + a) ^ 4 / 6 * κ ^ 3 := fun l k =>
    spaceDeriv_vector_sub_cubic h ha k l (hM.current_space k l) hκ t hx
  have hvk : ∀ k, |v k| ≤ V * κ := fun k =>
    (by simpa using PiLp.norm_apply_le v k : |v k| ≤ ‖v‖).trans hv
  have hsum : |∑ k, v k * (m i k - m k i)| ≤ V * (M * (R + a) ^ 4) * κ ^ 4 := by
    have hC : 0 ≤ M * (R + a) ^ 4 / 6 * κ ^ 3 := by
      have : 0 ≤ R + a := by linarith [norm_nonneg x]
      positivity
    calc |∑ k, v k * (m i k - m k i)| ≤ ∑ k, |v k * (m i k - m k i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3, V * κ * (2 * (M * (R + a) ^ 4 / 6 * κ ^ 3)) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [abs_mul]
          refine mul_le_mul (hvk k) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hvk k))
          linarith [abs_sub (m i k) (m k i), hbm i k, hbm k i]
      _ = V * (M * (R + a) ^ 4) * κ ^ 4 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  rw [hid]
  calc |e1 + ∑ k, v k * (m i k - m k i)| ≤ |e1| + |∑ k, v k * (m i k - m k i)| :=
        abs_add_le _ _
    _ ≤ (M * (R + a) ^ 6 / 72 + M * (R + a) ^ 4 / 6) * κ ^ 4 + V * (M * (R + a) ^ 4) * κ ^ 4 := by
        gcongr
    _ = _ := by ring

/-! ### Parity about a moving centre -/

/-- `F(s, c(s) − y) = σ F(s, c(s) + y)` for all `s` and `y`: the function is even (`σ = 1`) or odd
(`σ = −1`) about the moving centre `c(s)`. -/
def ReflectsAbout (c : ℝ → E3) (σ : ℝ) (F : ℝ × E3 → ℝ) : Prop :=
  ∀ s y, F (s, c s - y) = σ * F (s, c s + y)

/-- The derivative along the line `λ ↦ (s, z + αλ eₘ)` is `α ∂ₘG(s, z)`. -/
theorem hasDerivAt_spaceLine {G : ℝ × E3 → ℝ} {s : ℝ} {z : E3}
    (hG : DifferentiableAt ℝ G (s, z)) (m : Fin 3) (α : ℝ) :
    HasDerivAt (fun l : ℝ => G (s, z + (α * l) • EuclideanSpace.single m 1))
      (α * spaceDeriv m G (s, z)) 0 := by
  have hp : HasDerivAt (fun l : ℝ => ((s, z + (α * l) • (EuclideanSpace.single m 1 : E3)) :
      ℝ × E3)) ((0 : ℝ), α • (EuclideanSpace.single m 1 : E3)) 0 := by
    refine (hasDerivAt_const 0 s).prodMk ?_
    have := (((hasDerivAt_id' (0 : ℝ)).const_mul α).smul_const
      (EuclideanSpace.single m 1 : E3)).const_add z
    simpa using this
  have h2 := hG.hasFDerivAt.comp_hasDerivAt_of_eq 0 hp (by simp)
  have he : fderiv ℝ G (s, z) ((0 : ℝ), α • (EuclideanSpace.single m 1 : E3)) =
      α * spaceDeriv m G (s, z) := by
    rw [spaceDeriv, ← smul_eq_mul, ← map_smul]
    simp
  rw [← he]
  exact h2

namespace ReflectsAbout

variable {c : ℝ → E3} {σ : ℝ} {F G : ℝ × E3 → ℝ}

theorem add (hF : ReflectsAbout c σ F) (hG : ReflectsAbout c σ G) :
    ReflectsAbout c σ (fun p => F p + G p) := fun s y => by
  simp only [hF s y, hG s y]
  ring

theorem neg (hF : ReflectsAbout c σ F) : ReflectsAbout c σ (fun p => -F p) := fun s y => by
  simp only [hF s y]
  ring

theorem sub (hF : ReflectsAbout c σ F) (hG : ReflectsAbout c σ G) :
    ReflectsAbout c σ (fun p => F p - G p) := fun s y => by
  simp only [hF s y, hG s y]
  ring

theorem mul_left (g : ℝ → ℝ) (hF : ReflectsAbout c σ F) :
    ReflectsAbout c σ (fun p => g p.1 * F p) := fun s y => by
  simp only [hF s y]
  ring

theorem const_mul (r : ℝ) (hF : ReflectsAbout c σ F) :
    ReflectsAbout c σ (fun p => r * F p) := hF.mul_left fun _ => r

theorem sum {ι : Type*} (S : Finset ι) {F : ι → ℝ × E3 → ℝ}
    (hF : ∀ k ∈ S, ReflectsAbout c σ (F k)) :
    ReflectsAbout c σ (fun p => ∑ k ∈ S, F k p) := fun s y => by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k hk => hF k hk s y

/-- The slow rescaling moves the centre to `c(κt)`. -/
theorem rescale (hF : ReflectsAbout c σ F) (κ : ℝ) :
    ReflectsAbout (fun t => c (κ * t)) σ (slow κ F) := fun t y => hF (κ * t) y

/-- An even kernel keeps the parity about the centre. -/
theorem kernel {K : E3 → ℝ} (hK : ∀ y, K (-y) = K y) (hF : ReflectsAbout c σ F) :
    ReflectsAbout c σ (kernelIntegral K F) := fun s y => by
  simp only [kernelIntegral, smul_eq_mul, Prod.mk_sub_mk, sub_zero]
  rw [← integral_neg_eq_self (fun w => K w * F (s, c s + y - w)), ← integral_const_mul]
  congr 1
  funext w
  rw [show c s - y - w = c s - (y + w) by abel, hF s (y + w), hK,
    show c s + y - -w = c s + (y + w) by abel]
  ring

/-- A spatial derivative reverses the parity. -/
theorem gradient (hG : Differentiable ℝ G) (h : ReflectsAbout c σ G) (m : Fin 3) :
    ReflectsAbout c (-σ) (spaceDeriv m G) := fun s y => by
  have h1 := hasDerivAt_spaceLine (hG (s, c s - y)) m 1
  have h2 := (hasDerivAt_spaceLine (hG (s, c s + y)) m (-1)).const_mul σ
  have he : (fun l : ℝ => G (s, c s - y + (1 * l) • EuclideanSpace.single m 1)) =
      fun l => σ * G (s, c s + y + (-1 * l) • EuclideanSpace.single m 1) := by
    funext l
    rw [show c s - y + (1 * l) • (EuclideanSpace.single m 1 : E3) =
        c s - (y - l • EuclideanSpace.single m 1) by module, h s,
      show c s + (y - l • (EuclideanSpace.single m 1 : E3)) =
        c s + y + (-1 * l) • EuclideanSpace.single m 1 by module]
  rw [he] at h1
  linear_combination h1.unique h2

end ReflectsAbout

/-- **The average of an odd function over an even distribution vanishes**: if `ρ₀` is even and
`H(c − y) = −H(c + y)`, then `∫ ρ₀(x − c) H(x) dx = 0`. -/
theorem integral_mul_eq_zero_of_odd {ρ₀ : E3 → ℝ} (hρ₀ : ∀ y, ρ₀ (-y) = ρ₀ y) {H : E3 → ℝ}
    {c : E3} (hH : ∀ y, H (c - y) = -H (c + y)) : ∫ x, ρ₀ (x - c) * H x = 0 := by
  have h1 : ∫ x, ρ₀ (x - c) * H x = ∫ y, ρ₀ y * H (c + y) := by
    rw [← integral_add_right_eq_self (fun x => ρ₀ (x - c) * H x) c]
    congr 1
    funext y
    rw [add_sub_cancel_right, add_comm]
  have h2 : ∫ y, ρ₀ y * H (c + y) = -∫ y, ρ₀ y * H (c + y) := by
    rw [← integral_neg, ← integral_neg_eq_self (fun y => ρ₀ y * H (c + y))]
    congr 1
    funext y
    rw [hρ₀, show c + -y = c - y by abel, hH]
    ring
  linarith

/-! ### A rigid charge on a prescribed slow path -/

/-- The time derivative of a profile carried along a path: `∂ₛ G(z − c(s)) = −dG(z − c(s)) ċ(s)`.
-/
theorem timeDeriv_comp_sub_path {G : E3 → ℝ} (hG : Differentiable ℝ G) {c : ℝ → E3}
    (hc : Differentiable ℝ c) (s : ℝ) (z : E3) :
    timeDeriv (fun p : ℝ × E3 => G (p.2 - c p.1)) (s, z) = -fderiv ℝ G (z - c s) (deriv c s) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × E3 => G (p.2 - c p.1)) (s, z) :=
    (hG _).comp (s, z) (differentiableAt_snd.sub ((hc _).comp (s, z) differentiableAt_fst))
  refine timeDeriv_eq_of_hasDerivAt hd ?_
  have hl : HasDerivAt (fun s' => z - c s') (-deriv c s) s :=
    ((hasDerivAt_const s z).sub (hc s).hasDerivAt).congr_deriv (by simp)
  have := (hG (z - c s)).hasFDerivAt.comp_hasDerivAt s hl
  rw [map_neg] at this
  exact this

/-- The spatial derivative of a profile carried along a path: `∂ₘ G(z − c(s)) = ∂ₘG(z − c(s))`.
-/
theorem spaceDeriv_comp_sub_path {G : E3 → ℝ} (hG : Differentiable ℝ G) {c : ℝ → E3}
    (hc : Differentiable ℝ c) (s : ℝ) (z : E3) (m : Fin 3) :
    spaceDeriv m (fun p : ℝ × E3 => G (p.2 - c p.1)) (s, z) =
      fderiv ℝ G (z - c s) (EuclideanSpace.single m 1) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × E3 => G (p.2 - c p.1)) (s, z) :=
    (hG _).comp (s, z) (differentiableAt_snd.sub ((hc _).comp (s, z) differentiableAt_fst))
  refine spaceDeriv_eq_of_hasDerivAt hd m ?_
  have hl : HasDerivAt (fun l : ℝ => z + l • (EuclideanSpace.single m 1 : E3) - c s)
      (EuclideanSpace.single m 1) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).smul_const (EuclideanSpace.single m 1 : E3)).const_add
      z).sub_const (c s)
    simpa using this
  have := (hG (z - c s)).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl (by simp)
  have he : (fun l : ℝ => (fun p : ℝ × E3 => G (p.2 - c p.1))
      (s, z + l • EuclideanSpace.single m 1)) =
      G ∘ fun l : ℝ => z + l • (EuclideanSpace.single m 1 : E3) - c s := by
    funext l
    simp only [Function.comp_apply]
  rw [he]
  exact this

/-- The spatial derivative of a product with a function of time. -/
theorem spaceDeriv_mul_time {g : ℝ → ℝ} {F : ℝ × E3 → ℝ} (hg : Differentiable ℝ g)
    (hF : Differentiable ℝ F) (m : Fin 3) (p : ℝ × E3) :
    spaceDeriv m (fun q => g q.1 * F q) p = g p.1 * spaceDeriv m F p := by
  have h : HasFDerivAt (fun q : ℝ × E3 => g q.1 * F q) (g p.1 • fderiv ℝ F p +
      F p • (fderiv ℝ g p.1).comp (ContinuousLinearMap.fst ℝ ℝ E3)) p :=
    ((hg p.1).hasFDerivAt.comp p hasFDerivAt_fst).mul (hF p).hasFDerivAt
  rw [spaceDeriv, h.fderiv, spaceDeriv]
  simp

/-- The time derivative of a product with a function of time. -/
theorem timeDeriv_mul_time {g : ℝ → ℝ} {F : ℝ × E3 → ℝ} (hg : Differentiable ℝ g)
    (hF : Differentiable ℝ F) (p : ℝ × E3) :
    timeDeriv (fun q => g q.1 * F q) p = deriv g p.1 * F p + g p.1 * timeDeriv F p := by
  have h : HasFDerivAt (fun q : ℝ × E3 => g q.1 * F q) (g p.1 • fderiv ℝ F p +
      F p • (fderiv ℝ g p.1).comp (ContinuousLinearMap.fst ℝ ℝ E3)) p :=
    ((hg p.1).hasFDerivAt.comp p hasFDerivAt_fst).mul (hF p).hasFDerivAt
  rw [timeDeriv, h.fderiv, timeDeriv]
  simp
  ring

/-- A linear form on `ℝ³` in components: `ℓ(w) = Σₖ wₖ ℓ(eₖ)`. -/
theorem clm_apply_eq_sum (ℓ : E3 →L[ℝ] ℝ) (w : E3) :
    ℓ w = ∑ k, w k * ℓ (EuclideanSpace.single k 1) := by
  have h := clm_apply_one_vec (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ E3)) w
  simpa using h

/-- The component `ṙₖ(s)` of the velocity of a path, as a real function. -/
def pathVelocity (R : ℝ → E3) (k : Fin 3) (s : ℝ) : ℝ := deriv R s k

theorem contDiff_pathVelocity {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) (k : Fin 3) :
    ContDiff ℝ ∞ (pathVelocity R k) :=
  (EuclideanSpace.proj k : E3 →L[ℝ] ℝ).contDiff.comp (contDiff_infty_iff_deriv.mp hR).2

theorem deriv_pathVelocity {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) (k : Fin 3) (s : ℝ) :
    deriv (pathVelocity R k) s = deriv (deriv R) s k := by
  have hd : Differentiable ℝ (deriv R) := (contDiff_infty_iff_deriv.mp
    (contDiff_infty_iff_deriv.mp hR).2).1
  exact (hasDerivAt_component_path (hd s).hasDerivAt k).deriv

/-- The current of a rigid charge is its charge times the velocity. -/
theorem rigidCurrent_eq_mul (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (k : Fin 3) :
    rigidCurrent e η R k = fun p => pathVelocity R k p.1 * rigidCharge e η R p := by
  funext p
  simp only [rigidCurrent, rigidCharge, pathVelocity]
  ring

section Rigid

variable {e : ℝ} {η : E3 → ℝ} {R : ℝ → E3}

theorem contDiff_rigidCharge (hη : ContDiff ℝ ∞ η) (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (rigidCharge e η R) :=
  contDiff_const.mul (hη.comp (contDiff_snd.sub (hR.comp contDiff_fst)))

theorem spaceDeriv_rigidCharge (hη : ContDiff ℝ ∞ η) (hR : ContDiff ℝ ∞ R) (m : Fin 3) (s : ℝ)
    (z : E3) :
    spaceDeriv m (rigidCharge e η R) (s, z) =
      e * fderiv ℝ η (z - R s) (EuclideanSpace.single m 1) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × E3 => η (p.2 - R p.1)) (s, z) :=
    (hη.differentiable (by simp) _).comp (s, z) (differentiableAt_snd.sub
      ((hR.differentiable (by simp) _).comp (s, z) differentiableAt_fst))
  rw [show rigidCharge e η R = fun p => e * η (p.2 - R p.1) from rfl,
    spaceDeriv_const_mul hd, spaceDeriv_comp_sub_path (hη.differentiable (by simp))
      (hR.differentiable (by simp))]

theorem timeDeriv_rigidCharge (hη : ContDiff ℝ ∞ η) (hR : ContDiff ℝ ∞ R) (s : ℝ) (z : E3) :
    timeDeriv (rigidCharge e η R) (s, z) = -(e * fderiv ℝ η (z - R s) (deriv R s)) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × E3 => η (p.2 - R p.1)) (s, z) :=
    (hη.differentiable (by simp) _).comp (s, z) (differentiableAt_snd.sub
      ((hR.differentiable (by simp) _).comp (s, z) differentiableAt_fst))
  rw [show rigidCharge e η R = fun p => e * η (p.2 - R p.1) from rfl,
    timeDeriv_const_mul hd, timeDeriv_comp_sub_path (hη.differentiable (by simp))
      (hR.differentiable (by simp)), mul_neg]

/-- **A rigid charge is a slow source**: a smooth profile `η` vanishing outside `‖z‖ ≤ b`, carried
along a smooth path with `‖R(s)‖ ≤ L`, gives the conserved source `(eη(x − R), eṘη(x − R))`
supported in the ball of radius `L + b`. -/
theorem slowSource_rigid (e : ℝ) (hη : ContDiff ℝ ∞ η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hR : ContDiff ℝ ∞ R) {L : ℝ} (hL : ∀ s, ‖R s‖ ≤ L) :
    SlowSource (L + b) (rigidCharge e η R) (rigidCurrent e η R) where
  smooth_charge := contDiff_rigidCharge hη hR
  smooth_current k := by
    rw [rigidCurrent_eq_mul]
    exact ((contDiff_pathVelocity hR k).comp contDiff_fst).mul (contDiff_rigidCharge hη hR)
  support_charge := fun p hp => by
    have h1 : b < ‖p.2 - R p.1‖ := by
      have := norm_le_norm_add_norm_sub' p.2 (R p.1)
      linarith [hL p.1]
    simp [rigidCharge, hb _ h1]
  support_current k := fun p hp => by
    have h1 : b < ‖p.2 - R p.1‖ := by
      have := norm_le_norm_add_norm_sub' p.2 (R p.1)
      linarith [hL p.1]
    simp [rigidCurrent, hb _ h1]
  continuity := fun p => by
    obtain ⟨s, z⟩ := p
    have hρd : Differentiable ℝ (rigidCharge e η R) :=
      (contDiff_rigidCharge hη hR).differentiable (by simp)
    have hk : ∀ k, spaceDeriv k (rigidCurrent e η R k) (s, z) =
        deriv R s k * (e * fderiv ℝ η (z - R s) (EuclideanSpace.single k 1)) := fun k => by
      rw [rigidCurrent_eq_mul, spaceDeriv_mul_time ((contDiff_pathVelocity hR k).differentiable
        (by simp)) hρd, spaceDeriv_rigidCharge hη hR]
      rfl
    rw [timeDeriv_rigidCharge hη hR, Finset.sum_congr rfl fun k _ => hk k,
      clm_apply_eq_sum (fderiv ℝ η (z - R s)) (deriv R s), Finset.mul_sum, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    ring

/-- The rigid charge of an even profile is even about the path. -/
theorem reflectsAbout_rigidCharge (hηe : ∀ z, η (-z) = η z) :
    ReflectsAbout R 1 (rigidCharge e η R) := fun s y => by
  simp [rigidCharge, hηe]

theorem reflectsAbout_rigidCurrent (hηe : ∀ z, η (-z) = η z) (k : Fin 3) :
    ReflectsAbout R 1 (rigidCurrent e η R k) := by
  rw [rigidCurrent_eq_mul]
  exact (reflectsAbout_rigidCharge hηe).mul_left _

/-- The time derivative of the rigid charge of an even profile is odd about the path, by the
equation of continuity. -/
theorem reflectsAbout_timeDeriv_rigidCharge (hη : ContDiff ℝ ∞ η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hηe : ∀ z, η (-z) = η z) (hR : ContDiff ℝ ∞ R)
    {L : ℝ} (hL : ∀ s, ‖R s‖ ≤ L) :
    ReflectsAbout R (-1) (timeDeriv (rigidCharge e η R)) := by
  have h := slowSource_rigid e hη hb hR hL
  have he : timeDeriv (rigidCharge e η R) =
      fun p => -∑ k, spaceDeriv k (rigidCurrent e η R k) p := by
    funext p
    linarith [h.continuity p]
  rw [he]
  refine (ReflectsAbout.sum _ fun k _ => ?_).neg
  exact (reflectsAbout_rigidCurrent hηe k).gradient
    ((h.smooth_current k).differentiable (by simp)) k

end Rigid

/-! ### The self-force of the potentials of Darwin -/

/-- The Newton kernel is even. -/
theorem newtonKernel_neg (y : E3) : Potential.newtonKernel (-y) = Potential.newtonKernel y := by
  simp [Potential.newtonKernel]

/-- The kernel of Darwin is even. -/
theorem darwinKernel_neg (i k : Fin 3) (y : E3) : darwinKernel i k (-y) = darwinKernel i k y := by
  simp [darwinKernel]

/-- **The electromagnetic mass tensor** of a rigid charge `eη`:
`δmᵢₖ = e² ∫∫ η(x) η(z) (δᵢₖ + nᵢnₖ)/(8π‖x − z‖) dx dz`, the kernel of Darwin (65.6) averaged
over the charge. -/
def selfMass (e : ℝ) (η : E3 → ℝ) (i k : Fin 3) : ℝ :=
  e ^ 2 * ∫ x, η x * ∫ y, darwinKernel i k y * η (x - y)

/-- The electrostatic self-energy `U = (e²/2) ∫∫ η(x) η(z)/(4π‖x − z‖) dx dz` of a rigid charge. -/
def selfEnergy (e : ℝ) (η : E3 → ℝ) : ℝ :=
  e ^ 2 / 2 * ∫ x, η x * ∫ y, Potential.newtonKernel y * η (x - y)

/-- The average over the charge of a kernel integral of the charge does not depend on the
position: it is `e² ∫ η(x) ∫ K(y) η(x − y) dy dx`. -/
theorem integral_rigid_mul_kernelIntegral (e : ℝ) (η : E3 → ℝ) (R : ℝ → E3) (K : E3 → ℝ)
    (κ t : ℝ) :
    ∫ x, e * η (x - R (κ * t)) * kernelIntegral K (slow κ (rigidCharge e η R)) (t, x) =
      e ^ 2 * ∫ x, η x * ∫ y, K y * η (x - y) := by
  rw [← integral_add_right_eq_self _ (R (κ * t)), ← integral_const_mul]
  congr 1
  funext x
  simp only [kernelIntegral, slow, rigidCharge, smul_eq_mul, Prod.mk_sub_mk, sub_zero,
    add_sub_cancel_right]
  have hx : ∀ y, x + R (κ * t) - y - R (κ * t) = x - y := fun y => by abel
  simp only [hx]
  have he : (fun y => K y * (e * η (x - y))) = fun y => e * (K y * η (x - y)) := by
    funext y
    ring
  rw [he, integral_const_mul]
  ring

/-- The kernel integral of a combination `f(s) F + g(s) G` with coefficients depending on time. -/
theorem kernelIntegral_slow_mul_add {K : E3 → ℝ} (hK : LocallyIntegrable K) {F G : ℝ × E3 → ℝ}
    (hF : Continuous F) (hG : Continuous G) {a : ℝ} (hFs : SpatialSupport a F)
    (hGs : SpatialSupport a G) (f g : ℝ → ℝ) (κ t : ℝ) (x : E3) :
    kernelIntegral K (slow κ (fun q => f q.1 * F q + g q.1 * G q)) (t, x) =
      f (κ * t) * kernelIntegral K (slow κ F) (t, x) +
        g (κ * t) * kernelIntegral K (slow κ G) (t, x) := by
  have cF : Continuous (slow κ F) := by
    rw [slow_eq_comp]
    exact hF.comp (slowMap κ).continuous
  have cG : Continuous (slow κ G) := by
    rw [slow_eq_comp]
    exact hG.comp (slowMap κ).continuous
  have iF := ((hFs.slow κ).kernelSupport K).integrable hK cF (t, x)
  have iG := ((hGs.slow κ).kernelSupport K).integrable hK cG (t, x)
  simp only [kernelIntegral]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iF.const_mul _) (iG.const_mul _)]
  congr 1
  funext y
  simp only [slow, smul_eq_mul, Prod.mk_sub_mk, sub_zero]
  ring

/-- The time derivative of the vector potential of Darwin is the potential of `∂ₛ𝐣`. -/
theorem timeDeriv_darwinVector (h : SlowSource a ρ j) (κ : ℝ) (i : Fin 3) (p : ℝ × E3) :
    timeDeriv (darwinVector κ j i) p =
      κ * ∑ k, κ * kernelIntegral (darwinKernel i k) (slow κ (timeDeriv (j k))) p := by
  have hd : ∀ k, Differentiable ℝ (kernelIntegral (darwinKernel i k) (slow κ (j k))) := fun k =>
    (contDiff_kernelIntegral (locallyIntegrable_darwinKernel i k)
      (contDiff_slow (h.smooth_current k) κ)
      (((h.support_current k).slow κ).kernelSupport _)).differentiable (by simp)
  change timeDeriv (fun p => κ * ∑ k, kernelIntegral (darwinKernel i k) (slow κ (j k)) p) p = _
  rw [timeDeriv_const_mul ((Differentiable.fun_sum fun k _ => hd k) p),
    timeDeriv_fun_sum _ (fun k _ => hd k p)]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [timeDeriv_kernelIntegral_slow (locallyIntegrable_darwinKernel i k)
    ((h.smooth_current k).of_le (by simp)) (h.support_current k)]

/-- **The self-force of a rigid charge in its own potentials of Darwin** (Landau–Lifshitz §75,
the term of the order `1/c²`): for an even smooth profile `η` vanishing outside `‖z‖ ≤ b`, carried
along a smooth bounded path `R` at the slowness `κ`, the force `∫ eη(x − r) (E' + 𝐯 × B')` of
the potentials of Darwin of the charge itself is exactly `−Σₖ δmᵢₖ v̇ₖ` with `v̇ = κ² R̈(κt)` and
the electromagnetic mass tensor `selfMass`. The Coulomb force, the magnetic force and the terms
with `Ṙ ⊗ Ṙ` vanish by the parity of the profile. -/
theorem selfForce_darwin (e : ℝ) {η : E3 → ℝ} (hη : ContDiff ℝ ∞ η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hηe : ∀ z, η (-z) = η z) {R : ℝ → E3}
    (hR : ContDiff ℝ ∞ R) {L : ℝ} (hL : ∀ s, ‖R s‖ ≤ L) (κ t : ℝ) (i : Fin 3) :
    ∫ x, e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
        (darwinVector κ (rigidCurrent e η R)) (κ • deriv R (κ * t)) i (t, x) =
      -(κ ^ 2 * ∑ k, selfMass e η i k * deriv (deriv R) (κ * t) k) := by
  have hS := slowSource_rigid e hη hb hR hL
  have hρc : Continuous (rigidCharge e η R) := (contDiff_rigidCharge hη hR).continuous
  have hρtc : Continuous (timeDeriv (rigidCharge e η R)) :=
    (contDiff_infty_timeDeriv (contDiff_rigidCharge hη hR)).continuous
  have hsc : Continuous (slow κ (rigidCharge e η R)) := (contDiff_slow
    (contDiff_rigidCharge hη hR) κ).continuous
  -- parities about the centre `R(κt)`
  have hφodd : ReflectsAbout (fun t => R (κ * t)) (-1)
      (spaceDeriv i (darwinScalar κ (rigidCharge e η R))) :=
    (((reflectsAbout_rigidCharge hηe).rescale κ).kernel newtonKernel_neg).gradient
      ((hS.contDiff_darwinScalar κ).differentiable (by simp)) i
  have haeven : ∀ k, ReflectsAbout (fun t => R (κ * t)) 1
      (darwinVector κ (rigidCurrent e η R) k) := fun k =>
    (ReflectsAbout.sum _ fun l _ => ((reflectsAbout_rigidCurrent hηe l).rescale κ).kernel
      (darwinKernel_neg k l)).const_mul κ
  have haodd : ∀ l k, ReflectsAbout (fun t => R (κ * t)) (-1)
      (spaceDeriv l (darwinVector κ (rigidCurrent e η R) k)) := fun l k =>
    (haeven k).gradient ((hS.contDiff_darwinVector κ k).differentiable (by simp)) l
  have hBodd : ∀ k, ReflectsAbout (fun t => R (κ * t)) (-1)
      (kernelIntegral (darwinKernel i k) (slow κ (timeDeriv (rigidCharge e η R)))) := fun k =>
    ((reflectsAbout_timeDeriv_rigidCharge hη hb hηe hR hL).rescale κ).kernel (darwinKernel_neg i k)
  set v : E3 := κ • deriv R (κ * t) with hv
  set O : ℝ × E3 → ℝ := fun p => -spaceDeriv i (darwinScalar κ (rigidCharge e η R)) p -
    κ * ∑ k, κ * (pathVelocity R k (κ * t) *
      kernelIntegral (darwinKernel i k) (slow κ (timeDeriv (rigidCharge e η R))) p) +
    ∑ k, v k * (spaceDeriv i (darwinVector κ (rigidCurrent e η R) k) p -
      spaceDeriv k (darwinVector κ (rigidCurrent e η R) i) p) with hOdef
  have hO : ReflectsAbout (fun t => R (κ * t)) (-1) O :=
    ((hφodd.neg).sub ((ReflectsAbout.sum _ fun k _ => ((hBodd k).const_mul _).const_mul κ).const_mul
      κ)).add (ReflectsAbout.sum _ fun k _ => ((haodd i k).sub (haodd k i)).const_mul (v k))
  set main : ℝ × E3 → ℝ := fun p => -(κ * ∑ k, κ * (deriv (deriv R) (κ * t) k *
    kernelIntegral (darwinKernel i k) (slow κ (rigidCharge e η R)) p)) with hmaindef
  -- the decomposition of the density
  have htj : ∀ k, timeDeriv (rigidCurrent e η R k) = fun q =>
      deriv (pathVelocity R k) q.1 * rigidCharge e η R q +
        pathVelocity R k q.1 * timeDeriv (rigidCharge e η R) q := fun k => by
    funext q
    rw [rigidCurrent_eq_mul, timeDeriv_mul_time ((contDiff_pathVelocity hR k).differentiable
      (by simp)) ((contDiff_rigidCharge hη hR).differentiable (by simp))]
  have hdec : ∀ x, lorentzDensity (darwinScalar κ (rigidCharge e η R))
      (darwinVector κ (rigidCurrent e η R)) v i (t, x) = main (t, x) + O (t, x) := by
    intro x
    have hk : ∀ k, kernelIntegral (darwinKernel i k) (slow κ (timeDeriv (rigidCurrent e η R k)))
        (t, x) = deriv (deriv R) (κ * t) k *
          kernelIntegral (darwinKernel i k) (slow κ (rigidCharge e η R)) (t, x) +
        pathVelocity R k (κ * t) *
          kernelIntegral (darwinKernel i k) (slow κ (timeDeriv (rigidCharge e η R))) (t, x) := by
      intro k
      rw [htj k, kernelIntegral_slow_mul_add (locallyIntegrable_darwinKernel i k) hρc hρtc
        hS.support_charge hS.support_charge.timeDeriv, deriv_pathVelocity hR]
    rw [lorentzDensity, crossProduct_magneticOf, electricOf, timeDeriv_darwinVector hS]
    simp only [hk, hmaindef, hOdef, mul_add, Finset.sum_add_distrib]
    ring
  -- the integral
  have hρ₀ : Continuous fun z : E3 => e * η z := continuous_const.mul hη.continuous
  have hρ₀c : HasCompactSupport fun z : E3 => e * η z :=
    HasCompactSupport.intro (isCompact_closedBall 0 b) fun z hz => by
      simp [hb z (by simpa using hz)]
  have hAc : ∀ k, Continuous (kernelIntegral (darwinKernel i k) (slow κ (rigidCharge e η R))) :=
    fun k => continuous_kernelIntegral (locallyIntegrable_darwinKernel i k) hsc
      ((hS.support_charge.slow κ).kernelSupport _)
  have hLD : Continuous (lorentzDensity (darwinScalar κ (rigidCharge e η R))
      (darwinVector κ (rigidCurrent e η R)) v i) :=
    continuous_lorentzDensity ((hS.contDiff_darwinScalar κ).of_le (by simp))
      (fun k => (hS.contDiff_darwinVector κ k).of_le (by simp)) v i
  have hmainc : Continuous main := by
    simp only [hmaindef]
    exact (continuous_const.mul (continuous_finsetSum _ fun k _ =>
      continuous_const.mul (continuous_const.mul (hAc k)))).neg
  have i1 := integrable_smear hρ₀ hρ₀c hLD t (R (κ * t))
  have i2 := integrable_smear hρ₀ hρ₀c hmainc t (R (κ * t))
  have hzero : ∫ x, e * η (x - R (κ * t)) * O (t, x) = 0 :=
    integral_mul_eq_zero_of_odd (ρ₀ := fun z => e * η z) (by simp [hηe])
      (fun y => by have := hO t y; linarith)
  have hsplit : ∫ x, e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
      (darwinVector κ (rigidCurrent e η R)) v i (t, x) =
      ∫ x, e * η (x - R (κ * t)) * main (t, x) := by
    have h0 : ∫ x, (e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
        (darwinVector κ (rigidCurrent e η R)) v i (t, x) -
        e * η (x - R (κ * t)) * main (t, x)) = 0 := by
      rw [← hzero]
      congr 1
      funext x
      rw [hdec x]
      ring
    rw [integral_sub i1 i2] at h0
    linarith
  have i3 : ∀ k, Integrable fun x => e * η (x - R (κ * t)) *
      kernelIntegral (darwinKernel i k) (slow κ (rigidCharge e η R)) (t, x) := fun k =>
    integrable_smear hρ₀ hρ₀c (hAc k) t (R (κ * t))
  have hmain : ∀ x, e * η (x - R (κ * t)) * main (t, x) = -(κ * ∑ k, κ *
      (deriv (deriv R) (κ * t) k * (e * η (x - R (κ * t)) *
        kernelIntegral (darwinKernel i k) (slow κ (rigidCharge e η R)) (t, x)))) := by
    intro x
    simp only [hmaindef, mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, integral_congr_ae (Eventually.of_forall hmain), integral_neg, integral_const_mul,
    integral_finsetSum _ fun k _ => ((i3 k).const_mul _).const_mul _]
  simp only [integral_const_mul, integral_rigid_mul_kernelIntegral, selfMass, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### The self-force to the third order -/

/-- The iterated derivatives of a multiple: `(Af)⁽ⁿ⁾ = A f⁽ⁿ⁾`. -/
theorem iterate_deriv_const_mul (A : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    deriv^[n] (fun s => A * f s) = fun s => A * deriv^[n] f s := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, deriv_const_mul_field']
    exact ih (deriv f)

/-- The iterated derivatives of a component of a smooth path are the components of its iterated
derivatives. -/
theorem iterate_deriv_component {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) (i : Fin 3) (n : ℕ) :
    deriv^[n] (fun s => R s i) = fun s => deriv^[n] R s i := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    have hd : deriv (fun s => R s i) = fun s => deriv R s i := funext fun s =>
      (hasDerivAt_component_path ((hR.differentiable (by simp)) s).hasDerivAt i).deriv
    rw [hd]
    exact ih (contDiff_infty_iff_deriv.mp hR).2

/-- The dipole moment of a rigid charge of total charge `e`: `dᵢ(s) = e Rᵢ(s) + e ∫ yᵢ η(y) dy`. -/
theorem dipoleMoment_rigidCharge (e : ℝ) {η : E3 → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) (hη1 : ∫ z, η z = 1) (R : ℝ → E3) (i : Fin 3) :
    dipoleMoment (rigidCharge e η R) i = fun s => e * (R s i : ℝ) + e * ∫ y, (y i : ℝ) * η y := by
  funext s
  set w : E3 → ℝ := fun z => z i with hw
  have hi1 : Integrable fun y : E3 => w (R s) * η y :=
    (hη.integrable_of_hasCompactSupport hc).const_mul _
  have hi2 : Integrable fun y : E3 => w y * η y :=
    ((continuous_component i).mul hη).integrable_of_hasCompactSupport hc.mul_left
  have h1 : dipoleMoment (rigidCharge e η R) i s = ∫ y, e * (w (R s) * η y + w y * η y) := by
    rw [dipoleMoment, ← integral_add_right_eq_self _ (R s)]
    congr 1
    funext y
    simp only [rigidCharge, add_sub_cancel_right, hw, PiLp.add_apply]
    ring
  rw [h1, integral_const_mul, integral_add hi1 hi2, integral_const_mul, hη1]
  simp only [hw]
  ring

/-- The third derivative of the dipole moment of a rigid charge is `e R⃛`. -/
theorem iterate_deriv_dipoleMoment_rigidCharge (e : ℝ) {η : E3 → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) (hη1 : ∫ z, η z = 1) {R : ℝ → E3} (hR : ContDiff ℝ ∞ R)
    (i : Fin 3) (s : ℝ) :
    deriv^[3] (dipoleMoment (rigidCharge e η R) i) s = e * deriv^[3] R s i := by
  rw [dipoleMoment_rigidCharge e hη hc hη1 R i, Function.iterate_succ_apply]
  have hd : deriv (fun s => e * (R s i : ℝ) + e * ∫ y, (y i : ℝ) * η y) =
      fun s => e * deriv (fun s => (R s i : ℝ)) s := by
    funext s
    rw [deriv_add_const, deriv_const_mul_field']
  rw [hd, iterate_deriv_const_mul, ← Function.iterate_succ_apply (f := deriv),
    iterate_deriv_component hR]

/-- **The self-force of a rigid charge to the third order** (Landau–Lifshitz (75.8)): for an even
smooth profile `η` of mass one vanishing outside `‖z‖ ≤ b`, carried along a smooth path with
`‖R‖ ≤ L` and `‖Ṙ‖ ≤ V` whose charge and current have the bounds `DampingBounds M`, the force
`∫ eη(x − r) (E + 𝐯 × B)` of the retarded field of the charge on itself at the slowness `κ`,
with `r(t) = R(κt)`, `v̇ = κ² R̈(κt)` and `v̈ = κ³ R⃛(κt)`, is

  `−Σₖ δmᵢₖ v̇ₖ + (2/3)(e²/4π) v̈ᵢ`

up to `(∫|eη|)(M r⁶/72 + M r⁴/6 + V M r⁴) κ⁴` with `r = 2(L + b)`. The coefficients of `κ²` and
`κ³` are exact for every size of the charge: the mass `selfMass` (`δm = (4/3)U` for a spherical
charge, `trace_selfMass`) diverges as the size goes to zero, the damping force does not depend on
the size, and the constant of the remainder grows with the derivatives of `η`. -/
theorem selfForce_expansion (e : ℝ) {η : E3 → ℝ} (hη : ContDiff ℝ ∞ η) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) (hηe : ∀ z, η (-z) = η z) (hη1 : ∫ z, η z = 1)
    {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) {L V M : ℝ} (hL : ∀ s, ‖R s‖ ≤ L)
    (hV : ∀ s, ‖deriv R s‖ ≤ V) (hM : DampingBounds M (rigidCharge e η R) (rigidCurrent e η R))
    {κ : ℝ} (hκ : 0 ≤ κ) (t : ℝ) (i : Fin 3) :
    |(∫ x, e * η (x - R (κ * t)) * lorentzDensity (slowScalar κ (rigidCharge e η R))
        (slowVector κ (rigidCurrent e η R)) (κ • deriv R (κ * t)) i (t, x)) -
      (-(κ ^ 2 * ∑ k, selfMass e η i k * deriv (deriv R) (κ * t) k) +
        2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] R (κ * t) i))| ≤
      (∫ z, |e * η z|) * ((M * (2 * (L + b)) ^ 6 / 72 + M * (2 * (L + b)) ^ 4 / 6 +
        V * (M * (2 * (L + b)) ^ 4)) * κ ^ 4) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have ha : 0 ≤ L + b := by linarith
  have hS := slowSource_rigid e hη hb hR hL
  have hηc : HasCompactSupport η :=
    HasCompactSupport.intro (isCompact_closedBall 0 b) fun z hz => hb z (by simpa using hz)
  have hρ₀ : Continuous fun z : E3 => e * η z := continuous_const.mul hη.continuous
  have hρ₀c : HasCompactSupport fun z : E3 => e * η z := hηc.mul_left
  set v : E3 := κ • deriv R (κ * t) with hvdef
  have hv : ‖v‖ ≤ V * κ := by
    rw [hvdef, norm_smul, Real.norm_of_nonneg hκ, mul_comm]
    exact mul_le_mul_of_nonneg_right (hV _) hκ
  set D := 2 / 3 * (4 * π)⁻¹ * κ ^ 3 *
    deriv^[3] (dipoleMoment (rigidCharge e η R) i) (κ * t) with hD
  have hφR : ContDiff ℝ 1 (slowScalar κ (rigidCharge e η R)) :=
    (hS.contDiff_slowScalar κ).of_le (by simp)
  have haR : ∀ k, ContDiff ℝ 1 (slowVector κ (rigidCurrent e η R) k) := fun k =>
    (hS.contDiff_slowVector κ k).of_le (by simp)
  have hφD : ContDiff ℝ 1 (darwinScalar κ (rigidCharge e η R)) :=
    (hS.contDiff_darwinScalar κ).of_le (by simp)
  have haD : ∀ k, ContDiff ℝ 1 (darwinVector κ (rigidCurrent e η R) k) := fun k =>
    (hS.contDiff_darwinVector κ k).of_le (by simp)
  have i1 := integrable_smear hρ₀ hρ₀c (continuous_lorentzDensity hφR haR v i) t (R (κ * t))
  have i2 := integrable_smear hρ₀ hρ₀c (continuous_lorentzDensity hφD haD v i) t (R (κ * t))
  have hshift : Integrable fun x => e * η (x - R (κ * t)) :=
    (hρ₀.comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      (hρ₀c.comp_homeomorph (Homeomorph.subRight (R (κ * t))))
  have i3 : Integrable fun x => e * η (x - R (κ * t)) * D := hshift.mul_const D
  have hmass : ∫ x, e * η (x - R (κ * t)) * D = e * D := by
    rw [integral_mul_const, integral_sub_right_eq_self (fun z => e * η z), integral_const_mul,
      hη1, mul_one]
  have hdamp : 2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] R (κ * t) i) = e * D := by
    rw [hD, iterate_deriv_dipoleMoment_rigidCharge e hη.continuous hηc hη1 hR]
    ring
  rw [← selfForce_darwin e hη hb hηe hR hL κ t i, hdamp]
  have key : (∫ x, e * η (x - R (κ * t)) * lorentzDensity (slowScalar κ (rigidCharge e η R))
        (slowVector κ (rigidCurrent e η R)) v i (t, x)) -
      ((∫ x, e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
        (darwinVector κ (rigidCurrent e η R)) v i (t, x)) + e * D) =
      ∫ x, (e * η (x - R (κ * t)) * lorentzDensity (slowScalar κ (rigidCharge e η R))
        (slowVector κ (rigidCurrent e η R)) v i (t, x) -
        e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
          (darwinVector κ (rigidCurrent e η R)) v i (t, x) - e * η (x - R (κ * t)) * D) := by
    have i12 : Integrable fun x => e * η (x - R (κ * t)) *
        lorentzDensity (slowScalar κ (rigidCharge e η R)) (slowVector κ (rigidCurrent e η R)) v i
          (t, x) - e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
          (darwinVector κ (rigidCurrent e η R)) v i (t, x) := i1.sub i2
    rw [integral_sub i12 i3, integral_sub i1 i2, hmass]
    ring
  rw [key]
  set C := (M * (2 * (L + b)) ^ 6 / 72 + M * (2 * (L + b)) ^ 4 / 6 +
    V * (M * (2 * (L + b)) ^ 4)) * κ ^ 4 with hC
  have hint : Integrable fun x => |e * η (x - R (κ * t))| * C := hshift.abs.mul_const C
  have hpt : ∀ x, ‖e * η (x - R (κ * t)) * lorentzDensity (slowScalar κ (rigidCharge e η R))
        (slowVector κ (rigidCurrent e η R)) v i (t, x) -
        e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
          (darwinVector κ (rigidCurrent e η R)) v i (t, x) - e * η (x - R (κ * t)) * D‖ ≤
      |e * η (x - R (κ * t))| * C := by
    intro x
    rw [← mul_sub, ← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hx : ‖x - R (κ * t)‖ ≤ b
    · have hxR : ‖x‖ ≤ L + b := by
        have := norm_le_norm_add_norm_sub' x (R (κ * t))
        linarith [hL (κ * t)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have H := lorentzDensity_expansion hS ha hM hκ t hxR hv i
      rw [show L + b + (L + b) = 2 * (L + b) by ring] at H
      exact H
    · simp [hb _ (not_le.mp hx)]
  rw [← Real.norm_eq_abs]
  calc ‖∫ x, (e * η (x - R (κ * t)) * lorentzDensity (slowScalar κ (rigidCharge e η R))
        (slowVector κ (rigidCurrent e η R)) v i (t, x) -
        e * η (x - R (κ * t)) * lorentzDensity (darwinScalar κ (rigidCharge e η R))
          (darwinVector κ (rigidCurrent e η R)) v i (t, x) - e * η (x - R (κ * t)) * D)‖
      ≤ ∫ x, |e * η (x - R (κ * t))| * C :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = (∫ z, |e * η z|) * C := by
        rw [integral_mul_const, integral_sub_right_eq_self (fun z => |e * η z|) (R (κ * t))]

/-! ### The electromagnetic mass and the self-energy -/

/-- The trace of the kernel of Darwin is twice the Newton kernel: `Σᵢ (1 + nᵢ²)/(8πR) = 2/(4πR)`.
-/
theorem sum_darwinKernel_self (y : E3) :
    ∑ i, darwinKernel i i y = 2 * Potential.newtonKernel y := by
  have hs : ∑ i, (y i : ℝ) * (y i : ℝ) = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs, sq]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [darwinKernel, Potential.newtonKernel]
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    have he : ∑ i, darwinKernel i i y =
        (3 / ‖y‖ + (∑ i, (y i : ℝ) * (y i : ℝ)) / ‖y‖ ^ 3) / (8 * π) := by
      simp only [darwinKernel, ite_true, Fin.sum_univ_three]
      ring
    rw [he, hs, Potential.newtonKernel]
    field_simp
    ring

/-- **The electromagnetic mass is four thirds of the self-energy on average** (the `4/3` of the
electromagnetic mass of Abraham and Lorentz): `Σᵢ δmᵢᵢ = 4U`, so a spherically symmetric charge,
for which `δmᵢₖ = δm δᵢₖ`, has `δm = (4/3) U`. -/
theorem trace_selfMass (e : ℝ) {η : E3 → ℝ} (hη : Continuous η) (hc : HasCompactSupport η) :
    ∑ i, selfMass e η i i = 4 * selfEnergy e η := by
  obtain ⟨b, hb⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set F : ℝ × E3 → ℝ := fun p => η p.2 with hF
  have hFc : Continuous F := hη.comp continuous_snd
  have hFs : SpatialSupport b F := fun p hp => by
    simp only [hF]
    refine image_eq_zero_of_notMem_tsupport fun hmem => ?_
    have := hb hmem
    rw [mem_closedBall_zero_iff] at this
    linarith
  have hin : ∀ (K : E3 → ℝ), LocallyIntegrable K → ∀ x : E3,
      Integrable fun y => K y * η (x - y) := fun K hK x => by
    have := (hFs.kernelSupport K).integrable hK hFc (0, x)
    simpa [hF, smul_eq_mul] using this
  have hcont : ∀ (K : E3 → ℝ), LocallyIntegrable K →
      Continuous fun x : E3 => ∫ y, K y * η (x - y) := fun K hK => by
    have := (continuous_kernelIntegral hK hFc (hFs.kernelSupport K)).comp
      (continuous_const.prodMk continuous_id : Continuous fun x : E3 => ((0 : ℝ), x))
    simpa [Function.comp_def, kernelIntegral, hF, smul_eq_mul] using this
  have hout : ∀ (K : E3 → ℝ), LocallyIntegrable K →
      Integrable fun x => η x * ∫ y, K y * η (x - y) := fun K hK =>
    (hη.mul (hcont K hK)).integrable_of_hasCompactSupport hc.mul_right
  have hinner : ∀ x, ∑ i, ∫ y, darwinKernel i i y * η (x - y) =
      2 * ∫ y, Potential.newtonKernel y * η (x - y) := fun x => by
    rw [← integral_finsetSum _ fun i _ => hin _ (locallyIntegrable_darwinKernel i i) x,
      ← integral_const_mul]
    congr 1
    funext y
    rw [← Finset.sum_mul, sum_darwinKernel_self]
    ring
  simp only [selfMass, selfEnergy]
  rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ =>
    hout _ (locallyIntegrable_darwinKernel i i)]
  have he : (fun x => ∑ i, η x * ∫ y, darwinKernel i i y * η (x - y)) =
      fun x => 2 * (η x * ∫ y, Potential.newtonKernel y * η (x - y)) := by
    funext x
    rw [← Finset.mul_sum, hinner]
    ring
  rw [he, integral_const_mul]
  ring

/-! ### Bounds for a periodic motion -/

/-- A function on `ℝ × ℝ³` with the period `T` in time. -/
def TimePeriodic (T : ℝ) (F : ℝ × E3 → ℝ) : Prop := ∀ s z, F (s + T, z) = F (s, z)

namespace TimePeriodic

variable {T : ℝ} {F : ℝ × E3 → ℝ}

theorem fderiv_eq (hF : TimePeriodic T F) (s : ℝ) (z : E3) :
    fderiv ℝ F (s + T, z) = fderiv ℝ F (s, z) := by
  have h1 : (fun p : ℝ × E3 => F (p + (T, 0))) = F := by
    funext p
    obtain ⟨s', z'⟩ := p
    simp [hF s' z']
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := ((s, z) : ℝ × E3)) ((T, 0) : ℝ × E3)
  rw [h1] at h2
  rw [h2]
  simp

theorem deriv_time (hF : TimePeriodic T F) : TimePeriodic T (timeDeriv F) := fun s z => by
  simp only [timeDeriv, hF.fderiv_eq s z]

theorem deriv_space (hF : TimePeriodic T F) (i : Fin 3) : TimePeriodic T (spaceDeriv i F) :=
  fun s z => by simp only [spaceDeriv, hF.fderiv_eq s z]

theorem iterate_deriv_time (hF : TimePeriodic T F) (n : ℕ) :
    TimePeriodic T (timeDeriv^[n] F) := by
  induction n generalizing F with
  | zero => exact hF
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih hF.deriv_time

/-- A continuous function periodic in time and supported in a cylinder is bounded. -/
theorem exists_bound (hT : 0 < T) (hF : TimePeriodic T F) (hc : Continuous F) {a : ℝ}
    (hs : SpatialSupport a F) : ∃ M, ∀ p, |F p| ≤ M := by
  obtain ⟨M, hM⟩ :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : E3) a)).exists_bound_of_continuousOn
    (f := F) (s := Icc 0 T ×ˢ closedBall (0 : E3) a) hc.continuousOn
  refine ⟨max M 0, fun p => ?_⟩
  obtain ⟨s, z⟩ := p
  by_cases hz : a < ‖z‖
  · rw [hs (s, z) hz, abs_zero]
    exact le_max_right _ _
  · obtain ⟨y, hy, hyeq⟩ :=
      (show Function.Periodic (fun s => F (s, z)) T from fun s => hF s z).exists_mem_Ico₀ hT s
    have h := hM (y, z) ⟨⟨hy.1, hy.2.le⟩, by simpa using not_lt.mp hz⟩
    rw [Real.norm_eq_abs] at h
    exact (show |F (s, z)| ≤ M from hyeq ▸ h).trans (le_max_left _ _)

end TimePeriodic

/-- Finitely many bounded functions have a common bound. -/
theorem exists_forall_bound {ι : Type*} [Fintype ι] {f : ι → ℝ × E3 → ℝ}
    (h : ∀ i, ∃ M, ∀ p, |f i p| ≤ M) : ∃ M, ∀ i p, |f i p| ≤ M := by
  choose M hM using h
  exact ⟨∑ i, |M i|, fun i p => (hM i p).trans ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (M j)) (Finset.mem_univ i)))⟩

theorem timePeriodic_rigidCharge (e : ℝ) (η : E3 → ℝ) {R : ℝ → E3} {T : ℝ}
    (hRT : Function.Periodic R T) : TimePeriodic T (rigidCharge e η R) := fun s z => by
  simp [rigidCharge, hRT s]

theorem timePeriodic_rigidCurrent (e : ℝ) (η : E3 → ℝ) {R : ℝ → E3} {T : ℝ}
    (hRT : Function.Periodic R T) (k : Fin 3) : TimePeriodic T (rigidCurrent e η R k) :=
  fun s z => by
    have hd : deriv R (s + T) = deriv R s := by
      have := deriv_comp_add_const R T s
      rw [show (fun x => R (x + T)) = R from funext hRT] at this
      exact this.symm
    simp [rigidCurrent, hRT s, hd]

/-- **A periodic motion has the bounds of the damping expansion**: a rigid charge on a smooth
periodic path has bounded derivatives of every order, in particular `DampingBounds M`. -/
theorem exists_dampingBounds_of_periodic (e : ℝ) {η : E3 → ℝ} (hη : ContDiff ℝ ∞ η) {b : ℝ}
    (hb : ∀ z : E3, b < ‖z‖ → η z = 0) {R : ℝ → E3} (hR : ContDiff ℝ ∞ R) {L : ℝ}
    (hL : ∀ s, ‖R s‖ ≤ L) {T : ℝ} (hT : 0 < T) (hRT : Function.Periodic R T) :
    ∃ M, DampingBounds M (rigidCharge e η R) (rigidCurrent e η R) := by
  have hS := slowSource_rigid e hη hb hR hL
  have key : ∀ G : ℝ × E3 → ℝ, ContDiff ℝ ∞ G → TimePeriodic T G → SpatialSupport (L + b) G →
      ∀ n, ∃ M, ∀ p, |timeDeriv^[n] G p| ≤ M := fun G hG hp hs n =>
    (hp.iterate_deriv_time n).exists_bound hT (contDiff_iterate_timeDeriv_infty hG n).continuous
      (hs.iterate_timeDeriv n)
  obtain ⟨M₁, h₁⟩ := exists_forall_bound fun i : Fin 3 =>
    key _ (contDiff_infty_spaceDeriv hS.smooth_charge i)
      ((timePeriodic_rigidCharge e η hRT).deriv_space i) (hS.support_charge.spaceDeriv i) 4
  obtain ⟨M₂, h₂⟩ := exists_forall_bound fun i : Fin 3 =>
    key _ (hS.smooth_current i) (timePeriodic_rigidCurrent e η hRT i) (hS.support_current i) 3
  obtain ⟨M₃, h₃⟩ := exists_forall_bound fun il : Fin 3 × Fin 3 =>
    key _ (contDiff_infty_spaceDeriv (hS.smooth_current il.1) il.2)
      ((timePeriodic_rigidCurrent e η hRT il.1).deriv_space il.2)
      ((hS.support_current il.1).spaceDeriv il.2) 2
  exact ⟨max M₁ (max M₂ M₃), fun i p => (h₁ i p).trans (le_max_left _ _),
    fun i p => (h₂ i p).trans ((le_max_left _ _).trans (le_max_right _ _)),
    fun i l p => (h₃ (i, l) p).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-! ### An instance: an oscillating charge -/

/-- The oscillating path `R(s) = sin s · e₁`. -/
def oscillatingPath (s : ℝ) : E3 := Real.sin s • EuclideanSpace.single 0 1

theorem contDiff_oscillatingPath : ContDiff ℝ ∞ oscillatingPath :=
  Real.contDiff_sin.smul contDiff_const

theorem norm_oscillatingPath_le (s : ℝ) : ‖oscillatingPath s‖ ≤ 1 := by
  simp [oscillatingPath, norm_smul, Real.abs_sin_le_one]

theorem deriv_oscillatingPath (s : ℝ) :
    deriv oscillatingPath s = Real.cos s • EuclideanSpace.single 0 1 :=
  ((Real.hasDerivAt_sin s).smul_const _).deriv

theorem norm_deriv_oscillatingPath_le (s : ℝ) : ‖deriv oscillatingPath s‖ ≤ 1 := by
  simp [deriv_oscillatingPath, norm_smul, Real.abs_cos_le_one]

theorem periodic_oscillatingPath : Function.Periodic oscillatingPath (2 * π) := fun s => by
  simp [oscillatingPath, Real.sin_periodic s]

theorem pointBump_one_eq :
    pointBump 1 = (⟨1 / 2, 1, by norm_num, by norm_num⟩ : ContDiffBump (0 : E3)).normed volume := by
  simp only [pointBump, zero_lt_one, ↓reduceDIte]

theorem contDiff_pointBump_one : ContDiff ℝ ∞ (pointBump 1) := by
  rw [pointBump_one_eq]
  exact ContDiffBump.contDiff_normed _

theorem pointBump_one_eq_zero {z : E3} (hz : 1 < ‖z‖) : pointBump 1 z = 0 := by
  rw [pointBump_one_eq]
  refine Function.notMem_support.mp fun hmem => ?_
  rw [ContDiffBump.support_normed_eq, mem_ball_zero_iff] at hmem
  exact absurd hz (not_lt.mpr hmem.le)

theorem pointBump_one_neg (z : E3) : pointBump 1 (-z) = pointBump 1 z := by
  rw [pointBump_one_eq]
  exact ContDiffBump.normed_neg _ z

theorem integral_pointBump_one : ∫ z, pointBump 1 z = 1 := by
  rw [pointBump_one_eq]
  exact ContDiffBump.integral_normed _

/-- **The instance of the self-force expansion**: the normalized bump of radius one, oscillating
along `R(s) = sin s · e₁`, satisfies the hypotheses of `selfForce_expansion`; its self-force is
`−Σₖ δmᵢₖ v̇ₖ + (2/3)(e²/4π) v̈ᵢ + O(κ⁴)` uniformly in time. -/
theorem selfForce_expansion_oscillating (e : ℝ) :
    ∃ C, ∀ κ, 0 ≤ κ → ∀ (t : ℝ) (i : Fin 3),
      |(∫ x, e * pointBump 1 (x - oscillatingPath (κ * t)) *
          lorentzDensity (slowScalar κ (rigidCharge e (pointBump 1) oscillatingPath))
            (slowVector κ (rigidCurrent e (pointBump 1) oscillatingPath))
            (κ • deriv oscillatingPath (κ * t)) i (t, x)) -
        (-(κ ^ 2 * ∑ k, selfMass e (pointBump 1) i k * deriv (deriv oscillatingPath) (κ * t) k) +
          2 / 3 * (e ^ 2 / (4 * π)) * (κ ^ 3 * deriv^[3] oscillatingPath (κ * t) i))| ≤
        C * κ ^ 4 := by
  obtain ⟨M, hM⟩ := exists_dampingBounds_of_periodic e contDiff_pointBump_one
    (fun z hz => pointBump_one_eq_zero hz) contDiff_oscillatingPath norm_oscillatingPath_le
    (by positivity) periodic_oscillatingPath
  refine ⟨(∫ z, |e * pointBump 1 z|) * (M * (2 * (1 + 1)) ^ 6 / 72 + M * (2 * (1 + 1)) ^ 4 / 6 +
    1 * (M * (2 * (1 + 1)) ^ 4)), fun κ hκ t i => ?_⟩
  have H := selfForce_expansion e contDiff_pointBump_one zero_le_one
    (fun z hz => pointBump_one_eq_zero hz) pointBump_one_neg integral_pointBump_one
    contDiff_oscillatingPath norm_oscillatingPath_le norm_deriv_oscillatingPath_le hM hκ t i
  exact H.trans (le_of_eq (by ring))

/-! ### The work of the damping force -/

/-- The damping force `𝐟 = (2/3)(e²/4π) v̈` (75.8) on a charge `e` with the velocity `𝐯(t)`. -/
def dampingForce (e : ℝ) (v : ℝ → E3) (t : ℝ) : E3 :=
  (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv v) t

/-- **The work of the damping force** (Landau–Lifshitz (75.9)): over a time interval,
`∫ 𝐟 · 𝐯 dt = −(2/3)(e²/4π) ∫ v̇² dt + (2/3)(e²/4π) [v̇ · 𝐯]`, the energy radiated by Larmor's
formula and the change of the term of Schott. -/
theorem work_dampingForce_eq (e : ℝ) {v : ℝ → E3} (hv : ContDiff ℝ 2 v) (t₀ t₁ : ℝ) :
    ∫ t in t₀..t₁, inner ℝ (dampingForce e v t) (v t) =
      -(2 / 3 * (e ^ 2 / (4 * π))) * (∫ t in t₀..t₁, ‖deriv v t‖ ^ 2) +
        2 / 3 * (e ^ 2 / (4 * π)) *
          (inner ℝ (deriv v t₁) (v t₁) - inner ℝ (deriv v t₀) (v t₀)) := by
  have hd1 : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hc1 : ContDiff ℝ 1 (deriv v) := hv.deriv'
  have hd2 : Differentiable ℝ (deriv v) := hc1.differentiable (by norm_num)
  have hc2 : Continuous (deriv (deriv v)) := hc1.continuous_deriv le_rfl
  have hder : ∀ t, HasDerivAt (fun t => inner ℝ (deriv v t) (v t))
      (inner ℝ (deriv v t) (deriv v t) + inner ℝ (deriv (deriv v) t) (v t)) t := fun t =>
    (hd2 t).hasDerivAt.inner ℝ (hd1 t).hasDerivAt
  have i1 : IntervalIntegrable (fun t => ‖deriv v t‖ ^ 2) MeasureTheory.volume t₀ t₁ :=
    (hc1.continuous.norm.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun t => inner ℝ (deriv (deriv v) t) (v t))
      MeasureTheory.volume t₀ t₁ :=
    (hc2.inner hd1.continuous).intervalIntegrable _ _
  have i12 : IntervalIntegrable (fun t => inner ℝ (deriv v t) (deriv v t) +
      inner ℝ (deriv (deriv v) t) (v t)) MeasureTheory.volume t₀ t₁ :=
    ((hc1.continuous.inner hc1.continuous).add (hc2.inner hd1.continuous)).intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hder t) i12
  have hmain : ∫ t in t₀..t₁, inner ℝ (deriv (deriv v) t) (v t) =
      (inner ℝ (deriv v t₁) (v t₁) - inner ℝ (deriv v t₀) (v t₀)) -
        ∫ t in t₀..t₁, ‖deriv v t‖ ^ 2 := by
    rw [← hFTC, ← intervalIntegral.integral_sub i12 i1]
    congr 1
    funext t
    rw [real_inner_self_eq_norm_sq]
    ring
  simp only [dampingForce, real_inner_smul_left]
  rw [intervalIntegral.integral_const_mul, hmain]
  ring

/-- For a periodic motion, or any motion with `v̇ · 𝐯` equal at the ends, the work of the damping
force is minus the energy radiated: `∫ 𝐟 · 𝐯 dt = −(2/3)(e²/4π) ∫ v̇² dt` (75.10). -/
theorem work_dampingForce_eq_of_eq (e : ℝ) {v : ℝ → E3} (hv : ContDiff ℝ 2 v) {t₀ t₁ : ℝ}
    (h : inner ℝ (deriv v t₁) (v t₁) = inner ℝ (deriv v t₀) (v t₀)) :
    ∫ t in t₀..t₁, inner ℝ (dampingForce e v t) (v t) =
      -(2 / 3 * (e ^ 2 / (4 * π))) * ∫ t in t₀..t₁, ‖deriv v t‖ ^ 2 := by
  rw [work_dampingForce_eq e hv, h, sub_self, mul_zero, add_zero]

/-! ### The runaway solutions -/

theorem dampingConstant_pos {e : ℝ} (he : e ≠ 0) : 0 < 2 / 3 * (e ^ 2 / (4 * π)) := by
  have := pow_pos (abs_pos.mpr he) 2
  rw [sq_abs] at this
  positivity

/-- **The free equation of Abraham and Lorentz** `m v̇ = (2/3)(e²/4π) v̈` determines the
acceleration from its initial value: `v̇(t) = e^{t/τ} v̇(0)` with `τ = (2/3)(e²/4π)/m`. -/
theorem abrahamLorentz_free (e m : ℝ) (he : e ≠ 0) {v : ℝ → E3} (hv : ContDiff ℝ 2 v)
    (h : ∀ t, m • deriv v t = (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv v) t) (t : ℝ) :
    deriv v t = Real.exp (m / (2 / 3 * (e ^ 2 / (4 * π))) * t) • deriv v 0 := by
  set k := 2 / 3 * (e ^ 2 / (4 * π)) with hk
  have hk0 : k ≠ 0 := (dampingConstant_pos he).ne'
  set r := m / k with hr
  have hd2 : Differentiable ℝ (deriv v) :=
    (ContDiff.deriv' (n := 1) hv).differentiable (by norm_num)
  have hacc : ∀ t, deriv (deriv v) t = r • deriv v t := fun t => by
    have := congrArg (fun w => k⁻¹ • w) (h t)
    simp only [smul_smul, inv_mul_cancel₀ hk0, one_smul] at this
    rw [← this, hr, div_eq_inv_mul]
  set g : ℝ → E3 := fun t => Real.exp (-r * t) • deriv v t with hg
  have hgd : ∀ t, HasDerivAt g 0 t := fun t => by
    have h1 : HasDerivAt (fun t => Real.exp (-r * t)) (Real.exp (-r * t) * (-r * 1)) t :=
      ((hasDerivAt_id' t).const_mul (-r)).exp
    have h2 : HasDerivAt g (Real.exp (-r * t) • deriv (deriv v) t +
        (Real.exp (-r * t) * (-r * 1)) • deriv v t) t := h1.smul (hd2 t).hasDerivAt
    convert h2 using 1
    rw [hacc t, smul_smul, ← add_smul]
    rw [show Real.exp (-r * t) * r + Real.exp (-r * t) * (-r * 1) = 0 by ring, zero_smul]
  have hc := is_const_of_deriv_eq_zero (fun t => (hgd t).differentiableAt) (fun t => (hgd t).deriv)
    t 0
  simp only [hg, mul_zero, Real.exp_zero, one_smul] at hc
  calc deriv v t = Real.exp (r * t) • (Real.exp (-r * t) • deriv v t) := by
        rw [smul_smul, ← Real.exp_add, show r * t + -r * t = 0 by ring, Real.exp_zero, one_smul]
    _ = Real.exp (r * t) • deriv v 0 := by rw [hc]

/-- The runaway velocity `𝐯(t) = τ (e^{t/τ} − 1) 𝐰` with `τ = (2/3)(e²/4π)/m`. -/
def runawayVelocity (e m : ℝ) (w : E3) (t : ℝ) : E3 :=
  ((2 / 3 * (e ^ 2 / (4 * π))) / m * (Real.exp (m / (2 / 3 * (e ^ 2 / (4 * π))) * t) - 1)) • w

theorem deriv_runawayVelocity (e m : ℝ) (he : e ≠ 0) (hm : m ≠ 0) (w : E3) (t : ℝ) :
    deriv (runawayVelocity e m w) t =
      Real.exp (m / (2 / 3 * (e ^ 2 / (4 * π))) * t) • w := by
  set k := 2 / 3 * (e ^ 2 / (4 * π))
  have hk0 : k ≠ 0 := (dampingConstant_pos he).ne'
  have h1 : HasDerivAt (fun t => Real.exp (m / k * t)) (Real.exp (m / k * t) * (m / k * 1)) t :=
    ((hasDerivAt_id' t).const_mul (m / k)).exp
  have h : HasDerivAt (fun t => (k / m * (Real.exp (m / k * t) - 1)) • w)
      ((k / m * (Real.exp (m / k * t) * (m / k * 1))) • w) t :=
    ((h1.sub_const 1).const_mul (k / m)).smul_const w
  rw [show runawayVelocity e m w = fun t => (k / m * (Real.exp (m / k * t) - 1)) • w from rfl,
    h.deriv]
  congr 1
  field_simp

/-- **The runaway solutions** (Landau–Lifshitz §75): for `m > 0` and `e ≠ 0`, every
`𝐯(t) = τ (e^{t/τ} − 1) 𝐰` solves the free equation `m v̇ = (2/3)(e²/4π) v̈` with
`v̇(t) = e^{t/τ} 𝐰`, and for `𝐰 ≠ 0` the acceleration grows without bound in the absence of any
force. So not every solution of the equation of Abraham and Lorentz is physical. -/
theorem runaway (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {w : E3} (hw : w ≠ 0) :
    (∀ t, m • deriv (runawayVelocity e m w) t =
        (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv (runawayVelocity e m w)) t) ∧
      Tendsto (fun t => ‖deriv (runawayVelocity e m w) t‖) atTop atTop := by
  set k := 2 / 3 * (e ^ 2 / (4 * π)) with hk
  have hk0 : 0 < k := dampingConstant_pos he
  have hd : deriv (runawayVelocity e m w) = fun t => Real.exp (m / k * t) • w :=
    funext (deriv_runawayVelocity e m he hm.ne' w)
  have hdd : ∀ t, deriv (deriv (runawayVelocity e m w)) t =
      (m / k * Real.exp (m / k * t)) • w := fun t => by
    rw [hd]
    have h := (((hasDerivAt_id' t).const_mul (m / k)).exp).smul_const w
    rw [h.deriv]
    congr 1
    ring
  refine ⟨fun t => ?_, ?_⟩
  · rw [hdd, hd]
    show m • (Real.exp (m / k * t) • w) = k • ((m / k * Real.exp (m / k * t)) • w)
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
  · rw [hd]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.tendsto_exp_atTop.comp
      (tendsto_id.const_mul_atTop (div_pos hm hk0))).atTop_mul_const
      (norm_pos_iff.mpr hw)

/-- **Only uniform motion has a bounded acceleration**: for `m > 0` and `e ≠ 0`, a solution of the
free equation of Abraham and Lorentz whose acceleration stays bounded for `t ≥ 0` has `v̇ = 0`. -/
theorem abrahamLorentz_free_eq_zero (e m : ℝ) (he : e ≠ 0) (hm : 0 < m) {v : ℝ → E3}
    (hv : ContDiff ℝ 2 v)
    (h : ∀ t, m • deriv v t = (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv v) t) {C : ℝ}
    (hC : ∀ t, 0 ≤ t → ‖deriv v t‖ ≤ C) (t : ℝ) : deriv v t = 0 := by
  have h0 : deriv v 0 = 0 := by
    by_contra hne
    have hpos : 0 < ‖deriv v 0‖ := norm_pos_iff.mpr hne
    have hlim : Tendsto (fun t => Real.exp (m / (2 / 3 * (e ^ 2 / (4 * π))) * t) *
        ‖deriv v 0‖) atTop atTop :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop
        (div_pos hm (dampingConstant_pos he)))).atTop_mul_const hpos
    obtain ⟨s, hs⟩ := ((hlim.eventually_gt_atTop C).and (eventually_ge_atTop 0)).exists
    have := hC s hs.2
    rw [abrahamLorentz_free e m he hv h s, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at this
    linarith [hs.1]
  rw [abrahamLorentz_free e m he hv h t, h0, smul_zero]

/-! ### The charged oscillator -/

open Mechanics SmoothAlgebra in
/-- **The reduced equation of a charged oscillator**: `ẍ = u + τ u̇` with the force per unit mass
`u = g − ω₀² x` of the spring and of an external field `g`, and `τ = (2/3)(e²/4π)/m`. The term
`τ x⃛` of the equation of Abraham and Lorentz is replaced by its value `τ u̇` on the motion without
damping. -/
def IsReducedOscillator (τ ω₀ : ℝ) (g x : Mechanics.TimeFunction) : Prop :=
  timeDerivative (timeDerivative x) =
    (g - algebraMap ℝ TimeFunction (ω₀ ^ 2) * x) +
      algebraMap ℝ TimeFunction τ * timeDerivative (g - algebraMap ℝ TimeFunction (ω₀ ^ 2) * x)

open Mechanics SmoothAlgebra in
/-- The reduced equation is that of a forced damped oscillator with `γ = τ ω₀²/2` and the force
`g + τ ġ`. -/
theorem isReducedOscillator_iff (τ ω₀ : ℝ) (g x : Mechanics.TimeFunction) :
    IsReducedOscillator τ ω₀ g x ↔
      IsForced (τ * ω₀ ^ 2 / 2) ω₀ (g + algebraMap ℝ TimeFunction τ * timeDerivative g) x := by
  unfold IsReducedOscillator IsForced
  rw [map_sub, SmoothDerivation.map_algebraMap_mul, smul_eq_mul]
  have h2 : algebraMap ℝ TimeFunction (2 * (τ * ω₀ ^ 2 / 2)) =
      algebraMap ℝ TimeFunction τ * algebraMap ℝ TimeFunction (ω₀ ^ 2) := by
    rw [← map_mul]
    congr 1
    ring
  rw [h2]
  constructor <;> intro h <;> rw [h] <;> ring

open Mechanics SmoothAlgebra in
/-- **The damping of a charged oscillator** (Landau–Lifshitz §75, problem): the reduced equation of
a charge `e` of mass `m` on a spring of frequency `ω₀` is the forced damped equation of the
library with the damping coefficient `γ = e² ω₀²/(12π m)` (Heaviside–Lorentz units; `e² ω₀²/(3m)`
in Gaussian units). -/
theorem reducedOscillator (e m ω₀ : ℝ) (g x : Mechanics.TimeFunction) :
    IsReducedOscillator (2 / 3 * (e ^ 2 / (4 * π)) / m) ω₀ g x ↔
      IsForced (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ω₀
        (g + algebraMap ℝ TimeFunction (2 / 3 * (e ^ 2 / (4 * π)) / m) * timeDerivative g) x := by
  rw [isReducedOscillator_iff]
  have hγ : 2 / 3 * (e ^ 2 / (4 * π)) / m * ω₀ ^ 2 / 2 = e ^ 2 * ω₀ ^ 2 / (12 * π * m) := by
    ring
  rw [hγ]

open Mechanics SmoothAlgebra in
/-- **The free charged oscillator decays**: for `e ≠ 0`, `m > 0` and `ω₀ ≠ 0`, a solution of the
reduced equation without an external force is a damped oscillation with `γ = e²ω₀²/(12πm) > 0`,
its energy `ẋ² + ω₀² x²` does not increase and it tends to rest. -/
theorem reducedOscillator_free (e m ω₀ : ℝ) (he : e ≠ 0) (hm : 0 < m) (hω₀ : ω₀ ≠ 0)
    {x : Mechanics.TimeFunction} (hx : IsReducedOscillator (2 / 3 * (e ^ 2 / (4 * π)) / m) ω₀ 0 x) :
    IsDamped (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ω₀ x ∧
      Antitone (fun t : ℝ => timeDerivative x (fun _ => t) ^ 2 + ω₀ ^ 2 * x (fun _ => t) ^ 2) ∧
      Tendsto (fun t : ℝ => x fun _ => t) atTop (𝓝 0) := by
  have hγ : 0 < e ^ 2 * ω₀ ^ 2 / (12 * π * m) := by
    have h1 := pow_pos (abs_pos.mpr he) 2
    have h2 := pow_pos (abs_pos.mpr hω₀) 2
    rw [sq_abs] at h1 h2
    positivity
  have hd : IsDamped (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ω₀ x := by
    have h := (reducedOscillator e m ω₀ 0 x).mp hx
    rw [map_zero, mul_zero, add_zero] at h
    exact isForced_zero_iff.mp h
  exact ⟨hd, hd.energy_antitone hγ.le, hd.tendsto_zero hγ hω₀⟩

open Mechanics SmoothAlgebra in
/-- **An instance of the reduced equation**: for weak damping `γ² ≤ ω₀²`,
`γ = e²ω₀²/(12πm)`, the damped oscillation `e^{−γt} cos ωt` with `ω² = ω₀² − γ²` solves the
reduced equation without an external force. -/
theorem isReducedOscillator_damped (e m ω₀ : ℝ)
    (hweak : (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ^ 2 ≤ ω₀ ^ 2) :
    IsReducedOscillator (2 / 3 * (e ^ 2 / (4 * π)) / m) ω₀ 0
      (TimeFunction.expMul (-(e ^ 2 * ω₀ ^ 2 / (12 * π * m))) *
        TimeFunction.cosMul (√(ω₀ ^ 2 - (e ^ 2 * ω₀ ^ 2 / (12 * π * m)) ^ 2))) := by
  rw [reducedOscillator, map_zero, mul_zero, add_zero, isForced_zero_iff]
  exact (isHarmonic_cosMul _).isDamped_expMul_neg_mul (Real.sq_sqrt (by linarith))

open Mechanics SmoothAlgebra in
/-- **The reduced equation solves the equation of Abraham and Lorentz to the second order in `τ`**:
for a solution of `ẍ = u + τ u̇`, `u = g − ω₀² x`, the residual of `ẍ = u + τ x⃛` is exactly
`−τ² ü`. -/
theorem abrahamLorentz_residual {τ ω₀ : ℝ} {g x : Mechanics.TimeFunction}
    (h : IsReducedOscillator τ ω₀ g x) :
    timeDerivative (timeDerivative x) - (g - algebraMap ℝ TimeFunction (ω₀ ^ 2) * x) -
        algebraMap ℝ TimeFunction τ * timeDerivative (timeDerivative (timeDerivative x)) =
      -(algebraMap ℝ TimeFunction τ * algebraMap ℝ TimeFunction τ *
        timeDerivative (timeDerivative (g - algebraMap ℝ TimeFunction (ω₀ ^ 2) * x))) := by
  unfold IsReducedOscillator at h
  rw [h, map_add, SmoothDerivation.map_algebraMap_mul, smul_eq_mul]
  ring

/-! ### The damping force in the relativistic case -/

section Relativistic

open SmoothGeometry.Minkowski Examples

/-- The derivative of the Minkowski product along two curves. -/
theorem hasDerivAt_minkowskiForm {f g : ℝ → Spacetime} {f' g' : Spacetime} {τ : ℝ}
    (hf : HasDerivAt f f' τ) (hg : HasDerivAt g g' τ) :
    HasDerivAt (fun σ => minkowskiForm .timeNegative 3 (f σ) (g σ))
      (minkowskiForm .timeNegative 3 f' (g τ) + minkowskiForm .timeNegative 3 (f τ) g') τ :=
  ((minkowskiForm .timeNegative 3).hasFDerivAt.comp_hasDerivAt τ hf).clm_apply hg

/-- **The force of Lorentz and Dirac** (Landau–Lifshitz (76.2), signature `(−+++)`, `c = 1`,
Heaviside–Lorentz units): for a four-velocity `u(τ)` in the proper time,
`gᵘ = (2/3)(e²/4π) (üᵘ + (ü · u) uᵘ)`, the part of `(2/3)(e²/4π) ü` orthogonal to `u`. -/
def lorentzDiracForce (e : ℝ) (u : ℝ → Spacetime) (τ : ℝ) : Spacetime :=
  (2 / 3 * (e ^ 2 / (4 * π))) • (deriv (deriv u) τ +
    minkowskiForm .timeNegative 3 (deriv (deriv u) τ) (u τ) • u τ)

/-- **The force of Lorentz and Dirac is orthogonal to the four-velocity**: `g · u = 0` when
`u · u = −1`. -/
theorem lorentzDirac_orthogonal (e : ℝ) {u : ℝ → Spacetime} {τ : ℝ}
    (hu : minkowskiForm .timeNegative 3 (u τ) (u τ) = -1) :
    minkowskiForm .timeNegative 3 (lorentzDiracForce e u τ) (u τ) = 0 := by
  simp only [lorentzDiracForce, map_smul, map_add, smul_apply,
    add_apply, smul_eq_mul, hu]
  ring

/-- Along a unit four-velocity, `u̇ · u = 0` and `ü · u = −u̇ · u̇`. -/
theorem minkowskiForm_deriv_of_unit {u : ℝ → Spacetime} (hu : ContDiff ℝ 2 u)
    (hunit : ∀ σ, minkowskiForm .timeNegative 3 (u σ) (u σ) = -1) (τ : ℝ) :
    minkowskiForm .timeNegative 3 (deriv u τ) (u τ) = 0 ∧
      minkowskiForm .timeNegative 3 (deriv (deriv u) τ) (u τ) =
        -minkowskiForm .timeNegative 3 (deriv u τ) (deriv u τ) := by
  have hd1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv u) :=
    (ContDiff.deriv' (n := 1) hu).differentiable (by norm_num)
  have h1 : ∀ σ, minkowskiForm .timeNegative 3 (deriv u σ) (u σ) = 0 := fun σ => by
    have hd := hasDerivAt_minkowskiForm (hd1 σ).hasDerivAt (hd1 σ).hasDerivAt
    have hc : (fun σ => minkowskiForm .timeNegative 3 (u σ) (u σ)) = fun _ => -1 := funext hunit
    rw [hc] at hd
    have := hd.unique (hasDerivAt_const σ (-1))
    rw [minkowskiForm_symmetric .timeNegative (u σ) (deriv u σ)] at this
    linarith
  refine ⟨h1 τ, ?_⟩
  have hd := hasDerivAt_minkowskiForm (hd2 τ).hasDerivAt (hd1 τ).hasDerivAt
  have hc : (fun σ => minkowskiForm .timeNegative 3 (deriv u σ) (u σ)) = fun _ => 0 := funext h1
  rw [hc] at hd
  have := hd.unique (hasDerivAt_const τ 0)
  linarith

/-- Along a unit four-velocity the force of Lorentz and Dirac is
`(2/3)(e²/4π) (ü − (u̇ · u̇) u)`. -/
theorem lorentzDiracForce_eq_of_unit (e : ℝ) {u : ℝ → Spacetime} (hu : ContDiff ℝ 2 u)
    (hunit : ∀ σ, minkowskiForm .timeNegative 3 (u σ) (u σ) = -1) (τ : ℝ) :
    lorentzDiracForce e u τ = (2 / 3 * (e ^ 2 / (4 * π))) • (deriv (deriv u) τ -
      minkowskiForm .timeNegative 3 (deriv u τ) (deriv u τ) • u τ) := by
  rw [lorentzDiracForce, (minkowskiForm_deriv_of_unit hu hunit τ).2, neg_smul, ← sub_eq_add_neg]

/-- The four-momentum radiated per unit proper time, `(2/3)(e²/4π) (u̇ · u̇) u` (73.4); its time
component is the power of Liénard times `dt/dτ` (`Radiation.Relativistic.norm_sq_fourAcceleration`).
-/
def radiatedMomentumRate (e : ℝ) (u : ℝ → Spacetime) (τ : ℝ) : Spacetime :=
  (2 / 3 * (e ^ 2 / (4 * π)) * minkowskiForm .timeNegative 3 (deriv u τ) (deriv u τ)) • u τ

/-- **The balance of the four-momentum** (Landau–Lifshitz §76): along a unit four-velocity, the
impulse of the force of Lorentz and Dirac is the change of the term of Schott
`(2/3)(e²/4π) u̇` minus the four-momentum radiated,
`∫ g dτ = (2/3)(e²/4π) [u̇] − ∫ (2/3)(e²/4π) (u̇ · u̇) u dτ`. -/
theorem integral_lorentzDirac_eq (e : ℝ) {u : ℝ → Spacetime} (hu : ContDiff ℝ 2 u)
    (hunit : ∀ σ, minkowskiForm .timeNegative 3 (u σ) (u σ) = -1) (τ₀ τ₁ : ℝ) :
    ∫ τ in τ₀..τ₁, lorentzDiracForce e u τ =
      (2 / 3 * (e ^ 2 / (4 * π))) • (deriv u τ₁ - deriv u τ₀) -
        ∫ τ in τ₀..τ₁, radiatedMomentumRate e u τ := by
  have hc1 : ContDiff ℝ 1 (deriv u) := ContDiff.deriv' (n := 1) hu
  have hd2 : Differentiable ℝ (deriv u) := hc1.differentiable (by norm_num)
  have hcont2 : Continuous (deriv (deriv u)) := hc1.continuous_deriv le_rfl
  have hrc : Continuous (radiatedMomentumRate e u) :=
    (continuous_const.mul (((minkowskiForm .timeNegative 3).continuous.comp
      hc1.continuous).clm_apply hc1.continuous)).smul hu.continuous
  have he : ∀ τ, lorentzDiracForce e u τ = (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv u) τ -
      radiatedMomentumRate e u τ := fun τ => by
    rw [lorentzDiracForce_eq_of_unit e hu hunit, radiatedMomentumRate, smul_sub, smul_smul]
  have i1 : IntervalIntegrable (fun τ => (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv u) τ)
      MeasureTheory.volume τ₀ τ₁ :=
    (show Continuous fun τ => (2 / 3 * (e ^ 2 / (4 * π))) • deriv (deriv u) τ by
      fun_prop).intervalIntegrable _ _
  simp only [he]
  rw [intervalIntegral.integral_sub i1 (hrc.intervalIntegrable _ _), intervalIntegral.integral_smul,
    intervalIntegral.integral_deriv_eq_sub (fun x _ => hd2 x) (hcont2.intervalIntegrable _ _)]

/-- The Lorentz force is linear in the velocity. -/
theorem lorentzForce_smul (e c : ℝ) (F : TwoForm) (v : Spacetime) :
    lorentzForce e F (c • v) = c • lorentzForce e F v := by
  simp only [lorentzForce, map_smul, smul_comm (-e) c]

/-- The Lorentz force is antisymmetric for the Minkowski product:
`(F♯v) · w = −v · (F♯w)`. -/
theorem minkowskiForm_lorentzForce_swap (e : ℝ) (F : TwoForm) (v w : Spacetime) :
    minkowskiForm .timeNegative 3 (lorentzForce e F v) w =
      -minkowskiForm .timeNegative 3 v (lorentzForce e F w) := by
  rw [lorentzForce_lowered, minkowskiForm_symmetric, lorentzForce_lowered, twoForm_swap F v w]
  ring

/-- A two-form in its first slot: `F(v, w) = Σᵥ vᵛ F(e_ν, w)`. -/
theorem twoForm_apply_eq_sum (F : TwoForm) (v w : Spacetime) :
    F ![v, w] = ∑ ν, v ν * F ![Pi.single ν 1, w] := by
  set L : Spacetime →L[ℝ] ℝ :=
    ((ContinuousLinearMap.apply ℝ ℝ w).comp oneCovector.toContinuousLinearMap).comp F.curryLeft
  have hL : ∀ x, L x = F ![x, w] := fun x => oneCovector_curryLeft F x w
  have hv : v = ∑ ν, v ν • (Pi.single ν 1 : Spacetime) := by
    ext μ
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← hL]
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [map_smul, smul_eq_mul, hL]

/-- The Lorentz force in components: `(eF♯v)^μ = ημμ (−e) Σᵥ vᵛ F(e_ν, e_μ)`. -/
theorem lorentzForce_apply_eq_sum (e : ℝ) (F : TwoForm) (v : Spacetime) (μ : Fin 4) :
    lorentzForce e F v μ = lorentzSign .timeNegative μ *
      (-e * ∑ ν, v ν * F ![Pi.single ν 1, Pi.single μ 1]) := by
  rw [lorentzForce, sharp_apply, smul_apply, oneCovector_curryLeft, smul_eq_mul,
    twoForm_apply_eq_sum]

/-- **The product rule for the Lorentz force** along a world line in a field `F(τ)` whose
components `F(τ)(e_ν, e_μ)` have the derivatives `F'(e_ν, e_μ)`. -/
theorem hasDerivAt_lorentzForce (e : ℝ) {Fx : ℝ → TwoForm} {F' : TwoForm} {u : ℝ → Spacetime}
    {u' : Spacetime} {τ : ℝ}
    (hF : ∀ μ ν : Fin 4, HasDerivAt (fun σ => Fx σ ![Pi.single ν 1, Pi.single μ 1])
      (F' ![Pi.single ν 1, Pi.single μ 1]) τ) (hu : HasDerivAt u u' τ) :
    HasDerivAt (fun σ => lorentzForce e (Fx σ) (u σ))
      (lorentzForce e F' (u τ) + lorentzForce e (Fx τ) u') τ := by
  refine hasDerivAt_pi.mpr fun μ => ?_
  simp only [lorentzForce_apply_eq_sum, Pi.add_apply]
  have hs : HasDerivAt (fun σ => ∑ ν, u σ ν * Fx σ ![Pi.single ν 1, Pi.single μ 1])
      (∑ ν, (u' ν * Fx τ ![Pi.single ν 1, Pi.single μ 1] +
        u τ ν * F' ![Pi.single ν 1, Pi.single μ 1])) τ :=
    HasDerivAt.fun_sum fun ν _ => (hasDerivAt_pi.mp hu ν).mul (hF μ ν)
  convert (hs.const_mul (-e)).const_mul (lorentzSign .timeNegative μ) using 1
  rw [Finset.sum_add_distrib]
  ring

/-- **The reduced force of Landau and Lifshitz** (76.3) in an external field `F` whose derivative
along the world line is `F'`: the force of Lorentz and Dirac evaluated on the motion
`m u̇ = e F♯u` without damping,
`(2/3)(e²/4π) [m⁻¹ e F'♯u + m⁻² (eF♯)²u − m⁻² ((eF♯u) · (eF♯u)) u]`. -/
def landauLifshitzForce (m e : ℝ) (F F' : TwoForm) (u : Spacetime) : Spacetime :=
  (2 / 3 * (e ^ 2 / (4 * π))) • (m⁻¹ • lorentzForce e F' u +
    (m⁻¹ ^ 2) • lorentzForce e F (lorentzForce e F u) -
    (m⁻¹ ^ 2 * minkowskiForm .timeNegative 3 (lorentzForce e F u) (lorentzForce e F u)) • u)

/-- **The reduced force is orthogonal to the four-velocity** for `u · u = −1`. -/
theorem landauLifshitz_orthogonal (m e : ℝ) (F F' : TwoForm) {u : Spacetime}
    (hu : minkowskiForm .timeNegative 3 u u = -1) :
    minkowskiForm .timeNegative 3 (landauLifshitzForce m e F F' u) u = 0 := by
  simp only [landauLifshitzForce, map_smul, map_add, map_sub, smul_apply,
    add_apply, sub_apply, smul_eq_mul, hu,
    lorentzForce_orthogonal, minkowskiForm_lorentzForce_swap e F (lorentzForce e F u) u]
  ring

/-- **The force of Lorentz and Dirac on the undamped motion is the reduced force** (76.3): if
`m u̇ = e F(τ)♯u` along the world line, where the components of the field `F(τ)` at the charge
have the derivatives `F'` at `τ` (`F' = (u · ∂)F` for a field on space-time), then
`g = landauLifshitzForce m e F(τ) F' u`. -/
theorem lorentzDirac_eq_landauLifshitz (m e : ℝ) {u : ℝ → Spacetime} {Fx : ℝ → TwoForm}
    {F' : TwoForm} {τ : ℝ}
    (hF : ∀ μ ν : Fin 4, HasDerivAt (fun σ => Fx σ ![Pi.single ν 1, Pi.single μ 1])
      (F' ![Pi.single ν 1, Pi.single μ 1]) τ)
    (hu : ∀ σ, HasDerivAt u (m⁻¹ • lorentzForce e (Fx σ) (u σ)) σ) :
    lorentzDiracForce e u τ = landauLifshitzForce m e (Fx τ) F' (u τ) := by
  have hd : deriv u = fun σ => m⁻¹ • lorentzForce e (Fx σ) (u σ) := funext fun σ => (hu σ).deriv
  have hdd : deriv (deriv u) τ = m⁻¹ • lorentzForce e F' (u τ) +
      (m⁻¹ ^ 2) • lorentzForce e (Fx τ) (lorentzForce e (Fx τ) (u τ)) := by
    rw [hd]
    have h : HasDerivAt (fun σ => m⁻¹ • lorentzForce e (Fx σ) (u σ))
        (m⁻¹ • (lorentzForce e F' (u τ) + lorentzForce e (Fx τ)
          (m⁻¹ • lorentzForce e (Fx τ) (u τ)))) τ :=
      (hasDerivAt_lorentzForce e hF (hu τ)).const_smul m⁻¹
    rw [h.deriv, lorentzForce_smul, smul_add, smul_smul, sq]
  unfold lorentzDiracForce landauLifshitzForce
  rw [hdd]
  congr 1
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul, lorentzForce_orthogonal,
    minkowskiForm_lorentzForce_swap e (Fx τ) (lorentzForce e (Fx τ) (u τ)) (u τ)]
  module

/-! ### Hyperbolic motion -/

theorem contDiff_hyperbolaVelocity : ContDiff ℝ 2 hyperbolaVelocity := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact Real.contDiff_cosh
  · exact Real.contDiff_sinh
  · exact contDiff_const
  · exact contDiff_const

theorem minkowskiForm_hyperbolaVelocity (τ : ℝ) :
    minkowskiForm .timeNegative 3 (hyperbolaVelocity τ) (hyperbolaVelocity τ) = -1 := by
  simp [minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign, hyperbolaVelocity]
  nlinarith [Real.cosh_sq_sub_sinh_sq τ]

theorem minkowskiForm_hyperbola (τ : ℝ) :
    minkowskiForm .timeNegative 3 (hyperbola τ) (hyperbola τ) = 1 := by
  simp [minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign, hyperbola]
  nlinarith [Real.cosh_sq_sub_sinh_sq τ]

/-- **In hyperbolic motion the force of Lorentz and Dirac vanishes**: for the uniformly
accelerated four-velocity `u = (cosh τ, sinh τ, 0, 0)`, `ü = u` and `u̇ · u̇ = 1`. -/
theorem lorentzDiracForce_hyperbolaVelocity (e τ : ℝ) :
    lorentzDiracForce e hyperbolaVelocity τ = 0 := by
  have hd : deriv hyperbolaVelocity = hyperbola := funext hyperbolaVelocity_deriv
  have hdd : deriv hyperbola = hyperbolaVelocity := funext hyperbola_deriv
  rw [lorentzDiracForce, hd, hdd, minkowskiForm_hyperbolaVelocity]
  simp

/-- The hyperbolic motion of a unit charge of unit mass in the unit constant electric field solves
the equation of Lorentz and Dirac `m u̇ = e F♯u + g` with the same initial data as without
damping. -/
theorem hyperbola_lorentzDirac_equation (τ : ℝ) :
    (1 : ℝ) • deriv hyperbolaVelocity τ =
      lorentzForce 1 (uniformField 1 0) (hyperbolaVelocity τ) +
        lorentzDiracForce 1 hyperbolaVelocity τ := by
  rw [lorentzDiracForce_hyperbolaVelocity, add_zero, one_smul, hyperbolaVelocity_deriv,
    hyperbola_lorentzForce]

/-- **The reduced force in a constant electric field vanishes on the hyperbola**: with `m = e = 1`,
the unit field and `F' = 0`, `landauLifshitzForce = g = 0`. -/
theorem landauLifshitzForce_hyperbola (τ : ℝ) :
    landauLifshitzForce 1 1 (uniformField 1 0) 0 (hyperbolaVelocity τ) = 0 := by
  rw [← lorentzDirac_eq_landauLifshitz 1 1 (Fx := fun _ => uniformField 1 0)
    (fun μ ν => by
      simpa using hasDerivAt_const τ (uniformField 1 0 ![Pi.single ν 1, Pi.single μ 1]))
    (fun σ => ?_), lorentzDiracForce_hyperbolaVelocity]
  rw [inv_one, one_smul, hyperbola_lorentzForce, ← hyperbolaVelocity_deriv]
  exact (contDiff_hyperbolaVelocity.differentiable (by norm_num) σ).hasDerivAt

/-- **The radiated four-momentum in hyperbolic motion is supplied by the term of Schott**: the
charge radiates `∫ (2/3)(e²/4π) (u̇ · u̇) u dτ = (2/3)(e²/4π) [u̇]` while the force of Lorentz and
Dirac vanishes. -/
theorem integral_radiatedMomentumRate_hyperbola (e τ₀ τ₁ : ℝ) :
    ∫ τ in τ₀..τ₁, radiatedMomentumRate e hyperbolaVelocity τ =
      (2 / 3 * (e ^ 2 / (4 * π))) • (hyperbola τ₁ - hyperbola τ₀) := by
  have h := integral_lorentzDirac_eq e contDiff_hyperbolaVelocity minkowskiForm_hyperbolaVelocity
    τ₀ τ₁
  simp only [lorentzDiracForce_hyperbolaVelocity, intervalIntegral.integral_zero,
    hyperbolaVelocity_deriv] at h
  rw [eq_comm, sub_eq_zero] at h
  exact h.symm

/-! ### The nonrelativistic limit -/

/-- The Lorentz factor `γ = (1 − ẋ²)^{−1/2}` of a path `x(t)` in the coordinate time. -/
def lorentzFactor (x : ℝ → E3) (t : ℝ) : ℝ := (√(1 - ‖deriv x t‖ ^ 2))⁻¹

/-- The four-velocity `γ (1, ẋ)` of a path, as a function of the coordinate time. -/
def pathFourVelocity (x : ℝ → E3) (t : ℝ) : Spacetime :=
  lorentzFactor x t • Minkowski.vector 1 (deriv x t)

/-- The Minkowski product of two vectors `(a, y)` and `(b, z)` is `−ab + y · z`. -/
theorem minkowskiForm_vector (a b : ℝ) (y z : E3) :
    minkowskiForm .timeNegative 3 (Minkowski.vector a y) (Minkowski.vector b z) =
      -(a * b) + inner ℝ y z := by
  rw [metric_eq, pair_apply]
  simp
  ring

/-- The four-velocity of a path is a unit vector. -/
theorem minkowskiForm_pathFourVelocity {x : ℝ → E3} {t : ℝ} (hv : ‖deriv x t‖ < 1) :
    minkowskiForm .timeNegative 3 (pathFourVelocity x t) (pathFourVelocity x t) = -1 := by
  have hpos : 0 < 1 - ‖deriv x t‖ ^ 2 := by nlinarith [norm_nonneg (deriv x t)]
  have hs := Real.sq_sqrt hpos.le
  have hs0 := (Real.sqrt_pos.mpr hpos).ne'
  simp only [pathFourVelocity, map_smul, smul_apply, smul_eq_mul, minkowskiForm_vector,
    real_inner_self_eq_norm_sq, lorentzFactor]
  field_simp
  linarith

theorem contDiff_vector (c : ℝ) {y : ℝ → E3} (hy : ContDiff ℝ ∞ y) :
    ContDiff ℝ ∞ fun t => Minkowski.vector c (y t) := by
  refine contDiff_pi.mpr fun μ => ?_
  refine Fin.cases ?_ (fun i => ?_) μ
  · simpa using (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => c)
  · have h := (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).contDiff.comp hy
    simp only [Minkowski.vector_succ]
    exact h

theorem hasDerivAt_vector (c : ℝ) {y : ℝ → E3} {y' : E3} {t : ℝ} (hy : HasDerivAt y y' t) :
    HasDerivAt (fun s => Minkowski.vector c (y s)) (Minkowski.vector 0 y') t := by
  refine hasDerivAt_pi.mpr fun μ => ?_
  refine Fin.cases ?_ (fun i => ?_) μ
  · simpa using hasDerivAt_const t c
  · simpa using hasDerivAt_component_path hy i

theorem contDiff_lorentzFactor {x : ℝ → E3} (hx : ContDiff ℝ ∞ x) (hv : ∀ t, ‖deriv x t‖ < 1) :
    ContDiff ℝ ∞ (lorentzFactor x) := by
  have hd : ContDiff ℝ ∞ (deriv x) := (contDiff_infty_iff_deriv.mp hx).2
  have hpos : ∀ t, 0 < 1 - ‖deriv x t‖ ^ 2 := fun t => by
    nlinarith [hv t, norm_nonneg (deriv x t)]
  have hsq := (contDiff_const.sub (hd.norm_sq ℝ)).sqrt fun t => (hpos t).ne'
  exact hsq.inv fun t => (Real.sqrt_pos.mpr (hpos t)).ne'

/-- At an instant of rest the Lorentz factor is stationary: `γ̇ = γ³ ẋ · ẍ = 0`. -/
theorem hasDerivAt_lorentzFactor_of_rest {x : ℝ → E3} (hx : ContDiff ℝ ∞ x)
    (hv : ∀ t, ‖deriv x t‖ < 1) {t₀ : ℝ} (h0 : deriv x t₀ = 0) :
    HasDerivAt (lorentzFactor x) 0 t₀ := by
  have hd2 : Differentiable ℝ (deriv x) :=
    ((contDiff_infty_iff_deriv.mp hx).2).differentiable (by simp)
  have hq : HasDerivAt (fun t => ‖deriv x t‖ ^ 2)
      (2 * inner ℝ (deriv x t₀) (deriv (deriv x) t₀)) t₀ := (hd2 t₀).hasDerivAt.norm_sq
  rw [h0, inner_zero_left, mul_zero] at hq
  have h1 : 0 < 1 - ‖deriv x t₀‖ ^ 2 := by nlinarith [hv t₀, norm_nonneg (deriv x t₀)]
  have hf : DifferentiableAt ℝ (fun s : ℝ => (√(1 - s))⁻¹) (‖deriv x t₀‖ ^ 2) :=
    (((differentiableAt_const 1).sub differentiableAt_id).sqrt h1.ne').inv
      (Real.sqrt_pos.mpr h1).ne'
  have h := hf.hasDerivAt.comp t₀ hq
  rw [mul_zero] at h
  exact h

/-- **The second derivative in the proper time at an instant of rest**: if `θ(τ)` is the
coordinate time, `θ' = γ(θ)`, then at a proper time where `γ = 1` and `γ̇ = 0` the second
derivative of `U(θ(τ))` is `Ü(θ(τ))`. -/
theorem deriv_deriv_comp_of_rest {U : ℝ → Spacetime} (hU : ContDiff ℝ 2 U) {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ 1 γ) {θ : ℝ → ℝ} (hθ : ∀ τ, HasDerivAt θ (γ (θ τ)) τ) {τ₀ : ℝ}
    (h1 : γ (θ τ₀) = 1) (h0 : deriv γ (θ τ₀) = 0) :
    deriv (deriv fun τ => U (θ τ)) τ₀ = deriv (deriv U) (θ τ₀) := by
  have hU1 : Differentiable ℝ U := hU.differentiable (by norm_num)
  have hU2 : Differentiable ℝ (deriv U) :=
    (ContDiff.deriv' (n := 1) hU).differentiable (by norm_num)
  have hγd : Differentiable ℝ γ := hγ.differentiable (by norm_num)
  have hd : deriv (fun τ => U (θ τ)) = fun τ => γ (θ τ) • deriv U (θ τ) := funext fun τ =>
    ((hU1 (θ τ)).hasDerivAt.scomp τ (hθ τ)).deriv
  rw [hd]
  have hG : HasDerivAt (fun t => γ t • deriv U t)
      (γ (θ τ₀) • deriv (deriv U) (θ τ₀) + deriv γ (θ τ₀) • deriv U (θ τ₀)) (θ τ₀) :=
    (hγd _).hasDerivAt.smul (hU2 _).hasDerivAt
  have h2 := hG.scomp τ₀ (hθ τ₀)
  rw [show (fun τ => γ (θ τ) • deriv U (θ τ)) = (fun t => γ t • deriv U t) ∘ θ from rfl,
    h2.deriv, h1, h0]
  simp

/-- At an instant of rest `Ü = γ̈ (1, 0) + (0, x⃛)` for the four-velocity in the coordinate
time. -/
theorem deriv_deriv_pathFourVelocity_of_rest {x : ℝ → E3} (hx : ContDiff ℝ ∞ x)
    (hv : ∀ t, ‖deriv x t‖ < 1) {t₀ : ℝ} (h0 : deriv x t₀ = 0) :
    ∃ c : ℝ, deriv (deriv (pathFourVelocity x)) t₀ =
      c • Minkowski.vector 1 0 + Minkowski.vector 0 (deriv^[3] x t₀) := by
  have hγ := contDiff_lorentzFactor hx hv
  have hγ1 : Differentiable ℝ (lorentzFactor x) := hγ.differentiable (by simp)
  have hγ2 : Differentiable ℝ (deriv (lorentzFactor x)) :=
    ((contDiff_infty_iff_deriv.mp hγ).2).differentiable (by simp)
  have hd1 : ContDiff ℝ ∞ (deriv x) := (contDiff_infty_iff_deriv.mp hx).2
  have hd2 : ContDiff ℝ ∞ (deriv (deriv x)) := (contDiff_infty_iff_deriv.mp hd1).2
  have hd3 : Differentiable ℝ (deriv (deriv x)) := hd2.differentiable (by simp)
  have hw : ∀ t, HasDerivAt (fun s => Minkowski.vector 1 (deriv x s))
      (Minkowski.vector 0 (deriv (deriv x) t)) t := fun t =>
    hasDerivAt_vector 1 ((hd1.differentiable (by simp)) t).hasDerivAt
  have hw' : ∀ t, HasDerivAt (fun s => Minkowski.vector 0 (deriv (deriv x) s))
      (Minkowski.vector 0 (deriv (deriv (deriv x)) t)) t := fun t =>
    hasDerivAt_vector 0 (hd3 t).hasDerivAt
  have hU : deriv (pathFourVelocity x) = fun t => lorentzFactor x t •
      Minkowski.vector 0 (deriv (deriv x) t) + deriv (lorentzFactor x) t •
        Minkowski.vector 1 (deriv x t) := funext fun t =>
    ((hγ1 t).hasDerivAt.smul (hw t)).deriv
  have hU' : HasDerivAt (deriv (pathFourVelocity x))
      ((lorentzFactor x t₀ • Minkowski.vector 0 (deriv (deriv (deriv x)) t₀) +
        deriv (lorentzFactor x) t₀ • Minkowski.vector 0 (deriv (deriv x) t₀)) +
      (deriv (lorentzFactor x) t₀ • Minkowski.vector 0 (deriv (deriv x) t₀) +
        deriv (deriv (lorentzFactor x)) t₀ • Minkowski.vector 1 (deriv x t₀))) t₀ := by
    rw [hU]
    exact ((hγ1 t₀).hasDerivAt.smul (hw' t₀)).add ((hγ2 t₀).hasDerivAt.smul (hw t₀))
  have h1 : lorentzFactor x t₀ = 1 := by simp [lorentzFactor, h0]
  have h0' : deriv (lorentzFactor x) t₀ = 0 := (hasDerivAt_lorentzFactor_of_rest hx hv h0).deriv
  refine ⟨deriv (deriv (lorentzFactor x)) t₀, ?_⟩
  rw [hU'.deriv, h1, h0', h0]
  simp only [one_smul, zero_smul, add_zero, zero_add]
  rw [add_comm]
  rfl

/-- **The force of Lorentz and Dirac reduces to the damping force of §75 at rest**
(Landau–Lifshitz §76): for a path `x(t)` with `|ẋ| < 1`, its four-velocity `u(τ) = γ(1, ẋ)(θ(τ))`
in the proper time, where the coordinate time `θ(τ)` has `θ' = γ(θ)`, and an instant `τ₀` of rest
`ẋ(θ(τ₀)) = 0`, the force of Lorentz and Dirac is `(0, (2/3)(e²/4π) x⃛)`: its time component
vanishes and its spatial part is the damping force `(2/3)(e²/4π) v̈` (75.8). -/
theorem lorentzDirac_nonrelativistic (e : ℝ) {x : ℝ → E3} (hx : ContDiff ℝ ∞ x)
    (hv : ∀ t, ‖deriv x t‖ < 1) {θ : ℝ → ℝ} (hθ : ∀ τ, HasDerivAt θ (lorentzFactor x (θ τ)) τ)
    {τ₀ : ℝ} (hrest : deriv x (θ τ₀) = 0) :
    lorentzDiracForce e (fun τ => pathFourVelocity x (θ τ)) τ₀ =
      Minkowski.vector 0 ((2 / 3 * (e ^ 2 / (4 * π))) • deriv^[3] x (θ τ₀)) := by
  have hγ := contDiff_lorentzFactor hx hv
  have hU : ContDiff ℝ ∞ (pathFourVelocity x) :=
    hγ.smul (contDiff_vector 1 (contDiff_infty_iff_deriv.mp hx).2)
  have h1 : lorentzFactor x (θ τ₀) = 1 := by simp [lorentzFactor, hrest]
  have h0 : deriv (lorentzFactor x) (θ τ₀) = 0 :=
    (hasDerivAt_lorentzFactor_of_rest hx hv hrest).deriv
  have hU0 : pathFourVelocity x (θ τ₀) = Minkowski.vector 1 0 := by
    simp [pathFourVelocity, h1, hrest]
  obtain ⟨c, hc⟩ := deriv_deriv_pathFourVelocity_of_rest hx hv hrest
  rw [lorentzDiracForce,
    deriv_deriv_comp_of_rest (hU.of_le (by simp)) (hγ.of_le (by simp)) hθ h1 h0,
    hc, hU0]
  have hg : minkowskiForm .timeNegative 3
      (c • Minkowski.vector 1 0 + Minkowski.vector 0 (deriv^[3] x (θ τ₀)))
        (Minkowski.vector 1 0) = -c := by
    rw [map_add, map_smul, add_apply, smul_apply, minkowskiForm_vector, minkowskiForm_vector]
    simp
  rw [hg]
  ext μ
  refine Fin.cases ?_ (fun i => ?_) μ <;> simp

/-- The hyperbolic motion `x(t) = (√(1 + t²) − 1) e₁` in the coordinate time. -/
def hyperbolicPath (t : ℝ) : E3 := (√(1 + t ^ 2) - 1) • EuclideanSpace.single 0 1

theorem deriv_hyperbolicPath (t : ℝ) :
    deriv hyperbolicPath t = (t / √(1 + t ^ 2)) • EuclideanSpace.single 0 1 := by
  have h1 : 1 + t ^ 2 ≠ 0 := by positivity
  have hs : HasDerivAt (fun t : ℝ => √(1 + t ^ 2)) ((0 + 2 * t ^ 1 * 1) / (2 * √(1 + t ^ 2))) t :=
    ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id' t).pow 2)).sqrt h1
  have h := (hs.sub_const 1).smul_const (EuclideanSpace.single 0 1 : E3)
  rw [show hyperbolicPath = fun t => (√(1 + t ^ 2) - 1) • EuclideanSpace.single 0 1 from rfl,
    h.deriv]
  congr 1
  rw [zero_add, pow_one, mul_one, mul_div_mul_left _ _ two_ne_zero]

theorem contDiff_hyperbolicPath : ContDiff ℝ ∞ hyperbolicPath :=
  (((contDiff_const.add (contDiff_id.pow 2)).sqrt fun t => by positivity).sub
    contDiff_const).smul contDiff_const

theorem norm_deriv_hyperbolicPath_lt (t : ℝ) : ‖deriv hyperbolicPath t‖ < 1 := by
  have hp : 0 < √(1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hlt : |t| < √(1 + t ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg t) (by linarith)
  rw [deriv_hyperbolicPath, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs,
    abs_div, abs_of_pos hp, div_lt_one hp]
  exact hlt

/-- In the proper time `τ` of the hyperbolic motion the coordinate time is `sinh τ`. -/
theorem lorentzFactor_hyperbolicPath (τ : ℝ) : lorentzFactor hyperbolicPath (Real.sinh τ) =
    Real.cosh τ := by
  have hc : √(1 + Real.sinh τ ^ 2) = Real.cosh τ := by
    rw [← Real.cosh_sq', Real.sqrt_sq (Real.cosh_pos τ).le]
  have hpos := Real.cosh_pos τ
  rw [lorentzFactor, deriv_hyperbolicPath, hc, norm_smul, PiLp.norm_single, norm_one, mul_one,
    Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_pow, sq_abs]
  have h1 : 1 - Real.sinh τ ^ 2 / Real.cosh τ ^ 2 = (Real.cosh τ)⁻¹ ^ 2 := by
    calc 1 - Real.sinh τ ^ 2 / Real.cosh τ ^ 2 =
          (Real.cosh τ ^ 2 - Real.sinh τ ^ 2) / Real.cosh τ ^ 2 := by field_simp
      _ = (Real.cosh τ)⁻¹ ^ 2 := by rw [Real.cosh_sq_sub_sinh_sq, inv_pow, one_div]
  rw [h1, Real.sqrt_sq (by positivity), inv_inv]

/-- **An instance of `lorentzDirac_nonrelativistic`**: the hyperbolic motion with the proper time
`θ = sinh`, at its instant of rest `τ = 0`, where the acceleration `ẍ(0) = e₁` does not vanish. -/
theorem lorentzDirac_nonrelativistic_hyperbolic (e : ℝ) :
    lorentzDiracForce e (fun τ => pathFourVelocity hyperbolicPath (Real.sinh τ)) 0 =
      Minkowski.vector 0 ((2 / 3 * (e ^ 2 / (4 * π))) • deriv^[3] hyperbolicPath (Real.sinh 0)) :=
  lorentzDirac_nonrelativistic e contDiff_hyperbolicPath norm_deriv_hyperbolicPath_lt
    (fun τ => by rw [lorentzFactor_hyperbolicPath]; exact Real.hasDerivAt_sinh τ)
    (by simp [deriv_hyperbolicPath])

end Relativistic

end ProjectAinos.Electrodynamics.RadiationReaction
