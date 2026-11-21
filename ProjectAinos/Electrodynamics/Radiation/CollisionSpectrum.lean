/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Relativistic
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Radiation of low frequency in collisions

Landau–Lifshitz, *The Classical Theory of Fields*, §69, with the time transform of the far-zone
radiation amplitude of a point charge that §64 leaves out. The units have `c = 1` and
`div E = k⁰`. The Fourier transform has Mathlib's normalization `𝓕g(ν) = ∫ e^{−2πiνt} g(t) dt`
in the frequency `ν = ω/2π`; a real vector function `f` is transformed as `complexify ∘ f`, with
`complexify : ℝ³ →L[ℝ] ℂ³` (`norm_complexify`).

* `tendsto_fourier_complexify`: the transform of an integrable `f` is continuous and equals
  `∫ f` at `ν = 0`; `norm_fourier_complexify_neg`: `|𝓕f(−ν)| = |𝓕f(ν)|` for a real `f`.
* **The dipole spectrum** (69.1). `tendsto_fourier_acceleration`: for a velocity `v` with an
  integrable derivative `a` and the limits `v₁`, `v₂` at `∓∞`, `𝓕a(ν) → v₂ − v₁` as `ν → 0`.
  `dipoleSpectrum e a ν = (2/3)(e²/4π)|𝓕a(ν)|²` is the density over all `ν ∈ ℝ`, even in `ν`
  (`dipoleSpectrum_neg`); it tends to `(2/3)(e²/4π)|v₂ − v₁|²` (`tendsto_dipoleSpectrum`), and the
  density over `ν > 0`, twice it, to `(4/3)(e²/4π)|v₂ − v₁|²`
  (`tendsto_two_mul_dipoleSpectrum`), that is `(2/3π)(e²/4π)|v₂ − v₁|²` per unit `ω`.
* **The time of the observer** in the direction `n`, `observerTime w n τ = τ − n·r(τ)`, for a
  subluminal world line `w`: it is onto (`surjective_observerTime`) and strictly increasing
  (`strictMono_observerTime`), with `dt/dτ = 1 − n·v ≥ 1 − v₀ > 0` (`hasDerivAt_observerTime`).
  Its inverse `retardedOfObserver` is continuous with `dτ/dt = 1/(1 − n·v)`
  (`hasDerivAt_retardedOfObserver`).
* **The radiation amplitude** `amplitude e w n τ = e n × ((n − v) × v̇)/(4π(1 − n·v)³)`: on the
  light cone of `r(τ)`, `ρ E_a = A` for the acceleration field (`smul_accelerationField_lightCone`)
  and `ρ² S·n → |A|²` (`tendsto_sq_mul_inner_poyntingVector_lightCone_eq`). With
  `velocityAmplitude e n v = e n × (n × v)/(4π(1 − n·v))`,
  `d/dτ velocityAmplitude e n v(τ) = (1 − n·v) A` (`hasDerivAt_velocityAmplitude`), so that the
  amplitude in the time of the observer, `observedAmplitude e w n t = A(τ(t), n)`, is
  `d/dt velocityAmplitude e n v(τ(t))` (`hasDerivAt_velocityAmplitude_retardedOfObserver`,
  `radiationAmplitude_eq_deriv`).
* **The spectral resolution of the amplitude**, `fourier_radiationAmplitude`:
  `∫ e^{−2πiνt} A dt = ∫ e^{−2πiν(τ − n·r(τ))} (1 − n·v) A dτ` by the change of variables
  `t = τ − n·r(τ)`; `fourier_radiationAmplitude_eq_deriv` writes the integrand as the total
  derivative of the velocity amplitude, as Landau–Lifshitz do before (69.2).
* **The low-frequency limit** (69.2). For an integrable acceleration
  (`integrable_observedAmplitude`) with the asymptotic velocities `v₁`, `v₂`, `∫ A dt` is the
  change of the velocity amplitude (`integral_observedAmplitude`). The angular spectral density
  `angularSpectrum e w n ν = |𝓕A(ν)|²`, even in `ν` (`angularSpectrum_neg`), tends to
  `|velocityAmplitude e n v₂ − velocityAmplitude e n v₁|²` as `ν → 0`
  (`tendsto_fourier_observedAmplitude`, `tendsto_relativisticSpectrum`), and the density over
  `ν > 0` to twice it (`tendsto_two_mul_relativisticSpectrum`).
* **The total low-frequency spectrum over the directions.** In the slow limit the one-sided
  density `2|(e/4π) n × (n × Δv)|²` integrates to the dipole value `(4/3)(e²/4π)|Δv|²`
  (`integral_two_mul_norm_sq_smul_cross_cross`). For a charge that starts suddenly, `v₁ = 0` and
  `|v₂| = β`, it is `(e²/2π)((1/β) log((1 + β)/(1 − β)) − 2)`
  (`integral_two_mul_norm_sq_velocityAmplitude`), by Archimedes and
  `∫_{−1}^{1} (1 − s²)/(1 − βs)² ds = 2(log((1 + β)/(1 − β)) − 2β)/β³`
  (`integral_one_sub_sq_div_one_sub_mul_sq`).
* An instance: `arctanWorldline β`, `|β| < 1`, with the velocity `(2β/π) arctan t e₁`, has an
  integrable acceleration and the asymptotic velocities `∓β e₁`. In the direction `e₂` the angular
  density tends to `(eβ/2π)²` (`tendsto_angularSpectrum_arctanWorldline`), and the dipole density
  of its acceleration to `(2/3)(e²/4π)(2β)²` (`tendsto_dipoleSpectrum_arctanPath`).

The spectral densities are those of the far-zone amplitude of a given trajectory. By Plancherel,
their integrals over `ν` are `∫ (2/3)(e²/4π)|a|² dt` and `∫ |A|² dt` when `a` and `A` are square
integrable; that identity is not used here. The identification
of `∫ |A|² dt` with the energy that crosses a sphere at infinity over all times is not stated: the
far-zone limits of `Radiation.Relativistic` are taken along the light cone at a fixed retarded
time, and a world line with distinct asymptotic velocities is unbounded in space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter Real
open scoped Topology FourierTransform ContDiff ComplexConjugate

namespace ProjectAinos.Electrodynamics.Radiation.CollisionSpectrum

open SmoothGeometry SmoothGeometry.Sphere Relativistic

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "C3" => EuclideanSpace ℂ (Fin 3)

/-! ### Complex vectors and the Fourier transform at low frequency -/

/-- The **complexification** `ℝ³ → ℂ³` of the components, as a continuous real-linear map. The
Fourier transform `𝓕g(ν) = ∫ e^{−2πiνt} g(t) dt` of a real vector function `f` is that of
`g = complexify ∘ f`. -/
def complexify : E3 →L[ℝ] C3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 fun i => (x i : ℂ)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun c x => by ext i; simp }

/-- The components of `complexify x` are those of `x`. -/
theorem complexify_apply (x : E3) (i : Fin 3) : complexify x i = (x i : ℂ) := rfl

/-- The complexification preserves the Euclidean norm. -/
theorem norm_complexify (x : E3) : ‖complexify x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [complexify_apply, Complex.norm_real]

/-- The complexification is injective. -/
theorem complexify_injective : Function.Injective complexify := by
  intro x y h
  rw [← sub_eq_zero, ← norm_eq_zero, ← norm_complexify, map_sub, h, sub_self, norm_zero]

/-- **The Fourier transform at low frequency**: for an integrable `f : ℝ → ℝ³` the transform
`ν ↦ ∫ e^{−2πiνt} f(t) dt` is continuous, so it tends to `∫ f` as `ν → 0`. -/
theorem tendsto_fourier_complexify {f : ℝ → E3} (hf : Integrable f) :
    Tendsto (𝓕 (fun t => complexify (f t))) (𝓝 0) (𝓝 (complexify (∫ t, f t))) := by
  have hcf : Integrable fun t => complexify (f t) := complexify.integrable_comp hf
  have hcont : Continuous (𝓕 (fun t => complexify (f t))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hcf
  have h0 : 𝓕 (fun t => complexify (f t)) 0 = complexify (∫ t, f t) := by
    rw [Real.fourier_real_eq]
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
    exact complexify.integral_comp_comm hf
  rw [← h0]
  exact hcont.tendsto 0

/-- The components of the Fourier transform of `complexify ∘ f` for an integrable `f`. -/
theorem fourier_complexify_apply {f : ℝ → E3} (hf : Integrable f) (ν : ℝ) (i : Fin 3) :
    𝓕 (fun t => complexify (f t)) ν i = ∫ t, (𝐞 (-(t * ν)) : ℂ) * (f t i : ℂ) := by
  have hcf : Integrable fun t => complexify (f t) := complexify.integrable_comp hf
  have hint : Integrable fun t => 𝐞 (-(t * ν)) • complexify (f t) := by
    refine hcf.norm.mono' ?_ (Eventually.of_forall fun t => by rw [Circle.norm_smul])
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).aestronglyMeasurable).smul hcf.1
  rw [Real.fourier_real_eq]
  rw [show (∫ t, 𝐞 (-(t * ν)) • complexify (f t)) i =
      (EuclideanSpace.proj i : C3 →L[ℂ] ℂ) (∫ t, 𝐞 (-(t * ν)) • complexify (f t)) from rfl,
    ← (EuclideanSpace.proj i : C3 →L[ℂ] ℂ).integral_comp_comm hint]
  rfl

/-- **The spectrum of a real function is even**: for an integrable `f : ℝ → ℝ³` the transform at
`−ν` is the complex conjugate of that at `ν`, so that `|𝓕f(−ν)| = |𝓕f(ν)|`. -/
theorem norm_fourier_complexify_neg {f : ℝ → E3} (hf : Integrable f) (ν : ℝ) :
    ‖𝓕 (fun t => complexify (f t)) (-ν)‖ = ‖𝓕 (fun t => complexify (f t)) ν‖ := by
  have hconj (i : Fin 3) : 𝓕 (fun t => complexify (f t)) (-ν) i =
      conj (𝓕 (fun t => complexify (f t)) ν i) := by
    rw [fourier_complexify_apply hf, fourier_complexify_apply hf, ← integral_conj]
    congr 1
    ext t
    rw [map_mul, Complex.conj_ofReal, Real.fourierChar_apply, Real.fourierChar_apply,
      ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 2
    push_cast
    ring
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp only [hconj, RCLike.norm_conj]

/-! ### The spectrum of the dipole radiation -/

/-- **The low-frequency limit of the Fourier transform of the acceleration**: if the velocity
`v` has the integrable derivative `a` and the limits `v₁`, `v₂` at `∓∞`, then
`𝓕a(ν) = ∫ e^{−2πiνt} a(t) dt` tends to `v₂ − v₁` as `ν → 0`: at the frequency zero it is
`∫ a = v₂ − v₁`, and the transform of an integrable function is continuous. -/
theorem tendsto_fourier_acceleration {v a : ℝ → E3} {v₁ v₂ : E3}
    (hv : ∀ t, HasDerivAt v (a t) t) (ha : Integrable a) (hbot : Tendsto v atBot (𝓝 v₁))
    (htop : Tendsto v atTop (𝓝 v₂)) :
    Tendsto (𝓕 (fun t => complexify (a t))) (𝓝 0) (𝓝 (complexify (v₂ - v₁))) := by
  rw [← integral_of_hasDerivAt_of_tendsto hv ha hbot htop]
  exact tendsto_fourier_complexify ha

/-- **The spectral density of the dipole radiation** of a charge `e` with the acceleration
`a(t)`, `(2/3)(e²/4π)|𝓕a(ν)|²` with `𝓕a(ν) = ∫ e^{−2πiνt} a(t) dt`, in Mathlib's normalization:
by Plancherel's theorem its integral over all frequencies `ν ∈ ℝ` is the energy
`∫ (2/3)(e²/4π)|a|² dt` radiated with the dipole power (67.8) of `d = e r`. It is even in `ν`
(`dipoleSpectrum_neg`), so the density over `ν > 0` is twice it, and the density over the
angular frequency `ω = 2πν > 0` is `(2/3)(e²/4π)|𝓕a|²/π`, Landau–Lifshitz's
`(4/3)(e²/4π)|a_ω|² dω/2π` with `a_ω = ∫ a e^{iωt} dt`. -/
def dipoleSpectrum (e : ℝ) (a : ℝ → E3) (ν : ℝ) : ℝ :=
  2 / 3 * (e ^ 2 / (4 * π)) * ‖𝓕 (fun t => complexify (a t)) ν‖ ^ 2

/-- The dipole spectral density is even in the frequency. -/
theorem dipoleSpectrum_neg (e : ℝ) {a : ℝ → E3} (ha : Integrable a) (ν : ℝ) :
    dipoleSpectrum e a (-ν) = dipoleSpectrum e a ν := by
  rw [dipoleSpectrum, dipoleSpectrum, norm_fourier_complexify_neg ha]

/-- **The low-frequency limit of the dipole spectrum** (Landau–Lifshitz (69.1)): the spectral
density tends to `(2/3)(e²/4π)|v₂ − v₁|²` as `ν → 0`; it depends only on the change of the
velocity in the collision. -/
theorem tendsto_dipoleSpectrum (e : ℝ) {v a : ℝ → E3} {v₁ v₂ : E3}
    (hv : ∀ t, HasDerivAt v (a t) t) (ha : Integrable a) (hbot : Tendsto v atBot (𝓝 v₁))
    (htop : Tendsto v atTop (𝓝 v₂)) :
    Tendsto (dipoleSpectrum e a) (𝓝 0) (𝓝 (2 / 3 * (e ^ 2 / (4 * π)) * ‖v₂ - v₁‖ ^ 2)) := by
  have h := ((tendsto_fourier_acceleration hv ha hbot htop).norm.pow 2).const_mul
    (2 / 3 * (e ^ 2 / (4 * π)))
  rwa [norm_complexify] at h

/-- **The one-sided low-frequency limit**: the density over the frequencies `ν > 0`, twice
`dipoleSpectrum`, tends to `(4/3)(e²/4π)|v₂ − v₁|²` as `ν → 0⁺`, that is
`(2/3π)(e²/4π)|v₂ − v₁|²` per unit angular frequency, Landau–Lifshitz's
`(2e²/3πc³)(v₂ − v₁)²` in Heaviside–Lorentz units. -/
theorem tendsto_two_mul_dipoleSpectrum (e : ℝ) {v a : ℝ → E3} {v₁ v₂ : E3}
    (hv : ∀ t, HasDerivAt v (a t) t) (ha : Integrable a) (hbot : Tendsto v atBot (𝓝 v₁))
    (htop : Tendsto v atTop (𝓝 v₂)) :
    Tendsto (fun ν => 2 * dipoleSpectrum e a ν) (𝓝[>] 0)
      (𝓝 (4 / 3 * (e ^ 2 / (4 * π)) * ‖v₂ - v₁‖ ^ 2)) := by
  have h := ((tendsto_dipoleSpectrum e hv ha hbot htop).const_mul 2).mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  convert h using 2
  ring

/-! ### The time of the observer -/

/-- The **time of the observer** in the direction `n`, `t = τ − n·r(τ)`: the light emitted at
the retarded time `τ` reaches the point `R n` at the time `R + τ − n·r(τ) + O(1/R)`, and `t` is
this time less `R`. -/
def observerTime (w : SubluminalWorldline) (n : E3) (τ : ℝ) : ℝ := τ - inner ℝ n (w.r τ)

variable (w : SubluminalWorldline)

/-- `dt/dτ = 1 − n·v`. -/
theorem hasDerivAt_observerTime (n : E3) (τ : ℝ) :
    HasDerivAt (observerTime w n) (1 - inner ℝ n (deriv w.r τ)) τ := by
  have h := (hasDerivAt_const τ n).inner ℝ (w.differentiable_r τ).hasDerivAt
  simp only [inner_zero_left, add_zero] at h
  exact (hasDerivAt_id τ).sub h

/-- The time of the observer is continuous. -/
theorem continuous_observerTime (n : E3) : Continuous (observerTime w n) :=
  continuous_id.sub (continuous_const.inner w.contDiff_r.continuous)

/-- `1 − v₀ > 0`. -/
theorem one_sub_v₀_pos : 0 < 1 - w.v₀ := by linarith [w.v₀_lt_one]

/-- `1 − n·v ≥ 1 − v₀` for a unit vector `n`. -/
theorem one_sub_v₀_le (τ : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    1 - w.v₀ ≤ 1 - inner ℝ n (deriv w.r τ) := by
  have h1 := real_inner_le_norm n (deriv w.r τ)
  rw [hn, one_mul] at h1
  linarith [w.norm_deriv_le τ]

/-- The time of the observer grows at least at the rate `1 − v₀`:
`t(τ₂) − t(τ₁) ≥ (1 − v₀)(τ₂ − τ₁)` for `τ₁ ≤ τ₂`. -/
theorem mul_sub_le_observerTime_sub {n : E3} (hn : ‖n‖ = 1) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    (1 - w.v₀) * (τ₂ - τ₁) ≤ observerTime w n τ₂ - observerTime w n τ₁ := by
  have h1 := real_inner_le_norm n (w.r τ₂ - w.r τ₁)
  have h2 := w.norm_sub_le τ₁ τ₂
  rw [abs_of_nonneg (sub_nonneg.mpr h)] at h2
  rw [hn, one_mul, inner_sub_right] at h1
  simp only [observerTime]
  nlinarith

/-- The time of the observer is strictly increasing. -/
theorem strictMono_observerTime {n : E3} (hn : ‖n‖ = 1) : StrictMono (observerTime w n) := by
  intro τ₁ τ₂ h
  have h1 := mul_sub_le_observerTime_sub w hn h.le
  have h2 := mul_pos (one_sub_v₀_pos w) (sub_pos.mpr h)
  linarith

/-- Every time of the observer is reached: `t(τ) → ±∞` as `τ → ±∞`. -/
theorem surjective_observerTime {n : E3} (hn : ‖n‖ = 1) :
    Function.Surjective (observerTime w n) := by
  have hv := one_sub_v₀_pos w
  refine (continuous_observerTime w n).surjective ?_ ?_
  · refine tendsto_atTop_mono' atTop ?_
      (tendsto_atTop_add_const_right _ (observerTime w n 0) (tendsto_id.const_mul_atTop hv))
    filter_upwards [eventually_ge_atTop 0] with τ hτ
    have := mul_sub_le_observerTime_sub w hn hτ
    simp only [id, sub_zero] at this ⊢
    linarith
  · refine tendsto_atBot_mono' atBot ?_
      (tendsto_atBot_add_const_right _ (observerTime w n 0) (tendsto_id.const_mul_atBot hv))
    filter_upwards [eventually_le_atBot 0] with τ hτ
    have := mul_sub_le_observerTime_sub w hn hτ
    simp only [id, zero_sub] at this ⊢
    linarith

/-- The **retarded time as a function of the time of the observer**, the inverse of
`observerTime`. -/
def retardedOfObserver (w : SubluminalWorldline) (n : E3) : ℝ → ℝ :=
  Function.invFun (observerTime w n)

/-- `t(τ(t)) = t`. -/
theorem observerTime_retardedOfObserver {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    observerTime w n (retardedOfObserver w n t) = t :=
  Function.invFun_eq (surjective_observerTime w hn t)

/-- `τ(t(τ)) = τ`. -/
theorem retardedOfObserver_observerTime {n : E3} (hn : ‖n‖ = 1) (τ : ℝ) :
    retardedOfObserver w n (observerTime w n τ) = τ :=
  Function.leftInverse_invFun (strictMono_observerTime w hn).injective τ

/-- The retarded time is a continuous function of the time of the observer. -/
theorem continuous_retardedOfObserver {n : E3} (hn : ‖n‖ = 1) :
    Continuous (retardedOfObserver w n) := by
  refine Monotone.continuous_of_surjective (fun t₁ t₂ h => ?_)
    (fun τ => ⟨_, retardedOfObserver_observerTime w hn τ⟩)
  rw [← (strictMono_observerTime w hn).le_iff_le, observerTime_retardedOfObserver w hn,
    observerTime_retardedOfObserver w hn]
  exact h

/-- `dτ/dt = 1/(1 − n·v)`. -/
theorem hasDerivAt_retardedOfObserver {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    HasDerivAt (retardedOfObserver w n)
      (1 - inner ℝ n (deriv w.r (retardedOfObserver w n t)))⁻¹ t :=
  HasDerivAt.of_local_left_inverse (continuous_retardedOfObserver w hn).continuousAt
    (hasDerivAt_observerTime w n _) (one_sub_inner_pos w _ hn).ne'
    (Eventually.of_forall (observerTime_retardedOfObserver w hn))

/-! ### The radiation amplitude -/

/-- The **radiation amplitude** of the charge `e` on the world line `w` in the direction `n` at
the retarded time `τ`, `A = e n × ((n − v) × v̇)/(4π(1 − n·v)³)` with `v = ṙ(τ)`, `v̇ = r̈(τ)`:
the acceleration field is `A/ρ` on the light cone of `r(τ)` (`smul_accelerationField_lightCone`),
and `|A|²` is the energy per unit solid angle and unit time of the observer
(`tendsto_sq_mul_inner_poyntingVector_lightCone_eq`). -/
def amplitude (e : ℝ) (w : SubluminalWorldline) (n : E3) (τ : ℝ) : E3 :=
  (e / (4 * π * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) •
    cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))

/-- **The amplitude is the far field on the light cone**: at the event `(τ + ρ, r(τ) + ρ n)`
with `ρ > 0`, `ρ E_a = A`, for the acceleration field `E_a` of (63.8). -/
theorem smul_accelerationField_lightCone (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : E3}
    (hn : ‖n‖ = 1) :
    ρ • LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n) = amplitude e w n τ := by
  rw [accelerationField_lightCone_eq_cross w e hρ hn, smul_smul, amplitude]
  congr 1
  have hk := (one_sub_inner_pos w τ hn).ne'
  field_simp

/-- **The flux of energy per unit solid angle** is `|A|²`: as `ρ → ∞` along the light cone,
`ρ² S·n → |A|²`, per unit time of the observer. -/
theorem tendsto_sq_mul_inner_poyntingVector_lightCone_eq (e τ : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    Tendsto (fun ρ => ρ ^ 2 * ∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i) atTop
      (𝓝 (‖amplitude e w n τ‖ ^ 2)) := by
  convert tendsto_sq_mul_inner_poyntingVector_lightCone w e τ hn using 2
  have hk := one_sub_inner_pos w τ hn
  rw [amplitude, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- The amplitude is continuous in the retarded time. -/
theorem continuous_amplitude (e : ℝ) {n : E3} (hn : ‖n‖ = 1) : Continuous (amplitude e w n) := by
  have hv := w.contDiff_deriv.continuous
  have ha := w.contDiff_deriv_deriv.continuous
  have heq : amplitude e w n = fun τ => (e / (4 * π * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) •
      (inner ℝ n (deriv (deriv w.r) τ) • (n - deriv w.r τ) -
        inner ℝ n (n - deriv w.r τ) • deriv (deriv w.r) τ) := by
    funext τ
    rw [amplitude, cross_cross]
  rw [heq]
  have hd : Continuous fun τ => 4 * π * (1 - inner ℝ n (deriv w.r τ)) ^ 3 := by fun_prop
  have hV : Continuous fun τ => inner ℝ n (deriv (deriv w.r) τ) • (n - deriv w.r τ) -
      inner ℝ n (n - deriv w.r τ) • deriv (deriv w.r) τ := by fun_prop
  refine (continuous_const.div hd fun τ => ?_).smul hV
  exact mul_ne_zero (by positivity) (pow_ne_zero 3 (one_sub_inner_pos w τ hn).ne')

/-- `|u × v| ≤ |u||v|`. -/
theorem norm_cross_le (u v : E3) : ‖cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  have h : ‖cross u v‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    rw [norm_cross_sq, mul_pow]
    nlinarith [sq_nonneg (inner ℝ u v)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h

/-- `|(1 − n·v) A| ≤ 2|e| |v̇|/(4π(1 − v₀)²)`. -/
theorem norm_smul_amplitude_le (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (τ : ℝ) :
    ‖(1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ‖ ≤
      2 * |e| / (4 * π * (1 - w.v₀) ^ 2) * ‖deriv (deriv w.r) τ‖ := by
  have hk : 0 < 1 - inner ℝ n (deriv w.r τ) := one_sub_inner_pos w τ hn
  have hk0 := one_sub_v₀_le w τ hn
  have hv0 := one_sub_v₀_pos w
  have hX : ‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ≤
      2 * ‖deriv (deriv w.r) τ‖ := by
    have hnv : ‖n - deriv w.r τ‖ ≤ 2 := by
      have := norm_sub_le n (deriv w.r τ)
      linarith [w.norm_deriv_le τ, w.v₀_lt_one]
    calc _ ≤ ‖n‖ * (‖n - deriv w.r τ‖ * ‖deriv (deriv w.r) τ‖) :=
          (norm_cross_le _ _).trans (mul_le_mul_of_nonneg_left (norm_cross_le _ _) (norm_nonneg _))
      _ ≤ 1 * (2 * ‖deriv (deriv w.r) τ‖) := by
          rw [hn]
          gcongr
      _ = _ := one_mul _
  rw [amplitude, smul_smul, norm_smul, Real.norm_eq_abs]
  have habs : |(1 - inner ℝ n (deriv w.r τ)) * (e / (4 * π * (1 - inner ℝ n (deriv w.r τ)) ^ 3))| =
      |e| / (4 * π * (1 - inner ℝ n (deriv w.r τ)) ^ 2) := by
    rw [abs_mul, abs_div, abs_of_pos hk, abs_of_pos (by positivity : (0 : ℝ) < 4 * π *
      (1 - inner ℝ n (deriv w.r τ)) ^ 3)]
    field_simp
  rw [habs]
  calc |e| / (4 * π * (1 - inner ℝ n (deriv w.r τ)) ^ 2) *
        ‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ≤
      |e| / (4 * π * (1 - w.v₀) ^ 2) * (2 * ‖deriv (deriv w.r) τ‖) := by
        gcongr
    _ = _ := by ring

/-- For an integrable acceleration, `(1 − n·v) A` is integrable in the retarded time. -/
theorem integrable_smul_amplitude (e : ℝ) {n : E3} (hn : ‖n‖ = 1)
    (ha : Integrable (deriv (deriv w.r))) :
    Integrable fun τ => (1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ := by
  refine (ha.norm.const_mul (2 * |e| / (4 * π * (1 - w.v₀) ^ 2))).mono' ?_
    (Eventually.of_forall (norm_smul_amplitude_le w e hn))
  have hv := w.contDiff_deriv.continuous
  have hk : Continuous fun τ => 1 - inner ℝ n (deriv w.r τ) := by fun_prop
  exact (hk.smul (continuous_amplitude w e hn)).aestronglyMeasurable

/-- The vector `e n × (n × v)/(4π(1 − n·v))` of a charge moving with the velocity `v` in the
direction `n`; the low-frequency radiation of a collision is its change (69.2). -/
def velocityAmplitude (e : ℝ) (n v : E3) : E3 :=
  (e / (4 * π * (1 - inner ℝ n v))) • cross n (cross n v)

/-- The velocity amplitude is continuous where `n·v ≠ 1`. -/
theorem continuousAt_velocityAmplitude (e : ℝ) (n : E3) {v : E3} (hv : inner ℝ n v ≠ 1) :
    ContinuousAt (velocityAmplitude e n) v := by
  have heq : velocityAmplitude e n =
      fun x => (e / (4 * π * (1 - inner ℝ n x))) • (inner ℝ n x • n - inner ℝ n n • x) := by
    funext x
    rw [velocityAmplitude, cross_cross]
  rw [heq]
  have hne : 4 * π * (1 - inner ℝ n v) ≠ 0 :=
    mul_ne_zero (by positivity) (sub_ne_zero.mpr (Ne.symm hv))
  have hd : ContinuousAt (fun x : E3 => 4 * π * (1 - inner ℝ n x)) v := by fun_prop
  have hV : ContinuousAt (fun x : E3 => inner ℝ n x • n - inner ℝ n n • x) v := by fun_prop
  exact (continuousAt_const.div hd hne).smul hV

/-- **The amplitude is a total derivative in the retarded time**:
`d/dτ [e n × (n × v)/(4π(1 − n·v))] = (1 − n·v) A`. -/
theorem hasDerivAt_velocityAmplitude (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (τ : ℝ) :
    HasDerivAt (fun s => velocityAmplitude e n (deriv w.r s))
      ((1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ) τ := by
  have hnn : inner ℝ n n = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hv : HasDerivAt (deriv w.r) (deriv (deriv w.r) τ) τ :=
    (w.contDiff_deriv.differentiable (by simp) τ).hasDerivAt
  have hi : HasDerivAt (fun s => inner ℝ n (deriv w.r s)) (inner ℝ n (deriv (deriv w.r) τ)) τ := by
    have h := (hasDerivAt_const τ n).inner ℝ hv
    simpa only [inner_zero_left, add_zero] using h
  have hk := (one_sub_inner_pos w τ hn).ne'
  have hd : HasDerivAt (fun s => 4 * π * (1 - inner ℝ n (deriv w.r s)))
      (4 * π * -inner ℝ n (deriv (deriv w.r) τ)) τ := by
    simpa using (hi.const_sub 1).const_mul (4 * π)
  have hc := (hasDerivAt_const τ e).fun_div hd (mul_ne_zero (by positivity) hk)
  have hV : HasDerivAt (fun s => inner ℝ n (deriv w.r s) • n - inner ℝ n n • deriv w.r s)
      (inner ℝ n (deriv (deriv w.r) τ) • n - inner ℝ n n • deriv (deriv w.r) τ) τ :=
    (hi.smul_const n).sub (hv.const_smul (inner ℝ n n))
  have h := hc.smul hV
  have heq : (fun s => velocityAmplitude e n (deriv w.r s)) = fun s =>
      (e / (4 * π * (1 - inner ℝ n (deriv w.r s)))) •
        (inner ℝ n (deriv w.r s) • n - inner ℝ n n • deriv w.r s) := by
    funext s
    rw [velocityAmplitude, cross_cross]
  rw [heq]
  convert h using 1
  rw [amplitude, cross_cross, inner_sub_right, hnn]
  match_scalars <;> field_simp <;> ring

/-! ### The amplitude in the time of the observer and its spectrum -/

/-- The **radiation amplitude as a function of the time of the observer** `t = τ − n·r(τ)`,
`A(τ(t), n)`. -/
def observedAmplitude (e : ℝ) (w : SubluminalWorldline) (n : E3) (t : ℝ) : E3 :=
  amplitude e w n (retardedOfObserver w n t)

/-- **The amplitude is a total derivative in the time of the observer**:
`A = d/dt [e n × (n × v)/(4π(1 − n·v))]`, the identity behind (69.1). -/
theorem hasDerivAt_velocityAmplitude_retardedOfObserver (e : ℝ) {n : E3} (hn : ‖n‖ = 1)
    (t : ℝ) :
    HasDerivAt (fun t => velocityAmplitude e n (deriv w.r (retardedOfObserver w n t)))
      (observedAmplitude e w n t) t := by
  have h : HasDerivAt (fun t => velocityAmplitude e n (deriv w.r (retardedOfObserver w n t))) _ t :=
    (hasDerivAt_velocityAmplitude w e hn (retardedOfObserver w n t)).scomp t
      (hasDerivAt_retardedOfObserver w hn t)
  convert h using 1
  rw [smul_smul, inv_mul_cancel₀ (one_sub_inner_pos w _ hn).ne', one_smul, observedAmplitude]

/-- **The amplitude is the derivative of the velocity amplitude in the time of the observer**,
`A(τ(t), n) = d/dt [e n × (n × v)/(4π(1 − n·v))]`. -/
theorem radiationAmplitude_eq_deriv (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    observedAmplitude e w n t =
      deriv (fun t => velocityAmplitude e n (deriv w.r (retardedOfObserver w n t))) t :=
  (hasDerivAt_velocityAmplitude_retardedOfObserver w e hn t).deriv.symm

/-- **The spectral resolution of the radiation amplitude** (the transform of §64 for a point
charge): the Fourier transform in the time of the observer is an integral over the retarded
time, `∫ e^{−2πiνt} A dt = ∫ e^{−2πiν(τ − n·r(τ))} (1 − n·v) A dτ`, by the change of variables
`t = τ − n·r(τ)`, strictly increasing with `dt/dτ = 1 − n·v ≥ 1 − v₀ > 0`. -/
theorem fourier_radiationAmplitude (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (ν : ℝ) :
    𝓕 (fun t => complexify (observedAmplitude e w n t)) ν =
      ∫ τ, 𝐞 (-(observerTime w n τ * ν)) •
        complexify ((1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ) := by
  rw [Real.fourier_real_eq]
  have hcv := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun τ _ => (hasDerivAt_observerTime w n τ).hasDerivWithinAt)
    (strictMono_observerTime w hn).injective.injOn
    (fun t => 𝐞 (-(t * ν)) • complexify (observedAmplitude e w n t))
  rw [image_univ, (surjective_observerTime w hn).range_eq] at hcv
  simp only [Measure.restrict_univ] at hcv
  rw [hcv]
  congr 1
  ext1 τ
  rw [abs_of_pos (one_sub_inner_pos w τ hn), observedAmplitude,
    retardedOfObserver_observerTime w hn, map_smul, smul_comm]

/-- **The spectral resolution as the transform of a total derivative**:
`∫ e^{−2πiνt} A dt = ∫ e^{−2πiν(τ − n·r(τ))} d[e n × (n × v)/(4π(1 − n·v))]`. -/
theorem fourier_radiationAmplitude_eq_deriv (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (ν : ℝ) :
    𝓕 (fun t => complexify (observedAmplitude e w n t)) ν =
      ∫ τ, 𝐞 (-(observerTime w n τ * ν)) •
        complexify (deriv (fun s => velocityAmplitude e n (deriv w.r s)) τ) := by
  rw [fourier_radiationAmplitude w e hn]
  congr 1
  ext1 τ
  rw [(hasDerivAt_velocityAmplitude w e hn τ).deriv]

/-- For an integrable acceleration the amplitude is integrable in the time of the observer. -/
theorem integrable_observedAmplitude (e : ℝ) {n : E3} (hn : ‖n‖ = 1)
    (ha : Integrable (deriv (deriv w.r))) : Integrable (observedAmplitude e w n) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun τ _ => (hasDerivAt_observerTime w n τ).hasDerivWithinAt)
    (strictMono_observerTime w hn).injective.injOn (observedAmplitude e w n)
  rw [image_univ, (surjective_observerTime w hn).range_eq, integrableOn_univ,
    integrableOn_univ] at h
  refine h.mpr ((integrable_smul_amplitude w e hn ha).congr (Eventually.of_forall fun τ => ?_))
  simp only [observedAmplitude, retardedOfObserver_observerTime w hn,
    abs_of_pos (one_sub_inner_pos w τ hn)]

/-- A limit of the velocity has the norm at most `v₀`. -/
theorem norm_le_of_tendsto {l : Filter ℝ} [l.NeBot] {v : E3} (h : Tendsto (deriv w.r) l (𝓝 v)) :
    ‖v‖ ≤ w.v₀ :=
  le_of_tendsto' h.norm w.norm_deriv_le

/-- `n·v ≠ 1` for a unit vector `n` and `|v| ≤ v₀`. -/
theorem inner_ne_one {n v : E3} (hn : ‖n‖ = 1) (hv : ‖v‖ ≤ w.v₀) : inner ℝ n v ≠ 1 := by
  have h1 := real_inner_le_norm n v
  rw [hn, one_mul] at h1
  intro h
  linarith [w.v₀_lt_one]

/-- **The integral of the amplitude over the time of the observer** is the change of the
velocity amplitude, `∫ A dt = e/(4π) [n × (n × v₂)/(1 − n·v₂) − n × (n × v₁)/(1 − n·v₁)]`, for
an integrable acceleration with the asymptotic velocities `v₁`, `v₂`. -/
theorem integral_observedAmplitude (e : ℝ) {n : E3} (hn : ‖n‖ = 1) {v₁ v₂ : E3}
    (ha : Integrable (deriv (deriv w.r))) (hbot : Tendsto (deriv w.r) atBot (𝓝 v₁))
    (htop : Tendsto (deriv w.r) atTop (𝓝 v₂)) :
    ∫ t, observedAmplitude e w n t = velocityAmplitude e n v₂ - velocityAmplitude e n v₁ := by
  have hcv := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun τ _ => (hasDerivAt_observerTime w n τ).hasDerivWithinAt)
    (strictMono_observerTime w hn).injective.injOn (observedAmplitude e w n)
  rw [image_univ, (surjective_observerTime w hn).range_eq] at hcv
  simp only [Measure.restrict_univ] at hcv
  rw [hcv]
  have heq : (fun τ => |1 - inner ℝ n (deriv w.r τ)| •
      observedAmplitude e w n (observerTime w n τ)) =
      fun τ => (1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ := by
    funext τ
    rw [abs_of_pos (one_sub_inner_pos w τ hn), observedAmplitude,
      retardedOfObserver_observerTime w hn]
  rw [heq]
  have h₁ := continuousAt_velocityAmplitude e n (inner_ne_one w hn (norm_le_of_tendsto w hbot))
  have h₂ := continuousAt_velocityAmplitude e n (inner_ne_one w hn (norm_le_of_tendsto w htop))
  exact integral_of_hasDerivAt_of_tendsto (hasDerivAt_velocityAmplitude w e hn)
    (integrable_smul_amplitude w e hn ha) (h₁.tendsto.comp hbot) (h₂.tendsto.comp htop)

/-- **The low-frequency limit of the transform of the amplitude**: for an integrable
acceleration with the asymptotic velocities `v₁`, `v₂`, the Fourier transform of the amplitude
in the time of the observer tends, as `ν → 0`, to the change
`e/(4π) [n × (n × v₂)/(1 − n·v₂) − n × (n × v₁)/(1 − n·v₁)]` of the velocity amplitude. -/
theorem tendsto_fourier_observedAmplitude (e : ℝ) {n : E3} (hn : ‖n‖ = 1) {v₁ v₂ : E3}
    (ha : Integrable (deriv (deriv w.r))) (hbot : Tendsto (deriv w.r) atBot (𝓝 v₁))
    (htop : Tendsto (deriv w.r) atTop (𝓝 v₂)) :
    Tendsto (𝓕 (fun t => complexify (observedAmplitude e w n t))) (𝓝 0)
      (𝓝 (complexify (velocityAmplitude e n v₂ - velocityAmplitude e n v₁))) := by
  rw [← integral_observedAmplitude w e hn ha hbot htop]
  exact tendsto_fourier_complexify (integrable_observedAmplitude w e hn ha)

/-- **The angular spectral density** of the radiation of the charge `e` on `w` in the direction
`n`, `|𝓕A(ν)|²` with `𝓕A(ν) = ∫ e^{−2πiνt} A dt` in the time of the observer: the energy per
unit solid angle is `∫ |A|² dt`, and by Plancherel's theorem `∫ |𝓕A|² dν` over all `ν ∈ ℝ`. It is
even in `ν` (`angularSpectrum_neg`), so the density over `ν > 0` is twice it and that over
`ω = 2πν > 0` is `|𝓕A|²/π`. -/
def angularSpectrum (e : ℝ) (w : SubluminalWorldline) (n : E3) (ν : ℝ) : ℝ :=
  ‖𝓕 (fun t => complexify (observedAmplitude e w n t)) ν‖ ^ 2

/-- The angular spectral density is even in the frequency. -/
theorem angularSpectrum_neg (e : ℝ) {n : E3} (hn : ‖n‖ = 1)
    (ha : Integrable (deriv (deriv w.r))) (ν : ℝ) :
    angularSpectrum e w n (-ν) = angularSpectrum e w n ν := by
  rw [angularSpectrum, angularSpectrum,
    norm_fourier_complexify_neg (integrable_observedAmplitude w e hn ha)]

/-- **The low-frequency limit of the angular spectrum** (Landau–Lifshitz (69.2)): the angular
spectral density tends, as `ν → 0`, to the square of the change of the velocity amplitude,
`(e/4π)² |n × (n × v₂)/(1 − n·v₂) − n × (n × v₁)/(1 − n·v₁)|²`; it depends only on the
asymptotic velocities. -/
theorem tendsto_relativisticSpectrum (e : ℝ) {n : E3} (hn : ‖n‖ = 1) {v₁ v₂ : E3}
    (ha : Integrable (deriv (deriv w.r))) (hbot : Tendsto (deriv w.r) atBot (𝓝 v₁))
    (htop : Tendsto (deriv w.r) atTop (𝓝 v₂)) :
    Tendsto (angularSpectrum e w n) (𝓝 0)
      (𝓝 (‖velocityAmplitude e n v₂ - velocityAmplitude e n v₁‖ ^ 2)) := by
  have h := (tendsto_fourier_observedAmplitude w e hn ha hbot htop).norm.pow 2
  rwa [norm_complexify] at h

/-- **The one-sided low-frequency limit of the angular spectrum**: the density over `ν > 0`,
twice `angularSpectrum`, tends to `2 |Δ(e n × (n × v)/(4π(1 − n·v)))|²` as `ν → 0⁺`, that is
`|Δ(…)|²/π` per unit angular frequency, Landau–Lifshitz's (69.2) in Heaviside–Lorentz units. -/
theorem tendsto_two_mul_relativisticSpectrum (e : ℝ) {n : E3} (hn : ‖n‖ = 1) {v₁ v₂ : E3}
    (ha : Integrable (deriv (deriv w.r))) (hbot : Tendsto (deriv w.r) atBot (𝓝 v₁))
    (htop : Tendsto (deriv w.r) atTop (𝓝 v₂)) :
    Tendsto (fun ν => 2 * angularSpectrum e w n ν) (𝓝[>] 0)
      (𝓝 (2 * ‖velocityAmplitude e n v₂ - velocityAmplitude e n v₁‖ ^ 2)) :=
  ((tendsto_relativisticSpectrum w e hn ha hbot htop).const_mul 2).mono_left nhdsWithin_le_nhds

/-! ### The slow limit -/

/-- **The total low-frequency spectrum in the slow limit**: for `|v| ≪ 1` the change of the
velocity amplitude is `(e/4π) n × (n × Δv)`, and the integral over the directions of twice its
square (the one-sided density) is `(4/3)(e²/4π)|Δv|²`, the one-sided dipole limit of
`tendsto_two_mul_dipoleSpectrum`. -/
theorem integral_two_mul_norm_sq_smul_cross_cross (e : ℝ) (X : E3) :
    ∫ n : sphere (0 : E3) 1, 2 * ‖(e / (4 * π)) • cross n (cross n X)‖ ^ 2 ∂sphereMeasure =
      4 / 3 * (e ^ 2 / (4 * π)) * ‖X‖ ^ 2 := by
  have h (n : sphere (0 : E3) 1) : 2 * ‖(e / (4 * π)) • cross n (cross n X)‖ ^ 2 =
      2 * (e / (4 * π)) ^ 2 * ‖X‖ ^ 2 - 2 * (e / (4 * π)) ^ 2 * inner ℝ (n : E3) X ^ 2 := by
    have hn : ‖(n : E3)‖ = 1 := by simp
    have hnn : inner ℝ (n : E3) n = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, cross_cross, hnn, one_smul,
      norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hn, real_inner_smul_left,
      real_inner_comm]
    ring
  have hc : Continuous fun n : sphere (0 : E3) 1 => inner ℝ (n : E3) X ^ 2 := by fun_prop
  rw [integral_congr_ae (Eventually.of_forall h), integral_sub (integrable_const _)
    ((integrable_of_continuous hc).const_mul _), integral_const, integral_const_mul,
    integral_inner_sq, smul_eq_mul, sphereMeasure_real_univ]
  field_simp
  ring

/-! ### A charge that starts suddenly -/

/-- `∫_{−1}^{1} (1 − s²)/(1 − βs)² ds = 2(log((1 + β)/(1 − β)) − 2β)/β³` for `0 < |β| < 1`,
with the antiderivative `((1 − βs) − 2 log(1 − βs) − (1 − β²)/(1 − βs))/β³`. -/
theorem integral_one_sub_sq_div_one_sub_mul_sq {β : ℝ} (hβ : |β| < 1) (hβ0 : β ≠ 0) :
    ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) / (1 - β * s) ^ 2 =
      2 * (log ((1 + β) / (1 - β)) - 2 * β) / β ^ 3 := by
  have hIcc : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hF : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt
      (fun s => ((1 - β * s) - 2 * log (1 - β * s) - (1 - β ^ 2) / (1 - β * s)) / β ^ 3)
      ((1 - s ^ 2) / (1 - β * s) ^ 2) s := by
    intro s hs
    rw [hIcc] at hs
    have hk := one_sub_mul_pos hβ hs
    have hk' := hk.ne'
    have hu : HasDerivAt (fun s => 1 - β * s) (-β) s := by
      simpa using (hasDerivAt_const s (1 : ℝ)).fun_sub ((hasDerivAt_id' s).const_mul β)
    have hq := (hasDerivAt_const s (1 - β ^ 2)).fun_div hu hk.ne'
    have hl := (hu.log hk.ne').const_mul 2
    have h := ((hu.fun_sub hl).fun_sub hq).div_const (β ^ 3)
    convert h using 1
    obtain ⟨u, hu_def⟩ : ∃ u, u = 1 - β * s := ⟨_, rfl⟩
    rw [← hu_def] at hk' ⊢
    field_simp
    rw [hu_def]
    ring
  have hβ1 : 0 < 1 - β := by linarith [(abs_lt.mp hβ).2]
  have hβ2 : 0 < 1 + β := by linarith [(abs_lt.mp hβ).1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (ContinuousOn.intervalIntegrable (by
      rw [hIcc]
      exact continuousOn_div_one_sub_mul_pow hβ (by fun_prop) 2)),
    Real.log_div hβ2.ne' hβ1.ne']
  norm_num
  field_simp
  ring

/-- The pointwise form of the sudden start: for `v = β ê` with a unit vector `ê`, `|β| < 1`, and
`n` on the unit sphere, `2|Δ(velocity amplitude)|² = (e²β²/8π²)(1 − s²)/(1 − βs)²` with
`s = n·ê`. -/
theorem two_mul_norm_sq_velocityAmplitude_smul (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ}
    (hβ : |β| < 1) (n : sphere (0 : E3) 1) :
    2 * ‖velocityAmplitude e n (β • ê) - velocityAmplitude e n 0‖ ^ 2 =
      e ^ 2 * β ^ 2 / (8 * π ^ 2) *
        ((1 - inner ℝ (n : E3) ê ^ 2) / (1 - β * inner ℝ (n : E3) ê) ^ 2) := by
  have hn : ‖(n : E3)‖ = 1 := by simp
  have hnn : inner ℝ (n : E3) n = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  have hk := (one_sub_mul_pos hβ (inner_mem_Icc he n)).ne'
  have h0 : velocityAmplitude e n 0 = 0 := by
    rw [velocityAmplitude, cross_cross]
    simp
  rw [h0, sub_zero, velocityAmplitude, cross_cross, hnn, one_smul, real_inner_smul_right,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sub_sq_real, norm_smul, norm_smul,
    mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hn, he,
    real_inner_smul_left, real_inner_smul_right, real_inner_comm ê]
  field_simp
  ring

/-- **The total low-frequency spectrum of a charge that starts suddenly** (Landau–Lifshitz §69,
problem): for the asymptotic velocities `v₁ = 0` and `v₂ = v` with `0 < |v| < 1`, the integral
over the directions of twice the square of the change of the velocity amplitude (the one-sided
limit of `tendsto_two_mul_relativisticSpectrum`) is `(e²/2π)((1/β) log((1 + β)/(1 − β)) − 2)`
with `β = |v|`; for `β → 0` it is `(e²/2π)(2β²/3 + O(β⁴)) ≈ (4/3)(e²/4π)β²`, the dipole limit. -/
theorem integral_two_mul_norm_sq_velocityAmplitude (e : ℝ) {v : E3} (hv : ‖v‖ < 1)
    (hv0 : v ≠ 0) :
    ∫ n : sphere (0 : E3) 1,
        2 * ‖velocityAmplitude e n v - velocityAmplitude e n 0‖ ^ 2 ∂sphereMeasure =
      e ^ 2 / (2 * π) * (log ((1 + ‖v‖) / (1 - ‖v‖)) / ‖v‖ - 2) := by
  have hβpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hβ : |‖v‖| < 1 := by rwa [abs_of_pos hβpos]
  have he : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hβpos.ne']
  have hvê : v = ‖v‖ • ‖v‖⁻¹ • v := by
    rw [smul_smul, mul_inv_cancel₀ hβpos.ne', one_smul]
  have hg : ContinuousOn (fun s : ℝ => e ^ 2 * ‖v‖ ^ 2 / (8 * π ^ 2) *
      ((1 - s ^ 2) / (1 - ‖v‖ * s) ^ 2)) (Icc (-1) 1) :=
    continuousOn_const.mul (continuousOn_div_one_sub_mul_pow hβ (by fun_prop) 2)
  have hpt (n : sphere (0 : E3) 1) :
      2 * ‖velocityAmplitude e n v - velocityAmplitude e n 0‖ ^ 2 =
        e ^ 2 * ‖v‖ ^ 2 / (8 * π ^ 2) * ((1 - inner ℝ (n : E3) (‖v‖⁻¹ • v) ^ 2) /
          (1 - ‖v‖ * inner ℝ (n : E3) (‖v‖⁻¹ • v)) ^ 2) := by
    conv_lhs => rw [hvê]
    exact two_mul_norm_sq_velocityAmplitude_smul e he hβ n
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_comp_inner he hg,
    intervalIntegral.integral_const_mul, integral_one_sub_sq_div_one_sub_mul_sq hβ hβpos.ne']
  field_simp
  ring

/-! ### An instance -/

/-- The unit vector `e₁` has the norm one. -/
theorem norm_single_zero : ‖(EuclideanSpace.single 0 1 : E3)‖ = 1 := by simp

/-- The path `r(t) = (2β/π)(t arctan t − log(1 + t²)/2) e₁` along the first axis, with the
velocity `(2β/π) arctan t e₁` and the acceleration `(2β/π) e₁/(1 + t²)`: a charge that comes
from `−∞` with the velocity `−β e₁` and goes to `+∞` with the velocity `β e₁`. -/
def arctanPath (β t : ℝ) : E3 :=
  (2 * β / π * (t * arctan t - log (1 + t ^ 2) / 2)) • EuclideanSpace.single 0 1

/-- The velocity of `arctanPath` is `(2β/π) arctan t e₁`. -/
theorem hasDerivAt_arctanPath (β t : ℝ) :
    HasDerivAt (arctanPath β) ((2 * β / π * arctan t) • EuclideanSpace.single 0 1) t := by
  have h1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hlog : HasDerivAt (fun s : ℝ => log (1 + s ^ 2)) (2 * t / (1 + t ^ 2)) t := by
    have h := ((hasDerivAt_pow 2 t).const_add 1).log h1.ne'
    convert h using 1
    push_cast
    ring
  have hs : HasDerivAt (fun s => s * arctan s - log (1 + s ^ 2) / 2) (arctan t) t := by
    have h := ((hasDerivAt_id' t).fun_mul (hasDerivAt_arctan t)).fun_sub (hlog.div_const 2)
    convert h using 1
    field_simp
    ring
  exact (hs.const_mul (2 * β / π)).smul_const _

/-- The velocity of `arctanPath`. -/
theorem deriv_arctanPath (β : ℝ) :
    deriv (arctanPath β) = fun t => (2 * β / π * arctan t) • EuclideanSpace.single 0 1 :=
  funext fun t => (hasDerivAt_arctanPath β t).deriv

/-- The acceleration of `arctanPath` is `(2β/π) e₁/(1 + t²)`. -/
theorem hasDerivAt_deriv_arctanPath (β t : ℝ) :
    HasDerivAt (deriv (arctanPath β))
      ((2 * β / π * (1 + t ^ 2)⁻¹) • EuclideanSpace.single 0 1) t := by
  rw [deriv_arctanPath]
  have h := ((hasDerivAt_arctan t).const_mul (2 * β / π)).smul_const
    (EuclideanSpace.single 0 1 : E3)
  convert h using 2
  rw [one_div]

/-- The acceleration of `arctanPath`. -/
theorem deriv_deriv_arctanPath (β : ℝ) :
    deriv (deriv (arctanPath β)) =
      fun t => (2 * β / π * (1 + t ^ 2)⁻¹) • EuclideanSpace.single 0 1 :=
  funext fun t => (hasDerivAt_deriv_arctanPath β t).deriv

/-- The acceleration of `arctanPath` is integrable. -/
theorem integrable_deriv_deriv_arctanPath (β : ℝ) :
    Integrable (deriv (deriv (arctanPath β))) := by
  rw [deriv_deriv_arctanPath]
  exact (integrable_inv_one_add_sq.const_mul _).smul_const _

/-- The velocity of `arctanPath` tends to `β e₁` as `t → +∞`. -/
theorem tendsto_deriv_arctanPath_atTop (β : ℝ) :
    Tendsto (deriv (arctanPath β)) atTop (𝓝 (β • EuclideanSpace.single 0 1)) := by
  rw [deriv_arctanPath]
  have h := ((tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul
    (2 * β / π)).smul_const (EuclideanSpace.single 0 1 : E3)
  convert h using 2
  field_simp

/-- The velocity of `arctanPath` tends to `−β e₁` as `t → −∞`. -/
theorem tendsto_deriv_arctanPath_atBot (β : ℝ) :
    Tendsto (deriv (arctanPath β)) atBot (𝓝 ((-β) • EuclideanSpace.single 0 1)) := by
  rw [deriv_arctanPath]
  have h := ((tendsto_arctan_atBot.mono_right nhdsWithin_le_nhds).const_mul
    (2 * β / π)).smul_const (EuclideanSpace.single 0 1 : E3)
  convert h using 2
  field_simp

/-- **A subluminal world line with distinct asymptotic velocities** `∓β e₁`, `|β| < 1`: the path
`arctanPath β`, of the speed `(2|β|/π)|arctan t| < |β|`. -/
def arctanWorldline (β : ℝ) (hβ : |β| < 1) : SubluminalWorldline where
  r := arctanPath β
  contDiff_r := by
    unfold arctanPath
    have hl : ContDiff ℝ ∞ fun t : ℝ => log (1 + t ^ 2) :=
      (contDiff_const.add (contDiff_id.pow 2)).log fun t => by positivity
    exact (contDiff_const.mul ((contDiff_id.mul contDiff_arctan).sub
      (hl.div_const 2))).smul contDiff_const
  v₀ := |β|
  v₀_nonneg := abs_nonneg β
  v₀_lt_one := hβ
  norm_deriv_le t := by
    rw [deriv_arctanPath, norm_smul, norm_single_zero, mul_one,
      Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_two, abs_of_pos pi_pos]
    have h := abs_lt.mpr ⟨neg_pi_div_two_lt_arctan t, arctan_lt_pi_div_two t⟩
    calc 2 * |β| / π * |arctan t| ≤ 2 * |β| / π * (π / 2) := by gcongr
      _ = |β| := by field_simp

/-- The velocity amplitude in the direction `e₂` of a velocity `c e₁` along the first axis is
`−(ec/4π) e₁`. -/
theorem velocityAmplitude_single (e c : ℝ) :
    velocityAmplitude e (EuclideanSpace.single 1 1) (c • EuclideanSpace.single 0 1) =
      (-(e * c) / (4 * π)) • EuclideanSpace.single 0 1 := by
  have h0 : inner ℝ (EuclideanSpace.single 1 1 : E3) (c • EuclideanSpace.single 0 1) = 0 := by
    simp [EuclideanSpace.inner_single_left]
  have h1 : inner ℝ (EuclideanSpace.single 1 1 : E3) (EuclideanSpace.single 1 1) = 1 := by
    simp
  rw [velocityAmplitude, cross_cross, h0, h1, sub_zero, zero_smul, zero_sub, one_smul,
    smul_neg, smul_smul, ← neg_smul]
  congr 1
  field_simp

/-- **The instance of the relativistic limit**: for the charge on `arctanWorldline β`, the
angular spectral density in the direction `e₂` orthogonal to the motion tends to
`(eβ/2π)² ≠ 0` (for `e, β ≠ 0`) as `ν → 0`: the jump of the velocity amplitude is `−(eβ/2π) e₁`.
-/
theorem tendsto_angularSpectrum_arctanWorldline (e β : ℝ) (hβ : |β| < 1) :
    Tendsto (angularSpectrum e (arctanWorldline β hβ) (EuclideanSpace.single 1 1)) (𝓝 0)
      (𝓝 ((e * β / (2 * π)) ^ 2)) := by
  have h := tendsto_relativisticSpectrum (arctanWorldline β hβ) e
    (n := EuclideanSpace.single 1 1) (by simp) (integrable_deriv_deriv_arctanPath β)
    (tendsto_deriv_arctanPath_atBot β) (tendsto_deriv_arctanPath_atTop β)
  convert h using 2
  rw [velocityAmplitude_single, velocityAmplitude_single, ← sub_smul, norm_smul,
    norm_single_zero, mul_one, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- **The instance of the dipole limit**: for the acceleration of `arctanPath β` the dipole
spectral density tends to `(2/3)(e²/4π)(2β)²` as `ν → 0`. -/
theorem tendsto_dipoleSpectrum_arctanPath (e β : ℝ) :
    Tendsto (dipoleSpectrum e (deriv (deriv (arctanPath β)))) (𝓝 0)
      (𝓝 (2 / 3 * (e ^ 2 / (4 * π)) * (2 * β) ^ 2)) := by
  have h := tendsto_dipoleSpectrum e
    (fun t => (hasDerivAt_deriv_arctanPath β t).differentiableAt.hasDerivAt)
    (integrable_deriv_deriv_arctanPath β) (tendsto_deriv_arctanPath_atBot β)
    (tendsto_deriv_arctanPath_atTop β)
  convert h using 3
  rw [← sub_smul, norm_smul, norm_single_zero, mul_one, Real.norm_eq_abs,
    sq_abs]
  ring

end ProjectAinos.Electrodynamics.Radiation.CollisionSpectrum
