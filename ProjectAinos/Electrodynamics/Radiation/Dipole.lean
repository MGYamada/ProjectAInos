/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Tactic

/-!
# Dipole radiation

Landau–Lifshitz, *The Classical Theory of Fields*, §67. The units have `c = 1` and `div E = k⁰`.
A current `k = (ρ, 𝐣)` is a `LocalizedSource k a M N` if it is smooth and conserved, vanishes for
`‖𝐱‖ > a` at all times, and its time derivatives `∂₀ᵐ𝐣` of the orders `m ≤ N` have Euclidean norm
at most `M`. Its **slow family** `slowCurrent κ k` is `k_κ(t, 𝐱) = (ρ(κt, 𝐱), κ𝐣(κt, 𝐱))` for
`0 < κ ≤ 1`, the same motion `κ` times more slowly, so that the size `a` of the system is small
compared with the wavelengths `~ 1/κ`. It is again conserved (`divergence4_slowCurrent`), and
`∂₀k_κ = κ (∂₀k)_κ` (`currentRate_slowCurrent`).

* The conservation of charge on a slice of time, `integral_mul_currentRate_zero`:
  `∫ W ∂₀ρ d𝐲 = ∫ ∇W · 𝐣 d𝐲` for a `C¹` weight `W` (integration by parts against
  `∂₀ρ = −div 𝐣`). With the dipole moment `𝐝(s) = ∫ ρ(s, 𝐲) 𝐲 d𝐲` (`dipoleMoment`):
  `hasDerivAt_dipoleMoment`, `𝐝̇ = ∫ 𝐣 d𝐲`; `deriv_deriv_dipoleMoment`, `𝐝̈ = ∫ ∂ₛ𝐣 d𝐲`; and
  `hasDerivAt_secondMoment`, `∫ (yᵢjₗ + yₗjᵢ) d𝐲 = d/ds ∫ ρ yᵢyₗ d𝐲`. The derivatives pass under
  the integral because the support is bounded (`hasDerivAt_integral_of_ballSupport`).
* The amplitude of the slow family (`amplitudeVector_slowCurrent`) is `(κ²/4π) Φ(n)` with
  `Φ(n) = ∫ ∂ₛ𝐣(κu + κ⟨n, 𝐲⟩, 𝐲) d𝐲` (`slowAmplitude`). Taylor's formula in the delay
  `κ⟨n, 𝐲⟩` (`norm_slowAmplitude_sub_le`) gives `Φ(n) = 𝐝̈(κu) + κ𝐜(n) + O(κ²)` with the first
  correction `𝐜(n) = ∫ ⟨n, 𝐲⟩ ∂ₛ²𝐣 d𝐲` (`firstCorrection`).
* The angular density `|∂ᵤÃ|² − ⟨n, ∂ᵤÃ⟩²` (`angularIntensity`, the integrand of `radiatedPower`) is
  `(κ²/4π)² (|Φ|² − ⟨n, Φ⟩²)` (`angularIntensity_slowCurrent`). `dipoleAngular` (67.7): it is
  `κ⁴(|𝐝̈|² − ⟨n, 𝐝̈⟩²)/(16π²)` up to `O(κ⁵)`. `dipolePower_sub_le` (67.8): **the radiated power
  is `κ⁴|𝐝̈(κu)|²/(6π)` up to `(4π/9) M² a⁸ (5 + 4a + a²) κ⁶`**, because the term of the order
  `κ⁵` is odd in `n` (`integral_inner_firstCorrection`) and
  `∫ (|𝐛|² − ⟨n, 𝐛⟩²) dσ = (8π/3)|𝐛|²` (`integral_norm_sq_sub_inner_sq`). The coefficient
  `2/(3c³)` of (67.8) becomes `(2/3)(1/4π) = 1/(6π)` in these units.
* An instance: `oscillatingCurrent f φ`, with `ρ = cos(s + φ) ∂₁f` and `𝐣 = sin(s + φ) f e₁`, is a
  localized source for a smooth profile `f` of bounded support
  (`localizedSource_oscillatingCurrent`), with `𝐝(s) = −cos(s + φ) (∫ f) e₁`
  (`dipoleMoment_oscillatingCurrent`). For the bump `χ = dipoleBump` (`oscillatingDipole`),
  `𝐝̈(s) = cos s (∫ χ) e₁` with `∫ χ > 0`, and `dipolePower_oscillatingDipole` applies the theorem
  with a positive leading term.

The relation of `radiatedPower` to the flux of the Poynting vector through large spheres is not
used here. The axis `1` of the text is the index `0` of `Fin 3`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.Radiation

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The slow family of a current -/

/-- The dilation `(t, 𝐱) ↦ (κt, 𝐱)` of the time. -/
def timeDilation (κ : ℝ) : Spacetime →L[ℝ] Spacetime :=
  (Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] Spacetime).comp
    (((κ • ContinuousLinearMap.fst ℝ ℝ E3).prod (ContinuousLinearMap.snd ℝ ℝ E3)).comp
      (Wave.timeSpaceEquiv : Spacetime →L[ℝ] ℝ × E3))

/-- The dilation in components: `(v⁰, 𝐯) ↦ (κv⁰, 𝐯)`. -/
theorem timeDilation_apply (κ : ℝ) (v : Spacetime) :
    timeDilation κ v = vector (κ * v 0) (space v) := rfl

/-- The dilation of `(t, 𝐱)` is `(κt, 𝐱)`. -/
theorem timeDilation_vector (κ t : ℝ) (x : E3) :
    timeDilation κ (vector t x) = vector (κ * t) x := by
  rw [timeDilation_apply, vector_zero, space_vector]

/-- The rescaling `(w⁰, 𝐰) ↦ (w⁰, κ𝐰)` of the spatial components of a vector. -/
def spaceScaling (κ : ℝ) : Spacetime →L[ℝ] Spacetime :=
  (Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] Spacetime).comp
    (((ContinuousLinearMap.fst ℝ ℝ E3).prod (κ • ContinuousLinearMap.snd ℝ ℝ E3)).comp
      (Wave.timeSpaceEquiv : Spacetime →L[ℝ] ℝ × E3))

/-- The rescaling in components: `(w⁰, 𝐰) ↦ (w⁰, κ𝐰)`. -/
theorem spaceScaling_apply (κ : ℝ) (w : Spacetime) :
    spaceScaling κ w = vector (w 0) (κ • space w) := rfl

/-- The rescaling keeps the time component. -/
theorem spaceScaling_apply_zero (κ : ℝ) (w : Spacetime) : spaceScaling κ w 0 = w 0 := rfl

/-- The rescaling multiplies the spatial components by `κ`. -/
theorem spaceScaling_apply_succ (κ : ℝ) (w : Spacetime) (i : Fin 3) :
    spaceScaling κ w i.succ = κ * w i.succ := rfl

/-- **The slow family** of a current `k = (ρ, 𝐣)`: `k_κ(t, 𝐱) = (ρ(κt, 𝐱), κ𝐣(κt, 𝐱))`. For
`0 < κ ≤ 1` the charges move `κ` times more slowly, and their velocities are `κ` times smaller. -/
def slowCurrent (κ : ℝ) (k : Spacetime → Spacetime) : Spacetime → Spacetime :=
  fun v => spaceScaling κ (k (timeDilation κ v))

/-- The charge density of the slow family: `ρ_κ(t, 𝐱) = ρ(κt, 𝐱)`. -/
theorem slowCurrent_vector_zero (κ : ℝ) (k : Spacetime → Spacetime) (t : ℝ) (x : E3) :
    slowCurrent κ k (vector t x) 0 = k (vector (κ * t) x) 0 := by
  rw [slowCurrent, spaceScaling_apply_zero, timeDilation_vector]

/-- The current of the slow family: `j_κ(t, 𝐱) = κ j(κt, 𝐱)`. -/
theorem slowCurrent_vector_succ (κ : ℝ) (k : Spacetime → Spacetime) (t : ℝ) (x : E3)
    (i : Fin 3) : slowCurrent κ k (vector t x) i.succ = κ * k (vector (κ * t) x) i.succ := by
  rw [slowCurrent, spaceScaling_apply_succ, timeDilation_vector]

/-- The spatial current of the slow family: `𝐣_κ(t, 𝐱) = κ 𝐣(κt, 𝐱)`. -/
theorem space_slowCurrent_vector (κ : ℝ) (k : Spacetime → Spacetime) (t : ℝ) (x : E3) :
    space (slowCurrent κ k (vector t x)) = κ • space (k (vector (κ * t) x)) := by
  rw [slowCurrent, spaceScaling_apply, space_vector, timeDilation_vector]

/-- The derivative of the slow family, by the chain rule through the two linear maps. -/
theorem hasFDerivAt_slowCurrent {κ : ℝ} {k : Spacetime → Spacetime} {v : Spacetime}
    (hk : DifferentiableAt ℝ k (timeDilation κ v)) :
    HasFDerivAt (slowCurrent κ k)
      ((spaceScaling κ).comp ((fderiv ℝ k (timeDilation κ v)).comp (timeDilation κ))) v :=
  (spaceScaling κ).hasFDerivAt.comp v (hk.hasFDerivAt.comp v (timeDilation κ).hasFDerivAt)

/-- The dilation maps the axis of time to `κ` times itself. -/
theorem timeDilation_single_zero (κ : ℝ) :
    timeDilation κ (Pi.single 0 1) = κ • (Pi.single 0 1 : Spacetime) := by
  ext μ
  refine Fin.cases ?_ (fun i => ?_) μ
  · simp [timeDilation_apply]
  · simp [timeDilation_apply, space_apply, Fin.succ_ne_zero]

/-- The dilation fixes the axes of space. -/
theorem timeDilation_single_succ (κ : ℝ) (i : Fin 3) :
    timeDilation κ (Pi.single i.succ 1) = (Pi.single i.succ 1 : Spacetime) := by
  ext μ
  refine Fin.cases ?_ (fun j => ?_) μ
  · simp [timeDilation_apply, (Fin.succ_ne_zero i)]
  · simp [timeDilation_apply, space_apply]

/-- The time derivative of a differentiable current is the derivative along the axis of time. -/
theorem currentRate_eq_fderiv {K : Spacetime → Spacetime} {v : Spacetime}
    (hK : DifferentiableAt ℝ K v) : currentRate K v = fderiv ℝ K v (Pi.single 0 1) := by
  funext μ
  exact partialAt_component_eq hK μ 0

/-- The time derivative of the slow family: `∂₀k_κ = κ (∂₀k)_κ`. -/
theorem currentRate_slowCurrent {k : Spacetime → Spacetime} (hk : Differentiable ℝ k) (κ : ℝ) :
    currentRate (slowCurrent κ k) = κ • slowCurrent κ (currentRate k) := by
  funext v
  have h := hasFDerivAt_slowCurrent (κ := κ) (hk (timeDilation κ v))
  rw [currentRate_eq_fderiv h.differentiableAt, h.fderiv, Pi.smul_apply, slowCurrent,
    currentRate_eq_fderiv (hk _)]
  simp only [ContinuousLinearMap.comp_apply, timeDilation_single_zero, map_smul]

/-- **The slow family is conserved**: `∂_μ k_κ^μ = κ (∂_μ k^μ)(κt, 𝐱) = 0`. -/
theorem divergence4_slowCurrent {k : Spacetime → Spacetime} (hk : Differentiable ℝ k)
    (hdiv : ∀ v, divergence4 k v = 0) (κ : ℝ) (v : Spacetime) :
    divergence4 (slowCurrent κ k) v = 0 := by
  have h := hdiv (timeDilation κ v)
  rw [divergence4, Fin.sum_univ_succ] at h
  rw [divergence4, (hasFDerivAt_slowCurrent (hk (timeDilation κ v))).fderiv, Fin.sum_univ_succ]
  simp only [ContinuousLinearMap.comp_apply, timeDilation_single_zero, timeDilation_single_succ,
    map_smul, Pi.smul_apply, smul_eq_mul, spaceScaling_apply_zero, spaceScaling_apply_succ]
  rw [← Finset.mul_sum]
  linear_combination κ * h

/-! ### Localized sources -/

/-- A smooth conserved current `k = (ρ, 𝐣)` whose spatial support lies in the ball `‖𝐱‖ ≤ a` at all
times and whose time derivatives `∂₀ᵐ𝐣` of orders `m ≤ N` have Euclidean norm at most `M`. -/
structure LocalizedSource (k : Spacetime → Spacetime) (a M : ℝ) (N : ℕ) : Prop where
  radius_nonneg : 0 ≤ a
  contDiff : ContDiff ℝ ∞ k
  conserved : ∀ v, divergence4 k v = 0
  support : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0
  bound : ∀ m ≤ N, ∀ v, ‖space ((currentRate^[m] k) v)‖ ≤ M

/-- The time derivative of a smooth current is smooth. -/
theorem contDiff_currentRate {K : Spacetime → Spacetime} (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (currentRate K) := by
  have h : currentRate K = fun v => fderiv ℝ K v (Pi.single 0 1) :=
    funext fun v => currentRate_eq_fderiv ((hK.differentiable (by simp)) v)
  rw [h]
  exact (hK.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- A function that vanishes outside the ball `‖𝐱‖ ≤ a` has a derivative that vanishes there. -/
theorem fderiv_eq_zero_of_ballSupport {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : Spacetime → G} {a : ℝ} (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → F (vector t x) = 0)
    {t : ℝ} {x : E3} (hx : a < ‖x‖) : fderiv ℝ F (vector t x) = 0 := by
  have hU : IsOpen {w : Spacetime | a < ‖space w‖} :=
    isOpen_lt continuous_const (continuous_norm.comp space.continuous)
  have hev : F =ᶠ[𝓝 (vector t x)] fun _ => 0 := by
    filter_upwards [hU.mem_nhds (by simpa using hx)] with w hw
    have h := hs (time w) (space w) hw
    rwa [vector_time_space] at h
  rw [hev.fderiv_eq]
  simp

/-- The time derivative of a current with spatial support in the ball `‖𝐱‖ ≤ a` has its support
there. -/
theorem currentRate_eq_zero_of_ballSupport {K : Spacetime → Spacetime} {a : ℝ}
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (t : ℝ) (x : E3) (hx : a < ‖x‖) :
    currentRate K (vector t x) = 0 := by
  funext μ
  have hμ : ∀ (t : ℝ) (x : E3), a < ‖x‖ → (fun w => K w μ) (vector t x) = 0 :=
    fun t x hx => by simp [hs t x hx]
  simp only [currentRate, partialAt]
  rw [fderiv_eq_zero_of_ballSupport (F := fun w => K w μ) hμ hx]
  rfl

/-- The time derivatives of a localized source are smooth. -/
theorem LocalizedSource.contDiff_iterate {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (m : ℕ) : ContDiff ℝ ∞ (currentRate^[m] k) := by
  induction m with
  | zero => exact hk.contDiff
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact contDiff_currentRate ih

/-- The time derivatives of a localized source vanish outside the ball `‖𝐱‖ ≤ a`. -/
theorem LocalizedSource.support_iterate {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (m : ℕ) :
    ∀ (t : ℝ) (x : E3), a < ‖x‖ → (currentRate^[m] k) (vector t x) = 0 := by
  induction m with
  | zero => exact hk.support
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact currentRate_eq_zero_of_ballSupport ih

/-- The bound of a localized source is nonnegative. -/
theorem LocalizedSource.bound_nonneg {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) : 0 ≤ M :=
  (norm_nonneg _).trans (hk.bound 0 (Nat.zero_le N) 0)

/-! ### Integrals over space -/

/-- A constant on the ball `‖y‖ ≤ a` is integrable. -/
theorem integrable_indicator_closedBall_const (a C : ℝ) :
    Integrable ((closedBall (0 : E3) a).indicator fun _ => C) :=
  (integrable_indicator_iff measurableSet_closedBall).2
    (integrableOn_const (by simp [ENNReal.mul_eq_top]))

/-- A function that vanishes outside the ball `‖y‖ ≤ a` and is bounded by `C` on it has
`‖∫ f‖ ≤ C · (4π/3)a³`. -/
theorem norm_integral_le_of_ballSupport {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E3 → G} {a C : ℝ} (ha : 0 ≤ a) (hf : ∀ y, a < ‖y‖ → f y = 0)
    (hb : ∀ y, ‖y‖ ≤ a → ‖f y‖ ≤ C) : ‖∫ y, f y‖ ≤ C * (4 * π / 3 * a ^ 3) := by
  have hg := integrable_indicator_closedBall_const a C
  calc ‖∫ y, f y‖ ≤ ∫ y, (closedBall (0 : E3) a).indicator (fun _ => C) y := by
        refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun y => ?_)
        by_cases hy : ‖y‖ ≤ a
        · rw [indicator_of_mem (by simpa using hy)]
          exact hb y hy
        · rw [hf y (not_le.1 hy), indicator_of_notMem (by simpa using hy)]
          simp
    _ = C * (4 * π / 3 * a ^ 3) := by
        rw [integral_indicator_const _ measurableSet_closedBall, smul_eq_mul, Measure.real,
          EuclideanSpace.volume_closedBall_fin_three, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal (by positivity)]
        ring

/-- A continuous function on space that vanishes for `‖y‖ > a` is integrable. -/
theorem integrable_of_ballSupport {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E3 → G} {a : ℝ} (hc : Continuous f) (hf : ∀ y, a < ‖y‖ → f y = 0) : Integrable f :=
  hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_closedBall 0 a) fun y hy => hf y (by simpa using hy))

/-- A continuous function on space-time is continuous in `(s, y)`. -/
theorem continuous_comp_vector_slice {G : Type*} [TopologicalSpace G] {F : Spacetime → G}
    (hF : Continuous F) : Continuous fun p : ℝ × E3 => F (vector p.1 p.2) :=
  hF.comp Wave.timeSpaceEquiv.symm.continuous

/-- **Differentiation under the integral sign** for functions of `(s, y)` that vanish for
`‖y‖ > a`, with jointly continuous derivative in `s`. -/
theorem hasDerivAt_integral_of_ballSupport {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {F F' : ℝ → E3 → G} {a : ℝ} (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F')) (hs : ∀ s y, a < ‖y‖ → F s y = 0)
    (hs' : ∀ s y, a < ‖y‖ → F' s y = 0) (hd : ∀ s y, HasDerivAt (fun s => F s y) (F' s y) s)
    (s₀ : ℝ) : HasDerivAt (fun s => ∫ y, F s y) (∫ y, F' s₀ y) s₀ := by
  have hsl : ∀ {H : ℝ → E3 → G}, Continuous (Function.uncurry H) → ∀ s,
      Continuous (H s) := fun hH s =>
    hH.comp (continuous_const.prodMk continuous_id : Continuous fun y : E3 => (s, y))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod
    (isCompact_closedBall (0 : E3) a)).exists_bound_of_continuousOn hF'.continuousOn
  have hg := integrable_indicator_closedBall_const a C
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s =>
      (integrable_of_ballSupport (hsl hF s) (hs s)).aestronglyMeasurable)
    (integrable_of_ballSupport (hsl hF s₀) (hs s₀))
    (integrable_of_ballSupport (hsl hF' s₀) (hs' s₀)).aestronglyMeasurable
    (Eventually.of_forall fun y s hs₁ => ?_) hg
    (Eventually.of_forall fun y s _ => hd s y)).2
  by_cases hy : ‖y‖ ≤ a
  · rw [indicator_of_mem (by simpa using hy)]
    exact hC (s, y) ⟨ball_subset_closedBall hs₁, by simpa using hy⟩
  · rw [hs' s y (not_le.1 hy), indicator_of_notMem (by simpa using hy)]
    simp

/-! ### Derivatives along time and space -/

/-- The line of time `t ↦ (t, 𝐲)` has the velocity `e₀`. -/
theorem hasDerivAt_vector_time (t : ℝ) (y : E3) :
    HasDerivAt (fun t => vector t y) (Pi.single 0 1 : Spacetime) t := by
  have h : HasDerivAt (fun t : ℝ => ((t, y) : ℝ × E3)) ((1 : ℝ), (0 : E3)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  have h2 := Wave.timeSpaceEquiv.symm.hasFDerivAt.comp_hasDerivAt t h
  rwa [← Wave.timeSpaceEquiv_single_zero, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] at h2

/-- The derivative of a function along a line of time. -/
theorem hasDerivAt_comp_vector_time {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : Spacetime → G} {t : ℝ} {y : E3} (hF : DifferentiableAt ℝ F (vector t y)) :
    HasDerivAt (fun t => F (vector t y)) (fderiv ℝ F (vector t y) (Pi.single 0 1)) t :=
  hF.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_vector_time t y)

/-- The time derivative of a current along a line of time. -/
theorem hasDerivAt_current_vector {K : Spacetime → Spacetime} (hK : Differentiable ℝ K)
    (t : ℝ) (y : E3) :
    HasDerivAt (fun t => K (vector t y)) (currentRate K (vector t y)) t := by
  rw [currentRate_eq_fderiv (hK _)]
  exact hasDerivAt_comp_vector_time (hK _)

/-- The time derivative of the spatial current along a line of time. -/
theorem hasDerivAt_space_current_vector {K : Spacetime → Spacetime} (hK : Differentiable ℝ K)
    (t : ℝ) (y : E3) :
    HasDerivAt (fun t => space (K (vector t y))) (space (currentRate K (vector t y))) t :=
  space.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_current_vector hK t y)

/-- The derivative of the slice `𝐲 ↦ (s, 𝐲)`. -/
theorem hasFDerivAt_vector_space (s : ℝ) (y : E3) :
    HasFDerivAt (fun y => vector s y)
      ((Wave.timeSpaceEquiv.symm : ℝ × E3 →L[ℝ] Spacetime).comp
        ((0 : E3 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E3))) y :=
  Wave.timeSpaceEquiv.symm.hasFDerivAt.comp y ((hasFDerivAt_const s y).prodMk (hasFDerivAt_id y))

/-- The derivative of a slice along the axis `i` of space. -/
theorem fderiv_comp_vector_single {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : Spacetime → G} {s : ℝ} {y : E3} (hF : DifferentiableAt ℝ F (vector s y)) (i : Fin 3) :
    fderiv ℝ (fun y => F (vector s y)) y (EuclideanSpace.single i 1) =
      fderiv ℝ F (vector s y) (Pi.single i.succ 1) := by
  have h : HasFDerivAt (fun y => F (vector s y)) _ y :=
    hF.hasFDerivAt.comp y (hasFDerivAt_vector_space s y)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]
  rw [← Wave.timeSpaceEquiv_single_succ, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- A function on space that vanishes outside the ball `‖y‖ ≤ a` has a derivative that vanishes
there. -/
theorem fderiv_space_eq_zero_of_ballSupport {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E3 → G} {a : ℝ} (hf : ∀ y, a < ‖y‖ → f y = 0) {y : E3} (hy : a < ‖y‖) :
    fderiv ℝ f y = 0 := by
  have hev : f =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact hf z hz
  rw [hev.fderiv_eq]
  simp

/-- A vector of `ℝ³` is the sum of its components along the axes. -/
theorem eq_sum_euclideanSingle (x : E3) :
    x = ∑ l : Fin 3, x l • EuclideanSpace.single l (1 : ℝ) := by
  ext j
  simp [Pi.single_apply]

/-- **Differentiation under the integral sign** for the moments `∫ K^μ(s, y) w(y) dy` of a smooth
current with spatial support in a ball, against a continuous weight `w`. -/
theorem hasDerivAt_integral_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) {w : E3 → G} (hw : Continuous w)
    (μ : Fin 4) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, K (vector s y) μ • w y)
      (∫ y, currentRate K (vector s y) μ • w y) s := by
  have hK1 : Differentiable ℝ K := hK.differentiable (by simp)
  have hc : ∀ {L : Spacetime → Spacetime}, ContDiff ℝ ∞ L →
      Continuous (Function.uncurry fun s y => L (vector s y) μ • w y) := fun hL =>
    ((continuous_apply μ).comp (continuous_comp_vector_slice hL.continuous)).smul
      (hw.comp continuous_snd)
  exact hasDerivAt_integral_of_ballSupport (a := a) (hc hK) (hc (contDiff_currentRate hK))
    (fun s y hy => by simp [hs s y hy])
    (fun s y hy => by simp [currentRate_eq_zero_of_ballSupport hs s y hy])
    (fun s y => ((hasDerivAt_pi.1 (hasDerivAt_current_vector hK1 s y)) μ).smul_const (w y)) s

/-- The spatial current `∫ 𝐊(s, y) dy` of a smooth current with spatial support in a ball has the
derivative `∫ ∂₀𝐊(s, y) dy`. -/
theorem hasDerivAt_integral_space {K : Spacetime → Spacetime} {a : ℝ} (hK : ContDiff ℝ ∞ K)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → K (vector t x) = 0) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, space (K (vector s y)))
      (∫ y, space (currentRate K (vector s y))) s := by
  have hK1 : Differentiable ℝ K := hK.differentiable (by simp)
  have hc : ∀ {L : Spacetime → Spacetime}, ContDiff ℝ ∞ L →
      Continuous (Function.uncurry fun s y => space (L (vector s y))) := fun hL =>
    space.continuous.comp (continuous_comp_vector_slice hL.continuous)
  exact hasDerivAt_integral_of_ballSupport (a := a) (hc hK) (hc (contDiff_currentRate hK))
    (fun s y hy => by simp [hs s y hy])
    (fun s y hy => by simp [currentRate_eq_zero_of_ballSupport hs s y hy])
    (fun s y => hasDerivAt_space_current_vector hK1 s y) s

/-! ### The conservation of charge -/

/-- The continuity equation `∂₀ρ = −Σₗ ∂ₗjₗ` on a slice of time. -/
theorem currentRate_zero_eq_neg_sum {k : Spacetime → Spacetime} (hk : Differentiable ℝ k)
    (hdiv : ∀ v, divergence4 k v = 0) (s : ℝ) (y : E3) :
    currentRate k (vector s y) 0 =
      -∑ l : Fin 3, fderiv ℝ (fun y => k (vector s y) l.succ) y (EuclideanSpace.single l 1) := by
  have h := hdiv (vector s y)
  rw [divergence4, Fin.sum_univ_succ] at h
  have hl : ∀ l : Fin 3,
      fderiv ℝ (fun y => k (vector s y) l.succ) y (EuclideanSpace.single l 1) =
        fderiv ℝ k (vector s y) (Pi.single l.succ 1) l.succ := by
    intro l
    rw [fderiv_comp_vector_single (F := fun w => k w l.succ) (differentiableAt_pi.1 (hk _) _) l]
    exact partialAt_component_eq (hk _) l.succ l.succ
  rw [currentRate_eq_fderiv (hk _), Finset.sum_congr rfl fun l _ => hl l]
  linarith

/-- **Integration by parts against the continuity equation**: for a `C¹` weight `W`,
`∫ W ∂₀ρ dy = ∫ ∇W · 𝐣 dy` on every slice of time. -/
theorem integral_mul_currentRate_zero {k : Spacetime → Spacetime} {a : ℝ}
    (hk : ContDiff ℝ ∞ k) (hdiv : ∀ v, divergence4 k v = 0)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) {W : E3 → ℝ}
    (hW : ContDiff ℝ 1 W) (s : ℝ) :
    ∫ y, W y * currentRate k (vector s y) 0 = ∫ y, fderiv ℝ W y (space (k (vector s y))) := by
  have hk1 : Differentiable ℝ k := hk.differentiable (by simp)
  set g : Fin 3 → E3 → ℝ := fun l y => k (vector s y) l.succ with hg
  have hgc : ∀ l, ContDiff ℝ 1 (g l) := fun l =>
    (ContinuousLinearMap.proj l.succ : Spacetime →L[ℝ] ℝ).contDiff.comp
      ((hk.of_le (by simp)).comp
        (Wave.timeSpaceEquiv.symm.contDiff.comp (contDiff_const.prodMk contDiff_id)))
  have hgs : ∀ l y, a < ‖y‖ → g l y = 0 := fun l y hy => by simp [hg, hs s y hy]
  have hgs' : ∀ l y, a < ‖y‖ → fderiv ℝ (g l) y = 0 := fun l y hy =>
    fderiv_space_eq_zero_of_ballSupport (hgs l) hy
  have hWc : Continuous W := hW.continuous
  have hW' : ∀ v, Continuous fun y => fderiv ℝ W y v := fun v =>
    (hW.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg' : ∀ l v, Continuous fun y => fderiv ℝ (g l) y v := fun l v =>
    ((hgc l).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i1 : ∀ l, Integrable fun y => fderiv ℝ W y (EuclideanSpace.single l 1) * g l y :=
    fun l => integrable_of_ballSupport (a := a) ((hW' _).mul (hgc l).continuous)
      fun y hy => by simp [hgs l y hy]
  have i2 : ∀ l, Integrable fun y => W y * fderiv ℝ (g l) y (EuclideanSpace.single l 1) :=
    fun l => integrable_of_ballSupport (a := a) (hWc.mul (hg' l _)) fun y hy => by
      simp [hgs' l y hy]
  have i3 : ∀ l, Integrable fun y => W y * g l y :=
    fun l => integrable_of_ballSupport (a := a) (hWc.mul (hgc l).continuous) fun y hy => by
      simp [hgs l y hy]
  have ibp : ∀ l, ∫ y, W y * fderiv ℝ (g l) y (EuclideanSpace.single l 1) =
      -∫ y, fderiv ℝ W y (EuclideanSpace.single l 1) * g l y := fun l =>
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (i1 l) (i2 l) (i3 l)
      (fun y _ => (hW.differentiable one_ne_zero) y)
      (fun y _ => ((hgc l).differentiable one_ne_zero) y)
  have h1 : ∀ y, W y * currentRate k (vector s y) 0 =
      ∑ l, -(W y * fderiv ℝ (g l) y (EuclideanSpace.single l 1)) := fun y => by
    rw [currentRate_zero_eq_neg_sum hk1 hdiv s y, mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  have h2 : ∀ y, fderiv ℝ W y (space (k (vector s y))) =
      ∑ l, fderiv ℝ W y (EuclideanSpace.single l 1) * g l y := fun y => by
    conv_lhs => rw [eq_sum_euclideanSingle (space (k (vector s y)))]
    simp [map_sum, map_smul, hg, mul_comm]
  simp_rw [h1, h2]
  rw [integral_finsetSum (f := fun l y => -(W y * fderiv ℝ (g l) y (EuclideanSpace.single l 1)))
    _ fun l _ => (i2 l).neg, integral_finsetSum _ fun l _ => i1 l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_neg, ibp l, neg_neg]

/-- The electric dipole moment `𝐝(s) = ∫ ρ(s, 𝐲) 𝐲 d𝐲` of a current at the time `s`. -/
def dipoleMoment (k : Spacetime → Spacetime) (s : ℝ) : E3 := ∫ y, k (vector s y) 0 • y

/-- **The conservation of charge** for the dipole moment: `∫ 𝐣 d𝐲 = ∫ ∂₀ρ 𝐲 d𝐲`. -/
theorem integral_space_eq {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    ∫ y, space (k (vector s y)) = ∫ y, currentRate k (vector s y) 0 • y := by
  have hint1 : Integrable fun y => space (k (vector s y)) :=
    integrable_of_ballSupport (a := a) (space.continuous.comp
      ((continuous_comp_vector_slice hk.continuous).comp
      (continuous_const.prodMk continuous_id))) fun y hy => by simp [hs s y hy]
  have hint2 : Integrable fun y => currentRate k (vector s y) 0 • y :=
    integrable_of_ballSupport (a := a) (((continuous_apply 0).comp ((continuous_comp_vector_slice
      (contDiff_currentRate hk).continuous).comp (continuous_const.prodMk continuous_id))).smul
        continuous_id) fun y hy => by simp [currentRate_eq_zero_of_ballSupport hs s y hy]
  refine ext_inner_left ℝ fun e => ?_
  rw [← integral_inner hint1, ← integral_inner hint2]
  have hW : ∀ y, fderiv ℝ (fun y => inner ℝ e y) y = innerSL ℝ e := fun y =>
    (innerSL ℝ e).fderiv
  have h := integral_mul_currentRate_zero hk hdiv hs (W := fun y => inner ℝ e y)
    (innerSL ℝ e).contDiff s
  simp only [hW, innerSL_apply_apply] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [inner_smul_right]
  ring

/-- **The time derivative of the dipole moment** is the integral of the current:
`𝐝̇(s) = ∫ 𝐣(s, 𝐲) d𝐲`. -/
theorem hasDerivAt_dipoleMoment {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    HasDerivAt (dipoleMoment k) (∫ y, space (k (vector s y))) s := by
  rw [integral_space_eq hk hdiv hs s]
  exact hasDerivAt_integral_smul hk hs continuous_id 0 s

/-- The second derivative of the dipole moment: `𝐝̈(s) = ∫ ∂₀𝐣(s, 𝐲) d𝐲`. -/
theorem deriv_deriv_dipoleMoment {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    deriv (deriv (dipoleMoment k)) s = ∫ y, space (currentRate k (vector s y)) := by
  have h : deriv (dipoleMoment k) = fun s => ∫ y, space (k (vector s y)) :=
    funext fun s => (hasDerivAt_dipoleMoment hk hdiv hs s).deriv
  rw [h]
  exact (hasDerivAt_integral_space hk hs s).deriv

/-- **The conservation of charge for the second moment**:
`∫ (yᵢjₗ + yₗjᵢ) d𝐲 = d/ds ∫ ρ yᵢyₗ d𝐲`. -/
theorem hasDerivAt_secondMoment {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hdiv : ∀ v, divergence4 k v = 0)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (i l : Fin 3) (s : ℝ) :
    HasDerivAt (fun s => ∫ y, k (vector s y) 0 * (y i * y l))
      (∫ y, (y i * k (vector s y) l.succ + y l * k (vector s y) i.succ)) s := by
  have h := hasDerivAt_integral_smul hk hs (w := fun y : E3 => y i * y l) (by fun_prop) 0 s
  simp only [smul_eq_mul] at h ⊢
  convert h using 1
  have hW : ∀ y : E3, HasFDerivAt (fun y : E3 => y i * y l)
      (y i • EuclideanSpace.proj l + y l • EuclideanSpace.proj i) y := fun y => by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.fun_mul
      (EuclideanSpace.proj (𝕜 := ℝ) l).hasFDerivAt (x := y)
  have hc : ContDiff ℝ 1 fun y : E3 => y i * y l := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.mul
      (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff (n := 1)
  have h2 := integral_mul_currentRate_zero hk hdiv hs hc s
  simp only [(hW _).fderiv] at h2
  rw [show (fun y => currentRate k (vector s y) 0 * (y i * y l)) =
    fun y => y i * y l * currentRate k (vector s y) 0 from funext fun y => mul_comm _ _, h2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [PiLp.proj_apply, space_apply]

/-! ### The amplitude of the slow family -/

/-- The inner product of `ℝ³` in components. -/
theorem inner_eq_sum_mul_fin_three (x y : E3) : inner ℝ x y = ∑ i : Fin 3, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

/-- Continuity of `x ↦ (τ(x), f(x))` in space-time. -/
theorem continuous_vector_of_continuous {X : Type*} [TopologicalSpace X] {τ : X → ℝ} {f : X → E3}
    (hτ : Continuous τ) (hf : Continuous f) : Continuous fun x => vector (τ x) (f x) :=
  Wave.timeSpaceEquiv.symm.continuous.comp (hτ.prodMk hf)

/-- The angular density `|∂ᵤÃ|² − ⟨n, ∂ᵤÃ⟩²` of the power radiated by a current in the direction
`n`, the integrand of `radiatedPower`. -/
def angularIntensity (k : Spacetime → Spacetime) (u : ℝ) (n : E3) : ℝ :=
  (∑ i : Fin 3, radiationAmplitude (currentRate k) u n i.succ ^ 2) -
    (∑ i : Fin 3, n i * radiationAmplitude (currentRate k) u n i.succ) ^ 2

/-- The radiated power is the integral of the angular density over the unit sphere. -/
theorem radiatedPower_eq_integral (k : Spacetime → Spacetime) (u : ℝ) :
    radiatedPower k u = ∫ n : sphere (0 : E3) 1, angularIntensity k u n ∂sphereMeasure := rfl

/-- The vector `∂ᵤÃ(u, n)` of the spatial components of the amplitude of `∂₀k`. -/
def amplitudeVector (k : Spacetime → Spacetime) (u : ℝ) (n : E3) : E3 :=
  WithLp.toLp 2 fun i => radiationAmplitude (currentRate k) u n i.succ

/-- The angular density in terms of the vector `∂ᵤÃ`: `|∂ᵤÃ|² − ⟨n, ∂ᵤÃ⟩²`. -/
theorem angularIntensity_eq (k : Spacetime → Spacetime) (u : ℝ) (n : E3) :
    angularIntensity k u n =
      ‖amplitudeVector k u n‖ ^ 2 - inner ℝ n (amplitudeVector k u n) ^ 2 := by
  rw [angularIntensity, EuclideanSpace.real_norm_sq_eq, inner_eq_sum_mul_fin_three]
  rfl

/-- The amplitude `∫ ∂ₛ𝐣(s + κ⟨n, y⟩, y) dy` of the slow family at the slow time `s = κu`, without
the factor `κ²/4π`. -/
def slowAmplitude (k : Spacetime → Spacetime) (κ s : ℝ) (n : E3) : E3 :=
  ∫ y, space (currentRate k (vector (s + κ * inner ℝ n y) y))

/-- The first correction `∫ ⟨n, y⟩ ∂ₛ²𝐣(s, y) dy` to the amplitude of the slow family. -/
def firstCorrection (k : Spacetime → Spacetime) (s : ℝ) (n : E3) : E3 :=
  ∫ y, inner ℝ n y • space (currentRate (currentRate k) (vector s y))

/-- The amplitude of the slow family: `∂ᵤÃ(u, n) = (κ²/4π) ∫ ∂ₛ𝐣(κu + κ⟨n, y⟩, y) dy`. -/
theorem amplitudeVector_slowCurrent {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (κ u : ℝ) (n : E3) :
    amplitudeVector (slowCurrent κ k) u n = (κ ^ 2 / (4 * π)) • slowAmplitude k κ (κ * u) n := by
  have hk1 : Differentiable ℝ k := hk.differentiable (by simp)
  have hint : Integrable fun y => space (currentRate k (vector (κ * u + κ * inner ℝ n y) y)) :=
    integrable_of_ballSupport (a := a) (space.continuous.comp
      ((contDiff_currentRate hk).continuous.comp
      (continuous_vector_of_continuous (by fun_prop) continuous_id)))
      fun y hy => by simp [currentRate_eq_zero_of_ballSupport hs _ y hy]
  ext i
  rw [amplitudeVector, PiLp.toLp_apply, radiationAmplitude, currentRate_slowCurrent hk1,
    PiLp.smul_apply, slowAmplitude, eval_integral_piLp (fun j => hint.eval_piLp j), smul_eq_mul,
    ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, slowCurrent_vector_succ, space_apply]
  rw [mul_add]
  field_simp

/-- The angular density of the slow family: `(κ²/4π)² (|Φ|² − ⟨n, Φ⟩²)` with the amplitude `Φ` of
`slowAmplitude`. -/
theorem angularIntensity_slowCurrent {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (κ u : ℝ) (n : E3) :
    angularIntensity (slowCurrent κ k) u n = (κ ^ 2 / (4 * π)) ^ 2 *
      (‖slowAmplitude k κ (κ * u) n‖ ^ 2 - inner ℝ n (slowAmplitude k κ (κ * u) n) ^ 2) := by
  rw [angularIntensity_eq, amplitudeVector_slowCurrent hk hs, norm_smul, real_inner_smul_right,
    Real.norm_eq_abs, mul_pow, sq_abs, mul_pow]
  ring

/-- A function of `(x, y)` that vanishes for `‖y‖ > a` has a continuous integral in `y`. -/
theorem continuous_integral_of_ballSupport {X G : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : X → E3 → G} {a : ℝ} (hF : Continuous (Function.uncurry F))
    (hs : ∀ x y, a < ‖y‖ → F x y = 0) : Continuous fun x => ∫ y, F x y := by
  have h : (fun x => ∫ y, F x y) = fun x => ∫ y in closedBall (0 : E3) a, F x y :=
    funext fun x => (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy =>
      hs x y (by simpa using hy)).symm
  rw [h]
  exact continuous_parametric_integral_of_continuous hF (isCompact_closedBall 0 a)

/-- The amplitude `Φ(n)` of the slow family is continuous in the direction. -/
theorem continuous_slowAmplitude {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (κ s : ℝ) :
    Continuous (slowAmplitude k κ s) :=
  continuous_integral_of_ballSupport (a := a) (space.continuous.comp
    ((contDiff_currentRate hk).continuous.comp (continuous_vector_of_continuous (by fun_prop)
      continuous_snd)))
    fun n y hy => by simp [currentRate_eq_zero_of_ballSupport hs _ y hy]

/-- The first correction `𝐜(n)` is continuous in the direction. -/
theorem continuous_firstCorrection {k : Spacetime → Spacetime} {a : ℝ} (hk : ContDiff ℝ ∞ k)
    (hs : ∀ (t : ℝ) (x : E3), a < ‖x‖ → k (vector t x) = 0) (s : ℝ) :
    Continuous (firstCorrection k s) := by
  have hc : Continuous fun p : E3 × E3 =>
      inner ℝ p.1 p.2 • space (currentRate (currentRate k) (vector s p.2)) :=
    (continuous_fst.inner continuous_snd).fun_smul
      (space.continuous.comp ((contDiff_currentRate (contDiff_currentRate hk)).continuous.comp
        (continuous_vector_of_continuous continuous_const continuous_snd)))
  exact continuous_integral_of_ballSupport (a := a) hc fun n y hy => by
    simp [currentRate_eq_zero_of_ballSupport (currentRate_eq_zero_of_ballSupport hs) _ y hy]

/-- The first correction is odd in the direction. -/
theorem firstCorrection_neg (k : Spacetime → Spacetime) (s : ℝ) (n : E3) :
    firstCorrection k s (-n) = -firstCorrection k s n := by
  simp only [firstCorrection, inner_neg_left, neg_smul, integral_neg]

/-- **Taylor's formula** with a bounded second derivative:
`‖f(h) − f(0) − h f'(0)‖ ≤ M h²`. -/
theorem norm_sub_sub_smul_le_of_deriv_two {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f f' f'' : ℝ → G} {M : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) (hM : ∀ t, ‖f'' t‖ ≤ M) (h : ℝ) :
    ‖f h - f 0 - h • f' 0‖ ≤ M * h ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have h1 : ∀ t, ‖f' t - f' 0‖ ≤ M * |t| := fun t => by
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f') (f' := f'')
      (s := univ) (fun x _ => (hf' x).hasDerivWithinAt) (fun x _ => hM x) convex_univ
      (mem_univ 0) (mem_univ t)
    simpa [Real.norm_eq_abs] using this
  have hd : ∀ x, HasDerivAt (fun t => f t - t • f' 0) (f' x - f' 0) x := fun x => by
    simpa using (hf x).fun_sub ((hasDerivAt_id x).smul_const (f' 0))
  have h2 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => f t - t • f' 0) (f' := fun t => f' t - f' 0) (s := uIcc 0 h) (C := M * |h|)
    (fun x _ => (hd x).hasDerivWithinAt)
    (fun x hx => (h1 x).trans (mul_le_mul_of_nonneg_left
      (by simpa using abs_sub_left_of_mem_uIcc hx) hM0)) (convex_uIcc 0 h) left_mem_uIcc
    right_mem_uIcc
  have he : f h - f 0 - h • f' 0 = (f h - h • f' 0) - (f 0 - (0 : ℝ) • f' 0) := by
    rw [zero_smul, sub_zero, sub_right_comm]
  rw [he]
  calc _ ≤ M * |h| * ‖h - 0‖ := h2
    _ = M * h ^ 2 := by rw [sub_zero, Real.norm_eq_abs, mul_assoc, abs_mul_abs_self, sq]

/-- **The expansion of the amplitude** in the slowness: `Φ(n) = 𝐝̈(s) + κ 𝐜(n) + 𝐞(n)` with
`‖𝐞(n)‖ ≤ M κ² a² (4π/3)a³`, by Taylor's formula in the delay `κ⟨n, y⟩` of the retarded time. -/
theorem norm_slowAmplitude_sub_le {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 3 ≤ N) (κ s : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    ‖slowAmplitude k κ s n - (∫ y, space (currentRate k (vector s y))) -
        κ • firstCorrection k s n‖ ≤ M * κ ^ 2 * a ^ 2 * (4 * π / 3 * a ^ 3) := by
  have hc1 : ContDiff ℝ ∞ (currentRate k) := contDiff_currentRate hk.contDiff
  have hc2 : ContDiff ℝ ∞ (currentRate (currentRate k)) := contDiff_currentRate hc1
  have hs1 : ∀ (t : ℝ) (x : E3), a < ‖x‖ → currentRate k (vector t x) = 0 :=
    currentRate_eq_zero_of_ballSupport hk.support
  have hs2 : ∀ (t : ℝ) (x : E3), a < ‖x‖ → currentRate (currentRate k) (vector t x) = 0 :=
    currentRate_eq_zero_of_ballSupport hs1
  have i1 : Integrable fun y => space (currentRate k (vector (s + κ * inner ℝ n y) y)) :=
    integrable_of_ballSupport (a := a) (space.continuous.comp (hc1.continuous.comp
      (continuous_vector_of_continuous (by fun_prop) continuous_id))) fun y hy => by
        simp [hs1 _ y hy]
  have i2 : Integrable fun y => space (currentRate k (vector s y)) :=
    integrable_of_ballSupport (a := a) (space.continuous.comp (hc1.continuous.comp
      (continuous_vector_of_continuous continuous_const continuous_id))) fun y hy => by
        simp [hs1 _ y hy]
  have hc3 : Continuous fun y => inner ℝ n y • space (currentRate (currentRate k) (vector s y)) :=
    (continuous_const.inner continuous_id).fun_smul (space.continuous.comp (hc2.continuous.comp
      (continuous_vector_of_continuous continuous_const continuous_id)))
  have i3 : Integrable fun y => inner ℝ n y • space (currentRate (currentRate k) (vector s y)) :=
    integrable_of_ballSupport (a := a) hc3 fun y hy => by simp [hs2 _ y hy]
  have i12 : Integrable fun y => space (currentRate k (vector (s + κ * inner ℝ n y) y)) -
      space (currentRate k (vector s y)) := i1.sub i2
  have i3' : Integrable fun y =>
      κ • (inner ℝ n y • space (currentRate (currentRate k) (vector s y))) := i3.smul κ
  rw [slowAmplitude, firstCorrection, ← integral_smul, ← integral_sub i1 i2,
    ← integral_sub i12 i3']
  refine norm_integral_le_of_ballSupport hk.radius_nonneg
    (fun y hy => by simp [hs1 _ y hy, hs2 _ y hy])
    fun y hy => ?_
  have hd1 : ∀ t, HasDerivAt (fun t => space (currentRate k (vector (s + t) y)))
      (space (currentRate (currentRate k) (vector (s + t) y))) t := fun t =>
    (hasDerivAt_space_current_vector (hc1.differentiable (by simp)) (s + t) y).comp_const_add s t
  have hd2 : ∀ t, HasDerivAt (fun t => space (currentRate (currentRate k) (vector (s + t) y)))
      (space (currentRate (currentRate (currentRate k)) (vector (s + t) y))) t := fun t =>
    (hasDerivAt_space_current_vector (hc2.differentiable (by simp)) (s + t) y).comp_const_add s t
  have hT := norm_sub_sub_smul_le_of_deriv_two hd1 hd2 (fun t => hk.bound 3 hN _) (κ * inner ℝ n y)
  simp only [add_zero] at hT
  rw [smul_smul]
  have hny : |inner ℝ n y| ≤ a := by
    calc |inner ℝ n y| ≤ ‖n‖ * ‖y‖ := abs_real_inner_le_norm n y
      _ ≤ a := by rw [hn, one_mul]; exact hy
  calc _ ≤ M * (κ * inner ℝ n y) ^ 2 := hT
    _ ≤ M * κ ^ 2 * a ^ 2 := by
        rw [mul_pow, mul_assoc]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (sq_nonneg κ))
          hk.bound_nonneg
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hny 2

/-- The bound `‖𝐝̈‖ = ‖∫ ∂ₛ𝐣 dy‖ ≤ M (4π/3)a³`. -/
theorem norm_integral_currentRate_le {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 1 ≤ N) (s : ℝ) :
    ‖∫ y, space (currentRate k (vector s y))‖ ≤ M * (4 * π / 3 * a ^ 3) :=
  norm_integral_le_of_ballSupport hk.radius_nonneg
    (fun y hy => by simp [currentRate_eq_zero_of_ballSupport hk.support _ y hy])
    fun y _ => hk.bound 1 hN _

/-- The bound `‖𝐜(n)‖ ≤ a M (4π/3)a³` of the first correction. -/
theorem norm_firstCorrection_le {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 2 ≤ N) (s : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    ‖firstCorrection k s n‖ ≤ a * M * (4 * π / 3 * a ^ 3) := by
  refine norm_integral_le_of_ballSupport hk.radius_nonneg (fun y hy => by
    simp [currentRate_eq_zero_of_ballSupport
      (currentRate_eq_zero_of_ballSupport hk.support) _ y hy])
    fun y hy => ?_
  rw [norm_smul, Real.norm_eq_abs]
  refine mul_le_mul ?_ (hk.bound 2 hN _) (norm_nonneg _) hk.radius_nonneg
  calc |inner ℝ n y| ≤ ‖n‖ * ‖y‖ := abs_real_inner_le_norm n y
    _ ≤ a := by rw [hn, one_mul]; exact hy

/-! ### The angular algebra -/

/-- The expansion of `|v|² − ⟨n, v⟩²` at `v = b + κc + e`. -/
theorem transverse_sq_expand (n b c e : E3) (κ : ℝ) :
    ‖b + κ • c + e‖ ^ 2 - inner ℝ n (b + κ • c + e) ^ 2 =
      (‖b‖ ^ 2 - inner ℝ n b ^ 2) + 2 * κ * (inner ℝ b c - inner ℝ n b * inner ℝ n c) +
        (κ ^ 2 * (‖c‖ ^ 2 - inner ℝ n c ^ 2) + 2 * (inner ℝ b e - inner ℝ n b * inner ℝ n e) +
          2 * κ * (inner ℝ c e - inner ℝ n c * inner ℝ n e) + (‖e‖ ^ 2 - inner ℝ n e ^ 2)) := by
  simp only [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm c b, real_inner_comm e b, real_inner_comm e c]
  ring

/-- For a unit vector `n`, `0 ≤ |v|² − ⟨n, v⟩² ≤ |v|²`. -/
theorem abs_transverse_sq_le {n v : E3} (hn : ‖n‖ = 1) :
    |‖v‖ ^ 2 - inner ℝ n v ^ 2| ≤ ‖v‖ ^ 2 := by
  have h : |inner ℝ n v| ≤ ‖v‖ := by simpa [hn] using abs_real_inner_le_norm n v
  have h2 : inner ℝ n v ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (inner ℝ n v)]

/-- For a unit vector `n`, `|⟨v, w⟩ − ⟨n, v⟩⟨n, w⟩| ≤ 2|v||w|`. -/
theorem abs_transverse_inner_le {n v w : E3} (hn : ‖n‖ = 1) :
    |inner ℝ v w - inner ℝ n v * inner ℝ n w| ≤ 2 * (‖v‖ * ‖w‖) := by
  have h1 : |inner ℝ n v| ≤ ‖v‖ := by simpa [hn] using abs_real_inner_le_norm n v
  have h2 : |inner ℝ n w| ≤ ‖w‖ := by simpa [hn] using abs_real_inner_le_norm n w
  calc _ ≤ |inner ℝ v w| + |inner ℝ n v * inner ℝ n w| := abs_sub _ _
    _ ≤ ‖v‖ * ‖w‖ + ‖v‖ * ‖w‖ := by
        rw [abs_mul]
        exact add_le_add (abs_real_inner_le_norm v w)
          (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _))
    _ = 2 * (‖v‖ * ‖w‖) := by ring

/-- The angular average of `|b|² − ⟨n, b⟩²`: `∫ (|b|² − ⟨n, b⟩²) dσ = (8π/3)|b|²`. -/
theorem integral_norm_sq_sub_inner_sq (b : E3) :
    ∫ n : sphere (0 : E3) 1, (‖b‖ ^ 2 - inner ℝ (n : E3) b ^ 2) ∂sphereMeasure =
      8 * π / 3 * ‖b‖ ^ 2 := by
  rw [integral_sub (integrable_const _) (integrable_of_continuous (by fun_prop)),
    integral_const, smul_eq_mul, sphereMeasure_real_univ, integral_inner_sq]
  ring

/-- The remainder of `transverse_sq_expand` for `‖b‖ ≤ β`, `‖c‖ ≤ γ`, `‖e‖ ≤ ε` and a unit vector
`n`. -/
theorem abs_transverse_remainder_le {n b c e : E3} {κ β γ ε : ℝ} (hn : ‖n‖ = 1) (hκ0 : 0 ≤ κ)
    (hb : ‖b‖ ≤ β) (hc : ‖c‖ ≤ γ) (he : ‖e‖ ≤ ε) :
    |κ ^ 2 * (‖c‖ ^ 2 - inner ℝ n c ^ 2) + 2 * (inner ℝ b e - inner ℝ n b * inner ℝ n e) +
        2 * κ * (inner ℝ c e - inner ℝ n c * inner ℝ n e) + (‖e‖ ^ 2 - inner ℝ n e ^ 2)| ≤
      κ ^ 2 * γ ^ 2 + 4 * β * ε + 4 * κ * γ * ε + ε ^ 2 := by
  have h1 := abs_transverse_sq_le (v := c) hn
  have h2 := abs_transverse_inner_le (v := b) (w := e) hn
  have h3 := abs_transverse_inner_le (v := c) (w := e) hn
  have h4 := abs_transverse_sq_le (v := e) hn
  have hb0 := norm_nonneg b
  have hc0 := norm_nonneg c
  have he0 := norm_nonneg e
  have hc2 : ‖c‖ ^ 2 ≤ γ ^ 2 := pow_le_pow_left₀ hc0 hc 2
  have he2 : ‖e‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ he0 he 2
  have hbe : ‖b‖ * ‖e‖ ≤ β * ε := mul_le_mul hb he he0 (hb0.trans hb)
  have hce : ‖c‖ * ‖e‖ ≤ γ * ε := mul_le_mul hc he he0 (hc0.trans hc)
  calc _ ≤ |κ ^ 2 * (‖c‖ ^ 2 - inner ℝ n c ^ 2)| +
          |2 * (inner ℝ b e - inner ℝ n b * inner ℝ n e)| +
          |2 * κ * (inner ℝ c e - inner ℝ n c * inner ℝ n e)| + |‖e‖ ^ 2 - inner ℝ n e ^ 2| :=
        (abs_add_le _ _).trans (add_le_add_left ((abs_add_le _ _).trans
          (add_le_add_left (abs_add_le _ _) _)) _)
    _ ≤ κ ^ 2 * γ ^ 2 + 2 * (2 * (β * ε)) + 2 * κ * (2 * (γ * ε)) + ε ^ 2 := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ κ ^ 2),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * κ)]
        gcongr
        · exact h1.trans hc2
        · exact h2.trans (by linarith)
        · exact h3.trans (by linarith)
        · exact h4.trans he2
    _ = κ ^ 2 * γ ^ 2 + 4 * β * ε + 4 * κ * γ * ε + ε ^ 2 := by ring

/-- The angular average of the term `⟨b, 𝐜(n)⟩ − ⟨n, b⟩⟨n, 𝐜(n)⟩` vanishes: it is odd in `n`. -/
theorem integral_inner_firstCorrection (k : Spacetime → Spacetime) (s : ℝ) (b : E3) :
    ∫ n : sphere (0 : E3) 1, (inner ℝ b (firstCorrection k s n) -
      inner ℝ (n : E3) b * inner ℝ (n : E3) (firstCorrection k s n)) ∂sphereMeasure = 0 :=
  integral_eq_zero_of_odd (f := fun x : E3 => inner ℝ b (firstCorrection k s x) -
      inner ℝ x b * inner ℝ x (firstCorrection k s x)) fun x => by
    simp only [firstCorrection_neg, inner_neg_left, inner_neg_right]
    ring

/-- **The angular density of the slow family**, to the order `κ⁵`: with `𝐛 = 𝐝̈(κu)` and the
first correction `𝐜(n)`, the density is `(κ²/4π)² (|𝐛|² − ⟨n, 𝐛⟩² + 2κ(⟨𝐛, 𝐜⟩ − ⟨n, 𝐛⟩⟨n, 𝐜⟩))`
up to `(κ²/4π)² κ² M² V² a²(5 + 4a + a²)`, where `V = (4π/3)a³`. -/
theorem abs_angularIntensity_slowCurrent_sub_le {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 3 ≤ N) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ)
    {n : E3} (hn : ‖n‖ = 1) :
    |angularIntensity (slowCurrent κ k) u n - (κ ^ 2 / (4 * π)) ^ 2 *
        ((‖∫ y, space (currentRate k (vector (κ * u) y))‖ ^ 2 -
          inner ℝ n (∫ y, space (currentRate k (vector (κ * u) y))) ^ 2) +
        2 * κ * (inner ℝ (∫ y, space (currentRate k (vector (κ * u) y)))
            (firstCorrection k (κ * u) n) -
          inner ℝ n (∫ y, space (currentRate k (vector (κ * u) y))) *
            inner ℝ n (firstCorrection k (κ * u) n)))| ≤
      (κ ^ 2 / (4 * π)) ^ 2 *
        (κ ^ 2 * (M ^ 2 * (4 * π / 3 * a ^ 3) ^ 2 * a ^ 2 * (5 + 4 * a + a ^ 2))) := by
  set b := ∫ y, space (currentRate k (vector (κ * u) y))
  set c := firstCorrection k (κ * u) n
  set V := 4 * π / 3 * a ^ 3 with hV
  set e := slowAmplitude k κ (κ * u) n - b - κ • c
  have hM := hk.bound_nonneg
  have ha := hk.radius_nonneg
  have hV0 : 0 ≤ V := by positivity
  have hbβ : ‖b‖ ≤ M * V := norm_integral_currentRate_le hk (by omega) _
  have hcγ : ‖c‖ ≤ a * M * V := norm_firstCorrection_le hk (by omega) _ hn
  have heε : ‖e‖ ≤ M * κ ^ 2 * a ^ 2 * V := norm_slowAmplitude_sub_le hk hN κ _ hn
  have hΦ : slowAmplitude k κ (κ * u) n = b + κ • c + e := by
    simp only [e]
    abel
  rw [angularIntensity_slowCurrent hk.contDiff hk.support, hΦ, transverse_sq_expand,
    show ∀ A B R : ℝ, (κ ^ 2 / (4 * π)) ^ 2 * (A + B + R) - (κ ^ 2 / (4 * π)) ^ 2 * (A + B) =
      (κ ^ 2 / (4 * π)) ^ 2 * R from fun A B R => by ring,
    abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ((abs_transverse_remainder_le hn hκ0.le hbβ hcγ heε).trans ?_)
    (by positivity)
  have hk3 : κ ^ 3 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0.le hκ1 (by norm_num)
  have hk4 : κ ^ 4 ≤ κ ^ 2 := pow_le_pow_of_le_one hκ0.le hκ1 (by norm_num)
  have hMV : 0 ≤ M ^ 2 * V ^ 2 := by positivity
  calc _ = M ^ 2 * V ^ 2 * (5 * κ ^ 2 * a ^ 2 + 4 * κ ^ 3 * a ^ 3 + κ ^ 4 * a ^ 4) := by ring
    _ ≤ M ^ 2 * V ^ 2 * (5 * κ ^ 2 * a ^ 2 + 4 * κ ^ 2 * a ^ 3 + κ ^ 2 * a ^ 4) := by gcongr
    _ = _ := by ring

/-- **The dipole radiation** (Landau–Lifshitz, §67, (67.8)): for the slow family of a localized
source, the radiated power is `I = κ⁴ (2/3)(1/4π) |𝐝̈(κu)|² = κ⁴ |𝐝̈|²/(6π)` up to
`(4π/9) M² a⁸ (5 + 4a + a²) κ⁶`; the term of order `κ⁵` is odd in the direction and vanishes. -/
theorem dipolePower_sub_le {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 3 ≤ N) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) :
    |radiatedPower (slowCurrent κ k) u -
        κ ^ 4 * (1 / (6 * π)) * ‖deriv (deriv (dipoleMoment k)) (κ * u)‖ ^ 2| ≤
      4 * π / 9 * M ^ 2 * a ^ 8 * (5 + 4 * a + a ^ 2) * κ ^ 6 := by
  rw [deriv_deriv_dipoleMoment hk.contDiff hk.conserved hk.support, radiatedPower_eq_integral]
  set b := ∫ y, space (currentRate k (vector (κ * u) y))
  set c := firstCorrection k (κ * u)
  set Φ := slowAmplitude k κ (κ * u)
  set C₀ := (κ ^ 2 / (4 * π)) ^ 2 with hC₀
  set main : E3 → ℝ := fun n => C₀ * ((‖b‖ ^ 2 - inner ℝ n b ^ 2) +
    2 * κ * (inner ℝ b (c n) - inner ℝ n b * inner ℝ n (c n))) with hmain
  have hcΦ : Continuous Φ := continuous_slowAmplitude hk.contDiff hk.support κ _
  have hcc : Continuous c := continuous_firstCorrection hk.contDiff hk.support _
  have hAP : (fun n : sphere (0 : E3) 1 => angularIntensity (slowCurrent κ k) u n) =
      fun n : sphere (0 : E3) 1 => C₀ * (‖Φ (n : E3)‖ ^ 2 - inner ℝ (n : E3) (Φ n) ^ 2) :=
    funext fun n => angularIntensity_slowCurrent hk.contDiff hk.support κ u n
  have hint1 : Integrable (fun n : sphere (0 : E3) 1 => angularIntensity (slowCurrent κ k) u n)
      sphereMeasure := by
    rw [hAP]
    exact integrable_of_continuous (by fun_prop)
  have hint2 : Integrable (fun n : sphere (0 : E3) 1 => main n) sphereMeasure :=
    integrable_of_continuous (by fun_prop)
  have hmain_int : ∫ n : sphere (0 : E3) 1, main n ∂sphereMeasure =
      κ ^ 4 * (1 / (6 * π)) * ‖b‖ ^ 2 := by
    simp only [hmain]
    rw [integral_const_mul, integral_add (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)), integral_norm_sq_sub_inner_sq,
      integral_const_mul, integral_inner_firstCorrection, hC₀]
    field_simp
    ring
  have hpt : ∀ n : sphere (0 : E3) 1, ‖angularIntensity (slowCurrent κ k) u n - main n‖ ≤
      C₀ * (κ ^ 2 * (M ^ 2 * (4 * π / 3 * a ^ 3) ^ 2 * a ^ 2 * (5 + 4 * a + a ^ 2))) :=
    fun n => abs_angularIntensity_slowCurrent_sub_le hk hN hκ0 hκ1 u (by simp)
  calc _ = |∫ n : sphere (0 : E3) 1, (angularIntensity (slowCurrent κ k) u n - main n)
        ∂sphereMeasure| := by rw [integral_sub hint1 hint2, hmain_int]
    _ ≤ C₀ * (κ ^ 2 * (M ^ 2 * (4 * π / 3 * a ^ 3) ^ 2 * a ^ 2 * (5 + 4 * a + a ^ 2))) *
          sphereMeasure.real univ := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le_const (Eventually.of_forall hpt)
    _ = _ := by
        rw [sphereMeasure_real_univ, hC₀]
        field_simp
        ring

/-- **The angular distribution of the dipole radiation** (Landau–Lifshitz, (67.7)): the angular
density of the slow family is `κ⁴ (|𝐝̈|² − ⟨n, 𝐝̈⟩²)/(16π²) = κ⁴ |𝐝̈ × n|²/(16π²)` up to
`M² a⁷ (4 + 5a + 4a² + a³) κ⁵/9`. -/
theorem dipoleAngular {k : Spacetime → Spacetime} {a M : ℝ} {N : ℕ}
    (hk : LocalizedSource k a M N) (hN : 3 ≤ N) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ)
    {n : E3} (hn : ‖n‖ = 1) :
    |angularIntensity (slowCurrent κ k) u n -
        κ ^ 4 * ((‖deriv (deriv (dipoleMoment k)) (κ * u)‖ ^ 2 -
          inner ℝ n (deriv (deriv (dipoleMoment k)) (κ * u)) ^ 2) / (16 * π ^ 2))| ≤
      M ^ 2 * a ^ 7 * (4 + 5 * a + 4 * a ^ 2 + a ^ 3) / 9 * κ ^ 5 := by
  rw [deriv_deriv_dipoleMoment hk.contDiff hk.conserved hk.support]
  set b := ∫ y, space (currentRate k (vector (κ * u) y))
  set c := firstCorrection k (κ * u) n
  set V := 4 * π / 3 * a ^ 3 with hV
  have hM := hk.bound_nonneg
  have ha := hk.radius_nonneg
  have hV0 : 0 ≤ V := by positivity
  have hbβ : ‖b‖ ≤ M * V := norm_integral_currentRate_le hk (by omega) _
  have hcγ : ‖c‖ ≤ a * M * V := norm_firstCorrection_le hk (by omega) _ hn
  have hB := abs_transverse_inner_le (v := b) (w := c) hn
  have h := abs_angularIntensity_slowCurrent_sub_le hk hN hκ0 hκ1 u hn
  have hbc : ‖b‖ * ‖c‖ ≤ M * V * (a * M * V) :=
    mul_le_mul hbβ hcγ (norm_nonneg _) (by positivity)
  have hk2 : κ ^ 2 ≤ κ := by nlinarith
  have hπ : (κ ^ 2 / (4 * π)) ^ 2 = κ ^ 4 / (16 * π ^ 2) := by ring
  rw [hπ] at h
  calc _ = |(angularIntensity (slowCurrent κ k) u n - κ ^ 4 / (16 * π ^ 2) *
          ((‖b‖ ^ 2 - inner ℝ n b ^ 2) +
            2 * κ * (inner ℝ b c - inner ℝ n b * inner ℝ n c))) +
          κ ^ 4 / (16 * π ^ 2) * (2 * κ * (inner ℝ b c - inner ℝ n b * inner ℝ n c))| := by
        congr 1
        ring
    _ ≤ κ ^ 4 / (16 * π ^ 2) *
          (κ ^ 2 * (M ^ 2 * V ^ 2 * a ^ 2 * (5 + 4 * a + a ^ 2))) +
        κ ^ 4 / (16 * π ^ 2) * (2 * κ * (2 * (M * V * (a * M * V)))) := by
        refine (abs_add_le _ _).trans (add_le_add h ?_)
        rw [abs_mul, abs_of_nonneg (by positivity), abs_mul,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * κ)]
        gcongr
        exact hB.trans (by linarith)
    _ ≤ κ ^ 4 / (16 * π ^ 2) * (κ * (M ^ 2 * V ^ 2 * a ^ 2 * (5 + 4 * a + a ^ 2))) +
        κ ^ 4 / (16 * π ^ 2) * (2 * κ * (2 * (M * V * (a * M * V)))) := by gcongr
    _ = _ := by
        rw [hV]
        field_simp
        ring

/-! ### An instance: the oscillating dipole -/

/-- The derivative `∂₁f = ∂f/∂x¹` of a function on space along the first axis. -/
def partialOne (f : E3 → ℝ) (x : E3) : ℝ := fderiv ℝ f x (EuclideanSpace.single 0 1)

/-- The derivative `∂₁f` of a smooth function is smooth. -/
theorem contDiff_partialOne {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (partialOne f) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- The derivative `∂₁f` vanishes where `f` vanishes near the point. -/
theorem partialOne_eq_zero {f : E3 → ℝ} {r : ℝ} (hf : ∀ x, r < ‖x‖ → f x = 0) {x : E3}
    (hx : r < ‖x‖) : partialOne f x = 0 := by
  simp [partialOne, fderiv_space_eq_zero_of_ballSupport hf hx]

/-- The oscillating current of a profile `f` on space with the phase `φ`:
`ρ(s, 𝐱) = cos(s + φ) ∂₁f(𝐱)` and `𝐣(s, 𝐱) = sin(s + φ) f(𝐱) e₁`. It is conserved,
`∂ₛρ + div 𝐣 = −sin(s + φ) ∂₁f + sin(s + φ) ∂₁f = 0`. -/
def oscillatingCurrent (f : E3 → ℝ) (φ : ℝ) : Spacetime → Spacetime := fun v =>
  (cos (v 0 + φ) * partialOne f (space v)) • (Pi.single 0 1 : Spacetime) +
    (sin (v 0 + φ) * f (space v)) • (Pi.single 1 1 : Spacetime)

/-- The charge density of the oscillating current. -/
theorem oscillatingCurrent_apply_zero (f : E3 → ℝ) (φ : ℝ) (v : Spacetime) :
    oscillatingCurrent f φ v 0 = cos (v 0 + φ) * partialOne f (space v) := by
  simp [oscillatingCurrent]

/-- The spatial current of the oscillating current. -/
theorem space_oscillatingCurrent (f : E3 → ℝ) (φ : ℝ) (v : Spacetime) :
    space (oscillatingCurrent f φ v) =
      (sin (v 0 + φ) * f (space v)) • EuclideanSpace.single 0 (1 : ℝ) := by
  ext i
  fin_cases i <;> simp [oscillatingCurrent, space_apply]

/-- The axis of time has no spatial part. -/
theorem space_pi_single_time : space (Pi.single 0 1 : Spacetime) = 0 := by
  ext i
  simp [space_apply, Fin.succ_ne_zero]

/-- The spatial part of the axis `1` of space-time is `e₁`. -/
theorem space_pi_single_one : space (Pi.single 1 1 : Spacetime) = EuclideanSpace.single 0 1 := by
  ext i
  fin_cases i <;> simp [space_apply]

/-- The unit vector `e₁` has norm `1`. -/
theorem norm_euclideanSingle_one : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 1 := by
  simp

/-- The derivative of `w ↦ P(w⁰) F(𝐰)`. -/
theorem hasFDerivAt_time_mul_space {P : ℝ → ℝ} {p : ℝ} {F : E3 → ℝ} {v : Spacetime}
    (hP : HasDerivAt P p (v 0)) (hF : DifferentiableAt ℝ F (space v)) :
    HasFDerivAt (fun w : Spacetime => P (w 0) * F (space w))
      (P (v 0) • (fderiv ℝ F (space v)).comp space +
        F (space v) • p • (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ)) v := by
  have h1 : HasFDerivAt (fun w : Spacetime => P (w 0))
      (p • (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ)) v :=
    hP.comp_hasFDerivAt v (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun w : Spacetime => F (space w)) ((fderiv ℝ F (space v)).comp space) v :=
    hF.hasFDerivAt.comp v space.hasFDerivAt
  exact h1.fun_mul h2

/-- The derivative of the oscillating current in the direction `w`. -/
theorem fderiv_oscillatingCurrent {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ) (v w : Spacetime) :
    fderiv ℝ (oscillatingCurrent f φ) v w =
      (cos (v 0 + φ) * fderiv ℝ (partialOne f) (space v) (space w) +
          partialOne f (space v) * (-sin (v 0 + φ) * w 0)) • (Pi.single 0 1 : Spacetime) +
        (sin (v 0 + φ) * fderiv ℝ f (space v) (space w) +
          f (space v) * (cos (v 0 + φ) * w 0)) • (Pi.single 1 1 : Spacetime) := by
  have hc : HasDerivAt (fun t => cos (t + φ)) (-sin (v 0 + φ)) (v 0) := by
    simpa using ((hasDerivAt_id' (v 0)).add_const φ).cos
  have hs : HasDerivAt (fun t => sin (t + φ)) (cos (v 0 + φ)) (v 0) := by
    simpa using ((hasDerivAt_id' (v 0)).add_const φ).sin
  have hA := hasFDerivAt_time_mul_space hc
    ((contDiff_partialOne hf).differentiable (by simp) (space v))
  have hB := hasFDerivAt_time_mul_space hs (hf.differentiable (by simp) (space v))
  have h := (hA.smul_const (Pi.single 0 1 : Spacetime)).fun_add
    (hB.smul_const (Pi.single 1 1 : Spacetime))
  have h' : HasFDerivAt (oscillatingCurrent f φ) _ v := h
  rw [h'.fderiv]
  simp only [FunLike.coe_add, Pi.add_apply, ContinuousLinearMap.smulRight_apply,
    FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- The oscillating current of a smooth profile is smooth. -/
theorem contDiff_oscillatingCurrent {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ) :
    ContDiff ℝ ∞ (oscillatingCurrent f φ) := by
  have h0 : ContDiff ℝ ∞ fun v : Spacetime => v 0 :=
    (ContinuousLinearMap.proj 0 : Spacetime →L[ℝ] ℝ).contDiff
  refine ((((h0.add contDiff_const).cos).mul ((contDiff_partialOne hf).comp
    space.contDiff)).smul contDiff_const).add ((((h0.add contDiff_const).sin).mul
      (hf.comp space.contDiff)).smul contDiff_const)

/-- The time derivative turns the phase by a quarter: `∂₀k_φ = k_{φ + π/2}`. -/
theorem currentRate_oscillatingCurrent {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ) :
    currentRate (oscillatingCurrent f φ) = oscillatingCurrent f (φ + π / 2) := by
  funext v
  rw [currentRate_eq_fderiv ((contDiff_oscillatingCurrent hf φ).differentiable (by simp) v),
    fderiv_oscillatingCurrent hf, space_pi_single_time, oscillatingCurrent]
  simp only [map_zero, mul_zero, zero_add, Pi.single_eq_same, mul_one]
  rw [← add_assoc, cos_add_pi_div_two, sin_add_pi_div_two]
  ring_nf

/-- The `m`-th time derivative turns the phase by `mπ/2`. -/
theorem currentRate_iterate_oscillatingCurrent {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ)
    (m : ℕ) :
    currentRate^[m] (oscillatingCurrent f φ) = oscillatingCurrent f (φ + m * (π / 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, currentRate_oscillatingCurrent hf]
    push_cast
    ring_nf

/-- The oscillating current is conserved. -/
theorem divergence4_oscillatingCurrent {f : E3 → ℝ} (hf : ContDiff ℝ ∞ f) (φ : ℝ)
    (v : Spacetime) : divergence4 (oscillatingCurrent f φ) v = 0 := by
  rw [divergence4, Fin.sum_univ_four]
  simp only [fderiv_oscillatingCurrent hf, space_pi_single_time, space_pi_single_one, map_zero,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp [partialOne]
  ring

/-- The oscillating current vanishes outside the support of the profile. -/
theorem oscillatingCurrent_eq_zero {f : E3 → ℝ} {r : ℝ} (hf : ∀ x, r < ‖x‖ → f x = 0) (φ : ℝ)
    (t : ℝ) (x : E3) (hx : r < ‖x‖) : oscillatingCurrent f φ (vector t x) = 0 := by
  simp [oscillatingCurrent, hf x hx, partialOne_eq_zero hf hx]

/-- **The oscillating current is a localized source**: for a smooth profile `f` supported in the
ball of radius `r` with `|f| ≤ B`, the oscillating current satisfies the hypotheses with the bound
`B` for the time derivatives of all orders. -/
theorem localizedSource_oscillatingCurrent {f : E3 → ℝ} {r B : ℝ} (hf : ContDiff ℝ ∞ f)
    (hr : 0 ≤ r) (hs : ∀ x, r < ‖x‖ → f x = 0) (hB : ∀ x, |f x| ≤ B) (φ : ℝ) (N : ℕ) :
    LocalizedSource (oscillatingCurrent f φ) r B N where
  radius_nonneg := hr
  contDiff := contDiff_oscillatingCurrent hf φ
  conserved := divergence4_oscillatingCurrent hf φ
  support := oscillatingCurrent_eq_zero hs φ
  bound m _ v := by
    rw [currentRate_iterate_oscillatingCurrent hf, space_oscillatingCurrent, norm_smul,
      norm_euclideanSingle_one, mul_one, Real.norm_eq_abs, abs_mul]
    calc _ ≤ 1 * B := mul_le_mul (abs_sin_le_one _) (hB _) (abs_nonneg _) zero_le_one
      _ = B := one_mul B

/-- **Integration by parts** for the first moment of a derivative:
`∫ ∂₁f(𝐲) 𝐲 d𝐲 = −(∫ f) e₁` for a smooth `f` supported in a ball. -/
theorem integral_partialOne_smul {f : E3 → ℝ} {r : ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : ∀ x, r < ‖x‖ → f x = 0) :
    ∫ y : E3, partialOne f y • y = (-∫ y, f y) • EuclideanSpace.single 0 (1 : ℝ) := by
  have hpc : Continuous (partialOne f) := (contDiff_partialOne hf).continuous
  have hint : Integrable fun y : E3 => partialOne f y • y :=
    integrable_of_ballSupport (a := r) (hpc.smul continuous_id)
      fun y hy => by simp [partialOne_eq_zero hs hy]
  have hfi : Integrable f := integrable_of_ballSupport (a := r) hf.continuous hs
  refine ext_inner_left ℝ fun e => ?_
  rw [← integral_inner hint, real_inner_smul_right]
  have hW : ∀ y : E3, fderiv ℝ (fun y => inner ℝ e y) y = innerSL ℝ e := fun y =>
    (innerSL ℝ e).fderiv
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y : E3 => inner ℝ e y) (g := f) (v := EuclideanSpace.single 0 1)
    (by simpa [hW] using hfi.const_mul (inner ℝ e (EuclideanSpace.single 0 1)))
    (integrable_of_ballSupport (a := r) ((continuous_const.inner continuous_id).mul hpc)
      fun y hy => by simp [fderiv_space_eq_zero_of_ballSupport hs hy])
    (integrable_of_ballSupport (a := r) ((continuous_const.inner continuous_id).mul
      hf.continuous) fun y hy => by simp [hs y hy])
    (fun y _ => (innerSL ℝ e).differentiableAt) (fun y _ => hf.differentiable (by simp) y)
  simp only [hW, innerSL_apply_apply] at h
  rw [show (fun y : E3 => inner ℝ e (partialOne f y • y)) =
    fun y => inner ℝ e y * fderiv ℝ f y (EuclideanSpace.single 0 1) from funext fun y => by
      rw [real_inner_smul_right, partialOne, mul_comm], h, integral_const_mul]
  ring

/-- The dipole moment of the oscillating current: `𝐝(s) = −cos(s + φ) (∫ f) e₁`, by the
integration by parts `∫ ∂₁f(𝐲) 𝐲 d𝐲 = −(∫ f) e₁`. -/
theorem dipoleMoment_oscillatingCurrent {f : E3 → ℝ} {r : ℝ} (hf : ContDiff ℝ ∞ f)
    (hs : ∀ x, r < ‖x‖ → f x = 0) (φ s : ℝ) :
    dipoleMoment (oscillatingCurrent f φ) s =
      (-(cos (s + φ) * ∫ y, f y)) • EuclideanSpace.single 0 (1 : ℝ) := by
  rw [dipoleMoment]
  simp only [oscillatingCurrent_apply_zero, vector_zero, space_vector]
  simp_rw [mul_smul]
  rw [integral_smul, integral_partialOne_smul hf hs, smul_smul]
  ring_nf

/-- A smooth bump on space: `1` on the unit ball, supported in the ball of radius `2`. -/
def dipoleBump : ContDiffBump (0 : E3) := ⟨1, 2, by norm_num, by norm_num⟩

/-- The bump vanishes outside the ball of radius `2`. -/
theorem dipoleBump_eq_zero (x : E3) (hx : 2 < ‖x‖) : dipoleBump x = 0 :=
  dipoleBump.zero_of_le_dist (by simpa [dipoleBump] using hx.le)

/-- The bump takes values in `[0, 1]`. -/
theorem abs_dipoleBump_le (x : E3) : |dipoleBump x| ≤ 1 := by
  rw [abs_of_nonneg (dipoleBump.nonneg' x)]
  exact dipoleBump.le_one

/-- The oscillating dipole `ρ = cos s ∂₁χ`, `𝐣 = sin s χ e₁` of the bump `χ = dipoleBump`. -/
def oscillatingDipole : Spacetime → Spacetime := oscillatingCurrent dipoleBump 0

/-- The oscillating dipole is a localized source with `a = 2` and `M = 1`. -/
theorem localizedSource_oscillatingDipole (N : ℕ) : LocalizedSource oscillatingDipole 2 1 N :=
  localizedSource_oscillatingCurrent dipoleBump.contDiff (by norm_num) dipoleBump_eq_zero
    abs_dipoleBump_le 0 N

/-- The dipole moment of the oscillating dipole: `𝐝(s) = −cos s (∫ χ) e₁`. -/
theorem dipoleMoment_oscillatingDipole (s : ℝ) :
    dipoleMoment oscillatingDipole s =
      (-(cos s * ∫ y, dipoleBump y)) • EuclideanSpace.single 0 (1 : ℝ) := by
  simpa [oscillatingDipole] using
    dipoleMoment_oscillatingCurrent dipoleBump.contDiff dipoleBump_eq_zero 0 s

/-- The second derivative of the dipole moment of the oscillating dipole:
`𝐝̈(s) = cos s (∫ χ) e₁`. -/
theorem deriv_deriv_dipoleMoment_oscillatingDipole (s : ℝ) :
    deriv (deriv (dipoleMoment oscillatingDipole)) s =
      (cos s * ∫ y, dipoleBump y) • EuclideanSpace.single 0 (1 : ℝ) := by
  have hk := localizedSource_oscillatingDipole 0
  rw [deriv_deriv_dipoleMoment hk.contDiff hk.conserved hk.support, oscillatingDipole,
    currentRate_oscillatingCurrent dipoleBump.contDiff]
  simp only [space_oscillatingCurrent, vector_zero, space_vector, zero_add, sin_add_pi_div_two]
  rw [integral_smul_const, integral_const_mul]

/-- The leading term of the oscillating dipole does not vanish: `∫ χ > 0`, so
`|𝐝̈(s)|² = cos² s (∫ χ)² > 0` whenever `cos s ≠ 0`. -/
theorem norm_deriv_deriv_dipoleMoment_oscillatingDipole (s : ℝ) :
    ‖deriv (deriv (dipoleMoment oscillatingDipole)) s‖ ^ 2 =
      cos s ^ 2 * (∫ y, dipoleBump y) ^ 2 := by
  rw [deriv_deriv_dipoleMoment_oscillatingDipole, norm_smul, norm_euclideanSingle_one,
    mul_one, Real.norm_eq_abs, sq_abs, mul_pow]

/-- The integral of the bump is positive. -/
theorem integral_dipoleBump_pos : 0 < ∫ y : E3, dipoleBump y := dipoleBump.integral_pos

/-- **An instance of the dipole formula**: the slow family of the oscillating dipole radiates
`κ⁴ cos²(κu) (∫ χ)²/(6π)` up to `(4π/9) 2⁸ · 17 κ⁶`, and the leading term is positive at `u = 0`. -/
theorem dipolePower_oscillatingDipole {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (u : ℝ) :
    |radiatedPower (slowCurrent κ oscillatingDipole) u -
        κ ^ 4 * (1 / (6 * π)) * (cos (κ * u) ^ 2 * (∫ y, dipoleBump y) ^ 2)| ≤
      4 * π / 9 * 2 ^ 8 * 17 * κ ^ 6 ∧
    0 < κ ^ 4 * (1 / (6 * π)) * (cos (κ * 0) ^ 2 * (∫ y, dipoleBump y) ^ 2) := by
  refine ⟨?_, ?_⟩
  · have h := dipolePower_sub_le (localizedSource_oscillatingDipole 3) le_rfl hκ0 hκ1 u
    rw [norm_deriv_deriv_dipoleMoment_oscillatingDipole] at h
    convert h using 1
    norm_num
  · have := integral_dipoleBump_pos
    simp only [mul_zero, cos_zero, one_pow, one_mul]
    positivity

end ProjectAinos.Electrodynamics.Radiation
