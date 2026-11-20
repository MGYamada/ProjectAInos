/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.Relativistic
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Tactic

/-!
# The radiation of an ultrarelativistic charge

The angular concentration of the radiation of a charge with the velocity `v = β ê` close to the
velocity of light (Landau–Lifshitz, *The Classical Theory of Fields*, §§73, 77; units with
`c = 1`), with `γ = 1/√(1 − β²)`, a unit vector `ê` and the angular distribution `angularPower`
of `Radiation.Relativistic`.

* `integral_one_sub_inner_mul_angularPower`: for every acceleration, the mean of `1 − n·ê`
  under the angular distribution is exactly `1 − β`, which is `≈ 1/(2γ²)` for `β → 1`.
* `integral_indicator_outsideCone_le`: the power radiated outside the cone of the half-angle
  `c/γ` about the velocity (`outsideCone ê (c √(1 − β²))`) is at most `π²/(2c²(1 + β))` times
  the total power; `integral_indicator_outsideCone_le_uniform`: at most `π²/(2c²)` times, for
  every `γ ≥ 1`, and the bound tends to `0` as `c → ∞` (`tendsto_concentrationBound`). The
  proof is the inequality of Markov for the weight `1 − n·ê`, which is at least `2θ²/π²` outside
  the cone of the half-angle `θ` (`le_one_sub_inner_of_mem_outsideCone`,
  `two_mul_sq_div_pi_sq_le_one_sub_cos`).
* The two cases of Landau–Lifshitz: the acceleration along the velocity, with the distribution
  `e² α² (1 − (n·ê)²)/(16π²(1 − β n·ê)⁵)` (`angularPower_smul_smul`), and the acceleration
  orthogonal to it (`angularPower_smul_of_inner_eq_zero`).

Not formalized (§77): the spectral resolution of the radiation, the characteristic frequency
`ω ∼ γ³|Ω|` of the synchrotron spectrum and its form in terms of Airy and Macdonald functions,
which need the method of stationary phase and special functions absent from Mathlib.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology

namespace ProjectAinos.Electrodynamics.Radiation.Ultrarelativistic

open SmoothGeometry SmoothGeometry.Sphere Relativistic

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `1 − cos θ ≥ 2θ²/π²` for `0 ≤ θ ≤ π`. -/
theorem two_mul_sq_div_pi_sq_le_one_sub_cos {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    2 * θ ^ 2 / π ^ 2 ≤ 1 - Real.cos θ := by
  have h1 : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h
    rw [h, Real.cos_sq']
    ring
  have h2 : θ / π ≤ Real.sin (θ / 2) := by
    have h := Real.mul_le_sin (x := θ / 2) (by positivity) (by linarith)
    calc θ / π = 2 / π * (θ / 2) := by field_simp
      _ ≤ _ := h
  have h3 : (θ / π) ^ 2 ≤ Real.sin (θ / 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
  rw [h1]
  have h4 : 2 * θ ^ 2 / π ^ 2 = 2 * (θ / π) ^ 2 := by ring
  linarith

/-- The directions of the unit sphere that make an angle larger than `θ` with `ê`: the outside
of the cone of the half-angle `θ` about `ê`. -/
def outsideCone (ê : E3) (θ : ℝ) : Set (sphere (0 : E3) 1) :=
  {n | θ < InnerProductGeometry.angle (n : E3) ê}

/-- On the unit sphere, the angle with the unit vector `ê` is `arccos (n·ê)`. -/
theorem angle_eq_arccos {ê : E3} (he : ‖ê‖ = 1) (n : sphere (0 : E3) 1) :
    InnerProductGeometry.angle (n : E3) ê = Real.arccos (inner ℝ (n : E3) ê) := by
  rw [InnerProductGeometry.angle, norm_eq_of_mem_sphere n, he, mul_one, div_one]

/-- The outside of a cone is measurable (it is open). -/
theorem measurableSet_outsideCone {ê : E3} (he : ‖ê‖ = 1) (θ : ℝ) :
    MeasurableSet (outsideCone ê θ) := by
  have h : outsideCone ê θ = {n : sphere (0 : E3) 1 | θ < Real.arccos (inner ℝ (n : E3) ê)} := by
    ext n
    simp only [outsideCone, Set.mem_ofPred_eq, angle_eq_arccos he n]
  rw [h]
  exact (isOpen_lt continuous_const
    (Real.continuous_arccos.comp (continuous_subtype_val.inner continuous_const))).measurableSet

/-- Outside the cone of the half-angle `θ > 0` about `ê`, `1 − n·ê ≥ 2θ²/π²`. -/
theorem le_one_sub_inner_of_mem_outsideCone {ê : E3} (he : ‖ê‖ = 1) {θ : ℝ} (hθ : 0 < θ)
    {n : sphere (0 : E3) 1} (hn : n ∈ outsideCone ê θ) :
    2 * θ ^ 2 / π ^ 2 ≤ 1 - inner ℝ (n : E3) ê := by
  have h1 : θ < Real.arccos (inner ℝ (n : E3) ê) := by
    rw [← angle_eq_arccos he n]
    exact hn
  have h2 := Real.arccos_le_pi (inner ℝ (n : E3) ê)
  have hs := inner_mem_Icc he n
  have h3 : inner ℝ (n : E3) ê < Real.cos θ := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi hθ.le h2 h1
    rwa [Real.cos_arccos hs.1 hs.2] at h
  have h4 := two_mul_sq_div_pi_sq_le_one_sub_cos hθ.le (by linarith)
  linarith

/-! ### The mean of `1 − n·ê` -/

/-- **The mean of `1 − cos θ` under the angular distribution** is `1 − β`: for the velocity
`v = β ê` with a unit vector `ê` and `|β| < 1` and any acceleration,
`∫ (1 − n·ê) dI/dΩ dσ = (1 − β) ∫ dI/dΩ dσ`; for `β → 1`, `1 − β ≈ 1/(2γ²)`. -/
theorem integral_one_sub_inner_mul_angularPower (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ}
    (hβ : |β| < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) ê) * angularPower e (β • ê) a n
        ∂sphereMeasure =
      (1 - β) * ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure := by
  have hv : ‖β • ê‖ < 1 := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs]
    exact hβ
  have cP := continuous_angularPower e hv a
  have iP := integrable_of_continuous cP
  have iQ : Integrable (fun n : sphere (0 : E3) 1 =>
      inner ℝ (n : E3) ê * angularPower e (β • ê) a n) sphereMeasure :=
    integrable_of_continuous ((continuous_subtype_val.inner continuous_const).mul cP)
  have h : ∀ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) ê) * angularPower e (β • ê) a n =
      angularPower e (β • ê) a n - inner ℝ (n : E3) ê * angularPower e (β • ê) a n := by
    intro n
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_sub iP iQ,
    integral_inner_mul_angularPower_of_eq_smul e he hβ a]
  ring

/-! ### The concentration in a cone of the half-angle `c/γ` -/

/-- **The radiation of a fast charge is concentrated in a cone of the half-angle `c/γ`**
(Landau–Lifshitz §77): for the velocity `v = β ê` with `0 ≤ β < 1`, `γ = 1/√(1 − β²)`, any
acceleration `a` and `c > 0`, the power radiated outside the cone of the half-angle
`c/γ = c √(1 − β²)` about `ê` is at most `π²/(2c²(1 + β))` times the total power. -/
theorem integral_indicator_outsideCone_le (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (a : E3) {c : ℝ} (hc : 0 < c) :
    ∫ n : sphere (0 : E3) 1, (outsideCone ê (c * √(1 - β ^ 2))).indicator
        (fun n => angularPower e (β • ê) a n) n ∂sphereMeasure ≤
      π ^ 2 / (2 * c ^ 2 * (1 + β)) *
        ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure := by
  have hβ : |β| < 1 := by rwa [abs_of_nonneg hβ0]
  have hv : ‖β • ê‖ < 1 := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs]
    exact hβ
  have hb : 0 < 1 - β ^ 2 := by nlinarith
  set θ := c * √(1 - β ^ 2) with hθdef
  have hθ : 0 < θ := mul_pos hc (Real.sqrt_pos.mpr hb)
  have hθsq : θ ^ 2 = c ^ 2 * (1 - β ^ 2) := by rw [hθdef, mul_pow, Real.sq_sqrt hb.le]
  have cP := continuous_angularPower e hv a
  have iP := integrable_of_continuous cP
  set K := π ^ 2 / (2 * θ ^ 2) with hK
  have hK0 : 0 < K := by positivity
  have iQ : Integrable (fun n : sphere (0 : E3) 1 =>
      K * ((1 - inner ℝ (n : E3) ê) * angularPower e (β • ê) a n)) sphereMeasure :=
    integrable_of_continuous (continuous_const.mul
      ((continuous_const.sub (continuous_subtype_val.inner continuous_const)).mul cP))
  have hbound : ∀ n : sphere (0 : E3) 1, (outsideCone ê θ).indicator
      (fun n => angularPower e (β • ê) a n) n ≤
        K * ((1 - inner ℝ (n : E3) ê) * angularPower e (β • ê) a n) := by
    intro n
    have hP := angularPower_nonneg e hv a n
    by_cases hn : n ∈ outsideCone ê θ
    · rw [indicator_of_mem hn]
      have h5 := le_one_sub_inner_of_mem_outsideCone he hθ hn
      have h6 : 1 ≤ K * (1 - inner ℝ (n : E3) ê) := by
        rw [hK, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        rw [div_le_iff₀ (by positivity)] at h5
        linarith
      calc angularPower e (β • ê) a n = 1 * angularPower e (β • ê) a n := (one_mul _).symm
        _ ≤ K * (1 - inner ℝ (n : E3) ê) * angularPower e (β • ê) a n :=
          mul_le_mul_of_nonneg_right h6 hP
        _ = _ := by ring
    · rw [indicator_of_notMem hn]
      have hs := (inner_mem_Icc he n).2
      have : 0 ≤ 1 - inner ℝ (n : E3) ê := by linarith
      positivity
  calc ∫ n : sphere (0 : E3) 1, (outsideCone ê θ).indicator
        (fun n => angularPower e (β • ê) a n) n ∂sphereMeasure
      ≤ ∫ n : sphere (0 : E3) 1, K * ((1 - inner ℝ (n : E3) ê) * angularPower e (β • ê) a n)
          ∂sphereMeasure :=
        integral_mono (iP.indicator (measurableSet_outsideCone he θ)) iQ hbound
    _ = K * ((1 - β) * ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure) := by
        rw [integral_const_mul, integral_one_sub_inner_mul_angularPower e he hβ a]
    _ = π ^ 2 / (2 * c ^ 2 * (1 + β)) *
        ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure := by
        rw [hK, hθsq]
        have h1 : 1 + β ≠ 0 := by linarith
        have h2 : 1 - β ≠ 0 := by linarith
        field_simp
        ring

/-- **The concentration, uniformly in `γ ≥ 1`**: the fraction of the power radiated outside the
cone of the half-angle `c/γ` about the velocity is at most `π²/(2c²)`, which tends to `0` as
`c → ∞` (`tendsto_concentrationBound`). -/
theorem integral_indicator_outsideCone_le_uniform (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (a : E3) {c : ℝ} (hc : 0 < c) :
    ∫ n : sphere (0 : E3) 1, (outsideCone ê (c * √(1 - β ^ 2))).indicator
        (fun n => angularPower e (β • ê) a n) n ∂sphereMeasure ≤
      π ^ 2 / (2 * c ^ 2) *
        ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure := by
  have hv : ‖β • ê‖ < 1 := by
    rw [norm_smul, he, mul_one, Real.norm_of_nonneg hβ0]
    exact hβ1
  have hI : 0 ≤ ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure :=
    integral_nonneg (angularPower_nonneg e hv a)
  refine (integral_indicator_outsideCone_le e he hβ0 hβ1 a hc).trans
    (mul_le_mul_of_nonneg_right ?_ hI)
  rw [div_le_div_iff_of_pos_left (by positivity) (by positivity) (by positivity)]
  nlinarith [sq_nonneg c]

/-- The bound `π²/(2c²)` of the fraction outside the cone tends to `0` as `c → ∞`. -/
theorem tendsto_concentrationBound :
    Tendsto (fun c : ℝ => π ^ 2 / (2 * c ^ 2)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop (two_ne_zero (α := ℕ))).const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  exact tendsto_const_nhds.div_atTop h

/-! ### The two cases of Landau–Lifshitz -/

/-- **The acceleration along the velocity**: for `v = β ê` and `a = α ê`,
`dI/dΩ = e² α² (1 − (n·ê)²)/(16π²(1 − β n·ê)⁵)`, which vanishes along the velocity. -/
theorem angularPower_smul_smul (e α β : ℝ) {ê n : E3} (he : ‖ê‖ = 1) (hn : ‖n‖ = 1) :
    angularPower e (β • ê) (α • ê) n =
      e ^ 2 * α ^ 2 * (1 - inner ℝ n ê ^ 2) / (16 * π ^ 2 * (1 - β * inner ℝ n ê) ^ 5) := by
  rw [angularPower, norm_cross_cross_sq hn, real_inner_smul_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_smul_right, norm_smul, norm_smul, he,
    real_inner_self_eq_norm_sq, he]
  simp only [mul_one, Real.norm_eq_abs, mul_pow, sq_abs, one_pow]
  congr 1
  ring

/-- **The acceleration orthogonal to the velocity**: for `v = β ê` with `|β| < 1` and `a ⊥ ê`,
`dI/dΩ = (e²/16π²)(a²/(1 − β n·ê)³ − (1 − β²)(n·a)²/(1 − β n·ê)⁵)`. -/
theorem angularPower_smul_of_inner_eq_zero (e β : ℝ) {ê a n : E3} (he : ‖ê‖ = 1)
    (hβ : |β| < 1) (ha : inner ℝ a ê = 0) (hn : ‖n‖ = 1) :
    angularPower e (β • ê) a n = e ^ 2 / (16 * π ^ 2) *
      (‖a‖ ^ 2 / (1 - β * inner ℝ n ê) ^ 3 -
        (1 - β ^ 2) * inner ℝ n a ^ 2 / (1 - β * inner ℝ n ê) ^ 5) := by
  have hv : ‖β • ê‖ < 1 := by
    rw [norm_smul, he, mul_one, Real.norm_eq_abs]
    exact hβ
  have hva : inner ℝ (β • ê) a = 0 := by rw [real_inner_smul_left, real_inner_comm, ha, mul_zero]
  rw [angularPower_of_inner_eq_zero e hv hva hn, real_inner_smul_right, norm_smul, he, mul_one,
    Real.norm_eq_abs, sq_abs]

end ProjectAinos.Electrodynamics.Radiation.Ultrarelativistic
