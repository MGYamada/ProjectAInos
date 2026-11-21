/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Euclidean.PolarIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Tactic

/-!
# Integrals over the unit sphere of `ℝ³`

The surface measure of the unit sphere `S² ⊂ ℝ³ = EuclideanSpace ℝ (Fin 3)` is
`sphereMeasure = volume.toSphere`, of total mass `4π` (`sphereMeasure_real_univ`). A continuous
function on the sphere is integrable (`integrable_of_continuous`), and
`integral_eq_integral_sphere_mul` is the formula of polar co-ordinates
`∫ F = (∫ f dσ) ∫₀^∞ r² h(r) dr` for `F(r n) = f(n) h(r)`.

* `integral_comp_linearIsometryEquiv`: the measure is invariant under the linear isometries
  (`measurePreserving_sphereMap`); `integral_eq_zero_of_comp_eq_neg`: the integral of a function
  whose sign an isometry reverses vanishes, and `integral_eq_zero_of_odd`: so does the integral of
  an odd function.
* **Archimedes**, `integral_comp_inner`: for a unit vector `e` and `g` continuous on `[−1, 1]`,
  `∫ g(⟨n, e⟩) dσ = 2π ∫_{−1}^{1} g`. With a vector orthogonal to `e`:
  `integral_inner_mul_comp_inner` (`= 0`), `integral_inner_sq_mul_comp_inner` and
  `integral_inner_mul_inner_mul_comp_inner`
  `∫ ⟨n, w₁⟩⟨n, w₂⟩ g(⟨n, e⟩) dσ = (⟨w₁, w₂⟩/2) ∫ (1 − ⟨n, e⟩²) g(⟨n, e⟩) dσ`.
* The moments: `integral_inner_pow` `∫ ⟨n, a⟩ᵏ dσ = ‖a‖ᵏ · 2π ∫_{−1}^{1} sᵏ ds`,
  `integral_inner_sq` and `integral_inner_pow_four` (`(4π/3)‖a‖²` and `(4π/5)‖a‖⁴`);
  `integral_inner` (first, `0`), `integral_inner_mul_inner`
  `∫ ⟨n, a⟩⟨n, b⟩ dσ = (4π/3)⟨a, b⟩` (second), `integral_inner_mul_inner_mul_inner` (third, `0`)
  and `integral_inner_mul_inner_mul_inner_mul_inner`
  `= (4π/15)(⟨a, b⟩⟨c, d⟩ + ⟨a, c⟩⟨b, d⟩ + ⟨a, d⟩⟨b, c⟩)` (fourth).

The invariance holds because `σ(s) = 3 vol((0, 1) • s)` and a linear isometry maps the cone over
`s` to the cone over its image. Archimedes is proved first for the moments `∫ n₃ᵏ dσ`, from the
integral of `x₃ᵏ e^{−|x|²}` over `ℝ³` computed once in polar co-ordinates and once by Fubini
(Gaussian and Gamma integrals), then for polynomials, and for continuous `g` by the Weierstrass
approximation theorem; a reflection carries `e` to the third unit vector. The second and fourth
moments follow by polarization from `∫ ⟨n, a⟩² dσ` and `∫ ⟨n, a⟩⁴ dσ`. For `w ⊥ e`, the
reflection in the plane orthogonal to `w` fixes `e` and reverses `⟨n, w⟩`; for the quadratic
moment, `e`, a unit vector `u ⊥ e` and `f = e × u` form an orthonormal basis, a reflection fixing
`e` exchanges `u` and `f`, and `⟨n, u⟩² + ⟨n, f⟩² = 1 − ⟨n, e⟩²` on the sphere.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real
open scoped Pointwise

namespace ProjectAinos.SmoothGeometry.Sphere

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The surface measure `σ` of the unit sphere of `ℝ³`. -/
abbrev sphereMeasure : Measure (sphere (0 : E3) 1) := (volume : Measure E3).toSphere

/-- The area of the unit sphere is `4π`. -/
theorem sphereMeasure_real_univ : sphereMeasure.real univ = 4 * π := by
  have hvol : (volume : Measure E3).real (ball 0 1) = π * 4 / 3 := by
    simp [Measure.real, ENNReal.toReal_ofReal (by positivity : 0 ≤ π * 4 / 3)]
  rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, hvol]
  push_cast
  ring

/-- A continuous function on the unit sphere is integrable for the surface measure. -/
theorem integrable_of_continuous {f : sphere (0 : E3) 1 → ℝ} (hf : Continuous f) :
    Integrable f sphereMeasure :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- The restriction of a linear isometry `L` of `ℝ³` to the unit sphere, as a measurable
equivalence. -/
def sphereMap (L : E3 ≃ₗᵢ[ℝ] E3) : sphere (0 : E3) 1 ≃ᵐ sphere (0 : E3) 1 where
  toFun n := ⟨L n, by simp⟩
  invFun n := ⟨L.symm n, by simp⟩
  left_inv n := by ext1; simp
  right_inv n := by ext1; simp
  measurable_toFun := by
    refine Measurable.subtype_mk ?_
    exact L.continuous.measurable.comp measurable_subtype_coe
  measurable_invFun := by
    refine Measurable.subtype_mk ?_
    exact L.symm.continuous.measurable.comp measurable_subtype_coe

/-- A linear isometry preserves the surface measure: `σ(L⁻¹ s) = 3 vol((0, 1) • L⁻¹ s)` and the
cone over `L⁻¹ s` is the preimage of the cone over `s`. -/
theorem measurePreserving_sphereMap (L : E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (sphereMap L) sphereMeasure sphereMeasure := by
  refine ⟨(sphereMap L).measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply (sphereMap L).measurable hs,
    Measure.toSphere_apply' _ ((sphereMap L).measurable hs), Measure.toSphere_apply' _ hs]
  congr 1
  have himage : ((↑) '' (sphereMap L ⁻¹' s) : Set E3) = L ⁻¹' ((↑) '' s) := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨sphereMap L n, hn, rfl⟩
    · rintro ⟨m, hm, hmx⟩
      have hx : x ∈ sphere (0 : E3) 1 := by
        have : ‖L x‖ = 1 := by rw [← hmx]; simp
        simpa using this
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      have : sphereMap L ⟨x, hx⟩ = m := by ext1; exact hmx.symm
      simpa [this] using hm
  have hcone : Ioo (0 : ℝ) 1 • (L ⁻¹' ((↑) '' s) : Set E3) =
      L ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [Set.mem_smul, Set.mem_preimage]
    constructor
    · rintro ⟨r, hr, y, hy, rfl⟩
      exact ⟨r, hr, L y, hy, by simp⟩
    · rintro ⟨r, hr, y, hy, hx⟩
      refine ⟨r, hr, L.symm y, by simpa using hy, ?_⟩
      apply L.injective
      simp [hx]
  rw [himage, hcone]
  exact (show MeasurePreserving L.toMeasurableEquiv volume volume from
    L.measurePreserving).measure_preimage_equiv _

/-- The surface measure is invariant under the linear isometries of `ℝ³`. -/
theorem integral_comp_linearIsometryEquiv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E3 ≃ₗᵢ[ℝ] E3) (f : E3 → G) :
    ∫ n : sphere (0 : E3) 1, f (L n) ∂sphereMeasure =
      ∫ n : sphere (0 : E3) 1, f n ∂sphereMeasure :=
  (measurePreserving_sphereMap L).integral_comp' (fun n : sphere (0 : E3) 1 => f n)

/-- If a linear isometry `L` changes the sign of `f`, `f ∘ L = −f`, then `∫ f dσ = 0`. -/
theorem integral_eq_zero_of_comp_eq_neg {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E3 ≃ₗᵢ[ℝ] E3) {f : E3 → G} (hf : ∀ x, f (L x) = -f x) :
    ∫ n : sphere (0 : E3) 1, f n ∂sphereMeasure = 0 := by
  have h := integral_comp_linearIsometryEquiv L f
  simp only [hf, integral_neg] at h
  have h2 : (2 : ℝ) • ∫ n : sphere (0 : E3) 1, f n ∂sphereMeasure = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/-- The integral over the sphere of an odd function vanishes. -/
theorem integral_eq_zero_of_odd {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E3 → G} (hf : ∀ x, f (-x) = -f x) :
    ∫ n : sphere (0 : E3) 1, f n ∂sphereMeasure = 0 :=
  integral_eq_zero_of_comp_eq_neg (LinearIsometryEquiv.neg ℝ) fun x => by simpa using hf x

/-- The first moment of the sphere vanishes. -/
theorem integral_inner (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ∂sphereMeasure = 0 :=
  integral_eq_zero_of_odd (f := fun x => inner ℝ x a) fun x => by rw [inner_neg_left]

/-- The third moment of the sphere vanishes. -/
theorem integral_inner_mul_inner_mul_inner (a b c : E3) :
    ∫ n : sphere (0 : E3) 1,
      inner ℝ (n : E3) a * inner ℝ (n : E3) b * inner ℝ (n : E3) c ∂sphereMeasure = 0 :=
  integral_eq_zero_of_odd (f := fun x => inner ℝ x a * inner ℝ x b * inner ℝ x c) fun x => by
    simp only [inner_neg_left]; ring

/-- A reflection is self-adjoint. -/
private theorem inner_reflection_left (K : Submodule ℝ E3) [K.HasOrthogonalProjection] (x y : E3) :
    inner ℝ (K.reflection x) y = inner ℝ x (K.reflection y) := by
  rw [LinearIsometryEquiv.inner_map_eq_flip, Submodule.reflection_symm]

/-- The integral of a function of `⟨n, e⟩` depends only on the length of `e`: the reflection
in the plane orthogonal to `e − e'` exchanges `e` and `e'`. -/
theorem integral_comp_inner_of_norm_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {e e' : E3} (h : ‖e‖ = ‖e'‖) (F : ℝ → G) :
    ∫ n : sphere (0 : E3) 1, F (inner ℝ (n : E3) e) ∂sphereMeasure =
      ∫ n : sphere (0 : E3) 1, F (inner ℝ (n : E3) e') ∂sphereMeasure := by
  set R := (ℝ ∙ (e - e'))ᗮ.reflection
  have hR : R e = e' := Submodule.reflection_sub h
  rw [← integral_comp_linearIsometryEquiv R (fun x => F (inner ℝ x e'))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  simp only
  rw [← hR, LinearIsometryEquiv.inner_map_map]

/-- **Polar co-ordinates** in `ℝ³`: if `F(r n) = f(n) h(r)` for `r > 0` and `n` on the unit
sphere, then `∫ F = (∫ f dσ) ∫₀^∞ r² h(r) dr`. -/
theorem integral_eq_integral_sphere_mul (F : E3 → ℝ) (f : sphere (0 : E3) 1 → ℝ) (h : ℝ → ℝ)
    (hF : ∀ (n : sphere (0 : E3) 1) (r : ℝ), 0 < r → F (r • (n : E3)) = f n * h r) :
    ∫ x, F x = (∫ n, f n ∂sphereMeasure) * ∫ r in Ioi (0 : ℝ), r ^ 2 * h r := by
  simpa using integral_polar_mul volume F f h hF

/-- Fubini for a Gaussian weight: `∫ x₃ᵏ e^{−|x|²} dx = (∫ e^{−z²} dz)² ∫ zᵏ e^{−z²} dz`. -/
private theorem integral_coord_pow_mul_gaussian (k : ℕ) :
    ∫ x : E3, (x 2) ^ k * exp (-‖x‖ ^ 2) =
      (∫ z : ℝ, exp (-z ^ 2)) ^ 2 * ∫ z : ℝ, z ^ k * exp (-z ^ 2) := by
  let g : Fin 3 → ℝ → ℝ := fun i z => (if i = 2 then z ^ k else 1) * exp (-z ^ 2)
  have hcoord : ∀ x : E3, (x 2) ^ k * exp (-‖x‖ ^ 2) = ∏ i : Fin 3, g i (x i) := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq, Fin.prod_univ_three, Fin.sum_univ_three]
    simp only [g, neg_add, exp_add]
    simp
    ring
  simp_rw [hcoord]
  have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun y : Fin 3 → ℝ => ∏ i : Fin 3, g i (y i))
  rw [show (∫ x : E3, ∏ i : Fin 3, g i (x i)) =
      ∫ x : E3, ∏ i : Fin 3, g i (((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm x) i) from rfl,
    this, integral_fintype_prod_volume_eq_prod, Fin.prod_univ_three]
  simp only [g, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide, ite_false,
    ite_true, one_mul]
  ring

/-- The third unit vector has length one. -/
private theorem norm_single_two : ‖(EuclideanSpace.single 2 1 : E3)‖ = 1 := by simp

/-- The component along the third unit vector. -/
private theorem inner_single_two (x : E3) : inner ℝ x (EuclideanSpace.single 2 1 : E3) = x 2 := by
  simp [EuclideanSpace.inner_single_right]

/-- The even moments of the third co-ordinate, `∫ n₃^{2m} dσ = 4π/(2m + 1)`, by comparing
polar co-ordinates with Fubini for `x₃^{2m} e^{−|x|²}`. -/
private theorem integral_inner_single_pow_even (m : ℕ) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) (EuclideanSpace.single 2 1 : E3) ^ (2 * m)
      ∂sphereMeasure = 4 * π / (2 * m + 1) := by
  set k := 2 * m with hk
  have hpolar := integral_eq_integral_sphere_mul (fun x : E3 => (x 2) ^ k * exp (-‖x‖ ^ 2))
    (fun n => inner ℝ (n : E3) (EuclideanSpace.single 2 1 : E3) ^ k)
    (fun r => r ^ k * exp (-r ^ 2)) (by
      intro n r hr
      simp only [inner_single_two, norm_smul, Real.norm_of_nonneg hr.le, norm_eq_of_mem_sphere,
        mul_one]
      simp only [PiLp.smul_apply, smul_eq_mul]
      ring)
  rw [integral_coord_pow_mul_gaussian k] at hpolar
  have hI : ∀ q : ℕ, ∫ x in Ioi (0 : ℝ), x ^ q * exp (-x ^ 2) = 1 / 2 * Gamma ((q + 1) / 2) := by
    intro q
    have := integral_rpow_mul_exp_neg_rpow (p := 2) (q := q) two_pos
      (by linarith [(q.cast_nonneg : (0 : ℝ) ≤ q)])
    simpa only [Real.rpow_natCast, Real.rpow_two] using this
  have hgauss : ∫ z : ℝ, exp (-z ^ 2) = √π := by
    simpa using integral_gaussian 1
  have habs : ∫ z : ℝ, z ^ k * exp (-z ^ 2) = 2 * ∫ z in Ioi (0 : ℝ), z ^ k * exp (-z ^ 2) := by
    rw [← integral_comp_abs (f := fun z => z ^ k * exp (-z ^ 2))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [sq_abs, hk, Even.pow_abs ⟨m, two_mul m⟩]
  have hrad : ∫ r in Ioi (0 : ℝ), r ^ 2 * (r ^ k * exp (-r ^ 2)) =
      ∫ r in Ioi (0 : ℝ), r ^ (k + 2) * exp (-r ^ 2) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only
    ring
  rw [hrad, hgauss, habs, hI, hI, Real.sq_sqrt pi_pos.le] at hpolar
  have hΓ : Gamma ((((k + 2 : ℕ) : ℝ) + 1) / 2) =
      (2 * m + 1) / 2 * Gamma ((((k : ℕ) : ℝ) + 1) / 2) := by
    rw [show (((k + 2 : ℕ) : ℝ) + 1) / 2 = (((k : ℕ) : ℝ) + 1) / 2 + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity)]
    rw [hk]
    push_cast
    ring
  rw [hΓ] at hpolar
  have hG : 0 < Gamma ((((k : ℕ) : ℝ) + 1) / 2) := Real.Gamma_pos_of_pos (by positivity)
  rw [eq_div_iff (by positivity)]
  have h3 : (∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) (EuclideanSpace.single 2 1 : E3) ^ k
      ∂sphereMeasure) * (2 * m + 1) * Gamma ((((k : ℕ) : ℝ) + 1) / 2) =
      4 * π * Gamma ((((k : ℕ) : ℝ) + 1) / 2) := by
    linear_combination 4 * hpolar.symm
  exact mul_right_cancel₀ hG.ne' h3

/-- The moments of the third co-ordinate, `∫ n₃ᵏ dσ = 2π ∫_{−1}^{1} sᵏ ds`. -/
private theorem integral_inner_single_pow (k : ℕ) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) (EuclideanSpace.single 2 1 : E3) ^ k
      ∂sphereMeasure = 2 * π * ∫ s in (-1 : ℝ)..1, s ^ k := by
  rw [integral_pow]
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [← two_mul, integral_inner_single_pow_even, Odd.neg_one_pow ⟨m, rfl⟩]
    push_cast
    field_simp
    ring
  · rw [integral_eq_zero_of_odd (f := fun x : E3 =>
        inner ℝ x (EuclideanSpace.single 2 1 : E3) ^ (2 * m + 1))
      fun x => by rw [inner_neg_left, Odd.neg_pow ⟨m, rfl⟩],
      Even.neg_one_pow ⟨m + 1, by ring⟩]
    simp


/-- For a unit vector `e` and `n` on the unit sphere, `⟨n, e⟩ ∈ [−1, 1]`. -/
theorem inner_mem_Icc {e : E3} (he : ‖e‖ = 1) (n : sphere (0 : E3) 1) :
    inner ℝ (n : E3) e ∈ Icc (-1 : ℝ) 1 := by
  have h := abs_real_inner_le_norm (n : E3) e
  rw [he, norm_eq_of_mem_sphere, mul_one] at h
  exact abs_le.mp h

/-- For a unit vector `e` and `g` continuous on `[−1, 1]`, `n ↦ g(⟨n, e⟩)` is continuous on the
sphere. -/
theorem continuous_comp_inner {e : E3} (he : ‖e‖ = 1) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1) 1)) :
    Continuous fun n : sphere (0 : E3) 1 => g (inner ℝ (n : E3) e) :=
  hg.comp_continuous (by fun_prop) (inner_mem_Icc he)

/-- Archimedes for a polynomial `p`: `∫ p(⟨n, e⟩) dσ = 2π ∫_{−1}^{1} p(s) ds`. -/
private theorem integral_eval_inner {e : E3} (he : ‖e‖ = 1) (p : Polynomial ℝ) :
    ∫ n : sphere (0 : E3) 1, p.eval (inner ℝ (n : E3) e) ∂sphereMeasure =
      2 * π * ∫ s in (-1 : ℝ)..1, p.eval s := by
  rw [integral_comp_inner_of_norm_eq (he.trans norm_single_two.symm) (fun s => p.eval s)]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    rw [integral_add (integrable_of_continuous (by fun_prop))
        (integrable_of_continuous (by fun_prop)),
      intervalIntegral.integral_add (p.continuous.intervalIntegrable _ _)
        (q.continuous.intervalIntegrable _ _), hp, hq]
    ring
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    rw [integral_const_mul, intervalIntegral.integral_const_mul, integral_inner_single_pow]
    ring

/-- **Archimedes**: for a unit vector `e` and a function `g` continuous on `[−1, 1]`,
`∫ g(⟨n, e⟩) dσ = 2π ∫_{−1}^{1} g(s) ds`. -/
theorem integral_comp_inner {e : E3} (he : ‖e‖ = 1) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, g (inner ℝ (n : E3) e) ∂sphereMeasure =
      2 * π * ∫ s in (-1 : ℝ)..1, g s := by
  have hIcc : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)
  have hgi : IntervalIntegrable g volume (-1) 1 := (hIcc ▸ hg).intervalIntegrable
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1) 1 g hg (ε / (8 * π))
    (by positivity)
  have h1 : ‖(∫ n : sphere (0 : E3) 1, g (inner ℝ (n : E3) e) ∂sphereMeasure) -
      ∫ n : sphere (0 : E3) 1, p.eval (inner ℝ (n : E3) e) ∂sphereMeasure‖ ≤
      ε / (8 * π) * (4 * π) := by
    rw [← integral_sub (integrable_of_continuous (continuous_comp_inner he hg))
      (integrable_of_continuous (by fun_prop)), ← sphereMeasure_real_univ]
    refine norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun n => ?_)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact (hp _ (inner_mem_Icc he n)).le
  have h2 : ‖(∫ s in (-1 : ℝ)..1, g s) - ∫ s in (-1 : ℝ)..1, p.eval s‖ ≤
      ε / (8 * π) * |(1 : ℝ) - (-1)| := by
    rw [← intervalIntegral.integral_sub hgi (p.continuous.intervalIntegrable _ _)]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
    rw [Real.norm_eq_abs, abs_sub_comm]
    have hx' : x ∈ Icc (-1 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num)] at hx
      exact Ioc_subset_Icc_self hx
    exact (hp x hx').le
  rw [integral_eval_inner he] at h1
  rw [Real.dist_eq]
  rw [Real.norm_eq_abs] at h1 h2
  have hpi := pi_pos
  have h2' : |2 * π * ((∫ s in (-1 : ℝ)..1, g s) - ∫ s in (-1 : ℝ)..1, p.eval s)| ≤
      2 * π * (ε / (8 * π) * |(1 : ℝ) - (-1)|) := by
    rw [abs_mul, abs_of_pos (by positivity)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  calc |(∫ n : sphere (0 : E3) 1, g (inner ℝ (n : E3) e) ∂sphereMeasure) -
        2 * π * ∫ s in (-1 : ℝ)..1, g s|
      = |((∫ n : sphere (0 : E3) 1, g (inner ℝ (n : E3) e) ∂sphereMeasure) -
          2 * π * ∫ s in (-1 : ℝ)..1, p.eval s) -
          2 * π * ((∫ s in (-1 : ℝ)..1, g s) - ∫ s in (-1 : ℝ)..1, p.eval s)| := by ring_nf
    _ ≤ ε / (8 * π) * (4 * π) + 2 * π * (ε / (8 * π) * |(1 : ℝ) - (-1)|) :=
        (abs_sub _ _).trans (add_le_add h1 h2')
    _ = ε := by
        rw [show |(1 : ℝ) - (-1)| = 2 by norm_num]
        field_simp
        ring


/-- Every vector is a multiple `a = ‖a‖ u` of a unit vector. -/
private theorem exists_unit_smul_eq (a : E3) : ∃ u : E3, ‖u‖ = 1 ∧ a = ‖a‖ • u := by
  by_cases ha : a = 0
  · exact ⟨EuclideanSpace.single 2 1, norm_single_two, by simp [ha]⟩
  · refine ⟨‖a‖⁻¹ • a, norm_smul_inv_norm ha, ?_⟩
    rw [smul_inv_smul₀ (norm_ne_zero_iff.mpr ha)]

/-- The moments in one direction: `∫ ⟨n, a⟩ᵏ dσ = ‖a‖ᵏ · 2π ∫_{−1}^{1} sᵏ ds`. -/
theorem integral_inner_pow (a : E3) (k : ℕ) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ^ k ∂sphereMeasure =
      ‖a‖ ^ k * (2 * π * ∫ s in (-1 : ℝ)..1, s ^ k) := by
  obtain ⟨u, hu, hau⟩ := exists_unit_smul_eq a
  have h : ∀ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ^ k = ‖a‖ ^ k * inner ℝ (n : E3) u ^ k := by
    intro n
    conv_lhs => rw [hau]
    rw [real_inner_smul_right, mul_pow]
  simp_rw [h]
  rw [integral_const_mul, integral_comp_inner hu (g := fun s => s ^ k) (by fun_prop)]

/-- `∫ ⟨n, a⟩² dσ = (4π/3)‖a‖²`. -/
theorem integral_inner_sq (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ^ 2 ∂sphereMeasure = 4 * π / 3 * ‖a‖ ^ 2 := by
  rw [integral_inner_pow, integral_pow]
  norm_num
  ring

/-- `∫ ⟨n, a⟩⁴ dσ = (4π/5)‖a‖⁴`. -/
theorem integral_inner_pow_four (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a ^ 4 ∂sphereMeasure =
      4 * π / 5 * (‖a‖ ^ 2) ^ 2 := by
  rw [integral_inner_pow, integral_pow]
  norm_num
  ring

/-- The second moment of the sphere: `∫ ⟨n, a⟩⟨n, b⟩ dσ = (4π/3)⟨a, b⟩`. -/
theorem integral_inner_mul_inner (a b : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a * inner ℝ (n : E3) b ∂sphereMeasure =
      4 * π / 3 * inner ℝ a b := by
  have h : ∀ n : sphere (0 : E3) 1, inner ℝ (n : E3) a * inner ℝ (n : E3) b =
      (inner ℝ (n : E3) (a + b) ^ 2 - inner ℝ (n : E3) (a - b) ^ 2) / 4 := by
    intro n
    rw [inner_add_right, inner_sub_right]
    ring
  simp_rw [h]
  rw [integral_div, integral_sub (integrable_of_continuous (by fun_prop))
      (integrable_of_continuous (by fun_prop)), integral_inner_sq, integral_inner_sq,
    norm_add_sq_real, norm_sub_sq_real]
  ring

/-- The square of the norm of `a + s b + t c + u d`. -/
private theorem norm_add_smul_sq (a b c d : E3) (s t u : ℝ) :
    ‖a + s • b + t • c + u • d‖ ^ 2 = ‖a‖ ^ 2 + s ^ 2 * ‖b‖ ^ 2 + t ^ 2 * ‖c‖ ^ 2 +
      u ^ 2 * ‖d‖ ^ 2 + 2 * s * inner ℝ a b + 2 * t * inner ℝ a c + 2 * u * inner ℝ a d +
      2 * s * t * inner ℝ b c + 2 * s * u * inner ℝ b d + 2 * t * u * inner ℝ c d := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq]
  rw [real_inner_comm a b, real_inner_comm a c, real_inner_comm a d, real_inner_comm b c,
    real_inner_comm b d, real_inner_comm c d]
  ring

/-- The fourth moment of the sphere:
`∫ ⟨n, a⟩⟨n, b⟩⟨n, c⟩⟨n, d⟩ dσ = (4π/15)(⟨a, b⟩⟨c, d⟩ + ⟨a, c⟩⟨b, d⟩ + ⟨a, d⟩⟨b, c⟩)`. -/
theorem integral_inner_mul_inner_mul_inner_mul_inner (a b c d : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) a * inner ℝ (n : E3) b * inner ℝ (n : E3) c *
      inner ℝ (n : E3) d ∂sphereMeasure =
      4 * π / 15 * (inner ℝ a b * inner ℝ c d + inner ℝ a c * inner ℝ b d +
        inner ℝ a d * inner ℝ b c) := by
  have h : ∀ n : sphere (0 : E3) 1, inner ℝ (n : E3) a * inner ℝ (n : E3) b *
      inner ℝ (n : E3) c * inner ℝ (n : E3) d =
        ∑ i : Fin 8, (![1, -1, -1, 1, -1, 1, 1, -1] : Fin 8 → ℝ) i *
          inner ℝ (n : E3) (a + (![1, 1, 1, 1, -1, -1, -1, -1] : Fin 8 → ℝ) i • b +
            (![1, 1, -1, -1, 1, 1, -1, -1] : Fin 8 → ℝ) i • c +
            (![1, -1, 1, -1, 1, -1, 1, -1] : Fin 8 → ℝ) i • d) ^ 4 / 192 := by
    intro n
    simp only [Fin.sum_univ_eight, inner_add_right]
    simp
    ring
  simp_rw [h]
  rw [integral_finsetSum _ fun i _ =>
    ((integrable_of_continuous (by fun_prop)).const_mul _).div_const _]
  simp only [integral_div, integral_const_mul, integral_inner_pow_four]
  simp only [norm_add_smul_sq]
  simp [Fin.sum_univ_eight]
  ring


/-- The inner product in the co-ordinates. -/
private theorem inner_eq_coords (x y : E3) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- Two orthonormal vectors `e, u` of `ℝ³` are completed by `f = e × u` to an orthonormal
basis, with `⟨x, e⟩² + ⟨x, u⟩² + ⟨x, f⟩² = ‖x‖²`. -/
private theorem exists_orthonormal_third {e u : E3} (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (hue : inner ℝ u e = 0) :
    ∃ f : E3, ‖f‖ = 1 ∧ inner ℝ e f = 0 ∧ inner ℝ u f = 0 ∧
      ∀ x : E3, inner ℝ x e ^ 2 + inner ℝ x u ^ 2 + inner ℝ x f ^ 2 = ‖x‖ ^ 2 := by
  have he2 : e 0 ^ 2 + e 1 ^ 2 + e 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq e
    rw [he, Fin.sum_univ_three] at h
    linarith
  have hu2 : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq u
    rw [hu, Fin.sum_univ_three] at h
    linarith
  have hue' : u 0 * e 0 + u 1 * e 1 + u 2 * e 2 = 0 := by
    rw [inner_eq_coords] at hue
    exact hue
  let f : E3 := WithLp.toLp 2 ![e 1 * u 2 - e 2 * u 1, e 2 * u 0 - e 0 * u 2,
    e 0 * u 1 - e 1 * u 0]
  have hf0 : f 0 = e 1 * u 2 - e 2 * u 1 := rfl
  have hf1 : f 1 = e 2 * u 0 - e 0 * u 2 := rfl
  have hf2 : f 2 = e 0 * u 1 - e 1 * u 0 := rfl
  refine ⟨f, ?_, ?_, ?_, fun x => ?_⟩
  · have h : ‖f‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, hf0, hf1, hf2]
      linear_combination (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) * he2 + hu2 -
        (u 0 * e 0 + u 1 * e 1 + u 2 * e 2) * hue'
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg f) two_ne_zero).mp h
  · rw [inner_eq_coords, hf0, hf1, hf2]
    ring
  · rw [inner_eq_coords, hf0, hf1, hf2]
    ring
  · rw [inner_eq_coords, inner_eq_coords, inner_eq_coords, hf0, hf1, hf2,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    linear_combination
      (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 - (x 0 * e 0 + x 1 * e 1 + x 2 * e 2) ^ 2) * hu2 +
      ((x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) -
        (x 0 * u 0 + x 1 * u 1 + x 2 * u 2) ^ 2) * he2 +
      (2 * (x 0 * e 0 + x 1 * e 1 + x 2 * e 2) * (x 0 * u 0 + x 1 * u 1 + x 2 * u 2) -
        (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) * (u 0 * e 0 + u 1 * e 1 + u 2 * e 2)) * hue'

/-- For a unit vector `e`, a vector `w ⊥ e` and `g` continuous on `[−1, 1]`,
`∫ ⟨n, w⟩ g(⟨n, e⟩) dσ = 0`. -/
theorem integral_inner_mul_comp_inner {e w : E3} (he : ‖e‖ = 1) (hw : inner ℝ w e = 0)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) w * g (inner ℝ (n : E3) e) ∂sphereMeasure = 0 := by
  -- The reflection argument needs neither the normalization of `e` nor the continuity of `g`.
  have _ := continuous_comp_inner he hg
  have hRw : (ℝ ∙ w)ᗮ.reflection w = -w :=
    Submodule.reflection_orthogonalComplement_singleton_eq_neg w
  have hRe : (ℝ ∙ w)ᗮ.reflection e = e :=
    Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hw)
  refine integral_eq_zero_of_comp_eq_neg (ℝ ∙ w)ᗮ.reflection
    (f := fun x => inner ℝ x w * g (inner ℝ x e)) fun x => ?_
  rw [inner_reflection_left, inner_reflection_left, hRw, hRe, inner_neg_right]
  ring

/-- For orthonormal `e, u`: `∫ ⟨n, u⟩² g(⟨n, e⟩) dσ = ½ ∫ (1 − ⟨n, e⟩²) g(⟨n, e⟩) dσ`. -/
private theorem integral_inner_sq_mul_comp_inner_of_unit {e u : E3} (he : ‖e‖ = 1) (hu : ‖u‖ = 1)
    (hue : inner ℝ u e = 0) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) u ^ 2 * g (inner ℝ (n : E3) e) ∂sphereMeasure =
      1 / 2 * ∫ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) e ^ 2) * g (inner ℝ (n : E3) e)
        ∂sphereMeasure := by
  obtain ⟨f, hf, hef, huf, hpars⟩ := exists_orthonormal_third he hu hue
  have hRu : (ℝ ∙ (u - f))ᗮ.reflection u = f := Submodule.reflection_sub (hu.trans hf.symm)
  have hRe : (ℝ ∙ (u - f))ᗮ.reflection e = e := by
    refine Submodule.reflection_mem_subspace_eq_self
      (Submodule.mem_orthogonal_singleton_iff_inner_right.mpr ?_)
    rw [inner_sub_left, hue, real_inner_comm, hef, sub_zero]
  have hswap : ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) f ^ 2 * g (inner ℝ (n : E3) e)
      ∂sphereMeasure =
      ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) u ^ 2 * g (inner ℝ (n : E3) e) ∂sphereMeasure := by
    rw [← integral_comp_linearIsometryEquiv (ℝ ∙ (u - f))ᗮ.reflection
      (fun x => inner ℝ x f ^ 2 * g (inner ℝ x e))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    have h1 := LinearIsometryEquiv.inner_map_map (ℝ ∙ (u - f))ᗮ.reflection (n : E3) u
    have h2 := LinearIsometryEquiv.inner_map_map (ℝ ∙ (u - f))ᗮ.reflection (n : E3) e
    rw [hRu] at h1
    rw [hRe] at h2
    simp only [h1, h2]
  have hcont := continuous_comp_inner he hg
  have hsum : ∫ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) e ^ 2) * g (inner ℝ (n : E3) e)
      ∂sphereMeasure =
      ∫ n : sphere (0 : E3) 1, (inner ℝ (n : E3) u ^ 2 * g (inner ℝ (n : E3) e) +
        inner ℝ (n : E3) f ^ 2 * g (inner ℝ (n : E3) e)) ∂sphereMeasure := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
    have h := hpars n
    rw [norm_eq_of_mem_sphere, one_pow] at h
    simp only
    linear_combination -(g (inner ℝ (n : E3) e)) * h
  have hc : ∀ v : E3, Continuous fun n : sphere (0 : E3) 1 =>
      inner ℝ (n : E3) v ^ 2 * g (inner ℝ (n : E3) e) := fun v =>
    ((continuous_subtype_val.inner continuous_const).pow 2).mul hcont
  rw [hsum, integral_add (integrable_of_continuous (hc u)) (integrable_of_continuous (hc f)),
    hswap]
  ring

/-- For a unit vector `e`, a vector `w ⊥ e` and `g` continuous on `[−1, 1]`,
`∫ ⟨n, w⟩² g(⟨n, e⟩) dσ = (‖w‖²/2) ∫ (1 − ⟨n, e⟩²) g(⟨n, e⟩) dσ`. -/
theorem integral_inner_sq_mul_comp_inner {e w : E3} (he : ‖e‖ = 1) (hw : inner ℝ w e = 0)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) w ^ 2 * g (inner ℝ (n : E3) e) ∂sphereMeasure =
      ‖w‖ ^ 2 / 2 * ∫ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) e ^ 2) *
        g (inner ℝ (n : E3) e) ∂sphereMeasure := by
  by_cases hw0 : w = 0
  · simp [hw0]
  · have hu : ‖‖w‖⁻¹ • w‖ = 1 := norm_smul_inv_norm hw0
    have hue : inner ℝ (‖w‖⁻¹ • w) e = 0 := by rw [real_inner_smul_left, hw, mul_zero]
    have h : ∀ n : sphere (0 : E3) 1, inner ℝ (n : E3) w ^ 2 * g (inner ℝ (n : E3) e) =
        ‖w‖ ^ 2 * (inner ℝ (n : E3) (‖w‖⁻¹ • w) ^ 2 * g (inner ℝ (n : E3) e)) := by
      intro n
      rw [real_inner_smul_right]
      field_simp
    simp_rw [h]
    rw [integral_const_mul, integral_inner_sq_mul_comp_inner_of_unit he hu hue hg]
    ring

/-- For a unit vector `e`, vectors `w₁, w₂ ⊥ e` and `g` continuous on `[−1, 1]`,
`∫ ⟨n, w₁⟩⟨n, w₂⟩ g(⟨n, e⟩) dσ = (⟨w₁, w₂⟩/2) ∫ (1 − ⟨n, e⟩²) g(⟨n, e⟩) dσ`. -/
theorem integral_inner_mul_inner_mul_comp_inner {e w₁ w₂ : E3} (he : ‖e‖ = 1)
    (hw₁ : inner ℝ w₁ e = 0) (hw₂ : inner ℝ w₂ e = 0) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1,
      inner ℝ (n : E3) w₁ * inner ℝ (n : E3) w₂ * g (inner ℝ (n : E3) e) ∂sphereMeasure =
      inner ℝ w₁ w₂ / 2 *
        ∫ n : sphere (0 : E3) 1, (1 - inner ℝ (n : E3) e ^ 2) * g (inner ℝ (n : E3) e)
          ∂sphereMeasure := by
  have hcont := continuous_comp_inner he hg
  have hc : ∀ v : E3, Continuous fun n : sphere (0 : E3) 1 =>
      inner ℝ (n : E3) v ^ 2 * g (inner ℝ (n : E3) e) := fun v =>
    ((continuous_subtype_val.inner continuous_const).pow 2).mul hcont
  have h : ∀ n : sphere (0 : E3) 1,
      inner ℝ (n : E3) w₁ * inner ℝ (n : E3) w₂ * g (inner ℝ (n : E3) e) =
      (inner ℝ (n : E3) (w₁ + w₂) ^ 2 * g (inner ℝ (n : E3) e) -
        inner ℝ (n : E3) (w₁ - w₂) ^ 2 * g (inner ℝ (n : E3) e)) / 4 := by
    intro n
    rw [inner_add_right, inner_sub_right]
    ring
  simp_rw [h]
  rw [integral_div, integral_sub (integrable_of_continuous (hc _))
      (integrable_of_continuous (hc _)),
    integral_inner_sq_mul_comp_inner he (by rw [inner_add_left, hw₁, hw₂, add_zero]) hg,
    integral_inner_sq_mul_comp_inner he (by rw [inner_sub_left, hw₁, hw₂, sub_zero]) hg,
    norm_add_sq_real, norm_sub_sq_real]
  ring

end ProjectAinos.SmoothGeometry.Sphere
