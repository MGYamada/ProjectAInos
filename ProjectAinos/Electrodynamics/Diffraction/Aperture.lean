/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Diffraction: the scalar aperture field

Space is `ℝ³ = EuclideanSpace ℝ (Fin 3)` and the screen is the plane `z = 0`, whose points
`planePoint y = (y₁, y₂, 0)` are labelled by `y ∈ ℝ² = EuclideanSpace ℝ (Fin 2)`; the point at
the height `z` over `x ∈ ℝ²` is `spacePoint x z`. The light behind the screen is a complex
scalar field `u e^{−iωt}` of the wave number `k = ω` in the half-space
`upperHalfSpace = {z > 0}`, with given values `u₀` in the plane of the aperture: this is the
scalar model of diffraction (Landau–Lifshitz, *The Classical Theory of Fields*, §59). The data
`u₀` are continuous with compact support; they need not be smooth.

* `sphericalWave k q = e^{ik|q|}/(4π|q|)`, the outgoing spherical wave `G_k`, and
  `rayleighKernel k q = q_z e^{ik|q|}(1 − ik|q|)/(2π|q|³)`, which is `−2∂_z G_k`
  (`rayleighKernel_eq_fderiv_sphericalWave`), with the radial profile `kernelProfile`.
* `apertureField k u₀ p = ∫ u₀(y) (−2∂_z G_k)(p − (y, 0)) dy`, **the Rayleigh–Sommerfeld
  integral**, a case of the integral `planeIntegral u₀ g` over the aperture.
* `contDiffOn_apertureField`: the field is smooth on `z > 0`. The derivatives are taken under the
  integral: `hasFDerivAt_planeIntegral` for a kernel of class `C¹` on `z > 0`, and
  `contDiffOn_planeIntegral` by induction on the order.
* `helmholtz_apertureField`: **the Helmholtz equation** `Δu + k²u = 0` on `z > 0`, with Mathlib's
  Laplacian, because the kernel solves it away from its pole: `sum_fderiv_fderiv_rayleighKernel`
  from the radial equation `kernelSlope_radial`, and `helmholtz_rayleighKernel`.
* `tendsto_apertureField_boundary`: **the boundary values**, `u(x, z) → u₀(x)` as `z → 0⁺`. The
  kernel is the Poisson kernel `poissonKernel z w = z/(2πR³)` of the half-space times
  `e^{ikR}(1 − ikR)` (`rayleighKernel_spacePoint`); after the substitution `w = zv`
  (`apertureField_spacePoint_eq`) the limit is dominated convergence, and the Poisson kernel has
  the integral one (`integral_poissonKernel_one`).
* `integral_ball_rayleighKernel`, `tendsto_integral_ball_rayleighKernel`: the unobstructed
  plane wave, `∫_{|w| < L} K(w, z) dw = e^{ikz} − z e^{ikR_L}/R_L → e^{ikz}`. The kernel decays
  like `|w|⁻²` and is not integrable on the plane, so the constant data `1` are reproduced only
  in this improper sense.
* `IsRadiating k u`: **the Sommerfeld radiation condition** in the half-space, `u = O(1/r)` and
  `r(∂_r u − iku) → 0` uniformly in the direction. `norm_mul_apertureField_le` and
  `norm_radiation_apertureField_le` give the explicit rates `r|u| ≤ (4/r + 2k)‖u₀‖₁/π` and
  `r|∂_r u − iku| = O(1/r)`, from the kernel bounds `norm_mul_rayleighKernel_le` and
  `norm_radial_rayleighKernel_le`; `apertureField_isRadiating` is the condition.
* `apertureBump`: a smooth aperture of compact support, with the instances
  `contDiffOn_apertureField_apertureBump`, `helmholtz_apertureField_apertureBump`,
  `apertureField_apertureBump_tendsto`, `apertureField_apertureBump_isRadiating` and
  `norm_radiation_apertureField_apertureBump_le`.

Not proved here: the relation of the scalar model to the screen problem of Maxwell's equations.
The values of Kirchhoff's approximation are not the trace of a solution, and the vector problem
of a screen is a mixed boundary problem with edge singularities (the conditions of Meixner),
which the library cannot state. Nor is the uniqueness of the radiating solution of the
half-space Dirichlet problem, which needs Green's representation formula on bounded domains.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Complex
open scoped Topology ContDiff Laplacian InnerProductSpace Real

namespace ProjectAinos.Electrodynamics.Diffraction

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Points of the plane and of space -/

/-- The point `(y₁, y₂, 0)` of the screen `z = 0` over `y ∈ ℝ²`. -/
def planePoint (y : E2) : E3 := !₂[y 0, y 1, 0]

/-- The point `(x₁, x₂, z)` of space at the height `z` over `x ∈ ℝ²`. -/
def spacePoint (x : E2) (z : ℝ) : E3 := !₂[x 0, x 1, z]

/-- The half-space `z > 0` behind the screen. -/
def upperHalfSpace : Set E3 := {p | 0 < p 2}

/-- The screen is the plane `z = 0`. -/
@[simp] theorem planePoint_apply_two (y : E2) : planePoint y 2 = 0 := by
  simp [planePoint]

/-- The point `spacePoint x z` has the height `z`. -/
@[simp] theorem spacePoint_apply_two (x : E2) (z : ℝ) : spacePoint x z 2 = z := by
  simp [spacePoint]

/-- A translation along the screen keeps the height. -/
@[simp] theorem sub_planePoint_apply_two (p : E3) (y : E2) : (p - planePoint y) 2 = p 2 := by
  simp

/-- The squared norm of `ℝ³` in the co-ordinates. -/
theorem norm_sq_eq_three (q : E3) : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- The squared norm of `ℝ²` in the co-ordinates. -/
theorem norm_sq_eq_two (y : E2) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- `|(x, z)|² = |x|² + z²`. -/
theorem norm_sq_spacePoint (x : E2) (z : ℝ) : ‖spacePoint x z‖ ^ 2 = ‖x‖ ^ 2 + z ^ 2 := by
  rw [norm_sq_eq_three, norm_sq_eq_two]
  simp [spacePoint]

/-- `|(x, z)| = (|x|² + z²)^{1/2}`. -/
theorem norm_spacePoint (x : E2) (z : ℝ) : ‖spacePoint x z‖ = √(‖x‖ ^ 2 + z ^ 2) := by
  rw [← norm_sq_spacePoint, Real.sqrt_sq (norm_nonneg _)]

/-- The embedding of the screen is an isometry. -/
theorem norm_planePoint (y : E2) : ‖planePoint y‖ = ‖y‖ := by
  have h : ‖planePoint y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [norm_sq_eq_three, norm_sq_eq_two]
    simp [planePoint]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- `(x, z) − (y, 0) = (x − y, z)`. -/
theorem spacePoint_sub_planePoint (x y : E2) (z : ℝ) :
    spacePoint x z - planePoint y = spacePoint (x - y) z := by
  ext i
  fin_cases i <;> simp [spacePoint, planePoint]

/-- `c(x, z) = (cx, cz)`. -/
theorem spacePoint_smul (c : ℝ) (x : E2) (z : ℝ) :
    spacePoint (c • x) (c * z) = c • spacePoint x z := by
  ext i
  fin_cases i <;> simp [spacePoint]

/-- The embedding of the screen is continuous. -/
theorem continuous_planePoint : Continuous planePoint := by
  unfold planePoint
  fun_prop

/-- The half-space `z > 0` is open. -/
theorem isOpen_upperHalfSpace : IsOpen upperHalfSpace :=
  isOpen_lt continuous_const (by fun_prop)

/-- `⟨p, (y, 0)⟩ = p₁y₁ + p₂y₂`. -/
theorem inner_planePoint (p : E3) (y : E2) :
    ⟪p, planePoint y⟫_ℝ = p 0 * y 0 + p 1 * y 1 := by
  simp [planePoint, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

/-- A point of the closed ball of radius `p_z/2` about `p` lies at a height of at least
`p_z/2`. -/
theorem half_le_of_mem_closedBall {p q : E3} (hq : q ∈ closedBall p (p 2 / 2)) :
    p 2 / 2 ≤ q 2 := by
  have h1 : |q 2 - p 2| ≤ ‖q - p‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (q - p) 2
  have h2 : ‖q - p‖ ≤ p 2 / 2 := by rwa [mem_closedBall, dist_eq_norm] at hq
  have := neg_abs_le (q 2 - p 2)
  linarith

/-- A point of `z > 0` is never a point of the screen. -/
theorem sub_planePoint_ne_zero {p : E3} (hp : 0 < p 2) (y : E2) : p - planePoint y ≠ 0 := by
  intro h
  have := congrArg (fun q : E3 => q 2) h
  simp only [sub_planePoint_apply_two, PiLp.zero_apply] at this
  linarith

/-! ### The kernels -/

/-- The radial profile `ψ_k(R) = e^{ikR}(1 − ikR)/(2πR³)` of the Rayleigh–Sommerfeld kernel. -/
def kernelProfile (k R : ℝ) : ℂ := cexp (I * k * R) * (1 - I * k * R) / (2 * π * R ^ 3)

/-- The slope `χ_k(R) = ψ_k′(R)/R = e^{ikR}(k²R² + 3ikR − 3)/(2πR⁵)` of the profile. -/
def kernelSlope (k R : ℝ) : ℂ :=
  cexp (I * k * R) * (k ^ 2 * R ^ 2 + 3 * I * k * R - 3) / (2 * π * R ^ 5)

/-- The derivative `χ_k′(R) = e^{ikR}(ik³R³ − 6k²R² − 15ikR + 15)/(2πR⁶)` of the slope. -/
def kernelSlopeDeriv (k R : ℝ) : ℂ :=
  cexp (I * k * R) * (I * k ^ 3 * R ^ 3 - 6 * k ^ 2 * R ^ 2 - 15 * I * k * R + 15) /
    (2 * π * R ^ 6)

/-- The outgoing spherical wave `G_k(q) = e^{ik|q|}/(4π|q|)`. -/
def sphericalWave (k : ℝ) (q : E3) : ℂ := cexp (I * k * ‖q‖) / (4 * π * ‖q‖)

/-- **The Rayleigh–Sommerfeld kernel** `−2∂_z G_k(q) = q_z e^{ik|q|}(1 − ik|q|)/(2π|q|³)`. -/
def rayleighKernel (k : ℝ) (q : E3) : ℂ := q 2 * kernelProfile k ‖q‖

/-- The derivative of the phase factor `e^{ikR}` is `ik e^{ikR}`. -/
theorem hasDerivAt_cexp_I_mul (k R : ℝ) :
    HasDerivAt (fun R : ℝ => cexp (I * k * R)) (cexp (I * k * R) * (I * k)) R := by
  have h : HasDerivAt (fun R : ℝ => I * k * (R : ℂ)) (I * k * 1) R :=
    (hasDerivAt_id R).ofReal_comp.const_mul (I * k)
  simpa using h.cexp

/-- The phase factor `e^{ikR}` has the modulus one. -/
theorem norm_cexp_I_mul (k R : ℝ) : ‖cexp (I * k * R)‖ = 1 := by
  rw [show I * (k : ℂ) * (R : ℂ) = I * ((k * R : ℝ) : ℂ) by push_cast; ring]
  exact Complex.norm_exp_I_mul_ofReal _

/-- The profile has the derivative `R χ_k(R)`. -/
theorem hasDerivAt_kernelProfile (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (kernelProfile k) (R * kernelSlope k R) R := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have h1 : HasDerivAt (fun R : ℝ => (1 : ℂ) - I * k * R) (-(I * k)) R := by
    simpa using ((hasDerivAt_id R).ofReal_comp.const_mul (I * k)).const_sub 1
  have h2 : HasDerivAt (fun R : ℝ => (2 * π * (R : ℂ) ^ 3))
      (2 * (π : ℂ) * (3 * (R : ℂ) ^ 2)) R := by
    have := ((hasDerivAt_id R).ofReal_comp.pow 3).const_mul (2 * (π : ℂ))
    simpa using this
  have h := ((hasDerivAt_cexp_I_mul k R).fun_mul h1).fun_div h2 (by simp [hR', Real.pi_ne_zero])
  unfold kernelProfile
  refine h.congr_deriv ?_
  unfold kernelSlope
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- The slope has the derivative `χ_k′`. -/
theorem hasDerivAt_kernelSlope (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (kernelSlope k) (kernelSlopeDeriv k R) R := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have h1 : HasDerivAt (fun R : ℝ => (k : ℂ) ^ 2 * (R : ℂ) ^ 2 + 3 * I * k * R - 3)
      (k ^ 2 * (2 * R) + 3 * I * k) R := by
    have ha := ((hasDerivAt_id R).ofReal_comp.pow 2).const_mul ((k : ℂ) ^ 2)
    have hb := (hasDerivAt_id R).ofReal_comp.const_mul (3 * I * k)
    simpa using (ha.add hb).sub_const 3
  have h2 : HasDerivAt (fun R : ℝ => (2 * π * (R : ℂ) ^ 5))
      (2 * (π : ℂ) * (5 * (R : ℂ) ^ 4)) R := by
    have := ((hasDerivAt_id R).ofReal_comp.pow 5).const_mul (2 * (π : ℂ))
    simpa using this
  have h := ((hasDerivAt_cexp_I_mul k R).fun_mul h1).fun_div h2 (by simp [hR', Real.pi_ne_zero])
  unfold kernelSlope
  refine h.congr_deriv ?_
  unfold kernelSlopeDeriv
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The radial equation of the kernel, `5χ_k + Rχ_k′ + k²ψ_k = 0`: with `χ_k = ψ_k′/R` it is
`ψ_k″ + 4ψ_k′/R + k²ψ_k = 0`. -/
theorem kernelSlope_radial (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    5 * kernelSlope k R + R * kernelSlopeDeriv k R + k ^ 2 * kernelProfile k R = 0 := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold kernelSlope kernelSlopeDeriv kernelProfile
  field_simp
  ring

/-- The slope splits as `χ_k = ikψ_k/R + e^{ikR}(2ikR − 3)/(2πR⁵)`. -/
theorem kernelSlope_eq (k : ℝ) {R : ℝ} (hR : R ≠ 0) :
    kernelSlope k R = I * k * kernelProfile k R / R +
      cexp (I * k * R) * (2 * I * k * R - 3) / (2 * π * R ^ 5) := by
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold kernelSlope kernelProfile
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-! ### The derivatives of the kernel -/

/-- The derivative of the norm away from the origin, `D|q| = ⟨q, ·⟩/|q|`. -/
theorem hasFDerivAt_norm_of_ne_zero {q : E3} (hq : q ≠ 0) :
    HasFDerivAt (fun y : E3 => ‖y‖) (‖q‖⁻¹ • innerSL ℝ q) q := by
  have hq' : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have h := (hasStrictFDerivAt_norm_sq q).hasFDerivAt.sqrt (by positivity)
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  refine h.congr_fderiv ?_
  ext v
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, two_smul, add_apply]
  field_simp
  ring

/-- The height `q ↦ q_z`, as a complex function. -/
theorem hasFDerivAt_height (q : E3) :
    HasFDerivAt (fun y : E3 => ((y 2 : ℝ) : ℂ))
      (ofRealCLM.comp (EuclideanSpace.proj (2 : Fin 3))) q :=
  (ofRealCLM.comp (EuclideanSpace.proj (2 : Fin 3))).hasFDerivAt

/-- The derivative of a radial profile `f(|q|)` away from the origin. -/
theorem hasFDerivAt_comp_norm {f : ℝ → ℂ} {f' : ℂ} {q : E3} (hq : q ≠ 0)
    (hf : HasDerivAt f f' ‖q‖) :
    HasFDerivAt (fun y : E3 => f ‖y‖) ((‖q‖⁻¹ • innerSL ℝ q).smulRight f') q := by
  refine (hf.hasFDerivAt.comp q (hasFDerivAt_norm_of_ne_zero hq)).congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  simp

/-- The derivative of the kernel, `D K(q) v = v_z ψ_k(|q|) + q_z χ_k(|q|) ⟨q, v⟩`. -/
theorem hasFDerivAt_rayleighKernel (k : ℝ) {q : E3} (hq : q ≠ 0) :
    HasFDerivAt (rayleighKernel k)
      (((q 2 : ℝ) : ℂ) • ((‖q‖⁻¹ • innerSL ℝ q).smulRight (‖q‖ * kernelSlope k ‖q‖)) +
        kernelProfile k ‖q‖ • ofRealCLM.comp (EuclideanSpace.proj (2 : Fin 3))) q := by
  have hR : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  exact (hasFDerivAt_height q).mul
    (hasFDerivAt_comp_norm hq (hasDerivAt_kernelProfile k hR))

/-- The derivative of the kernel along `v`, `DK(q)v = v_z ψ_k(|q|) + q_z χ_k(|q|) ⟨q, v⟩`. -/
theorem fderiv_rayleighKernel_apply (k : ℝ) {q : E3} (hq : q ≠ 0) (v : E3) :
    fderiv ℝ (rayleighKernel k) q v =
      v 2 * kernelProfile k ‖q‖ + q 2 * kernelSlope k ‖q‖ * ⟪q, v⟫_ℝ := by
  have hR : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hq
  rw [(hasFDerivAt_rayleighKernel k hq).fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, ofRealCLM_apply, smul_eq_mul,
    Complex.real_smul]
  push_cast
  field_simp
  ring

/-- The kernel is smooth away from the origin. -/
theorem contDiffAt_rayleighKernel (k : ℝ) {q : E3} (hq : q ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (rayleighKernel k) q := by
  have hR : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hq
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn : ContDiffAt ℝ n (fun y : E3 => ((‖y‖ : ℝ) : ℂ)) q :=
    ofRealCLM.contDiff.contDiffAt.comp q (contDiffAt_norm ℝ hq)
  have hz : ContDiffAt ℝ n (fun y : E3 => ((y 2 : ℝ) : ℂ)) q :=
    (ofRealCLM.comp (EuclideanSpace.proj (2 : Fin 3))).contDiff.contDiffAt
  have he : ContDiffAt ℝ n (fun y : E3 => cexp (I * k * ‖y‖)) q :=
    (contDiffAt_const.mul hn).cexp
  have hd : ContDiffAt ℝ n (fun y : E3 => (2 * π * (‖y‖ : ℂ) ^ 3)⁻¹) q :=
    (contDiffAt_const.mul (hn.pow 3)).inv (by simp [hR, hpi])
  have h := hz.mul ((he.mul ((contDiffAt_const (c := (1 : ℂ))).sub
    ((contDiffAt_const (c := I * k)).mul hn))).mul hd)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  simp [rayleighKernel, kernelProfile, div_eq_mul_inv, mul_assoc]

/-- The kernel is smooth on the half-space `z > 0`. -/
theorem contDiffOn_rayleighKernel (k : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (rayleighKernel k) upperHalfSpace := by
  intro q hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp [upperHalfSpace] at hq
  exact (contDiffAt_rayleighKernel k hq0).contDiffWithinAt

/-- The kernel is `−2∂_z G_k`. -/
theorem rayleighKernel_eq_fderiv_sphericalWave (k : ℝ) {q : E3} (hq : q ≠ 0) :
    rayleighKernel k q = -2 * fderiv ℝ (sphericalWave k) q (EuclideanSpace.single 2 1) := by
  have hR : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hR' : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast hR
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : HasDerivAt (fun R : ℝ => (4 * π * (R : ℂ))) (4 * π) ‖q‖ := by
    simpa using (hasDerivAt_id ‖q‖).ofReal_comp.const_mul (4 * (π : ℂ))
  have hG : HasDerivAt (fun R : ℝ => cexp (I * k * R) / (4 * π * R))
      ((cexp (I * k * ‖q‖) * (I * k) * (4 * π * ‖q‖) - cexp (I * k * ‖q‖) * (4 * π)) /
        (4 * π * ‖q‖) ^ 2) ‖q‖ :=
    (hasDerivAt_cexp_I_mul k ‖q‖).fun_div h1 (by simp [hR', hpi])
  have hS : sphericalWave k = fun y : E3 => cexp (I * k * ‖y‖) / (4 * π * ‖y‖) := rfl
  rw [hS, (hasFDerivAt_comp_norm hq hG).fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, innerSL_apply_apply,
    EuclideanSpace.inner_single_right, smul_eq_mul, Complex.real_smul, conj_trivial]
  unfold rayleighKernel kernelProfile
  push_cast
  field_simp
  ring

/-! ### The Helmholtz equation of the kernel -/

/-- For a function that is `C²` at `x`, Mathlib's Laplacian is the sum `Σᵢ ∂ᵢ∂ᵢ f` in the
co-ordinates. -/
theorem laplacian_eq_sum_fderiv {f : E3 → ℂ} {x : E3} (hf : ContDiffAt ℝ 2 f x) :
    Δ f x = ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
    (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp only [iteratedFDeriv_two_apply, EuclideanSpace.basisFun_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

/-- The second derivative of the kernel along `v`,
`∂ᵥ∂ᵥK(q) = 2v_z χ_k ⟨q, v⟩ + q_z χ_k′ ⟨q, v⟩²/|q| + q_z χ_k |v|²`. -/
theorem fderiv_fderiv_rayleighKernel (k : ℝ) {q : E3} (hq : q ≠ 0) (v : E3) :
    fderiv ℝ (fun y => fderiv ℝ (rayleighKernel k) y v) q v =
      2 * v 2 * kernelSlope k ‖q‖ * ⟪q, v⟫_ℝ +
        q 2 * kernelSlopeDeriv k ‖q‖ / ‖q‖ * ⟪q, v⟫_ℝ ^ 2 +
        q 2 * kernelSlope k ‖q‖ * ⟪v, v⟫_ℝ := by
  have hR : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hR' : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast hR
  have hev : (fun y => fderiv ℝ (rayleighKernel k) y v) =ᶠ[𝓝 q] fun y =>
      (v 2 : ℂ) * kernelProfile k ‖y‖ + (y 2 : ℂ) * kernelSlope k ‖y‖ * (⟪y, v⟫_ℝ : ℂ) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.mpr hq)] with y hy
    exact fderiv_rayleighKernel_apply k (mem_compl_singleton_iff.mp hy) v
  have hin : HasFDerivAt (fun y : E3 => ((⟪y, v⟫_ℝ : ℝ) : ℂ))
      (ofRealCLM.comp (innerSL ℝ v)) q := by
    refine (ofRealCLM.comp (innerSL ℝ v)).hasFDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall fun y => ?_)
    simp [real_inner_comm]
  have h := ((hasFDerivAt_comp_norm hq (hasDerivAt_kernelProfile k hR)).const_mul
    (v 2 : ℂ)).fun_add (((hasFDerivAt_height q).fun_mul
      (hasFDerivAt_comp_norm hq (hasDerivAt_kernelSlope k hR))).fun_mul hin)
  rw [hev.fderiv_eq, h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, ofRealCLM_apply, smul_eq_mul,
    Complex.real_smul]
  push_cast
  field_simp
  ring

/-- **The kernel solves the Helmholtz equation** away from its pole, in the co-ordinates:
`Σᵢ ∂ᵢ∂ᵢK + k²K = 0`. -/
theorem sum_fderiv_fderiv_rayleighKernel (k : ℝ) {q : E3} (hq : q ≠ 0) :
    ∑ i, fderiv ℝ (fun y => fderiv ℝ (rayleighKernel k) y (EuclideanSpace.single i 1)) q
      (EuclideanSpace.single i 1) = -(k ^ 2) * rayleighKernel k q := by
  have hR : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  have hR' : (‖q‖ : ℂ) ≠ 0 := by exact_mod_cast hR
  have hRinv : (‖q‖ : ℂ) * (‖q‖ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hR'
  have hsum : ((q 0 : ℂ) ^ 2 + (q 1 : ℂ) ^ 2 + (q 2 : ℂ) ^ 2) = (‖q‖ : ℂ) ^ 2 := by
    exact_mod_cast (norm_sq_eq_three q).symm
  have hrad := kernelSlope_radial k hR
  simp only [fderiv_fderiv_rayleighKernel k hq, Fin.sum_univ_three,
    EuclideanSpace.inner_single_right, conj_trivial]
  simp [rayleighKernel]
  linear_combination (q 2 : ℂ) * hrad + (q 2 * kernelSlopeDeriv k ‖q‖ / ‖q‖ : ℂ) * hsum +
    (q 2 * kernelSlopeDeriv k ‖q‖ * ‖q‖ : ℂ) * hRinv

/-- **The Helmholtz equation of the kernel**: `ΔK + k²K = 0` away from the pole. -/
theorem helmholtz_rayleighKernel (k : ℝ) {q : E3} (hq : q ≠ 0) :
    Δ (rayleighKernel k) q + k ^ 2 * rayleighKernel k q = 0 := by
  rw [laplacian_eq_sum_fderiv (contDiffAt_rayleighKernel k hq),
    sum_fderiv_fderiv_rayleighKernel k hq]
  ring

/-! ### Integrals over the aperture -/

section PlaneIntegral

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- The integral `∫ u₀(y) g(p − (y, 0)) dy` of a kernel `g` over the aperture plane. -/
def planeIntegral (u₀ : E2 → ℂ) (g : E3 → V) (p : E3) : V :=
  ∫ y, u₀ y • g (p - planePoint y)

/-- For `z > 0` the integrand of the aperture integral is integrable. -/
theorem integrable_planeIntegrand {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀)
    {g : E3 → V} (hg : ContinuousOn g upperHalfSpace) {p : E3} (hp : 0 < p 2) :
    Integrable (fun y => u₀ y • g (p - planePoint y)) := by
  have hcont : Continuous fun y => g (p - planePoint y) :=
    hg.comp_continuous (continuous_const.sub continuous_planePoint)
      (fun y => by simpa [upperHalfSpace] using hp)
  exact (hc.smul hcont).integrable_of_hasCompactSupport hs.smul_right

/-- **Differentiation under the integral**: for a kernel `g` that is `C¹` on `z > 0`, the
integral over the aperture has the derivative `∫ u₀(y) Dg(p − (y, 0)) dy` at a point of
`z > 0`. -/
theorem hasFDerivAt_planeIntegral {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) {g : E3 → V} (hg : ContDiffOn ℝ 1 g upperHalfSpace) {p : E3}
    (hp : 0 < p 2) :
    HasFDerivAt (planeIntegral u₀ g) (planeIntegral u₀ (fderiv ℝ g) p) p := by
  have hU := isOpen_upperHalfSpace
  have hgc : ContinuousOn g upperHalfSpace := hg.continuousOn
  have hg'c : ContinuousOn (fderiv ℝ g) upperHalfSpace :=
    hg.continuousOn_fderiv_of_isOpen hU le_rfl
  have hp2 : 0 < p 2 / 2 := by linarith
  have hmem : ∀ q ∈ closedBall p (p 2 / 2), ∀ y : E2, q - planePoint y ∈ upperHalfSpace := by
    intro q hq y
    show 0 < (q - planePoint y) 2
    rw [sub_planePoint_apply_two]
    linarith [half_le_of_mem_closedBall hq]
  have hball : ball p (p 2 / 2) ⊆ closedBall p (p 2 / 2) := ball_subset_closedBall
  have hpos : ∀ q ∈ ball p (p 2 / 2), 0 < q 2 := fun q hq => by
    linarith [half_le_of_mem_closedBall (hball hq)]
  set C := (fun x : E3 × E2 => x.1 - planePoint x.2) '' (closedBall p (p 2 / 2) ×ˢ tsupport u₀)
  have hC : IsCompact C :=
    ((isCompact_closedBall p _).prod hs).image
      (continuous_fst.sub (continuous_planePoint.comp continuous_snd))
  have hCU : C ⊆ upperHalfSpace := by
    rintro _ ⟨⟨q, y⟩, ⟨hq, -⟩, rfl⟩
    exact hmem q hq y
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hg'c.mono hCU)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun y => ‖u₀ y‖ * M)
    (F' := fun q y => u₀ y • fderiv ℝ g (q - planePoint y))
    (ball_mem_nhds p hp2) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [ball_mem_nhds p hp2] with q hq
    exact (integrable_planeIntegrand hc hs hgc (hpos q hq)).aestronglyMeasurable
  · exact integrable_planeIntegrand hc hs hgc hp
  · exact (integrable_planeIntegrand hc hs hg'c hp).aestronglyMeasurable
  · refine Eventually.of_forall fun y q hq => ?_
    by_cases hy : y ∈ tsupport u₀
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hM _ ⟨⟨q, y⟩, ⟨hball hq, hy⟩, rfl⟩) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hc.integrable_of_hasCompactSupport hs).norm.mul_const M
  · refine Eventually.of_forall fun y q hq => ?_
    have hqU := hmem q (hball hq) y
    have hd : DifferentiableAt ℝ g (q - planePoint y) :=
      (hg.differentiableOn one_ne_zero _ hqU).differentiableAt (hU.mem_nhds hqU)
    have h := (hd.hasFDerivAt.comp q ((hasFDerivAt_id q).sub_const (planePoint y))).const_smul
      (u₀ y)
    simp only [ContinuousLinearMap.comp_id] at h
    exact h

/-- The derivative of the integral over the aperture is the integral of the derivative. -/
theorem fderiv_planeIntegral {u₀ : E2 → ℂ} (hc : Continuous u₀) (hs : HasCompactSupport u₀)
    {g : E3 → V} (hg : ContDiffOn ℝ 1 g upperHalfSpace) {p : E3} (hp : 0 < p 2) :
    fderiv ℝ (planeIntegral u₀ g) p = planeIntegral u₀ (fderiv ℝ g) p :=
  (hasFDerivAt_planeIntegral hc hs hg hp).fderiv

/-- The derivative along `v` of the integral is the integral of the derivative along `v`. -/
theorem fderiv_planeIntegral_apply {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) {g : E3 → V} (hg : ContDiffOn ℝ 1 g upperHalfSpace) {p : E3}
    (hp : 0 < p 2) (v : E3) :
    fderiv ℝ (planeIntegral u₀ g) p v = planeIntegral u₀ (fun q => fderiv ℝ g q v) p := by
  rw [fderiv_planeIntegral hc hs hg hp]
  unfold planeIntegral
  rw [ContinuousLinearMap.integral_apply (integrable_planeIntegrand hc hs
    (hg.continuousOn_fderiv_of_isOpen isOpen_upperHalfSpace le_rfl) hp)]
  simp

/-- A kernel of class `Cⁿ⁺¹` on `z > 0` gives an integral of class `Cⁿ`. -/
theorem contDiffOn_planeIntegral_of_succ {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℂ W] {g : E3 → W},
      ContDiffOn ℝ (n + 1) g upperHalfSpace →
        ContDiffOn ℝ n (planeIntegral u₀ g) upperHalfSpace := by
  induction n with
  | zero =>
    intro W _ _ g hg
    have hg1 : ContDiffOn ℝ 1 g upperHalfSpace := by simpa using hg
    refine contDiffOn_zero.mpr fun p hp => ?_
    exact (hasFDerivAt_planeIntegral hc hs hg1 hp).continuousAt.continuousWithinAt
  | succ n ih =>
    intro W _ _ g hg
    have hU := isOpen_upperHalfSpace
    have hg1 : ContDiffOn ℝ 1 g upperHalfSpace := hg.of_le (by norm_cast; omega)
    have hg' : ContDiffOn ℝ (n + 1) (fderiv ℝ g) upperHalfSpace :=
      hg.fderiv_of_isOpen hU (by norm_cast)
    have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun p hp => (hasFDerivAt_planeIntegral hc hs hg1 hp).differentiableAt
      |>.differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    exact (ih hg').congr fun p hp => fderiv_planeIntegral hc hs hg1 hp

/-- **The integral over the aperture of a smooth kernel is smooth** on `z > 0`. -/
theorem contDiffOn_planeIntegral {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) {g : E3 → V} (hg : ContDiffOn ℝ ∞ g upperHalfSpace) :
    ContDiffOn ℝ ∞ (planeIntegral u₀ g) upperHalfSpace :=
  contDiffOn_infty.mpr fun n =>
    contDiffOn_planeIntegral_of_succ hc hs n (hg.of_le (by simp))

end PlaneIntegral

/-! ### The aperture field -/

/-- **The Rayleigh–Sommerfeld integral** `u(p) = ∫ u₀(y) (−2∂_z G_k)(p − (y, 0)) dy`: the
field behind the screen with the values `u₀` in the plane `z = 0`. -/
def apertureField (k : ℝ) (u₀ : E2 → ℂ) (p : E3) : ℂ :=
  ∫ y, u₀ y * rayleighKernel k (p - planePoint y)

/-- The aperture field is the integral over the aperture of the kernel. -/
theorem apertureField_eq_planeIntegral (k : ℝ) (u₀ : E2 → ℂ) :
    apertureField k u₀ = planeIntegral u₀ (rayleighKernel k) := rfl

/-- **The aperture field is smooth** on the half-space `z > 0`. -/
theorem contDiffOn_apertureField (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) : ContDiffOn ℝ ∞ (apertureField k u₀) upperHalfSpace :=
  contDiffOn_planeIntegral hc hs (contDiffOn_rayleighKernel k)

/-- **The Helmholtz equation**: the aperture field satisfies `Δu + k²u = 0` on `z > 0`. -/
theorem helmholtz_apertureField (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) {p : E3} (hp : 0 < p 2) :
    Δ (apertureField k u₀) p + k ^ 2 * apertureField k u₀ p = 0 := by
  have hU := isOpen_upperHalfSpace
  have hK : ContDiffOn ℝ ∞ (rayleighKernel k) upperHalfSpace := contDiffOn_rayleighKernel k
  have hu : ContDiffAt ℝ 2 (apertureField k u₀) p :=
    ((contDiffOn_apertureField k hc hs).contDiffAt (hU.mem_nhds hp)).of_le (by simp)
  have hK1 : ContDiffOn ℝ 1 (rayleighKernel k) upperHalfSpace :=
    hK.of_le (by simp)
  have hKv (v : E3) : ContDiffOn ℝ ∞ (fun q => fderiv ℝ (rayleighKernel k) q v)
      upperHalfSpace :=
    (hK.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply contDiffOn_const
  have hKvv (v : E3) : ContinuousOn
      (fun q => fderiv ℝ (fun y => fderiv ℝ (rayleighKernel k) y v) q v) upperHalfSpace :=
    (((hKv v).fderiv_of_isOpen (m := ∞) hU (by simp)).clm_apply
      contDiffOn_const).continuousOn
  have hstep (v : E3) : fderiv ℝ (fun y => fderiv ℝ (apertureField k u₀) y v) p v =
      planeIntegral u₀ (fun q => fderiv ℝ (fun y => fderiv ℝ (rayleighKernel k) y v) q v) p := by
    have hev : (fun y => fderiv ℝ (apertureField k u₀) y v) =ᶠ[𝓝 p]
        planeIntegral u₀ (fun q => fderiv ℝ (rayleighKernel k) q v) := by
      filter_upwards [hU.mem_nhds hp] with y hy
      exact fderiv_planeIntegral_apply hc hs hK1 hy v
    rw [hev.fderiv_eq]
    exact fderiv_planeIntegral_apply hc hs ((hKv v).of_le (by simp)) hp v
  have hsum : ∑ i : Fin 3, planeIntegral u₀ (fun q => fderiv ℝ
      (fun y => fderiv ℝ (rayleighKernel k) y (EuclideanSpace.single i 1)) q
        (EuclideanSpace.single i 1)) p =
      planeIntegral u₀ (fun q => -(k ^ 2 : ℂ) * rayleighKernel k q) p := by
    unfold planeIntegral
    rw [← integral_finsetSum _ fun i _ => integrable_planeIntegrand hc hs (hKvv _) hp]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [← Finset.smul_sum]
    rw [sum_fderiv_fderiv_rayleighKernel k (sub_planePoint_ne_zero hp y)]
  have hlin : planeIntegral u₀ (fun q => -(k ^ 2 : ℂ) * rayleighKernel k q) p =
      -(k ^ 2 : ℂ) * apertureField k u₀ p := by
    unfold planeIntegral apertureField
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [smul_eq_mul]
    ring
  rw [laplacian_eq_sum_fderiv hu]
  simp only [hstep]
  rw [hsum, hlin]
  ring

/-! ### The boundary values -/

/-- The Poisson kernel `P_z(w) = z/(2π(|w|² + z²)^{3/2})` of the half-space. -/
def poissonKernel (z : ℝ) (w : E2) : ℝ := z / (2 * π * √(‖w‖ ^ 2 + z ^ 2) ^ 3)

/-- The kernel is the Poisson kernel times `e^{ikR}(1 − ikR)`, with `R = (|w|² + z²)^{1/2}`. -/
theorem rayleighKernel_spacePoint (k : ℝ) (w : E2) (z : ℝ) :
    rayleighKernel k (spacePoint w z) = poissonKernel z w *
      (cexp (I * k * √(‖w‖ ^ 2 + z ^ 2)) * (1 - I * k * √(‖w‖ ^ 2 + z ^ 2))) := by
  unfold rayleighKernel kernelProfile poissonKernel
  rw [norm_spacePoint, spacePoint_apply_two]
  push_cast
  ring

/-- The primitive `−(r² + 1)^{-1/2}` of `r(r² + 1)^{-3/2}`. -/
theorem hasDerivAt_neg_inv_sqrt (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(√(r ^ 2 + 1))⁻¹) (r * (√(r ^ 2 + 1) ^ 3)⁻¹) r := by
  have hpos : 0 < r ^ 2 + 1 := by positivity
  have hs : 0 < √(r ^ 2 + 1) := Real.sqrt_pos.mpr hpos
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + 1) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).add_const 1
  have h2 := (h1.sqrt hpos.ne').inv hs.ne'
  refine h2.neg.congr_deriv ?_
  field_simp

/-- The radial integral `∫₀^∞ r (r² + 1)^{-3/2} dr = 1`. -/
theorem integral_Ioi_poissonProfile :
    ∫ r in Ioi (0 : ℝ), r * (√(r ^ 2 + 1) ^ 3)⁻¹ = 1 := by
  have hlim : Tendsto (fun r : ℝ => -(√(r ^ 2 + 1))⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => √(r ^ 2 + 1)) atTop atTop := by
      refine Real.tendsto_sqrt_atTop.comp ?_
      exact tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop two_ne_zero)
    simpa using (tendsto_inv_atTop_zero.comp h).neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg
    (hasDerivAt_neg_inv_sqrt 0).continuousAt.continuousWithinAt
    (fun r _ => hasDerivAt_neg_inv_sqrt r)
    (fun r hr => mul_nonneg (le_of_lt hr) (by positivity)) hlim]
  simp

/-- The radial profile `r(r² + 1)^{-3/2}` is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_poissonProfile :
    IntegrableOn (fun r : ℝ => r * (√(r ^ 2 + 1) ^ 3)⁻¹) (Ioi 0) := by
  have hlim : Tendsto (fun r : ℝ => -(√(r ^ 2 + 1))⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ => √(r ^ 2 + 1)) atTop atTop := by
      refine Real.tendsto_sqrt_atTop.comp ?_
      exact tendsto_atTop_add_const_right _ 1 (tendsto_pow_atTop two_ne_zero)
    simpa using (tendsto_inv_atTop_zero.comp h).neg
  exact integrableOn_Ioi_deriv_of_nonneg (hasDerivAt_neg_inv_sqrt 0).continuousAt.continuousWithinAt
    (fun r _ => hasDerivAt_neg_inv_sqrt r)
    (fun r hr => mul_nonneg (le_of_lt hr) (by positivity)) hlim

/-- `P₁(w) = (2π)⁻¹ (|w|² + 1)^{-3/2}`. -/
theorem poissonKernel_one (w : E2) :
    poissonKernel 1 w = (2 * π)⁻¹ * (√(‖w‖ ^ 2 + 1) ^ 3)⁻¹ := by
  unfold poissonKernel
  rw [one_pow]
  field_simp

/-- The Poisson kernel is integrable on the plane. -/
theorem integrable_poissonKernel_one : Integrable (poissonKernel 1) := by
  have h : Integrable (fun w : E2 => (√(‖w‖ ^ 2 + 1) ^ 3)⁻¹) := by
    refine (integrable_fun_norm_addHaar volume (f := fun r : ℝ => (√(r ^ 2 + 1) ^ 3)⁻¹)).mpr ?_
    simpa [finrank_euclideanSpace_fin] using integrableOn_Ioi_poissonProfile
  rw [show poissonKernel 1 = fun w : E2 => (2 * π)⁻¹ * (√(‖w‖ ^ 2 + 1) ^ 3)⁻¹ from
    funext poissonKernel_one]
  exact h.const_mul _

/-- **The Poisson kernel has the integral one**. -/
theorem integral_poissonKernel_one : ∫ w : E2, poissonKernel 1 w = 1 := by
  simp only [poissonKernel_one]
  rw [integral_const_mul]
  have h := integral_fun_norm_addHaar (volume : Measure E2)
    (fun r : ℝ => (√(r ^ 2 + 1) ^ 3)⁻¹)
  have hvol : (volume : Measure E2).real (ball 0 1) = π := by
    simp [Measure.real, ENNReal.toReal_ofReal Real.pi_pos.le]
  simp only [finrank_euclideanSpace_fin] at h
  rw [h, hvol, show (2 : ℕ) - 1 = 1 by norm_num]
  simp only [nsmul_eq_mul, smul_eq_mul, pow_one]
  rw [integral_Ioi_poissonProfile]
  field_simp
  norm_num

/-- The aperture field at the height `z > 0` in the scaled variable `w = z v`:
`u(x, z) = ∫ u₀(x − zv) e^{ikzρ}(1 − ikzρ) P₁(v) dv` with `ρ = (|v|² + 1)^{1/2}`. -/
theorem apertureField_spacePoint_eq (k : ℝ) (u₀ : E2 → ℂ) (x : E2) {z : ℝ} (hz : 0 < z) :
    apertureField k u₀ (spacePoint x z) = ∫ v : E2, u₀ (x - z • v) *
      (cexp (I * k * (z * √(‖v‖ ^ 2 + 1))) * (1 - I * k * (z * √(‖v‖ ^ 2 + 1)))) *
        (poissonKernel 1 v : ℂ) := by
  set f : E2 → ℂ := fun w => u₀ (x - w) * rayleighKernel k (spacePoint w z) with hf
  have h1 : apertureField k u₀ (spacePoint x z) = ∫ w, f w := by
    rw [← integral_sub_left_eq_self f volume x]
    unfold apertureField
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [hf, spacePoint_sub_planePoint]
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have h2 : ∫ w, f w = ∫ v : E2, (z ^ 2 : ℂ) * f (z • v) := by
    rw [integral_const_mul, Measure.integral_comp_smul volume f z, finrank_euclideanSpace_fin,
      abs_inv, abs_pow, abs_of_pos hz, Complex.real_smul]
    push_cast
    field_simp
  rw [h1, h2]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  have hn : ‖z • v‖ ^ 2 + z ^ 2 = z ^ 2 * (‖v‖ ^ 2 + 1) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  have hsq : √(‖z • v‖ ^ 2 + z ^ 2) = z * √(‖v‖ ^ 2 + 1) := by
    rw [hn, Real.sqrt_mul (sq_nonneg z), Real.sqrt_sq hz.le]
  have hρ : (√(‖v‖ ^ 2 + 1) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < ‖v‖ ^ 2 + 1)).ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [hf, rayleighKernel_spacePoint, hsq, poissonKernel]
  push_cast
  field_simp

/-- **The boundary values**: the aperture field tends to the aperture data, `u(x, z) → u₀(x)`
as `z → 0⁺`. -/
theorem tendsto_apertureField_boundary (k : ℝ) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) (x : E2) :
    Tendsto (fun z => apertureField k u₀ (spacePoint x z)) (𝓝[>] 0) (𝓝 (u₀ x)) := by
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hs
  obtain ⟨a₀, ha₀⟩ := hs.isBounded.subset_closedBall 0
  set a := max a₀ 0 with ha_def
  have ha : tsupport u₀ ⊆ closedBall 0 a :=
    ha₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have ha0 : 0 ≤ a := le_max_right _ _
  set ρ : E2 → ℝ := fun v => √(‖v‖ ^ 2 + 1) with hρ
  set H : ℝ → E2 → ℂ := fun z v => u₀ (x - z • v) *
      (cexp (I * k * (z * ρ v)) * (1 - I * k * (z * ρ v))) * (poissonKernel 1 v : ℂ) with hH
  have hHc (v : E2) : Continuous fun z => H z v := by
    simp only [hH]
    fun_prop
  have hHv (z : ℝ) : Continuous (H z) := by
    have : Continuous ρ := by
      simp only [hρ]
      fun_prop
    have hP : Continuous (poissonKernel 1) := by
      rw [show poissonKernel 1 = fun w : E2 => (2 * π)⁻¹ * (√(‖w‖ ^ 2 + 1) ^ 3)⁻¹ from
        funext poissonKernel_one]
      have : ∀ v : E2, √(‖v‖ ^ 2 + 1) ^ 3 ≠ 0 := fun v =>
        pow_ne_zero _ (Real.sqrt_pos.mpr (by positivity)).ne'
      fun_prop (disch := exact this _)
    simp only [hH]
    fun_prop
  set bound : E2 → ℝ := fun v => M * (1 + |k| * (‖x‖ + a + 1)) * poissonKernel 1 v with hb
  have hP0 (v : E2) : 0 ≤ poissonKernel 1 v := by
    rw [poissonKernel_one]
    positivity
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x)
  have hbound : ∀ᶠ z in 𝓝[>] (0 : ℝ), ∀ᵐ v ∂(volume : Measure E2), ‖H z v‖ ≤ bound v := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with z hz
    refine Eventually.of_forall fun v => ?_
    have hz0 : 0 < z := hz.1
    have hz1 : z < 1 := hz.2
    by_cases hv : u₀ (x - z • v) = 0
    · simp only [hH, hv, zero_mul, norm_zero, hb]
      have : 0 ≤ 1 + |k| * (‖x‖ + a + 1) := by positivity
      exact mul_nonneg (mul_nonneg hM0 this) (hP0 v)
    · have hxa : ‖x - z • v‖ ≤ a := by
        have := ha (subset_tsupport _ hv)
        simpa [dist_eq_norm] using this
      have hzv : z * ‖v‖ ≤ ‖x‖ + a := by
        have h1 : ‖z • v‖ ≤ ‖x‖ + ‖x - z • v‖ := by
          calc ‖z • v‖ = ‖x - (x - z • v)‖ := by rw [sub_sub_cancel]
            _ ≤ ‖x‖ + ‖x - z • v‖ := norm_sub_le _ _
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hz0] at h1
        linarith
      have hρv : ρ v ≤ ‖v‖ + 1 := by
        simp only [hρ]
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [norm_nonneg v]
      have hθ : 0 ≤ z * ρ v := by positivity
      have hθ1 : z * ρ v ≤ ‖x‖ + a + 1 := by
        have : z * ρ v ≤ z * (‖v‖ + 1) := mul_le_mul_of_nonneg_left hρv hz0.le
        nlinarith
      have he : ‖cexp (I * k * (z * ρ v))‖ = 1 := by
        rw [show I * (k : ℂ) * ((z : ℂ) * (ρ v : ℂ)) = I * ((k * (z * ρ v) : ℝ) : ℂ) by
          push_cast; ring]
        exact Complex.norm_exp_I_mul_ofReal _
      have h1 : ‖(1 : ℂ) - I * k * (z * ρ v)‖ ≤ 1 + |k| * (‖x‖ + a + 1) := by
        calc ‖(1 : ℂ) - I * k * (z * ρ v)‖ ≤ ‖(1 : ℂ)‖ + ‖I * k * (z * ρ v)‖ := norm_sub_le _ _
          _ = 1 + |k| * (z * ρ v) := by
            rw [show I * (k : ℂ) * ((z : ℂ) * (ρ v : ℂ)) = I * ((k * (z * ρ v) : ℝ) : ℂ) by
              push_cast; ring]
            rw [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg hθ]
            simp
          _ ≤ 1 + |k| * (‖x‖ + a + 1) := by gcongr
      simp only [hH, hb, norm_mul, he, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hP0 v), one_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hM _) h1 (norm_nonneg _) hM0) (hP0 v)
  have hbi : Integrable bound := integrable_poissonKernel_one.const_mul _
  have hlim : ∀ᵐ v ∂(volume : Measure E2), Tendsto (fun z => H z v) (𝓝[>] 0)
      (𝓝 (u₀ x * (poissonKernel 1 v : ℂ))) := by
    refine Eventually.of_forall fun v => ?_
    have h := ((hHc v).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [hH] using h
  have hT := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall fun z => (hHv z).aestronglyMeasurable) hbound hbi hlim
  have hval : ∫ v : E2, u₀ x * (poissonKernel 1 v : ℂ) = u₀ x := by
    rw [integral_const_mul, integral_complex_ofReal, integral_poissonKernel_one]
    simp
  rw [hval] at hT
  refine hT.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (apertureField_spacePoint_eq k u₀ x hz).symm

/-! ### The unobstructed plane wave -/

/-- The primitive of the radial kernel: with `R = (s² + z²)^{1/2}`,
`d/ds [−z e^{ikR}/(2πR)] = s z ψ_k(R)`. -/
theorem hasDerivAt_planeWavePrimitive (k : ℝ) {z : ℝ} (hz : 0 < z) (s : ℝ) :
    HasDerivAt (fun s : ℝ => -(z * cexp (I * k * √(s ^ 2 + z ^ 2)) /
        (2 * π * √(s ^ 2 + z ^ 2))))
      (s * (z * kernelProfile k √(s ^ 2 + z ^ 2))) s := by
  have hpos : 0 < s ^ 2 + z ^ 2 := by positivity
  have hR0 : 0 < √(s ^ 2 + z ^ 2) := Real.sqrt_pos.mpr hpos
  have hR' : ((√(s ^ 2 + z ^ 2) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + z ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (z ^ 2)
  have hR : HasDerivAt (fun s : ℝ => ((√(s ^ 2 + z ^ 2) : ℝ) : ℂ))
      ((2 * s / (2 * √(s ^ 2 + z ^ 2)) : ℝ) : ℂ) s :=
    (h1.sqrt hpos.ne').ofReal_comp
  have he : HasDerivAt (fun s : ℝ => cexp (I * k * √(s ^ 2 + z ^ 2)))
      (cexp (I * k * √(s ^ 2 + z ^ 2)) * (I * k * ((2 * s / (2 * √(s ^ 2 + z ^ 2)) : ℝ) : ℂ)))
      s := (hR.const_mul (I * k)).cexp
  have hd : HasDerivAt (fun s : ℝ => 2 * π * ((√(s ^ 2 + z ^ 2) : ℝ) : ℂ))
      (2 * π * ((2 * s / (2 * √(s ^ 2 + z ^ 2)) : ℝ) : ℂ)) s := hR.const_mul _
  have h := ((he.const_mul (z : ℂ)).fun_div hd (by simp [hR', hpi])).neg
  refine h.congr_deriv ?_
  unfold kernelProfile
  push_cast
  field_simp
  ring

/-- **The unobstructed plane wave**: the Rayleigh–Sommerfeld integral of the constant data `1`
over the disc of radius `L` is `e^{ikz} − z e^{ikR_L}/R_L`, with `R_L = (L² + z²)^{1/2}`. -/
theorem integral_ball_rayleighKernel (k : ℝ) {z : ℝ} (hz : 0 < z) {L : ℝ} (hL : 0 ≤ L) :
    ∫ w in ball (0 : E2) L, rayleighKernel k (spacePoint w z) =
      cexp (I * k * z) - z * cexp (I * k * √(L ^ 2 + z ^ 2)) / √(L ^ 2 + z ^ 2) := by
  set f : ℝ → ℂ := fun s => z * kernelProfile k √(s ^ 2 + z ^ 2) with hf
  have hfK (w : E2) : rayleighKernel k (spacePoint w z) = f ‖w‖ := by
    simp [hf, rayleighKernel, norm_spacePoint]
  have hfc : Continuous f := by
    have hP : Continuous fun s : ℝ => kernelProfile k √(s ^ 2 + z ^ 2) := by
      refine continuous_iff_continuousAt.mpr fun s => ?_
      have hR0 : 0 < √(s ^ 2 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
      exact ContinuousAt.comp (f := fun s : ℝ => √(s ^ 2 + z ^ 2))
        (hasDerivAt_kernelProfile k hR0.ne').continuousAt (by fun_prop)
    exact continuous_const.mul hP
  have h1 : ∫ w in ball (0 : E2) L, rayleighKernel k (spacePoint w z) =
      ∫ w : E2, (Iio L).indicator f ‖w‖ := by
    rw [← integral_indicator measurableSet_ball]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : ‖w‖ < L
    · simp [indicator_of_mem (mem_ball_zero_iff.mpr hw), indicator_of_mem (mem_Iio.mpr hw), hfK]
    · simp [indicator_of_notMem (fun h => hw (mem_ball_zero_iff.mp h)),
        indicator_of_notMem (fun h => hw (mem_Iio.mp h))]
  have h2 := integral_fun_norm_addHaar (volume : Measure E2) ((Iio L).indicator f)
  have hvol : (volume : Measure E2).real (ball 0 1) = π := by
    simp [Measure.real, ENNReal.toReal_ofReal Real.pi_pos.le]
  simp only [finrank_euclideanSpace_fin, show (2 : ℕ) - 1 = 1 by norm_num, pow_one] at h2
  have h3 : ∫ y in Ioi (0 : ℝ), y • (Iio L).indicator f y =
      ∫ y in (0 : ℝ)..L, (y : ℂ) * f y := by
    have he : (fun y : ℝ => y • (Iio L).indicator f y) =
        (Iio L).indicator fun y => (y : ℂ) * f y := by
      funext y
      by_cases hy : y < L
      · simp [indicator_of_mem (mem_Iio.mpr hy), Complex.real_smul]
      · simp [indicator_of_notMem (fun h => hy (mem_Iio.mp h))]
    rw [he, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio,
      intervalIntegral.integral_of_le hL, integral_Ioc_eq_integral_Ioo]
  have h4 : ∫ y in (0 : ℝ)..L, (y : ℂ) * f y =
      -(z * cexp (I * k * √(L ^ 2 + z ^ 2)) / (2 * π * √(L ^ 2 + z ^ 2))) -
        -(z * cexp (I * k * √(0 ^ 2 + z ^ 2)) / (2 * π * √(0 ^ 2 + z ^ 2))) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => hasDerivAt_planeWavePrimitive k hz s)
      ((continuous_ofReal.mul hfc).intervalIntegrable _ _)
  rw [h1, h2, hvol, h3, h4]
  have hz0 : √(0 ^ 2 + z ^ 2) = z := by
    rw [zero_pow two_ne_zero, zero_add, Real.sqrt_sq hz.le]
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hR' : ((√(L ^ 2 + z ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < L ^ 2 + z ^ 2)).ne'
  rw [hz0]
  simp only [nsmul_eq_mul, Complex.real_smul]
  push_cast
  field_simp
  ring

/-- The unobstructed plane wave is reproduced in the limit of large discs,
`∫_{|w| < L} K(w, z) dw → e^{ikz}`; the kernel is not integrable on the plane, so the integral
over the plane converges only in this improper sense. -/
theorem tendsto_integral_ball_rayleighKernel (k : ℝ) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun L => ∫ w in ball (0 : E2) L, rayleighKernel k (spacePoint w z)) atTop
      (𝓝 (cexp (I * k * z))) := by
  have hR : Tendsto (fun L : ℝ => √(L ^ 2 + z ^ 2)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right _ _ (tendsto_pow_atTop two_ne_zero))
  have h0 : Tendsto (fun L : ℝ => (z : ℂ) * cexp (I * k * √(L ^ 2 + z ^ 2)) /
      √(L ^ 2 + z ^ 2)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h : Tendsto (fun L : ℝ => z / √(L ^ 2 + z ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hR
    refine h.congr fun L => ?_
    have hR0 : 0 < √(L ^ 2 + z ^ 2) := Real.sqrt_pos.mpr (by positivity)
    rw [norm_div, norm_mul, norm_cexp_I_mul, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hz, abs_of_pos hR0]
  have h := (tendsto_const_nhds (x := cexp (I * k * z))).sub h0
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with L hL
  exact (integral_ball_rayleighKernel k hz hL).symm

/-! ### The radiation condition -/

/-- **The Sommerfeld radiation condition** in the half-space `z > 0`, uniformly in the
direction: `u = O(1/r)` and `r(∂_r u − iku) → 0` as `r = |p| → ∞`, where
`∂_r u = Du(p)(p/|p|)` is the radial derivative. -/
def IsRadiating (k : ℝ) (u : E3 → ℂ) : Prop :=
  (∃ C R₀ : ℝ, ∀ p : E3, 0 < p 2 → R₀ ≤ ‖p‖ → ‖p‖ * ‖u p‖ ≤ C) ∧
    ∀ ε > 0, ∃ R₀ : ℝ, ∀ p : E3, 0 < p 2 → R₀ ≤ ‖p‖ →
      ‖p‖ * ‖fderiv ℝ u p (‖p‖⁻¹ • p) - I * k * u p‖ ≤ ε

/-- `|e^{ia} − e^{ib}| ≤ |a − b|` for real `a`, `b`. -/
theorem norm_cexp_I_mul_sub_le (a b : ℝ) :
    ‖cexp (I * a) - cexp (I * b)‖ ≤ |a - b| := by
  have h : cexp (I * a) - cexp (I * b) = cexp (I * b) * (cexp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [h, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, ← Real.norm_eq_abs]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- `|ψ_k(R)| ≤ (1 + |k|R)/(2πR³)`. -/
theorem norm_kernelProfile_le (k : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖kernelProfile k R‖ ≤ (1 + |k| * R) / (2 * π * R ^ 3) := by
  have h1 : ‖(1 : ℂ) - I * k * R‖ ≤ 1 + |k| * R := by
    calc ‖(1 : ℂ) - I * k * R‖ ≤ ‖(1 : ℂ)‖ + ‖I * k * R‖ := norm_sub_le _ _
      _ = 1 + |k| * R := by
        rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hR]
        simp
  unfold kernelProfile
  rw [norm_div, norm_mul, norm_cexp_I_mul, one_mul,
    show (2 * π * (R : ℂ) ^ 3) = ((2 * π * R ^ 3 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  gcongr

/-- Geometry of the far zone: for `|y| ≤ a` and `2a ≤ |p|`, the distance `R = |p − (y, 0)|`
from a point of the aperture satisfies `R ≥ |p|/2`. -/
theorem half_le_norm_sub_planePoint {a : ℝ} {p : E3} {y : E2} (hy : ‖y‖ ≤ a)
    (hr : 2 * a ≤ ‖p‖) : ‖p‖ / 2 ≤ ‖p - planePoint y‖ := by
  have := norm_sub_norm_le p (planePoint y)
  rw [norm_planePoint] at this
  linarith

/-- The height is at most the norm. -/
theorem abs_apply_two_le (p : E3) : |p 2| ≤ ‖p‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le p 2

/-- The kernel at a far point: `|p| |K(p − (y, 0))| ≤ (4/|p| + 2k)/π` for `|y| ≤ a ≤ |p|/2`. -/
theorem norm_mul_rayleighKernel_le {k a : ℝ} (hk : 0 ≤ k) {p : E3} {y : E2} (hp : 0 < p 2)
    (hy : ‖y‖ ≤ a) (hr : 2 * a ≤ ‖p‖) :
    ‖p‖ * ‖rayleighKernel k (p - planePoint y)‖ ≤ (4 / ‖p‖ + 2 * k) / π := by
  set R := ‖p - planePoint y‖ with hRdef
  set r := ‖p‖ with hrdef
  have hz : p 2 ≤ r := (le_abs_self _).trans (abs_apply_two_le p)
  have hr0 : 0 < r := hp.trans_le hz
  have hRr : r / 2 ≤ R := half_le_norm_sub_planePoint hy hr
  have hR0 : 0 < R := by linarith
  have hψ := norm_kernelProfile_le k hR0
  rw [abs_of_nonneg hk] at hψ
  have hK : ‖rayleighKernel k (p - planePoint y)‖ = p 2 * ‖kernelProfile k R‖ := by
    rw [rayleighKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs, sub_planePoint_apply_two,
      abs_of_pos hp]
  rw [hK]
  calc r * (p 2 * ‖kernelProfile k R‖)
        ≤ (2 * R) * ((2 * R) * ((1 + k * R) / (2 * π * R ^ 3))) := by
        gcongr <;> linarith
    _ = 2 / (π * R) + 2 * k / π := by
        field_simp
    _ ≤ 2 / (π * (r / 2)) + 2 * k / π := by gcongr
    _ = (4 / r + 2 * k) / π := by
        field_simp
        ring

/-- **The radiation condition of the kernel**: for `|y| ≤ a ≤ |p|/2`,
`|DK(q)p − ik|p| K(q)| ≤ (4(7 + 2ka)/|p|² + 2k(5 + 2ka)/|p|)/π` with `q = p − (y, 0)`; the
leading terms `ikψ ⟨q, p⟩/R` and `ik|p|ψ` cancel up to `ikψ(⟨q, p⟩/R − |p|) = O(ka)`. -/
theorem norm_radial_rayleighKernel_le {k a : ℝ} (hk : 0 ≤ k) {p : E3} {y : E2} (hp : 0 < p 2)
    (hy : ‖y‖ ≤ a) (hr : 2 * a ≤ ‖p‖) :
    ‖fderiv ℝ (rayleighKernel k) (p - planePoint y) p -
        I * k * ‖p‖ * rayleighKernel k (p - planePoint y)‖ ≤
      (4 * (7 + 2 * k * a) / ‖p‖ ^ 2 + 2 * k * (5 + 2 * k * a) / ‖p‖) / π := by
  have hq : p - planePoint y ≠ 0 := sub_planePoint_ne_zero hp y
  set q := p - planePoint y with hqdef
  set R := ‖q‖ with hRdef
  set r := ‖p‖ with hrdef
  set c := ⟪q, p⟫_ℝ with hcdef
  have hz : p 2 ≤ r := (le_abs_self _).trans (abs_apply_two_le p)
  have hr0 : 0 < r := hp.trans_le hz
  have hRr : r / 2 ≤ R := half_le_norm_sub_planePoint hy hr
  have hR0 : 0 < R := by linarith
  have ha0 : 0 ≤ a := (norm_nonneg y).trans hy
  have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR0.ne'
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  -- the two geometric facts
  have hc : |c| ≤ R * r := abs_real_inner_le_norm q p
  have ht : |c / R - r| ≤ 2 * a := by
    have hpq : p = q + planePoint y := by rw [hqdef]; abel
    have hc' : c = R ^ 2 + ⟪q, planePoint y⟫_ℝ := by
      rw [hcdef, hpq, inner_add_right, real_inner_self_eq_norm_sq]
    have h1 : |R - r| ≤ a := by
      have := abs_norm_sub_norm_le q p
      rw [hqdef, sub_sub_cancel_left, norm_neg, norm_planePoint] at this
      exact this.trans hy
    have h2 : |⟪q, planePoint y⟫_ℝ / R| ≤ a := by
      rw [abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
      calc |⟪q, planePoint y⟫_ℝ| ≤ R * ‖planePoint y‖ := abs_real_inner_le_norm _ _
        _ ≤ a * R := by rw [norm_planePoint]; nlinarith
    have he : c / R - r = (R - r) + ⟪q, planePoint y⟫_ℝ / R := by
      rw [hc']
      field_simp
      ring
    rw [he]
    calc |(R - r) + ⟪q, planePoint y⟫_ℝ / R| ≤ |R - r| + |⟪q, planePoint y⟫_ℝ / R| :=
          abs_add_le _ _
      _ ≤ 2 * a := by linarith
  -- the decomposition
  set e : ℂ := cexp (I * k * R) * (2 * I * k * R - 3) / (2 * π * R ^ 5) with hedef
  have hE : fderiv ℝ (rayleighKernel k) q p - I * k * r * rayleighKernel k q =
      (p 2 : ℂ) * kernelProfile k R * (1 + I * k * ((c / R - r : ℝ) : ℂ)) +
        (p 2 : ℂ) * e * c := by
    have hq2 : q 2 = p 2 := sub_planePoint_apply_two p y
    rw [fderiv_rayleighKernel_apply k hq, rayleighKernel, hq2, ← hRdef, ← hcdef,
      kernelSlope_eq k hR0.ne', hedef]
    push_cast
    field_simp
    ring
  have hψ := norm_kernelProfile_le k hR0
  rw [abs_of_nonneg hk] at hψ
  have hA : ‖(p 2 : ℂ) * kernelProfile k R * (1 + I * k * ((c / R - r : ℝ) : ℂ))‖ ≤
      p 2 * ((1 + k * R) / (2 * π * R ^ 3)) * (1 + 2 * k * a) := by
    have h1 : ‖(1 : ℂ) + I * k * ((c / R - r : ℝ) : ℂ)‖ ≤ 1 + 2 * k * a := by
      calc ‖(1 : ℂ) + I * k * ((c / R - r : ℝ) : ℂ)‖
          ≤ ‖(1 : ℂ)‖ + ‖I * k * ((c / R - r : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = 1 + k * |c / R - r| := by
          rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk]
          simp
        _ ≤ 1 + k * (2 * a) := by gcongr
        _ = 1 + 2 * k * a := by ring
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
    gcongr
  have hB : ‖(p 2 : ℂ) * e * c‖ ≤ p 2 * ((2 * k * R + 3) / (2 * π * R ^ 5)) * (R * r) := by
    have he : ‖e‖ ≤ (2 * k * R + 3) / (2 * π * R ^ 5) := by
      have h1 : ‖2 * I * (k : ℂ) * R - 3‖ ≤ 2 * k * R + 3 := by
        calc ‖2 * I * (k : ℂ) * R - 3‖ ≤ ‖2 * I * (k : ℂ) * R‖ + ‖(3 : ℂ)‖ := norm_sub_le _ _
          _ = 2 * k * R + 3 := by
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
              Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hk,
              abs_of_pos hR0]
            simp
      rw [hedef, norm_div, norm_mul, norm_cexp_I_mul, one_mul,
        show (2 * π * (R : ℂ) ^ 5) = ((2 * π * R ^ 5 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      gcongr
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hp]
    gcongr
  rw [hE]
  have hz2 : p 2 ≤ 2 * R := by linarith
  have hr2 : r ≤ 2 * R := by linarith
  calc _ ≤ ‖(p 2 : ℂ) * kernelProfile k R * (1 + I * k * ((c / R - r : ℝ) : ℂ))‖ +
        ‖(p 2 : ℂ) * e * c‖ := norm_add_le _ _
    _ ≤ p 2 * ((1 + k * R) / (2 * π * R ^ 3)) * (1 + 2 * k * a) +
        p 2 * ((2 * k * R + 3) / (2 * π * R ^ 5)) * (R * r) := add_le_add hA hB
    _ ≤ (2 * R) * ((1 + k * R) / (2 * π * R ^ 3)) * (1 + 2 * k * a) +
        (2 * R) * ((2 * k * R + 3) / (2 * π * R ^ 5)) * (R * (2 * R)) := by gcongr
    _ = (7 + 2 * k * a) / (π * R ^ 2) + k * (5 + 2 * k * a) / (π * R) := by
        field_simp
        ring
    _ ≤ (7 + 2 * k * a) / (π * (r / 2) ^ 2) + k * (5 + 2 * k * a) / (π * (r / 2)) := by
        gcongr
    _ = (4 * (7 + 2 * k * a) / r ^ 2 + 2 * k * (5 + 2 * k * a) / r) / π := by
        field_simp
        ring

/-- The rate `r u = O(1)` of the aperture field, for data supported in `|y| ≤ a ≤ |p|/2`. -/
theorem norm_mul_apertureField_le {k a : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) (ha : ∀ y ∈ tsupport u₀, ‖y‖ ≤ a) {p : E3} (hp : 0 < p 2)
    (hr : 2 * a ≤ ‖p‖) :
    ‖p‖ * ‖apertureField k u₀ p‖ ≤ (4 / ‖p‖ + 2 * k) / π * ∫ y, ‖u₀ y‖ := by
  have hr0 : 0 < ‖p‖ := hp.trans_le ((le_abs_self _).trans (abs_apply_two_le p))
  set B := (4 / ‖p‖ + 2 * k) / π with hB
  have h : ‖apertureField k u₀ p‖ ≤ ∫ y, ‖u₀ y‖ * (B / ‖p‖) := by
    refine norm_integral_le_of_norm_le
      ((hc.integrable_of_hasCompactSupport hs).norm.mul_const _)
      (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport u₀
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [le_div_iff₀ hr0, mul_comm]
      exact norm_mul_rayleighKernel_le hk hp (ha y hy) hr
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [integral_mul_const] at h
  calc ‖p‖ * ‖apertureField k u₀ p‖ ≤ ‖p‖ * ((∫ y, ‖u₀ y‖) * (B / ‖p‖)) :=
        mul_le_mul_of_nonneg_left h hr0.le
    _ = B * ∫ y, ‖u₀ y‖ := by
        field_simp

/-- The rate `r(∂_r u − iku) = O(1/r)` of the aperture field, for data supported in
`|y| ≤ a ≤ |p|/2`. -/
theorem norm_radiation_apertureField_le {k a : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ}
    (hc : Continuous u₀) (hs : HasCompactSupport u₀) (ha : ∀ y ∈ tsupport u₀, ‖y‖ ≤ a)
    {p : E3} (hp : 0 < p 2) (hr : 2 * a ≤ ‖p‖) :
    ‖p‖ * ‖fderiv ℝ (apertureField k u₀) p (‖p‖⁻¹ • p) - I * k * apertureField k u₀ p‖ ≤
      (4 * (7 + 2 * k * a) / ‖p‖ ^ 2 + 2 * k * (5 + 2 * k * a) / ‖p‖) / π *
        ∫ y, ‖u₀ y‖ := by
  have hr0 : 0 < ‖p‖ := hp.trans_le ((le_abs_self _).trans (abs_apply_two_le p))
  have hK1 : ContDiffOn ℝ 1 (rayleighKernel k) upperHalfSpace := contDiffOn_rayleighKernel k
  have hKp : ContinuousOn (fun q => fderiv ℝ (rayleighKernel k) q p) upperHalfSpace :=
    ((contDiffOn_rayleighKernel k (n := 1)).continuousOn_fderiv_of_isOpen isOpen_upperHalfSpace
      le_rfl).clm_apply continuousOn_const
  have hKc : ContinuousOn (rayleighKernel k) upperHalfSpace := hK1.continuousOn
  have hD : fderiv ℝ (apertureField k u₀) p p =
      ∫ y, u₀ y * fderiv ℝ (rayleighKernel k) (p - planePoint y) p := by
    rw [apertureField_eq_planeIntegral, fderiv_planeIntegral_apply hc hs hK1 hp p]
    rfl
  have hsplit : ‖p‖ * ‖fderiv ℝ (apertureField k u₀) p (‖p‖⁻¹ • p) -
      I * k * apertureField k u₀ p‖ = ‖∫ y, u₀ y * (fderiv ℝ (rayleighKernel k)
        (p - planePoint y) p - I * k * ‖p‖ * rayleighKernel k (p - planePoint y))‖ := by
    have h1 : fderiv ℝ (apertureField k u₀) p (‖p‖⁻¹ • p) =
        ((‖p‖⁻¹ : ℝ) : ℂ) * fderiv ℝ (apertureField k u₀) p p := by
      rw [map_smul, Complex.real_smul]
    have h2 : ∫ y, u₀ y * (fderiv ℝ (rayleighKernel k) (p - planePoint y) p -
          I * k * ‖p‖ * rayleighKernel k (p - planePoint y)) =
        fderiv ℝ (apertureField k u₀) p p - I * k * ‖p‖ * apertureField k u₀ p := by
      rw [hD, apertureField, ← integral_const_mul, ← integral_sub]
      · refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only
        ring
      · exact integrable_planeIntegrand hc hs hKp hp
      · exact (integrable_planeIntegrand hc hs hKc hp).const_mul _
    rw [h2, h1, show ∀ X : ℂ, ‖p‖ * ‖X‖ = ‖((‖p‖ : ℝ) : ℂ) * X‖ from fun X => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]]
    congr 1
    have hp' : ((‖p‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    push_cast
    field_simp
  rw [hsplit]
  set B := (4 * (7 + 2 * k * a) / ‖p‖ ^ 2 + 2 * k * (5 + 2 * k * a) / ‖p‖) / π with hB
  have h : ‖∫ y, u₀ y * (fderiv ℝ (rayleighKernel k) (p - planePoint y) p -
      I * k * ‖p‖ * rayleighKernel k (p - planePoint y))‖ ≤ ∫ y, ‖u₀ y‖ * B := by
    refine norm_integral_le_of_norm_le
      ((hc.integrable_of_hasCompactSupport hs).norm.mul_const _)
      (Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ tsupport u₀
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_radial_rayleighKernel_le hk hp (ha y hy) hr)
        (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  rw [integral_mul_const] at h
  linarith

/-- **The aperture field satisfies the radiation condition**. -/
theorem apertureField_isRadiating {k : ℝ} (hk : 0 ≤ k) {u₀ : E2 → ℂ} (hc : Continuous u₀)
    (hs : HasCompactSupport u₀) : IsRadiating k (apertureField k u₀) := by
  obtain ⟨a₀, ha₀⟩ := hs.isBounded.subset_closedBall 0
  set a := max a₀ 0 with ha_def
  have ha0 : 0 ≤ a := le_max_right _ _
  have ha : ∀ y ∈ tsupport u₀, ‖y‖ ≤ a := fun y hy => by
    have := ha₀ hy
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set L := ∫ y, ‖u₀ y‖ with hL
  have hL0 : 0 ≤ L := integral_nonneg fun y => norm_nonneg _
  refine ⟨⟨(4 + 2 * k) / π * L, 2 * a + 1, fun p hp hr => ?_⟩, fun ε hε => ?_⟩
  · have hr1 : 1 ≤ ‖p‖ := by linarith
    refine (norm_mul_apertureField_le hk hc hs ha hp (by linarith)).trans ?_
    gcongr
    rw [div_le_iff₀ (by linarith)]
    linarith
  · have hT : Tendsto (fun r : ℝ => (4 * (7 + 2 * k * a) / r ^ 2 +
        2 * k * (5 + 2 * k * a) / r) / π * L) atTop (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => 4 * (7 + 2 * k * a) / r ^ 2) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
      have h2 : Tendsto (fun r : ℝ => 2 * k * (5 + 2 * k * a) / r) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      simpa using ((h1.add h2).div_const π).mul_const L
    obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (hT.eventually (Iic_mem_nhds hε))
    refine ⟨max R₁ (2 * a), fun p hp hr => ?_⟩
    exact (norm_radiation_apertureField_le hk hc hs ha hp ((le_max_right _ _).trans hr)).trans
      (hR₁ _ ((le_max_left _ _).trans hr))

/-! ### A smooth aperture -/

/-- A smooth aperture of compact support, `χ(y) = s(1 − |y|²)` with the smooth transition `s`
from `0` to `1`: it is `1` at the centre and vanishes for `|y| ≥ 1`. -/
def apertureBump (y : E2) : ℂ := (Real.smoothTransition (1 - ‖y‖ ^ 2) : ℂ)

/-- The smooth aperture is smooth. -/
theorem contDiff_apertureBump {n : ℕ∞} : ContDiff ℝ n apertureBump :=
  ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_norm_sq ℝ)))

/-- The smooth aperture is continuous. -/
theorem continuous_apertureBump : Continuous apertureBump :=
  (contDiff_apertureBump (n := 0)).continuous

/-- The smooth aperture is `1` at the centre. -/
theorem apertureBump_zero : apertureBump 0 = 1 := by
  simp [apertureBump]

/-- The smooth aperture vanishes for `|y| ≥ 1`. -/
theorem apertureBump_eq_zero {y : E2} (hy : 1 ≤ ‖y‖) : apertureBump y = 0 := by
  have h : 1 - ‖y‖ ^ 2 ≤ 0 := by nlinarith
  simp [apertureBump, Real.smoothTransition.zero_of_nonpos h]

/-- The smooth aperture is supported in the closed unit disc. -/
theorem tsupport_apertureBump : tsupport apertureBump ⊆ closedBall 0 1 := by
  refine closure_minimal (fun y hy => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hy (apertureBump_eq_zero (le_of_lt (not_le.mp h)))

/-- On the support of the smooth aperture `|y| ≤ 1`. -/
theorem norm_le_one_of_mem_tsupport_apertureBump {y : E2} (hy : y ∈ tsupport apertureBump) :
    ‖y‖ ≤ 1 := by
  simpa using tsupport_apertureBump hy

/-- The smooth aperture has a compact support. -/
theorem hasCompactSupport_apertureBump : HasCompactSupport apertureBump :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) fun y hy => apertureBump_eq_zero (by
    rw [mem_closedBall, dist_zero_right, not_le] at hy
    exact hy.le)

/-- The field of the smooth aperture is smooth on `z > 0`. -/
theorem contDiffOn_apertureField_apertureBump (k : ℝ) :
    ContDiffOn ℝ ∞ (apertureField k apertureBump) upperHalfSpace :=
  contDiffOn_apertureField k continuous_apertureBump hasCompactSupport_apertureBump

/-- The field of the smooth aperture solves the Helmholtz equation on `z > 0`. -/
theorem helmholtz_apertureField_apertureBump (k : ℝ) {p : E3} (hp : 0 < p 2) :
    Δ (apertureField k apertureBump) p + k ^ 2 * apertureField k apertureBump p = 0 :=
  helmholtz_apertureField k continuous_apertureBump hasCompactSupport_apertureBump hp

/-- The field of the smooth aperture tends to `1` at the centre of the aperture. -/
theorem apertureField_apertureBump_tendsto (k : ℝ) :
    Tendsto (fun z => apertureField k apertureBump (spacePoint 0 z)) (𝓝[>] 0) (𝓝 1) := by
  simpa [apertureBump_zero] using
    tendsto_apertureField_boundary k continuous_apertureBump hasCompactSupport_apertureBump 0

/-- The field of the smooth aperture satisfies the radiation condition. -/
theorem apertureField_apertureBump_isRadiating {k : ℝ} (hk : 0 ≤ k) :
    IsRadiating k (apertureField k apertureBump) :=
  apertureField_isRadiating hk continuous_apertureBump hasCompactSupport_apertureBump

/-- The rates of the radiation condition for the smooth aperture, at `|p| ≥ 2`. -/
theorem norm_radiation_apertureField_apertureBump_le {k : ℝ} (hk : 0 ≤ k) {p : E3}
    (hp : 0 < p 2) (hr : 2 ≤ ‖p‖) :
    ‖p‖ * ‖apertureField k apertureBump p‖ ≤
        (4 / ‖p‖ + 2 * k) / π * ∫ y, ‖apertureBump y‖ ∧
      ‖p‖ * ‖fderiv ℝ (apertureField k apertureBump) p (‖p‖⁻¹ • p) -
          I * k * apertureField k apertureBump p‖ ≤
        (4 * (7 + 2 * k * 1) / ‖p‖ ^ 2 + 2 * k * (5 + 2 * k * 1) / ‖p‖) / π *
          ∫ y, ‖apertureBump y‖ :=
  ⟨norm_mul_apertureField_le hk continuous_apertureBump hasCompactSupport_apertureBump
      (fun _ hy => norm_le_one_of_mem_tsupport_apertureBump hy) hp (by linarith),
    norm_radiation_apertureField_le hk continuous_apertureBump hasCompactSupport_apertureBump
      (fun _ hy => norm_le_one_of_mem_tsupport_apertureBump hy) hp (by linarith)⟩

end ProjectAinos.Electrodynamics.Diffraction
