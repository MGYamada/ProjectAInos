/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Magnetostatics
public import ProjectAinos.SmoothGeometry.Potential.Multipole
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-!
# Magnetic moments

The magnetic moment of a static current `j` of compact support is `𝔪 = ½∫ y × j(y) dy`
(Landau–Lifshitz, *The Classical Theory of Fields*, §44). Space is `EuclideanSpace ℝ (Fin 3)`,
the current is a `C¹` field `E3 → Fin 3 → ℝ` of compact support with `div j = 0`, and the cross
product is Mathlib's `⨯₃` on `Fin 3 → ℝ`.

* `integral_mul_div3`: `∫ f div j = −∫ Σₗ ∂ₗf jₗ`. With `f = yᵢ` it gives
  `integral_current_eq_zero`, `∫ jᵢ = 0`, and with `f = yᵢyₖ` it gives `integral_moment_symm`,
  `∫ (yᵢjₖ + yₖjᵢ) = 0`: the first moments `Mᵢₖ = ∫ yₖ jᵢ` (`firstMoment`) are antisymmetric.
* `cross_magneticMoment_apply`: `(𝔪 × v)ᵢ = Σₖ vₖ Mᵢₖ`, so `∫ jᵢ(y) ⟪x, y⟫ dy = (𝔪 × x)ᵢ`
  (`integral_mul_inner`).
* `norm_vectorPotential_sub_dipole_le`: **the dipole field**. Outside a ball `‖y‖ ≤ a` that
  contains the support, `‖a(x) − 𝔪 × x/(4π‖x‖³)‖ ≤ (∫ ‖j‖ ‖y‖²)/(4π(‖x‖ − a)³)`; the monopole
  term is absent because `∫ j = 0`, and the remainder is bounded with the dipole remainder
  `abs_newtonKernel_sub_dipole_le` of the kernel.
* `StationaryFlow`: the matter model, a smooth mass density `μ` of compact support carried by a
  smooth velocity `v` with `div(μv) = 0`, and its instance `rigidRotation Ω`, a radial density
  rotating rigidly with `v = Ω × x`. `magneticMoment_flow`: for the charge density
  `ρₑ = (e/m)μ` and the current `j = ρₑv`, the moment is `𝔪 = (e/2m) 𝔐` with the angular
  momentum `𝔐 = ∫ μ y × v` of the flow, the ratio `e/2m` of Landau–Lifshitz (44.5).
* `torque_uniformField`: in a uniform field `B₀` the torque on the current is
  `∫ y × (j × B₀) = 𝔪 × B₀`, and `force_uniformField`: the force `∫ j × B₀` vanishes.

Landau–Lifshitz average the current of point charges over time; the time averages and the point
particles are not used here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real Matrix
open scoped Topology ContDiff

namespace ProjectAinos.Electrodynamics.MagneticMoment

open SmoothGeometry SmoothGeometry.Potential Magnetostatics

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Integration by parts -/

/-- **Integration by parts against the divergence**: `∫ f div j = −∫ Σₗ ∂ₗf jₗ` for a `C¹`
function `f` and a `C¹` field `j` of compact support. -/
theorem integral_mul_div3 {f : E3 → ℝ} {j : E3 → Fin 3 → ℝ} (hf : ContDiff ℝ 1 f)
    (hj : ContDiff ℝ 1 j) (hcj : HasCompactSupport j) :
    ∫ x, f x * div3 j x = -∫ x, ∑ l, partial3 f l x * j x l := by
  have hjl (l : Fin 3) : ContDiff ℝ 1 fun x => j x l := contDiff_pi.mp hj l
  have hcl (l : Fin 3) := hasCompactSupport_component hcj l
  have hpf (l : Fin 3) : Continuous (partial3 f l) :=
    (contDiff_partial3 (m := 0) hf (by norm_num) l).continuous
  have hpj (l : Fin 3) : Continuous (partial3 (fun x => j x l) l) :=
    (contDiff_partial3 (m := 0) (hjl l) (by norm_num) l).continuous
  have hi1 (l : Fin 3) : Integrable fun x => partial3 f l x * j x l :=
    ((hpf l).mul (hjl l).continuous).integrable_of_hasCompactSupport (hcl l).mul_left
  have hi2 (l : Fin 3) : Integrable fun x => f x * partial3 (fun y => j y l) l x :=
    (hf.continuous.mul (hpj l)).integrable_of_hasCompactSupport
      ((hcl l).fderiv_apply (𝕜 := ℝ) _).mul_left
  have hstep (l : Fin 3) :
      ∫ x, f x * partial3 (fun y => j y l) l x = -∫ x, partial3 f l x * j x l :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hi1 l) (hi2 l)
      ((hf.continuous.mul (hjl l).continuous).integrable_of_hasCompactSupport (hcl l).mul_left)
      (fun x _ => (hf.differentiable (by norm_num)).differentiableAt)
      (fun x _ => ((hjl l).differentiable (by norm_num)).differentiableAt)
  simp only [div3, Finset.mul_sum]
  rw [integral_finsetSum _ fun l _ => hi2 l, integral_finsetSum _ fun l _ => hi1 l,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun l _ => hstep l

/-- The derivative of the co-ordinate `yᵢ` along the axis `l`. -/
theorem partial3_coord (i l : Fin 3) (x : E3) :
    partial3 (fun y : E3 => y i) l x = if i = l then 1 else 0 := by
  have h : HasFDerivAt (fun y : E3 => y i) (EuclideanSpace.proj (𝕜 := ℝ) i) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt
  simp only [partial3]
  rw [h.fderiv]
  simp [PiLp.single_apply]

/-- The co-ordinate `yᵢ` is smooth. -/
theorem contDiff_coord (i : Fin 3) : ContDiff ℝ ∞ fun y : E3 => y i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

/-- The product of a co-ordinate and a component of a continuous field of compact support is
integrable. -/
theorem integrable_coord_mul {j : E3 → Fin 3 → ℝ} (hj : Continuous j) (hcj : HasCompactSupport j)
    (k i : Fin 3) : Integrable fun y : E3 => y k * j y i :=
  ((contDiff_coord k).continuous.mul ((continuous_apply i).comp hj)).integrable_of_hasCompactSupport
    (hasCompactSupport_component hcj i).mul_left

/-! ### The moments of a conserved current -/

/-- **The integral of a conserved current vanishes**: `∫ jᵢ = 0` for a `C¹` current of compact
support with `div j = 0`. -/
theorem integral_current_eq_zero {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) (i : Fin 3) : ∫ x, j x i = 0 := by
  have h := integral_mul_div3 ((contDiff_coord i).of_le (by simp)) hj hcj
  simp only [hdiv, mul_zero, integral_zero, partial3_coord, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true] at h
  linarith

/-- The first moments `Mᵢₖ = ∫ yₖ jᵢ(y) dy` of a current. -/
def firstMoment (j : E3 → Fin 3 → ℝ) (i k : Fin 3) : ℝ :=
  ∫ y, y k * j y i

/-- **The symmetric part of the first moments vanishes**: `∫ (yᵢjₖ + yₖjᵢ) = 0` for a `C¹`
current of compact support with `div j = 0`. -/
theorem integral_moment_symm {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) (i k : Fin 3) :
    ∫ y, (y i * j y k + y k * j y i) = 0 := by
  have hf : ContDiff ℝ 1 fun y : E3 => y i * y k :=
    ((contDiff_coord i).mul (contDiff_coord k)).of_le (by simp)
  have hp (l : Fin 3) (y : E3) : partial3 (fun y : E3 => y i * y k) l y =
      (if i = l then 1 else 0) * y k + y i * (if k = l then 1 else 0) := by
    have h : HasFDerivAt (fun y : E3 => y i * y k)
        (y i • EuclideanSpace.proj (𝕜 := ℝ) k + y k • EuclideanSpace.proj (𝕜 := ℝ) i) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.mul (EuclideanSpace.proj (𝕜 := ℝ) k).hasFDerivAt
    simp only [partial3]
    rw [h.fderiv]
    simp [PiLp.single_apply]
    ring
  have hs (y : E3) : ∑ l, partial3 (fun y : E3 => y i * y k) l y * j y l =
      y i * j y k + y k * j y i := by
    simp only [hp, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have h := integral_mul_div3 hf hj hcj
  simp only [hdiv, mul_zero, integral_zero, hs] at h
  linarith

/-- **The first moments of a conserved current are antisymmetric**, `Mᵢₖ = −Mₖᵢ`. -/
theorem firstMoment_antisymm {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) (i k : Fin 3) :
    firstMoment j i k = -firstMoment j k i := by
  have h := integral_moment_symm hj hcj hdiv i k
  rw [integral_add (integrable_coord_mul hj.continuous hcj i k)
    (integrable_coord_mul hj.continuous hcj k i)] at h
  simp only [firstMoment]
  linarith

/-- The diagonal first moments of a conserved current vanish, `Mᵢᵢ = 0`. -/
theorem firstMoment_self {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) (i : Fin 3) :
    firstMoment j i i = 0 := by
  have h := firstMoment_antisymm hj hcj hdiv i i
  linarith

/-! ### The magnetic moment -/

/-- The magnetic moment `𝔪 = ½∫ y × j(y) dy` of a current. -/
def magneticMoment (j : E3 → Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (1 / 2 : ℝ) * ∫ y, (WithLp.ofLp y ⨯₃ j y) i

/-- The magnetic moment in terms of the first moments. -/
theorem magneticMoment_eq {j : E3 → Fin 3 → ℝ} (hj : Continuous j) (hcj : HasCompactSupport j) :
    magneticMoment j = ![(firstMoment j 2 1 - firstMoment j 1 2) / 2,
      (firstMoment j 0 2 - firstMoment j 2 0) / 2,
      (firstMoment j 1 0 - firstMoment j 0 1) / 2] := by
  have hi := integrable_coord_mul hj hcj
  funext i
  fin_cases i
  · simp only [magneticMoment, cross_apply]
    change (1 / 2 : ℝ) * ∫ y : E3, (y 1 * j y 2 - y 2 * j y 1) = _
    rw [integral_sub (hi 1 2) (hi 2 1)]
    simp [firstMoment]
    ring
  · simp only [magneticMoment, cross_apply]
    change (1 / 2 : ℝ) * ∫ y : E3, (y 2 * j y 0 - y 0 * j y 2) = _
    rw [integral_sub (hi 2 0) (hi 0 2)]
    simp [firstMoment]
    ring
  · simp only [magneticMoment, cross_apply]
    change (1 / 2 : ℝ) * ∫ y : E3, (y 0 * j y 1 - y 1 * j y 0) = _
    rw [integral_sub (hi 0 1) (hi 1 0)]
    simp [firstMoment]
    ring

/-- **The moment and the first moments**: for a conserved current, `(𝔪 × v)ᵢ = Σₖ vₖ Mᵢₖ`. -/
theorem cross_magneticMoment_apply {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) (v : Fin 3 → ℝ) (i : Fin 3) :
    (magneticMoment j ⨯₃ v) i = ∑ k, v k * firstMoment j i k := by
  have ha := firstMoment_antisymm hj hcj hdiv
  have hs := firstMoment_self hj hcj hdiv
  rw [magneticMoment_eq hj.continuous hcj, cross_apply, Fin.sum_univ_three]
  fin_cases i <;>
    simp [ha 1 0, ha 2 0, ha 2 1, hs] <;> ring

/-- **The dipole term**: for a conserved current, `∫ jᵢ(y) ⟪x, y⟫ dy = (𝔪 × x)ᵢ`. -/
theorem integral_mul_inner {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) (x : E3) (i : Fin 3) :
    ∫ y, j y i * inner ℝ x y = (magneticMoment j ⨯₃ WithLp.ofLp x) i := by
  have hpt (y : E3) : j y i * inner ℝ x y = ∑ k, x k * (y k * j y i) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [hpt]
  rw [integral_finsetSum _ fun k _ => (integrable_coord_mul hj.continuous hcj k i).const_mul _,
    cross_magneticMoment_apply hj hcj hdiv]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]
  rfl

/-! ### The dipole field -/

/-- The integrand `jᵢ(y) K(x − y)` of the vector potential is integrable. -/
theorem integrable_mul_newtonKernel_sub {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (x : E3) : Integrable fun y => ρ y * newtonKernel (x - y) := by
  have h := (integrable_newtonKernel_mul hcρ hρ x).comp_sub_left x
  simp only [sub_sub_cancel] at h
  exact h.congr (Eventually.of_forall fun y => mul_comm _ _)

/-- **The dipole field**: for a conserved `C¹` current of compact support in the ball `‖y‖ ≤ a`,
`‖a(x) − 𝔪 × x/(4π‖x‖³)‖ ≤ (∫ ‖j‖ ‖y‖²)/(4π(‖x‖ − a)³)` for `‖x‖ > a`. -/
theorem norm_vectorPotential_sub_dipole_le {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) {a : ℝ}
    (ha : tsupport j ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    ‖vectorPotential j x - (4 * π * ‖x‖ ^ 3)⁻¹ • (magneticMoment j ⨯₃ WithLp.ofLp x)‖ ≤
      (∫ y, ‖j y‖ * ‖y‖ ^ 2) / (4 * π * (‖x‖ - a) ^ 3) := by
  have hd : 0 < ‖x‖ - a := by linarith
  have hD : 0 < 4 * π * (‖x‖ - a) ^ 3 := by positivity
  set D := 4 * π * (‖x‖ - a) ^ 3 with hDdef
  set R : E3 → ℝ := fun y =>
    newtonKernel (x - y) - newtonKernel x - inner ℝ x y / (4 * π * ‖x‖ ^ 3) with hR
  have hjc : Continuous j := hj.continuous
  have hji (i : Fin 3) : Continuous fun y => j y i := (continuous_apply i).comp hjc
  have hinner : Continuous fun y : E3 => inner ℝ x y := continuous_const.inner continuous_id
  refine (pi_norm_le_iff_of_nonneg (div_nonneg
    (integral_nonneg fun y => by positivity) hD.le)).mpr fun i => ?_
  have hci := hasCompactSupport_component hcj i
  have hI1 := integrable_mul_newtonKernel_sub (hji i) hci x
  have hI2 : Integrable fun y => j y i * newtonKernel x :=
    ((hji i).mul continuous_const).integrable_of_hasCompactSupport hci.mul_right
  have hI3 : Integrable fun y => j y i * (inner ℝ x y / (4 * π * ‖x‖ ^ 3)) :=
    ((hji i).mul (hinner.div_const _)).integrable_of_hasCompactSupport hci.mul_right
  have hrep : vectorPotential j x i - (4 * π * ‖x‖ ^ 3)⁻¹ * (magneticMoment j ⨯₃ WithLp.ofLp x) i
      = ∫ y, j y i * R y := by
    have h1 : ∫ y, j y i * R y = (∫ y, j y i * newtonKernel (x - y)) -
        (∫ y, j y i * newtonKernel x) - ∫ y, j y i * (inner ℝ x y / (4 * π * ‖x‖ ^ 3)) := by
      have h12 : Integrable fun y => j y i * newtonKernel (x - y) - j y i * newtonKernel x :=
        hI1.sub hI2
      rw [← integral_sub hI1 hI2, ← integral_sub h12 hI3]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hR]
      ring
    have h2 : ∫ y, j y i * newtonKernel x = 0 := by
      rw [integral_mul_const, integral_current_eq_zero hj hcj hdiv i, zero_mul]
    have h3 : ∫ y, j y i * (inner ℝ x y / (4 * π * ‖x‖ ^ 3)) =
        (4 * π * ‖x‖ ^ 3)⁻¹ * (magneticMoment j ⨯₃ WithLp.ofLp x) i := by
      simp only [← mul_div_assoc]
      rw [integral_div, integral_mul_inner hj hcj hdiv]
      ring
    rw [h1, h2, h3, vectorPotential, newtonPotential_eq_integral]
    ring
  have hbound (y : E3) : ‖j y i * R y‖ ≤ ‖j y‖ * ‖y‖ ^ 2 * D⁻¹ := by
    by_cases hy : j y = 0
    · simp [hy]
    · have hya : ‖y‖ ≤ a := by simpa using ha (subset_tsupport j hy)
      have hyx : ‖y‖ < ‖x‖ := hya.trans_lt hx
      have hK := abs_newtonKernel_sub_dipole_le hyx
      have hle : ‖y‖ ^ 2 / (4 * π * (‖x‖ - ‖y‖) ^ 3) ≤ ‖y‖ ^ 2 * D⁻¹ := by
        rw [← div_eq_mul_inv]
        refine div_le_div_of_nonneg_left (by positivity) hD ?_
        have : (‖x‖ - a) ^ 3 ≤ (‖x‖ - ‖y‖) ^ 3 := pow_le_pow_left₀ hd.le (by linarith) 3
        nlinarith [pi_pos]
      rw [norm_mul, mul_assoc]
      exact mul_le_mul (norm_le_pi_norm (j y) i) (hK.trans hle) (abs_nonneg _) (norm_nonneg _)
  have hg : Integrable fun y => ‖j y‖ * ‖y‖ ^ 2 * D⁻¹ := by
    exact ((hjc.norm.mul (continuous_norm.pow 2)).mul continuous_const
      ).integrable_of_hasCompactSupport hcj.norm.mul_right.mul_right
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hrep, div_eq_mul_inv, ← integral_mul_const]
  exact norm_integral_le_of_norm_le hg (Eventually.of_forall hbound)

/-! ### The matter model -/

/-- A **stationary flow** of matter: a smooth mass density `μ` of compact support carried by a
smooth velocity `v`, with the stationary equation of continuity `div(μv) = 0`. -/
structure StationaryFlow where
  /-- The mass density `μ`. -/
  density : E3 → ℝ
  /-- The velocity `v`. -/
  velocity : E3 → Fin 3 → ℝ
  /-- The density is smooth. -/
  contDiff_density : ContDiff ℝ ∞ density
  /-- The velocity is smooth. -/
  contDiff_velocity : ContDiff ℝ ∞ velocity
  /-- The density has a compact support. -/
  hasCompactSupport_density : HasCompactSupport density
  /-- The stationary equation of continuity `div(μv) = 0`. -/
  div3_flux : ∀ x, div3 (fun y => density y • velocity y) x = 0

/-- The divergence of a constant multiple of a differentiable field. -/
theorem div3_const_smul {f : E3 → Fin 3 → ℝ} (hf : Differentiable ℝ f) (c : ℝ) (x : E3) :
    div3 (fun y => c • f y) x = c * div3 f x := by
  have hd (l : Fin 3) : DifferentiableAt ℝ (fun y => f y l) x := differentiable_pi.mp hf l x
  simp only [div3, partial3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fderiv_const_mul (hd l)]
  rfl

namespace StationaryFlow

/-- The electric current `j = ρₑ v` of the charge density `ρₑ = (e/m)μ`, for matter of one ratio
`e/m` of the charge to the mass. -/
def current (F : StationaryFlow) (e m : ℝ) : E3 → Fin 3 → ℝ :=
  fun y => (e / m * F.density y) • F.velocity y

/-- The current is smooth. -/
theorem contDiff_current (F : StationaryFlow) (e m : ℝ) : ContDiff ℝ ∞ (F.current e m) :=
  (contDiff_const.mul F.contDiff_density).smul F.contDiff_velocity

/-- The current has a compact support. -/
theorem hasCompactSupport_current (F : StationaryFlow) (e m : ℝ) :
    HasCompactSupport (F.current e m) :=
  (F.hasCompactSupport_density.mul_left (f := fun _ => e / m)).smul_right

/-- **The current is conserved**, `div j = 0`. -/
theorem div3_current (F : StationaryFlow) (e m : ℝ) (x : E3) : div3 (F.current e m) x = 0 := by
  have hflux : Differentiable ℝ fun y => F.density y • F.velocity y :=
    (F.contDiff_density.smul F.contDiff_velocity).differentiable (by simp)
  have h : F.current e m = fun y => (e / m) • (F.density y • F.velocity y) := by
    funext y
    simp only [current, smul_smul]
  rw [h, div3_const_smul hflux, F.div3_flux, mul_zero]

/-- The angular momentum `𝔐 = ∫ μ y × v` of the flow. -/
def angularMomentum (F : StationaryFlow) : Fin 3 → ℝ :=
  fun i => ∫ y, F.density y * (WithLp.ofLp y ⨯₃ F.velocity y) i

end StationaryFlow

/-- **The ratio of the magnetic moment to the angular momentum**: for matter of one ratio `e/m`,
the moment of the current `j = (e/m)μv` is `𝔪 = (e/2m) 𝔐` (Landau–Lifshitz (44.5)). -/
theorem magneticMoment_flow (F : StationaryFlow) (e m : ℝ) :
    magneticMoment (F.current e m) = (e / (2 * m)) • F.angularMomentum := by
  funext i
  have h (y : E3) : (WithLp.ofLp y ⨯₃ F.current e m y) i =
      e / m * (F.density y * (WithLp.ofLp y ⨯₃ F.velocity y) i) := by
    simp only [StationaryFlow.current, map_smul, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [magneticMoment, h, integral_const_mul, StationaryFlow.angularMomentum,
    Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The rigid rotation -/

/-- The bump profile on the line that is `1` on `[−1, 1]` and `0` outside `(−2, 2)`. -/
def bumpProfile : ContDiffBump (0 : ℝ) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The radial density `μ(x) = g(‖x‖²)` with the bump profile `g`. -/
def radialDensity (x : E3) : ℝ :=
  bumpProfile (‖x‖ ^ 2)

/-- The radial density is smooth. -/
theorem contDiff_radialDensity : ContDiff ℝ ∞ radialDensity :=
  bumpProfile.contDiff.comp (contDiff_norm_sq ℝ)

/-- The radial density vanishes outside the ball of radius `2`. -/
theorem hasCompactSupport_radialDensity : HasCompactSupport radialDensity := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E3) 2) fun x hx => ?_
  have hx2 : 2 < ‖x‖ := by simpa using hx
  refine bumpProfile.zero_of_le_dist ?_
  have h4 : (2 : ℝ) ≤ ‖x‖ ^ 2 := by nlinarith
  simpa [bumpProfile, Real.dist_eq, abs_of_nonneg (sq_nonneg ‖x‖)] using h4

/-- The derivative of the radial density along `v` is `2 g′(‖x‖²) ⟪x, v⟫`. -/
theorem fderiv_radialDensity_apply (x v : E3) :
    fderiv ℝ radialDensity x v = 2 * deriv bumpProfile (‖x‖ ^ 2) * inner ℝ x v := by
  have hg : HasDerivAt bumpProfile (deriv bumpProfile (‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    ((bumpProfile.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  change fderiv ℝ (fun z => bumpProfile (‖z‖ ^ 2)) x v = _
  rw [(hasFDerivAt_comp_normSq hg).fderiv]
  simp

/-- The velocity `x ↦ Ω × x` of a rigid rotation, as a continuous linear map. -/
def rigidVelocity (Ω : Fin 3 → ℝ) : E3 →L[ℝ] Fin 3 → ℝ :=
  (LinearMap.toContinuousLinearMap (crossProduct Ω)).comp
    (EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearMap

/-- The velocity of the rigid rotation is `x ↦ Ω × x`. -/
theorem rigidVelocity_apply (Ω : Fin 3 → ℝ) (x : E3) :
    rigidVelocity Ω x = Ω ⨯₃ WithLp.ofLp x :=
  rfl

/-- **The rigid rotation** of the radial density with the angular velocity `Ω`, `v = Ω × x`. -/
def rigidRotation (Ω : Fin 3 → ℝ) : StationaryFlow where
  density := radialDensity
  velocity := rigidVelocity Ω
  contDiff_density := contDiff_radialDensity
  contDiff_velocity := (rigidVelocity Ω).contDiff
  hasCompactSupport_density := hasCompactSupport_radialDensity
  div3_flux x := by
    have hμ : DifferentiableAt ℝ radialDensity x :=
      (contDiff_radialDensity.differentiable (by simp)) x
    have hv (l : Fin 3) : HasFDerivAt (fun y => rigidVelocity Ω y l)
        ((ContinuousLinearMap.proj l).comp (rigidVelocity Ω)) x :=
      ((ContinuousLinearMap.proj l).comp (rigidVelocity Ω)).hasFDerivAt
    have hterm (l : Fin 3) : partial3 (fun y => (radialDensity y • rigidVelocity Ω y) l) l x =
        radialDensity x * rigidVelocity Ω (EuclideanSpace.single l 1) l +
          rigidVelocity Ω x l * (2 * deriv bumpProfile (‖x‖ ^ 2) * x l) := by
      simp only [partial3, Pi.smul_apply, smul_eq_mul]
      rw [fderiv_fun_mul hμ (hv l).differentiableAt, (hv l).fderiv]
      simp [fderiv_radialDensity_apply, EuclideanSpace.inner_single_right]
    simp only [div3, Fin.sum_univ_three]
    rw [hterm 0, hterm 1, hterm 2]
    simp only [rigidVelocity_apply, cross_apply]
    simp
    ring

/-! ### The force and the torque in a uniform field -/

/-- **No force in a uniform field**: `∫ j × B₀ = 0` for a conserved current. -/
theorem force_uniformField {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) (B₀ : Fin 3 → ℝ) :
    (fun i => ∫ y, (j y ⨯₃ B₀) i) = 0 := by
  have hji (i k : Fin 3) : Integrable fun y => j y i * B₀ k :=
    (((continuous_apply i).comp hj.continuous).mul continuous_const).integrable_of_hasCompactSupport
      (hasCompactSupport_component hcj i).mul_right
  have h0 := integral_current_eq_zero hj hcj hdiv
  funext i
  fin_cases i
  · simp only [cross_apply]
    change ∫ y, (j y 1 * B₀ 2 - j y 2 * B₀ 1) = 0
    rw [integral_sub (hji 1 2) (hji 2 1), integral_mul_const, integral_mul_const, h0, h0]
    ring
  · simp only [cross_apply]
    change ∫ y, (j y 2 * B₀ 0 - j y 0 * B₀ 2) = 0
    rw [integral_sub (hji 2 0) (hji 0 2), integral_mul_const, integral_mul_const, h0, h0]
    ring
  · simp only [cross_apply]
    change ∫ y, (j y 0 * B₀ 1 - j y 1 * B₀ 0) = 0
    rw [integral_sub (hji 0 1) (hji 1 0), integral_mul_const, integral_mul_const, h0, h0]
    ring

/-- **The torque in a uniform field**: `∫ y × (j × B₀) = 𝔪 × B₀` for a conserved current. -/
theorem torque_uniformField {j : E3 → Fin 3 → ℝ} (hj : ContDiff ℝ 1 j)
    (hcj : HasCompactSupport j) (hdiv : ∀ x, div3 j x = 0) (B₀ : Fin 3 → ℝ) :
    (fun i => ∫ y, (WithLp.ofLp y ⨯₃ (j y ⨯₃ B₀)) i) = magneticMoment j ⨯₃ B₀ := by
  have hint := integrable_coord_mul hj.continuous hcj
  funext i
  have hpt (y : E3) : (WithLp.ofLp y ⨯₃ (j y ⨯₃ B₀)) i =
      ∑ k, B₀ k * (y k * j y i) - B₀ i * ∑ k, y k * j y k := by
    simp only [Fin.sum_univ_three]
    fin_cases i <;> simp [cross_apply] <;> ring
  simp only [hpt]
  rw [integral_sub (integrable_finsetSum _ fun k _ => (hint k i).const_mul _)
      ((integrable_finsetSum _ fun k _ => hint k k).const_mul _),
    integral_finsetSum _ fun k _ => (hint k i).const_mul _, integral_const_mul,
    integral_finsetSum _ fun k _ => hint k k, cross_magneticMoment_apply hj hcj hdiv]
  have hs (k : Fin 3) : ∫ y, y k * j y k = 0 := firstMoment_self hj hcj hdiv k
  simp only [integral_const_mul, hs, Finset.sum_const_zero, mul_zero, sub_zero]
  rfl

end ProjectAinos.Electrodynamics.MagneticMoment
