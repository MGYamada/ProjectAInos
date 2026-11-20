/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Potential.Multipole
public import ProjectAinos.Electrodynamics.ElectrostaticEnergy
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic

/-!
# Multipole moments and a system of charges in an external field

Space is `EuclideanSpace ℝ (Fin 3)`; the units have `div E = ρ`, so the potential of a charge
density `ρ` is the Newton potential `φ(x) = ∫ ρ(y)/(4π‖x − y‖) dy` (Landau–Lifshitz, *The Classical
Theory of Fields*, §§40–42). The density is continuous with its support in the ball `‖y‖ ≤ a`.

**The dipole moment (§40).**

* `totalCharge`, `dipoleMoment`: `Q = ∫ ρ` and `d = ∫ ρ(y) y dy`.
* `abs_newtonPotential_sub_dipole_le`: uniformly on `‖x‖ > a`,
  `|φ(x) − Q/(4π‖x‖) − ⟪d,x⟫/(4π‖x‖³)| ≤ (∫|ρ|‖y‖²)/(4π(‖x‖ − a)³)`.
* `dipoleMoment_translate`: moving the origin by `b` changes `d` into `d − Qb`.
* `hasGradientAt_dipolePotential`: the field of the dipole potential `⟪d,x⟫/(4π‖x‖³)` is
  `(3⟪n,d⟫n − d)/(4π‖x‖³)` with `n = x/‖x‖`.

**Multipole moments (§41).**

* `multipoleTerm`: the term `φ⁽ᵏ⁾(x) = (k!)⁻¹ ∫ ρ(y) DᵏK(x)(−y, …, −y) dy` of the expansion,
  homogeneous of degree `−(k + 1)` (`multipoleTerm_smul`).
* `abs_newtonPotential_sub_multipole_le`: for every order `n` there is a constant `Cₙ`, which
  depends only on `n`, with `|φ(x) − Σ_{k ≤ n} φ⁽ᵏ⁾(x)| ≤ Cₙ(∫|ρ|‖y‖ⁿ⁺¹)/(‖x‖ − a)ⁿ⁺²`.
* `quadrupoleMoment`: `Dᵢⱼ = ∫ ρ(3yᵢyⱼ − ‖y‖²δᵢⱼ)`, traceless (`quadrupoleMoment_trace`), with
  `multipoleTerm_two_eq`: `φ⁽²⁾(x) = Σ Dᵢⱼxᵢxⱼ/(8π‖x‖⁵)`.
* `abs_newtonPotential_sub_moments_le`: the expansion to the quadrupole with an explicit
  constant, `|φ − Q/(4π‖x‖) − ⟪d,x⟫/(4π‖x‖³) − ΣDᵢⱼxᵢxⱼ/(8π‖x‖⁵)| ≤
  (∫|ρ|‖y‖³)/(4π(‖x‖ − a)⁴)`.
* `multipoleTerm_translate`: if the terms below the order `k` vanish, the `k`-th term does not
  depend on the origin. The proof separates the orders of the expansion of the translated
  potential `φ(x + b)` along a ray with `eq_zero_of_abs_sum_mul_pow_le`.

**A system of charges in an external field (§42).**

* `externalEnergy`, `abs_externalEnergy_sub_le`: for an external potential `ψ` of class `C³` near
  the source ball with `Δψ(0) = 0`, `∫ρψ = Qψ(0) + ⟪d,∇ψ(0)⟫ + (1/6)Σ Dᵢⱼ∂ᵢ∂ⱼψ(0) + R` with
  `|R| ≤ (∫|ρ|‖y‖³)/6 · sup‖D³ψ‖`.
* `externalForce`, `norm_externalForce_sub_le`: `F = −∫ρ∇ψ = QE(0) + ∇(d·E)(0) + R` with the field
  `E = −∇ψ` and `‖R‖ ≤ (∫|ρ|‖y‖²)/2 · sup‖D³ψ‖`.
* `externalTorque`, `norm_externalTorque_sub_le`: `K = ∫ρ y × E = d × E(0) + R` with
  `‖R‖ ≤ (∫|ρ|‖y‖²) · sup‖D²ψ‖`, the cross product `cross3` taken in the co-ordinates.
* `abs_externalEnergy_dipolePotential_sub_le`: a neutral source in the field of a point dipole
  `d₁` at the separation `R` has the energy `(⟪d₁,d₂⟫ − 3⟪n,d₁⟫⟪n,d₂⟫)/(4π‖R‖³) + O(‖R‖⁻⁴)`.

**Instances.** `bumpCharge_dipole_instance`, `bumpCharge_multipole_instance`,
`bumpCharge_external_instance`, `bumpCharge_torque_instance`: the bump charge of
`ElectrostaticEnergy` (with `Q > 0`) in a uniform field; `neutralPair_translate_instance`,
`neutralPair_dipole_dipole_instance`: a neutral pair of bumps with the dipole moment `−Qc`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Metric Real Nat
open scoped Topology ContDiff RealInnerProductSpace Laplacian

namespace ProjectAinos.Electrodynamics.Multipole

open SmoothGeometry.Potential

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### Integrability -/

/-- A density with its support in a closed ball has a compact support. -/
theorem hasCompactSupport_of_tsupport_subset {ρ : E3 → ℝ} {a : ℝ}
    (ha : tsupport ρ ⊆ closedBall 0 a) : HasCompactSupport ρ :=
  (isCompact_closedBall 0 a).of_isClosed_subset (isClosed_tsupport ρ) ha

/-- The product of a continuous density with its support in `s` and a function continuous at the
points of `s` is continuous. -/
theorem continuous_smul_of_tsupport_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ρ : E3 → ℝ} {g : E3 → F} {s : Set E3} (hρ : Continuous ρ) (hs : tsupport ρ ⊆ s)
    (hg : ∀ w ∈ s, ContinuousAt g w) : Continuous fun y => ρ y • g y := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w ∈ tsupport ρ
  · exact hρ.continuousAt.smul (hg w (hs hw))
  · have h0 : (fun y => ρ y • g y) =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with y hy
      simp [hy]
    exact continuousAt_const.congr h0.symm

/-- The product of a continuous density of compact support and a continuous function is
integrable. -/
theorem integrable_density_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ρ : E3 → ℝ}
    (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {g : E3 → F} (hg : Continuous g) :
    Integrable fun y => ρ y • g y :=
  (hρ.smul hg).integrable_of_hasCompactSupport (hcρ.smul_right)

/-- The product of a continuous density of compact support and a continuous function is
integrable. -/
theorem integrable_density_mul {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    {g : E3 → ℝ}
    (hg : Continuous g) : Integrable fun y => ρ y * g y :=
  integrable_density_smul hρ hcρ hg

/-- The integrand of the potential, `ρ(y)K(x − y)`, is integrable. -/
theorem integrable_density_mul_newtonKernel_sub {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) (x : E3) : Integrable fun y => ρ y * newtonKernel (x - y) := by
  have h := (integrable_newtonKernel_mul hcρ hρ x).comp_sub_left x
  refine h.congr (Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel]
  ring

/-! ### The moments -/

/-- The total charge `Q = ∫ ρ`. -/
def totalCharge (ρ : E3 → ℝ) : ℝ := ∫ y, ρ y

/-- The dipole moment `d = ∫ ρ(y) y dy`. -/
def dipoleMoment (ρ : E3 → ℝ) : E3 := ∫ y, ρ y • y

/-- The quadrupole moment `Dᵢⱼ = ∫ ρ(y)(3yᵢyⱼ − ‖y‖²δᵢⱼ) dy`. -/
def quadrupoleMoment (ρ : E3 → ℝ) (i j : Fin 3) : ℝ :=
  ∫ y, ρ y * (3 * y i * y j - ‖y‖ ^ 2 * if i = j then 1 else 0)

/-- The term of order `k` of the multipole expansion,
`φ⁽ᵏ⁾(x) = (k!)⁻¹ ∫ ρ(y) DᵏK(x)(−y, …, −y) dy`. -/
def multipoleTerm (ρ : E3 → ℝ) (k : ℕ) (x : E3) : ℝ :=
  (k ! : ℝ)⁻¹ * ∫ y, ρ y * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)

/-- A multilinear map evaluated on the diagonal `(−y, …, −y)` is continuous in `y`. -/
theorem continuous_apply_neg {k : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => E3) ℝ) :
    Continuous fun y : E3 => L (fun _ => -y) :=
  L.coe_continuous.comp (continuous_pi fun _ => continuous_neg)

/-- A multilinear map evaluated on the diagonal is bounded by `‖L‖‖y‖ᵏ`. -/
theorem abs_apply_neg_le {k : ℕ} (L : ContinuousMultilinearMap ℝ (fun _ : Fin k => E3) ℝ)
    (y : E3) : |L (fun _ => -y)| ≤ ‖L‖ * ‖y‖ ^ k := by
  have h := L.le_opNorm (fun _ => -y)
  simpa [Finset.prod_const] using h

/-- The term of order `0` is the potential `Q/(4π‖x‖)` of the total charge. -/
theorem multipoleTerm_zero (ρ : E3 → ℝ) (x : E3) :
    multipoleTerm ρ 0 x = totalCharge ρ * newtonKernel x := by
  simp [multipoleTerm, totalCharge, integral_mul_const]

/-- The term of order `1` is the dipole potential `⟪d,x⟫/(4π‖x‖³)`. -/
theorem multipoleTerm_one {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) {x : E3}
    (hx : x ≠ 0) : multipoleTerm ρ 1 x = ⟪dipoleMoment ρ, x⟫ / (4 * π * ‖x‖ ^ 3) := by
  simp only [multipoleTerm, iteratedFDeriv_one_apply, fderiv_newtonKernel_neg_apply hx,
    Nat.factorial_one, Nat.cast_one, inv_one, one_mul]
  rw [dipoleMoment, real_inner_comm,
    ← integral_inner (integrable_density_smul (g := fun y : E3 => y) hρ hcρ continuous_id) x,
    ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [inner_smul_right]
  ring

/-- A point where the density does not vanish lies in the ball `‖y‖ ≤ a`. -/
theorem norm_le_of_ne_zero {ρ : E3 → ℝ} {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a) {y : E3}
    (hy : ρ y ≠ 0) : ‖y‖ ≤ a := by
  simpa using ha (subset_tsupport ρ hy)

/-- A remainder bounded by `c‖y‖ᵐ` where the density does not vanish contributes at most
`(∫|ρ|‖y‖ᵐ) c` to an integral against the density. -/
theorem abs_integral_mul_le {ρ R : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    {m : ℕ} {c : ℝ} (hR : ∀ y, ρ y ≠ 0 → |R y| ≤ c * ‖y‖ ^ m) :
    |∫ y, ρ y * R y| ≤ (∫ y, |ρ y| * ‖y‖ ^ m) * c := by
  rw [← integral_mul_const, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le
    ((integrable_density_mul hρ.abs hcρ.abs (continuous_norm.pow m)).mul_const c)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  by_cases hy : ρ y = 0
  · simp [hy]
  · calc |ρ y| * |R y| ≤ |ρ y| * (c * ‖y‖ ^ m) :=
          mul_le_mul_of_nonneg_left (hR y hy) (abs_nonneg _)
      _ = |ρ y| * ‖y‖ ^ m * c := by ring

/-- The total charge against a constant: `Q c = ∫ ρ c`. -/
theorem totalCharge_mul (ρ : E3 → ℝ) (c : ℝ) : totalCharge ρ * c = ∫ y, ρ y * c := by
  rw [totalCharge, integral_mul_const]

/-- The dipole moment against a vector: `⟪d, x⟫ = ∫ ρ(y)⟪x,y⟫ dy`. -/
theorem inner_dipoleMoment {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (x : E3) : ⟪dipoleMoment ρ, x⟫ = ∫ y, ρ y * ⟪x, y⟫ := by
  rw [dipoleMoment, real_inner_comm,
    ← integral_inner (integrable_density_smul (g := fun y : E3 => y) hρ hcρ continuous_id) x]
  simp only [inner_smul_right]

/-! ### The dipole expansion -/

/-- **The dipole expansion (§40)**: for a continuous density with its support in the ball
`‖y‖ ≤ a`, uniformly on `‖x‖ > a`,
`|φ(x) − Q/(4π‖x‖) − ⟪d,x⟫/(4π‖x‖³)| ≤ (∫|ρ|‖y‖²)/(4π(‖x‖ − a)³)`. -/
theorem abs_newtonPotential_sub_dipole_le {ρ : E3 → ℝ} (hρ : Continuous ρ) {a : ℝ}
    (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    |newtonPotential ρ x - totalCharge ρ / (4 * π * ‖x‖) -
        ⟪dipoleMoment ρ, x⟫ / (4 * π * ‖x‖ ^ 3)| ≤
      (∫ y, |ρ y| * ‖y‖ ^ 2) / (4 * π * (‖x‖ - a) ^ 3) := by
  have hcρ := hasCompactSupport_of_tsupport_subset ha
  have hd : 0 < ‖x‖ - a := by linarith
  have h2 : totalCharge ρ / (4 * π * ‖x‖) = ∫ y, ρ y * newtonKernel x := by
    rw [← totalCharge_mul, newtonKernel, div_eq_mul_inv]
  have h3 : ⟪dipoleMoment ρ, x⟫ / (4 * π * ‖x‖ ^ 3) =
      ∫ y, ρ y * (⟪x, y⟫ / (4 * π * ‖x‖ ^ 3)) := by
    rw [inner_dipoleMoment hρ hcρ, ← integral_div]
    simp only [mul_div_assoc]
  have hi1 := integrable_density_mul_newtonKernel_sub hρ hcρ x
  have hi2 : Integrable fun y => ρ y * newtonKernel x :=
    integrable_density_mul hρ hcρ continuous_const
  have hi3 : Integrable fun y => ρ y * (⟪x, y⟫ / (4 * π * ‖x‖ ^ 3)) :=
    integrable_density_mul hρ hcρ (by fun_prop)
  have hi12 : Integrable fun y => ρ y * newtonKernel (x - y) - ρ y * newtonKernel x :=
    hi1.sub hi2
  have hsplit : newtonPotential ρ x - totalCharge ρ / (4 * π * ‖x‖) -
      ⟪dipoleMoment ρ, x⟫ / (4 * π * ‖x‖ ^ 3) = ∫ y, ρ y * (newtonKernel (x - y) -
        newtonKernel x - ⟪x, y⟫ / (4 * π * ‖x‖ ^ 3)) := by
    rw [newtonPotential_eq_integral, h2, h3, ← integral_sub hi1 hi2, ← integral_sub hi12 hi3]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [hsplit, div_eq_mul_inv]
  refine abs_integral_mul_le hρ hcρ (fun y hy => ?_)
  have hya := norm_le_of_ne_zero ha hy
  refine (abs_newtonKernel_sub_dipole_le (hya.trans_lt hx)).trans ?_
  have hd' : 0 < ‖x‖ - ‖y‖ := by linarith
  rw [div_eq_mul_inv, mul_comm]
  refine mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) ?_) (by positivity)
  have : (‖x‖ - a) ^ 3 ≤ (‖x‖ - ‖y‖) ^ 3 := pow_le_pow_left₀ hd.le (by linarith) 3
  nlinarith [pi_pos]

/-! ### Translations and the dipole field -/

/-- The total charge does not depend on the origin. -/
theorem totalCharge_translate (ρ : E3 → ℝ) (b : E3) :
    totalCharge (fun y => ρ (y + b)) = totalCharge ρ :=
  integral_add_right_eq_self (μ := volume) ρ b

/-- **The dipole moment under a change of origin**: with the origin moved to `b` the density is
`ρ(· + b)`, and the dipole moment is `d − Qb`. -/
theorem dipoleMoment_translate {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (b : E3) : dipoleMoment (fun y => ρ (y + b)) = dipoleMoment ρ - totalCharge ρ • b := by
  have h := integral_add_right_eq_self (μ := volume) (fun y => ρ y • (y - b)) b
  simp only [add_sub_cancel_right] at h
  rw [dipoleMoment, h, dipoleMoment, totalCharge]
  simp only [smul_sub]
  rw [integral_sub (integrable_density_smul (g := fun y : E3 => y) hρ hcρ continuous_id)
    (integrable_density_smul hρ hcρ continuous_const), integral_smul_const]

/-- The potential of the translated density is the translated potential. -/
theorem newtonPotential_translate (ρ : E3 → ℝ) (b x : E3) :
    newtonPotential (fun y => ρ (y + b)) x = newtonPotential ρ (x + b) := by
  rw [newtonPotential_eq_integral, newtonPotential_eq_integral]
  have h := integral_add_right_eq_self (μ := volume) (fun y => ρ y * newtonKernel (x + b - y)) b
  simp only [add_sub_add_right_eq_sub] at h
  exact h

/-- The translated density has its support in the ball `‖y‖ ≤ a + ‖b‖`. -/
theorem tsupport_translate_subset {ρ : E3 → ℝ} {a : ℝ} (ha : tsupport ρ ⊆ closedBall 0 a)
    (b : E3) : tsupport (fun y => ρ (y + b)) ⊆ closedBall 0 (a + ‖b‖) := by
  have h := tsupport_comp_eq_preimage ρ (Homeomorph.addRight b)
  intro y hy
  have hyb : y + b ∈ tsupport ρ := by
    have : y ∈ ⇑(Homeomorph.addRight b) ⁻¹' tsupport ρ := h ▸ hy
    simpa using this
  have h2 := ha hyb
  rw [mem_closedBall_zero_iff] at h2 ⊢
  calc ‖y‖ = ‖(y + b) - b‖ := by simp
    _ ≤ ‖y + b‖ + ‖b‖ := norm_sub_le _ _
    _ ≤ a + ‖b‖ := by linarith

/-- The potential `⟪d,x⟫/(4π‖x‖³)` of a point dipole `d`. -/
def dipolePotential (d x : E3) : ℝ := ⟪d, x⟫ / (4 * π * ‖x‖ ^ 3)

/-- The field `(3⟪n,d⟫n − d)/(4π‖x‖³)` of a point dipole `d`, with `n = x/‖x‖`. -/
def dipoleField (d x : E3) : E3 :=
  (4 * π * ‖x‖ ^ 3)⁻¹ • ((3 * ⟪‖x‖⁻¹ • x, d⟫) • (‖x‖⁻¹ • x) - d)

/-- The term of order `1` is the potential of the point dipole `d`. -/
theorem multipoleTerm_one_eq_dipolePotential {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {x : E3} (hx : x ≠ 0) :
    multipoleTerm ρ 1 x = dipolePotential (dipoleMoment ρ) x :=
  multipoleTerm_one hρ hcρ hx

/-- The dipole potential is the derivative of the kernel along `−d`. -/
theorem dipolePotential_eq {d x : E3} (hx : x ≠ 0) :
    dipolePotential d x = fderiv ℝ newtonKernel x (-d) := by
  rw [fderiv_newtonKernel_neg_apply hx, dipolePotential, real_inner_comm]

/-- **The field of a dipole (§40)**: away from the origin the gradient of the dipole potential
is `−(3⟪n,d⟫n − d)/(4π‖x‖³)`, so the field `E = −∇φ` is `dipoleField d x`. -/
theorem hasGradientAt_dipolePotential (d : E3) {x : E3} (hx : x ≠ 0) :
    HasGradientAt (dipolePotential d) (-dipoleField d x) x := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hK := contDiffAt_newtonKernel hx (n := 2)
  have heq : dipolePotential d =ᶠ[𝓝 x] fun y => fderiv ℝ newtonKernel y (-d) := by
    filter_upwards [eventually_ne_nhds hx] with y hy using dipolePotential_eq hy
  have hdiff : DifferentiableAt ℝ (fun y => fderiv ℝ newtonKernel y (-d)) x :=
    ((hK.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hdiff.hasFDerivAt.congr_of_eventuallyEq heq).congr_fderiv ?_
  ext u
  have h2 := iteratedFDeriv_two_newtonKernel hx ![u, -d]
  rw [iteratedFDeriv_two_apply] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [fderiv_fderiv_apply hK, h2, InnerProductSpace.toDual_apply_apply, dipoleField]
  simp only [inner_neg_left, inner_smul_left, inner_sub_left, inner_neg_right,
    RCLike.conj_to_real, real_inner_comm u d, real_inner_comm u x]
  field_simp
  ring

/-- The field of a dipole is minus the gradient of its potential. -/
theorem neg_gradient_dipolePotential (d : E3) {x : E3} (hx : x ≠ 0) :
    -gradient (dipolePotential d) x = dipoleField d x := by
  rw [(hasGradientAt_dipolePotential d hx).gradient, neg_neg]

/-! ### The multipole expansion of every order -/

/-- The sum of the terms up to the order `n` is the integral of `ρ` against the Taylor
polynomial of the kernel. -/
theorem sum_multipoleTerm_eq {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (n : ℕ) (x : E3) :
    ∑ k ∈ Finset.range (n + 1), multipoleTerm ρ k x = ∫ y, ρ y * ∑ k ∈ Finset.range (n + 1),
      (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y) := by
  have hint (k : ℕ) : Integrable fun y =>
      (k ! : ℝ)⁻¹ * (ρ y * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)) :=
    (integrable_density_mul hρ hcρ (continuous_apply_neg _)).const_mul _
  rw [show (fun y => ρ y * ∑ k ∈ Finset.range (n + 1),
      (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)) =
      fun y => ∑ k ∈ Finset.range (n + 1),
        (k ! : ℝ)⁻¹ * (ρ y * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)) by
    funext y
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring,
    integral_finsetSum _ fun k _ => hint k]
  exact Finset.sum_congr rfl fun k _ => by rw [multipoleTerm, integral_const_mul]

/-- **The multipole expansion of every order (§41)**: for every order `n` there is a constant
`Cₙ`, which depends only on `n`, such that for a continuous density with its support in the ball
`‖y‖ ≤ a`, uniformly on `‖x‖ > a`,
`|φ(x) − Σ_{k ≤ n} φ⁽ᵏ⁾(x)| ≤ Cₙ (∫|ρ|‖y‖ⁿ⁺¹)/(‖x‖ − a)ⁿ⁺²`. -/
theorem abs_newtonPotential_sub_multipole_le (n : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ {ρ : E3 → ℝ}, Continuous ρ → ∀ {a : ℝ}, tsupport ρ ⊆ closedBall 0 a →
      ∀ {x : E3}, a < ‖x‖ →
        |newtonPotential ρ x - ∑ k ∈ Finset.range (n + 1), multipoleTerm ρ k x| ≤
          C * (∫ y, |ρ y| * ‖y‖ ^ (n + 1)) / (‖x‖ - a) ^ (n + 2) := by
  obtain ⟨C, hC0, hC⟩ := newtonKernel_taylor_le n
  refine ⟨C, hC0, fun {ρ} hρ {a} ha {x} hx => ?_⟩
  have hcρ := hasCompactSupport_of_tsupport_subset ha
  have hd : 0 < ‖x‖ - a := by linarith
  have hint : Integrable fun y => ρ y * ∑ k ∈ Finset.range (n + 1),
      (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y) :=
    integrable_density_mul hρ hcρ (continuous_finsetSum _ fun k _ =>
      continuous_const.mul (continuous_apply_neg _))
  rw [newtonPotential_eq_integral, sum_multipoleTerm_eq hρ hcρ,
    ← integral_sub (integrable_density_mul_newtonKernel_sub hρ hcρ x) hint]
  simp only [← mul_sub]
  refine (abs_integral_mul_le (m := n + 1) (c := C / (‖x‖ - a) ^ (n + 2)) hρ hcρ
    (fun y hy => ?_)).trans_eq (by ring)
  have hya := norm_le_of_ne_zero ha hy
  refine (hC x y (hya.trans_lt hx)).trans ?_
  have hd' : 0 < ‖x‖ - ‖y‖ := by linarith
  rw [div_mul_eq_mul_div, mul_comm C]
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  exact pow_le_pow_left₀ hd.le (by linarith) _

/-- **The quadrupole expansion with an explicit constant (§41)**: for a continuous density
with its support in the ball `‖y‖ ≤ a`, uniformly on `‖x‖ > a`,
`|φ(x) − φ⁽⁰⁾(x) − φ⁽¹⁾(x) − φ⁽²⁾(x)| ≤ (∫|ρ|‖y‖³)/(4π(‖x‖ − a)⁴)`. -/
theorem abs_newtonPotential_sub_quadrupole_le {ρ : E3 → ℝ} (hρ : Continuous ρ) {a : ℝ}
    (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    |newtonPotential ρ x - ∑ k ∈ Finset.range 3, multipoleTerm ρ k x| ≤
      (∫ y, |ρ y| * ‖y‖ ^ 3) / (4 * π * (‖x‖ - a) ^ 4) := by
  have hcρ := hasCompactSupport_of_tsupport_subset ha
  have hd : 0 < ‖x‖ - a := by linarith
  have hint : Integrable fun y => ρ y * ∑ k ∈ Finset.range 3,
      (k ! : ℝ)⁻¹ * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y) :=
    integrable_density_mul hρ hcρ (continuous_finsetSum _ fun k _ =>
      continuous_const.mul (continuous_apply_neg _))
  rw [newtonPotential_eq_integral, sum_multipoleTerm_eq hρ hcρ 2,
    ← integral_sub (integrable_density_mul_newtonKernel_sub hρ hcρ x) hint]
  simp only [← mul_sub]
  rw [div_eq_mul_inv]
  refine abs_integral_mul_le (m := 3) hρ hcρ (fun y hy => ?_)
  have hya := norm_le_of_ne_zero ha hy
  refine (abs_newtonKernel_sub_taylor_two_le (hya.trans_lt hx)).trans ?_
  have hd' : 0 < ‖x‖ - ‖y‖ := by linarith
  rw [div_eq_mul_inv, mul_comm]
  refine mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) ?_) (by positivity)
  have : (‖x‖ - a) ^ 4 ≤ (‖x‖ - ‖y‖) ^ 4 := pow_le_pow_left₀ hd.le (by linarith) 4
  nlinarith [pi_pos]

/-- **Homogeneity**: the term of order `k` is homogeneous of degree `−(k + 1)`,
`φ⁽ᵏ⁾(cx) = c^{-(k+1)} φ⁽ᵏ⁾(x)` for `c > 0` and `x ≠ 0`. -/
theorem multipoleTerm_smul (ρ : E3 → ℝ) (k : ℕ) {c : ℝ} (hc : 0 < c) {x : E3} (hx : x ≠ 0) :
    multipoleTerm ρ k (c • x) = (c ^ (k + 1))⁻¹ * multipoleTerm ρ k x := by
  simp only [multipoleTerm, iteratedFDeriv_newtonKernel_smul hc hx, smul_apply, smul_eq_mul]
  rw [show (fun y => ρ y * ((c ^ (k + 1))⁻¹ *
      iteratedFDeriv ℝ k newtonKernel x (fun _ => -y))) =
      fun y => (c ^ (k + 1))⁻¹ * (ρ y * iteratedFDeriv ℝ k newtonKernel x (fun _ => -y)) by
    funext y
    ring, integral_const_mul]
  ring

/-- The variation of the term of order `k` between two points is controlled by the variation
of `DᵏK`: `|φ⁽ᵏ⁾(x') − φ⁽ᵏ⁾(x)| ≤ (k!)⁻¹ (∫|ρ|‖y‖ᵏ) ‖DᵏK(x') − DᵏK(x)‖`. -/
theorem abs_multipoleTerm_sub_le {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (k : ℕ) (x x' : E3) :
    |multipoleTerm ρ k x' - multipoleTerm ρ k x| ≤ (k ! : ℝ)⁻¹ * ((∫ y, |ρ y| * ‖y‖ ^ k) *
      ‖iteratedFDeriv ℝ k newtonKernel x' - iteratedFDeriv ℝ k newtonKernel x‖) := by
  have h1 := integrable_density_mul hρ hcρ
    (continuous_apply_neg (iteratedFDeriv ℝ k newtonKernel x'))
  have h2 := integrable_density_mul hρ hcρ
    (continuous_apply_neg (iteratedFDeriv ℝ k newtonKernel x))
  rw [multipoleTerm, multipoleTerm, ← mul_sub, ← integral_sub h1 h2, abs_mul,
    abs_of_pos (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simp only [← mul_sub]
  refine abs_integral_mul_le hρ hcρ (fun y _ => ?_)
  have := abs_apply_neg_le (iteratedFDeriv ℝ k newtonKernel x' -
    iteratedFDeriv ℝ k newtonKernel x) y
  simpa only [sub_apply] using this

/-! ### The translation law -/

/-- The bound behind the translation law: if the terms of `ρ` below the order `k` vanish away
from the origin, the coefficients `cⱼ = φ'⁽ʲ⁾(x) − [j = k] φ⁽ᵏ⁾(x)` of the translated density
`ρ' = ρ(· + b)` satisfy `|Σ_{j ≤ k} cⱼ tʲ| ≤ M tᵏ⁺¹` for small `t > 0`. -/
theorem exists_abs_sum_multipoleTerm_translate_le {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {k : ℕ}
    (hlow : ∀ j < k, ∀ x : E3, x ≠ 0 → multipoleTerm ρ j x = 0) (b : E3) {x : E3}
    (hx : x ≠ 0) : ∃ M t₀, 0 < t₀ ∧ ∀ t, 0 < t → t ≤ t₀ →
      |∑ j ∈ Finset.range (k + 1), (multipoleTerm (fun y => ρ (y + b)) j x -
        if j = k then multipoleTerm ρ k x else 0) * t ^ j| ≤ M * t ^ (k + 1) := by
  obtain ⟨a, ha0, ha⟩ := exists_tsupport_subset_closedBall hcρ
  set ρ' : E3 → ℝ := fun y => ρ (y + b) with hρ'def
  have hρ' : Continuous ρ' := hρ.comp (continuous_id.add continuous_const)
  have ha' : tsupport ρ' ⊆ closedBall 0 (a + ‖b‖) := tsupport_translate_subset ha b
  obtain ⟨C₁, hC₁0, hC₁⟩ := abs_newtonPotential_sub_multipole_le k
  obtain ⟨C₂, hC₂0, hC₂⟩ := norm_iteratedFDeriv_newtonKernel_add_sub_le k
  set a' := a + ‖b‖ with ha'def
  have ha'0 : 0 ≤ a' := by positivity
  set A₁ := ∫ y, |ρ y| * ‖y‖ ^ (k + 1)
  set A₂ := ∫ y, |ρ' y| * ‖y‖ ^ (k + 1)
  set A₀ := ∫ y, |ρ y| * ‖y‖ ^ k
  have hA₁ : 0 ≤ A₁ := integral_nonneg fun y => by positivity
  have hA₂ : 0 ≤ A₂ := integral_nonneg fun y => by positivity
  have hA₀ : 0 ≤ A₀ := integral_nonneg fun y => by positivity
  set E := C₁ * A₂ + C₁ * A₁ + (k ! : ℝ)⁻¹ * (A₀ * (C₂ * ‖b‖)) with hEdef
  have hE : 0 ≤ E := by positivity
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  refine ⟨E * 2 ^ (k + 2) / ‖x‖ ^ (k + 2), ‖x‖ / (2 * a' + 1), by positivity,
    fun t ht htt => ?_⟩
  set X : E3 := t⁻¹ • x with hXdef
  have hX : ‖X‖ = t⁻¹ * ‖x‖ := by
    rw [hXdef, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
  have hXbig : 2 * a' + 1 ≤ ‖X‖ := by
    rw [le_div_iff₀ (by positivity)] at htt
    rw [hX, ← div_eq_inv_mul, le_div_iff₀ ht]
    linarith
  have hXb : ‖X‖ - ‖b‖ ≤ ‖X + b‖ := by
    have := norm_sub_norm_le X (-b)
    simpa using this
  have hXb0 : X + b ≠ 0 := norm_pos_iff.mp (by linarith [norm_nonneg b])
  have hT1 := hC₁ hρ' ha' (x := X) (by linarith)
  have hT2 := hC₁ hρ ha (x := X + b) (by linarith)
  have hT3 : |multipoleTerm ρ k (X + b) - multipoleTerm ρ k X| ≤
      (k ! : ℝ)⁻¹ * (A₀ * (C₂ * ‖b‖ / (‖X‖ - ‖b‖) ^ (k + 2))) :=
    (abs_multipoleTerm_sub_le hρ hcρ k X (X + b)).trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hC₂ X b (by linarith)) hA₀) (by positivity))
  have hsum : ∑ j ∈ Finset.range (k + 1), multipoleTerm ρ j (X + b) =
      multipoleTerm ρ k (X + b) := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero
      (fun j hj => hlow j (Finset.mem_range.mp hj) _ hXb0), zero_add]
  have htrans : newtonPotential ρ' X = newtonPotential ρ (X + b) := newtonPotential_translate ρ b X
  set D := (‖X‖ - a') ^ (k + 2) with hDdef
  have hD : 0 < D := by
    rw [hDdef]
    exact pow_pos (by linarith) _
  have hD2 : C₁ * A₁ / (‖X + b‖ - a) ^ (k + 2) ≤ C₁ * A₁ / D :=
    div_le_div_of_nonneg_left (by positivity) hD (pow_le_pow_left₀ (by linarith) (by linarith) _)
  have hD3 : C₂ * ‖b‖ / (‖X‖ - ‖b‖) ^ (k + 2) ≤ C₂ * ‖b‖ / D :=
    div_le_div_of_nonneg_left (by positivity) hD (pow_le_pow_left₀ (by linarith) (by linarith) _)
  have hF : |∑ j ∈ Finset.range (k + 1), multipoleTerm ρ' j X - multipoleTerm ρ k X| ≤ E / D := by
    have key : ∑ j ∈ Finset.range (k + 1), multipoleTerm ρ' j X - multipoleTerm ρ k X =
        -(newtonPotential ρ' X - ∑ j ∈ Finset.range (k + 1), multipoleTerm ρ' j X) +
        (newtonPotential ρ (X + b) - ∑ j ∈ Finset.range (k + 1), multipoleTerm ρ j (X + b)) +
        (multipoleTerm ρ k (X + b) - multipoleTerm ρ k X) := by
      rw [htrans, hsum]
      ring
    rw [key]
    calc _ ≤ |newtonPotential ρ' X - ∑ j ∈ Finset.range (k + 1), multipoleTerm ρ' j X| +
          |newtonPotential ρ (X + b) - ∑ j ∈ Finset.range (k + 1), multipoleTerm ρ j (X + b)| +
          |multipoleTerm ρ k (X + b) - multipoleTerm ρ k X| := by
          refine (abs_add_le _ _).trans ?_
          gcongr
          exact (abs_add_le _ _).trans (by rw [abs_neg])
      _ ≤ C₁ * A₂ / D + C₁ * A₁ / D + (k ! : ℝ)⁻¹ * (A₀ * (C₂ * ‖b‖ / D)) :=
          add_le_add (add_le_add hT1 (hT2.trans hD2)) (hT3.trans (by gcongr))
      _ = E / D := by
          rw [hEdef]
          ring
  have hED : E / D ≤ E * 2 ^ (k + 2) / ‖x‖ ^ (k + 2) * t ^ (k + 2) := by
    have hD' : (t⁻¹ * ‖x‖ / 2) ^ (k + 2) ≤ D := by
      rw [hDdef, ← hX]
      exact pow_le_pow_left₀ (by positivity) (by linarith) _
    calc E / D ≤ E / (t⁻¹ * ‖x‖ / 2) ^ (k + 2) :=
          div_le_div_of_nonneg_left hE (by positivity) hD'
      _ = E * 2 ^ (k + 2) / ‖x‖ ^ (k + 2) * t ^ (k + 2) := by
          rw [div_pow, mul_pow, inv_pow]
          field_simp
  have hhom : ∑ j ∈ Finset.range (k + 1), multipoleTerm ρ' j X - multipoleTerm ρ k X =
      (∑ j ∈ Finset.range (k + 1), (multipoleTerm ρ' j x -
        if j = k then multipoleTerm ρ k x else 0) * t ^ j) * t := by
    have hs (σ : E3 → ℝ) (j : ℕ) : multipoleTerm σ j X = t ^ (j + 1) * multipoleTerm σ j x := by
      rw [hXdef, multipoleTerm_smul σ j (inv_pos.mpr ht) hx, inv_pow, inv_inv]
    simp only [hs, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_range, lt_add_one, ite_true]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · ring
  have h := hF.trans hED
  rw [hhom, abs_mul, abs_of_pos ht] at h
  refine le_of_mul_le_mul_right ?_ ht
  calc _ ≤ E * 2 ^ (k + 2) / ‖x‖ ^ (k + 2) * t ^ (k + 2) := h
    _ = _ := by ring

/-- **The translation law (§41)**: if the terms of the orders below `k` vanish away from the
origin, then away from the origin the term of order `k` of the translated density `ρ(· + b)`
is the term of `ρ`: the first nonvanishing multipole does not depend on the origin. -/
theorem multipoleTerm_translate {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    {k : ℕ} (hlow : ∀ j < k, ∀ x : E3, x ≠ 0 → multipoleTerm ρ j x = 0) (b : E3) {x : E3}
    (hx : x ≠ 0) : multipoleTerm (fun y => ρ (y + b)) k x = multipoleTerm ρ k x := by
  obtain ⟨M, t₀, ht₀, h⟩ := exists_abs_sum_multipoleTerm_translate_le hρ hcρ hlow b hx
  have := eq_zero_of_abs_sum_mul_pow_le ht₀ h k le_rfl
  simpa [sub_eq_zero] using this

/-- Under the hypothesis of the translation law the terms of the translated density below the
order `k` vanish as well. -/
theorem multipoleTerm_translate_of_lt {ρ : E3 → ℝ} (hρ : Continuous ρ)
    (hcρ : HasCompactSupport ρ) {k : ℕ}
    (hlow : ∀ j < k, ∀ x : E3, x ≠ 0 → multipoleTerm ρ j x = 0) (b : E3) {j : ℕ} (hj : j < k)
    {x : E3} (hx : x ≠ 0) : multipoleTerm (fun y => ρ (y + b)) j x = 0 := by
  obtain ⟨M, t₀, ht₀, h⟩ := exists_abs_sum_multipoleTerm_translate_le hρ hcρ hlow b hx
  have := eq_zero_of_abs_sum_mul_pow_le ht₀ h j hj.le
  simpa [hj.ne] using this

/-! ### The quadrupole moment -/

/-- The quadrupole moment is symmetric. -/
theorem quadrupoleMoment_symm (ρ : E3 → ℝ) (i j : Fin 3) :
    quadrupoleMoment ρ i j = quadrupoleMoment ρ j i := by
  unfold quadrupoleMoment
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [eq_comm (a := i)]
  ring

/-- A vector is the sum of its components along the unit vectors. -/
theorem sum_smul_single (y : E3) : ∑ i : Fin 3, y i • EuclideanSpace.single i (1 : ℝ) = y := by
  simpa [EuclideanSpace.basisFun_apply] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr y

/-- A bilinear form on the diagonal in the co-ordinates, `B(y, y) = Σᵢⱼ yᵢyⱼ B(eᵢ, eⱼ)`. -/
theorem bilinear_apply_eq_sum (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) (y : E3) :
    B y y = ∑ i : Fin 3, ∑ j : Fin 3, y i * y j *
      B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  conv_lhs => rw [← sum_smul_single y]
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The square of the norm in the co-ordinates. -/
theorem norm_sq_eq_sum (y : E3) : ‖y‖ ^ 2 = ∑ i : Fin 3, y i ^ 2 :=
  EuclideanSpace.real_norm_sq_eq y

/-- The co-ordinate functions are continuous. -/
theorem continuous_coord (i : Fin 3) : Continuous fun y : E3 => y i :=
  (EuclideanSpace.proj i : E3 →L[ℝ] ℝ).continuous

/-- **The quadrupole moment is traceless**: `Σᵢ Dᵢᵢ = 0`. -/
theorem quadrupoleMoment_trace {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ) :
    ∑ i : Fin 3, quadrupoleMoment ρ i i = 0 := by
  unfold quadrupoleMoment
  rw [← integral_finsetSum Finset.univ fun i _ => integrable_density_mul hρ hcρ
    (g := fun y : E3 => 3 * y i * y i - ‖y‖ ^ 2 * if i = i then 1 else 0)
    (((continuous_const.mul (continuous_coord i)).mul (continuous_coord i)).sub
      ((continuous_norm.pow 2).mul continuous_const))]
  have h0 : ∀ y : E3, ∑ i : Fin 3, ρ y * (3 * y i * y i - ‖y‖ ^ 2) = 0 := by
    intro y
    simp only [Fin.sum_univ_three, norm_sq_eq_sum y]
    ring
  simp [h0]

/-- **The quadrupole moment against a bilinear form**:
`Σᵢⱼ Dᵢⱼ B(eᵢ, eⱼ) = 3∫ρ B(y, y) − (∫ρ‖y‖²) Σᵢ B(eᵢ, eᵢ)`. -/
theorem sum_quadrupoleMoment_mul {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (B : E3 →L[ℝ] E3 →L[ℝ] ℝ) :
    ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      3 * (∫ y, ρ y * B y y) - (∫ y, ρ y * ‖y‖ ^ 2) *
        ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have hint (i j : Fin 3) : Integrable fun y : E3 =>
      ρ y * (3 * y i * y j - ‖y‖ ^ 2 * if i = j then 1 else 0) *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
    (integrable_density_mul hρ hcρ (((continuous_const.mul (continuous_coord i)).mul
      (continuous_coord j)).sub ((continuous_norm.pow 2).mul continuous_const))).mul_const _
  have hB : Continuous fun y : E3 => B y y :=
    (B.continuous.clm_apply continuous_id)
  have hL : ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      ∫ y, ∑ i : Fin 3, ∑ j : Fin 3, ρ y * (3 * y i * y j - ‖y‖ ^ 2 * if i = j then 1 else 0) *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hint i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [quadrupoleMoment, integral_mul_const]
  have hR : 3 * (∫ y, ρ y * B y y) - (∫ y, ρ y * ‖y‖ ^ 2) *
        ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) =
      ∫ y, (3 * (ρ y * B y y) - ρ y * ‖y‖ ^ 2 *
        ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) := by
    have h1 : Integrable fun y => 3 * (ρ y * B y y) :=
      (integrable_density_mul hρ hcρ hB).const_mul 3
    have h2 : Integrable fun y => ρ y * ‖y‖ ^ 2 *
        ∑ i : Fin 3, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) :=
      (integrable_density_mul (g := fun y : E3 => ‖y‖ ^ 2) hρ hcρ
        (continuous_norm.pow 2)).mul_const _
    rw [integral_sub h1 h2, integral_const_mul, integral_mul_const]
  rw [hL, hR]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [bilinear_apply_eq_sum B y, norm_sq_eq_sum y, Fin.sum_univ_three]
  simp
  ring

/-- **The quadrupole term (§41)**: away from the origin,
`φ⁽²⁾(x) = Σᵢⱼ Dᵢⱼxᵢxⱼ/(8π‖x‖⁵)`. -/
theorem multipoleTerm_two_eq {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    {x : E3} (hx : x ≠ 0) :
    multipoleTerm ρ 2 x =
      (∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j * x i * x j) / (8 * π * ‖x‖ ^ 5) := by
  have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set B : E3 →L[ℝ] E3 →L[ℝ] ℝ := (innerSL ℝ x).smulRight (innerSL ℝ x) with hBdef
  have hBapp (u v : E3) : B u v = ⟪x, u⟫ * ⟪x, v⟫ := by
    simp [hBdef]
  have hsum := sum_quadrupoleMoment_mul hρ hcρ B
  simp only [hBapp, EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] at hsum
  have htr : ∑ i : Fin 3, x i * x i = ‖x‖ ^ 2 := by
    rw [norm_sq_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hlhs : ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j * x i * x j =
      ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j * (x i * x j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hlhs, hsum, htr]
  have hi1 : Integrable fun y => 3 * (ρ y * (⟪x, y⟫ * ⟪x, y⟫)) :=
    (integrable_density_mul hρ hcρ (g := fun y => ⟪x, y⟫ * ⟪x, y⟫) (by fun_prop)).const_mul 3
  have hi2 : Integrable fun y => ρ y * ‖y‖ ^ 2 * ‖x‖ ^ 2 :=
    (integrable_density_mul (g := fun y : E3 => ‖y‖ ^ 2) hρ hcρ (continuous_norm.pow 2)).mul_const _
  have hcomb : 3 * (∫ y, ρ y * (⟪x, y⟫ * ⟪x, y⟫)) - (∫ y, ρ y * ‖y‖ ^ 2) * ‖x‖ ^ 2 =
      ∫ y, ρ y * (3 * ⟪x, y⟫ * ⟪x, y⟫ - ‖x‖ ^ 2 * ‖y‖ ^ 2) := by
    rw [← integral_const_mul, ← integral_mul_const, ← integral_sub hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    ring
  rw [hcomb, multipoleTerm, ← integral_div, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [iteratedFDeriv_two_newtonKernel hx]
  simp only [inner_neg_right]
  norm_num
  field_simp
  ring

/-- **The expansion to the quadrupole in the moments (§41)**: for a continuous density with
its support in the ball `‖y‖ ≤ a`, `a ≥ 0`, uniformly on `‖x‖ > a`,
`|φ(x) − Q/(4π‖x‖) − ⟪d,x⟫/(4π‖x‖³) − Σ Dᵢⱼxᵢxⱼ/(8π‖x‖⁵)| ≤ (∫|ρ|‖y‖³)/(4π(‖x‖ − a)⁴)`. -/
theorem abs_newtonPotential_sub_moments_le {ρ : E3 → ℝ} (hρ : Continuous ρ) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : tsupport ρ ⊆ closedBall 0 a) {x : E3} (hx : a < ‖x‖) :
    |newtonPotential ρ x - totalCharge ρ / (4 * π * ‖x‖) -
        ⟪dipoleMoment ρ, x⟫ / (4 * π * ‖x‖ ^ 3) -
        (∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j * x i * x j) / (8 * π * ‖x‖ ^ 5)| ≤
      (∫ y, |ρ y| * ‖y‖ ^ 3) / (4 * π * (‖x‖ - a) ^ 4) := by
  have hcρ := hasCompactSupport_of_tsupport_subset ha
  have hx0 : x ≠ 0 := norm_pos_iff.mp (ha0.trans_lt hx)
  have h := abs_newtonPotential_sub_quadrupole_le hρ ha hx
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, multipoleTerm_zero,
    multipoleTerm_one hρ hcρ hx0, multipoleTerm_two_eq hρ hcρ hx0, newtonKernel,
    ← div_eq_mul_inv] at h
  convert h using 2
  ring

/-! ### Taylor's formula for the external potential -/

/-- The segment from the origin to a point of the ball `‖y‖ ≤ a` lies in the ball. -/
theorem zero_add_smul_mem_closedBall {a : ℝ} {y : E3} (hy : ‖y‖ ≤ a) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (0 : E3) + t • y ∈ closedBall (0 : E3) a := by
  rw [zero_add, mem_closedBall_zero_iff, norm_smul, Real.norm_of_nonneg ht.1]
  nlinarith [norm_nonneg y, ht.2]

/-- Taylor's formula to the second order for a function of class `C³` on the ball `‖w‖ ≤ a`
about the origin: `|ψ(y) − ψ(0) − Dψ(0)y − D²ψ(0)(y, y)/2| ≤ (B/6)‖y‖³` with `B` a bound of
`‖D³ψ‖` on the ball. -/
theorem abs_sub_taylor_two_le {ψ : E3 → ℝ} {a B : ℝ}
    (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 3 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 3 ψ w‖ ≤ B) {y : E3} (hy : ‖y‖ ≤ a) :
    |ψ y - ψ 0 - fderiv ℝ ψ 0 y - fderiv ℝ (fderiv ℝ ψ) 0 y y / 2| ≤ B / 6 * ‖y‖ ^ 3 := by
  have h := norm_sub_sum_iteratedFDeriv_le (f := ψ) (x := 0) (y := y) (n := 2)
    (M := B * ‖y‖ ^ 3) (fun t ht => hψ _ (zero_add_smul_mem_closedBall hy ht))
    (fun t ht => by
      refine ((iteratedFDeriv ℝ (2 + 1) ψ (0 + t • y)).le_opNorm _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (hB _ (zero_add_smul_mem_closedBall hy ht)) (by positivity))
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, iteratedFDeriv_two_apply, smul_eq_mul,
    Real.norm_eq_abs] at h
  convert h using 1
  · norm_num
    ring_nf
  · norm_num [Nat.factorial]
    ring

/-- Taylor's formula to the first order for the derivative of a function of class `C³` on the
ball `‖w‖ ≤ a`: `|Dψ(y)v − Dψ(0)v − D²ψ(0)(y, v)| ≤ (B/2)‖y‖²‖v‖`. -/
theorem abs_fderiv_sub_taylor_one_le {ψ : E3 → ℝ} {a B : ℝ}
    (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 3 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 3 ψ w‖ ≤ B) {y : E3} (hy : ‖y‖ ≤ a)
    (v : E3) :
    |fderiv ℝ ψ y v - fderiv ℝ ψ 0 v - fderiv ℝ (fderiv ℝ ψ) 0 y v| ≤ B / 2 * ‖y‖ ^ 2 * ‖v‖ := by
  have h := norm_sub_sum_iteratedFDeriv_le (f := fderiv ℝ ψ) (x := 0) (y := y) (n := 1)
    (M := B * ‖y‖ ^ 2)
    (fun t ht => (hψ _ (zero_add_smul_mem_closedBall hy ht)).fderiv_right (m := 1 + 1)
      (by norm_num))
    (fun t ht => by
      refine ((iteratedFDeriv ℝ (1 + 1) (fderiv ℝ ψ) (0 + t • y)).le_opNorm _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [norm_iteratedFDeriv_fderiv]
      exact mul_le_mul_of_nonneg_right (hB _ (zero_add_smul_mem_closedBall hy ht)) (by positivity))
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, inv_one, one_smul] at h
  have h2 := ((fderiv ℝ ψ y - (fderiv ℝ ψ 0 + fderiv ℝ (fderiv ℝ ψ) 0 y)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right h (norm_nonneg v))
  rw [Real.norm_eq_abs] at h2
  simp only [sub_apply, add_apply] at h2
  calc _ = |fderiv ℝ ψ y v - (fderiv ℝ ψ 0 v + fderiv ℝ (fderiv ℝ ψ) 0 y v)| := by ring_nf
    _ ≤ B * ‖y‖ ^ 2 / ↑(1 + 1)! * ‖v‖ := h2
    _ = _ := by
        rw [show (1 + 1)! = 2 from rfl, Nat.cast_ofNat]
        ring

/-! ### A system of charges in an external field -/

/-- The energy `∫ ρψ` of a charge density in an external potential `ψ`. -/
def externalEnergy (ρ ψ : E3 → ℝ) : ℝ := ∫ y, ρ y * ψ y

/-- The force `F = −∫ ρ∇ψ` on a charge density in an external potential `ψ`, that is
`∫ ρE` with the external field `E = −∇ψ`. -/
def externalForce (ρ ψ : E3 → ℝ) : E3 := -∫ y, ρ y • gradient ψ y

/-- The dipole moment against a linear form: `L d = ∫ ρ(y) L(y) dy`. -/
theorem clm_dipoleMoment {ρ : E3 → ℝ} (hρ : Continuous ρ) (hcρ : HasCompactSupport ρ)
    (L : E3 →L[ℝ] ℝ) : L (dipoleMoment ρ) = ∫ y, ρ y * L y := by
  rw [dipoleMoment, ← L.integral_comp_comm (integrable_density_smul (g := fun y : E3 => y) hρ hcρ
    continuous_id)]
  simp only [map_smul, smul_eq_mul]

/-- The trace `Σᵢ D²ψ(0)(eᵢ, eᵢ)` is the Laplacian `Δψ(0)`. -/
theorem sum_fderiv_fderiv_single_eq_laplacian {ψ : E3 → ℝ} {x : E3} (hψ : ContDiffAt ℝ 2 ψ x) :
    ∑ i : Fin 3, fderiv ℝ (fderiv ℝ ψ) x (EuclideanSpace.single i 1)
      (EuclideanSpace.single i 1) = Δ ψ x := by
  rw [← coordLaplacian_eq_laplacian hψ, coordLaplacian]
  exact Finset.sum_congr rfl fun i _ => (fderiv_fderiv_apply hψ _ _).symm

/-- **The energy in an external field (§42)**: for a continuous density with its support in the
ball `‖y‖ ≤ a` and an external potential `ψ` of class `C³` on the ball with `Δψ(0) = 0` and
`‖D³ψ‖ ≤ B` there, `∫ρψ = Qψ(0) + ⟪d,∇ψ(0)⟫ + (1/6)Σᵢⱼ Dᵢⱼ∂ᵢ∂ⱼψ(0) + R` with
`|R| ≤ (∫|ρ|‖y‖³)/6 · B`. -/
theorem abs_externalEnergy_sub_le {ρ ψ : E3 → ℝ} (hρ : Continuous ρ) {a B : ℝ} (ha0 : 0 ≤ a)
    (ha : tsupport ρ ⊆ closedBall 0 a) (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 3 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 3 ψ w‖ ≤ B) (hΔ : Δ ψ 0 = 0) :
    |externalEnergy ρ ψ - (totalCharge ρ * ψ 0 + fderiv ℝ ψ 0 (dipoleMoment ρ) +
        1 / 6 * ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j *
          fderiv ℝ (fderiv ℝ ψ) 0 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))| ≤
      (∫ y, |ρ y| * ‖y‖ ^ 3) / 6 * B := by
  have hcρ := hasCompactSupport_of_tsupport_subset ha
  have hψ0 : ContDiffAt ℝ 2 ψ 0 := (hψ 0 (mem_closedBall_self ha0)).of_le (by norm_num)
  set H := fderiv ℝ (fderiv ℝ ψ) 0 with hHdef
  set L := fderiv ℝ ψ 0 with hLdef
  have hquad : 1 / 6 * ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j *
      H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      1 / 2 * ∫ y, ρ y * H y y := by
    rw [sum_quadrupoleMoment_mul hρ hcρ H, hHdef, sum_fderiv_fderiv_single_eq_laplacian hψ0, hΔ]
    ring
  have hiψ : Integrable fun y => ρ y * ψ y :=
    (continuous_smul_of_tsupport_subset hρ ha fun w hw => (hψ w hw).continuousAt
      ).integrable_of_hasCompactSupport hcρ.mul_right
  have hi0 : Integrable fun y => ρ y * ψ 0 := integrable_density_mul hρ hcρ continuous_const
  have hiL : Integrable fun y => ρ y * L y := integrable_density_mul hρ hcρ L.continuous
  have hiH : Integrable fun y => 1 / 2 * (ρ y * H y y) :=
    (integrable_density_mul hρ hcρ (H.continuous.clm_apply continuous_id)).const_mul _
  have e : ∫ y, ρ y * (ψ y - ψ 0 - L y - H y y / 2) = (∫ y, ρ y * ψ y) -
      (∫ y, ρ y * ψ 0) - (∫ y, ρ y * L y) - ∫ y, 1 / 2 * (ρ y * H y y) := by
    have h1 : Integrable fun y => ρ y * ψ y - ρ y * ψ 0 := hiψ.sub hi0
    have h2 : Integrable fun y => ρ y * ψ y - ρ y * ψ 0 - ρ y * L y := h1.sub hiL
    rw [← integral_sub hiψ hi0, ← integral_sub h1 hiL, ← integral_sub h2 hiH]
    congr 1
    funext y
    ring
  have hsplit : externalEnergy ρ ψ - (totalCharge ρ * ψ 0 + L (dipoleMoment ρ) +
      1 / 6 * ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment ρ i j *
        H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) =
      ∫ y, ρ y * (ψ y - ψ 0 - L y - H y y / 2) := by
    rw [hquad, clm_dipoleMoment hρ hcρ, totalCharge_mul, externalEnergy, e, integral_const_mul]
    ring
  rw [hsplit]
  refine (abs_integral_mul_le (m := 3) (c := B / 6) hρ hcρ (fun y hy => ?_)).trans_eq (by ring)
  exact abs_sub_taylor_two_le hψ hB (norm_le_of_ne_zero ha hy)

/-- A vector whose inner products are bounded by `C‖v‖` has the norm at most `C`. -/
theorem norm_le_of_forall_abs_inner_le {w : E3} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v : E3, |⟪w, v⟫| ≤ C * ‖v‖) : ‖w‖ ≤ C := by
  have h1 := h w
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (by positivity)] at h1
  by_cases hw : ‖w‖ = 0
  · rw [hw]
    exact hC
  · have hw' : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw)
    nlinarith

/-- The gradient of a function that is `C¹` at a point is continuous there. -/
theorem continuousAt_gradient {ψ : E3 → ℝ} {w : E3} (hψ : ContDiffAt ℝ 1 ψ w) :
    ContinuousAt (gradient ψ) w := by
  have h : ContinuousAt (fderiv ℝ ψ) w :=
    (hψ.fderiv_right (m := 0) (by norm_num)).continuousAt
  exact (InnerProductSpace.toDual ℝ E3).symm.continuous.continuousAt.comp h

/-- **The force in an external field (§42)**: for a continuous density with its support in the
ball `‖y‖ ≤ a` and an external potential `ψ` of class `C³` on the ball with `‖D³ψ‖ ≤ B` there,
the force is `F = QE(0) + ∇(d·E)(0) + R` with the external field `E = −∇ψ` and
`‖R‖ ≤ (∫|ρ|‖y‖²)/2 · B`. Since `E` is a gradient, `∇(d·E) = (d·∇)E`. -/
theorem norm_externalForce_sub_le {ρ ψ : E3 → ℝ} (hρ : Continuous ρ) {a B : ℝ} (ha0 : 0 ≤ a)
    (ha : tsupport ρ ⊆ closedBall 0 a) (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 3 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 3 ψ w‖ ≤ B) :
    ‖externalForce ρ ψ - (totalCharge ρ • -gradient ψ 0 -
        gradient (fun y => fderiv ℝ ψ y (dipoleMoment ρ)) 0)‖ ≤
      (∫ y, |ρ y| * ‖y‖ ^ 2) / 2 * B := by
  have hcρ := hasCompactSupport_of_tsupport_subset ha
  have hmem0 : (0 : E3) ∈ closedBall (0 : E3) a := mem_closedBall_self ha0
  have hψ0 : ContDiffAt ℝ 2 ψ 0 := (hψ 0 hmem0).of_le (by norm_num)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 hmem0)
  have hA : 0 ≤ ∫ y, |ρ y| * ‖y‖ ^ 2 := integral_nonneg fun y => by positivity
  set H := fderiv ℝ (fderiv ℝ ψ) 0 with hHdef
  set d := dipoleMoment ρ with hd
  have hig : Integrable fun y => ρ y • gradient ψ y :=
    (continuous_smul_of_tsupport_subset hρ ha fun w hw =>
      continuousAt_gradient ((hψ w hw).of_le (by norm_num))
      ).integrable_of_hasCompactSupport hcρ.smul_right
  refine norm_le_of_forall_abs_inner_le (by positivity) fun v => ?_
  have hF : ⟪externalForce ρ ψ, v⟫ = -∫ y, ρ y * fderiv ℝ ψ y v := by
    rw [externalForce, inner_neg_left, real_inner_comm, ← integral_inner hig v]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [inner_smul_right]
    rw [real_inner_comm, inner_gradient_left]
  have hG : ⟪gradient (fun y => fderiv ℝ ψ y d) 0, v⟫ = ∫ y, ρ y * H y v := by
    rw [inner_gradient_left, fderiv_fderiv_apply hψ0,
      (hψ0.isSymmSndFDerivAt (by simp)) v d, hd]
    have := clm_dipoleMoment hρ hcρ ((ContinuousLinearMap.apply ℝ ℝ v).comp H)
    simpa using this
  have hiψ : Integrable fun y => ρ y * fderiv ℝ ψ y v :=
    (continuous_smul_of_tsupport_subset (g := fun y => fderiv ℝ ψ y v) hρ ha fun w hw =>
      ((hψ w hw).fderiv_right (m := 2) (by norm_num)).continuousAt.clm_apply
        continuousAt_const).integrable_of_hasCompactSupport hcρ.mul_right
  have hi0 : Integrable fun y => ρ y * fderiv ℝ ψ 0 v :=
    integrable_density_mul hρ hcρ continuous_const
  have hiH : Integrable fun y => ρ y * H y v :=
    integrable_density_mul hρ hcρ ((H.continuous.clm_apply continuous_const))
  have e : ∫ y, ρ y * (fderiv ℝ ψ y v - fderiv ℝ ψ 0 v - H y v) = (∫ y, ρ y * fderiv ℝ ψ y v) -
      (∫ y, ρ y * fderiv ℝ ψ 0 v) - ∫ y, ρ y * H y v := by
    have h1 : Integrable fun y => ρ y * fderiv ℝ ψ y v - ρ y * fderiv ℝ ψ 0 v := hiψ.sub hi0
    rw [← integral_sub hiψ hi0, ← integral_sub h1 hiH]
    congr 1
    funext y
    ring
  have hQ := totalCharge_mul ρ (fderiv ℝ ψ 0 v)
  have hsplit : ⟪externalForce ρ ψ - (totalCharge ρ • -gradient ψ 0 -
      gradient (fun y => fderiv ℝ ψ y d) 0), v⟫ =
      -∫ y, ρ y * (fderiv ℝ ψ y v - fderiv ℝ ψ 0 v - H y v) := by
    rw [inner_sub_left, inner_sub_left, hF, hG, inner_smul_left, inner_neg_left,
      inner_gradient_left, RCLike.conj_to_real, e, ← hQ]
    ring
  rw [hsplit, abs_neg]
  refine (abs_integral_mul_le (m := 2) (c := B / 2 * ‖v‖) hρ hcρ (fun y hy => ?_)).trans_eq
    (by ring)
  have := abs_fderiv_sub_taylor_one_le hψ hB (norm_le_of_ne_zero ha hy) v
  calc _ ≤ B / 2 * ‖y‖ ^ 2 * ‖v‖ := this
    _ = _ := by ring

/-! ### Instances -/

/-- The bump charge of `ElectrostaticEnergy` is continuous. -/
theorem continuous_bumpCharge : Continuous Electrostatics.bumpCharge :=
  Electrostatics.contDiff_bumpCharge.continuous

/-- The bump charge has its support in the ball of radius `2`. -/
theorem tsupport_bumpCharge : tsupport Electrostatics.bumpCharge ⊆ closedBall 0 2 := by
  rw [show Electrostatics.bumpCharge = ⇑Electrostatics.unitBump from rfl,
    Electrostatics.unitBump.tsupport_eq]
  rfl

/-- The bump charge has a positive total charge. -/
theorem totalCharge_bumpCharge_pos : 0 < totalCharge Electrostatics.bumpCharge :=
  Electrostatics.unitBump.integral_pos

/-- **An instance of the dipole expansion**: the bump charge, with a positive total charge,
satisfies the hypotheses of `abs_newtonPotential_sub_dipole_le` on `‖x‖ > 2`. -/
theorem bumpCharge_dipole_instance :
    0 < totalCharge Electrostatics.bumpCharge ∧ ∀ x : E3, 2 < ‖x‖ →
      |newtonPotential Electrostatics.bumpCharge x -
          totalCharge Electrostatics.bumpCharge / (4 * π * ‖x‖) -
          ⟪dipoleMoment Electrostatics.bumpCharge, x⟫ / (4 * π * ‖x‖ ^ 3)| ≤
        (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ 2) / (4 * π * (‖x‖ - 2) ^ 3) :=
  ⟨totalCharge_bumpCharge_pos, fun _ hx =>
    abs_newtonPotential_sub_dipole_le continuous_bumpCharge tsupport_bumpCharge hx⟩

/-- **An instance of the multipole expansion**: the bump charge satisfies the hypotheses of
`abs_newtonPotential_sub_multipole_le` on `‖x‖ > 2`, at every order. -/
theorem bumpCharge_multipole_instance (n : ℕ) :
    ∃ C, ∀ x : E3, 2 < ‖x‖ →
      |newtonPotential Electrostatics.bumpCharge x -
          ∑ k ∈ Finset.range (n + 1), multipoleTerm Electrostatics.bumpCharge k x| ≤
        C * (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ (n + 1)) / (‖x‖ - 2) ^ (n + 2) := by
  obtain ⟨C, -, hC⟩ := abs_newtonPotential_sub_multipole_le n
  exact ⟨C, fun _ hx => hC continuous_bumpCharge tsupport_bumpCharge hx⟩

/-- A neutral pair: the bump charge at the origin and the opposite bump charge at `c`. -/
def neutralPair (c y : E3) : ℝ := Electrostatics.bumpCharge y - Electrostatics.bumpCharge (y - c)

/-- The neutral pair is continuous. -/
theorem continuous_neutralPair (c : E3) : Continuous (neutralPair c) :=
  continuous_bumpCharge.sub (continuous_bumpCharge.comp (continuous_id.sub continuous_const))

/-- The neutral pair has a compact support. -/
theorem hasCompactSupport_neutralPair (c : E3) : HasCompactSupport (neutralPair c) :=
  Electrostatics.hasCompactSupport_bumpCharge.sub
    (Electrostatics.hasCompactSupport_bumpCharge.comp_homeomorph (Homeomorph.subRight c))

/-- The neutral pair has the total charge `0`. -/
theorem totalCharge_neutralPair (c : E3) : totalCharge (neutralPair c) = 0 := by
  have h1 : Integrable Electrostatics.bumpCharge :=
    continuous_bumpCharge.integrable_of_hasCompactSupport
      Electrostatics.hasCompactSupport_bumpCharge
  rw [totalCharge]
  simp only [neutralPair]
  rw [integral_sub h1 (h1.comp_sub_right c),
    integral_sub_right_eq_self (μ := volume) Electrostatics.bumpCharge c, sub_self]

/-- The neutral pair has the dipole moment `−Qc`, with `Q > 0` the charge of the bump: it is
not zero for `c ≠ 0`. -/
theorem dipoleMoment_neutralPair (c : E3) :
    dipoleMoment (neutralPair c) = -(totalCharge Electrostatics.bumpCharge • c) := by
  have hc := Electrostatics.hasCompactSupport_bumpCharge
  have h1 : Integrable fun y => Electrostatics.bumpCharge y • y :=
    integrable_density_smul (g := fun y : E3 => y) continuous_bumpCharge hc continuous_id
  have h2 : Integrable fun y => Electrostatics.bumpCharge (y + -c) • y :=
    integrable_density_smul (g := fun y : E3 => y)
      (continuous_bumpCharge.comp (continuous_id.add continuous_const))
      (hc.comp_homeomorph (Homeomorph.addRight (-c))) continuous_id
  have ht := dipoleMoment_translate continuous_bumpCharge hc (-c)
  rw [dipoleMoment] at ht ⊢
  simp only [neutralPair, sub_smul, ← sub_eq_add_neg] at ht h2 ⊢
  rw [integral_sub h1 h2, ht, dipoleMoment, smul_neg]
  abel

/-- **An instance of the translation law**: the neutral pair has a vanishing monopole term, so
its dipole term does not depend on the origin. -/
theorem neutralPair_translate_instance (c b : E3) {x : E3} (hx : x ≠ 0) :
    multipoleTerm (fun y => neutralPair c (y + b)) 1 x = multipoleTerm (neutralPair c) 1 x := by
  refine multipoleTerm_translate (continuous_neutralPair c) (hasCompactSupport_neutralPair c)
    (fun j hj y _ => ?_) b hx
  rw [Nat.lt_one_iff.mp hj, multipoleTerm_zero, totalCharge_neutralPair, zero_mul]

/-- The potential `⟪e, y⟫` of a uniform external field `−e`. -/
def uniformFieldPotential (e y : E3) : ℝ := ⟪e, y⟫

/-- The uniform potential is smooth. -/
theorem contDiff_uniformFieldPotential (e : E3) {n : WithTop ℕ∞} :
    ContDiff ℝ n (uniformFieldPotential e) :=
  (innerSL ℝ e).contDiff

/-- The derivative of the uniform potential is the constant form `⟪e, ·⟫`. -/
theorem fderiv_uniformFieldPotential (e : E3) :
    fderiv ℝ (uniformFieldPotential e) = fun _ => innerSL ℝ e := by
  funext w
  exact (innerSL ℝ e).hasFDerivAt.fderiv

/-- The third derivative of the uniform potential vanishes. -/
theorem norm_iteratedFDeriv_three_uniformFieldPotential (e w : E3) :
    ‖iteratedFDeriv ℝ 3 (uniformFieldPotential e) w‖ = 0 := by
  rw [← norm_iteratedFDeriv_fderiv, fderiv_uniformFieldPotential,
    iteratedFDeriv_const_of_ne (by norm_num)]
  simp

/-- The uniform potential is harmonic. -/
theorem laplacian_uniformFieldPotential (e : E3) : Δ (uniformFieldPotential e) 0 = 0 := by
  rw [← sum_fderiv_fderiv_single_eq_laplacian (contDiff_uniformFieldPotential e).contDiffAt,
    fderiv_uniformFieldPotential]
  simp

/-- **An instance of the energy and the force in an external field**: the bump charge in the
uniform potential `⟪e, y⟫` satisfies the hypotheses of `abs_externalEnergy_sub_le` and
`norm_externalForce_sub_le` with `a = 2` and `B = 0`. -/
theorem bumpCharge_external_instance (e : E3) :
    |externalEnergy Electrostatics.bumpCharge (uniformFieldPotential e) -
        (totalCharge Electrostatics.bumpCharge * uniformFieldPotential e 0 +
          fderiv ℝ (uniformFieldPotential e) 0 (dipoleMoment Electrostatics.bumpCharge) +
          1 / 6 * ∑ i : Fin 3, ∑ j : Fin 3, quadrupoleMoment Electrostatics.bumpCharge i j *
            fderiv ℝ (fderiv ℝ (uniformFieldPotential e)) 0 (EuclideanSpace.single i 1)
              (EuclideanSpace.single j 1))| ≤
        (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ 3) / 6 * 0 ∧
    ‖externalForce Electrostatics.bumpCharge (uniformFieldPotential e) -
        (totalCharge Electrostatics.bumpCharge • -gradient (uniformFieldPotential e) 0 -
          gradient (fun y => fderiv ℝ (uniformFieldPotential e) y
            (dipoleMoment Electrostatics.bumpCharge)) 0)‖ ≤
        (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ 2) / 2 * 0 := by
  have hψ : ∀ w ∈ closedBall (0 : E3) 2, ContDiffAt ℝ 3 (uniformFieldPotential e) w :=
    fun _ _ => (contDiff_uniformFieldPotential e).contDiffAt
  have hB : ∀ w ∈ closedBall (0 : E3) 2, ‖iteratedFDeriv ℝ 3 (uniformFieldPotential e) w‖ ≤ 0 :=
    fun w _ => (norm_iteratedFDeriv_three_uniformFieldPotential e w).le
  exact ⟨abs_externalEnergy_sub_le continuous_bumpCharge zero_le_two tsupport_bumpCharge hψ hB
    (laplacian_uniformFieldPotential e),
    norm_externalForce_sub_le continuous_bumpCharge zero_le_two tsupport_bumpCharge hψ hB⟩

/-! ### The torque -/

/-- The cross product `u × v` on space, through the co-ordinates. -/
def cross3 (u v : E3) : E3 := WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

/-- The cross product is additive in the first argument. -/
theorem cross3_add_left (u u' v : E3) : cross3 (u + u') v = cross3 u v + cross3 u' v := by
  simp [cross3]

/-- The cross product is homogeneous in the first argument. -/
theorem cross3_smul_left (c : ℝ) (u v : E3) : cross3 (c • u) v = c • cross3 u v := by
  simp [cross3]

/-- The cross product is additive in the second argument. -/
theorem cross3_sub_right (u v v' : E3) : cross3 u v - cross3 u v' = cross3 u (v - v') := by
  simp [cross3]

/-- **Lagrange's identity**: `‖u × v‖² = ‖u‖²‖v‖² − ⟪u,v⟫²`. -/
theorem norm_cross3_sq (u v : E3) : ‖cross3 u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  simp [cross3, PiLp.inner_apply, Fin.sum_univ_three, cross_apply]
  ring

/-- The cross product is bounded by `‖u × v‖ ≤ ‖u‖‖v‖`. -/
theorem norm_cross3_le (u v : E3) : ‖cross3 u v‖ ≤ ‖u‖ * ‖v‖ := by
  have h : ‖cross3 u v‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    rw [norm_cross3_sq, mul_pow]
    nlinarith [sq_nonneg ⟪u, v⟫]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- The cross product is continuous. -/
theorem continuous_cross3 : Continuous fun p : E3 × E3 => cross3 p.1 p.2 := by
  unfold cross3
  fun_prop

/-- The cross product `u ↦ u × w` as a continuous linear map. -/
def cross3Right (w : E3) : E3 →L[ℝ] E3 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => cross3 u w
      map_add' := fun u u' => cross3_add_left u u' w
      map_smul' := fun c u => cross3_smul_left c u w }

/-- The map `cross3Right w` is `u ↦ u × w`. -/
theorem cross3Right_apply (w u : E3) : cross3Right w u = cross3 u w := rfl

/-- The torque `K = ∫ ρ(y) y × E(y) dy` on a charge density in an external potential `ψ`, with
the external field `E = −∇ψ`. -/
def externalTorque (ρ ψ : E3 → ℝ) : E3 := ∫ y, ρ y • cross3 y (-gradient ψ y)

/-- The variation of the gradient of a function of class `C²` on the ball `‖w‖ ≤ a`:
`‖∇ψ(y) − ∇ψ(0)‖ ≤ B‖y‖` with `B` a bound of `‖D²ψ‖` on the ball. -/
theorem norm_gradient_sub_le {ψ : E3 → ℝ} {a B : ℝ}
    (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 2 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 2 ψ w‖ ≤ B) {y : E3} (hy : ‖y‖ ≤ a) :
    ‖gradient ψ y - gradient ψ 0‖ ≤ B * ‖y‖ := by
  have h := norm_sub_sum_iteratedFDeriv_le (f := fderiv ℝ ψ) (x := 0) (y := y) (n := 0)
    (M := B * ‖y‖)
    (fun t ht => (hψ _ (zero_add_smul_mem_closedBall hy ht)).fderiv_right (m := 0 + 1)
      (by norm_num))
    (fun t ht => by
      refine ((iteratedFDeriv ℝ (0 + 1) (fderiv ℝ ψ) (0 + t • y)).le_opNorm _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [norm_iteratedFDeriv_fderiv, zero_add, pow_one]
      exact mul_le_mul_of_nonneg_right (hB _ (zero_add_smul_mem_closedBall hy ht)) (norm_nonneg y))
  simp only [Finset.range_one, Finset.sum_singleton, iteratedFDeriv_zero_apply,
    Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, zero_add, Nat.factorial_one,
    div_one] at h
  have heq : gradient ψ y - gradient ψ 0 =
      (InnerProductSpace.toDual ℝ E3).symm (fderiv ℝ ψ y - fderiv ℝ ψ 0) := by
    rw [map_sub]
    rfl
  rw [heq, LinearIsometryEquiv.norm_map]
  exact h

/-- **The torque in an external field (§42)**: for a continuous density with its support in the
ball `‖y‖ ≤ a` and an external potential `ψ` of class `C²` on the ball with `‖D²ψ‖ ≤ B` there,
the torque is `K = d × E(0) + R` with the external field `E = −∇ψ` and
`‖R‖ ≤ (∫|ρ|‖y‖²) · B`. -/
theorem norm_externalTorque_sub_le {ρ ψ : E3 → ℝ} (hρ : Continuous ρ) {a B : ℝ}
    (ha : tsupport ρ ⊆ closedBall 0 a) (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 2 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 2 ψ w‖ ≤ B) :
    ‖externalTorque ρ ψ - cross3 (dipoleMoment ρ) (-gradient ψ 0)‖ ≤
      (∫ y, |ρ y| * ‖y‖ ^ 2) * B := by
  have hcρ := hasCompactSupport_of_tsupport_subset ha
  have hi1 : Integrable fun y => ρ y • cross3 y (-gradient ψ y) :=
    (continuous_smul_of_tsupport_subset (g := fun y => cross3 y (-gradient ψ y)) hρ ha
      fun w hw => continuous_cross3.continuousAt.comp (continuousAt_id.prodMk
        (continuousAt_gradient ((hψ w hw).of_le (by norm_num))).neg)
      ).integrable_of_hasCompactSupport hcρ.smul_right
  have hi2 : Integrable fun y => ρ y • cross3 y (-gradient ψ 0) :=
    integrable_density_smul hρ hcρ (continuous_cross3.comp (continuous_id.prodMk continuous_const))
  have hd : cross3 (dipoleMoment ρ) (-gradient ψ 0) = ∫ y, ρ y • cross3 y (-gradient ψ 0) := by
    rw [dipoleMoment, ← cross3Right_apply, ← (cross3Right _).integral_comp_comm
      (integrable_density_smul (g := fun y : E3 => y) hρ hcρ continuous_id)]
    simp only [map_smul, cross3Right_apply]
  rw [externalTorque, hd, ← integral_sub hi1 hi2, ← integral_mul_const]
  refine norm_integral_le_of_norm_le
    ((integrable_density_mul hρ.abs hcρ.abs (continuous_norm.pow 2)).mul_const B)
    (Eventually.of_forall fun y => ?_)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, cross3_sub_right]
  by_cases hy : ρ y = 0
  · simp [hy]
  · have h1 := norm_gradient_sub_le hψ hB (norm_le_of_ne_zero ha hy)
    have hu : ‖-gradient ψ y - -gradient ψ 0‖ = ‖gradient ψ y - gradient ψ 0‖ := by
      rw [show -gradient ψ y - -gradient ψ 0 = -(gradient ψ y - gradient ψ 0) by abel,
        norm_neg]
    have h2 := norm_cross3_le y (-gradient ψ y - -gradient ψ 0)
    rw [hu] at h2
    calc |ρ y| * ‖cross3 y (-gradient ψ y - -gradient ψ 0)‖ ≤ |ρ y| * (‖y‖ * (B * ‖y‖)) :=
          mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)))
            (abs_nonneg _)
      _ = |ρ y| * ‖y‖ ^ 2 * B := by ring

/-- The second derivative of the uniform potential vanishes. -/
theorem norm_iteratedFDeriv_two_uniformFieldPotential (e w : E3) :
    ‖iteratedFDeriv ℝ 2 (uniformFieldPotential e) w‖ = 0 := by
  rw [← norm_iteratedFDeriv_fderiv, fderiv_uniformFieldPotential,
    iteratedFDeriv_const_of_ne (by norm_num)]
  simp

/-- **An instance of the torque in an external field**: the bump charge in the uniform potential
`⟪e, y⟫` satisfies the hypotheses of `norm_externalTorque_sub_le` with `a = 2` and `B = 0`. -/
theorem bumpCharge_torque_instance (e : E3) :
    ‖externalTorque Electrostatics.bumpCharge (uniformFieldPotential e) -
        cross3 (dipoleMoment Electrostatics.bumpCharge) (-gradient (uniformFieldPotential e) 0)‖ ≤
      (∫ y, |Electrostatics.bumpCharge y| * ‖y‖ ^ 2) * 0 :=
  norm_externalTorque_sub_le continuous_bumpCharge tsupport_bumpCharge
    (fun _ _ => (contDiff_uniformFieldPotential e).contDiffAt)
    (fun w _ => (norm_iteratedFDeriv_two_uniformFieldPotential e w).le)

/-! ### The interaction of two dipoles -/

/-- The evaluation `L ↦ L v` has the norm at most `‖v‖`. -/
theorem norm_apply_le (v : E3) : ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun L => by
    rw [ContinuousLinearMap.apply_apply, mul_comm]
    exact L.le_opNorm v

/-- Away from the origin the dipole potential agrees near `w` with `x ↦ DK(x)(−d)`. -/
theorem dipolePotential_eventuallyEq {d w : E3} (hw : w ≠ 0) :
    dipolePotential d =ᶠ[𝓝 w] fun x => fderiv ℝ newtonKernel x (-d) := by
  filter_upwards [eventually_ne_nhds hw] with x hx using dipolePotential_eq hx

/-- The dipole potential is smooth away from the origin. -/
theorem contDiffAt_dipolePotential (d : E3) {w : E3} (hw : w ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (dipolePotential d) w := by
  have h : ContDiffAt ℝ n (fun x => fderiv ℝ newtonKernel x (-d)) w :=
    ((contDiffAt_newtonKernel hw (n := ω)).fderiv_right (m := n) le_top).clm_apply
      contDiffAt_const
  exact h.congr_of_eventuallyEq (dipolePotential_eventuallyEq hw)

/-- **The second derivative of the dipole potential**: there is a constant `C` with
`‖D²φ_d(w)‖ ≤ C‖d‖/‖w‖⁴` away from the origin. -/
theorem norm_iteratedFDeriv_two_dipolePotential_le :
    ∃ C, 0 ≤ C ∧ ∀ d w : E3, w ≠ 0 →
      ‖iteratedFDeriv ℝ 2 (dipolePotential d) w‖ ≤ C * ‖d‖ / ‖w‖ ^ 4 := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_newtonKernel_le 3
  refine ⟨C, hC0, fun d w hw => ?_⟩
  have hK := contDiffAt_newtonKernel hw (n := ω)
  have heq : iteratedFDeriv ℝ 2 (dipolePotential d) w =
      iteratedFDeriv ℝ 2 (fun x => fderiv ℝ newtonKernel x (-d)) w :=
    ((dipolePotential_eventuallyEq hw).iteratedFDeriv ℝ 2).eq_of_nhds
  rw [heq]
  change ‖iteratedFDeriv ℝ 2 (⇑(ContinuousLinearMap.apply ℝ ℝ (-d)) ∘
    fderiv ℝ newtonKernel) w‖ ≤ _
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ (hK.fderiv_right (m := 2) le_top) le_rfl]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  calc ‖ContinuousLinearMap.apply ℝ ℝ (-d)‖ * ‖iteratedFDeriv ℝ (2 + 1) newtonKernel w‖
      ≤ ‖d‖ * (C / ‖w‖ ^ (3 + 1)) :=
        mul_le_mul ((norm_apply_le (-d)).trans (norm_neg d).le) (hC w hw) (norm_nonneg _)
          (norm_nonneg _)
    _ = C * ‖d‖ / ‖w‖ ^ 4 := by ring

/-- Taylor's formula to the first order for a function of class `C²` on the ball `‖w‖ ≤ a`
about the origin: `|ψ(y) − ψ(0) − Dψ(0)y| ≤ (B/2)‖y‖²` with `B` a bound of `‖D²ψ‖` on the
ball. -/
theorem abs_sub_taylor_one_le {ψ : E3 → ℝ} {a B : ℝ}
    (hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 2 ψ w)
    (hB : ∀ w ∈ closedBall (0 : E3) a, ‖iteratedFDeriv ℝ 2 ψ w‖ ≤ B) {y : E3} (hy : ‖y‖ ≤ a) :
    |ψ y - ψ 0 - fderiv ℝ ψ 0 y| ≤ B / 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_sum_iteratedFDeriv_le (f := ψ) (x := 0) (y := y) (n := 1)
    (M := B * ‖y‖ ^ 2) (fun t ht => hψ _ (zero_add_smul_mem_closedBall hy ht))
    (fun t ht => by
      refine ((iteratedFDeriv ℝ (1 + 1) ψ (0 + t • y)).le_opNorm _).trans ?_
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact mul_le_mul_of_nonneg_right (hB _ (zero_add_smul_mem_closedBall hy ht))
        (by positivity))
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    iteratedFDeriv_zero_apply, iteratedFDeriv_one_apply, smul_eq_mul, Real.norm_eq_abs,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, inv_one, one_mul] at h
  calc _ = |ψ y - (ψ 0 + fderiv ℝ ψ 0 y)| := by ring_nf
    _ ≤ B * ‖y‖ ^ 2 / ↑(1 + 1)! := h
    _ = _ := by
        rw [show (1 + 1)! = 2 from rfl, Nat.cast_ofNat]
        ring

/-- The interaction energy `(⟪d₁,d₂⟫ − 3⟪n,d₁⟫⟪n,d₂⟫)/(4π‖R‖³)` of two point dipoles at the
separation `R`, with `n = R/‖R‖`. -/
def dipoleInteraction (d₁ d₂ R : E3) : ℝ :=
  (⟪d₁, d₂⟫ - 3 * ⟪‖R‖⁻¹ • R, d₁⟫ * ⟪‖R‖⁻¹ • R, d₂⟫) / (4 * π * ‖R‖ ^ 3)

/-- The energy of a point dipole `d₂` in the field of a point dipole `d₁` at the separation
`R`: `Dφ_{d₁}(R) d₂ = −⟪E_{d₁}(R), d₂⟫` is the interaction energy. -/
theorem fderiv_dipolePotential_apply (d₁ d₂ : E3) {R : E3} (hR : R ≠ 0) :
    fderiv ℝ (dipolePotential d₁) R d₂ = dipoleInteraction d₁ d₂ R := by
  have hR' : 0 < ‖R‖ := norm_pos_iff.mpr hR
  rw [(hasGradientAt_dipolePotential d₁ hR).fderiv_apply, dipoleField, dipoleInteraction]
  simp only [inner_neg_left, inner_smul_left, inner_sub_left, RCLike.conj_to_real]
  field_simp
  ring

/-- **The interaction of two dipoles (§41, §42)**: for a neutral continuous density with its
support in the ball `‖y‖ ≤ a` and the field of a point dipole `d₁` at `−R`, the energy is the
dipole–dipole interaction `(⟪d₁,d₂⟫ − 3⟪n,d₁⟫⟪n,d₂⟫)/(4π‖R‖³)` with `d₂` the dipole moment of
the density, up to `C‖d₁‖(∫|ρ|‖y‖²)/(‖R‖ − a)⁴` with a universal constant `C`. -/
theorem abs_externalEnergy_dipolePotential_sub_le :
    ∃ C, 0 ≤ C ∧ ∀ {ρ : E3 → ℝ}, Continuous ρ → ∀ {a : ℝ}, 0 ≤ a →
      tsupport ρ ⊆ closedBall 0 a → totalCharge ρ = 0 → ∀ d₁ R : E3, a < ‖R‖ →
        |externalEnergy ρ (fun y => dipolePotential d₁ (y + R)) -
            dipoleInteraction d₁ (dipoleMoment ρ) R| ≤
          C * ‖d₁‖ * (∫ y, |ρ y| * ‖y‖ ^ 2) / (‖R‖ - a) ^ 4 := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_two_dipolePotential_le
  refine ⟨C / 2, by positivity, fun {ρ} hρ {a} ha0 ha hQ d₁ R hR => ?_⟩
  have hcρ := hasCompactSupport_of_tsupport_subset ha
  have hd : 0 < ‖R‖ - a := by linarith
  have hR0 : R ≠ 0 := norm_pos_iff.mp (ha0.trans_lt hR)
  set ψ : E3 → ℝ := fun y => dipolePotential d₁ (y + R) with hψdef
  have hfar : ∀ w ∈ closedBall (0 : E3) a, ‖R‖ - a ≤ ‖w + R‖ := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    have := norm_sub_norm_le R (-w)
    rw [sub_neg_eq_add, norm_neg, add_comm R w] at this
    linarith
  have hne : ∀ w ∈ closedBall (0 : E3) a, w + R ≠ 0 := fun w hw =>
    norm_pos_iff.mp (hd.trans_le (hfar w hw))
  have hψ : ∀ w ∈ closedBall (0 : E3) a, ContDiffAt ℝ 2 ψ w := fun w hw =>
    (contDiffAt_dipolePotential d₁ (hne w hw)).comp w (contDiffAt_id.add contDiffAt_const)
  have hB : ∀ w ∈ closedBall (0 : E3) a,
      ‖iteratedFDeriv ℝ 2 ψ w‖ ≤ C * ‖d₁‖ / (‖R‖ - a) ^ 4 := by
    intro w hw
    rw [hψdef, iteratedFDeriv_comp_add_right]
    refine (hC d₁ _ (hne w hw)).trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hd.le (hfar w hw) 4)
  have hiψ : Integrable fun y => ρ y * ψ y :=
    (continuous_smul_of_tsupport_subset hρ ha fun w hw => (hψ w hw).continuousAt
      ).integrable_of_hasCompactSupport hcρ.mul_right
  have hi0 : Integrable fun y => ρ y * ψ 0 := integrable_density_mul hρ hcρ continuous_const
  have hiL : Integrable fun y => ρ y * fderiv ℝ ψ 0 y :=
    integrable_density_mul hρ hcρ (fderiv ℝ ψ 0).continuous
  have hlin : fderiv ℝ ψ 0 (dipoleMoment ρ) = dipoleInteraction d₁ (dipoleMoment ρ) R := by
    rw [hψdef, fderiv_comp_add_right, zero_add, fderiv_dipolePotential_apply _ _ hR0]
  have hsplit : externalEnergy ρ ψ - dipoleInteraction d₁ (dipoleMoment ρ) R =
      ∫ y, ρ y * (ψ y - ψ 0 - fderiv ℝ ψ 0 y) := by
    have h1 : Integrable fun y => ρ y * ψ y - ρ y * ψ 0 := hiψ.sub hi0
    rw [← hlin, clm_dipoleMoment hρ hcρ, externalEnergy,
      show (∫ y, ρ y * (ψ y - ψ 0 - fderiv ℝ ψ 0 y)) =
        ∫ y, ρ y * ψ y - ρ y * ψ 0 - ρ y * fderiv ℝ ψ 0 y by
        congr 1
        funext y
        ring,
      integral_sub h1 hiL, integral_sub hiψ hi0, ← totalCharge_mul, hQ]
    ring
  rw [hsplit]
  refine (abs_integral_mul_le (m := 2) (c := C * ‖d₁‖ / (‖R‖ - a) ^ 4 / 2) hρ hcρ
    (fun y hy => ?_)).trans_eq (by ring)
  exact abs_sub_taylor_one_le hψ hB (norm_le_of_ne_zero ha hy)

/-- The neutral pair has its support in the ball of radius `2 + ‖c‖`. -/
theorem tsupport_neutralPair (c : E3) : tsupport (neutralPair c) ⊆ closedBall 0 (2 + ‖c‖) := by
  have h1 : tsupport Electrostatics.bumpCharge ⊆ closedBall 0 (2 + ‖c‖) :=
    tsupport_bumpCharge.trans (closedBall_subset_closedBall (by linarith [norm_nonneg c]))
  have h2 : tsupport (fun y => Electrostatics.bumpCharge (y - c)) ⊆ closedBall 0 (2 + ‖c‖) := by
    have := tsupport_translate_subset tsupport_bumpCharge (-c)
    simpa [← sub_eq_add_neg] using this
  exact (tsupport_sub _ _).trans (union_subset h1 h2)

/-- **An instance of the dipole–dipole interaction**: the neutral pair satisfies the
hypotheses of `abs_externalEnergy_dipolePotential_sub_le` with `a = 2 + ‖c‖`. -/
theorem neutralPair_dipole_dipole_instance (c : E3) :
    ∃ C, ∀ d₁ R : E3, 2 + ‖c‖ < ‖R‖ →
      |externalEnergy (neutralPair c) (fun y => dipolePotential d₁ (y + R)) -
          dipoleInteraction d₁ (dipoleMoment (neutralPair c)) R| ≤
        C * ‖d₁‖ * (∫ y, |neutralPair c y| * ‖y‖ ^ 2) / (‖R‖ - (2 + ‖c‖)) ^ 4 := by
  obtain ⟨C, -, hC⟩ := abs_externalEnergy_dipolePotential_sub_le
  exact ⟨C, fun d₁ R hR => hC (continuous_neutralPair c) (by positivity) (tsupport_neutralPair c)
    (totalCharge_neutralPair c) d₁ R hR⟩

end ProjectAinos.Electrodynamics.Multipole
