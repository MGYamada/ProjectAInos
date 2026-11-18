/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinHilbert
public import ProjectAinos.SmoothGeometry.Lorentzian.ExponentialConformalExample
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The Einstein–Hilbert action

The action of the gravitational field (Landau–Lifshitz, §93, with `c = 1` and the signature
`(−+++)`) is `S = (1/2κ) ∫ (R − 2Λ) √|g| d⁴x` with `κ = 8πG`. A metric is given by its
coefficients on an open set `U` of `ℝ⁴`, and a variation `g + εh` by a smooth symmetric `h` with
compact support in `U`. The action of a region that is not compact need not converge, so we
differentiate the relative action `ΔS(ε) = S[g + εh] − S[g]`, the integral of the difference of
the densities, which vanishes off the support of `h`.

* `eventually_relativeAction_integrand`: for every `ε` near `0` the form `g + εh` is a Lorentz
  metric on `U`, and the integrand of `ΔS` is the difference of the native Lagrangians
  `(R − 2Λ) √|g| / 2κ` of `g + εh` and of `g`.
* `hasDerivAt_relativeAction`: `ΔS'(0) = (1/2κ) ∫ (G_{ik} + Λ g_{ik}) δg^{ik} √|g| d⁴x`, with the
  Einstein tensor `G_{ik} = R_{ik} − ½ R g_{ik}` and `δg^{ik} = −g^{im} h_{mn} g^{nk}`. The term
  `g^{ik} δR_{ik} √|g|` is the divergence `∂_a(√|g| V^a)` of a field with compact support and
  drops out.
* `integrand_eq_native`: in the integrand, `G_{ik}`, `g_{ik}` and `√|g|` are the native Einstein
  tensor, metric and density on the co-ordinate fields.
* `hasDerivAt_relativeAction_flat`: for the Minkowski metric and `h = f η`,
  `ΔS'(0) = −(2Λ/κ) ∫ f`; for a bump function `f` it is not zero when `Λ ≠ 0`
  (`exists_deriv_relativeAction_flat_ne_zero`).
* `hasDerivAt_relativeAction_conformal`: for the curved metric `e^{2z} η` of
  `ExponentialConformalExample` and `h = f η`, `ΔS'(0) = −(1/2κ) ∫ f (6 + 4Λ e^{2z})`; the `6` is
  `η^{ik} G_{ik}`, and for a bump function the derivative is not zero even when `Λ = 0`
  (`exists_deriv_relativeAction_conformal_ne_zero`).
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EinsteinHilbert

open SmoothGeometry CoordinateMetric
open LorentzMetric (chartField)

variable {U : Opens (MinkowskiModel 3)}

/-- The Einstein–Hilbert Lagrangian density `(R − 2Λ) √|g| / 2κ` at a point of `U`, in the
co-ordinates of `U`. -/
def lagrangian (g : CoordinateMetric .timeNegative 3 U) (κ Λ : ℝ) (y : U) : ℝ :=
  (2 * κ)⁻¹ * ((g.toLorentzMetric.scalarCurvature y - 2 * Λ) *
    g.toLorentzMetric.chartDensity (physicalChart y) y)

variable (g : CoordinateMetric .timeNegative 3 U)
  (h : MinkowskiModel 3 → MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ)

/-- The relative action `ΔS(ε) = S[g + εh] − S[g]`. -/
def relativeAction (κ Λ ε : ℝ) : ℝ :=
  (2 * κ)⁻¹ * ∫ x, (g.scalarDensity h Λ (ε, x) - g.scalarDensity h Λ (0, x))

@[simp] theorem relativeAction_zero (κ Λ : ℝ) : relativeAction g h κ Λ 0 = 0 := by
  simp [relativeAction]

variable {g h}

/-- For an admissible `ε` the integrand at a point of `U` is the difference of the
Lagrangians. -/
theorem relativeAction_integrand (hh : ContDiffOn ℝ ∞ h U) {ε : ℝ} (hε : g.IsAdmissible h ε)
    (κ Λ : ℝ) (y : U) :
    (2 * κ)⁻¹ * (g.scalarDensity h Λ (ε, y) - g.scalarDensity h Λ (0, y)) =
      lagrangian (g.addVariation h hh ε hε) κ Λ y - lagrangian g κ Λ y := by
  rw [scalarDensity_eq_toLorentzMetric hh hε, scalarDensity_zero_eq_toLorentzMetric, lagrangian,
    lagrangian, mul_sub]

/-- Off the support of `h` the integrand vanishes. -/
theorem relativeAction_integrand_of_notMem {x : MinkowskiModel 3} (hx : x ∉ tsupport h)
    (Λ ε : ℝ) : g.scalarDensity h Λ (ε, x) - g.scalarDensity h Λ (0, x) = 0 := by
  rw [scalarDensity_of_notMem Λ hx ε, sub_self]

/-- Near `ε = 0` every `g + εh` is a Lorentz metric, and `ΔS` integrates the difference of the
Lagrangians. -/
theorem eventually_relativeAction_integrand (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h)
    (hKU : tsupport h ⊆ U) (hs : ∀ z v w, h z v w = h z w v) (κ Λ : ℝ) :
    ∀ᶠ ε in 𝓝 0, ∃ hε : g.IsAdmissible h ε, ∀ y : U,
      (2 * κ)⁻¹ * (g.scalarDensity h Λ (ε, y) - g.scalarDensity h Λ (0, y)) =
        lagrangian (g.addVariation h hh.contDiffOn ε hε) κ Λ y - lagrangian g κ Λ y :=
  (g.eventually_isAdmissible hh.continuous hK hKU hs).mono fun _ hε =>
    ⟨hε, relativeAction_integrand hh.contDiffOn hε κ Λ⟩

/-- **The first variation of the Einstein–Hilbert action.** For a smooth symmetric variation `h`
with compact support in `U`,
`ΔS'(0) = (1/2κ) ∫ (G_{ik} + Λ g_{ik}) δg^{ik} √|g| d⁴x`. -/
theorem hasDerivAt_relativeAction (hh : ContDiff ℝ ∞ h) (hK : HasCompactSupport h)
    (hKU : tsupport h ⊆ U) (hs : ∀ z v w, h z v w = h z w v) (κ Λ : ℝ) :
    HasDerivAt (relativeAction g h κ Λ)
      ((2 * κ)⁻¹ * ∫ x, (∑ i, ∑ k, (einsteinOf g.coefficient x i k +
        Λ * g.coefficient x i k) * g.inverseVariation h x i k) * densityOf g.coefficient x) 0 := by
  have hd := (g.hasDerivAt_integral_scalarDensity hh hK hKU hs Λ).const_mul (2 * κ)⁻¹
  simp_rw [g.eulerLagrangeDensity_eq hKU Λ] at hd
  exact hd

/-- In the integrand, `G_{ik}`, `g_{ik}` and `√|g|` are the native Einstein tensor, metric and
density on the co-ordinate fields. -/
theorem integrand_eq_native (Λ : ℝ) (y : U) :
    (∑ i, ∑ k, (einsteinOf g.coefficient y i k + Λ * g.coefficient y i k) *
      g.inverseVariation h y i k) * densityOf g.coefficient y =
    (∑ i, ∑ k, (g.toLorentzMetric.einstein y (chartField (physicalChart y) (Pi.single i 1) y)
      (chartField (physicalChart y) (Pi.single k 1) y) +
      Λ * g.toLorentzMetric.chartComponent (physicalChart y) y i k) *
      g.inverseVariation h y i k) * g.toLorentzMetric.chartDensity (physicalChart y) y := by
  simp only [toLorentzMetric_einstein_chartField, toLorentzMetric_chartComponent,
    toLorentzMetric_chartDensity]
  rfl

/-! ### The flat metric with a cosmological constant -/

section Flat

local notation "η₄" => CoordinateMetric.minkowski LorentzConvention.timeNegative 3 ⊤

/-- The variation `h = f η` of the Minkowski metric. -/
def flatVariation (f : MinkowskiModel 3 → ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
  f x • minkowskiForm .timeNegative 3

variable {f : MinkowskiModel 3 → ℝ}

theorem contDiff_flatVariation (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (flatVariation f) := by
  refine contDiff_clm_apply_iff.mpr fun v => contDiff_clm_apply_iff.mpr fun w => ?_
  simp only [flatVariation, smul_apply, smul_eq_mul]
  exact hf.mul contDiff_const

theorem hasCompactSupport_flatVariation (hfK : HasCompactSupport f) :
    HasCompactSupport (flatVariation f) := hfK.mono fun x hx hfx => hx (by
  ext v w
  simp [flatVariation, hfx])

theorem flatVariation_symm (z v w : MinkowskiModel 3) :
    flatVariation f z v w = flatVariation f z w v := by
  simp [flatVariation, minkowskiForm_symmetric .timeNegative v w]

theorem formCoeff_flatVariation (x : MinkowskiModel 3) :
    formCoeff (flatVariation f) x = f x • Matrix.diagonal (lorentzSign .timeNegative) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [formCoeff, flatVariation, minkowskiForm_apply, Pi.single_apply]
  · simp [formCoeff, flatVariation, minkowskiForm_apply, Pi.single_apply, hij, Ne.symm hij]

/-- For the Minkowski metric, `G = 0`, `√|η| = 1` and `η_{ik} η^{ik} = 4`: the integrand is
`−4Λ f`. -/
theorem flat_integrand (Λ : ℝ) (x : MinkowskiModel 3) :
    (∑ i, ∑ k, (einsteinOf (η₄).coefficient x i k + Λ * (η₄).coefficient x i k) *
      (η₄).inverseVariation (flatVariation f) x i k) * densityOf (η₄).coefficient x =
      -(4 * Λ * f x) := by
  have hF : formCoeff (flatVariation f) x = f x • (η₄).coefficient x := by
    ext i j
    simp [formCoeff, flatVariation, coefficient, CoordinateMetric.minkowski]
  have hC : (η₄).coefficient = fun _ => Matrix.diagonal (lorentzSign .timeNegative) :=
    funext minkowski_coefficient
  have hDD : Matrix.diagonal (lorentzSign .timeNegative) *
      Matrix.diagonal (lorentzSign .timeNegative) = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [lorentzSign_sq, Matrix.diagonal_one]
  have hinv : (Matrix.diagonal (lorentzSign .timeNegative))⁻¹ =
      Matrix.diagonal (lorentzSign (d := 3) .timeNegative) :=
    Matrix.inv_eq_left_inv hDD
  unfold inverseVariation
  rw [hF, hC]
  simp only [hinv, Matrix.mul_smul, Matrix.smul_mul, hDD, Matrix.one_mul, einsteinOf_const,
    zero_add]
  have hdet : densityOf (fun _ : MinkowskiModel 3 =>
      Matrix.diagonal (lorentzSign (d := 3) .timeNegative)) x = 1 := by
    simp [densityOf, Matrix.det_diagonal, lorentzSign,
      LorentzConvention.timeSign]
  rw [hdet, mul_one]
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp [Fin.sum_univ_four, lorentzSign, LorentzConvention.timeSign]
  ring

/-- For the Minkowski metric and `h = f η`, `ΔS'(0) = −(2Λ/κ) ∫ f`. -/
theorem hasDerivAt_relativeAction_flat (hf : ContDiff ℝ ∞ f) (hfK : HasCompactSupport f)
    (κ Λ : ℝ) :
    HasDerivAt (relativeAction (η₄) (flatVariation f) κ Λ)
      (-(2 * Λ / κ) * ∫ x, f x) 0 := by
  have hKU : tsupport (flatVariation f) ⊆ (⊤ : Opens (MinkowskiModel 3)) := fun _ _ => by simp
  convert hasDerivAt_relativeAction (contDiff_flatVariation hf)
    (hasCompactSupport_flatVariation hfK) hKU flatVariation_symm κ Λ using 1
  simp_rw [flat_integrand]
  rw [integral_neg, integral_const_mul]
  ring

/-- The first variation is not zero for a bump function when `Λ ≠ 0`. -/
theorem exists_deriv_relativeAction_flat_ne_zero {κ Λ : ℝ} (hκ : κ ≠ 0) (hΛ : Λ ≠ 0) :
    ∃ f : MinkowskiModel 3 → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      deriv (relativeAction (η₄) (flatVariation f) κ Λ) 0 ≠ 0 := by
  let b : ContDiffBump (0 : MinkowskiModel 3) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_⟩
  rw [(hasDerivAt_relativeAction_flat b.contDiff b.hasCompactSupport κ Λ).deriv]
  have hI : 0 < ∫ x, b x := b.integral_pos
  exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (mul_ne_zero two_ne_zero hΛ) hκ)) hI.ne'

end Flat

/-! ### The curved metric `e^{2z} η` -/

section Conformal

local notation "D" => Matrix.diagonal (lorentzSign (d := 3) LorentzConvention.timeNegative)
local notation "gc" => ExponentialConformalExample.metric

variable {f : MinkowskiModel 3 → ℝ}

theorem conformal_coefficient (y : MinkowskiModel 3) :
    (gc).coefficient y = Real.exp (2 * y 3) • D := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [coefficient, ExponentialConformalExample.metric, ExponentialConformalExample.form_apply,
      minkowskiForm_apply, Pi.single_apply]
  · simp [coefficient, ExponentialConformalExample.metric, ExponentialConformalExample.form_apply,
      minkowskiForm_apply, Pi.single_apply, hij, Ne.symm hij]

/-- The Einstein tensor `G_{ik} = 2 δ_{i3} δ_{k3} + η_{ik}` of `e^{2z} η`. -/
theorem conformal_einsteinOf (y : MinkowskiModel 3) (i k : Fin 4) :
    einsteinOf (gc).coefficient y i k =
      2 * ((Pi.single i 1 : MinkowskiModel 3) 3 * (Pi.single k 1 : MinkowskiModel 3) 3) +
        D i k := by
  have h := (toLorentzMetric_einstein_chartField (g := gc) ⟨y, by simp⟩ ⟨y, by simp⟩ i k).symm.trans
    (ExponentialConformalExample.metric_einstein_chartField ⟨y, by simp⟩ ⟨y, by simp⟩ _ _)
  rw [h]
  congr 1
  by_cases hik : i = k
  · subst hik
    simp [minkowskiForm_apply, Pi.single_apply]
  · simp [minkowskiForm_apply, Pi.single_apply, hik, Ne.symm hik]

/-- For `e^{2z} η` and `h = f η`, the integrand is `−f (6 + 4Λ e^{2z})`. -/
theorem conformal_integrand (Λ : ℝ) (x : MinkowskiModel 3) :
    (∑ i, ∑ k, (einsteinOf (gc).coefficient x i k + Λ * (gc).coefficient x i k) *
      (gc).inverseVariation (flatVariation f) x i k) * densityOf (gc).coefficient x =
      -(f x * (6 + 4 * Λ * Real.exp (2 * x 3))) := by
  have hDD : D * D = (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [lorentzSign_sq, Matrix.diagonal_one]
  have hexp : Real.exp (-(2 * x 3)) * Real.exp (2 * x 3) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hinv : (Real.exp (2 * x 3) • D)⁻¹ = Real.exp (-(2 * x 3)) • D := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, hDD, smul_smul, hexp, one_smul]
  have hdens : densityOf (gc).coefficient x = Real.exp (4 * x 3) := by
    rw [densityOf, conformal_coefficient, Matrix.det_smul, Matrix.det_diagonal]
    have h4 : Real.exp (2 * x 3) ^ Fintype.card (Fin 4) = Real.exp (4 * x 3) ^ 2 := by
      rw [Fintype.card_fin, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      ring_nf
    rw [h4]
    simp [lorentzSign, LorentzConvention.timeSign, Real.sqrt_sq (Real.exp_pos _).le]
  have h4 : Real.exp (-(2 * x 3)) * Real.exp (-(2 * x 3)) * Real.exp (4 * x 3) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  unfold inverseVariation
  rw [hdens, formCoeff_flatVariation, conformal_coefficient, hinv]
  simp only [conformal_einsteinOf, Matrix.smul_mul, Matrix.mul_smul, hDD, smul_smul,
    Matrix.smul_apply, smul_eq_mul]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, lorentzSign, LorentzConvention.timeSign,
    Pi.single_apply]
  linear_combination (-(f x * (6 + 4 * Λ * Real.exp (2 * x 3)))) * h4

/-- For `e^{2z} η` and `h = f η`, `ΔS'(0) = −(1/2κ) ∫ f (6 + 4Λ e^{2z})`. -/
theorem hasDerivAt_relativeAction_conformal (hf : ContDiff ℝ ∞ f) (hfK : HasCompactSupport f)
    (κ Λ : ℝ) :
    HasDerivAt (relativeAction (gc) (flatVariation f) κ Λ)
      (-(2 * κ)⁻¹ * ∫ x, f x * (6 + 4 * Λ * Real.exp (2 * x 3))) 0 := by
  have hKU : tsupport (flatVariation f) ⊆ (⊤ : Opens (MinkowskiModel 3)) := fun _ _ => by simp
  convert hasDerivAt_relativeAction (contDiff_flatVariation hf)
    (hasCompactSupport_flatVariation hfK) hKU flatVariation_symm κ Λ using 1
  simp_rw [conformal_integrand]
  rw [integral_neg]
  ring

/-- Without a cosmological constant the first variation at `e^{2z} η` is `−(3/κ) ∫ f`, which is
not zero for a bump function: the Einstein tensor contributes. -/
theorem exists_deriv_relativeAction_conformal_ne_zero {κ : ℝ} (hκ : κ ≠ 0) :
    ∃ f : MinkowskiModel 3 → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      deriv (relativeAction (gc) (flatVariation f) κ 0) 0 ≠ 0 := by
  let b : ContDiffBump (0 : MinkowskiModel 3) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨b, b.contDiff, b.hasCompactSupport, ?_⟩
  rw [(hasDerivAt_relativeAction_conformal b.contDiff b.hasCompactSupport κ 0).deriv]
  have hI : 0 < ∫ x, b x := b.integral_pos
  simp only [mul_zero, zero_mul, add_zero]
  rw [integral_mul_const]
  exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero two_ne_zero hκ)))
    (mul_ne_zero hI.ne' (by norm_num))

end Conformal

end ProjectAinos.GeneralRelativity.EinsteinHilbert
