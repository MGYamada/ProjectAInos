/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildExterior
public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinEquation
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFrameCriterion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Kerr field

In the Boyer–Lindquist co-ordinates `(t, r, χ, φ)` with `χ = cos θ`, signature `(−, +, +, +)`
and `G = c = 1`, the field of a mass `M` with the angular momentum `Ma` is (Landau–Lifshitz,
§104, (104.1))
`ds² = −(1 − 2Mr/Σ) dt² − (4Mar(1 − χ²)/Σ) dt dφ + (Σ/Δ) dr² + (Σ/(1 − χ²)) dχ²
+ (r² + a² + 2Ma²r(1 − χ²)/Σ)(1 − χ²) dφ²`, with `Σ = r² + a²χ²` and `Δ = r² − 2Mr + a²`.
The co-ordinate `χ` makes every coefficient a rational function. The domain is `r > r₊`,
`−1 < χ < 1`, with the outer horizon `r₊ = M + √(M² − a²)`: the region outside the outer
horizon, off the axis; the angle `φ` is read on the real line.

* `metric`: for `M > 0` and `a² ≤ M²` the form is a Lorentz metric on the domain. Since `g_tt`
  changes sign in the ergoregion, the signature is checked in the frame `e₀ + ω e₃`, `e₁`, `e₂`,
  `e₃` with `ω = −g_tφ/g_φφ` (`pointFrame`), on which the form is
  `diag(−Δ(1 − χ²)/g_φφ, g_rr, g_χχ, g_φφ)`.
* `christoffelOf_eq`: the Christoffel symbols are the table `christoffelTable` of twenty
  independent rational functions, certified by their lowered identities.
* `ricciOf_eq_zero`, `ricci_eq_zero`, `isEinstein_zero`, `satisfiesEinstein_zero`: **the Kerr
  field is a vacuum solution**, `R_{ik} = 0` on the whole domain, in the co-ordinates and for the
  native Ricci tensor.
* `isKillingField_time`, `isKillingField_angle`: `∂_t` and `∂_φ` are Killing fields.
* `ergoregion_iff`, `ergoregion_nonempty`: on the domain `g_tt > 0` exactly where
  `r² − 2Mr + a²χ² < 0`; for `a ≠ 0` this ergoregion is not empty (on the equator it is
  `r₊ < r < 2M`).
* `form_rotating_neg_iff`, `omegaMinus_pos`: the world line `φ = Ωt + const` at fixed `r` and `χ`
  is timelike exactly for `Ω₋ < Ω < Ω₊`; in the ergoregion `Ω₋ > 0` for `a > 0`, so that no
  observer is at rest and every stationary observer rotates with the source.
* `tendsto_omegaPlus`, `tendsto_omegaMinus`: as `r → r₊` both ends of the window tend to the
  angular velocity of the horizon `Ω_H = a/(r₊² + a²)`.
* `inverse_rr`, `tendsto_inverse_rr`: `g^{rr} = Δ/Σ`, which tends to `0` as `r → r₊`.
* `form_zero_toAngle`: for `a = 0` the form is the exterior Schwarzschild form pulled back by
  `(t, r, χ, φ) ↦ (t, r, arccos χ, φ)`, whose derivative is `toAngleDeriv`
  (`hasFDerivAt_toAngle`).

The Ricci tensor is computed from the table (`ChristoffelCertificate`): the lowered identities,
the partial derivatives of the twenty symbols and the components of the Ricci formula are
rational identities in `r`, `χ`, `M`, `a`, proved by `field_simp` and `ring` with `Σ` and `Δ`
kept as atoms. These private lemmas were generated with SymPy. Not covered here: the region
`r ≤ r₊`, the axis `χ = ±1`, the extension across the horizon and the motion in the field.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.Kerr

open SmoothGeometry Minkowski
open LorentzMetric (chartField)
open CoordinateMetric (physicalChart christoffelOf ricciOf ricciOfChristoffel scalarOf einsteinOf)

variable {M a : ℝ}

/-! ### The functions `Σ`, `Δ` and the outer horizon -/

/-- The function `Σ = r² + a²χ²` of the Kerr metric. -/
def sig (a r c : ℝ) : ℝ := r ^ 2 + a ^ 2 * c ^ 2

/-- The function `Δ = r² − 2Mr + a²` of the Kerr metric. -/
def del (M a r : ℝ) : ℝ := r ^ 2 - 2 * M * r + a ^ 2

/-- The radius `r₊ = M + √(M² − a²)` of the outer horizon. -/
def horizon (M a : ℝ) : ℝ := M + Real.sqrt (M ^ 2 - a ^ 2)

/-- `Σ > 0` for `r > 0`. -/
theorem sig_pos (a c : ℝ) {r : ℝ} (hr : 0 < r) : 0 < sig a r c := by
  unfold sig
  positivity

/-- `Δ` vanishes at the outer horizon. -/
theorem del_horizon (ha : a ^ 2 ≤ M ^ 2) : del M a (horizon M a) = 0 := by
  have h := Real.sq_sqrt (show 0 ≤ M ^ 2 - a ^ 2 by linarith)
  unfold del horizon
  linear_combination h

/-- The outer horizon lies outside `r = M`. -/
theorem le_horizon (M a : ℝ) : M ≤ horizon M a :=
  le_add_of_nonneg_right (Real.sqrt_nonneg _)

/-- `Δ > 0` outside the outer horizon: `Δ = (r − r₊)(r − r₋)` with `r₋ ≤ r₊`. -/
theorem del_pos (ha : a ^ 2 ≤ M ^ 2) {r : ℝ} (hr : horizon M a < r) : 0 < del M a r := by
  have h := Real.sq_sqrt (show 0 ≤ M ^ 2 - a ^ 2 by linarith)
  have hs := Real.sqrt_nonneg (M ^ 2 - a ^ 2)
  unfold horizon at hr
  have e : del M a r =
      (r - M - Real.sqrt (M ^ 2 - a ^ 2)) * (r - M + Real.sqrt (M ^ 2 - a ^ 2)) := by
    unfold del
    linear_combination h
  rw [e]
  exact mul_pos (by linarith) (by linarith)

/-! ### The coefficients and the form -/

/-- The coefficient `g_tt = −(1 − 2Mr/Σ)` of the Kerr metric. -/
def gtt (M a r c : ℝ) : ℝ :=
  -(1 - 2 * M * r / sig a r c)

/-- The coefficient `g_tφ = −2Mar(1 − χ²)/Σ` of the Kerr metric. -/
def gtp (M a r c : ℝ) : ℝ :=
  -(2 * M * a * r * (1 - c ^ 2) / sig a r c)

/-- The coefficient `g_rr = Σ/Δ` of the Kerr metric. -/
def grr (M a r c : ℝ) : ℝ :=
  sig a r c / del M a r

/-- The coefficient `g_χχ = Σ/(1 − χ²)` of the Kerr metric. -/
def gcc (a r c : ℝ) : ℝ :=
  sig a r c / (1 - c ^ 2)

/-- The coefficient `g_φφ = (r² + a² + 2Ma²r(1 − χ²)/Σ)(1 − χ²)` of the Kerr metric. -/
def gpp (M a r c : ℝ) : ℝ :=
  (r ^ 2 + a ^ 2 + 2 * M * a ^ 2 * r * (1 - c ^ 2) / sig a r c) * (1 - c ^ 2)

/-- `g_tt g_φφ − g_tφ² = −Δ(1 − χ²)`. -/
theorem gtt_mul_gpp_sub_sq {r c : ℝ} (hS : sig a r c ≠ 0) :
    gtt M a r c * gpp M a r c - gtp M a r c ^ 2 = -(del M a r * (1 - c ^ 2)) := by
  unfold gtt gpp gtp del
  field_simp
  unfold sig
  ring

/-- `g_φφ > 0` for `M ≥ 0`, `r > 0` and `χ² < 1`. -/
theorem gpp_pos (hM : 0 ≤ M) {r c : ℝ} (hr : 0 < r) (hc : 0 < 1 - c ^ 2) :
    0 < gpp M a r c := by
  have hS := sig_pos a c hr
  have h : 0 ≤ 2 * M * a ^ 2 * r * (1 - c ^ 2) / sig a r c :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hM) (sq_nonneg a))
      hr.le) hc.le) hS.le
  have h2 := pow_pos hr 2
  have h3 := sq_nonneg a
  unfold gpp
  exact mul_pos (by linarith) hc

/-- The domain `r > r₊`, `−1 < χ < 1` of the Boyer–Lindquist co-ordinates `(t, r, χ, φ)`,
outside the outer horizon and off the axis. -/
def domain (M a : ℝ) : Opens (MinkowskiModel 3) :=
  ⟨{x | horizon M a < x 1 ∧ -1 < x 2 ∧ x 2 < 1},
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const)))⟩

/-- The radius is positive on the domain. -/
theorem radius_pos (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ domain M a) : 0 < x 1 :=
  (hM.trans_le (le_horizon M a)).trans hx.1

/-- `1 − χ² > 0` on the domain. -/
theorem one_sub_sq_pos {x : MinkowskiModel 3} (hx : x ∈ domain M a) : 0 < 1 - x 2 ^ 2 := by
  have h1 : -1 < x 2 := hx.2.1
  have h2 : x 2 < 1 := hx.2.2
  nlinarith [mul_pos (sub_pos.mpr h2) (show 0 < 1 + x 2 by linarith)]

/-- The Kerr form at the point `x = (t, r, χ, φ)`: `g_tt dt ⊗ dt + g_tφ (dt ⊗ dφ + dφ ⊗ dt) +
g_rr dr ⊗ dr + g_χχ dχ ⊗ dχ + g_φφ dφ ⊗ dφ`. -/
def form (M a : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
  gtt M a (x 1) (x 2) •
      (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
    gtp M a (x 1) (x 2) •
      ((proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ) +
        (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ)) +
    grr M a (x 1) (x 2) •
      (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
    gcc a (x 1) (x 2) •
      (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ) +
    gpp M a (x 1) (x 2) •
      (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ)

/-- The value of the Kerr form on two vectors. -/
theorem form_apply (x v w : MinkowskiModel 3) :
    form M a x v w = gtt M a (x 1) (x 2) * (v 0 * w 0) +
      gtp M a (x 1) (x 2) * (v 0 * w 3 + v 3 * w 0) + grr M a (x 1) (x 2) * (v 1 * w 1) +
      gcc a (x 1) (x 2) * (v 2 * w 2) + gpp M a (x 1) (x 2) * (v 3 * w 3) := by
  simp only [form, add_apply, smul_apply, smulRight_apply, proj_apply, smul_eq_mul]

/-- The Kerr form is symmetric. -/
theorem form_symm (x v w : MinkowskiModel 3) : form M a x v w = form M a x w v := by
  rw [form_apply, form_apply]
  ring

/-- The Kerr form is smooth on the domain. -/
theorem contDiffOn_form (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    ContDiffOn ℝ ∞ (form M a) (domain M a) := by
  refine contDiffOn_clm_apply.mpr fun v => contDiffOn_clm_apply.mpr fun w => ?_
  have hr : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 1 := contDiff_apply ℝ (fun _ => ℝ) 1
  have hc : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 2 := contDiff_apply ℝ (fun _ => ℝ) 2
  have hS : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => sig a (x 1) (x 2) := by
    unfold sig
    exact (hr.pow 2).add (contDiff_const.mul (hc.pow 2))
  have hD : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => del M a (x 1) := by
    unfold del
    exact ((hr.pow 2).sub (contDiff_const.mul hr)).add contDiff_const
  have hC : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => 1 - x 2 ^ 2 := contDiff_const.sub (hc.pow 2)
  have hS0 : ∀ x ∈ (domain M a : Set (MinkowskiModel 3)), sig a (x 1) (x 2) ≠ 0 :=
    fun x hx => (sig_pos a _ (radius_pos hM hx)).ne'
  have hD0 : ∀ x ∈ (domain M a : Set (MinkowskiModel 3)), del M a (x 1) ≠ 0 :=
    fun x hx => (del_pos ha hx.1).ne'
  have hC0 : ∀ x ∈ (domain M a : Set (MinkowskiModel 3)), 1 - x 2 ^ 2 ≠ 0 :=
    fun x hx => (one_sub_sq_pos hx).ne'
  have hq : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => 2 * M * a ^ 2 * x 1 * (1 - x 2 ^ 2) /
      sig a (x 1) (x 2)) (domain M a) :=
    ((contDiff_const.mul hr).mul hC).contDiffOn.div hS.contDiffOn hS0
  have htt : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => gtt M a (x 1) (x 2)) (domain M a) := by
    unfold gtt
    exact (contDiffOn_const.sub ((contDiff_const.mul hr).contDiffOn.div hS.contDiffOn hS0)).neg
  have htp : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => gtp M a (x 1) (x 2)) (domain M a) := by
    unfold gtp
    exact (((contDiff_const.mul hr).mul hC).contDiffOn.div hS.contDiffOn hS0).neg
  have hrr : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => grr M a (x 1) (x 2)) (domain M a) := by
    unfold grr
    exact hS.contDiffOn.div hD.contDiffOn hD0
  have hcc : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => gcc a (x 1) (x 2)) (domain M a) := by
    unfold gcc
    exact hS.contDiffOn.div hC.contDiffOn hC0
  have hpp : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => gpp M a (x 1) (x 2)) (domain M a) := by
    unfold gpp
    exact (((hr.pow 2).add contDiff_const).contDiffOn.add hq).mul hC.contDiffOn
  simp only [form_apply]
  exact ((((htt.mul contDiffOn_const).add (htp.mul contDiffOn_const)).add
    (hrr.mul contDiffOn_const)).add (hcc.mul contDiffOn_const)).add (hpp.mul contDiffOn_const)

/-! ### The metric -/

/-- The shear `v ↦ (v₀, v₁, v₂, v₃ + k v₀)` as a linear equivalence. -/
def shearLinear (k : ℝ) : MinkowskiModel 3 ≃ₗ[ℝ] MinkowskiModel 3 where
  toFun v := ![v 0, v 1, v 2, v 3 + k * v 0]
  invFun v := ![v 0, v 1, v 2, v 3 - k * v 0]
  map_add' v w := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' t v := by
    funext i
    fin_cases i <;> simp
    ring
  left_inv v := by
    funext i
    fin_cases i <;> simp
  right_inv v := by
    funext i
    fin_cases i <;> simp

/-- The shear `e₀ ↦ e₀ + k e₃`, the identity on `e₁`, `e₂`, `e₃`. -/
def shear (k : ℝ) : MinkowskiModel 3 ≃L[ℝ] MinkowskiModel 3 :=
  (shearLinear k).toContinuousLinearEquiv

/-- The value of the shear. -/
theorem shear_apply (k : ℝ) (v : MinkowskiModel 3) :
    shear k v = ![v 0, v 1, v 2, v 3 + k * v 0] := by
  rw [shear, LinearEquiv.coe_toContinuousLinearEquiv']
  rfl

/-- The angular velocity `ω = −g_tφ/g_φφ` of the frame `pointFrame`. -/
def frameRate (M a : ℝ) (x : MinkowskiModel 3) : ℝ :=
  -gtp M a (x 1) (x 2) / gpp M a (x 1) (x 2)

/-- The pointwise frame `P x`: `e₀ ↦ e₀ + ω e₃` with `ω = frameRate M a x`, the identity on
`e₁`, `e₂`, `e₃`. -/
def pointFrame (M a : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 ≃L[ℝ] MinkowskiModel 3 :=
  shear (frameRate M a x)

/-- The form on the time vector of the frame: `B(Pe₀, Pe₀) = g_tt − g_tφ²/g_φφ =
−Δ(1 − χ²)/g_φφ`. -/
theorem form_pointFrame_time {x : MinkowskiModel 3} (hS : sig a (x 1) (x 2) ≠ 0)
    (hp : gpp M a (x 1) (x 2) ≠ 0) :
    form M a x (pointFrame M a x (Fin.cons 1 (0 : Fin 3 → ℝ)))
        (pointFrame M a x (Fin.cons 1 (0 : Fin 3 → ℝ))) =
      -(del M a (x 1) * (1 - x 2 ^ 2)) / gpp M a (x 1) (x 2) := by
  have key := gtt_mul_gpp_sub_sq (M := M) hS
  rw [pointFrame, shear_apply, form_apply]
  have e1 : (Fin.cons 1 (0 : Fin 3 → ℝ) : MinkowskiModel 3) 1 = 0 := rfl
  have e2 : (Fin.cons 1 (0 : Fin 3 → ℝ) : MinkowskiModel 3) 2 = 0 := rfl
  have e3 : (Fin.cons 1 (0 : Fin 3 → ℝ) : MinkowskiModel 3) 3 = 0 := rfl
  simp [e1, e2, e3, frameRate]
  field_simp
  linear_combination key

/-- The form on the spatial vectors of the frame: `B(P(0, v), P(0, v)) = g_rr v₀² + g_χχ v₁² +
g_φφ v₂²`. -/
theorem form_pointFrame_space (x : MinkowskiModel 3) (v : Fin 3 → ℝ) :
    form M a x (pointFrame M a x (Fin.cons 0 v)) (pointFrame M a x (Fin.cons 0 v)) =
      grr M a (x 1) (x 2) * (v 0 * v 0) + gcc a (x 1) (x 2) * (v 1 * v 1) +
        gpp M a (x 1) (x 2) * (v 2 * v 2) := by
  rw [pointFrame, shear_apply, form_apply]
  have e1 : (Fin.cons 0 v : MinkowskiModel 3) 1 = v 0 := rfl
  have e2 : (Fin.cons 0 v : MinkowskiModel 3) 2 = v 1 := rfl
  have e3 : (Fin.cons 0 v : MinkowskiModel 3) 3 = v 2 := rfl
  simp [e1, e2, e3]

/-- A diagonal form with positive coefficients is positive on the nonzero vectors. -/
theorem diagonal_pos {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) {v : Fin 3 → ℝ}
    (hv : v ≠ 0) : 0 < p * (v 0 * v 0) + q * (v 1 * v 1) + s * (v 2 * v 2) := by
  have h0 := mul_nonneg hp.le (mul_self_nonneg (v 0))
  have h1 := mul_nonneg hq.le (mul_self_nonneg (v 1))
  have h2 := mul_nonneg hs.le (mul_self_nonneg (v 2))
  by_contra hle
  apply hv
  have z0 : v 0 * v 0 = 0 :=
    (mul_eq_zero.mp (le_antisymm (by linarith) h0)).resolve_left hp.ne'
  have z1 : v 1 * v 1 = 0 :=
    (mul_eq_zero.mp (le_antisymm (by linarith) h1)).resolve_left hq.ne'
  have z2 : v 2 * v 2 = 0 :=
    (mul_eq_zero.mp (le_antisymm (by linarith) h2)).resolve_left hs.ne'
  funext i
  fin_cases i
  · exact mul_self_eq_zero.mp z0
  · exact mul_self_eq_zero.mp z1
  · exact mul_self_eq_zero.mp z2

/-- **The Kerr metric** (Landau–Lifshitz, (104.1)) for `M > 0` and `a² ≤ M²`, a Lorentz metric
on the domain `r > r₊`, `−1 < χ < 1`. The signature is checked in the frame `pointFrame`, since
`g_tt` changes sign in the ergoregion. -/
def metric (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) : CoordinateMetric .timeNegative 3 (domain M a) :=
  CoordinateMetric.ofFrameCriterion (form M a) (contDiffOn_form hM ha)
    (fun x _ v w => form_symm x v w) (pointFrame M a)
    (fun x hx => by
      have hr := radius_pos hM hx
      have hc := one_sub_sq_pos hx
      have hp := gpp_pos (a := a) hM.le hr hc
      rw [form_pointFrame_time (sig_pos a (x 2) hr).ne' hp.ne',
        LorentzConvention.timeSign_timeNegative, neg_neg, one_mul]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos (mul_pos (del_pos ha hx.1) hc)) hp)
    (fun x hx v hv => by
      have hr := radius_pos hM hx
      have hS := sig_pos a (x 2) hr
      have hc := one_sub_sq_pos hx
      rw [form_pointFrame_space, LorentzConvention.timeSign_timeNegative, neg_neg, one_mul]
      exact diagonal_pos (div_pos hS (del_pos ha hx.1)) (div_pos hS hc) (gpp_pos hM.le hr hc)
        hv)

/-- The form of the metric is the Kerr form. -/
theorem metric_form (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x : MinkowskiModel 3) :
    (metric hM ha).form x = form M a x := rfl

/-- The coefficients of the metric are the values of the form on the basis vectors. -/
theorem coefficient_apply (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x : MinkowskiModel 3)
    (i j : Fin 4) :
    (metric hM ha).coefficient x i j = form M a x (Pi.single i 1) (Pi.single j 1) := rfl

/-! ### The Killing fields `∂_t` and `∂_φ` -/

/-- The Kerr form depends on neither `t` nor `φ`. -/
theorem form_add (k : Fin 4) (hk : k = 0 ∨ k = 3) (y : MinkowskiModel 3) (t : ℝ) :
    form M a (y + t • Pi.single k 1) = form M a y := by
  have h1 : (y + t • Pi.single k 1 : MinkowskiModel 3) 1 = y 1 := by
    rcases hk with rfl | rfl <;> simp
  have h2 : (y + t • Pi.single k 1 : MinkowskiModel 3) 2 = y 2 := by
    rcases hk with rfl | rfl <;> simp
  simp only [form, h1, h2]

/-- `∂_t` is a Killing field of the Kerr metric. -/
theorem isKillingField_time (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x₀ : domain M a) :
    (metric hM ha).toLorentzMetric.IsKillingField
      (chartField (physicalChart x₀) (Pi.single 0 1)) :=
  CoordinateMetric.isKillingField_of_invariant (metric hM ha) x₀ 0 (form_add 0 (Or.inl rfl))

/-- `∂_φ` is a Killing field of the Kerr metric. -/
theorem isKillingField_angle (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x₀ : domain M a) :
    (metric hM ha).toLorentzMetric.IsKillingField
      (chartField (physicalChart x₀) (Pi.single 3 1)) :=
  CoordinateMetric.isKillingField_of_invariant (metric hM ha) x₀ 3 (form_add 3 (Or.inr rfl))

/-! ### The Christoffel symbols -/

/-- The Christoffel symbol `Γ^0_{01}` `= Γ^0_{10}` of the Kerr metric. -/
def chris0_01 (M a r c : ℝ) : ℝ :=
  M * (a * c + r) * (-(a * c) + r) * (a ^ 2 + r ^ 2) / (del M a r * sig a r c ^ 2)

/-- The Christoffel symbol `Γ^0_{02}` `= Γ^0_{20}` of the Kerr metric. -/
def chris0_02 (M a r c : ℝ) : ℝ :=
  2 * M * c * r * a ^ 2 / sig a r c ^ 2

/-- The Christoffel symbol `Γ^0_{13}` `= Γ^0_{31}` of the Kerr metric. -/
def chris0_13 (M a r c : ℝ) : ℝ :=
  M * a * (c + 1) * (c - 1) * (-(a ^ 4 * c ^ 2) + a ^ 2 * c ^ 2 * r ^ 2 + a ^ 2 * r ^ 2 + 3 *
      r ^ 4) / (del M a r * sig a r c ^ 2)

/-- The Christoffel symbol `Γ^0_{23}` `= Γ^0_{32}` of the Kerr metric. -/
def chris0_23 (M a r c : ℝ) : ℝ :=
  2 * M * c * r * a ^ 3 * (c + 1) * (c - 1) / sig a r c ^ 2

/-- The Christoffel symbol `Γ^1_{00}` of the Kerr metric. -/
def chris1_00 (M a r c : ℝ) : ℝ :=
  del M a r * M * (a * c + r) * (-(a * c) + r) / sig a r c ^ 3

/-- The Christoffel symbol `Γ^1_{03}` `= Γ^1_{30}` of the Kerr metric. -/
def chris1_03 (M a r c : ℝ) : ℝ :=
  del M a r * M * a * (c + 1) * (c - 1) * (a * c + r) * (-(a * c) + r) / sig a r c ^ 3

/-- The Christoffel symbol `Γ^1_{11}` of the Kerr metric. -/
def chris1_11 (M a r c : ℝ) : ℝ :=
  -((-(M * a ^ 2 * c ^ 2) + M * r ^ 2 + r * a ^ 2 * c ^ 2 - r * a ^ 2) / (del M a r * sig a r c))

/-- The Christoffel symbol `Γ^1_{12}` `= Γ^1_{21}` of the Kerr metric. -/
def chris1_12 (a r c : ℝ) : ℝ :=
  c * a ^ 2 / sig a r c

/-- The Christoffel symbol `Γ^1_{22}` of the Kerr metric. -/
def chris1_22 (M a r c : ℝ) : ℝ :=
  del M a r * r / (sig a r c * (c + 1) * (c - 1))

/-- The Christoffel symbol `Γ^1_{33}` of the Kerr metric. -/
def chris1_33 (M a r c : ℝ) : ℝ :=
  del M a r * (c + 1) * (c - 1) * (-(M * a ^ 4 * c ^ 4) + M * a ^ 4 * c ^ 2 + M * a ^ 2 *
      c ^ 2 * r ^ 2 - M * a ^ 2 * r ^ 2 + r * a ^ 4 * c ^ 4 + 2 * a ^ 2 * c ^ 2 * r ^ 3 +
      r ^ 5) / sig a r c ^ 3

/-- The Christoffel symbol `Γ^2_{00}` of the Kerr metric. -/
def chris2_00 (M a r c : ℝ) : ℝ :=
  -(2 * M * c * r * a ^ 2 * (c + 1) * (c - 1) / sig a r c ^ 3)

/-- The Christoffel symbol `Γ^2_{03}` `= Γ^2_{30}` of the Kerr metric. -/
def chris2_03 (M a r c : ℝ) : ℝ :=
  2 * M * a * c * r * (c + 1) * (c - 1) * (a ^ 2 + r ^ 2) / sig a r c ^ 3

/-- The Christoffel symbol `Γ^2_{11}` of the Kerr metric. -/
def chris2_11 (M a r c : ℝ) : ℝ :=
  c * a ^ 2 * (c + 1) * (c - 1) / (del M a r * sig a r c)

/-- The Christoffel symbol `Γ^2_{12}` `= Γ^2_{21}` of the Kerr metric. -/
def chris2_12 (a r c : ℝ) : ℝ :=
  r / sig a r c

/-- The Christoffel symbol `Γ^2_{22}` of the Kerr metric. -/
def chris2_22 (a r c : ℝ) : ℝ :=
  -(c * (a ^ 2 + r ^ 2) / (sig a r c * (c + 1) * (c - 1)))

/-- The Christoffel symbol `Γ^2_{33}` of the Kerr metric. -/
def chris2_33 (M a r c : ℝ) : ℝ :=
  -(c * (c + 1) * (c - 1) * (-(2 * M * r * a ^ 4 * c ^ 4) + 2 * M * r * a ^ 4 - 4 * M *
      a ^ 2 * c ^ 2 * r ^ 3 + 4 * M * a ^ 2 * r ^ 3 + a ^ 6 * c ^ 4 + a ^ 4 * c ^ 4 * r ^ 2 +
      2 * a ^ 4 * c ^ 2 * r ^ 2 + 2 * a ^ 2 * c ^ 2 * r ^ 4 + a ^ 2 * r ^ 4 + r ^ 6) /
      sig a r c ^ 3)

/-- The Christoffel symbol `Γ^3_{01}` `= Γ^3_{10}` of the Kerr metric. -/
def chris3_01 (M a r c : ℝ) : ℝ :=
  M * a * (a * c + r) * (-(a * c) + r) / (del M a r * sig a r c ^ 2)

/-- The Christoffel symbol `Γ^3_{02}` `= Γ^3_{20}` of the Kerr metric. -/
def chris3_02 (M a r c : ℝ) : ℝ :=
  -(2 * M * a * c * r / (sig a r c ^ 2 * (c + 1) * (c - 1)))

/-- The Christoffel symbol `Γ^3_{13}` `= Γ^3_{31}` of the Kerr metric. -/
def chris3_13 (M a r c : ℝ) : ℝ :=
  (-(M * a ^ 4 * c ^ 4) + M * a ^ 4 * c ^ 2 - M * a ^ 2 * c ^ 2 * r ^ 2 - M * a ^ 2 * r ^ 2 - 2 *
      M * r ^ 4 + r * a ^ 4 * c ^ 4 + 2 * a ^ 2 * c ^ 2 * r ^ 3 + r ^ 5) / (del M a r *
      sig a r c ^ 2)

/-- The Christoffel symbol `Γ^3_{23}` `= Γ^3_{32}` of the Kerr metric. -/
def chris3_23 (M a r c : ℝ) : ℝ :=
  c * (-(2 * M * r * a ^ 2 * c ^ 2) + 2 * M * r * a ^ 2 + a ^ 4 * c ^ 4 + 2 * a ^ 2 * c ^ 2 *
      r ^ 2 + r ^ 4) / (sig a r c ^ 2 * (c + 1) * (c - 1))

/-- **The Christoffel symbols of the Kerr metric** as functions of `r` and `χ`:
`christoffelTable M a r χ k i j` is `Γ^k_{ij}`, symmetric in the lower indices, with the twenty
independent nonzero symbols `chris…` and the others zero. -/
def christoffelTable (M a r c : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, chris0_01 M a r c, chris0_02 M a r c, 0],
      ![chris0_01 M a r c, 0, 0, chris0_13 M a r c],
      ![chris0_02 M a r c, 0, 0, chris0_23 M a r c],
      ![0, chris0_13 M a r c, chris0_23 M a r c, 0]],
    ![![chris1_00 M a r c, 0, 0, chris1_03 M a r c],
      ![0, chris1_11 M a r c, chris1_12 a r c, 0],
      ![0, chris1_12 a r c, chris1_22 M a r c, 0],
      ![chris1_03 M a r c, 0, 0, chris1_33 M a r c]],
    ![![chris2_00 M a r c, 0, 0, chris2_03 M a r c],
      ![0, chris2_11 M a r c, chris2_12 a r c, 0],
      ![0, chris2_12 a r c, chris2_22 a r c, 0],
      ![chris2_03 M a r c, 0, 0, chris2_33 M a r c]],
    ![![0, chris3_01 M a r c, chris3_02 M a r c, 0],
      ![chris3_01 M a r c, 0, 0, chris3_13 M a r c],
      ![chris3_02 M a r c, 0, 0, chris3_23 M a r c],
      ![0, chris3_13 M a r c, chris3_23 M a r c, 0]]]

/-- The Christoffel symbols `Γ^k_{ij}` (`christoffel M a x k i j`) of the Kerr metric at the
point `x`: the table `christoffelTable` at `r = x 1`, `χ = x 2`. -/
def christoffel (M a : ℝ) (x : MinkowskiModel 3) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffelTable M a (x 1) (x 2)

/-! #### Partial derivatives in `r` and `χ` -/

private theorem hasDerivAt_sig_r (a r c : ℝ) : HasDerivAt (fun s => sig a s c) (2 * r) r := by
  have h := ((hasDerivAt_id' r).fun_pow 2).fun_add (hasDerivAt_const r (a ^ 2 * c ^ 2))
  unfold sig
  convert h using 1
  simp

private theorem hasDerivAt_sig_c (a r c : ℝ) :
    HasDerivAt (fun s => sig a r s) (2 * a ^ 2 * c) c := by
  have h := (hasDerivAt_const c (r ^ 2)).fun_add (((hasDerivAt_id' c).fun_pow 2).const_mul (a ^ 2))
  unfold sig
  convert h using 1
  simp
  ring

private theorem hasDerivAt_del_r (M a r : ℝ) :
    HasDerivAt (fun s => del M a s) (2 * r - 2 * M) r := by
  have h := (((hasDerivAt_id' r).fun_pow 2).fun_sub ((hasDerivAt_id' r).const_mul (2 * M))).fun_add
    (hasDerivAt_const r (a ^ 2))
  unfold del
  convert h using 1
  simp

private def dgtt_r (M a r c : ℝ) : ℝ :=
  -(2 * M * (a * c + r) * (-(a * c) + r) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_gtt_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => gtt M a s c) (dgtt_r M a r c) r := by
  unfold gtt dgtt_r
  refine HasDerivAt.congr_deriv ((hasDerivAt_const r (1 : ℝ)).fun_sub ((HasDerivAt.const_mul (2 *
      M : ℝ) (hasDerivAt_id' r)).fun_div (hasDerivAt_sig_r a r c) hS)).fun_neg ?_
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dgtt_c (M a r c : ℝ) : ℝ :=
  -(4 * M * c * r * a ^ (2 : ℕ) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_gtt_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => gtt M a r s) (dgtt_c M a r c) c := by
  unfold gtt dgtt_c
  refine HasDerivAt.congr_deriv ((hasDerivAt_const c (1 : ℝ)).fun_sub ((hasDerivAt_const c (2 *
      M * r : ℝ)).fun_div (hasDerivAt_sig_c a r c) hS)).fun_neg ?_
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dgtp_r (M a r c : ℝ) : ℝ :=
  -(2 * M * a * (c + 1) * (c - 1) * (a * c + r) * (-(a * c) + r) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_gtp_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => gtp M a s c) (dgtp_r M a r c) r := by
  unfold gtp dgtp_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (HasDerivAt.const_mul (2 * M *
      a : ℝ) (hasDerivAt_id' r)) (1 - c ^ 2 : ℝ)).fun_div (hasDerivAt_sig_r a r c) hS).fun_neg ?_
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dgtp_c (M a r c : ℝ) : ℝ :=
  4 * M * a * c * r * (a ^ (2 : ℕ) + r ^ (2 : ℕ)) / sig a r c ^ (2 : ℕ)

private theorem hasDerivAt_gtp_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => gtp M a r s) (dgtp_c M a r c) c := by
  unfold gtp dgtp_c
  refine HasDerivAt.congr_deriv ((HasDerivAt.const_mul (2 * M * a * r : ℝ)
      ((hasDerivAt_const c (1 : ℝ)).fun_sub ((hasDerivAt_id' c).fun_pow 2))).fun_div
      (hasDerivAt_sig_c a r c) hS).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dgrr_r (M a r c : ℝ) : ℝ :=
  -(2 * (-(M * a ^ (2 : ℕ) * c ^ (2 : ℕ)) + M * r ^ (2 : ℕ) + r * a ^ (2 : ℕ) * c ^ (2 : ℕ) -
      r * a ^ (2 : ℕ)) / del M a r ^ (2 : ℕ))

private theorem hasDerivAt_grr_r (M a r c : ℝ) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => grr M a s c) (dgrr_r M a r c) r := by
  unfold grr dgrr_r
  refine HasDerivAt.congr_deriv ((hasDerivAt_sig_r a r c).fun_div (hasDerivAt_del_r M a r) hD) ?_
  generalize hSd : sig a r c = S
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dgrr_c (M a r c : ℝ) : ℝ :=
  2 * c * a ^ (2 : ℕ) / del M a r

private theorem hasDerivAt_grr_c (M a r c : ℝ) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => grr M a r s) (dgrr_c M a r c) c := by
  unfold grr dgrr_c
  refine HasDerivAt.congr_deriv (HasDerivAt.div_const (hasDerivAt_sig_c a r c) (del M a r : ℝ)) ?_
  field_simp

private def dgcc_r (r c : ℝ) : ℝ :=
  -(2 * r / ((c + 1) * (c - 1)))

private theorem hasDerivAt_gcc_r (a r c : ℝ) (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0)
    (h1c : 1 - c ^ 2 ≠ 0) :
    HasDerivAt (fun s => gcc a s c) (dgcc_r r c) r := by
  unfold gcc dgcc_r
  refine HasDerivAt.congr_deriv (HasDerivAt.div_const (hasDerivAt_sig_r a r c) (1 - c ^ 2 : ℝ)) ?_
  generalize hSd : sig a r c = S
  field_simp
  unfold sig at hSd
  subst hSd
  ring

private def dgcc_c (a r c : ℝ) : ℝ :=
  2 * c * (a ^ (2 : ℕ) + r ^ (2 : ℕ)) / ((c + 1) ^ (2 : ℕ) * (c - 1) ^ (2 : ℕ))

private theorem hasDerivAt_gcc_c (a r c : ℝ) (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0)
    (h1c : 1 - c ^ 2 ≠ 0) :
    HasDerivAt (fun s => gcc a r s) (dgcc_c a r c) c := by
  unfold gcc dgcc_c
  refine HasDerivAt.congr_deriv ((hasDerivAt_sig_c a r c).fun_div ((hasDerivAt_const c
      (1 : ℝ)).fun_sub ((hasDerivAt_id' c).fun_pow 2)) h1c) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S
  field_simp
  unfold sig at hSd
  subst hSd
  ring

private def dgpp_r (M a r c : ℝ) : ℝ :=
  -(2 * (c + 1) * (c - 1) * (-(M * a ^ (4 : ℕ) * c ^ (4 : ℕ)) + M * a ^ (4 : ℕ) * c ^ (2 : ℕ) +
      M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) - M * a ^ (2 : ℕ) * r ^ (2 : ℕ) + r *
      a ^ (4 : ℕ) * c ^ (4 : ℕ) + 2 * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + r ^ (5 : ℕ)) /
      sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_gpp_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => gpp M a s c) (dgpp_r M a r c) r := by
  unfold gpp dgpp_r
  refine HasDerivAt.congr_deriv (HasDerivAt.mul_const ((((hasDerivAt_id' r).fun_pow 2).fun_add
      (hasDerivAt_const r (a ^ 2 : ℝ))).fun_add ((HasDerivAt.mul_const (HasDerivAt.const_mul (2 *
      M * a ^ 2 : ℝ) (hasDerivAt_id' r)) (1 - c ^ 2 : ℝ)).fun_div (hasDerivAt_sig_r a r c) hS))
      (1 - c ^ 2 : ℝ)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dgpp_c (M a r c : ℝ) : ℝ :=
  -(2 * c * (-(2 * M * r * a ^ (4 : ℕ) * c ^ (4 : ℕ)) + 2 * M * r * a ^ (4 : ℕ) - 4 *
      M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + 4 * M * a ^ (2 : ℕ) * r ^ (3 : ℕ) +
      a ^ (6 : ℕ) * c ^ (4 : ℕ) + a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) + 2 *
      a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) + 2 * a ^ (2 : ℕ) * c ^ (2 : ℕ) *
      r ^ (4 : ℕ) + a ^ (2 : ℕ) * r ^ (4 : ℕ) + r ^ (6 : ℕ)) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_gpp_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => gpp M a r s) (dgpp_c M a r c) c := by
  unfold gpp dgpp_c
  refine HasDerivAt.congr_deriv (((hasDerivAt_const c (r ^ 2 +
      a ^ 2 : ℝ)).fun_add ((HasDerivAt.const_mul (2 * M * a ^ 2 * r : ℝ)
      ((hasDerivAt_const c (1 : ℝ)).fun_sub ((hasDerivAt_id' c).fun_pow 2))).fun_div
      (hasDerivAt_sig_c a r c) hS)).fun_mul ((hasDerivAt_const c (1 : ℝ)).fun_sub ((hasDerivAt_id'
      c).fun_pow 2))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

/-- The coefficients of the Kerr metric as functions of `r` and `χ`. -/
private def metricTable (M a r c : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![gtt M a r c, 0, 0, gtp M a r c], ![0, grr M a r c, 0, 0], ![0, 0, gcc a r c, 0],
    ![gtp M a r c, 0, 0, gpp M a r c]]

private def metricR (M a r c : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![dgtt_r M a r c, 0, 0, dgtp_r M a r c],
    ![0, dgrr_r M a r c, 0, 0],
    ![0, 0, dgcc_r r c, 0],
    ![dgtp_r M a r c, 0, 0, dgpp_r M a r c]]

private def metricC (M a r c : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![dgtt_c M a r c, 0, 0, dgtp_c M a r c],
    ![0, dgrr_c M a r c, 0, 0],
    ![0, 0, dgcc_c a r c, 0],
    ![dgtp_c M a r c, 0, 0, dgpp_c M a r c]]

private theorem hasDerivAt_metricTable_r (M a r c : ℝ) (hS : sig a r c ≠ 0)
    (hD : del M a r ≠ 0) (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) (i j : Fin 4) :
    HasDerivAt (fun s => metricTable M a s c i j) (metricR M a r c i j) r := by
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_gtt_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_gtp_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_grr_r M a r c hD
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_gcc_r a r c hc1 hc2 h1c
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_gtp_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_gpp_r M a r c hS

private theorem hasDerivAt_metricTable_c (M a r c : ℝ) (hS : sig a r c ≠ 0)
    (hD : del M a r ≠ 0) (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) (i j : Fin 4) :
    HasDerivAt (fun s => metricTable M a r s i j) (metricC M a r c i j) c := by
  fin_cases i <;> fin_cases j
  · exact hasDerivAt_gtt_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_gtp_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_grr_c M a r c hD
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_gcc_c a r c hc1 hc2 h1c
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_gtp_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_gpp_c M a r c hS

/-- The partial derivatives `∂_l g_{ij}`: zero along `t` and `φ`. -/
private def metricPartial (M a : ℝ) (l : Fin 4) (r c : ℝ) (i j : Fin 4) : ℝ :=
  ![0, metricR M a r c i j, metricC M a r c i j, 0] l

private def dchris0_01_r (M a r c : ℝ) : ℝ :=
  -(2 * M * (M * a ^ (6 : ℕ) * c ^ (4 : ℕ) - M * a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) + 6 *
      M * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) + 6 * M * a ^ (2 : ℕ) * c ^ (2 : ℕ) *
      r ^ (4 : ℕ) - 3 * M * a ^ (2 : ℕ) * r ^ (4 : ℕ) - M * r ^ (6 : ℕ) - 3 * r *
      a ^ (6 : ℕ) * c ^ (2 : ℕ) - 6 * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) +
      a ^ (4 : ℕ) * r ^ (3 : ℕ) - 3 * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (5 : ℕ) + 2 *
      a ^ (2 : ℕ) * r ^ (5 : ℕ) + r ^ (7 : ℕ)) / (del M a r ^ (2 : ℕ) * sig a r c ^ (3 : ℕ)))

private theorem hasDerivAt_chris0_01_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris0_01 M a s c) (dchris0_01_r M a r c) r := by
  unfold chris0_01 dchris0_01_r
  refine HasDerivAt.congr_deriv ((((HasDerivAt.const_mul (M : ℝ)
      ((hasDerivAt_const r (a * c : ℝ)).fun_add (hasDerivAt_id' r))).fun_mul ((hasDerivAt_const r
      (-(a * c) : ℝ)).fun_add (hasDerivAt_id' r))).fun_mul ((hasDerivAt_const r (a ^ 2 : ℝ)).fun_add
      ((hasDerivAt_id' r).fun_pow 2))).fun_div ((hasDerivAt_del_r M a r).fun_mul ((hasDerivAt_sig_r
      a r c).fun_pow 2)) (mul_ne_zero hD (pow_ne_zero 2 hS))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris0_01_c (M a r c : ℝ) : ℝ :=
  -(2 * M * c * a ^ (2 : ℕ) * (a ^ (2 : ℕ) + r ^ (2 : ℕ)) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) +
      3 * r ^ (2 : ℕ)) / (del M a r * sig a r c ^ (3 : ℕ)))

private theorem hasDerivAt_chris0_01_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris0_01 M a r s) (dchris0_01_c M a r c) c := by
  unfold chris0_01 dchris0_01_c
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const ((HasDerivAt.const_mul (M : ℝ)
      ((HasDerivAt.const_mul (a : ℝ) (hasDerivAt_id' c)).fun_add (hasDerivAt_const c
      (r : ℝ)))).fun_mul ((HasDerivAt.const_mul (a : ℝ) (hasDerivAt_id' c)).fun_neg.fun_add
      (hasDerivAt_const c (r : ℝ)))) (a ^ 2 + r ^ 2 : ℝ)).fun_div (HasDerivAt.const_mul (del M a
      r : ℝ) ((hasDerivAt_sig_c a r c).fun_pow 2)) (mul_ne_zero hD (pow_ne_zero 2 hS))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris0_02_r (M a r c : ℝ) : ℝ :=
  -(2 * M * c * a ^ (2 : ℕ) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) + 3 * r ^ (2 : ℕ)) /
      sig a r c ^ (3 : ℕ))

private theorem hasDerivAt_chris0_02_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris0_02 M a s c) (dchris0_02_r M a r c) r := by
  unfold chris0_02 dchris0_02_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (HasDerivAt.const_mul (2 * M *
      c : ℝ) (hasDerivAt_id' r)) (a ^ 2 : ℝ)).fun_div ((hasDerivAt_sig_r a r c).fun_pow 2)
      (pow_ne_zero 2 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris0_02_c (M a r c : ℝ) : ℝ :=
  2 * M * r * a ^ (2 : ℕ) * (-(3 * a ^ (2 : ℕ) * c ^ (2 : ℕ)) + r ^ (2 : ℕ)) / sig a r c ^ (3 : ℕ)

private theorem hasDerivAt_chris0_02_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris0_02 M a r s) (dchris0_02_c M a r c) c := by
  unfold chris0_02 dchris0_02_c
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.const_mul
      (2 * M : ℝ) (hasDerivAt_id' c)) (r : ℝ)) (a ^ 2 : ℝ)).fun_div ((hasDerivAt_sig_c a r
      c).fun_pow 2) (pow_ne_zero 2 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris0_13_r (M a r c : ℝ) : ℝ :=
  -(2 * M * a * (c + 1) * (c - 1) * (M * a ^ (6 : ℕ) * c ^ (4 : ℕ) + M * a ^ (4 : ℕ) *
      c ^ (4 : ℕ) * r ^ (2 : ℕ) + 6 * M * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) + 6 *
      M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (4 : ℕ) - 3 * M * a ^ (2 : ℕ) * r ^ (4 : ℕ) - 3 *
      M * r ^ (6 : ℕ) - 2 * r * a ^ (6 : ℕ) * c ^ (4 : ℕ) - 3 * r * a ^ (6 : ℕ) * c ^ (2 : ℕ) -
      8 * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + a ^ (4 : ℕ) * r ^ (3 : ℕ) -
      a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (5 : ℕ) + 2 * a ^ (2 : ℕ) * r ^ (5 : ℕ) + 3 *
      r ^ (7 : ℕ)) / (del M a r ^ (2 : ℕ) * sig a r c ^ (3 : ℕ)))

private theorem hasDerivAt_chris0_13_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris0_13 M a s c) (dchris0_13_r M a r c) r := by
  unfold chris0_13 dchris0_13_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.const_mul (M * a * (c + 1) * (c -
      1) : ℝ) ((((hasDerivAt_const r (-(a ^ 4 * c ^ 2) : ℝ)).fun_add (HasDerivAt.const_mul (a ^ 2 *
      c ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 2))).fun_add (HasDerivAt.const_mul (a ^ 2 : ℝ)
      ((hasDerivAt_id' r).fun_pow 2))).fun_add (HasDerivAt.const_mul (3 : ℝ)
      ((hasDerivAt_id' r).fun_pow 4)))).fun_div ((hasDerivAt_del_r M a r).fun_mul ((hasDerivAt_sig_r
      a r c).fun_pow 2)) (mul_ne_zero hD (pow_ne_zero 2 hS))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris0_13_c (M a r c : ℝ) : ℝ :=
  2 * M * a * c * (a ^ (2 : ℕ) + r ^ (2 : ℕ)) ^ (2 : ℕ) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) +
      3 * r ^ (2 : ℕ)) / (del M a r * sig a r c ^ (3 : ℕ))

private theorem hasDerivAt_chris0_13_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris0_13 M a r s) (dchris0_13_c M a r c) c := by
  unfold chris0_13 dchris0_13_c
  refine HasDerivAt.congr_deriv ((((HasDerivAt.const_mul (M * a : ℝ)
      ((hasDerivAt_id' c).fun_add (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub
      (hasDerivAt_const c (1 : ℝ)))).fun_mul ((((HasDerivAt.const_mul (a ^ 4 : ℝ)
      ((hasDerivAt_id' c).fun_pow 2)).fun_neg.fun_add (HasDerivAt.mul_const (HasDerivAt.const_mul
      (a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2)) (r ^ 2 : ℝ))).fun_add (hasDerivAt_const c (a ^ 2 *
      r ^ 2 : ℝ))).fun_add (hasDerivAt_const c (3 * r ^ 4 : ℝ)))).fun_div (HasDerivAt.const_mul (del
      M a r : ℝ) ((hasDerivAt_sig_c a r c).fun_pow 2)) (mul_ne_zero hD (pow_ne_zero 2 hS))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris0_23_r (M a r c : ℝ) : ℝ :=
  -(2 * M * c * a ^ (3 : ℕ) * (c + 1) * (c - 1) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) + 3 *
      r ^ (2 : ℕ)) / sig a r c ^ (3 : ℕ))

private theorem hasDerivAt_chris0_23_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris0_23 M a s c) (dchris0_23_r M a r c) r := by
  unfold chris0_23 dchris0_23_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.mul_const
      (HasDerivAt.const_mul (2 * M * c : ℝ) (hasDerivAt_id' r)) (a ^ 3 : ℝ)) (c + 1 : ℝ))
      (c - 1 : ℝ)).fun_div ((hasDerivAt_sig_r a r c).fun_pow 2) (pow_ne_zero 2 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris0_23_c (M a r c : ℝ) : ℝ :=
  2 * M * r * a ^ (3 : ℕ) * (-(a ^ (2 : ℕ) * c ^ (4 : ℕ)) + 3 * a ^ (2 : ℕ) * c ^ (2 : ℕ) +
      3 * c ^ (2 : ℕ) * r ^ (2 : ℕ) - r ^ (2 : ℕ)) / sig a r c ^ (3 : ℕ)

private theorem hasDerivAt_chris0_23_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris0_23 M a r s) (dchris0_23_c M a r c) c := by
  unfold chris0_23 dchris0_23_c
  refine HasDerivAt.congr_deriv ((((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.const_mul
      (2 * M : ℝ) (hasDerivAt_id' c)) (r : ℝ)) (a ^ 3 : ℝ)).fun_mul ((hasDerivAt_id' c).fun_add
      (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub (hasDerivAt_const c
      (1 : ℝ)))).fun_div ((hasDerivAt_sig_c a r c).fun_pow 2) (pow_ne_zero 2 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_00_r (M a r c : ℝ) : ℝ :=
  -(2 * M * (-(M * a ^ (4 : ℕ) * c ^ (4 : ℕ)) + 8 * M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) -
      3 * M * r ^ (4 : ℕ) + r * a ^ (4 : ℕ) * c ^ (4 : ℕ) - 4 * r * a ^ (4 : ℕ) * c ^ (2 : ℕ) -
      4 * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + 2 * a ^ (2 : ℕ) * r ^ (3 : ℕ) +
      r ^ (5 : ℕ)) / sig a r c ^ (4 : ℕ))

private theorem hasDerivAt_chris1_00_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris1_00 M a s c) (dchris1_00_r M a r c) r := by
  unfold chris1_00 dchris1_00_r
  refine HasDerivAt.congr_deriv ((((HasDerivAt.mul_const (hasDerivAt_del_r M a r)
      (M : ℝ)).fun_mul ((hasDerivAt_const r (a * c : ℝ)).fun_add (hasDerivAt_id' r))).fun_mul
      ((hasDerivAt_const r (-(a * c) : ℝ)).fun_add (hasDerivAt_id' r))).fun_div ((hasDerivAt_sig_r a
      r c).fun_pow 3) (pow_ne_zero 3 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_00_c (M a r c : ℝ) : ℝ :=
  -(4 * del M a r * M * c * a ^ (2 : ℕ) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) + 2 * r ^ (2 : ℕ)) /
      sig a r c ^ (4 : ℕ))

private theorem hasDerivAt_chris1_00_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris1_00 M a r s) (dchris1_00_c M a r c) c := by
  unfold chris1_00 dchris1_00_c
  refine HasDerivAt.congr_deriv (((HasDerivAt.const_mul (del M a r * M : ℝ)
      ((HasDerivAt.const_mul (a : ℝ) (hasDerivAt_id' c)).fun_add (hasDerivAt_const c
      (r : ℝ)))).fun_mul ((HasDerivAt.const_mul (a : ℝ) (hasDerivAt_id' c)).fun_neg.fun_add
      (hasDerivAt_const c (r : ℝ)))).fun_div ((hasDerivAt_sig_c a r c).fun_pow 3)
      (pow_ne_zero 3 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_03_r (M a r c : ℝ) : ℝ :=
  -(2 * M * a * (c + 1) * (c - 1) * (-(M * a ^ (4 : ℕ) * c ^ (4 : ℕ)) + 8 * M *
      a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) - 3 * M * r ^ (4 : ℕ) + r * a ^ (4 : ℕ) *
      c ^ (4 : ℕ) - 4 * r * a ^ (4 : ℕ) * c ^ (2 : ℕ) - 4 * a ^ (2 : ℕ) * c ^ (2 : ℕ) *
      r ^ (3 : ℕ) + 2 * a ^ (2 : ℕ) * r ^ (3 : ℕ) + r ^ (5 : ℕ)) / sig a r c ^ (4 : ℕ))

private theorem hasDerivAt_chris1_03_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris1_03 M a s c) (dchris1_03_r M a r c) r := by
  unfold chris1_03 dchris1_03_r
  refine HasDerivAt.congr_deriv ((((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.mul_const
      (HasDerivAt.mul_const (hasDerivAt_del_r M a r) (M : ℝ)) (a : ℝ)) (c + 1 : ℝ))
      (c - 1 : ℝ)).fun_mul ((hasDerivAt_const r (a * c : ℝ)).fun_add (hasDerivAt_id' r))).fun_mul
      ((hasDerivAt_const r (-(a * c) : ℝ)).fun_add (hasDerivAt_id' r))).fun_div ((hasDerivAt_sig_r a
      r c).fun_pow 3) (pow_ne_zero 3 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_03_c (M a r c : ℝ) : ℝ :=
  2 * del M a r * M * a * c * (a ^ (4 : ℕ) * c ^ (4 : ℕ) - 2 * a ^ (4 : ℕ) * c ^ (2 : ℕ) -
      4 * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) + 4 * a ^ (2 : ℕ) * r ^ (2 : ℕ) +
      r ^ (4 : ℕ)) / sig a r c ^ (4 : ℕ)

private theorem hasDerivAt_chris1_03_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris1_03 M a r s) (dchris1_03_c M a r c) c := by
  unfold chris1_03 dchris1_03_c
  refine HasDerivAt.congr_deriv (((((HasDerivAt.const_mul (del M a r * M * a : ℝ)
      ((hasDerivAt_id' c).fun_add (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub
      (hasDerivAt_const c (1 : ℝ)))).fun_mul ((HasDerivAt.const_mul (a : ℝ)
      (hasDerivAt_id' c)).fun_add (hasDerivAt_const c (r : ℝ)))).fun_mul ((HasDerivAt.const_mul
      (a : ℝ) (hasDerivAt_id' c)).fun_neg.fun_add (hasDerivAt_const c (r : ℝ)))).fun_div
      ((hasDerivAt_sig_c a r c).fun_pow 3) (pow_ne_zero 3 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_11_r (M a r c : ℝ) : ℝ :=
  (2 * M ^ (2 : ℕ) * a ^ (4 : ℕ) * c ^ (4 : ℕ) + 8 * M ^ (2 : ℕ) * a ^ (2 : ℕ) *
      c ^ (2 : ℕ) * r ^ (2 : ℕ) - 2 * M ^ (2 : ℕ) * r ^ (4 : ℕ) - 2 * M * r *
      a ^ (4 : ℕ) * c ^ (4 : ℕ) - 4 * M * r * a ^ (4 : ℕ) * c ^ (2 : ℕ) - 8 * M *
      a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + 4 * M * a ^ (2 : ℕ) * r ^ (3 : ℕ) + 2 *
      M * r ^ (5 : ℕ) - a ^ (6 : ℕ) * c ^ (4 : ℕ) + a ^ (6 : ℕ) * c ^ (2 : ℕ) +
      a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) - a ^ (4 : ℕ) * r ^ (2 : ℕ) + 3 *
      a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (4 : ℕ) - 3 * a ^ (2 : ℕ) * r ^ (4 : ℕ)) /
      (del M a r ^ (2 : ℕ) * sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_chris1_11_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris1_11 M a s c) (dchris1_11_r M a r c) r := by
  unfold chris1_11 dchris1_11_r
  refine HasDerivAt.congr_deriv (((((hasDerivAt_const r (-(M * a ^ 2 *
      c ^ 2) : ℝ)).fun_add (HasDerivAt.const_mul (M : ℝ) ((hasDerivAt_id' r).fun_pow 2))).fun_add
      (HasDerivAt.mul_const (HasDerivAt.mul_const (hasDerivAt_id' r)
      (a ^ 2 : ℝ)) (c ^ 2 : ℝ))).fun_sub (HasDerivAt.mul_const (hasDerivAt_id' r)
      (a ^ 2 : ℝ))).fun_div ((hasDerivAt_del_r M a r).fun_mul (hasDerivAt_sig_r a r c))
      (mul_ne_zero hD hS)).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_11_c (a r c : ℝ) : ℝ :=
  -(2 * c * r * a ^ (2 : ℕ) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_chris1_11_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris1_11 M a r s) (dchris1_11_c a r c) c := by
  unfold chris1_11 dchris1_11_c
  refine HasDerivAt.congr_deriv (((((HasDerivAt.const_mul (M * a ^ 2 : ℝ)
      ((hasDerivAt_id' c).fun_pow 2)).fun_neg.fun_add (hasDerivAt_const c (M *
      r ^ 2 : ℝ))).fun_add (HasDerivAt.const_mul (r * a ^ 2 : ℝ)
      ((hasDerivAt_id' c).fun_pow 2))).fun_sub (hasDerivAt_const c (r *
      a ^ 2 : ℝ))).fun_div (HasDerivAt.const_mul (del M a r : ℝ)
      (hasDerivAt_sig_c a r c)) (mul_ne_zero hD hS)).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_12_r (a r c : ℝ) : ℝ :=
  -(2 * c * r * a ^ (2 : ℕ) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_chris1_12_r (a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris1_12 a s c) (dchris1_12_r a r c) r := by
  unfold chris1_12 dchris1_12_r
  refine HasDerivAt.congr_deriv ((hasDerivAt_const r (c * a ^ 2 : ℝ)).fun_div (hasDerivAt_sig_r a r
      c) hS) ?_
  generalize hSd : sig a r c = S at hS ⊢
  field_simp
  unfold sig at hSd
  subst hSd
  ring

private def dchris1_12_c (a r c : ℝ) : ℝ :=
  a ^ (2 : ℕ) * (a * c + r) * (-(a * c) + r) / sig a r c ^ (2 : ℕ)

private theorem hasDerivAt_chris1_12_c (a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris1_12 a r s) (dchris1_12_c a r c) c := by
  unfold chris1_12 dchris1_12_c
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (hasDerivAt_id' c)
      (a ^ 2 : ℝ)).fun_div (hasDerivAt_sig_c a r c) hS) ?_
  generalize hSd : sig a r c = S at hS ⊢
  field_simp
  unfold sig at hSd
  subst hSd
  ring

private def dchris1_22_r (M a r c : ℝ) : ℝ :=
  (-(4 * M * r * a ^ (2 : ℕ) * c ^ (2 : ℕ)) + a ^ (4 : ℕ) * c ^ (2 : ℕ) + 3 *
      a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) - a ^ (2 : ℕ) * r ^ (2 : ℕ) + r ^ (4 : ℕ)) /
      (sig a r c ^ (2 : ℕ) * (c + 1) * (c - 1))

private theorem hasDerivAt_chris1_22_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    HasDerivAt (fun s => chris1_22 M a s c) (dchris1_22_r M a r c) r := by
  unfold chris1_22 dchris1_22_r
  refine HasDerivAt.congr_deriv (((hasDerivAt_del_r M a r).fun_mul (hasDerivAt_id' r)).fun_div
      (HasDerivAt.mul_const (HasDerivAt.mul_const (hasDerivAt_sig_r a r c) (c + 1 : ℝ))
      (c - 1 : ℝ)) (mul_ne_zero (mul_ne_zero hS hc2) hc1)) ?_
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_22_c (M a r c : ℝ) : ℝ :=
  -(2 * del M a r * c * r * (2 * a ^ (2 : ℕ) * c ^ (2 : ℕ) - a ^ (2 : ℕ) + r ^ (2 : ℕ)) /
      (sig a r c ^ (2 : ℕ) * (c + 1) ^ (2 : ℕ) * (c - 1) ^ (2 : ℕ)))

private theorem hasDerivAt_chris1_22_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    HasDerivAt (fun s => chris1_22 M a r s) (dchris1_22_c M a r c) c := by
  unfold chris1_22 dchris1_22_c
  refine HasDerivAt.congr_deriv ((hasDerivAt_const c (del M a r *
      r : ℝ)).fun_div (((hasDerivAt_sig_c a r c).fun_mul ((hasDerivAt_id' c).fun_add
      (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub (hasDerivAt_const c
      (1 : ℝ)))) (mul_ne_zero (mul_ne_zero hS hc2) hc1)) ?_
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_33_r (M a r c : ℝ) : ℝ :=
  (c + 1) * (c - 1) * (2 * M ^ (2 : ℕ) * a ^ (6 : ℕ) * c ^ (6 : ℕ) - 2 * M ^ (2 : ℕ) *
      a ^ (6 : ℕ) * c ^ (4 : ℕ) - 16 * M ^ (2 : ℕ) * a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) +
      16 * M ^ (2 : ℕ) * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) + 6 * M ^ (2 : ℕ) *
      a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (4 : ℕ) - 6 * M ^ (2 : ℕ) * a ^ (2 : ℕ) * r ^ (4 : ℕ) - 6 *
      M * r * a ^ (6 : ℕ) * c ^ (6 : ℕ) + 10 * M * r * a ^ (6 : ℕ) * c ^ (4 : ℕ) - 8 * M *
      r * a ^ (6 : ℕ) * c ^ (2 : ℕ) - 12 * M * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + 4 *
      M * a ^ (4 : ℕ) * r ^ (3 : ℕ) - 6 * M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (5 : ℕ) + 2 *
      M * a ^ (2 : ℕ) * r ^ (5 : ℕ) + a ^ (8 : ℕ) * c ^ (6 : ℕ) + 3 * a ^ (6 : ℕ) *
      c ^ (6 : ℕ) * r ^ (2 : ℕ) + a ^ (6 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) + 7 *
      a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (4 : ℕ) - a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (4 : ℕ) +
      5 * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (6 : ℕ) - a ^ (2 : ℕ) * r ^ (6 : ℕ) + r ^ (8 : ℕ)) /
      sig a r c ^ (4 : ℕ)

private theorem hasDerivAt_chris1_33_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris1_33 M a s c) (dchris1_33_r M a r c) r := by
  unfold chris1_33 dchris1_33_r
  refine HasDerivAt.congr_deriv (((HasDerivAt.mul_const (HasDerivAt.mul_const (hasDerivAt_del_r M a
      r) (c + 1 : ℝ)) (c - 1 : ℝ)).fun_mul ((((((hasDerivAt_const r (-(M * a ^ 4 * c ^ 4) +
      M * a ^ 4 * c ^ 2 : ℝ)).fun_add (HasDerivAt.const_mul (M * a ^ 2 * c ^ 2 : ℝ)
      ((hasDerivAt_id' r).fun_pow 2))).fun_sub (HasDerivAt.const_mul (M *
      a ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 2))).fun_add (HasDerivAt.mul_const
      (HasDerivAt.mul_const (hasDerivAt_id' r) (a ^ 4 : ℝ)) (c ^ 4 : ℝ))).fun_add
      (HasDerivAt.const_mul (2 * a ^ 2 * c ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 3))).fun_add
      ((hasDerivAt_id' r).fun_pow 5))).fun_div ((hasDerivAt_sig_r a r c).fun_pow 3)
      (pow_ne_zero 3 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris1_33_c (M a r c : ℝ) : ℝ :=
  2 * del M a r * c * (-(2 * M * a ^ (6 : ℕ) * c ^ (4 : ℕ)) + 2 * M * a ^ (6 : ℕ) * c ^ (2 : ℕ) -
      4 * M * a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) + 8 * M * a ^ (4 : ℕ) *
      c ^ (2 : ℕ) * r ^ (2 : ℕ) - 4 * M * a ^ (4 : ℕ) * r ^ (2 : ℕ) + 2 * M *
      a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (4 : ℕ) - 2 * M * a ^ (2 : ℕ) * r ^ (4 : ℕ) + r *
      a ^ (6 : ℕ) * c ^ (4 : ℕ) + a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (3 : ℕ) + 2 *
      a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + 2 * a ^ (2 : ℕ) * c ^ (2 : ℕ) *
      r ^ (5 : ℕ) + a ^ (2 : ℕ) * r ^ (5 : ℕ) + r ^ (7 : ℕ)) / sig a r c ^ (4 : ℕ)

private theorem hasDerivAt_chris1_33_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris1_33 M a r s) (dchris1_33_c M a r c) c := by
  unfold chris1_33 dchris1_33_c
  refine HasDerivAt.congr_deriv ((((HasDerivAt.const_mul (del M a r : ℝ)
      ((hasDerivAt_id' c).fun_add (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub
      (hasDerivAt_const c (1 : ℝ)))).fun_mul (((((((HasDerivAt.const_mul (M *
      a ^ 4 : ℝ) ((hasDerivAt_id' c).fun_pow 4)).fun_neg.fun_add (HasDerivAt.const_mul (M *
      a ^ 4 : ℝ) ((hasDerivAt_id' c).fun_pow 2))).fun_add (HasDerivAt.mul_const
      (HasDerivAt.const_mul (M * a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2))
      (r ^ 2 : ℝ))).fun_sub (hasDerivAt_const c (M * a ^ 2 *
      r ^ 2 : ℝ))).fun_add (HasDerivAt.const_mul (r * a ^ 4 : ℝ)
      ((hasDerivAt_id' c).fun_pow 4))).fun_add (HasDerivAt.mul_const (HasDerivAt.const_mul (2 *
      a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2)) (r ^ 3 : ℝ))).fun_add (hasDerivAt_const c
      (r ^ 5 : ℝ)))).fun_div ((hasDerivAt_sig_c a r c).fun_pow 3) (pow_ne_zero 3 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris2_00_r (M a r c : ℝ) : ℝ :=
  2 * M * c * a ^ (2 : ℕ) * (c + 1) * (c - 1) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) + 5 *
      r ^ (2 : ℕ)) / sig a r c ^ (4 : ℕ)

private theorem hasDerivAt_chris2_00_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris2_00 M a s c) (dchris2_00_r M a r c) r := by
  unfold chris2_00 dchris2_00_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.mul_const
      (HasDerivAt.const_mul (2 * M * c : ℝ) (hasDerivAt_id' r)) (a ^ 2 : ℝ)) (c + 1 : ℝ))
      (c - 1 : ℝ)).fun_div ((hasDerivAt_sig_r a r c).fun_pow 3) (pow_ne_zero 3 hS)).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris2_00_c (M a r c : ℝ) : ℝ :=
  -(2 * M * r * a ^ (2 : ℕ) * (-(3 * a ^ (2 : ℕ) * c ^ (4 : ℕ)) + 5 * a ^ (2 : ℕ) * c ^ (2 : ℕ) +
      3 * c ^ (2 : ℕ) * r ^ (2 : ℕ) - r ^ (2 : ℕ)) / sig a r c ^ (4 : ℕ))

private theorem hasDerivAt_chris2_00_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris2_00 M a r s) (dchris2_00_c M a r c) c := by
  unfold chris2_00 dchris2_00_c
  refine HasDerivAt.congr_deriv ((((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.const_mul
      (2 * M : ℝ) (hasDerivAt_id' c)) (r : ℝ)) (a ^ 2 : ℝ)).fun_mul ((hasDerivAt_id' c).fun_add
      (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub (hasDerivAt_const c
      (1 : ℝ)))).fun_div ((hasDerivAt_sig_c a r c).fun_pow 3) (pow_ne_zero 3 hS)).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris2_03_r (M a r c : ℝ) : ℝ :=
  -(2 * M * a * c * (c + 1) * (c - 1) * (-(a ^ (4 : ℕ) * c ^ (2 : ℕ)) - 3 *
      a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) + 5 * a ^ (2 : ℕ) * r ^ (2 : ℕ) + 3 *
      r ^ (4 : ℕ)) / sig a r c ^ (4 : ℕ))

private theorem hasDerivAt_chris2_03_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris2_03 M a s c) (dchris2_03_r M a r c) r := by
  unfold chris2_03 dchris2_03_r
  refine HasDerivAt.congr_deriv (((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.const_mul
      (2 * M * a * c : ℝ) (hasDerivAt_id' r)) (c + 1 : ℝ)) (c -
      1 : ℝ)).fun_mul ((hasDerivAt_const r (a ^ 2 : ℝ)).fun_add ((hasDerivAt_id' r).fun_pow
      2))).fun_div ((hasDerivAt_sig_r a r c).fun_pow 3) (pow_ne_zero 3 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris2_03_c (M a r c : ℝ) : ℝ :=
  2 * M * a * r * (a ^ (2 : ℕ) + r ^ (2 : ℕ)) * (-(3 * a ^ (2 : ℕ) * c ^ (4 : ℕ)) + 5 *
      a ^ (2 : ℕ) * c ^ (2 : ℕ) + 3 * c ^ (2 : ℕ) * r ^ (2 : ℕ) - r ^ (2 : ℕ)) / sig a r c ^ (4 : ℕ)

private theorem hasDerivAt_chris2_03_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris2_03 M a r s) (dchris2_03_c M a r c) c := by
  unfold chris2_03 dchris2_03_c
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (((HasDerivAt.mul_const (HasDerivAt.const_mul
      (2 * M * a : ℝ) (hasDerivAt_id' c)) (r : ℝ)).fun_mul ((hasDerivAt_id' c).fun_add
      (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub (hasDerivAt_const c
      (1 : ℝ)))) (a ^ 2 + r ^ 2 : ℝ)).fun_div ((hasDerivAt_sig_c a r c).fun_pow 3)
      (pow_ne_zero 3 hS)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris2_11_r (M a r c : ℝ) : ℝ :=
  -(2 * c * a ^ (2 : ℕ) * (c + 1) * (c - 1) * (-(M * a ^ (2 : ℕ) * c ^ (2 : ℕ)) - 3 *
      M * r ^ (2 : ℕ) + r * a ^ (2 : ℕ) * c ^ (2 : ℕ) + r * a ^ (2 : ℕ) + 2 * r ^ (3 : ℕ)) /
      (del M a r ^ (2 : ℕ) * sig a r c ^ (2 : ℕ)))

private theorem hasDerivAt_chris2_11_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris2_11 M a s c) (dchris2_11_r M a r c) r := by
  unfold chris2_11 dchris2_11_r
  refine HasDerivAt.congr_deriv ((hasDerivAt_const r (c * a ^ 2 * (c + 1) * (c -
      1) : ℝ)).fun_div ((hasDerivAt_del_r M a r).fun_mul (hasDerivAt_sig_r a r c))
      (mul_ne_zero hD hS)) ?_
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris2_11_c (M a r c : ℝ) : ℝ :=
  a ^ (2 : ℕ) * (a ^ (2 : ℕ) * c ^ (4 : ℕ) + a ^ (2 : ℕ) * c ^ (2 : ℕ) + 3 *
      c ^ (2 : ℕ) * r ^ (2 : ℕ) - r ^ (2 : ℕ)) / (del M a r * sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_chris2_11_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris2_11 M a r s) (dchris2_11_c M a r c) c := by
  unfold chris2_11 dchris2_11_c
  refine HasDerivAt.congr_deriv ((((HasDerivAt.mul_const (hasDerivAt_id' c)
      (a ^ 2 : ℝ)).fun_mul ((hasDerivAt_id' c).fun_add (hasDerivAt_const c (1 : ℝ)))).fun_mul
      ((hasDerivAt_id' c).fun_sub (hasDerivAt_const c (1 : ℝ)))).fun_div (HasDerivAt.const_mul (del
      M a r : ℝ) (hasDerivAt_sig_c a r c)) (mul_ne_zero hD hS)) ?_
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris2_12_r (a r c : ℝ) : ℝ :=
  -((a * c + r) * (-(a * c) + r) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_chris2_12_r (a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris2_12 a s c) (dchris2_12_r a r c) r := by
  unfold chris2_12 dchris2_12_r
  refine HasDerivAt.congr_deriv ((hasDerivAt_id' r).fun_div (hasDerivAt_sig_r a r c) hS) ?_
  generalize hSd : sig a r c = S at hS ⊢
  field_simp
  unfold sig at hSd
  subst hSd
  ring

private def dchris2_12_c (a r c : ℝ) : ℝ :=
  -(2 * c * r * a ^ (2 : ℕ) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_chris2_12_c (a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris2_12 a r s) (dchris2_12_c a r c) c := by
  unfold chris2_12 dchris2_12_c
  refine HasDerivAt.congr_deriv ((hasDerivAt_const c (r : ℝ)).fun_div (hasDerivAt_sig_c a r c) hS)
      ?_
  generalize hSd : sig a r c = S at hS ⊢
  field_simp
  unfold sig at hSd
  subst hSd
  ring

private def dchris2_22_r (a r c : ℝ) : ℝ :=
  -(2 * c * r * a ^ (2 : ℕ) / sig a r c ^ (2 : ℕ))

private theorem hasDerivAt_chris2_22_r (a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    HasDerivAt (fun s => chris2_22 a s c) (dchris2_22_r a r c) r := by
  unfold chris2_22 dchris2_22_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.const_mul (c : ℝ)
      ((hasDerivAt_const r (a ^ 2 : ℝ)).fun_add ((hasDerivAt_id' r).fun_pow 2))).fun_div
      (HasDerivAt.mul_const (HasDerivAt.mul_const (hasDerivAt_sig_r a r c) (c + 1 : ℝ))
      (c - 1 : ℝ)) (mul_ne_zero (mul_ne_zero hS hc2) hc1)).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  field_simp
  unfold sig at hSd
  subst hSd
  ring

private def dchris2_22_c (a r c : ℝ) : ℝ :=
  (a ^ (2 : ℕ) + r ^ (2 : ℕ)) * (3 * a ^ (2 : ℕ) * c ^ (4 : ℕ) - a ^ (2 : ℕ) *
      c ^ (2 : ℕ) + c ^ (2 : ℕ) * r ^ (2 : ℕ) + r ^ (2 : ℕ)) / (sig a r c ^ (2 : ℕ) *
      (c + 1) ^ (2 : ℕ) * (c - 1) ^ (2 : ℕ))

private theorem hasDerivAt_chris2_22_c (a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    HasDerivAt (fun s => chris2_22 a r s) (dchris2_22_c a r c) c := by
  unfold chris2_22 dchris2_22_c
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (hasDerivAt_id' c)
      (a ^ 2 + r ^ 2 : ℝ)).fun_div (((hasDerivAt_sig_c a r c).fun_mul ((hasDerivAt_id' c).fun_add
      (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub (hasDerivAt_const c
      (1 : ℝ)))) (mul_ne_zero (mul_ne_zero hS hc2) hc1)).fun_neg ?_
  generalize hSd : sig a r c = S at hS ⊢
  field_simp
  unfold sig at hSd
  subst hSd
  ring

private def dchris2_33_r (M a r c : ℝ) : ℝ :=
  -(2 * c * a ^ (2 : ℕ) * (c + 1) ^ (2 : ℕ) * (c - 1) ^ (2 : ℕ) * (-(M * a ^ (4 : ℕ) *
      c ^ (4 : ℕ)) - M * a ^ (4 : ℕ) * c ^ (2 : ℕ) - M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) +
      5 * M * a ^ (2 : ℕ) * r ^ (2 : ℕ) + 6 * M * r ^ (4 : ℕ) + r * a ^ (4 : ℕ) * c ^ (4 : ℕ) +
      2 * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + r ^ (5 : ℕ)) / sig a r c ^ (4 : ℕ))

private theorem hasDerivAt_chris2_33_r (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris2_33 M a s c) (dchris2_33_r M a r c) r := by
  unfold chris2_33 dchris2_33_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.const_mul (c * (c + 1) * (c -
      1) : ℝ) ((((((((((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.const_mul (2 *
      M : ℝ) (hasDerivAt_id' r)) (a ^ 4 : ℝ)) (c ^ 4 : ℝ)).fun_neg.fun_add (HasDerivAt.mul_const
      (HasDerivAt.const_mul (2 * M : ℝ) (hasDerivAt_id' r)) (a ^ 4 : ℝ))).fun_sub
      (HasDerivAt.const_mul (4 * M * a ^ 2 * c ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 3))).fun_add
      (HasDerivAt.const_mul (4 * M * a ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 3))).fun_add
      (hasDerivAt_const r (a ^ 6 * c ^ 4 : ℝ))).fun_add (HasDerivAt.const_mul (a ^ 4 *
      c ^ 4 : ℝ) ((hasDerivAt_id' r).fun_pow 2))).fun_add (HasDerivAt.const_mul (2 *
      a ^ 4 * c ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 2))).fun_add (HasDerivAt.const_mul (2 *
      a ^ 2 * c ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 4))).fun_add (HasDerivAt.const_mul (a ^ 2 : ℝ)
      ((hasDerivAt_id' r).fun_pow 4))).fun_add ((hasDerivAt_id' r).fun_pow 6))).fun_div
      ((hasDerivAt_sig_r a r c).fun_pow 3) (pow_ne_zero 3 hS)).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris2_33_c (M a r c : ℝ) : ℝ :=
  -((-(2 * M * r * a ^ (6 : ℕ) * c ^ (8 : ℕ)) - 2 * M * r * a ^ (6 : ℕ) * c ^ (6 : ℕ) - 6 * M *
      r * a ^ (6 : ℕ) * c ^ (4 : ℕ) + 10 * M * r * a ^ (6 : ℕ) * c ^ (2 : ℕ) - 10 * M *
      a ^ (4 : ℕ) * c ^ (6 : ℕ) * r ^ (3 : ℕ) - 14 * M * a ^ (4 : ℕ) * c ^ (4 : ℕ) *
      r ^ (3 : ℕ) + 26 * M * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) - 2 * M *
      a ^ (4 : ℕ) * r ^ (3 : ℕ) - 20 * M * a ^ (2 : ℕ) * c ^ (4 : ℕ) * r ^ (5 : ℕ) + 24 *
      M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (5 : ℕ) - 4 * M * a ^ (2 : ℕ) * r ^ (5 : ℕ) +
      a ^ (8 : ℕ) * c ^ (8 : ℕ) + a ^ (8 : ℕ) * c ^ (6 : ℕ) + a ^ (6 : ℕ) *
      c ^ (8 : ℕ) * r ^ (2 : ℕ) + 6 * a ^ (6 : ℕ) * c ^ (6 : ℕ) * r ^ (2 : ℕ) +
      a ^ (6 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) + 5 * a ^ (4 : ℕ) * c ^ (6 : ℕ) * r ^ (4 : ℕ) +
      8 * a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (4 : ℕ) - a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (4 : ℕ) +
      7 * a ^ (2 : ℕ) * c ^ (4 : ℕ) * r ^ (6 : ℕ) + 2 * a ^ (2 : ℕ) * c ^ (2 : ℕ) *
      r ^ (6 : ℕ) - a ^ (2 : ℕ) * r ^ (6 : ℕ) + 3 * c ^ (2 : ℕ) * r ^ (8 : ℕ) - r ^ (8 : ℕ)) /
      sig a r c ^ (4 : ℕ))

private theorem hasDerivAt_chris2_33_c (M a r c : ℝ) (hS : sig a r c ≠ 0) :
    HasDerivAt (fun s => chris2_33 M a r s) (dchris2_33_c M a r c) c := by
  unfold chris2_33 dchris2_33_c
  refine HasDerivAt.congr_deriv (((((hasDerivAt_id' c).fun_mul ((hasDerivAt_id' c).fun_add
      (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub (hasDerivAt_const c
      (1 : ℝ)))).fun_mul ((((((((((HasDerivAt.const_mul (2 * M * r * a ^ 4 : ℝ)
      ((hasDerivAt_id' c).fun_pow 4)).fun_neg.fun_add (hasDerivAt_const c (2 * M *
      r * a ^ 4 : ℝ))).fun_sub (HasDerivAt.mul_const (HasDerivAt.const_mul (4 * M *
      a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2)) (r ^ 3 : ℝ))).fun_add (hasDerivAt_const c (4 *
      M * a ^ 2 * r ^ 3 : ℝ))).fun_add (HasDerivAt.const_mul (a ^ 6 : ℝ)
      ((hasDerivAt_id' c).fun_pow 4))).fun_add (HasDerivAt.mul_const (HasDerivAt.const_mul
      (a ^ 4 : ℝ) ((hasDerivAt_id' c).fun_pow 4)) (r ^ 2 : ℝ))).fun_add (HasDerivAt.mul_const
      (HasDerivAt.const_mul (2 * a ^ 4 : ℝ) ((hasDerivAt_id' c).fun_pow 2))
      (r ^ 2 : ℝ))).fun_add (HasDerivAt.mul_const (HasDerivAt.const_mul (2 *
      a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2)) (r ^ 4 : ℝ))).fun_add (hasDerivAt_const c (a ^ 2 *
      r ^ 4 : ℝ))).fun_add (hasDerivAt_const c (r ^ 6 : ℝ)))).fun_div ((hasDerivAt_sig_c a r
      c).fun_pow 3) (pow_ne_zero 3 hS)).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris3_01_r (M a r c : ℝ) : ℝ :=
  -(2 * M * a * (M * a ^ (4 : ℕ) * c ^ (4 : ℕ) + 6 * M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) -
      3 * M * r ^ (4 : ℕ) - r * a ^ (4 : ℕ) * c ^ (4 : ℕ) - 3 * r * a ^ (4 : ℕ) * c ^ (2 : ℕ) -
      3 * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + a ^ (2 : ℕ) * r ^ (3 : ℕ) + 2 *
      r ^ (5 : ℕ)) / (del M a r ^ (2 : ℕ) * sig a r c ^ (3 : ℕ)))

private theorem hasDerivAt_chris3_01_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris3_01 M a s c) (dchris3_01_r M a r c) r := by
  unfold chris3_01 dchris3_01_r
  refine HasDerivAt.congr_deriv (((HasDerivAt.const_mul (M * a : ℝ)
      ((hasDerivAt_const r (a * c : ℝ)).fun_add (hasDerivAt_id' r))).fun_mul ((hasDerivAt_const r
      (-(a * c) : ℝ)).fun_add (hasDerivAt_id' r))).fun_div ((hasDerivAt_del_r M a r).fun_mul
      ((hasDerivAt_sig_r a r c).fun_pow 2)) (mul_ne_zero hD (pow_ne_zero 2 hS))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris3_01_c (M a r c : ℝ) : ℝ :=
  -(2 * M * c * a ^ (3 : ℕ) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) + 3 * r ^ (2 : ℕ)) / (del M a r *
      sig a r c ^ (3 : ℕ)))

private theorem hasDerivAt_chris3_01_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris3_01 M a r s) (dchris3_01_c M a r c) c := by
  unfold chris3_01 dchris3_01_c
  refine HasDerivAt.congr_deriv (((HasDerivAt.const_mul (M * a : ℝ)
      ((HasDerivAt.const_mul (a : ℝ) (hasDerivAt_id' c)).fun_add (hasDerivAt_const c
      (r : ℝ)))).fun_mul ((HasDerivAt.const_mul (a : ℝ) (hasDerivAt_id' c)).fun_neg.fun_add
      (hasDerivAt_const c (r : ℝ)))).fun_div (HasDerivAt.const_mul (del M a r : ℝ)
      ((hasDerivAt_sig_c a r c).fun_pow 2)) (mul_ne_zero hD (pow_ne_zero 2 hS))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris3_02_r (M a r c : ℝ) : ℝ :=
  2 * M * a * c * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) + 3 * r ^ (2 : ℕ)) / (sig a r c ^ (3 : ℕ) * (c +
      1) * (c - 1))

private theorem hasDerivAt_chris3_02_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    HasDerivAt (fun s => chris3_02 M a s c) (dchris3_02_r M a r c) r := by
  unfold chris3_02 dchris3_02_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.const_mul (2 * M * a * c : ℝ)
      (hasDerivAt_id' r)).fun_div (HasDerivAt.mul_const (HasDerivAt.mul_const ((hasDerivAt_sig_r a r
      c).fun_pow 2) (c + 1 : ℝ)) (c - 1 : ℝ)) (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hS) hc2)
      hc1)).fun_neg ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris3_02_c (M a r c : ℝ) : ℝ :=
  2 * M * a * r * (5 * a ^ (2 : ℕ) * c ^ (4 : ℕ) - 3 * a ^ (2 : ℕ) * c ^ (2 : ℕ) +
      c ^ (2 : ℕ) * r ^ (2 : ℕ) + r ^ (2 : ℕ)) / (sig a r c ^ (3 : ℕ) * (c + 1) ^ (2 : ℕ) *
      (c - 1) ^ (2 : ℕ))

private theorem hasDerivAt_chris3_02_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    HasDerivAt (fun s => chris3_02 M a r s) (dchris3_02_c M a r c) c := by
  unfold chris3_02 dchris3_02_c
  refine HasDerivAt.congr_deriv ((HasDerivAt.mul_const (HasDerivAt.const_mul (2 * M *
      a : ℝ) (hasDerivAt_id' c)) (r : ℝ)).fun_div ((((hasDerivAt_sig_c a r c).fun_pow 2).fun_mul
      ((hasDerivAt_id' c).fun_add (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub
      (hasDerivAt_const c (1 : ℝ)))) (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hS) hc2) hc1)).fun_neg
      ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris3_13_r (M a r c : ℝ) : ℝ :=
  -((2 * M ^ (2 : ℕ) * a ^ (6 : ℕ) * c ^ (6 : ℕ) - 2 * M ^ (2 : ℕ) * a ^ (6 : ℕ) * c ^ (4 : ℕ) +
      8 * M ^ (2 : ℕ) * a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) - 12 * M ^ (2 : ℕ) *
      a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (2 : ℕ) - 6 * M ^ (2 : ℕ) * a ^ (2 : ℕ) *
      c ^ (2 : ℕ) * r ^ (4 : ℕ) + 6 * M ^ (2 : ℕ) * a ^ (2 : ℕ) * r ^ (4 : ℕ) + 4 *
      M ^ (2 : ℕ) * r ^ (6 : ℕ) - 2 * M * r * a ^ (6 : ℕ) * c ^ (6 : ℕ) + 6 * M * r *
      a ^ (6 : ℕ) * c ^ (2 : ℕ) - 6 * M * a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (3 : ℕ) + 12 *
      M * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) - 2 * M * a ^ (4 : ℕ) * r ^ (3 : ℕ) - 4 *
      M * a ^ (2 : ℕ) * r ^ (5 : ℕ) - 4 * M * r ^ (7 : ℕ) - a ^ (8 : ℕ) * c ^ (6 : ℕ) +
      a ^ (6 : ℕ) * c ^ (6 : ℕ) * r ^ (2 : ℕ) - 3 * a ^ (6 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) +
      3 * a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (4 : ℕ) - 3 * a ^ (4 : ℕ) * c ^ (2 : ℕ) * r ^ (4 : ℕ) +
      3 * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (6 : ℕ) - a ^ (2 : ℕ) * r ^ (6 : ℕ) + r ^ (8 : ℕ)) /
      (del M a r ^ (2 : ℕ) * sig a r c ^ (3 : ℕ)))

private theorem hasDerivAt_chris3_13_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris3_13 M a s c) (dchris3_13_r M a r c) r := by
  unfold chris3_13 dchris3_13_r
  refine HasDerivAt.congr_deriv ((((((((hasDerivAt_const r (-(M * a ^ 4 * c ^ 4) + M *
      a ^ 4 * c ^ 2 : ℝ)).fun_sub (HasDerivAt.const_mul (M * a ^ 2 * c ^ 2 : ℝ)
      ((hasDerivAt_id' r).fun_pow 2))).fun_sub (HasDerivAt.const_mul (M *
      a ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 2))).fun_sub (HasDerivAt.const_mul (2 *
      M : ℝ) ((hasDerivAt_id' r).fun_pow 4))).fun_add (HasDerivAt.mul_const (HasDerivAt.mul_const
      (hasDerivAt_id' r) (a ^ 4 : ℝ)) (c ^ 4 : ℝ))).fun_add (HasDerivAt.const_mul (2 *
      a ^ 2 * c ^ 2 : ℝ) ((hasDerivAt_id' r).fun_pow 3))).fun_add ((hasDerivAt_id' r).fun_pow
      5)).fun_div ((hasDerivAt_del_r M a r).fun_mul ((hasDerivAt_sig_r a r c).fun_pow 2))
      (mul_ne_zero hD (pow_ne_zero 2 hS))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris3_13_c (M a r c : ℝ) : ℝ :=
  2 * M * c * a ^ (2 : ℕ) * (a ^ (2 : ℕ) + r ^ (2 : ℕ)) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) +
      3 * r ^ (2 : ℕ)) / (del M a r * sig a r c ^ (3 : ℕ))

private theorem hasDerivAt_chris3_13_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    HasDerivAt (fun s => chris3_13 M a r s) (dchris3_13_c M a r c) c := by
  unfold chris3_13 dchris3_13_c
  refine HasDerivAt.congr_deriv (((((((((HasDerivAt.const_mul (M * a ^ 4 : ℝ)
      ((hasDerivAt_id' c).fun_pow 4)).fun_neg.fun_add (HasDerivAt.const_mul (M *
      a ^ 4 : ℝ) ((hasDerivAt_id' c).fun_pow 2))).fun_sub (HasDerivAt.mul_const
      (HasDerivAt.const_mul (M * a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2))
      (r ^ 2 : ℝ))).fun_sub (hasDerivAt_const c (M * a ^ 2 *
      r ^ 2 : ℝ))).fun_sub (hasDerivAt_const c (2 * M * r ^ 4 : ℝ))).fun_add (HasDerivAt.const_mul
      (r * a ^ 4 : ℝ) ((hasDerivAt_id' c).fun_pow 4))).fun_add (HasDerivAt.mul_const
      (HasDerivAt.const_mul (2 * a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2))
      (r ^ 3 : ℝ))).fun_add (hasDerivAt_const c (r ^ 5 : ℝ))).fun_div (HasDerivAt.const_mul (del M a
      r : ℝ) ((hasDerivAt_sig_c a r c).fun_pow 2)) (mul_ne_zero hD (pow_ne_zero 2 hS))) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris3_23_r (M a r c : ℝ) : ℝ :=
  2 * M * c * a ^ (2 : ℕ) * (-(a ^ (2 : ℕ) * c ^ (2 : ℕ)) + 3 * r ^ (2 : ℕ)) / sig a r c ^ (3 : ℕ)

private theorem hasDerivAt_chris3_23_r (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    HasDerivAt (fun s => chris3_23 M a s c) (dchris3_23_r M a r c) r := by
  unfold chris3_23 dchris3_23_r
  refine HasDerivAt.congr_deriv ((HasDerivAt.const_mul (c : ℝ)
      (((((HasDerivAt.mul_const (HasDerivAt.mul_const (HasDerivAt.const_mul (2 *
      M : ℝ) (hasDerivAt_id' r)) (a ^ 2 : ℝ)) (c ^ 2 : ℝ)).fun_neg.fun_add (HasDerivAt.mul_const
      (HasDerivAt.const_mul (2 * M : ℝ) (hasDerivAt_id' r)) (a ^ 2 : ℝ))).fun_add (hasDerivAt_const
      r (a ^ 4 * c ^ 4 : ℝ))).fun_add (HasDerivAt.const_mul (2 * a ^ 2 * c ^ 2 : ℝ)
      ((hasDerivAt_id' r).fun_pow 2))).fun_add ((hasDerivAt_id' r).fun_pow 4))).fun_div
      (HasDerivAt.mul_const (HasDerivAt.mul_const ((hasDerivAt_sig_r a r c).fun_pow 2)
      (c + 1 : ℝ)) (c - 1 : ℝ)) (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hS) hc2) hc1)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def dchris3_23_c (M a r c : ℝ) : ℝ :=
  -((-(6 * M * r * a ^ (4 : ℕ) * c ^ (6 : ℕ)) + 12 * M * r * a ^ (4 : ℕ) * c ^ (4 : ℕ) - 6 * M *
      r * a ^ (4 : ℕ) * c ^ (2 : ℕ) + 2 * M * a ^ (2 : ℕ) * c ^ (4 : ℕ) * r ^ (3 : ℕ) - 4 *
      M * a ^ (2 : ℕ) * c ^ (2 : ℕ) * r ^ (3 : ℕ) + 2 * M * a ^ (2 : ℕ) * r ^ (3 : ℕ) +
      a ^ (6 : ℕ) * c ^ (8 : ℕ) + a ^ (6 : ℕ) * c ^ (6 : ℕ) + 3 * a ^ (4 : ℕ) *
      c ^ (6 : ℕ) * r ^ (2 : ℕ) + 3 * a ^ (4 : ℕ) * c ^ (4 : ℕ) * r ^ (2 : ℕ) + 3 *
      a ^ (2 : ℕ) * c ^ (4 : ℕ) * r ^ (4 : ℕ) + 3 * a ^ (2 : ℕ) * c ^ (2 : ℕ) *
      r ^ (4 : ℕ) + c ^ (2 : ℕ) * r ^ (6 : ℕ) + r ^ (6 : ℕ)) / (sig a r c ^ (3 : ℕ) *
      (c + 1) ^ (2 : ℕ) * (c - 1) ^ (2 : ℕ)))

private theorem hasDerivAt_chris3_23_c (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    HasDerivAt (fun s => chris3_23 M a r s) (dchris3_23_c M a r c) c := by
  unfold chris3_23 dchris3_23_c
  refine HasDerivAt.congr_deriv (((hasDerivAt_id' c).fun_mul (((((HasDerivAt.const_mul (2 * M *
      r * a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2)).fun_neg.fun_add (hasDerivAt_const c (2 * M *
      r * a ^ 2 : ℝ))).fun_add (HasDerivAt.const_mul (a ^ 4 : ℝ)
      ((hasDerivAt_id' c).fun_pow 4))).fun_add (HasDerivAt.mul_const (HasDerivAt.const_mul (2 *
      a ^ 2 : ℝ) ((hasDerivAt_id' c).fun_pow 2)) (r ^ 2 : ℝ))).fun_add (hasDerivAt_const c
      (r ^ 4 : ℝ)))).fun_div ((((hasDerivAt_sig_c a r c).fun_pow 2).fun_mul ((hasDerivAt_id'
      c).fun_add (hasDerivAt_const c (1 : ℝ)))).fun_mul ((hasDerivAt_id' c).fun_sub
      (hasDerivAt_const c (1 : ℝ)))) (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hS) hc2) hc1)) ?_
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private def christoffelR (M a r c : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, dchris0_01_r M a r c, dchris0_02_r M a r c, 0],
      ![dchris0_01_r M a r c, 0, 0, dchris0_13_r M a r c],
      ![dchris0_02_r M a r c, 0, 0, dchris0_23_r M a r c],
      ![0, dchris0_13_r M a r c, dchris0_23_r M a r c, 0]],
    ![![dchris1_00_r M a r c, 0, 0, dchris1_03_r M a r c],
      ![0, dchris1_11_r M a r c, dchris1_12_r a r c, 0],
      ![0, dchris1_12_r a r c, dchris1_22_r M a r c, 0],
      ![dchris1_03_r M a r c, 0, 0, dchris1_33_r M a r c]],
    ![![dchris2_00_r M a r c, 0, 0, dchris2_03_r M a r c],
      ![0, dchris2_11_r M a r c, dchris2_12_r a r c, 0],
      ![0, dchris2_12_r a r c, dchris2_22_r a r c, 0],
      ![dchris2_03_r M a r c, 0, 0, dchris2_33_r M a r c]],
    ![![0, dchris3_01_r M a r c, dchris3_02_r M a r c, 0],
      ![dchris3_01_r M a r c, 0, 0, dchris3_13_r M a r c],
      ![dchris3_02_r M a r c, 0, 0, dchris3_23_r M a r c],
      ![0, dchris3_13_r M a r c, dchris3_23_r M a r c, 0]]]

private def christoffelC (M a r c : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, dchris0_01_c M a r c, dchris0_02_c M a r c, 0],
      ![dchris0_01_c M a r c, 0, 0, dchris0_13_c M a r c],
      ![dchris0_02_c M a r c, 0, 0, dchris0_23_c M a r c],
      ![0, dchris0_13_c M a r c, dchris0_23_c M a r c, 0]],
    ![![dchris1_00_c M a r c, 0, 0, dchris1_03_c M a r c],
      ![0, dchris1_11_c a r c, dchris1_12_c a r c, 0],
      ![0, dchris1_12_c a r c, dchris1_22_c M a r c, 0],
      ![dchris1_03_c M a r c, 0, 0, dchris1_33_c M a r c]],
    ![![dchris2_00_c M a r c, 0, 0, dchris2_03_c M a r c],
      ![0, dchris2_11_c M a r c, dchris2_12_c a r c, 0],
      ![0, dchris2_12_c a r c, dchris2_22_c a r c, 0],
      ![dchris2_03_c M a r c, 0, 0, dchris2_33_c M a r c]],
    ![![0, dchris3_01_c M a r c, dchris3_02_c M a r c, 0],
      ![dchris3_01_c M a r c, 0, 0, dchris3_13_c M a r c],
      ![dchris3_02_c M a r c, 0, 0, dchris3_23_c M a r c],
      ![0, dchris3_13_c M a r c, dchris3_23_c M a r c, 0]]]

private theorem hasDerivAt_christoffelTable_r (M a r c : ℝ) (hS : sig a r c ≠ 0)
    (hD : del M a r ≠ 0) (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) (q i j : Fin 4) :
    HasDerivAt (fun s => christoffelTable M a s c q i j) (christoffelR M a r c q i j) r := by
  fin_cases q <;> fin_cases i <;> fin_cases j
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris0_01_r M a r c hS hD
  · exact hasDerivAt_chris0_02_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris0_01_r M a r c hS hD
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris0_13_r M a r c hS hD
  · exact hasDerivAt_chris0_02_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris0_23_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris0_13_r M a r c hS hD
  · exact hasDerivAt_chris0_23_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris1_00_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris1_03_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris1_11_r M a r c hS hD
  · exact hasDerivAt_chris1_12_r a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris1_12_r a r c hS
  · exact hasDerivAt_chris1_22_r M a r c hS hc1 hc2
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris1_03_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris1_33_r M a r c hS
  · exact hasDerivAt_chris2_00_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris2_03_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris2_11_r M a r c hS hD
  · exact hasDerivAt_chris2_12_r a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris2_12_r a r c hS
  · exact hasDerivAt_chris2_22_r a r c hS hc1 hc2
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris2_03_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris2_33_r M a r c hS
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris3_01_r M a r c hS hD
  · exact hasDerivAt_chris3_02_r M a r c hS hc1 hc2
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris3_01_r M a r c hS hD
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris3_13_r M a r c hS hD
  · exact hasDerivAt_chris3_02_r M a r c hS hc1 hc2
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris3_23_r M a r c hS hc1 hc2
  · exact hasDerivAt_const r (0 : ℝ)
  · exact hasDerivAt_chris3_13_r M a r c hS hD
  · exact hasDerivAt_chris3_23_r M a r c hS hc1 hc2
  · exact hasDerivAt_const r (0 : ℝ)

private theorem hasDerivAt_christoffelTable_c (M a r c : ℝ) (hS : sig a r c ≠ 0)
    (hD : del M a r ≠ 0) (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) (q i j : Fin 4) :
    HasDerivAt (fun s => christoffelTable M a r s q i j) (christoffelC M a r c q i j) c := by
  fin_cases q <;> fin_cases i <;> fin_cases j
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris0_01_c M a r c hS hD
  · exact hasDerivAt_chris0_02_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris0_01_c M a r c hS hD
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris0_13_c M a r c hS hD
  · exact hasDerivAt_chris0_02_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris0_23_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris0_13_c M a r c hS hD
  · exact hasDerivAt_chris0_23_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris1_00_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris1_03_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris1_11_c M a r c hS hD
  · exact hasDerivAt_chris1_12_c a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris1_12_c a r c hS
  · exact hasDerivAt_chris1_22_c M a r c hS hc1 hc2
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris1_03_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris1_33_c M a r c hS
  · exact hasDerivAt_chris2_00_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris2_03_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris2_11_c M a r c hS hD
  · exact hasDerivAt_chris2_12_c a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris2_12_c a r c hS
  · exact hasDerivAt_chris2_22_c a r c hS hc1 hc2
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris2_03_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris2_33_c M a r c hS
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris3_01_c M a r c hS hD
  · exact hasDerivAt_chris3_02_c M a r c hS hc1 hc2
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris3_01_c M a r c hS hD
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris3_13_c M a r c hS hD
  · exact hasDerivAt_chris3_02_c M a r c hS hc1 hc2
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris3_23_c M a r c hS hc1 hc2
  · exact hasDerivAt_const c (0 : ℝ)
  · exact hasDerivAt_chris3_13_c M a r c hS hD
  · exact hasDerivAt_chris3_23_c M a r c hS hc1 hc2
  · exact hasDerivAt_const c (0 : ℝ)

/-- The partial derivatives `∂_l Γ^k_{ij}`: zero along `t` and `φ`. -/
private def christoffelPartial (M a : ℝ) (l : Fin 4) (r c : ℝ) (k i j : Fin 4) : ℝ :=
  ![0, christoffelR M a r c k i j, christoffelC M a r c k i j, 0] l

/-- A function of `r = w 1` and `χ = w 2` has the partial derivatives `0`, `∂_r F`, `∂_χ F`,
`0`. -/
private theorem fderiv_apply_rc {F : ℝ → ℝ → ℝ} {y : MinkowskiModel 3}
    (hF : DifferentiableAt ℝ (fun w : MinkowskiModel 3 => F (w 1) (w 2)) y) {Fr Fc : ℝ}
    (hr : HasDerivAt (fun s => F s (y 2)) Fr (y 1))
    (hc : HasDerivAt (fun s => F (y 1) s) Fc (y 2)) (l : Fin 4) :
    fderiv ℝ (fun w : MinkowskiModel 3 => F (w 1) (w 2)) y (Pi.single l 1) =
      ![0, Fr, Fc, 0] l := by
  rw [CoordinateMetric.fderiv_single_eq_deriv_update hF l]
  fin_cases l
  · simp
  · simpa using hr.deriv
  · simpa using hc.deriv
  · simp

private theorem sig_ne (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    sig a (x 1) (x 2) ≠ 0 :=
  (sig_pos a _ (radius_pos hM hx)).ne'

private theorem del_ne (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    del M a (x 1) ≠ 0 :=
  (del_pos ha hx.1).ne'

private theorem sub_one_ne {x : MinkowskiModel 3} (hx : x ∈ domain M a) : x 2 - 1 ≠ 0 :=
  (sub_neg.mpr hx.2.2).ne

private theorem add_one_ne {x : MinkowskiModel 3} (hx : x ∈ domain M a) : x 2 + 1 ≠ 0 := by
  have h : -1 < x 2 := hx.2.1
  exact (show 0 < x 2 + 1 by linarith).ne'

private theorem one_sub_sq_ne {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    1 - x 2 ^ 2 ≠ 0 :=
  (one_sub_sq_pos hx).ne'

private theorem coefficient_eq (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x : MinkowskiModel 3)
    (i j : Fin 4) : (metric hM ha).coefficient x i j = metricTable M a (x 1) (x 2) i j := by
  rw [coefficient_apply, form_apply]
  fin_cases i <;> fin_cases j <;> simp [metricTable]

private theorem fderiv_metricTable (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {z : MinkowskiModel 3}
    (hz : z ∈ domain M a) (l i j : Fin 4) :
    fderiv ℝ (fun w : MinkowskiModel 3 => metricTable M a (w 1) (w 2) i j) z (Pi.single l 1) =
      metricPartial M a l (z 1) (z 2) i j := by
  have hd : DifferentiableAt ℝ (fun w : MinkowskiModel 3 => metricTable M a (w 1) (w 2) i j)
      z := by
    have h := (((metric hM ha).coefficient_contDiffOn i j).contDiffAt
      ((domain M a).isOpen.mem_nhds hz)).differentiableAt (by simp)
    have e : (fun y => (metric hM ha).coefficient y i j) =
        fun w : MinkowskiModel 3 => metricTable M a (w 1) (w 2) i j :=
      funext fun y => coefficient_eq hM ha y i j
    rwa [e] at h
  exact fderiv_apply_rc (F := fun r c => metricTable M a r c i j) hd
    (hasDerivAt_metricTable_r M a (z 1) (z 2) (sig_ne hM hz) (del_ne ha hz)
        (sub_one_ne hz) (add_one_ne hz) (one_sub_sq_ne hz) i j)
    (hasDerivAt_metricTable_c M a (z 1) (z 2) (sig_ne hM hz) (del_ne ha hz)
        (sub_one_ne hz) (add_one_ne hz) (one_sub_sq_ne hz) i j) l

private theorem lowered_0_00 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 0 0 = (metricPartial M a 0 r c 0 0 +
        metricPartial M a 0 r c 0 0 - metricPartial M a 0 r c 0 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, Matrix.cons_val, gtt,
      chris1_00, chris2_00, gtp]
  ring

private theorem lowered_0_01 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 0 1 = (metricPartial M a 0 r c 1 0 +
        metricPartial M a 1 r c 0 0 - metricPartial M a 0 r c 0 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtt, chris0_01, gtp, chris3_01, dgtt_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_0_02 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 0 2 = (metricPartial M a 0 r c 2 0 +
        metricPartial M a 2 r c 0 0 - metricPartial M a 0 r c 0 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtt, chris0_02, gtp, chris3_02, dgtt_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_0_03 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 0 3 = (metricPartial M a 0 r c 3 0 +
        metricPartial M a 3 r c 0 0 - metricPartial M a 0 r c 0 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, Matrix.cons_val, gtt,
      chris1_03, chris2_03, gtp]
  ring

private theorem lowered_0_10 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 1 0 = (metricPartial M a 1 r c 0 0 +
        metricPartial M a 0 r c 0 1 - metricPartial M a 0 r c 1 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtt, chris0_01, gtp, chris3_01, dgtt_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_0_11 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 1 1 = (metricPartial M a 1 r c 1 0 +
        metricPartial M a 1 r c 0 1 - metricPartial M a 0 r c 1 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtt, chris1_11, chris2_11, gtp]
  ring

private theorem lowered_0_12 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 1 2 = (metricPartial M a 1 r c 2 0 +
        metricPartial M a 2 r c 0 1 - metricPartial M a 0 r c 1 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, gtt, chris1_12, chris2_12, gtp]
  ring

private theorem lowered_0_13 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 1 3 = (metricPartial M a 1 r c 3 0 +
        metricPartial M a 3 r c 0 1 - metricPartial M a 0 r c 1 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtt, chris0_13, gtp, chris3_13, dgtp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_0_20 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 2 0 = (metricPartial M a 2 r c 0 0 +
        metricPartial M a 0 r c 0 2 - metricPartial M a 0 r c 2 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtt, chris0_02, gtp, chris3_02, dgtt_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_0_21 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 2 1 = (metricPartial M a 2 r c 1 0 +
        metricPartial M a 1 r c 0 2 - metricPartial M a 0 r c 2 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, gtt, chris1_12, chris2_12, gtp]
  ring

private theorem lowered_0_22 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 2 2 = (metricPartial M a 2 r c 2 0 +
        metricPartial M a 2 r c 0 2 - metricPartial M a 0 r c 2 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtt, chris1_22, chris2_22, gtp]
  ring

private theorem lowered_0_23 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 2 3 = (metricPartial M a 2 r c 3 0 +
        metricPartial M a 3 r c 0 2 - metricPartial M a 0 r c 2 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtt, chris0_23, gtp, chris3_23, dgtp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_0_30 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 3 0 = (metricPartial M a 3 r c 0 0 +
        metricPartial M a 0 r c 0 3 - metricPartial M a 0 r c 3 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, Matrix.cons_val, gtt,
      chris1_03, chris2_03, gtp]
  ring

private theorem lowered_0_31 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 3 1 = (metricPartial M a 3 r c 1 0 +
        metricPartial M a 1 r c 0 3 - metricPartial M a 0 r c 3 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtt, chris0_13, gtp, chris3_13, dgtp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_0_32 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 3 2 = (metricPartial M a 3 r c 2 0 +
        metricPartial M a 2 r c 0 3 - metricPartial M a 0 r c 3 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtt, chris0_23, gtp, chris3_23, dgtp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_0_33 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 0 q * christoffelTable M a r c q 3 3 = (metricPartial M a 3 r c 3 0 +
        metricPartial M a 3 r c 0 3 - metricPartial M a 0 r c 3 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, Matrix.cons_val, gtt,
      chris1_33, chris2_33, gtp]
  ring

private theorem lowered_1_00 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 0 0 = (metricPartial M a 0 r c 0 1 +
        metricPartial M a 0 r c 1 0 - metricPartial M a 1 r c 0 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, grr, chris1_00, chris2_00, dgtt_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_1_01 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 0 1 = (metricPartial M a 0 r c 1 1 +
        metricPartial M a 1 r c 1 0 - metricPartial M a 1 r c 0 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, chris0_01, grr, chris3_01]
  ring

private theorem lowered_1_02 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 0 2 = (metricPartial M a 0 r c 2 1 +
        metricPartial M a 2 r c 1 0 - metricPartial M a 1 r c 0 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris0_02, grr, chris3_02]
  ring

private theorem lowered_1_03 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 0 3 = (metricPartial M a 0 r c 3 1 +
        metricPartial M a 3 r c 1 0 - metricPartial M a 1 r c 0 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, grr, chris1_03, chris2_03, dgtp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_1_10 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 1 0 = (metricPartial M a 1 r c 0 1 +
        metricPartial M a 0 r c 1 1 - metricPartial M a 1 r c 1 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, chris0_01, grr, chris3_01]
  ring

private theorem lowered_1_11 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 1 1 = (metricPartial M a 1 r c 1 1 +
        metricPartial M a 1 r c 1 1 - metricPartial M a 1 r c 1 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, grr, chris1_11, chris2_11, dgrr_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_1_12 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 1 2 = (metricPartial M a 1 r c 2 1 +
        metricPartial M a 2 r c 1 1 - metricPartial M a 1 r c 1 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, grr, chris1_12, chris2_12, dgrr_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_1_13 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 1 3 = (metricPartial M a 1 r c 3 1 +
        metricPartial M a 3 r c 1 1 - metricPartial M a 1 r c 1 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, chris0_13, grr, chris3_13]
  ring

private theorem lowered_1_20 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 2 0 = (metricPartial M a 2 r c 0 1 +
        metricPartial M a 0 r c 1 2 - metricPartial M a 1 r c 2 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris0_02, grr, chris3_02]
  ring

private theorem lowered_1_21 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 2 1 = (metricPartial M a 2 r c 1 1 +
        metricPartial M a 1 r c 1 2 - metricPartial M a 1 r c 2 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, grr, chris1_12, chris2_12, dgrr_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_1_22 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 2 2 = (metricPartial M a 2 r c 2 1 +
        metricPartial M a 2 r c 1 2 - metricPartial M a 1 r c 2 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, grr, chris1_22, chris2_22, dgcc_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_1_23 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 2 3 = (metricPartial M a 2 r c 3 1 +
        metricPartial M a 3 r c 1 2 - metricPartial M a 1 r c 2 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris0_23, grr, chris3_23]
  ring

private theorem lowered_1_30 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 3 0 = (metricPartial M a 3 r c 0 1 +
        metricPartial M a 0 r c 1 3 - metricPartial M a 1 r c 3 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, grr, chris1_03, chris2_03, dgtp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_1_31 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 3 1 = (metricPartial M a 3 r c 1 1 +
        metricPartial M a 1 r c 1 3 - metricPartial M a 1 r c 3 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, chris0_13, grr, chris3_13]
  ring

private theorem lowered_1_32 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 3 2 = (metricPartial M a 3 r c 2 1 +
        metricPartial M a 2 r c 1 3 - metricPartial M a 1 r c 3 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris0_23, grr, chris3_23]
  ring

private theorem lowered_1_33 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 1 q * christoffelTable M a r c q 3 3 = (metricPartial M a 3 r c 3 1 +
        metricPartial M a 3 r c 1 3 - metricPartial M a 1 r c 3 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, grr, chris1_33, chris2_33, dgpp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_2_00 (M a r c : ℝ) (hS : sig a r c ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 0 0 = (metricPartial M a 0 r c 0 2 +
        metricPartial M a 0 r c 2 0 - metricPartial M a 2 r c 0 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris1_00, gcc, chris2_00, dgtt_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_2_01 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 0 1 = (metricPartial M a 0 r c 1 2 +
        metricPartial M a 1 r c 2 0 - metricPartial M a 2 r c 0 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris0_01, gcc, chris3_01]
  ring

private theorem lowered_2_02 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 0 2 = (metricPartial M a 0 r c 2 2 +
        metricPartial M a 2 r c 2 0 - metricPartial M a 2 r c 0 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris0_02, gcc, chris3_02]
  ring

private theorem lowered_2_03 (M a r c : ℝ) (hS : sig a r c ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 0 3 = (metricPartial M a 0 r c 3 2 +
        metricPartial M a 3 r c 2 0 - metricPartial M a 2 r c 0 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris1_03, gcc, chris2_03, dgtp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_2_10 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 1 0 = (metricPartial M a 1 r c 0 2 +
        metricPartial M a 0 r c 2 1 - metricPartial M a 2 r c 1 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris0_01, gcc, chris3_01]
  ring

private theorem lowered_2_11 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (h1c : 1 - c ^ 2 ≠ 0) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 1 1 = (metricPartial M a 1 r c 1 2 +
        metricPartial M a 1 r c 2 1 - metricPartial M a 2 r c 1 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris1_11, gcc, chris2_11, dgrr_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_2_12 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 1 2 = (metricPartial M a 1 r c 2 2 +
        metricPartial M a 2 r c 2 1 - metricPartial M a 2 r c 1 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris1_12, gcc, chris2_12, dgcc_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_2_13 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 1 3 = (metricPartial M a 1 r c 3 2 +
        metricPartial M a 3 r c 2 1 - metricPartial M a 2 r c 1 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris0_13, gcc, chris3_13]
  ring

private theorem lowered_2_20 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 2 0 = (metricPartial M a 2 r c 0 2 +
        metricPartial M a 0 r c 2 2 - metricPartial M a 2 r c 2 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris0_02, gcc, chris3_02]
  ring

private theorem lowered_2_21 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 2 1 = (metricPartial M a 2 r c 1 2 +
        metricPartial M a 1 r c 2 2 - metricPartial M a 2 r c 2 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris1_12, gcc, chris2_12, dgcc_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_2_22 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 2 2 = (metricPartial M a 2 r c 2 2 +
        metricPartial M a 2 r c 2 2 - metricPartial M a 2 r c 2 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris1_22, gcc, chris2_22, dgcc_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_2_23 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 2 3 = (metricPartial M a 2 r c 3 2 +
        metricPartial M a 3 r c 2 2 - metricPartial M a 2 r c 2 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris0_23, gcc, chris3_23]
  ring

private theorem lowered_2_30 (M a r c : ℝ) (hS : sig a r c ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 3 0 = (metricPartial M a 3 r c 0 2 +
        metricPartial M a 0 r c 2 3 - metricPartial M a 2 r c 3 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris1_03, gcc, chris2_03, dgtp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_2_31 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 3 1 = (metricPartial M a 3 r c 1 2 +
        metricPartial M a 1 r c 2 3 - metricPartial M a 2 r c 3 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, chris0_13, gcc, chris3_13]
  ring

private theorem lowered_2_32 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 3 2 = (metricPartial M a 3 r c 2 2 +
        metricPartial M a 2 r c 2 3 - metricPartial M a 2 r c 3 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris0_23, gcc, chris3_23]
  ring

private theorem lowered_2_33 (M a r c : ℝ) (hS : sig a r c ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) :
    ∑ q, metricTable M a r c 2 q * christoffelTable M a r c q 3 3 = (metricPartial M a 3 r c 3 2 +
        metricPartial M a 3 r c 2 3 - metricPartial M a 2 r c 3 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, chris1_33, gcc, chris2_33, dgpp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_00 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 0 0 = (metricPartial M a 0 r c 0 3 +
        metricPartial M a 0 r c 3 0 - metricPartial M a 3 r c 0 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, Matrix.cons_val, gtp,
      chris1_00, chris2_00, gpp]
  ring

private theorem lowered_3_01 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 0 1 = (metricPartial M a 0 r c 1 3 +
        metricPartial M a 1 r c 3 0 - metricPartial M a 3 r c 0 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtp, chris0_01, gpp, chris3_01, dgtp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_02 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 0 2 = (metricPartial M a 0 r c 2 3 +
        metricPartial M a 2 r c 3 0 - metricPartial M a 3 r c 0 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtp, chris0_02, gpp, chris3_02, dgtp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_03 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 0 3 = (metricPartial M a 0 r c 3 3 +
        metricPartial M a 3 r c 3 0 - metricPartial M a 3 r c 0 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, Matrix.cons_val, gtp,
      chris1_03, chris2_03, gpp]
  ring

private theorem lowered_3_10 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 1 0 = (metricPartial M a 1 r c 0 3 +
        metricPartial M a 0 r c 3 1 - metricPartial M a 3 r c 1 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtp, chris0_01, gpp, chris3_01, dgtp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_11 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 1 1 = (metricPartial M a 1 r c 1 3 +
        metricPartial M a 1 r c 3 1 - metricPartial M a 3 r c 1 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtp, chris1_11, chris2_11, gpp]
  ring

private theorem lowered_3_12 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 1 2 = (metricPartial M a 1 r c 2 3 +
        metricPartial M a 2 r c 3 1 - metricPartial M a 3 r c 1 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, gtp, chris1_12, chris2_12, gpp]
  ring

private theorem lowered_3_13 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 1 3 = (metricPartial M a 1 r c 3 3 +
        metricPartial M a 3 r c 3 1 - metricPartial M a 3 r c 1 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtp, chris0_13, gpp, chris3_13, dgpp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_20 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 2 0 = (metricPartial M a 2 r c 0 3 +
        metricPartial M a 0 r c 3 2 - metricPartial M a 3 r c 2 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtp, chris0_02, gpp, chris3_02, dgtp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_21 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 2 1 = (metricPartial M a 2 r c 1 3 +
        metricPartial M a 1 r c 3 2 - metricPartial M a 3 r c 2 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR, metricC,
      Matrix.cons_val, gtp, chris1_12, chris2_12, gpp]
  ring

private theorem lowered_3_22 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 2 2 = (metricPartial M a 2 r c 2 3 +
        metricPartial M a 2 r c 3 2 - metricPartial M a 3 r c 2 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtp, chris1_22, chris2_22, gpp]
  ring

private theorem lowered_3_23 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 2 3 = (metricPartial M a 2 r c 3 3 +
        metricPartial M a 3 r c 3 2 - metricPartial M a 3 r c 2 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtp, chris0_23, gpp, chris3_23, dgpp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_30 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 3 0 = (metricPartial M a 3 r c 0 3 +
        metricPartial M a 0 r c 3 3 - metricPartial M a 3 r c 3 0) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, Matrix.cons_val, gtp,
      chris1_03, chris2_03, gpp]
  ring

private theorem lowered_3_31 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 3 1 = (metricPartial M a 3 r c 1 3 +
        metricPartial M a 1 r c 3 3 - metricPartial M a 3 r c 3 1) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricR,
      Matrix.cons_val, gtp, chris0_13, gpp, chris3_13, dgpp_r]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_32 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hc1 : c - 1 ≠ 0)
    (hc2 : c + 1 ≠ 0) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 3 2 = (metricPartial M a 3 r c 2 3 +
        metricPartial M a 2 r c 3 3 - metricPartial M a 3 r c 3 2) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, metricC,
      Matrix.cons_val, gtp, chris0_23, gpp, chris3_23, dgpp_c]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem lowered_3_33 (M a r c : ℝ) :
    ∑ q, metricTable M a r c 3 q * christoffelTable M a r c q 3 3 = (metricPartial M a 3 r c 3 3 +
        metricPartial M a 3 r c 3 3 - metricPartial M a 3 r c 3 3) / 2 := by
  simp only [Fin.sum_univ_four, metricTable, christoffelTable, metricPartial, Matrix.cons_val, gtp,
      chris1_33, chris2_33, gpp]
  ring

private theorem lowered (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) (h1c : 1 - c ^ 2 ≠ 0) (l i j : Fin 4) :
    ∑ q, metricTable M a r c l q * christoffelTable M a r c q i j = (metricPartial M a i r c j l +
        metricPartial M a j r c l i - metricPartial M a l r c i j) / 2 := by
  fin_cases l <;> fin_cases i <;> fin_cases j
  · exact lowered_0_00 M a r c
  · exact lowered_0_01 M a r c hS hD
  · exact lowered_0_02 M a r c hS hc1 hc2
  · exact lowered_0_03 M a r c
  · exact lowered_0_10 M a r c hS hD
  · exact lowered_0_11 M a r c
  · exact lowered_0_12 M a r c
  · exact lowered_0_13 M a r c hS hD
  · exact lowered_0_20 M a r c hS hc1 hc2
  · exact lowered_0_21 M a r c
  · exact lowered_0_22 M a r c
  · exact lowered_0_23 M a r c hS hc1 hc2
  · exact lowered_0_30 M a r c
  · exact lowered_0_31 M a r c hS hD
  · exact lowered_0_32 M a r c hS hc1 hc2
  · exact lowered_0_33 M a r c
  · exact lowered_1_00 M a r c hS hD
  · exact lowered_1_01 M a r c
  · exact lowered_1_02 M a r c
  · exact lowered_1_03 M a r c hS hD
  · exact lowered_1_10 M a r c
  · exact lowered_1_11 M a r c hS hD
  · exact lowered_1_12 M a r c hS hD
  · exact lowered_1_13 M a r c
  · exact lowered_1_20 M a r c
  · exact lowered_1_21 M a r c hS hD
  · exact lowered_1_22 M a r c hS hD hc1 hc2
  · exact lowered_1_23 M a r c
  · exact lowered_1_30 M a r c hS hD
  · exact lowered_1_31 M a r c
  · exact lowered_1_32 M a r c
  · exact lowered_1_33 M a r c hS hD
  · exact lowered_2_00 M a r c hS h1c
  · exact lowered_2_01 M a r c
  · exact lowered_2_02 M a r c
  · exact lowered_2_03 M a r c hS h1c
  · exact lowered_2_10 M a r c
  · exact lowered_2_11 M a r c hS hD h1c
  · exact lowered_2_12 M a r c hS hc1 hc2 h1c
  · exact lowered_2_13 M a r c
  · exact lowered_2_20 M a r c
  · exact lowered_2_21 M a r c hS hc1 hc2 h1c
  · exact lowered_2_22 M a r c hS hc1 hc2 h1c
  · exact lowered_2_23 M a r c
  · exact lowered_2_30 M a r c hS h1c
  · exact lowered_2_31 M a r c
  · exact lowered_2_32 M a r c
  · exact lowered_2_33 M a r c hS h1c
  · exact lowered_3_00 M a r c
  · exact lowered_3_01 M a r c hS hD
  · exact lowered_3_02 M a r c hS hc1 hc2
  · exact lowered_3_03 M a r c
  · exact lowered_3_10 M a r c hS hD
  · exact lowered_3_11 M a r c
  · exact lowered_3_12 M a r c
  · exact lowered_3_13 M a r c hS hD
  · exact lowered_3_20 M a r c hS hc1 hc2
  · exact lowered_3_21 M a r c
  · exact lowered_3_22 M a r c
  · exact lowered_3_23 M a r c hS hc1 hc2
  · exact lowered_3_30 M a r c
  · exact lowered_3_31 M a r c hS hD
  · exact lowered_3_32 M a r c hS hc1 hc2
  · exact lowered_3_33 M a r c

/-- **The Christoffel symbols of the Kerr metric** are the table `christoffel`, certified by its
lowered identity. -/
theorem christoffelOf_eq (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) (k i j : Fin 4) :
    christoffelOf (metric hM ha).coefficient x k i j = christoffel M a x k i j := by
  refine CoordinateMetric.christoffelOf_eq_of_lowered (metric hM ha) hx (christoffel M a x)
    (fun l i j => ?_) k i j
  simp only [coefficient_eq hM ha, fderiv_metricTable hM ha hx]
  exact lowered M a (x 1) (x 2) (sig_ne hM hx) (del_ne ha hx) (sub_one_ne hx)
      (add_one_ne hx) (one_sub_sq_ne hx) l i j

private theorem fderiv_christoffel (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {z : MinkowskiModel 3}
    (hz : z ∈ domain M a) (l q i j : Fin 4) :
    fderiv ℝ (fun w => christoffel M a w q i j) z (Pi.single l 1) =
      christoffelPartial M a l (z 1) (z 2) q i j := by
  have hU := (domain M a).isOpen.mem_nhds hz
  have hd : DifferentiableAt ℝ (fun w => christoffel M a w q i j) z := by
    have h := (((metric hM ha).contDiffOn_christoffelOf q i j).contDiffAt hU).differentiableAt
      (by simp)
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hU] with w hw using (christoffelOf_eq hM ha hw q i j).symm
  exact fderiv_apply_rc (F := fun r c => christoffelTable M a r c q i j) hd
    (hasDerivAt_christoffelTable_r M a (z 1) (z 2) (sig_ne hM hz) (del_ne ha hz)
        (sub_one_ne hz) (add_one_ne hz) q i j)
    (hasDerivAt_christoffelTable_c M a (z 1) (z 2) (sig_ne hM hz) (del_ne ha hz)
        (sub_one_ne hz) (add_one_ne hz) q i j) l

/-! ### The Ricci tensor -/

/-- The Ricci formula of the table, as a function of `r` and `χ`. -/
private def ricciTab (M a r c : ℝ) (j k : Fin 4) : ℝ :=
  ∑ i, (christoffelPartial M a i r c i j k - christoffelPartial M a j r c i i k +
    ∑ b, (christoffelTable M a r c i i b * christoffelTable M a r c b j k -
      christoffelTable M a r c i j b * christoffelTable M a r c b i k))

private theorem ricciTab_00 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ricciTab M a r c 0 0 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val, chris0_01, chris1_00, chris0_02, chris2_00, dchris1_00_r,
      chris1_11, chris1_12, chris1_03, chris3_01, dchris2_00_c, chris2_12, chris2_22, chris2_03,
      chris3_02, chris3_13, chris3_23]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem ricciTab_01 (M a r c : ℝ) :
    ricciTab M a r c 0 1 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val]
  ring

private theorem ricciTab_02 (M a r c : ℝ) :
    ricciTab M a r c 0 2 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val]
  ring

private theorem ricciTab_03 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ricciTab M a r c 0 3 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val, chris0_01, chris1_03, chris0_02, chris2_03, dchris1_03_r,
      chris1_00, chris0_13, chris1_11, chris1_12, chris3_13, dchris2_03_c, chris2_00, chris0_23,
      chris2_12, chris2_22, chris3_23, chris3_01, chris1_33, chris3_02, chris2_33]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem ricciTab_10 (M a r c : ℝ) :
    ricciTab M a r c 1 0 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val]
  ring

private theorem ricciTab_11 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ricciTab M a r c 1 1 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val, dchris0_01_r, chris0_01, chris1_11, chris0_02, chris2_11,
      chris0_13, chris3_01, dchris1_11_r, chris1_12, dchris2_11_c, dchris2_12_r, chris2_12,
      chris2_22, dchris3_13_r, chris3_13, chris3_23]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem ricciTab_12 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ricciTab M a r c 1 2 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val, dchris0_02_r, chris0_01, chris0_02, chris1_12, chris2_12,
      chris0_13, chris3_02, dchris1_12_r, chris1_11, dchris2_12_c, dchris2_22_r, chris2_11,
      chris1_22, chris2_22, dchris3_23_r, chris3_01, chris0_23, chris3_13, chris3_23]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem ricciTab_13 (M a r c : ℝ) :
    ricciTab M a r c 1 3 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val]
  ring

private theorem ricciTab_20 (M a r c : ℝ) :
    ricciTab M a r c 2 0 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val]
  ring

private theorem ricciTab_21 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ricciTab M a r c 2 1 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val, dchris0_01_c, chris0_02, chris0_01, chris1_12, chris2_12,
      chris0_23, chris3_01, dchris1_12_r, dchris1_11_c, chris1_11, chris1_22, chris2_11,
      dchris2_12_c, chris2_22, dchris3_13_c, chris3_02, chris0_13, chris3_13, chris3_23]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem ricciTab_22 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ricciTab M a r c 2 2 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val, dchris0_02_c, chris0_02, chris0_01, chris1_22, chris2_22,
      chris0_23, chris3_02, dchris1_22_r, dchris1_12_c, chris1_11, chris1_12, chris2_12,
      dchris2_22_c, dchris3_23_c, chris3_13, chris3_23]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem ricciTab_23 (M a r c : ℝ) :
    ricciTab M a r c 2 3 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val]
  ring

private theorem ricciTab_30 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ricciTab M a r c 3 0 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val, chris0_01, chris1_03, chris0_13, chris1_00, chris0_02,
      chris2_03, chris0_23, chris2_00, dchris1_03_r, chris1_11, chris1_12, chris1_33, chris3_01,
      dchris2_03_c, chris2_12, chris2_22, chris2_33, chris3_02, chris3_13, chris3_23]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem ricciTab_31 (M a r c : ℝ) :
    ricciTab M a r c 3 1 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val]
  ring

private theorem ricciTab_32 (M a r c : ℝ) :
    ricciTab M a r c 3 2 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val]
  ring

private theorem ricciTab_33 (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) :
    ricciTab M a r c 3 3 = 0 := by
  simp only [ricciTab, Fin.sum_univ_four, christoffelTable, christoffelPartial, christoffelR,
      christoffelC, Matrix.cons_val, chris0_01, chris1_33, chris0_13, chris1_03, chris0_02,
      chris2_33, chris0_23, chris2_03, dchris1_33_r, chris1_11, chris1_12, chris3_13, dchris2_33_c,
      chris2_12, chris2_22, chris3_23]
  generalize hSd : sig a r c = S at hS ⊢
  generalize hDd : del M a r = D at hD ⊢
  field_simp
  unfold sig at hSd
  unfold del at hDd
  subst hSd hDd
  ring

private theorem ricciTab_eq_zero (M a r c : ℝ) (hS : sig a r c ≠ 0) (hD : del M a r ≠ 0)
    (hc1 : c - 1 ≠ 0) (hc2 : c + 1 ≠ 0) (j k : Fin 4) :
    ricciTab M a r c j k = 0 := by
  fin_cases j <;> fin_cases k
  · exact ricciTab_00 M a r c hS hD hc1 hc2
  · exact ricciTab_01 M a r c
  · exact ricciTab_02 M a r c
  · exact ricciTab_03 M a r c hS hD hc1 hc2
  · exact ricciTab_10 M a r c
  · exact ricciTab_11 M a r c hS hD hc1 hc2
  · exact ricciTab_12 M a r c hS hD hc1 hc2
  · exact ricciTab_13 M a r c
  · exact ricciTab_20 M a r c
  · exact ricciTab_21 M a r c hS hD hc1 hc2
  · exact ricciTab_22 M a r c hS hD hc1 hc2
  · exact ricciTab_23 M a r c
  · exact ricciTab_30 M a r c hS hD hc1 hc2
  · exact ricciTab_31 M a r c
  · exact ricciTab_32 M a r c
  · exact ricciTab_33 M a r c hS hD hc1 hc2

private theorem ricciOfChristoffel_eq (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {z : MinkowskiModel 3}
    (hz : z ∈ domain M a) (j k : Fin 4) :
    ricciOfChristoffel (christoffel M a) z j k = ricciTab M a (z 1) (z 2) j k := by
  simp only [ricciOfChristoffel, fderiv_christoffel hM ha hz]
  rfl

/-- **The Kerr field is Ricci flat** (Landau–Lifshitz, §104): `R_{ik} = 0` at every point of the
domain. -/
theorem ricciOf_eq_zero (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) (j k : Fin 4) : ricciOf (metric hM ha).coefficient x j k = 0 := by
  have hG : ∀ᶠ z in 𝓝 x, ∀ p q s, christoffelOf (metric hM ha).coefficient z p q s =
      christoffel M a z p q s := by
    filter_upwards [(domain M a).isOpen.mem_nhds hx] with z hz using christoffelOf_eq hM ha hz
  rw [CoordinateMetric.ricciOf_eq_ricciOfChristoffel hG, ricciOfChristoffel_eq hM ha hx]
  exact ricciTab_eq_zero M a (x 1) (x 2) (sig_ne hM hx) (del_ne ha hx) (sub_one_ne hx)
      (add_one_ne hx) j k

/-- The scalar curvature of the Kerr field vanishes on the domain. -/
theorem scalarOf_eq_zero (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) : scalarOf (metric hM ha).coefficient x = 0 := by
  simp [scalarOf, ricciOf_eq_zero hM ha hx]

/-- The Einstein tensor of the Kerr field vanishes on the domain. -/
theorem einsteinOf_eq_zero (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) (i k : Fin 4) : einsteinOf (metric hM ha).coefficient x i k = 0 := by
  simp [einsteinOf, ricciOf_eq_zero hM ha hx, scalarOf_eq_zero hM ha hx]

/-- **The Kerr field solves the vacuum Einstein equations** `G_{ik} = κ · 0` on the domain, in
the co-ordinates, for every coupling constant `κ`. -/
theorem isEinstein_zero (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (κ : ℝ) :
    (metric hM ha).IsEinstein κ 0 0 := by
  intro x hx i k
  simp [einsteinOf_eq_zero hM ha hx]

/-- The native Einstein tensor of the Kerr field vanishes on co-ordinate fields. -/
theorem einstein_chartField (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x y : domain M a) (i k : Fin 4) :
    (metric hM ha).toLorentzMetric.einstein y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 := by
  rw [(metric hM ha).toLorentzMetric_einstein_chartField x y,
    einsteinOf_eq_zero hM ha y.property]

/-- **The native vacuum Einstein equations**: the Kerr field satisfies `G + 0 · g = κ · 0` on
the domain for every coupling constant `κ`. -/
theorem satisfiesEinstein_zero (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (κ : ℝ) :
    (metric hM ha).toLorentzMetric.SatisfiesEinstein κ 0 0 := by
  intro y
  refine LorentzMetric.ext_chartField (CoordinateMetric.physicalChart_mem y) (by simp) fun i => ?_
  refine LorentzMetric.ext_chartField (CoordinateMetric.physicalChart_mem y) (by simp) fun k => ?_
  simp only [add_apply, smul_apply, smul_eq_mul, zero_mul, add_zero]
  rw [einstein_chartField hM ha y y i k]
  simp

/-- The native Ricci tensor of the Kerr field vanishes on co-ordinate fields. -/
theorem ricci_chartField (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x y : domain M a) (j k : Fin 4) :
    (metric hM ha).toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 := by
  rw [(metric hM ha).toLorentzMetric_ricci_chartField x y, ricciOf_eq_zero hM ha y.property]

/-- **The native Ricci tensor of the Kerr field vanishes** at every point of the domain, on all
pairs of tangent vectors. -/
theorem ricci_eq_zero (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (y : domain M a)
    (u w : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) :
    (metric hM ha).toLorentzMetric.ricci y u w = 0 := by
  have he (i : Fin 4) : (Pi.single i 1 : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) =
      chartField (physicalChart y) (Pi.single i 1) y :=
    (CoordinateMetric.physicalChart_chartField y y _).symm
  have hc (j k : Fin 4) : (metric hM ha).toLorentzMetric.ricci y
      (Pi.single j 1 : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) (Pi.single k 1) = 0 := by
    have h := ricci_chartField hM ha y y j k
    rwa [← he, ← he] at h
  let B : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
    (metric hM ha).toLorentzMetric.ricci y
  have hB (j k : Fin 4) : B (Pi.single j 1) (Pi.single k 1) = 0 := hc j k
  have key (u w : MinkowskiModel 3) : B u w = 0 := by
    rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
    simp only [map_sum, map_smul, _root_.sum_apply, smul_apply, hB, smul_zero,
      Finset.sum_const_zero]
  exact key u w

/-! ### The ergoregion -/

/-- The coefficient `g_tt` is the value of the form on `e₀`. -/
theorem form_time (x : MinkowskiModel 3) :
    form M a x (Pi.single 0 1) (Pi.single 0 1) = gtt M a (x 1) (x 2) := by
  rw [form_apply]
  simp

/-- **The ergoregion** (Landau–Lifshitz §104): at a point of the domain `g_tt > 0` exactly where
`r² − 2Mr + a²χ² < 0`, inside the surface `r = M + √(M² − a²χ²)`. -/
theorem ergoregion_iff (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    0 < form M a x (Pi.single 0 1) (Pi.single 0 1) ↔
      x 1 ^ 2 - 2 * M * x 1 + a ^ 2 * x 2 ^ 2 < 0 := by
  have hS := sig_pos a (x 2) (radius_pos hM hx)
  have e : gtt M a (x 1) (x 2) =
      -(x 1 ^ 2 - 2 * M * x 1 + a ^ 2 * x 2 ^ 2) / sig a (x 1) (x 2) := by
    unfold gtt
    field_simp
    unfold sig
    ring
  rw [form_time, e, lt_div_iff₀ hS]
  constructor <;> intro h <;> linarith

/-- For `a ≠ 0` the outer horizon lies inside the sphere `r = 2M`. -/
theorem horizon_lt_two_mul (hM : 0 < M) (ha0 : a ≠ 0) : horizon M a < 2 * M := by
  have hpos : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha0))
  have h : Real.sqrt (M ^ 2 - a ^ 2) < M := by
    rw [Real.sqrt_lt' hM]
    linarith
  unfold horizon
  linarith

/-- **The ergoregion is not empty** for `a ≠ 0`: on the equator `χ = 0` it contains the radii
`r₊ < r < 2M`. -/
theorem ergoregion_nonempty (hM : 0 < M) (ha0 : a ≠ 0) :
    ∃ x ∈ domain M a, 0 < form M a x (Pi.single 0 1) (Pi.single 0 1) := by
  obtain ⟨r, hr1, hr2⟩ : ∃ r, horizon M a < r ∧ r < 2 * M :=
    ⟨(horizon M a + 2 * M) / 2, by linarith [horizon_lt_two_mul hM ha0],
      by linarith [horizon_lt_two_mul hM ha0]⟩
  have hr0 : 0 < r := (hM.trans_le (le_horizon M a)).trans hr1
  have hx : (![0, r, 0, 0] : MinkowskiModel 3) ∈ domain M a :=
    ⟨show horizon M a < r from hr1, show (-1 : ℝ) < 0 by norm_num, show (0 : ℝ) < 1 by norm_num⟩
  refine ⟨_, hx, (ergoregion_iff hM hx).mpr ?_⟩
  show r ^ 2 - 2 * M * r + a ^ 2 * 0 ^ 2 < 0
  nlinarith [mul_pos hr0 (sub_pos.mpr hr2)]

/-! ### Stationary observers and the dragging of frames -/

/-- The upper end `Ω₊ = (−g_tφ + √(Δ(1 − χ²)))/g_φφ` of the window of angular velocities of
the stationary observers. -/
def omegaPlus (M a r c : ℝ) : ℝ :=
  (-gtp M a r c + Real.sqrt (del M a r * (1 - c ^ 2))) / gpp M a r c

/-- The lower end `Ω₋ = (−g_tφ − √(Δ(1 − χ²)))/g_φφ` of the window of angular velocities of
the stationary observers. -/
def omegaMinus (M a r c : ℝ) : ℝ :=
  (-gtp M a r c - Real.sqrt (del M a r * (1 - c ^ 2))) / gpp M a r c

/-- The form on `e₀ + Ω e₃`, the velocity of the world line `φ = Ωt + const` at fixed `r`, `χ`:
`g_tt + 2Ω g_tφ + Ω² g_φφ`. -/
theorem form_rotating (x : MinkowskiModel 3) (Ω : ℝ) :
    form M a x ![1, 0, 0, Ω] ![1, 0, 0, Ω] =
      gtt M a (x 1) (x 2) + 2 * Ω * gtp M a (x 1) (x 2) + Ω ^ 2 * gpp M a (x 1) (x 2) := by
  rw [form_apply]
  simp
  ring

/-- **The window of stationary observers** (Landau–Lifshitz §104): at a point of the domain the
world line `φ = Ωt + const` at fixed `r`, `χ` is timelike exactly for `Ω₋ < Ω < Ω₊`. -/
theorem form_rotating_neg_iff (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) (Ω : ℝ) :
    form M a x ![1, 0, 0, Ω] ![1, 0, 0, Ω] < 0 ↔
      omegaMinus M a (x 1) (x 2) < Ω ∧ Ω < omegaPlus M a (x 1) (x 2) := by
  have hr := radius_pos hM hx
  have hS := sig_pos a (x 2) hr
  have hc := one_sub_sq_pos hx
  have hp := gpp_pos (a := a) hM.le hr hc
  have hd : 0 ≤ del M a (x 1) * (1 - x 2 ^ 2) := (mul_pos (del_pos ha hx.1) hc).le
  have key := gtt_mul_gpp_sub_sq (M := M) hS.ne'
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg (del M a (x 1) * (1 - x 2 ^ 2))
  rw [form_rotating, omegaMinus, omegaPlus, div_lt_iff₀ hp, lt_div_iff₀ hp]
  set t := gtt M a (x 1) (x 2)
  set b := gtp M a (x 1) (x 2)
  set p := gpp M a (x 1) (x 2)
  set s := Real.sqrt (del M a (x 1) * (1 - x 2 ^ 2))
  have hprod : p * (t + 2 * Ω * b + Ω ^ 2 * p) = (Ω * p + b - s) * (Ω * p + b + s) := by
    linear_combination key + hs
  constructor
  · intro h
    have h' : (Ω * p + b - s) * (Ω * p + b + s) < 0 := by
      rw [← hprod]
      exact mul_neg_of_pos_of_neg hp h
    rcases mul_neg_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exfalso
      linarith
    · constructor <;> linarith
  · rintro ⟨h1, h2⟩
    have h' : (Ω * p + b - s) * (Ω * p + b + s) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    rw [← hprod] at h'
    by_contra hge
    linarith [mul_nonneg hp.le (not_lt.mp hge)]

/-- **The dragging of frames** (Landau–Lifshitz §104): in the ergoregion, for `a > 0`, the lower
end of the window is positive, so that no observer is at rest and every stationary observer
rotates in the sense of the source. -/
theorem omegaMinus_pos (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (ha0 : 0 < a) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) (hergo : 0 < form M a x (Pi.single 0 1) (Pi.single 0 1)) :
    0 < omegaMinus M a (x 1) (x 2) := by
  have hr := radius_pos hM hx
  have hS := sig_pos a (x 2) hr
  have hc := one_sub_sq_pos hx
  have hp := gpp_pos (a := a) hM.le hr hc
  have hd : 0 ≤ del M a (x 1) * (1 - x 2 ^ 2) := (mul_pos (del_pos ha hx.1) hc).le
  have key := gtt_mul_gpp_sub_sq (M := M) hS.ne'
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg (del M a (x 1) * (1 - x 2 ^ 2))
  rw [form_time] at hergo
  have hb : 0 < -gtp M a (x 1) (x 2) := by
    unfold gtp
    rw [neg_neg]
    exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos two_pos hM) ha0) hr) hc) hS
  unfold omegaMinus
  refine div_pos ?_ hp
  set t := gtt M a (x 1) (x 2)
  set b := gtp M a (x 1) (x 2)
  set p := gpp M a (x 1) (x 2)
  set s := Real.sqrt (del M a (x 1) * (1 - x 2 ^ 2))
  have h1 : (-b - s) * (-b + s) = t * p := by
    linear_combination (-1 : ℝ) * key - hs
  have h2 : 0 < -b + s := by linarith
  nlinarith [mul_pos hergo hp]

/-! ### The horizon -/

/-- The angular velocity `Ω_H = a/(r₊² + a²)` of the outer horizon. -/
def horizonRate (M a : ℝ) : ℝ := a / (horizon M a ^ 2 + a ^ 2)

private theorem continuousAt_gtp {r c : ℝ} (hS : sig a r c ≠ 0) :
    ContinuousAt (fun s => gtp M a s c) r := by
  have h : ContinuousAt (fun s => sig a s c) r := by
    unfold sig
    fun_prop
  unfold gtp
  exact ((by fun_prop : Continuous fun s : ℝ => 2 * M * a * s * (1 - c ^ 2)).continuousAt.div
    h hS).neg

private theorem continuousAt_gpp {r c : ℝ} (hS : sig a r c ≠ 0) :
    ContinuousAt (fun s => gpp M a s c) r := by
  have h : ContinuousAt (fun s => sig a s c) r := by
    unfold sig
    fun_prop
  unfold gpp
  exact (((by fun_prop : Continuous fun s : ℝ => s ^ 2 + a ^ 2).continuousAt.add
    ((by fun_prop : Continuous fun s : ℝ => 2 * M * a ^ 2 * s * (1 - c ^ 2)).continuousAt.div
      h hS)).mul continuousAt_const)

private theorem continuousAt_sqrt (c : ℝ) {r : ℝ} :
    ContinuousAt (fun s => Real.sqrt (del M a s * (1 - c ^ 2))) r :=
  (Real.continuous_sqrt.comp (by unfold del; fun_prop)).continuousAt

/-- On the horizon `−g_tφ/g_φφ = a/(r₊² + a²)`. -/
private theorem rate_identity {r c : ℝ} (hM : M ≠ 0) (hr : r ≠ 0) (hc : 1 - c ^ 2 ≠ 0)
    (hS : sig a r c ≠ 0) (hd : r ^ 2 - 2 * M * r + a ^ 2 = 0) (hq : r ^ 2 + a ^ 2 ≠ 0) :
    -gtp M a r c / gpp M a r c = a / (r ^ 2 + a ^ 2) := by
  have e1 : r ^ 2 + a ^ 2 + 2 * M * a ^ 2 * r * (1 - c ^ 2) / sig a r c =
      2 * M * r * (r ^ 2 + a ^ 2) / sig a r c := by
    rw [eq_div_iff hS, add_mul, div_mul_cancel₀ _ hS]
    unfold sig
    linear_combination (r ^ 2 + a ^ 2 * c ^ 2) * hd
  unfold gpp gtp
  rw [e1]
  field_simp

/-- **The angular velocity of the horizon** (Landau–Lifshitz §104): as `r → r₊` from above, the
upper end `Ω₊` of the window tends to `Ω_H = a/(r₊² + a²)`. -/
theorem tendsto_omegaPlus (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {c : ℝ} (hc1 : -1 < c)
    (hc2 : c < 1) :
    Tendsto (fun r => omegaPlus M a r c) (𝓝[>] horizon M a) (𝓝 (horizonRate M a)) := by
  have hc : 0 < 1 - c ^ 2 := by nlinarith
  have hr : 0 < horizon M a := hM.trans_le (le_horizon M a)
  have hS := sig_pos a c hr
  have hp := gpp_pos (a := a) hM.le hr hc
  have hcont : ContinuousAt (fun r => omegaPlus M a r c) (horizon M a) :=
    ((continuousAt_gtp (M := M) hS.ne').neg.add (continuousAt_sqrt (M := M) (a := a) c)).div
      (continuousAt_gpp hS.ne') hp.ne'
  have hv : omegaPlus M a (horizon M a) c = horizonRate M a := by
    have hd := del_horizon ha
    rw [omegaPlus, hd, zero_mul, Real.sqrt_zero, add_zero, horizonRate]
    unfold del at hd
    exact rate_identity hM.ne' hr.ne' hc.ne' hS.ne' hd
      (add_pos_of_pos_of_nonneg (pow_pos hr 2) (sq_nonneg a)).ne'
  rw [← hv]
  exact tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto

/-- As `r → r₊` from above, the lower end `Ω₋` of the window tends to `Ω_H = a/(r₊² + a²)`: the
window closes on the angular velocity of the horizon. -/
theorem tendsto_omegaMinus (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {c : ℝ} (hc1 : -1 < c)
    (hc2 : c < 1) :
    Tendsto (fun r => omegaMinus M a r c) (𝓝[>] horizon M a) (𝓝 (horizonRate M a)) := by
  have hc : 0 < 1 - c ^ 2 := by nlinarith
  have hr : 0 < horizon M a := hM.trans_le (le_horizon M a)
  have hS := sig_pos a c hr
  have hp := gpp_pos (a := a) hM.le hr hc
  have hcont : ContinuousAt (fun r => omegaMinus M a r c) (horizon M a) :=
    ((continuousAt_gtp (M := M) hS.ne').neg.sub (continuousAt_sqrt (M := M) (a := a) c)).div
      (continuousAt_gpp hS.ne') hp.ne'
  have hv : omegaMinus M a (horizon M a) c = horizonRate M a := by
    have hd := del_horizon ha
    rw [omegaMinus, hd, zero_mul, Real.sqrt_zero, sub_zero, horizonRate]
    unfold del at hd
    exact rate_identity hM.ne' hr.ne' hc.ne' hS.ne' hd
      (add_pos_of_pos_of_nonneg (pow_pos hr 2) (sq_nonneg a)).ne'
  rw [← hv]
  exact tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto

/-- The inverse coefficients of the Kerr metric: `g^{tt} = −g_φφ/(Δ(1 − χ²))`,
`g^{tφ} = g_tφ/(Δ(1 − χ²))`, `g^{rr} = Δ/Σ`, `g^{χχ} = (1 − χ²)/Σ`,
`g^{φφ} = −g_tt/(Δ(1 − χ²))`. -/
def inverseTable (M a r c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-gpp M a r c / (del M a r * (1 - c ^ 2)), 0, 0, gtp M a r c / (del M a r * (1 - c ^ 2));
    0, del M a r / sig a r c, 0, 0;
    0, 0, (1 - c ^ 2) / sig a r c, 0;
    gtp M a r c / (del M a r * (1 - c ^ 2)), 0, 0, -gtt M a r c / (del M a r * (1 - c ^ 2))]

/-- The inverse of the matrix of coefficients is `inverseTable`. -/
theorem coefficient_inv (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) :
    ((metric hM ha).coefficient x)⁻¹ = inverseTable M a (x 1) (x 2) := by
  have hS := sig_ne hM hx
  have hD := del_ne ha hx
  have hc := one_sub_sq_ne hx
  have key := gtt_mul_gpp_sub_sq (M := M) hS
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  simp only [coefficient_eq hM ha]
  fin_cases i <;> fin_cases j <;> simp [metricTable, inverseTable, grr, gcc]
  all_goals field_simp
  all_goals first | linear_combination (-1 : ℝ) * key | ring

/-- **The horizon as the surface `g^{rr} = 0`** (Landau–Lifshitz §104): on the domain
`g^{rr} = Δ/Σ`. -/
theorem inverse_rr (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) :
    ((metric hM ha).coefficient x)⁻¹ 1 1 = del M a (x 1) / sig a (x 1) (x 2) := by
  rw [coefficient_inv hM ha hx]
  simp [inverseTable]

/-- As `r → r₊` from above at fixed `t`, `χ`, `φ`, the inverse coefficient `g^{rr} = Δ/Σ` tends
to `0`. -/
theorem tendsto_inverse_rr (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (t c φ : ℝ) (hc1 : -1 < c)
    (hc2 : c < 1) :
    Tendsto (fun r => ((metric hM ha).coefficient ![t, r, c, φ])⁻¹ 1 1) (𝓝[>] horizon M a)
      (𝓝 0) := by
  have hr : 0 < horizon M a := hM.trans_le (le_horizon M a)
  have hS := sig_pos a c hr
  have heq : (fun r => del M a r / sig a r c) =ᶠ[𝓝[>] horizon M a]
      fun r => ((metric hM ha).coefficient ![t, r, c, φ])⁻¹ 1 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr'
    have hmem : (![t, r, c, φ] : MinkowskiModel 3) ∈ domain M a :=
      ⟨show horizon M a < r from hr', show -1 < c from hc1, show c < 1 from hc2⟩
    rw [inverse_rr hM ha hmem]
    rfl
  refine Tendsto.congr' heq ?_
  have hcont : ContinuousAt (fun r => del M a r / sig a r c) (horizon M a) :=
    ((by unfold del; fun_prop : Continuous fun r => del M a r).continuousAt).div
      ((by unfold sig; fun_prop : Continuous fun r => sig a r c).continuousAt) hS.ne'
  have h0 : del M a (horizon M a) / sig a (horizon M a) c = 0 := by
    rw [del_horizon ha, zero_div]
  rw [← h0]
  exact tendsto_nhdsWithin_of_tendsto_nhds hcont.tendsto

/-! ### The Schwarzschild limit `a = 0` -/

/-- For `a = 0` the outer horizon is the sphere `r = 2M`. -/
theorem horizon_zero (hM : 0 ≤ M) : horizon M 0 = 2 * M := by
  unfold horizon
  rw [zero_pow two_ne_zero, sub_zero, Real.sqrt_sq hM]
  ring

/-- The map `(t, r, χ, φ) ↦ (t, r, arccos χ, φ)` to the co-ordinates `(t, r, θ, φ)` of
`SchwarzschildExterior`. -/
def toAngle (x : MinkowskiModel 3) : MinkowskiModel 3 := ![x 0, x 1, Real.arccos (x 2), x 3]

/-- The linear map `(v₀, v₁, v₂, v₃) ↦ (v₀, v₁, −v₂/√(1 − χ²), v₃)` at the point `x`. -/
def toAngleLinear (x : MinkowskiModel 3) : MinkowskiModel 3 →ₗ[ℝ] MinkowskiModel 3 where
  toFun v := ![v 0, v 1, -(v 2 / Real.sqrt (1 - x 2 ^ 2)), v 3]
  map_add' v w := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' t v := by
    funext i
    fin_cases i <;> simp
    ring

/-- The derivative `(v₀, v₁, v₂, v₃) ↦ (v₀, v₁, −v₂/√(1 − χ²), v₃)` of `toAngle` at `x`. -/
def toAngleDeriv (x : MinkowskiModel 3) : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  LinearMap.toContinuousLinearMap (toAngleLinear x)

/-- The value of the derivative of `toAngle`. -/
theorem toAngleDeriv_apply (x v : MinkowskiModel 3) :
    toAngleDeriv x v = ![v 0, v 1, -(v 2 / Real.sqrt (1 - x 2 ^ 2)), v 3] := rfl

/-- A function of `χ = z 2` has the derivative `F'(χ) dχ`. -/
private theorem hasFDerivAt_comp_angle {F : ℝ → ℝ} {F' : ℝ} {y : MinkowskiModel 3}
    (hF : HasDerivAt F F' (y 2)) :
    HasFDerivAt (fun z : MinkowskiModel 3 => F (z 2))
      (F' • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hF.comp_hasFDerivAt y (hasFDerivAt_apply 2 y)

/-- The derivative of `toAngle` at a point with `−1 < χ < 1` is `toAngleDeriv`. -/
theorem hasFDerivAt_toAngle {x : MinkowskiModel 3} (h1 : -1 < x 2) (h2 : x 2 < 1) :
    HasFDerivAt toAngle (toAngleDeriv x) x := by
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · refine (hasFDerivAt_apply 0 x).congr_fderiv ?_
    ext w
    simp [toAngleDeriv_apply]
  · refine (hasFDerivAt_apply 1 x).congr_fderiv ?_
    ext w
    simp [toAngleDeriv_apply]
  · have h := hasFDerivAt_comp_angle (y := x) (Real.hasDerivAt_arccos h1.ne' h2.ne)
    refine h.congr_fderiv ?_
    ext w
    simp [toAngleDeriv_apply]
    ring
  · refine (hasFDerivAt_apply 3 x).congr_fderiv ?_
    ext w
    simp [toAngleDeriv_apply]

/-- `toAngle` sends the domain of the Kerr metric with `a = 0` into the exterior Schwarzschild
domain. -/
theorem toAngle_mem (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M 0) :
    toAngle x ∈ SchwarzschildExterior.domain M := by
  have h1 : horizon M 0 < x 1 := hx.1
  rw [horizon_zero hM] at h1
  exact ⟨h1, Real.arccos_pos.mpr hx.2.2, Real.arccos_lt_pi.mpr hx.2.1⟩

/-- **The Schwarzschild limit** (Landau–Lifshitz §104): for `a = 0` the Kerr form is the exterior
Schwarzschild form pulled back by `toAngle`, `g_S(J v, J w) = g(v, w)` with the derivative
`J = toAngleDeriv x` of `toAngle` (`hasFDerivAt_toAngle`). -/
theorem form_zero_toAngle (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M 0)
    (v w : MinkowskiModel 3) :
    SchwarzschildExterior.form M (toAngle x) (toAngleDeriv x v) (toAngleDeriv x w) =
      form M 0 x v w := by
  have h1 : horizon M 0 < x 1 := hx.1
  rw [horizon_zero hM] at h1
  have hr : x 1 ≠ 0 := by linarith
  have hr2 : x 1 - 2 * M ≠ 0 := by linarith
  have hc := one_sub_sq_pos hx
  have hs : Real.sqrt (1 - x 2 ^ 2) ^ 2 = 1 - x 2 ^ 2 := Real.sq_sqrt hc.le
  have hs0 : Real.sqrt (1 - x 2 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hS0 : x 1 ^ 2 + 0 ^ 2 * x 2 ^ 2 ≠ 0 := by
    rw [zero_pow two_ne_zero, zero_mul, add_zero]
    exact pow_ne_zero 2 hr
  have hD0 : x 1 ^ 2 - 2 * M * x 1 + 0 ^ 2 ≠ 0 := by
    rw [zero_pow two_ne_zero, add_zero, show x 1 ^ 2 - 2 * M * x 1 = x 1 * (x 1 - 2 * M) by ring]
    exact mul_ne_zero hr hr2
  rw [SchwarzschildExterior.form_apply, form_apply, toAngleDeriv_apply, toAngleDeriv_apply]
  simp only [toAngle, Matrix.cons_val, Real.sin_arccos, gtt, gtp, grr, gcc, gpp, sig, del]
  generalize Real.sqrt (1 - x 2 ^ 2) = s at hs hs0 ⊢
  rw [← hs]
  field_simp
  ring

/-! ### Regression: `M = 1`, `a = 1/2` -/

/-- For `M = 1`, `a = 1/2` the outer horizon `r₊ = 1 + √3/2` lies below `r = 19/10`. -/
theorem horizon_regression : horizon 1 (1 / 2) < 19 / 10 := by
  have h : Real.sqrt (1 ^ 2 - (1 / 2) ^ 2) < 9 / 10 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  unfold horizon
  linarith

/-- For `M = 1`, `a = 1/2` the equatorial point `r = 3` lies in the domain, with
`g_tt = −1/3` and `g_tφ = −1/3` there. -/
theorem regression_form :
    (![0, 3, 0, 0] : MinkowskiModel 3) ∈ domain 1 (1 / 2) ∧
      form 1 (1 / 2) ![0, 3, 0, 0] (Pi.single 0 1) (Pi.single 0 1) = -1 / 3 ∧
      form 1 (1 / 2) ![0, 3, 0, 0] (Pi.single 0 1) (Pi.single 3 1) = -1 / 3 := by
  refine ⟨⟨show horizon 1 (1 / 2) < 3 by linarith [horizon_regression],
    show (-1 : ℝ) < 0 by norm_num, show (0 : ℝ) < 1 by norm_num⟩, ?_, ?_⟩
  · rw [form_time]
    norm_num [gtt, sig]
  · rw [form_apply]
    norm_num [gtp, sig]

/-- For `M = 1`, `a = 1/2` the equatorial point `r = 19/10` lies in the ergoregion:
`g_tt = 19/361 > 0`. -/
theorem regression_ergoregion :
    (![0, 19 / 10, 0, 0] : MinkowskiModel 3) ∈ domain 1 (1 / 2) ∧
      0 < form 1 (1 / 2) ![0, 19 / 10, 0, 0] (Pi.single 0 1) (Pi.single 0 1) := by
  refine ⟨⟨show horizon 1 (1 / 2) < 19 / 10 from horizon_regression,
    show (-1 : ℝ) < 0 by norm_num, show (0 : ℝ) < 1 by norm_num⟩, ?_⟩
  rw [form_time]
  norm_num [gtt, sig]

end ProjectAinos.GeneralRelativity.Kerr
