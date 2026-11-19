/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.GeneralRelativity.Kerr

/-! Public consumers of the Kerr field (Landau–Lifshitz §104): the metric in Boyer–Lindquist
co-ordinates with `χ = cos θ` on the exterior domain, its certified Christoffel symbols and the
vacuum equations, the Killing fields, the ergoregion, the window of the angular velocities of
stationary observers with its limit at the horizon, the inverse metric, and the Schwarzschild
limit. Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section


open ContinuousLinearMap Set Filter TopologicalSpace

open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.Kerr

open SmoothGeometry Minkowski

open LorentzMetric (chartField)

open CoordinateMetric (physicalChart christoffelOf ricciOf ricciOfChristoffel scalarOf einsteinOf)

variable {M a : ℝ}

example (a r c : ℝ) :
    ℝ :=
  sig a r c

example (M a r : ℝ) :
    ℝ :=
  del M a r

example (M a : ℝ) :
    ℝ :=
  horizon M a

example (a c : ℝ) {r : ℝ} (hr : 0 < r) :
    0 < sig a r c :=
  sig_pos a c hr

example (ha : a ^ 2 ≤ M ^ 2) :
    del M a (horizon M a) = 0 :=
  del_horizon ha

example (M a : ℝ) :
    M ≤ horizon M a :=
  le_horizon M a

example (ha : a ^ 2 ≤ M ^ 2) {r : ℝ} (hr : horizon M a < r) :
    0 < del M a r :=
  del_pos ha hr

example (M a r c : ℝ) :
    ℝ :=
  gtt M a r c

example (M a r c : ℝ) :
    ℝ :=
  gtp M a r c

example (M a r c : ℝ) :
    ℝ :=
  grr M a r c

example (a r c : ℝ) :
    ℝ :=
  gcc a r c

example (M a r c : ℝ) :
    ℝ :=
  gpp M a r c

example {r c : ℝ} (hS : sig a r c ≠ 0) :
    gtt M a r c * gpp M a r c - gtp M a r c ^ 2 = -(del M a r * (1 - c ^ 2)) :=
  gtt_mul_gpp_sub_sq hS

example (hM : 0 ≤ M) {r c : ℝ} (hr : 0 < r) (hc : 0 < 1 - c ^ 2) :
    0 < gpp M a r c :=
  gpp_pos hM hr hc

example (M a : ℝ) :
    Opens (MinkowskiModel 3) :=
  domain M a

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    0 < x 1 :=
  radius_pos hM hx

example {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    0 < 1 - x 2 ^ 2 :=
  one_sub_sq_pos hx

example (M a : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
  form M a x

example (x v w : MinkowskiModel 3) :
    form M a x v w = gtt M a (x 1) (x 2) * (v 0 * w 0) +
      gtp M a (x 1) (x 2) * (v 0 * w 3 + v 3 * w 0) + grr M a (x 1) (x 2) * (v 1 * w 1) +
      gcc a (x 1) (x 2) * (v 2 * w 2) + gpp M a (x 1) (x 2) * (v 3 * w 3) :=
  form_apply x v w

example (x v w : MinkowskiModel 3) :
    form M a x v w = form M a x w v :=
  form_symm x v w

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    ContDiffOn ℝ ∞ (form M a) (domain M a) :=
  contDiffOn_form hM ha

example (k : ℝ) :
    MinkowskiModel 3 ≃ₗ[ℝ] MinkowskiModel 3 :=
  shearLinear k

example (k : ℝ) :
    MinkowskiModel 3 ≃L[ℝ] MinkowskiModel 3 :=
  shear k

example (k : ℝ) (v : MinkowskiModel 3) :
    shear k v = ![v 0, v 1, v 2, v 3 + k * v 0] :=
  shear_apply k v

example (M a : ℝ) (x : MinkowskiModel 3) :
    ℝ :=
  frameRate M a x

example (M a : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 ≃L[ℝ] MinkowskiModel 3 :=
  pointFrame M a x

example {x : MinkowskiModel 3} (hS : sig a (x 1) (x 2) ≠ 0) (hp : gpp M a (x 1) (x 2) ≠ 0) :
    form M a x (pointFrame M a x (Fin.cons 1 (0 : Fin 3 → ℝ)))
        (pointFrame M a x (Fin.cons 1 (0 : Fin 3 → ℝ))) =
      -(del M a (x 1) * (1 - x 2 ^ 2)) / gpp M a (x 1) (x 2) :=
  form_pointFrame_time hS hp

example (x : MinkowskiModel 3) (v : Fin 3 → ℝ) :
    form M a x (pointFrame M a x (Fin.cons 0 v)) (pointFrame M a x (Fin.cons 0 v)) =
      grr M a (x 1) (x 2) * (v 0 * v 0) + gcc a (x 1) (x 2) * (v 1 * v 1) +
        gpp M a (x 1) (x 2) * (v 2 * v 2) :=
  form_pointFrame_space x v

example {p q s : ℝ} (hp : 0 < p) (hq : 0 < q) (hs : 0 < s) {v : Fin 3 → ℝ} (hv : v ≠ 0) :
    0 < p * (v 0 * v 0) + q * (v 1 * v 1) + s * (v 2 * v 2) :=
  diagonal_pos hp hq hs hv

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    CoordinateMetric .timeNegative 3 (domain M a) :=
  metric hM ha

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x : MinkowskiModel 3) :
    (metric hM ha).form x = form M a x :=
  metric_form hM ha x

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x : MinkowskiModel 3) (i j : Fin 4) :
    (metric hM ha).coefficient x i j = form M a x (Pi.single i 1) (Pi.single j 1) :=
  coefficient_apply hM ha x i j

example (k : Fin 4) (hk : k = 0 ∨ k = 3) (y : MinkowskiModel 3) (t : ℝ) :
    form M a (y + t • Pi.single k 1) = form M a y :=
  form_add k hk y t

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x₀ : domain M a) :
    (metric hM ha).toLorentzMetric.IsKillingField
      (chartField (physicalChart x₀) (Pi.single 0 1)) :=
  isKillingField_time hM ha x₀

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x₀ : domain M a) :
    (metric hM ha).toLorentzMetric.IsKillingField
      (chartField (physicalChart x₀) (Pi.single 3 1)) :=
  isKillingField_angle hM ha x₀

example (M a r c : ℝ) :
    ℝ :=
  chris0_01 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris0_02 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris0_13 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris0_23 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris1_00 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris1_03 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris1_11 M a r c

example (a r c : ℝ) :
    ℝ :=
  chris1_12 a r c

example (M a r c : ℝ) :
    ℝ :=
  chris1_22 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris1_33 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris2_00 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris2_03 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris2_11 M a r c

example (a r c : ℝ) :
    ℝ :=
  chris2_12 a r c

example (a r c : ℝ) :
    ℝ :=
  chris2_22 a r c

example (M a r c : ℝ) :
    ℝ :=
  chris2_33 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris3_01 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris3_02 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris3_13 M a r c

example (M a r c : ℝ) :
    ℝ :=
  chris3_23 M a r c

example (M a r c : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffelTable M a r c

example (M a : ℝ) (x : MinkowskiModel 3) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  christoffel M a x

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3} (hx : x ∈ domain M a)
    (k i j : Fin 4) :
    christoffelOf (metric hM ha).coefficient x k i j = christoffel M a x k i j :=
  christoffelOf_eq hM ha hx k i j

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3} (hx : x ∈ domain M a)
    (j k : Fin 4) :
    ricciOf (metric hM ha).coefficient x j k = 0 :=
  ricciOf_eq_zero hM ha hx j k

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    scalarOf (metric hM ha).coefficient x = 0 :=
  scalarOf_eq_zero hM ha hx

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3} (hx : x ∈ domain M a)
    (i k : Fin 4) :
    einsteinOf (metric hM ha).coefficient x i k = 0 :=
  einsteinOf_eq_zero hM ha hx i k

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (κ : ℝ) :
    (metric hM ha).IsEinstein κ 0 0 :=
  isEinstein_zero hM ha κ

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x y : domain M a) (i k : Fin 4) :
    (metric hM ha).toLorentzMetric.einstein y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 :=
  einstein_chartField hM ha x y i k

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (κ : ℝ) :
    (metric hM ha).toLorentzMetric.SatisfiesEinstein κ 0 0 :=
  satisfiesEinstein_zero hM ha κ

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (x y : domain M a) (j k : Fin 4) :
    (metric hM ha).toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 :=
  ricci_chartField hM ha x y j k

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (y : domain M a)
    (u w : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) :
    (metric hM ha).toLorentzMetric.ricci y u w = 0 :=
  ricci_eq_zero hM ha y u w

example (x : MinkowskiModel 3) :
    form M a x (Pi.single 0 1) (Pi.single 0 1) = gtt M a (x 1) (x 2) :=
  form_time x

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    0 < form M a x (Pi.single 0 1) (Pi.single 0 1) ↔
      x 1 ^ 2 - 2 * M * x 1 + a ^ 2 * x 2 ^ 2 < 0 :=
  ergoregion_iff hM hx

example (hM : 0 < M) (ha0 : a ≠ 0) :
    horizon M a < 2 * M :=
  horizon_lt_two_mul hM ha0

example (hM : 0 < M) (ha0 : a ≠ 0) :
    ∃ x ∈ domain M a, 0 < form M a x (Pi.single 0 1) (Pi.single 0 1) :=
  ergoregion_nonempty hM ha0

example (M a r c : ℝ) :
    ℝ :=
  omegaPlus M a r c

example (M a r c : ℝ) :
    ℝ :=
  omegaMinus M a r c

example (x : MinkowskiModel 3) (Ω : ℝ) :
    form M a x ![1, 0, 0, Ω] ![1, 0, 0, Ω] =
      gtt M a (x 1) (x 2) + 2 * Ω * gtp M a (x 1) (x 2) + Ω ^ 2 * gpp M a (x 1) (x 2) :=
  form_rotating x Ω

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3} (hx : x ∈ domain M a) (Ω : ℝ) :
    form M a x ![1, 0, 0, Ω] ![1, 0, 0, Ω] < 0 ↔
      omegaMinus M a (x 1) (x 2) < Ω ∧ Ω < omegaPlus M a (x 1) (x 2) :=
  form_rotating_neg_iff hM ha hx Ω

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (ha0 : 0 < a) {x : MinkowskiModel 3}
    (hx : x ∈ domain M a) (hergo : 0 < form M a x (Pi.single 0 1) (Pi.single 0 1)) :
    0 < omegaMinus M a (x 1) (x 2) :=
  omegaMinus_pos hM ha ha0 hx hergo

example (M a : ℝ) :
    ℝ :=
  horizonRate M a

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {c : ℝ} (hc1 : -1 < c) (hc2 : c < 1) :
    Tendsto (fun r => omegaPlus M a r c) (𝓝[>] horizon M a) (𝓝 (horizonRate M a)) :=
  tendsto_omegaPlus hM ha hc1 hc2

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {c : ℝ} (hc1 : -1 < c) (hc2 : c < 1) :
    Tendsto (fun r => omegaMinus M a r c) (𝓝[>] horizon M a) (𝓝 (horizonRate M a)) :=
  tendsto_omegaMinus hM ha hc1 hc2

example (M a r c : ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  inverseTable M a r c

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    ((metric hM ha).coefficient x)⁻¹ = inverseTable M a (x 1) (x 2) :=
  coefficient_inv hM ha hx

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) {x : MinkowskiModel 3} (hx : x ∈ domain M a) :
    ((metric hM ha).coefficient x)⁻¹ 1 1 = del M a (x 1) / sig a (x 1) (x 2) :=
  inverse_rr hM ha hx

example (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) (t c φ : ℝ) (hc1 : -1 < c) (hc2 : c < 1) :
    Tendsto (fun r => ((metric hM ha).coefficient ![t, r, c, φ])⁻¹ 1 1) (𝓝[>] horizon M a)
      (𝓝 0) :=
  tendsto_inverse_rr hM ha t c φ hc1 hc2

example (hM : 0 ≤ M) :
    horizon M 0 = 2 * M :=
  horizon_zero hM

example (x : MinkowskiModel 3) :
    MinkowskiModel 3 :=
  toAngle x

example (x : MinkowskiModel 3) :
    MinkowskiModel 3 →ₗ[ℝ] MinkowskiModel 3 :=
  toAngleLinear x

example (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  toAngleDeriv x

example (x v : MinkowskiModel 3) :
    toAngleDeriv x v = ![v 0, v 1, -(v 2 / Real.sqrt (1 - x 2 ^ 2)), v 3] :=
  toAngleDeriv_apply x v

example {x : MinkowskiModel 3} (h1 : -1 < x 2) (h2 : x 2 < 1) :
    HasFDerivAt toAngle (toAngleDeriv x) x :=
  hasFDerivAt_toAngle h1 h2

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M 0) :
    toAngle x ∈ SchwarzschildExterior.domain M :=
  toAngle_mem hM hx

example (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M 0) (v w : MinkowskiModel 3) :
    SchwarzschildExterior.form M (toAngle x) (toAngleDeriv x v) (toAngleDeriv x w) =
      form M 0 x v w :=
  form_zero_toAngle hM hx v w

example :
    horizon 1 (1 / 2) < 19 / 10 :=
  horizon_regression

example :
    (![0, 3, 0, 0] : MinkowskiModel 3) ∈ domain 1 (1 / 2) ∧
      form 1 (1 / 2) ![0, 3, 0, 0] (Pi.single 0 1) (Pi.single 0 1) = -1 / 3 ∧
      form 1 (1 / 2) ![0, 3, 0, 0] (Pi.single 0 1) (Pi.single 3 1) = -1 / 3 :=
  regression_form

example :
    (![0, 19 / 10, 0, 0] : MinkowskiModel 3) ∈ domain 1 (1 / 2) ∧
      0 < form 1 (1 / 2) ![0, 19 / 10, 0, 0] (Pi.single 0 1) (Pi.single 0 1) :=
  regression_ergoregion

end ProjectAinos.GeneralRelativity.Kerr
