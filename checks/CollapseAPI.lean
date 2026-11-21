/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.SmoothGeometry.Lorentzian.OrthogonalSlicing
import ProjectAinos.GeneralRelativity.Collapse

/-! Public consumers of the gravitational collapse of a spherical body (Landau–Lifshitz §102): the
orthogonal slicings with their induced metric, unit normal and second fundamental form, radial
free fall to the horizon in a finite proper time and to the centre, the divergence of the
Schwarzschild time, the red shift of the collapsing surface, the trapping inside `r < 2M` in the
Lemaître chart, and the junction of Oppenheimer and Snyder of a flat dust interior with the
Lemaître exterior. Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its type. -/

noncomputable section


section OrthogonalSlicing

open Set Filter TopologicalSpace

open scoped Topology ContDiff

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

example (g : CoordinateMetric σ d U) (k : Fin (d + 1)) :
    Prop :=
  IsOrthogonalSlicing g k

example (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (z : MinkowskiModel d) :
    Matrix (Fin d) (Fin d) ℝ :=
  inducedMetric g k z

example (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (ε : ℝ) (z : MinkowskiModel d) :
    MinkowskiModel d :=
  unitNormal g k ε z

example (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (ε : ℝ) (z : MinkowskiModel d) :
    Matrix (Fin d) (Fin d) ℝ :=
  secondFundamental g k ε z

example (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (z : MinkowskiModel d) (a b : Fin d) :
    g.inducedMetric k z a b = g.coefficient z (k.succAbove a) (k.succAbove b) :=
  inducedMetric_apply g k z a b

example (g : CoordinateMetric σ d U) (k : Fin (d + 1)) (ε : ℝ) (z : MinkowskiModel d)
    (a b : Fin d) :
    g.secondFundamental k ε z a b = ε / (2 * Real.sqrt |g.coefficient z k k|) *
      fderiv ℝ (fun w => g.coefficient w (k.succAbove a) (k.succAbove b)) z (Pi.single k 1) :=
  secondFundamental_apply g k ε z a b

namespace IsOrthogonalSlicing

variable {g : CoordinateMetric σ d U} {k : Fin (d + 1)} (hg : g.IsOrthogonalSlicing k)
  {z : MinkowskiModel d}

include hg

example (hz : z ∈ U) {μ : Fin (d + 1)} (hμ : μ ≠ k) :
    g.coefficient z μ k = 0 :=
  coefficient_right hg hz hμ

example (hz : z ∈ U) (j : Fin (d + 1)) :
    g.coefficient z k k * (g.coefficient z)⁻¹ k j = if k = j then 1 else 0 :=
  mul_inv_row hg hz j

example (hz : z ∈ U) :
    g.coefficient z k k ≠ 0 :=
  coefficient_self_ne_zero hg hz

example (hz : z ∈ U) (j : Fin (d + 1)) :
    (g.coefficient z)⁻¹ k j = if j = k then (g.coefficient z k k)⁻¹ else 0 :=
  inv_row hg hz j

example (hz : z ∈ U) {μ : Fin (d + 1)} (hμ : μ ≠ k) (v : MinkowskiModel d) :
    fderiv ℝ (fun w => g.coefficient w μ k) z v = 0 :=
  fderiv_coefficient_right hg hz hμ v

example (hz : z ∈ U) {μ : Fin (d + 1)} (hμ : μ ≠ k) (v : MinkowskiModel d) :
    fderiv ℝ (fun w => g.coefficient w k μ) z v = 0 :=
  fderiv_coefficient_left hg hz hμ v

example (hz : z ∈ U) (a b : Fin d) :
    christoffelOf g.coefficient z k (k.succAbove a) (k.succAbove b) =
      -(fderiv ℝ (fun w => g.coefficient w (k.succAbove a) (k.succAbove b)) z
        (Pi.single k 1)) / (2 * g.coefficient z k k) :=
  christoffel_normal hg hz a b

example (hz : z ∈ U) (ε : ℝ) (w : MinkowskiModel d) :
    g.form z (unitNormal g k ε z) w =
      ε / Real.sqrt |g.coefficient z k k| * g.coefficient z k k * w k :=
  form_unitNormal hg hz ε w

example (hz : z ∈ U) (ε : ℝ) :
    g.form z (unitNormal g k ε z) (unitNormal g k ε z) =
      ε ^ 2 * g.coefficient z k k / |g.coefficient z k k| :=
  form_unitNormal_self hg hz ε

example (hz : z ∈ U) (ε : ℝ) (a : Fin d) :
    g.form z (unitNormal g k ε z) (Pi.single (k.succAbove a) 1) = 0 :=
  form_unitNormal_tangent hg hz ε a

example (hz : z ∈ U) (ε : ℝ) (a b : Fin d) :
    g.secondFundamental k ε z a b =
      -g.form z (unitNormal g k ε z)
        (fun μ => christoffelOf g.coefficient z μ (k.succAbove a) (k.succAbove b)) :=
  secondFundamental_eq hg hz ε a b

end IsOrthogonalSlicing

section Diagonal

variable (c : MinkowskiModel d → Fin (d + 1) → ℝ)
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ)

example (k : Fin (d + 1)) :
    (ofDiagonal c hc h0 hs).IsOrthogonalSlicing k :=
  isOrthogonalSlicing_ofDiagonal c hc h0 hs k

example (k : Fin (d + 1)) (z : MinkowskiModel d) :
    (ofDiagonal c hc h0 hs).inducedMetric k z = Matrix.diagonal fun a => c z (k.succAbove a) :=
  inducedMetric_ofDiagonal c hc h0 hs k z

example (k : Fin (d + 1)) (ε : ℝ) (z : MinkowskiModel d) :
    (ofDiagonal c hc h0 hs).secondFundamental k ε z = Matrix.diagonal fun a =>
      ε / (2 * Real.sqrt |c z k|) *
        fderiv ℝ (fun w => c w (k.succAbove a)) z (Pi.single k 1) :=
  secondFundamental_ofDiagonal c hc h0 hs k ε z

end Diagonal

example (k : Fin (d + 1)) :
    (minkowski σ d U).IsOrthogonalSlicing k :=
  isOrthogonalSlicing_minkowski k

namespace IsSynchronous

variable {g : CoordinateMetric .timeNegative d U} (hs : g.IsSynchronous)

include hs

example :
    g.IsOrthogonalSlicing 0 :=
  isOrthogonalSlicing hs

example (z : MinkowskiModel d) (α β : Fin d) :
    g.inducedMetric 0 z α β = g.coefficient z α.succ β.succ :=
  inducedMetric_eq z α β

example {z : MinkowskiModel d} (hz : z ∈ U) (ε : ℝ) (α β : Fin d) :
    g.secondFundamental 0 ε z α β = ε / 2 * g.metricRate z α β :=
  secondFundamental_eq hs hz ε α β

example {z : MinkowskiModel d} (hz : z ∈ U) (ε : ℝ) (α β : Fin d) :
    ∑ δ : Fin d, (g.coefficient z)⁻¹ α.succ δ.succ * g.secondFundamental 0 ε z β δ =
      ε / 2 * g.extrinsicRate z α β :=
  sum_inv_mul_secondFundamental hs hz ε α β

end IsSynchronous

end ProjectAinos.SmoothGeometry.CoordinateMetric

end OrthogonalSlicing

section Collapse

open Set Filter TopologicalSpace

open scoped ContDiff Topology Real

namespace ProjectAinos.GeneralRelativity.Collapse

open SmoothGeometry

example (η : ℝ) :
    ℝ :=
  cycloidTime η

example {h : ℝ} (hh : 0 < h) :
    |Real.sin h| < h :=
  abs_sin_lt hh

example :
    StrictMono cycloidTime :=
  strictMono_cycloidTime

example :
    Continuous cycloidTime :=
  continuous_cycloidTime

example :
    ContDiff ℝ ∞ cycloidTime :=
  contDiff_cycloidTime

example (η : ℝ) :
    HasDerivAt cycloidTime (1 + Real.cos η) η :=
  hasDerivAt_cycloidTime η

example :
    Function.Surjective cycloidTime :=
  surjective_cycloidTime

example (η : ℝ) :
    cycloidTime (-η) = -cycloidTime η :=
  cycloidTime_neg η

example :
    cycloidTime π = π :=
  cycloidTime_pi

example :
    ℝ ≃ₜ ℝ :=
  cycloidHomeomorph

example (s : ℝ) :
    ℝ :=
  cycloidParam s

example (η : ℝ) :
    cycloidHomeomorph η = cycloidTime η :=
  cycloidHomeomorph_apply η

example (s : ℝ) :
    cycloidTime (cycloidParam s) = s :=
  cycloidTime_cycloidParam s

example (η : ℝ) :
    cycloidParam (cycloidTime η) = η :=
  cycloidParam_cycloidTime η

example :
    StrictMono cycloidParam :=
  strictMono_cycloidParam

example :
    Continuous cycloidParam :=
  continuous_cycloidParam

example {s : ℝ} (hs : s ∈ Ioo (-π) π) :
    cycloidParam s ∈ Ioo (-π) π :=
  cycloidParam_mem_Ioo hs

example {η : ℝ} (hη : η ∈ Ioo (-π) π) :
    0 < 1 + Real.cos η :=
  one_add_cos_pos hη

example {s : ℝ} (hs : s ∈ Ioo (-π) π) :
    HasDerivAt cycloidParam (1 + Real.cos (cycloidParam s))⁻¹ s :=
  hasDerivAt_cycloidParam hs

example {s : ℝ} (hs : s ∈ Ioo (-π) π) :
    ContDiffAt ℝ ∞ cycloidParam s :=
  contDiffAt_cycloidParam hs

variable {M r₀ : ℝ}

example (M r₀ : ℝ) :
    ℝ :=
  fallScale M r₀

example (M r₀ : ℝ) :
    ℝ :=
  crunchTime M r₀

example (M r₀ τ : ℝ) :
    ℝ :=
  fallAngle M r₀ τ

example (M r₀ τ : ℝ) :
    ℝ :=
  fallRadius M r₀ τ

example (M r₀ τ : ℝ) :
    ℝ :=
  fallVelocity M r₀ τ

example (hM : 0 < M) (hr : 2 * M < r₀) :
    0 < r₀ :=
  pos_of_two_mul_lt hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    0 < fallScale M r₀ :=
  fallScale_pos hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    fallScale M r₀ ^ 2 = r₀ ^ 3 / (8 * M) :=
  fallScale_sq hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    0 < crunchTime M r₀ :=
  crunchTime_pos hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) (τ : ℝ) :
    fallScale M r₀ * cycloidTime (fallAngle M r₀ τ) = τ :=
  fallScale_mul_cycloidTime hM hr τ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    τ / fallScale M r₀ ∈ Ioo (-π) π :=
  div_fallScale_mem hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    fallAngle M r₀ τ ∈ Ioo (-π) π :=
  fallAngle_mem hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    0 < 1 + Real.cos (fallAngle M r₀ τ) :=
  one_add_cos_fallAngle_pos hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    0 < fallRadius M r₀ τ :=
  fallRadius_pos hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) (τ : ℝ) :
    fallRadius M r₀ τ ≤ r₀ :=
  fallRadius_le hM hr τ

example :
    cycloidParam 0 = 0 :=
  cycloidParam_zero

example :
    fallRadius M r₀ 0 = r₀ :=
  fallRadius_zero

example (hM : 0 < M) (hr : 2 * M < r₀) :
    fallRadius M r₀ (crunchTime M r₀) = 0 :=
  fallRadius_crunchTime hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ fallAngle M r₀ τ :=
  fallAngle_nonneg hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (fallAngle M r₀) (fallScale M r₀ * (1 + Real.cos (fallAngle M r₀ τ)))⁻¹ τ :=
  hasDerivAt_fallAngle hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (fallRadius M r₀) (fallVelocity M r₀ τ) τ :=
  hasDerivAt_fallRadius hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    fallVelocity M r₀ τ ^ 2 = 2 * M / fallRadius M r₀ τ - 2 * M / r₀ :=
  fallVelocity_sq hM hr hτ

example {η : ℝ} (hη : 0 < 1 + Real.cos η) :
    HasDerivAt (fun x => Real.sin x / (1 + Real.cos x)) (1 + Real.cos η)⁻¹ η :=
  hasDerivAt_sin_div hη

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ioo (-crunchTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (fallVelocity M r₀) (-(M / fallRadius M r₀ τ ^ 2)) τ :=
  hasDerivAt_fallVelocity hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ ∞ (fallRadius M r₀) (Ioo (-crunchTime M r₀) (crunchTime M r₀)) :=
  contDiffOn_fallRadius hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ico 0 (crunchTime M r₀)) :
    fallVelocity M r₀ τ ≤ 0 :=
  fallVelocity_nonpos hM hr hτ

example (M r₀ : ℝ) :
    ℝ :=
  horizonAngle M r₀

example (M r₀ : ℝ) :
    ℝ :=
  horizonTime M r₀

example (hM : 0 < M) (hr : 2 * M < r₀) :
    4 * M / r₀ - 1 ∈ Ioo (-1) 1 :=
  horizon_arg_mem hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    horizonAngle M r₀ ∈ Ioo 0 π :=
  horizonAngle_mem hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    Real.cos (horizonAngle M r₀) = 4 * M / r₀ - 1 :=
  cos_horizonAngle hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    0 < horizonTime M r₀ :=
  horizonTime_pos hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    horizonTime M r₀ < crunchTime M r₀ :=
  horizonTime_lt_crunchTime hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    Ioo (-horizonTime M r₀) (horizonTime M r₀) ⊆ Ioo (-crunchTime M r₀) (crunchTime M r₀) :=
  horizon_subset hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    (0 : ℝ) ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀) :=
  zero_mem_horizon hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    fallAngle M r₀ (horizonTime M r₀) = horizonAngle M r₀ :=
  fallAngle_horizonTime hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    fallRadius M r₀ (horizonTime M r₀) = 2 * M :=
  fallRadius_horizonTime hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    |fallAngle M r₀ τ| < horizonAngle M r₀ :=
  abs_fallAngle_lt hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    2 * M < fallRadius M r₀ τ :=
  two_mul_lt_fallRadius hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    0 < 1 - 2 * M / fallRadius M r₀ τ :=
  lapse_fall_pos hM hr hτ

example (M r₀ : ℝ) :
    ℝ :=
  fallEnergy M r₀

example (hM : 0 < M) (hr : 2 * M < r₀) :
    fallEnergy M r₀ ^ 2 = 1 - 2 * M / r₀ :=
  fallEnergy_sq hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    0 < fallEnergy M r₀ :=
  fallEnergy_pos hM hr

example (M r₀ τ : ℝ) :
    ℝ :=
  fallTimeRate M r₀ τ

example (M r₀ τ : ℝ) :
    ℝ :=
  fallTime M r₀ τ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    HasDerivAt (fallTimeRate M r₀)
      (-(fallEnergy M r₀ * (2 * M * fallVelocity M r₀ τ / fallRadius M r₀ τ ^ 2)) /
        (1 - 2 * M / fallRadius M r₀ τ) ^ 2) τ :=
  hasDerivAt_fallTimeRate hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) :
    ContinuousOn (fallTimeRate M r₀) (Ioo (-horizonTime M r₀) (horizonTime M r₀)) :=
  continuousOn_fallTimeRate hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    HasDerivAt (fallTime M r₀) (fallTimeRate M r₀ τ) τ :=
  hasDerivAt_fallTime hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ ∞ (fallTimeRate M r₀) (Ioo (-horizonTime M r₀) (horizonTime M r₀)) :=
  contDiffOn_fallTimeRate hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ 2 (fallTime M r₀) (Ioo (-horizonTime M r₀) (horizonTime M r₀)) :=
  contDiffOn_fallTime hM hr

example (M : ℝ) :
    MinkowskiModel 3 :=
  basePoint M

example (M : ℝ) :
    basePoint M ∈ SchwarzschildExterior.domain M :=
  basePoint_mem M

example {a b c e : ℝ → ℝ} {a' b' c' e' τ : ℝ} (ha : HasDerivAt a a' τ) (hb : HasDerivAt b b' τ)
    (hc : HasDerivAt c c' τ) (he : HasDerivAt e e' τ) :
    HasDerivAt (fun σ => (![a σ, b σ, c σ, e σ] : MinkowskiModel 3)) ![a', b', c', e'] τ :=
  hasDerivAt_vec ha hb hc he

example (M r₀ θ₀ φ₀ τ : ℝ) :
    MinkowskiModel 3 :=
  fallPoint M r₀ θ₀ φ₀ τ

open Classical in

example (M r₀ θ₀ φ₀ : ℝ) (τ : ℝ) :
    SchwarzschildExterior.domain M :=
  fall M r₀ θ₀ φ₀ τ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    fallPoint M r₀ θ₀ φ₀ τ ∈ SchwarzschildExterior.domain M :=
  fallPoint_mem hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) = fallPoint M r₀ θ₀ φ₀ τ :=
  fall_val hM hr hθ hτ

example (M r₀ τ : ℝ) :
    ℝ :=
  fallTimeAccel M r₀ τ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) :
    (SchwarzschildExterior.metric hM.le).toLorentzMetric.IsGeodesicOn
      (Ioo (-horizonTime M r₀) (horizonTime M r₀)) (fall M r₀ θ₀ φ₀) :=
  isGeodesicOn_fall hM hr φ₀ hθ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    HasDerivAt (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3))
      ![fallTimeRate M r₀ τ, fallVelocity M r₀ τ, 0, 0] τ :=
  deriv_fall hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    (SchwarzschildExterior.metric hM.le).toLorentzMetric.form (fall M r₀ θ₀ φ₀ τ)
      (LorentzMetric.curveVelocity (fall M r₀ θ₀ φ₀) τ)
      (LorentzMetric.curveVelocity (fall M r₀ θ₀ φ₀) τ) = -1 :=
  form_curveVelocity_fall hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ : ℝ} (hθ : θ₀ ∈ Ioo 0 π) :
    (fall M r₀ θ₀ φ₀ 0 : MinkowskiModel 3) 1 = r₀ ∧
      deriv (fun σ => (fall M r₀ θ₀ φ₀ σ : MinkowskiModel 3)) 0 1 = 0 :=
  fall_rest hM hr hθ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    properTime (SchwarzschildExterior.metric hM.le).toLorentzMetric (fall M r₀ θ₀ φ₀) 0 τ = τ :=
  properTime_fall hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) :
    (∀ τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀),
      (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 1 =
          r₀ / 2 * (1 + Real.cos (fallAngle M r₀ τ)) ∧
        τ = Real.sqrt (r₀ ^ 3 / (8 * M)) *
          (fallAngle M r₀ τ + Real.sin (fallAngle M r₀ τ)) ∧
        properTime (SchwarzschildExterior.metric hM.le).toLorentzMetric (fall M r₀ θ₀ φ₀) 0 τ =
          τ) ∧
      horizonTime M r₀ = Real.sqrt (r₀ ^ 3 / (8 * M)) *
        (Real.arccos (4 * M / r₀ - 1) + Real.sin (Real.arccos (4 * M / r₀ - 1))) ∧
      Tendsto (fun τ => (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 1) (𝓝[<] horizonTime M r₀)
        (𝓝 (2 * M)) ∧
      horizonTime M r₀ < π * Real.sqrt (r₀ ^ 3 / (8 * M)) ∧
      (∀ τ ∈ Ioo (-(π * Real.sqrt (r₀ ^ 3 / (8 * M)))) (π * Real.sqrt (r₀ ^ 3 / (8 * M))),
        0 < fallRadius M r₀ τ ∧
          fallVelocity M r₀ τ ^ 2 = 2 * M / fallRadius M r₀ τ - 2 * M / r₀ ∧
          HasDerivAt (fallRadius M r₀) (fallVelocity M r₀ τ) τ ∧
          HasDerivAt (fallVelocity M r₀) (-(M / fallRadius M r₀ τ ^ 2)) τ) ∧
      Tendsto (fallRadius M r₀) (𝓝[<] (π * Real.sqrt (r₀ ^ 3 / (8 * M)))) (𝓝 0) :=
  radialInfall_properTime hM hr φ₀ hθ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    -1 < fallVelocity M r₀ τ :=
  neg_one_lt_fallVelocity hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Icc 0 (horizonTime M r₀)) :
    fallRadius M r₀ τ - 2 * M ≤ horizonTime M r₀ - τ :=
  fallRadius_sub_le hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ} (hτ : τ ∈ Ico 0 (horizonTime M r₀)) :
    2 * M * fallEnergy M r₀ *
        (Real.log (horizonTime M r₀) - Real.log (horizonTime M r₀ - τ)) ≤ fallTime M r₀ τ :=
  fallTime_ge hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) :
    Tendsto (fun τ => (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 0) (𝓝[<] horizonTime M r₀)
      atTop :=
  tendsto_coordinateTime hM hr φ₀ hθ

example (M r : ℝ) :
    ℝ :=
  tortoise M r

example (M r : ℝ) :
    ℝ :=
  rayRate M r

example {r : ℝ} (h : 2 * M < r) :
    HasDerivAt (tortoise M) (rayRate M r) r :=
  hasDerivAt_tortoise h

example {r : ℝ} (h : 2 * M < r) :
    HasDerivAt (rayRate M) (-(2 * M) / (r - 2 * M) ^ 2) r :=
  hasDerivAt_rayRate h

example (M t₁ r₁ θ₀ φ₀ s : ℝ) :
    MinkowskiModel 3 :=
  rayPoint M t₁ r₁ θ₀ φ₀ s

open Classical in

example (M t₁ r₁ θ₀ φ₀ : ℝ) (s : ℝ) :
    SchwarzschildExterior.domain M :=
  outgoingRay M t₁ r₁ θ₀ φ₀ s

example {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hs : s ∈ Ioi (2 * M - r₁)) :
    rayPoint M t₁ r₁ θ₀ φ₀ s ∈ SchwarzschildExterior.domain M :=
  rayPoint_mem hθ hs

example {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hs : s ∈ Ioi (2 * M - r₁)) :
    (outgoingRay M t₁ r₁ θ₀ φ₀ s : MinkowskiModel 3) = rayPoint M t₁ r₁ θ₀ φ₀ s :=
  outgoingRay_val hθ hs

example {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hs : s ∈ Ioi (2 * M - r₁)) :
    HasDerivAt (fun s => (outgoingRay M t₁ r₁ θ₀ φ₀ s : MinkowskiModel 3))
      ![rayRate M (r₁ + s), 1, 0, 0] s :=
  deriv_outgoingRay hθ hs

example (hM : 0 ≤ M) (t₁ r₁ : ℝ) {θ₀ : ℝ} (φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) :
    (SchwarzschildExterior.metric hM).toLorentzMetric.IsGeodesicOn (Ioi (2 * M - r₁))
      (outgoingRay M t₁ r₁ θ₀ φ₀) :=
  isGeodesicOn_outgoingRay hM t₁ r₁ φ₀ hθ

example (hM : 0 ≤ M) {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hs : s ∈ Ioi (2 * M - r₁)) :
    (SchwarzschildExterior.metric hM).toLorentzMetric.form (outgoingRay M t₁ r₁ θ₀ φ₀ s)
      (LorentzMetric.curveVelocity (outgoingRay M t₁ r₁ θ₀ φ₀) s)
      (LorentzMetric.curveVelocity (outgoingRay M t₁ r₁ θ₀ φ₀) s) = 0 :=
  form_outgoingRay_velocity hM hθ hs

example (hM : 0 ≤ M) (x₀ : SchwarzschildExterior.domain M) {t₁ r₁ θ₀ φ₀ s : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hs : s ∈ Ioi (2 * M - r₁)) :
    (SchwarzschildExterior.metric hM).toLorentzMetric.observedFrequency
        (LorentzMetric.chartField (CoordinateMetric.physicalChart x₀) (Pi.single 0 1))
        (outgoingRay M t₁ r₁ θ₀ φ₀) s =
      1 / Real.sqrt (1 - 2 * M / (r₁ + s)) :=
  observedFrequency_outgoingRay hM x₀ hθ hs

example (M r₀ θ₀ φ₀ τ : ℝ) :
    ℝ → SchwarzschildExterior.domain M :=
  emissionRay M r₀ θ₀ φ₀ τ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    (0 : ℝ) ∈ Ioi (2 * M - fallRadius M r₀ τ) :=
  zero_mem_emission hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    emissionRay M r₀ θ₀ φ₀ τ 0 = fall M r₀ θ₀ φ₀ τ :=
  emissionRay_zero hM hr hθ hτ

example (hM : 0 ≤ M) (r₀ θ₀ φ₀ τ : ℝ) :
    ℝ :=
  emittedFrequency hM r₀ θ₀ φ₀ τ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    emittedFrequency hM.le r₀ θ₀ φ₀ τ =
      (fallEnergy M r₀ - fallVelocity M r₀ τ) / (1 - 2 * M / fallRadius M r₀ τ) :=
  emittedFrequency_eq hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π)
    (x₀ : SchwarzschildExterior.domain M) {R : ℝ} (hR : 2 * M < R) :
    Tendsto (fun τ => (SchwarzschildExterior.metric hM.le).toLorentzMetric.observedFrequency
        (LorentzMetric.chartField (CoordinateMetric.physicalChart x₀) (Pi.single 0 1))
        (emissionRay M r₀ θ₀ φ₀ τ) (R - fallRadius M r₀ τ) / emittedFrequency hM.le r₀ θ₀ φ₀ τ)
      (𝓝[<] horizonTime M r₀) (𝓝 0) :=
  tendsto_observedFrequency hM hr φ₀ hθ x₀ hR

example (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ ∞ (fallVelocity M r₀) (Ioo (-crunchTime M r₀) (crunchTime M r₀)) :=
  contDiffOn_fallVelocity hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    0 < fallEnergy M r₀ - fallVelocity M r₀ τ :=
  fallEnergy_sub_fallVelocity_pos hM hr hτ

example (M r₀ τ : ℝ) :
    ℝ :=
  advancedRate M r₀ τ

example (M r₀ τ : ℝ) :
    ℝ :=
  advancedTime M r₀ τ

example (hM : 0 < M) (hr : 2 * M < r₀) :
    Ioo (-horizonTime M r₀) (crunchTime M r₀) ⊆ Ioo (-crunchTime M r₀) (crunchTime M r₀) :=
  ioo_horizon_crunch_subset hM hr

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (advancedRate M r₀)
      (-(M / fallRadius M r₀ τ ^ 2) / (fallEnergy M r₀ - fallVelocity M r₀ τ) ^ 2) τ :=
  hasDerivAt_advancedRate hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {τ : ℝ}
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (advancedTime M r₀) (advancedRate M r₀ τ) τ :=
  hasDerivAt_advancedTime hM hr hτ

example (hM : 0 < M) (hr : 2 * M < r₀) :
    ContDiffOn ℝ 2 (advancedTime M r₀) (Ioo (-horizonTime M r₀) (crunchTime M r₀)) :=
  contDiffOn_advancedTime hM hr

example (M r₀ θ₀ φ₀ τ : ℝ) :
    MinkowskiModel 3 :=
  advancedPoint M r₀ θ₀ φ₀ τ

example :
    (![0, 1, π / 2, 0] : MinkowskiModel 3) ∈
    EddingtonFinkelstein.domain :=
  basePoint_mem_eddington

open Classical in

example (M r₀ θ₀ φ₀ : ℝ) (τ : ℝ) :
    EddingtonFinkelstein.domain :=
  advancedFall M r₀ θ₀ φ₀ τ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    (advancedFall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) = advancedPoint M r₀ θ₀ φ₀ τ :=
  advancedFall_val hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    HasDerivAt (fun σ => (advancedFall M r₀ θ₀ φ₀ σ : MinkowskiModel 3))
      ![advancedRate M r₀ τ, fallVelocity M r₀ τ, 0, 0] τ :=
  deriv_advancedFall hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) :
    (EddingtonFinkelstein.metric M).toLorentzMetric.IsGeodesicOn
      (Ioo (-horizonTime M r₀) (crunchTime M r₀)) (advancedFall M r₀ θ₀ φ₀) :=
  isGeodesicOn_advancedFall hM hr φ₀ hθ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀)) :
    (EddingtonFinkelstein.metric M).toLorentzMetric.form (advancedFall M r₀ θ₀ φ₀ τ)
      (LorentzMetric.curveVelocity (advancedFall M r₀ θ₀ φ₀) τ)
      (LorentzMetric.curveVelocity (advancedFall M r₀ θ₀ φ₀) τ) = -1 :=
  form_curveVelocity_advancedFall hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π)
    (hτ : τ ∈ Ioo (-horizonTime M r₀) (horizonTime M r₀)) :
    EddingtonFinkelstein.toEddington M (fall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) =
      (advancedFall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) :=
  toEddington_fall hM hr hθ hτ

example (hM : 0 < M) (hr : 2 * M < r₀) {θ₀ : ℝ} (φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) :
    (∀ τ ∈ Ioo (-horizonTime M r₀) (crunchTime M r₀),
      properTime (EddingtonFinkelstein.metric M).toLorentzMetric (advancedFall M r₀ θ₀ φ₀) 0 τ =
        τ) ∧
      (∀ τ ∈ Ioo (horizonTime M r₀) (crunchTime M r₀),
        (advancedFall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 1 < 2 * M) ∧
      Tendsto (fun τ => (advancedFall M r₀ θ₀ φ₀ τ : MinkowskiModel 3) 1)
        (𝓝[<] crunchTime M r₀) (𝓝 0) :=
  advancedFall_properTime hM hr φ₀ hθ

namespace ComovingData

variable (D : ComovingData)

example (x : MinkowskiModel 3) :
    Fin 4 → ℝ :=
  coefficients D x

example (i : Fin 4) :
    ContDiffOn ℝ ∞ (fun x => D.coefficients x i) D.domain :=
  contDiffOn_coefficients D i

example :
    CoordinateMetric .timeNegative 3 D.domain :=
  metric D

example (x : MinkowskiModel 3) :
    D.metric.coefficient x = Matrix.diagonal (D.coefficients x) :=
  coefficient_metric D x

example (x v w : MinkowskiModel 3) :
    D.metric.form x v w = -(v 0 * w 0) + D.A x * (v 1 * w 1) + D.r x ^ 2 * (v 2 * w 2) +
      D.r x ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * w 3) :=
  metric_form_apply D x v w

example :
    D.metric.IsSynchronous :=
  isSynchronous D

example :
    D.metric.IsOrthogonalSlicing 1 :=
  isOrthogonalSlicing D

example (x : MinkowskiModel 3) :
    ℝ :=
  shellEnergy D x

example (x : MinkowskiModel 3) :
    D.metric.inducedMetric 1 x =
      Matrix.diagonal ![-1, D.r x ^ 2, D.r x ^ 2 * Real.sin (x 2) ^ 2] :=
  inducedMetric_eq D x

example {x : MinkowskiModel 3} (hx : x ∈ D.domain) (ε : ℝ) :
    D.metric.secondFundamental 1 ε x =
      Matrix.diagonal ![0, ε * D.shellEnergy x * D.r x,
        ε * D.shellEnergy x * D.r x * Real.sin (x 2) ^ 2] :=
  secondFundamental_eq D hx ε

example {D₁ D₂ : ComovingData} {x₁ x₂ : MinkowskiModel 3} (hx₁ : x₁ ∈ D₁.domain)
    (hx₂ : x₂ ∈ D₂.domain) (hθ : x₁ 2 = x₂ 2) (hr : D₁.r x₁ = D₂.r x₂)
    (hE : D₁.shellEnergy x₁ = D₂.shellEnergy x₂) (ε : ℝ) :
    D₁.metric.inducedMetric 1 x₁ = D₂.metric.inducedMetric 1 x₂ ∧
      D₁.metric.secondFundamental 1 ε x₁ = D₂.metric.secondFundamental 1 ε x₂ :=
  junction hx₁ hx₂ hθ hr hE ε

example {D₁ D₂ : ComovingData} {x₁ x₂ : MinkowskiModel 3} (hx₁ : x₁ ∈ D₁.domain)
    (hx₂ : x₂ ∈ D₂.domain) (hθ : x₁ 2 = x₂ 2) :
    D₁.metric.inducedMetric 1 x₁ = D₂.metric.inducedMetric 1 x₂ ↔ D₁.r x₁ = D₂.r x₂ :=
  inducedMetric_eq_iff hx₁ hx₂ hθ

end ComovingData

example :
    Opens (MinkowskiModel 3) :=
  lemaitreDomain

example (M : ℝ) (x : MinkowskiModel 3) :
    ℝ :=
  lemaitreRadius M x

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    0 < 9 / 2 * M * (x 1 - x 0) ^ 2 :=
  lemaitreBase_pos hM hx

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    0 < lemaitreRadius M x :=
  lemaitreRadius_pos hM hx

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    lemaitreRadius M x ^ 3 = 9 / 2 * M * (x 1 - x 0) ^ 2 :=
  lemaitreRadius_cube hM hx

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    HasFDerivAt (lemaitreRadius M)
      ((2 / 3 * lemaitreRadius M x / (x 1 - x 0)) •
        ((ContinuousLinearMap.proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) -
          ContinuousLinearMap.proj 0)) x :=
  hasFDerivAt_lemaitreRadius hM hx

example (hM : 0 < M) :
    ContDiffOn ℝ ∞ (lemaitreRadius M) lemaitreDomain :=
  contDiffOn_lemaitreRadius hM

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    Real.sqrt (2 * M / lemaitreRadius M x) = 2 / 3 * lemaitreRadius M x / (x 1 - x 0) :=
  sqrt_two_mul_div_lemaitreRadius hM hx

example (hM : 0 < M) :
    ComovingData :=
  lemaitre hM

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    (lemaitre hM).shellEnergy x = 1 :=
  shellEnergy_lemaitre hM hx

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    lemaitreRadius M x < 2 * M ↔ 3 * (x 1 - x 0) < 4 * M :=
  lemaitreRadius_lt_iff hM hx

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ lemaitreDomain)
    (hr : lemaitreRadius M x < 2 * M) {u : MinkowskiModel 3}
    (hu : (lemaitre hM).metric.form x u u ≤ 0) (hu₀ : 0 < u 0) :
    fderiv ℝ (lemaitreRadius M) x u < 0 :=
  radius_deriv_neg_of_causal hM hx hr hu hu₀

open Classical in

example (R₀ θ₀ φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) (τ : ℝ) :
    lemaitreDomain :=
  lemaitreObserver R₀ θ₀ φ₀ hθ τ

example {R₀ θ₀ φ₀ τ : ℝ} (hθ : θ₀ ∈ Ioo 0 π) (hτ : τ < R₀) :
    (lemaitreObserver R₀ θ₀ φ₀ hθ τ : MinkowskiModel 3) = ![τ, R₀, θ₀, φ₀] :=
  lemaitreObserver_val hθ hτ

example (hM : 0 < M) (R₀ : ℝ) {θ₀ : ℝ} (φ₀ : ℝ) (hθ : θ₀ ∈ Ioo 0 π) :
    (lemaitre hM).metric.toLorentzMetric.IsGeodesicOn (Iio R₀)
        (lemaitreObserver R₀ θ₀ φ₀ hθ) ∧
      (∀ τ₁ τ₂ : ℝ, τ₁ < R₀ → τ₂ < R₀ →
        properTime (lemaitre hM).metric.toLorentzMetric (lemaitreObserver R₀ θ₀ φ₀ hθ) τ₁ τ₂ =
          τ₂ - τ₁) ∧
      (∀ τ < R₀, lemaitreRadius M (lemaitreObserver R₀ θ₀ φ₀ hθ τ) < 2 * M ↔
        R₀ - 4 * M / 3 < τ) ∧
      Tendsto (fun τ => lemaitreRadius M (lemaitreObserver R₀ θ₀ φ₀ hθ τ)) (𝓝[<] R₀)
        (𝓝 0) :=
  lemaitreObserver_properTime hM R₀ φ₀ hθ

example (M r : ℝ) :
    ℝ :=
  lemaitreShift M r

example (hM : 0 < M) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (lemaitreShift M) (1 / (1 + Real.sqrt (2 * M / r))) r :=
  hasDerivAt_lemaitreShift hM hr

example (M : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 :=
  lemaitreToEddington M x

example (β : ℝ) :
    MinkowskiModel 3 →ₗ[ℝ] MinkowskiModel 3 :=
  lemaitreToEddingtonLinear β

example (M : ℝ) (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  lemaitreToEddingtonDeriv M x

example (x v : MinkowskiModel 3) :
    lemaitreToEddingtonDeriv M x v =
      ![v 0 + 2 / 3 * lemaitreRadius M x / (x 1 - x 0) /
          (1 + 2 / 3 * lemaitreRadius M x / (x 1 - x 0)) * (v 1 - v 0),
        2 / 3 * lemaitreRadius M x / (x 1 - x 0) * (v 1 - v 0), v 2, v 3] :=
  lemaitreToEddingtonDeriv_apply x v

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x ∈ lemaitreDomain) :
    lemaitreToEddington M x ∈ EddingtonFinkelstein.domain :=
  lemaitreToEddington_mem hM hx

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) :
    HasFDerivAt (lemaitreToEddington M) (lemaitreToEddingtonDeriv M x) x :=
  hasFDerivAt_lemaitreToEddington hM hx

example (hM : 0 < M) {x : MinkowskiModel 3} (hx : x 0 < x 1) (v w : MinkowskiModel 3) :
    EddingtonFinkelstein.form M (lemaitreToEddington M x) (lemaitreToEddingtonDeriv M x v)
        (lemaitreToEddingtonDeriv M x w) =
      (lemaitre hM).metric.form x v w :=
  form_lemaitreToEddington hM hx v w

variable {τc : ℝ}

example (τc τ : ℝ) :
    ℝ :=
  dustScale τc τ

example (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) :
    0 < (τc - τ) / τc :=
  dustBase_pos hτc hτ

example (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) :
    0 < dustScale τc τ :=
  dustScale_pos hτc hτ

example (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) :
    dustScale τc τ ^ 3 = ((τc - τ) / τc) ^ 2 :=
  dustScale_cube hτc hτ

example (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) :
    HasDerivAt (dustScale τc) (-(2 / 3) * dustScale τc τ / (τc - τ)) τ :=
  hasDerivAt_dustScale hτc hτ

example (hτc : 0 < τc) :
    ContDiffOn ℝ ∞ (dustScale τc) (Iio τc) :=
  contDiffOn_dustScale hτc

example (hτc : 0 < τc) {τ : ℝ} (hτ : τ < τc) :
    HasDerivAt (deriv (dustScale τc)) (-(2 / 9) * dustScale τc τ / (τc - τ) ^ 2) τ :=
  hasDerivAt_deriv_dustScale hτc hτ

example (τc : ℝ) :
    Opens (MinkowskiModel 3) :=
  dustDomain τc

example (hτc : 0 < τc) :
    ComovingData :=
  dustInterior hτc

example (hτc : 0 < τc) {x : MinkowskiModel 3} (hx : x ∈ dustDomain τc) :
    (dustInterior hτc).shellEnergy x = 1 :=
  shellEnergy_dustInterior hτc hx

example (hτc : 0 < τc) :
    FLRW.Data :=
  dustData hτc

example (κ τc τ : ℝ) :
    ℝ :=
  dustDensity κ τc τ

example (hτc : 0 < τc) {κ : ℝ} (hκ : κ ≠ 0) :
    (FLRW.metric (dustData hτc)).IsEinstein κ 0
      (FLRW.perfectFluidStress (dustData hτc) (dustDensity κ τc) fun _ => 0) :=
  isEinstein_dustData hτc hκ

example (x : MinkowskiModel 3) :
    MinkowskiModel 3 :=
  toCartesian x

example (x : MinkowskiModel 3) :
    MinkowskiModel 3 →ₗ[ℝ] MinkowskiModel 3 :=
  toCartesianLinear x

example (x : MinkowskiModel 3) :
    MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  toCartesianDeriv x

example (x v : MinkowskiModel 3) :
    toCartesianDeriv x v = ![v 0,
      v 1 * Real.sin (x 2) * Real.cos (x 3) + x 1 * Real.cos (x 2) * Real.cos (x 3) * v 2 -
        x 1 * Real.sin (x 2) * Real.sin (x 3) * v 3,
      v 1 * Real.sin (x 2) * Real.sin (x 3) + x 1 * Real.cos (x 2) * Real.sin (x 3) * v 2 +
        x 1 * Real.sin (x 2) * Real.cos (x 3) * v 3,
      v 1 * Real.cos (x 2) - x 1 * Real.sin (x 2) * v 2] :=
  toCartesianDeriv_apply x v

example (x : MinkowskiModel 3) :
    HasFDerivAt toCartesian (toCartesianDeriv x) x :=
  hasFDerivAt_toCartesian x

example (hτc : 0 < τc) {x : MinkowskiModel 3} (hx : x ∈ dustDomain τc) :
    toCartesian x ∈ FLRW.domain (dustData hτc) :=
  toCartesian_mem hτc hx

example (hτc : 0 < τc) (x v w : MinkowskiModel 3) :
    (FLRW.metric (dustData hτc)).form (toCartesian x) (toCartesianDeriv x v)
        (toCartesianDeriv x w) =
      (dustInterior hτc).metric.form x v w :=
  form_toCartesian hτc x v w

example (hτc : 0 < τc) {κ M χb : ℝ} (hκ : κ ≠ 0) :
    2 * M = κ / 3 * dustDensity κ τc 0 * χb ^ 3 ↔ 9 * M * τc ^ 2 = 2 * χb ^ 3 :=
  mass_iff hτc hκ

example (hM : 0 < M) (hτc : 0 < τc) {χb : ℝ} (hχ : 0 < χb) (hmass : 9 * M * τc ^ 2 = 2 * χb ^ 3)
    {τ θ φ : ℝ} (hτ : τ < τc) :
    lemaitreRadius M ![τ, τc, θ, φ] = dustScale τc τ * χb :=
  dustScale_mul_eq_lemaitreRadius hM hτc hχ hmass hτ

example (hM : 0 < M) {χb Rb : ℝ} (hτc : 0 < τc) (hχ : 0 < χb) {κ : ℝ} (hκ : κ ≠ 0) {θ : ℝ} (φ : ℝ)
    (hθ : θ ∈ Ioo 0 π) (ε : ℝ) :
    ((∀ τ < min Rb τc, (lemaitre hM).metric.inducedMetric 1 ![τ, Rb, θ, φ] =
        (dustInterior hτc).metric.inducedMetric 1 ![τ, χb, θ, φ]) ↔
      Rb = τc ∧ 2 * M = κ / 3 * dustDensity κ τc 0 * χb ^ 3) ∧
    (Rb = τc → 2 * M = κ / 3 * dustDensity κ τc 0 * χb ^ 3 → ∀ τ < τc,
      (lemaitre hM).metric.inducedMetric 1 ![τ, Rb, θ, φ] =
          (dustInterior hτc).metric.inducedMetric 1 ![τ, χb, θ, φ] ∧
        (lemaitre hM).metric.secondFundamental 1 ε ![τ, Rb, θ, φ] =
          (dustInterior hτc).metric.secondFundamental 1 ε ![τ, χb, θ, φ] ∧
        κ / 3 * dustDensity κ τc τ * (dustScale τc τ * χb) ^ 3 = 2 * M) :=
  junction_oppenheimerSnyder hM hτc hχ hκ φ hθ ε

example {D₁ D₂ : ComovingData} {x₁ x₂ : MinkowskiModel 3} (hx₁ : x₁ ∈ D₁.domain)
    (hx₂ : x₂ ∈ D₂.domain) (hθ : x₁ 2 = x₂ 2) (hr : D₁.r x₁ = D₂.r x₂) {ε : ℝ} (hε : ε ≠ 0) :
    D₁.metric.secondFundamental 1 ε x₁ = D₂.metric.secondFundamental 1 ε x₂ ↔
      D₁.shellEnergy x₁ = D₂.shellEnergy x₂ :=
  ComovingData.secondFundamental_eq_iff hx₁ hx₂ hθ hr hε

example (I : Set ℝ) (hI : IsOpen I) :
    Opens (MinkowskiModel 3) :=
  closedDomain I hI

example (I : Set ℝ) (hI : IsOpen I) (a : ℝ → ℝ) (ha : ContDiffOn ℝ ∞ a I)
    (hpos : ∀ τ ∈ I, 0 < a τ) :
    ComovingData :=
  closedInterior I hI a ha hpos

example {I : Set ℝ} {hI : IsOpen I} {a : ℝ → ℝ} {ha : ContDiffOn ℝ ∞ a I}
    {hpos : ∀ τ ∈ I, 0 < a τ} {x : MinkowskiModel 3} (hx : x ∈ closedDomain I hI) :
    (closedInterior I hI a ha hpos).shellEnergy x = Real.cos (x 1) :=
  shellEnergy_closedInterior hx

example (hM : 0 < M) {I : Set ℝ} {hI : IsOpen I} {a : ℝ → ℝ} {ha : ContDiffOn ℝ ∞ a I}
    {hpos : ∀ τ ∈ I, 0 < a τ} {xL xI : MinkowskiModel 3} (hxL : xL ∈ lemaitreDomain)
    (hxI : xI ∈ closedDomain I hI) (hθ : xL 2 = xI 2)
    (h : (lemaitre hM).metric.inducedMetric 1 xL =
      (closedInterior I hI a ha hpos).metric.inducedMetric 1 xI)
    {ε : ℝ} (hε : ε ≠ 0) :
    (lemaitre hM).metric.secondFundamental 1 ε xL ≠
      (closedInterior I hI a ha hpos).metric.secondFundamental 1 ε xI :=
  secondFundamental_closedInterior_ne_lemaitre hM hxL hxI hθ h hε

end ProjectAinos.GeneralRelativity.Collapse

end Collapse
