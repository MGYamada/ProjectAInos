/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildExterior
public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateFrameCriterion
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateGeodesic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The Schwarzschild field in Eddington–Finkelstein co-ordinates

In the ingoing co-ordinates `(v, r, θ, φ)` of Eddington and Finkelstein on the domain `r > 0`,
`0 < θ < π`, the field of a mass `M` has the metric
`ds² = −(1 − 2M/r) dv² + 2 dv dr + r² dθ² + r² sin²θ dφ²` (Landau–Lifshitz, §§100, 102). The
coefficients are regular across the sphere `r = 2M`, where the co-ordinate `v` becomes null, so
the Lorentz signature is checked in a pointwise frame (`ofFrameCriterion`) and not on the axis
`e₀`.

* `metric`: the form is a Lorentz metric on the whole domain, through the horizon.
* `christoffelOf_eq`: the Christoffel symbols are the table `christoffel`, certified by its
  lowered identity.
* `ricciOf_eq_zero`, `ricci_eq_zero`: the field is a vacuum solution, `R_{ik} = 0`, in the
  co-ordinates and for the native Ricci tensor.
* `isGeodesicOn_ingoing`, `form_ingoingRay_velocity`, `exists_ingoingRay_lt`: the curves
  `λ ↦ (v₀, r₀ − λ, θ₀, φ₀)` are null geodesics, and they cross the sphere `r = 2M`.
* `radial_lt_zero_of_causal`: inside the sphere `r = 2M` every causal vector with `dv > 0` has
  `dr < 0` (§102: no particle remains at rest inside, every one falls to the centre).
* `hasFDerivAt_toEddington`, `form_toEddington`: for `M > 0` and `r > 2M` the map
  `(t, r, θ, φ) ↦ (t + r + 2M log(r/2M − 1), r, θ, φ)` pulls this metric back to the exterior
  Schwarzschild metric of `SchwarzschildExterior`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.EddingtonFinkelstein

open SmoothGeometry Minkowski
open LorentzMetric (chartField curveVelocity)
open CoordinateMetric (physicalChart christoffelOf ricciOf ricciOfChristoffel)

variable {M : ℝ}

/-! ### The form and the metric -/

/-- The domain `r > 0`, `0 < θ < π` of the co-ordinates `(v, r, θ, φ)`, through the sphere
`r = 2M`. -/
def domain : Opens (MinkowskiModel 3) :=
  ⟨{x | 0 < x 1 ∧ 0 < x 2 ∧ x 2 < Real.pi},
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      ((isOpen_lt continuous_const (continuous_apply 2)).inter
        (isOpen_lt (continuous_apply 2) continuous_const)))⟩

/-- The Eddington–Finkelstein form
`−(1 − 2M/r) dv ⊗ dv + dv ⊗ dr + dr ⊗ dv + r² dθ ⊗ dθ + r² sin²θ dφ ⊗ dφ` at the point `x`. -/
def form (M : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ :=
  (-(1 - 2 * M / x 1)) •
      (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
    (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
    (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 0 : MinkowskiModel 3 →L[ℝ] ℝ) +
    (x 1 ^ 2) •
      (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ) +
    (x 1 ^ 2 * Real.sin (x 2) ^ 2) •
      (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ).smulRight (proj 3 : MinkowskiModel 3 →L[ℝ] ℝ)

/-- The value of the Eddington–Finkelstein form on two vectors. -/
theorem form_apply (x v w : MinkowskiModel 3) :
    form M x v w = -(1 - 2 * M / x 1) * (v 0 * w 0) + v 0 * w 1 + v 1 * w 0 +
      x 1 ^ 2 * (v 2 * w 2) + x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * w 3) := by
  simp only [form, add_apply, smul_apply, smulRight_apply, proj_apply, smul_eq_mul]

/-- The form is symmetric. -/
theorem form_symm (x v w : MinkowskiModel 3) : form M x v w = form M x w v := by
  rw [form_apply, form_apply]
  ring

/-- The form is smooth on the domain. -/
theorem contDiffOn_form : ContDiffOn ℝ ∞ (form M) domain := by
  refine contDiffOn_clm_apply.mpr fun v => contDiffOn_clm_apply.mpr fun w => ?_
  have h1 : ∀ x ∈ (domain : Set (MinkowskiModel 3)), x 1 ≠ 0 := fun x hx => hx.1.ne'
  have hr : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 1 := contDiff_apply ℝ (fun _ => ℝ) 1
  have hθ : ContDiff ℝ ∞ fun x : MinkowskiModel 3 => x 2 := contDiff_apply ℝ (fun _ => ℝ) 2
  have hA : ContDiffOn ℝ ∞ (fun x : MinkowskiModel 3 => 2 * M / x 1) domain :=
    contDiffOn_const.div hr.contDiffOn h1
  simp only [form_apply]
  have hv (a b : Fin 4) : ContDiff ℝ ∞ fun _ : MinkowskiModel 3 => v a * w b := contDiff_const
  exact (((((contDiffOn_const.sub hA).neg.mul (hv 0 0).contDiffOn).add (hv 0 1).contDiffOn).add
    (hv 1 0).contDiffOn).add ((hr.pow 2).contDiffOn.mul (hv 2 2).contDiffOn)).add
    (((hr.pow 2).mul (hθ.sin.pow 2)).contDiffOn.mul (hv 3 3).contDiffOn)

/-- The linear map `(v₀, v₁, v₂, v₃) ↦ (v₀ + b v₁, v₁ − a v₀, v₂, v₃)`, invertible when
`1 + a b ≠ 0`. -/
def frameLinear (a b : ℝ) (h : 1 + a * b ≠ 0) : MinkowskiModel 3 ≃ₗ[ℝ] MinkowskiModel 3 where
  toFun v := ![v 0 + b * v 1, v 1 - a * v 0, v 2, v 3]
  invFun w := ![(w 0 - b * w 1) / (1 + a * b), (a * w 0 + w 1) / (1 + a * b), w 2, w 3]
  map_add' v w := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp <;> ring
  left_inv v := by
    have h' : 1 + b * a ≠ 0 := by rwa [mul_comm]
    funext i
    fin_cases i <;> simp
    · field_simp
      ring
    · field_simp
      ring
  right_inv v := by
    have h' : 1 + b * a ≠ 0 := by rwa [mul_comm]
    funext i
    fin_cases i <;> simp
    · field_simp
      ring
    · field_simp
      ring

/-- The change of basis `e₀ ↦ e₀ − a e₁`, `e₁ ↦ e₁ + b e₀`, `e₂ ↦ e₂`, `e₃ ↦ e₃`, for
`1 + a b ≠ 0`. -/
def frame (a b : ℝ) (h : 1 + a * b ≠ 0) : MinkowskiModel 3 ≃L[ℝ] MinkowskiModel 3 :=
  (frameLinear a b h).toContinuousLinearEquiv

/-- The value of the change of basis. -/
theorem frame_apply (a b : ℝ) (h : 1 + a * b ≠ 0) (v : MinkowskiModel 3) :
    frame a b h v = ![v 0 + b * v 1, v 1 - a * v 0, v 2, v 3] := by
  rw [frame, LinearEquiv.coe_toContinuousLinearEquiv']
  rfl

/-- The coefficient `λ = 1 + |M|/|r|` of the frame: on the domain it is `1 + |M|/r`. -/
def frameTime (M : ℝ) (x : MinkowskiModel 3) : ℝ := 1 + |M| / |x 1|

/-- The coefficient `μ = 1/(1 + |1 − 2M/r|)` of the frame. -/
def frameSpace (M : ℝ) (x : MinkowskiModel 3) : ℝ := 1 / (1 + |1 - 2 * M / x 1|)

/-- On the domain the coefficient `λ` of the frame is `1 + |M|/r`. -/
theorem frameTime_eq {x : MinkowskiModel 3} (hx : x ∈ domain) : frameTime M x = 1 + |M| / x 1 := by
  rw [frameTime, abs_of_pos hx.1]

/-- The coefficient `λ` of the frame is positive. -/
theorem frameTime_pos (M : ℝ) (x : MinkowskiModel 3) : 0 < frameTime M x := by
  unfold frameTime
  positivity

/-- The coefficient `μ` of the frame is positive. -/
theorem frameSpace_pos (M : ℝ) (x : MinkowskiModel 3) : 0 < frameSpace M x := by
  unfold frameSpace
  positivity

/-- The determinant `1 + λ μ` of the frame does not vanish. -/
theorem frame_det_ne_zero (M : ℝ) (x : MinkowskiModel 3) :
    1 + frameTime M x * frameSpace M x ≠ 0 :=
  (add_pos one_pos (mul_pos (frameTime_pos M x) (frameSpace_pos M x))).ne'

/-- The pointwise frame `P x`: `e₀ ↦ e₀ − λ e₁`, `e₁ ↦ e₁ + μ e₀`, with `λ = frameTime M x`
and `μ = frameSpace M x`. -/
def pointFrame (M : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 ≃L[ℝ] MinkowskiModel 3 :=
  frame (frameTime M x) (frameSpace M x) (frame_det_ne_zero M x)

/-- The form on the time vector of the frame: `B(Pe₀, Pe₀) = −(1 − 2M/r) − 2λ`. -/
theorem form_pointFrame_time (x : MinkowskiModel 3) :
    form M x (pointFrame M x (Fin.cons 1 (0 : Fin 3 → ℝ)))
        (pointFrame M x (Fin.cons 1 (0 : Fin 3 → ℝ))) =
      -(1 - 2 * M / x 1) - 2 * frameTime M x := by
  rw [pointFrame, frame_apply, form_apply]
  have e1 : (Fin.cons 1 (0 : Fin 3 → ℝ) : MinkowskiModel 3) 1 = 0 := rfl
  have e2 : (Fin.cons 1 (0 : Fin 3 → ℝ) : MinkowskiModel 3) 2 = 0 := rfl
  have e3 : (Fin.cons 1 (0 : Fin 3 → ℝ) : MinkowskiModel 3) 3 = 0 := rfl
  simp [e1, e2, e3]
  ring

/-- The form on the spatial vectors of the frame:
`B(P(0, v), P(0, v)) = μ (2 − μ (1 − 2M/r)) v₀² + r² v₁² + r² sin²θ v₂²`. -/
theorem form_pointFrame_space (x : MinkowskiModel 3) (v : Fin 3 → ℝ) :
    form M x (pointFrame M x (Fin.cons 0 v)) (pointFrame M x (Fin.cons 0 v)) =
      frameSpace M x * (2 - frameSpace M x * (1 - 2 * M / x 1)) * (v 0 * v 0) +
        x 1 ^ 2 * (v 1 * v 1) + x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 2 * v 2) := by
  rw [pointFrame, frame_apply, form_apply]
  have e1 : (Fin.cons 0 v : MinkowskiModel 3) 1 = v 0 := rfl
  have e2 : (Fin.cons 0 v : MinkowskiModel 3) 2 = v 1 := rfl
  have e3 : (Fin.cons 0 v : MinkowskiModel 3) 3 = v 2 := rfl
  simp [e1, e2, e3]
  ring

/-- The Schwarzschild field in ingoing Eddington–Finkelstein co-ordinates, a Lorentz metric on
the domain `r > 0`, `0 < θ < π`, through the sphere `r = 2M`. The signature is checked in the
frame `pointFrame`, since `v` is null on `r = 2M`. -/
def metric (M : ℝ) : CoordinateMetric .timeNegative 3 domain :=
  CoordinateMetric.ofFrameCriterion (form M) contDiffOn_form (fun x _ v w => form_symm x v w)
    (pointFrame M)
    (fun x hx => by
      have hr : 0 < x 1 := hx.1
      rw [form_pointFrame_time, LorentzConvention.timeSign_timeNegative]
      have hle : M / x 1 ≤ |M| / |x 1| := by
        rw [abs_of_pos hr]
        exact div_le_div_of_nonneg_right (le_abs_self M) hr.le
      have h2 : 2 * M / x 1 = 2 * (M / x 1) := by ring
      rw [h2]
      unfold frameTime
      linarith)
    (fun x hx v hv => by
      have hr : 0 < x 1 := hx.1
      have hs : 0 < Real.sin (x 2) := Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2
      rw [form_pointFrame_space, LorentzConvention.timeSign_timeNegative, neg_neg, one_mul]
      set f := 1 - 2 * M / x 1
      have hμ := frameSpace_pos M x
      have hμf : frameSpace M x * f < 1 := by
        have h1 : frameSpace M x * (1 + |f|) = 1 :=
          one_div_mul_cancel (by positivity)
        have h2 : frameSpace M x * f ≤ frameSpace M x * |f| :=
          mul_le_mul_of_nonneg_left (le_abs_self f) hμ.le
        nlinarith
      have hB : 0 < frameSpace M x * (2 - frameSpace M x * f) := mul_pos hμ (by linarith)
      have hq : 0 ≤ frameSpace M x * (2 - frameSpace M x * f) * (v 0 * v 0) :=
        mul_nonneg hB.le (mul_self_nonneg _)
      have hq2 : 0 ≤ x 1 ^ 2 * (v 1 * v 1) := mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
      have hq3 : 0 ≤ x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 2 * v 2) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_self_nonneg _)
      by_contra hle
      apply hv
      have z0 : v 0 * v 0 = 0 :=
        (mul_eq_zero.mp (le_antisymm (by linarith) hq)).resolve_left hB.ne'
      have z1 : v 1 * v 1 = 0 :=
        (mul_eq_zero.mp (le_antisymm (by linarith) hq2)).resolve_left (pow_pos hr 2).ne'
      have z2 : v 2 * v 2 = 0 :=
        (mul_eq_zero.mp (le_antisymm (by linarith) hq3)).resolve_left
          (mul_pos (pow_pos hr 2) (pow_pos hs 2)).ne'
      funext i
      fin_cases i
      · exact mul_self_eq_zero.mp z0
      · exact mul_self_eq_zero.mp z1
      · exact mul_self_eq_zero.mp z2)

/-- The form of the metric is the Eddington–Finkelstein form. -/
theorem metric_form (x : MinkowskiModel 3) : (metric M).form x = form M x := rfl

/-- The coefficients of the metric are the values of the form on the basis vectors. -/
theorem coefficient_apply (x : MinkowskiModel 3) (i j : Fin 4) :
    (metric M).coefficient x i j = form M x (Pi.single i 1) (Pi.single j 1) := rfl

/-! ### The derivatives of the coefficients -/

/-- A sum over the four indices of the co-ordinates. -/
theorem sum_four (f : Fin (3 + 1) → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 :=
  Fin.sum_univ_four f

/-- A function of the radius `r = x 1` has the derivative `F'(r) dr`. -/
theorem hasFDerivAt_radial {F : ℝ → ℝ} {F' : ℝ} {y : MinkowskiModel 3}
    (hF : HasDerivAt F F' (y 1)) :
    HasFDerivAt (fun z : MinkowskiModel 3 => F (z 1))
      (F' • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hF.comp_hasFDerivAt y (hasFDerivAt_apply 1 y)

/-- A function of the angle `θ = x 2` has the derivative `G'(θ) dθ`. -/
theorem hasFDerivAt_angular {G : ℝ → ℝ} {G' : ℝ} {y : MinkowskiModel 3}
    (hG : HasDerivAt G G' (y 2)) :
    HasFDerivAt (fun z : MinkowskiModel 3 => G (z 2))
      (G' • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hG.comp_hasFDerivAt y (hasFDerivAt_apply 2 y)

/-- The derivative of the Eddington–Finkelstein form on two constant vectors:
`∂_r g(v, u) dr + ∂_θ g(v, u) dθ`. -/
theorem hasFDerivAt_form_apply {z : MinkowskiModel 3} (hz : z 1 ≠ 0) (v u : MinkowskiModel 3) :
    HasFDerivAt (fun x => form M x v u)
      ((-(2 * M / z 1 ^ 2) * (v 0 * u 0) + 2 * z 1 * (v 2 * u 2) +
          2 * z 1 * Real.sin (z 2) ^ 2 * (v 3 * u 3)) • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
        (z 1 ^ 2 * (2 * Real.sin (z 2) * Real.cos (z 2)) * (v 3 * u 3)) •
          (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) z := by
  have he : (fun x => form M x v u) = fun x =>
      -(1 - 2 * M / x 1) * (v 0 * u 0) + v 0 * u 1 + v 1 * u 0 +
        x 1 ^ 2 * (v 2 * u 2) + x 1 ^ 2 * Real.sin (x 2) ^ 2 * (v 3 * u 3) :=
    funext fun x => form_apply x v u
  rw [he]
  have dA : HasDerivAt (fun r => -(1 - 2 * M / r)) (-(2 * M / z 1 ^ 2)) (z 1) := by
    have h := ((hasDerivAt_id' (z 1)).inv hz).const_mul (2 * M)
    convert (h.const_sub 1).neg using 1
    · funext r
      simp [div_eq_mul_inv]
    · field_simp
  have dR : HasDerivAt (fun r : ℝ => r ^ 2) (2 * z 1) (z 1) := by
    simpa using hasDerivAt_pow 2 (z 1)
  have dS : HasDerivAt (fun θ => Real.sin θ ^ 2) (2 * Real.sin (z 2) * Real.cos (z 2)) (z 2) := by
    convert (Real.hasDerivAt_sin (z 2)).pow 2 using 1
    ring
  have hA := hasFDerivAt_radial dA
  have hR := hasFDerivAt_radial dR
  have hS := hasFDerivAt_angular dS
  have h := ((((hA.mul_const (v 0 * u 0)).add_const (v 0 * u 1)).add_const (v 1 * u 0)).add
    (hR.mul_const (v 2 * u 2))).add ((hR.mul hS).mul_const (v 3 * u 3))
  refine h.congr_fderiv ?_
  ext w
  simp
  ring

/-- The partial derivatives of the form on two constant vectors. -/
theorem fderiv_form_apply {z : MinkowskiModel 3} (hz : z 1 ≠ 0) (v u w : MinkowskiModel 3) :
    fderiv ℝ (fun x => form M x v u) z w =
      w 1 * (-(2 * M / z 1 ^ 2) * (v 0 * u 0) + 2 * z 1 * (v 2 * u 2) +
          2 * z 1 * Real.sin (z 2) ^ 2 * (v 3 * u 3)) +
        w 2 * (z 1 ^ 2 * (2 * Real.sin (z 2) * Real.cos (z 2)) * (v 3 * u 3)) := by
  rw [(hasFDerivAt_form_apply hz v u).fderiv]
  simp
  ring

/-! ### The Christoffel symbols -/

/-- The Christoffel symbols `Γ^k_{ij}` (`christoffel M x k i j`) of the Eddington–Finkelstein
metric: `Γ^0_{00} = M/r²`, `Γ^0_{22} = −r`, `Γ^0_{33} = −r sin²θ`, `Γ^1_{00} = M(r − 2M)/r³`,
`Γ^1_{01} = −M/r²`, `Γ^1_{22} = 2M − r`, `Γ^1_{33} = −(r − 2M) sin²θ`, `Γ^2_{12} = 1/r`,
`Γ^2_{33} = −sin θ cos θ`, `Γ^3_{13} = 1/r`, `Γ^3_{23} = cos θ/sin θ`, symmetric in the lower
indices, the others zero. -/
def christoffel (M : ℝ) (x : MinkowskiModel 3) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![M / x 1 ^ 2, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, -x 1, 0],
      ![0, 0, 0, -x 1 * Real.sin (x 2) ^ 2]],
    ![![M * (x 1 - 2 * M) / x 1 ^ 3, -(M / x 1 ^ 2), 0, 0], ![-(M / x 1 ^ 2), 0, 0, 0],
      ![0, 0, 2 * M - x 1, 0], ![0, 0, 0, (2 * M - x 1) * Real.sin (x 2) ^ 2]],
    ![![0, 0, 0, 0], ![0, 0, 1 / x 1, 0], ![0, 1 / x 1, 0, 0],
      ![0, 0, 0, -(Real.sin (x 2) * Real.cos (x 2))]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1 / x 1], ![0, 0, 0, Real.cos (x 2) / Real.sin (x 2)],
      ![0, 1 / x 1, Real.cos (x 2) / Real.sin (x 2), 0]]]

/-- **The Christoffel symbols of the Eddington–Finkelstein metric** are the table
`christoffel`, certified by its lowered identity. -/
theorem christoffelOf_eq {x : MinkowskiModel 3} (hx : x ∈ domain) (k i j : Fin 4) :
    christoffelOf (metric M).coefficient x k i j = christoffel M x k i j := by
  have hr : x 1 ≠ 0 := hx.1.ne'
  have hs : Real.sin (x 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2).ne'
  refine CoordinateMetric.christoffelOf_eq_of_lowered (metric M) hx (christoffel M x)
    (fun l i j => ?_) k i j
  simp only [coefficient_apply]
  simp only [fderiv_form_apply hr]
  simp only [form_apply, sum_four]
  fin_cases l <;> fin_cases i <;> fin_cases j <;> simp [christoffel] <;> field_simp <;> ring

/-! ### The Ricci tensor -/

/-- The radial derivatives `∂_r Γ^k_{ij}` of the Christoffel symbols. -/
def christoffelRadial (M : ℝ) (x : MinkowskiModel 3) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![-(2 * M) / x 1 ^ 3, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, -1, 0],
      ![0, 0, 0, -Real.sin (x 2) ^ 2]],
    ![![M * (6 * M - 2 * x 1) / x 1 ^ 4, 2 * M / x 1 ^ 3, 0, 0], ![2 * M / x 1 ^ 3, 0, 0, 0],
      ![0, 0, -1, 0], ![0, 0, 0, -Real.sin (x 2) ^ 2]],
    ![![0, 0, 0, 0], ![0, 0, -(1 / x 1 ^ 2), 0], ![0, -(1 / x 1 ^ 2), 0, 0], ![0, 0, 0, 0]],
    ![![0, 0, 0, 0], ![0, 0, 0, -(1 / x 1 ^ 2)], ![0, 0, 0, 0],
      ![0, -(1 / x 1 ^ 2), 0, 0]]]

/-- The angular derivatives `∂_θ Γ^k_{ij}` of the Christoffel symbols. -/
def christoffelAngular (M : ℝ) (x : MinkowskiModel 3) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
      ![0, 0, 0, -x 1 * (2 * Real.sin (x 2) * Real.cos (x 2))]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
      ![0, 0, 0, (2 * M - x 1) * (2 * Real.sin (x 2) * Real.cos (x 2))]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, 0],
      ![0, 0, 0, Real.sin (x 2) ^ 2 - Real.cos (x 2) ^ 2]],
    ![![0, 0, 0, 0], ![0, 0, 0, 0], ![0, 0, 0, -(1 / Real.sin (x 2) ^ 2)],
      ![0, 0, -(1 / Real.sin (x 2) ^ 2), 0]]]

/-- A radial function with the derivative `A dr + B dθ`, `B = 0`. -/
theorem hasFDerivAt_radial_of_eq {F : ℝ → ℝ} {F' A B : ℝ} {y : MinkowskiModel 3}
    (hF : HasDerivAt F F' (y 1)) (hA : F' = A) (hB : B = 0) :
    HasFDerivAt (fun z : MinkowskiModel 3 => F (z 1))
      (A • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) + B • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y := by
  subst hA hB
  simpa using hasFDerivAt_radial hF

/-- An angular function with the derivative `A dr + B dθ`, `A = 0`. -/
theorem hasFDerivAt_angular_of_eq {G : ℝ → ℝ} {G' A B : ℝ} {y : MinkowskiModel 3}
    (hG : HasDerivAt G G' (y 2)) (hA : A = 0) (hB : G' = B) :
    HasFDerivAt (fun z : MinkowskiModel 3 => G (z 2))
      (A • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) + B • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y := by
  subst hA hB
  simpa using hasFDerivAt_angular hG

/-- A product of a radial and an angular function has the derivative `A dr + B dθ`. -/
theorem hasFDerivAt_radial_mul_angular {F G : ℝ → ℝ} {F' G' A B : ℝ} {y : MinkowskiModel 3}
    (hF : HasDerivAt F F' (y 1)) (hG : HasDerivAt G G' (y 2)) (hA : F' * G (y 2) = A)
    (hB : F (y 1) * G' = B) :
    HasFDerivAt (fun z : MinkowskiModel 3 => F (z 1) * G (z 2))
      (A • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) + B • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y := by
  refine ((hasFDerivAt_radial hF).mul (hasFDerivAt_angular hG)).congr_fderiv ?_
  subst hA hB
  ext w
  simp
  ring

/-- The constant zero has the derivative `0 dr + 0 dθ`. -/
theorem hasFDerivAt_zero_of_eq {A B : ℝ} {y : MinkowskiModel 3} (hA : A = 0) (hB : B = 0) :
    HasFDerivAt (fun _ : MinkowskiModel 3 => (0 : ℝ))
      (A • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) + B • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y := by
  subst hA hB
  simpa using hasFDerivAt_const (0 : ℝ) y

/-- The Christoffel symbols depend on `r` and `θ` only, with the derivatives
`christoffelRadial` and `christoffelAngular`. -/
theorem hasFDerivAt_christoffel {y : MinkowskiModel 3} (hy : y ∈ domain) (a b c : Fin 4) :
    HasFDerivAt (fun z => christoffel M z a b c)
      (christoffelRadial M y a b c • (proj 1 : MinkowskiModel 3 →L[ℝ] ℝ) +
        christoffelAngular M y a b c • (proj 2 : MinkowskiModel 3 →L[ℝ] ℝ)) y := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hs : Real.sin (y 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2).ne'
  have d1 : HasDerivAt (fun r => M / r ^ 2) (-(2 * M) / y 1 ^ 3) (y 1) := by
    convert (hasDerivAt_const (y 1) M).fun_div (hasDerivAt_pow 2 (y 1)) (pow_ne_zero 2 hr)
      using 1
    field_simp
    ring
  have d2 : HasDerivAt (fun r : ℝ => -r) (-1) (y 1) := (hasDerivAt_id' (y 1)).neg
  have d3 : HasDerivAt (fun r => M * (r - 2 * M) / r ^ 3) (M * (6 * M - 2 * y 1) / y 1 ^ 4)
      (y 1) := by
    convert (((hasDerivAt_id' (y 1)).sub_const (2 * M)).const_mul M).fun_div
      (hasDerivAt_pow 3 (y 1)) (pow_ne_zero 3 hr) using 1
    field_simp
    ring
  have d4 : HasDerivAt (fun r => -(M / r ^ 2)) (2 * M / y 1 ^ 3) (y 1) := by
    convert d1.neg using 1
    ring
  have d5 : HasDerivAt (fun r : ℝ => 2 * M - r) (-1) (y 1) := by
    simpa using (hasDerivAt_id' (y 1)).const_sub (2 * M)
  have d6 : HasDerivAt (fun r : ℝ => 1 / r) (-(1 / y 1 ^ 2)) (y 1) := by
    convert (hasDerivAt_const (y 1) (1 : ℝ)).fun_div (hasDerivAt_id' (y 1)) hr using 1
    field_simp
    ring
  have a1 : HasDerivAt (fun θ => Real.sin θ ^ 2) (2 * Real.sin (y 2) * Real.cos (y 2)) (y 2) := by
    convert (Real.hasDerivAt_sin (y 2)).pow 2 using 1
    ring
  have a2 : HasDerivAt (fun θ => -(Real.sin θ * Real.cos θ))
      (Real.sin (y 2) ^ 2 - Real.cos (y 2) ^ 2) (y 2) := by
    convert ((Real.hasDerivAt_sin (y 2)).fun_mul (Real.hasDerivAt_cos (y 2))).neg using 1
    ring
  have a3 : HasDerivAt (fun θ => Real.cos θ / Real.sin θ) (-(1 / Real.sin (y 2) ^ 2)) (y 2) := by
    convert (Real.hasDerivAt_cos (y 2)).fun_div (Real.hasDerivAt_sin (y 2)) hs using 1
    field_simp
    linear_combination Real.sin_sq_add_cos_sq (y 2)
  fin_cases a <;> fin_cases b <;> fin_cases c
  all_goals first
    | exact hasFDerivAt_zero_of_eq (by simp [christoffelRadial]) (by simp [christoffelAngular])
    | exact hasFDerivAt_radial_of_eq d1 (by simp [christoffelRadial]) (by simp [christoffelAngular])
    | exact hasFDerivAt_radial_of_eq d2 (by simp [christoffelRadial]) (by simp [christoffelAngular])
    | exact hasFDerivAt_radial_of_eq d3 (by simp [christoffelRadial]) (by simp [christoffelAngular])
    | exact hasFDerivAt_radial_of_eq d4 (by simp [christoffelRadial]) (by simp [christoffelAngular])
    | exact hasFDerivAt_radial_of_eq d5 (by simp [christoffelRadial]) (by simp [christoffelAngular])
    | exact hasFDerivAt_radial_of_eq d6 (by simp [christoffelRadial]) (by simp [christoffelAngular])
    | exact hasFDerivAt_angular_of_eq a2 (by simp [christoffelRadial])
        (by simp [christoffelAngular])
    | exact hasFDerivAt_angular_of_eq a3 (by simp [christoffelRadial])
        (by simp [christoffelAngular])
    | exact hasFDerivAt_radial_mul_angular d2 a1 (by simp [christoffelRadial])
        (by simp [christoffelAngular])
    | exact hasFDerivAt_radial_mul_angular d5 a1 (by simp [christoffelRadial])
        (by simp [christoffelAngular])

/-- The partial derivatives of the Christoffel symbols. -/
theorem fderiv_christoffel {y : MinkowskiModel 3} (hy : y ∈ domain) (a b c : Fin 4)
    (w : MinkowskiModel 3) :
    fderiv ℝ (fun z => christoffel M z a b c) y w =
      w 1 * christoffelRadial M y a b c + w 2 * christoffelAngular M y a b c := by
  rw [(hasFDerivAt_christoffel hy a b c).fderiv]
  simp
  ring

/-- The Ricci formula of the table `christoffel` vanishes on the domain. -/
theorem ricciOfChristoffel_eq_zero {y : MinkowskiModel 3} (hy : y ∈ domain) (j k : Fin 4) :
    ricciOfChristoffel (christoffel M) y j k = 0 := by
  have hr : y 1 ≠ 0 := hy.1.ne'
  have hs : Real.sin (y 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2).ne'
  simp only [ricciOfChristoffel, fderiv_christoffel hy]
  simp only [sum_four]
  fin_cases j <;> fin_cases k <;> simp [christoffel, christoffelRadial, christoffelAngular] <;>
    field_simp <;> first | ring1 | linear_combination (-y 1) * Real.sin_sq_add_cos_sq (y 2)

/-- **The Eddington–Finkelstein field is a vacuum solution**: its Ricci tensor vanishes on the
whole domain, through the sphere `r = 2M` (Landau–Lifshitz §100). -/
theorem ricciOf_eq_zero {x : MinkowskiModel 3} (hx : x ∈ domain) (j k : Fin 4) :
    ricciOf (metric M).coefficient x j k = 0 := by
  have hG : ∀ᶠ z in 𝓝 x, ∀ a b c, christoffelOf (metric M).coefficient z a b c =
      christoffel M z a b c := by
    filter_upwards [domain.isOpen.mem_nhds hx] with z hz using christoffelOf_eq hz
  rw [CoordinateMetric.ricciOf_eq_ricciOfChristoffel hG, ricciOfChristoffel_eq_zero hx]

/-- The native Ricci tensor of the Eddington–Finkelstein metric vanishes on co-ordinate
fields. -/
theorem ricci_chartField (x y : domain) (j k : Fin 4) :
    (metric M).toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 := by
  rw [(metric M).toLorentzMetric_ricci_chartField x y, ricciOf_eq_zero y.property]

/-- **The native Ricci tensor of the Eddington–Finkelstein metric vanishes** at every point of
the domain, through the sphere `r = 2M`. -/
theorem ricci_eq_zero (y : domain) (u w : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) :
    (metric M).toLorentzMetric.ricci y u w = 0 := by
  have he (i : Fin 4) : (Pi.single i 1 : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) =
      chartField (physicalChart y) (Pi.single i 1) y :=
    (CoordinateMetric.physicalChart_chartField y y _).symm
  have hc (j k : Fin 4) : (metric M).toLorentzMetric.ricci y
      (Pi.single j 1 : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) (Pi.single k 1) = 0 := by
    have h := ricci_chartField (M := M) y y j k
    rwa [← he, ← he] at h
  let B : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ := (metric M).toLorentzMetric.ricci y
  have hB (j k : Fin 4) : B (Pi.single j 1) (Pi.single k 1) = 0 := hc j k
  have key (u w : MinkowskiModel 3) : B u w = 0 := by
    rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
    simp only [map_sum, map_smul, _root_.sum_apply, smul_apply, hB, smul_zero,
      Finset.sum_const_zero]
  exact key u w

/-! ### Ingoing radial light rays -/

/-- The ingoing radial ray `λ ↦ (v₀, r₀ − λ, θ₀, φ₀)` for `λ < r₀`, as a curve in the domain;
for `λ ≥ r₀`, where it leaves the domain, it is held at its initial point. -/
def ingoingRay (v₀ r₀ θ₀ φ₀ : ℝ) (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) (t : ℝ) : domain :=
  if h : t < r₀ then ⟨![v₀, r₀ - t, θ₀, φ₀], sub_pos.mpr h, hθ.1, hθ.2⟩
  else ⟨![v₀, r₀, θ₀, φ₀], hr₀, hθ.1, hθ.2⟩

/-- For `λ < r₀` the ray is at `(v₀, r₀ − λ, θ₀, φ₀)`. -/
theorem ingoingRay_val {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) {t : ℝ}
    (ht : t < r₀) :
    (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t : MinkowskiModel 3) = ![v₀, r₀ - t, θ₀, φ₀] := by
  simp [ingoingRay, ht]

/-- For `λ < r₀` the ray is the affine line `(v₀, r₀, θ₀, φ₀) + λ (0, −1, 0, 0)`. -/
theorem ingoingRay_eq_line {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) {t : ℝ}
    (ht : t < r₀) :
    (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t : MinkowskiModel 3) =
      ![v₀, r₀, θ₀, φ₀] + t • ![0, -1, 0, 0] := by
  rw [ingoingRay_val hr₀ hθ ht]
  funext i
  fin_cases i <;> simp
  ring

/-- The velocity of the ray is `(0, −1, 0, 0)` on `λ < r₀`, and its coordinates are `C²`. -/
theorem ingoingRay_deriv {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) {t : ℝ}
    (ht : t < r₀) :
    HasDerivAt (fun t => (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t : MinkowskiModel 3))
      (![0, -1, 0, 0] : MinkowskiModel 3) t := by
  have hev : (fun t' => (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t' : MinkowskiModel 3)) =ᶠ[𝓝 t]
      fun t' => ![v₀, r₀, θ₀, φ₀] + t' • ![0, -1, 0, 0] :=
    eventually_of_mem (isOpen_Iio.mem_nhds ht) fun t' ht' => ingoingRay_eq_line hr₀ hθ ht'
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev
  simpa using ((hasDerivAt_id t).smul_const (![0, -1, 0, 0] : MinkowskiModel 3)).const_add
    (![v₀, r₀, θ₀, φ₀] : MinkowskiModel 3)

/-- **The ingoing radial rays are geodesics** of the Eddington–Finkelstein metric, for every
mass `M`: the curve `λ ↦ (v₀, r₀ − λ, θ₀, φ₀)` on `λ < r₀`. -/
theorem isGeodesicOn_ingoing (M v₀ r₀ θ₀ φ₀ : ℝ) (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi) :
    (metric M).toLorentzMetric.IsGeodesicOn (Iio r₀) (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ) := by
  set γ := ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ
  have hev (t : ℝ) (ht : t ∈ Iio r₀) : (fun t' => (γ t' : MinkowskiModel 3)) =ᶠ[𝓝 t]
      fun t' => ![v₀, r₀, θ₀, φ₀] + t' • ![0, -1, 0, 0] :=
    eventually_of_mem (isOpen_Iio.mem_nhds ht) fun t' ht' => ingoingRay_eq_line hr₀ hθ ht'
  have hline : ContDiff ℝ 2 (fun t : ℝ => (![v₀, r₀, θ₀, φ₀] : MinkowskiModel 3) +
      t • (![0, -1, 0, 0] : MinkowskiModel 3)) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hc : ContDiffOn ℝ 2 (fun t => (γ t : MinkowskiModel 3)) (Iio r₀) :=
    fun t ht => (hline.contDiffAt.congr_of_eventuallyEq (hev t ht)).contDiffWithinAt
  have hderiv (t : ℝ) (ht : t ∈ Iio r₀) :
      deriv (fun t' => (γ t' : MinkowskiModel 3)) t = ![0, -1, 0, 0] :=
    (ingoingRay_deriv hr₀ hθ ht).deriv
  rw [(metric M).isGeodesicOn_iff isOpen_Iio hc]
  intro t ht k
  have hdd : deriv (deriv (fun t' => (γ t' : MinkowskiModel 3))) t = 0 := by
    have h : deriv (fun t' => (γ t' : MinkowskiModel 3)) =ᶠ[𝓝 t] fun _ => ![0, -1, 0, 0] :=
      eventually_of_mem (isOpen_Iio.mem_nhds ht) hderiv
    rw [h.deriv_eq, deriv_const]
  rw [hdd, hderiv t ht]
  simp only [christoffelOf_eq (γ t).property, sum_four]
  fin_cases k <;> simp [christoffel]

/-- **The ingoing radial rays are null**: `g(γ̇, γ̇) = 0` on `λ < r₀`. -/
theorem form_ingoingRay_velocity (M : ℝ) {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀)
    (hθ : θ₀ ∈ Ioo 0 Real.pi) {t : ℝ} (ht : t ∈ Iio r₀) :
    (metric M).toLorentzMetric.form (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t)
      (curveVelocity (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ) t)
      (curveVelocity (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ) t) = 0 := by
  have hd := ingoingRay_deriv (v₀ := v₀) (φ₀ := φ₀) hr₀ hθ ht
  rw [(metric M).form_curveVelocity hd.differentiableAt, hd.deriv, ← CoordinateMetric.form_apply,
    metric_form, form_apply]
  simp

/-- For `0 < M` and `2M < r₀` the ingoing ray starts outside the sphere `r = 2M` and crosses
it: it reaches `r < 2M` at a parameter `λ < r₀`. -/
theorem exists_ingoingRay_lt {v₀ r₀ θ₀ φ₀ : ℝ} (hr₀ : 0 < r₀) (hθ : θ₀ ∈ Ioo 0 Real.pi)
    (hM : 0 < M) (h : 2 * M < r₀) :
    2 * M < (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ 0 : MinkowskiModel 3) 1 ∧
      ∃ t ∈ Iio r₀, (ingoingRay v₀ r₀ θ₀ φ₀ hr₀ hθ t : MinkowskiModel 3) 1 = r₀ - t ∧
        r₀ - t < 2 * M := by
  refine ⟨?_, r₀ - M, ?_, ?_, ?_⟩
  · rw [ingoingRay_val hr₀ hθ hr₀]
    simpa using h
  · change r₀ - M < r₀
    linarith
  · rw [ingoingRay_val hr₀ hθ (by linarith)]
    simp
  · linarith

/-! ### Inside the sphere `r = 2M` -/

/-- **Inside the sphere `r = 2M` every causal vector with `dv > 0` points to decreasing `r`**
(Landau–Lifshitz §102): no particle can be at rest there, and every one moves to the centre. -/
theorem radial_lt_zero_of_causal {x : MinkowskiModel 3} (hx : x ∈ domain) (hr : x 1 < 2 * M)
    {u : MinkowskiModel 3} (hu : form M x u u ≤ 0) (hu₀ : 0 < u 0) : u 1 < 0 := by
  have h0 : 0 < x 1 := hx.1
  rw [form_apply] at hu
  have hf : 1 < 2 * M / x 1 := (one_lt_div h0).mpr hr
  have hpos : 0 < -(1 - 2 * M / x 1) * (u 0 * u 0) := mul_pos (by linarith) (mul_pos hu₀ hu₀)
  have hq2 : 0 ≤ x 1 ^ 2 * (u 2 * u 2) := mul_nonneg (sq_nonneg _) (mul_self_nonneg _)
  have hq3 : 0 ≤ x 1 ^ 2 * Real.sin (x 2) ^ 2 * (u 3 * u 3) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (mul_self_nonneg _)
  by_contra hle
  have h1 : 0 ≤ u 1 := le_of_not_gt hle
  have h01 : 0 ≤ u 0 * u 1 := mul_nonneg hu₀.le h1
  have h10 : 0 ≤ u 1 * u 0 := mul_nonneg h1 hu₀.le
  linarith

/- The hypotheses of `radial_lt_zero_of_causal` hold: for `M = 1` the point
`(0, 1, π/2, 0)` lies inside the sphere `r = 2`, and there the vector `(1, −1, 0, 0)` is
timelike, `g(u, u) = −1`, with `dv > 0`. -/
example : (![0, 1, Real.pi / 2, 0] : MinkowskiModel 3) ∈ domain ∧
    (![0, 1, Real.pi / 2, 0] : MinkowskiModel 3) 1 < 2 * 1 ∧
    form 1 ![0, 1, Real.pi / 2, 0] ![1, -1, 0, 0] ![1, -1, 0, 0] = -1 ∧
    (0 : ℝ) < (![1, -1, 0, 0] : MinkowskiModel 3) 0 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · change (0 : ℝ) < 1
    norm_num
  · change 0 < Real.pi / 2
    positivity
  · change Real.pi / 2 < Real.pi
    linarith [Real.pi_pos]
  · change (1 : ℝ) < 2 * 1
    norm_num
  · rw [form_apply]
    simp
    norm_num
  · change (0 : ℝ) < 1
    norm_num

/-! ### The exterior Schwarzschild metric as a pullback -/

/-- The map `(t, r, θ, φ) ↦ (t + r + 2M log(r/2M − 1), r, θ, φ)` from the exterior
Schwarzschild co-ordinates to the Eddington–Finkelstein co-ordinates: `v = t + r*`, with the
tortoise co-ordinate `r* = r + 2M log(r/2M − 1)`. -/
def toEddington (M : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 :=
  ![x 0 + x 1 + 2 * M * Real.log (x 1 / (2 * M) - 1), x 1, x 2, x 3]

/-- The linear map `(v₀, v₁, v₂, v₃) ↦ (v₀ + v₁/(1 − 2M/r), v₁, v₂, v₃)`. -/
def toEddingtonLinear (M : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 →ₗ[ℝ] MinkowskiModel 3 where
  toFun v := ![v 0 + v 1 / (1 - 2 * M / x 1), v 1, v 2, v 3]
  map_add' v w := by
    funext i
    fin_cases i <;> simp
    ring
  map_smul' c v := by
    funext i
    fin_cases i <;> simp
    ring

/-- The Jacobian `(v₀, v₁, v₂, v₃) ↦ (v₀ + v₁/(1 − 2M/r), v₁, v₂, v₃)` of `toEddington`. -/
def toEddingtonDeriv (M : ℝ) (x : MinkowskiModel 3) : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 :=
  LinearMap.toContinuousLinearMap (toEddingtonLinear M x)

/-- The value of the Jacobian of `toEddington`. -/
theorem toEddingtonDeriv_apply (x v : MinkowskiModel 3) :
    toEddingtonDeriv M x v = ![v 0 + v 1 / (1 - 2 * M / x 1), v 1, v 2, v 3] := rfl

/-- The map `toEddington` sends the exterior domain into the Eddington–Finkelstein domain. -/
theorem toEddington_mem (hM : 0 ≤ M) {x : MinkowskiModel 3}
    (hx : x ∈ SchwarzschildExterior.domain M) : toEddington M x ∈ domain :=
  ⟨by have := hx.1; change 0 < x 1; linarith, hx.2.1, hx.2.2⟩

/-- The derivative of `toEddington` at a point of the exterior is `toEddingtonDeriv`. -/
theorem hasFDerivAt_toEddington (hM : 0 < M) {x : MinkowskiModel 3} (hx : 2 * M < x 1) :
    HasFDerivAt (toEddington M) (toEddingtonDeriv M x) x := by
  have h0 : x 1 ≠ 0 := by linarith
  have h2 : x 1 - 2 * M ≠ 0 := by linarith
  have hM' : M ≠ 0 := hM.ne'
  have hl : x 1 / (2 * M) - 1 ≠ 0 := by
    rw [div_sub_one (by positivity)]
    exact div_ne_zero h2 (by positivity)
  refine hasFDerivAt_pi'' fun i => ?_
  fin_cases i
  · have dL : HasDerivAt (fun r => Real.log (r / (2 * M) - 1)) (1 / (2 * M) / (x 1 / (2 * M) - 1))
        (x 1) := by
      have h := (((hasDerivAt_id' (x 1)).div_const (2 * M)).sub_const 1).log hl
      simpa using h
    refine (((hasFDerivAt_apply 0 x).add (hasFDerivAt_apply 1 x)).add
      ((hasFDerivAt_radial dL).const_mul (2 * M))).congr_fderiv ?_
    ext w
    simp [toEddingtonDeriv_apply]
    field_simp
    ring
  · refine (hasFDerivAt_apply 1 x).congr_fderiv ?_
    ext w
    simp [toEddingtonDeriv_apply]
  · refine (hasFDerivAt_apply 2 x).congr_fderiv ?_
    ext w
    simp [toEddingtonDeriv_apply]
  · refine (hasFDerivAt_apply 3 x).congr_fderiv ?_
    ext w
    simp [toEddingtonDeriv_apply]

/-- **The exterior Schwarzschild metric is the pullback of the Eddington–Finkelstein metric**
by `toEddington`: `g_EF(J v, J w) = g_S(v, w)` at every point with `r > 2M`, where `J` is the
Jacobian `toEddingtonDeriv` (Landau–Lifshitz §102). -/
theorem form_toEddington {x : MinkowskiModel 3} (h0 : 0 < x 1) (hx : 2 * M < x 1)
    (v w : MinkowskiModel 3) :
    form M (toEddington M x) (toEddingtonDeriv M x v) (toEddingtonDeriv M x w) =
      SchwarzschildExterior.form M x v w := by
  have h1 : x 1 ≠ 0 := h0.ne'
  have h2 : x 1 - 2 * M ≠ 0 := by linarith
  rw [form_apply, SchwarzschildExterior.form_apply, toEddingtonDeriv_apply, toEddingtonDeriv_apply]
  simp [toEddington]
  field_simp
  ring

end ProjectAinos.GeneralRelativity.EddingtonFinkelstein
