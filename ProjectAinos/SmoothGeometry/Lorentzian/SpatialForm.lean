/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Minkowski.Observer
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The spatial form measured by an observer

Let `B` be a bilinear form on the model space `MinkowskiModel d` with a Lorentz frame for the
convention `.timeNegative`, and let `u` be a timelike vector, `B(u, u) < 0`. An observer with
the velocity `u` measures the distance of a displacement `v` by the spatial form
`γ_u(v, w) = B(v, w) − B(u, v) B(u, w) / B(u, u)`, the metric of the parts of `v` and `w`
orthogonal to `u` (`spatialForm_eq`). This is the measurement of Landau–Lifshitz, §84, by light
signals: if a signal leaves the observer at the parameter `τ₁`, reaches the event `v` and returns
at `τ₂`, half the proper time of the round trip is `√(γ_u(v, v))`, and the event of the worldline
at the middle time is simultaneous with `v` (`radar`, `radar_distance`, `exists_radar`). The
statements are about one tangent space: the displacements are infinitesimal.

* `spatialForm_nonneg`, `spatialForm_pos`: `γ_u` is positive semidefinite, and positive on
  every vector that is not a multiple of `u`.
* `pos_of_orthogonal`: a nonzero vector orthogonal to a timelike vector is spacelike.
* For the observer at rest in the co-ordinates, `u = e₀`, the spatial form is
  `γ_{ij} dx^i dx^j` with `γ_{ij} = g_{ij} − g_{0i} g_{0j}/g_{00}`, independent of `dx⁰`
  (`spatialForm_timeAxis`), and `γ` is positive definite where `g₀₀ < 0`
  (`spatialMetric_pos`). Two events are simultaneous for this observer when
  `dx⁰ = −g_{0i} dx^i / g_{00}` (`orthogonal_timeAxis_iff`).
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap

namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

variable (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)

/-- The spatial form `B(v, w) − B(u, v) B(u, w) / B(u, u)` of the observer with the velocity
`u`. -/
def spatialForm (u : MinkowskiModel d) : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  B - (B u u)⁻¹ • (B u).smulRight (B u)

theorem spatialForm_apply (u v w : MinkowskiModel d) :
    spatialForm B u v w = B v w - B u v * B u w / B u u := by
  simp only [spatialForm, sub_apply, smul_apply, smulRight_apply, smul_eq_mul]
  ring

/-- The part `v − (B(u, v)/B(u, u)) u` of `v` orthogonal to `u`. -/
def orthogonalPart (u v : MinkowskiModel d) : MinkowskiModel d := v - (B u v / B u u) • u

variable {B}

theorem orthogonalPart_orthogonal {u : MinkowskiModel d} (hu : B u u ≠ 0)
    (v : MinkowskiModel d) : B u (orthogonalPart B u v) = 0 := by
  rw [orthogonalPart, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hu, sub_self]

/-- The spatial form is the metric of the orthogonal parts. -/
theorem spatialForm_eq (hs : ∀ v w, B v w = B w v) {u : MinkowskiModel d} (hu : B u u ≠ 0)
    (v w : MinkowskiModel d) :
    spatialForm B u v w = B (orthogonalPart B u v) (orthogonalPart B u w) := by
  rw [spatialForm_apply, orthogonalPart, orthogonalPart]
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hs v u]
  field_simp
  ring

theorem spatialForm_self_left {u : MinkowskiModel d} (hu : B u u ≠ 0) (w : MinkowskiModel d) :
    spatialForm B u u w = 0 := by
  rw [spatialForm_apply]
  field_simp
  ring

theorem spatialForm_self_right (hs : ∀ v w, B v w = B w v) {u : MinkowskiModel d}
    (hu : B u u ≠ 0) (v : MinkowskiModel d) : spatialForm B u v u = 0 := by
  rw [spatialForm_apply, hs v u]
  field_simp
  ring

/-- A form with a Lorentz frame is symmetric. -/
theorem symm_of_frame {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) (v w : MinkowskiModel d) :
    B v w = B w v := by
  rw [he, he, minkowskiForm_symmetric]

theorem neg_form_eq_pair {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) (v w : MinkowskiModel d) :
    B v w = -pair (e v) (e w) := by
  rw [he, metric_eq]
  simp [LorentzConvention.timeSign]

/-- A nonzero vector orthogonal to a timelike vector is spacelike. -/
theorem pos_of_orthogonal {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) {u v : MinkowskiModel d}
    (hu : B u u < 0) (hv : B u v = 0) (hv0 : v ≠ 0) : 0 < B v v := by
  rw [neg_form_eq_pair he] at hu hv ⊢
  have h := intervalQuadratic_neg_of_pair_eq_zero (U := e u) (W := e v)
    (by rw [intervalQuadratic_apply]; linarith) (by linarith)
    (fun h => hv0 (e.injective (h.trans e.map_zero.symm)))
  rw [intervalQuadratic_apply] at h
  linarith

/-- The spatial form of a timelike observer is positive semidefinite. -/
theorem spatialForm_nonneg {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) {u : MinkowskiModel d}
    (hu : B u u < 0) (v : MinkowskiModel d) : 0 ≤ spatialForm B u v v := by
  rw [spatialForm_eq (symm_of_frame he) hu.ne]
  by_cases h0 : orthogonalPart B u v = 0
  · simp [h0]
  · exact (pos_of_orthogonal he hu (orthogonalPart_orthogonal hu.ne v) h0).le

/-- The spatial form of a timelike observer is positive on every vector whose orthogonal part is
not zero, that is on every vector that is not a multiple of `u`. -/
theorem spatialForm_pos {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) {u v : MinkowskiModel d}
    (hu : B u u < 0) (hv : orthogonalPart B u v ≠ 0) : 0 < spatialForm B u v v := by
  rw [spatialForm_eq (symm_of_frame he) hu.ne]
  exact pos_of_orthogonal he hu (orthogonalPart_orthogonal hu.ne v) hv

/-! ### Light signals -/

theorem form_sub_smul (hs : ∀ v w, B v w = B w v) (u v : MinkowskiModel d) (τ : ℝ) :
    B (v - τ • u) (v - τ • u) = B v v - 2 * τ * B u v + τ ^ 2 * B u u := by
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hs v u]
  ring

/-- **Radar measurement** (Landau–Lifshitz, §84). A light signal leaves the worldline
`τ ↦ τ u` of an observer at `τ₁`, reaches the event `v` and returns at `τ₂`: the displacements
`v − τ₁ u` and `v − τ₂ u` are null. Then `−B(u, u) ((τ₂ − τ₁)/2)² = γ_u(v, v)`, and the event of
the worldline at the middle parameter is simultaneous with `v`. -/
theorem radar (hs : ∀ v w, B v w = B w v) {u v : MinkowskiModel d} (hu : B u u ≠ 0)
    {τ₁ τ₂ : ℝ} (hne : τ₁ ≠ τ₂) (h₁ : B (v - τ₁ • u) (v - τ₁ • u) = 0)
    (h₂ : B (v - τ₂ • u) (v - τ₂ • u) = 0) :
    -B u u * ((τ₂ - τ₁) / 2) ^ 2 = spatialForm B u v v ∧
      B u (v - ((τ₁ + τ₂) / 2) • u) = 0 := by
  rw [form_sub_smul hs] at h₁ h₂
  have hsum : B u u * (τ₁ + τ₂) = 2 * B u v := by
    have h := sub_eq_zero.mpr (h₁.trans h₂.symm)
    have h' : (τ₁ - τ₂) * (B u u * (τ₁ + τ₂) - 2 * B u v) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hne))
  have hprod : B v v = B u u * τ₁ * τ₂ := by linear_combination h₁ - τ₁ * hsum
  refine ⟨?_, ?_⟩
  · rw [spatialForm_apply, hprod]
    have huv : B u v = B u u * (τ₁ + τ₂) / 2 := by linear_combination -hsum / 2
    rw [huv]
    field_simp
    ring
  · rw [map_sub, map_smul, smul_eq_mul]
    linear_combination -hsum / 2

/-- The radar distance: half the parameter time of the round trip, measured with the rate
`√(−B(u, u))` of the observer's proper time, is `√(γ_u(v, v))`. -/
theorem radar_distance (hs : ∀ v w, B v w = B w v) {u v : MinkowskiModel d} (hu : B u u < 0)
    {τ₁ τ₂ : ℝ} (h12 : τ₁ < τ₂) (h₁ : B (v - τ₁ • u) (v - τ₁ • u) = 0)
    (h₂ : B (v - τ₂ • u) (v - τ₂ • u) = 0) :
    Real.sqrt (-B u u) * (τ₂ - τ₁) / 2 = Real.sqrt (spatialForm B u v v) := by
  rw [← (radar hs hu.ne h12.ne h₁ h₂).1, Real.sqrt_mul (neg_nonneg.mpr hu.le),
    Real.sqrt_sq (by linarith)]
  ring

/-- For a timelike observer and an event that is not on its worldline, the two light signals
exist. -/
theorem exists_radar {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w)) {u v : MinkowskiModel d}
    (hu : B u u < 0) (hv : orthogonalPart B u v ≠ 0) :
    ∃ τ₁ τ₂ : ℝ, τ₁ < τ₂ ∧ B (v - τ₁ • u) (v - τ₁ • u) = 0 ∧
      B (v - τ₂ • u) (v - τ₂ • u) = 0 := by
  have hs := symm_of_frame he
  have ha : B u u ≠ 0 := hu.ne
  have hγ := spatialForm_pos he hu hv
  rw [spatialForm_apply] at hγ
  have hD : 0 < B u v ^ 2 - B u u * B v v := by
    have h : 0 < -B u u * (B v v - B u v * B u v / B u u) := mul_pos (neg_pos.mpr hu) hγ
    have h' : -B u u * (B v v - B u v * B u v / B u u) = B u v ^ 2 - B u u * B v v := by
      field_simp
      ring
    linarith
  have hr : Real.sqrt (B u v ^ 2 - B u u * B v v) * Real.sqrt (B u v ^ 2 - B u u * B v v) =
      B u v ^ 2 - B u u * B v v := Real.mul_self_sqrt hD.le
  have hr0 : 0 < Real.sqrt (B u v ^ 2 - B u u * B v v) := Real.sqrt_pos.mpr hD
  have hnull (r : ℝ) (hr' : r * r = B u v ^ 2 - B u u * B v v) :
      B (v - ((B u v + r) / B u u) • u) (v - ((B u v + r) / B u u) • u) = 0 := by
    rw [form_sub_smul hs]
    have h : B v v - 2 * ((B u v + r) / B u u) * B u v + ((B u v + r) / B u u) ^ 2 * B u u =
        (B u u * B v v - B u v ^ 2 + r * r) / B u u := by
      field_simp
      ring
    rw [h, hr', show B u u * B v v - B u v ^ 2 + (B u v ^ 2 - B u u * B v v) = 0 by ring,
      zero_div]
  refine ⟨(B u v + Real.sqrt (B u v ^ 2 - B u u * B v v)) / B u u,
    (B u v + -Real.sqrt (B u v ^ 2 - B u u * B v v)) / B u u, ?_, hnull _ hr, hnull _ ?_⟩
  · exact (div_lt_div_right_of_neg hu).mpr (by linarith)
  · rw [neg_mul_neg]
    exact hr

/-! ### The observer at rest in the co-ordinates -/

theorem eq_time_add_space (v : MinkowskiModel d) :
    v = v 0 • Pi.single 0 1 + ∑ i : Fin d, v i.succ • Pi.single i.succ 1 := by
  ext μ
  refine Fin.cases ?_ (fun j => ?_) μ
  · simp [(Fin.succ_ne_zero _).symm]
  · simp [Pi.single_apply, Fin.succ_ne_zero, Fin.succ_inj]

variable (B) in
/-- The spatial metric `γ_{ij} = g_{ij} − g_{0i} g_{0j} / g_{00}` of the observer at rest. -/
def spatialMetric (i j : Fin d) : ℝ :=
  B (Pi.single i.succ 1) (Pi.single j.succ 1) -
    B (Pi.single 0 1) (Pi.single i.succ 1) * B (Pi.single 0 1) (Pi.single j.succ 1) /
      B (Pi.single 0 1) (Pi.single 0 1)

theorem spatialMetric_eq (i j : Fin d) :
    spatialMetric B i j =
      spatialForm B (Pi.single 0 1) (Pi.single i.succ 1) (Pi.single j.succ 1) := by
  rw [spatialForm_apply, spatialMetric]

/-- The spatial form of the observer at rest is `γ_{ij} dx^i dx^j`; it does not depend on the
time components. -/
theorem spatialForm_timeAxis (hs : ∀ v w, B v w = B w v)
    (h00 : B (Pi.single 0 1) (Pi.single 0 1) ≠ 0) (v w : MinkowskiModel d) :
    spatialForm B (Pi.single 0 1) v w = ∑ i, ∑ j, spatialMetric B i j * v i.succ * w j.succ := by
  conv_lhs => rw [eq_time_add_space v, eq_time_add_space w]
  simp only [map_add, map_smul, map_sum, add_apply, smul_apply, sum_apply,
    spatialForm_self_left h00, spatialForm_self_right hs h00, smul_eq_mul, mul_zero, zero_add,
    Finset.sum_const_zero, add_zero, Finset.mul_sum, spatialMetric_eq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- The spatial metric of the observer at rest is positive definite where `g_{00} < 0`. -/
theorem spatialMetric_pos {e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d}
    (he : ∀ v w, B v w = minkowskiForm .timeNegative d (e v) (e w))
    (h00 : B (Pi.single 0 1) (Pi.single 0 1) < 0) {ξ : Fin d → ℝ} (hξ : ξ ≠ 0) :
    0 < ∑ i, ∑ j, spatialMetric B i j * ξ i * ξ j := by
  have h := spatialForm_pos he h00 (v := Fin.cons 0 ξ) (fun h => hξ (by
    funext i
    have hi := congrFun h i.succ
    simpa [orthogonalPart, Pi.single_apply, Fin.succ_ne_zero] using hi))
  rw [spatialForm_timeAxis (symm_of_frame he) h00.ne] at h
  simpa using h

/-- Two events are simultaneous for the observer at rest, `B(e₀, dx) = 0`, exactly when
`dx⁰ = −g_{0i} dx^i / g_{00}`. -/
theorem orthogonal_timeAxis_iff (h00 : B (Pi.single 0 1) (Pi.single 0 1) ≠ 0)
    (v : MinkowskiModel d) :
    B (Pi.single 0 1) v = 0 ↔
      v 0 = -(∑ i : Fin d, B (Pi.single 0 1) (Pi.single i.succ 1) * v i.succ) /
        B (Pi.single 0 1) (Pi.single 0 1) := by
  conv_lhs => rw [eq_time_add_space v]
  simp only [map_add, map_smul, map_sum, smul_eq_mul]
  have hc : ∑ i : Fin d, v i.succ * B (Pi.single 0 1) (Pi.single i.succ 1) =
      ∑ i : Fin d, B (Pi.single 0 1) (Pi.single i.succ 1) * v i.succ :=
    Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hc]
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

end ProjectAinos.SmoothGeometry.Minkowski
