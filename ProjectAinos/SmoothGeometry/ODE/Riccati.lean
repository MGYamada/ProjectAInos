/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.FlowVariation
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The matrix Riccati equation `H′ = −H²`

For operators `H(s)` on a Banach space `E`, the equation `H′ = −H²` with `H(0) = H₀` has the
solution `H(s) = H₀ (1 + s H₀)⁻¹` while `1 + s H₀` is invertible. It is the equation of the
second derivative of a solution of the eikonal equation along a ray (Landau–Lifshitz, *The
Classical Theory of Fields*, §56).

* `eqOn_zero_of_hasDerivAt`: uniqueness for a linear equation `w′ = A(t) w` with a bounded
  coefficient on an interval.
* `one_add_smul_mul_eq`: a solution on the interval between `0` and `l` satisfies
  `(1 + l H₀) H(l) = H₀ = H(l) (1 + l H₀)`.
* `isUnit_one_add_smul`: hence `1 + l H₀` is invertible, with inverse `1 − l H(l)`: a solution
  on a closed interval never meets a point where `1 + s H₀` is singular.
* `matrix_eq_of_hasDerivAt`: `H(l) = H₀ (1 + l H₀)⁻¹`.
* `hasDerivAt_solution`: conversely `solution H₀ s = H₀ (1 + s H₀)⁻¹` solves the equation where
  `1 + s H₀` is invertible (`E` complete).

On a finite-dimensional space:

* `hasDerivAt_det_one_add_smul`: Jacobi's formula
  `d/ds det(1 + s H₀) = det(1 + s H₀) tr(H₀ (1 + s H₀)⁻¹)`.
* `hasDerivAt_log_det`: the trace formula `tr H(s) = d/ds log det(1 + s H₀)`.
* `det_pos`: `det(1 + s H₀) > 0` on the interval of a solution.
* `eq_div_sqrt_det`: a solution of the transport equation `α′ = −α tr H / 2` along a solution
  is `α(l) = α(0) / √det(1 + l H₀)`.
* `tendsto_abs_div_sqrt_det`: such an `α` with `α(0) ≠ 0` tends to infinity in absolute value
  at a zero `l₀ > 0` of `det(1 + l H₀)`.

For a family `Φ(t, y)` that is `C²` on an open set of `ℝ × F`, `F` finite-dimensional, such as a
flow (`NonlinearODE.isLocalFlowOn_flow`):

* `NonlinearODE.exists_norm_sub_sub_fderiv_le`: the second-order Taylor bound
  `‖Φ(t, z₀ + w) − Φ(t, z₀) − D_yΦ(t, z₀) w‖ ≤ C ‖w‖²`, uniform on a compact set of times.
-/

@[expose] public section
noncomputable section

open Set Filter ContinuousLinearMap
open scoped Topology NNReal

namespace ProjectAinos.SmoothGeometry.Riccati

open LinearODE

/-! ### Uniqueness for a linear equation with a bounded coefficient -/

section Linear

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Uniqueness for a linear equation `w′ = A(t) w` with a bounded coefficient: a solution on the
interval between `a` and `b` that vanishes at `a` vanishes on the interval. -/
theorem eqOn_zero_of_hasDerivAt {A : ℝ → F →L[ℝ] F} {a b C : ℝ}
    (hA : ∀ t ∈ uIcc a b, ‖A t‖ ≤ C) {w : ℝ → F}
    (hw : ∀ t ∈ uIcc a b, HasDerivAt w (A t (w t)) t) (ha : w a = 0) :
    EqOn w 0 (uIcc a b) := by
  have hlip : ∀ t ∈ uIcc a b, LipschitzOnWith C.toNNReal (fun u => A t u) univ := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun u _ u' _ => ?_
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal']
    calc ‖A t (u - u')‖ ≤ ‖A t‖ * ‖u - u'‖ := (A t).le_opNorm _
      _ ≤ max C 0 * ‖u - u'‖ := by
        gcongr
        exact (hA t ht).trans (le_max_left _ _)
  have hwc : ContinuousOn w (uIcc a b) := fun t ht =>
    (hw t ht).continuousAt.continuousWithinAt
  have h0 : ∀ t : ℝ, HasDerivAt (0 : ℝ → F) (A t ((0 : ℝ → F) t)) t := by
    intro t
    simp
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at hw hwc hlip ⊢
    exact ODE_solution_unique_of_mem_Icc_right (v := fun t u => A t u) (s := fun _ => univ)
      (fun t ht => hlip t (Ico_subset_Icc_self ht)) hwc
      (fun t ht => (hw t (Ico_subset_Icc_self ht)).hasDerivWithinAt) (fun _ _ => mem_univ _)
      continuousOn_const (fun t _ => (h0 t).hasDerivWithinAt) (fun _ _ => mem_univ _) ha
  · rw [uIcc_of_ge hab] at hw hwc hlip ⊢
    exact ODE_solution_unique_of_mem_Icc_left (v := fun t u => A t u) (s := fun _ => univ)
      (fun t ht => hlip t (Ioc_subset_Icc_self ht)) hwc
      (fun t ht => (hw t (Ioc_subset_Icc_self ht)).hasDerivWithinAt) (fun _ _ => mem_univ _)
      continuousOn_const (fun t _ => (h0 t).hasDerivWithinAt) (fun _ _ => mem_univ _) ha

end Linear

/-! ### The Riccati equation -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit solution `H₀ (1 + s H₀)⁻¹` of `H′ = −H²` with `H(0) = H₀`. Where `1 + s H₀` is
not invertible, `Ring.inverse` is zero. -/
def solution (H₀ : E →L[ℝ] E) (s : ℝ) : E →L[ℝ] E := H₀ * Ring.inverse (1 + s • H₀)

theorem solution_zero (H₀ : E →L[ℝ] E) : solution H₀ 0 = H₀ := by
  simp [solution]

/-- A solution of `H′ = −H²` on the interval between `0` and `l` with `H(0) = H₀` satisfies
`(1 + l H₀) H(l) = H₀` and `H(l) (1 + l H₀) = H₀`. The differences solve the linear equations
`D′ = −D H` and `D′ = −H D` and vanish at `0`. -/
theorem one_add_smul_mul_eq {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    (1 + l • H₀) * H l = H₀ ∧ H l * (1 + l • H₀) = H₀ := by
  have hc : ContinuousOn H (uIcc 0 l) := fun s hs => (hH s hs).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hc
  have hA : ∀ s : ℝ, HasDerivAt (fun r : ℝ => (1 : E →L[ℝ] E) + r • H₀) H₀ s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const H₀).const_add (1 : E →L[ℝ] E)
  have hmem : l ∈ uIcc 0 l := right_mem_uIcc
  constructor
  · -- `D(s) = (1 + s H₀) H(s) − H₀` solves `D′ = −D H(s)`
    have hB : ∀ s ∈ uIcc 0 l,
        ‖-(ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).flip (H s)‖ ≤ C := by
      intro s hs
      rw [norm_neg]
      refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans (hC s hs))
        fun D => ?_
      rw [flip_apply, mul_apply']
      calc ‖D * H s‖ ≤ ‖D‖ * ‖H s‖ := norm_mul_le _ _
        _ ≤ C * ‖D‖ := by rw [mul_comm]; gcongr; exact hC s hs
    have hD := eqOn_zero_of_hasDerivAt (w := fun s => (1 + s • H₀) * H s - H₀) hB
      (fun s hs => by
        have h := ((hA s).mul (hH s hs)).sub_const H₀
        refine h.congr_deriv ?_
        simp only [neg_apply, flip_apply, mul_apply', add_mul, sub_mul, one_mul, mul_neg,
          smul_mul_assoc, mul_assoc]
        abel)
      (by simp [h0])
    have := hD hmem
    simpa [sub_eq_zero] using this
  · -- `D(s) = H(s) (1 + s H₀) − H₀` solves `D′ = −H(s) D`
    have hB : ∀ s ∈ uIcc 0 l, ‖-(ContinuousLinearMap.mul ℝ (E →L[ℝ] E)) (H s)‖ ≤ C := by
      intro s hs
      rw [norm_neg]
      exact (opNorm_mul_apply_le ℝ (E →L[ℝ] E) (H s)).trans (hC s hs)
    have hD := eqOn_zero_of_hasDerivAt (w := fun s => H s * (1 + s • H₀) - H₀) hB
      (fun s hs => by
        have h := ((hH s hs).mul (hA s)).sub_const H₀
        refine h.congr_deriv ?_
        simp only [neg_apply, mul_apply', mul_sub, mul_add, mul_one, neg_mul,
          mul_smul_comm, mul_assoc, smul_neg]
        abel)
      (by simp [h0])
    have := hD hmem
    simpa [sub_eq_zero] using this

/-- A solution of `H′ = −H²` on the interval between `0` and `l` with `H(0) = H₀` makes
`1 + l H₀` invertible, with inverse `1 − l H(l)`. -/
theorem isUnit_one_add_smul {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    IsUnit (1 + l • H₀) ∧ Ring.inverse (1 + l • H₀) = 1 - l • H l := by
  obtain ⟨h1, h2⟩ := one_add_smul_mul_eq hH h0
  have hr : (1 + l • H₀) * (1 - l • H l) = 1 := by
    rw [mul_sub, mul_one, mul_smul_comm, h1]
    abel
  have hl : (1 - l • H l) * (1 + l • H₀) = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc, h2]
    abel
  let u : (E →L[ℝ] E)ˣ := ⟨1 + l • H₀, 1 - l • H l, hr, hl⟩
  refine ⟨⟨u, rfl⟩, ?_⟩
  change Ring.inverse (u : E →L[ℝ] E) = _
  rw [Ring.inverse_unit]
  rfl

/-- **The Riccati equation (§56)**: a solution of `H′ = −H²` on the interval between `0` and `l`
with `H(0) = H₀` is `H(l) = H₀ (1 + l H₀)⁻¹`, and `1 + l H₀` is invertible. -/
theorem matrix_eq_of_hasDerivAt {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    H l = H₀ * Ring.inverse (1 + l • H₀) := by
  obtain ⟨h1, -⟩ := one_add_smul_mul_eq hH h0
  rw [(isUnit_one_add_smul hH h0).2, mul_sub, mul_one, mul_smul_comm]
  rw [add_mul, one_mul, smul_mul_assoc] at h1
  exact eq_sub_of_add_eq h1

/-- **Existence (§56)**: where `1 + s H₀` is invertible, `H₀ (1 + s H₀)⁻¹` solves
`H′ = −H²`. -/
theorem hasDerivAt_solution [CompleteSpace E] (H₀ : E →L[ℝ] E) {s : ℝ}
    (hs : IsUnit (1 + s • H₀)) :
    HasDerivAt (solution H₀) (-(solution H₀ s * solution H₀ s)) s := by
  obtain ⟨u, hu⟩ := hs
  have hA : HasDerivAt (fun r : ℝ => (1 : E →L[ℝ] E) + r • H₀) H₀ s := by
    simpa using ((hasDerivAt_id s).smul_const H₀).const_add (1 : E →L[ℝ] E)
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hinv
  have h := (hinv.comp_hasDerivAt s hA).const_mul H₀
  refine h.congr_deriv ?_
  rw [solution, ← hu, Ring.inverse_unit]
  simp only [neg_apply, mulLeftRight_apply]
  noncomm_ring

/-! ### The determinant and the trace -/

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- Jacobi's formula at zero: `d/dr det(1 + r C)` at `r = 0` is `tr C`. -/
theorem hasDerivAt_det_one_add_smul_zero (C : E →L[ℝ] E) :
    HasDerivAt (fun r : ℝ => LinearMap.det ((1 + r • C : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (traceCLM C) 0 := by
  let b := Module.finBasis ℝ E
  let M : ℝ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun r i j => b.repr ((1 + r • C : E →L[ℝ] E) (b j)) i
  have hMeq : ∀ r : ℝ, Matrix.of (M r) =
      LinearMap.toMatrix b b ((1 + r • C : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    intro r
    ext i j
    simp [M, LinearMap.toMatrix_apply]
  have hM0 : Matrix.of (M 0) = 1 := by
    rw [hMeq]
    simp
  have hMd : HasDerivAt M (fun i j => b.repr (C (b j)) i) 0 := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    have hline : HasDerivAt (fun r : ℝ => (1 + r • C : E →L[ℝ] E) (b j)) (C (b j)) 0 := by
      have h := ((hasDerivAt_id (0 : ℝ)).smul_const (C (b j))).const_add (b j)
      simpa using h
    exact (LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hd := hasDerivAt_det_of_eq_one hM0 hMd
  have htrace : Matrix.trace (Matrix.of fun i j => b.repr (C (b j)) i) = traceCLM C := by
    rw [traceCLM_apply, LinearMap.trace_eq_matrix_trace ℝ b]
    congr 1
    ext i j
    simp [LinearMap.toMatrix_apply]
  rw [htrace] at hd
  refine hd.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
  change LinearMap.det _ = Matrix.det (Matrix.of (M r))
  rw [hMeq, LinearMap.det_toMatrix]

/-- A unit of the operators has a nonzero determinant. -/
theorem det_ne_zero_of_isUnit {A : E →L[ℝ] E} (hA : IsUnit A) :
    LinearMap.det (A : E →ₗ[ℝ] E) ≠ 0 :=
  (LinearMap.isUnit_iff_isUnit_det _).mp (hA.map (ContinuousLinearMap.toLinearMapRingHom))
    |>.ne_zero

/-- **Jacobi's formula**: where `1 + s H₀` is invertible,
`d/ds det(1 + s H₀) = det(1 + s H₀) tr(H₀ (1 + s H₀)⁻¹)`. -/
theorem hasDerivAt_det_one_add_smul (H₀ : E →L[ℝ] E) {s : ℝ} (hs : IsUnit (1 + s • H₀)) :
    HasDerivAt (fun r : ℝ => LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (LinearMap.det ((1 + s • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) * traceCLM (solution H₀ s)) s := by
  set A : E →L[ℝ] E := 1 + s • H₀ with hAdef
  set B : E →L[ℝ] E := Ring.inverse A
  have hAB : A * B = 1 := Ring.mul_inverse_cancel A hs
  have hsplit : ∀ r : ℝ, (1 + r • H₀ : E →L[ℝ] E) = A * (1 + (r - s) • (B * H₀)) := by
    intro r
    rw [mul_add, mul_one, mul_smul_comm, ← mul_assoc, hAB, one_mul, hAdef, add_assoc,
      ← add_smul]
    congr 2
    ring
  have hdet : ∀ r : ℝ, LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      LinearMap.det (A : E →ₗ[ℝ] E) *
        LinearMap.det ((1 + (r - s) • (B * H₀) : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
    intro r
    rw [hsplit r, ContinuousLinearMap.mul_def, ContinuousLinearMap.toLinearMap_comp,
      LinearMap.det_comp]
  have h0 := hasDerivAt_det_one_add_smul_zero (B * H₀)
  have h1 : HasDerivAt
      (fun r : ℝ => LinearMap.det ((1 + (r - s) • (B * H₀) : E →L[ℝ] E) : E →ₗ[ℝ] E))
      (traceCLM (B * H₀)) s := by
    have h0' : HasDerivAt
        (fun r : ℝ => LinearMap.det ((1 + r • (B * H₀) : E →L[ℝ] E) : E →ₗ[ℝ] E))
        (traceCLM (B * H₀)) (s - s) := by
      rw [sub_self]
      exact h0
    exact h0'.comp_sub_const s s
  have h2 := h1.const_mul (LinearMap.det (A : E →ₗ[ℝ] E))
  have htr : traceCLM (B * H₀) = traceCLM (solution H₀ s) := by
    rw [solution, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, traceCLM_comp_comm]
  rw [htr] at h2
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
  exact hdet r

/-- The trace formula where `1 + s H₀` is invertible:
`d/ds log det(1 + s H₀) = tr(H₀ (1 + s H₀)⁻¹)`. -/
theorem hasDerivAt_log_det_solution (H₀ : E →L[ℝ] E) {s : ℝ} (hs : IsUnit (1 + s • H₀)) :
    HasDerivAt (fun r : ℝ => Real.log (LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)))
      (traceCLM (solution H₀ s)) s := by
  have hne := det_ne_zero_of_isUnit hs
  have h := (hasDerivAt_det_one_add_smul H₀ hs).log hne
  refine h.congr_deriv ?_
  field_simp

/-- **The trace formula (§56)**: along a solution of `H′ = −H²` on the interval between `0` and
`l` with `H(0) = H₀`, `tr H(l) = d/dl log det(1 + l H₀)`. -/
theorem hasDerivAt_log_det {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    HasDerivAt (fun r : ℝ => Real.log (LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)))
      (traceCLM (H l)) l := by
  have h := hasDerivAt_log_det_solution H₀ (isUnit_one_add_smul hH h0).1
  rwa [solution, ← matrix_eq_of_hasDerivAt hH h0] at h

omit [FiniteDimensional ℝ E] in
theorem continuous_det_one_add_smul (H₀ : E →L[ℝ] E) :
    Continuous fun r : ℝ => LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) :=
  (ContinuousLinearMap.continuous_det (E := E)).comp (continuous_const.add
    (continuous_id.smul continuous_const))

/-- Along a solution of `H′ = −H²` on the interval between `0` and `l` with `H(0) = H₀`, the
determinant `det(1 + s H₀)` is positive: it does not vanish and is `1` at `0`. -/
theorem det_pos {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) :
    ∀ s ∈ uIcc 0 l, 0 < LinearMap.det ((1 + s • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  intro s hs
  have hne : ∀ r ∈ uIcc 0 l,
      LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) ≠ 0 := by
    intro r hr
    have hsub : uIcc 0 r ⊆ uIcc 0 l := uIcc_subset_uIcc left_mem_uIcc hr
    exact det_ne_zero_of_isUnit (isUnit_one_add_smul (fun t ht => hH t (hsub ht)) h0).1
  by_contra hle
  rw [not_lt] at hle
  have hivt := isPreconnected_uIcc.intermediate_value hs (left_mem_uIcc (b := l))
    (continuous_det_one_add_smul H₀).continuousOn
  have h1 : LinearMap.det ((1 + (0 : ℝ) • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 := by simp
  rw [h1] at hivt
  obtain ⟨r, hr, hr0⟩ := hivt ⟨hle, zero_le_one⟩
  exact hne r hr hr0

/-- **The transport along a solution (§56)**: if `α′ = −α tr H / 2` on the interval between `0`
and `l`, along a solution of `H′ = −H²` with `H(0) = H₀`, then
`α(l) = α(0) / √det(1 + l H₀)`. -/
theorem eq_div_sqrt_det {H : ℝ → E →L[ℝ] E} {H₀ : E →L[ℝ] E} {l : ℝ}
    (hH : ∀ s ∈ uIcc 0 l, HasDerivAt H (-(H s * H s)) s) (h0 : H 0 = H₀) {α : ℝ → ℝ}
    (hα : ∀ s ∈ uIcc 0 l, HasDerivAt α (-(α s * traceCLM (H s)) / 2) s) :
    α l = α 0 / Real.sqrt (LinearMap.det ((1 + l • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)) := by
  set δ : ℝ → ℝ := fun r => LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) with hδ
  have hpos := det_pos hH h0
  have hφ : ∀ s ∈ uIcc 0 l, HasDerivAt (fun r => α r * Real.sqrt (δ r)) 0 s := by
    intro s hs
    have hsub : uIcc 0 s ⊆ uIcc 0 l := uIcc_subset_uIcc left_mem_uIcc hs
    have hHs : ∀ t ∈ uIcc 0 s, HasDerivAt H (-(H t * H t)) t := fun t ht => hH t (hsub ht)
    have hu := (isUnit_one_add_smul hHs h0).1
    have hd := hasDerivAt_det_one_add_smul H₀ hu
    rw [solution, ← matrix_eq_of_hasDerivAt hHs h0] at hd
    have hδs : 0 < δ s := hpos s hs
    have h := (hα s hs).mul (hd.sqrt hδs.ne')
    refine h.congr_deriv ?_
    have hsq : Real.sqrt (δ s) ^ 2 = δ s := Real.sq_sqrt hδs.le
    have hsqpos : 0 < Real.sqrt (δ s) := Real.sqrt_pos.mpr hδs
    have key : δ s / Real.sqrt (δ s) = Real.sqrt (δ s) := by
      rw [div_eq_iff hsqpos.ne', ← sq, hsq]
    change -(α s * traceCLM (H s)) / 2 * Real.sqrt (δ s) +
      α s * (δ s * traceCLM (H s) / (2 * Real.sqrt (δ s))) = 0
    calc -(α s * traceCLM (H s)) / 2 * Real.sqrt (δ s) +
          α s * (δ s * traceCLM (H s) / (2 * Real.sqrt (δ s)))
        = -(α s * traceCLM (H s)) / 2 * Real.sqrt (δ s) +
          α s * traceCLM (H s) / 2 * (δ s / Real.sqrt (δ s)) := by ring
      _ = 0 := by rw [key]; ring
  have hconst := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun r => α r * Real.sqrt (δ r)) (C := 0)
    (fun s hs => (hφ s hs).hasDerivWithinAt) (fun _ _ => by simp) (convex_uIcc 0 l)
    left_mem_uIcc right_mem_uIcc
  rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hconst
  have hδ0 : δ 0 = 1 := by simp [hδ]
  simp only [hδ0, Real.sqrt_one, mul_one] at hconst
  have hl : 0 < Real.sqrt (δ l) := Real.sqrt_pos.mpr (hpos l right_mem_uIcc)
  rw [← hconst]
  change α l = α l * Real.sqrt (δ l) / Real.sqrt (δ l)
  rw [mul_div_assoc, div_self hl.ne', mul_one]

omit [FiniteDimensional ℝ E] in
/-- **The blow-up at a focal point (§56)**: if `α(s) = α(0) / √det(1 + s H₀)` on `[0, l₀)` with
`α(0) ≠ 0`, `det(1 + s H₀) > 0` there and `det(1 + l₀ H₀) = 0`, then `|α(s)| → ∞` as
`s → l₀⁻`. -/
theorem tendsto_abs_div_sqrt_det {H₀ : E →L[ℝ] E} {l₀ : ℝ} (hl₀ : 0 < l₀) {α : ℝ → ℝ}
    (hα : ∀ s ∈ Ico 0 l₀,
      α s = α 0 / Real.sqrt (LinearMap.det ((1 + s • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)))
    (hpos : ∀ s ∈ Ico 0 l₀, 0 < LinearMap.det ((1 + s • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E))
    (hdet : LinearMap.det ((1 + l₀ • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) = 0) (h0 : α 0 ≠ 0) :
    Tendsto (fun s => |α s|) (𝓝[<] l₀) atTop := by
  set δ : ℝ → ℝ := fun r => LinearMap.det ((1 + r • H₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) with hδ
  have hev : ∀ᶠ s in 𝓝[<] l₀, s ∈ Ico 0 l₀ := Ico_mem_nhdsLT hl₀
  have hsq : Tendsto (fun s => Real.sqrt (δ s)) (𝓝[<] l₀) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Tendsto (fun s => Real.sqrt (δ s)) (𝓝 l₀) (𝓝 (Real.sqrt (δ l₀))) :=
        ((continuous_det_one_add_smul H₀).sqrt).tendsto l₀
      have hδl : Real.sqrt (δ l₀) = 0 := by
        change Real.sqrt (LinearMap.det _) = 0
        rw [hdet, Real.sqrt_zero]
      rw [hδl] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [hev] with s hs
      exact Real.sqrt_pos.mpr (hpos s hs)
  have hinv := (tendsto_inv_nhdsGT_zero.comp hsq).const_mul_atTop (abs_pos.mpr h0)
  refine hinv.congr' ?_
  filter_upwards [hev] with s hs
  rw [hα s hs, abs_div, abs_of_pos (Real.sqrt_pos.mpr (hpos s hs))]
  rfl

end FiniteDimensional

end ProjectAinos.SmoothGeometry.Riccati

/-! ### A narrow beam of a smooth family: the second-order Taylor bound -/

namespace ProjectAinos.SmoothGeometry.NonlinearODE

/-- A second-order Taylor bound in the initial point, uniform on a compact set of times: if
`Φ(t, y)` is `C²` on an open set `Ω` of `ℝ × F`, `F` finite-dimensional, that contains `K × {z₀}`
with `K` compact, then `‖Φ(t, z₀ + w) − Φ(t, z₀) − D_yΦ(t, z₀) w‖ ≤ C ‖w‖²` for `t ∈ K` and
`‖w‖ ≤ δ`, for some `δ > 0` and `C`. -/
theorem exists_norm_sub_sub_fderiv_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {Φ : ℝ × F → F} {Ω : Set (ℝ × F)} (hΩ : IsOpen Ω)
    (hΦ : ∀ p ∈ Ω, ContDiffAt ℝ 2 Φ p) {K : Set ℝ} (hK : IsCompact K) {z₀ : F}
    (hKz : ∀ t ∈ K, (t, z₀) ∈ Ω) :
    ∃ δ > 0, ∃ C : ℝ, ∀ t ∈ K, ∀ w : F, ‖w‖ ≤ δ →
      ‖Φ (t, z₀ + w) - Φ (t, z₀) - fderiv ℝ (fun y => Φ (t, y)) z₀ w‖ ≤ C * ‖w‖ ^ 2 := by
  have hS : IsCompact (K ×ˢ ({z₀} : Set F)) := hK.prod isCompact_singleton
  have hSΩ : K ×ˢ ({z₀} : Set F) ⊆ Ω := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    obtain rfl : y = z₀ := hy
    exact hKz t ht
  obtain ⟨δ, hδ, hδΩ⟩ := hS.exists_cthickening_subset_open hΩ hSΩ
  have hT : ∀ t ∈ K, ∀ y ∈ Metric.closedBall z₀ δ, (t, y) ∈ Ω := by
    intro t ht y hy
    apply hδΩ
    refine Metric.mem_cthickening_of_dist_le (t, y) (t, z₀) δ _ ⟨ht, rfl⟩ ?_
    rw [Prod.dist_eq, dist_self]
    exact max_le hδ.le (Metric.mem_closedBall.mp hy)
  have hTc : IsCompact (K ×ˢ Metric.closedBall z₀ δ) := hK.prod (isCompact_closedBall z₀ δ)
  have hloc : LocallyLipschitzOn (K ×ˢ Metric.closedBall z₀ δ) (fderiv ℝ Φ) := by
    intro p hp
    obtain ⟨L, s, hs, hL⟩ :=
      ((hΦ p (hT p.1 hp.1 p.2 hp.2)).fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
    exact ⟨L, s, mem_nhdsWithin_of_mem_nhds hs, hL⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hTc
  refine ⟨δ, hδ, L, fun t ht w hw => ?_⟩
  have hdiff : ∀ y ∈ Metric.closedBall z₀ δ, HasFDerivAt (fun y => Φ (t, y))
      (fderiv ℝ Φ (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ F) y := fun y hy =>
    hasFDerivAt_slice ((hΦ _ (hT t ht y hy)).differentiableAt (by norm_num))
  have hz₀ : z₀ ∈ Metric.closedBall z₀ δ := Metric.mem_closedBall_self hδ.le
  have hball : Metric.closedBall z₀ ‖w‖ ⊆ Metric.closedBall z₀ δ :=
    Metric.closedBall_subset_closedBall hw
  have hinr : ‖ContinuousLinearMap.inr ℝ ℝ F‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]
  have hbound : ∀ y ∈ Metric.closedBall z₀ ‖w‖,
      ‖fderiv ℝ Φ (t, y) ∘L ContinuousLinearMap.inr ℝ ℝ F -
        fderiv ℝ Φ (t, z₀) ∘L ContinuousLinearMap.inr ℝ ℝ F‖ ≤ L * ‖w‖ := by
    intro y hy
    rw [← ContinuousLinearMap.sub_comp]
    have h1 : ‖fderiv ℝ Φ (t, y) - fderiv ℝ Φ (t, z₀)‖ ≤ L * ‖w‖ := by
      rw [← dist_eq_norm]
      calc dist (fderiv ℝ Φ (t, y)) (fderiv ℝ Φ (t, z₀)) ≤ L * dist (t, y) (t, z₀) :=
            hL.dist_le_mul _ ⟨ht, hball hy⟩ _ ⟨ht, hz₀⟩
        _ ≤ L * ‖w‖ := by
          gcongr
          rw [Prod.dist_eq, dist_self]
          exact max_le (norm_nonneg _) (Metric.mem_closedBall.mp hy)
    calc ‖(fderiv ℝ Φ (t, y) - fderiv ℝ Φ (t, z₀)) ∘L ContinuousLinearMap.inr ℝ ℝ F‖
        ≤ ‖fderiv ℝ Φ (t, y) - fderiv ℝ Φ (t, z₀)‖ * ‖ContinuousLinearMap.inr ℝ ℝ F‖ :=
          opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ Φ (t, y) - fderiv ℝ Φ (t, z₀)‖ * 1 := by gcongr
      _ ≤ L * ‖w‖ := by rw [mul_one]; exact h1
  have hmv := (convex_closedBall z₀ ‖w‖).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun y => Φ (t, y)) (x := z₀) (y := z₀ + w)
    (fun y hy => (hdiff y (hball hy)).hasFDerivWithinAt) hbound
    (Metric.mem_closedBall_self (norm_nonneg w))
    (by simp [Metric.mem_closedBall, dist_eq_norm])
  rw [(hdiff z₀ hz₀).fderiv]
  simp only [add_sub_cancel_left] at hmv
  calc _ ≤ L * ‖w‖ * ‖w‖ := hmv
    _ = L * ‖w‖ ^ 2 := by ring

end ProjectAinos.SmoothGeometry.NonlinearODE
