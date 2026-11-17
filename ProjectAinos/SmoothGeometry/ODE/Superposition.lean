/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.ODE.ContinuousFamily

/-!
# The superposition operator on continuous functions

For a compact space `K` and a continuous map `X : E → F`, the superposition
operator `γ ↦ X ∘ γ` maps `C(K, E)` to `C(K, F)`. If `X` is `n` times
continuously differentiable, so is the superposition operator for the
supremum norms. Its derivative at `γ` applies `DX(γ(t))` at every point `t`.

`ContinuousFamily.slices_contDiff` treats a fixed inner function and a
parameter. Here the function itself is the variable, and the pointwise
derivative `t ↦ DX(γ(t)) ∘ eval_t` is not continuous in `t` for the operator
norm, so the derivative is estimated directly by the mean value inequality.
-/

@[expose] public section
noncomputable section

open Set Filter Metric ContinuousLinearMap Asymptotics
open scoped Topology ContDiff

universe u

namespace ProjectAinos.SmoothGeometry.Superposition

variable {K : Type*} {E F : Type u} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Composition of a continuous function on `K` with a continuous map. -/
def comp (X : E → F) (hX : Continuous X) (γ : C(K, E)) : C(K, F) :=
  ⟨fun t => X (γ t), hX.comp γ.continuous⟩

omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
@[simp] theorem comp_apply (X : E → F) (hX : Continuous X) (γ : C(K, E)) (t : K) :
    comp X hX γ t = X (γ t) := rfl

omit [CompactSpace K] [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem comp_continuous (X : E → F) (hX : Continuous X) :
    Continuous (comp (K := K) X hX) :=
  ContinuousMap.continuous_postcomp (⟨X, hX⟩ : C(E, F))

/-- Apply a continuous family of operators to a continuous family of vectors. -/
def pointwiseApply (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) : C(K, F) :=
  ⟨fun t => A t (γ t), A.continuous.clm_apply γ.continuous⟩

theorem pointwiseApply_norm_le (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) :
    ‖pointwiseApply A γ‖ ≤ ‖A‖ * ‖γ‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg γ))).mpr
  intro t
  exact ((A t).le_opNorm (γ t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (γ.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _))

/-- Pointwise application of a continuous family of operators, as an operator
on continuous functions. -/
def pointwiseCLM (A : C(K, E →L[ℝ] F)) : C(K, E) →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := pointwiseApply A
      map_add' := by intro u v; ext t; exact (A t).map_add (u t) (v t)
      map_smul' := by intro a v; ext t; exact (A t).map_smul a (v t) }
    ‖A‖ (pointwiseApply_norm_le A)

@[simp] theorem pointwiseCLM_apply (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) (t : K) :
    pointwiseCLM A γ t = A t (γ t) := rfl

theorem pointwiseCLM_norm_le (A : C(K, E →L[ℝ] F)) : ‖pointwiseCLM A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- Pointwise application is bounded and linear in the family of operators. -/
def pointwise : C(K, E →L[ℝ] F) →L[ℝ] (C(K, E) →L[ℝ] C(K, F)) := by
  let L : C(K, E →L[ℝ] F) →ₗ[ℝ] (C(K, E) →L[ℝ] C(K, F)) :=
    { toFun := pointwiseCLM
      map_add' := by intro A B; ext v t; rfl
      map_smul' := by intro a A; ext v t; rfl }
  have hL : ∀ A, ‖L A‖ ≤ 1 * ‖A‖ := by
    intro A
    change ‖pointwiseCLM A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using pointwiseCLM_norm_le A
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K, E →L[ℝ] F)) (F := C(K, E) →L[ℝ] C(K, F)) (σ := RingHom.id ℝ) L 1 hL

@[simp] theorem pointwise_apply (A : C(K, E →L[ℝ] F)) (γ : C(K, E)) (t : K) :
    pointwise A γ t = A t (γ t) := rfl

/-- The derivative of the superposition operator at `γ` applies `DX(γ(t))` at
every point. -/
theorem hasFDerivAt_comp {X : E → F} (hX : ContDiff ℝ 1 X) (γ : C(K, E)) :
    HasFDerivAt (comp (K := K) X hX.continuous)
      (pointwise (comp (fderiv ℝ X) (hX.continuous_fderiv one_ne_zero) γ)) γ := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  have hcont := (comp_continuous (K := K) (fderiv ℝ X)
    (hX.continuous_fderiv one_ne_zero)).continuousAt (x := γ)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hcont (ball_mem_nhds _ hc))
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨r, hr, fun η hη => ?_⟩
  apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg _))).mpr
  intro t
  change ‖X (η t) - X (γ t) - fderiv ℝ X (γ t) (η t - γ t)‖ ≤ c * ‖η - γ‖
  have hseg : ∀ y ∈ segment ℝ (γ t) (η t), ‖fderiv ℝ X y - fderiv ℝ X (γ t)‖ ≤ c := by
    rintro y ⟨a, b, ha, hb, hab, rfl⟩
    have hmem : a • γ + b • η ∈ ball γ r := by
      rw [mem_ball, dist_eq_norm] at hη ⊢
      have hd : a • γ + b • η - γ = b • (η - γ) := by
        have ha' : a = 1 - b := by linarith
        subst ha'
        module
      rw [hd, norm_smul, Real.norm_of_nonneg hb]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (by linarith)) hη
    have h := hball hmem
    rw [mem_preimage, mem_ball, dist_eq_norm] at h
    exact (ContinuousMap.norm_coe_le_norm _ t).trans h.le
  have h := (convex_segment (γ t) (η t)).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := X) (f' := fderiv ℝ X) (φ := fderiv ℝ X (γ t))
    (fun y _ => ((hX.differentiable one_ne_zero) y).hasFDerivAt.hasFDerivWithinAt) hseg
    (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  exact h.trans (mul_le_mul_of_nonneg_left ((η - γ).norm_coe_le_norm t) hc.le)

/-- The superposition operator of a map of class `Cⁿ` is of class `Cⁿ`. -/
theorem comp_contDiff_nat (n : ℕ) {X : E → F} (hX : ContDiff ℝ n X) :
    ContDiff ℝ n (comp (K := K) X hX.continuous) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (comp_continuous X hX.continuous)
  | succ n ih =>
    have hD : ContDiff ℝ n (fderiv ℝ X) := hX.fderiv_right (by simp)
    have hp := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : ℕ∞ω))
      (E := C(K, E →L[ℝ] F)) (F := C(K, E) →L[ℝ] C(K, F)) (pointwise (K := K) (E := E) (F := F))
    apply contDiff_succ_iff_hasFDerivAt.mpr
    exact ⟨fun γ => pointwise (comp (fderiv ℝ X) hD.continuous γ), hp.comp (ih hD),
      fun γ => hasFDerivAt_comp (hX.of_le (by simp)) γ⟩

/-- The superposition operator of a smooth map is smooth. -/
theorem comp_contDiff {X : E → F} (hX : ContDiff ℝ ∞ X) :
    ContDiff ℝ ∞ (comp (K := K) X hX.continuous) := by
  apply contDiff_infty.mpr
  intro n
  exact comp_contDiff_nat n (hX.of_le (by simp))

end ProjectAinos.SmoothGeometry.Superposition
