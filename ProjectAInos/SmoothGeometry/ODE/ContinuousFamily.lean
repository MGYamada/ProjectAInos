/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Differentiating compact continuous families

A continuous family of pointwise derivatives gives the derivative of a map
into a supremum-norm space of continuous functions. Compactness makes the
mean-value estimates uniform in the family index. This is used to lift
smooth coordinate coefficients to the coefficient curves of a linear ODE.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set Filter Metric ContinuousLinearMap Asymptotics
open scoped Topology ContDiff

namespace ProjectAInos.SmoothGeometry.ContinuousFamily

variable {K P F : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Apply every map in a continuous family to the same vector. -/
def applyFamily (A : C(K, P →L[ℝ] F)) (v : P) : C(K, F) :=
  ⟨fun t => A t v, A.continuous.clm_apply continuous_const⟩

theorem applyFamily_norm_le (A : C(K, P →L[ℝ] F)) (v : P) :
    ‖applyFamily A v‖ ≤ ‖A‖ * ‖v‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))).mpr
  intro t
  exact ((A t).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm t) (norm_nonneg v))

/-- A family of pointwise derivatives, as a derivative into continuous functions. -/
def derivativeMap (A : C(K, P →L[ℝ] F)) : P →L[ℝ] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := applyFamily A
      map_add' := by intro u v; ext t; exact (A t).map_add u v
      map_smul' := by intro a v; ext t; exact (A t).map_smul a v }
    ‖A‖ (applyFamily_norm_le A)

@[simp] theorem derivativeMap_apply (A : C(K, P →L[ℝ] F)) (v : P) (t : K) :
    derivativeMap A v t = A t v := rfl

theorem derivativeMap_norm_le (A : C(K, P →L[ℝ] F)) : ‖derivativeMap A‖ ≤ ‖A‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg A) _

/-- Assembling pointwise derivatives is itself bounded and linear. -/
def assemble : C(K, P →L[ℝ] F) →L[ℝ] (P →L[ℝ] C(K, F)) := by
  let L : C(K, P →L[ℝ] F) →ₗ[ℝ] (P →L[ℝ] C(K, F)) :=
    { toFun := derivativeMap
      map_add' := by intro A B; ext v t; rfl
      map_smul' := by intro a A; ext v t; rfl }
  have hL : ∀ A, ‖L A‖ ≤ 1 * ‖A‖ := by
    intro A
    change ‖derivativeMap A‖ ≤ 1 * ‖A‖
    simpa only [one_mul] using derivativeMap_norm_le A
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(K, P →L[ℝ] F)) (F := P →L[ℝ] C(K, F)) (σ := RingHom.id ℝ) L 1 hL

/-- Continuous pointwise derivatives imply strict differentiability into the
space of continuous functions, with uniform control over the compact index. -/
theorem hasStrictFDerivAt {f : P → C(K, F)} {A : P → C(K, P →L[ℝ] F)} {p : P}
    (hder : ∀ᶠ q in 𝓝 p, ∀ t, HasFDerivAt (fun x => f x t) (A q t) q)
    (hcont : ContinuousAt A p) :
    HasStrictFDerivAt f (derivativeMap (A p)) p := by
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro c hc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hder (hcont (ball_mem_nhds (A p) hc)))
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨r, hr, ?_⟩
  rintro ⟨a, b⟩ hab
  rw [← ball_prod_same, prodMk_mem_set_prod_eq] at hab
  apply (ContinuousMap.norm_le _ (mul_nonneg hc.le (norm_nonneg _))).mpr
  intro t
  change ‖f a t - f b t - A p t (a - b)‖ ≤ c * ‖a - b‖
  apply (convex_ball p r).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (f := fun x => f x t) (f' := fun x => A x t)
    (fun q hq => (hball hq).1 t |>.hasFDerivWithinAt) ?_ hab.2 hab.1
  intro q hq
  have hb : ‖A q - A p‖ < c := by
    calc
      ‖A q - A p‖ = dist (A q) (A p) := (dist_eq_norm (A q) (A p)).symm
      _ < c := (hball hq).2
  exact ((A q - A p).norm_coe_le_norm t).trans hb.le

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T]

/-- Restrict the second variable of a jointly continuous function to a fixed
continuous map from a compact index space. -/
def slices (f : P × T → F) (hf : Continuous f) (g : C(K, T)) (p : P) : C(K, F) :=
  ⟨fun t => f (p, g t), hf.comp (continuous_const.prodMk g.continuous)⟩

omit [CompactSpace K] [NormedSpace ℝ P] [NormedSpace ℝ F] [NormedSpace ℝ T] in
theorem slices_continuous (f : P × T → F) (hf : Continuous f) (g : C(K, T)) :
    Continuous (slices f hf g) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (hf.comp (continuous_fst.prodMk (g.continuous.comp continuous_snd)))

/-- Joint finite regularity lifts to the supremum-norm space after restricting
the second variable to any fixed compact continuous family. -/
theorem slices_contDiff_nat (n : ℕ) {f : P × T → F} (hf : ContDiff ℝ n f) (g : C(K, T)) :
    ContDiff ℝ n (slices f hf.continuous g) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (slices_continuous f hf.continuous g)
  | succ n ih =>
    let D : P × T → P →L[ℝ] F := fun q =>
      (fderiv ℝ f q).comp (ContinuousLinearMap.inl ℝ P T)
    have hD : ContDiff ℝ n D :=
      (hf.fderiv_right (by simp)).clm_comp contDiff_const
    have hDS := ih hD
    have ha := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := (n : ℕ∞ω))
      (E := C(K, P →L[ℝ] F)) (F := P →L[ℝ] C(K, F)) (assemble (K := K) (P := P) (F := F))
    apply contDiff_succ_iff_hasFDerivAt.mpr
    refine ⟨fun p => derivativeMap (slices D hD.continuous g p), ha.comp hDS, ?_⟩
    intro p
    apply (hasStrictFDerivAt (A := slices D hD.continuous g) ?_
      (slices_continuous D hD.continuous g).continuousAt).hasFDerivAt
    apply Filter.Eventually.of_forall
    intro q t
    exact ((hf.differentiable (by simp) (q, g t)).hasFDerivAt).comp q
      (hasFDerivAt_prodMk_left q (g t))

/-- Joint smoothness lifts to smooth dependence in the supremum norm. -/
theorem slices_contDiff {f : P × T → F} (hf : ContDiff ℝ ∞ f) (g : C(K, T)) :
    ContDiff ℝ ∞ (slices f hf.continuous g) := by
  apply contDiff_infty.mpr
  intro n
  exact slices_contDiff_nat n (hf.of_le (by simp)) g

end ProjectAInos.SmoothGeometry.ContinuousFamily
