/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.Synchronous
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# De Sitter space in the flat slicing

The metric `−dt² + e^{2t} (dx² + dy² + dz²)` on `ℝ⁴` is synchronous (`isSynchronous`), with
`κ^α_β = 2 δ^α_β` (`extrinsicRate_eq`). The formulas of the synchronous system give
`R_{00} = −3`, `R_{0α} = 0` and `R_{αβ} = 3 e^{2t} δ_{αβ}`, that is `Ric = 3 g`
(`ricci_eq`): de Sitter space solves the vacuum Einstein equations with `Λ = 3`.
-/

@[expose] public section

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology

namespace ProjectAinos.GeneralRelativity.DeSitterSlicing

open SmoothGeometry CoordinateMetric LorentzMetric

local notation "E" => MinkowskiModel 3

/-- The coefficients `−1, e^{2t}, e^{2t}, e^{2t}` at the point `q = (t, x, y, z)`. -/
def coefficients (q : E) (i : Fin 4) : ℝ := if i = 0 then -1 else Real.exp (2 * q 0)

/-- The form `−dt² + e^{2t} (dx² + dy² + dz²)`. -/
def form (q : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ i, coefficients q i •
    (ContinuousLinearMap.proj i : E →L[ℝ] ℝ).smulRight (ContinuousLinearMap.proj i : E →L[ℝ] ℝ)

theorem form_apply (q v w : E) : form q v w = ∑ i, coefficients q i * (v i * w i) := by
  simp [form, smul_eq_mul]

theorem contDiff_form : ContDiff ℝ ∞ form := by
  refine contDiff_clm_apply_iff.mpr fun v => contDiff_clm_apply_iff.mpr fun w => ?_
  simp only [form_apply, coefficients, Fin.sum_univ_four]
  simp only [Fin.isValue, ite_true, show (1 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 0 by decide,
    show (3 : Fin 4) ≠ 0 by decide, ite_false]
  fun_prop

theorem scaleFactor_ne_zero (q : E) (i : Fin 4) :
    (if i = 0 then (1 : ℝ) else Real.exp (q 0)) ≠ 0 := by
  split_ifs
  · exact one_ne_zero
  · exact (Real.exp_pos _).ne'

/-- The scaling `(v₀, e^t v₁, e^t v₂, e^t v₃)`. -/
def scaleLinear (q : E) : E ≃ₗ[ℝ] E where
  toFun v i := (if i = 0 then 1 else Real.exp (q 0)) * v i
  invFun v i := v i / (if i = 0 then 1 else Real.exp (q 0))
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, mul_add]
  map_smul' c v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring
  left_inv v := by
    funext i
    have h := scaleFactor_ne_zero q i
    simp only
    field_simp
  right_inv v := by
    funext i
    have h := scaleFactor_ne_zero q i
    simp only
    field_simp

/-- The scaling as a continuous linear equivalence, an orthonormal frame of the form. -/
def scale (q : E) : E ≃L[ℝ] E := (scaleLinear q).toContinuousLinearEquiv

theorem scale_apply (q v : E) (i : Fin 4) :
    scale q v i = (if i = 0 then 1 else Real.exp (q 0)) * v i := by
  rw [scale, LinearEquiv.coe_toContinuousLinearEquiv']
  rfl

/-- **De Sitter space in the flat slicing** on all of `ℝ⁴`. -/
def metric : CoordinateMetric .timeNegative 3 ⊤ where
  form := form
  smooth := contDiff_form.contDiffOn
  signature q _ := by
    refine ⟨scale q, fun v w => ?_⟩
    rw [form_apply, minkowskiForm_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [scale_apply, scale_apply]
    by_cases hi : i = 0
    · simp [coefficients, hi, lorentzSign, LorentzConvention.timeSign]
    · simp only [coefficients, hi, ite_false, lorentzSign, LorentzConvention.timeSign]
      rw [show 2 * q 0 = q 0 + q 0 by ring, Real.exp_add]
      ring

theorem coefficient_eq (z : E) :
    metric.coefficient z = Matrix.diagonal (coefficients z) := by
  ext i j
  simp only [coefficient, Matrix.of_apply, Matrix.diagonal_apply]
  rw [show metric.form z = form z from rfl, form_apply]
  by_cases h : i = j
  · subst h
    simp [Pi.single_apply]
  · simp [Pi.single_apply, h]
    intro hj
    exact absurd hj.symm h

theorem coefficient_inv_eq (z : E) :
    (metric.coefficient z)⁻¹ =
      Matrix.diagonal fun i => if i = 0 then -1 else Real.exp (-(2 * z 0)) := by
  rw [coefficient_eq]
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases hi : i = 0
  · simp [coefficients, hi]
  · simp only [coefficients, hi, ite_false, ← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- De Sitter space is synchronous in these co-ordinates. -/
theorem isSynchronous : metric.IsSynchronous := fun z _ => by
  refine ⟨?_, fun α => ?_⟩
  · simp [coefficient_eq, coefficients]
  · simp [coefficient_eq, (Fin.succ_ne_zero α).symm]

theorem coefficient_succ (w : E) (α β : Fin 3) :
    metric.coefficient w α.succ β.succ = if α = β then Real.exp (2 * w 0) else 0 := by
  simp [coefficient_eq, Matrix.diagonal_apply, coefficients, Fin.succ_ne_zero, Fin.succ_inj]

theorem hasFDerivAt_exp (z : E) :
    HasFDerivAt (fun w : E => Real.exp (2 * w 0))
      (Real.exp (2 * z 0) • (2 : ℝ) • (ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ)) z := by
  have h := ((ContinuousLinearMap.proj 0 : E →L[ℝ] ℝ).hasFDerivAt (x := z)).const_smul (2 : ℝ)
  exact h.exp

/-- `∂_t γ_{αβ} = 2 e^{2t} δ_{αβ}`. -/
theorem metricRate_eq (z : E) (α β : Fin 3) :
    metric.metricRate z α β = if α = β then 2 * Real.exp (2 * z 0) else 0 := by
  unfold metricRate
  have hf : (fun w => metric.coefficient w α.succ β.succ) =
      fun w => if α = β then Real.exp (2 * w 0) else 0 := funext fun w => coefficient_succ w α β
  rw [hf]
  by_cases h : α = β
  · simp only [h, ite_true, (hasFDerivAt_exp z).fderiv, smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply, Pi.single_eq_same]
    ring
  · simp [h]

/-- `κ^α_β = 2 δ^α_β`. -/
theorem extrinsicRate_eq (z : E) (α β : Fin 3) :
    metric.extrinsicRate z α β = if α = β then 2 else 0 := by
  have hm (δ : Fin 3) : fderiv ℝ (fun w => metric.coefficient w β.succ δ.succ) z
      (Pi.single 0 1) = if β = δ then 2 * Real.exp (2 * z 0) else 0 :=
    metricRate_eq z β δ
  have hinv (δ : Fin 3) : (metric.coefficient z)⁻¹ α.succ δ.succ =
      if α = δ then Real.exp (-(2 * z 0)) else 0 := by
    rw [coefficient_inv_eq, Matrix.diagonal_apply]
    simp [Fin.succ_ne_zero, Fin.succ_inj]
  unfold extrinsicRate
  simp only [hm, hinv]
  by_cases h : α = β
  · subst h
    rw [Finset.sum_eq_single α (fun δ _ hδ => by simp [Ne.symm hδ]) (by simp)]
    simp only [ite_true]
    rw [← mul_assoc, mul_comm (Real.exp _) 2, mul_assoc, ← Real.exp_add, neg_add_cancel,
      Real.exp_zero, mul_one]
  · simp only [h, ite_false]
    refine Finset.sum_eq_zero fun δ _ => ?_
    by_cases hδ : α = δ
    · subst hδ
      simp [Ne.symm h]
    · simp [hδ]

/-- The coefficients do not depend on the spatial co-ordinates. -/
theorem fderiv_coefficient_spatial (w : E) (i j : Fin 4) (k : Fin 3) :
    fderiv ℝ (fun v => metric.coefficient v i j) w (Pi.single k.succ 1) = 0 := by
  have hf : (fun v => metric.coefficient v i j) =
      fun v => if i = j then (if i = 0 then -1 else Real.exp (2 * v 0)) else 0 := by
    funext v
    rw [coefficient_eq, Matrix.diagonal_apply]
    rfl
  rw [hf]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, ite_true, ite_false]
      rw [(hasFDerivAt_exp w).fderiv, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
        ContinuousLinearMap.proj_apply, Pi.single_apply]
      simp [(Fin.succ_ne_zero k).symm]
  · simp [hij]

/-- The spatial Christoffel symbols vanish. -/
theorem christoffel_spatial (w : E) (γ α β : Fin 3) :
    christoffelOf metric.coefficient w γ.succ α.succ β.succ = 0 := by
  unfold christoffelOf
  rw [coefficient_inv_eq]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.diagonal_apply]
  by_cases hl : γ.succ = l
  · subst hl
    rw [fderiv_coefficient_spatial, fderiv_coefficient_spatial, fderiv_coefficient_spatial]
    ring
  · simp [hl]

theorem fderiv_extrinsicRate (z : E) (α β : Fin 3) (v : E) :
    fderiv ℝ (fun w => metric.extrinsicRate w α β) z v = 0 := by
  have hf : (fun w => metric.extrinsicRate w α β) = fun _ => if α = β then 2 else 0 :=
    funext fun w => extrinsicRate_eq w α β
  rw [hf, fderiv_const_apply, zero_apply]

/-- **The Ricci tensor of de Sitter space**: `Ric = 3 g`. -/
theorem ricci_eq (z : E) (i j : Fin 4) :
    ricciOf metric.coefficient z i j = 3 * metric.coefficient z i j := by
  have hz : z ∈ (⊤ : Opens E) := trivial
  have h00 : ricciOf metric.coefficient z 0 0 = 3 * metric.coefficient z 0 0 := by
    rw [isSynchronous.ricci_zero_zero hz, (isSynchronous z hz).1]
    simp only [extrinsicRate_eq, mul_ite,
      mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, eq_comm]
    simp
    norm_num
  have h0s (α : Fin 3) : ricciOf metric.coefficient z 0 α.succ =
      3 * metric.coefficient z 0 α.succ := by
    rw [isSynchronous.ricci_zero_succ hz, (isSynchronous z hz).2 α]
    simp [fderiv_extrinsicRate, christoffel_spatial]
  have hss (α β : Fin 3) : ricciOf metric.coefficient z α.succ β.succ =
      3 * metric.coefficient z α.succ β.succ := by
    have hrate (w : E) : metric.metricRate w α β = if α = β then 2 * Real.exp (2 * w 0) else 0 :=
      metricRate_eq w α β
    have hd : fderiv ℝ (fun w => metric.metricRate w α β) z (Pi.single 0 1) =
        if α = β then 4 * Real.exp (2 * z 0) else 0 := by
      rw [show (fun w => metric.metricRate w α β) =
        fun w => if α = β then 2 * Real.exp (2 * w 0) else 0 from funext hrate]
      by_cases h : α = β
      · simp only [h, ite_true, ((hasFDerivAt_exp z).const_mul 2).fderiv, smul_apply,
          smul_eq_mul, ContinuousLinearMap.proj_apply, Pi.single_eq_same]
        ring
      · simp [h]
    rw [isSynchronous.ricci_succ_succ hz, hd, coefficient_succ]
    simp only [sliceRicci, christoffel_spatial, fderiv_const_apply, zero_apply, mul_zero,
      sub_zero, Finset.sum_const_zero, zero_add, metricRate_eq, extrinsicRate_eq]
    by_cases h : α = β
    · subst h
      simp only [ite_true, Fin.sum_univ_three]
      fin_cases α <;> simp <;> ring
    · simp only [h, ite_false, mul_zero, zero_div]
      rw [Finset.sum_eq_zero fun γ _ => by
        by_cases hγ : α = γ <;> by_cases hγ' : γ = β <;> simp_all [Ne.symm h]]
      simp
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨α, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨β, rfl⟩
    · exact h00
    · exact h0s β
  · rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨β, rfl⟩
    · have hsym := metric.toLorentzMetric.ricci_symmetric (⟨z, hz⟩ : (⊤ : Opens E))
        (chartField (physicalChart ⟨z, hz⟩) (Pi.single α.succ 1) ⟨z, hz⟩)
        (chartField (physicalChart ⟨z, hz⟩) (Pi.single 0 1) ⟨z, hz⟩)
      rw [toLorentzMetric_ricci_chartField, toLorentzMetric_ricci_chartField] at hsym
      rw [hsym, h0s α, metric.coefficient_symmetric hz]
    · exact hss α β

end ProjectAinos.GeneralRelativity.DeSitterSlicing
