/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.LorentzFrame

/-! # The Lorentz signature is stable under small symmetric perturbations

A symmetric bilinear form close to a form with a Lorentz frame has a Lorentz frame of the same
convention. The bound is explicit: if `B₀(v, w) = η(e₀ v, e₀ w)`,
`|B(u, u) − B₀(u, u)| ≤ δ ‖u‖²` and `δ ‖e₀⁻¹‖² < 1`, then `B` is the Minkowski form in some frame
(`Minkowski.exists_lorentzFrame_of_near`). The proof checks the criterion
`exists_lorentzFrame_convention` in the frame `e₀`: the perturbation changes `η(e₀, e₀) = ±1`
and `±Σ vᵢ²` on the space by less than the margin.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap

namespace ProjectAinos.SmoothGeometry.Minkowski

variable {d : ℕ}

theorem minkowskiForm_cons_one (σ : LorentzConvention) :
    minkowskiForm σ d (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) =
      σ.timeSign := by
  simp [minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign]

theorem minkowskiForm_cons_zero (σ : LorentzConvention) (v : Fin d → ℝ) :
    minkowskiForm σ d (Fin.cons 0 v) (Fin.cons 0 v) = -σ.timeSign * ∑ i, v i ^ 2 := by
  simp only [minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign, Fin.cons_zero, Fin.cons_succ,
    Fin.succ_ne_zero, ↓reduceIte, mul_zero, zero_add, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem norm_cons_one_le : ‖(Fin.cons 1 (0 : Fin d → ℝ) : MinkowskiModel d)‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem norm_cons_zero_le (v : Fin d → ℝ) : ‖(Fin.cons 0 v : MinkowskiModel d)‖ ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using norm_le_pi_norm v j

/-- The square of the sup norm is at most the sum of squares. -/
theorem sq_norm_le_sum_sq (v : Fin d → ℝ) : ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
  have hs : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have h : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (v j))
      (Finset.mem_univ i))
  calc ‖v‖ ^ 2 ≤ Real.sqrt (∑ i, v i ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg v) h 2
    _ = ∑ i, v i ^ 2 := Real.sq_sqrt hs

/-- A bilinear form on the model is bounded on the diagonal by the sum of its coefficients. -/
theorem abs_apply_self_le (B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
    (u : MinkowskiModel d) :
    |B u u| ≤ (∑ i, ∑ j, |B (Pi.single i 1) (Pi.single j 1)|) * ‖u‖ ^ 2 := by
  have hu (i : Fin (d + 1)) : |u i| ≤ ‖u‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm u i
  have hB : B u u = ∑ i, ∑ j, u i * u j * B (Pi.single i 1) (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ' u]
    simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hB, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_mul, mul_comm (|B (Pi.single i 1) (Pi.single j 1)|)]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  rw [sq]
  exact mul_le_mul (hu i) (hu j) (abs_nonneg _) (norm_nonneg _)

/-- **Stability of the Lorentz signature.** A symmetric form `B` with
`|B(u, u) − B₀(u, u)| ≤ δ ‖u‖²` and `δ ‖e₀⁻¹‖² < 1`, where `B₀` is the Minkowski form in the
frame `e₀`, is the Minkowski form in another frame. -/
theorem exists_lorentzFrame_of_near (σ : LorentzConvention)
    {B₀ B : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ}
    (e₀ : MinkowskiModel d ≃L[ℝ] MinkowskiModel d)
    (h₀ : ∀ v w, B₀ v w = minkowskiForm σ d (e₀ v) (e₀ w)) (hs : ∀ v w, B v w = B w v)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hB : ∀ u, |B u u - B₀ u u| ≤ δ * ‖u‖ ^ 2)
    (hδ : δ * ‖(e₀.symm : MinkowskiModel d →L[ℝ] MinkowskiModel d)‖ ^ 2 < 1) :
    ∃ e : MinkowskiModel d ≃L[ℝ] MinkowskiModel d,
      ∀ v w, B v w = minkowskiForm σ d (e v) (e w) := by
  set f : MinkowskiModel d →L[ℝ] MinkowskiModel d :=
    (e₀.symm : MinkowskiModel d →L[ℝ] MinkowskiModel d)
  set c := δ * ‖f‖ ^ 2
  have hc : 0 ≤ c := by positivity
  let B' := B.bilinearComp f f
  have hB' (u : MinkowskiModel d) :
      B' u u = minkowskiForm σ d u u + (B (f u) (f u) - B₀ (f u) (f u)) := by
    simp only [B', bilinearComp_apply, h₀, f, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
    ring
  have hδu (u : MinkowskiModel d) : |B (f u) (f u) - B₀ (f u) (f u)| ≤ c * ‖u‖ ^ 2 := by
    calc |B (f u) (f u) - B₀ (f u) (f u)| ≤ δ * ‖f u‖ ^ 2 := hB (f u)
      _ ≤ δ * (‖f‖ * ‖u‖) ^ 2 := by gcongr; exact f.le_opNorm u
      _ = c * ‖u‖ ^ 2 := by ring
  have ht : -σ.timeSign * B' (Fin.cons 1 (0 : Fin d → ℝ)) (Fin.cons 1 (0 : Fin d → ℝ)) < 0 := by
    rw [hB', minkowskiForm_cons_one]
    have h1 := hδu (Fin.cons 1 (0 : Fin d → ℝ))
    have hn : ‖(Fin.cons 1 (0 : Fin d → ℝ) : MinkowskiModel d)‖ ^ 2 ≤ 1 := by
      have := norm_cons_one_le (d := d)
      nlinarith [norm_nonneg (Fin.cons 1 (0 : Fin d → ℝ) : MinkowskiModel d)]
    have h2 : |B (f (Fin.cons 1 0)) (f (Fin.cons 1 0)) - B₀ (f (Fin.cons 1 0))
        (f (Fin.cons 1 0))| < 1 :=
      lt_of_le_of_lt (h1.trans (by nlinarith)) hδ
    cases σ <;> simp only [LorentzConvention.timeSign] <;> linarith [abs_lt.mp h2]
  have hx (v : Fin d → ℝ) (hv : v ≠ 0) :
      0 < -σ.timeSign * B' (Fin.cons 0 v) (Fin.cons 0 v) := by
    rw [hB', minkowskiForm_cons_zero]
    have h1 := hδu (Fin.cons 0 v)
    have hn := norm_cons_zero_le v
    have hsq := sq_norm_le_sum_sq v
    have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖(Fin.cons 0 v : MinkowskiModel d)‖ ^ 2 ≤ ‖v‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    set δ' := B (f (Fin.cons 0 v)) (f (Fin.cons 0 v)) - B₀ (f (Fin.cons 0 v)) (f (Fin.cons 0 v))
    have h2 : |δ'| < ‖v‖ ^ 2 := by
      calc |δ'| ≤ c * ‖(Fin.cons 0 v : MinkowskiModel d)‖ ^ 2 := h1
        _ ≤ c * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_left hu hc
        _ < 1 * ‖v‖ ^ 2 := mul_lt_mul_of_pos_right hδ (by positivity)
        _ = ‖v‖ ^ 2 := one_mul _
    have hts := σ.timeSign_mul_self
    have : -σ.timeSign * (-σ.timeSign * ∑ i, v i ^ 2 + δ') =
        ∑ i, v i ^ 2 - σ.timeSign * δ' := by
      linear_combination (∑ i, v i ^ 2) * hts
    rw [this]
    cases σ <;> simp only [LorentzConvention.timeSign] <;> linarith [abs_lt.mp h2]
  obtain ⟨e', he'⟩ := exists_lorentzFrame_convention σ B'
    (fun v w => by simp only [B', bilinearComp_apply, hs]) ht hx
  refine ⟨e₀.trans e', fun v w => ?_⟩
  have h := he' (e₀ v) (e₀ w)
  simp only [B', bilinearComp_apply, f, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply] at h
  simpa only [ContinuousLinearEquiv.trans_apply] using h

end ProjectAinos.SmoothGeometry.Minkowski
