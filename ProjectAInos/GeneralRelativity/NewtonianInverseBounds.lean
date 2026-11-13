/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianLorentz

/-! # Inverse coefficient estimates for Newtonian metric families -/

@[expose] public section
noncomputable section

open Matrix TopologicalSpace

namespace ProjectAInos.GeneralRelativity.NewtonianMetricFamily

local notation "E" => NewtonianCoordinates

/-- The signed row multiplier removes the diverging time-time coefficient. -/
def rowScale (c : ℝ) (i : Fin 4) : ℝ := (Fin.cons (-epsilon c) (fun _ : Fin 3 => (1 : ℝ)) : E) i

private def scaledError {U : Opens E} (f : NewtonianMetricFamily U) (c : ℝ) (q : E) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (rowScale c) * f.coefficient c q - 1

private theorem scaledError_abs_le {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (q : U) (i j : Fin 4) :
    |f.scaledError c q i j| ≤ 3 * f.bound * epsilon c := by
  have he := epsilon_nonneg c
  have he1 := epsilon_le_one hc
  have hK := f.bound_nonneg
  have hp : |f.potential q| ≤ f.bound := f.potential_bound.value q q.property
  have ha : |f.timeCorrection c q| ≤ f.bound := (f.time_bound c hc).value q q.property
  have hb (i : Fin 3) := spaceComponent_abs_le ((f.mixed_bound c hc).value q q.property) i
  have hh (i j : Fin 3) := spatialComponent_abs_le ((f.spatial_bound c hc).value q q.property) i j
  have hεc : epsilon c * c^2 = 1 := inv_mul_cancel₀ (by positivity)
  have h₁ : ∀ a : ℝ, |a| ≤ f.bound → |epsilon c * a| ≤ f.bound * epsilon c := by
    intro a h
    rw [abs_mul, abs_of_nonneg he, mul_comm (f.bound)]
    exact mul_le_mul_of_nonneg_left h he
  simp only [scaledError, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.one_apply]
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · change |(-epsilon c) * (-c^2 - 2 * f.potential q + epsilon c * f.timeCorrection c q) - 1| ≤ _
      rw [show -epsilon c * (-c^2 - 2 * f.potential q + epsilon c * f.timeCorrection c q) - 1 =
        epsilon c * (2 * f.potential q - epsilon c * f.timeCorrection c q) by
          linear_combination hεc]
      rw [abs_mul, abs_of_nonneg he, mul_comm (3 * f.bound)]
      apply mul_le_mul_of_nonneg_left _ he
      calc
        _ ≤ |2 * f.potential q| + |epsilon c * f.timeCorrection c q| := by simpa [sub_eq_add_neg] using abs_add_le (2 * f.potential q) (-(epsilon c * f.timeCorrection c q))
        _ ≤ 3 * f.bound := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
          nlinarith [h₁ _ ha, mul_le_mul_of_nonneg_right he1 hK]
    · simp only [rowScale, Fin.cons_zero, coefficient_mixed, Ne.symm (Fin.succ_ne_zero j),
        ite_false, sub_zero, neg_mul, abs_neg]
      rw [abs_mul, abs_of_nonneg he]
      nlinarith [h₁ _ (hb j), mul_le_mul_of_nonneg_right he1 (mul_nonneg hK he)]
  · refine Fin.cases ?_ (fun j => ?_) j
    · change |1 * (epsilon c * f.mixedCorrection c q i) -
        (if i.succ = 0 then 1 else 0)| ≤ _
      simp only [one_mul, Fin.succ_ne_zero, ite_false, sub_zero]
      linarith [h₁ _ (hb i), mul_nonneg hK he]
    · simp only [rowScale, Fin.cons_succ, coefficient_spatial, one_mul, Fin.succ_inj, add_sub_cancel_left]
      linarith [h₁ _ (hh i j), mul_nonneg hK he]

private theorem scaledError_mulVec_bound {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (q : U) (v : E) :
    ‖f.scaledError c q *ᵥ v‖ ≤ (12 * f.bound * epsilon c) * ‖v‖ := by
  have hK := f.bound_nonneg
  have he := epsilon_nonneg c
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |f.scaledError c q i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, 3 * f.bound * epsilon c * ‖v‖ := Finset.sum_le_sum fun j _ => by
      rw [abs_mul, ← Real.norm_eq_abs (v j)]
      exact mul_le_mul (f.scaledError_abs_le hc q i j) (norm_le_pi_norm v j)
        (norm_nonneg _) (by positivity)
    _ = _ := by simp; ring

/-- Uniform inverse bounds on the full open domain. A temporal index contributes
a factor `c⁻²` and the spatial inverse differs from the identity by `O(c⁻²)`. -/
theorem inverseComponent_bounds {U : Opens E} (f : NewtonianMetricFamily U) {c : ℝ}
    (hc : 1 ≤ c) (hlarge : 24 * f.bound < c^2) (q : U) :
    (∀ i : Fin 4, |(f.coefficient c q)⁻¹ i 0| ≤ 2 * epsilon c) ∧
    (∀ j : Fin 4, |(f.coefficient c q)⁻¹ 0 j| ≤ 2 * epsilon c) ∧
    (∀ i j : Fin 3,
      |(f.coefficient c q)⁻¹ i.succ j.succ - (if i = j then 1 else 0)| ≤
        24 * f.bound * epsilon c) := by
  have hK := f.bound_nonneg
  have he := epsilon_nonneg c
  have hsmall : 12 * f.bound * epsilon c ≤ 1 / 2 := by
    have hc2 : 0 < c^2 := by positivity
    simpa [epsilon, div_eq_mul_inv] using
      (show (12 * f.bound) / c^2 ≤ 1 / 2 from (div_le_iff₀ hc2).2 (by linarith))
  let A := f.coefficient c q
  let D := Matrix.diagonal (rowScale c)
  let R := f.scaledError c q
  have hA : A * A⁻¹ = 1 := f.coefficient_mul_inverse hc (by linarith) q
  have hcol (j : Fin 4) :
      ‖A⁻¹ *ᵥ (Pi.single j 1 : E)‖ ≤ 2 * |rowScale c j| ∧
      ‖A⁻¹ *ᵥ (Pi.single j 1 : E) - Pi.single j (rowScale c j)‖ ≤
        (24 * f.bound * epsilon c) * |rowScale c j| := by
    let v := A⁻¹ *ᵥ (Pi.single j 1 : E)
    let w : E := Pi.single j (rowScale c j)
    have heq : v + R *ᵥ v = w := by
      change v + (D * A - 1) *ᵥ v = w
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel, mulVec_mulVec,
        Matrix.mul_assoc, hA, Matrix.mul_one, Matrix.diagonal_mulVec_single]
      simp [w]
    have hdiff : v - w = -(R *ᵥ v) := by rw [← heq]; abel
    have hR := f.scaledError_mulVec_bound hc q v
    have hw : ‖w‖ = |rowScale c j| := by simp [w, Pi.norm_single, Real.norm_eq_abs]
    have hv : ‖v‖ ≤ 2 * |rowScale c j| := by
      have h := norm_sub_le w (R *ᵥ v)
      have hleft : w - R *ᵥ v = v := by rw [← heq]; abel
      rw [hleft, hw] at h
      change ‖R *ᵥ v‖ ≤ _ at hR
      linarith [mul_le_mul_of_nonneg_right hsmall (norm_nonneg v)]
    refine ⟨hv, ?_⟩
    change ‖v - w‖ ≤ _
    rw [hdiff, norm_neg]
    have hmul := mul_le_mul_of_nonneg_left hv
      (show 0 ≤ 12 * f.bound * epsilon c by positivity)
    exact hR.trans (by linarith)
  have ht (i : Fin 4) : |A⁻¹ i 0| ≤ 2 * epsilon c := by
    have h := (norm_le_pi_norm (A⁻¹ *ᵥ (Pi.single 0 1 : E)) i).trans (hcol 0).1
    simpa [Matrix.mulVec_single_one, Real.norm_eq_abs, rowScale, abs_of_nonneg he] using h
  have hsym : Aᵀ = A := Matrix.ext fun i j => f.coefficient_symmetric (by linarith) q.property j i
  have hisym : A⁻¹ᵀ = A⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsym]
  refine ⟨ht, fun j => ?_, fun i j => ?_⟩
  · change |A⁻¹ 0 j| ≤ _
    have hj : A⁻¹ 0 j = A⁻¹ j 0 := congrFun (congrFun hisym j) 0
    rw [hj]
    exact ht j
  · let v : E := A⁻¹ *ᵥ (Pi.single j.succ 1 : E) -
        Pi.single j.succ (rowScale c j.succ)
    have hV : ‖v‖ ≤ (24 * f.bound * epsilon c) * |rowScale c j.succ| := (hcol j.succ).2
    have h := (norm_le_pi_norm v i.succ).trans hV
    dsimp only [v] at h
    rw [Matrix.mulVec_single_one] at h
    change |A⁻¹ i.succ j.succ - (if i = j then 1 else 0)| ≤ _
    simpa only [Pi.sub_apply, Real.norm_eq_abs, rowScale, Fin.cons_succ,
      Matrix.col, Matrix.transpose_apply, Pi.single_apply, Fin.succ_inj, abs_one, mul_one, eq_comm] using h

end ProjectAInos.GeneralRelativity.NewtonianMetricFamily
