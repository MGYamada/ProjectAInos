/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.NewtonianMetric

/-! # Uniform coefficient and timelike bounds for Newtonian families -/

@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped Topology

namespace ProjectAInos.GeneralRelativity
namespace NewtonianMetricFamily

variable {U : Opens NewtonianCoordinates} (f : NewtonianMetricFamily U)

lemma epsilon_nonneg (c : ℝ) : 0 ≤ epsilon c := inv_nonneg.mpr (sq_nonneg c)

lemma epsilon_le_one {c : ℝ} (hc : 1 ≤ c) : epsilon c ≤ 1 :=
  inv_le_one_of_one_le₀ (by nlinarith : 1 ≤ c ^ 2)

lemma spatialComponent_abs_le {H : NewtonianSpatialMatrix} {K : ℝ}
    (hH : ‖H‖ ≤ K) (i j : Fin 3) : |H i j| ≤ K := by
  simpa only [Real.norm_eq_abs] using
    ((norm_le_pi_norm (H i) j).trans ((norm_le_pi_norm H i).trans hH))

lemma spaceComponent_abs_le {v : NewtonianSpace} {V : ℝ}
    (hv : ‖v‖ ≤ V) (i : Fin 3) : |v i| ≤ V := by
  simpa only [Real.norm_eq_abs] using (norm_le_pi_norm v i).trans hv

/-- Uniform estimate for the mixed coefficient contraction, in the coordinate sup norm. -/
theorem mixedPairing_abs_le {B v : NewtonianSpace} {K V : ℝ}
    (hB : ‖B‖ ≤ K) (hv : ‖v‖ ≤ V) (hK : 0 ≤ K) :
    |∑ i : Fin 3, B i * v i| ≤ 3 * K * V := by
  calc
    |∑ i : Fin 3, B i * v i| ≤ ∑ i : Fin 3, |B i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, K * V := Finset.sum_le_sum fun i _ => by
      rw [abs_mul]
      exact mul_le_mul (spaceComponent_abs_le hB i) (spaceComponent_abs_le hv i)
        (abs_nonneg _) hK
    _ = 3 * K * V := by simp; ring

/-- Uniform estimate for the full spatial correction, including off-diagonal terms. -/
theorem spatialPairing_abs_le {H : NewtonianSpatialMatrix} {v : NewtonianSpace} {K V : ℝ}
    (hH : ‖H‖ ≤ K) (hv : ‖v‖ ≤ V) (hK : 0 ≤ K) (hV : 0 ≤ V) :
    |∑ i : Fin 3, ∑ j : Fin 3, H i j * v i * v j| ≤ 9 * K * V ^ 2 := by
  calc
    |∑ i : Fin 3, ∑ j : Fin 3, H i j * v i * v j| ≤
        ∑ i : Fin 3, ∑ j : Fin 3, |H i j * v i * v j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun _ _ =>
        Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, K * V * V := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_mul]
      exact mul_le_mul
        (mul_le_mul (spatialComponent_abs_le hH i j) (spaceComponent_abs_le hv i)
          (abs_nonneg _) hK)
        (spaceComponent_abs_le hv j) (abs_nonneg _) (mul_nonneg hK hV)
    _ = 9 * K * V ^ 2 := by simp; ring

lemma spatialSquare_le {v : NewtonianSpace} {V : ℝ} (hv : ‖v‖ ≤ V) (hV : 0 ≤ V) :
    (∑ i : Fin 3, v i ^ 2) ≤ 3 * V ^ 2 := by
  calc
    (∑ i : Fin 3, v i ^ 2) ≤ ∑ _i : Fin 3, V ^ 2 := Finset.sum_le_sum fun i _ => by
      have h := (sq_le_sq₀ (abs_nonneg (v i)) hV).mpr (spaceComponent_abs_le hv i)
      simpa only [sq_abs] using h
    _ = 3 * V ^ 2 := by simp

/-- A coarse but uniform threshold, independent of the particular member and point. -/
def timelikeThreshold (V : ℝ) : ℝ :=
  3 * f.bound + 6 * f.bound * V + (3 + 9 * f.bound) * V ^ 2

/-- The large negative physical-time coefficient dominates bounded velocities,
even with all time-dependent correction families present. -/
theorem form_timeVelocity_le {c : ℝ} (hc : 1 ≤ c) {q : NewtonianCoordinates}
    (hq : q ∈ U) {v : NewtonianSpace} {V : ℝ} (hv : ‖v‖ ≤ V) (hV : 0 ≤ V) :
    f.form c q (timeVelocity v) (timeVelocity v) ≤ -c ^ 2 + f.timelikeThreshold V := by
  have hK := f.bound_nonneg
  have hp : |f.potential q| ≤ f.bound := by
    simpa only [Real.norm_eq_abs] using f.potential_bound.value q hq
  have ha : |f.timeCorrection c q| ≤ f.bound := by
    simpa only [Real.norm_eq_abs] using (f.time_bound c hc).value q hq
  have hb := mixedPairing_abs_le ((f.mixed_bound c hc).value q hq) hv f.bound_nonneg
  have hh := spatialPairing_abs_le ((f.spatial_bound c hc).value q hq) hv f.bound_nonneg hV
  have he := epsilon_nonneg c
  have he1 := epsilon_le_one hc
  have hp' : -2 * f.potential q ≤ 2 * f.bound := by linarith [(abs_le.mp hp).1]
  have ha' : epsilon c * f.timeCorrection c q ≤ f.bound := by
    calc
      _ ≤ epsilon c * f.bound := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans ha) he
      _ ≤ 1 * f.bound := mul_le_mul_of_nonneg_right he1 f.bound_nonneg
      _ = f.bound := one_mul _
  have hb' : 2 * epsilon c * (∑ i : Fin 3, f.mixedCorrection c q i * v i) ≤
      6 * f.bound * V := by
    calc
      _ ≤ 2 * epsilon c * (3 * f.bound * V) :=
        mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hb) (by positivity)
      _ ≤ 2 * 1 * (3 * f.bound * V) := by gcongr
      _ = 6 * f.bound * V := by ring
  have hh' : epsilon c * (∑ i : Fin 3, ∑ j : Fin 3, f.spatialCorrection c q i j * v i * v j) ≤
      9 * f.bound * V ^ 2 := by
    calc
      _ ≤ epsilon c * (9 * f.bound * V ^ 2) :=
        mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans hh) he
      _ ≤ 1 * (9 * f.bound * V ^ 2) := by gcongr
      _ = 9 * f.bound * V ^ 2 := one_mul _
  rw [f.form_timeVelocity]
  dsimp [timelikeThreshold]
  nlinarith [spatialSquare_le hv hV]

/-- Timelikeness is derived from the coefficient contract, rather than assumed in it. -/
theorem form_timeVelocity_neg {c : ℝ} (hc : 1 ≤ c) {q : NewtonianCoordinates}
    (hq : q ∈ U) {v : NewtonianSpace} {V : ℝ} (hv : ‖v‖ ≤ V) (hV : 0 ≤ V)
    (hlarge : f.timelikeThreshold V < c ^ 2) :
    f.form c q (timeVelocity v) (timeVelocity v) < 0 := by
  have h := f.form_timeVelocity_le hc hq hv hV
  linarith

/-- The same tail works simultaneously for every point and every velocity in the range. -/
theorem eventually_form_timeVelocity_neg {V : ℝ} (hV : 0 ≤ V) :
    ∀ᶠ c in Filter.atTop, ∀ q ∈ U, ∀ v : NewtonianSpace, ‖v‖ ≤ V →
      f.form c q (timeVelocity v) (timeVelocity v) < 0 := by
  have hK := f.bound_nonneg
  have hT : 0 ≤ f.timelikeThreshold V := by dsimp [timelikeThreshold]; positivity
  apply Filter.eventually_atTop.mpr
  refine ⟨max 1 (f.timelikeThreshold V + 2), ?_⟩
  intro c hc q hq v hv
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hc
  have hcT : f.timelikeThreshold V + 2 ≤ c := (le_max_right _ _).trans hc
  exact f.form_timeVelocity_neg hc1 hq hv hV (by nlinarith [sq_nonneg (c - 1)])

lemma norm_sq_le_spatialSquare (v : NewtonianSpace) :
    ‖v‖ ^ 2 ≤ ∑ i : Fin 3, v i ^ 2 := by
  obtain ⟨⟨i, hi⟩, _⟩ := IsGreatest.pi_norm v
  calc
    ‖v‖ ^ 2 = v i ^ 2 := by rw [← hi]; simp only [Real.norm_eq_abs, sq_abs]
    _ ≤ ∑ j : Fin 3, v j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

/-- The spatial restriction is positive definite for a uniform large-`c` tail.
Together with a negative time direction this supplies the inertia argument. -/
theorem form_spatial_pos {c : ℝ} (hc : 1 ≤ c) {q : NewtonianCoordinates}
    (hq : q ∈ U) (hlarge : 9 * f.bound < c ^ 2) {v : NewtonianSpace} (hv : v ≠ 0) :
    0 < f.form c q (Fin.cons 0 v) (Fin.cons 0 v) := by
  have he := epsilon_nonneg c
  have hc2 : 0 < c ^ 2 := by positivity
  have hsmall : 9 * epsilon c * f.bound < 1 := by
    have h := (div_lt_one hc2).mpr hlarge
    simpa only [epsilon, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hH := spatialPairing_abs_le ((f.spatial_bound c hc).value q hq)
    (le_rfl : ‖v‖ ≤ ‖v‖) f.bound_nonneg (norm_nonneg v)
  have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hH).1 he
  have hpos : 0 < (1 - 9 * epsilon c * f.bound) * ‖v‖ ^ 2 :=
    mul_pos (sub_pos.mpr hsmall) (sq_pos_of_pos (norm_pos_iff.mpr hv))
  rw [f.form_spatial]
  nlinarith [norm_sq_le_spatialSquare v]

end NewtonianMetricFamily
end ProjectAInos.GeneralRelativity
