/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateCurvature

/-!
# Metrics with diagonal coefficients

A family of diagonal coefficients `c : E → Fin (d + 1) → ℝ` on the model space gives the forms
`g = ∑ᵢ cᵢ dxⁱ ⊗ dxⁱ` (`diagonalForm`). Where `−σ.timeSign c₀ < 0` and `0 < −σ.timeSign c_α`
for every spatial index, they have the signature of `σ`, and they form a coordinate metric
(`ofDiagonal`) whose matrix of coefficients is `diag(c)` (`coefficient_ofDiagonal`).

* `christoffelOf_diagonal`: the Christoffel symbols of a diagonal matrix of coefficients are
  `Γ^k_{ij} = (δ_{kj} ∂_i c_k + δ_{ki} ∂_j c_k − δ_{ij} ∂_k c_i)/(2 c_k)`, where no coefficient
  vanishes. No differentiability is needed: the off-diagonal entries are the constant `0`.
* `minkowski_eq_ofDiagonal`, `christoffelOf_minkowski`: the Minkowski metric is the diagonal
  metric of the constant signs `lorentzSign σ i`, and its Christoffel symbols vanish.
* `diagonalExampleMetric`, `christoffelOf_diagonalExampleMetric`: the nonconstant diagonal metric
  `−(1 + x₁²) dt² + dx₁²` on the whole model has `Γ^1_{00} = x₁`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set TopologicalSpace
open scoped ContDiff

namespace ProjectAinos.SmoothGeometry.CoordinateMetric

variable {σ : LorentzConvention} {d : ℕ} {U : Opens (MinkowskiModel d)}

/-! ### Diagonal forms -/

/-- The diagonal form `∑ᵢ cᵢ(x) dxⁱ ⊗ dxⁱ` at the point `x`. -/
def diagonalForm (c : MinkowskiModel d → Fin (d + 1) → ℝ) (x : MinkowskiModel d) :
    MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  ∑ i, c x i • (proj i : MinkowskiModel d →L[ℝ] ℝ).smulRight (proj i : MinkowskiModel d →L[ℝ] ℝ)

/-- The diagonal form evaluates to `g(v, w) = ∑ᵢ cᵢ(x) vⁱ wⁱ`. -/
theorem diagonalForm_apply (c : MinkowskiModel d → Fin (d + 1) → ℝ) (x v w : MinkowskiModel d) :
    diagonalForm c x v w = ∑ i, c x i * v i * w i := by
  simp only [diagonalForm, _root_.sum_apply, smul_apply, smulRight_apply, proj_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The diagonal forms are smooth where the coefficients are. -/
theorem contDiffOn_diagonalForm {c : MinkowskiModel d → Fin (d + 1) → ℝ}
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U) : ContDiffOn ℝ ∞ (diagonalForm c) U := by
  refine contDiffOn_clm_apply.mpr fun v => contDiffOn_clm_apply.mpr fun w => ?_
  simp only [diagonalForm_apply]
  exact ContDiffOn.sum fun i _ => ((hc i).mul contDiffOn_const).mul contDiffOn_const

/-! ### The coordinate metric -/

/-- The diagonal coordinate metric `∑ᵢ cᵢ dxⁱ ⊗ dxⁱ`, on an open set where the coefficients are
smooth, `−σ.timeSign c₀ < 0` and `0 < −σ.timeSign c_α` for every spatial index `α`. -/
def ofDiagonal (c : MinkowskiModel d → Fin (d + 1) → ℝ)
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ) : CoordinateMetric σ d U :=
  ofCriterion (diagonalForm c) (contDiffOn_diagonalForm hc)
    (fun x _ v w => by
      rw [diagonalForm_apply, diagonalForm_apply]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (fun x hx => by
      rw [diagonalForm_apply, Fin.sum_univ_succ]
      simpa using h0 x hx)
    (fun x hx v hv => by
      rw [diagonalForm_apply, Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, Finset.mul_sum]
      obtain ⟨α, hα⟩ := Function.ne_iff.mp hv
      refine Finset.sum_pos' (fun β _ => ?_) ⟨α, Finset.mem_univ α, ?_⟩
      · have := hs x hx β
        nlinarith [mul_self_nonneg (v β)]
      · have := hs x hx α
        have hα' : 0 < v α * v α := mul_self_pos.mpr hα
        nlinarith)

/-- The form of the diagonal coordinate metric is the diagonal form of its coefficients. -/
@[simp] theorem ofDiagonal_form (c : MinkowskiModel d → Fin (d + 1) → ℝ)
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ) :
    (ofDiagonal c hc h0 hs).form = diagonalForm c := rfl

/-- The matrix of coefficients of the diagonal metric is `diag(c)` at every point. -/
theorem coefficient_ofDiagonal (c : MinkowskiModel d → Fin (d + 1) → ℝ)
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ) (y : MinkowskiModel d) :
    (ofDiagonal c hc h0 hs).coefficient y = Matrix.diagonal (c y) := by
  ext i j
  simp only [coefficient, ofDiagonal_form, Matrix.of_apply, diagonalForm_apply,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/-! ### The Christoffel symbols -/

/-- The derivative of an entry of a diagonal matrix of coefficients. -/
theorem fderiv_diagonal_apply (c : MinkowskiModel d → Fin (d + 1) → ℝ) (y v : MinkowskiModel d)
    (i j : Fin (d + 1)) :
    fderiv ℝ (fun z => Matrix.diagonal (c z) i j) y v =
      if i = j then fderiv ℝ (fun z => c z i) y v else 0 := by
  by_cases h : i = j
  · subst h
    simp only [Matrix.diagonal_apply_eq, ite_true]
  · simp only [Matrix.diagonal_apply_ne _ h, h, ite_false, fderiv_const_apply, zero_apply]

/-- The Christoffel symbols of a diagonal matrix of coefficients with no vanishing entry:
`Γ^k_{ij} = (δ_{kj} ∂_i c_k + δ_{ki} ∂_j c_k − δ_{ij} ∂_k c_i)/(2 c_k)`. -/
theorem christoffelOf_diagonal (c : MinkowskiModel d → Fin (d + 1) → ℝ) (y : MinkowskiModel d)
    (hy : ∀ i, c y i ≠ 0) (k i j : Fin (d + 1)) :
    christoffelOf (fun z => Matrix.diagonal (c z)) y k i j =
      ((if k = j then fderiv ℝ (fun z => c z k) y (Pi.single i 1) else 0) +
        (if k = i then fderiv ℝ (fun z => c z k) y (Pi.single j 1) else 0) -
        (if i = j then fderiv ℝ (fun z => c z i) y (Pi.single k 1) else 0)) / (2 * c y k) := by
  have hinv : (Matrix.diagonal (c y))⁻¹ = Matrix.diagonal fun l => (c y l)⁻¹ := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with l
    exact inv_mul_cancel₀ (hy l)
  simp only [christoffelOf, hinv, fderiv_diagonal_apply]
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [Matrix.diagonal_apply_ne _ (Ne.symm hl)])
    (fun h => absurd (Finset.mem_univ k) h)]
  rw [Matrix.diagonal_apply_eq]
  simp only [@eq_comm _ j k]
  rw [inv_mul_eq_div, div_div, mul_comm (c y k)]
  rcases eq_or_ne k j with rfl | hkj
  · rfl
  · simp only [hkj, ite_false]

/-- The Christoffel symbols of the diagonal coordinate metric, where no coefficient vanishes:
`Γ^k_{ij} = (δ_{kj} ∂_i c_k + δ_{ki} ∂_j c_k − δ_{ij} ∂_k c_i)/(2 c_k)`. -/
theorem christoffelOf_ofDiagonal (c : MinkowskiModel d → Fin (d + 1) → ℝ)
    (hc : ∀ i, ContDiffOn ℝ ∞ (fun x => c x i) U)
    (h0 : ∀ x ∈ U, -σ.timeSign * c x 0 < 0)
    (hs : ∀ x ∈ U, ∀ α : Fin d, 0 < -σ.timeSign * c x α.succ) (y : MinkowskiModel d)
    (hy : ∀ i, c y i ≠ 0) (k i j : Fin (d + 1)) :
    christoffelOf (ofDiagonal c hc h0 hs).coefficient y k i j =
      ((if k = j then fderiv ℝ (fun z => c z k) y (Pi.single i 1) else 0) +
        (if k = i then fderiv ℝ (fun z => c z k) y (Pi.single j 1) else 0) -
        (if i = j then fderiv ℝ (fun z => c z i) y (Pi.single k 1) else 0)) / (2 * c y k) := by
  rw [show (ofDiagonal c hc h0 hs).coefficient = fun z => Matrix.diagonal (c z) from
    funext (coefficient_ofDiagonal c hc h0 hs)]
  exact christoffelOf_diagonal c y hy k i j

/-! ### Instances -/

/-- The Minkowski sign of the time axis satisfies the time condition of `ofDiagonal`. -/
theorem lorentzSign_time_neg (σ : LorentzConvention) :
    -σ.timeSign * lorentzSign σ (0 : Fin (d + 1)) < 0 := by
  cases σ <;> simp [lorentzSign]

/-- The Minkowski sign of a spatial axis satisfies the space condition of `ofDiagonal`. -/
theorem lorentzSign_space_pos (σ : LorentzConvention) (α : Fin d) :
    0 < -σ.timeSign * lorentzSign σ α.succ := by
  cases σ <;> simp [lorentzSign]

variable (σ d U) in
/-- The Minkowski metric is the diagonal metric of the constant signs `lorentzSign σ i`. -/
theorem minkowski_eq_ofDiagonal :
    minkowski σ d U = ofDiagonal (fun _ => lorentzSign σ) (fun _ => contDiffOn_const)
      (fun _ _ => lorentzSign_time_neg σ) (fun _ _ α => lorentzSign_space_pos σ α) := rfl

/-- The Christoffel symbols of the Minkowski metric vanish. -/
theorem christoffelOf_minkowski (y : MinkowskiModel d) (k i j : Fin (d + 1)) :
    christoffelOf (minkowski σ d U).coefficient y k i j = 0 := by
  have hy (i : Fin (d + 1)) : lorentzSign σ i ≠ 0 := by
    cases σ <;> by_cases h : i = 0 <;> simp [lorentzSign, h]
  rw [minkowski_eq_ofDiagonal, christoffelOf_ofDiagonal _ _ _ _ y hy]
  simp

/-- The nonconstant diagonal coefficients `diag(−(1 + x₁²), 1)` in one spatial dimension. -/
def diagonalExample (x : MinkowskiModel 1) : Fin 2 → ℝ := ![-(1 + x 1 ^ 2), 1]

/-- The time coefficient of the example is `−(1 + x₁²)`. -/
theorem diagonalExample_zero (x : MinkowskiModel 1) : diagonalExample x 0 = -(1 + x 1 ^ 2) :=
  rfl

/-- The space coefficient of the example is `1`. -/
theorem diagonalExample_one (x : MinkowskiModel 1) : diagonalExample x 1 = 1 := rfl

/-- No coefficient of the example vanishes. -/
theorem diagonalExample_ne_zero (x : MinkowskiModel 1) (i : Fin 2) : diagonalExample x i ≠ 0 := by
  fin_cases i
  · change -(1 + x 1 ^ 2) ≠ 0
    nlinarith [sq_nonneg (x 1)]
  · exact one_ne_zero

/-- The metric `ds² = −(1 + x₁²) dt² + dx₁²` on the whole model, with `σ = timeNegative`. -/
def diagonalExampleMetric : CoordinateMetric .timeNegative 1 ⊤ :=
  ofDiagonal diagonalExample
    (fun i => by
      fin_cases i
      · change ContDiffOn ℝ ∞ (fun x : MinkowskiModel 1 => -(1 + x 1 ^ 2)) ⊤
        exact (contDiff_const.add ((contDiff_apply ℝ (fun _ : Fin 2 => ℝ) 1).pow 2)).neg.contDiffOn
      · exact contDiffOn_const)
    (fun x _ => by
      rw [diagonalExample_zero, LorentzConvention.timeSign_timeNegative]
      nlinarith [sq_nonneg (x 1)])
    (fun x _ α => by
      fin_cases α
      change 0 < -(-1 : ℝ) * diagonalExample x 1
      rw [diagonalExample_one]
      norm_num)

/-- A nonzero Christoffel symbol: `Γ^1_{00} = x₁` for the metric `−(1 + x₁²) dt² + dx₁²`. -/
theorem christoffelOf_diagonalExampleMetric (y : MinkowskiModel 1) :
    christoffelOf diagonalExampleMetric.coefficient y 1 0 0 = y 1 := by
  rw [diagonalExampleMetric, christoffelOf_ofDiagonal _ _ _ _ y (diagonalExample_ne_zero y)]
  have hd : HasFDerivAt (fun z : MinkowskiModel 1 => diagonalExample z 0)
      (-((2 * y 1) • (proj 1 : MinkowskiModel 1 →L[ℝ] ℝ))) y := by
    have h1 : HasFDerivAt (fun z : MinkowskiModel 1 => z 1)
        (proj 1 : MinkowskiModel 1 →L[ℝ] ℝ) y := hasFDerivAt_apply 1 y
    refine ((h1.pow 2).const_add 1).neg.congr_fderiv ?_
    ext v
    simp
  rw [hd.fderiv]
  simp [diagonalExample_one]

end ProjectAinos.SmoothGeometry.CoordinateMetric
