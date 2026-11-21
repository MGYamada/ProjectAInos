/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.PseudotensorFlux
public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Tactic

/-!
# Energy and momentum at large distances from bodies

Landau–Lifshitz, §96, (96.16)–(96.17), and §105, for coordinate metrics on open sets of
`MinkowskiModel 3` with the slices `x⁰ = t`, `x ∈ ℝ³ = EuclideanSpace ℝ (Fin 3)`, the
normalization `∂_l h^{ikl} = 2 |g| (G^{ik} + t^{ik})` of `Pseudotensor.lean` and the Einstein
equations `G^{ik} = κ T^{ik}` (`κ = 8πG`, `c = 1`). The charges are
`P^i(t, R) = ½ ∮_{r = R} h^{i0α} n_α dA` (`CoordinateMetric.surfaceCharge`); they are `κ` times the
`P^i` of (96.17).

* `IsAsymptoticallyGalileanAt g t R₀ C`: on the slice `x⁰ = t`, for `r = ‖x‖ ≥ R₀`,
  `|g_{ab} − η_{ab}| ≤ C/r`, `|∂_c g_{ab}| ≤ C/r²` and `|∂_c ∂_e g_{ab}| ≤ C/r³`;
  `IsAsymptoticallyGalilean g R₀ C`: on every slice.
* `inv_bound_of_near_minkowski`: a matrix within `1/8` of `η` is invertible with inverse entries
  at most `2` and `|det| ≤ 384`; hence beyond `max R₀ (8C)` the Christoffel symbols are
  `O(r⁻²)` (`abs_christoffelOf_le`) and **the pseudotensor is `O(r⁻⁴)`**
  (`abs_pseudotensor_le`), and outside compact matter so is the total `|g| (κ T^{ik} + t^{ik})`
  (`abs_totalDensity_le`).
* `integrable_of_le_div_pow_four`, `tendsto_surfaceCharge_of_integrable`; **`tendsto_surfaceCharge`
  and `charge_eq_integral`**: for a slice in `U` with the decay and compact matter, the surface
  charges converge to `P^i(t) = ∫ |g| (κ T^{i0} + t^{i0}) dV` (`charge`), (96.16).
* **`charge_const_of_flux`**: if the flux of the total through the spheres tends to `0`
  uniformly in `t ∈ [t₁, t₂]`, the charges at `t₁` and `t₂` agree; `abs_totalFlux_le`: with the
  decay on every slice of the interval and compact matter, the flux is `O(R⁻²)`, so
  **`charge_const`**: `P^i(t₁) = P^i(t₂)`, the conservation (96.8) in integral form.
* Instances: `isAsymptoticallyGalilean_minkowski` (`C = 0`), with `tendsto_surfaceCharge_minkowski`
  and `charge_const_minkowski`; the linearized Schwarzschild field in isotropic form
  `η + 2Mρ (dt² + dx²)` (`isotropicMetric`), with `ρ = 1/r` for `r ≥ 2R₀` glued smoothly to `0`
  inside (`isotropicProfile`), is Galilean at large distances
  (`isAsymptoticallyGalilean_isotropicMetric`, `R₀' = 3R₀`, `C = 8M`); its charges are
  `P⁰(t, R) = 8πM (1 + 2M/R)` for `R > 2R₀` (`surfaceCharge_isotropicMetric`), so
  **`charge_zero_eq_mass`**: `P⁰ = 8πM = κM`, the mass `M` in the normalization of (96.17).

The four-vector character of `P^i` under linear Lorentz changes of the co-ordinates is not
treated here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter TopologicalSpace
open scoped Topology ContDiff Matrix

namespace ProjectAinos.GeneralRelativity

open SmoothGeometry SmoothGeometry.CoordinateMetric SmoothGeometry.Minkowski

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {σ : LorentzConvention} {U : Opens (MinkowskiModel 3)}

/-! ### Asymptotically Galilean metrics -/

/-- The Minkowski coefficients `η = diag(lorentzSign σ)`. -/
abbrev minkowskiCoefficient (σ : LorentzConvention) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (lorentzSign σ)

/-- **A metric that is Galilean at large distances on the slice `x⁰ = t`**, Landau–Lifshitz
§§96, 105: for `r = ‖x‖ ≥ R₀` the events `(t, x)` lie in `U`, and `|g_{ab} − η_{ab}| ≤ C/r`,
`|∂_c g_{ab}| ≤ C/r²` and `|∂_c ∂_e g_{ab}| ≤ C/r³` (derivatives along all four axes). -/
structure IsAsymptoticallyGalileanAt (g : CoordinateMetric σ 3 U) (t R₀ C : ℝ) : Prop where
  /-- The radius beyond which the bounds hold is positive. -/
  radius_pos : 0 < R₀
  /-- The exterior of the ball of radius `R₀` lies in `U`. -/
  mem : ∀ x : E3, R₀ ≤ ‖x‖ → vector t x ∈ U
  /-- `|g_{ab} − η_{ab}| ≤ C/r`. -/
  coefficient_le : ∀ x : E3, R₀ ≤ ‖x‖ → ∀ a b,
    |g.coefficient (vector t x) a b - minkowskiCoefficient σ a b| ≤ C / ‖x‖
  /-- `|∂_c g_{ab}| ≤ C/r²`. -/
  fderiv_le : ∀ x : E3, R₀ ≤ ‖x‖ → ∀ a b c,
    |fderiv ℝ (fun w => g.coefficient w a b) (vector t x) (Pi.single c 1)| ≤ C / ‖x‖ ^ 2
  /-- `|∂_c ∂_e g_{ab}| ≤ C/r³`. -/
  secondDerivative_le : ∀ x : E3, R₀ ≤ ‖x‖ → ∀ a b c e,
    |g.secondDerivative (vector t x) a b c e| ≤ C / ‖x‖ ^ 3

/-- A metric that is Galilean at large distances on every slice, with the same constants. -/
def IsAsymptoticallyGalilean (g : CoordinateMetric σ 3 U) (R₀ C : ℝ) : Prop :=
  ∀ t, IsAsymptoticallyGalileanAt g t R₀ C

/-! ### Bounds near the Minkowski coefficients -/

theorem abs_lorentzSign (σ : LorentzConvention) (a : Fin 4) : |lorentzSign σ a| = 1 := by
  cases σ <;> by_cases h : a = 0 <;> simp [lorentzSign, h]

theorem abs_minkowskiCoefficient_le (σ : LorentzConvention) (a b : Fin 4) :
    |minkowskiCoefficient σ a b| ≤ 1 := by
  by_cases h : a = b
  · subst h
    simp [abs_lorentzSign]
  · simp [Matrix.diagonal_apply_ne _ h]

/-- **Matrices near the Minkowski coefficients**: if every entry of `M − η` is at most `1/8`,
then `M` is invertible, the entries of `M⁻¹` are at most `2` and `|det M| ≤ 384`. -/
theorem inv_bound_of_near_minkowski {M : Matrix (Fin 4) (Fin 4) ℝ}
    (hM : ∀ a b, |M a b - minkowskiCoefficient σ a b| ≤ 1 / 8) :
    M.det ≠ 0 ∧ (∀ a b, |M⁻¹ a b| ≤ 2) ∧ |M.det| ≤ 384 := by
  have hlow (v : Fin 4 → ℝ) : ‖v‖ ≤ 2 * ‖M *ᵥ v‖ := by
    have h1 : ‖v‖ ≤ ‖minkowskiCoefficient σ *ᵥ v‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun a => ?_
      have ha : (minkowskiCoefficient σ *ᵥ v) a = lorentzSign σ a * v a := by
        simp [Matrix.mulVec_diagonal]
      calc ‖v a‖ = ‖(minkowskiCoefficient σ *ᵥ v) a‖ := by
            rw [ha, norm_mul, Real.norm_eq_abs (lorentzSign σ a), abs_lorentzSign, one_mul]
        _ ≤ _ := norm_le_pi_norm _ a
    have h2 : ‖(M - minkowskiCoefficient σ) *ᵥ v‖ ≤ 1 / 2 * ‖v‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
      rw [Real.norm_eq_abs]
      have h := abs_sum_fin_le (f := fun b => (M - minkowskiCoefficient σ) a b * v b)
        (c := 1 / 8 * ‖v‖) fun b => abs_mul_le_mul_of_le (by simpa using hM a b)
          (by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v b)
      change |∑ b, (M - minkowskiCoefficient σ) a b * v b| ≤ _
      norm_num at h ⊢
      linarith
    have h3 : minkowskiCoefficient σ *ᵥ v = M *ᵥ v - (M - minkowskiCoefficient σ) *ᵥ v := by
      rw [Matrix.sub_mulVec]
      abel
    rw [h3] at h1
    linarith [norm_sub_le (M *ᵥ v) ((M - minkowskiCoefficient σ) *ᵥ v)]
  have hdet : M.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h := hlow v
    rw [hMv, norm_zero, mul_zero] at h
    exact hv (norm_le_zero_iff.mp h)
  refine ⟨hdet, fun a b => ?_, ?_⟩
  · set w := M⁻¹ *ᵥ (Pi.single b 1 : Fin 4 → ℝ) with hw
    have hMw : M *ᵥ w = Pi.single b 1 := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mulVec]
    have hwn : ‖w‖ ≤ 2 := by
      have h := hlow w
      rw [hMw] at h
      have hs : ‖(Pi.single b (1 : ℝ) : Fin 4 → ℝ)‖ = 1 := by simp [Pi.norm_single]
      linarith
    have hwa : w a = M⁻¹ a b := by
      rw [hw, Matrix.mulVec_single_one]
      rfl
    rw [← hwa, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm w a).trans hwn
  · have hle (a b : Fin 4) : AbsoluteValue.abs (M a b) ≤ 2 := by
      rw [AbsoluteValue.abs_apply]
      have h1 := hM a b
      have h2 := abs_minkowskiCoefficient_le σ a b
      calc |M a b| = |(M a b - minkowskiCoefficient σ a b) + minkowskiCoefficient σ a b| := by
            ring_nf
        _ ≤ |M a b - minkowskiCoefficient σ a b| + |minkowskiCoefficient σ a b| := abs_add_le _ _
        _ ≤ 2 := by linarith
    have h := Matrix.det_le hle
    rw [AbsoluteValue.abs_apply] at h
    norm_num [Nat.factorial] at h
    exact h

/-! ### The decay of the pseudotensor -/

/-- The constant `384 · 1327104 C²` of the bound `|g| |t^{ik}| ≤ K/r⁴`. -/
def decayConstant (C : ℝ) : ℝ := 384 * (1327104 * C ^ 2)

theorem decayConstant_nonneg (C : ℝ) : 0 ≤ decayConstant C := by
  unfold decayConstant
  positivity

namespace IsAsymptoticallyGalileanAt

variable {g : CoordinateMetric σ 3 U} {t R₀ C : ℝ}

theorem norm_pos (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3} (hx : R₀ ≤ ‖x‖) :
    0 < ‖x‖ :=
  h.radius_pos.trans_le hx

/-- Beyond `max R₀ (8C)` the coefficients are within `1/8` of the Minkowski coefficients. -/
theorem coefficient_near (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3}
    (hx : max R₀ (8 * C) ≤ ‖x‖) (a b : Fin 4) :
    |g.coefficient (vector t x) a b - minkowskiCoefficient σ a b| ≤ 1 / 8 := by
  have hR := le_of_max_le_left hx
  have hC := le_of_max_le_right hx
  have hpos := h.norm_pos hR
  refine (h.coefficient_le x hR a b).trans ?_
  rw [div_le_iff₀ hpos]
  linarith

/-- Beyond `max R₀ (8C)` the entries of the inverse metric are at most `2`. -/
theorem abs_inv_le (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3}
    (hx : max R₀ (8 * C) ≤ ‖x‖) (a b : Fin 4) :
    |(g.coefficient (vector t x))⁻¹ a b| ≤ 2 :=
  (inv_bound_of_near_minkowski (h.coefficient_near hx)).2.1 a b

/-- Beyond `max R₀ (8C)`, `|g| ≤ 384`. -/
theorem densityOf_sq_le (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3}
    (hx : max R₀ (8 * C) ≤ ‖x‖) : densityOf g.coefficient (vector t x) ^ 2 ≤ 384 := by
  rw [densityOf, Real.sq_sqrt (abs_nonneg _)]
  exact (inv_bound_of_near_minkowski (h.coefficient_near hx)).2.2

/-- Beyond `max R₀ (8C)` the Christoffel symbols are at most `12 C/r²`. -/
theorem abs_christoffelOf_le (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3}
    (hx : max R₀ (8 * C) ≤ ‖x‖) (k i j : Fin 4) :
    |christoffelOf g.coefficient (vector t x) k i j| ≤ 12 * C / ‖x‖ ^ 2 := by
  have hD := h.fderiv_le x (le_of_max_le_left hx)
  unfold christoffelOf
  have hterm (l : Fin 4) : |(g.coefficient (vector t x))⁻¹ k l *
      (fderiv ℝ (fun z => g.coefficient z j l) (vector t x) (Pi.single i 1) +
       fderiv ℝ (fun z => g.coefficient z l i) (vector t x) (Pi.single j 1) -
       fderiv ℝ (fun z => g.coefficient z i j) (vector t x) (Pi.single l 1)) / 2| ≤
      3 * C / ‖x‖ ^ 2 := by
    rw [mul_div_assoc]
    have h3 : |(fderiv ℝ (fun z => g.coefficient z j l) (vector t x) (Pi.single i 1) +
        fderiv ℝ (fun z => g.coefficient z l i) (vector t x) (Pi.single j 1) -
        fderiv ℝ (fun z => g.coefficient z i j) (vector t x) (Pi.single l 1)) / 2| ≤
        3 * C / ‖x‖ ^ 2 / 2 := by
      obtain ⟨h1, h1'⟩ := abs_le.mp (hD j l i)
      obtain ⟨h2, h2'⟩ := abs_le.mp (hD l i j)
      obtain ⟨h3, h3'⟩ := abs_le.mp (hD i j l)
      rw [abs_div, abs_two]
      refine div_le_div_of_nonneg_right ?_ zero_le_two
      refine abs_le.mpr ⟨?_, ?_⟩ <;> rw [mul_div_assoc] <;> linarith
    calc _ ≤ 2 * (3 * C / ‖x‖ ^ 2 / 2) := abs_mul_le_mul_of_le (h.abs_inv_le hx k l) h3
      _ = 3 * C / ‖x‖ ^ 2 := by ring
  calc _ ≤ ((4 : ℕ) : ℝ) * (3 * C / ‖x‖ ^ 2) := abs_sum_fin_le hterm
    _ = 12 * C / ‖x‖ ^ 2 := by push_cast; ring

/-- **The pseudotensor decays like `r⁻⁴`**: beyond `max R₀ (8C)`,
`|t^{ik}| ≤ 1327104 C²/r⁴`, since it is quadratic in the Christoffel symbols (96.9). -/
theorem abs_pseudotensor_le (h : IsAsymptoticallyGalileanAt g t R₀ C) {x : E3}
    (hx : max R₀ (8 * C) ≤ ‖x‖) (i k : Fin 4) :
    |g.pseudotensor (vector t x) i k| ≤ 1327104 * C ^ 2 / ‖x‖ ^ 4 := by
  have hpos := h.norm_pos (le_of_max_le_left hx)
  rw [pseudotensor_eq (h.mem x (le_of_max_le_left hx))]
  have hb := abs_pseudoBraces_le (n := 4) (K := 2) (B := 12 * C / ‖x‖ ^ 2)
    (fun a b => h.abs_inv_le hx a b) (fun a b c => h.abs_christoffelOf_le hx a b c) i k
  rw [abs_div, abs_two]
  calc _ ≤ 18 * ((4 : ℕ) : ℝ) ^ 4 * 2 ^ 2 * (12 * C / ‖x‖ ^ 2) ^ 2 / 2 :=
        div_le_div_of_nonneg_right hb zero_le_two
    _ = 1327104 * C ^ 2 / ‖x‖ ^ 4 := by
      field_simp
      norm_num
      ring

/-- **The total decays like `r⁻⁴` outside compact matter**: if `G^{ik} = κ T^{ik}` and `T^{ik}`
vanishes beyond `R_m`, then `|g| |G^{ik} + t^{ik}| ≤ K/r⁴` beyond `max (max R₀ (8C)) R_m`. -/
theorem abs_totalDensity_le (h : IsAsymptoticallyGalileanAt g t R₀ C) {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {Rm : ℝ} {i k : Fin 4}
    (hm : ∀ x : E3, Rm ≤ ‖x‖ → T (vector t x) i k = 0) {x : E3}
    (hx : max (max R₀ (8 * C)) Rm ≤ ‖x‖) :
    |g.totalDensity (vector t x) i k| ≤ decayConstant C / ‖x‖ ^ 4 := by
  have hx1 := le_of_max_le_left hx
  have hpos := h.norm_pos (le_of_max_le_left hx1)
  rw [g.totalDensity_eq hT (h.mem x (le_of_max_le_left hx1)), hm x (le_of_max_le_right hx),
    mul_zero, zero_add, abs_mul, abs_of_nonneg (sq_nonneg _), decayConstant, mul_div_assoc]
  exact mul_le_mul (h.densityOf_sq_le hx1) (h.abs_pseudotensor_le hx1 i k) (abs_nonneg _)
    (by norm_num)

end IsAsymptoticallyGalileanAt

/-! ### Integrability and the limit of the surface charges -/

/-- A continuous function on `ℝ³` that is `O(r⁻⁴)` at infinity is integrable. -/
theorem integrable_of_le_div_pow_four {f : E3 → ℝ} (hf : Continuous f) {R K : ℝ}
    (hK0 : 0 ≤ K) (hK : ∀ x : E3, R ≤ ‖x‖ → |f x| ≤ K / ‖x‖ ^ 4) : Integrable f := by
  set R' := max R 1 with hR'
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E3) R').exists_bound_of_continuousOn
    hf.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (mem_closedBall_self (by positivity)))
  set A := max (16 * K) (B * (1 + R') ^ 4) with hA
  have hint : Integrable fun x : E3 => (1 + ‖x‖) ^ (-(4 : ℝ)) :=
    integrable_one_add_norm (by norm_num [finrank_euclideanSpace_fin])
  refine (hint.const_mul A).mono' hf.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hpos : 0 < 1 + ‖x‖ := by positivity
  rw [Real.rpow_neg hpos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.norm_eq_abs]
  by_cases hx : ‖x‖ ≤ R'
  · have h1 : |f x| ≤ B := by
      simpa [Real.norm_eq_abs] using hB x (mem_closedBall_zero_iff.mpr hx)
    have h2 : B ≤ B * (1 + R') ^ 4 * ((1 + ‖x‖) ^ 4)⁻¹ := by
      rw [mul_assoc]
      refine le_mul_of_one_le_right hB0 ?_
      rw [le_mul_inv_iff₀ (by positivity), one_mul]
      gcongr
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  · push Not at hx
    have h1 : 1 ≤ ‖x‖ := (le_max_right R 1).trans hx.le
    have h2 : R ≤ ‖x‖ := (le_max_left R 1).trans hx.le
    have hxpos : 0 < ‖x‖ := by linarith
    refine (hK x h2).trans ?_
    have h3 : (1 + ‖x‖) ^ 4 ≤ 16 * ‖x‖ ^ 4 := by
      have : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
      calc (1 + ‖x‖) ^ 4 ≤ (2 * ‖x‖) ^ 4 := by gcongr
        _ = 16 * ‖x‖ ^ 4 := by ring
    calc K / ‖x‖ ^ 4 ≤ 16 * K * ((1 + ‖x‖) ^ 4)⁻¹ := by
          rw [div_eq_mul_inv, mul_comm 16 K, mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hK0
          rw [le_mul_inv_iff₀ (by positivity)]
          calc (‖x‖ ^ 4)⁻¹ * (1 + ‖x‖) ^ 4 ≤ (‖x‖ ^ 4)⁻¹ * (16 * ‖x‖ ^ 4) := by gcongr
            _ = 16 := by field_simp
      _ ≤ A * ((1 + ‖x‖) ^ 4)⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

/-- The total density on a slice that lies in `U` is continuous. -/
theorem continuous_totalDensity_slice {g : CoordinateMetric σ 3 U} {t : ℝ}
    (hU : ∀ x : E3, vector t x ∈ U) (i k : Fin 4) :
    Continuous fun x : E3 => g.totalDensity (vector t x) i k :=
  (g.contDiffOn_totalDensity i k).continuousOn.comp_continuous
    (contDiff_vector_space t (n := 0)).continuous hU

/-- If the total density of a slice that lies in `U` is integrable, the surface charges converge
to its integral as the radius tends to infinity. -/
theorem tendsto_surfaceCharge_of_integrable {g : CoordinateMetric σ 3 U} {t : ℝ}
    (hU : ∀ x : E3, vector t x ∈ U) {i : Fin 4}
    (hint : Integrable fun x : E3 => g.totalDensity (vector t x) i 0) :
    Tendsto (fun R => g.surfaceCharge t R i) atTop
      (𝓝 (∫ x : E3, g.totalDensity (vector t x) i 0)) := by
  have heq : (fun R => ∫ x : E3, (ball (0 : E3) R).indicator
      (fun x => g.totalDensity (vector t x) i 0) x) =ᶠ[atTop]
      fun R => g.surfaceCharge t R i := by
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [integral_indicator measurableSet_ball,
      g.surfaceCharge_eq_integral_ball hR (fun x _ => hU x) i]
  refine Tendsto.congr' heq ?_
  refine tendsto_integral_filter_of_dominated_convergence
    (fun x => ‖g.totalDensity (vector t x) i 0‖) ?_ ?_ hint.norm ?_
  · exact Eventually.of_forall fun R => hint.aestronglyMeasurable.indicator measurableSet_ball
  · exact Eventually.of_forall fun R => Eventually.of_forall fun x =>
      norm_indicator_le_norm_self _ _
  · refine Eventually.of_forall fun x => tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ‖x‖] with R hR
    rw [indicator_of_mem (mem_ball_zero_iff.mpr hR)]

/-- The charge `P^i(t) = lim_{R → ∞} P^i(t, R)` of the slice `x⁰ = t`. -/
def charge (g : CoordinateMetric σ 3 U) (t : ℝ) (i : Fin 4) : ℝ :=
  limUnder atTop fun R => g.surfaceCharge t R i

/-- **The energy and momentum of matter and field**, Landau–Lifshitz (96.16)–(96.17): for a
metric that is Galilean at large distances on a slice `x⁰ = t` contained in `U`, with the
Einstein equations `G^{ik} = κ T^{ik}` and matter that vanishes outside a ball, the surface
charges `½ ∮ h^{i0α} n_α dA` converge, as the radius tends to infinity, to the integral
`∫ |g| (κ T^{i0} + t^{i0}) dV` over the slice. -/
theorem tendsto_surfaceCharge {g : CoordinateMetric σ 3 U} {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t R₀ C Rm : ℝ}
    (hg : IsAsymptoticallyGalileanAt g t R₀ C) (hU : ∀ x : E3, vector t x ∈ U) {i : Fin 4}
    (hm : ∀ x : E3, Rm ≤ ‖x‖ → T (vector t x) i 0 = 0) :
    Tendsto (fun R => g.surfaceCharge t R i) atTop
      (𝓝 (∫ x : E3, densityOf g.coefficient (vector t x) ^ 2 *
        (κ * T (vector t x) i 0 + g.pseudotensor (vector t x) i 0))) := by
  have hint : Integrable fun x : E3 => g.totalDensity (vector t x) i 0 :=
    integrable_of_le_div_pow_four (continuous_totalDensity_slice hU i 0)
      (decayConstant_nonneg C) fun x hx => hg.abs_totalDensity_le hT hm hx
  have h := tendsto_surfaceCharge_of_integrable hU hint
  rwa [integral_congr_ae (Eventually.of_forall fun x => g.totalDensity_eq hT (hU x) i 0)] at h

/-- **The charge is the volume integral of the total**, `P^i = ∫ |g| (κ T^{i0} + t^{i0}) dV`. -/
theorem charge_eq_integral {g : CoordinateMetric σ 3 U} {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t R₀ C Rm : ℝ}
    (hg : IsAsymptoticallyGalileanAt g t R₀ C) (hU : ∀ x : E3, vector t x ∈ U) {i : Fin 4}
    (hm : ∀ x : E3, Rm ≤ ‖x‖ → T (vector t x) i 0 = 0) :
    charge g t i = ∫ x : E3, densityOf g.coefficient (vector t x) ^ 2 *
      (κ * T (vector t x) i 0 + g.pseudotensor (vector t x) i 0) :=
  (tendsto_surfaceCharge hT hg hU hm).limUnder_eq

/-! ### Conservation -/

/-- **The conservation of the charges when no flux escapes to infinity** (96.8): if the
exterior regions `‖x‖ ≥ R₀` of the slices `t ∈ [t₁, t₂]` lie in `U` and the flux
`∮ |g| (G^{iα} + t^{iα}) n_α dA` through the spheres tends to `0` uniformly in `t`, then the limits
of the surface charges at `t₁` and `t₂` agree: `dP^i/dt = 0`. -/
theorem charge_const_of_flux {g : CoordinateMetric σ 3 U} {t₁ t₂ R₀ : ℝ} (ht : t₁ ≤ t₂)
    (hR₀ : 0 < R₀) (hU : ∀ t ∈ Icc t₁ t₂, ∀ x : E3, R₀ ≤ ‖x‖ → vector t x ∈ U) {i : Fin 4}
    {P₁ P₂ : ℝ} (h₁ : Tendsto (fun R => g.surfaceCharge t₁ R i) atTop (𝓝 P₁))
    (h₂ : Tendsto (fun R => g.surfaceCharge t₂ R i) atTop (𝓝 P₂))
    (hflux : ∀ ε > 0, ∀ᶠ R in atTop, ∀ t ∈ Icc t₁ t₂, |g.totalFlux t R i| ≤ ε) :
    P₁ = P₂ := by
  have hd := h₂.sub h₁
  have h0 : Tendsto (fun R => g.surfaceCharge t₂ R i - g.surfaceCharge t₁ R i) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hδ : 0 < ε / (2 * (t₂ - t₁ + 1)) := by
      have : 0 < t₂ - t₁ + 1 := by linarith
      positivity
    filter_upwards [hflux _ hδ, eventually_ge_atTop R₀] with R hR hRR
    rw [Real.dist_eq, sub_zero, g.surfaceCharge_sub_surfaceCharge_time ht (hR₀.trans_le hRR)
      (fun t ht' x hx => hU t ht' x (hx ▸ hRR)) i, abs_neg, ← Real.norm_eq_abs]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => g.totalFlux t R i) (C := ε / (2 * (t₂ - t₁ + 1))) (fun t ht' => by
        rw [uIoc_of_le ht] at ht'
        rw [Real.norm_eq_abs]
        exact hR t ⟨ht'.1.le, ht'.2⟩)
    refine hb.trans_lt ?_
    rw [abs_of_nonneg (by linarith : 0 ≤ t₂ - t₁)]
    have h1 : 0 < t₂ - t₁ + 1 := by linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith [tendsto_nhds_unique hd h0]

/-- **The flux through a large sphere decays like `R⁻²`**: on a slice where the metric is
Galilean at large distances and the matter vanishes beyond `R_m`, the flux of the total through
the sphere of radius `R ≥ max (max R₀ (8C)) R_m` is at most `12π K/R²`, `K = decayConstant C`. -/
theorem abs_totalFlux_le {g : CoordinateMetric σ 3 U} {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t R₀ C Rm R : ℝ}
    (hg : IsAsymptoticallyGalileanAt g t R₀ C) {i : Fin 4}
    (hm : ∀ x : E3, Rm ≤ ‖x‖ → ∀ k, T (vector t x) i k = 0)
    (hR : max (max R₀ (8 * C)) Rm ≤ R) :
    |g.totalFlux t R i| ≤ 12 * π * decayConstant C / R ^ 2 := by
  have hRpos : 0 < R :=
    hg.radius_pos.trans_le ((le_max_left _ _).trans ((le_max_left _ _).trans hR))
  have hpt : ∀ n : sphere (0 : E3) 1, ‖R ^ 2 * ∑ α, g.totalFluxField t i α (R • (n : E3)) *
      (n : E3) α‖ ≤ 3 * decayConstant C / R ^ 2 := fun n => by
    have hnorm : ‖R • (n : E3)‖ = R := by
      rw [norm_smul, norm_eq_of_mem_sphere n, mul_one, Real.norm_eq_abs, abs_of_pos hRpos]
    have hterm (α : Fin 3) : |g.totalFluxField t i α (R • (n : E3)) * (n : E3) α| ≤
        decayConstant C / R ^ 4 := by
      have h1 := hg.abs_totalDensity_le hT (fun x hx => hm x hx α.succ) (x := R • (n : E3))
        (by rw [hnorm]; exact hR)
      rw [hnorm] at h1
      have h2 : |(n : E3) α| ≤ 1 := by
        rw [← Real.norm_eq_abs]
        exact (PiLp.norm_apply_le (n : E3) α).trans (norm_eq_of_mem_sphere n).le
      calc _ ≤ decayConstant C / R ^ 4 * 1 := abs_mul_le_mul_of_le h1 h2
        _ = _ := mul_one _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg R)]
    calc R ^ 2 * |∑ α, g.totalFluxField t i α (R • (n : E3)) * (n : E3) α| ≤
        R ^ 2 * (((3 : ℕ) : ℝ) * (decayConstant C / R ^ 4)) :=
          mul_le_mul_of_nonneg_left (abs_sum_fin_le hterm) (sq_nonneg R)
      _ = 3 * decayConstant C / R ^ 2 := by
        push_cast
        field_simp
  have h := norm_integral_le_of_norm_le_const (μ := Sphere.sphereMeasure)
    (Eventually.of_forall hpt)
  rw [Sphere.sphereMeasure_real_univ] at h
  rw [totalFlux, Sphere.flux, ← Real.norm_eq_abs]
  calc _ ≤ 3 * decayConstant C / R ^ 2 * (4 * π) := h
    _ = 12 * π * decayConstant C / R ^ 2 := by ring

/-- **The conservation of energy and momentum**, Landau–Lifshitz (96.8) and (96.16): if the
metric is Galilean at large distances on the slices `t ∈ [t₁, t₂]` with the same constants,
the slices `x⁰ = t₁` and `x⁰ = t₂` lie in `U`, the Einstein equations `G^{ik} = κ T^{ik}` hold and
the matter vanishes outside a ball, then `P^i = ∫ |g| (κ T^{i0} + t^{i0}) dV` is the same on both
slices. -/
theorem charge_const {g : CoordinateMetric σ 3 U} {κ : ℝ}
    {T : MinkowskiModel 3 → Fin 4 → Fin 4 → ℝ}
    (hT : ∀ w ∈ U, ∀ i k, g.raisedEinstein w i k = κ * T w i k) {t₁ t₂ R₀ C Rm : ℝ}
    (ht : t₁ ≤ t₂) (hg : ∀ t ∈ Icc t₁ t₂, IsAsymptoticallyGalileanAt g t R₀ C)
    (hU₁ : ∀ x : E3, vector t₁ x ∈ U) (hU₂ : ∀ x : E3, vector t₂ x ∈ U) {i : Fin 4}
    (hm : ∀ t ∈ Icc t₁ t₂, ∀ x : E3, Rm ≤ ‖x‖ → ∀ k, T (vector t x) i k = 0) :
    ∫ x : E3, densityOf g.coefficient (vector t₁ x) ^ 2 *
        (κ * T (vector t₁ x) i 0 + g.pseudotensor (vector t₁ x) i 0) =
      ∫ x : E3, densityOf g.coefficient (vector t₂ x) ^ 2 *
        (κ * T (vector t₂ x) i 0 + g.pseudotensor (vector t₂ x) i 0) := by
  have ht₁ : t₁ ∈ Icc t₁ t₂ := ⟨le_rfl, ht⟩
  have ht₂ : t₂ ∈ Icc t₁ t₂ := ⟨ht, le_rfl⟩
  refine charge_const_of_flux ht (hg t₁ ht₁).radius_pos (fun t ht' x hx => (hg t ht').mem x hx)
    (tendsto_surfaceCharge hT (hg t₁ ht₁) hU₁ fun x hx => hm t₁ ht₁ x hx 0)
    (tendsto_surfaceCharge hT (hg t₂ ht₂) hU₂ fun x hx => hm t₂ ht₂ x hx 0) fun ε hε => ?_
  have hlim : Tendsto (fun R : ℝ => 12 * π * decayConstant C / R ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  filter_upwards [hlim.eventually (eventually_le_nhds hε),
    eventually_ge_atTop (max (max R₀ (8 * C)) Rm)] with R hR hRR t ht'
  exact (abs_totalFlux_le hT (hg t ht') (hm t ht') hRR).trans hR

/-! ### The radial profile `1/r` glued smoothly inside a ball -/

/-- The profile `ρ(x) = χ(x)/‖x‖` with the cutoff `χ = Wave.cutoff R₀`: it vanishes for
`‖x‖ ≤ R₀` and is `1/‖x‖` for `‖x‖ ≥ 2R₀`. -/
def isotropicProfile (R₀ : ℝ) (x : E3) : ℝ := Wave.cutoff R₀ x / ‖x‖

theorem contDiff_isotropicProfile {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ContDiff ℝ ∞ (isotropicProfile R₀) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Wave.cutoff_eventuallyEq_zero hR₀] with y hy
    simp [isotropicProfile, hy]
  · exact (Wave.contDiff_cutoff hR₀ (n := ⊤)).contDiffAt.div (contDiffAt_norm ℝ hx)
      (norm_ne_zero_iff.mpr hx)

theorem isotropicProfile_nonneg (R₀ : ℝ) (x : E3) : 0 ≤ isotropicProfile R₀ x :=
  div_nonneg (Wave.cutoff_mem_Icc _ _).1 (norm_nonneg _)

theorem isotropicProfile_le {R₀ : ℝ} (hR₀ : 0 < R₀) (x : E3) : isotropicProfile R₀ x ≤ R₀⁻¹ := by
  by_cases hx : ‖x‖ ≤ R₀
  · rw [isotropicProfile, Wave.cutoff_eq_zero hR₀ hx, zero_div]
    positivity
  · push Not at hx
    calc Wave.cutoff R₀ x / ‖x‖ ≤ 1 / ‖x‖ :=
          div_le_div_of_nonneg_right (Wave.cutoff_mem_Icc _ _).2 (norm_nonneg _)
      _ ≤ R₀⁻¹ := by
          rw [one_div]
          exact inv_anti₀ hR₀ hx.le

theorem isotropicProfile_eq {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ ≤ ‖x‖) :
    isotropicProfile R₀ x = ‖x‖⁻¹ := by
  rw [isotropicProfile, Wave.cutoff_eq_one hR₀ hx, one_div]

theorem isotropicProfile_eventuallyEq {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖) :
    isotropicProfile R₀ =ᶠ[𝓝 x] fun y => ‖y‖⁻¹ := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact isotropicProfile_eq hR₀ (le_of_lt hy)

/-- The derivative of `1/‖·‖` away from the origin is `v ↦ −⟨x, v⟩/‖x‖³`. -/
theorem hasFDerivAt_norm_inv {x : E3} (hx : x ≠ 0) :
    HasFDerivAt (fun y : E3 => ‖y‖⁻¹) (-(‖x‖ ^ 3)⁻¹ • innerSL ℝ x) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := (hasFDerivAt_inv hn).comp x (Wave.hasFDerivAt_norm_of_ne_zero hx)
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    innerSL_apply_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
  field_simp

/-- The derivative of the profile beyond `2R₀`: `∂ρ(x)(u) = −⟨x, u⟩/‖x‖³`. -/
theorem fderiv_isotropicProfile {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖)
    (u : E3) : fderiv ℝ (isotropicProfile R₀) x u = -(inner ℝ x u / ‖x‖ ^ 3) := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [(isotropicProfile_eventuallyEq hR₀ hx).fderiv_eq, (hasFDerivAt_norm_inv hx0).fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- The second derivative of the profile beyond `2R₀`:
`∂(∂ρ(·)(u))(x)(v) = −⟨v, u⟩/‖x‖³ + 3⟨x, u⟩⟨x, v⟩/‖x‖⁵`. -/
theorem fderiv_fderiv_isotropicProfile {R₀ : ℝ} (hR₀ : 0 < R₀) {x : E3} (hx : 2 * R₀ < ‖x‖)
    (u v : E3) : fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x v =
      -(inner ℝ v u / ‖x‖ ^ 3) + 3 * inner ℝ x u * inner ℝ x v / ‖x‖ ^ 5 := by
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have he : (fun y => fderiv ℝ (isotropicProfile R₀) y u) =ᶠ[𝓝 x]
      fun y => -(innerSL ℝ u y * (‖y‖⁻¹) ^ 3) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    rw [fderiv_isotropicProfile hR₀ hy, innerSL_apply_apply, real_inner_comm, div_eq_mul_inv,
      inv_pow]
  have hd := ((innerSL ℝ u).hasFDerivAt.fun_mul ((hasFDerivAt_norm_inv hx0).pow 3)).fun_neg
  rw [he.fderiv_eq, hd.fderiv]
  simp only [neg_apply, add_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm u v, real_inner_comm u x]
  simp only [inv_pow, nsmul_eq_mul]
  field_simp
  ring

/-! ### The linearized Schwarzschild field in isotropic form -/

/-- The diagonal coefficients `η_i − σ.timeSign · 2M ρ` of the metric `η + 2M ρ (dt² + dx²)` in
the convention `σ`; for `σ = timeNegative` it is `−(1 − 2Mρ) dt² + (1 + 2Mρ) dx²`, the
linearized Schwarzschild field `ds² = −(1 − 2M/r) dt² + (1 + 2M/r) dx²` in isotropic form for
`r ≥ 2R₀`. -/
def isotropicCoefficient (σ : LorentzConvention) (M R₀ : ℝ) (z : MinkowskiModel 3)
    (i : Fin 4) : ℝ :=
  lorentzSign σ i - σ.timeSign * (2 * M * isotropicProfile R₀ (space z))

theorem isotropicCoefficient_zero (σ : LorentzConvention) (M R₀ : ℝ) (z : MinkowskiModel 3) :
    isotropicCoefficient σ M R₀ z 0 =
      σ.timeSign * (1 - 2 * M * isotropicProfile R₀ (space z)) := by
  simp [isotropicCoefficient, lorentzSign]
  ring

theorem isotropicCoefficient_succ (σ : LorentzConvention) (M R₀ : ℝ) (z : MinkowskiModel 3)
    (α : Fin 3) : isotropicCoefficient σ M R₀ z α.succ =
      -σ.timeSign * (1 + 2 * M * isotropicProfile R₀ (space z)) := by
  simp [isotropicCoefficient, lorentzSign, Fin.succ_ne_zero]
  ring

theorem hasFDerivAt_isotropicProfile_space {R₀ : ℝ} (hR₀ : 0 < R₀) (z : MinkowskiModel 3) :
    HasFDerivAt (fun w : MinkowskiModel 3 => isotropicProfile R₀ (space w))
      ((fderiv ℝ (isotropicProfile R₀) (space z)).comp space) z :=
  ((contDiff_isotropicProfile hR₀).differentiable (by simp) _).hasFDerivAt.comp z
    space.hasFDerivAt

theorem contDiff_isotropicCoefficient (σ : LorentzConvention) (M : ℝ) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (i : Fin 4) : ContDiff ℝ ∞ fun z => isotropicCoefficient σ M R₀ z i :=
  contDiff_const.sub (contDiff_const.mul (contDiff_const.mul
    ((contDiff_isotropicProfile hR₀).comp space.contDiff)))

/-- The derivative of a coefficient: `∂_v c_i = −σ.timeSign · 2M ∂ρ(x)(v_space)`. -/
theorem fderiv_isotropicCoefficient (σ : LorentzConvention) (M : ℝ) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (z v : MinkowskiModel 3) (i : Fin 4) :
    fderiv ℝ (fun w => isotropicCoefficient σ M R₀ w i) z v =
      -σ.timeSign * (2 * M * fderiv ℝ (isotropicProfile R₀) (space z) (space v)) := by
  have h := (((hasFDerivAt_isotropicProfile_space hR₀ z).const_mul (2 * M)).const_mul
    σ.timeSign).const_sub (lorentzSign σ i)
  rw [show (fun w => isotropicCoefficient σ M R₀ w i) = fun w => lorentzSign σ i -
    σ.timeSign * (2 * M * isotropicProfile R₀ (space w)) from rfl, h.fderiv]
  simp only [neg_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  ring

/-- `0 ≤ 2Mρ < 1` everywhere when `0 ≤ M` and `2M < R₀`. -/
theorem isotropic_bounds {M R₀ : ℝ} (hM : 0 ≤ M) (hR : 2 * M < R₀) (x : E3) :
    0 ≤ 2 * M * isotropicProfile R₀ x ∧ 2 * M * isotropicProfile R₀ x < 1 := by
  have hR₀ : 0 < R₀ := by linarith
  refine ⟨by have := isotropicProfile_nonneg R₀ x; positivity, ?_⟩
  calc 2 * M * isotropicProfile R₀ x ≤ 2 * M * R₀⁻¹ :=
        mul_le_mul_of_nonneg_left (isotropicProfile_le hR₀ x) (by positivity)
    _ < 1 := by rw [← div_eq_mul_inv, div_lt_one hR₀]; exact hR

/-- **The linearized Schwarzschild metric in isotropic form**, glued smoothly to a regular metric
inside a ball: `η + 2M ρ (dt² + dx²)` on all of space-time, which is
`η + (2M/r)(dt² + dx²)` for `r ≥ 2R₀`, for `0 ≤ M` and `2M < R₀`. -/
def isotropicMetric (σ : LorentzConvention) (M R₀ : ℝ) (hM : 0 ≤ M) (hR : 2 * M < R₀) :
    CoordinateMetric σ 3 ⊤ :=
  ofDiagonal (isotropicCoefficient σ M R₀)
    (fun i => (contDiff_isotropicCoefficient σ M (by linarith) i).contDiffOn)
    (fun z _ => by
      have h := (isotropic_bounds hM hR (space z)).2
      rw [isotropicCoefficient_zero, show -σ.timeSign * (σ.timeSign *
        (1 - 2 * M * isotropicProfile R₀ (space z))) = -(σ.timeSign * σ.timeSign) *
          (1 - 2 * M * isotropicProfile R₀ (space z)) by ring, σ.timeSign_mul_self]
      linarith)
    (fun z _ α => by
      have h := (isotropic_bounds hM hR (space z)).1
      rw [isotropicCoefficient_succ, show -σ.timeSign * (-σ.timeSign *
        (1 + 2 * M * isotropicProfile R₀ (space z))) = (σ.timeSign * σ.timeSign) *
          (1 + 2 * M * isotropicProfile R₀ (space z)) by ring, σ.timeSign_mul_self]
      linarith)

variable {M R₀ : ℝ} {hM : 0 ≤ M} {hR : 2 * M < R₀}

theorem coefficient_isotropicMetric (z : MinkowskiModel 3) :
    (isotropicMetric σ M R₀ hM hR).coefficient z =
      Matrix.diagonal (isotropicCoefficient σ M R₀ z) :=
  coefficient_ofDiagonal _ _ _ _ z

theorem norm_space_single_le (c : Fin 4) : ‖space (Pi.single c 1 : MinkowskiModel 3)‖ ≤ 1 := by
  refine Fin.cases ?_ (fun α => ?_) c
  · have h := congrArg Prod.snd Wave.timeSpaceEquiv_single_zero
    simp only [Wave.timeSpaceEquiv_apply] at h
    rw [h, norm_zero]
    exact zero_le_one
  · have h := congrArg Prod.snd (Wave.timeSpaceEquiv_single_succ α)
    simp only [Wave.timeSpaceEquiv_apply] at h
    rw [h, PiLp.norm_single, norm_one]

/-- **The isotropic metric is Galilean at large distances**, with `R₀' = 3R₀` and `C = 8M`. -/
theorem isAsymptoticallyGalilean_isotropicMetric :
    IsAsymptoticallyGalilean (isotropicMetric σ M R₀ hM hR) (3 * R₀) (8 * M) := by
  have hR₀ : 0 < R₀ := by linarith
  intro t
  have hfar {x : E3} (hx : 3 * R₀ ≤ ‖x‖) : 2 * R₀ < ‖x‖ := by linarith
  have hxpos {x : E3} (hx : 3 * R₀ ≤ ‖x‖) : 0 < ‖x‖ := by linarith
  have hs : |σ.timeSign| = 1 := by cases σ <;> simp
  refine ⟨by linarith, fun _ _ => trivial, fun x hx a b => ?_, fun x hx a b c => ?_,
    fun x hx a b c e => ?_⟩
  · rw [coefficient_isotropicMetric, minkowskiCoefficient]
    by_cases hab : a = b
    · subst hab
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, isotropicCoefficient, space_vector,
        isotropicProfile_eq hR₀ (hfar hx).le, sub_sub_cancel_left, abs_neg, abs_mul, hs, one_mul,
        abs_of_nonneg (by have := hxpos hx; positivity)]
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (by linarith) (norm_nonneg _)
    · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab, sub_zero, abs_zero]
      have := hxpos hx
      positivity
  · have hfun : (fun w => (isotropicMetric σ M R₀ hM hR).coefficient w a b) =
        fun w => Matrix.diagonal (isotropicCoefficient σ M R₀ w) a b :=
      funext fun w => by rw [coefficient_isotropicMetric]
    rw [hfun, fderiv_diagonal_apply]
    have hxp := hxpos hx
    split_ifs
    · rw [fderiv_isotropicCoefficient σ M hR₀, space_vector,
        fderiv_isotropicProfile hR₀ (hfar hx), abs_mul, abs_neg, hs, one_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * M), abs_neg, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ ^ 3)]
      have hin := abs_real_inner_le_norm x (space (Pi.single c 1 : MinkowskiModel 3))
      have hu := norm_space_single_le c
      have h1 : |inner ℝ x (space (Pi.single c 1 : MinkowskiModel 3))| / ‖x‖ ^ 3 ≤
          1 / ‖x‖ ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc |inner ℝ x (space (Pi.single c 1 : MinkowskiModel 3))| * ‖x‖ ^ 2 ≤
            ‖x‖ * 1 * ‖x‖ ^ 2 := by gcongr; exact hin.trans (by gcongr)
          _ = 1 * ‖x‖ ^ 3 := by ring
      calc 2 * M * (|inner ℝ x (space (Pi.single c 1 : MinkowskiModel 3))| / ‖x‖ ^ 3) ≤
          2 * M * (1 / ‖x‖ ^ 2) := by gcongr
        _ ≤ 8 * M / ‖x‖ ^ 2 := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    · rw [abs_zero]
      positivity
  · have hxp := hxpos hx
    have hfun : (fun w => fderiv ℝ (fun v => (isotropicMetric σ M R₀ hM hR).coefficient v a b) w
        (Pi.single e 1)) = fun w => if a = b then -σ.timeSign * (2 * M *
          fderiv ℝ (isotropicProfile R₀) (space w) (space (Pi.single e 1 : MinkowskiModel 3)))
          else 0 := by
      funext w
      have hf : (fun v => (isotropicMetric σ M R₀ hM hR).coefficient v a b) =
          fun v => Matrix.diagonal (isotropicCoefficient σ M R₀ v) a b :=
        funext fun v => by rw [coefficient_isotropicMetric]
      rw [hf, fderiv_diagonal_apply]
      split_ifs with hab
      · subst hab
        exact fderiv_isotropicCoefficient σ M hR₀ w _ a
      · rfl
    unfold secondDerivative
    rw [hfun]
    split_ifs with hab
    · set u := space (Pi.single e 1 : MinkowskiModel 3)
      set u' := space (Pi.single c 1 : MinkowskiModel 3)
      have hG : DifferentiableAt ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x :=
        (((contDiff_isotropicProfile hR₀).fderiv_right (m := 1) (by simp)).clm_apply
          contDiff_const).differentiable (by simp) x
      have hG' : HasFDerivAt (fun y => fderiv ℝ (isotropicProfile R₀) y u)
          (fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x) (space (vector t x)) := by
        rw [space_vector]
        exact hG.hasFDerivAt
      have hcomp : HasFDerivAt (fun w : MinkowskiModel 3 =>
          fderiv ℝ (isotropicProfile R₀) (space w) u)
          ((fderiv ℝ (fun y => fderiv ℝ (isotropicProfile R₀) y u) x).comp space)
          (vector t x) :=
        hG'.comp (vector t x) space.hasFDerivAt
      have h := (hcomp.const_mul (2 * M)).const_mul (-σ.timeSign)
      rw [h.fderiv]
      simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
      rw [fderiv_fderiv_isotropicProfile hR₀ (hfar hx), abs_mul, abs_neg, hs, one_mul,
        abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * M)]
      have hu := norm_space_single_le e
      have hu' := norm_space_single_le c
      have h1 := abs_real_inner_le_norm u' u
      have h2 := abs_real_inner_le_norm x u
      have h3 := abs_real_inner_le_norm x u'
      have hb : |-(inner ℝ u' u / ‖x‖ ^ 3) + 3 * inner ℝ x u * inner ℝ x u' / ‖x‖ ^ 5| ≤
          4 / ‖x‖ ^ 3 := by
        have hA : |inner ℝ u' u| ≤ 1 := h1.trans (by nlinarith [norm_nonneg u, norm_nonneg u'])
        have hB : |inner ℝ x u * inner ℝ x u'| ≤ ‖x‖ ^ 2 := by
          rw [abs_mul]
          calc |inner ℝ x u| * |inner ℝ x u'| ≤ (‖x‖ * 1) * (‖x‖ * 1) := by
                gcongr
                · exact h2.trans (by gcongr)
                · exact h3.trans (by gcongr)
            _ = ‖x‖ ^ 2 := by ring
        calc _ ≤ |-(inner ℝ u' u / ‖x‖ ^ 3)| + |3 * inner ℝ x u * inner ℝ x u' / ‖x‖ ^ 5| :=
              abs_add_le _ _
          _ = |inner ℝ u' u| / ‖x‖ ^ 3 + 3 * |inner ℝ x u * inner ℝ x u'| / ‖x‖ ^ 5 := by
              rw [abs_neg, abs_div, abs_div, mul_assoc, abs_mul,
                abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ ^ 3),
                abs_of_pos (by positivity : (0 : ℝ) < ‖x‖ ^ 5),
                abs_of_pos (by norm_num : (0 : ℝ) < 3)]
          _ ≤ 1 / ‖x‖ ^ 3 + 3 * ‖x‖ ^ 2 / ‖x‖ ^ 5 := by gcongr
          _ = 4 / ‖x‖ ^ 3 := by field_simp; ring
      calc 2 * M * |-(inner ℝ u' u / ‖x‖ ^ 3) + 3 * inner ℝ x u * inner ℝ x u' / ‖x‖ ^ 5| ≤
          2 * M * (4 / ‖x‖ ^ 3) := by gcongr
        _ = 8 * M / ‖x‖ ^ 3 := by ring
    · rw [fderiv_const_apply, zero_apply, abs_zero]
      positivity

/-! ### The mass of the isotropic metric -/

theorem space_single_succ (α : Fin 3) :
    space (Pi.single α.succ 1 : MinkowskiModel 3) = EuclideanSpace.single α 1 := by
  have h := congrArg Prod.snd (Wave.timeSpaceEquiv_single_succ α)
  simpa only [Wave.timeSpaceEquiv_apply] using h

/-- The inverse of a diagonal matrix without zero entries. -/
theorem inv_diagonal_of_ne_zero {c : Fin 4 → ℝ} (hc : ∀ i, c i ≠ 0) :
    (Matrix.diagonal c)⁻¹ = Matrix.diagonal fun l => (c l)⁻¹ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.diagonal_mul_diagonal]
  convert Matrix.diagonal_one with l
  exact inv_mul_cancel₀ (hc l)

/-- `λ^{00αm} = −(1 + 2Mρ)² δ^{αm}` for the isotropic metric: the factor `|g|` cancels the
product `g^{00} g^{αα}` up to `(1 + 2Mρ)²`. -/
theorem superpotentialDensity_isotropicMetric (z : MinkowskiModel 3) (α : Fin 3) (m : Fin 4) :
    (isotropicMetric σ M R₀ hM hR).superpotentialDensity z 0 0 α.succ m =
      if m = α.succ then -(1 + 2 * M * isotropicProfile R₀ (space z)) ^ 2 else 0 := by
  obtain ⟨hP0, hP1⟩ := isotropic_bounds hM hR (space z)
  set P := 2 * M * isotropicProfile R₀ (space z) with hP
  set s := σ.timeSign with hsdef
  have hss : s * s = 1 := σ.timeSign_mul_self
  have hs0 : s ≠ 0 := by
    rintro h
    rw [h, mul_zero] at hss
    exact zero_ne_one hss
  have hc0 : isotropicCoefficient σ M R₀ z 0 = s * (1 - P) := isotropicCoefficient_zero σ M R₀ z
  have hcs (β : Fin 3) : isotropicCoefficient σ M R₀ z β.succ = -s * (1 + P) :=
    isotropicCoefficient_succ σ M R₀ z β
  have hne (i : Fin 4) : isotropicCoefficient σ M R₀ z i ≠ 0 := by
    refine Fin.cases ?_ (fun β => ?_) i
    · rw [hc0]
      exact mul_ne_zero hs0 (by linarith)
    · rw [hcs β]
      exact mul_ne_zero (neg_ne_zero.mpr hs0) (by linarith)
  have h1 : isotropicCoefficient σ M R₀ z 1 = -s * (1 + P) := hcs 0
  have h2 : isotropicCoefficient σ M R₀ z 2 = -s * (1 + P) := hcs 1
  have h3 : isotropicCoefficient σ M R₀ z 3 = -s * (1 + P) := hcs 2
  have hprod : isotropicCoefficient σ M R₀ z 0 * isotropicCoefficient σ M R₀ z 1 *
      isotropicCoefficient σ M R₀ z 2 * isotropicCoefficient σ M R₀ z 3 =
      -((1 - P) * (1 + P) ^ 3) := by
    rw [hc0, h1, h2, h3]
    linear_combination (-(1 - P) * (1 + P) ^ 3 * (s * s + 1)) * hss
  have habs : |isotropicCoefficient σ M R₀ z 0 * isotropicCoefficient σ M R₀ z 1 *
      isotropicCoefficient σ M R₀ z 2 * isotropicCoefficient σ M R₀ z 3| =
      (1 - P) * (1 + P) ^ 3 := by
    rw [hprod, abs_neg, abs_of_pos (mul_pos (by linarith) (pow_pos (by linarith) 3))]
  unfold superpotentialDensity
  rw [densityOf, Real.sq_sqrt (abs_nonneg _), coefficient_isotropicMetric,
    inv_diagonal_of_ne_zero hne, Matrix.det_diagonal, Fin.prod_univ_four, habs]
  have h0s : (0 : Fin 4) ≠ α.succ := (Fin.succ_ne_zero α).symm
  by_cases hm : m = α.succ
  · subst hm
    simp only [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ h0s, mul_zero, sub_zero,
      ite_true]
    rw [hc0, hcs α]
    have hq : 0 < 1 - P := by linarith
    have hq' : 0 < 1 + P := by linarith
    have hs2 : s ^ 2 = 1 := by rw [sq]; exact hss
    field_simp
    ring_nf
    simp only [hs2]
  · simp only [Matrix.diagonal_apply_ne _ h0s, Matrix.diagonal_apply_ne _ (Ne.symm hm),
      mul_zero, zero_mul, sub_zero, hm, ite_false]

/-- The superpotential `h^{00α} = −∂_α (1 + 2Mρ)²` of the isotropic metric. -/
theorem superpotential_isotropicMetric (z : MinkowskiModel 3) (α : Fin 3) :
    (isotropicMetric σ M R₀ hM hR).superpotential z 0 0 α.succ =
      -(2 * (1 + 2 * M * isotropicProfile R₀ (space z)) *
        (2 * M * fderiv ℝ (isotropicProfile R₀) (space z) (EuclideanSpace.single α 1))) := by
  have hR₀ : 0 < R₀ := by linarith
  unfold superpotential
  have hf (m : Fin 4) : (fun w =>
      (isotropicMetric σ M R₀ hM hR).superpotentialDensity w 0 0 α.succ m) =
      fun w => if m = α.succ then -(1 + 2 * M * isotropicProfile R₀ (space w)) ^ 2 else 0 :=
    funext fun w => superpotentialDensity_isotropicMetric w α m
  simp only [hf]
  rw [Finset.sum_eq_single α.succ (fun m _ hm => by simp [hm]) (by simp)]
  simp only [ite_true]
  have h := ((((hasFDerivAt_isotropicProfile_space hR₀ z).const_mul (2 * M)).const_add
    1).pow 2).fun_neg
  rw [h.fderiv]
  simp only [neg_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    space_single_succ, nsmul_eq_mul]
  ring

/-- **The surface charge of the isotropic metric**: on a sphere of radius `R > 2R₀`,
`P⁰(t, R) = 8πM (1 + 2M/R)`. -/
theorem surfaceCharge_isotropicMetric (t : ℝ) {R : ℝ} (hRR : 2 * R₀ < R) :
    (isotropicMetric σ M R₀ hM hR).surfaceCharge t R 0 = 8 * π * M * (1 + 2 * M / R) := by
  have hR₀ : 0 < R₀ := by linarith
  have hRpos : 0 < R := by linarith
  have hpt (n : sphere (0 : E3) 1) : R ^ 2 * ∑ α,
      (isotropicMetric σ M R₀ hM hR).chargeField t 0 α (R • (n : E3)) * (n : E3) α =
      4 * M * (1 + 2 * M / R) := by
    have hnorm : ‖R • (n : E3)‖ = R := by
      rw [norm_smul, norm_eq_of_mem_sphere n, mul_one, Real.norm_eq_abs, abs_of_pos hRpos]
    have hfar : 2 * R₀ < ‖R • (n : E3)‖ := by rw [hnorm]; exact hRR
    have hterm (α : Fin 3) : (isotropicMetric σ M R₀ hM hR).chargeField t 0 α (R • (n : E3)) *
        (n : E3) α = 4 * M * (1 + 2 * M / R) / R ^ 2 * (n : E3) α ^ 2 := by
      simp only [chargeField, superpotential_isotropicMetric, space_vector,
        isotropicProfile_eq hR₀ hfar.le, fderiv_isotropicProfile hR₀ hfar, hnorm,
        EuclideanSpace.inner_single_right, PiLp.smul_apply, smul_eq_mul, one_mul,
        conj_trivial]
      field_simp
      ring
    rw [Finset.sum_congr rfl fun α _ => hterm α, ← Finset.mul_sum,
      Sphere.sum_sq_of_mem_sphere n]
    field_simp
  rw [surfaceCharge, Sphere.flux, integral_congr_ae (Eventually.of_forall hpt), integral_const,
    smul_eq_mul, Sphere.sphereMeasure_real_univ]
  ring

/-- The surface charges of the isotropic metric converge to `8πM`. -/
theorem tendsto_surfaceCharge_isotropicMetric (t : ℝ) :
    Tendsto (fun R => (isotropicMetric σ M R₀ hM hR).surfaceCharge t R 0) atTop
      (𝓝 (8 * π * M)) := by
  have hlim : Tendsto (fun R : ℝ => 8 * π * M * (1 + 2 * M / R)) atTop (𝓝 (8 * π * M)) := by
    have h := ((tendsto_const_nhds (x := 2 * M)).div_atTop tendsto_id).const_add 1
      |>.const_mul (8 * π * M)
    simpa using h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (2 * R₀)] with R hR
  exact (surfaceCharge_isotropicMetric t hR).symm

/-- **`P⁰ = M`**, Landau–Lifshitz §105: the energy of the isotropic metric, the limit of the
surface charges `½ ∮ h^{00α} n_α dA`, is `8πM = κ M` with `κ = 8πG`, `G = c = 1`; in the
normalization `(1/κ) ∮` of (96.17), `P⁰ = M`. -/
theorem charge_zero_eq_mass (t : ℝ) :
    charge (isotropicMetric σ M R₀ hM hR) t 0 = 8 * π * M :=
  (tendsto_surfaceCharge_isotropicMetric t).limUnder_eq

/-! ### Minkowski space -/

theorem coefficient_minkowski (z : MinkowskiModel 3) :
    (CoordinateMetric.minkowski σ 3 U).coefficient z = minkowskiCoefficient σ := by
  rw [minkowski_eq_ofDiagonal, coefficient_ofDiagonal]

/-- **Minkowski space is Galilean at large distances**, with `C = 0`. -/
theorem isAsymptoticallyGalilean_minkowski (σ : LorentzConvention) :
    IsAsymptoticallyGalilean (CoordinateMetric.minkowski σ 3 ⊤) 1 0 := by
  intro t
  have hc (a b : Fin 4) : (fun w => (CoordinateMetric.minkowski σ 3 ⊤).coefficient w a b) =
      fun _ => minkowskiCoefficient σ a b :=
    funext fun w => by rw [coefficient_minkowski]
  refine ⟨one_pos, fun _ _ => trivial, fun x _ a b => ?_, fun x _ a b c => ?_,
    fun x _ a b c e => ?_⟩
  · rw [coefficient_minkowski, sub_self, abs_zero, zero_div]
  · rw [hc, fderiv_const_apply, zero_apply, abs_zero, zero_div]
  · unfold secondDerivative
    simp [hc]

/-- The Einstein tensor of Minkowski space vanishes. -/
theorem raisedEinstein_minkowski {z : MinkowskiModel 3} (hz : z ∈ U) (i k : Fin 4) :
    (CoordinateMetric.minkowski σ 3 U).raisedEinstein z i k = 0 := by
  simp [raisedEinstein, scalarOf, minkowski_ricciOf hz]

/-- The pseudotensor of Minkowski space vanishes. -/
theorem pseudotensor_minkowski {z : MinkowskiModel 3} (hz : z ∈ U) (i k : Fin 4) :
    (CoordinateMetric.minkowski σ 3 U).pseudotensor z i k = 0 := by
  rw [pseudotensor_eq hz]
  simp [pseudoBraces, christoffelOf_minkowski]

/-- **An instance of `tendsto_surfaceCharge`**: Minkowski space with `T = 0` satisfies its
hypotheses, and its charges vanish. -/
theorem tendsto_surfaceCharge_minkowski (σ : LorentzConvention) (t : ℝ) (i : Fin 4) :
    Tendsto (fun R => (CoordinateMetric.minkowski σ 3 ⊤).surfaceCharge t R i) atTop (𝓝 0) := by
  have h := tendsto_surfaceCharge (κ := 1) (T := fun _ _ _ => 0)
    (fun w hw i k => by simp [raisedEinstein_minkowski hw]) (isAsymptoticallyGalilean_minkowski σ t)
    (fun _ => trivial) (Rm := 0) (i := i) (fun _ _ => rfl)
  simpa [pseudotensor_minkowski] using h

/-- **An instance of `charge_const`**: Minkowski space with `T = 0` satisfies its hypotheses on
every time interval. -/
theorem charge_const_minkowski (σ : LorentzConvention) {t₁ t₂ : ℝ} (ht : t₁ ≤ t₂) (i : Fin 4) :
    ∫ x : E3, densityOf (CoordinateMetric.minkowski σ 3 ⊤).coefficient (vector t₁ x) ^ 2 *
        (1 * 0 + (CoordinateMetric.minkowski σ 3 ⊤).pseudotensor (vector t₁ x) i 0) =
      ∫ x : E3, densityOf (CoordinateMetric.minkowski σ 3 ⊤).coefficient (vector t₂ x) ^ 2 *
        (1 * 0 + (CoordinateMetric.minkowski σ 3 ⊤).pseudotensor (vector t₂ x) i 0) :=
  charge_const (κ := 1) (T := fun _ _ _ => 0)
    (fun w hw i k => by simp [raisedEinstein_minkowski hw]) ht
    (fun t _ => isAsymptoticallyGalilean_minkowski σ t) (fun _ => trivial) (fun _ => trivial)
    (Rm := 0) (fun _ _ _ _ _ => rfl)

end ProjectAinos.GeneralRelativity
