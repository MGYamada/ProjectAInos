/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildCircular
public import ProjectAinos.GeneralRelativity.SphericalAnsatz
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateEinsteinEquation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The Schwarzschild field solves the vacuum Einstein equations

The exterior Schwarzschild metric of a mass `M ≥ 0` (`SchwarzschildExterior.metric`) is the
centrally symmetric ansatz of Landau–Lifshitz §100 with `A = e^ν = 1 − 2M/r` and
`B = e^λ = 1/(1 − 2M/r)` for all times and the radii `r > 2M` (`ansatzData`): the two metrics have
the same domain (`domain_ansatzData`) and the same coefficients (`coefficient_eq_ansatz`). The
partial derivatives of `A` and `B` are `∂_t A = ∂_t B = 0`, `∂_r A = 2M/r²`,
`∂_r B = −2M/(r − 2M)²`, `∂_r² A = −4M/r³` and `∂_r² B = 4M/(r − 2M)³`.

Substituting them into the Ricci tensor of the ansatz gives the vacuum equations, the solution
(100.14) of Landau–Lifshitz with `G = c = 1` and `r_g = 2M`; for instance
`R₂₂ = r B_r/(2B²) − r A_r/(2AB) + 1 − 1/B = −M/r − M/r + 2M/r = 0`.

* `ricciOf_eq_zero`, `scalarOf_eq_zero`, `einsteinOf_eq_zero`: in the co-ordinates the Ricci
  tensor, the scalar curvature and the Einstein tensor vanish at every point of the domain.
* `isEinstein_zero`, `satisfiesEinstein_zero`: the metric satisfies the vacuum Einstein equations
  `G_{ik} = κ · 0` for every coupling constant `κ`, in the co-ordinates and natively; the native
  Einstein tensor vanishes on co-ordinate fields (`einstein_chartField`).
* `ricci_chartField`, `ricci_eq_zero`: the native Ricci tensor of the metric vanishes on all pairs
  of tangent vectors.
* `ansatzData_zero_A`, `ansatzData_zero_B`, `domain_zero`, `coefficient_zero`: for `M = 0` the
  ansatz is flat space in spherical co-ordinates, `SphericalAnsatz.Data.flat`, on its domain
  `r > 0`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set
open scoped Manifold ContDiff

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski
open LorentzMetric (chartField)
open CoordinateMetric (physicalChart ricciOf scalarOf einsteinOf)
open SphericalAnsatz (partialT partialR)

variable {M : ℝ}

/-! ### The Schwarzschild field as a centrally symmetric ansatz -/

/-- **The Schwarzschild field as a centrally symmetric ansatz** (Landau–Lifshitz, (100.14)):
`A = (r − 2M)/r` and `B = r/(r − 2M)` for all times and the radii `r > 2M`. -/
def ansatzData (hM : 0 ≤ M) : SphericalAnsatz.Data where
  I := univ
  J := Ioi (2 * M)
  A := fun _ r => (r - 2 * M) / r
  B := fun _ r => r / (r - 2 * M)
  isOpen_I := isOpen_univ
  isOpen_J := isOpen_Ioi
  J_pos := fun r (hr : 2 * M < r) => show 0 < r by linarith
  contDiffOn_A := by
    change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (p.2 - 2 * M) / p.2) _
    exact (contDiff_snd.sub contDiff_const).contDiffOn.div contDiff_snd.contDiffOn
      fun p (hp : p ∈ univ ×ˢ Ioi (2 * M)) => by
        have : 2 * M < p.2 := hp.2
        exact (show 0 < p.2 by linarith).ne'
  contDiffOn_B := by
    change ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => p.2 / (p.2 - 2 * M)) _
    exact contDiff_snd.contDiffOn.div (contDiff_snd.sub contDiff_const).contDiffOn
      fun p (hp : p ∈ univ ×ˢ Ioi (2 * M)) => by
        have : 2 * M < p.2 := hp.2
        exact sub_ne_zero.mpr this.ne'
  A_pos := fun _ _ r (hr : 2 * M < r) => div_pos (by linarith) (by linarith)
  B_pos := fun _ _ r (hr : 2 * M < r) => div_pos (by linarith) (by linarith)

/-- The domain of the ansatz is the exterior domain `r > 2M`, `0 < θ < π`. -/
theorem domain_ansatzData (hM : 0 ≤ M) : SphericalAnsatz.domain (ansatzData hM) = domain M := by
  ext x
  change x 0 ∈ univ ∧ x 1 ∈ Ioi (2 * M) ∧ 0 < x 2 ∧ x 2 < Real.pi ↔
    2 * M < x 1 ∧ 0 < x 2 ∧ x 2 < Real.pi
  simp

/-- A point of the exterior domain is a point of the domain of the ansatz. -/
theorem mem_ansatzDomain (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M) :
    x ∈ SphericalAnsatz.domain (ansatzData hM) := by
  rw [domain_ansatzData]
  exact hx

/-- The diagonal coefficients of the exterior metric are those of the ansatz. -/
theorem diagonalCoefficients_eq_coefficients (hM : 0 ≤ M) :
    diagonalCoefficients M = SphericalAnsatz.coefficients (ansatzData hM) := by
  funext y i
  fin_cases i <;> rfl

/-- **The exterior metric is the ansatz**: the two matrices of coefficients agree at every
point. -/
theorem coefficient_eq_ansatz (hM : 0 ≤ M) :
    (metric hM).coefficient = (SphericalAnsatz.metric (ansatzData hM)).coefficient := by
  funext y
  rw [coefficient_eq_diagonal hM, SphericalAnsatz.coefficient_metric,
    diagonalCoefficients_eq_coefficients hM]

/-! ### The partial derivatives of `A` and `B` -/

/-- `∂_t A = 0`. -/
theorem partialT_ansatzA (hM : 0 ≤ M) : partialT (ansatzData hM).A = fun _ _ => 0 := by
  funext t r
  simp [SphericalAnsatz.partialT, ansatzData]

/-- `∂_t B = 0`. -/
theorem partialT_ansatzB (hM : 0 ≤ M) : partialT (ansatzData hM).B = fun _ _ => 0 := by
  funext t r
  simp [SphericalAnsatz.partialT, ansatzData]

private theorem hasDerivAt_ansatzA (M : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => (s - 2 * M) / s) (2 * M / r ^ 2) r := by
  refine (((hasDerivAt_id r).sub_const (2 * M)).div (hasDerivAt_id r) hr).congr_deriv ?_
  simp only [id]
  field_simp
  ring

private theorem hasDerivAt_ansatzB (M : ℝ) {r : ℝ} (hr : r - 2 * M ≠ 0) :
    HasDerivAt (fun s : ℝ => s / (s - 2 * M)) (-(2 * M) / (r - 2 * M) ^ 2) r := by
  refine ((hasDerivAt_id r).div ((hasDerivAt_id r).sub_const (2 * M)) hr).congr_deriv ?_
  simp only [id]
  field_simp
  ring

/-- `∂_r A = 2M/r²`. -/
theorem partialR_ansatzA (hM : 0 ≤ M) (t : ℝ) {r : ℝ} (hr : r ≠ 0) :
    partialR (ansatzData hM).A t r = 2 * M / r ^ 2 :=
  (hasDerivAt_ansatzA M hr).deriv

/-- `∂_r B = −2M/(r − 2M)²`. -/
theorem partialR_ansatzB (hM : 0 ≤ M) (t : ℝ) {r : ℝ} (hr : r ≠ 2 * M) :
    partialR (ansatzData hM).B t r = -(2 * M) / (r - 2 * M) ^ 2 :=
  (hasDerivAt_ansatzB M (sub_ne_zero.mpr hr)).deriv

/-- `∂_r² A = −4M/r³`. -/
theorem partialR_partialR_ansatzA (hM : 0 ≤ M) (t : ℝ) {r : ℝ} (hr : r ≠ 0) :
    partialR (partialR (ansatzData hM).A) t r = -(4 * M) / r ^ 3 := by
  have h : HasDerivAt (fun s : ℝ => 2 * M / s ^ 2) (-(4 * M) / r ^ 3) r := by
    refine ((hasDerivAt_const r (2 * M)).div ((hasDerivAt_id r).pow 2)
      (pow_ne_zero 2 hr)).congr_deriv ?_
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  refine (h.congr_of_eventuallyEq ?_).deriv
  filter_upwards [isOpen_ne.mem_nhds hr] with s hs using partialR_ansatzA hM t hs

/-- `∂_r² B = 4M/(r − 2M)³`. -/
theorem partialR_partialR_ansatzB (hM : 0 ≤ M) (t : ℝ) {r : ℝ} (hr : r ≠ 2 * M) :
    partialR (partialR (ansatzData hM).B) t r = 4 * M / (r - 2 * M) ^ 3 := by
  have hr' : r - 2 * M ≠ 0 := sub_ne_zero.mpr hr
  have h : HasDerivAt (fun s : ℝ => -(2 * M) / (s - 2 * M) ^ 2) (4 * M / (r - 2 * M) ^ 3) r := by
    refine ((hasDerivAt_const r (-(2 * M))).div (((hasDerivAt_id r).sub_const (2 * M)).pow 2)
      (pow_ne_zero 2 hr')).congr_deriv ?_
    simp only [id, Pi.pow_apply]
    field_simp
    ring
  refine (h.congr_of_eventuallyEq ?_).deriv
  filter_upwards [isOpen_ne.mem_nhds hr] with s hs using partialR_ansatzB hM t hs

/-- `∂_t² A = 0`. -/
theorem partialT_partialT_ansatzA (hM : 0 ≤ M) :
    partialT (partialT (ansatzData hM).A) = fun _ _ => 0 := by
  rw [partialT_ansatzA, SphericalAnsatz.partialT_const]

/-- `∂_t² B = 0`. -/
theorem partialT_partialT_ansatzB (hM : 0 ≤ M) :
    partialT (partialT (ansatzData hM).B) = fun _ _ => 0 := by
  rw [partialT_ansatzB, SphericalAnsatz.partialT_const]

/-- `∂_t ∂_r A = 0`. -/
theorem partialT_partialR_ansatzA (hM : 0 ≤ M) :
    partialT (partialR (ansatzData hM).A) = fun _ _ => 0 := by
  funext t r
  simp [SphericalAnsatz.partialT, SphericalAnsatz.partialR, ansatzData]

/-- `∂_t ∂_r B = 0`. -/
theorem partialT_partialR_ansatzB (hM : 0 ≤ M) :
    partialT (partialR (ansatzData hM).B) = fun _ _ => 0 := by
  funext t r
  simp [SphericalAnsatz.partialT, SphericalAnsatz.partialR, ansatzData]

/-! ### The vacuum equations in the co-ordinates -/

/-- **The Schwarzschild field is Ricci flat** (Landau–Lifshitz, (100.14)): `R_{ik} = 0` at every
point of the exterior domain. -/
theorem ricciOf_eq_zero (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M) (j k : Fin 4) :
    ricciOf (metric hM).coefficient x j k = 0 := by
  have hr : 2 * M < x 1 := hx.1
  have h0 : x 1 ≠ 0 := by linarith
  have h1 : x 1 ≠ 2 * M := hr.ne'
  have h2 : x 1 - 2 * M ≠ 0 := sub_ne_zero.mpr h1
  rw [coefficient_eq_ansatz hM, SphericalAnsatz.ricciOf_eq (mem_ansatzDomain hM hx)]
  fin_cases j <;> fin_cases k <;>
  · simp only [SphericalAnsatz.ricci, partialT_ansatzA, partialT_ansatzB,
      SphericalAnsatz.partialT_const, partialR_ansatzA hM _ h0, partialR_ansatzB hM _ h1,
      partialR_partialR_ansatzA hM _ h0, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Matrix.cons_val]
    all_goals simp only [ansatzData]
    all_goals field_simp
    all_goals ring

/-- The scalar curvature of the Schwarzschild field vanishes on the exterior domain. -/
theorem scalarOf_eq_zero (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M) :
    scalarOf (metric hM).coefficient x = 0 := by
  simp [scalarOf, ricciOf_eq_zero hM hx]

/-- The Einstein tensor of the Schwarzschild field vanishes on the exterior domain. -/
theorem einsteinOf_eq_zero (hM : 0 ≤ M) {x : MinkowskiModel 3} (hx : x ∈ domain M)
    (i k : Fin 4) : einsteinOf (metric hM).coefficient x i k = 0 := by
  simp [einsteinOf, ricciOf_eq_zero hM hx, scalarOf_eq_zero hM hx]

/-- **The Schwarzschild field solves the vacuum Einstein equations** `G_{ik} = κ · 0` on the
exterior domain, in the co-ordinates, for every coupling constant `κ`. -/
theorem isEinstein_zero (hM : 0 ≤ M) (κ : ℝ) : (metric hM).IsEinstein κ 0 0 := by
  intro x hx i k
  simp [einsteinOf_eq_zero hM hx]

/-! ### The native tensors -/

/-- The native Einstein tensor of the Schwarzschild field vanishes on co-ordinate fields. -/
theorem einstein_chartField (hM : 0 ≤ M) (x y : domain M) (i k : Fin 4) :
    (metric hM).toLorentzMetric.einstein y (chartField (physicalChart x) (Pi.single i 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 := by
  rw [(metric hM).toLorentzMetric_einstein_chartField x y, einsteinOf_eq_zero hM y.property]

/-- **The native vacuum Einstein equations**: the Schwarzschild field satisfies
`G + 0 · g = κ · 0` on the exterior domain for every coupling constant `κ`. -/
theorem satisfiesEinstein_zero (hM : 0 ≤ M) (κ : ℝ) :
    (metric hM).toLorentzMetric.SatisfiesEinstein κ 0 0 := by
  intro y
  refine LorentzMetric.ext_chartField (CoordinateMetric.physicalChart_mem y) (by simp) fun i => ?_
  refine LorentzMetric.ext_chartField (CoordinateMetric.physicalChart_mem y) (by simp) fun k => ?_
  simp only [add_apply, smul_apply, smul_eq_mul, zero_mul, add_zero]
  rw [einstein_chartField hM y y i k]
  simp

/-- The native Ricci tensor of the Schwarzschild field vanishes on co-ordinate fields. -/
theorem ricci_chartField (hM : 0 ≤ M) (x y : domain M) (j k : Fin 4) :
    (metric hM).toLorentzMetric.ricci y (chartField (physicalChart x) (Pi.single j 1) y)
      (chartField (physicalChart x) (Pi.single k 1) y) = 0 := by
  rw [(metric hM).toLorentzMetric_ricci_chartField x y, ricciOf_eq_zero hM y.property]

/-- **The native Ricci tensor of the Schwarzschild field vanishes** at every point of the
exterior domain, on all pairs of tangent vectors. -/
theorem ricci_eq_zero (hM : 0 ≤ M) (y : domain M) (u w : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) :
    (metric hM).toLorentzMetric.ricci y u w = 0 := by
  have he (i : Fin 4) : (Pi.single i 1 : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) =
      chartField (physicalChart y) (Pi.single i 1) y :=
    (CoordinateMetric.physicalChart_chartField y y _).symm
  have hc (j k : Fin 4) : (metric hM).toLorentzMetric.ricci y
      (Pi.single j 1 : TangentSpace 𝓘(ℝ, MinkowskiModel 3) y) (Pi.single k 1) = 0 := by
    have h := ricci_chartField hM y y j k
    rwa [← he, ← he] at h
  let B : MinkowskiModel 3 →L[ℝ] MinkowskiModel 3 →L[ℝ] ℝ := (metric hM).toLorentzMetric.ricci y
  have hB (j k : Fin 4) : B (Pi.single j 1) (Pi.single k 1) = 0 := hc j k
  have key (u w : MinkowskiModel 3) : B u w = 0 := by
    rw [pi_eq_sum_univ' u, pi_eq_sum_univ' w]
    simp only [map_sum, map_smul, _root_.sum_apply, smul_apply, hB, smul_zero,
      Finset.sum_const_zero]
  exact key u w

/-! ### Regression: flat space for `M = 0` -/

/-- For `M = 0` the coefficient `A` is `1` at every radius of the ansatz. -/
theorem ansatzData_zero_A {t r : ℝ} (hr : r ∈ (ansatzData (le_refl (0 : ℝ))).J) :
    (ansatzData (le_refl (0 : ℝ))).A t r = 1 := by
  have h : 0 < r := by simpa [ansatzData] using hr
  simp [ansatzData, h.ne']

/-- For `M = 0` the coefficient `B` is `1` at every radius of the ansatz. -/
theorem ansatzData_zero_B {t r : ℝ} (hr : r ∈ (ansatzData (le_refl (0 : ℝ))).J) :
    (ansatzData (le_refl (0 : ℝ))).B t r = 1 := by
  have h : 0 < r := by simpa [ansatzData] using hr
  simp [ansatzData, h.ne']

/-- For `M = 0` the ansatz has the sets of times and radii of flat space, `ℝ × (0, ∞)`. -/
theorem ansatzData_zero_sets :
    (ansatzData (le_refl (0 : ℝ))).I = SphericalAnsatz.Data.flat.I ∧
      (ansatzData (le_refl (0 : ℝ))).J = SphericalAnsatz.Data.flat.J := by
  refine ⟨rfl, ?_⟩
  simp [ansatzData, SphericalAnsatz.Data.flat]

/-- For `M = 0` the exterior domain is the domain `r > 0`, `0 < θ < π` of flat space. -/
theorem domain_zero : domain 0 = SphericalAnsatz.domain SphericalAnsatz.Data.flat := by
  ext x
  change 2 * 0 < x 1 ∧ 0 < x 2 ∧ x 2 < Real.pi ↔
    x 0 ∈ univ ∧ x 1 ∈ Ioi 0 ∧ 0 < x 2 ∧ x 2 < Real.pi
  simp

/-- For `M = 0` the exterior metric is flat space in spherical co-ordinates on its domain. -/
theorem coefficient_zero {x : MinkowskiModel 3} (hx : x ∈ domain 0) :
    (metric (le_refl (0 : ℝ))).coefficient x =
      (SphericalAnsatz.metric SphericalAnsatz.Data.flat).coefficient x := by
  have h : x 1 ≠ 0 := by
    have : 2 * 0 < x 1 := hx.1
    linarith
  rw [coefficient_eq_diagonal, SphericalAnsatz.coefficient_metric]
  congr 1
  funext i
  fin_cases i <;> simp [diagonalCoefficients, SphericalAnsatz.coefficients,
    SphericalAnsatz.Data.flat, h]

end ProjectAinos.GeneralRelativity.SchwarzschildExterior
