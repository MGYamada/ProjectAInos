/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.GeneralRelativity.SchwarzschildExterior
public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
public import ProjectAinos.SmoothGeometry.Lorentzian.CoordinateGeodesic
import Mathlib.Tactic.FieldSimp

/-!
# The effective potential and the circular orbits of the Schwarzschild field

In the co-ordinates `(t, r, θ, φ)` of the exterior Schwarzschild field of mass `M ≥ 0`
(`SchwarzschildExterior.metric`), the matrix of coefficients is diagonal at every point
(`coefficient_eq_diagonal`), and its Christoffel symbols on the domain `r > 2M`, `0 < θ < π` are
the table `christoffel` (`christoffelOf_metric`): `Γ^0_{01} = M/(r(r − 2M))`,
`Γ^1_{00} = M(r − 2M)/r³`, `Γ^1_{11} = −M/(r(r − 2M))`, `Γ^1_{22} = −(r − 2M)`,
`Γ^1_{33} = −(r − 2M) sin²θ`, `Γ^2_{12} = Γ^3_{13} = 1/r`, `Γ^2_{33} = −sin θ cos θ`,
`Γ^3_{23} = cos θ/sin θ`, the symmetric entries, and `0` otherwise.

The radial motion in the equatorial plane is the motion in the effective potential
`V(r) = (1 − 2M/r)(κ + L²/r²)` (`effectivePotential`), with `κ = 1` for a body and `κ = 0` for
light: `(dr/dτ)² = E² − V(r)` (Landau–Lifshitz, §101, (101.2)–(101.6)). This first integral is
not formalized here; for the circular orbits its two conditions `V(R) = E²` and `V'(R) = 0` are
(`effectivePotential_circular`, `deriv_effectivePotential_circular`).

* `deriv_effectivePotential`: `V' = 2(Mκr² − L²r + 3ML²)/r⁴`.
* `deriv_effectivePotential_eq_zero_iff`, `three_mul_lt_of_deriv_effectivePotential_eq_zero`:
  for a body, `V'(R) = 0` exactly when `L²(R − 3M) = MR²`, and then `R > 3M`.
* `deriv_deriv_effectivePotential_of_deriv_eq_zero`, `deriv_deriv_effectivePotential_pos_iff`:
  at a circular orbit `V''(R) = 2M(R − 6M)/(R³(R − 3M))`, so the orbit is stable exactly when
  `R > 6M`: the innermost stable circular orbit is at `r = 6M` (the problem of §101).
* `deriv_effectivePotential_light_eq_zero_iff`, `isMaxOn_effectivePotential_light`: for light,
  `V' = 2L²(3M − r)/r⁴` vanishes only at `r = 3M`, where `V` has its maximum.
* `isGeodesicOn_circular`, `form_curveVelocity_circular`: for `R > 3M`, with
  `α = 1/√(1 − 3M/R)` and `Ω = α √(M/R³)`, the curve `s ↦ (α s, R, π/2, Ω s)` is a geodesic
  parametrized by proper time; for `M = 0` it is a body at rest (`circularOrbit_zero`).
* `circularEnergy_sq`, `circularAngularMomentum_sq`: its energy `E = (1 − 2M/R) α` and angular
  momentum `L = R² Ω` satisfy `E² = (1 − 2M/R)²/(1 − 3M/R)` and `L² = MR²/(R − 3M)`, and
  `E² = V(R)`, `V'(R) = 0` (`effectivePotential_circular`, `deriv_effectivePotential_circular`).
* `isGeodesicOn_photonCircle`, `form_curveVelocity_photonCircle`: for `M > 0` the curve
  `s ↦ (a s, 3M, π/2, a s/(3√3 M))` is a null geodesic for every `a`.
-/

@[expose] public section

noncomputable section

open ContinuousLinearMap Set Filter TopologicalSpace
open scoped ContDiff Topology

namespace ProjectAinos.GeneralRelativity.SchwarzschildExterior

open SmoothGeometry Minkowski
open CoordinateMetric (christoffelOf physicalChart)
open LorentzMetric (curveVelocity chartField)

variable {M : ℝ}

/-! ### The Christoffel symbols -/

/-- The diagonal coefficients `(−(r − 2M)/r, r/(r − 2M), r², r² sin²θ)` of the exterior metric at
the point `y`. -/
def diagonalCoefficients (M : ℝ) (y : MinkowskiModel 3) : Fin 4 → ℝ :=
  ![-((y 1 - 2 * M) / y 1), y 1 / (y 1 - 2 * M), y 1 ^ 2, y 1 ^ 2 * Real.sin (y 2) ^ 2]

/-- The matrix of coefficients of the exterior metric is `diag(diagonalCoefficients M y)` at every
point. -/
theorem coefficient_eq_diagonal (hM : 0 ≤ M) (y : MinkowskiModel 3) :
    (metric hM).coefficient y = Matrix.diagonal (diagonalCoefficients M y) := by
  ext i j
  simp only [CoordinateMetric.coefficient, Matrix.of_apply, metric_form, form_apply,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [diagonalCoefficients]

/-- No diagonal coefficient vanishes on the domain. -/
theorem diagonalCoefficients_ne_zero (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M)
    (i : Fin 4) : diagonalCoefficients M y i ≠ 0 := by
  have hr : 2 * M < y 1 := hy.1
  have hs : 0 < Real.sin (y 2) := Real.sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2
  have h0 : 0 < y 1 := by linarith
  have h1 : 0 < y 1 - 2 * M := by linarith
  fin_cases i <;> simp [diagonalCoefficients, h0.ne', h1.ne', hs.ne']

/-- The partial derivatives `∂_b c_a` of the diagonal coefficients, indexed by `a` and then `b`. -/
def coefficientDerivative (M : ℝ) (y : MinkowskiModel 3) : Fin 4 → Fin 4 → ℝ :=
  ![![0, -(2 * M / y 1 ^ 2), 0, 0], ![0, -(2 * M / (y 1 - 2 * M) ^ 2), 0, 0],
    ![0, 2 * y 1, 0, 0],
    ![0, 2 * y 1 * Real.sin (y 2) ^ 2, 2 * y 1 ^ 2 * Real.sin (y 2) * Real.cos (y 2), 0]]

/-- A function of one co-ordinate `z ↦ f(z a)` has the derivative `f'(y a) dxᵃ`. -/
theorem hasFDerivAt_coord {f : ℝ → ℝ} {f' : ℝ} (a : Fin 4) {y : MinkowskiModel 3}
    (hf : HasDerivAt f f' (y a)) :
    HasFDerivAt (fun z : MinkowskiModel 3 => f (z a))
      (f' • (proj a : MinkowskiModel 3 →L[ℝ] ℝ)) y :=
  hf.comp_hasFDerivAt y (hasFDerivAt_apply a y)

/-- The partial derivatives of the diagonal coefficients on the domain are
`coefficientDerivative`. -/
theorem fderiv_diagonalCoefficients (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M)
    (a b : Fin 4) :
    fderiv ℝ (fun z => diagonalCoefficients M z a) y (Pi.single b 1) =
      coefficientDerivative M y a b := by
  have hr : 2 * M < y 1 := hy.1
  have h0 : y 1 ≠ 0 := by linarith
  have h1 : y 1 - 2 * M ≠ 0 := by linarith
  fin_cases a
  · have hd : HasDerivAt (fun r : ℝ => -((r - 2 * M) / r)) (-(2 * M / y 1 ^ 2)) (y 1) := by
      have := (((hasDerivAt_id (y 1)).sub_const (2 * M)).div (hasDerivAt_id (y 1)) h0).neg
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    rw [show (fun z => diagonalCoefficients M z ((fun i => i) ⟨0, by norm_num⟩)) =
      fun z : MinkowskiModel 3 => -((z 1 - 2 * M) / z 1) from rfl,
      (hasFDerivAt_coord 1 hd).fderiv]
    fin_cases b <;> simp [coefficientDerivative]
  · have hd : HasDerivAt (fun r : ℝ => r / (r - 2 * M)) (-(2 * M / (y 1 - 2 * M) ^ 2))
        (y 1) := by
      have := (hasDerivAt_id (y 1)).div ((hasDerivAt_id (y 1)).sub_const (2 * M)) h1
      refine this.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    rw [show (fun z => diagonalCoefficients M z ((fun i => i) ⟨1, by norm_num⟩)) =
      fun z : MinkowskiModel 3 => z 1 / (z 1 - 2 * M) from rfl,
      (hasFDerivAt_coord 1 hd).fderiv]
    fin_cases b <;> simp [coefficientDerivative]
  · have hd : HasDerivAt (fun r : ℝ => r ^ 2) (2 * y 1) (y 1) := by
      simpa using hasDerivAt_pow 2 (y 1)
    rw [show (fun z => diagonalCoefficients M z ((fun i => i) ⟨2, by norm_num⟩)) =
      fun z : MinkowskiModel 3 => z 1 ^ 2 from rfl,
      (hasFDerivAt_coord 1 hd).fderiv]
    fin_cases b <;> simp [coefficientDerivative]
  · have hd1 : HasDerivAt (fun r : ℝ => r ^ 2) (2 * y 1) (y 1) := by
      simpa using hasDerivAt_pow 2 (y 1)
    have hd2 : HasDerivAt (fun θ : ℝ => Real.sin θ ^ 2)
        (2 * Real.sin (y 2) * Real.cos (y 2)) (y 2) := by
      have := (Real.hasDerivAt_sin (y 2)).pow 2
      convert this using 1
      ring
    rw [show (fun z => diagonalCoefficients M z ((fun i => i) ⟨3, by norm_num⟩)) =
      fun z : MinkowskiModel 3 => z 1 ^ 2 * Real.sin (z 2) ^ 2 from rfl,
      ((hasFDerivAt_coord 1 hd1).fun_mul (hasFDerivAt_coord 2 hd2)).fderiv]
    fin_cases b <;> simp [coefficientDerivative] <;> ring

/-- The Christoffel symbols `Γ^k_{ij}` of the exterior metric, indexed by `k`, `i`, `j`. -/
def christoffel (M : ℝ) (y : MinkowskiModel 3) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  ![![![0, M / (y 1 * (y 1 - 2 * M)), 0, 0], ![M / (y 1 * (y 1 - 2 * M)), 0, 0, 0],
      ![0, 0, 0, 0], ![0, 0, 0, 0]],
    ![![M * (y 1 - 2 * M) / y 1 ^ 3, 0, 0, 0], ![0, -(M / (y 1 * (y 1 - 2 * M))), 0, 0],
      ![0, 0, -(y 1 - 2 * M), 0], ![0, 0, 0, -((y 1 - 2 * M) * Real.sin (y 2) ^ 2)]],
    ![![0, 0, 0, 0], ![0, 0, 1 / y 1, 0], ![0, 1 / y 1, 0, 0],
      ![0, 0, 0, -(Real.sin (y 2) * Real.cos (y 2))]],
    ![![0, 0, 0, 0], ![0, 0, 0, 1 / y 1], ![0, 0, 0, Real.cos (y 2) / Real.sin (y 2)],
      ![0, 1 / y 1, Real.cos (y 2) / Real.sin (y 2), 0]]]

/-- The Christoffel symbols of the exterior metric on the domain, from the diagonal formula
`Γ^k_{ij} = (δ_{kj} ∂_i c_k + δ_{ki} ∂_j c_k − δ_{ij} ∂_k c_i)/(2 c_k)`. -/
theorem christoffelOf_metric_eq_formula (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M)
    (k i j : Fin 4) :
    christoffelOf (metric hM).coefficient y k i j =
      ((if k = j then coefficientDerivative M y k i else 0) +
        (if k = i then coefficientDerivative M y k j else 0) -
        (if i = j then coefficientDerivative M y i k else 0)) /
          (2 * diagonalCoefficients M y k) := by
  rw [show (metric hM).coefficient = fun z => Matrix.diagonal (diagonalCoefficients M z) from
    funext (coefficient_eq_diagonal hM),
    CoordinateMetric.christoffelOf_diagonal _ y (diagonalCoefficients_ne_zero hM hy)]
  simp only [fderiv_diagonalCoefficients hM hy]

/-- The Christoffel symbols of the exterior metric on the domain are the table `christoffel`. -/
theorem christoffelOf_metric (hM : 0 ≤ M) {y : MinkowskiModel 3} (hy : y ∈ domain M)
    (k i j : Fin 4) :
    christoffelOf (metric hM).coefficient y k i j = christoffel M y k i j := by
  have hr : 2 * M < y 1 := hy.1
  have hs : Real.sin (y 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hy.2.1 hy.2.2).ne'
  have h0 : y 1 ≠ 0 := by linarith
  have h1 : y 1 - 2 * M ≠ 0 := by linarith
  rw [christoffelOf_metric_eq_formula hM hy]
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    simp [coefficientDerivative, christoffel, diagonalCoefficients] <;> field_simp
  all_goals ring

/-! ### The effective potential -/

/-- The effective potential `V(r) = (1 − 2M/r)(κ + L²/r²)` of the radial motion, with `κ = 1` for
a body and `κ = 0` for light. For a body it is the square `(U/m)²` of the effective potential `U`
of Landau–Lifshitz, §101, with `r_g = 2M` and the angular momentum `L` per unit mass. -/
def effectivePotential (M κ L r : ℝ) : ℝ := (1 - 2 * M / r) * (κ + L ^ 2 / r ^ 2)

/-- The derivative of the effective potential is `V' = 2(Mκr² − L²r + 3ML²)/r⁴`. -/
theorem hasDerivAt_effectivePotential (M κ L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (effectivePotential M κ L)
      (2 * (M * κ * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2) / r ^ 4) r := by
  have h1 : HasDerivAt (fun r : ℝ => 1 - 2 * M / r) (2 * M / r ^ 2) r := by
    have := ((hasDerivAt_const r (2 * M)).div (hasDerivAt_id r) hr).const_sub 1
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have h2 : HasDerivAt (fun r : ℝ => κ + L ^ 2 / r ^ 2) (-(2 * L ^ 2 / r ^ 3)) r := by
    have := ((hasDerivAt_const r (L ^ 2)).div (hasDerivAt_pow 2 r)
      (pow_ne_zero 2 hr)).const_add κ
    refine this.congr_deriv ?_
    field_simp
    ring
  refine (h1.mul h2).congr_deriv ?_
  field_simp
  ring

/-- `V'(r) = 2(Mκr² − L²r + 3ML²)/r⁴`. -/
theorem deriv_effectivePotential (M κ L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (effectivePotential M κ L) r =
      2 * (M * κ * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2) / r ^ 4 :=
  (hasDerivAt_effectivePotential M κ L hr).deriv

/-- The second derivative of the effective potential is
`V'' = 2(−2Mκr² + 3L²r − 12ML²)/r⁵`. -/
theorem hasDerivAt_deriv_effectivePotential (M κ L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (deriv (effectivePotential M κ L))
      (2 * (-2 * M * κ * r ^ 2 + 3 * L ^ 2 * r - 12 * M * L ^ 2) / r ^ 5) r := by
  have hev : deriv (effectivePotential M κ L) =ᶠ[𝓝 r]
      fun r => 2 * (M * κ * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2) / r ^ 4 :=
    eventually_of_mem (isOpen_ne.mem_nhds hr) fun s hs => deriv_effectivePotential M κ L hs
  have hp : HasDerivAt (fun r : ℝ => 2 * (M * κ * r ^ 2 - L ^ 2 * r + 3 * M * L ^ 2))
      (2 * (M * κ * (2 * r) - L ^ 2)) r := by
    have := ((((hasDerivAt_pow 2 r).const_mul (M * κ)).sub
      ((hasDerivAt_id r).const_mul (L ^ 2))).add_const (3 * M * L ^ 2)).const_mul 2
    refine this.congr_deriv ?_
    simp
  refine ((hp.div (hasDerivAt_pow 4 r) (pow_ne_zero 4 hr)).congr_of_eventuallyEq hev).congr_deriv
    ?_
  field_simp
  ring

/-- `V''(r) = 2(−2Mκr² + 3L²r − 12ML²)/r⁵`. -/
theorem deriv_deriv_effectivePotential (M κ L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (deriv (effectivePotential M κ L)) r =
      2 * (-2 * M * κ * r ^ 2 + 3 * L ^ 2 * r - 12 * M * L ^ 2) / r ^ 5 :=
  (hasDerivAt_deriv_effectivePotential M κ L hr).deriv

/-- **Circular orbits of a body** (Landau–Lifshitz, §101). The effective potential of a body is
stationary at `R` exactly when `L²(R − 3M) = MR²`. -/
theorem deriv_effectivePotential_eq_zero_iff (L : ℝ) {R : ℝ} (hR : R ≠ 0) :
    deriv (effectivePotential M 1 L) R = 0 ↔ L ^ 2 * (R - 3 * M) = M * R ^ 2 := by
  rw [deriv_effectivePotential M 1 L hR, div_eq_zero_iff, or_iff_left (pow_ne_zero 4 hR)]
  constructor <;> intro h <;> linarith

/-- A circular orbit of a body around a mass `M > 0` has the radius `R > 3M`. -/
theorem three_mul_lt_of_deriv_effectivePotential_eq_zero (hM : 0 < M) {L R : ℝ} (hR : R ≠ 0)
    (h : deriv (effectivePotential M 1 L) R = 0) : 3 * M < R := by
  have h' := (deriv_effectivePotential_eq_zero_iff L hR).mp h
  by_contra hle
  have : L ^ 2 * (R - 3 * M) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg L) (by linarith)
  have : 0 < M * R ^ 2 := mul_pos hM (by positivity)
  linarith

/-- At a circular orbit of a body, `V''(R) = 2M(R − 6M)/(R³(R − 3M))`. -/
theorem deriv_deriv_effectivePotential_of_deriv_eq_zero (hM : 0 < M) {L R : ℝ} (hR : R ≠ 0)
    (h : deriv (effectivePotential M 1 L) R = 0) :
    deriv (deriv (effectivePotential M 1 L)) R = 2 * M * (R - 6 * M) / (R ^ 3 * (R - 3 * M)) := by
  have h3 : R - 3 * M ≠ 0 := by
    have := three_mul_lt_of_deriv_effectivePotential_eq_zero hM hR h
    linarith
  have hL := (deriv_effectivePotential_eq_zero_iff L hR).mp h
  rw [deriv_deriv_effectivePotential M 1 L hR, div_eq_div_iff (pow_ne_zero 5 hR)
    (mul_ne_zero (pow_ne_zero 3 hR) h3)]
  linear_combination 2 * R ^ 3 * (3 * R - 12 * M) * hL

/-- **The innermost stable circular orbit** (Landau–Lifshitz, §101, problem). A circular orbit of
a body is a minimum of the effective potential with `V''(R) > 0` exactly when `R > 6M`. -/
theorem deriv_deriv_effectivePotential_pos_iff (hM : 0 < M) {L R : ℝ} (hR : R ≠ 0)
    (h : deriv (effectivePotential M 1 L) R = 0) :
    0 < deriv (deriv (effectivePotential M 1 L)) R ↔ 6 * M < R := by
  have h3 := three_mul_lt_of_deriv_effectivePotential_eq_zero hM hR h
  have hR0 : 0 < R := by linarith
  have hD : 0 < R ^ 3 * (R - 3 * M) := mul_pos (pow_pos hR0 3) (by linarith)
  rw [deriv_deriv_effectivePotential_of_deriv_eq_zero hM hR h, div_pos_iff_of_pos_right hD]
  constructor
  · intro hp
    by_contra hle
    have : 2 * M * (R - 6 * M) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    linarith
  · intro hlt
    exact mul_pos (by linarith) (by linarith)

/-- For light, `V'(r) = 2L²(3M − r)/r⁴`. -/
theorem deriv_effectivePotential_light (M L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    deriv (effectivePotential M 0 L) r = 2 * L ^ 2 * (3 * M - r) / r ^ 4 := by
  rw [deriv_effectivePotential M 0 L hr]
  ring

/-- **The circular orbit of light** (Landau–Lifshitz, §101). For `L ≠ 0` the effective potential
of light is stationary only at `r = 3M`. -/
theorem deriv_effectivePotential_light_eq_zero_iff {L R : ℝ} (hL : L ≠ 0) (hR : R ≠ 0) :
    deriv (effectivePotential M 0 L) R = 0 ↔ R = 3 * M := by
  rw [deriv_effectivePotential_light M L hR, div_eq_zero_iff, or_iff_left (pow_ne_zero 4 hR),
    mul_eq_zero, or_iff_right (mul_ne_zero two_ne_zero (pow_ne_zero 2 hL)), sub_eq_zero,
    eq_comm]

/-- At `r = 3M` the effective potential of light has `V''(3M) < 0`. -/
theorem deriv_deriv_effectivePotential_light (hM : 0 < M) {L : ℝ} (hL : L ≠ 0) :
    deriv (deriv (effectivePotential M 0 L)) (3 * M) < 0 := by
  rw [deriv_deriv_effectivePotential M 0 L (by positivity)]
  have hL2 : 0 < L ^ 2 := by positivity
  have : 2 * (-2 * M * 0 * (3 * M) ^ 2 + 3 * L ^ 2 * (3 * M) - 12 * M * L ^ 2) =
      -(6 * M * L ^ 2) := by ring
  rw [this, neg_div]
  exact neg_neg_of_pos (by positivity)

/-- For light, `V(r) = L²(r − 2M)/r³`. -/
theorem effectivePotential_light_eq (M L : ℝ) {r : ℝ} (hr : r ≠ 0) :
    effectivePotential M 0 L r = L ^ 2 * (r - 2 * M) / r ^ 3 := by
  unfold effectivePotential
  field_simp
  ring

/-- The effective potential of light has its maximum over `r > 0` at `r = 3M`, since
`r³ − 27M²r + 54M³ = (r − 3M)²(r + 6M)`. -/
theorem isMaxOn_effectivePotential_light (hM : 0 < M) (L : ℝ) :
    IsMaxOn (effectivePotential M 0 L) (Ioi 0) (3 * M) := by
  intro r hr
  have hr : 0 < r := hr
  show effectivePotential M 0 L r ≤ effectivePotential M 0 L (3 * M)
  rw [effectivePotential_light_eq M L hr.ne', effectivePotential_light_eq M L (by positivity),
    div_le_div_iff₀ (pow_pos hr 3) (by positivity)]
  nlinarith [mul_nonneg (mul_nonneg (sq_nonneg L) hM.le)
    (mul_nonneg (sq_nonneg (r - 3 * M)) (by linarith : (0 : ℝ) ≤ r + 6 * M))]

/-! ### Curves with affine co-ordinates -/

/-- A curve whose co-ordinates are the affine line `p + t v` is a geodesic on `univ` when
`Γ^k_{ij} vⁱ vʲ = 0` along it. -/
theorem isGeodesicOn_univ_of_line {σ : LorentzConvention} {d : ℕ}
    {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U) {γ : ℝ → U}
    (p v : MinkowskiModel d) (hγ : ∀ t, (γ t : MinkowskiModel d) = p + t • v)
    (h : ∀ t k, ∑ i, ∑ j, christoffelOf g.coefficient (γ t) k i j * v i * v j = 0) :
    g.toLorentzMetric.IsGeodesicOn univ γ := by
  have he : (fun t => (γ t : MinkowskiModel d)) = fun t => p + t • v := funext hγ
  have hline : ContDiff ℝ 2 (fun t : ℝ => p + t • v) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  have hd : deriv (fun t => (γ t : MinkowskiModel d)) = fun _ => v := by
    rw [he]
    funext t
    simpa using (((hasDerivAt_id t).smul_const v).const_add p).deriv
  rw [g.isGeodesicOn_iff isOpen_univ (by rw [he]; exact hline.contDiffOn)]
  intro t _ k
  rw [hd, deriv_const]
  simpa using h t k

/-- Along a curve with the affine co-ordinates `p + t v`, the squared velocity is
`g_{ij} vⁱ vʲ`. -/
theorem form_curveVelocity_of_line {σ : LorentzConvention} {d : ℕ}
    {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U) {γ : ℝ → U}
    (p v : MinkowskiModel d) (hγ : ∀ t, (γ t : MinkowskiModel d) = p + t • v) (t : ℝ) :
    g.toLorentzMetric.form (γ t) (curveVelocity γ t) (curveVelocity γ t) =
      ∑ i, ∑ j, g.coefficient (γ t) i j * v i * v j := by
  have he : (fun t => (γ t : MinkowskiModel d)) = fun t => p + t • v := funext hγ
  have hv : HasDerivAt (fun t => (γ t : MinkowskiModel d)) v t := by
    rw [he]
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  rw [g.form_curveVelocity hv.differentiableAt, hv.deriv]

/-- Along a curve with the affine co-ordinates `p + t v`, the pairing of a co-ordinate vector `w`
with the velocity is `g_{ij} wⁱ vʲ`. -/
theorem pairing_curveVelocity_of_line {σ : LorentzConvention} {d : ℕ}
    {U : Opens (MinkowskiModel d)} (g : CoordinateMetric σ d U) {γ : ℝ → U}
    (p v : MinkowskiModel d) (hγ : ∀ t, (γ t : MinkowskiModel d) = p + t • v) (t : ℝ) (x : U)
    (w : MinkowskiModel d) :
    g.toLorentzMetric.form (γ t) (chartField (physicalChart x) w (γ t)) (curveVelocity γ t) =
      ∑ i, ∑ j, g.coefficient (γ t) i j * w i * v j := by
  have he : (fun t => (γ t : MinkowskiModel d)) = fun t => p + t • v := funext hγ
  have hv : HasDerivAt (fun t => (γ t : MinkowskiModel d)) v t := by
    rw [he]
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  rw [g.pairing_curveVelocity hv.differentiableAt, hv.deriv]

/-! ### The circular orbits of a body -/

/-- The rate `α = dt/dτ = 1/√(1 − 3M/R)` of the circular orbit of radius `R`. -/
def circularTimeRate (M R : ℝ) : ℝ := 1 / Real.sqrt (1 - 3 * M / R)

/-- The rate `Ω = dφ/dτ = α √(M/R³)` of the circular orbit of radius `R`. -/
def circularAngleRate (M R : ℝ) : ℝ := circularTimeRate M R * Real.sqrt (M / R ^ 3)

/-- `α² = R/(R − 3M)`. -/
theorem circularTimeRate_sq (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    circularTimeRate M R ^ 2 = R / (R - 3 * M) := by
  have hR0 : 0 < R := by linarith
  have hx : 0 < 1 - 3 * M / R := by
    rw [sub_pos, div_lt_one hR0]
    exact hR
  rw [circularTimeRate, div_pow, Real.sq_sqrt hx.le]
  field_simp

/-- `Ω² = α² M/R³`. -/
theorem circularAngleRate_sq (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    circularAngleRate M R ^ 2 = circularTimeRate M R ^ 2 * (M / R ^ 3) := by
  have hR0 : 0 < R := by linarith
  rw [circularAngleRate, mul_pow, Real.sq_sqrt (by positivity)]

/-- Without a mass, `Ω = 0`. -/
theorem circularAngleRate_zero (R : ℝ) : circularAngleRate 0 R = 0 := by
  simp [circularAngleRate]

/-- Without a mass, `α = 1`. -/
theorem circularTimeRate_zero (R : ℝ) : circularTimeRate 0 R = 1 := by
  simp [circularTimeRate]

/-- The points `(α s, R, π/2, Ω s)` with `R > 3M` lie in the domain. -/
theorem mem_domain_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (s : ℝ) :
    (![circularTimeRate M R * s, R, Real.pi / 2, circularAngleRate M R * s] :
      MinkowskiModel 3) ∈ domain M :=
  ⟨by simp; linarith, by simp; positivity, by simp; linarith [Real.pi_pos]⟩

/-- The circular orbit `s ↦ (α s, R, π/2, Ω s)` of radius `R > 3M` in the equatorial plane,
parametrized by its proper time. -/
def circularOrbit (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (s : ℝ) : domain M :=
  ⟨![circularTimeRate M R * s, R, Real.pi / 2, circularAngleRate M R * s],
    mem_domain_circular hM hR s⟩

/-- The co-ordinates of the circular orbit are the affine line `(0, R, π/2, 0) + s (α, 0, 0, Ω)`. -/
theorem circularOrbit_eq_line (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (s : ℝ) :
    (circularOrbit hM hR s : MinkowskiModel 3) =
      ![0, R, Real.pi / 2, 0] + s • ![circularTimeRate M R, 0, 0, circularAngleRate M R] := by
  funext i
  fin_cases i <;> simp [circularOrbit, mul_comm]

/-- **The circular orbits** (Landau–Lifshitz, §101). For `R > 3M` the curve
`s ↦ (α s, R, π/2, Ω s)`, with `α = 1/√(1 − 3M/R)` and `Ω = α √(M/R³)`, is a geodesic of the
exterior metric. -/
theorem isGeodesicOn_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    (metric hM).toLorentzMetric.IsGeodesicOn univ (circularOrbit hM hR) := by
  refine isGeodesicOn_univ_of_line _ _ _ (circularOrbit_eq_line hM hR) fun t k => ?_
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [christoffelOf_metric hM (circularOrbit hM hR t).2]]
  have hΩ := circularAngleRate_sq hM hR
  fin_cases k <;> simp [Fin.sum_univ_four, christoffel, circularOrbit]
  linear_combination (-(R - 2 * M)) * hΩ

/-- The circular orbit is parametrized by its proper time: `g(γ̇, γ̇) = −1`. -/
theorem form_curveVelocity_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (t : ℝ) :
    (metric hM).toLorentzMetric.form (circularOrbit hM hR t)
      (curveVelocity (circularOrbit hM hR) t) (curveVelocity (circularOrbit hM hR) t) = -1 := by
  rw [form_curveVelocity_of_line _ _ _ (circularOrbit_eq_line hM hR), coefficient_eq_diagonal]
  have hR0 : 0 < R := by linarith
  have h3 : R - 3 * M ≠ 0 := by linarith
  have hα := circularTimeRate_sq hM hR
  have hΩ := circularAngleRate_sq hM hR
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, diagonalCoefficients, circularOrbit]
  have hα' : circularTimeRate M R ^ 2 * (R - 3 * M) = R := by
    rw [hα]
    field_simp
  calc -((R - 2 * M) / R * circularTimeRate M R * circularTimeRate M R) +
        R ^ 2 * circularAngleRate M R * circularAngleRate M R =
        -(circularTimeRate M R ^ 2 * (R - 3 * M)) / R := by
        rw [show R ^ 2 * circularAngleRate M R * circularAngleRate M R =
          R ^ 2 * circularAngleRate M R ^ 2 by ring, hΩ]
        field_simp
        ring
    _ = -1 := by
        rw [hα']
        field_simp

/-- Without a mass, the circular orbit is a body at rest: `s ↦ (s, R, π/2, 0)`. -/
theorem circularOrbit_zero {R : ℝ} (hR : 3 * 0 < R) (s : ℝ) :
    (circularOrbit le_rfl hR s : MinkowskiModel 3) = ![s, R, Real.pi / 2, 0] := by
  simp [circularOrbit, circularTimeRate_zero, circularAngleRate_zero]

/-- The pairing of `∂_t` with the velocity of the circular orbit is `−E = −(1 − 2M/R) α`. -/
theorem pairing_time_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (t : ℝ) :
    (metric hM).toLorentzMetric.form (circularOrbit hM hR t)
      (chartField (physicalChart x₀) (Pi.single 0 1) (circularOrbit hM hR t))
      (curveVelocity (circularOrbit hM hR) t) = -((1 - 2 * M / R) * circularTimeRate M R) := by
  rw [pairing_curveVelocity_of_line _ _ _ (circularOrbit_eq_line hM hR), coefficient_eq_diagonal]
  have hR0 : R ≠ 0 := by linarith
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, diagonalCoefficients, circularOrbit]
  exact Or.inl (by rw [sub_div, div_self hR0])

/-- The pairing of `∂_φ` with the velocity of the circular orbit is the angular momentum
`L = R² Ω`. -/
theorem pairing_angle_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) (x₀ : domain M) (t : ℝ) :
    (metric hM).toLorentzMetric.form (circularOrbit hM hR t)
      (chartField (physicalChart x₀) (Pi.single 3 1) (circularOrbit hM hR t))
      (curveVelocity (circularOrbit hM hR) t) = R ^ 2 * circularAngleRate M R := by
  rw [pairing_curveVelocity_of_line _ _ _ (circularOrbit_eq_line hM hR), coefficient_eq_diagonal]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, diagonalCoefficients, circularOrbit]

/-- The energy of the circular orbit: `E² = (1 − 2M/R)²/(1 − 3M/R)`. -/
theorem circularEnergy_sq (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    ((1 - 2 * M / R) * circularTimeRate M R) ^ 2 = (1 - 2 * M / R) ^ 2 / (1 - 3 * M / R) := by
  have hR0 : 0 < R := by linarith
  have h3 : R - 3 * M ≠ 0 := by linarith
  rw [mul_pow, circularTimeRate_sq hM hR]
  field_simp

/-- The angular momentum of the circular orbit: `L² = MR²/(R − 3M)`. -/
theorem circularAngularMomentum_sq (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    (R ^ 2 * circularAngleRate M R) ^ 2 = M * R ^ 2 / (R - 3 * M) := by
  have hR0 : 0 < R := by linarith
  have h3 : R - 3 * M ≠ 0 := by linarith
  rw [mul_pow, circularAngleRate_sq hM hR, circularTimeRate_sq hM hR]
  field_simp

/-- With the angular momentum `L = R² Ω` of the circular orbit, `V'(R) = 0`. -/
theorem deriv_effectivePotential_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    deriv (effectivePotential M 1 (R ^ 2 * circularAngleRate M R)) R = 0 := by
  have hR0 : 0 < R := by linarith
  have h3 : R - 3 * M ≠ 0 := by linarith
  rw [deriv_effectivePotential_eq_zero_iff _ hR0.ne', circularAngularMomentum_sq hM hR,
    div_mul_cancel₀ _ h3]

/-- With the angular momentum `L = R² Ω` of the circular orbit, `V(R) = E²`: the radial velocity
`(dr/dτ)² = E² − V(R)` vanishes. -/
theorem effectivePotential_circular (hM : 0 ≤ M) {R : ℝ} (hR : 3 * M < R) :
    effectivePotential M 1 (R ^ 2 * circularAngleRate M R) R =
      ((1 - 2 * M / R) * circularTimeRate M R) ^ 2 := by
  have hR0 : 0 < R := by linarith
  rw [effectivePotential, circularAngularMomentum_sq hM hR, circularEnergy_sq hM hR,
    one_sub_div hR0.ne', one_sub_div hR0.ne']
  have h3' : R - M * 3 ≠ 0 := (by linarith : 0 < R - M * 3).ne'
  field_simp
  ring

/-! ### The circular orbit of light -/

/-- The rate `dφ/ds = a/(3√3 M)` of the circular light orbit at `r = 3M`. -/
def photonAngleRate (M a : ℝ) : ℝ := a / (3 * Real.sqrt 3 * M)

/-- `(a/(3√3 M))² = a²/(27M²)`. -/
theorem photonAngleRate_sq (M a : ℝ) :
    photonAngleRate M a ^ 2 = a ^ 2 / (27 * M ^ 2) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [photonAngleRate, div_pow, mul_pow, mul_pow, h3]
  ring

/-- The points `(a s, 3M, π/2, a s/(3√3 M))` with `M > 0` lie in the domain. -/
theorem mem_domain_photon (hM : 0 < M) (a s : ℝ) :
    (![a * s, 3 * M, Real.pi / 2, photonAngleRate M a * s] : MinkowskiModel 3) ∈ domain M :=
  ⟨by simp; linarith, by simp; positivity, by simp; linarith [Real.pi_pos]⟩

/-- The circular light orbit `s ↦ (a s, 3M, π/2, a s/(3√3 M))` at the radius `3M`. -/
def photonOrbit (hM : 0 < M) (a s : ℝ) : domain M :=
  ⟨![a * s, 3 * M, Real.pi / 2, photonAngleRate M a * s], mem_domain_photon hM a s⟩

/-- The co-ordinates of the light orbit are the affine line `(0, 3M, π/2, 0) + s (a, 0, 0, b)`. -/
theorem photonOrbit_eq_line (hM : 0 < M) (a s : ℝ) :
    (photonOrbit hM a s : MinkowskiModel 3) =
      ![0, 3 * M, Real.pi / 2, 0] + s • ![a, 0, 0, photonAngleRate M a] := by
  funext i
  fin_cases i <;> simp [photonOrbit, mul_comm]

/-- **The circular orbit of light** (Landau–Lifshitz, §101). For `M > 0` and every `a` the curve
`s ↦ (a s, 3M, π/2, a s/(3√3 M))` is a geodesic of the exterior metric. -/
theorem isGeodesicOn_photonCircle (hM : 0 < M) (a : ℝ) :
    (metric hM.le).toLorentzMetric.IsGeodesicOn univ (photonOrbit hM a) := by
  refine isGeodesicOn_univ_of_line _ _ _ (photonOrbit_eq_line hM a) fun t k => ?_
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [christoffelOf_metric hM.le (photonOrbit hM a t).2]]
  have hb := photonAngleRate_sq M a
  have hM0 : M ≠ 0 := hM.ne'
  fin_cases k <;> simp [Fin.sum_univ_four, christoffel, photonOrbit]
  rw [mul_assoc (2 * M - 3 * M), ← sq, hb]
  field_simp
  ring

/-- The circular light orbit is null: `g(γ̇, γ̇) = 0`. -/
theorem form_curveVelocity_photonCircle (hM : 0 < M) (a t : ℝ) :
    (metric hM.le).toLorentzMetric.form (photonOrbit hM a t)
      (curveVelocity (photonOrbit hM a) t) (curveVelocity (photonOrbit hM a) t) = 0 := by
  rw [form_curveVelocity_of_line _ _ _ (photonOrbit_eq_line hM a), coefficient_eq_diagonal]
  have hb := photonAngleRate_sq M a
  have hM0 : M ≠ 0 := hM.ne'
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, diagonalCoefficients, photonOrbit]
  rw [mul_assoc ((3 * M) ^ 2), ← sq, hb]
  field_simp
  ring

/-! ### Instances -/

/- For `M = 1` the radius `R = 12` carries a circular orbit with `L = 4`, and it is stable. -/
example : deriv (effectivePotential 1 1 4) 12 = 0 := by
  rw [deriv_effectivePotential_eq_zero_iff 4 (by norm_num)]
  norm_num

example : 0 < deriv (deriv (effectivePotential 1 1 4)) 12 := by
  have h : deriv (effectivePotential 1 1 4) 12 = 0 := by
    rw [deriv_effectivePotential_eq_zero_iff 4 (by norm_num)]
    norm_num
  rw [deriv_deriv_effectivePotential_pos_iff one_pos (by norm_num) h]
  norm_num

/- The circular orbit of radius `4` around the mass `1` is a geodesic. -/
example : (metric zero_le_one).toLorentzMetric.IsGeodesicOn univ
    (circularOrbit zero_le_one (by norm_num : 3 * (1 : ℝ) < 4)) :=
  isGeodesicOn_circular zero_le_one _

/- The same angular momentum `L = 4` also gives the circular orbit `R = 4 < 6M`, which is
unstable: `V''(4) = 2(4 − 6)/(4³ · 1) = −1/16`. -/
example : deriv (deriv (effectivePotential 1 1 4)) 4 = -1 / 16 := by
  have h : deriv (effectivePotential 1 1 4) 4 = 0 := by
    rw [deriv_effectivePotential_eq_zero_iff 4 (by norm_num)]
    norm_num
  rw [deriv_deriv_effectivePotential_of_deriv_eq_zero one_pos (by norm_num) h]
  norm_num

/- The orbit of radius `4` around the mass `1` has `L² = MR²/(R − 3M) = 16` and
`E² = (1 − 2M/R)²/(1 − 3M/R) = 1`. -/
example : (4 ^ 2 * circularAngleRate 1 4) ^ 2 = 16 ∧
    ((1 - 2 * 1 / 4) * circularTimeRate 1 4) ^ 2 = 1 := by
  rw [circularAngularMomentum_sq zero_le_one (by norm_num),
    circularEnergy_sq zero_le_one (by norm_num)]
  norm_num

/- The circular light orbit around the mass `1` at `r = 3` is a null geodesic. -/
example : (metric zero_le_one).toLorentzMetric.IsGeodesicOn univ (photonOrbit one_pos 1) ∧
    ∀ t, (metric zero_le_one).toLorentzMetric.form (photonOrbit one_pos 1 t)
      (curveVelocity (photonOrbit one_pos 1) t) (curveVelocity (photonOrbit one_pos 1) t) = 0 :=
  ⟨isGeodesicOn_photonCircle one_pos 1, form_curveVelocity_photonCircle one_pos 1⟩

/- At `(0, 4, π/2, 0)` around the mass `1`: `Γ^1_{00} = M(r − 2M)/r³ = 1/32`. -/
example : christoffelOf (metric zero_le_one).coefficient ![0, 4, Real.pi / 2, 0] 1 0 0 =
    1 / 32 := by
  have hy : (![0, 4, Real.pi / 2, 0] : MinkowskiModel 3) ∈ domain 1 :=
    ⟨by norm_num, by simp; positivity, by simp; linarith [Real.pi_pos]⟩
  rw [christoffelOf_metric zero_le_one hy]
  norm_num [christoffel]

end ProjectAinos.GeneralRelativity.SchwarzschildExterior
