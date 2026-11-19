/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.Lorentzian.ChristoffelCertificate
public import ProjectAinos.SmoothGeometry.Lorentzian.DiagonalMetric
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The three-dimensional spaces of constant curvature

An isotropic space (Landau–Lifshitz, §111) has constant curvature `k`. In the stereographic
co-ordinates `x ∈ ℝ³` its metric is conformally flat,
`dl² = (dx₁² + dx₂² + dx₃²) / Ω_k(x)²` with `Ω_k(x) = 1 + (k/4)|x|²` (`conformalFactor`), on the
open set `domain k = {Ω_k > 0}`: all of `ℝ³` for `k ≥ 0` (`domain_eq_univ`), and the ball
`|x|² < −4/k`, of radius `2/√(−k)`, for `k < 0` (`domain_of_neg`). The matrix of coefficients
is `coefficient k x = Ω_k(x)⁻² · 1`, positive definite on the domain (`posDef_coefficient`).

The metric is Riemannian, so it is not a `CoordinateMetric` (which is Lorentzian). The
formula-level quantities `christoffelOf`, `ricciOf`, `scalarOf`, `densityOf` and
`curvatureOf` are defined for any matrix of coefficients on `MinkowskiModel d`; the space is
`MinkowskiModel 2 = Fin 3 → ℝ`, and the time and space names of its axes play no role.

* `christoffelOf_eq`: `Γ^l_{ij} = −(k / 2Ω)(δ_{lj} x_i + δ_{li} x_j − δ_{ij} x_l)` on the domain
  (from `christoffelOf_diagonal`).
* `curvatureOf_eq`: the curvature is `R^l_{ijm} = k (δ^l_i h_{jm} − δ^l_j h_{im})` in the index
  convention of `curvatureOf`: the space has constant curvature `k`, Landau–Lifshitz (111.1).
* `ricciOf_eq`, `scalarOf_eq`: `P_{jm} = 2k h_{jm}` and `P = 6k`, Landau–Lifshitz (111.2).
* `densityOf_coefficient`: the volume element is `√h = Ω_k⁻³`.

The topology of the three models:

* `k = 1`: the lift `X(x) = ((4 − |x|²)/(4 + |x|²), 4x/(4 + |x|²))` (`lift`, `lift_one_apply`)
  is injective with image the unit sphere `S³ ⊂ ℝ⁴` minus the point `(−1, 0, 0, 0)`
  (`sphere_embedding`), a homeomorphism `ℝ³ ≃ₜ S³ ∖ {pt}` (`sphereHomeomorph`) whose inverse is
  the stereographic projection, and it pulls the Euclidean metric of `ℝ⁴` back to the metric
  (`sphere_firstFundamentalForm`).
* `k = −1`: the lift of the ball `|x| < 2` is injective with image the upper sheet of the
  hyperboloid `−X₀² + X₁² + X₂² + X₃² = −1` (`hyperboloid_embedding`), a homeomorphism
  (`hyperboloidHomeomorph`), and it pulls the Minkowski form back to the metric
  (`hyperboloid_firstFundamentalForm`).
* `k = 0`: the space is `ℝ³` with the Euclidean metric (`coefficient_flat`,
  `christoffel_flat`), lifted to the hyperplane `X₀ = 1` (`lift_flat`).

The closed space `k > 0` has the finite volume `∫ Ω_k⁻³ d³x = 2π² / k^{3/2}`, which is `2π²a³`
for the radius `a = k^{−1/2}` (`integral_inv_conformalFactor_pow_three`,
`integral_inv_conformalFactor_pow_three_of_pos`).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace ProjectAinos.SmoothGeometry.SpaceForm

open CoordinateMetric

/-! ### The conformal factor, the domain and the coefficients -/

/-- The conformal factor `Ω_k(x) = 1 + (k/4)|x|²` of the space of constant curvature `k` in
stereographic co-ordinates. -/
def conformalFactor (k : ℝ) (x : MinkowskiModel 2) : ℝ := 1 + k / 4 * ∑ i, x i ^ 2

/-- The domain `{x | Ω_k(x) > 0}` of the stereographic chart: all of `ℝ³` for `k ≥ 0`, the ball
of radius `2/√(−k)` for `k < 0`. -/
def domain (k : ℝ) : Set (MinkowskiModel 2) := {x | 0 < conformalFactor k x}

/-- The coefficients `h_{ij} = δ_{ij} / Ω_k(x)²` of the metric of constant curvature `k`: the
stereographic chart of the sphere minus a point for `k > 0`, flat space for `k = 0`, the
Poincaré ball for `k < 0`. -/
def coefficient (k : ℝ) (x : MinkowskiModel 2) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal fun _ => (conformalFactor k x)⁻¹ ^ 2

/-- The entries of the coefficient matrix. -/
theorem coefficient_apply (k : ℝ) (x : MinkowskiModel 2) (i j : Fin 3) :
    coefficient k x i j = if i = j then (conformalFactor k x)⁻¹ ^ 2 else 0 :=
  Matrix.diagonal_apply _ _ _

/-- Scaling the co-ordinates rescales the curvature: `Ω_k(c x) = Ω_{c² k}(x)`. -/
theorem conformalFactor_smul (k c : ℝ) (x : MinkowskiModel 2) :
    conformalFactor k (c • x) = conformalFactor (c ^ 2 * k) x := by
  simp only [conformalFactor, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  ring

/-- For `k ≥ 0` the conformal factor is positive. -/
theorem conformalFactor_pos_of_nonneg {k : ℝ} (hk : 0 ≤ k) (x : MinkowskiModel 2) :
    0 < conformalFactor k x := by
  unfold conformalFactor
  have : 0 ≤ k / 4 * ∑ i, x i ^ 2 :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
  linarith

/-- For `k ≤ 0` the conformal factor is at most `1`. -/
theorem conformalFactor_le_one {k : ℝ} (hk : k ≤ 0) (x : MinkowskiModel 2) :
    conformalFactor k x ≤ 1 := by
  unfold conformalFactor
  have : k / 4 * ∑ i, x i ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (Finset.sum_nonneg fun i _ => sq_nonneg (x i))
  linarith

/-- For `k ≥ 0` the chart covers all of `ℝ³`. -/
theorem domain_eq_univ {k : ℝ} (hk : 0 ≤ k) : domain k = univ :=
  eq_univ_of_forall (conformalFactor_pos_of_nonneg hk)

/-- For `k < 0` the domain is the ball `|x|² < −4/k`, of radius `2/√(−k)`. -/
theorem domain_of_neg {k : ℝ} (hk : k < 0) : domain k = {x | ∑ i, x i ^ 2 < -4 / k} := by
  ext x
  simp only [domain, conformalFactor, mem_ofPred_eq, lt_div_iff_of_neg hk]
  constructor <;> intro h <;> linarith

/-- The differential of the conformal factor: `dΩ_k(v) = (k/2) ∑ᵢ xᵢ vⁱ`. -/
theorem hasFDerivAt_conformalFactor (k : ℝ) (y : MinkowskiModel 2) :
    HasFDerivAt (conformalFactor k)
      ((k / 2) • ∑ i, y i • (ContinuousLinearMap.proj i : MinkowskiModel 2 →L[ℝ] ℝ)) y := by
  have h : HasFDerivAt (fun z : MinkowskiModel 2 => ∑ i, z i ^ 2)
      (∑ i, ((2 : ℕ) • y i ^ (2 - 1)) • (ContinuousLinearMap.proj i : MinkowskiModel 2 →L[ℝ] ℝ))
      y := HasFDerivAt.fun_sum fun i _ => (hasFDerivAt_apply i y).pow 2
  refine (h.const_mul (k / 4)).const_add 1 |>.congr_fderiv ?_
  ext v
  simp [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The derivative of the conformal factor along `v`. -/
theorem fderiv_conformalFactor (k : ℝ) (y v : MinkowskiModel 2) :
    fderiv ℝ (conformalFactor k) y v = k / 2 * ∑ i, y i * v i := by
  rw [(hasFDerivAt_conformalFactor k y).fderiv]
  simp

/-- The conformal factor is continuous. -/
theorem continuous_conformalFactor (k : ℝ) : Continuous (conformalFactor k) :=
  continuous_iff_continuousAt.2 fun y => (hasFDerivAt_conformalFactor k y).continuousAt

/-- The domain is open. -/
theorem isOpen_domain (k : ℝ) : IsOpen (domain k) :=
  isOpen_lt continuous_const (continuous_conformalFactor k)

/-- The coefficient matrix is positive definite on the domain: the metric is Riemannian. -/
theorem posDef_coefficient (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) :
    (coefficient k x).PosDef :=
  Matrix.PosDef.diagonal fun _ => pow_pos (inv_pos.mpr hx) 2

/-- The volume element is `√(det h) = Ω_k⁻³`. -/
theorem densityOf_coefficient (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) :
    densityOf (coefficient k) x = (conformalFactor k x)⁻¹ ^ 3 := by
  have hw : 0 ≤ (conformalFactor k x)⁻¹ :=
    inv_nonneg.mpr (show 0 < conformalFactor k x from hx).le
  simp only [densityOf, coefficient, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [show ((conformalFactor k x)⁻¹ ^ 2) ^ 3 = ((conformalFactor k x)⁻¹ ^ 3) ^ 2 by ring,
    abs_of_nonneg (sq_nonneg _), Real.sqrt_sq (pow_nonneg hw 3)]

/-! ### The Christoffel symbols -/

/-- The differential of `Ω_k⁻¹` where `Ω_k` does not vanish. -/
theorem hasFDerivAt_inv_conformalFactor (k : ℝ) {y : MinkowskiModel 2}
    (hy : conformalFactor k y ≠ 0) :
    HasFDerivAt (fun z => (conformalFactor k z)⁻¹)
      ((-(conformalFactor k y ^ 2)⁻¹) •
        (k / 2) • ∑ i, y i • (ContinuousLinearMap.proj i : MinkowskiModel 2 →L[ℝ] ℝ)) y :=
  (hasDerivAt_inv hy).comp_hasFDerivAt y (hasFDerivAt_conformalFactor k y)

/-- The derivative of the diagonal coefficient `Ω_k⁻²` along `v` is `−k Ω_k⁻³ ∑ᵢ xᵢ vⁱ`. -/
theorem fderiv_inv_conformalFactor_sq (k : ℝ) {y : MinkowskiModel 2}
    (hy : conformalFactor k y ≠ 0) (v : MinkowskiModel 2) :
    fderiv ℝ (fun z => (conformalFactor k z)⁻¹ ^ 2) y v =
      -(k * (conformalFactor k y)⁻¹ ^ 3) * ∑ i, y i * v i := by
  rw [((hasFDerivAt_inv_conformalFactor k hy).pow 2).fderiv]
  simp
  ring

/-- The table `Γ^l_{ij} = −(k / 2Ω_k)(δ_{lj} x_i + δ_{li} x_j − δ_{ij} x_l)` of Christoffel
symbols of the metric of constant curvature `k`. -/
def christoffel (k : ℝ) (x : MinkowskiModel 2) (l i j : Fin 3) : ℝ :=
  -(k / 2 * (conformalFactor k x)⁻¹) *
    ((if l = j then x i else 0) + (if l = i then x j else 0) - (if i = j then x l else 0))

/-- A co-ordinate that is present or absent according to a fixed proposition is linear. -/
private theorem hasFDerivAt_ite_apply (p : Prop) [Decidable p] (a : Fin 3) (y : MinkowskiModel 2) :
    HasFDerivAt (fun z : MinkowskiModel 2 => if p then z a else 0)
      ((if p then (1 : ℝ) else 0) • (ContinuousLinearMap.proj a : MinkowskiModel 2 →L[ℝ] ℝ))
      y := by
  by_cases hp : p
  · simpa [hp] using hasFDerivAt_apply a y
  · simpa [hp] using hasFDerivAt_const (0 : ℝ) y

/-- The derivative of an entry of the table along `v`. -/
theorem fderiv_christoffel (k : ℝ) {y : MinkowskiModel 2} (hy : conformalFactor k y ≠ 0)
    (l i j : Fin 3) (v : MinkowskiModel 2) :
    fderiv ℝ (fun z => christoffel k z l i j) y v =
      k ^ 2 / 4 * (conformalFactor k y)⁻¹ ^ 2 * (∑ a, y a * v a) *
          ((if l = j then y i else 0) + (if l = i then y j else 0) - (if i = j then y l else 0)) -
        k / 2 * (conformalFactor k y)⁻¹ *
          ((if l = j then v i else 0) + (if l = i then v j else 0) -
            (if i = j then v l else 0)) := by
  have hB := ((hasFDerivAt_ite_apply (l = j) i y).add (hasFDerivAt_ite_apply (l = i) j y)).sub
    (hasFDerivAt_ite_apply (i = j) l y)
  have hF := ((hasFDerivAt_inv_conformalFactor k hy).const_mul (k / 2)).neg
  have h : HasFDerivAt (fun z => christoffel k z l i j) _ y := hF.mul hB
  have hite (p : Prop) [Decidable p] (a : Fin 3) :
      (if p then (ContinuousLinearMap.proj a : MinkowskiModel 2 →L[ℝ] ℝ) else 0) v =
        if p then v a else 0 := by
    split_ifs <;> rfl
  rw [h.fderiv]
  simp [hite]
  ring

/-- **The Christoffel symbols** of the metric of constant curvature `k` are the table
`christoffel k` wherever `Ω_k` does not vanish. -/
theorem christoffelOf_eq_of_ne_zero (k : ℝ) {x : MinkowskiModel 2}
    (hx : conformalFactor k x ≠ 0) (l i j : Fin 3) :
    christoffelOf (coefficient k) x l i j = christoffel k x l i j := by
  have h := christoffelOf_diagonal (fun z (_ : Fin 3) => (conformalFactor k z)⁻¹ ^ 2) x
    (fun _ => pow_ne_zero 2 (inv_ne_zero hx)) l i j
  rw [show coefficient k = fun z => Matrix.diagonal fun _ => (conformalFactor k z)⁻¹ ^ 2 from rfl,
    h]
  simp only [fderiv_inv_conformalFactor_sq k hx, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  unfold christoffel
  split_ifs <;> field_simp <;> ring

/-- **The Christoffel symbols** on the domain:
`Γ^l_{ij} = −(k / 2Ω_k)(δ_{lj} x_i + δ_{li} x_j − δ_{ij} x_l)`. -/
theorem christoffelOf_eq (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) (l i j : Fin 3) :
    christoffelOf (coefficient k) x l i j = christoffel k x l i j :=
  christoffelOf_eq_of_ne_zero k (show 0 < conformalFactor k x from hx).ne' l i j

/-- The table agrees with the Christoffel symbols near every point of the domain. -/
theorem eventually_christoffelOf_eq (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) :
    ∀ᶠ z in 𝓝 x, ∀ l i j, christoffelOf (coefficient k) z l i j = christoffel k z l i j := by
  filter_upwards [(isOpen_domain k).mem_nhds hx] with z hz
  exact christoffelOf_eq k hz

/-! ### The curvature -/

/-- The Kronecker symbol as a real number, an atom for `ring`. -/
private def kd (a b : Fin 3) : ℝ := if a = b then 1 else 0

private theorem ite_eq_kd (a b : Fin 3) [Decidable (a = b)] (r : ℝ) :
    (if a = b then r else 0) = kd a b * r := by
  unfold kd
  by_cases h : a = b <;> simp [h]

private theorem kd_comm (a b : Fin 3) : kd a b = kd b a := by
  unfold kd
  simp only [eq_comm]

private theorem single_eq_kd (i j : Fin 3) :
    (Pi.single i (1 : ℝ) : MinkowskiModel 2) j = kd j i := by
  simp [Pi.single_apply, kd]

private theorem sum_mul_single (y : MinkowskiModel 2) (i : Fin 3) :
    ∑ a, y a * (Pi.single i (1 : ℝ) : MinkowskiModel 2) a = y i := by
  simp [Pi.single_apply]

/-- The bracket `δ_{lj} x_i + δ_{li} x_j − δ_{ij} x_l` of the table. -/
private def bracket (x : MinkowskiModel 2) (l i j : Fin 3) : ℝ :=
  (if l = j then x i else 0) + (if l = i then x j else 0) - (if i = j then x l else 0)

/-- The contraction `∑ₐ B^l_{ia} B^a_{jm}` of two brackets. -/
private theorem sum_bracket_mul_bracket (y : MinkowskiModel 2) (l i j m : Fin 3) :
    ∑ a, bracket y l i a * bracket y a j m =
      (if l = m then y i * y j else 0) + (if l = j then y i * y m else 0) +
        2 * (if l = i then y j * y m else 0) - (if i = m then y l * y j else 0) -
        (if i = j then y l * y m else 0) -
        (if l = i then (if j = m then ∑ a, y a ^ 2 else 0) else 0) := by
  simp only [bracket, add_mul, mul_add, sub_mul, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [ite_eq_kd, sq]
  ring

/-- The curvature formula of the table is `R^l_{ijm} = k (δ^l_i h_{jm} − δ^l_j h_{im})`. -/
theorem curvatureOf_christoffel (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k)
    (l i j m : Fin 3) :
    curvatureOf (christoffel k) x l i j m =
      k * ((if l = i then coefficient k x j m else 0) -
        (if l = j then coefficient k x i m else 0)) := by
  have hx0 : conformalFactor k x ≠ 0 := (show 0 < conformalFactor k x from hx).ne'
  have hw : (conformalFactor k x)⁻¹ * conformalFactor k x = 1 := inv_mul_cancel₀ hx0
  have hsum : ∑ a, (christoffel k x l i a * christoffel k x a j m -
      christoffel k x l j a * christoffel k x a i m) = (k / 2 * (conformalFactor k x)⁻¹) ^ 2 *
        (∑ a, bracket x l i a * bracket x a j m - ∑ a, bracket x l j a * bracket x a i m) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by simp only [christoffel, bracket]; ring
  unfold curvatureOf
  rw [fderiv_christoffel k hx0, fderiv_christoffel k hx0, hsum, sum_bracket_mul_bracket,
    sum_bracket_mul_bracket]
  simp only [coefficient_apply]
  generalize (conformalFactor k x)⁻¹ = w at hw ⊢
  simp only [conformalFactor] at hw
  simp only [sum_mul_single]
  simp only [single_eq_kd, ite_eq_kd]
  linear_combination (norm := skip) (-(k * w * (kd l i * kd j m - kd l j * kd i m))) * hw
  simp only [kd_comm]
  ring1

/-- **Constant curvature**, Landau–Lifshitz (111.1): on the domain, the curvature of the metric is
`R^l_{ijm} = k (δ^l_i h_{jm} − δ^l_j h_{im})` in the index convention of `curvatureOf`. -/
theorem curvatureOf_eq (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) (l i j m : Fin 3) :
    curvatureOf (christoffelOf (coefficient k)) x l i j m =
      k * ((if l = i then coefficient k x j m else 0) -
        (if l = j then coefficient k x i m else 0)) := by
  have he (a b c : Fin 3) : (fun z => christoffelOf (coefficient k) z a b c) =ᶠ[𝓝 x]
      fun z => christoffel k z a b c := by
    filter_upwards [eventually_christoffelOf_eq k hx] with z hz using hz a b c
  have hy := (eventually_christoffelOf_eq k hx).self_of_nhds
  rw [← curvatureOf_christoffel k hx]
  unfold curvatureOf
  simp only [(he _ _ _).fderiv_eq, hy]

/-- **The Ricci tensor**, Landau–Lifshitz (111.2): `P_{jm} = 2k h_{jm}` on the domain. -/
theorem ricciOf_eq (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) (j m : Fin 3) :
    ricciOf (coefficient k) x j m = 2 * k * coefficient k x j m := by
  rw [ricciOf_eq_ricciOfChristoffel (eventually_christoffelOf_eq k hx),
    ricciOfChristoffel_eq_sum_curvatureOf]
  simp [curvatureOf_christoffel k hx, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- **The scalar curvature**, Landau–Lifshitz (111.2): `P = 6k` on the domain. -/
theorem scalarOf_eq (k : ℝ) {x : MinkowskiModel 2} (hx : x ∈ domain k) :
    scalarOf (coefficient k) x = 6 * k := by
  have hx0 : conformalFactor k x ≠ 0 := (show 0 < conformalFactor k x from hx).ne'
  have hinv : (coefficient k x)⁻¹ = Matrix.diagonal fun _ => conformalFactor k x ^ 2 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [coefficient, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one with l
    field_simp
  simp only [scalarOf, ricciOf_eq k hx, hinv, coefficient_apply, Matrix.diagonal_apply]
  simp
  field_simp
  ring

/-! ### The lift to `ℝ⁴` and the stereographic projection -/

/-- The lift `X(x) = (2/Ω_k − 1, x/Ω_k)` of the chart to `ℝ⁴`, with the pole co-ordinate first. For
`k = 1` it is the inverse stereographic projection onto the unit sphere, for `k = −1` onto the
upper sheet of the unit hyperboloid, and for `k = 0` the inclusion of the hyperplane `X₀ = 1`. -/
def lift (k : ℝ) (x : MinkowskiModel 2) : MinkowskiModel 3 :=
  Fin.cons (2 * (conformalFactor k x)⁻¹ - 1) fun a => x a * (conformalFactor k x)⁻¹

/-- The pole co-ordinate of the lift. -/
@[simp] theorem lift_zero (k : ℝ) (x : MinkowskiModel 2) :
    lift k x 0 = 2 * (conformalFactor k x)⁻¹ - 1 := rfl

/-- The other co-ordinates of the lift. -/
@[simp] theorem lift_succ (k : ℝ) (x : MinkowskiModel 2) (a : Fin 3) :
    lift k x a.succ = x a * (conformalFactor k x)⁻¹ := rfl

/-- For `k = 1` the lift is `X(x) = ((4 − |x|²)/(4 + |x|²), 4x/(4 + |x|²))`. -/
theorem lift_one_apply (x : MinkowskiModel 2) :
    lift 1 x 0 = (4 - ∑ i, x i ^ 2) / (4 + ∑ i, x i ^ 2) ∧
      ∀ a : Fin 3, lift 1 x a.succ = 4 * x a / (4 + ∑ i, x i ^ 2) := by
  have h : 0 < 4 + ∑ i, x i ^ 2 := by positivity
  refine ⟨?_, fun a => ?_⟩
  · rw [lift_zero, conformalFactor]
    field_simp
    ring
  · rw [lift_succ, conformalFactor]
    field_simp

/-- For `k² = 1` the lift lies on the quadric `k X₀² + X₁² + X₂² + X₃² = k`. -/
theorem quadric_lift {k : ℝ} (hk : k ^ 2 = 1) {x : MinkowskiModel 2}
    (hx : conformalFactor k x ≠ 0) :
    k * lift k x 0 ^ 2 + ∑ a : Fin 3, lift k x a.succ ^ 2 = k := by
  have hw : (conformalFactor k x)⁻¹ * conformalFactor k x = 1 := inv_mul_cancel₀ hx
  simp only [lift_zero, lift_succ, mul_pow, ← Finset.sum_mul]
  generalize (conformalFactor k x)⁻¹ = w at hw ⊢
  simp only [conformalFactor] at hw
  linear_combination (4 * k * w) * hw - ((∑ i, x i ^ 2) * w ^ 2) * hk

/-- The stereographic projection `x = 2X'/(1 + X₀)` from the point `(−1, 0, 0, 0)`. -/
def stereographic (X : MinkowskiModel 3) : MinkowskiModel 2 :=
  fun a => 2 * X a.succ / (1 + X 0)

/-- The stereographic projection inverts the lift. -/
theorem stereographic_lift (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) :
    stereographic (lift k x) = x := by
  funext a
  simp only [stereographic, lift_zero, lift_succ]
  field_simp
  ring

/-- On the quadric `k X₀² + |X'|² = k`, `k² = 1`, the conformal factor at the projection is
`2/(1 + X₀)`. -/
theorem conformalFactor_stereographic {k : ℝ} (hk : k ^ 2 = 1) {X : MinkowskiModel 3}
    (hX : k * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 = k) (h : 1 + X 0 ≠ 0) :
    conformalFactor k (stereographic X) = 2 / (1 + X 0) := by
  simp only [conformalFactor, stereographic, div_pow, mul_pow, ← Finset.sum_div,
    ← Finset.mul_sum]
  rw [show ∑ a : Fin 3, X a.succ ^ 2 = k - k * X 0 ^ 2 by linarith]
  field_simp
  linear_combination (4 * (1 - X 0) * (1 + X 0)) * hk

/-- The lift inverts the stereographic projection on the quadric `k X₀² + |X'|² = k`,
`k² = 1`, away from `X₀ = −1`. -/
theorem lift_stereographic {k : ℝ} (hk : k ^ 2 = 1) {X : MinkowskiModel 3}
    (hX : k * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 = k) (h : 1 + X 0 ≠ 0) :
    lift k (stereographic X) = X := by
  funext A
  refine Fin.cases ?_ (fun a => ?_) A
  · rw [lift_zero, conformalFactor_stereographic hk hX h]
    field_simp
    ring
  · rw [lift_succ, conformalFactor_stereographic hk hX h]
    simp only [stereographic]
    field_simp

/-- The lift is differentiable where `Ω_k` does not vanish. -/
theorem differentiableAt_lift (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) :
    DifferentiableAt ℝ (lift k) x := by
  refine differentiableAt_pi.2 fun A => Fin.cases ?_ (fun a => ?_) A
  · exact (((hasFDerivAt_inv_conformalFactor k hx).const_mul 2).sub_const 1).differentiableAt
  · exact ((hasFDerivAt_apply a x).mul (hasFDerivAt_inv_conformalFactor k hx)).differentiableAt

/-- The lift is continuous where `Ω_k` does not vanish. -/
theorem continuousAt_lift (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0) :
    ContinuousAt (lift k) x :=
  (differentiableAt_lift k hx).continuousAt

/-- The stereographic projection is continuous on a set that avoids `X₀ = −1`. -/
theorem continuous_stereographic_on {S : Set (MinkowskiModel 3)}
    (hS : ∀ X ∈ S, 1 + X 0 ≠ 0) : Continuous fun X : S => stereographic X := by
  refine continuous_pi fun a => ?_
  exact (continuous_const.mul ((continuous_apply a.succ).comp continuous_subtype_val)).div
    (continuous_const.add ((continuous_apply 0).comp continuous_subtype_val))
    fun X => hS X X.2

/-! ### The closed space: the sphere -/

/-- The unit sphere `X₀² + X₁² + X₂² + X₃² = 1` of `ℝ⁴`. -/
def sphere : Set (MinkowskiModel 3) := {X | ∑ A, X A ^ 2 = 1}

/-- The point `(−1, 0, 0, 0)`, the centre of the stereographic projection. -/
def southPole : MinkowskiModel 3 := Fin.cons (-1) 0

/-- The Euclidean square of `X ∈ ℝ⁴` in the form of the quadric with `k = 1`. -/
theorem sum_sq_eq_quadric (X : MinkowskiModel 3) :
    ∑ A, X A ^ 2 = 1 * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 := by
  rw [Fin.sum_univ_succ, one_mul]

/-- A point of the sphere with `X₀ = −1` is the south pole. -/
theorem eq_southPole {X : MinkowskiModel 3}
    (hX : 1 * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 = 1) (h : X 0 = -1) : X = southPole := by
  have hs : ∑ a : Fin 3, X a.succ ^ 2 = 0 := by rw [h] at hX; linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg fun a _ => sq_nonneg _] at hs
  funext A
  refine Fin.cases ?_ (fun a => ?_) A
  · simp [southPole, h]
  · simpa [southPole] using hs a (Finset.mem_univ a)

/-- On the sphere minus the south pole, `1 + X₀ ≠ 0`. -/
theorem one_add_ne_zero_of_mem_sphere {X : MinkowskiModel 3}
    (hX : X ∈ sphere \ {southPole}) : 1 + X 0 ≠ 0 := by
  obtain ⟨hX, hne⟩ := hX
  rw [sphere, mem_ofPred_eq, sum_sq_eq_quadric] at hX
  exact fun h => hne (eq_southPole hX (by linarith))

/-- The lift of `k = 1` lies on the unit sphere. -/
theorem lift_one_mem_sphere (x : MinkowskiModel 2) : lift 1 x ∈ sphere := by
  have h := quadric_lift (k := 1) (by norm_num) (conformalFactor_pos_of_nonneg zero_le_one x).ne'
  rw [sphere, mem_ofPred_eq, sum_sq_eq_quadric, h]

/-- The lift of `k = 1` misses the south pole. -/
theorem lift_one_ne_southPole (x : MinkowskiModel 2) : lift 1 x ≠ southPole := by
  intro h
  have h0 := congrFun h 0
  rw [lift_zero, southPole, Fin.cons_zero] at h0
  have := inv_pos.mpr (conformalFactor_pos_of_nonneg zero_le_one x)
  linarith

/-- The lift of `k = 1` is injective. -/
theorem injective_lift_one : Function.Injective (lift 1) :=
  Function.LeftInverse.injective fun x =>
    stereographic_lift 1 (conformalFactor_pos_of_nonneg zero_le_one x).ne'

/-- The image of the lift of `k = 1` is the unit sphere minus the south pole. -/
theorem range_lift_one : range (lift 1) = sphere \ {southPole} := by
  ext X
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨lift_one_mem_sphere x, lift_one_ne_southPole x⟩
  · intro hX
    have h0 := one_add_ne_zero_of_mem_sphere hX
    have hq := hX.1
    rw [sphere, mem_ofPred_eq, sum_sq_eq_quadric] at hq
    exact ⟨stereographic X, lift_stereographic (by norm_num) hq h0⟩

/-- **The closed space.** The chart of `k = 1` is the stereographic chart of the unit sphere
`S³ ⊂ ℝ⁴`: the lift is injective with image `S³ ∖ {(−1, 0, 0, 0)}`. -/
theorem sphere_embedding :
    Function.Injective (lift 1) ∧ range (lift 1) = sphere \ {southPole} :=
  ⟨injective_lift_one, range_lift_one⟩

/-- **The topology of the closed space:** `ℝ³` is homeomorphic to `S³ ∖ {pt}` by the lift, with
the stereographic projection as inverse. -/
def sphereHomeomorph : MinkowskiModel 2 ≃ₜ ↥(sphere \ {southPole}) where
  toFun x := ⟨lift 1 x, lift_one_mem_sphere x, lift_one_ne_southPole x⟩
  invFun X := stereographic X
  left_inv x := stereographic_lift 1 (conformalFactor_pos_of_nonneg zero_le_one x).ne'
  right_inv X := by
    obtain ⟨X, hX⟩ := X
    refine Subtype.ext (lift_stereographic (by norm_num) ?_ (one_add_ne_zero_of_mem_sphere hX))
    have h := hX.1
    rwa [sphere, mem_ofPred_eq, sum_sq_eq_quadric] at h
  continuous_toFun := (continuous_iff_continuousAt.2 fun x => continuousAt_lift 1
    (conformalFactor_pos_of_nonneg zero_le_one x).ne').subtype_mk _
  continuous_invFun := continuous_stereographic_on fun _ hX => one_add_ne_zero_of_mem_sphere hX

/-! ### The open space: the hyperboloid -/

/-- The upper sheet `−X₀² + X₁² + X₂² + X₃² = −1`, `X₀ > 0`, of the unit hyperboloid in Minkowski
space `ℝ^{1,3}`. -/
def upperSheet : Set (MinkowskiModel 3) :=
  {X | minkowskiForm .timeNegative 3 X X = -1 ∧ 0 < X 0}

/-- The Minkowski form with the signature `(−, +, +, +)`. -/
theorem minkowskiForm_timeNegative_eq (V W : MinkowskiModel 3) :
    minkowskiForm .timeNegative 3 V W = -1 * (V 0 * W 0) + ∑ a : Fin 3, V a.succ * W a.succ := by
  simp [minkowskiForm_apply, Fin.sum_univ_succ, lorentzSign]

/-- The Minkowski square of `X` in the form of the quadric with `k = −1`. -/
theorem minkowskiForm_self_eq_quadric (X : MinkowskiModel 3) :
    minkowskiForm .timeNegative 3 X X = -1 * X 0 ^ 2 + ∑ a : Fin 3, X a.succ ^ 2 := by
  simp [minkowskiForm_timeNegative_eq, sq]

/-- The lift of a point of the ball `|x| < 2` lies on the upper sheet. -/
theorem lift_neg_one_mem_upperSheet {x : MinkowskiModel 2} (hx : x ∈ domain (-1)) :
    lift (-1) x ∈ upperSheet := by
  have hx0 : 0 < conformalFactor (-1) x := hx
  refine ⟨?_, ?_⟩
  · rw [minkowskiForm_self_eq_quadric, quadric_lift (by norm_num) hx0.ne']
  · rw [lift_zero]
    have := (one_le_inv₀ hx0).mpr (conformalFactor_le_one (by norm_num) x)
    linarith

/-- The projection of a point of the upper sheet lies in the ball `|x| < 2`. -/
theorem stereographic_mem_domain {X : MinkowskiModel 3} (hX : X ∈ upperSheet) :
    stereographic X ∈ domain (-1) := by
  obtain ⟨hX, h0⟩ := hX
  rw [minkowskiForm_self_eq_quadric] at hX
  show 0 < conformalFactor (-1) (stereographic X)
  rw [conformalFactor_stereographic (by norm_num) hX (by linarith)]
  positivity

/-- The lift of `k = −1` is injective on the ball. -/
theorem injOn_lift_neg_one : InjOn (lift (-1)) (domain (-1)) := fun x hx y hy h => by
  rw [← stereographic_lift (-1) (show 0 < conformalFactor (-1) x from hx).ne', h,
    stereographic_lift (-1) (show 0 < conformalFactor (-1) y from hy).ne']

/-- The image of the ball under the lift of `k = −1` is the upper sheet. -/
theorem image_lift_neg_one : lift (-1) '' domain (-1) = upperSheet := by
  ext X
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact lift_neg_one_mem_upperSheet hx
  · intro hX
    have hq := hX.1
    rw [minkowskiForm_self_eq_quadric] at hq
    exact ⟨stereographic X, stereographic_mem_domain hX,
      lift_stereographic (by norm_num) hq (by linarith [hX.2])⟩

/-- **The open space.** The chart of `k = −1` is the Poincaré ball: the lift is injective on the
ball `|x| < 2` with image the upper sheet of the hyperboloid. -/
theorem hyperboloid_embedding :
    InjOn (lift (-1)) (domain (-1)) ∧ lift (-1) '' domain (-1) = upperSheet :=
  ⟨injOn_lift_neg_one, image_lift_neg_one⟩

/-- **The topology of the open space:** the ball `|x| < 2` is homeomorphic to the upper sheet of
the hyperboloid by the lift, with the stereographic projection as inverse. -/
def hyperboloidHomeomorph : ↥(domain (-1)) ≃ₜ ↥upperSheet where
  toFun x := ⟨lift (-1) x, lift_neg_one_mem_upperSheet x.2⟩
  invFun X := ⟨stereographic X, stereographic_mem_domain X.2⟩
  left_inv x := Subtype.ext
    (stereographic_lift (-1) (show 0 < conformalFactor (-1) x from x.2).ne')
  right_inv X := by
    obtain ⟨X, hX, h0⟩ := X
    rw [minkowskiForm_self_eq_quadric] at hX
    exact Subtype.ext (lift_stereographic (by norm_num) hX (by linarith))
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_iff_continuousAt.2 fun x => (continuousAt_lift (-1)
      (show 0 < conformalFactor (-1) x from x.2).ne').comp continuous_subtype_val.continuousAt
  continuous_invFun := (continuous_stereographic_on fun X hX => by
    have := hX.2
    linarith).subtype_mk fun X => stereographic_mem_domain X.2

/-! ### The first fundamental forms -/

/-- The derivative of the pole co-ordinate of the lift along `v`. -/
theorem fderiv_lift_zero (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0)
    (v : MinkowskiModel 2) :
    fderiv ℝ (fun z => lift k z 0) x v =
      -(k * (conformalFactor k x)⁻¹ ^ 2) * ∑ i, x i * v i := by
  have h : HasFDerivAt (fun z => lift k z 0) _ x :=
    ((hasFDerivAt_inv_conformalFactor k hx).const_mul 2).sub_const 1
  rw [h.fderiv]
  simp
  ring

/-- The derivative of the other co-ordinates of the lift along `v`. -/
theorem fderiv_lift_succ (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0)
    (a : Fin 3) (v : MinkowskiModel 2) :
    fderiv ℝ (fun z => lift k z a.succ) x v =
      v a * (conformalFactor k x)⁻¹ -
        k / 2 * (conformalFactor k x)⁻¹ ^ 2 * x a * ∑ i, x i * v i := by
  have h : HasFDerivAt (fun z => lift k z a.succ) _ x :=
    (hasFDerivAt_apply a x).mul (hasFDerivAt_inv_conformalFactor k hx)
  rw [h.fderiv]
  simp
  ring

/-- The components of the derivative of the lift are the derivatives of its components. -/
theorem fderiv_lift_apply (k : ℝ) {x : MinkowskiModel 2} (hx : conformalFactor k x ≠ 0)
    (v : MinkowskiModel 2) (A : Fin 4) :
    fderiv ℝ (lift k) x v A = fderiv ℝ (fun z => lift k z A) x v := by
  rw [fderiv_apply (differentiableAt_lift k hx) A]
  rfl

/-- The pullback of the quadratic form `k dX₀² + dX₁² + dX₂² + dX₃²` by the lift is
`Ω_k⁻² |dx|²` for `k³ = k`, that is `k ∈ {−1, 0, 1}`. -/
theorem lift_pullback {k : ℝ} (hk : k ^ 3 = k) {x : MinkowskiModel 2}
    (hx : conformalFactor k x ≠ 0) (v w : MinkowskiModel 2) :
    k * (fderiv ℝ (lift k) x v 0 * fderiv ℝ (lift k) x w 0) +
        ∑ a : Fin 3, fderiv ℝ (lift k) x v a.succ * fderiv ℝ (lift k) x w a.succ =
      (conformalFactor k x)⁻¹ ^ 2 * ∑ i, v i * w i := by
  have hW : (conformalFactor k x)⁻¹ * conformalFactor k x = 1 := inv_mul_cancel₀ hx
  simp only [fderiv_lift_apply k hx, fderiv_lift_zero k hx, fderiv_lift_succ k hx]
  generalize (conformalFactor k x)⁻¹ = W at hW ⊢
  simp only [conformalFactor] at hW
  have key (a : Fin 3) : (v a * W - k / 2 * W ^ 2 * x a * ∑ i, x i * v i) *
      (w a * W - k / 2 * W ^ 2 * x a * ∑ i, x i * w i) =
      W ^ 2 * (v a * w a) - k / 2 * W ^ 3 * (∑ i, x i * w i) * (x a * v a) -
        k / 2 * W ^ 3 * (∑ i, x i * v i) * (x a * w a) +
        k ^ 2 / 4 * W ^ 4 * (∑ i, x i * v i) * (∑ i, x i * w i) * x a ^ 2 := by
    ring
  rw [Finset.sum_congr rfl fun a _ => key a]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination ((∑ i, x i * v i) * (∑ i, x i * w i) * W ^ 3 * k) * hW +
    ((∑ i, x i * v i) * (∑ i, x i * w i) * W ^ 4) * hk

private theorem sum_single_mul_single (i j : Fin 3) :
    ∑ a, (Pi.single i (1 : ℝ) : MinkowskiModel 2) a * (Pi.single j (1 : ℝ) : MinkowskiModel 2) a =
      if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [Pi.single_apply]
  · simp [Pi.single_apply, h, Ne.symm h]

/-- The lift of `k = 1` pulls the Euclidean metric of `ℝ⁴` back to `Ω_1⁻² |dx|²`. -/
theorem sphere_pullback (x v w : MinkowskiModel 2) :
    ∑ A, fderiv ℝ (lift 1) x v A * fderiv ℝ (lift 1) x w A =
      (conformalFactor 1 x)⁻¹ ^ 2 * ∑ i, v i * w i := by
  rw [Fin.sum_univ_succ, ← one_mul (fderiv ℝ (lift 1) x v 0 * _)]
  exact lift_pullback (by norm_num) (conformalFactor_pos_of_nonneg zero_le_one x).ne' v w

/-- **The first fundamental form of the sphere:** `∑_A ∂_iX^A ∂_jX^A = h_{ij}` for `k = 1`. -/
theorem sphere_firstFundamentalForm (x : MinkowskiModel 2) (i j : Fin 3) :
    ∑ A, fderiv ℝ (lift 1) x (Pi.single i 1) A * fderiv ℝ (lift 1) x (Pi.single j 1) A =
      coefficient 1 x i j := by
  rw [sphere_pullback, sum_single_mul_single, coefficient_apply]
  split_ifs <;> simp

/-- The lift of `k = −1` pulls the Minkowski form of `ℝ^{1,3}` back to `Ω_{−1}⁻² |dx|²` on the
ball. -/
theorem hyperboloid_pullback {x : MinkowskiModel 2} (hx : x ∈ domain (-1))
    (v w : MinkowskiModel 2) :
    minkowskiForm .timeNegative 3 (fderiv ℝ (lift (-1)) x v) (fderiv ℝ (lift (-1)) x w) =
      (conformalFactor (-1) x)⁻¹ ^ 2 * ∑ i, v i * w i := by
  rw [minkowskiForm_timeNegative_eq]
  exact lift_pullback (by norm_num) (show 0 < conformalFactor (-1) x from hx).ne' v w

/-- **The first fundamental form of the hyperboloid:** `η_{AB} ∂_iX^A ∂_jX^B = h_{ij}` for
`k = −1` on the ball. -/
theorem hyperboloid_firstFundamentalForm {x : MinkowskiModel 2} (hx : x ∈ domain (-1))
    (i j : Fin 3) :
    minkowskiForm .timeNegative 3 (fderiv ℝ (lift (-1)) x (Pi.single i 1))
        (fderiv ℝ (lift (-1)) x (Pi.single j 1)) = coefficient (-1) x i j := by
  rw [hyperboloid_pullback hx, sum_single_mul_single, coefficient_apply]
  split_ifs <;> simp

/-! ### The volume of the closed space -/

/-- A primitive of `r² (1 + r²/4)⁻³`. -/
private def radialPrimitive (r : ℝ) : ℝ :=
  Real.arctan (r / 2) + 2 * r * (r ^ 2 - 4) / (4 + r ^ 2) ^ 2

private theorem radialPrimitive_eq :
    radialPrimitive = fun r => Real.arctan (r / 2) + 2 * r * (r ^ 2 - 4) / (4 + r ^ 2) ^ 2 := by
  funext r
  rfl

private theorem hasDerivAt_radialPrimitive (r : ℝ) :
    HasDerivAt radialPrimitive (r ^ 2 * (1 + 1 / 4 * r ^ 2)⁻¹ ^ 3) r := by
  have h4 : (4 + r ^ 2) ≠ 0 := by positivity
  have ha : HasDerivAt (fun y => Real.arctan (y / 2)) _ r :=
    ((hasDerivAt_id' r).div_const 2).arctan
  rw [radialPrimitive_eq]
  have h := ha.fun_add
      ((((hasDerivAt_id' r).const_mul 2).fun_mul ((hasDerivAt_pow 2 r).sub_const 4)).fun_div
        (((hasDerivAt_pow 2 r).const_add 4).fun_pow 2) (pow_ne_zero 2 h4))
  refine h.congr_deriv ?_
  field_simp
  ring

private theorem tendsto_radialPrimitive : Tendsto radialPrimitive atTop (𝓝 (Real.pi / 2)) := by
  have h1 : Tendsto (fun r : ℝ => Real.arctan (r / 2)) atTop (𝓝 (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
      (tendsto_id.atTop_div_const (by norm_num))
  have h2 : Tendsto (fun r : ℝ => 2 * r * (r ^ 2 - 4) / (4 + r ^ 2) ^ 2) atTop (𝓝 0) := by
    have hu : Tendsto (fun r : ℝ => 2 * r⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with r hr
      have : 0 ≤ r ^ 2 - 4 := by nlinarith
      positivity
    · filter_upwards [eventually_ge_atTop 2] with r hr
      have hr0 : 0 < r := by linarith
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [sq_nonneg r, sq_nonneg (r ^ 2)]
  rw [radialPrimitive_eq]
  simpa only [add_zero] using h1.add h2

private theorem integral_radial :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (1 + 1 / 4 * r ^ 2)⁻¹ ^ 3 = Real.pi / 2 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun r _ => hasDerivAt_radialPrimitive r)
    (fun r _ => by positivity) tendsto_radialPrimitive]
  simp [radialPrimitive]

/-- **The volume of the closed space of unit radius** is `∫ Ω_1⁻³ d³x = 2π²`, the volume of
`S³`. -/
theorem integral_inv_conformalFactor_pow_three :
    ∫ x : MinkowskiModel 2, (conformalFactor 1 x)⁻¹ ^ 3 = 2 * Real.pi ^ 2 := by
  have he := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun x : MinkowskiModel 2 => (conformalFactor 1 x)⁻¹ ^ 3)
  rw [← he]
  have hn (y : EuclideanSpace ℝ (Fin 3)) :
      conformalFactor 1 ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm y) =
        1 + 1 / 4 * ‖y‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  simp only [hn]
  rw [integral_fun_norm_addHaar volume (fun r => (1 + 1 / 4 * r ^ 2)⁻¹ ^ 3)]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, nsmul_eq_mul]
  rw [show 3 - 1 = 2 from rfl, integral_radial]
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
    one_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

/-- **The volume of the closed space** of curvature `k > 0`, radius `a = k^{−1/2}`, is
`∫ Ω_k⁻³ d³x = 2π² / k^{3/2} = 2π² a³`. -/
theorem integral_inv_conformalFactor_pow_three_of_pos {k : ℝ} (hk : 0 < k) :
    ∫ x : MinkowskiModel 2, (conformalFactor k x)⁻¹ ^ 3 = 2 * Real.pi ^ 2 / Real.sqrt k ^ 3 := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have h := Measure.integral_comp_smul (volume : Measure (MinkowskiModel 2))
    (fun x => (conformalFactor k x)⁻¹ ^ 3) (Real.sqrt k)⁻¹
  have hc : ((Real.sqrt k)⁻¹) ^ 2 * k = 1 := by
    rw [inv_pow, Real.sq_sqrt hk.le, inv_mul_cancel₀ hk.ne']
  simp only [conformalFactor_smul, hc, integral_inv_conformalFactor_pow_three,
    Module.finrank_fin_fun, smul_eq_mul] at h
  rw [abs_of_pos (by positivity), inv_pow, inv_inv] at h
  rw [eq_div_iff (by positivity), h]
  ring

/-! ### Instances -/

/-- At the origin the conformal factor is `1`. -/
theorem conformalFactor_origin (k : ℝ) : conformalFactor k 0 = 1 := by
  simp [conformalFactor]

/-- For `k = 0` the conformal factor is `1`. -/
theorem conformalFactor_flat (x : MinkowskiModel 2) : conformalFactor 0 x = 1 := by
  simp [conformalFactor]

/-- The origin lies in every domain. -/
theorem zero_mem_domain (k : ℝ) : (0 : MinkowskiModel 2) ∈ domain k := by
  show 0 < conformalFactor k 0
  rw [conformalFactor_origin]
  exact one_pos

/-- The domain of `k = −1` is the ball `|x|² < 4`. -/
theorem domain_neg_one : domain (-1) = {x | ∑ i, x i ^ 2 < 4} := by
  rw [domain_of_neg (by norm_num)]
  norm_num

/-- At the origin the metric is Euclidean. -/
theorem coefficient_origin (k : ℝ) : coefficient k 0 = 1 := by
  simp [coefficient, conformalFactor_origin]

/-- For `k = 0` the metric is Euclidean everywhere: the space is `ℝ³`. -/
theorem coefficient_flat (x : MinkowskiModel 2) : coefficient 0 x = 1 := by
  simp [coefficient, conformalFactor_flat]

/-- The table vanishes at the origin. -/
theorem christoffel_origin (k : ℝ) (l i j : Fin 3) : christoffel k 0 l i j = 0 := by
  simp [christoffel]

/-- For `k = 0` the table vanishes. -/
theorem christoffel_flat (x : MinkowskiModel 2) (l i j : Fin 3) : christoffel 0 x l i j = 0 := by
  simp [christoffel]

/-- The origin lifts to the pole `(1, 0, 0, 0)`. -/
theorem lift_origin (k : ℝ) : lift k 0 = Pi.single 0 1 := by
  funext A
  refine Fin.cases ?_ (fun a => ?_) A
  · rw [lift_zero, conformalFactor_origin]
    norm_num
  · simp [lift_succ]

/-- For `k = 0` the lift is the inclusion `x ↦ (1, x)` of the hyperplane `X₀ = 1`. -/
theorem lift_flat (x : MinkowskiModel 2) : lift 0 x = Fin.cons 1 x := by
  funext A
  refine Fin.cases ?_ (fun a => ?_) A
  · rw [lift_zero, conformalFactor_flat]
    norm_num
  · rw [lift_succ, conformalFactor_flat]
    simp

/-- The sectional curvature component `R^0_{011} = 1` of the unit sphere at the origin. -/
theorem curvatureOf_sphere_origin :
    curvatureOf (christoffelOf (coefficient 1)) 0 0 0 1 1 = 1 := by
  rw [curvatureOf_eq 1 (zero_mem_domain 1), coefficient_origin]
  simp

/-- The Ricci component `P_{00} = −2` of the open space `k = −1` at the origin. -/
theorem ricciOf_hyperbolic_origin : ricciOf (coefficient (-1)) 0 0 0 = -2 := by
  rw [ricciOf_eq (-1) (zero_mem_domain (-1)), coefficient_origin]
  simp

end ProjectAinos.SmoothGeometry.SpaceForm
