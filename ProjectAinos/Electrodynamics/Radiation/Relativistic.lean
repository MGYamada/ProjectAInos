/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.LienardWiechert
public import ProjectAinos.Electrodynamics.EnergyMomentum
public import ProjectAinos.SmoothGeometry.Euclidean.SphereIntegral
import Mathlib.Tactic

/-!
# Radiation from a rapidly moving charge

The field of Liénard and Wiechert of a charge `e` on a subluminal world line `w` far from the
charge (Landau–Lifshitz, *The Classical Theory of Fields*, §73; units with `c = 1` and
`div E = k⁰`, so that the potentials carry `1/4π`). At the event `(τ + ρ, r(τ) + ρ n)` of the
light cone of the point `r(τ)`, with `ρ > 0`, `‖n‖ = 1`, `v = ṙ(τ)` and `v̇ = r̈(τ)`:

* `sq_mul_inner_poyntingVector_lightCone`: since `B = n × E`, the vector of Poynting `S = E × B`
  has `S·n = |E|² − (E·n)²` (`sum_poyntingVector_mul_eq`), and `ρ² S·n` is
  `e² |n × ((n − v) × v̇)|²/(16π²(1 − n·v)⁶)` plus a cross term of the order `1/ρ` and the square
  of the velocity field of the order `1/ρ²`. The acceleration field
  `E_a = e n × ((n − v) × v̇)/(4πρ(1 − n·v)³)` (`accelerationField_lightCone_eq_cross`) is
  orthogonal to `n` (`inner_accelerationField_lightCone`) and carries the flux `|E_a|²`
  (`sq_mul_inner_cross_cross_accelerationField_lightCone`).
* `tendsto_sq_mul_inner_poyntingVector_lightCone`: as `ρ → ∞`, `ρ² S·n` tends to
  `e² |n × ((n − v) × v̇)|²/(16π²(1 − n·v)⁶)`, the energy per unit solid angle and unit time of
  the observer; `tendsto_sq_mul_inner_poyntingVector_mul_lightCone`: `ρ² (S·n)(1 − n·v)` tends
  to `angularPower e v v̇ n = e² |n × ((n − v) × v̇)|²/(16π²(1 − n·v)⁵)`, the energy per unit
  solid angle and unit retarded time (73.9). At a fixed point of observation
  `∂τ/∂t = 1/(1 − n·v)` (`fderiv_retardedTime_time_lightCone`).
* **The formula of Liénard**, `integral_lienard`: for `|v| < 1`,
  `∫ |n × ((n − v) × a)|²/(1 − n·v)⁵ dσ = (8π/3) γ⁶ (a² − (v × a)²)` with `γ² = 1/(1 − v²)`, so
  that the power per unit retarded time is `(2/3)(e²/4π) γ⁶ (a² − (v × a)²)`
  (`integral_angularPower`, (73.4)), the limit of the energy radiated through the spheres of the
  light cone per unit retarded time (`tendsto_integral_power_lightCone`). With the
  four-acceleration `w`, it is `−(2/3)(e²/4π) w^μ w_μ` (`norm_sq_fourAcceleration`).
* `integral_inner_mul_angularPower`: `∫ (n·v) dI = v² ∫ dI`, the component along `v` of
  `dP = v dE`; `integral_inner_mul_angularPower_of_eq_smul`: `∫ (n·ê) dI = β ∫ dI` for
  `v = β ê`.

`cross u v` is the cross product of `ℝ³ = EuclideanSpace ℝ (Fin 3)` (`crossProduct` of the
components), with `cross_cross` `u × (v × w) = (u·w) v − (u·v) w` and `norm_cross_sq`
`|u × v|² = u²v² − (u·v)²`; for a unit vector `n`,
`|n × ((n − v) × a)|² = (1 − n·v)² a² + 2(1 − n·v)(v·a)(n·a) − (1 − v²)(n·a)²`
(`norm_cross_cross_sq`). The integral over the sphere is computed for `v = β ê` and
`a = α ê + b` with `b ⊥ ê` and a weight `g(n·ê)` (`integral_comp_inner_mul_lienard`): the term
linear in `n·b` vanishes, `(n·b)²` averages to `(b²/2)(1 − (n·ê)²)`, and Archimedes' theorem
reduces the rest to `∫_{−1}^{1} ds/(1 − βs)³ = 2/(1 − β²)²` and
`∫_{−1}^{1} (1 − s²) ds/(1 − βs)⁵ = 4/(3(1 − β²)³)`, and to the same integrals with the factor
`s`, which are `β` times as large; they are computed with explicit antiderivatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped Topology

namespace ProjectAinos.Electrodynamics.Radiation.Relativistic

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.Sphere SmoothGeometry.DifferentialForm
  SpecialRelativity

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The cross product of `ℝ³` -/

/-- The cross product `u × v` of two vectors of `ℝ³ = EuclideanSpace ℝ (Fin 3)`, the product
`crossProduct` of their components. -/
def cross (u v : E3) : E3 := WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))

/-- The components of `u × v` are those of `crossProduct`. -/
theorem ofLp_cross (u v : E3) :
    WithLp.ofLp (cross u v) = crossProduct (WithLp.ofLp u) (WithLp.ofLp v) := rfl

/-- `u × (v × w) = (u·w) v − (u·v) w`. -/
theorem cross_cross (u v w : E3) :
    cross u (cross v w) = inner ℝ u w • v - inner ℝ u v • w := by
  ext i
  fin_cases i <;>
    simp [cross, cross_apply, LienardWiechert.inner_eq_sum] <;> ring

/-- `u · (u × v) = 0`. -/
theorem inner_cross_self (u v : E3) : inner ℝ u (cross u v) = 0 := by
  rw [LienardWiechert.inner_eq_sum]
  simp [cross, cross_apply]
  ring

/-- `|u × v|² = |u|²|v|² − (u·v)²`. -/
theorem norm_cross_sq (u v : E3) : ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - inner ℝ u v ^ 2 := by
  rw [LienardWiechert.norm_sq_eq_sum, LienardWiechert.norm_sq_eq_sum,
    LienardWiechert.norm_sq_eq_sum, LienardWiechert.inner_eq_sum]
  simp [cross, cross_apply]
  ring

/-- For a unit vector `n`,
`|n × ((n − v) × a)|² = (1 − n·v)²|a|² + 2(1 − n·v)(v·a)(n·a) − (1 − v²)(n·a)²`. -/
theorem norm_cross_cross_sq {n : E3} (hn : ‖n‖ = 1) (v a : E3) :
    ‖cross n (cross (n - v) a)‖ ^ 2 =
      (1 - inner ℝ n v) ^ 2 * ‖a‖ ^ 2 + 2 * (1 - inner ℝ n v) * inner ℝ v a * inner ℝ n a -
        (1 - ‖v‖ ^ 2) * inner ℝ n a ^ 2 := by
  have hnn : inner ℝ n n = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hn, one_pow]
  rw [cross_cross, norm_sub_sq_real, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    Real.norm_eq_abs, sq_abs, sq_abs, real_inner_smul_left, real_inner_smul_right,
    norm_sub_sq_real, hn, inner_sub_right, inner_sub_left, hnn]
  ring

/-- `n × w` is orthogonal to `n`, in particular `n × ((n − v) × a)`. -/
theorem inner_cross_cross_left (n v a : E3) : inner ℝ (cross n (cross v a)) n = 0 := by
  rw [real_inner_comm, inner_cross_self]

/-! ### The Poynting vector of a field with `B = n × E` -/

/-- If the magnetic field is `B = n × E` at the event `y`, the component of the vector of
Poynting along `n` is `⟨E × (n × E), n⟩ = |E|²|n|² − (E·n)²`. -/
theorem sum_poyntingVector_mul_eq {G : Field} {y : Spacetime} {n X : Space 3}
    (hE : electricVector (G y) = WithLp.ofLp X)
    (hB : magneticVector (G y) = crossProduct (WithLp.ofLp n) (WithLp.ofLp X)) :
    ∑ i : Fin 3, poyntingVector G i y * n i = ‖X‖ ^ 2 * ‖n‖ ^ 2 - inner ℝ X n ^ 2 := by
  have hE' (i : Fin 3) : electricField G i y = X i := by
    simp only [electricField, hE]
  have hB' (i : Fin 3) : magneticField G i y = crossProduct (WithLp.ofLp n) (WithLp.ofLp X) i := by
    simp only [magneticField, hB]
  simp only [Fin.sum_univ_three, poyntingVector, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hE', hB', cross_apply]
  rw [LienardWiechert.norm_sq_eq_sum, LienardWiechert.norm_sq_eq_sum,
    LienardWiechert.inner_eq_sum]
  simp
  ring

/-- **The acceleration part of the field carries the energy outwards**: for `E ⊥ n` and the
unit vector `n`, `⟨E × (n × E), n⟩ = |E|²`. -/
theorem inner_cross_cross_self {n X : E3} (hn : ‖n‖ = 1) (hX : inner ℝ X n = 0) :
    inner ℝ (cross X (cross n X)) n = ‖X‖ ^ 2 := by
  rw [cross_cross, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hX,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hn]
  ring

/-! ### The field far from the charge -/

variable (w : SubluminalWorldline)

/-- `1 − n·ṙ(τ) > 0` for a unit vector `n`. -/
theorem one_sub_inner_pos (τ : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    0 < 1 - inner ℝ n (deriv w.r τ) := by
  have h1 := real_inner_le_norm n (deriv w.r τ)
  rw [hn, one_mul] at h1
  linarith [w.norm_deriv_le τ, w.v₀_lt_one]

/-- **The flux of energy on the light cone** of the point `r(τ)`: at the event
`(τ + ρ, r(τ) + ρ n)` with `ρ > 0` and `‖n‖ = 1`, the vector of Poynting `S = E × B` of the
field of Liénard and Wiechert has
`ρ² S·n = e²/(16π²(1 − n·v)⁶) (|n × ((n − v) × v̇)|² + 2(1 − v²)(n − v)·(n × ((n − v) × v̇))/ρ
  + (1 − v²)²(|n − v|² − ((n − v)·n)²)/ρ²)` with `v = ṙ(τ)` and `v̇ = r̈(τ)`: the square of the
acceleration field, a cross term of the order `1/ρ` and the square of the velocity field of the
order `1/ρ²`. -/
theorem sq_mul_inner_poyntingVector_lightCone (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3}
    (hn : ‖n‖ = 1) :
    ρ ^ 2 * ∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i =
      e ^ 2 / (16 * π ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 6) *
        (‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ^ 2 +
          2 * (1 - ‖deriv w.r τ‖ ^ 2) *
            inner ℝ (n - deriv w.r τ) (cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))) /
              ρ +
          (1 - ‖deriv w.r τ‖ ^ 2) ^ 2 *
            (‖n - deriv w.r τ‖ ^ 2 - inner ℝ (n - deriv w.r τ) n ^ 2) / ρ ^ 2) := by
  have hE := electricVector_lienardWiechert_lightCone w e (τ := τ) hρ hn
  have hB := magneticVector_lienardWiechert_lightCone w e (τ := τ) hρ hn
  rw [hE] at hB
  rw [sum_poyntingVector_mul_eq hE hB, hn, one_pow, mul_one, ← cross_cross]
  set v := deriv w.r τ
  set R := cross n (cross (n - v) (deriv (deriv w.r) τ))
  have hk := one_sub_inner_pos w τ hn
  have hRn : inner ℝ R n = 0 := inner_cross_cross_left _ _ _
  set k := 1 - inner ℝ n v
  rw [norm_add_sq_real, inner_add_left, norm_smul, norm_smul]
  simp only [real_inner_smul_left, real_inner_smul_right, hRn, mul_pow, Real.norm_eq_abs, sq_abs]
  field_simp
  ring

/-- The acceleration field on the light cone in the form of a double cross product,
`E_a = e n × ((n − v) × v̇)/(4πρ(1 − n·v)³)`. -/
theorem accelerationField_lightCone_eq_cross (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3}
    (hn : ‖n‖ = 1) :
    LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n) =
      (e / (4 * π * ρ * (1 - inner ℝ n (deriv w.r τ)) ^ 3)) •
        cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ)) := by
  rw [LienardWiechert.accelerationField_lightCone w e hρ hn, cross_cross]

/-- The acceleration field on the light cone is orthogonal to the direction `n`. -/
theorem inner_accelerationField_lightCone (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3}
    (hn : ‖n‖ = 1) :
    inner ℝ (LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n)) n = 0 := by
  rw [accelerationField_lightCone_eq_cross w e hρ hn, real_inner_smul_left,
    inner_cross_cross_left, mul_zero]

/-- **The flux of the acceleration field**: with `E_a` the acceleration field and `B_a = n × E_a`,
`⟨E_a × B_a, n⟩ = |E_a|²` and `ρ² |E_a|² = e² |n × ((n − v) × v̇)|²/(16π²(1 − n·v)⁶)`. -/
theorem sq_mul_inner_cross_cross_accelerationField_lightCone (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ)
    {n : Space 3} (hn : ‖n‖ = 1) :
    ρ ^ 2 * inner ℝ (cross (LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n))
        (cross n (LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n)))) n =
      e ^ 2 * ‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ^ 2 /
        (16 * π ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 6) := by
  rw [inner_cross_cross_self hn (inner_accelerationField_lightCone w e hρ hn),
    accelerationField_lightCone_eq_cross w e hρ hn, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]
  have hk := (one_sub_inner_pos w τ hn).ne'
  field_simp
  ring

/-- **The angular distribution of the radiation** (Landau–Lifshitz (73.9)): the energy radiated
per unit solid angle in the direction `n` and per unit retarded time by a charge `e` with the
velocity `v` and the acceleration `a`, `dI/dΩ = e² |n × ((n − v) × a)|²/(16π²(1 − n·v)⁵)`. -/
def angularPower (e : ℝ) (v a n : E3) : ℝ :=
  e ^ 2 * ‖cross n (cross (n - v) a)‖ ^ 2 / (16 * π ^ 2 * (1 - inner ℝ n v) ^ 5)

/-- **The radiation zone**: at the distance `ρ → ∞` along the light cone of `r(τ)`, `ρ² S·n`
tends to `e² |n × ((n − v) × v̇)|²/(16π²(1 − n·v)⁶)`, the energy that crosses a unit solid angle
per unit time `t` of the observer. -/
theorem tendsto_sq_mul_inner_poyntingVector_lightCone (e τ : ℝ) {n : Space 3} (hn : ‖n‖ = 1) :
    Tendsto (fun ρ => ρ ^ 2 * ∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i) atTop
      (𝓝 (e ^ 2 * ‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ^ 2 /
        (16 * π ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 6))) := by
  set C := e ^ 2 / (16 * π ^ 2 * (1 - inner ℝ n (deriv w.r τ)) ^ 6)
  set A := ‖cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ))‖ ^ 2
  set B := 2 * (1 - ‖deriv w.r τ‖ ^ 2) *
    inner ℝ (n - deriv w.r τ) (cross n (cross (n - deriv w.r τ) (deriv (deriv w.r) τ)))
  set D := (1 - ‖deriv w.r τ‖ ^ 2) ^ 2 *
    (‖n - deriv w.r τ‖ ^ 2 - inner ℝ (n - deriv w.r τ) n ^ 2)
  have key : (fun ρ : ℝ => C * (A + B * ρ⁻¹ + D * ρ⁻¹ ^ 2)) =ᶠ[atTop]
      fun ρ => ρ ^ 2 * ∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i := by
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    rw [sq_mul_inner_poyntingVector_lightCone w e hρ hn]
    simp only [C, A, B, D]
    field_simp
  have hlim : Tendsto (fun ρ : ℝ => C * (A + B * ρ⁻¹ + D * ρ⁻¹ ^ 2)) atTop
      (𝓝 (C * (A + B * 0 + D * 0 ^ 2))) :=
    (((tendsto_inv_atTop_zero.const_mul B).const_add A).add
      ((tendsto_inv_atTop_zero.pow 2).const_mul D)).const_mul C
  refine (hlim.congr' key).trans (le_of_eq ?_)
  congr 1
  simp only [C, A]
  ring

/-- **The power per unit retarded time** (Landau–Lifshitz (73.9)): `ρ² (S·n)(1 − n·v)` tends to
`angularPower e v v̇ n = e² |n × ((n − v) × v̇)|²/(16π²(1 − n·v)⁵)`. The factor `1 − n·v` is
`dt/dτ` at a fixed point of observation (`fderiv_retardedTime_time_lightCone`). -/
theorem tendsto_sq_mul_inner_poyntingVector_mul_lightCone (e τ : ℝ) {n : Space 3}
    (hn : ‖n‖ = 1) :
    Tendsto (fun ρ => ρ ^ 2 * (∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i) * (1 - inner ℝ n (deriv w.r τ))) atTop
      (𝓝 (angularPower e (deriv w.r τ) (deriv (deriv w.r) τ) n)) := by
  have hk := (one_sub_inner_pos w τ hn).ne'
  have h := (tendsto_sq_mul_inner_poyntingVector_lightCone w e τ hn).mul_const
    (1 - inner ℝ n (deriv w.r τ))
  convert h using 2
  rw [angularPower]
  field_simp

/-- At the event `(τ + ρ, r(τ) + ρ n)`, the derivative of the retarded time in the time of the
observer at a fixed point is `∂τ/∂t = 1/(1 − n·ṙ(τ))`. -/
theorem fderiv_retardedTime_time_lightCone {τ ρ : ℝ} (hρ : 0 < ρ) {n : Space 3}
    (hn : ‖n‖ = 1) :
    fderiv ℝ (fun p : ℝ × Space 3 => w.retardedTime p.1 p.2) (τ + ρ, w.r τ + ρ • n) (1, 0) =
      (1 - inner ℝ n (deriv w.r τ))⁻¹ := by
  have hoff := LienardWiechert.mem_offWorldline_lightCone w (τ := τ) hρ hn
  simp only [SubluminalWorldline.offWorldline, Set.mem_ofPred_eq, space_vector, vector_zero] at hoff
  rw [w.fderiv_retardedTime_time hoff, w.retardedDenominator_eq_mul,
    retardedDirection_lightCone w hρ hn]
  have hnorm : ‖ρ • n‖ = ρ := by rw [norm_smul, hn, mul_one, Real.norm_of_nonneg hρ.le]
  have hsep : w.retardedSeparation (τ + ρ) (w.r τ + ρ • n) = ρ • n := by
    have h := w.retardedSeparation_add_norm τ (ρ • n)
    rwa [hnorm] at h
  have hvel : w.retardedVelocity (τ + ρ) (w.r τ + ρ • n) = deriv w.r τ := by
    have h := w.retardedVelocity_add_norm τ (ρ • n)
    rwa [hnorm] at h
  rw [hsep, hvel, hnorm]
  have hk := (one_sub_inner_pos w τ hn).ne'
  field_simp

/-! ### Four integrals over `[−1, 1]` -/

/-- `1 − βs > 0` for `|β| < 1` and `s ∈ [−1, 1]`. -/
theorem one_sub_mul_pos {β : ℝ} (hβ : |β| < 1) {s : ℝ} (hs : s ∈ Icc (-1 : ℝ) 1) :
    0 < 1 - β * s := by
  have h1 : |β * s| ≤ |β| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_le.mpr hs)
  linarith [le_abs_self (β * s)]

/-- `p(s)/(1 − βs)ᵐ` is continuous on `[−1, 1]` for `|β| < 1` and `p` continuous there. -/
theorem continuousOn_div_one_sub_mul_pow {β : ℝ} (hβ : |β| < 1) {p : ℝ → ℝ}
    (hp : ContinuousOn p (Icc (-1) 1)) (m : ℕ) :
    ContinuousOn (fun s => p s / (1 - β * s) ^ m) (Icc (-1) 1) :=
  hp.div (by fun_prop) fun s hs => (pow_pos (one_sub_mul_pos hβ hs) m).ne'

private theorem uIcc_neg_one_one : uIcc (-1 : ℝ) 1 = Icc (-1) 1 := uIcc_of_le (by norm_num)

private theorem hasDerivAt_one_sub_mul_pow (β c : ℝ) (m : ℕ) (s : ℝ) :
    HasDerivAt (fun s => c * (1 - β * s) ^ m) (c * (m * (1 - β * s) ^ (m - 1) * (0 - β * 1))) s :=
  (((hasDerivAt_const s (1 : ℝ)).fun_sub ((hasDerivAt_id' s).const_mul β)).fun_pow m).const_mul c

private theorem ne_zero_of_abs_lt {β : ℝ} (hβ : |β| < 1) :
    1 - β ≠ 0 ∧ 1 + β ≠ 0 ∧ 1 - β ^ 2 ≠ 0 := by
  have h1 : 1 - β ≠ 0 := by linarith [(abs_lt.mp hβ).2]
  have h2 : 1 + β ≠ 0 := by linarith [(abs_lt.mp hβ).1]
  refine ⟨h1, h2, ?_⟩
  have : 1 - β ^ 2 = (1 - β) * (1 + β) := by ring
  rw [this]
  exact mul_ne_zero h1 h2

/-- `∫_{−1}^{1} ds/(1 − βs)³ = 2/(1 − β²)²`. -/
theorem integral_one_div_one_sub_mul_pow_three {β : ℝ} (hβ : |β| < 1) :
    ∫ s in (-1 : ℝ)..1, 1 / (1 - β * s) ^ 3 = 2 / (1 - β ^ 2) ^ 2 := by
  have hF : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt
      (fun s => (2 * s - β * s ^ 2) / (2 * (1 - β * s) ^ 2)) (1 / (1 - β * s) ^ 3) s := by
    intro s hs
    rw [uIcc_neg_one_one] at hs
    have hk := (one_sub_mul_pos hβ hs).ne'
    have hp := ((hasDerivAt_id' s).const_mul 2).fun_sub ((hasDerivAt_pow 2 s).const_mul β)
    convert hp.div (hasDerivAt_one_sub_mul_pow β 2 2 s) (by positivity) using 1
    norm_num
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (ContinuousOn.intervalIntegrable (by
      rw [uIcc_neg_one_one]
      exact continuousOn_div_one_sub_mul_pow hβ continuousOn_const 3))]
  obtain ⟨h1, h2, h3⟩ := ne_zero_of_abs_lt hβ
  norm_num
  field_simp
  ring

/-- `∫_{−1}^{1} s ds/(1 − βs)³ = 2β/(1 − β²)²`. -/
theorem integral_div_one_sub_mul_pow_three {β : ℝ} (hβ : |β| < 1) :
    ∫ s in (-1 : ℝ)..1, s / (1 - β * s) ^ 3 = 2 * β / (1 - β ^ 2) ^ 2 := by
  have hF : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt
      (fun s => s ^ 2 / (2 * (1 - β * s) ^ 2)) (s / (1 - β * s) ^ 3) s := by
    intro s hs
    rw [uIcc_neg_one_one] at hs
    have hk := (one_sub_mul_pos hβ hs).ne'
    convert (hasDerivAt_pow 2 s).div (hasDerivAt_one_sub_mul_pow β 2 2 s) (by positivity) using 1
    norm_num
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (ContinuousOn.intervalIntegrable (by
      rw [uIcc_neg_one_one]
      exact continuousOn_div_one_sub_mul_pow hβ continuousOn_id 3))]
  obtain ⟨h1, h2, h3⟩ := ne_zero_of_abs_lt hβ
  norm_num
  field_simp
  ring

/-- `∫_{−1}^{1} (1 − s²) ds/(1 − βs)⁵ = 4/(3(1 − β²)³)`. -/
theorem integral_one_sub_sq_div_one_sub_mul_pow_five {β : ℝ} (hβ : |β| < 1) :
    ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) / (1 - β * s) ^ 5 = 4 / (3 * (1 - β ^ 2) ^ 3) := by
  have hF : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt
      (fun s => (12 * s - 18 * β * s ^ 2 + (12 * β ^ 2 - 4) * s ^ 3 + (β - 3 * β ^ 3) * s ^ 4) /
        (12 * (1 - β * s) ^ 4)) ((1 - s ^ 2) / (1 - β * s) ^ 5) s := by
    intro s hs
    rw [uIcc_neg_one_one] at hs
    have hk := (one_sub_mul_pos hβ hs).ne'
    have hp := ((((hasDerivAt_id' s).const_mul 12).fun_sub
      ((hasDerivAt_pow 2 s).const_mul (18 * β))).fun_add
        ((hasDerivAt_pow 3 s).const_mul (12 * β ^ 2 - 4))).fun_add
          ((hasDerivAt_pow 4 s).const_mul (β - 3 * β ^ 3))
    convert hp.div (hasDerivAt_one_sub_mul_pow β 12 4 s) (by positivity) using 1
    norm_num
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (ContinuousOn.intervalIntegrable (by
      rw [uIcc_neg_one_one]
      exact continuousOn_div_one_sub_mul_pow hβ (by fun_prop) 5))]
  obtain ⟨h1, h2, h3⟩ := ne_zero_of_abs_lt hβ
  norm_num
  field_simp
  ring

/-- `∫_{−1}^{1} s (1 − s²) ds/(1 − βs)⁵ = 4β/(3(1 − β²)³)`. -/
theorem integral_mul_one_sub_sq_div_one_sub_mul_pow_five {β : ℝ} (hβ : |β| < 1) :
    ∫ s in (-1 : ℝ)..1, s * (1 - s ^ 2) / (1 - β * s) ^ 5 = 4 * β / (3 * (1 - β ^ 2) ^ 3) := by
  have hF : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt
      (fun s => (6 * s ^ 2 - 4 * β * s ^ 3 + (β ^ 2 - 3) * s ^ 4) / (12 * (1 - β * s) ^ 4))
      (s * (1 - s ^ 2) / (1 - β * s) ^ 5) s := by
    intro s hs
    rw [uIcc_neg_one_one] at hs
    have hk := (one_sub_mul_pos hβ hs).ne'
    have hp := (((hasDerivAt_pow 2 s).const_mul 6).fun_sub
      ((hasDerivAt_pow 3 s).const_mul (4 * β))).fun_add
        ((hasDerivAt_pow 4 s).const_mul (β ^ 2 - 3))
    convert hp.div (hasDerivAt_one_sub_mul_pow β 12 4 s) (by positivity) using 1
    norm_num
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
    (ContinuousOn.intervalIntegrable (by
      rw [uIcc_neg_one_one]
      exact continuousOn_div_one_sub_mul_pow hβ (by fun_prop) 5))]
  obtain ⟨h1, h2, h3⟩ := ne_zero_of_abs_lt hβ
  norm_num
  field_simp
  ring

/-! ### The formula of Liénard -/

/-- **The angular integrals of the radiation of a moving charge.** For a unit vector `ê`, the
velocity `v = β ê` with `|β| < 1`, the acceleration `a = α ê + b` with `α = a·ê` and `b ⊥ ê`,
and `g` continuous on `[−1, 1]`, `∫ g(n·ê) |n × ((n − v) × a)|²/(1 − n·v)⁵ dσ` is
`2π (α² ∫ g(s)(1 − s²)/(1 − βs)⁵ ds + |b|² (∫ g(s)/(1 − βs)³ ds
  − ((1 − β²)/2) ∫ g(s)(1 − s²)/(1 − βs)⁵ ds))`, the integrals over `[−1, 1]`. -/
theorem integral_comp_inner_mul_lienard {ê : E3} (he : ‖ê‖ = 1) {β : ℝ} (hβ : |β| < 1)
    (a : E3) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (-1) 1)) :
    ∫ n : sphere (0 : E3) 1, g (inner ℝ (n : E3) ê) *
        (‖cross n (cross ((n : E3) - β • ê) a)‖ ^ 2 / (1 - inner ℝ (n : E3) (β • ê)) ^ 5)
        ∂sphereMeasure =
      2 * π * (inner ℝ a ê ^ 2 * (∫ s in (-1 : ℝ)..1, g s * (1 - s ^ 2) / (1 - β * s) ^ 5) +
        ‖a - inner ℝ a ê • ê‖ ^ 2 * ((∫ s in (-1 : ℝ)..1, g s / (1 - β * s) ^ 3) -
          (1 - β ^ 2) / 2 * ∫ s in (-1 : ℝ)..1, g s * (1 - s ^ 2) / (1 - β * s) ^ 5)) := by
  set α := inner ℝ a ê with hα
  set b := a - α • ê with hb
  have hbe : inner ℝ b ê = 0 := by
    rw [hb, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
    ring
  have hab : a = α • ê + b := by
    rw [hb]
    abel
  set K₁ : ℝ → ℝ := fun s => g s * (1 - s ^ 2) / (1 - β * s) ^ 5 with hK₁
  set K₃ : ℝ → ℝ := fun s => g s / (1 - β * s) ^ 3 with hK₃
  set H : ℝ → ℝ := fun s => g s * (2 * α * (β - s)) / (1 - β * s) ^ 5 with hH
  set K₅ : ℝ → ℝ := fun s => g s / (1 - β * s) ^ 5 with hK₅
  have cK₁ : ContinuousOn K₁ (Icc (-1) 1) :=
    continuousOn_div_one_sub_mul_pow hβ (hg.mul (by fun_prop)) 5
  have cK₃ : ContinuousOn K₃ (Icc (-1) 1) := continuousOn_div_one_sub_mul_pow hβ hg 3
  have cH : ContinuousOn H (Icc (-1) 1) :=
    continuousOn_div_one_sub_mul_pow hβ (hg.mul (by fun_prop)) 5
  have cK₅ : ContinuousOn K₅ (Icc (-1) 1) := continuousOn_div_one_sub_mul_pow hβ hg 5
  have hpt : ∀ n : sphere (0 : E3) 1, g (inner ℝ (n : E3) ê) *
        (‖cross n (cross ((n : E3) - β • ê) a)‖ ^ 2 / (1 - inner ℝ (n : E3) (β • ê)) ^ 5) =
      α ^ 2 * K₁ (inner ℝ (n : E3) ê) + ‖b‖ ^ 2 * K₃ (inner ℝ (n : E3) ê) +
        (inner ℝ (n : E3) b * H (inner ℝ (n : E3) ê) -
          (1 - β ^ 2) * (inner ℝ (n : E3) b ^ 2 * K₅ (inner ℝ (n : E3) ê))) := by
    intro n
    have hn : ‖(n : E3)‖ = 1 := norm_eq_of_mem_sphere n
    have hk := (one_sub_mul_pos hβ (inner_mem_Icc he n)).ne'
    have hna : inner ℝ (n : E3) a = α * inner ℝ (n : E3) ê + inner ℝ (n : E3) b := by
      conv_lhs => rw [hab]
      rw [inner_add_right, real_inner_smul_right]
    have hnorm : ‖a‖ ^ 2 = α ^ 2 + ‖b‖ ^ 2 := by
      conv_lhs => rw [hab]
      rw [norm_add_sq_real, real_inner_smul_left, real_inner_comm, hbe, norm_smul, he,
        Real.norm_eq_abs, mul_one, sq_abs]
      ring
    have hva : inner ℝ (β • ê) a = β * α := by
      rw [real_inner_smul_left, real_inner_comm]
    have hnv : inner ℝ (n : E3) (β • ê) = β * inner ℝ (n : E3) ê := real_inner_smul_right _ _ _
    have hvv : ‖β • ê‖ ^ 2 = β ^ 2 := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
    rw [norm_cross_cross_sq hn, hna, hnorm, hva, hnv, hvv]
    simp only [hK₁, hK₃, hH, hK₅]
    field_simp
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have iK₁ : Integrable (fun n : sphere (0 : E3) 1 => α ^ 2 * K₁ (inner ℝ (n : E3) ê))
      sphereMeasure :=
    integrable_of_continuous (continuous_const.mul (continuous_comp_inner he cK₁))
  have iK₃ : Integrable (fun n : sphere (0 : E3) 1 => ‖b‖ ^ 2 * K₃ (inner ℝ (n : E3) ê))
      sphereMeasure :=
    integrable_of_continuous (continuous_const.mul (continuous_comp_inner he cK₃))
  have iH : Integrable (fun n : sphere (0 : E3) 1 => inner ℝ (n : E3) b * H (inner ℝ (n : E3) ê))
      sphereMeasure := integrable_of_continuous
        ((continuous_subtype_val.inner continuous_const).mul (continuous_comp_inner he cH))
  have iK₅ : Integrable (fun n : sphere (0 : E3) 1 =>
      (1 - β ^ 2) * (inner ℝ (n : E3) b ^ 2 * K₅ (inner ℝ (n : E3) ê))) sphereMeasure :=
    integrable_of_continuous (continuous_const.mul
      (((continuous_subtype_val.inner continuous_const).pow 2).mul (continuous_comp_inner he cK₅)))
  have iA : Integrable (fun n : sphere (0 : E3) 1 => α ^ 2 * K₁ (inner ℝ (n : E3) ê) +
      ‖b‖ ^ 2 * K₃ (inner ℝ (n : E3) ê)) sphereMeasure := iK₁.add iK₃
  have iB : Integrable (fun n : sphere (0 : E3) 1 => inner ℝ (n : E3) b * H (inner ℝ (n : E3) ê) -
      (1 - β ^ 2) * (inner ℝ (n : E3) b ^ 2 * K₅ (inner ℝ (n : E3) ê))) sphereMeasure :=
    iH.sub iK₅
  rw [integral_add iA iB, integral_add iK₁ iK₃, integral_sub iH iK₅,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_comp_inner he cK₁,
    integral_comp_inner he cK₃, integral_inner_mul_comp_inner he hbe cH,
    integral_inner_sq_mul_comp_inner he hbe cK₅]
  have h5 := integral_comp_inner he (g := fun s => (1 - s ^ 2) * K₅ s)
    ((continuousOn_const.sub (continuousOn_id.pow 2)).mul cK₅)
  rw [h5]
  have h15 : ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) * K₅ s = ∫ s in (-1 : ℝ)..1, K₁ s := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hK₁, hK₅]
    ring
  rw [h15]
  ring

private theorem exists_unit_smul_eq (v : E3) : ∃ ê : E3, ‖ê‖ = 1 ∧ v = ‖v‖ • ê := by
  by_cases hv : v = 0
  · exact ⟨EuclideanSpace.single 0 1, by simp, by simp [hv]⟩
  · have h := norm_ne_zero_iff.mpr hv
    refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h]
    · rw [smul_smul, mul_inv_cancel₀ h, one_smul]

/-- **The formula of Liénard** (Landau–Lifshitz (73.4)): for `|v| < 1`,
`∫ |n × ((n − v) × a)|²/(1 − n·v)⁵ dσ = (8π/3) γ⁶ (|a|² − |v × a|²)` with
`γ² = 1/(1 − v²)`. -/
theorem integral_lienard {v : E3} (hv : ‖v‖ < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, ‖cross n (cross ((n : E3) - v) a)‖ ^ 2 /
        (1 - inner ℝ (n : E3) v) ^ 5 ∂sphereMeasure =
      8 * π / 3 * ((1 - ‖v‖ ^ 2)⁻¹) ^ 3 * (‖a‖ ^ 2 - ‖cross v a‖ ^ 2) := by
  obtain ⟨ê, he, hvê⟩ := exists_unit_smul_eq v
  set β := ‖v‖ with hβdef
  have hβ : |β| < 1 := by
    rw [abs_of_nonneg (norm_nonneg v)]
    exact hv
  have hβ0 : 0 ≤ β := norm_nonneg v
  have h := integral_comp_inner_mul_lienard he hβ a (g := fun _ => 1) continuousOn_const
  simp only [one_mul] at h
  rw [hvê, h, integral_one_div_one_sub_mul_pow_three hβ,
    integral_one_sub_sq_div_one_sub_mul_pow_five hβ, norm_cross_sq, norm_smul, he,
    real_inner_smul_left, Real.norm_eq_abs, abs_of_nonneg hβ0]
  have hnorm : ‖a‖ ^ 2 = inner ℝ a ê ^ 2 + ‖a - inner ℝ a ê • ê‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, he, Real.norm_eq_abs, mul_one,
      sq_abs]
    ring
  rw [real_inner_comm a ê, hnorm]
  obtain ⟨h1, h2, h3⟩ := ne_zero_of_abs_lt hβ
  field_simp
  ring

/-! ### The power radiated by the charge -/

/-- `1 − n·v > 0` on the unit sphere for `|v| < 1`. -/
theorem one_sub_inner_pos_of_norm_lt {v : E3} (hv : ‖v‖ < 1) (n : sphere (0 : E3) 1) :
    0 < 1 - inner ℝ (n : E3) v := by
  have h1 := real_inner_le_norm (n : E3) v
  rw [norm_eq_of_mem_sphere n, one_mul] at h1
  linarith

/-- The angular distribution is not negative. -/
theorem angularPower_nonneg (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (a : E3) (n : sphere (0 : E3) 1) :
    0 ≤ angularPower e v a n := by
  have hk := one_sub_inner_pos_of_norm_lt hv n
  rw [angularPower]
  positivity

/-- The angular distribution is continuous on the unit sphere for `|v| < 1`. -/
theorem continuous_angularPower (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (a : E3) :
    Continuous fun n : sphere (0 : E3) 1 => angularPower e v a n := by
  simp only [angularPower, cross_cross]
  exact Continuous.div (by fun_prop) (by fun_prop) fun n =>
    (by have := one_sub_inner_pos_of_norm_lt hv n; positivity)

/-- The angular distribution for a velocity orthogonal to the acceleration:
`dI/dΩ = (e²/16π²)(|a|²/(1 − n·v)³ − (1 − v²)(n·a)²/(1 − n·v)⁵)`. -/
theorem angularPower_of_inner_eq_zero (e : ℝ) {v a : E3} (hv : ‖v‖ < 1)
    (hva : inner ℝ v a = 0) {n : E3} (hn : ‖n‖ = 1) :
    angularPower e v a n = e ^ 2 / (16 * π ^ 2) *
      (‖a‖ ^ 2 / (1 - inner ℝ n v) ^ 3 -
        (1 - ‖v‖ ^ 2) * inner ℝ n a ^ 2 / (1 - inner ℝ n v) ^ 5) := by
  have hk : 0 < 1 - inner ℝ n v := by
    have h1 := real_inner_le_norm n v
    rw [hn, one_mul] at h1
    linarith
  rw [angularPower, norm_cross_cross_sq hn, hva]
  field_simp
  ring

/-- **The total power** (Landau–Lifshitz (73.4)): the energy radiated per unit retarded time by
the charge `e` with the velocity `v` (`|v| < 1`) and the acceleration `a` is
`∫ dI/dΩ dσ = (2/3)(e²/4π) γ⁶ (a² − (v × a)²)`. -/
theorem integral_angularPower (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, angularPower e v a n ∂sphereMeasure =
      2 / 3 * (e ^ 2 / (4 * π)) * ((1 - ‖v‖ ^ 2)⁻¹) ^ 3 * (‖a‖ ^ 2 - ‖cross v a‖ ^ 2) := by
  have h : ∀ n : sphere (0 : E3) 1, angularPower e v a n = e ^ 2 / (16 * π ^ 2) *
      (‖cross n (cross ((n : E3) - v) a)‖ ^ 2 / (1 - inner ℝ (n : E3) v) ^ 5) := by
    intro n
    rw [angularPower, div_mul_div_comm]
  rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_const_mul, integral_lienard hv]
  field_simp
  ring

/-- **The momentum radiated along the velocity**: for `v = β ê` with a unit vector `ê` and
`|β| < 1`, `∫ (n·ê) dI/dΩ dσ = β ∫ dI/dΩ dσ`. -/
theorem integral_inner_mul_angularPower_of_eq_smul (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ}
    (hβ : |β| < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) ê * angularPower e (β • ê) a n ∂sphereMeasure =
      β * ∫ n : sphere (0 : E3) 1, angularPower e (β • ê) a n ∂sphereMeasure := by
  have h : ∀ n : sphere (0 : E3) 1, angularPower e (β • ê) a n = e ^ 2 / (16 * π ^ 2) *
      (‖cross n (cross ((n : E3) - β • ê) a)‖ ^ 2 / (1 - inner ℝ (n : E3) (β • ê)) ^ 5) := by
    intro n
    rw [angularPower, div_mul_div_comm]
  have h' : ∀ n : sphere (0 : E3) 1, inner ℝ (n : E3) ê * angularPower e (β • ê) a n =
      e ^ 2 / (16 * π ^ 2) * (inner ℝ (n : E3) ê *
        (‖cross n (cross ((n : E3) - β • ê) a)‖ ^ 2 / (1 - inner ℝ (n : E3) (β • ê)) ^ 5)) := by
    intro n
    rw [h]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h'),
    integral_congr_ae (Filter.Eventually.of_forall h), integral_const_mul, integral_const_mul]
  have h1 := integral_comp_inner_mul_lienard he hβ a (g := fun _ => 1) continuousOn_const
  have hs := integral_comp_inner_mul_lienard he hβ a (g := fun s => s) (continuousOn_id' _)
  simp only [one_mul] at h1
  rw [h1, hs, integral_one_div_one_sub_mul_pow_three hβ,
    integral_one_sub_sq_div_one_sub_mul_pow_five hβ, integral_div_one_sub_mul_pow_three hβ,
    integral_mul_one_sub_sq_div_one_sub_mul_pow_five hβ]
  ring

/-- The momentum radiated per unit retarded time has the component `v·P = v² I` along the
velocity: `∫ (n·v) dI/dΩ dσ = v² ∫ dI/dΩ dσ`, as for `dP = v dE`. -/
theorem integral_inner_mul_angularPower (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (a : E3) :
    ∫ n : sphere (0 : E3) 1, inner ℝ (n : E3) v * angularPower e v a n ∂sphereMeasure =
      ‖v‖ ^ 2 * ∫ n : sphere (0 : E3) 1, angularPower e v a n ∂sphereMeasure := by
  obtain ⟨ê, he, hvê⟩ := exists_unit_smul_eq v
  set β := ‖v‖ with hβdef
  have hβ : |β| < 1 := by
    rw [abs_of_nonneg (norm_nonneg v)]
    exact hv
  rw [hvê]
  have h : ∀ n : sphere (0 : E3) 1, inner ℝ (n : E3) (β • ê) * angularPower e (β • ê) a n =
      β * (inner ℝ (n : E3) ê * angularPower e (β • ê) a n) := by
    intro n
    rw [real_inner_smul_right]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_const_mul,
    integral_inner_mul_angularPower_of_eq_smul e he hβ a]
  ring

/-- **The four-vector form of the power** (Landau–Lifshitz (73.4)): with `γ²(1 − v²) = 1`, the
four-acceleration `w = du/ds` of the four-velocity `u = γ(1, v)` has `w⁰ = γ⁴ v·a` and
`𝐰 = γ² a + γ⁴ (v·a) v`, and `−w^μ w_μ = |𝐰|² − (w⁰)² = γ⁶ (a² − (v × a)²)`, so that the power
is `−(2/3)(e²/4π) w^μ w_μ`. -/
theorem norm_sq_fourAcceleration {v a : E3} {γ : ℝ} (hγ : γ ^ 2 * (1 - ‖v‖ ^ 2) = 1) :
    ‖γ ^ 2 • a + (γ ^ 4 * inner ℝ v a) • v‖ ^ 2 - (γ ^ 4 * inner ℝ v a) ^ 2 =
      γ ^ 6 * (‖a‖ ^ 2 - ‖cross v a‖ ^ 2) := by
  rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
    norm_cross_sq, mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs,
    real_inner_comm v a]
  linear_combination (-(γ ^ 4 * ‖a‖ ^ 2 + γ ^ 6 * inner ℝ v a ^ 2)) * hγ

/-- **The energy radiated per unit retarded time through the sphere of the light cone**: the
flux `∫ ρ² (S·n)(1 − n·v) dσ` through the sphere of radius `ρ` about the retarded position
`r(τ)` at the time `τ + ρ`, per unit retarded time, tends to
`(2/3)(e²/4π) γ⁶ (v̇² − (v × v̇)²)` as `ρ → ∞` (Landau–Lifshitz (73.4)). -/
theorem tendsto_integral_power_lightCone (e τ : ℝ) :
    Tendsto (fun ρ => ∫ n : sphere (0 : E3) 1, ρ ^ 2 * (∑ i : Fin 3,
        poyntingVector (fieldTensor (lienardWiechert e w)) i
          (Minkowski.vector (τ + ρ) (w.r τ + ρ • (n : E3))) * (n : E3) i) *
        (1 - inner ℝ (n : E3) (deriv w.r τ)) ∂sphereMeasure) atTop
      (𝓝 (2 / 3 * (e ^ 2 / (4 * π)) * ((1 - ‖deriv w.r τ‖ ^ 2)⁻¹) ^ 3 *
        (‖deriv (deriv w.r) τ‖ ^ 2 - ‖cross (deriv w.r τ) (deriv (deriv w.r) τ)‖ ^ 2))) := by
  have hv : ‖deriv w.r τ‖ < 1 := lt_of_le_of_lt (w.norm_deriv_le τ) w.v₀_lt_one
  set v := deriv w.r τ with hvdef
  set a := deriv (deriv w.r) τ with hadef
  set P : sphere (0 : E3) 1 → ℝ := fun n => angularPower e v a n with hP
  set B : sphere (0 : E3) 1 → ℝ := fun n =>
    e ^ 2 / (16 * π ^ 2 * (1 - inner ℝ (n : E3) v) ^ 5) *
      (2 * (1 - ‖v‖ ^ 2) * inner ℝ ((n : E3) - v) (cross n (cross ((n : E3) - v) a))) with hB
  set C : sphere (0 : E3) 1 → ℝ := fun n =>
    e ^ 2 / (16 * π ^ 2 * (1 - inner ℝ (n : E3) v) ^ 5) *
      ((1 - ‖v‖ ^ 2) ^ 2 * (‖(n : E3) - v‖ ^ 2 - inner ℝ ((n : E3) - v) n ^ 2)) with hC
  have hpt (ρ : ℝ) (hρ : 0 < ρ) (n : sphere (0 : E3) 1) :
      ρ ^ 2 * (∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
          (Minkowski.vector (τ + ρ) (w.r τ + ρ • (n : E3))) * (n : E3) i) *
          (1 - inner ℝ (n : E3) v) = P n + ρ⁻¹ * B n + ρ⁻¹ ^ 2 * C n := by
    have hn := norm_eq_of_mem_sphere n
    have hk : 0 < 1 - inner ℝ (n : E3) v := one_sub_inner_pos w τ hn
    rw [sq_mul_inner_poyntingVector_lightCone w e hρ hn, ← hvdef, ← hadef]
    simp only [hP, hB, hC, angularPower]
    field_simp
  have hden (n : sphere (0 : E3) 1) : 16 * π ^ 2 * (1 - inner ℝ (n : E3) v) ^ 5 ≠ 0 := by
    have := one_sub_inner_pos_of_norm_lt hv n
    positivity
  have cB : Continuous B := by
    simp only [hB, cross_cross]
    exact (continuous_const.div (by fun_prop) hden).mul (by fun_prop)
  have cC : Continuous C := by
    simp only [hC]
    exact (continuous_const.div (by fun_prop) hden).mul (by fun_prop)
  have iP : Integrable P sphereMeasure := integrable_of_continuous (continuous_angularPower e hv a)
  have key : (fun ρ : ℝ => (∫ n, P n ∂sphereMeasure) + ρ⁻¹ * (∫ n, B n ∂sphereMeasure) +
      ρ⁻¹ ^ 2 * (∫ n, C n ∂sphereMeasure)) =ᶠ[atTop]
      fun ρ => ∫ n : sphere (0 : E3) 1, ρ ^ 2 * (∑ i : Fin 3,
        poyntingVector (fieldTensor (lienardWiechert e w)) i
          (Minkowski.vector (τ + ρ) (w.r τ + ρ • (n : E3))) * (n : E3) i) *
        (1 - inner ℝ (n : E3) v) ∂sphereMeasure := by
    filter_upwards [eventually_gt_atTop 0] with ρ hρ
    rw [integral_congr_ae (Filter.Eventually.of_forall (hpt ρ hρ))]
    have i1 : Integrable (fun n : sphere (0 : E3) 1 => ρ⁻¹ * B n) sphereMeasure :=
      (integrable_of_continuous cB).const_mul _
    have i2 : Integrable (fun n : sphere (0 : E3) 1 => ρ⁻¹ ^ 2 * C n) sphereMeasure :=
      (integrable_of_continuous cC).const_mul _
    have i3 : Integrable (fun n : sphere (0 : E3) 1 => P n + ρ⁻¹ * B n) sphereMeasure :=
      iP.add i1
    rw [integral_add i3 i2, integral_add iP i1, integral_const_mul, integral_const_mul]
  refine Tendsto.congr' key ?_
  have hPint : ∫ n, P n ∂sphereMeasure =
      2 / 3 * (e ^ 2 / (4 * π)) * ((1 - ‖v‖ ^ 2)⁻¹) ^ 3 * (‖a‖ ^ 2 - ‖cross v a‖ ^ 2) :=
    integral_angularPower e hv a
  rw [← hPint]
  have hlim := ((tendsto_inv_atTop_zero.mul_const (∫ n, B n ∂sphereMeasure)).const_add
      (∫ n, P n ∂sphereMeasure)).add
    ((tendsto_inv_atTop_zero.pow 2).mul_const (∫ n, C n ∂sphereMeasure))
  simpa using hlim

end ProjectAinos.Electrodynamics.Radiation.Relativistic
