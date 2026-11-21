/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.HamiltonianField
public import ProjectAinos.Mechanics.Poisson.RigidBodyMotion
public import ProjectAinos.SmoothGeometry.ODE.JacobiElliptic
public import ProjectAinos.SpecialFunctions.JacobiCurves

/-!
# The asymmetrical top: the solution by elliptic functions

Euler's equations for the free body are, in the body frame,

`L̇₀ = a₀ L₁ L₂`, `L̇₁ = a₁ L₂ L₀`, `L̇₂ = a₂ L₀ L₁`,

with `a₀ = 1/I₂ − 1/I₁`, `a₁ = 1/I₀ − 1/I₂`, `a₂ = 1/I₁ − 1/I₀`
(`eulerField`, the vector field of the Lie–Poisson bracket). For
`I₀ < I₁ < I₂` the signs are `a₀ < 0 < a₁` and `a₂ < 0`.

* `hasDerivAt_jacobiCurve`: a curve `(A cn, B sn, C dn)(p t)` solves a system
  of this form when three algebraic relations hold between the amplitudes, the
  rate `p` and the modulus.
* `hasDerivAt_ellipticMotion`: the motion from the point `(A, 0, C)` of the
  plane of the axes `0` and `2`, when `a₂ A² > a₀ C²` (that is,
  `M² > 2E I₁`), is `(A cn, (a₁ A/q) sn, C dn)(C q t)` with `q = √(−a₀ a₁)`
  and the modulus `k² = a₂ A² / (a₀ C²)` (Landau–Lifshitz (37.10)).
  `flow_eulerField_ellipticMotion` states that this is the solution, and
  `ellipticMotion_add_period` that it has the period `2 · 2K / (C q)`.
* `hasDerivAt_ellipticMotion'`: in the other regime, `a₂ A² < a₀ C²`, the
  roles of the axes `0` and `2` are exchanged.
* `isTrajectory_ellipticTrajectory`: the motion is a trajectory of the
  Lie–Poisson bracket.
-/

@[expose] public section
noncomputable section

open Set
open scoped Real ContDiff

namespace ProjectAinos.Mechanics.RigidBody

open SmoothAlgebra SmoothRing FreeSmoothRing
open SmoothGeometry SmoothGeometry.NonlinearODE SmoothGeometry.JacobiElliptic

/-- The vector field of Euler's equations for the free body, on the space of
the angular momentum in the body frame. -/
def eulerField (I : Fin 3 → ℝ) : (Fin 3 → ℝ) → Fin 3 → ℝ :=
  realField (poisson.hamiltonian (kineticEnergy I))

theorem contDiff_eulerField (I : Fin 3 → ℝ) : ContDiff ℝ ∞ (eulerField I) :=
  contDiff_realField _

theorem eulerField_zero (I : Fin 3 → ℝ) (L : Fin 3 → ℝ) :
    eulerField I L 0 = ((I 2)⁻¹ - (I 1)⁻¹) * (L 1 * L 2) := by
  change (poisson.bracket (RigidBody.L 0) (kineticEnergy I)).val L = _
  rw [euler_equation_zero]
  rfl

theorem eulerField_one (I : Fin 3 → ℝ) (L : Fin 3 → ℝ) :
    eulerField I L 1 = ((I 0)⁻¹ - (I 2)⁻¹) * (L 2 * L 0) := by
  change (poisson.bracket (RigidBody.L 1) (kineticEnergy I)).val L = _
  rw [euler_equation_one]
  rfl

theorem eulerField_two (I : Fin 3 → ℝ) (L : Fin 3 → ℝ) :
    eulerField I L 2 = ((I 1)⁻¹ - (I 0)⁻¹) * (L 0 * L 1) := by
  change (poisson.bracket (RigidBody.L 2) (kineticEnergy I)).val L = _
  rw [euler_equation_two]
  rfl

export ProjectAinos.SpecialFunctions.JacobiElliptic
  (jacobiCurve jacobiCurve_zero hasDerivAt_jacobiCurve jacobiCurve' jacobiCurve'_zero
   hasDerivAt_jacobiCurve' exists_cos_sin_eq exists_jacobiCurve_eq jacobiCurve'_eq)

/-! ### The motion of the asymmetrical top -/

private theorem relation_first {a b q A C : ℝ} (hq : q ≠ 0) (hq2 : q ^ 2 = -(a * b)) :
    -(A * (C * q)) = a * (b * A / q * C) := by
  have hab : a * b = -(q ^ 2) := by linarith
  calc -(A * (C * q)) = -(q ^ 2) * A * C / q := by field_simp
    _ = a * b * A * C / q := by rw [hab]
    _ = a * (b * A / q * C) := by ring

private theorem relation_second {b q A C : ℝ} (hq : q ≠ 0) :
    b * A / q * (C * q) = b * (C * A) := by
  field_simp

private theorem relation_third {a b c q A C : ℝ} (ha : a ≠ 0) (hq : q ≠ 0) (hC : C ≠ 0)
    (hq2 : q ^ 2 = -(a * b)) :
    -(C * (C * q) * (c / a * A ^ 2 / C ^ 2)) = c * (A * (b * A / q)) := by
  have h1 : -(C * (C * q) * (c / a * A ^ 2 / C ^ 2)) = -(q * c * A ^ 2) / a := by
    field_simp
  have h2 : c * (A * (b * A / q)) = c * b * A ^ 2 / q := by ring
  rw [h1, h2, div_eq_div_iff ha hq]
  linear_combination (-(c * A ^ 2)) * hq2

/-- The modulus of the motion from `(A, 0, C)`: `k² = a₂ A² / (a₀ C²)`. -/
def topModulus (I : Fin 3 → ℝ) (A C : ℝ) : ℝ :=
  √(((I 1)⁻¹ - (I 0)⁻¹) / ((I 2)⁻¹ - (I 1)⁻¹)) * A / C

/-- The rate `q = √(−a₀ a₁)`. -/
def topRate (I : Fin 3 → ℝ) : ℝ := √(-(((I 2)⁻¹ - (I 1)⁻¹) * ((I 0)⁻¹ - (I 2)⁻¹)))

/-- The motion of the top from the point `(A, 0, C)`, for `M² > 2E I₁`. -/
def ellipticMotion (I : Fin 3 → ℝ) (A C t : ℝ) : Fin 3 → ℝ :=
  jacobiCurve A (((I 0)⁻¹ - (I 2)⁻¹) * A / topRate I) C (C * topRate I) (topModulus I A C) t

theorem ellipticMotion_zero (I : Fin 3 → ℝ) (A C : ℝ) : ellipticMotion I A C 0 = ![A, 0, C] :=
  jacobiCurve_zero _ _ _ _ _

variable {I : Fin 3 → ℝ}

theorem topRate_sq (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) :
    topRate I ^ 2 = -(((I 2)⁻¹ - (I 1)⁻¹) * ((I 0)⁻¹ - (I 2)⁻¹)) :=
  Real.sq_sqrt (by nlinarith)

theorem topRate_pos (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) :
    0 < topRate I :=
  Real.sqrt_pos.mpr (by nlinarith)

theorem topModulus_sq (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) (A C : ℝ) :
    topModulus I A C ^ 2 =
      ((I 1)⁻¹ - (I 0)⁻¹) / ((I 2)⁻¹ - (I 1)⁻¹) * A ^ 2 / C ^ 2 := by
  have hnn : 0 ≤ ((I 1)⁻¹ - (I 0)⁻¹) / ((I 2)⁻¹ - (I 1)⁻¹) :=
    div_nonneg_of_nonpos h2 h0.le
  rw [topModulus, div_pow, mul_pow, Real.sq_sqrt hnn]

/-- Landau–Lifshitz (37.10): the motion from `(A, 0, C)` solves Euler's
equations when the modulus is less than one, that is, for `M² > 2E I₁`. -/
theorem hasDerivAt_ellipticMotion (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) {A C : ℝ} (hC : C ≠ 0) (hk : topModulus I A C ^ 2 < 1)
    (t : ℝ) :
    HasDerivAt (ellipticMotion I A C) (eulerField I (ellipticMotion I A C t)) t := by
  have hq := topRate_pos h0 h1
  have hq2 := topRate_sq h0 h1
  have hk2 := topModulus_sq h0 h2 A C
  have hne0 : (I 2)⁻¹ - (I 1)⁻¹ ≠ 0 := h0.ne
  have hcurve := hasDerivAt_jacobiCurve hk (a₀ := (I 2)⁻¹ - (I 1)⁻¹)
    (a₁ := (I 0)⁻¹ - (I 2)⁻¹) (a₂ := (I 1)⁻¹ - (I 0)⁻¹) (A := A)
    (B := ((I 0)⁻¹ - (I 2)⁻¹) * A / topRate I) (C := C) (p := C * topRate I)
    (relation_first hq.ne' hq2) (relation_second hq.ne')
    (by
      rw [hk2]
      exact relation_third hne0 hq.ne' hC hq2) t
  refine hcurve.congr_deriv (funext fun i => ?_)
  fin_cases i
  · exact (eulerField_zero I _).symm
  · exact (eulerField_one I _).symm
  · exact (eulerField_two I _).symm

/-- The motion is the line of the flow of Euler's equations through
`(A, 0, C)`, defined for all times. -/
theorem flow_eulerField_ellipticMotion (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) {A C : ℝ} (hC : C ≠ 0)
    (hk : topModulus I A C ^ 2 < 1) (t : ℝ) :
    (t, ![A, 0, C]) ∈ flowDomain (eulerField I) ∧
      flow (eulerField I) (t, ![A, 0, C]) = ellipticMotion I A C t :=
  ⟨mem_flowDomain_of_hasDerivWithinAt (contDiff_eulerField I).continuous
      (ellipticMotion_zero I A C)
      fun r _ => (hasDerivAt_ellipticMotion h0 h1 h2 hC hk r).hasDerivWithinAt,
    flow_eq_of_hasDerivWithinAt ((contDiff_eulerField I).of_le (by simp))
      (ellipticMotion_zero I A C)
      fun r _ => (hasDerivAt_ellipticMotion h0 h1 h2 hC hk r).hasDerivWithinAt⟩

/-- The motion is periodic, with the period `2 · 2K / (C q)`. -/
theorem ellipticMotion_add_period (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    {A C : ℝ} (hC : C ≠ 0) (hk : topModulus I A C ^ 2 < 1) (t : ℝ) :
    ellipticMotion I A C (t + 2 * halfPeriod (topModulus I A C) / (C * topRate I)) =
      ellipticMotion I A C t := by
  have hq := (topRate_pos h0 h1).ne'
  have harg : C * topRate I * (t + 2 * halfPeriod (topModulus I A C) / (C * topRate I)) =
      C * topRate I * t + halfPeriod (topModulus I A C) + halfPeriod (topModulus I A C) := by
    field_simp
    ring
  simp only [ellipticMotion, jacobiCurve, harg, sn_add_halfPeriod hk, cn_add_halfPeriod hk,
    dn_add_halfPeriod hk, neg_neg]

/-- The motion of the top from the point `(A, 0, C)`, for `M² < 2E I₁`: the
axes `0` and `2` exchange their roles. -/
def ellipticMotion' (I : Fin 3 → ℝ) (A C t : ℝ) : Fin 3 → ℝ :=
  jacobiCurve' A (((I 0)⁻¹ - (I 2)⁻¹) * C /
      √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹)))) C
    (A * √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹))))
    (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) t

theorem ellipticMotion'_zero (I : Fin 3 → ℝ) (A C : ℝ) :
    ellipticMotion' I A C 0 = ![A, 0, C] :=
  jacobiCurve'_zero _ _ _ _ _

/-- The motion from `(A, 0, C)` in the regime `M² < 2E I₁`. -/
theorem hasDerivAt_ellipticMotion' (h0 : (I 2)⁻¹ - (I 1)⁻¹ ≤ 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {A C : ℝ} (hA : A ≠ 0)
    (hk : (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) ^ 2 < 1) (t : ℝ) :
    HasDerivAt (ellipticMotion' I A C) (eulerField I (ellipticMotion' I A C t)) t := by
  have hrad : 0 < -(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹)) := by nlinarith
  have hq : 0 < √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹))) := Real.sqrt_pos.mpr hrad
  have hq2 : √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹))) ^ 2 =
      -(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹)) := Real.sq_sqrt hrad.le
  have hnn : 0 ≤ ((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹) := div_nonneg_of_nonpos h0 h2.le
  have hk2 : (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) ^ 2 =
      ((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹) * C ^ 2 / A ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hnn]
  have hne2 : (I 1)⁻¹ - (I 0)⁻¹ ≠ 0 := h2.ne
  have hq2' : √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹))) ^ 2 =
      -(((I 1)⁻¹ - (I 0)⁻¹) * ((I 0)⁻¹ - (I 2)⁻¹)) := by
    rw [hq2]
    ring
  have hcurve := hasDerivAt_jacobiCurve' hk (a₀ := (I 2)⁻¹ - (I 1)⁻¹)
    (a₁ := (I 0)⁻¹ - (I 2)⁻¹) (a₂ := (I 1)⁻¹ - (I 0)⁻¹) (A := A)
    (B := ((I 0)⁻¹ - (I 2)⁻¹) * C / √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹)))) (C := C)
    (p := A * √(-(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹))))
    (by
      rw [hk2]
      exact (relation_third hne2 hq.ne' hA hq2').trans (by ring))
    ((relation_second hq.ne').trans (by ring))
    ((relation_first hq.ne' hq2').trans (by ring)) t
  refine hcurve.congr_deriv (funext fun i => ?_)
  fin_cases i
  · exact (eulerField_zero I _).symm
  · exact (eulerField_one I _).symm
  · exact (eulerField_two I _).symm

/-! ### Every motion of the regime is given by the elliptic functions -/

/-- Every point of the regime `M² > 2E I₁` is on a motion by elliptic functions
from a point of the plane of the axes `0` and `2`. -/
theorem exists_ellipticMotion_eq (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {L₀ : Fin 3 → ℝ}
    (hreg : ((I 2)⁻¹ - (I 1)⁻¹) * L₀ 2 ^ 2 < ((I 1)⁻¹ - (I 0)⁻¹) * L₀ 0 ^ 2) :
    ∃ A C t₀ : ℝ, C ≠ 0 ∧ topModulus I A C ^ 2 < 1 ∧ ellipticMotion I A C t₀ = L₀ := by
  obtain ⟨A, C, t₀, hC, hk, hcurve⟩ := exists_jacobiCurve_eq h0 h1 h2 (y := L₀ 1) hreg
  refine ⟨A, C, t₀, hC, hk, hcurve.trans ?_⟩
  funext i
  fin_cases i <;> rfl

/-- Landau–Lifshitz §37: every solution of Euler's equations in the regime
`M² > 2E I₁` is a motion by elliptic functions, up to a shift of the time. -/
theorem eq_ellipticMotion_of_hasDerivAt (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {y : ℝ → Fin 3 → ℝ}
    (hy : ∀ t, HasDerivAt y (eulerField I (y t)) t)
    (hreg : ((I 2)⁻¹ - (I 1)⁻¹) * y 0 2 ^ 2 < ((I 1)⁻¹ - (I 0)⁻¹) * y 0 0 ^ 2) :
    ∃ A C t₀ : ℝ, C ≠ 0 ∧ topModulus I A C ^ 2 < 1 ∧
      ∀ t, y t = ellipticMotion I A C (t + t₀) := by
  obtain ⟨A, C, t₀, hC, hk, h0y⟩ := exists_ellipticMotion_eq h0 h1 h2 hreg
  refine ⟨A, C, t₀, hC, hk, fun t => ?_⟩
  refine eq_of_hasDerivAt_of_eq ((contDiff_eulerField I).of_le (by simp)) (f := y)
    (g := fun r => ellipticMotion I A C (r + t₀)) (s := 0) (t := t) (fun r _ => hy r)
    (fun r _ => (hasDerivAt_ellipticMotion h0 h1 h2.le hC hk (r + t₀)).comp_add_const r t₀) ?_
  rw [zero_add, h0y]

/-- Every point of the regime `M² < 2E I₁` is on a motion by elliptic functions
from a point of the plane of the axes `0` and `2`. -/
theorem exists_ellipticMotion'_eq (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0) (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹)
    (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {L₀ : Fin 3 → ℝ}
    (hreg : ((I 1)⁻¹ - (I 0)⁻¹) * L₀ 0 ^ 2 < ((I 2)⁻¹ - (I 1)⁻¹) * L₀ 2 ^ 2) :
    ∃ A C t₀ : ℝ, A ≠ 0 ∧
      (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) ^ 2 < 1 ∧
      ellipticMotion' I A C t₀ = L₀ := by
  obtain ⟨A', C', t₀, hC', hk, hcurve⟩ := exists_jacobiCurve_eq h2 h1 h0 (x := L₀ 2)
    (y := L₀ 1) (z := L₀ 0) hreg
  have hcomm : -(((I 1)⁻¹ - (I 0)⁻¹) * ((I 0)⁻¹ - (I 2)⁻¹)) =
      -(((I 0)⁻¹ - (I 2)⁻¹) * ((I 1)⁻¹ - (I 0)⁻¹)) := by ring
  rw [hcomm] at hcurve
  refine ⟨C', A', t₀, hC', hk, ?_⟩
  rw [ellipticMotion', jacobiCurve'_eq, hcurve]
  funext i
  fin_cases i <;> rfl

/-- Every solution of Euler's equations in the regime `M² < 2E I₁` is a motion
by elliptic functions, up to a shift of the time. -/
theorem eq_ellipticMotion'_of_hasDerivAt (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ < 0) {y : ℝ → Fin 3 → ℝ}
    (hy : ∀ t, HasDerivAt y (eulerField I (y t)) t)
    (hreg : ((I 1)⁻¹ - (I 0)⁻¹) * y 0 0 ^ 2 < ((I 2)⁻¹ - (I 1)⁻¹) * y 0 2 ^ 2) :
    ∃ A C t₀ : ℝ, A ≠ 0 ∧
      (√(((I 2)⁻¹ - (I 1)⁻¹) / ((I 1)⁻¹ - (I 0)⁻¹)) * C / A) ^ 2 < 1 ∧
      ∀ t, y t = ellipticMotion' I A C (t + t₀) := by
  obtain ⟨A, C, t₀, hA, hk, h0y⟩ := exists_ellipticMotion'_eq h0 h1 h2 hreg
  refine ⟨A, C, t₀, hA, hk, fun t => ?_⟩
  refine eq_of_hasDerivAt_of_eq ((contDiff_eulerField I).of_le (by simp)) (f := y)
    (g := fun r => ellipticMotion' I A C (r + t₀)) (s := 0) (t := t) (fun r _ => hy r)
    (fun r _ => (hasDerivAt_ellipticMotion' h0.le h1 h2 hA hk (r + t₀)).comp_add_const r t₀)
    ?_
  rw [zero_add, h0y]

/-! ### The motion as a trajectory of the Lie–Poisson bracket -/

/-- The motion in the regime `M² > 2E I₁` as a family of smooth functions of
time. -/
def ellipticTrajectory (I : Fin 3 → ℝ) (A C : ℝ) (hk : topModulus I A C ^ 2 < 1) :
    Fin 3 → TimeFunction := fun i =>
  SmoothOperation.ofContDiff (fun s : Fin 1 → ℝ => ellipticMotion I A C (s 0) i) (by
    have hlin : ContDiff ℝ ∞ fun s : Fin 1 → ℝ => C * topRate I * s 0 :=
      contDiff_const.mul (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).contDiff
    fin_cases i
    · exact contDiff_const.mul ((contDiff_cn hk).comp hlin)
    · exact contDiff_const.mul ((contDiff_sn hk).comp hlin)
    · exact contDiff_const.mul ((contDiff_dn hk).comp hlin))

/-- The motion by elliptic functions is a trajectory of the rigid body. -/
theorem isTrajectory_ellipticTrajectory (h0 : (I 2)⁻¹ - (I 1)⁻¹ < 0)
    (h1 : 0 < (I 0)⁻¹ - (I 2)⁻¹) (h2 : (I 1)⁻¹ - (I 0)⁻¹ ≤ 0) {A C : ℝ} (hC : C ≠ 0)
    (hk : topModulus I A C ^ 2 < 1) :
    IsTrajectory poisson (kineticEnergy I) (ellipticTrajectory I A C hk) := by
  rw [isTrajectory_iff_hasDerivAt]
  intro t
  exact hasDerivAt_ellipticMotion h0 h1 h2 hC hk t

end ProjectAinos.Mechanics.RigidBody
