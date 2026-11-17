/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.HamiltonianField
public import ProjectAinos.Mechanics.Poisson.RigidBodyMotion
public import ProjectAinos.SmoothGeometry.ODE.JacobiElliptic

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

/-! ### Curves of Jacobi's functions -/

/-- The curve `(A cn, B sn, C dn)(p t)`. -/
def jacobiCurve (A B C p k t : ℝ) : Fin 3 → ℝ :=
  ![A * cn k (p * t), B * sn k (p * t), C * dn k (p * t)]

theorem jacobiCurve_zero (A B C p k : ℝ) : jacobiCurve A B C p k 0 = ![A, 0, C] := by
  simp [jacobiCurve]

/-- A curve `(A cn, B sn, C dn)(p t)` solves `L̇₀ = a₀ L₁ L₂`, `L̇₁ = a₁ L₂ L₀`,
`L̇₂ = a₂ L₀ L₁` when the amplitudes, the rate and the modulus satisfy three
relations. -/
theorem hasDerivAt_jacobiCurve {k : ℝ} (hk : k ^ 2 < 1) {a₀ a₁ a₂ A B C p : ℝ}
    (h0 : -(A * p) = a₀ * (B * C)) (h1 : B * p = a₁ * (C * A))
    (h2 : -(C * p * k ^ 2) = a₂ * (A * B)) (t : ℝ) :
    HasDerivAt (jacobiCurve A B C p k)
      ![a₀ * (jacobiCurve A B C p k t 1 * jacobiCurve A B C p k t 2),
        a₁ * (jacobiCurve A B C p k t 2 * jacobiCurve A B C p k t 0),
        a₂ * (jacobiCurve A B C p k t 0 * jacobiCurve A B C p k t 1)] t := by
  have hlin : HasDerivAt (fun t : ℝ => p * t) p t := by
    simpa using (hasDerivAt_id t).const_mul p
  have hs := (hasDerivAt_sn hk (p * t)).comp t hlin
  have hc := (hasDerivAt_cn hk (p * t)).comp t hlin
  have hd := (hasDerivAt_dn hk (p * t)).comp t hlin
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · refine (hc.const_mul A).congr_deriv ?_
    change A * (-(sn k (p * t) * dn k (p * t)) * p) =
      a₀ * (B * sn k (p * t) * (C * dn k (p * t)))
    linear_combination (sn k (p * t) * dn k (p * t)) * h0
  · refine (hs.const_mul B).congr_deriv ?_
    change B * (cn k (p * t) * dn k (p * t) * p) =
      a₁ * (C * dn k (p * t) * (A * cn k (p * t)))
    linear_combination (cn k (p * t) * dn k (p * t)) * h1
  · refine (hd.const_mul C).congr_deriv ?_
    change C * (-(k ^ 2 * sn k (p * t) * cn k (p * t)) * p) =
      a₂ * (A * cn k (p * t) * (B * sn k (p * t)))
    linear_combination (sn k (p * t) * cn k (p * t)) * h2

/-- The same with the roles of the first and the last co-ordinate exchanged:
the curve `(A dn, B sn, C cn)(p t)`. -/
def jacobiCurve' (A B C p k t : ℝ) : Fin 3 → ℝ :=
  ![A * dn k (p * t), B * sn k (p * t), C * cn k (p * t)]

theorem jacobiCurve'_zero (A B C p k : ℝ) : jacobiCurve' A B C p k 0 = ![A, 0, C] := by
  simp [jacobiCurve']

theorem hasDerivAt_jacobiCurve' {k : ℝ} (hk : k ^ 2 < 1) {a₀ a₁ a₂ A B C p : ℝ}
    (h0 : -(A * p * k ^ 2) = a₀ * (B * C)) (h1 : B * p = a₁ * (C * A))
    (h2 : -(C * p) = a₂ * (A * B)) (t : ℝ) :
    HasDerivAt (jacobiCurve' A B C p k)
      ![a₀ * (jacobiCurve' A B C p k t 1 * jacobiCurve' A B C p k t 2),
        a₁ * (jacobiCurve' A B C p k t 2 * jacobiCurve' A B C p k t 0),
        a₂ * (jacobiCurve' A B C p k t 0 * jacobiCurve' A B C p k t 1)] t := by
  have hlin : HasDerivAt (fun t : ℝ => p * t) p t := by
    simpa using (hasDerivAt_id t).const_mul p
  have hs := (hasDerivAt_sn hk (p * t)).comp t hlin
  have hc := (hasDerivAt_cn hk (p * t)).comp t hlin
  have hd := (hasDerivAt_dn hk (p * t)).comp t hlin
  rw [hasDerivAt_pi]
  intro i
  fin_cases i
  · refine (hd.const_mul A).congr_deriv ?_
    change A * (-(k ^ 2 * sn k (p * t) * cn k (p * t)) * p) =
      a₀ * (B * sn k (p * t) * (C * cn k (p * t)))
    linear_combination (sn k (p * t) * cn k (p * t)) * h0
  · refine (hs.const_mul B).congr_deriv ?_
    change B * (cn k (p * t) * dn k (p * t) * p) =
      a₁ * (C * cn k (p * t) * (A * dn k (p * t)))
    linear_combination (cn k (p * t) * dn k (p * t)) * h1
  · refine (hc.const_mul C).congr_deriv ?_
    change C * (-(sn k (p * t) * dn k (p * t)) * p) =
      a₂ * (A * dn k (p * t) * (B * sn k (p * t)))
    linear_combination (sn k (p * t) * dn k (p * t)) * h2

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

/-- A point of the plane with `u² + w² = 1` is `(cos φ, sin φ)`. -/
theorem exists_cos_sin_eq {u w : ℝ} (h : u ^ 2 + w ^ 2 = 1) :
    ∃ φ : ℝ, Real.cos φ = u ∧ Real.sin φ = w := by
  have hu1 : -1 ≤ u := by nlinarith [sq_nonneg w, sq_nonneg (u + 1)]
  have hu2 : u ≤ 1 := by nlinarith [sq_nonneg w, sq_nonneg (u - 1)]
  have hsin : Real.sin (Real.arccos u) = |w| := by
    rw [Real.sin_arccos, show 1 - u ^ 2 = w ^ 2 by linarith, Real.sqrt_sq_eq_abs]
  rcases le_total 0 w with hw | hw
  · exact ⟨Real.arccos u, Real.cos_arccos hu1 hu2, by rw [hsin, abs_of_nonneg hw]⟩
  · refine ⟨-Real.arccos u, by rw [Real.cos_neg, Real.cos_arccos hu1 hu2], ?_⟩
    rw [Real.sin_neg, hsin, abs_of_nonpos hw, neg_neg]

/-- Every point with `a z² < c x²`, for coefficients `a < 0 < b` and `c < 0`,
lies on a curve of Jacobi's functions that solves the system with these
coefficients. -/
theorem exists_jacobiCurve_eq {a b c : ℝ} (ha : a < 0) (hb : 0 < b) (hc : c < 0)
    {x y z : ℝ} (hreg : a * z ^ 2 < c * x ^ 2) :
    ∃ A C t₀ : ℝ, C ≠ 0 ∧ (√(c / a) * A / C) ^ 2 < 1 ∧
      jacobiCurve A (b * A / √(-(a * b))) C (C * √(-(a * b))) (√(c / a) * A / C) t₀ =
        ![x, y, z] := by
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0] at hreg
    nlinarith [sq_nonneg x]
  have hz2 : 0 < z ^ 2 := by positivity
  have hane : a ≠ 0 := ha.ne
  have hbne : b ≠ 0 := hb.ne'
  have hrad : 0 < -(a * b) := by nlinarith
  have hq : 0 < √(-(a * b)) := Real.sqrt_pos.mpr hrad
  have hq2 : √(-(a * b)) ^ 2 = -(a * b) := Real.sq_sqrt hrad.le
  have hab : a / b < 0 := div_neg_of_neg_of_pos ha hb
  have hcb : c / b < 0 := div_neg_of_neg_of_pos hc hb
  have hca : 0 ≤ c / a := div_nonneg_of_nonpos hc.le ha.le
  have hAsq : 0 ≤ x ^ 2 - a / b * y ^ 2 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hCsq : 0 < z ^ 2 - c / b * y ^ 2 := by nlinarith [sq_nonneg y]
  obtain ⟨A, hA0, hA2⟩ : ∃ A : ℝ, 0 ≤ A ∧ A ^ 2 = x ^ 2 - a / b * y ^ 2 :=
    ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt hAsq⟩
  obtain ⟨C, hCne, hC2, hCz⟩ : ∃ C : ℝ, C ≠ 0 ∧ C ^ 2 = z ^ 2 - c / b * y ^ 2 ∧ 0 < C * z := by
    have hS : 0 < √(z ^ 2 - c / b * y ^ 2) := Real.sqrt_pos.mpr hCsq
    have habs : 0 < |z| := abs_pos.mpr hz
    have hr : 0 < √(z ^ 2 - c / b * y ^ 2) / |z| := div_pos hS habs
    refine ⟨z * (√(z ^ 2 - c / b * y ^ 2) / |z|), mul_ne_zero hz hr.ne', ?_, by nlinarith⟩
    rw [mul_pow, div_pow, Real.sq_sqrt hCsq.le, sq_abs]
    field_simp
  have hk2 : (√(c / a) * A / C) ^ 2 = c / a * A ^ 2 / C ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hca]
  have hk : (√(c / a) * A / C) ^ 2 < 1 := by
    rw [hk2, hA2, hC2, div_lt_one hCsq]
    have h1 : c / a * (x ^ 2 - a / b * y ^ 2) = c / a * x ^ 2 - c / b * y ^ 2 := by
      field_simp
    have h2 : c / a * x ^ 2 < z ^ 2 := by
      rw [div_mul_eq_mul_div, div_lt_iff_of_neg ha]
      linarith
    linarith
  rcases eq_or_lt_of_le hA0 with hA | hA
  · -- the point is on the axis of the co-ordinate `z`
    have hzero : x ^ 2 - a / b * y ^ 2 = 0 := by rw [← hA2, ← hA]; ring
    have hy : y = 0 := by
      by_contra hy0
      have : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg x]
    have hx : x = 0 := by
      rw [hy] at hzero
      simpa using hzero
    have hCz' : C = z := by
      rw [hy] at hC2
      have h1 : (C - z) * (C + z) = 0 := by nlinarith
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · exfalso
        have : C = -z := by linarith
        rw [this] at hCz
        nlinarith
    refine ⟨A, C, 0, hCne, hk, ?_⟩
    rw [jacobiCurve_zero, ← hA, hx, hy, hCz']
  · -- the angle of the point `(x / A, y / B)` on the circle
    have hA2ne : A ^ 2 ≠ 0 := pow_ne_zero 2 hA.ne'
    have hB2 : (b * A / √(-(a * b))) ^ 2 = -(b / a) * A ^ 2 := by
      rw [div_pow, mul_pow, hq2]
      field_simp
    have hcirc : (x / A) ^ 2 + (y / (b * A / √(-(a * b)))) ^ 2 = 1 := by
      rw [div_pow, div_pow, hB2]
      have h1 : y ^ 2 / (-(b / a) * A ^ 2) = -(a / b * y ^ 2) / A ^ 2 := by
        field_simp
      rw [h1, ← add_div, div_eq_one_iff_eq hA2ne]
      linarith
    obtain ⟨φ, hcos, hsin⟩ := exists_cos_sin_eq hcirc
    obtain ⟨u₀, hu₀⟩ := am_surjective hk φ
    have harg : C * √(-(a * b)) * (u₀ / (C * √(-(a * b)))) = u₀ := by
      field_simp
    have hB : b * A / √(-(a * b)) ≠ 0 := (div_pos (mul_pos hb hA) hq).ne'
    refine ⟨A, C, u₀ / (C * √(-(a * b))), hCne, hk, ?_⟩
    funext i
    fin_cases i
    · change A * cn (√(c / a) * A / C) (C * √(-(a * b)) * (u₀ / (C * √(-(a * b))))) = x
      rw [harg, cn, hu₀, hcos, mul_comm, div_mul_cancel₀ x hA.ne']
    · change b * A / √(-(a * b)) *
        sn (√(c / a) * A / C) (C * √(-(a * b)) * (u₀ / (C * √(-(a * b))))) = y
      rw [harg, sn, hu₀, hsin, mul_comm, div_mul_cancel₀ y hB]
    · change C * dn (√(c / a) * A / C) (C * √(-(a * b)) * (u₀ / (C * √(-(a * b))))) = z
      have hC2ne : C ^ 2 ≠ 0 := pow_ne_zero 2 hCne
      have h1 : c / a * A ^ 2 / C ^ 2 * (y ^ 2 / (-(b / a) * A ^ 2)) =
          -(c / b * y ^ 2) / C ^ 2 := by
        field_simp
      have h2 : (1 - -(c / b * y ^ 2) / C ^ 2) * C ^ 2 = C ^ 2 + c / b * y ^ 2 := by
        field_simp
        ring
      have hval : 1 - (√(c / a) * A / C) ^ 2 * (y / (b * A / √(-(a * b)))) ^ 2 =
          z ^ 2 / C ^ 2 := by
        rw [hk2, div_pow y, hB2, h1, eq_div_iff hC2ne, h2, hC2]
        ring
      have hsqrt : √(z ^ 2 / C ^ 2) = |z| / |C| := by
        rw [Real.sqrt_div (sq_nonneg z), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
      have hdn : dn (√(c / a) * A / C) u₀ = |z| / |C| := by
        rw [dn, hu₀, amplitudeField, hsin, hval, hsqrt]
      rw [harg, hdn]
      rcases lt_or_gt_of_ne hCne with hCneg | hCpos
      · have hzneg : z < 0 := (neg_iff_neg_of_mul_pos hCz).mp hCneg
        rw [abs_of_neg hzneg, abs_of_neg hCneg]
        field_simp
      · have hzpos : 0 < z := (pos_iff_pos_of_mul_pos hCz).mp hCpos
        rw [abs_of_pos hzpos, abs_of_pos hCpos]
        field_simp

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

/-- The curve with the first and the last co-ordinate exchanged. -/
theorem jacobiCurve'_eq (A B C p k t : ℝ) :
    jacobiCurve' A B C p k t =
      ![jacobiCurve C B A p k t 2, jacobiCurve C B A p k t 1, jacobiCurve C B A p k t 0] := by
  funext i
  fin_cases i <;> rfl

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
