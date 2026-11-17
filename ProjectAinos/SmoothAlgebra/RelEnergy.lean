/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.Derivation
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# The relativistic energy in a C-infinity ring

The function `√(1 + Σ wᵢ²)` is smooth on all of `ℝᵈ`, so it is a smooth operation
`SmoothOperation.lorentzFactor d`, and so is its inverse. In every C-infinity ring they give
`lorentzFactor w` and `invLorentzFactor w` for a tuple `w`, with

* `lorentzFactor_mul_self`: `lorentzFactor w * lorentzFactor w = 1 + Σ wᵢ²`,
* `lorentzFactor_mul_invLorentzFactor`: `lorentzFactor w * invLorentzFactor w = 1`,
* `SmoothDerivation.apply_lorentzFactor`: a vector field `D` satisfies
  `D (lorentzFactor w) = invLorentzFactor w * Σ wᵢ D wᵢ`.

For a real number `m ≠ 0` the relativistic energy of the momenta `π` is
`relEnergy m π = m · lorentzFactor (π/m)`: it satisfies `relEnergy_mul_self`,
`E · E = m² + Σ πᵢ²`, it is invertible (`relEnergy_mul_relEnergyInv`), and
`D E = E⁻¹ Σ πᵢ D πᵢ` (`SmoothDerivation.apply_relEnergy`). On real numbers and for `m > 0` it
is `√(m² + Σ πᵢ²)` (`relEnergy_real`). The function `s ↦ √(m² + s)` is not smooth on the line,
so the energy is an operation of the `d` momenta and not of the sum of their squares. Calculations
with the energy use the two relations and the derivative, and no derivative of a square root.

The velocities `E⁻¹ πᵢ` satisfy `Σ (E⁻¹ πᵢ)² = 1 − m² E⁻²` (`sum_relEnergyInv_mul_sq`), so on
real numbers they lie inside the unit ball (`sum_sq_relEnergyInv_mul_lt_one`).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SmoothAlgebra

open SmoothRing
open scoped ContDiff

namespace SmoothOperation

variable {d : ℕ}

theorem one_add_sum_sq_pos (w : Fin d → ℝ) : 0 < 1 + ∑ i, w i ^ 2 :=
  add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => sq_nonneg (w i))

theorem contDiff_one_add_sum_sq :
    ContDiff ℝ ∞ (fun w : Fin d → ℝ => 1 + ∑ i, w i ^ 2) :=
  contDiff_const.add (ContDiff.sum fun i _ => (contDiff_apply ℝ (fun _ : Fin d => ℝ) i).pow 2)

/-- The operation `√(1 + Σ wᵢ²)`, smooth on all of `ℝᵈ`. -/
def lorentzFactor (d : ℕ) : SmoothOperation d :=
  ofContDiff (fun w => Real.sqrt (1 + ∑ i, w i ^ 2))
    (contDiff_one_add_sum_sq.sqrt fun w => (one_add_sum_sq_pos w).ne')

/-- The operation `1/√(1 + Σ wᵢ²)`. -/
def invLorentzFactor (d : ℕ) : SmoothOperation d :=
  ofContDiff (fun w => (Real.sqrt (1 + ∑ i, w i ^ 2))⁻¹)
    ((contDiff_one_add_sum_sq.sqrt fun w => (one_add_sum_sq_pos w).ne').inv
      fun w => (Real.sqrt_pos.mpr (one_add_sum_sq_pos w)).ne')

@[simp] theorem lorentzFactor_apply (w : Fin d → ℝ) :
    lorentzFactor d w = Real.sqrt (1 + ∑ i, w i ^ 2) := rfl

@[simp] theorem invLorentzFactor_apply (w : Fin d → ℝ) :
    invLorentzFactor d w = (Real.sqrt (1 + ∑ i, w i ^ 2))⁻¹ := rfl

theorem lorentzFactor_pos (w : Fin d → ℝ) : 0 < lorentzFactor d w :=
  Real.sqrt_pos.mpr (one_add_sum_sq_pos w)

/-- `√(1 + Σ wᵢ²)² = 1 + Σ wᵢ²`, as an identity of operations. -/
theorem lorentzFactor_mul_self :
    lorentzFactor d * lorentzFactor d = 1 + ∑ i, proj i * proj i := by
  ext w
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply, lorentzFactor_apply, ContMDiffMap.coe_add,
    Pi.add_apply, ContMDiffMap.coe_one, Pi.one_apply, sum_apply, proj_apply]
  rw [Real.mul_self_sqrt (one_add_sum_sq_pos w).le]
  simp only [pow_two]

theorem lorentzFactor_mul_invLorentzFactor :
    lorentzFactor d * invLorentzFactor d = 1 := by
  ext w
  simp only [ContMDiffMap.coe_mul, Pi.mul_apply, lorentzFactor_apply, invLorentzFactor_apply,
    ContMDiffMap.coe_one, Pi.one_apply]
  exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (one_add_sum_sq_pos w)).ne'

/-- The partial derivatives of `√(1 + Σ wᵢ²)` are `wᵢ/√(1 + Σ wᵢ²)`. -/
theorem partialDeriv_lorentzFactor (i : Fin d) :
    partialDeriv i (lorentzFactor d) = invLorentzFactor d * proj i := by
  ext w
  have hj (j : Fin d) : HasFDerivAt (fun w : Fin d → ℝ => w j ^ 2)
      ((2 * w j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) w := by
    simpa using ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j).hasFDerivAt
      (x := w)).pow 2
  have hg : HasFDerivAt (fun w : Fin d → ℝ => 1 + ∑ j, w j ^ 2)
      (∑ j, (2 * w j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) j)) w :=
    (HasFDerivAt.fun_sum fun j _ => hj j).const_add 1
  have hs := hg.sqrt (one_add_sum_sq_pos w).ne'
  have hpos := Real.sqrt_pos.mpr (one_add_sum_sq_pos w)
  change fderiv ℝ (fun w : Fin d → ℝ => Real.sqrt (1 + ∑ j, w j ^ 2)) w (Pi.single i 1) = _
  rw [hs.fderiv]
  simp only [smul_apply, _root_.sum_apply, ContinuousLinearMap.proj_apply, Pi.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ContMDiffMap.coe_mul, Pi.mul_apply, invLorentzFactor_apply, proj_apply]
  field_simp

end SmoothOperation

variable {A B : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B] {d : ℕ}

/-- `√(1 + Σ wᵢ²)` for a tuple of elements of a C-infinity ring. -/
def lorentzFactor (w : Fin d → A) : A := op (SmoothOperation.lorentzFactor d) w

/-- `1/√(1 + Σ wᵢ²)` for a tuple of elements of a C-infinity ring. -/
def invLorentzFactor (w : Fin d → A) : A := op (SmoothOperation.invLorentzFactor d) w

theorem lorentzFactor_mul_self (w : Fin d → A) :
    lorentzFactor w * lorentzFactor w = 1 + ∑ i, w i * w i := by
  rw [lorentzFactor, ← op_mul, SmoothOperation.lorentzFactor_mul_self, op_add, op_one, op_sum]
  simp only [op_mul, op_proj]

theorem lorentzFactor_mul_invLorentzFactor (w : Fin d → A) :
    lorentzFactor w * invLorentzFactor w = 1 := by
  rw [lorentzFactor, invLorentzFactor, ← op_mul,
    SmoothOperation.lorentzFactor_mul_invLorentzFactor, op_one]

/-- A smooth operation on real constants is the constant of its value. -/
theorem SmoothRing.op_algebraMap {n : ℕ} (f : SmoothOperation n) (a : Fin n → ℝ) :
    op f (fun i => algebraMap ℝ A (a i)) = algebraMap ℝ A (f a) := by
  have h := op_comp f (fun i => SmoothOperation.const 0 (a i)) (Fin.elim0 : Fin 0 → A)
  simp only [op_nullary] at h
  rw [← h]
  exact op_nullary (f a) Fin.elim0

/-- At zero the factor is one. -/
theorem lorentzFactor_zero : lorentzFactor (fun _ : Fin d => (0 : A)) = 1 := by
  have h := op_algebraMap (A := A) (SmoothOperation.lorentzFactor d) fun _ => 0
  simp only [map_zero] at h
  rw [lorentzFactor, h, SmoothOperation.lorentzFactor_apply]
  simp

/-- A vector field differentiates `√(1 + Σ wᵢ²)` by the chain rule. -/
theorem SmoothDerivation.apply_lorentzFactor (D : SmoothDerivation A A) (w : Fin d → A) :
    D (lorentzFactor w) = invLorentzFactor w * ∑ i, w i * D (w i) := by
  rw [lorentzFactor, D.chain, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [SmoothOperation.partialDeriv_lorentzFactor, op_mul, op_proj, smul_eq_mul, invLorentzFactor,
    mul_assoc]

theorem SmoothRingHom.map_lorentzFactor (φ : SmoothRingHom A B) (w : Fin d → A) :
    φ (lorentzFactor w) = lorentzFactor fun i => φ (w i) :=
  φ.map_op _ _

theorem SmoothRingHom.map_invLorentzFactor (φ : SmoothRingHom A B) (w : Fin d → A) :
    φ (invLorentzFactor w) = invLorentzFactor fun i => φ (w i) :=
  φ.map_op _ _

/-- The relativistic energy `m · √(1 + Σ (πᵢ/m)²)` of the momenta `π`. For `m > 0` it is
`√(m² + Σ πᵢ²)`; it has the sign of `m`. -/
def relEnergy (m : ℝ) (π : Fin d → A) : A :=
  algebraMap ℝ A m * lorentzFactor fun i => algebraMap ℝ A m⁻¹ * π i

/-- The inverse of the relativistic energy. -/
def relEnergyInv (m : ℝ) (π : Fin d → A) : A :=
  algebraMap ℝ A m⁻¹ * invLorentzFactor fun i => algebraMap ℝ A m⁻¹ * π i

/-- At zero momenta the energy is the mass. -/
theorem relEnergy_zero (m : ℝ) : relEnergy m (fun _ : Fin d => (0 : A)) = algebraMap ℝ A m := by
  rw [relEnergy]
  simp only [mul_zero]
  rw [lorentzFactor_zero, mul_one]

omit [SmoothRing A] in
theorem algebraMap_mul_algebraMap_inv {m : ℝ} (hm : m ≠ 0) :
    algebraMap ℝ A m * algebraMap ℝ A m⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel₀ hm, map_one]

/-- `E² = m² + Σ πᵢ²`. -/
theorem relEnergy_mul_self {m : ℝ} (hm : m ≠ 0) (π : Fin d → A) :
    relEnergy m π * relEnergy m π = algebraMap ℝ A (m ^ 2) + ∑ i, π i * π i := by
  have h := algebraMap_mul_algebraMap_inv (A := A) hm
  have hsum : algebraMap ℝ A m * algebraMap ℝ A m *
      ∑ i, algebraMap ℝ A m⁻¹ * π i * (algebraMap ℝ A m⁻¹ * π i) = ∑ i, π i * π i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (algebraMap ℝ A m * algebraMap ℝ A m⁻¹ + 1) * π i * π i * h
  rw [relEnergy, mul_mul_mul_comm, lorentzFactor_mul_self, mul_add, mul_one, hsum, pow_two,
    map_mul]

/-- The relativistic energy is invertible. -/
theorem relEnergy_mul_relEnergyInv {m : ℝ} (hm : m ≠ 0) (π : Fin d → A) :
    relEnergy m π * relEnergyInv m π = 1 := by
  rw [relEnergy, relEnergyInv, mul_mul_mul_comm, lorentzFactor_mul_invLorentzFactor, mul_one,
    algebraMap_mul_algebraMap_inv hm]

/-- A vector field differentiates the energy: `D E = E⁻¹ Σ πᵢ D πᵢ`. -/
theorem SmoothDerivation.apply_relEnergy {m : ℝ} (hm : m ≠ 0) (D : SmoothDerivation A A)
    (π : Fin d → A) : D (relEnergy m π) = relEnergyInv m π * ∑ i, π i * D (π i) := by
  have h := algebraMap_mul_algebraMap_inv (A := A) hm
  rw [relEnergy, D.map_mul, D.map_algebraMap, smul_zero, add_zero, D.apply_lorentzFactor,
    relEnergyInv, smul_eq_mul, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.map_mul, D.map_algebraMap, smul_zero, add_zero, smul_eq_mul]
  linear_combination algebraMap ℝ A m⁻¹ *
    invLorentzFactor (fun i => algebraMap ℝ A m⁻¹ * π i) * π i * D (π i) * h

/-- A vector field differentiates the inverse energy: `D E⁻¹ = −E⁻³ Σ πᵢ D πᵢ`. -/
theorem SmoothDerivation.apply_relEnergyInv {m : ℝ} (hm : m ≠ 0) (D : SmoothDerivation A A)
    (π : Fin d → A) : D (relEnergyInv m π) =
      -(relEnergyInv m π * relEnergyInv m π * relEnergyInv m π * ∑ i, π i * D (π i)) := by
  have h := relEnergy_mul_relEnergyInv (A := A) hm π
  have hD : D (relEnergy m π * relEnergyInv m π) = 0 := by rw [h, D.map_one]
  rw [D.map_mul, D.apply_relEnergy hm, smul_eq_mul, smul_eq_mul] at hD
  linear_combination relEnergyInv m π * hD - D (relEnergyInv m π) * h

/-- The velocities `E⁻¹ πᵢ` have `Σ (E⁻¹ πᵢ)² = 1 − m² E⁻²`. -/
theorem sum_relEnergyInv_mul_sq {m : ℝ} (hm : m ≠ 0) (π : Fin d → A) :
    ∑ i, relEnergyInv m π * π i * (relEnergyInv m π * π i) =
      1 - algebraMap ℝ A (m ^ 2) * (relEnergyInv m π * relEnergyInv m π) := by
  have h1 := relEnergy_mul_self (A := A) hm π
  have h2 := relEnergy_mul_relEnergyInv (A := A) hm π
  have hsum : ∑ i, relEnergyInv m π * π i * (relEnergyInv m π * π i) =
      relEnergyInv m π * relEnergyInv m π * ∑ i, π i * π i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  linear_combination (-(relEnergyInv m π * relEnergyInv m π)) * h1 +
    (relEnergy m π * relEnergyInv m π + 1) * h2

/-- On real numbers and for a positive mass the energy is `√(m² + Σ πᵢ²)`. -/
theorem relEnergy_real {m : ℝ} (hm : 0 < m) (π : Fin d → ℝ) :
    relEnergy m π = Real.sqrt (m ^ 2 + ∑ i, π i ^ 2) := by
  have hx : m ^ 2 + ∑ i, π i ^ 2 = m ^ 2 * (1 + ∑ i, (m⁻¹ * π i) ^ 2) := by
    rw [mul_add, mul_one, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
  rw [hx, Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq hm.le]
  rfl

/-- On real numbers the energy of a positive mass is positive. -/
theorem relEnergy_real_pos {m : ℝ} (hm : 0 < m) (π : Fin d → ℝ) : 0 < relEnergy m π :=
  mul_pos hm (SmoothOperation.lorentzFactor_pos _)

/-- On real numbers `relEnergyInv` is the inverse of the energy. -/
theorem relEnergyInv_real {m : ℝ} (hm : m ≠ 0) (π : Fin d → ℝ) :
    relEnergyInv m π = (relEnergy m π)⁻¹ :=
  eq_inv_of_mul_eq_one_right (relEnergy_mul_relEnergyInv hm π)

/-- On real numbers the velocity `π/E` is inside the unit ball: `Σ (πᵢ/E)² < 1`. -/
theorem sum_sq_relEnergyInv_mul_lt_one {m : ℝ} (hm : m ≠ 0) (π : Fin d → ℝ) :
    ∑ i, (relEnergyInv m π * π i) ^ 2 < 1 := by
  have h : ∑ i, relEnergyInv m π * π i * (relEnergyInv m π * π i) =
      1 - m ^ 2 * (relEnergyInv m π * relEnergyInv m π) := sum_relEnergyInv_mul_sq hm π
  have hne : relEnergyInv m π ≠ 0 := right_ne_zero_of_mul_eq_one (relEnergy_mul_relEnergyInv hm π)
  have hpos : 0 < m ^ 2 * (relEnergyInv m π * relEnergyInv m π) :=
    mul_pos (pow_pos (abs_pos.mpr hm) 2 |>.trans_eq (sq_abs m)) (mul_self_pos.mpr hne)
  simp only [pow_two]
  rw [h]
  linarith

/-- On real numbers each component of the velocity `π/E` is less than one. -/
theorem abs_relEnergyInv_mul_lt_one {m : ℝ} (hm : m ≠ 0) (π : Fin d → ℝ) (i : Fin d) :
    |relEnergyInv m π * π i| < 1 := by
  refine (sq_lt_one_iff_abs_lt_one _).mp (lt_of_le_of_lt ?_ (sum_sq_relEnergyInv_mul_lt_one hm π))
  exact Finset.single_le_sum (f := fun j => (relEnergyInv m π * π j) ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ i)

theorem SmoothRingHom.map_relEnergy (φ : SmoothRingHom A B) (m : ℝ) (π : Fin d → A) :
    φ (relEnergy m π) = relEnergy m fun i => φ (π i) := by
  simp only [relEnergy, map_mul, φ.map_lorentzFactor, φ.map_algebraMap]

theorem SmoothRingHom.map_relEnergyInv (φ : SmoothRingHom A B) (m : ℝ) (π : Fin d → A) :
    φ (relEnergyInv m π) = relEnergyInv m fun i => φ (π i) := by
  simp only [relEnergyInv, map_mul, φ.map_invLorentzFactor, φ.map_algebraMap]

end ProjectAinos.SmoothAlgebra
