/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Convention
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-! # Minkowski bilinear forms and convention-independent intervals -/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace ProjectAInos.SmoothGeometry

/-- One time coordinate and `d` spatial coordinates. -/
abbrev MinkowskiModel (d : ℕ) := Fin (d + 1) → ℝ

/-- The diagonal Lorentz signature in inertial coordinates. -/
def lorentzSign (σ : LorentzConvention) {d : ℕ} (i : Fin (d + 1)) : ℝ := σ.timeSign * (if i = 0 then 1 else -1)

/-- The continuous bilinear Minkowski form. -/
def minkowskiForm (σ : LorentzConvention) (d : ℕ) : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  ∑ i, lorentzSign σ i •
    (ContinuousLinearMap.proj i : MinkowskiModel d →L[ℝ] ℝ).smulRight
      (ContinuousLinearMap.proj i : MinkowskiModel d →L[ℝ] ℝ)

theorem minkowskiForm_apply (σ : LorentzConvention) {d : ℕ} (v w : MinkowskiModel d) :
    minkowskiForm σ d v w = ∑ i, lorentzSign σ i * (v i * w i) := by
  simp [minkowskiForm, smul_eq_mul]

theorem minkowskiForm_symmetric (σ : LorentzConvention) {d : ℕ} (v w : MinkowskiModel d) :
    minkowskiForm σ d v w = minkowskiForm σ d w v := by
  simp only [minkowskiForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (v i) (w i)]

theorem minkowskiForm_nondegenerate (σ : LorentzConvention) {d : ℕ} (v : MinkowskiModel d)
    (h : ∀ w, minkowskiForm σ d v w = 0) : v = 0 := by
  funext i
  have hi := h (Pi.single i 1)
  simp only [minkowskiForm_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hi
  have hs : lorentzSign σ i ≠ 0 := by simp [lorentzSign]; split <;> norm_num
  exact (mul_eq_zero.mp hi).resolve_left hs


@[simp] theorem lorentzSign_sq (σ : LorentzConvention) {d : ℕ} (i : Fin (d+1)) :
    lorentzSign σ i * lorentzSign σ i = 1 := by
  cases σ <;> by_cases h : i = 0 <;> simp [lorentzSign, h]

@[simp] theorem lorentzSign_opposite (σ : LorentzConvention) {d : ℕ} (i : Fin (d+1)) :
    lorentzSign σ.opposite i = -lorentzSign σ i := by
  by_cases h : i = 0 <;> simp [lorentzSign, h]

@[simp] theorem minkowskiForm_opposite (σ : LorentzConvention) (d : ℕ) :
    minkowskiForm σ.opposite d = -minkowskiForm σ d := by
  ext v w
  simp [minkowskiForm_apply, Finset.sum_neg_distrib]

theorem minkowskiForm_convention (σ : LorentzConvention) {d : ℕ} (v w : MinkowskiModel d) :
    minkowskiForm σ d v w = σ.timeSign * minkowskiForm .timePositive d v w := by
  simp [minkowskiForm_apply, lorentzSign, Finset.mul_sum]

namespace Minkowski

variable {d : ℕ}

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def time : MinkowskiModel d →L[ℝ] ℝ := ContinuousLinearMap.proj 0

def space : MinkowskiModel d →L[ℝ] Space d :=
  (EuclideanSpace.equiv (Fin d) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ)

@[simp] theorem time_apply (v : MinkowskiModel d) : time v = v 0 := rfl
@[simp] theorem space_apply (v : MinkowskiModel d) (i : Fin d) : space v i = v i.succ := rfl

/-- Assemble a time coordinate and a Euclidean spatial vector. -/
def vector (t : ℝ) (x : Space d) : MinkowskiModel d := Fin.cons t (fun i => x i)

@[simp] theorem vector_zero (t : ℝ) (x : Space d) : vector t x 0 = t := rfl
@[simp] theorem vector_succ (t : ℝ) (x : Space d) (i : Fin d) : vector t x i.succ = x i := rfl

@[simp] theorem time_vector (t : ℝ) (x : Space d) : time (vector t x) = t := rfl
@[simp] theorem space_vector (t : ℝ) (x : Space d) : space (vector t x) = x := by ext i; rfl
@[simp] theorem vector_time_space (v : MinkowskiModel d) : vector (time v) (space v) = v := by
  ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def pair : MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ :=
  minkowskiForm .timePositive d

theorem pair_apply (v w : MinkowskiModel d) :
    pair v w = time v * time w - inner ℝ (space v) (space w) := by
  simp [pair, minkowskiForm_apply, lorentzSign, Fin.sum_univ_succ,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, space_apply, sub_eq_add_neg,
    Finset.sum_neg_distrib, mul_comm]

/-- Positive on timelike vectors, independent of the metric convention. -/
def intervalQuadratic : QuadraticForm ℝ (MinkowskiModel d) :=
  LinearMap.BilinMap.toQuadraticMap pair.toLinearMap₁₂

theorem intervalQuadratic_apply (v : MinkowskiModel d) :
    intervalQuadratic v = pair v v := rfl

theorem intervalQuadratic_coordinates (v : MinkowskiModel d) :
    intervalQuadratic v = time v ^ 2 - ‖space v‖ ^ 2 := by
  simp only [intervalQuadratic_apply, pair_apply, real_inner_self_eq_norm_sq, pow_two]

theorem intervalQuadratic_convention (σ : LorentzConvention) (v : MinkowskiModel d) :
    σ.timeSign * minkowskiForm σ d v v = intervalQuadratic v := by
  rw [minkowskiForm_convention, ← mul_assoc, σ.timeSign_mul_self, one_mul]; rfl

theorem metric_eq (σ : LorentzConvention) (v w : MinkowskiModel d) :
    minkowskiForm σ d v w = σ.timeSign * pair v w := minkowskiForm_convention σ v w

@[simp] theorem pair_comm (v w : MinkowskiModel d) : pair v w = pair w v :=
  minkowskiForm_symmetric .timePositive v w

end Minkowski
end ProjectAInos.SmoothGeometry
